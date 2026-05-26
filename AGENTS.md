# AGENTS.md

Guidance for AI coding assistants (GitHub Copilot, Claude Code, Cursor,
Aider, Codex CLI, and friends) contributing to
[`OpenDevicePartnership/embedded-mcu`](https://github.com/OpenDevicePartnership/embedded-mcu).

Human contributors are welcome to read this file too — it captures the
conventions that the CI gates enforce.

> **Precedence.** When this document conflicts with
> [`.github/copilot-instructions.md`](.github/copilot-instructions.md), this
> document wins for everything *except* commit-message formatting and AI
> attribution, which `copilot-instructions.md` owns. When it conflicts with
> [`CONTRIBUTING.md`](CONTRIBUTING.md), `CONTRIBUTING.md` wins for legal /
> licensing / PR-etiquette topics.

---

## 1. Repository at a glance

`embedded-mcu` is a **Cargo workspace** of MCU-agnostic trait crates for
embedded firmware. It deliberately ships *no* MCU-specific code — concrete
implementations belong in board / chip support crates that depend on the
traits defined here.

```
embedded-mcu/
├── Cargo.toml              # workspace root (resolver = "2")
├── deny.toml               # cargo-deny configuration
├── rust-toolchain.toml     # pins rustfmt + clippy components
├── rustfmt.toml            # max_width = 120
├── supply-chain/           # cargo-vet audits
├── .github/
│   ├── copilot-instructions.md
│   └── workflows/          # check.yml, nostd.yml, cargo-vet*.yml
├── embedded-mcu-hal/       # trait crate: time / nvram / watchdog / i2c
└── storage-bus/            # trait crate: nor / nand storage bus
```

### Workspace members

| Crate | Path | MSRV | Edition | Purpose |
|-------|------|------|---------|---------|
| `embedded-mcu-hal` | `embedded-mcu-hal/` | 1.90 | 2021 | Traits for higher-level peripherals (RTC, NVRAM, watchdog, I²C target) — complements `embedded-hal`. |
| `storage_bus` | `storage-bus/` | 1.85 | 2024 | Generic storage-bus traits used by NOR/NAND flash device drivers (SPI, FlexSPI, …). |

> **Note the underscore.** The directory is `storage-bus/` but the crate
> name is `storage_bus`. Use the crate name in `Cargo.toml` / `use`
> statements and the directory name in file paths.

### Module inventory

`embedded-mcu-hal/src/`:

- `lib.rs` — crate root, gated `#![cfg_attr(not(test), no_std)]`
- `i2c/` — re-exports `embedded_hal::i2c` address types plus a `target`
  submodule for I²C *target* (slave) abstractions
- `nvram.rs` — `Nvram`, `NvramStorage` traits for byte-addressable
  non-volatile RAM
- `time/` — `Datetime`, `DatetimeFields`, `Month` value types and the
  `DatetimeClock` RTC trait (`datetime.rs`, `datetime_clock.rs`)
- `watchdog.rs` — `Watchdog` trait

`storage-bus/src/`:

- `lib.rs` — `#![no_std]` crate root
- `nor.rs` — NOR flash bus traits (e.g. `BlockingNorStorageBusDriver`,
  `NorStorageCmd`)
- `nand.rs` — NAND flash bus traits

---

## 2. Non-negotiable invariants

Treat the following as load-bearing. Do **not** loosen them without an
explicit human request:

1. **`no_std` first.** Every public item in every crate must be usable on
   bare metal with no allocator.
   - `embedded-mcu-hal/src/lib.rs` uses
     `#![cfg_attr(not(test), no_std)]` so `std` is linked only under
     `cfg(test)`.
   - `storage-bus/src/lib.rs` is unconditionally `#![no_std]`.
   - The `nostd` workflow (`.github/workflows/nostd.yml`) runs
     `cargo check --target thumbv8m.main-none-eabihf --locked` on every
     PR. If your change pulls in `std` it will fail there.
2. **Trait-only, MCU-agnostic.** No register addresses, magic values, or
   chip-specific types in public APIs. Concrete drivers belong elsewhere.
3. **Fallible by default.** Trait methods return `Result`. Infallible
   wrappers, if needed, live in downstream crates.
4. **No panics in library code.** The workspace lints below promote
   `unwrap`, `expect`, `panic`, `todo`, `unimplemented`, `unreachable`,
   and indexing-slice panics to `deny`. Use `Result` and `Option`
   combinators, or return a typed error.
5. **Features must be additive.** CI runs `cargo hack
   --feature-powerset`, so any combination of features must compile and
   pass clippy. Avoid `cfg(not(feature = "x"))` gates that would break
   under feature unification.
6. **MSRV is real.** `cargo +1.90 check --locked` runs in CI. Don't use
   APIs newer than 1.90 in `embedded-mcu-hal`, or newer than 1.85 in
   `storage_bus`, without bumping the corresponding `rust-version`
   *and* documenting why in `embedded-mcu-hal/src/lib.rs` (which today
   calls out `u16::is_multiple_of` as the reason for 1.90).
7. **Supply-chain hygiene.** New dependencies must pass `cargo deny`
   (licenses limited to MIT / Apache-2.0 / Unicode-3.0 / BSD-3-Clause)
   and `cargo vet`. The only allowed git source organization is
   `embassy-rs` (see `deny.toml` → `[sources.allow-org]`).

---

## 3. Workspace lints (the clippy contract)

`Cargo.toml` sets these at the workspace level and each member opts in
with `[lints] workspace = true`:

```toml
[workspace.lints.clippy]
correctness        = "deny"
expect_used        = "deny"
indexing_slicing   = "deny"
panic              = "deny"
panic_in_result_fn = "deny"
perf               = "deny"
suspicious         = "deny"
style              = "deny"
todo               = "deny"
unimplemented      = "deny"
unreachable        = "deny"
unwrap_used        = "deny"
```

Practical consequences for AI-generated code:

- Prefer `?`, `ok_or(...)`, `ok_or_else(...)`, `map_err(...)`, and
  pattern matching over `.unwrap()` / `.expect("...")`.
- Index slices via `.get(i).ok_or(Error::OutOfBounds)?` rather than
  `slice[i]`.
- Never insert `todo!()`, `unimplemented!()`, or `unreachable!()`
  placeholders, even in scaffolding. Either implement the function or
  leave the file out of the change.
- If you genuinely need `unreachable!` for a match arm the compiler
  cannot prove dead, add an `#[allow(clippy::unreachable)]` with a
  short justification comment — and only with a strong reason.

Formatting:

- `rustfmt.toml` sets `max_width = 120`. Run `cargo fmt` before
  committing. CI runs `cargo fmt --check` and will fail otherwise.

---

## 4. Build, test, lint, doc — what to run locally

These mirror the workflows in `.github/workflows/check.yml` and
`nostd.yml`. Run them from the workspace root.

| Goal | Command |
|------|---------|
| Format check | `cargo fmt --check` |
| Apply formatting | `cargo fmt` |
| Workspace build (host) | `cargo check --locked` |
| Embedded build | `cargo check --target thumbv8m.main-none-eabihf --locked` |
| Tests (all feature combos) | `cargo hack --feature-powerset test --locked` |
| Tests (quick) | `cargo test --locked` |
| Clippy (CI parity) | `cargo hack --feature-powerset --target thumbv8m.main-none-eabihf clippy --locked -- -Dwarnings -D clippy::suspicious -D clippy::correctness -D clippy::perf -D clippy::style` |
| Clippy (quick) | `cargo clippy --all-targets --locked -- -Dwarnings` |
| Docs (nightly, as CI runs) | `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --no-deps --all-features` |
| Docs (stable, quick) | `cargo doc --no-deps --all-features` |
| MSRV check | `cargo +1.90 check --locked` |
| Unused deps | `cargo machete` |
| Supply chain | `cargo deny --all-features --locked check` |
| Vetted deps | `cargo vet --locked` |

The MSRV, `cargo-hack`, `cargo-deny`, `cargo-machete`, and `cargo-vet`
tools are not in the default toolchain — install with
`cargo install cargo-hack cargo-deny cargo-machete cargo-vet` (or use
`taiki-e/install-action` if scripting in CI, matching `check.yml`).

> **Windows note.** On PowerShell the `RUSTDOCFLAGS` env-var syntax is
> `$env:RUSTDOCFLAGS = '--cfg docsrs'; cargo +nightly doc --no-deps --all-features`.

### Before declaring a change "done"

At minimum, run, in this order:

1. `cargo fmt`
2. `cargo clippy --all-targets --locked -- -Dwarnings`
3. `cargo test --locked`
4. `cargo check --target thumbv8m.main-none-eabihf --locked`
5. `cargo doc --no-deps --all-features`

If you touched dependencies or features, also run the `cargo hack`,
`cargo deny`, `cargo machete`, and `cargo vet` commands above.

---

## 5. Coding conventions

### API design

- Document every public item with rustdoc. Follow the prose style in
  `embedded-mcu-hal/src/lib.rs` — short summary, then a longer
  explanation, then examples if non-trivial.
- Prefer associated types and generics over `dyn Trait` in trait
  signatures — these crates target firmware that often disables dynamic
  dispatch.
- Errors should be enums in the module they describe. Make them
  `#[non_exhaustive]` when reasonable to preserve future additions.
- Gate optional integrations behind Cargo features (see `chrono`,
  `defmt` in `embedded-mcu-hal/Cargo.toml`). Add the feature to
  `[package.metadata.docs.rs] features = [...]` so docs.rs builds it.
- When deriving `defmt::Format`, gate the derive on
  `#[cfg_attr(feature = "defmt", derive(defmt::Format))]`.

### Tests

- Host tests live alongside the module (`#[cfg(test)] mod tests { … }`)
  and are run with `cargo test`. `embedded-mcu-hal` already uses
  `proptest` and `tokio` (`macros`, `rt`, `time`) under
  `[dev-dependencies]` — reuse them rather than adding a new test
  runner.
- New `dev-dependencies` must still satisfy `cargo deny` and `cargo
  vet`. Prefer existing dependencies when possible.
- For trait crates with no runtime code, the most valuable tests are:
  property tests on value types (e.g. `Datetime` round-trips) and
  compile-pass tests that exercise generic bounds.

### `no_std` discipline

- Do not add `use std::…` outside `#[cfg(test)]`.
- Prefer `core::` and `alloc::` (only if a feature gates alloc — none
  do today).
- Be careful with `format!`, `String`, `Vec`, `println!`,
  `std::time::*` — none of those are available in the embedded build.

### `defmt` integration

- For new public types, derive `Format` behind the `defmt` feature so
  downstream firmware can `defmt::info!("{}", value)` them.
- Do **not** call `defmt::*!` macros from library code — leave logging
  to consumers.

---

## 6. Commits, branches, and PRs

These rules come from `CONTRIBUTING.md` and
`.github/copilot-instructions.md`; AI agents must obey them.

### Branches

- Branch from `main` (or whichever upstream branch a reviewer asks for).
- Use a short, descriptive kebab-case branch name. Conventional prefixes
  like `feat/`, `fix/`, `docs/` are welcome but not required.

### Commits

- **Subject:** capitalized, ≤50 characters, imperative mood
  ("Add `Watchdog::feed`", not "Added feed").
- **Body:** wrap at 72 columns, blank line after the subject, explain
  *what* and *why* (not *how*).
- Each commit must **build cleanly without warnings**
  (`CONTRIBUTING.md` → "Clean Commit History"). Squash fix-up commits
  before pushing for review.
- Squash-merge is disabled on this repo; the merged history is the
  commits you push. Keep them tidy.

### AI attribution — required

Every commit containing AI-generated or AI-assisted work **must** carry
an `Assisted-by` trailer (and no `Signed-off-by` — only humans certify
the DCO):

```
Assisted-by: AGENT_NAME:MODEL_VERSION [TOOL1] [TOOL2]
```

Examples:

```
Assisted-by: GitHub Copilot:claude-opus-4.7
Assisted-by: GitHub Copilot:gpt-5
Assisted-by: GitHub Copilot:claude-sonnet-4.5 clippy
```

Rules:

- `AGENT_NAME` is the surfacing tool (`GitHub Copilot`, `Cursor`,
  `Aider`, `Claude Code`, `Codex CLI`, …).
- `MODEL_VERSION` is the *actual* underlying model. **Verify it at the
  start of the session** — do not copy a value from a previous task.
- Optional bracketed tool names are for specialized analyzers
  (`coccinelle`, `sparse`, `smatch`, `clang-tidy`, …). Routine tools
  (git, cargo, your editor) do **not** appear here.

### Author identity

Set the author per-commit; do **not** alter the global git config:

```bash
git -c user.name='Your Name' -c user.email='you@example.com' commit -m '…'
```

When committing on behalf of a human, use their name and email exactly
as they specify.

### Pull requests

- Open a **draft PR first** so the lint and CI workflows can run before
  reviewers are pinged.
- Confirm the `.github/` checks (fmt, clippy, doc, test, msrv, deny,
  vet, machete, nostd) are green, then move the PR out of draft.
- If reporting a regression, run `git bisect` first and cite the first
  offending commit.

### What AI agents must not do

- Do not run `git push --force` or `--force-with-lease` on shared
  branches without explicit human approval.
- Do not edit `.git/config`, modify global git settings, or change
  remote URLs without being asked.
- Do not commit secrets, API tokens, or vendor-specific datasheets.
- Do not add a `Signed-off-by` trailer on your own.

---

## 7. Dependency policy

- Prefer existing workspace dependencies (`embedded-hal` is the
  canonical example, declared in `[workspace.dependencies]`).
- New deps must:
  - Carry a permissive license already in `deny.toml`'s `allow` list.
  - Be `no_std` compatible (or feature-gated so they only appear in
    host builds / dev-deps).
  - Pass `cargo vet` (run `cargo vet` locally; if it flags a missing
    audit, follow up with the maintainers before merging).
- Pin git sources behind the `embassy-rs` org or open a discussion to
  add another to `deny.toml`.
- Use `default-features = false` whenever practical, then opt back in
  with explicit features — this minimizes the surface for both
  `cargo-deny` and the embedded build.

---

## 8. Per-pilot notes

### GitHub Copilot (chat & coding agent)

- Read `.github/copilot-instructions.md` first — it is loaded by Copilot
  automatically and is authoritative for commit format and AI
  attribution.
- When suggesting code in a function that returns `Result`, never
  introduce `.unwrap()` / `.expect()` — the workspace lints will reject
  it.
- When generating module scaffolds, ensure they compile cleanly; do not
  leave `todo!()` placeholders.
- The Copilot coding agent should run the §4 verification chain before
  pushing.

### Claude Code / Anthropic agents

- Treat the §2 invariants as hard constraints; do not rationalise around
  them.
- Use the workspace `cargo` commands rather than ad-hoc Python/Node
  tooling — there is no JS/Python in this repo.
- When editing trait definitions, search downstream usage with
  `rg "trait Name"` and audit every implementor before declaring a
  change complete.
- Prefer `view` + `edit` over rewriting whole files; this repo cares
  about a clean diff and a clean commit history.

### Cursor / Continue / Cody

- Honor `rustfmt.toml`'s `max_width = 120` — disable any global
  formatter override for this workspace.
- When generating multi-file edits, ensure each commit in the resulting
  series still builds (CI gate from `CONTRIBUTING.md`).
- Surface the relevant module's docstring in the chat context before
  proposing API changes.

### Aider

- Use `--lint-cmd "cargo fmt --check && cargo clippy --all-targets --locked -- -Dwarnings"`
  to mirror the CI gate locally.
- Pass `--test-cmd "cargo test --locked"` so Aider only commits when
  the suite passes.
- Aider's auto-commit messages must still satisfy §6 — pre-load the
  `Assisted-by` trailer via the `--commit-prompt` flag or amend before
  pushing.

### Codex CLI / OpenAI agents

- The default working directory should be the workspace root; nested
  crates have their own `Cargo.toml` but the `[workspace]` resolver
  expects commands to come from the root.
- Verify the model name (`gpt-5`, `o4-mini`, etc.) at session start and
  use it verbatim in the `Assisted-by` trailer.

### Generic / unknown agents

If the agent's identity is uncertain, do **not** invent an
`Assisted-by` value. Stop and ask the human operator for the correct
agent name and model version before committing.

---

## 9. Common pitfalls (and how to avoid them)

| Symptom | Likely cause | Fix |
|---------|--------------|-----|
| `clippy::unwrap_used` failure | `.unwrap()` in library code | Replace with `?`, `ok_or`, or pattern matching. |
| `clippy::indexing_slicing` failure | `slice[i]` access | Use `slice.get(i).ok_or(...)?`. |
| `cargo check --target thumbv8m.main-none-eabihf` fails | Pulled in `std` | Replace `std::` with `core::`; gate host-only code behind `#[cfg(test)]` or a feature. |
| `cargo hack --feature-powerset` fails | Non-additive features | Audit `cfg(not(feature = "x"))` blocks; ensure each feature only *adds* capability. |
| `cargo +1.90 check` fails | Used a post-1.90 API | Roll back the API, or bump `rust-version` *and* document the reason. |
| `cargo deny check` fails on license | Pulled in a GPL/AGPL crate | Replace with a permissively-licensed alternative or stop using it. |
| `cargo vet` fails | New transitive dep without audit | Add an audit (`cargo vet certify ...`) or pick a different crate. |
| `cargo fmt --check` fails | Forgot to format | Run `cargo fmt`. |
| `nostd` workflow passes locally, fails in CI | Default features differ | Run `cargo check --target thumbv8m.main-none-eabihf --no-default-features --locked` to match. |

---

## 10. Quick reference

```bash
# One-shot pre-push check (mirrors CI for most cases)
cargo fmt --check && \
cargo clippy --all-targets --locked -- -Dwarnings && \
cargo test --locked && \
cargo check --target thumbv8m.main-none-eabihf --locked && \
cargo doc --no-deps --all-features
```

```bash
# Author a commit as a human user without touching global git config
git -c user.name='Jane Doe' -c user.email='jane@example.com' commit \
    -m 'Add Watchdog::feed default impl' \
    -m '' \
    -m 'Provides a no-op blanket impl so chips without a watchdog' \
    -m 'still satisfy the trait bound used by generic drivers.' \
    -m '' \
    -m 'Assisted-by: GitHub Copilot:claude-opus-4.7'
```

---

*Last updated when this file was first introduced. If you change a CI
workflow, a workspace lint, the MSRV, or the workspace layout, update
this file in the same commit.*

## Model selection & cost discipline

Premium models (Opus, GPT-5 family, "high"/"xhigh" reasoning variants)
cost an order of magnitude more than standard models (Sonnet, Haiku,
mini). Most steps in a typical task do not need premium reasoning,
and over-using premium models wastes credits without improving
outcomes. The rules below apply to *all* model selection: your own
session, sub-agents launched via the `task` tool, and parallel work
launched via `/fleet`.

### Default posture

- **Default to the cheapest model that can do the job.** Reach for a
  premium model only when one of the escalation triggers below is hit.
- **Plan with premium, execute with cheap.** Spend at most one or two
  premium turns on design / planning, then downshift to a cheaper
  model for mechanical execution of the plan.
- **Never bump the model "just in case."** If you cannot articulate
  *why* a cheaper model would fail, use the cheaper model.

### Escalation triggers (use a premium model)

Reach for a premium model when *any* of these are true:

- Cross-module refactor, architectural design, or API design from
  scratch.
- Subtle correctness reasoning: concurrency, lifetimes, `unsafe`,
  FFI ABI, cryptography, safety-critical control paths.
- Debugging a failure that survived one prior cheap-model attempt.
- Reviewing code on a safety-, security-, or money-critical path.
- The diff cannot be predicted in advance — i.e. there is genuine
  creative or design work to do, not just typing.

### De-escalation triggers (use a cheap model)

Use the cheapest available model when *any* of these are true:

- Searching, reading, summarising files or docs.
- Single-file mechanical edits: rename, format, lint fix, dependency
  bump, boilerplate, scaffolding from a known template.
- Generating tests for code that already works.
- Running builds, tests, linters, or other commands where the model
  only needs to report success/failure.
- Routine commits, PR descriptions, changelog entries.
- The diff is essentially predictable before generation.

### Sub-agent routing (the `task` tool)

When delegating with the `task` tool, set `model:` explicitly. Do not
let sub-agents inherit a premium default for cheap work.

| Sub-agent type    | Default model             | Override to                                     |
|-------------------|---------------------------|-------------------------------------------------|
| `explore`         | cheap                     | keep cheap (`claude-haiku-4.5` or `gpt-5-mini`) |
| `task` (run cmd)  | cheap                     | keep cheap                                      |
| `research`        | cheap for breadth         | premium only for the final synthesis            |
| `general-purpose` | match task                | cheap for mechanical work; premium for design   |
| `rubber-duck`     | premium                   | keep premium — this is where reasoning pays off |
| `code-review`     | premium on critical paths | cheap on cosmetic / mechanical diffs            |

### `/fleet` (parallel sub-agents) rules

- Fleet mode multiplies cost by the fleet width. Apply the rules
  above *per worker*, not in aggregate.
- Split a fleet job along complexity lines: route the cheap,
  parallelisable workers (file edits, test runs, doc updates) to a
  cheap model; reserve premium models for the small number of
  workers that need real reasoning.
- If every worker in a fleet would need a premium model, the work is
  probably not a good fit for fleet mode — reconsider the
  decomposition before paying N× premium.

### Session hygiene

- Keep sessions short and focused. Long premium sessions are the
  single largest source of waste because every turn re-processes the
  full history.
- Use `/compact` when the conversation grows long, and `/new` for
  unrelated work.
- Prefer `/ask` for one-off side questions so they don't extend the
  main session.

### When in doubt

Ask: *"If a cheaper model produced the wrong answer here, would I
catch it in seconds (compiler, tests, my own review) or in
weeks (production incident)?"* If the former, use the cheap model
and let the feedback loop do its job.
