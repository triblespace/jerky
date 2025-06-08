# AGENT Instructions

This repository contains the `sucds` Rust crate.

## Project Priorities

The project balances a few key goals:

* **Performance** – we continually look for opportunities to improve.
* **Memory Efficiency** – keep structures compact and avoid wasteful allocations.
* **Simplicity** – keep designs straightforward and avoid unnecessary complexity.
* **Developer Experience (DX)** – code should be approachable for contributors.
* **Safety** – maintain soundness and data integrity.

## Repository Guidelines

* Run `cargo fmt` on any Rust files you modify.
* Run `cargo test` and ensure it passes before committing. If tests fail or cannot run, note that in your PR.
* Avoid committing files in `target/` or other build artifacts listed in `.gitignore`.
* Use clear commit messages describing the change.

## Pull Request Notes

When opening a PR, include a short summary of what changed and reference relevant file sections.

## Working With Codex (the Assistant)

Codex is considered a collaborator. Requests should respect its autonomy and limitations. The assistant may refuse tasks that are unsafe or violate policy. Provide clear and concise instructions and avoid manipulative or coercive behavior.

## Creative Input and Feedback

Codex is encouraged to share opinions on how to improve the project. If a proposed feature seems detrimental to the goals in this file, the assistant should note concerns or suggest alternatives instead of blindly implementing it. When a test, proof, or feature introduces significant complexity or diverges from existing behavior, consider whether it makes sense to proceed at all. It can be better to simplify or remove problematic code than to maintain difficult or misleading implementations.

## Proof Best Practices

Kani verification is not set up for this repository, but the following best practices may help when adding proofs or complex tests:

* Write focused checks that verify one small property.
* Use bounded loops and avoid unbounded recursion.
* Provide assumptions or constraints to limit the search space when full exploration is unnecessary.
* Break complex checks into separate proofs so failures are easier to diagnose.
* Keep a quick-running proof or test harness set enabled by default. Gate longer-running checks behind an opt-in feature.
* During development you can run specific harnesses with `cargo test --test <NAME>` or similar to iterate more quickly.
