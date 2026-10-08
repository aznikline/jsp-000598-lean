# JSP-000598: central binomial coefficients with the same prime factors — Lean formalization

Lean 4 + Mathlib formalization of the answer to JSP-000598:

> Can two distinct central binomial coefficients have exactly the same
> prime divisors?

The answer is **yes**. The smallest pair is `n = 87`, `m = 88` (a known
example, also noted in the Erdős–Graham–Ruzsa–Straus problem history
[EGRS75] and on Erdős problem #730):

- `primeFactors (C(174, 87)) = primeFactors (C(176, 88))`
- the common support is
  `{2, 3, 5, 7, 11, 13, 19, 23, 31, 47, 53, 89, 97, 101, 103, 107, 109,
   113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173}`.

## Proof idea

By Kummer's theorem (`Nat.factorization_choose`), the `p`-adic valuation of
`(2n choose n)` equals the number of carries when `n` is added to itself in
base `p`, i.e. the cardinality of `{i ≥ 1 | p ^ i ≤ n % p ^ i + n % p ^ i}`.
For `p > 2n` there are no carries, so only `p ≤ 176` need be checked; the
177 cases are decided in the kernel by `decide`.

## Theorems

- `factorization_centralBinom'` — `centralBinom n`'s factorization at `p`
  as a decidable `if p.Prime then (carry count) else 0`.
- `primeFactors_centralBinom_87_88` — the two supports are equal.
- `jsp_000598` — `∃ n m : ℕ, n ≠ m ∧
  (Nat.centralBinom n).primeFactors = (Nat.centralBinom m).primeFactors`,
  witnessed by `(87, 88)`.

## Toolchain

- Lean `leanprover/lean4:v4.34.0` (see `lean-toolchain`)
- Mathlib `v4.34.0` (pinned in `lakefile.toml` / `lake-manifest.json`)

## Verification

```sh
lake build          # type-checks all theorems
```

`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`
(standard Mathlib axioms; no `sorry`, no extra axioms).
