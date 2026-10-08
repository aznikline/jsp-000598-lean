import Mathlib

/-!
# JSP-000598: two distinct central binomial coefficients can share
exactly the same set of prime divisors

The question (Erdős–Graham–Ruzsa–Straus, EGRS75): can two distinct central
binomial coefficients have exactly the same prime divisors? The answer is
yes; the smallest pair is `n = 87`, `m = 88`.

Formal statement: there exist `n ≠ m` with
`(Nat.centralBinom n).primeFactors = (Nat.centralBinom m).primeFactors`.

Mathematical proof: by Kummer's theorem (`Nat.factorization_choose`), the
p-adic valuation of `centralBinom n = (2n choose n)` counts the carries when
adding `n + n` in base `p`. Hence `p ∈ primeFactors (centralBinom n)` iff
some `i` satisfies `p ^ i ≤ n % p ^ i + n % p ^ i`, a decidable predicate.
Any prime `p` in the support satisfies `p ≤ 2n`, so only `p ≤ 176` need be
checked; all 177 cases are discharged by `decide`.
-/

open Nat Finset

/-- Kummer criterion, packaged as a decidable `if`: the factorization of
`centralBinom n` at `p` is the number of carries when adding `n` to itself
in base `p`, or `0` when `p` is not prime. -/
theorem factorization_centralBinom' (n p : ℕ) :
    (Nat.centralBinom n).factorization p =
      if p.Prime
        then #{i ∈ Finset.Ico 1 (Nat.log p (n + n) + 1) |
                p ^ i ≤ n % p ^ i + n % p ^ i}
        else 0 := by
  by_cases hp : p.Prime
  · rw [ite_eq_left hp, Nat.centralBinom_eq_two_mul_choose, two_mul,
        Nat.factorization_choose' hp (Nat.lt_succ_self _)]
  · rw [ite_eq_right hp, Nat.factorization_eq_zero_of_not_prime _ hp]

set_option maxRecDepth 100000 in
/-- The supports of `centralBinom 87` and `centralBinom 88` agree. For
`p > 176` every carry test fails (`p ^ i ≥ p > 176 ≥ n % p ^ i + n % p ^ i`),
and for `p ≤ 176` all 177 cases are discharged by `decide`. -/
theorem primeFactors_centralBinom_87_88 :
    (Nat.centralBinom 87).primeFactors = (Nat.centralBinom 88).primeFactors := by
  ext p
  rw [← Nat.support_factorization, ← Nat.support_factorization,
      Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  by_cases h : p ≤ 176
  · rw [factorization_centralBinom' 87 p, factorization_centralBinom' 88 p]
    have key : ∀ q ∈ Finset.Ico 0 177,
        ((if q.Prime then #{i ∈ Finset.Ico 1 (Nat.log q (87 + 87) + 1) |
              q ^ i ≤ 87 % q ^ i + 87 % q ^ i} else 0) ≠ 0 ↔
         (if q.Prime then #{i ∈ Finset.Ico 1 (Nat.log q (88 + 88) + 1) |
              q ^ i ≤ 88 % q ^ i + 88 % q ^ i} else 0) ≠ 0) := by
      decide
    exact key p (Finset.mem_Ico.mpr ⟨Nat.zero_le p, by omega⟩)
  · have h0 : ∀ n : ℕ, n ≤ 88 →
        (if p.Prime
          then #{i ∈ Finset.Ico 1 (Nat.log p (n + n) + 1) |
                  p ^ i ≤ n % p ^ i + n % p ^ i}
          else 0) = 0 := by
      intro n hn
      by_cases hp : p.Prime
      · rw [ite_eq_left hp, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        rintro i hi
        rw [Finset.mem_filter, Finset.mem_Ico] at hi
        have hle : p ^ i ≤ n + n :=
          hi.2.trans (Nat.add_le_add (Nat.mod_le _ _) (Nat.mod_le _ _))
        have hlt : (176 : ℕ) < p ^ i :=
          lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
        omega
      · rw [ite_eq_right hp]
    rw [factorization_centralBinom' 87 p, factorization_centralBinom' 88 p,
        h0 87 (by norm_num), h0 88 (by norm_num)]

/-- JSP-000598: the answer is yes — `n = 87`, `m = 88`. -/
theorem jsp_000598 :
    ∃ n m : ℕ, n ≠ m ∧
      (Nat.centralBinom n).primeFactors = (Nat.centralBinom m).primeFactors :=
  ⟨87, 88, by decide, primeFactors_centralBinom_87_88⟩

#print axioms jsp_000598
