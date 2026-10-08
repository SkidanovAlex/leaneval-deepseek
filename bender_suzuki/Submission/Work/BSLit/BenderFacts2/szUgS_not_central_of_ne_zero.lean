import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- The root elements `u(a,b)` of the Suzuki `2`-group inside `SzModel n` are parametrised
injectively by `(a, b)`: this is `Submission.Sz.szUg_injective` transported through the
subgroup inclusion `SzModel n ≤ GL(4, F)`. -/
lemma szUgS_pair_injective {n : ℕ} {a b c d : Submission.Sz.SzField n}
    (h : szUgS n a b = szUgS n c d) : a = c ∧ b = d := by
  have hmat : Submission.Sz.szUg n a b = Submission.Sz.szUg n c d := by
    have h1 := Subtype.ext_iff.mp h
    rwa [szUgS_coe, szUgS_coe] at h1
  have h2 : Submission.Sz.szU n a b = Submission.Sz.szU n c d := by
    have h3 := congrArg (fun u : GL (Fin 4) (Submission.Sz.SzField n) =>
      ((u : Matrix (Fin 4) (Fin 4) (Submission.Sz.SzField n)))) hmat
    rwa [Submission.Sz.szUg_coe, Submission.Sz.szUg_coe] at h3
  have hone : (fun p : Submission.Sz.SzField n × Submission.Sz.SzField n =>
      Submission.Sz.szU n p.1 p.2) (a, b)
      = (fun p : Submission.Sz.SzField n × Submission.Sz.SzField n =>
      Submission.Sz.szU n p.1 p.2) (c, d) := h2
  exact Prod.ext_iff.mp (Submission.Sz.szU_injective n hone)

/-- A root element `u(a,b)` of the Suzuki `2`-group with `a ≠ 0` is not central in `SzModel n`:
the group-theoretic form of the multiplication law `u(a,b)·u(c,d) = u(a+c, b+d+a·c^(2^(n+1)))`
gives `u(a,b)·u(c,0) = u(c,0)·u(a,b)` only when `a·c^(2^(n+1)) = c·a^(2^(n+1))`, and the existence
of an element `x` of the field with `x^(2^(n+1)) ≠ x` turns that requirement into a contradiction
with `a ≠ 0`. -/
theorem szUgS_not_central_of_ne_zero (n : ℕ) (hn : 1 ≤ n) (a b : Submission.Sz.SzField n)
    (ha : a ≠ 0) :
    ¬ ∀ c d : Submission.Sz.SzField n,
      szUgS n a b * szUgS n c d = szUgS n c d * szUgS n a b := by
  intro h
  -- From `u(a,b)·u(c,0) = u(c,0)·u(a,b)` and injectivity we get `a * c^(2^(n+1)) = c * a^(2^(n+1))`.
  have hcomm : ∀ c : Submission.Sz.SzField n,
      a * c ^ (2 ^ (n + 1)) = c * a ^ (2 ^ (n + 1)) := by
    intro c
    have hc := h c 0
    rw [szUgS_mul, szUgS_mul] at hc
    have h2 := (szUgS_pair_injective hc).2
    simp only [add_zero, zero_add] at h2
    exact add_left_cancel h2
  -- Taking `c = 1` gives `a = a^(2^(n+1))`.
  have haq : a ^ (2 ^ (n + 1)) = a := by
    have h1 := hcomm 1
    simpa using h1.symm
  -- Hence `c^(2^(n+1)) = c` for every `c`, contradicting `exists_pow_two_pow_ne_self`.
  obtain ⟨x, hx⟩ := Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self n hn
  have hcx := hcomm x
  rw [haq] at hcx
  have h2 : x ^ (2 ^ (n + 1)) = x := by
    refine mul_left_cancel₀ ha ?_
    rw [mul_comm a x]
    exact hcx
  exact hx h2

end Work.BSLit.BenderFacts2
