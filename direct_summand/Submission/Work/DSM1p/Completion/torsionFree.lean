import Mathlib
import Submission.Work.DSM1p.Basic

/-!
# `p`-torsion-freeness passes to the `p`-adic completion

Let `S` be a commutative ring, `s ∈ S` a non-zero-divisor, `I = (s)` and `Ŝ` the `I`-adic
completion of `S`.  Then `s` is again a non-zero-divisor on `Ŝ`.

This is the infinitesimal form of the fact used in Bhatt's construction of a perfectoid
cover: a `p`-torsion-free ring has a `p`-torsion-free `p`-adic completion.

The proof only uses the description `Ŝ = lim_n S / s ^ n S` of the completion as a
submodule of the product `∏_n S / s ^ n S`, together with the elementary remark that
multiplication by `s` on `S / s ^ (n+1)` has image of its kernel inside the image of
`s ^ n S`; hence any `z ∈ Ŝ` with `s • z = 0` has `z.val n = 0` for every `n`.

## Main result

* `Work.DSM1p.Completion.isSMulRegular_adicCompletion` — the general statement;
* `Work.DSM1p.Completion.torsionFree` — the requested corollary for `R[a^{1/p^∞}]`.
-/

namespace Work.DSM1p.Completion

open Submodule

/-- The `n`-th power of the principal ideal `(s)` acting on `S` is the principal ideal
`(s ^ n)`, viewed as a submodule of `S`. -/
lemma pow_smul_top_eq_span (S : Type*) [CommRing S] (s : S) (n : ℕ) :
    (Ideal.span {s}) ^ n • (⊤ : Submodule S S) = Ideal.span {s ^ n} := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

/-- If `s` is a non-zero-divisor and `s ^ (n + 1) ∣ s * u`, then `s ^ n ∣ u`. -/
lemma pow_dvd_of_isSMulRegular (S : Type*) [CommRing S] (s : S) (h : IsSMulRegular S s)
    (n : ℕ) {u : S} (H : s ^ (n + 1) ∣ s * u) : s ^ n ∣ u := by
  obtain ⟨q, hq⟩ := H
  refine ⟨q, ?_⟩
  have heq : s * u = s * (s ^ n * q) := by rw [hq, pow_succ']; ring
  exact h heq

/-- **The key step.**  Multiplication by a non-zero-divisor `s` on the quotient
`S ⧸ s ^ (n + 1) S` has its kernel contained in the image of `s ^ n S`; consequently the
canonical map `S ⧸ s ^ (n + 1) S → S ⧸ s ^ n S` kills it. -/
lemma factorPow_smul_eq_zero (S : Type*) [CommRing S] (s : S) (h : IsSMulRegular S s)
    (n : ℕ) {w : S ⧸ (Ideal.span {s}) ^ (n + 1) • (⊤ : Submodule S S)}
    (hw : s • w = 0) :
    Submodule.factorPow (Ideal.span {s}) S (Nat.le_succ n) w = 0 := by
  classical
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective
    ((Ideal.span {s}) ^ (n + 1) • (⊤ : Submodule S S)) w
  have hmk : (Submodule.Quotient.mk (p := (Ideal.span {s}) ^ (n + 1) • (⊤ : Submodule S S))
      (s • u)) = 0 := by
    rw [Submodule.Quotient.mk_smul, hu]
    exact hw
  have hmem : s • u ∈ (Ideal.span {s}) ^ (n + 1) • (⊤ : Submodule S S) :=
    (Submodule.Quotient.mk_eq_zero _).mp hmk
  have hdiv : s ^ (n + 1) ∣ s * u := by
    rw [pow_smul_top_eq_span, Ideal.mem_span_singleton] at hmem
    simpa using hmem
  have hdiv2 : s ^ n ∣ u := pow_dvd_of_isSMulRegular S s h n hdiv
  have hz0 : (Submodule.Quotient.mk (p := (Ideal.span {s}) ^ n • (⊤ : Submodule S S)) u) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (by
      rw [pow_smul_top_eq_span, Ideal.mem_span_singleton]; exact hdiv2)
  have hfac : Submodule.factorPow (Ideal.span {s}) S (Nat.le_succ n) w
      = Submodule.Quotient.mk (p := (Ideal.span {s}) ^ n • (⊤ : Submodule S S)) u := by
    rw [← hu]
    exact Submodule.factor_mk _ u
  rw [hfac, hz0]

/-- **`p`-torsion-freeness passes to the `p`-adic completion.**  If `s` is a
non-zero-divisor of a commutative ring `S`, then it is a non-zero-divisor of the
`(s)`-adic completion of `S`. -/
theorem isSMulRegular_adicCompletion (S : Type*) [CommRing S] (s : S)
    (h : IsSMulRegular S s) :
    IsSMulRegular (AdicCompletion (Ideal.span {s}) S) s := by
  unfold IsSMulRegular Function.Injective
  intro x y hxy
  have hxy' : s • x = s • y := hxy
  have hz : s • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
  have key : x - y = 0 := by
    apply AdicCompletion.ext
    intro n
    have hs : s • (x - y).val (n + 1) = 0 := by
      have h1 := congrArg (fun z : AdicCompletion (Ideal.span {s}) S => z.val (n + 1)) hz
      rw [AdicCompletion.val_smul_apply] at h1
      simpa using h1
    rw [← (x - y).property (Nat.le_succ n)]
    exact factorPow_smul_eq_zero S s h n hs
  exact sub_eq_zero.mp key

theorem torsionFree (R : Type*) [CommRing R] (p : ℕ) (a : R)
    (hp : IsSMulRegular (Work.DSM1p.RootClosure R p a)
      (p : Work.DSM1p.RootClosure R p a)) :
    IsSMulRegular (Work.DSM1p.RootClosureCompletion R p a)
      (p : Work.DSM1p.RootClosureCompletion R p a) := by
  have hgen := isSMulRegular_adicCompletion (Work.DSM1p.RootClosure R p a)
    (p : Work.DSM1p.RootClosure R p a) hp
  have hsmul : ∀ x : Work.DSM1p.RootClosureCompletion R p a,
      (p : Work.DSM1p.RootClosureCompletion R p a) • x
        = (p : Work.DSM1p.RootClosure R p a) • x := by
    intro x
    rw [Algebra.smul_def]
    congr 1
  have hfun : (fun x : Work.DSM1p.RootClosureCompletion R p a =>
        (p : Work.DSM1p.RootClosureCompletion R p a) • x)
      = fun x : Work.DSM1p.RootClosureCompletion R p a =>
          (p : Work.DSM1p.RootClosure R p a) • x := funext hsmul
  rw [IsSMulRegular, hfun]
  exact hgen

end Work.DSM1p.Completion
