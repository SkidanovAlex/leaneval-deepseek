import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `derH w` and `derH w'` commute

`derH w` is the multidegree-preserving invariant derivation
`w₀ X₀₀ ∂_{X₀₁} + ∑ᵢ wᵢ X_{i1} ∂_{X_{i1}}` of the homogeneous coordinate ring
`MR N = ℂ[X_{i0}, X_{i1} : i < N+1]`.  This file proves that any two such derivations
commute, i.e. `derH w (derH w' F) = derH w' (derH w F)` for every `F`.

The argument is the standard one for derivations with constant coefficient data.  Package
`derH w` as a genuine `Derivation ℂ (MR N) (MR N)`, namely the `ℂ`-sum of the derivations
`(C (w j) * X (mulV j)) • ∂_{(j,1)}` (`mulV j` is `X_{00}` for `j = 0`, i.e. the direction
of the `G_a`-factor, and `X_{j1}` otherwise).  The commutator `⁅derH w, derH w'⁆` is then a
derivation again, and since derivations of a polynomial ring are determined by their values
on the generators `X u`, it suffices to check the claim on `X u`.  There the explicit value
`derH v (X u) = if u.2 = 1 then C (v u.1) * X (mulV u.1) else 0` reduces everything to a
one-line commutative-algebra identity.
-/

namespace Work.BW

open MvPolynomial (C X pderiv)

/-- The variable by which `derH v` multiplies in the direction `(j, 1)`: `X_{00}` for
`j = 0` (a translation along the `G_a` factor) and `X_{j1}` otherwise. -/
private def mulV {N : ℕ} (j : Fin (N + 1)) : Fin (N + 1) × Fin 2 :=
  if j = 0 then (0, 0) else (j, 1)

/-- `derH v` written as a single sum over `Fin (N + 1)`. -/
private lemma derH_eq_sum {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derH v F = ∑ j : Fin (N + 1), C (v j) * X (mulV j) * pderiv (j, 1) F := by
  rw [derH, Fin.sum_univ_succ]
  simp only [mulV, ite_true, Fin.succ_ne_zero]
  simp

/-- Value of `derH v` on a coordinate variable. -/
private lemma derH_X {N : ℕ} (v : Fin (N + 1) → ℂ) (u : Fin (N + 1) × Fin 2) :
    derH v (X u) = if u.2 = 1 then C (v u.1) * X (mulV u.1) else 0 := by
  obtain ⟨j0, b⟩ := u
  rw [derH_eq_sum]
  simp only [MvPolynomial.pderiv_X]
  by_cases hb : b = 1
  · subst hb
    rw [Finset.sum_eq_single j0]
    · rw [Pi.single_eq_same]; simp
    · intro x _ hx
      rw [Pi.single_eq_of_ne (by intro h; exact hx (Prod.ext_iff.mp h).1.symm)]; simp
    · intro h; exact absurd (Finset.mem_univ j0) h
  · rw [Finset.sum_eq_zero]
    · simp [hb]
    · intro x _
      rw [Pi.single_eq_of_ne (by intro h; exact hb (congrArg Prod.snd h))]; simp

/-- Value of `derH v` on the multiplier variable `X (mulV j)`. -/
private lemma derH_X_mulV {N : ℕ} (v : Fin (N + 1) → ℂ) (j : Fin (N + 1)) :
    derH v (X (mulV j)) = if j = 0 then 0 else C (v j) * X (mulV j) := by
  rw [derH_X]
  by_cases hj : j = 0
  · subst hj; simp [mulV]
  · simp [mulV, hj]

private lemma derH_zero {N : ℕ} (v : Fin (N + 1) → ℂ) : derH v 0 = 0 := by simp [derH]

private lemma derH_C_mul {N : ℕ} (v : Fin (N + 1) → ℂ) (c : ℂ) (F : MR N) :
    derH v (C c * F) = C c * derH v F := by
  simp only [derH, MvPolynomial.pderiv_C_mul]
  rw [mul_add, Finset.mul_sum]
  ring_nf

/-- `derH v` as a genuine derivation. -/
private noncomputable def derHd {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Derivation ℂ (MR N) (MR N) :=
  ∑ j : Fin (N + 1), (C (v j) * X (mulV j)) • pderiv (j, 1)

private lemma sum_deriv_apply {N : ℕ} (s : Finset (Fin (N + 1)))
    (D : Fin (N + 1) → Derivation ℂ (MR N) (MR N)) (F : MR N) :
    (∑ i ∈ s, D i) F = ∑ i ∈ s, D i F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

private lemma derHd_apply {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derHd v F = derH v F := by
  rw [derH_eq_sum, derHd, sum_deriv_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Derivation.smul_apply, smul_eq_mul]

/-- Any two of the invariant derivations `derH w`, `derH w'` commute. -/
lemma derH_comm {N : ℕ} (w w' : Fin (N + 1) → ℂ) (F : MR N) :
    derH w (derH w' F) = derH w' (derH w F) := by
  have h : ⁅derHd w, derHd w'⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro u
    simp only [Derivation.commutator_apply, derHd_apply, Derivation.zero_apply]
    by_cases h2 : u.2 = 1
    · by_cases h1 : u.1 = 0
      · rw [derH_X w' u, derH_X w u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_left h1, ite_eq_left h1]
        simp
      · rw [derH_X w' u, derH_X w u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_right h1, ite_eq_right h1]
        ring
    · rw [derH_X w' u, derH_X w u, ite_eq_right h2, ite_eq_right h2, derH_zero, derH_zero]
      ring
  have h2 : derH w (derH w' F) - derH w' (derH w F) = 0 := by
    have hh := Derivation.commutator_apply (D1 := derHd w) (D2 := derHd w') F
    rw [h, Derivation.zero_apply, derHd_apply, derHd_apply, derHd_apply, derHd_apply] at hh
    exact hh.symm
  exact sub_eq_zero.mp h2

end Work.BW
