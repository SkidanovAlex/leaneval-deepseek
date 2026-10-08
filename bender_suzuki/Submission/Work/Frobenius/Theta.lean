import Mathlib
import Submission.Work.Frobenius.ClassFun
import Submission.Work.Frobenius.Irr.charPair_irr_eq_ite
import Submission.Work.Frobenius.Irr.isIrr_one
import Submission.Work.Frobenius.Induction.charPair_indFun_resFun
import Submission.Work.Frobenius.Induction.indFun_apply_of_mem_complement
import Submission.Work.Frobenius.Induction.isClassFun_indFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The character `θ*` of a Frobenius complement

For a subgroup `H ≤ G` and a function `θ : H → ℂ` on it, put
`θ* := indFun H (θ - θ 1 • 1_H) + θ 1 • 1_G`, the class function used in the proof of
Frobenius' theorem (Isaacs, *Character Theory of Finite Groups*, Theorem 7.2).

The main results of this module are `charPair_thetaStar_one` and `charPair_thetaStar_self`:
for `θ ∈ Irr H`, `θ ≠ 1`, the class function `θ*` is orthogonal to the trivial character and
has norm one, so that `vchar_norm_one` identifies it with an irreducible character of `G` as
soon as `IsVChar θ*` is known.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise

namespace Work.Frobenius

variable {G : Type*} [Group G] [Fintype G]

section LocalFintype

/-- Every subgroup of a finite group is finite; declared as a `local instance` so that the
subgroup-level sums appearing below resolve without extra assumptions. -/
local instance instFintypeSubgroupTheta (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- The class function `θ* = (θ - θ 1 · 1_H)^G + θ 1 · 1_G` attached to `θ : H → ℂ`. -/
noncomputable def thetaStar (H : Subgroup G) (θ : H → ℂ) : G → ℂ :=
  indFun H (θ - (θ 1) • (1 : H → ℂ)) + (θ 1) • (1 : G → ℂ)

/-- The trace pairing of the trivial character with itself is `1`. -/
@[simp]
theorem charPair_one_one : charPair (1 : G → ℂ) (1 : G → ℂ) = 1 := by
  rw [charPair_apply]
  rw [show (∑ x : G, (1 : G → ℂ) x * (1 : G → ℂ) x⁻¹) = (Fintype.card G : ℂ) by simp]
  rw [Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (by simp)

/-- `indFun` at the identity, for a function vanishing at `1`. -/
theorem indFun_apply_one (H : Subgroup G) (f : H → ℂ) (hf : f 1 = 0) : indFun H f 1 = 0 := by
  have hsum : (∑ x : G, (if hx : x * 1 * x⁻¹ ∈ H then f ⟨x * 1 * x⁻¹, hx⟩ else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x * 1 * x⁻¹ ∈ H
    · rw [dif_pos hx]
      have hx1 : (⟨x * 1 * x⁻¹, hx⟩ : H) = 1 := by ext; simp
      rw [hx1, hf]
    · rw [dif_neg hx]
  simp only [indFun]
  rw [hsum, mul_zero]

/-- The degree of `θ*` is the degree of `θ`. -/
theorem thetaStar_apply_one (H : Subgroup G) (θ : H → ℂ) : thetaStar H θ 1 = θ 1 := by
  have hf : (θ - (θ 1) • (1 : H → ℂ)) 1 = 0 := by simp [Pi.sub_apply, Pi.smul_apply]
  simp only [thetaStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
  rw [indFun_apply_one H _ hf]
  ring

theorem isClassFun_thetaStar {H : Subgroup G} (θ : H → ℂ) :
    IsClassFun (thetaStar H θ) :=
  (Induction.isClassFun_indFun (θ - (θ 1) • (1 : H → ℂ))).add
    (IsClassFun.smul (θ 1) (isClassFun_const (1 : ℂ)))

/-- `θ*` is orthogonal to the trivial character of `G`. -/
theorem charPair_thetaStar_one {H : Subgroup G} {θ : H → ℂ} (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    charPair (thetaStar H θ) (1 : G → ℂ) = 0 := by
  have hpairθ1 : charPair (G := H) θ (1 : H → ℂ) = 0 := by
    have h := Work.Frobenius.Irr.charPair_irr_eq_ite (G := H) hθ (Work.Frobenius.Irr.isIrr_one)
    rw [ite_eq_right hθ1] at h
    exact h
  have hres : charPair (G := H) (θ - (θ 1) • (1 : H → ℂ)) (1 : H → ℂ) = -θ 1 := by
    rw [charPair_sub_left, charPair_smul_left, hpairθ1, charPair_one_one]
    ring
  have hres1 : resFun H (1 : G → ℂ) = (1 : H → ℂ) := rfl
  have hA1 : charPair (indFun H (θ - (θ 1) • (1 : H → ℂ))) (1 : G → ℂ) = -θ 1 := by
    rw [Induction.charPair_indFun_resFun (φ := θ - (θ 1) • (1 : H → ℂ))
      (ψ := (1 : G → ℂ)) isClassFun_one, hres1]
    exact hres
  rw [thetaStar, charPair_add_left, charPair_smul_left, hA1, charPair_one_one]
  ring

/-- The restriction of `(θ - θ 1 · 1_H)^G` to `H` equals `θ - θ 1 · 1_H`. -/
theorem resFun_indFun_sub {H : Subgroup G} (hH : IsFrobeniusComplement H) {θ : H → ℂ}
    (hθ : IsClassFun θ) :
    resFun H (indFun H (θ - (θ 1) • (1 : H → ℂ))) = θ - (θ 1) • (1 : H → ℂ) := by
  have hcf : IsClassFun (θ - (θ 1) • (1 : H → ℂ)) :=
    hθ.sub (IsClassFun.smul (θ 1) (isClassFun_const (1 : ℂ)))
  funext h
  rcases eq_or_ne h 1 with h1 | hne
  · subst h1
    show indFun H (θ - (θ 1) • (1 : H → ℂ)) (1 : G) = (θ - (θ 1) • (1 : H → ℂ)) 1
    rw [indFun_apply_one H _ (by simp [Pi.sub_apply, Pi.smul_apply])]
    simp [Pi.sub_apply, Pi.smul_apply]
  · have hh : (h : G) ∈ H := h.2
    have hh1 : (h : G) ≠ 1 := fun hc => hne (Subtype.ext hc)
    rw [resFun, Induction.indFun_apply_of_mem_complement (f := θ - (θ 1) • (1 : H → ℂ)) hH hcf hh hh1]

/-- `θ*` has norm one. -/
theorem charPair_thetaStar_self {H : Subgroup G} (hH : IsFrobeniusComplement H) {θ : H → ℂ}
    (hθ : θ ∈ Irr H) (hθ1 : θ ≠ 1) :
    charPair (thetaStar H θ) (thetaStar H θ) = 1 := by
  have hcfF : IsClassFun (θ - (θ 1) • (1 : H → ℂ)) :=
    (irr_isClassFun hθ).sub (IsClassFun.smul (θ 1) (isClassFun_const (1 : ℂ)))
  have hclassA : IsClassFun (indFun H (θ - (θ 1) • (1 : H → ℂ))) :=
    Induction.isClassFun_indFun _
  have hpairθθ : charPair (G := H) θ θ = 1 := by
    have h := Work.Frobenius.Irr.charPair_irr_eq_ite (G := H) hθ hθ
    simpa using h
  have hpairθ1 : charPair (G := H) θ (1 : H → ℂ) = 0 := by
    have h := Work.Frobenius.Irr.charPair_irr_eq_ite (G := H) hθ (Work.Frobenius.Irr.isIrr_one)
    rw [ite_eq_right hθ1] at h
    exact h
  have hFF : charPair (G := H) (θ - (θ 1) • (1 : H → ℂ)) (θ - (θ 1) • (1 : H → ℂ))
      = 1 + (θ 1) ^ 2 := by
    rw [charPair_sub_smul_sub_smul (f₁ := θ) (f₂ := θ) (g₁ := (1 : H → ℂ))
        (g₂ := (1 : H → ℂ)) (c := θ 1) (d := θ 1),
      hpairθθ, hpairθ1, charPair_comm (G := H) (1 : H → ℂ) θ, hpairθ1, charPair_one_one]
    ring
  have hA1 : charPair (indFun H (θ - (θ 1) • (1 : H → ℂ))) (1 : G → ℂ) = -θ 1 := by
    rw [Induction.charPair_indFun_resFun (φ := θ - (θ 1) • (1 : H → ℂ))
      (ψ := (1 : G → ℂ)) isClassFun_one]
    rw [show resFun H (1 : G → ℂ) = (1 : H → ℂ) from rfl]
    rw [charPair_sub_left, charPair_smul_left, hpairθ1, charPair_one_one]
    ring
  have hAA : charPair (indFun H (θ - (θ 1) • (1 : H → ℂ)))
      (indFun H (θ - (θ 1) • (1 : H → ℂ))) = 1 + (θ 1) ^ 2 := by
    rw [Induction.charPair_indFun_resFun (φ := θ - (θ 1) • (1 : H → ℂ))
      (ψ := indFun H (θ - (θ 1) • (1 : H → ℂ))) hclassA,
      resFun_indFun_sub hH (irr_isClassFun hθ)]
    exact hFF
  rw [thetaStar,
    charPair_add_smul_add_smul (f₁ := indFun H (θ - (θ 1) • (1 : H → ℂ)))
      (f₂ := indFun H (θ - (θ 1) • (1 : H → ℂ))) (g₁ := (1 : G → ℂ)) (g₂ := (1 : G → ℂ))
      (c := θ 1) (d := θ 1),
    hAA, hA1, charPair_comm (1 : G → ℂ) (indFun H (θ - (θ 1) • (1 : H → ℂ))), hA1,
    charPair_one_one]
  ring

end LocalFintype

end Work.Frobenius
