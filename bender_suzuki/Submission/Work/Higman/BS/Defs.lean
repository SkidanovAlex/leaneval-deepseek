/-
Copyright (c) 2024. All rights reserved.

# The quotient `P / Z(P)` of a Suzuki 2-group

Vocabulary for `Work.Higman.typeB_scalar`: an automorphism `ξ` of a finite group `P` induces an
automorphism `quotCenterAut ξ` of `P ⧸ Z(P)`, and the `ξ`-invariant layers of `P` correspond to
`quotCenterAut ξ`-invariant subgroups of `P ⧸ Z(P)` of order `|Z(P)|`.

Everything here is expressed for a finite group `P`; the Suzuki hypotheses enter only through the
lemma `quotCenterAut_pow_eq_one_iff`, which uses `|P| = |Z(P)| ^ 3` and the fixed-point-freeness
of the non-trivial powers of `ξ`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- Every automorphism of `P` maps the centre onto itself. -/
theorem map_center_eq (ξ : MulAut P) :
    (Subgroup.center P).map ξ.toMonoidHom = Subgroup.center P := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    have h : ξ (ξ.symm g * x) = ξ (x * ξ.symm g) := by
      rw [Subgroup.mem_center_iff.mp hx (ξ.symm g)]
    simpa using h
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨ξ.symm y, ?_, by simp⟩
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    have h : ξ.symm (ξ g * y) = ξ.symm (y * ξ g) := by
      rw [Subgroup.mem_center_iff.mp hy (ξ g)]
    simpa using h

/-- The automorphism of `P ⧸ Z(P)` induced by an automorphism `ξ` of `P`. -/
noncomputable def quotCenterAut (ξ : MulAut P) : MulAut (P ⧸ Subgroup.center P) :=
  QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) (ξ : P ≃* P) (map_center_eq ξ)

theorem quotCenterAut_mk (ξ : MulAut P) (x : P) :
    quotCenterAut ξ (QuotientGroup.mk' (Subgroup.center P) x) =
      QuotientGroup.mk' (Subgroup.center P) (ξ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem quotCenterAut_pow_mk (ξ : MulAut P) (k : ℕ) :
    ∀ x : P, ((quotCenterAut ξ) ^ k) (QuotientGroup.mk' (Subgroup.center P) x) =
      QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, quotCenterAut_mk, ih, pow_succ, MulAut.mul_apply]

/-- The canonical projection `P → P ⧸ Z(P)`. -/
abbrev centerProj : P →* P ⧸ Subgroup.center P := QuotientGroup.mk' (Subgroup.center P)

theorem centerProj_surjective : Function.Surjective (centerProj (P := P)) :=
  QuotientGroup.mk'_surjective _

/-- **`⟨ξ⟩` acts faithfully on `P ⧸ Z(P)`.**  If `ξ ^ k` acts trivially on `P ⧸ Z(P)`, then
`ξ ^ k = 1`: otherwise `x ↦ x⁻¹ · ξ ^ k x` would be an injective homomorphism `P → Z(P)`,
contradicting `|P| = |Z(P)| ^ 3` and `|P| > 1`. -/
theorem quotCenterAut_pow_eq_one_iff {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : FpfXi ξ) (k : ℕ) :
    (quotCenterAut ξ) ^ k = 1 ↔ ξ ^ k = 1 := by
  refine ⟨fun hσ => ?_, fun hk => ?_⟩
  · by_contra hk
    have hkey : ∀ x : P, QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x) =
        QuotientGroup.mk' (Subgroup.center P) x := by
      intro x
      have h2 := quotCenterAut_pow_mk ξ k x
      rw [hσ] at h2
      simpa using h2.symm
    have hmem : ∀ x : P, x⁻¹ * (ξ ^ k) x ∈ Subgroup.center P := by
      intro x
      have h1 : ((ξ ^ k) x)⁻¹ * x ∈ Subgroup.center P := by
        have := hkey x
        exact QuotientGroup.eq.mp this
      simpa using (Subgroup.center P).inv_mem h1
    let f : P →* ↥(Subgroup.center P) :=
      { toFun := fun x => ⟨x⁻¹ * (ξ ^ k) x, hmem x⟩
        map_one' := by simp
        map_mul' := fun x y => by
          refine Subtype.ext ?_
          have hc : x⁻¹ * (ξ ^ k) x ∈ Subgroup.center P := hmem x
          rw [Subgroup.mem_center_iff] at hc
          show (x * y)⁻¹ * (ξ ^ k) (x * y) =
            (x⁻¹ * (ξ ^ k) x) * (y⁻¹ * (ξ ^ k) y)
          rw [map_mul, mul_inv_rev]
          calc y⁻¹ * x⁻¹ * ((ξ ^ k) x * (ξ ^ k) y)
              = y⁻¹ * (x⁻¹ * (ξ ^ k) x) * (ξ ^ k) y := by group
            _ = (x⁻¹ * (ξ ^ k) x) * (y⁻¹ * (ξ ^ k) y) := by
                rw [hc y⁻¹]; group }
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      simp only [MonoidHom.mem_ker] at hx
      have h1 : x⁻¹ * (ξ ^ k) x = 1 := by
        have h3 : ((f x : ↥(Subgroup.center P)) : P) = 1 := by
          rw [hx]; rfl
        simpa [f] using h3
      have h2 : (ξ ^ k) x = x := by
        have h4 := congrArg (fun t => x * t) h1
        simpa [mul_assoc] using h4
      exact hξ.fpf k hk x h2
    have hle : Nat.card P ≤ Nat.card ↥(Subgroup.center P) :=
      Nat.card_le_card_of_injective f hinj
    have hq : Nat.card ↥(Subgroup.center P) = 1 := by
      set q := Nat.card ↥(Subgroup.center P) with hqdef
      have hc : Nat.card P = q ^ 3 := by rw [hqdef]; exact hξ.card_cube
      have h3 : q ^ 3 ≤ q := by rw [← hc]; exact hle
      have hpos : 0 < q := by rw [hqdef]; exact Nat.card_pos
      have h3' : q * (q * q) ≤ q * 1 := by
        rw [mul_one]
        calc q * (q * q) = q ^ 3 := by ring
          _ ≤ q := h3
      have h4 : q * q ≤ 1 := Nat.le_of_mul_le_mul_left h3' hpos
      have h5 : q ≤ 1 := by nlinarith [h4, hpos]
      omega
    haveI : Subsingleton P := by
      have hcardP : Nat.card P = 1 := by rw [hξ.card_cube, hq]; norm_num
      exact (Nat.card_eq_one_iff_unique.mp hcardP).1
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (by rw [Subsingleton.elim x y])
  · ext v
    obtain ⟨x, rfl⟩ := centerProj_surjective v
    rw [quotCenterAut_pow_mk, hk]
    rfl

end Work.Higman
