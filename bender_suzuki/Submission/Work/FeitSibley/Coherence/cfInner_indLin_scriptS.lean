import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.CharQ.scriptS_vanish
import Submission.Work.Induction.indFun_TI_apply
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.Induction.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.cfInner_indLin_scriptS`

The inner product of two characters of `𝒮` induced to `G`:

`⟨Ind_H^G χ, Ind_H^G ψ⟩_G = δ_{χψ} + ((|G:H| - 1)/|H|) χ(1) ψ(1)` for `χ, ψ ∈ 𝒮`.

The computation is the standard restriction/induction computation in the Feit–Sibley
configuration (`Q ⊴ H = Q ⋊ D`, `N_G(Q) = H`, `Q` a T.I. subgroup, members of `𝒮` vanish off
`Q`).  By Frobenius reciprocity it is equivalent to `⟨χ, Res_H^G(Ind_H^G ψ)⟩_H`, and the
restriction is

`Res_H^G(Ind_H^G ψ)(x) = ψ(x) + (|G:H| - 1) ψ(1) [x = 1]`  for `x ∈ H`,

obtained from `Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall` applied to `ν = ψ - ψ(1)·δ`
(`δ` the indicator of `1 ∈ H`) together with the direct evaluation of `Ind_H^G δ`.
-/

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- The indicator of the identity of a subgroup: `δ y = if y = 1 then 1 else 0`. -/
private def deltaId (H : Subgroup G) : ↥H → ℂ := fun y => if y = 1 then 1 else 0

/-- The coercion of `1 : ↥H` to `G`. -/
private theorem coe_one_subgroup (H : Subgroup G) : ((1 : ↥H) : G) = 1 := rfl

private theorem deltaId_classFun (H : Subgroup G) : Work.CharCore.IsClassFun (deltaId H) := by
  intro a b
  simp only [deltaId]
  by_cases hb : b = 1
  · subst hb; simp
  · have hne : a * b * a⁻¹ ≠ 1 := by
      intro hc
      exact hb (by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = 1 := by rw [hc]; group)
    simp [hb, hne]

/-- `Ind_H^G` of the indicator of `1` is `|G:H|` at `1` and `0` elsewhere. -/
private theorem indFun_deltaId (H : Subgroup G) (x : G) :
    Work.Induction.indFun H (deltaId H) x = if x = 1 then (H.index : ℂ) else 0 := by
  by_cases hx : x = 1
  · subst hx
    rw [Work.Induction.indFun_apply_one]
    simp [deltaId]
  · rw [if_neg hx, Work.Induction.indFun_apply_def]
    have hzero : (∑ y : G, dite (y * x * y⁻¹ ∈ H)
        (fun hy => deltaId H ⟨y * x * y⁻¹, hy⟩) (fun _ => 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y * x * y⁻¹ ∈ H
      · rw [dite_eq_left hy]
        have hne : (⟨y * x * y⁻¹, hy⟩ : ↥H) ≠ 1 := by
          intro hc
          have h1 : y * x * y⁻¹ = 1 := congrArg (Subtype.val) hc
          exact hx (by
            calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
              _ = 1 := by rw [h1]; group)
        simp [deltaId, hne]
      · rw [dite_eq_right hy]
    rw [hzero, mul_zero]

/-- **Restriction of the induced character at `H`.**  For `ψ ∈ 𝒮` and `x ∈ H`,

`Ind_H^G ψ (x) = ψ(x) + (|G:H| - 1) ψ(1) [x = 1]`.

The proof writes `ψ = ν + ψ(1)·δ` with `ν = ψ - ψ(1)·δ` (a class function on `H` vanishing at
`1` and off `Q`); `Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall` gives `Res_H^G(Ind ν) = ν`,
and `Ind δ` is evaluated by `indFun_deltaId`. -/
private theorem indFun_scriptS_apply (h : Work.FeitSibley.FSData G)
    {ψ : ↥h.H → ℂ} (hψ : ψ ∈ Work.FeitSibley.scriptS h.H h.Q1) :
    ∀ x : ↥h.H, Work.Induction.indFun h.H ψ (x : G)
      = ψ x + (if x = 1 then ((h.H.index : ℂ) - 1) * ψ 1 else 0) := by
  have hψirr : ψ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hψ).1
  have hψclass : Work.CharCore.IsClassFun ψ := Work.CharCore.isClassFun_of_mem_Irr hψirr
  have hψv : ∀ y : ↥h.H, (y : G) ∉ h.Q → ψ y = 0 :=
    fun y hy => Work.FeitSibley.CharQ.scriptS_vanish h hψ hy
  set c : ℂ := ψ 1 with hc
  let ν : ↥h.H → ℂ := ψ - c • deltaId h.H
  have hνclass : Work.CharCore.IsClassFun ν := by
    simp only [ν]
    exact hψclass.sub ((deltaId_classFun h.H).smul c)
  have hν1 : ν 1 = 0 := by
    have hδ : deltaId h.H (1 : ↥h.H) = 1 := by simp [deltaId]
    simp only [ν, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hδ, mul_one]
    rw [hc]; ring
  have hν0 : ∀ y : ↥h.H, (y : G) ∉ h.Q → ν y = 0 := by
    intro y hy
    have hy1 : y ≠ 1 := fun hh => hy (hh ▸ h.Q.one_mem)
    have hδ : deltaId h.H y = 0 := by simp [deltaId, hy1]
    simp only [ν, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hδ, mul_zero, sub_zero]
    exact hψv y hy
  have hresν : Work.Induction.resFun h.H (Work.Induction.indFun h.H ν) = ν :=
    Work.ThmG.resFun_indFun_eq_of_vanishes_off_hall (H := h.H) (Q := h.Q) (D := h.D)
      h.Q_sup_D h.Q_inf_D h.coprime_D_Q h.Q_normal_in_H h.Q_TI ν hνclass hν1 hν0
  have hψ_eq : ψ = ν + c • deltaId h.H := by
    funext y
    simp only [ν, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : Work.Induction.indFun h.H ψ
      = Work.Induction.indFun h.H ν + c • Work.Induction.indFun h.H (deltaId h.H) := by
    rw [hψ_eq, Work.Induction.indFun_add, Work.Induction.indFun_smul]
  intro x
  have hxν : Work.Induction.indFun h.H ν (x : G) = ν x := by
    have hh := congrFun hresν x
    simpa only [Work.Induction.resFun_apply] using hh
  have hInd : Work.Induction.indFun h.H ψ (x : G)
      = ν x + c * (if (x : G) = 1 then (h.H.index : ℂ) else 0) := by
    rw [h1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hxν, indFun_deltaId]
  rw [hInd, hc]
  by_cases hx1 : x = 1
  · subst hx1
    rw [coe_one_subgroup h.H, if_pos rfl, if_pos rfl, hν1]
    ring
  · have hxG : (x : G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
    have hδ : deltaId h.H x = 0 := by simp [deltaId, hx1]
    rw [if_neg hxG, if_neg hx1]
    simp only [ν, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hδ, mul_zero, sub_zero, add_zero]

/-- The `star`-corrected pointwise form used in the summation. -/
private theorem chi_mul_star_indFun_eq (h : Work.FeitSibley.FSData G)
    {ψ : ↥h.H → ℂ} (hψ : ψ ∈ Work.FeitSibley.scriptS h.H h.Q1) (χ : ↥h.H → ℂ) (x : ↥h.H) :
    χ x * starRingEnd ℂ (Work.Induction.indFun h.H ψ (x : G))
      = χ x * starRingEnd ℂ (ψ x) +
        (if x = 1 then ((h.H.index : ℂ) - 1) * (χ 1 * ψ 1) else 0) := by
  have hψirr : ψ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hψ).1
  have hψ1real : starRingEnd ℂ (ψ 1) = ψ 1 := by
    rw [Work.CharCore.irrDeg_spec hψirr]; simp
  rw [indFun_scriptS_apply h hψ x]
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, if_pos rfl]
    simp only [map_add, map_mul, map_sub, map_one, map_natCast, hψ1real]
    ring
  · rw [if_neg hx, if_neg hx]
    simp

theorem cfInner_indLin_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {χ ψ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptS h.H h.Q1)
    (hψ : ψ ∈ Work.FeitSibley.scriptS h.H h.Q1) :
    Work.Coherence.cfInner (Work.FeitSibley.indLin h.H χ) (Work.FeitSibley.indLin h.H ψ)
      = (if χ = ψ then 1 else 0) +
        (((h.H.index : ℂ) - 1) / (Nat.card h.H : ℂ)) * (χ 1 * ψ 1) := by
  have hχirr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχ).1
  have hψirr : ψ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hψ).1
  have hpoint : ∀ x : ↥h.H, χ x * starRingEnd ℂ (Work.Induction.indFun h.H ψ (x : G))
      = χ x * starRingEnd ℂ (ψ x) +
        (if x = 1 then ((h.H.index : ℂ) - 1) * (χ 1 * ψ 1) else 0) :=
    fun x => chi_mul_star_indFun_eq h hψ χ x
  have hsum : (∑ x : ↥h.H, χ x * starRingEnd ℂ (Work.Induction.indFun h.H ψ (x : G)))
      = (∑ x : ↥h.H, χ x * starRingEnd ℂ (ψ x))
        + ((h.H.index : ℂ) - 1) * (χ 1 * ψ 1) := by
    rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ (1 : ↥h.H)
      (fun _ => ((h.H.index : ℂ) - 1) * (χ 1 * ψ 1))]
    simp
  have hdiag : (∑ x : ↥h.H, χ x * starRingEnd ℂ (ψ x))
      = (Fintype.card ↥h.H : ℂ) * (if χ = ψ then 1 else 0) := by
    have h1 := Work.CharCore.irr_orthonormal χ ψ hχirr hψirr
    rw [Work.CharCore.cfInner_apply] at h1
    have hne : (Fintype.card ↥h.H : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
    have h2 := congrArg (fun z => (Fintype.card ↥h.H : ℂ) * z) h1
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at h2
    exact h2
  change Work.CharCore.cfInner (Work.Induction.indFun h.H χ) (Work.Induction.indFun h.H ψ)
      = (if χ = ψ then 1 else 0) +
        (((h.H.index : ℂ) - 1) / (Nat.card h.H : ℂ)) * (χ 1 * ψ 1)
  rw [Work.Induction.frobenius_reciprocity h.H χ (Work.Induction.indFun h.H ψ)
      (Work.Induction.isClassFun_indFun h.H ψ)]
  rw [Work.CharCore.cfInner_apply]
  simp only [Work.Induction.resFun_apply]
  rw [hsum, hdiag]
  have hcard : (Nat.card h.H : ℂ) = (Fintype.card ↥h.H : ℂ) := by
    rw [Nat.card_eq_fintype_card]
  have hne : (Fintype.card ↥h.H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  rw [hcard, div_eq_mul_inv]
  field_simp

end

end Work.FeitSibley.Coherence
