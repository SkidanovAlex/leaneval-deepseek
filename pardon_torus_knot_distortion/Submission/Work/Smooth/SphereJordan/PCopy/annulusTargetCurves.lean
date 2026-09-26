import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts

/-!
# The two target curves of the cut-and-paste: continuity, periodicity, injectivity

This module provides the elementary (but necessary) analysis of the two `4`-arc curves `pctgtUpB`,
`pctgtDnB` of `Submission/Work/Smooth/SphereJordan/pcannulusInjectionTwoCutsAlt.lean`:

* `pcperPt_mem`, `pcperPt_self`: the "one period" parameter `pcperPt` lands in `[0, 2π)` and is the
  identity there;
* `pctgtUpB_eq`, `pctgtDnB_eq`: both curves are the composition of the *unfolded* piecewise functions
  `pctgtUpBun`, `pctgtDnBun` (defined on the parameter `σ ∈ [0, 2π]` directly) with `pcperPt`;
* `continuous_tgtUpB`, `continuous_tgtDnB`: they are continuous — every junction of the four arcs is
  matched by the two endpoint equalities `hout₁`, `hout₂` (the outer endpoints are `±pccutDir`) and
  `hθ₁`, `hθ₂` (the inner endpoints are the curve points), so the jump of `pcperPt` is invisible;
* `periodic_tgtUpB`, `periodic_tgtDnB`: they are `2π`-periodic.
-/

namespace Work.SphereJordan

open Set Filter
open scoped Topology

variable {γ : Work.Smooth.Jordan.PlaneCurve}

theorem pctwo_pi_pos' : (0 : ℝ) < 2 * Real.pi := by positivity

theorem pcperPt_mem (τ : ℝ) : Work.Smooth.SphereJordan.pcperPt τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hpos := pctwo_pi_pos'
  rw [Work.Smooth.SphereJordan.pcperPt]
  refine ⟨?_, ?_⟩
  · have := (le_div_iff₀ hpos).mp (Int.floor_le (τ / (2 * Real.pi)))
    linarith
  · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (τ / (2 * Real.pi)))
    linarith

theorem pcperPt_self {τ : ℝ} (hτ : τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    Work.Smooth.SphereJordan.pcperPt τ = τ := by
  rw [show Work.Smooth.SphereJordan.pcperPt τ =
      τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
  have hpos := pctwo_pi_pos'
  have h0 : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · simpa using div_nonneg hτ.1 hpos.le
    · have h1 : τ / (2 * Real.pi) < 1 := by
        rw [div_lt_one hpos]; exact hτ.2
      simpa using h1
  rw [h0]
  norm_num

/-- The **unfolded** upper target curve: the same piecewise definition as `pctgtUpB`, read on the
parameter `σ ∈ [0, 2π]` itself (no reduction mod `2π`). -/
noncomputable def pctgtUpBun (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (σ : ℝ) : ℂ :=
  if σ ≤ Real.pi / 2 then Work.Smooth.SphereJordan.pcsrcOuterUp S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then
    Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂))
     else γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi)))
  else Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-- The **unfolded** lower target curve. -/
noncomputable def pctgtDnBun (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (σ : ℝ) : ℂ :=
  if σ ≤ Real.pi / 2 then Work.Smooth.SphereJordan.pcsrcOuterDn S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then
    Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₁ - 2 * Real.pi + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
     else γ.γ (θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁)))
  else Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

theorem pctgtUpB_eq (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) :
    Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ =
      pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt τ) := rfl

theorem pctgtDnB_eq (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) :
    Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ =
      pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt τ) := rfl

/-! ## Continuity of the four branch functions -/

theorem pccontinuous_srcOuterUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Continuous (Work.Smooth.SphereJordan.pcsrcOuterUp S) := by
  have h : (Work.Smooth.SphereJordan.pcsrcOuterUp S) =
      fun x : ℝ => Work.Smooth.SphereJordan.pccutDir S *
        Complex.exp ((((Real.pi * x : ℝ)) : ℂ) * Complex.I) := rfl
  rw [h]; fun_prop

theorem pccontinuous_srcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Continuous (Work.Smooth.SphereJordan.pcsrcOuterDn S) := by
  have h : (Work.Smooth.SphereJordan.pcsrcOuterDn S) =
      fun x : ℝ => -(Work.Smooth.SphereJordan.pccutDir S) *
        Complex.exp ((((Real.pi * x : ℝ)) : ℂ) * Complex.I) := rfl
  rw [h]; fun_prop

theorem pccontinuous_tgtCut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) :
    Continuous (Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁) := by
  have h : (Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁) =
      fun x : ℝ => (Work.Smooth.SphereJordan.pcbase S : ℂ) +
        ((s₁ + x * (t₁ - s₁) : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := rfl
  rw [h]; fun_prop

theorem pccontinuous_tgtCut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) :
    Continuous (Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂) := by
  have h : (Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂) =
      fun x : ℝ => (Work.Smooth.SphereJordan.pcbase S : ℂ) -
        ((s₂ + x * (t₂ - s₂) : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := rfl
  rw [h]; fun_prop

theorem pcexp_pi_I : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I

theorem pcsrcOuterUp_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.pcsrcOuterUp S 1 = -Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pcsrcOuterUp
  rw [show Real.pi * 1 = Real.pi from by ring, pcexp_pi_I]
  ring

theorem pcsrcOuterUp_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.pcsrcOuterUp S 0 = Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pcsrcOuterUp
  simp

theorem pcsrcOuterDn_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.pcsrcOuterDn S 1 = Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pcsrcOuterDn
  rw [show Real.pi * 1 = Real.pi from by ring, pcexp_pi_I]
  ring

theorem pcsrcOuterDn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.pcsrcOuterDn S 0 = -Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pcsrcOuterDn
  simp

theorem pctgtCut₁_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ 1 =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pctgtCut₁
  norm_num

theorem pctgtCut₁_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ 0 =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pctgtCut₁
  norm_num

theorem pctgtCut₂_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ 1 =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pctgtCut₂
  norm_num

theorem pctgtCut₂_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ 0 =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold Work.Smooth.SphereJordan.pctgtCut₂
  norm_num

/-! ## Continuity of the unfolded curves on one period -/

theorem pcIcc_union_Icc_eq_Icc' {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Set.Icc a b ∪ Set.Icc b c = Set.Icc a c :=
  Set.Icc_union_Icc_eq_Icc h₁ h₂

theorem pccontinuousOn_tgtUpBun (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    ContinuousOn (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := by
  have hA : Continuous (fun σ : ℝ => Work.Smooth.SphereJordan.pcsrcOuterUp S (σ / (Real.pi / 2))) :=
    (pccontinuous_srcOuterUp S).comp (by fun_prop)
  have hB : Continuous (fun σ : ℝ =>
      Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_tgtCut₂ S t₂ s₂).comp (by fun_prop)
  have hD : Continuous (fun σ : ℝ =>
      Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_tgtCut₁ S t₁ s₁).comp (by fun_prop)
  have hCc : Continuous (fun σ : ℝ =>
      (if b then γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂))
       else γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi)))) := by
    cases b <;> exact γ.cont.comp (by fun_prop)
  have h1 : ContinuousOn (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc 0 (Real.pi / 2)) :=
    (hA.continuousOn).congr fun σ hσ => by
      simp only [pctgtUpBun]; rw [if_pos hσ.2]
  have h2 : ContinuousOn (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (Real.pi / 2) Real.pi) :=
    (hB.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
        subst hσeq
        have hL : Work.Smooth.SphereJordan.pcsrcOuterUp S (Real.pi / 2 / (Real.pi / 2)) =
            -Work.Smooth.SphereJordan.pccutDir S := by
          rw [div_self (by positivity : Real.pi / 2 ≠ 0), pcsrcOuterUp_one]
        have hR : Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂
            ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
            -Work.Smooth.SphereJordan.pccutDir S := by
          rw [sub_self, zero_div, pctgtCut₂_zero, hout₂]
        simp only [pctgtUpBun]
        rw [if_pos le_rfl, hL, hR]
      · simp only [pctgtUpBun]
        rw [if_neg hσa, if_pos hσ.2]
  have h3 : ContinuousOn (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc Real.pi (3 * Real.pi / 2)) :=
    (hCc.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
        linarith [Real.pi_pos]
      · by_cases hσb : σ ≤ Real.pi
        · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
          subst hσeq
          have hR : Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂
              ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
              (Work.Smooth.SphereJordan.pcbase S : ℂ) -
                (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
            rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
              rw [div_eq_one_iff_eq (by positivity)]; ring, pctgtCut₂_one]
          have hb1 : θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂) = θ₂ := by ring
          have hb2 : θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi) = θ₂ := by
            ring
          simp only [pctgtUpBun]
          rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
            if_pos le_rfl, hR]
          simp only [hb1, hb2]
          by_cases hb : b = true
          · rw [if_pos hb]; exact hθ₂.symm
          · rw [if_neg hb]; exact hθ₂.symm
        · simp only [pctgtUpBun]
          rw [if_neg hσa, if_neg hσb, if_pos hσ.2]
  have h4 : ContinuousOn (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :=
    (hD.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : 3 * Real.pi / 2 ≤ Real.pi / 2 := le_trans hσ.1 hσa
        linarith [Real.pi_pos]
      · by_cases hσb : σ ≤ Real.pi
        · have : 3 * Real.pi / 2 ≤ Real.pi := le_trans hσ.1 hσb
          linarith [Real.pi_pos]
        · by_cases hσc : σ ≤ 3 * Real.pi / 2
          · have hσeq : σ = 3 * Real.pi / 2 := le_antisymm hσc hσ.1
            subst hσeq
            have hratio : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
              rw [div_eq_one_iff_eq (by positivity)]; ring
            have hDv : Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁
                (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) = γ.γ θ₁ := by
              rw [sub_self, zero_div, sub_zero, pctgtCut₁_one, hθ₁]
            simp only [pctgtUpBun]
            rw [if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi / 2)),
              if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi)),
              if_pos le_rfl, hDv, hratio]
            by_cases hb : b = true
            · rw [if_pos hb, show θ₂ + 1 * (θ₁ - θ₂) = θ₁ from by ring]
            · rw [if_neg hb, show θ₂ + 1 * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ - 2 * Real.pi from by ring]
              have hper := γ.apply_add_int_mul (θ₁ - 2 * Real.pi) 1
              rw [show θ₁ - 2 * Real.pi + (1:ℤ) * (2 * Real.pi) = θ₁ from by push_cast; ring] at hper
              exact hper.symm
          · simp only [pctgtUpBun]
            rw [if_neg hσa, if_neg hσb, if_neg hσc]
  have h12 := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rw [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)
    (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)] at h12
  have h34 := h3.union_of_isClosed h4 isClosed_Icc isClosed_Icc
  rw [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : Real.pi ≤ 3 * Real.pi / 2)
    (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi)] at h34
  have h1234 := h12.union_of_isClosed h34 isClosed_Icc isClosed_Icc
  rwa [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi)
    (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi)] at h1234

theorem pccontinuousOn_tgtDnBun (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    ContinuousOn (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := by
  have hA : Continuous (fun σ : ℝ => Work.Smooth.SphereJordan.pcsrcOuterDn S (σ / (Real.pi / 2))) :=
    (pccontinuous_srcOuterDn S).comp (by fun_prop)
  have hB : Continuous (fun σ : ℝ =>
      Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_tgtCut₁ S t₁ s₁).comp (by fun_prop)
  have hD : Continuous (fun σ : ℝ =>
      Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_tgtCut₂ S t₂ s₂).comp (by fun_prop)
  have hCc : Continuous (fun σ : ℝ =>
      (if b then γ.γ (θ₁ - 2 * Real.pi + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
       else γ.γ (θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁)))) := by
    cases b <;> exact γ.cont.comp (by fun_prop)
  have h1 : ContinuousOn (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc 0 (Real.pi / 2)) :=
    (hA.continuousOn).congr fun σ hσ => by
      simp only [pctgtDnBun]; rw [if_pos hσ.2]
  have h2 : ContinuousOn (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (Real.pi / 2) Real.pi) :=
    (hB.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
        subst hσeq
        have hL : Work.Smooth.SphereJordan.pcsrcOuterDn S (Real.pi / 2 / (Real.pi / 2)) =
            Work.Smooth.SphereJordan.pccutDir S := by
          rw [div_self (by positivity : Real.pi / 2 ≠ 0), pcsrcOuterDn_one]
        have hR : Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁
            ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
            Work.Smooth.SphereJordan.pccutDir S := by
          rw [sub_self, zero_div, pctgtCut₁_zero, hout₁]
        simp only [pctgtDnBun]
        rw [if_pos le_rfl, hL, hR]
      · simp only [pctgtDnBun]
        rw [if_neg hσa, if_pos hσ.2]
  have h3 : ContinuousOn (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc Real.pi (3 * Real.pi / 2)) :=
    (hCc.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
        linarith [Real.pi_pos]
      · by_cases hσb : σ ≤ Real.pi
        · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
          subst hσeq
          have hR : Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁
              ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
              (Work.Smooth.SphereJordan.pcbase S : ℂ) +
                (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
            rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
              rw [div_eq_one_iff_eq (by positivity)]; ring, pctgtCut₁_one]
          have hb1 : θ₁ - 2 * Real.pi + ((Real.pi - Real.pi) / (Real.pi / 2)) *
              (θ₂ - θ₁ + 2 * Real.pi) = θ₁ - 2 * Real.pi := by ring
          have hb2 : θ₁ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁) = θ₁ := by ring
          have hun1 : γ.γ (θ₁ - 2 * Real.pi) = γ.γ θ₁ := by
            have hper := γ.apply_add_int_mul (θ₁ - 2 * Real.pi) 1
            rw [show θ₁ - 2 * Real.pi + (1:ℤ) * (2 * Real.pi) = θ₁ from by push_cast; ring] at hper
            exact hper.symm
          simp only [pctgtDnBun]
          rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
            if_pos le_rfl, hR]
          by_cases hb : b = true
          · rw [if_pos hb, hb1, hun1]; exact hθ₁.symm
          · rw [if_neg hb, hb2]; exact hθ₁.symm
        · simp only [pctgtDnBun]
          rw [if_neg hσa, if_neg hσb, if_pos hσ.2]
  have h4 : ContinuousOn (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :=
    (hD.continuousOn).congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : 3 * Real.pi / 2 ≤ Real.pi / 2 := le_trans hσ.1 hσa
        linarith [Real.pi_pos]
      · by_cases hσb : σ ≤ Real.pi
        · have : 3 * Real.pi / 2 ≤ Real.pi := le_trans hσ.1 hσb
          linarith [Real.pi_pos]
        · by_cases hσc : σ ≤ 3 * Real.pi / 2
          · have hσeq : σ = 3 * Real.pi / 2 := le_antisymm hσc hσ.1
            subst hσeq
            have hratio : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
              rw [div_eq_one_iff_eq (by positivity)]; ring
            have hDv : Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂
                (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) =
                (Work.Smooth.SphereJordan.pcbase S : ℂ) -
                  (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
              rw [sub_self, zero_div, sub_zero, pctgtCut₂_one]
            simp only [pctgtDnBun]
            rw [if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi / 2)),
              if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi)),
              if_pos le_rfl, hDv, hratio]
            by_cases hb : b = true
            · rw [if_pos hb, show θ₁ - 2 * Real.pi + 1 * (θ₂ - θ₁ + 2 * Real.pi) = θ₂ from by ring,
                hθ₂]
            · rw [if_neg hb, show θ₁ + 1 * (θ₂ - θ₁) = θ₂ from by ring, hθ₂]
          · simp only [pctgtDnBun]
            rw [if_neg hσa, if_neg hσb, if_neg hσc]
  have h12 := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rw [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)
    (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)] at h12
  have h34 := h3.union_of_isClosed h4 isClosed_Icc isClosed_Icc
  rw [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : Real.pi ≤ 3 * Real.pi / 2)
    (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi)] at h34
  have h1234 := h12.union_of_isClosed h34 isClosed_Icc isClosed_Icc
  rwa [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi)
    (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi)] at h1234

/-! ## The two target curves are continuous and periodic -/

theorem pccontinuous_periodic_tgtUpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Continuous (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∧
      Function.Periodic (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
        (2 * Real.pi) := by
  have hG := pccontinuousOn_tgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₂ hθ₁ hθ₂
  have hG0 : pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ 0 =
      pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) := by
    have h1 : pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ 0 =
        Work.Smooth.SphereJordan.pccutDir S := by
      simp only [pctgtUpBun]
      rw [if_pos (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2), zero_div,
        pcsrcOuterUp_zero]
    have h2 : pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
        Work.Smooth.SphereJordan.pccutDir S := by
      simp only [pctgtUpBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ 3 * Real.pi / 2))]
      rw [show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [div_eq_one_iff_eq (by positivity)]; ring]
      rw [show (1 : ℝ) - 1 = 0 from by norm_num, pctgtCut₁_zero, hout₁]
    rw [h1, h2]
  have hper : Function.Periodic (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (2 * Real.pi) := by
    intro σ
    rw [pctgtUpB_eq, pctgtUpB_eq, Work.Smooth.SphereJordan.pcperPt_shift]
  have hEq : Set.EqOn (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (pctgtUpBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := by
    intro σ hσ
    rw [pctgtUpB_eq]
    by_cases h : σ = 2 * Real.pi
    · subst h
      have hper0 : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
        rw [show Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) =
          2 * Real.pi - (⌊2 * Real.pi / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
        rw [div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0),
          show ⌊(1 : ℝ)⌋ = 1 from Int.floor_one]
        norm_num
      rw [hper0]; exact hG0
    · rw [pcperPt_self ⟨hσ.1, lt_of_le_of_ne hσ.2 h⟩]
  have hcont : ContinuousOn (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc 0 (2 * Real.pi)) := hG.congr hEq
  have hcont' : ContinuousOn (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (-(2 * Real.pi)) (2 * Real.pi)) := by
    have hleft : ContinuousOn (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
        (Set.Icc (-(2 * Real.pi)) 0) := by
      have hshift : ContinuousOn
          (fun y : ℝ => Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (y + 2 * Real.pi))
          (Set.Icc (-(2 * Real.pi)) 0) :=
        ContinuousOn.comp hcont ((continuous_id.add continuous_const).continuousOn)
          (fun y hy => by
            rw [Set.mem_Icc] at hy ⊢
            exact ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩)
      rwa [show (fun y : ℝ =>
          Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (y + 2 * Real.pi)) =
          (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) from
        funext fun y => hper y] at hshift
    have hjoin := hleft.union_of_isClosed hcont isClosed_Icc isClosed_Icc
    rwa [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (-(2 * Real.pi) : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)] at hjoin
  refine ⟨?_, hper⟩
  rw [continuous_iff_continuousAt]
  intro τ
  have hmem := pcperPt_mem τ
  have hc : ContinuousAt (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Work.Smooth.SphereJordan.pcperPt τ) := by
    rcases eq_or_ne (Work.Smooth.SphereJordan.pcperPt τ) 0 with h0 | h0
    · have hnb : Set.Icc (-(2 * Real.pi)) (2 * Real.pi) ∈
          nhds (Work.Smooth.SphereJordan.pcperPt τ) := by
        rw [h0]
        exact Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds (by constructor <;> linarith [Real.pi_pos]))
          Set.Ioo_subset_Icc_self
      exact (hcont'.continuousWithinAt
        ⟨by linarith [hmem.1, Real.pi_pos], hmem.2.le⟩).continuousAt hnb
    · have hpos : 0 < Work.Smooth.SphereJordan.pcperPt τ :=
        lt_of_le_of_ne hmem.1 (Ne.symm h0)
      have hnb : Set.Icc 0 (2 * Real.pi) ∈ nhds (Work.Smooth.SphereJordan.pcperPt τ) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hpos, hmem.2⟩) Set.Ioo_subset_Icc_self
      exact (hcont.continuousWithinAt ⟨hmem.1, hmem.2.le⟩).continuousAt hnb
  have hdecomp : τ = Work.Smooth.SphereJordan.pcperPt τ +
      (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
    rw [show Work.Smooth.SphereJordan.pcperPt τ =
      τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
    ring
  rw [hdecomp]
  have hX : Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
      ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi) = Work.Smooth.SphereJordan.pcperPt τ := by
    push_cast; ring
  have heq : (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) =
      ((Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∘
        (fun z : ℝ => z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))) :=
    funext fun z => (hper.int_mul (-(⌊τ / (2 * Real.pi)⌋)) z).symm
  rw [heq]
  refine ContinuousAt.comp (f := fun z : ℝ => z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    (x := Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) ?_ ?_
  · change ContinuousAt (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
        ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    rw [hX]
    exact hc
  · fun_prop

theorem pccontinuous_periodic_tgtDnB (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Continuous (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∧
      Function.Periodic (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
        (2 * Real.pi) := by
  have hG := pccontinuousOn_tgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
  have hG0 : pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ 0 =
      pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) := by
    have h1 : pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ 0 =
        -Work.Smooth.SphereJordan.pccutDir S := by
      simp only [pctgtDnBun]
      rw [if_pos (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2), zero_div,
        pcsrcOuterDn_zero]
    have h2 : pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi) =
        -Work.Smooth.SphereJordan.pccutDir S := by
      simp only [pctgtDnBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ 3 * Real.pi / 2))]
      rw [show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [div_eq_one_iff_eq (by positivity)]; ring]
      rw [show (1 : ℝ) - 1 = 0 from by norm_num, pctgtCut₂_zero, hout₂]
    rw [h1, h2]
  have hper : Function.Periodic (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (2 * Real.pi) := by
    intro σ
    rw [pctgtDnB_eq, pctgtDnB_eq, Work.Smooth.SphereJordan.pcperPt_shift]
  have hEq : Set.EqOn (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (pctgtDnBun (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := by
    intro σ hσ
    rw [pctgtDnB_eq]
    by_cases h : σ = 2 * Real.pi
    · subst h
      have hper0 : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
        rw [show Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) =
          2 * Real.pi - (⌊2 * Real.pi / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
        rw [div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0),
          show ⌊(1 : ℝ)⌋ = 1 from Int.floor_one]
        norm_num
      rw [hper0]; exact hG0
    · rw [pcperPt_self ⟨hσ.1, lt_of_le_of_ne hσ.2 h⟩]
  have hcont : ContinuousOn (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc 0 (2 * Real.pi)) := hG.congr hEq
  have hcont' : ContinuousOn (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Set.Icc (-(2 * Real.pi)) (2 * Real.pi)) := by
    have hleft : ContinuousOn (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
        (Set.Icc (-(2 * Real.pi)) 0) := by
      have hshift : ContinuousOn
          (fun y : ℝ => Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (y + 2 * Real.pi))
          (Set.Icc (-(2 * Real.pi)) 0) :=
        ContinuousOn.comp hcont ((continuous_id.add continuous_const).continuousOn)
          (fun y hy => by
            rw [Set.mem_Icc] at hy ⊢
            exact ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩)
      rwa [show (fun y : ℝ =>
          Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (y + 2 * Real.pi)) =
          (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) from
        funext fun y => hper y] at hshift
    have hjoin := hleft.union_of_isClosed hcont isClosed_Icc isClosed_Icc
    rwa [pcIcc_union_Icc_eq_Icc' (by linarith [Real.pi_pos] : (-(2 * Real.pi) : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)] at hjoin
  refine ⟨?_, hper⟩
  rw [continuous_iff_continuousAt]
  intro τ
  have hmem := pcperPt_mem τ
  have hc : ContinuousAt (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Work.Smooth.SphereJordan.pcperPt τ) := by
    rcases eq_or_ne (Work.Smooth.SphereJordan.pcperPt τ) 0 with h0 | h0
    · have hnb : Set.Icc (-(2 * Real.pi)) (2 * Real.pi) ∈
          nhds (Work.Smooth.SphereJordan.pcperPt τ) := by
        rw [h0]
        exact Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds (by constructor <;> linarith [Real.pi_pos]))
          Set.Ioo_subset_Icc_self
      exact (hcont'.continuousWithinAt
        ⟨by linarith [hmem.1, Real.pi_pos], hmem.2.le⟩).continuousAt hnb
    · have hpos : 0 < Work.Smooth.SphereJordan.pcperPt τ :=
        lt_of_le_of_ne hmem.1 (Ne.symm h0)
      have hnb : Set.Icc 0 (2 * Real.pi) ∈ nhds (Work.Smooth.SphereJordan.pcperPt τ) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hpos, hmem.2⟩) Set.Ioo_subset_Icc_self
      exact (hcont.continuousWithinAt ⟨hmem.1, hmem.2.le⟩).continuousAt hnb
  have hdecomp : τ = Work.Smooth.SphereJordan.pcperPt τ +
      (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
    rw [show Work.Smooth.SphereJordan.pcperPt τ =
      τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
    ring
  rw [hdecomp]
  have hX : Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
      ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi) = Work.Smooth.SphereJordan.pcperPt τ := by
    push_cast; ring
  have heq : (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) =
      ((Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∘
        (fun z : ℝ => z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))) :=
    funext fun z => (hper.int_mul (-(⌊τ / (2 * Real.pi)⌋)) z).symm
  rw [heq]
  refine ContinuousAt.comp (f := fun z : ℝ => z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    (x := Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) ?_ ?_
  · change ContinuousAt (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂)
      (Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
        ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    rw [hX]
    exact hc
  · fun_prop

/-- `Work.SphereJordan.pctgtCurves_continuous_periodic`. -/
theorem pctgtCurves_continuous_periodic (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (t₁ s₁ t₂ s₂ : ℝ) (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Continuous (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∧
      Function.Periodic (Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂) (2 * Real.pi) ∧
      Continuous (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) ∧
      Function.Periodic (Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) (2 * Real.pi) := by
  obtain ⟨h1, h2⟩ := pccontinuous_periodic_tgtUpB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
  obtain ⟨h3, h4⟩ := pccontinuous_periodic_tgtDnB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂
  exact ⟨h1, h2, h3, h4⟩

/-! ## Injectivity of a simple curve on intervals shorter than a period -/

/-- A simple `2π`-periodic plane curve is injective on any interval of length at most `2π` whose
endpoints are not separated by a full period: if `|a - b| < 2π` then `γ a = γ b` forces `a = b`. -/
theorem pcinjOn_of_abs_lt {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) {a b : ℝ}
    (hab : |a - b| < 2 * Real.pi) : γ.γ a = γ.γ b → a = b := by
  intro h
  have hpos : (0 : ℝ) < 2 * Real.pi := pctwo_pi_pos'
  set a' : ℝ := a - (⌊a / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) with ha'
  set b' : ℝ := b - (⌊b / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) with hb'
  have ha'mem : a' ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    refine ⟨?_, ?_⟩
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (a / (2 * Real.pi)))
      simp only [ha']; linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (a / (2 * Real.pi)))
      simp only [ha']; linarith
  have hb'mem : b' ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    refine ⟨?_, ?_⟩
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (b / (2 * Real.pi)))
      simp only [hb']; linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (b / (2 * Real.pi)))
      simp only [hb']; linarith
  have hγa : γ.γ a' = γ.γ a := by
    have hper := γ.apply_add_int_mul a' ⌊a / (2 * Real.pi)⌋
    rw [show a' + (⌊a / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = a from by
      simp only [ha']; ring] at hper
    exact hper.symm
  have hγb : γ.γ b' = γ.γ b := by
    have hper := γ.apply_add_int_mul b' ⌊b / (2 * Real.pi)⌋
    rw [show b' + (⌊b / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = b from by
      simp only [hb']; ring] at hper
    exact hper.symm
  have hab' : a' = b' := hs ha'mem hb'mem (by rw [hγa, hγb, h])
  have hd : a - b = (((⌊a / (2 * Real.pi)⌋ - ⌊b / (2 * Real.pi)⌋ : ℤ)) : ℝ) * (2 * Real.pi) := by
    have h0 : a' = b' := hab'
    simp only [ha', hb'] at h0
    push_cast at h0 ⊢
    linarith
  by_contra hne
  have hk : ((⌊a / (2 * Real.pi)⌋ - ⌊b / (2 * Real.pi)⌋ : ℤ)) ≠ 0 := by
    intro hzero
    apply hne
    have := hd
    rw [hzero] at this
    push_cast at this
    linarith
  have hone : (1 : ℝ) ≤ |(((⌊a / (2 * Real.pi)⌋ - ⌊b / (2 * Real.pi)⌋ : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  have hbig : (2 * Real.pi : ℝ) ≤ |a - b| := by
    rw [hd, abs_mul, abs_of_pos hpos]
    nlinarith [hone]
  linarith

/-- A simple `2π`-periodic plane curve is injective on a closed parameter interval of length `< 2π`. -/
theorem pcinjOn_interval {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) {c d : ℝ}
    (hcd : d - c < 2 * Real.pi) : Set.InjOn γ.γ (Set.Icc c d) := by
  intro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩ hab
  refine pcinjOn_of_abs_lt hs ?_ hab
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ## The crosscut points in radial coordinates -/

end Work.SphereJordan
