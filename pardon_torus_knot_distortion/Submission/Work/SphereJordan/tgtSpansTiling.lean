import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.SpanSetup
import Submission.Work.SphereJordan.pairingSetup
import Submission.Work.SphereJordan.windIdentitiesProof
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.SphereJordan.gammaInjOnArc
import Submission.Work.SphereJordan.tgtCurvesTraceDiff
import Submission.Work.SphereJordan.annulusAux
import Submission.Work.SphereJordan.annulusTargetCurves
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint

/-!
# A self-contained copy of the two-cuts tiling

This module contains (renamed with the prefix `tgtT_`) copies of

* the twelve declarations of `Submission/Work/Smooth/SphereJordan/coreAuxTwoCuts.lean` on which the
  tiling depends (`norm_base_add*`, `norm_base_sub*`, `perPt_eq_self`, `tgtUpB_norm_le_one`,
  `tgtDnB_norm_le_one`, `upCurve_V_subset_annulus`, `dnCurve_V_subset_annulus`,
  `cuts_subset_trace_up`, `cuts_subset_trace_dn`, `cut_inter_sphere_subset`), together with
  `planeSeparation_V_subset_closedBall'` (from `radialTwoCutsPieces.lean`);
* the whole of `Submission/Work/SphereJordan/tilingOfPairing.lean`.

The reason for the copy: `coreAuxTwoCuts.lean` and `annulusSchoenfliesCore.lean` declare the same
names (`cuts_subset_trace_up`, `segPt`, `norm_base_add`, ...), so no module may import both, while
`annulusTargetSpans.lean` *is* imported by `annulusSchoenfliesCore.lean`.  Hence the tiling must be
available to `annulusTargetSpans` without importing `coreAuxTwoCuts`; copying the short part of
`coreAuxTwoCuts` used by the tiling achieves that.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

theorem tgtT_planeSeparation_V_subset_closedBall' {c : Work.Smooth.Jordan.PlaneCurve}
    (d : Work.Smooth.Jordan.PlaneSeparation c) (hc : c.trace ⊆ Metric.closedBall (0 : ℂ) 1) :
    d.V ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro x hxV
  by_contra hcon
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hcon
  have hx1 : 1 < ‖x‖ := not_le.mp hcon
  set R : Set ℂ := (fun s : ℝ => s • x) '' Set.Ici 1 with hR
  have hRpre : IsPreconnected R :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hxR : x ∈ R := ⟨1, Set.mem_Ici.mpr le_rfl, by simp⟩
  have hRsub : R ⊆ c.traceᶜ := by
    rintro y ⟨s, hs, rfl⟩ hy
    obtain ⟨θ, hθ⟩ := hy
    have hs1 : (1 : ℝ) ≤ s := Set.mem_Ici.mp hs
    have ht : ‖s • x‖ ≤ 1 := by
      have h1 := hc ⟨θ, hθ⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
      exact h1
    have hnorm : ‖s • x‖ = s * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1)]
    have hle : ‖x‖ ≤ ‖s • x‖ := by rw [hnorm]; nlinarith [norm_nonneg x]
    linarith
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset d hRpre hRsub with hU | hV
  · exact Set.disjoint_left.mp d.disjoint_UV (hU hxR) hxV
  · have hb := d.bounded_V.subset hV
    rw [isBounded_iff_forall_norm_le] at hb
    obtain ⟨C, hC⟩ := hb
    have hxn : 0 < ‖x‖ := lt_trans zero_lt_one hx1
    set s : ℝ := (C + 1) / ‖x‖ with hs
    have hs1 : (1 : ℝ) ≤ s := by
      rw [hs, le_div_iff₀ hxn]; linarith [hC x hxR]
    have hmem : s • x ∈ R := ⟨s, hs1, rfl⟩
    have hval : C + 1 ≤ C := by
      calc C + 1 = ‖s • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1), hs]
            field_simp
        _ ≤ C := hC _ hmem
    linarith

theorem tgtT_norm_base_add_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} (hc : 0 ≤ c) :
    base S + (c : ℂ) * cutDir S = ((‖base S‖ + c : ℝ) : ℂ) * cutDir S := by
  have hb : base S = ((‖base S‖ : ℝ) : ℂ) * cutDir S := base_eq_smul_cutDir S
  have h : ((‖base S‖ + c : ℝ) : ℂ) = ((‖base S‖ : ℝ) : ℂ) + ((c : ℝ) : ℂ) :=
    Complex.ofReal_add _ _
  rw [h, add_mul, ← hb]

theorem tgtT_norm_base_add (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} (hc : 0 ≤ c) :
    ‖base S + (c : ℂ) * cutDir S‖ = ‖base S‖ + c := by
  rw [tgtT_norm_base_add_smul S hc, norm_mul, norm_cutDir S, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hc)]

theorem tgtT_norm_base_sub_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} :
    base S - (c : ℂ) * cutDir S = ((‖base S‖ - c : ℝ) : ℂ) * cutDir S := by
  have hb : base S = ((‖base S‖ : ℝ) : ℂ) * cutDir S := base_eq_smul_cutDir S
  have h : ((‖base S‖ - c : ℝ) : ℂ) = ((‖base S‖ : ℝ) : ℂ) - ((c : ℝ) : ℂ) :=
    Complex.ofReal_sub _ _
  rw [h, sub_mul, ← hb]

theorem tgtT_norm_base_sub (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {c : ℝ} :
    ‖base S - (c : ℂ) * cutDir S‖ = |‖base S‖ - c| := by
  rw [tgtT_norm_base_sub_smul S, norm_mul, norm_cutDir S, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem tgtT_perPt_eq_self {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ < 2 * Real.pi) : perPt τ = τ := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hf : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h0 hpos.le, by rw [div_lt_one hpos]; exact h2⟩
  unfold perPt
  rw [hf]
  norm_num

theorem tgtT_tgtUpB_norm_le_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    ‖Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ‖ ≤ 1 := by
  have hpm := Work.SphereJordan.perPt_mem τ
  have hb : ‖(base S : ℂ)‖ < 1 := norm_base_lt_one S hball
  have hnorm₁ : ‖(base S : ℂ)‖ + s₁ = 1 := by
    have h := tgtT_norm_base_add S (c := s₁) (by linarith)
    rw [hb₁, norm_cutDir S] at h
    linarith
  have hnorm₂ : ‖(base S : ℂ)‖ - s₂ = -1 := by
    have h := tgtT_norm_base_sub_smul (S := S) (c := s₂)
    rw [hb₂] at h
    have h' : ((‖(base S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
      have h2 := congrArg (fun z : ℂ => z / cutDir S) h
      rw [mul_div_cancel_right₀ _ (cutDir_ne_zero S), neg_div,
        div_self (cutDir_ne_zero S)] at h2
      simpa using h2.symm
    exact_mod_cast h'
  rw [Work.Smooth.SphereJordan.tgtUpB]
  by_cases h1 : perPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    rw [srcOuterUp, norm_mul, norm_cutDir S, one_mul, Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : perPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (perPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (perPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      rw [tgtCut₂, tgtT_norm_base_sub, abs_le]
      refine ⟨?_, ?_⟩ <;>
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₂ - s₂ ≤ 0),
          mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂)
            (by linarith : (0:ℝ) ≤ 1 - (perPt τ - Real.pi / 2) / (Real.pi / 2))]
    · rw [if_neg h2]
      by_cases h3 : perPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact le_of_lt (hball _)
      · rw [if_neg h3]
        have hx0 : 0 ≤ (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        rw [tgtCut₁, tgtT_norm_base_add]
        · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
            mul_nonpos_of_nonpos_of_nonneg (by linarith : t₁ - s₁ ≤ 0)
              (by linarith : (0:ℝ) ≤ 1 - (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]
        · nlinarith

theorem tgtT_tgtDnB_norm_le_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (b : Bool) (θ₁ θ₂ : ℝ) (τ : ℝ) :
    ‖Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ‖ ≤ 1 := by
  have hpm := Work.SphereJordan.perPt_mem τ
  have hb : ‖(base S : ℂ)‖ < 1 := norm_base_lt_one S hball
  have hnorm₁ : ‖(base S : ℂ)‖ + s₁ = 1 := by
    have h := tgtT_norm_base_add S (c := s₁) (by linarith)
    rw [hb₁, norm_cutDir S] at h
    linarith
  have hnorm₂ : ‖(base S : ℂ)‖ - s₂ = -1 := by
    have h := tgtT_norm_base_sub_smul (S := S) (c := s₂)
    rw [hb₂] at h
    have h' : ((‖(base S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
      have h2 := congrArg (fun z : ℂ => z / cutDir S) h
      rw [mul_div_cancel_right₀ _ (cutDir_ne_zero S), neg_div,
        div_self (cutDir_ne_zero S)] at h2
      simpa using h2.symm
    exact_mod_cast h'
  rw [Work.Smooth.SphereJordan.tgtDnB]
  by_cases h1 : perPt τ ≤ Real.pi / 2
  · rw [if_pos h1]
    rw [srcOuterDn, norm_mul, norm_neg, norm_cutDir S, one_mul,
      Complex.norm_exp_ofReal_mul_I]
  · rw [if_neg h1]
    by_cases h2 : perPt τ ≤ Real.pi
    · rw [if_pos h2]
      have hx0 : 0 ≤ (perPt τ - Real.pi / 2) / (Real.pi / 2) :=
        div_nonneg (by linarith) (by positivity)
      have hx1 : (perPt τ - Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      rw [tgtCut₁, tgtT_norm_base_add]
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₁ - s₁ ≤ 0)]
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₁ - t₁) hx0,
          mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₁ - s₁ ≤ 0)]
    · rw [if_neg h2]
      by_cases h3 : perPt τ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        split_ifs <;> exact le_of_lt (hball _)
      · rw [if_neg h3]
        have hx0 : 0 ≤ (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hx1 : (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [hpm.2]
        rw [tgtCut₂, tgtT_norm_base_sub, abs_le]
        refine ⟨?_, ?_⟩ <;>
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂) hx0,
            mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith : t₂ - s₂ ≤ 0),
            mul_nonneg (by linarith : (0:ℝ) ≤ s₂ - t₂)
              (by linarith : (0:ℝ) ≤ 1 - (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2))]

theorem tgtT_upCurve_V_subset_annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hout₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hθ₁ : γ.γ θ₁ = (base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hθ₂ : γ.γ θ₂ = (base S : ℂ) - (t₂ : ℂ) * cutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.annulus S := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have hcl : T.V ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Work.Smooth.SphereJordan.tgtT_planeSeparation_V_subset_closedBall' T.toPlaneSeparation (by
        rintro _ ⟨τ, rfl⟩
        simpa using tgtT_tgtUpB_norm_le_one S hball hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ b θ₁ θ₂ τ)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hcl hx
  · intro hxV
    exact Set.disjoint_left.mp T.disjoint_UV (hVU hxV) hx

theorem tgtT_dnCurve_V_subset_annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hout₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hout₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hθ₁ : γ.γ θ₁ = (base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hθ₂ : γ.γ θ₂ = (base S : ℂ) - (t₂ : ℂ) * cutDir S)
    (T : Work.Smooth.Jordan.PlaneSchoenflies
      (Work.SphereJordan.tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂))
    (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.annulus S := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have hcl : T.V ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Work.Smooth.SphereJordan.tgtT_planeSeparation_V_subset_closedBall' T.toPlaneSeparation (by
        rintro _ ⟨τ, rfl⟩
        simpa using tgtT_tgtDnB_norm_le_one S hball hb₁ hb₂ ht₁ hts₁ ht₂ hts₂ b θ₁ θ₂ τ)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hcl hx
  · intro hxV
    exact Set.disjoint_left.mp T.disjoint_UV (hVU hxV) hx

theorem tgtT_cuts_subset_trace_up (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hout₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hout₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hθ₁ : γ.γ θ₁ = (base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hθ₂ : γ.γ θ₂ = (base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ ⊆
      (Work.SphereJordan.tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).trace := by
  have hpi : 0 < Real.pi := Real.pi_pos
  intro z hz
  rcases hz with hz | hz
  · -- first crosscut: z = base S + σ u, σ ∈ [t₁,s₁]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.1 with hσt | hσt
    · -- σ = t₁ : witness 3π/2, on the γ-arc endpoint a₁
      refine ⟨3 * Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2)
        = (base S : ℂ) + (σ : ℂ) * cutDir S
      have hper : perPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
        tgtT_perPt_eq_self (by positivity) (by linarith [hpi])
      have hcoef : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
        field_simp
        ring
      rw [Work.Smooth.SphereJordan.tgtUpB, hper,
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl, hcoef,
        ← hσt]
      split_ifs with hb
      · rw [show θ₂ + 1 * (θ₁ - θ₂) = θ₁ by ring, hθ₁]
      · rw [show θ₂ + 1 * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ - 2 * Real.pi by ring]
        rw [show γ.γ (θ₁ - 2 * Real.pi) = γ.γ θ₁ from by
          have h := γ.periodic (θ₁ - 2 * Real.pi)
          rw [show θ₁ - 2 * Real.pi + 2 * Real.pi = θ₁ by ring] at h
          exact h.symm]
        rw [hθ₁]
    · rcases eq_or_lt_of_le hσ.2 with hσs | hσs
      · -- σ = s₁ : witness 2π, on the outer semicircle start u
        refine ⟨2 * Real.pi, ?_⟩
        show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi)
          = (base S : ℂ) + (σ : ℂ) * cutDir S
        have hper : perPt (2 * Real.pi) = 0 := by
          have h := Work.Smooth.SphereJordan.perPt_shift (0 : ℝ)
          rw [show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h
          rw [h, tgtT_perPt_eq_self (le_refl 0) (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [Work.Smooth.SphereJordan.tgtUpB, hper,
          if_pos (by positivity : (0 : ℝ) ≤ Real.pi / 2), zero_div,
          Work.Smooth.SphereJordan.srcOuterUp, mul_zero, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, mul_one, hσs, hb₁]
      · -- t₁ < σ < s₁ : witness 3π/2 + ((σ-t₁)/(s₁-t₁))·(π/2), fourth branch
        refine ⟨3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2), ?_⟩
        show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
            (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2))
          = (base S : ℂ) + (σ : ℂ) * cutDir S
        have hy0 : 0 < (σ - t₁) / (s₁ - t₁) := by apply div_pos <;> linarith
        have hy1 : (σ - t₁) / (s₁ - t₁) < 1 := by
          rw [div_lt_one (by linarith)]; linarith [hσs]
        have hper : perPt (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2))
            = 3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) :=
          tgtT_perPt_eq_self (by positivity) (by nlinarith [hpi])
        rw [Work.Smooth.SphereJordan.tgtUpB, hper,
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ Real.pi / 2)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ Real.pi)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2)
              ≤ 3 * Real.pi / 2)),
          Work.Smooth.SphereJordan.tgtCut₁,
          show (3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) - 3 * Real.pi / 2)
              / (Real.pi / 2) = (σ - t₁) / (s₁ - t₁) by
            rw [show 3 * Real.pi / 2 + ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) - 3 * Real.pi / 2
              = ((σ - t₁) / (s₁ - t₁)) * (Real.pi / 2) by ring]
            exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
        have hst : s₁ - t₁ ≠ 0 := by linarith
        congr 1
        congr 1
        rw [Complex.ofReal_inj]
        field_simp
        ring
  · -- second crosscut: z = base S - σ u, σ ∈ [t₂,s₂]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.2 with hσs | hσs
    · -- σ = s₂ : witness π/2, on the outer semicircle end -u
      refine ⟨Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2)
        = (base S : ℂ) - (σ : ℂ) * cutDir S
      have hper : perPt (Real.pi / 2) = Real.pi / 2 :=
        tgtT_perPt_eq_self (by positivity) (by linarith [hpi])
      rw [Work.Smooth.SphereJordan.tgtUpB, hper, if_pos le_rfl,
        div_self (by positivity : (Real.pi / 2) ≠ 0), Work.Smooth.SphereJordan.srcOuterUp,
        mul_one, Complex.exp_pi_mul_I, mul_neg, mul_one, hσs, hb₂]
    · -- σ < s₂ : witness π/2 + ((s₂-σ)/(s₂-t₂))·(π/2), second branch
      refine ⟨Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2), ?_⟩
      show Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
          (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2))
        = (base S : ℂ) - (σ : ℂ) * cutDir S
      have hx0 : 0 < (s₂ - σ) / (s₂ - t₂) := by apply div_pos <;> linarith
      have hx1 : (s₂ - σ) / (s₂ - t₂) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith [hσ.1]
      have hper : perPt (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2))
          = Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) :=
        tgtT_perPt_eq_self (by positivity) (by nlinarith [hpi])
      rw [Work.Smooth.SphereJordan.tgtUpB, hper,
        if_neg (by nlinarith [hpi, hx0] : ¬ (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2)
            ≤ Real.pi / 2)),
        if_pos (by nlinarith [hpi, hx1] : Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2)
            ≤ Real.pi),
        Work.Smooth.SphereJordan.tgtCut₂,
        show (Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) - Real.pi / 2)
            / (Real.pi / 2) = (s₂ - σ) / (s₂ - t₂) by
          rw [show Real.pi / 2 + ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) - Real.pi / 2
            = ((s₂ - σ) / (s₂ - t₂)) * (Real.pi / 2) by ring]
          exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
      have hst : s₂ - t₂ ≠ 0 := by linarith
      congr 1
      congr 1
      rw [Complex.ofReal_inj]
      field_simp
      ring

theorem tgtT_cuts_subset_trace_dn (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} (b : Bool) (θ₁ θ₂ : ℝ)
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hts₁ : t₁ < s₁) (hts₂ : t₂ < s₂)
    (hout₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hout₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (hθ₁ : γ.γ θ₁ = (base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hθ₂ : γ.γ θ₂ = (base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ ⊆
      (Work.SphereJordan.tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).trace := by
  have hpi : 0 < Real.pi := Real.pi_pos
  intro z hz
  rcases hz with hz | hz
  · -- z = base S + σ u, σ ∈ [t₁,s₁]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.2 with hσs | hσs
    · -- σ = s₁ : the first branch, `srcOuterDn S 1 = cutDir S`
      refine ⟨Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (Real.pi / 2)
        = (base S : ℂ) + (σ : ℂ) * cutDir S
      have hper : perPt (Real.pi / 2) = Real.pi / 2 :=
        tgtT_perPt_eq_self (by positivity) (by linarith [hpi])
      rw [Work.Smooth.SphereJordan.tgtDnB, hper, if_pos le_rfl,
        div_self (by positivity : (Real.pi / 2) ≠ 0), Work.Smooth.SphereJordan.srcOuterDn,
        show (Real.pi * 1 : ℝ) = Real.pi by ring, Complex.exp_pi_mul_I,
        show -cutDir S * (-1) = cutDir S by ring, hσs, hb₁]
    · -- t₁ ≤ σ < s₁ : the second branch at π/2 + x·(π/2), x = (s₁-σ)/(s₁-t₁)
      refine ⟨Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2), ?_⟩
      show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
          (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2))
        = (base S : ℂ) + (σ : ℂ) * cutDir S
      have hx0 : 0 < (s₁ - σ) / (s₁ - t₁) :=
        div_pos (by linarith [hσs]) (by linarith [hts₁])
      have hx1 : (s₁ - σ) / (s₁ - t₁) ≤ 1 := by
        rw [div_le_one (by linarith [hts₁])]; linarith [hσ.1]
      have hper : perPt (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2))
          = Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) :=
        tgtT_perPt_eq_self (by positivity) (by nlinarith [hpi])
      rw [Work.Smooth.SphereJordan.tgtDnB, hper,
        if_neg (by nlinarith [hpi, hx0] : ¬ (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2)
            ≤ Real.pi / 2)),
        if_pos (by nlinarith [hpi, hx1] : Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2)
            ≤ Real.pi),
        Work.Smooth.SphereJordan.tgtCut₁,
        show (Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) - Real.pi / 2)
            / (Real.pi / 2) = (s₁ - σ) / (s₁ - t₁) by
          rw [show Real.pi / 2 + ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) - Real.pi / 2
            = ((s₁ - σ) / (s₁ - t₁)) * (Real.pi / 2) by ring]
          exact mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
      have hst : s₁ - t₁ ≠ 0 := by linarith
      congr 1
      congr 1
      rw [Complex.ofReal_inj]
      field_simp
      ring
  · -- z = base S - σ u, σ ∈ [t₂,s₂]
    obtain ⟨σ, hσ, rfl⟩ := hz
    rcases eq_or_lt_of_le hσ.1 with hσt | hσt
    · -- σ = t₂ : the third (γ-arc) branch with coefficient 1 lands on γ.γ θ₂ = a₂
      refine ⟨3 * Real.pi / 2, ?_⟩
      show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (3 * Real.pi / 2)
        = (base S : ℂ) - (σ : ℂ) * cutDir S
      have hper : perPt (3 * Real.pi / 2) = 3 * Real.pi / 2 :=
        tgtT_perPt_eq_self (by positivity) (by linarith [hpi])
      have hcoef : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
        field_simp
        ring
      rw [Work.Smooth.SphereJordan.tgtDnB, hper,
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [hpi] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl, hcoef]
      split_ifs with hb
      · rw [show θ₁ - 2 * Real.pi + 1 * (θ₂ - θ₁ + 2 * Real.pi) = θ₂ by ring, hθ₂, hσt]
      · rw [show θ₁ + 1 * (θ₂ - θ₁) = θ₂ by ring, hθ₂, hσt]
    · rcases eq_or_lt_of_le hσ.2 with hσs | hσs
      · -- σ = s₂ : the first branch, `srcOuterDn S 0 = -cutDir S`
        refine ⟨2 * Real.pi, ?_⟩
        show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ (2 * Real.pi)
          = (base S : ℂ) - (σ : ℂ) * cutDir S
        have hper : perPt (2 * Real.pi) = 0 := by
          have h := Work.Smooth.SphereJordan.perPt_shift (0 : ℝ)
          rw [show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h
          rw [h, tgtT_perPt_eq_self (le_refl 0) (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [Work.Smooth.SphereJordan.tgtDnB, hper,
          if_pos (by positivity : (0 : ℝ) ≤ Real.pi / 2), zero_div,
          Work.Smooth.SphereJordan.srcOuterDn,
          show (Real.pi * 0 : ℝ) = 0 by ring, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero, mul_one, hσs, hb₂]
      · -- t₂ < σ < s₂ : the fourth branch at 3π/2 + ((σ-t₂)/(s₂-t₂))·(π/2)
        refine ⟨3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2), ?_⟩
        show Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
            (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2))
          = (base S : ℂ) - (σ : ℂ) * cutDir S
        have hy0 : 0 < (σ - t₂) / (s₂ - t₂) :=
          div_pos (by linarith [hσt]) (by linarith [hts₂])
        have hy1 : (σ - t₂) / (s₂ - t₂) < 1 := by
          rw [div_lt_one (by linarith [hts₂])]; linarith [hσs]
        have hper : perPt (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2))
            = 3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) :=
          tgtT_perPt_eq_self (by positivity) (by nlinarith [hpi])
        rw [Work.Smooth.SphereJordan.tgtDnB, hper,
          if_neg (by nlinarith [hpi] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ Real.pi / 2)),
          if_neg (by nlinarith [hpi] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ Real.pi)),
          if_neg (by nlinarith [hpi, hy0] : ¬ (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2)
              ≤ 3 * Real.pi / 2)),
          Work.Smooth.SphereJordan.tgtCut₂,
          show 1 - (3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) - 3 * Real.pi / 2)
              / (Real.pi / 2) = (s₂ - σ) / (s₂ - t₂) by
            rw [show 3 * Real.pi / 2 + ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) - 3 * Real.pi / 2
              = ((σ - t₂) / (s₂ - t₂)) * (Real.pi / 2) by ring]
            rw [mul_div_cancel_right₀ _ (by positivity : (Real.pi / 2) ≠ 0)]
            have hst : s₂ - t₂ ≠ 0 := by linarith
            field_simp
            ring]
        have hst : s₂ - t₂ ≠ 0 := by linarith
        congr 1
        congr 1
        rw [Complex.ofReal_inj]
        field_simp
        ring

theorem tgtT_cut_inter_sphere_subset (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ}
    (hb₁ : (base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S)
    (hb₂ : (base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂) :
    ∀ z ∈ Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂,
      ‖z‖ = 1 → z ∈ ({cutDir S, -cutDir S} : Set ℂ) := by
  intro z hz hzn
  have hb : ‖(base S : ℂ)‖ < 1 := norm_base_lt_one S hball
  rcases hz with hz | hz
  · obtain ⟨σ, hσ, rfl⟩ := hz
    have h1 : ‖(base S : ℂ)‖ + σ = 1 := by
      have h := tgtT_norm_base_add S (c := σ) (le_trans (le_of_lt ht₁) hσ.1)
      rw [hzn] at h
      linarith
    have h2 : ‖(base S : ℂ)‖ + s₁ = 1 := by
      have h := tgtT_norm_base_add S (c := s₁) (by linarith)
      rw [hb₁, norm_cutDir S] at h
      linarith
    have hσ₁ : σ = s₁ := by linarith
    rw [hσ₁, hb₁]
    simp
  · obtain ⟨σ, hσ, rfl⟩ := hz
    have h3 : |‖(base S : ℂ)‖ - σ| = 1 := by
      have h := tgtT_norm_base_sub S (c := σ)
      rw [hzn] at h
      exact h.symm
    have h4 : ‖(base S : ℂ)‖ - s₂ = -1 := by
      have h := tgtT_norm_base_sub_smul (S := S) (c := s₂)
      rw [hb₂] at h
      have h' : ((‖(base S : ℂ)‖ - s₂ : ℝ) : ℂ) = -1 := by
        have h2 := congrArg (fun w : ℂ => w / cutDir S) h
        rw [mul_div_cancel_right₀ _ (cutDir_ne_zero S), neg_div,
          div_self (cutDir_ne_zero S)] at h2
        simpa using h2.symm
      exact_mod_cast h'
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h3 with h | h
    · exfalso; linarith [ht₂, hσ.1, hb]
    · have hσ₂ : σ = s₂ := by linarith
      rw [hσ₂, hb₂]
      simp


end

end Work.Smooth.SphereJordan

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

theorem tgtT_incOn_shift_two_pi {δ : ℝ → ℂ} (hδ : Continuous δ)
    (hper : Function.Periodic δ (2 * Real.pi)) (z : ℂ) (a b : ℝ) :
    incOn δ hδ z (a + 2 * Real.pi) (b + 2 * Real.pi) = incOn δ hδ z a b := by
  rw [incOn, incOn]
  refine Work.SphereJordan.pathIncTot_congr (fun t => ?_)
  simp only [ContinuousMap.coe_mk]
  congr 1
  rw [show a + 2 * Real.pi + (t : ℝ) * (b + 2 * Real.pi - (a + 2 * Real.pi))
      = (a + (t : ℝ) * (b - a)) + 2 * Real.pi from by ring]
  exact hper _

theorem tgtT_incOn_shift_neg_two_pi {δ : ℝ → ℂ} (hδ : Continuous δ)
    (hper : Function.Periodic δ (2 * Real.pi)) (z : ℂ) (a b : ℝ) :
    incOn δ hδ z (a - 2 * Real.pi) (b - 2 * Real.pi) = incOn δ hδ z a b := by
  have h := tgtT_incOn_shift_two_pi hδ hper z (a - 2 * Real.pi) (b - 2 * Real.pi)
  rw [show a - 2 * Real.pi + 2 * Real.pi = a from by ring,
    show b - 2 * Real.pi + 2 * Real.pi = b from by ring] at h
  exact h.symm

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-! ## The winding-number identity off the traces -/

theorem tgtT_outerLoop_ne_of_norm_lt (H : SpanHyp h hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    ∀ t, outerLoop H x t ≠ 0 := by
  intro t hcon
  have h1 : wiStdLoop S t = x := by
    have h2 : wiStdLoop S t - x = 0 := by rw [← wi_outerLoop_eq_std H x t]; exact hcon
    exact sub_eq_zero.mp h2
  have h2 : ‖x‖ = 1 := by rw [← h1, wi_std_norm S t]
  linarith

theorem tgtT_loopIndex_outer_of_norm_lt (H : SpanHyp h hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    Work.Smooth.SphereJordan.loopIndex (outerLoop H x) = 1 := by
  have hne0 : ∀ t : unitInterval, wiStdLoop S t ≠ 0 := by
    intro t h
    have h1 : ‖wiStdLoop S t‖ = 1 := wi_std_norm S t
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hne1 : ∀ t : unitInterval, outerLoop H x t ≠ 0 := tgtT_outerLoop_ne_of_norm_lt H hx
  set Hs : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => wiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x, by fun_prop⟩ with hHs
  have happ : ∀ p : unitInterval × unitInterval, Hs p =
      wiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, Hs p ≠ 0 := by
    rintro ⟨t, s⟩ hcon
    rw [happ] at hcon
    have hEq : wiStdLoop S t = ((((s : unitInterval) : ℝ)) : ℂ) * x := sub_eq_zero.mp hcon
    have h1 : ‖wiStdLoop S t‖ = 1 := wi_std_norm S t
    have h2 : ‖((((s : unitInterval) : ℝ)) : ℂ) * x‖ = 1 := by rw [← hEq, h1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1] at h2
    nlinarith [norm_nonneg x, hx, h2, s.2.1, s.2.2]
  have hH0 : ∀ t : unitInterval, Hs (t, 0) = wiStdLoop S t := by
    intro t; rw [happ]; simp
  have hH1 : ∀ t : unitInterval, Hs (t, 1) = outerLoop H x t := by
    intro t; rw [happ, wi_outerLoop_eq_std H x t]; simp
  have hHloop : ∀ s : unitInterval, Hs (0, s) = Hs (1, s) := by
    intro s; rw [happ, happ, wi_std_closed S]
  have h := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy hne0 hne1 Hs hHne hH0 hH1 hHloop
  exact h.symm.trans (wi_loopIndex_std S)

theorem tgtT_incr'_outer_of_norm_lt (H : SpanHyp h hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    incr' (outerLoop H x) = kappa := by
  rw [incr'_eq_loopIndex (tgtT_outerLoop_ne_of_norm_lt H hx) (wi_outerLoop_closed H x),
    tgtT_loopIndex_outer_of_norm_lt H hx]
  ring

theorem tgtT_incr'_semi_of_norm_lt (H : SpanHyp h hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    incr' (upP1 H x) + incr' (dnP1 H x) = kappa := by
  have hne : ∀ t, outerLoop H x t ≠ 0 := tgtT_outerLoop_ne_of_norm_lt H hx
  have hs' := wi_incr'_split (c := outerLoop H x) hne (σ := half1) (τ := half2)
    half1_zero half2_one (half1_one.trans half2_zero.symm)
  have h1 : incr' ((outerLoop H x).comp half1) = incr' (upP1 H x) :=
    incr'_congr (fun t => wi_outerLoop_half1 H x t)
  have h2 : incr' ((outerLoop H x).comp half2) = incr' (dnP1 H x) :=
    incr'_congr (fun t => wi_outerLoop_half2 H x t)
  exact (h1 ▸ h2 ▸ hs').trans (tgtT_incr'_outer_of_norm_lt H hx)

theorem tgtT_upP3_ne_of_notMem (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∉ γ.trace) (b : Bool) :
    ∀ t, upP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi)) - x ≠ 0
    intro hh
    exact hx ⟨_, sub_eq_zero.mp hh⟩
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂)) - x ≠ 0
    intro hh
    exact hx ⟨_, sub_eq_zero.mp hh⟩

theorem tgtT_dnP3_ne_of_notMem (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∉ γ.trace) (b : Bool) :
    ∀ t, dnP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁)) - x ≠ 0
    intro hh
    exact hx ⟨_, sub_eq_zero.mp hh⟩
  · show γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x ≠ 0
    intro hh
    exact hx ⟨_, sub_eq_zero.mp hh⟩

theorem tgtT_incr'_upP3_true_eq_incOn_of_notMem (H : SpanHyp h hs hball S) {x : ℂ}
    (hx : x ∉ γ.trace) :
    incr' (upP3 H x true) = incOn γ.γ γ.cont x H.θ₂ H.θ₁ := by
  rw [wi_incr'_eq_pathIncTot (tgtT_upP3_ne_of_notMem H hx true)]
  exact Work.SphereJordan.pathIncTot_congr (fun t => rfl)

theorem tgtT_incr'_dnP3_true_eq_incOn_of_notMem (H : SpanHyp h hs hball S) {x : ℂ}
    (hx : x ∉ γ.trace) :
    incr' (dnP3 H x true) = incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ := by
  rw [wi_incr'_eq_pathIncTot (tgtT_dnP3_ne_of_notMem H hx true)]
  refine Work.SphereJordan.pathIncTot_congr (fun t => ?_)
  show γ.γ (H.θ₁ - 2 * Real.pi + ((t : unitInterval) : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x
      = γ.γ (H.θ₁ - 2 * Real.pi +
          ((t : unitInterval) : ℝ) * (H.θ₂ - (H.θ₁ - 2 * Real.pi))) - x
  congr 1
  ring

theorem tgtT_incr'_upP3_false_eq_incOn_of_notMem (H : SpanHyp h hs hball S) {x : ℂ}
    (hx : x ∉ γ.trace) :
    incr' (upP3 H x false) = incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) := by
  rw [wi_incr'_eq_pathIncTot (tgtT_upP3_ne_of_notMem H hx false)]
  refine Work.SphereJordan.pathIncTot_congr (fun t => ?_)
  show γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi)) - x
      = γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * ((H.θ₁ - 2 * Real.pi) - H.θ₂)) - x
  congr 1
  ring

theorem tgtT_incr'_dnP3_false_eq_incOn_of_notMem (H : SpanHyp h hs hball S) {x : ℂ}
    (hx : x ∉ γ.trace) :
    incr' (dnP3 H x false) = incOn γ.γ γ.cont x H.θ₁ H.θ₂ := by
  rw [wi_incr'_eq_pathIncTot (tgtT_dnP3_ne_of_notMem H hx false)]
  exact Work.SphereJordan.pathIncTot_congr (fun t => rfl)

theorem tgtT_incr'_gamma_TT_of_notMem (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∉ γ.trace) :
    incr' (upP3 H x true) + incr' (dnP3 H x true) =
      (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * kappa := by
  have hz : ∀ t : ℝ, γ.γ t ≠ x := fun t => fun hh => hx ⟨t, hh⟩
  have hav : ∀ t ∈ Set.Icc (H.θ₁ - 2 * Real.pi) H.θ₁, γ.γ t ≠ x := fun t _ => hz t
  have hθ : H.θ₁ - 2 * Real.pi ≤ H.θ₂ := by linarith [H.hθ, H.hθ']
  have hθ' : H.θ₂ ≤ H.θ₁ := le_of_lt H.hθ
  have hadd := incOn_add γ.cont hθ hθ' hav
  have hper := incOn_period γ.cont γ.periodic x hz (H.θ₁ - 2 * Real.pi)
  have hk : H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ := by ring
  rw [hk] at hper
  rw [tgtT_incr'_upP3_true_eq_incOn_of_notMem H hx, tgtT_incr'_dnP3_true_eq_incOn_of_notMem H hx,
    kappa, ← hper, hadd]
  ring

theorem tgtT_incr'_gamma_FF (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∉ γ.trace) :
    incr' (upP3 H x false) + incr' (dnP3 H x false) =
      -((Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * kappa) := by
  have hz : ∀ t : ℝ, γ.γ t ≠ x := fun t => fun hh => hx ⟨t, hh⟩
  have hrev : incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) =
      -incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ :=
    incOn_rev γ.cont (by linarith [H.hθ, H.hθ']) (fun t _ => hz t)
  have hshift : incOn γ.γ γ.cont x H.θ₁ H.θ₂ =
      incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) (H.θ₂ - 2 * Real.pi) :=
    (tgtT_incOn_shift_neg_two_pi γ.cont γ.periodic x H.θ₁ H.θ₂).symm
  have hadd : incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) H.θ₂ =
      incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) (H.θ₁ - 2 * Real.pi) +
        incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ :=
    incOn_add γ.cont (by linarith [H.hθ]) (by linarith [H.hθ']) (fun t _ => hz t)
  have hrev2 : incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) (H.θ₂ - 2 * Real.pi) =
      -incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) (H.θ₁ - 2 * Real.pi) :=
    incOn_rev γ.cont (by linarith [H.hθ]) (fun t _ => hz t)
  have hper : incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) H.θ₂ =
      (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * kappa := by
    have h1 := tgtT_incOn_shift_two_pi γ.cont γ.periodic x (H.θ₂ - 2 * Real.pi) H.θ₂
    rw [show H.θ₂ - 2 * Real.pi + 2 * Real.pi = H.θ₂ from by ring] at h1
    rw [← h1, kappa, incOn_period γ.cont γ.periodic x hz H.θ₂]
  rw [tgtT_incr'_upP3_false_eq_incOn_of_notMem H hx, tgtT_incr'_dnP3_false_eq_incOn_of_notMem H hx,
    hrev, hshift, hrev2,
    show incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) (H.θ₁ - 2 * Real.pi) =
      incOn γ.γ γ.cont x (H.θ₂ - 2 * Real.pi) H.θ₂ -
        incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ from by rw [hadd]; ring,
    hper]
  ring

theorem tgtT_windSum_true (H : SpanHyp h hs hball S) {z : ℂ} (hzlt : ‖z‖ < 1) (hzγ : z ∉ γ.trace)
    (hzu : z ∉ (H.upPC true).trace) (hzd : z ∉ (H.dnPC true).trace) :
    Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont z
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont z
      = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z := by
  have hzu' : ∀ t, upLoop H z true t ≠ 0 := by
    intro t hh
    exact hzu ⟨2 * Real.pi * (t : ℝ), sub_eq_zero.mp hh⟩
  have hzd' : ∀ t, dnLoop H z true t ≠ 0 := by
    intro t hh
    exact hzd ⟨2 * Real.pi * (t : ℝ), sub_eq_zero.mp hh⟩
  have hU := wi_incr'_quarter (c := upLoop H z true) hzu'
  have hD := wi_incr'_quarter (c := dnLoop H z true) hzd'
  have hu1 : incr' ((upLoop H z true).comp q1) = incr' (upP1 H z) :=
    incr'_congr (fun t => wi_upLoop_q1 H z true t)
  have hu2 : incr' ((upLoop H z true).comp q2) = incr' (upP2 H z) :=
    incr'_congr (fun t => wi_upLoop_q2 H z true t)
  have hu3 : incr' ((upLoop H z true).comp q3) = incr' (upP3 H z true) :=
    incr'_congr (fun t => wi_upLoop_q3 H z true t)
  have hu4 : incr' ((upLoop H z true).comp q4) = incr' (upP4 H z) :=
    incr'_congr (fun t => wi_upLoop_q4 H z true t)
  have hd1 : incr' ((dnLoop H z true).comp q1) = incr' (dnP1 H z) :=
    incr'_congr (fun t => wi_dnLoop_q1 H z true t)
  have hd2 : incr' ((dnLoop H z true).comp q2) = incr' (dnP2 H z) :=
    incr'_congr (fun t => wi_dnLoop_q2 H z true t)
  have hd3 : incr' ((dnLoop H z true).comp q3) = incr' (dnP3 H z true) :=
    incr'_congr (fun t => wi_dnLoop_q3 H z true t)
  have hd4 : incr' ((dnLoop H z true).comp q4) = incr' (dnP4 H z) :=
    incr'_congr (fun t => wi_dnLoop_q4 H z true t)
  rw [hu1, hu2, hu3, hu4] at hU
  rw [hd1, hd2, hd3, hd4] at hD
  have hA := tgtT_incr'_semi_of_norm_lt H hzlt
  have hB := (wi_incr'_cut_pair H z).1
  have hC := (wi_incr'_cut_pair H z).2
  have hE := tgtT_incr'_gamma_TT_of_notMem H hzγ
  have hW : incr' (upLoop H z true) + incr' (dnLoop H z true)
      = (1 + (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z : ℂ)) * kappa := by
    rw [hU, hD]
    linear_combination hA + hB + hC + hE
  have h1 : incr' (upLoop H z true)
      = (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont z : ℂ) * kappa := by
    rw [incr'_eq_loopIndex hzu' (wi_upLoop_closed H z true), Work.SphereJordan.windNumber_upLoop]
  have h2 : incr' (dnLoop H z true)
      = (Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont z : ℂ) * kappa := by
    rw [incr'_eq_loopIndex hzd' (wi_dnLoop_closed H z true), Work.SphereJordan.windNumber_dnLoop]
  rw [h1, h2] at hW
  have hfin : ((Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont z
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont z : ℤ) : ℂ)
      = ((1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z : ℤ) : ℂ) := by
    refine mul_right_cancel₀ kappa_ne_zero ?_
    push_cast
    linear_combination hW
  exact_mod_cast hfin

theorem tgtT_windSum_false (H : SpanHyp h hs hball S) {z : ℂ} (hzlt : ‖z‖ < 1) (hzγ : z ∉ γ.trace)
    (hzu : z ∉ (H.upPC false).trace) (hzd : z ∉ (H.dnPC false).trace) :
    Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont z
      + Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont z
      = 1 - Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z := by
  have hzu' : ∀ t, upLoop H z false t ≠ 0 := by
    intro t hh
    exact hzu ⟨2 * Real.pi * (t : ℝ), sub_eq_zero.mp hh⟩
  have hzd' : ∀ t, dnLoop H z false t ≠ 0 := by
    intro t hh
    exact hzd ⟨2 * Real.pi * (t : ℝ), sub_eq_zero.mp hh⟩
  have hU := wi_incr'_quarter (c := upLoop H z false) hzu'
  have hD := wi_incr'_quarter (c := dnLoop H z false) hzd'
  have hu1 : incr' ((upLoop H z false).comp q1) = incr' (upP1 H z) :=
    incr'_congr (fun t => wi_upLoop_q1 H z false t)
  have hu2 : incr' ((upLoop H z false).comp q2) = incr' (upP2 H z) :=
    incr'_congr (fun t => wi_upLoop_q2 H z false t)
  have hu3 : incr' ((upLoop H z false).comp q3) = incr' (upP3 H z false) :=
    incr'_congr (fun t => wi_upLoop_q3 H z false t)
  have hu4 : incr' ((upLoop H z false).comp q4) = incr' (upP4 H z) :=
    incr'_congr (fun t => wi_upLoop_q4 H z false t)
  have hd1 : incr' ((dnLoop H z false).comp q1) = incr' (dnP1 H z) :=
    incr'_congr (fun t => wi_dnLoop_q1 H z false t)
  have hd2 : incr' ((dnLoop H z false).comp q2) = incr' (dnP2 H z) :=
    incr'_congr (fun t => wi_dnLoop_q2 H z false t)
  have hd3 : incr' ((dnLoop H z false).comp q3) = incr' (dnP3 H z false) :=
    incr'_congr (fun t => wi_dnLoop_q3 H z false t)
  have hd4 : incr' ((dnLoop H z false).comp q4) = incr' (dnP4 H z) :=
    incr'_congr (fun t => wi_dnLoop_q4 H z false t)
  rw [hu1, hu2, hu3, hu4] at hU
  rw [hd1, hd2, hd3, hd4] at hD
  have hA := tgtT_incr'_semi_of_norm_lt H hzlt
  have hB := (wi_incr'_cut_pair H z).1
  have hC := (wi_incr'_cut_pair H z).2
  have hE := tgtT_incr'_gamma_FF H hzγ
  have hW : incr' (upLoop H z false) + incr' (dnLoop H z false)
      = (1 - (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z : ℂ)) * kappa := by
    rw [hU, hD]
    linear_combination hA + hB + hC + hE
  have h1 : incr' (upLoop H z false)
      = (Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont z : ℂ) * kappa := by
    rw [incr'_eq_loopIndex hzu' (wi_upLoop_closed H z false), Work.SphereJordan.windNumber_upLoop]
  have h2 : incr' (dnLoop H z false)
      = (Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont z : ℂ) * kappa := by
    rw [incr'_eq_loopIndex hzd' (wi_dnLoop_closed H z false), Work.SphereJordan.windNumber_dnLoop]
  rw [h1, h2] at hW
  have hfin : ((Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont z
      + Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont z : ℤ) : ℂ)
      = ((1 - Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z : ℤ) : ℂ) := by
    refine mul_right_cancel₀ kappa_ne_zero ?_
    push_cast
    linear_combination hW
  exact_mod_cast hfin


/-! ## The traces of the two four-arc curves -/

def tgtT_arcImg (δ : ℝ → ℂ) (a b : ℝ) : Set ℂ := δ '' Set.Icc a b

theorem tgtT_gamma_trace_subset_arcs {θ₁ θ₂ : ℝ} :
    γ.trace ⊆ tgtT_arcImg γ.γ θ₂ θ₁ ∪ tgtT_arcImg γ.γ (θ₁ - 2 * Real.pi) θ₂ := by
  rintro _ ⟨s, rfl⟩
  set m : ℤ := ⌊(s - (θ₁ - 2 * Real.pi)) / (2 * Real.pi)⌋ with hm
  have hval : γ.γ (s - (m : ℝ) * (2 * Real.pi)) = γ.γ s := by
    have h := γ.periodic.int_mul m (s - (m : ℝ) * (2 * Real.pi))
    rw [show s - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = s from by ring] at h
    exact h.symm
  have hmem1 : θ₁ - 2 * Real.pi ≤ s - (m : ℝ) * (2 * Real.pi) := by
    have h := Int.floor_le ((s - (θ₁ - 2 * Real.pi)) / (2 * Real.pi))
    have h2 : (m : ℝ) ≤ (s - (θ₁ - 2 * Real.pi)) / (2 * Real.pi) := by exact_mod_cast h
    have h3 := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mp h2
    linarith
  have hmem2 : s - (m : ℝ) * (2 * Real.pi) < θ₁ := by
    have h := Int.lt_floor_add_one ((s - (θ₁ - 2 * Real.pi)) / (2 * Real.pi))
    have h2 : (s - (θ₁ - 2 * Real.pi)) / (2 * Real.pi) < (m : ℝ) + 1 := by exact_mod_cast h
    have h3 := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mp h2
    linarith
  by_cases hle : s - (m : ℝ) * (2 * Real.pi) ≤ θ₂
  · exact Or.inr ⟨s - (m : ℝ) * (2 * Real.pi), ⟨hmem1, hle⟩, hval⟩
  · exact Or.inl ⟨s - (m : ℝ) * (2 * Real.pi), ⟨le_of_lt (not_le.mp hle), hmem2.le⟩, hval⟩

theorem tgtT_arc_inter_arc_subset_cuts (H : SpanHyp h hs hball S) :
    tgtT_arcImg γ.γ H.θ₂ H.θ₁ ∩ tgtT_arcImg γ.γ (H.θ₁ - 2 * Real.pi) H.θ₂ ⊆
      Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ := by
  rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
  have hxy : γ.γ x = γ.γ y := by rw [hxz, hyz]
  obtain ⟨k, hk⟩ := Work.SphereJordan.gamma_eq_imp_mod hs hxy
  have hlow : (0:ℝ) ≤ x - y := by linarith [hx.1, hy.2]
  have hhigh : x - y ≤ 2 * Real.pi := by linarith [hx.2, hy.1]
  have hkR : (k : ℝ) = (x - y) / (2 * Real.pi) := by
    field_simp
    linarith [hk]
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by
    rw [hkR]; exact div_nonneg hlow (by positivity)
  have hk1 : (k:ℝ) ≤ 1 := by
    rw [hkR, div_le_one (by positivity)]; exact hhigh
  have hk0' : (0:ℤ) ≤ k := by exact_mod_cast hk0
  have hk1' : k ≤ 1 := by exact_mod_cast hk1
  interval_cases k
  · have h0 : x - y = 0 := by simpa using hk
    have hxy' : x = y := by linarith
    have hy' : y = H.θ₂ := le_antisymm hy.2 (by rw [← hxy']; exact hx.1)
    refine Or.inr ⟨H.t₂, ⟨le_rfl, H.ht₂s₂.le⟩, ?_⟩
    rw [← hyz, hy', H.hθ₂]
  · have h0 : x - y = 2 * Real.pi := by simpa using hk
    have hx' : x = H.θ₁ := le_antisymm hx.2 (by linarith [hy.1, h0])
    refine Or.inl ⟨H.t₁, ⟨le_rfl, H.ht₁s₁.le⟩, ?_⟩
    rw [← hxz, hx', H.hθ₁]

theorem tgtT_arcA_subset_trace_up (H : SpanHyp h hs hball S) :
    tgtT_arcImg γ.γ H.θ₂ H.θ₁ ⊆
      Set.range (Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ true H.θ₁ H.θ₂) := by
  rintro _ ⟨s, hs', rfl⟩
  have hden : 0 < H.θ₁ - H.θ₂ := by linarith [H.hθ]
  set t : ℝ := (s - H.θ₂) / (H.θ₁ - H.θ₂) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hs'.1]) hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith [hs'.2]
  have hst : H.θ₂ + t * (H.θ₁ - H.θ₂) = s := by rw [ht]; field_simp; ring
  set τ : ℝ := Real.pi + t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have harg : (τ - Real.pi) / (Real.pi / 2) = t := by rw [hτ]; field_simp; ring
  have hτnot1 : ¬ (τ ≤ Real.pi / 2) := by rw [hτ]; nlinarith [ht0, Real.pi_pos]
  rw [Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtUpBun,
    if_neg hτnot1]
  by_cases h2 : τ ≤ Real.pi
  · rw [if_pos h2]
    have hτπ : τ = Real.pi := le_antisymm h2 (by rw [hτ]; nlinarith [ht0, Real.pi_pos])
    have ht0' : t = 0 := by
      have hh : t * (Real.pi / 2) = 0 := by linarith [hτ]
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
    rw [show (τ - Real.pi / 2) / (Real.pi / 2) = 1 from by rw [hτπ]; field_simp; ring,
      Work.SphereJordan.tgtCut₂_one, ← H.hθ₂, ← hst, ht0', zero_mul, add_zero]
  · rw [if_neg h2,
      if_pos (by rw [hτ]; nlinarith [ht1, Real.pi_pos] : τ ≤ 3 * Real.pi / 2), if_pos rfl,
      harg, hst]

theorem tgtT_arcB_subset_trace_up (H : SpanHyp h hs hball S) :
    tgtT_arcImg γ.γ (H.θ₁ - 2 * Real.pi) H.θ₂ ⊆
      Set.range (Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ false H.θ₁ H.θ₂) := by
  rintro _ ⟨s, hs', rfl⟩
  have hden : 0 < H.θ₂ - (H.θ₁ - 2 * Real.pi) := by linarith [H.hθ']
  set t : ℝ := (H.θ₂ - s) / (H.θ₂ - (H.θ₁ - 2 * Real.pi)) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hs'.2]) hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith [hs'.1]
  have hst : H.θ₂ + t * (H.θ₁ - H.θ₂ - 2 * Real.pi) = s := by rw [ht]; field_simp; ring
  set τ : ℝ := Real.pi + t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have harg : (τ - Real.pi) / (Real.pi / 2) = t := by rw [hτ]; field_simp; ring
  have hτnot1 : ¬ (τ ≤ Real.pi / 2) := by rw [hτ]; nlinarith [ht0, Real.pi_pos]
  rw [Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtUpBun,
    if_neg hτnot1]
  by_cases h2 : τ ≤ Real.pi
  · rw [if_pos h2]
    have hτπ : τ = Real.pi := le_antisymm h2 (by rw [hτ]; nlinarith [ht0, Real.pi_pos])
    have ht0' : t = 0 := by
      have hh : t * (Real.pi / 2) = 0 := by linarith [hτ]
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
    rw [show (τ - Real.pi / 2) / (Real.pi / 2) = 1 from by rw [hτπ]; field_simp; ring,
      Work.SphereJordan.tgtCut₂_one, ← H.hθ₂, ← hst, ht0', zero_mul, add_zero]
  · rw [if_neg h2,
      if_pos (by rw [hτ]; nlinarith [ht1, Real.pi_pos] : τ ≤ 3 * Real.pi / 2),
      if_neg (by simp : ¬ (false = true)), harg, hst]

theorem tgtT_arcB_subset_trace_dn (H : SpanHyp h hs hball S) :
    tgtT_arcImg γ.γ (H.θ₁ - 2 * Real.pi) H.θ₂ ⊆
      Set.range (Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ true H.θ₁ H.θ₂) := by
  rintro _ ⟨s, hs', rfl⟩
  have hden : 0 < H.θ₂ - H.θ₁ + 2 * Real.pi := by linarith [H.hθ']
  set t : ℝ := (s - (H.θ₁ - 2 * Real.pi)) / (H.θ₂ - H.θ₁ + 2 * Real.pi) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hs'.1]) hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith [hs'.2]
  have hst : H.θ₁ - 2 * Real.pi + t * (H.θ₂ - H.θ₁ + 2 * Real.pi) = s := by
    rw [ht]; field_simp; ring
  set τ : ℝ := Real.pi + t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have harg : (τ - Real.pi) / (Real.pi / 2) = t := by rw [hτ]; field_simp; ring
  have hτnot1 : ¬ (τ ≤ Real.pi / 2) := by rw [hτ]; nlinarith [ht0, Real.pi_pos]
  rw [Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtDnBun,
    if_neg hτnot1]
  by_cases h2 : τ ≤ Real.pi
  · rw [if_pos h2]
    have hτπ : τ = Real.pi := le_antisymm h2 (by rw [hτ]; nlinarith [ht0, Real.pi_pos])
    have ht0' : t = 0 := by
      have hh : t * (Real.pi / 2) = 0 := by linarith [hτ]
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
    rw [show (τ - Real.pi / 2) / (Real.pi / 2) = 1 from by rw [hτπ]; field_simp; ring,
      Work.SphereJordan.tgtCut₁_one, ← H.hθ₁, ← hst, ht0', zero_mul, add_zero,
      show H.θ₁ - 2 * Real.pi = H.θ₁ + (-1 : ℤ) * (2 * Real.pi) from by push_cast; ring,
      γ.apply_add_int_mul]
  · rw [if_neg h2,
      if_pos (by rw [hτ]; nlinarith [ht1, Real.pi_pos] : τ ≤ 3 * Real.pi / 2), if_pos rfl,
      harg, hst]

theorem tgtT_arcA_subset_trace_dn (H : SpanHyp h hs hball S) :
    tgtT_arcImg γ.γ H.θ₂ H.θ₁ ⊆
      Set.range (Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ false H.θ₁ H.θ₂) := by
  rintro _ ⟨s, hs', rfl⟩
  have hden : 0 < H.θ₁ - H.θ₂ := by linarith [H.hθ]
  set t : ℝ := (H.θ₁ - s) / (H.θ₁ - H.θ₂) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hs'.2]) hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith [hs'.1]
  have hst : H.θ₁ + t * (H.θ₂ - H.θ₁) = s := by rw [ht]; field_simp; ring
  set τ : ℝ := Real.pi + t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) := ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have harg : (τ - Real.pi) / (Real.pi / 2) = t := by rw [hτ]; field_simp; ring
  have hτnot1 : ¬ (τ ≤ Real.pi / 2) := by rw [hτ]; nlinarith [ht0, Real.pi_pos]
  rw [Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtDnBun,
    if_neg hτnot1]
  by_cases h2 : τ ≤ Real.pi
  · rw [if_pos h2]
    have hτπ : τ = Real.pi := le_antisymm h2 (by rw [hτ]; nlinarith [ht0, Real.pi_pos])
    have ht0' : t = 0 := by
      have hh : t * (Real.pi / 2) = 0 := by linarith [hτ]
      exact (mul_eq_zero.mp hh).resolve_right (by positivity)
    rw [show (τ - Real.pi / 2) / (Real.pi / 2) = 1 from by rw [hτπ]; field_simp; ring,
      Work.SphereJordan.tgtCut₁_one, ← H.hθ₁, ← hst, ht0', zero_mul, add_zero,
      show H.θ₁ = H.θ₂ + (H.θ₁ - H.θ₂) from by ring]
  · rw [if_neg h2,
      if_pos (by rw [hτ]; nlinarith [ht1, Real.pi_pos] : τ ≤ 3 * Real.pi / 2),
      if_neg (by simp : ¬ (false = true)), harg, hst]

theorem tgtT_upArc_subset_trace_up (H : SpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.SphereJordan.upArc S ⊆
      Set.range (Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂) := by
  rintro z ⟨hzn, hzim⟩
  set w : ℂ := z / Work.Smooth.SphereJordan.cutDir S with hwdef
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_div, hzn, Work.Smooth.SphereJordan.norm_cutDir, div_one]
  have hwexp : Complex.exp (((w.arg : ℝ)) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hwn] at h
    simpa using h
  have harg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hzim
  have hargπ : w.arg ≤ Real.pi := Complex.arg_le_pi w
  set t : ℝ := w.arg / Real.pi with ht
  have ht1 : t ≤ 1 := by rw [ht, div_le_one Real.pi_pos]; exact hargπ
  set τ : ℝ := t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) :=
    ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have hτle : τ ≤ Real.pi / 2 := by rw [hτ]; nlinarith [ht1, Real.pi_pos]
  have hzu : z = Work.Smooth.SphereJordan.cutDir S * Complex.exp (((w.arg : ℝ)) * Complex.I) := by
    have h1 : Work.Smooth.SphereJordan.cutDir S * Complex.exp (((w.arg : ℝ)) * Complex.I) =
        Work.Smooth.SphereJordan.cutDir S * (z / Work.Smooth.SphereJordan.cutDir S) := by
      rw [hwexp]
    rw [h1, mul_comm]
    exact (div_mul_cancel₀ z (Work.Smooth.SphereJordan.cutDir_ne_zero S)).symm
  rw [Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtUpBun,
    if_pos hτle, Work.Smooth.SphereJordan.srcOuterUp, hzu]
  have harith : Real.pi * (τ / (Real.pi / 2)) = w.arg := by
    rw [hτ, ht]
    field_simp
  rw [harith]

theorem tgtT_downArc_subset_trace_dn (H : SpanHyp h hs hball S) (b : Bool) :
    Work.Smooth.SphereJordan.downArc S ⊆
      Set.range (Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂) := by
  rintro z ⟨hzn, hzim⟩
  set w : ℂ := -(z / Work.Smooth.SphereJordan.cutDir S) with hwdef
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_neg, norm_div, hzn, Work.Smooth.SphereJordan.norm_cutDir, div_one]
  have hwexp : Complex.exp (((w.arg : ℝ)) * Complex.I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hwn] at h
    simpa using h
  have harg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr (by rw [hwdef]; simpa using hzim)
  have hargπ : w.arg ≤ Real.pi := Complex.arg_le_pi w
  set t : ℝ := w.arg / Real.pi with ht
  have ht1 : t ≤ 1 := by rw [ht, div_le_one Real.pi_pos]; exact hargπ
  set τ : ℝ := t * (Real.pi / 2) with hτ
  refine ⟨τ, ?_⟩
  have hτmem : τ ∈ Set.Ico (0:ℝ) (2*Real.pi) :=
    ⟨by positivity, by nlinarith [ht1, Real.pi_pos]⟩
  have hτle : τ ≤ Real.pi / 2 := by rw [hτ]; nlinarith [ht1, Real.pi_pos]
  have hzu : z = -(Work.Smooth.SphereJordan.cutDir S *
      Complex.exp (((w.arg : ℝ)) * Complex.I)) := by
    have h1 : -(Work.Smooth.SphereJordan.cutDir S * Complex.exp (((w.arg : ℝ)) * Complex.I)) =
        -(Work.Smooth.SphereJordan.cutDir S * -(z / Work.Smooth.SphereJordan.cutDir S)) := by
      rw [hwexp]
    rw [h1, mul_neg, neg_neg, mul_comm]
    exact (div_mul_cancel₀ z (Work.Smooth.SphereJordan.cutDir_ne_zero S)).symm
  rw [Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hτmem, Work.SphereJordan.tgtDnBun,
    if_pos hτle, Work.Smooth.SphereJordan.srcOuterDn, hzu, neg_mul]
  have harith : Real.pi * (τ / (Real.pi / 2)) = w.arg := by
    rw [hτ, ht]
    field_simp
  rw [harith]

theorem tgtT_cutDir_mem_cut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S) (ht : t₁ ≤ s₁) :
    Work.Smooth.SphereJordan.cutDir S ∈ Work.Smooth.SphereJordan.cut₁ S t₁ s₁ :=
  ⟨s₁, ⟨ht, le_rfl⟩, hout₁.symm⟩

theorem tgtT_neg_cutDir_mem_cut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₂ s₂ : ℝ}
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S) (ht : t₂ ≤ s₂) :
    -Work.Smooth.SphereJordan.cutDir S ∈ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ :=
  ⟨s₂, ⟨ht, le_rfl⟩, hout₂.symm⟩

theorem tgtT_upArc_inter_downArc_subset_cuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (ht₁ : t₁ ≤ s₁) (ht₂ : t₂ ≤ s₂) :
    (Work.Smooth.SphereJordan.upArc S ∩ Work.Smooth.SphereJordan.downArc S) ⊆
      Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ := by
  intro z hz
  obtain ⟨⟨hzn, hzu⟩, -, hzd⟩ := hz
  have hwmem : ‖z / Work.Smooth.SphereJordan.cutDir S‖ = 1 := by
    rw [norm_div, hzn, Work.Smooth.SphereJordan.norm_cutDir, div_one]
  have hwim : (z / Work.Smooth.SphereJordan.cutDir S).im = 0 := le_antisymm hzd hzu
  have hwr : z / Work.Smooth.SphereJordan.cutDir S =
      (((z / Work.Smooth.SphereJordan.cutDir S).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hwim]
  have habs : |(z / Work.Smooth.SphereJordan.cutDir S).re| = 1 := by
    have h := hwmem
    rw [hwr, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hz' : z = Work.Smooth.SphereJordan.cutDir S * (z / Work.Smooth.SphereJordan.cutDir S) := by
    rw [mul_comm, div_mul_cancel₀ _ (Work.Smooth.SphereJordan.cutDir_ne_zero S)]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with h | h
  · left
    rw [hz', hwr, h]
    norm_num
    exact tgtT_cutDir_mem_cut₁ S hout₁ ht₁
  · right
    rw [hz', hwr, h]
    norm_num
    exact tgtT_neg_cutDir_mem_cut₂ S hout₂ ht₂

theorem tgtT_srcOuterUp_mem_upArc (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Work.Smooth.SphereJordan.srcOuterUp S x ∈ Work.Smooth.SphereJordan.upArc S := by
  refine ⟨?_, ?_⟩
  · have h := Work.SphereJordan.srcOuterUp_mem_sphere S x
    rwa [Metric.mem_sphere, dist_zero_right] at h
  · have hc : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
      Work.Smooth.SphereJordan.cutDir_ne_zero S
    have hdiv : Work.Smooth.SphereJordan.srcOuterUp S x / Work.Smooth.SphereJordan.cutDir S =
        Complex.exp (((Real.pi * x : ℝ)) * Complex.I) := by
      rw [Work.Smooth.SphereJordan.srcOuterUp]; field_simp
    rw [hdiv, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by nlinarith [hx.1, Real.pi_pos], by nlinarith [hx.2, Real.pi_pos]⟩

theorem tgtT_srcOuterDn_mem_downArc (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Work.Smooth.SphereJordan.srcOuterDn S x ∈ Work.Smooth.SphereJordan.downArc S := by
  refine ⟨?_, ?_⟩
  · have h := Work.SphereJordan.srcOuterDn_mem_sphere S x
    rwa [Metric.mem_sphere, dist_zero_right] at h
  · have hc : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
      Work.Smooth.SphereJordan.cutDir_ne_zero S
    have hdiv : Work.Smooth.SphereJordan.srcOuterDn S x / Work.Smooth.SphereJordan.cutDir S =
        -(Complex.exp (((Real.pi * x : ℝ)) * Complex.I)) := by
      rw [Work.Smooth.SphereJordan.srcOuterDn, neg_mul]; field_simp
    rw [hdiv, Complex.neg_im, Complex.exp_ofReal_mul_I_im]
    have hsin : 0 ≤ Real.sin (Real.pi * x) := Real.sin_nonneg_of_mem_Icc
      ⟨by nlinarith [hx.1, Real.pi_pos], by nlinarith [hx.2, Real.pi_pos]⟩
    linarith

theorem tgtT_tgtUpB_sphere_upArc (H : SpanHyp h hs hball S) (b : Bool) (τ : ℝ)
    (hτ : ‖Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ‖ = 1) :
    Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ ∈
      Work.Smooth.SphereJordan.upArc S ∪
        (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
  have hnorm : ‖Work.SphereJordan.tgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (Work.Smooth.SphereJordan.perPt τ)‖ = 1 := by
    rw [← Work.SphereJordan.tgtUpB_eq]; exact hτ
  set σ := Work.Smooth.SphereJordan.perPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2*Real.pi) := Work.SphereJordan.perPt_mem τ
  rw [Work.SphereJordan.tgtUpB_eq, ← hσdef, Work.SphereJordan.tgtUpBun]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    refine Or.inl (tgtT_srcOuterUp_mem_upArc S ⟨?_, ?_⟩)
    · exact div_nonneg hσmem.1 (by positivity)
    · rw [div_le_one (by positivity)]; exact h1
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ ((σ - Real.pi/2)/(Real.pi/2)) ∈
          Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ :=
        Work.SphereJordan.tgtCut₂_mem_cut₂ S H.ht₂s₂.le
          (Work.SphereJordan.halfParam_mem (le_of_lt (not_le.mp h1)) h2)
      have hnm : ‖Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
          ((σ - Real.pi/2)/(Real.pi/2))‖ = 1 := by
        simpa [Work.SphereJordan.tgtUpBun, if_neg h1, if_pos h2] using hnorm
      have hmem' := Work.Smooth.SphereJordan.tgtT_cut_inter_sphere_subset S hball H.hout₁ H.hout₂ H.ht₁
        H.ht₁s₁ H.ht₂ H.ht₂s₂ _ (Or.inr hmem) hnm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
      rcases hmem' with hh | hh
      · exact Or.inr (Or.inl (hh ▸ tgtT_cutDir_mem_cut₁ S H.hout₁ H.ht₁s₁.le))
      · exact Or.inr (Or.inr (hh ▸ tgtT_neg_cutDir_mem_cut₂ S H.hout₂ H.ht₂s₂.le))
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        exfalso
        cases b
        · have hnm : ‖γ.γ (H.θ₂ + (σ - Real.pi)/(Real.pi/2) * (H.θ₁ - H.θ₂ - 2*Real.pi))‖ = 1 := by
            simpa [Work.SphereJordan.tgtUpBun, if_neg h1, if_neg h2, if_pos h3,
              Bool.false_eq_true] using hnorm
          linarith [hball (H.θ₂ + (σ - Real.pi)/(Real.pi/2) * (H.θ₁ - H.θ₂ - 2*Real.pi)), hnm]
        · have hnm : ‖γ.γ (H.θ₂ + (σ - Real.pi)/(Real.pi/2) * (H.θ₁ - H.θ₂))‖ = 1 := by
            simpa [Work.SphereJordan.tgtUpBun, if_neg h1, if_neg h2, if_pos h3] using hnorm
          linarith [hball (H.θ₂ + (σ - Real.pi)/(Real.pi/2) * (H.θ₁ - H.θ₂)), hnm]
      · rw [if_neg h3]
        have hmem : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
            (1 - (σ - 3 * Real.pi/2)/(Real.pi/2)) ∈ Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ :=
          Work.SphereJordan.tgtCut₁_mem_cut₁ S H.ht₁s₁.le
            (Work.SphereJordan.lastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        have hnm : ‖Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
            (1 - (σ - 3 * Real.pi/2)/(Real.pi/2))‖ = 1 := by
          simpa [Work.SphereJordan.tgtUpBun, if_neg h1, if_neg h2, if_neg h3] using hnorm
        have hmem' := Work.Smooth.SphereJordan.tgtT_cut_inter_sphere_subset S hball H.hout₁ H.hout₂ H.ht₁
          H.ht₁s₁ H.ht₂ H.ht₂s₂ _ (Or.inl hmem) hnm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
        rcases hmem' with hh | hh
        · exact Or.inr (Or.inl (hh ▸ tgtT_cutDir_mem_cut₁ S H.hout₁ H.ht₁s₁.le))
        · exact Or.inr (Or.inr (hh ▸ tgtT_neg_cutDir_mem_cut₂ S H.hout₂ H.ht₂s₂.le))

theorem tgtT_tgtDnB_sphere_downArc (H : SpanHyp h hs hball S) (b : Bool) (τ : ℝ)
    (hτ : ‖Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ‖ = 1) :
    Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ ∈
      Work.Smooth.SphereJordan.downArc S ∪
        (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
  have hnorm : ‖Work.SphereJordan.tgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (Work.Smooth.SphereJordan.perPt τ)‖ = 1 := by
    rw [← Work.SphereJordan.tgtDnB_eq]; exact hτ
  set σ := Work.Smooth.SphereJordan.perPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2*Real.pi) := Work.SphereJordan.perPt_mem τ
  rw [Work.SphereJordan.tgtDnB_eq, ← hσdef, Work.SphereJordan.tgtDnBun]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    refine Or.inl (tgtT_srcOuterDn_mem_downArc S ⟨?_, ?_⟩)
    · exact div_nonneg hσmem.1 (by positivity)
    · rw [div_le_one (by positivity)]; exact h1
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ ((σ - Real.pi/2)/(Real.pi/2)) ∈
          Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ :=
        Work.SphereJordan.tgtCut₁_mem_cut₁ S H.ht₁s₁.le
          (Work.SphereJordan.halfParam_mem (le_of_lt (not_le.mp h1)) h2)
      have hnm : ‖Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
          ((σ - Real.pi/2)/(Real.pi/2))‖ = 1 := by
        simpa [Work.SphereJordan.tgtDnBun, if_neg h1, if_pos h2] using hnorm
      have hmem' := Work.Smooth.SphereJordan.tgtT_cut_inter_sphere_subset S hball H.hout₁ H.hout₂ H.ht₁
        H.ht₁s₁ H.ht₂ H.ht₂s₂ _ (Or.inl hmem) hnm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
      rcases hmem' with hh | hh
      · exact Or.inr (Or.inl (hh ▸ tgtT_cutDir_mem_cut₁ S H.hout₁ H.ht₁s₁.le))
      · exact Or.inr (Or.inr (hh ▸ tgtT_neg_cutDir_mem_cut₂ S H.hout₂ H.ht₂s₂.le))
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        exfalso
        cases b
        · have hnm : ‖γ.γ (H.θ₁ + (σ - Real.pi)/(Real.pi/2) * (H.θ₂ - H.θ₁))‖ = 1 := by
            simpa [Work.SphereJordan.tgtDnBun, if_neg h1, if_neg h2, if_pos h3,
              Bool.false_eq_true] using hnorm
          linarith [hball (H.θ₁ + (σ - Real.pi)/(Real.pi/2) * (H.θ₂ - H.θ₁)), hnm]
        · have hnm : ‖γ.γ (H.θ₁ - 2*Real.pi + (σ - Real.pi)/(Real.pi/2) *
              (H.θ₂ - H.θ₁ + 2*Real.pi))‖ = 1 := by
            simpa [Work.SphereJordan.tgtDnBun, if_neg h1, if_neg h2, if_pos h3] using hnorm
          linarith [hball (H.θ₁ - 2*Real.pi + (σ - Real.pi)/(Real.pi/2) *
            (H.θ₂ - H.θ₁ + 2*Real.pi)), hnm]
      · rw [if_neg h3]
        have hmem : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
            (1 - (σ - 3 * Real.pi/2)/(Real.pi/2)) ∈ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ :=
          Work.SphereJordan.tgtCut₂_mem_cut₂ S H.ht₂s₂.le
            (Work.SphereJordan.lastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        have hnm : ‖Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
            (1 - (σ - 3 * Real.pi/2)/(Real.pi/2))‖ = 1 := by
          simpa [Work.SphereJordan.tgtDnBun, if_neg h1, if_neg h2, if_neg h3] using hnorm
        have hmem' := Work.Smooth.SphereJordan.tgtT_cut_inter_sphere_subset S hball H.hout₁ H.hout₂ H.ht₁
          H.ht₁s₁ H.ht₂ H.ht₂s₂ _ (Or.inr hmem) hnm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
        rcases hmem' with hh | hh
        · exact Or.inr (Or.inl (hh ▸ tgtT_cutDir_mem_cut₁ S H.hout₁ H.ht₁s₁.le))
        · exact Or.inr (Or.inr (hh ▸ tgtT_neg_cutDir_mem_cut₂ S H.hout₂ H.ht₂s₂.le))

theorem tgtT_trace_inter_trace_subset_cuts (H : SpanHyp h hs hball S) (b : Bool) :
    (H.upPC b).trace ∩ (H.dnPC b).trace ⊆
      Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ := by
  intro z hz
  obtain ⟨hzu, hzd⟩ := hz
  obtain ⟨τ, hτ⟩ := hzu
  obtain ⟨τ', hτ'⟩ := hzd
  rw [SpanHyp.upPC_apply] at hτ
  rw [SpanHyp.dnPC_apply] at hτ'
  cases b
  case true =>
    have hZu : z ∈ Metric.sphere (0:ℂ) 1 ∪ (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
        Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ ∪ tgtT_arcImg γ.γ H.θ₂ H.θ₁) := by
      rw [← hτ]
      exact Work.SphereJordan.tgtUpB_true_mem_trace S H.ht₁s₁.le H.ht₂s₂.le H.hθ τ
    have hZd : z ∈ Metric.sphere (0:ℂ) 1 ∪ (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
        Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ ∪ tgtT_arcImg γ.γ (H.θ₁ - 2*Real.pi) H.θ₂) := by
      rw [← hτ']
      exact Work.SphereJordan.tgtDnB_true_mem_trace S H.ht₁s₁.le H.ht₂s₂.le H.hθ' τ'
    rcases hZu with hsp | hmid
    · rcases hZd with hsp' | hmid'
      · have hnu : ‖z‖ = 1 := by
          have h2 := Metric.mem_sphere.mp hsp
          rwa [dist_zero_right] at h2
        have hnd : ‖z‖ = 1 := by
          have h2 := Metric.mem_sphere.mp hsp'
          rwa [dist_zero_right] at h2
        have h1 : z ∈ Work.Smooth.SphereJordan.upArc S ∪
            (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
              Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
          rw [← hτ]
          exact tgtT_tgtUpB_sphere_upArc H true τ (by rw [hτ]; exact hnu)
        have h2 : z ∈ Work.Smooth.SphereJordan.downArc S ∪
            (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
              Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
          rw [← hτ']
          exact tgtT_tgtDnB_sphere_downArc H true τ' (by rw [hτ']; exact hnd)
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact tgtT_upArc_inter_downArc_subset_cuts S H.hout₁ H.hout₂ H.ht₁s₁.le H.ht₂s₂.le ⟨h1, h2⟩
          · exact h2
        · exact h1
      · rcases hmid' with hcuts' | harc'
        · exact hcuts'
        · exfalso
          obtain ⟨s, -, hs⟩ := harc'
          have h2 := Metric.mem_sphere.mp hsp
          rw [dist_zero_right, ← hs] at h2
          linarith [hball s]
    · rcases hmid with hcuts | harc
      · exact hcuts
      · rcases hZd with hsp' | hmid'
        · exfalso
          obtain ⟨s, -, hs⟩ := harc
          have h2 := Metric.mem_sphere.mp hsp'
          rw [dist_zero_right, ← hs] at h2
          linarith [hball s]
        · rcases hmid' with hcuts' | harc'
          · exact hcuts'
          · exact tgtT_arc_inter_arc_subset_cuts H ⟨harc, harc'⟩
  case false =>
    have hZu : z ∈ Metric.sphere (0:ℂ) 1 ∪ (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
        Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ ∪ tgtT_arcImg γ.γ (H.θ₁ - 2*Real.pi) H.θ₂) := by
      rw [← hτ]
      exact Work.SphereJordan.tgtUpB_false_mem_trace S H.ht₁s₁.le H.ht₂s₂.le H.hθ' τ
    have hZd : z ∈ Metric.sphere (0:ℂ) 1 ∪ (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
        Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ ∪ tgtT_arcImg γ.γ H.θ₂ H.θ₁) := by
      rw [← hτ']
      exact Work.SphereJordan.tgtDnB_false_mem_trace S H.ht₁s₁.le H.ht₂s₂.le H.hθ τ'
    rcases hZu with hsp | hmid
    · rcases hZd with hsp' | hmid'
      · have hnu : ‖z‖ = 1 := by
          have h2 := Metric.mem_sphere.mp hsp
          rwa [dist_zero_right] at h2
        have hnd : ‖z‖ = 1 := by
          have h2 := Metric.mem_sphere.mp hsp'
          rwa [dist_zero_right] at h2
        have h1 : z ∈ Work.Smooth.SphereJordan.upArc S ∪
            (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
              Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
          rw [← hτ]
          exact tgtT_tgtUpB_sphere_upArc H false τ (by rw [hτ]; exact hnu)
        have h2 : z ∈ Work.Smooth.SphereJordan.downArc S ∪
            (Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪
              Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂) := by
          rw [← hτ']
          exact tgtT_tgtDnB_sphere_downArc H false τ' (by rw [hτ']; exact hnd)
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact tgtT_upArc_inter_downArc_subset_cuts S H.hout₁ H.hout₂ H.ht₁s₁.le H.ht₂s₂.le ⟨h1, h2⟩
          · exact h2
        · exact h1
      · rcases hmid' with hcuts' | harc'
        · exact hcuts'
        · exfalso
          obtain ⟨s, -, hs⟩ := harc'
          have h2 := Metric.mem_sphere.mp hsp
          rw [dist_zero_right, ← hs] at h2
          linarith [hball s]
    · rcases hmid with hcuts | harc
      · exact hcuts
      · rcases hZd with hsp' | hmid'
        · exfalso
          obtain ⟨s, -, hs⟩ := harc
          have h2 := Metric.mem_sphere.mp hsp'
          rw [dist_zero_right, ← hs] at h2
          linarith [hball s]
        · rcases hmid' with hcuts' | harc'
          · exact hcuts'
          · exact tgtT_arc_inter_arc_subset_cuts H ⟨harc', harc⟩

theorem tgtT_norm_one_mem_upArc_or_downArc (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ}
    (hz : ‖z‖ = 1) :
    z ∈ Work.Smooth.SphereJordan.upArc S ∨ z ∈ Work.Smooth.SphereJordan.downArc S := by
  rcases le_total 0 ((z / Work.Smooth.SphereJordan.cutDir S).im) with hh | hh
  · exact Or.inl ⟨hz, hh⟩
  · exact Or.inr ⟨hz, hh⟩

theorem tgtT_isClosed_annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    IsClosed (Work.Smooth.SphereJordan.annulus S) :=
  Metric.isClosed_closedBall.sdiff S.isOpen_V

theorem tgtT_upPC_V_subset_annulus' (H : SpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b)) (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.annulus S :=
  Work.Smooth.SphereJordan.tgtT_upCurve_V_subset_annulus S hball b H.θ₁ H.θ₂ H.hout₁ H.hout₂
    H.ht₁ H.ht₁s₁ H.ht₂ H.ht₂s₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂ T hVU

theorem tgtT_dnPC_V_subset_annulus' (H : SpanHyp h hs hball S) (b : Bool)
    (T : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b)) (hVU : S.V ⊆ T.U) :
    T.V ⊆ Work.Smooth.SphereJordan.annulus S :=
  Work.Smooth.SphereJordan.tgtT_dnCurve_V_subset_annulus S hball b H.θ₁ H.θ₂ H.hout₁ H.hout₂
    H.ht₁ H.ht₁s₁ H.ht₂ H.ht₂s₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂ T hVU

theorem tgtT_annulus_offTrace_exclusive (H : SpanHyp h hs hball S) (b : Bool)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b)) {z : ℂ}
    (hz : z ∈ Work.Smooth.SphereJordan.annulus S)
    (hzu : z ∉ (H.upPC b).trace) (hzd : z ∉ (H.dnPC b).trace) :
    (z ∈ T_up.V ∧ z ∉ T_dn.V) ∨ (z ∈ T_dn.V ∧ z ∉ T_up.V) := by
  have hzle : ‖z‖ ≤ 1 := by
    have h := hz.1
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hzlt : ‖z‖ < 1 := by
    rcases lt_or_eq_of_le hzle with h | h
    · exact h
    · exfalso
      rcases tgtT_norm_one_mem_upArc_or_downArc S h with hc | hc
      · exact hzu (tgtT_upArc_subset_trace_up H b hc)
      · exact hzd (tgtT_downArc_subset_trace_dn H b hc)
  have hzγ : z ∉ γ.trace := by
    intro hc
    rcases tgtT_gamma_trace_subset_arcs (γ := γ) (θ₁ := H.θ₁) (θ₂ := H.θ₂) hc with harc | harc
    · cases b
      · exact hzd (tgtT_arcA_subset_trace_dn H harc)
      · exact hzu (tgtT_arcA_subset_trace_up H harc)
    · cases b
      · exact hzu (tgtT_arcB_subset_trace_up H harc)
      · exact hzd (tgtT_arcB_subset_trace_dn H harc)
  have hw0 : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z = 0 := by
    by_contra hne
    exact hz.2 ((Work.SphereJordan.mem_V_iff_windNumber_ne_zero S).mpr hne)
  have hsum : Work.Smooth.SphereJordan.windNumber (H.upPC b).γ (H.upPC b).cont z
      + Work.Smooth.SphereJordan.windNumber (H.dnPC b).γ (H.dnPC b).cont z = 1 := by
    cases b
    · have hh := tgtT_windSum_false H hzlt hzγ hzu hzd
      rw [hw0] at hh
      simpa using hh
    · have hh := tgtT_windSum_true H hzlt hzγ hzu hzd
      rw [hw0] at hh
      simpa using hh
  by_cases hVu : z ∈ T_up.V
  · refine Or.inl ⟨hVu, fun hVd => ?_⟩
    have hu : Work.Smooth.SphereJordan.windNumber (H.upPC b).γ (H.upPC b).cont z ≠ 0 :=
      (Work.SphereJordan.mem_V_iff_windNumber_ne_zero T_up).mp hVu
    have hd : Work.Smooth.SphereJordan.windNumber (H.dnPC b).γ (H.dnPC b).cont z ≠ 0 :=
      (Work.SphereJordan.mem_V_iff_windNumber_ne_zero T_dn).mp hVd
    obtain ⟨k, hk⟩ := Work.SphereJordan.odd_windNumber_of_ne_zero T_up hu
    obtain ⟨l, hl⟩ := Work.SphereJordan.odd_windNumber_of_ne_zero T_dn hd
    omega
  · refine Or.inr ⟨?_, hVu⟩
    have h0 : Work.Smooth.SphereJordan.windNumber (H.upPC b).γ (H.upPC b).cont z = 0 := by
      by_contra hne
      exact hVu ((Work.SphereJordan.mem_V_iff_windNumber_ne_zero T_up).mpr hne)
    have h1 : Work.Smooth.SphereJordan.windNumber (H.dnPC b).γ (H.dnPC b).cont z = 1 := by
      linarith
    exact (Work.SphereJordan.mem_V_iff_windNumber_ne_zero T_dn).mpr (by rw [h1]; norm_num)

theorem tgtT_upPC_V_inter_dnPC_V (H : SpanHyp h hs hball S) (b : Bool)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b))
    (hb : S.V ⊆ T_up.U ∧ S.V ⊆ T_dn.U) : T_up.V ∩ T_dn.V = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hzA : z ∈ Work.Smooth.SphereJordan.annulus S :=
    tgtT_upPC_V_subset_annulus' H b T_up hb.1 hz1
  have hzu : z ∉ (H.upPC b).trace := by
    have hsub : T_up.V ⊆ ((H.upPC b).trace)ᶜ := by
      rw [← T_up.union_eq]; exact Set.subset_union_right
    exact hsub hz1
  have hzd : z ∉ (H.dnPC b).trace := by
    have hsub : T_dn.V ⊆ ((H.dnPC b).trace)ᶜ := by
      rw [← T_dn.union_eq]; exact Set.subset_union_right
    exact hsub hz2
  rcases tgtT_annulus_offTrace_exclusive H b T_up T_dn hzA hzu hzd with ⟨-, hneg⟩ | ⟨-, hneg⟩
  · exact hneg hz2
  · exact hneg hz1

theorem tgtT_tilingOfPairing (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.SpanHyp h hs hball S) (b : Bool)
    (T_up : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC b))
    (T_dn : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC b))
    (hb : S.V ⊆ T_up.U ∧ S.V ⊆ T_dn.U) :
    closure T_up.V ∪ closure T_dn.V = Work.Smooth.SphereJordan.annulus S ∧
      closure T_up.V ∩ closure T_dn.V =
        Work.Smooth.SphereJordan.cut₁ S H.t₁ H.s₁ ∪ Work.Smooth.SphereJordan.cut₂ S H.t₂ H.s₂ := by
  have hVdisj : T_up.V ∩ T_dn.V = ∅ := tgtT_upPC_V_inter_dnPC_V H b T_up T_dn hb
  have hVcl : T_up.V ∩ closure T_dn.V = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨ε, hε, hballε⟩ := Metric.mem_nhds_iff.mp (T_up.isOpen_V.mem_nhds hz1)
    obtain ⟨w, hwV, hwε⟩ := Metric.mem_closure_iff.mp hz2 ε hε
    exact (Set.eq_empty_iff_forall_notMem.mp hVdisj) w
      ⟨hballε ((Metric.mem_ball).mpr (by simpa [dist_comm] using hwε)), hwV⟩
  have hVcl' : closure T_up.V ∩ T_dn.V = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨ε, hε, hballε⟩ := Metric.mem_nhds_iff.mp (T_dn.isOpen_V.mem_nhds hz2)
    obtain ⟨w, hwV, hwε⟩ := Metric.mem_closure_iff.mp hz1 ε hε
    exact (Set.eq_empty_iff_forall_notMem.mp hVdisj) w
      ⟨hwV, hballε ((Metric.mem_ball).mpr (by simpa [dist_comm] using hwε))⟩
  constructor
  · refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
    · exact closure_minimal (tgtT_upPC_V_subset_annulus' H b T_up hb.1) (tgtT_isClosed_annulus S)
    · exact closure_minimal (tgtT_dnPC_V_subset_annulus' H b T_dn hb.2) (tgtT_isClosed_annulus S)
    · intro z hz
      by_cases hzu : z ∈ (H.upPC b).trace
      · exact Or.inl (by rw [Work.Smooth.SphereJordan.closure_V_eq T_up]; exact Or.inr hzu)
      · by_cases hzd : z ∈ (H.dnPC b).trace
        · exact Or.inr (by rw [Work.Smooth.SphereJordan.closure_V_eq T_dn]; exact Or.inr hzd)
        · rcases tgtT_annulus_offTrace_exclusive H b T_up T_dn hz hzu hzd with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact Or.inl (subset_closure h1)
          · exact Or.inr (subset_closure h1)
  · refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      have hzA : z ∈ Work.Smooth.SphereJordan.annulus S :=
        closure_minimal (tgtT_upPC_V_subset_annulus' H b T_up hb.1) (tgtT_isClosed_annulus S) hz.1
      have hc1 := hz.1
      rw [Work.Smooth.SphereJordan.closure_V_eq T_up] at hc1
      have hc2 := hz.2
      rw [Work.Smooth.SphereJordan.closure_V_eq T_dn] at hc2
      have hut : z ∈ (H.upPC b).trace := by
        by_contra hzu
        have hv1 : z ∈ T_up.V := hc1.resolve_right hzu
        have hzd : z ∉ (H.dnPC b).trace := by
          intro hzd'
          have hcl : z ∈ closure T_dn.V := by
            rw [Work.Smooth.SphereJordan.closure_V_eq T_dn]; exact Or.inr hzd'
          exact (Set.eq_empty_iff_forall_notMem.mp hVcl) z ⟨hv1, hcl⟩
        have hv2 : z ∈ T_dn.V := hc2.resolve_right hzd
        rcases tgtT_annulus_offTrace_exclusive H b T_up T_dn hzA hzu hzd with ⟨-, hneg⟩ | ⟨-, hneg⟩
        · exact hneg hv2
        · exact hneg hv1
      have hdt : z ∈ (H.dnPC b).trace := by
        by_contra hzd
        have hv2 : z ∈ T_dn.V := hc2.resolve_right hzd
        have hzu : z ∉ (H.upPC b).trace := by
          intro hzu'
          have hcl : z ∈ closure T_up.V := by
            rw [Work.Smooth.SphereJordan.closure_V_eq T_up]; exact Or.inr hzu'
          exact (Set.eq_empty_iff_forall_notMem.mp hVcl') z ⟨hcl, hv2⟩
        have hv1 : z ∈ T_up.V := hc1.resolve_right hzu
        rcases tgtT_annulus_offTrace_exclusive H b T_up T_dn hzA hzu hzd with ⟨-, hneg⟩ | ⟨-, hneg⟩
        · exact hneg hv2
        · exact hneg hv1
      exact tgtT_trace_inter_trace_subset_cuts H b ⟨hut, hdt⟩
    · intro z hz
      have h1 : z ∈ (H.upPC b).trace :=
        Work.Smooth.SphereJordan.tgtT_cuts_subset_trace_up S hball b H.θ₁ H.θ₂ H.hout₁ H.hout₂
          H.ht₁s₁ H.ht₂s₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂ hz
      have h2 : z ∈ (H.dnPC b).trace :=
        Work.Smooth.SphereJordan.tgtT_cuts_subset_trace_dn S hball b H.θ₁ H.θ₂ H.hout₁ H.hout₂
          H.ht₁s₁ H.ht₂s₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂ hz
      exact ⟨by rw [Work.Smooth.SphereJordan.closure_V_eq T_up]; exact Or.inr h1,
        by rw [Work.Smooth.SphereJordan.closure_V_eq T_dn]; exact Or.inr h2⟩


end

end Work.SphereJordan
