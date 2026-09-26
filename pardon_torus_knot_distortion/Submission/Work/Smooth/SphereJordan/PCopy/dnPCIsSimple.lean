import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetCurves

/-!
# The lower four-arc curve `H.pcdnPC b` is a simple closed curve

`Work.SphereJordan.pcdnPCIsSimple`: for the two-pccuts configuration `H : pcSpanHyp h hs hball S` and any
flag `b`, the four-arc curve `H.pcdnPC b` is a simple closed plane curve.

This is the `pcdnPC` mirror of the proved `Work.SphereJordan.pctgtUpPC_isSimple`
(`Submission/Work/SphereJordan/pctgtUpPC_isSimple.lean`).  The four arcs of `pctgtDnB`, in the order in
which the parameter `σ ∈ [0, 2π)` meets them, are

  `pcsrcOuterDn` (the lower outer semicircle, from `-pccutDir S` to `pccutDir S`),
  `pctgtCut₁`    (the first cut, inward from `pccutDir S` to `γ θ₁`),
  the `γ`-arc from `γ θ₁` to `γ θ₂`,
  `pctgtCut₂`    (the second cut, outward from `γ θ₂` to `-pccutDir S`),

so the junctions are `-pccutDir S, pccutDir S, γ θ₁, γ θ₂`.  The generic four-arc lemma
`Work.SphereJordan.pcinjOn_four_arcs`, the arc injectivities `pctgtCut₁_injOn`, `pctgtCut₂_injOn`,
`pcgammaArc_injOn` and the disjointness lemma `pcdisj₂₄` are reused verbatim from
`pctgtUpPC_isSimple.lean`; the remaining disjointness facts are proved here.

The reason this module exists: the ready-made `Work.Smooth.SphereJordan.tgtDnB_injOn`
(`annulusSchoenfliesCore.lean`) proves the same statement but lives in a module that cannot be
imported alongside `pccoreAuxTwoCuts` (both declare `Work.Smooth.SphereJordan.pccuts_subset_trace_up`).
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## The lower outer semicircle -/

/-- The lower outer semicircle, as a multiple of the unit direction `pccutDir S`. -/
theorem pcdnPCS_srcOuter_cp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    Work.Smooth.SphereJordan.pcsrcOuterDn S x =
      -Work.Smooth.SphereJordan.pccutDir S *
        ((Work.Smooth.Jordan.circlePoint (Real.pi * x) : Work.Smooth.Jordan.Disc) : ℂ) := by
  rw [Work.Smooth.SphereJordan.pcsrcOuterDn, Work.Smooth.Jordan.circlePoint_coe]

/-- The lower outer semicircle lies on the unit circle. -/
theorem pcdnPCS_norm_srcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖Work.Smooth.SphereJordan.pcsrcOuterDn S x‖ = 1 := by
  rw [pcdnPCS_srcOuter_cp, norm_mul, norm_neg, pcnorm_cp, Work.Smooth.SphereJordan.pcnorm_cutDir,
    mul_one]

/-- The lower outer semicircle is injective on `[0,1]`. -/
theorem pcdnPCS_srcOuter_injOn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Set.InjOn (Work.Smooth.SphereJordan.pcsrcOuterDn S) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  rw [pcdnPCS_srcOuter_cp, pcdnPCS_srcOuter_cp] at hxy
  have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * x) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((Work.Smooth.Jordan.circlePoint (Real.pi * y) : Work.Smooth.Jordan.Disc) : ℂ) :=
    mul_left_cancel₀ (neg_ne_zero.mpr (Work.Smooth.SphereJordan.pccutDir_ne_zero S)) hxy
  have hpx : Real.pi * x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le hx.1, by nlinarith [Real.pi_pos, hx.1, hx.2]⟩
  have hpy : Real.pi * y ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le hy.1, by nlinarith [Real.pi_pos, hy.1, hy.2]⟩
  have h3 : Real.pi * x = Real.pi * y :=
    Work.Smooth.SphereJordan.injOn_circlePoint hpx hpy (Subtype.ext h2)
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) h3

/-- The lower outer semicircle is disjoint from the curve `γ` (which lies in the open unit disc). -/
theorem pcdnPCS_srcOuter_ne_gamma (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (a z : ℝ) :
    Work.Smooth.SphereJordan.pcsrcOuterDn S a ≠ γ.γ z := by
  intro h
  have h1 := pcdnPCS_norm_srcOuterDn S a
  rw [h] at h1
  have h2 := hball z
  linarith

/-! ## Disjointness of the four arcs of `pctgtDnB` -/

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The lower outer semicircle meets the first cut only at the common junction `pccutDir S`. -/
theorem pcdnPCS_disj₁₂ (H : pcSpanHyp h hs hball S) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterDn S a =
        Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ b → a = 1 ∧ b = 0 := by
  intro a ha b hb heq
  rw [pcdnPCS_srcOuter_cp S a, pctgtCut₁_nf S H.hout₁ b] at heq
  have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
      -(((1 - b * (H.s₁ - H.t₁) : ℝ)) : ℂ) := by
    have h3 : -Work.Smooth.SphereJordan.pccutDir S *
        ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
        -Work.Smooth.SphereJordan.pccutDir S * (-(((1 - b * (H.s₁ - H.t₁) : ℝ)) : ℂ)) := by
      rw [heq]; ring
    exact mul_left_cancel₀ (neg_ne_zero.mpr (Work.Smooth.SphereJordan.pccutDir_ne_zero S)) h3
  have hnorm : |1 - b * (H.s₁ - H.t₁)| = 1 := by
    have hh := congrArg (fun z : ℂ => ‖z‖) h2
    rw [pcnorm_cp, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.symm
  have hle : 1 - b * (H.s₁ - H.t₁) ≤ 1 := by
    have h1 : 0 ≤ b * (H.s₁ - H.t₁) := mul_nonneg hb.1 (by linarith [H.ht₁s₁])
    linarith
  have hgt : -1 < 1 - b * (H.s₁ - H.t₁) := by
    have h1 : b * (H.s₁ - H.t₁) ≤ H.s₁ - H.t₁ :=
      mul_le_of_le_one_left (by linarith [H.ht₁s₁]) hb.2
    linarith [h1, pcdiff_cuts_lt_two H]
  have hb0 : b = 0 := by
    have hc : 1 - b * (H.s₁ - H.t₁) = 1 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with hh | hh
      · exact hh
      · linarith
    have h1 : b * (H.s₁ - H.t₁) = 0 := by linarith
    exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (ne_of_lt H.ht₁s₁).symm)
  refine ⟨?_, hb0⟩
  subst hb0
  have h4 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((Work.Smooth.Jordan.circlePoint Real.pi : Work.Smooth.Jordan.Disc) : ℂ) := by
    rw [h2, pccp_pi]
    norm_num
  have hpa : Real.pi * a ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le ha.1, by nlinarith [Real.pi_pos, ha.1, ha.2]⟩
  have hpπ : Real.pi ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have h5 : Real.pi * a = Real.pi :=
    Work.Smooth.SphereJordan.injOn_circlePoint hpa hpπ (Subtype.ext h4)
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) (by simpa using h5)

/-- The lower outer semicircle never meets the γ-arc (which lies in the open disc). -/
theorem pcdnPCS_srcOuter_ne_gammaArc (_H : pcSpanHyp h hs hball S) (A K : ℝ) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterDn S a ≠ γ.γ (A + b * K) :=
  fun a _ b _ => pcdnPCS_srcOuter_ne_gamma S hball a (A + b * K)

/-- The lower outer semicircle meets the second cut only at the junction `-pccutDir S`. -/
theorem pcdnPCS_disj₁₄ (H : pcSpanHyp h hs hball S) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterDn S a =
        Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ b → b = 0 := by
  intro a ha b hb heq
  rw [pcdnPCS_srcOuter_cp S a, pctgtCut₂_nf S H.hout₂ b] at heq
  have hnorm : |b * (H.s₂ - H.t₂) - 1| = 1 := by
    have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
        -(((b * (H.s₂ - H.t₂) - 1 : ℝ)) : ℂ) := by
      have h3 : -Work.Smooth.SphereJordan.pccutDir S *
          ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
          -Work.Smooth.SphereJordan.pccutDir S * (-(((b * (H.s₂ - H.t₂) - 1 : ℝ)) : ℂ)) := by
        rw [heq]; ring
      exact mul_left_cancel₀ (neg_ne_zero.mpr (Work.Smooth.SphereJordan.pccutDir_ne_zero S)) h3
    have hh := congrArg (fun z : ℂ => ‖z‖) h2
    rw [pcnorm_cp, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.symm
  have hge : -1 ≤ b * (H.s₂ - H.t₂) - 1 := by
    have h1 : 0 ≤ b * (H.s₂ - H.t₂) := mul_nonneg hb.1 (by linarith [H.ht₂s₂])
    linarith
  have hlt : b * (H.s₂ - H.t₂) - 1 < 1 := by
    have h1 : b * (H.s₂ - H.t₂) ≤ H.s₂ - H.t₂ :=
      mul_le_of_le_one_left (by linarith [H.ht₂s₂]) hb.2
    linarith [h1, pcs₂_sub_t₂_lt_two H]
  have hcoeff : b * (H.s₂ - H.t₂) - 1 = -1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with hh | hh
    · linarith
    · exact hh
  have h1 : b * (H.s₂ - H.t₂) = 0 := by linarith
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (ne_of_lt H.ht₂s₂).symm)

/-- The first cut meets the γ-arc `x ↦ γ (A + x K)` only at the junction `γ θ₁`, which is its
endpoint `x = 0`. -/
theorem pcdnPCS_cut₁_ne_gammaArc (H : pcSpanHyp h hs hball S) {A K : ℝ}
    (hA : γ.γ A = γ.γ H.θ₁) (hK0 : K ≠ 0) (hK2 : |K| < 2 * Real.pi) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ a = γ.γ (A + w * K) →
        a = 1 ∧ w = 0 := by
  intro a ha w hw heq
  have hmem : γ.γ (A + w * K) ∈ closure S.V := by
    rw [← S.range_e]
    exact ⟨Work.Smooth.Jordan.circlePoint (A + w * K), S.boundary _⟩
  have hσle : H.s₁ + a * (H.t₁ - H.s₁) ≤ H.t₁ := by
    by_contra hcon
    have hlt : H.t₁ < H.s₁ + a * (H.t₁ - H.s₁) := not_le.mp hcon
    refine (H.hmax₁ _ hlt) ?_
    change Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ a ∈ closure S.V
    rw [heq]; exact hmem
  have ha1 : a = 1 := by
    have h1 : (a - 1) * (H.t₁ - H.s₁) ≤ 0 := by nlinarith [hσle]
    have h2 : H.t₁ - H.s₁ < 0 := by linarith [H.ht₁s₁]
    have h3 : 0 ≤ a - 1 := by
      by_contra hcon
      have h4 : 0 < (a - 1) * (H.t₁ - H.s₁) := mul_pos_of_neg_of_neg (not_le.mp hcon) h2
      linarith
    linarith [h3, ha.2]
  refine ⟨ha1, ?_⟩
  have hf2 : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ 1 = γ.γ H.θ₁ := by
    rw [Work.Smooth.SphereJordan.pctgtCut₁]
    have hh : ((H.s₁ + 1 * (H.t₁ - H.s₁) : ℝ) : ℂ) = (H.t₁ : ℂ) := by push_cast; ring
    rw [hh]; exact H.hθ₁.symm
  have hγeq : γ.γ (A + w * K) = γ.γ A := by
    rw [hA, ← hf2, ← ha1]
    exact heq.symm
  have hab : |(A + w * K) - A| < 2 * Real.pi := by
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hw.1]
    calc w * |K| ≤ 1 * |K| := mul_le_mul_of_nonneg_right hw.2 (abs_nonneg K)
      _ = |K| := by ring
      _ < 2 * Real.pi := hK2
  have h4 := Work.SphereJordan.pcinjOn_of_abs_lt hs hab hγeq
  have h5 : w * K = 0 := by linarith
  exact (mul_eq_zero.mp h5).resolve_right hK0

/-- The second cut meets the γ-arc `x ↦ γ (A + x K)` only at the junction `γ θ₂`, which is its
endpoint `x = 1`. -/
theorem pcdnPCS_cut₂_ne_gammaArc (H : pcSpanHyp h hs hball S) {A K : ℝ} (hK0 : K ≠ 0)
    (hKend : A + K = H.θ₂) (hK2 : |K| < 2 * Real.pi) :
    ∀ w ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      γ.γ (A + w * K) = Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ b →
        w = 1 ∧ b = 1 := by
  intro w hw b hb heq
  have hmem : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ b ∈ closure S.V := by
    rw [← heq, ← S.range_e]
    exact ⟨Work.Smooth.Jordan.circlePoint (A + w * K), S.boundary _⟩
  have hσle : H.s₂ + b * (H.t₂ - H.s₂) ≤ H.t₂ := by
    by_contra hcon
    have hlt : H.t₂ < H.s₂ + b * (H.t₂ - H.s₂) := not_le.mp hcon
    refine (H.hmax₂ _ hlt) ?_
    simpa only [Work.Smooth.SphereJordan.pctgtCut₂] using hmem
  have hb1 : b = 1 := by
    have h1 : (H.s₂ - H.t₂) * (1 - b) ≤ 0 := by nlinarith [hσle]
    have h2 : 0 < H.s₂ - H.t₂ := by linarith [H.ht₂s₂]
    have h3 : 1 - b ≤ 0 := nonpos_of_mul_nonpos_right h1 h2
    linarith [h3, hb.2]
  refine ⟨?_, hb1⟩
  have hf4 : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ 1 = γ.γ H.θ₂ := by
    rw [Work.Smooth.SphereJordan.pctgtCut₂]
    have hh : ((H.s₂ + 1 * (H.t₂ - H.s₂) : ℝ) : ℂ) = (H.t₂ : ℂ) := by push_cast; ring
    rw [hh]; exact H.hθ₂.symm
  have haeq : γ.γ (A + w * K) = γ.γ H.θ₂ := by
    rw [hb1] at heq
    rw [hf4] at heq
    exact heq
  have hγeq : γ.γ (A + w * K) = γ.γ (A + 1 * K) := by
    rw [one_mul, hKend]; exact haeq
  have hab : |(A + w * K) - (A + 1 * K)| < 2 * Real.pi := by
    rw [show A + w * K - (A + 1 * K) = (w - 1) * K by ring, abs_mul]
    calc |w - 1| * |K| ≤ 1 * |K| :=
          mul_le_mul_of_nonneg_right (by rw [abs_le]; constructor <;> linarith [hw.1, hw.2])
            (abs_nonneg K)
      _ = |K| := by ring
      _ < 2 * Real.pi := hK2
  have h4 := Work.SphereJordan.pcinjOn_of_abs_lt hs hab hγeq
  have h5 : (w - 1) * K = 0 := by linarith
  have h6 : w - 1 = 0 := (mul_eq_zero.mp h5).resolve_right hK0
  linarith

/-! ## The unfolded lower target curve is injective on one period -/

/-- `γ (θ₁ - 2π) = γ θ₁`. -/
theorem pcdnPCS_gamma_sub_two_pi (H : pcSpanHyp h hs hball S) :
    γ.γ (H.θ₁ - 2 * Real.pi) = γ.γ H.θ₁ := by
  have hp := γ.periodic (H.θ₁ - 2 * Real.pi)
  rw [show H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ from by ring] at hp
  exact hp.symm

theorem pcdnPCS_tgtDnBun_injOn (H : pcSpanHyp h hs hball S) (b : Bool) :
    Set.InjOn (Work.SphereJordan.pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂)
      (Set.Ico 0 (2 * Real.pi)) := by
  have hLneg : H.θ₂ - H.θ₁ < 0 := by linarith [H.hθ]
  have hLabs : |H.θ₂ - H.θ₁| = H.θ₁ - H.θ₂ := by rw [abs_of_neg hLneg]; ring
  have hLlt : H.θ₁ - H.θ₂ < 2 * Real.pi := by linarith [H.hθ']
  have hKpos : 0 < H.θ₂ - H.θ₁ + 2 * Real.pi := by linarith [H.hθ]
  have hKlt : H.θ₂ - H.θ₁ + 2 * Real.pi < 2 * Real.pi := by linarith [H.hθ']
  have hKabs : |H.θ₂ - H.θ₁ + 2 * Real.pi| = H.θ₂ - H.θ₁ + 2 * Real.pi :=
    abs_of_pos hKpos
  cases b
  · refine pcinjOn_four_arcs (F := Work.SphereJordan.pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ false
        H.θ₁ H.θ₂)
      (f₁ := Work.Smooth.SphereJordan.pcsrcOuterDn S)
      (f₂ := Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁)
      (f₃ := fun x : ℝ => γ.γ (H.θ₁ + x * (H.θ₂ - H.θ₁)))
      (f₄ := Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂)
      ?_ ?_ ?_ ?_
      (pcdnPCS_srcOuter_injOn S) (pctgtCut₁_injOn S H.hout₁ (ne_of_lt H.ht₁s₁))
      (pcgammaArc_injOn hs (a := H.θ₁) (L := H.θ₂ - H.θ₁)
        (by intro hh; linarith [hh, H.hθ]) (by rw [hLabs]; exact hLlt))
      (pctgtCut₂_injOn S H.hout₂ (ne_of_lt H.ht₂s₂))
      (pcdnPCS_disj₁₂ H) (pcdnPCS_srcOuter_ne_gammaArc H H.θ₁ (H.θ₂ - H.θ₁)) (pcdnPCS_disj₁₄ H)
      (pcdnPCS_cut₁_ne_gammaArc H (A := H.θ₁) (K := H.θ₂ - H.θ₁) rfl
        (by intro hh; linarith [hh, H.hθ]) (by rw [hLabs]; exact hLlt))
      (fun a ha b hb h => pcdisj₂₄ H b hb a ha h.symm)
      (pcdnPCS_cut₂_ne_gammaArc H (A := H.θ₁) (K := H.θ₂ - H.θ₁)
        (by intro hh; linarith [hh, H.hθ]) (by ring) (by rw [hLabs]; exact hLlt))
    · intro σ hσ; simp only [Work.SphereJordan.pctgtDnBun]; rw [if_pos hσ]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (not_le.mpr h1), if_pos h2]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2), if_neg (not_le.mpr h1), if_pos h2]
      simp
    · intro σ h1; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2),
        if_neg (not_le.mpr (by linarith [h1] : Real.pi < σ)), if_neg (not_le.mpr h1)]
  · refine pcinjOn_four_arcs (F := Work.SphereJordan.pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ true
        H.θ₁ H.θ₂)
      (f₁ := Work.Smooth.SphereJordan.pcsrcOuterDn S)
      (f₂ := Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁)
      (f₃ := fun x : ℝ => γ.γ (H.θ₁ - 2 * Real.pi + x * (H.θ₂ - H.θ₁ + 2 * Real.pi)))
      (f₄ := Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂)
      ?_ ?_ ?_ ?_
      (pcdnPCS_srcOuter_injOn S) (pctgtCut₁_injOn S H.hout₁ (ne_of_lt H.ht₁s₁))
      (pcgammaArc_injOn hs (a := H.θ₁ - 2 * Real.pi) (L := H.θ₂ - H.θ₁ + 2 * Real.pi)
        (by intro hh; linarith [hh, H.hθ]) (by rw [hKabs]; exact hKlt))
      (pctgtCut₂_injOn S H.hout₂ (ne_of_lt H.ht₂s₂))
      (pcdnPCS_disj₁₂ H)
      (pcdnPCS_srcOuter_ne_gammaArc H (H.θ₁ - 2 * Real.pi) (H.θ₂ - H.θ₁ + 2 * Real.pi))
      (pcdnPCS_disj₁₄ H)
      (pcdnPCS_cut₁_ne_gammaArc H (A := H.θ₁ - 2 * Real.pi) (K := H.θ₂ - H.θ₁ + 2 * Real.pi)
        (pcdnPCS_gamma_sub_two_pi H) (by intro hh; linarith [hh, H.hθ])
        (by rw [hKabs]; exact hKlt))
      (fun a ha b hb h => pcdisj₂₄ H b hb a ha h.symm)
      (pcdnPCS_cut₂_ne_gammaArc H (A := H.θ₁ - 2 * Real.pi) (K := H.θ₂ - H.θ₁ + 2 * Real.pi)
        (by intro hh; linarith [hh, H.hθ]) (by ring) (by rw [hKabs]; exact hKlt))
    · intro σ hσ; simp only [Work.SphereJordan.pctgtDnBun]; rw [if_pos hσ]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (not_le.mpr h1), if_pos h2]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2), if_neg (not_le.mpr h1), if_pos h2]
      simp
    · intro σ h1; simp only [Work.SphereJordan.pctgtDnBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2),
        if_neg (not_le.mpr (by linarith [h1] : Real.pi < σ)), if_neg (not_le.mpr h1)]

/-- **The lower four-arc curve is a simple closed plane curve.** -/
theorem pcdnPCIsSimple (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (H : Work.SphereJordan.pcSpanHyp h hs hball S)
    (b : Bool) : (H.pcdnPC b).IsSimple := by
  intro σ₁ h₁ σ₂ h₂ heq
  rw [Work.SphereJordan.pcSpanHyp.pcdnPC_apply, Work.SphereJordan.pcSpanHyp.pcdnPC_apply] at heq
  rw [Work.SphereJordan.pctgtDnB_eq, Work.SphereJordan.pctgtDnB_eq] at heq
  rw [Work.SphereJordan.pcperPt_self h₁, Work.SphereJordan.pcperPt_self h₂] at heq
  exact pcdnPCS_tgtDnBun_injOn H b h₁ h₂ heq

end

end Work.SphereJordan
