/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the pointwise `ℋ⁴`-supremum bound in the interior class

Two self-contained ingredients of the design-document lemma `SupQ` (§3.3 L-N4.5, the
`SmoothQuad`-version of Elgindi's Corollary `SecondDerivativesBounded`):

* `hardyZQ_lintegral`: the radial Hardy inequality of `Work.FTS.H2.HQ.HardyZQ` in `lintegral`
  (i.e. without a per-`θ` integrability hypothesis) form, for a `C¹` function on `(0,∞)`
  decaying at `+∞`;
* `exists_min_le_avg`: for a nonnegative function `φ` on `(0,π/2)` with finite integral there is
  `θ₀ ∈ (0,π/2)` with `φ θ₀ ≤ (2/π)∫_{Iθ} φ` (no continuity on the closed interval is needed;
  the values at the endpoints are irrelevant).

Both rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T2Qaux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial Hardy inequality in `lintegral` form -/

/-- **The radial Hardy inequality in `lintegral` form.**  For a function `v` of class `C¹` on
`(0,∞)` with `v → 0` at `+∞`,

  `(v z)² ≤ ∫⁻_s (s · v'(s))² w(s)²`   for every `z > 0`,

where `w(s) = (1+s)²/s²`.  No integrability hypothesis is needed: if the `lintegral` is `⊤`
the claim is trivial, and otherwise the weighted square is integrable and the classical
(Hardy) inequality `Work.FTS.H2.HQ.HardyZQ` applies. -/
theorem hardyZQ_lintegral {v : ℝ → ℝ} (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Tendsto v atTop (𝓝 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((v z) ^ 2) ≤ ∫⁻ s in Work.Spaces.Iz,
      ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  -- continuity of `deriv v` on `(0,∞)`
  have hdvcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) := by
    have h := hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
    exact h.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm
  have hcont : ContinuousOn (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hw : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0 : ℝ)) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) fun x hx => ?_
      have hx0 : x ≠ 0 := ne_of_gt hx
      exact pow_ne_zero 2 hx0
    exact ((continuousOn_id.mul hdvcont).pow 2).mul (hw.pow 2)
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have h1 : AEStronglyMeasurable
        (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have h2 : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
      exact (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
    rwa [h2]
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2 :=
    Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases htop : (∫⁻ s in Work.Spaces.Iz,
      ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)) = ⊤
  · rw [htop]; exact le_top
  · have hint : IntegrableOn (fun s : ℝ => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp htop
    have hH := Work.FTS.H2.HQ.HardyZQ v hcd hdec hint z (Set.mem_Ioi.mpr hz)
    calc ENNReal.ofReal ((v z) ^ 2)
        ≤ ENNReal.ofReal (∫ s, (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2
            ∂(volume.restrict Work.Spaces.Iz)) := ENNReal.ofReal_le_ofReal hH
      _ = ∫⁻ s in Work.Spaces.Iz,
            ENNReal.ofReal ((s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn

/-! ## A minimum below the average on the open interval -/

/-- Over the open interval `(0,π/2)` (of measure `π/2`) some point is below the average:
for `φ ≥ 0` a.e. on `Iθ` with `∫_{Iθ} φ < ∞` there is `θ₀ ∈ (0,π/2)` with
`φ θ₀ ≤ (2/π)·∫_{Iθ} φ`.  Only the values strictly inside the interval are constrained. -/
theorem exists_min_le_avg {φ : ℝ → ℝ} (hint : Integrable φ (volume.restrict Work.Spaces.Iθ))
    (hm : AEStronglyMeasurable φ (volume.restrict Work.Spaces.Iθ))
    (hnn : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ φ σ) :
    ∃ θ₀ ∈ Set.Ioo (0 : ℝ) (π / 2),
      φ θ₀ ≤ (2 / Real.pi) * ∫ σ in Work.Spaces.Iθ, φ σ := by
  by_contra h
  push_neg at h
  set c : ℝ := (2 / Real.pi) * ∫ σ in Work.Spaces.Iθ, φ σ with hc
  have hcpos : 0 < 2 / Real.pi := by positivity
  -- `φ - c > 0` on `(0,π/2)`
  have hpos : ∀ σ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < φ σ - c := fun σ hσ => sub_pos.mpr (h σ hσ)
  have hnn_on : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] fun σ => φ σ - c := by
    have h1 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (π / 2))] fun σ => φ σ - c :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => le_of_lt (hpos σ hσ)
    rwa [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  have hint' : Integrable (fun σ => φ σ - c) (volume.restrict Work.Spaces.Iθ) :=
    hint.sub (integrable_const c)
  have hsupp : Set.Ioo (0 : ℝ) (π / 2) ⊆ Function.support fun σ => φ σ - c := fun σ hσ =>
    ne_of_gt (hpos σ hσ)
  have hμpos : 0 < (volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
      show Set.Ioo (0 : ℝ) (π / 2) ∩ Work.Spaces.Iθ = Set.Ioo (0 : ℝ) (π / 2) from
        Set.inter_eq_left.mpr fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩,
      Real.volume_Ioo]
    simp only [sub_zero, ENNReal.ofReal_pos]
    positivity
  have hμ : 0 < (volume.restrict Work.Spaces.Iθ) (Function.support fun σ => φ σ - c) :=
    lt_of_lt_of_le hμpos (MeasureTheory.measure_mono hsupp)
  have hposint : 0 < ∫ σ in Work.Spaces.Iθ, (φ σ - c) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnn_on hint').mpr hμ
  rw [MeasureTheory.integral_sub hint (integrable_const c)] at hposint
  have hconst : ∫ σ in Work.Spaces.Iθ, c = c * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, Work.Spaces.Iθ, MeasureTheory.Measure.real_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul]
    ring
  rw [hconst] at hposint
  have hcval : c * (Real.pi / 2) = ∫ σ in Work.Spaces.Iθ, φ σ := by
    rw [hc]; field_simp
  rw [hcval, sub_self] at hposint
  exact lt_irrefl 0 hposint


/-! ## The `ℋ⁴`-integrand and the iterated `lintegral` of `HkSq` -/

/-- `ofReal (HkSq α 4 f)` is the `z`-outer iterated `lintegral` of
`ofReal (HkIntegrand α 4 f · ·)`; only the two components of `HkMem` are used. -/
theorem ofReal_HkSq_eq_lintegral (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ∫⁻ s in Work.Spaces.Iz, ∫⁻ σ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ) := by
  have hnn1 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      fun s => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ :=
    Eventually.of_forall fun s =>
      integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  have hstep : ENNReal.ofReal (Work.Spaces.HkSq α 4 f)
      = ∫⁻ s in Work.Spaces.Iz,
          ENNReal.ofReal (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s σ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 hnn1
  rw [hstep]
  refine MeasureTheory.lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ici ?_)
  intro s hs
  have hnn2 : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun σ => Work.Spaces.HkIntegrand α 4 f s σ :=
    Eventually.of_forall fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 s (Set.mem_Ici.mpr hs)) hnn2

/-- The closed rectangle `[0,∞) × [0,π/2]` agrees a.e. with the open quadrant
`(0,∞) × (0,π/2)` for the product of Lebesgue measure with itself; the two differences are
contained in the null sets `{0} × ℝ` and `ℝ × {0,π/2}`. -/
theorem ae_eq_quad : (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2) : Set (ℝ × ℝ))
    =ᵐ[volume.prod volume] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hnull2 : volume ({0, π / 2} : Set ℝ) = 0 := by
    rw [show ({0, π / 2} : Set ℝ) = {0} ∪ {π / 2} from rfl,
      measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton (π / 2)⟩
  have hnullA : (volume.prod volume) (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.prod_prod]; simp
  have hnullB : (volume.prod volume) ((Set.univ : Set ℝ) ×ˢ ({0, π / 2} : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.prod_prod, hnull2, mul_zero]
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
        ∪ ((Set.univ : Set ℝ) ×ˢ ({0, π / 2} : Set ℝ))) ?_ ?_
    · rintro p ⟨hp, hnab⟩
      obtain ⟨a, b⟩ := p
      simp only [Set.mem_prod, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioo] at hp hnab
      obtain ⟨ha, hb⟩ := hp
      obtain ⟨hb1, hb2⟩ := hb
      simp only [Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, Set.mem_union]
      rcases not_and_or.mp hnab with h | h
      · left
        exact ⟨le_antisymm (not_lt.mp h) ha, trivial⟩
      · right
        refine ⟨trivial, ?_⟩
        rcases eq_or_lt_of_le hb1 with h0 | h0
        · exact Or.inl (by simpa using h0.symm)
        · rcases eq_or_lt_of_le hb2 with hπ | hlt
          · exact Or.inr (by simpa using hπ)
          · exact absurd ⟨h0, hlt⟩ h
    · rw [measure_union_null_iff]; exact ⟨hnullA, hnullB⟩
  · have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
        ⊆ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (π / 2)) := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [Set.mem_prod, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioo] at hb ⊢
      obtain ⟨hb1, hb2⟩ := hb
      exact ⟨le_of_lt ha, le_of_lt hb1, le_of_lt (by linarith [hb2, Real.pi_pos])⟩
    rw [Set.sdiff_eq_empty.mpr hsub]
    simp

/-- The uncurried `ℋ⁴`-integrand is a.e. strongly measurable for the product of the two
interval measures (taken in the `z`-first order). -/
theorem aesm_HkIntegrand_prod (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f) :
    AEMeasurable (Function.uncurry fun s σ : ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsq)
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      ((volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable (by measurability)
  have hmeq : (volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact (MeasureTheory.Measure.restrict_congr_set (by
      rw [show ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
          = (Set.Ici 0 ×ˢ Set.Icc 0 (π / 2)) from rfl]
      exact ae_eq_quad)).symm
  rw [hmeq] at haesm
  exact haesm.aemeasurable

/-- **The `θ`-outer form of `HkSq`.**  The iterated `lintegral` of `ofReal (HkIntegrand)` in
the `θ`-outer order is `ofReal (HkSq α 4 f)`. -/
theorem lintegral_HkSq_theta_outer (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫⁻ σ in Work.Spaces.Iθ, ∫⁻ s in Work.Spaces.Iz,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := by
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (f := fun s σ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f s σ))
    (aesm_HkIntegrand_prod α f hsq)
  rw [← hswap, ← ofReal_HkSq_eq_lintegral α f hmem]

end Work.FTS.H2.T2Qaux
