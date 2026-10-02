/-
Copyright: Work.MRMT (mandelbar) subproject.

# Well-definedness of the principal solution: two records for the same coefficient agree

The record `PrincipalData μ` of a principal solution of the Beltrami equation is the data
produced by the Ahlfors–Bers limit construction: a homeomorphism `φ` with the normalisation
`φ z = z + O(1/‖z‖)`, together with approximating coefficients `μn n` (smooth, compactly
supported, `‖μn n‖ ≤ k < 1`, `μn n → μ` a.e.) and `C¹`-diffeomorphic solutions `Fn n` of the
Beltrami equation for `μn n`, converging locally uniformly to `φ`.

If two records for the *same* coefficient `μ` existed with different `φ`, the principal solution
would not be well defined.  The present file proves that this cannot happen:

`Work.MRMT.Found.records_agree`: `d.φ = d'.φ` for any two `d d' : PrincipalData μ`.

The proof uses the (already proved) uniqueness theorem `Work.MRMT.QC.eq_zero_of_beltrami_of_decay`:
a continuous solution `h` of a Beltrami equation `∂̄h = μ ∂h` with `‖μ‖ ≤ k < 1` a.e. and with
decay `h z = O(1/‖z‖)` vanishes.  It applies to `h = d.φ - d'.φ`, once the weak (distributional)
Wirtinger derivatives of `φ` are identified.  Those are obtained from the record itself:

* the `L²_loc` limit `D` of `∂(Fn n)`, which exists by the field `PrincipalData.dz_tendsto`,
  is a weak `∂`-derivative of `φ` (`Work.MRMT.Found.weakDeriv_of_approx`);
* `μ · D` is a weak `∂̄`-derivative of `φ`, because `∂̄(Fn n) = μn n · ∂(Fn n)` and `μn n → μ`
  a.e. with a uniform bound (`recD_dzbar_tendsto`).

Note that the statement carries *no* hypothesis on `μ` (in particular `μ` need not have bounded
support), so the arguments are built from the fields of the record alone; the a.e. bound
`‖μ‖ ≤ d.k` and the a.e. strong measurability of `μ` are derived from `d.tendsto_μn`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.weakDeriv_of_approx
import Submission.Work.MRMT.Found.PLWD2.eLpNorm_mul_sub_tendsto
import Submission.Work.MRMT.QC.principal_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Elementary facts about a record -/

/-- The coefficient of a record is a.e. strongly measurable (it is an a.e. limit of the
continuous approximants `μn n`). -/
theorem record_aestronglyMeasurable {μ : ℂ → ℂ} (d : PrincipalData μ) :
    AEStronglyMeasurable μ (volume : Measure ℂ) :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (d.contDiff_μn n).continuous.aestronglyMeasurable) d.tendsto_μn

/-- The coefficient of a record is a.e. bounded by the dilatation bound of the record. -/
theorem record_norm_le {μ : ℂ → ℂ} (d : PrincipalData μ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ d.k := by
  filter_upwards [d.tendsto_μn] with z hz
  exact le_of_tendsto hz.norm (Eventually.of_forall fun n => d.norm_μn n z)

/-- The dilatation bound of a record is non-negative. -/
theorem record_k_nonneg {μ : ℂ → ℂ} (d : PrincipalData μ) : 0 ≤ d.k :=
  (norm_nonneg _).trans (d.norm_μn 0 0)

/-! ## The `L²_loc` limit `recD d` of `∂(F n)` and its basic properties -/

/-- The `L²_loc` limit of `∂(F n)` supplied by the record. -/
noncomputable def recD {μ : ℂ → ℂ} (d : PrincipalData μ) : ℂ → ℂ :=
  Classical.choose d.dz_tendsto

/-- The defining property of `recD d`. -/
theorem recD_spec {μ : ℂ → ℂ} (d : PrincipalData μ) :
    ∀ K : Set ℂ, IsCompact K →
      Tendsto (fun n => eLpNorm (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - recD d z) 2
        ((volume : Measure ℂ).restrict K)) atTop (𝓝 0) :=
  Classical.choose_spec d.dz_tendsto

/-- `∂(F n)` is square integrable on every closed ball (it is continuous). -/
theorem memLp_dz_Fn_closedBall {μ : ℂ → ℂ} (d : PrincipalData μ) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) 2
      ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) := by
  haveI : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  have hc : Continuous (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z) :=
    continuous_dz_of_contDiff_one (d.contDiff_Fn n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable (max M 0) ?_
  have hcl : IsClosed (Metric.closedBall (0 : ℂ) R) := (isCompact_closedBall (0 : ℂ) R).isClosed
  rw [MeasureTheory.ae_restrict_iff' hcl.measurableSet]
  filter_upwards with z hz
  exact (hM z hz).trans (le_max_left _ _)

/-- `recD d` is square integrable on every closed ball. -/
theorem memLp_recD_closedBall {μ : ℂ → ℂ} (d : PrincipalData μ) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (recD d) 2 ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) :=
  PLWD2.memLp_of_tendsto_eLpNorm_two_sub (fun n => memLp_dz_Fn_closedBall d n hR)
    (recD_spec d (Metric.closedBall 0 R) (isCompact_closedBall 0 R))

/-- `recD d` is square integrable on every compact set. -/
theorem memLp_recD_restrict_compact {μ : ℂ → ℂ} (d : PrincipalData μ) {K : Set ℂ}
    (hK : IsCompact K) : MemLp (recD d) 2 ((volume : Measure ℂ).restrict K) := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hsub : K ⊆ Metric.closedBall 0 (max C 0) := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC z hz).trans (le_max_left _ _)
  exact (memLp_recD_closedBall d (le_max_right C 0)).mono_measure
    (Measure.restrict_mono (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) hsub le_rfl)

/-- `recD d` is a.e. strongly measurable on the whole plane. -/
theorem aestronglyMeasurable_recD {μ : ℂ → ℂ} (d : PrincipalData μ) :
    AEStronglyMeasurable (recD d) (volume : Measure ℂ) := by
  have h := AEStronglyMeasurable.iUnion (μ := (volume : Measure ℂ)) (f := recD d)
    (s := fun n : ℕ => Metric.ball 0 (n : ℝ)) (fun n => by
      have hsub : Metric.ball (0 : ℂ) (n : ℝ) ⊆ Metric.closedBall (0 : ℂ) (n : ℝ) :=
        Metric.ball_subset_closedBall
      have hle : ((volume : Measure ℂ).restrict (Metric.ball 0 (n : ℝ))) ≤
          ((volume : Measure ℂ).restrict (Metric.closedBall 0 (n : ℝ))) :=
        Measure.restrict_mono (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) hsub le_rfl
      exact ((memLp_recD_closedBall d (Nat.cast_nonneg n)).mono_measure hle).aestronglyMeasurable)
  rwa [Metric.iUnion_ball_nat, Measure.restrict_univ] at h

/-- `recD d` is locally square integrable. -/
theorem memL2Loc_recD {μ : ℂ → ℂ} (d : PrincipalData μ) : MemL2Loc (recD d) := by
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hsub : K ⊆ Metric.closedBall 0 (max C 0) := fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC z hz).trans (le_max_left _ _)
  have hmem := memLp_recD_closedBall d (le_max_right C 0)
  have hint : Integrable (fun z => ‖recD d z‖ ^ 2)
      ((volume : Measure ℂ).restrict (Metric.closedBall 0 (max C 0))) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hle : ((volume : Measure ℂ).restrict (K ∩ Set.univ)) ≤
      ((volume : Measure ℂ).restrict (Metric.closedBall 0 (max C 0))) :=
    Measure.restrict_mono (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
      (Set.inter_subset_left.trans hsub) le_rfl
  exact hint.mono_measure hle

/-! ## `∂̄(F n) → μ · D` in `L²` on compacta -/

/-- `(μn n - μ) · D → 0` in `L²`: dominated convergence for the coefficient difference.  The
dominating function is `2·k·‖D‖`, which is square integrable as soon as `D` is. -/
private theorem eLpNorm_mu_sub_mul_tendsto {μ : ℂ → ℂ} (d : PrincipalData μ) {ν : Measure ℂ}
    (hνle : ν ≤ (volume : Measure ℂ)) (hDmem : MemLp (recD d) 2 ν)
    (hμaesm : AEStronglyMeasurable μ ν) :
    Tendsto (fun n => eLpNorm (fun z => (d.μn n z - μ z) * recD d z) 2 ν) atTop (𝓝 0) := by
  have hk0 : 0 ≤ d.k := record_k_nonneg d
  have hbdd : ∀ᵐ z ∂ν, ‖μ z‖ ≤ d.k :=
    Filter.Eventually.filter_mono (ae_mono hνle) (record_norm_le d)
  have htend : ∀ᵐ z ∂ν, Tendsto (fun n => d.μn n z) atTop (𝓝 (μ z)) :=
    Filter.Eventually.filter_mono (ae_mono hνle) d.tendsto_μn
  refine PLWD2.eLpNorm_two_tendsto_of_dominated
    (h := fun z => ((2 * d.k : ℝ) : ℂ) * recD d z) ?_ ?_ ?_ ?_
  · intro n
    exact (((d.contDiff_μn n).continuous.aestronglyMeasurable.sub hμaesm).mul
      hDmem.aestronglyMeasurable)
  · exact hDmem.const_mul ((2 * d.k : ℝ) : ℂ)
  · intro n
    filter_upwards [hbdd] with z hz
    rw [norm_mul, norm_mul]
    have hnorm : ‖(((2 * d.k : ℝ)) : ℂ)‖ = 2 * d.k := by
      rw [Complex.norm_def, Complex.normSq_ofReal]
      exact Real.sqrt_mul_self (by linarith)
    rw [hnorm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖d.μn n z - μ z‖ ≤ ‖d.μn n z‖ + ‖μ z‖ := norm_sub_le _ _
      _ ≤ d.k + d.k := add_le_add (d.norm_μn n z) hz
      _ = 2 * d.k := by ring
  · filter_upwards [htend] with z hz
    have h1 : Tendsto (fun n => d.μn n z - μ z) atTop (𝓝 (μ z - μ z)) :=
      hz.sub tendsto_const_nhds
    have h2 : Tendsto (fun n => (d.μn n z - μ z) * recD d z) atTop
        (𝓝 ((μ z - μ z) * recD d z)) := h1.mul tendsto_const_nhds
    simpa using h2

/-- `∂̄(F n) = μn n · ∂(F n)` tends to `μ · D` in `L²` on compact sets, where `D = recD d`. -/
theorem recD_dzbar_tendsto {μ : ℂ → ℂ} (d : PrincipalData μ) :
    ∀ K : Set ℂ, IsCompact K →
      Tendsto (fun n => eLpNorm
        (fun z => dzbar ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - μ z * recD d z) 2
        ((volume : Measure ℂ).restrict K)) atTop (𝓝 0) := by
  intro K hK
  have hDmem : MemLp (recD d) 2 ((volume : Measure ℂ).restrict K) :=
    memLp_recD_restrict_compact d hK
  have hDaesm : AEStronglyMeasurable (recD d) ((volume : Measure ℂ).restrict K) :=
    hDmem.aestronglyMeasurable
  have hμaesm : AEStronglyMeasurable μ ((volume : Measure ℂ).restrict K) :=
    (record_aestronglyMeasurable d).mono_measure Measure.restrict_le_self
  -- first term: `μn n · (∂(F n) - D)`
  have h1 : Tendsto (fun n => eLpNorm
      (fun z => d.μn n z * (dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - recD d z)) 2
      ((volume : Measure ℂ).restrict K)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n => ENNReal.ofReal d.k *
        eLpNorm (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - recD d z) 2
          ((volume : Measure ℂ).restrict K))
      tendsto_const_nhds ?_ (fun n => bot_le) (fun n => ?_)
    · have hc := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal d.k) (recD_spec d K hK)
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using hc
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ ?_ 2
      · exact (d.contDiff_μn n).continuous.aestronglyMeasurable.mul
          ((continuous_dz_of_contDiff_one (d.contDiff_Fn n)).aestronglyMeasurable.sub hDaesm)
      · filter_upwards with z
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (d.norm_μn n z) (norm_nonneg _)
  -- second term: `(μn n - μ) · D`
  have h2 : Tendsto (fun n => eLpNorm (fun z => (d.μn n z - μ z) * recD d z) 2
      ((volume : Measure ℂ).restrict K)) atTop (𝓝 0) :=
    eLpNorm_mu_sub_mul_tendsto d Measure.restrict_le_self hDmem hμaesm
  -- pointwise decomposition
  have hpt : ∀ n, (fun z => dzbar ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - μ z * recD d z)
      = fun z => d.μn n z * (dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - recD d z)
          + (d.μn n z - μ z) * recD d z := by
    intro n
    funext z
    rw [d.beltrami_Fn n z]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n => eLpNorm
        (fun z => d.μn n z * (dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z - recD d z)) 2
          ((volume : Measure ℂ).restrict K)
      + eLpNorm (fun z => (d.μn n z - μ z) * recD d z) 2 ((volume : Measure ℂ).restrict K))
    tendsto_const_nhds ?_ (fun n => bot_le) (fun n => ?_)
  · simpa only [Pi.add_apply, zero_add] using h1.add h2
  · rw [hpt n]
    exact eLpNorm_add_le (by norm_num)

/-! ## The weak Wirtinger derivatives of a record -/

/-- **The weak Wirtinger derivatives of the principal solution.**  For any record `d`, the
`L²_loc` limit `D = recD d` of `∂(F n)` is a weak `∂`-derivative of `φ`, and `μ · D` is a weak
`∂̄`-derivative of `φ`. -/
theorem recD_weakDeriv {μ : ℂ → ℂ} (d : PrincipalData μ) :
    IsDzDeriv (d.φ : ℂ → ℂ) (recD d) ∧
      IsDbarDeriv (d.φ : ℂ → ℂ) (fun z => μ z * recD d z) :=
  weakDeriv_of_approx d.contDiff_Fn d.tendsto_Fn (recD_spec d) (recD_dzbar_tendsto d)

/-! ## Local square integrability of `μ · f` -/

/-- Multiplication by an a.e. bounded measurable field preserves local square integrability. -/
private theorem memL2Loc_mul_of_norm_le {f μ : ℂ → ℂ} {k : ℝ} (hf : MemL2Loc f)
    (hμaesm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (hfaesm : AEStronglyMeasurable f (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    MemL2Loc (fun z => μ z * f z) := by
  intro K hK
  have hfK : Integrable (fun z => ‖f z‖ ^ 2) ((volume : Measure ℂ).restrict (K ∩ Set.univ)) :=
    hf K hK
  have hC : 0 ≤ max k 0 := le_max_right _ _
  have hg : Integrable (fun z => (max k 0) ^ 2 * ‖f z‖ ^ 2)
      ((volume : Measure ℂ).restrict (K ∩ Set.univ)) :=
    hfK.const_mul ((max k 0) ^ 2)
  refine Integrable.mono' hg ?_ ?_
  · exact (((hμaesm.mono_measure Measure.restrict_le_self).mul
      (hfaesm.mono_measure Measure.restrict_le_self)).norm.pow 2)
  · filter_upwards [Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) hb] with z hz
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖μ z * f z‖ ^ 2 = ‖μ z‖ ^ 2 * ‖f z‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ (max k 0) ^ 2 * ‖f z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hz.trans (le_max_left k 0)) 2

/-! ## Two records agree -/

/-- **Well-definedness of the principal solution.**  Any two records of the principal solution
for the same Beltrami coefficient have the same homeomorphism. -/
theorem records_agree {μ : ℂ → ℂ} (d d' : PrincipalData μ) :
    (d.φ : ℂ → ℂ) = (d'.φ : ℂ → ℂ) := by
  obtain ⟨hdz, hdzbar⟩ := recD_weakDeriv d
  obtain ⟨hdz', hdzbar'⟩ := recD_weakDeriv d'
  -- weak derivatives of the difference
  have hp : IsDzDeriv ((d.φ : ℂ → ℂ) - (d'.φ : ℂ → ℂ)) (recD d - recD d') :=
    Work.MRMT.QC.IsDzDeriv.sub hdz hdz'
  have hq : IsDbarDeriv ((d.φ : ℂ → ℂ) - (d'.φ : ℂ → ℂ))
      (fun z => μ z * recD d z - μ z * recD d' z) :=
    Work.MRMT.QC.IsDbarDeriv.sub hdzbar hdzbar'
  -- local square integrability
  have hpL : MemL2Loc (recD d - recD d') :=
    Work.MRMT.QC.MemL2LocOn.sub (memL2Loc_recD d) (memL2Loc_recD d')
      (by simpa using aestronglyMeasurable_recD d)
      (by simpa using aestronglyMeasurable_recD d')
  have hqL : MemL2Loc (fun z => μ z * recD d z - μ z * recD d' z) := by
    have hfun : (fun z => μ z * recD d z - μ z * recD d' z)
        = fun z => μ z * (recD d - recD d') z := by
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [hfun]
    exact memL2Loc_mul_of_norm_le hpL (record_aestronglyMeasurable d)
      ((aestronglyMeasurable_recD d).sub (aestronglyMeasurable_recD d')) (record_norm_le d)
  -- the a.e. bounds
  have hk1 : max d.k d'.k < 1 := max_lt d.hk d'.hk
  have hμk : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ max d.k d'.k := by
    filter_upwards [record_norm_le d, record_norm_le d'] with z h1 h2
    exact h1.trans (le_max_left _ _)
  have hrel : ∀ᵐ z ∂(volume : Measure ℂ),
      (fun z => μ z * recD d z - μ z * recD d' z) z = μ z * (recD d - recD d') z :=
    Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring
  -- the decay of the difference
  have hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖((d.φ : ℂ → ℂ) - (d'.φ : ℂ → ℂ)) z‖ ≤ C / ‖z‖ := by
    refine ⟨max d.C 0 + max d'.C 0, max (max d.R d'.R) 1, by positivity, fun z hz => ?_⟩
    have hzR : d.R ≤ ‖z‖ := (le_max_left d.R d'.R).trans ((le_max_left _ _).trans hz)
    have hzR' : d'.R ≤ ‖z‖ := (le_max_right d.R d'.R).trans ((le_max_left _ _).trans hz)
    have hz1 : 1 ≤ ‖z‖ := (le_max_right (max d.R d'.R) 1).trans hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hgeom : ((d.φ : ℂ → ℂ) - (d'.φ : ℂ → ℂ)) z
        = ((d.φ : ℂ → ℂ) z - z) - ((d'.φ : ℂ → ℂ) z - z) := by
      simp only [Pi.sub_apply]
      ring
    rw [hgeom]
    calc ‖((d.φ : ℂ → ℂ) z - z) - ((d'.φ : ℂ → ℂ) z - z)‖
        ≤ ‖(d.φ : ℂ → ℂ) z - z‖ + ‖(d'.φ : ℂ → ℂ) z - z‖ := norm_sub_le _ _
      _ ≤ d.C / ‖z‖ + d'.C / ‖z‖ := add_le_add (d.decay z hzR) (d'.decay z hzR')
      _ ≤ max d.C 0 / ‖z‖ + max d'.C 0 / ‖z‖ :=
          add_le_add (div_le_div_of_nonneg_right (le_max_left d.C 0) hzpos.le)
            (div_le_div_of_nonneg_right (le_max_left d'.C 0) hzpos.le)
      _ = (max d.C 0 + max d'.C 0) / ‖z‖ := by ring
  -- apply the uniqueness theorem
  have hzero := Work.MRMT.QC.eq_zero_of_beltrami_of_decay_weak
    (h := (d.φ : ℂ → ℂ) - (d'.φ : ℂ → ℂ)) (p := recD d - recD d')
    (q := fun z => μ z * recD d z - μ z * recD d' z) (μ := μ) (k := max d.k d'.k)
    (d.φ.continuous.sub d'.φ.continuous) hp hq hpL hqL hk1 hμk hrel hdec
  funext z
  have hz := congrFun hzero z
  simp only [Pi.sub_apply] at hz
  exact sub_eq_zero.mp hz

end Work.MRMT.Found
