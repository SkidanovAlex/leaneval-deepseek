/-
Work.MRMT.Found — the uniform deviation energy of the principal solution.

`record_dev_energy`: for admissible coefficients `μ` with `‖μ‖ ≤ k < 1` a.e. and
`support μ ⊆ closedBall 0 R`, the deviation `D - 1` of the weak `∂`-derivative `D` of the
principal solution `φ` of a `PrincipalData μ` satisfies the *uniform* `L²` bound

  `∫ ‖D - 1‖² ≤ E(k,R)²`,   `E(k,R) = k √(vol (closedBall 0 R)) / (1 - k)`.

## Route of the proof

* `records_agree`: for any record `d` the `L²_loc` limit `recD d` of `∂(F n)` is a weak
  `∂`-derivative of `φ` and `μ · recD d` is a weak `∂̄`-derivative, with `recD d ∈ L²_loc`;
* the weak-derivative calculus (`IsDzDeriv.sub`, `IsDbarDeriv.sub`) moves from `φ` to
  `φ - id`: its weak `∂`-derivative is `D - 1` and its weak `∂̄`-derivative is
  `μ D = μ (1 + (D - 1))`;
* with `ω = μ D ∈ L²` (bounded support, `D ∈ L²_loc`) the Cauchy-transform representation
  `φ - id = C ω` (`ae_eq_cauchyTransform_of_isDbarDeriv`) together with `∂(C ω) = S ω` and
  *uniqueness* of the weak `∂`-derivative gives the Ahlfors–Bers equation `D - 1 = S ω` a.e.;
* the Beurling transform is an `L²` isometry and `ω` solves `ω = μ (1 + S ω)`, so `ω = hsolA`
  a.e. by `fw_ae_eq_hsolA_of_ae_eq_mul_one_add`, whence
  `‖ω‖₂ = ‖hsolA μ‖ ≤ (1-k)⁻¹ ‖μ‖₂` (`hsolA_spec`);
* finally `‖μ‖₂² = ∫ ‖μ‖² ≤ k² · vol (closedBall 0 R)` by the support and the a.e. bound.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.records_agree
import Submission.Work.MRMT.Found.ae_eq_cauchyTransform_of_isDbarDeriv
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add
import Submission.Work.MRMT.Found.memLp_two_mul_of_memL2Loc
import Submission.Work.MRMT.QC.principal_unique
import Submission.Work.MRMT.Sobolev.isDzDeriv_id_add
import Submission.Work.MRMT.Sobolev.mollification_pairing_tendsto
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_contDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-! ## Elementary facts -/

/-- The support of a product is contained in the support of the first factor. -/
private theorem support_mul_subset {μ D : ℂ → ℂ} :
    Function.support (fun z => μ z * D z) ⊆ Function.support μ := by
  intro z hz
  exact Function.mem_support.mpr fun h => hz (by simp [h])

/-- The distributional `∂`-relation only depends on the first function up to a.e. equality. -/
private theorem isDzDeriv_congr_ae_lhs' {f f' g : ℂ → ℂ} (h : Work.MRMT.IsDzDeriv f g)
    (hff' : f =ᵐ[(volume : Measure ℂ)] f') : Work.MRMT.IsDzDeriv f' g := by
  obtain ⟨hf, hg, hm⟩ := h
  refine ⟨hf.congr hff', hg, fun φ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hm φ
  have hdeg : (fun z => f z * Work.MRMT.dz (φ : ℂ → ℂ) z)
      =ᵐ[(volume : Measure ℂ)] (fun z => f' z * Work.MRMT.dz (φ : ℂ → ℂ) z) :=
    hff'.mono (fun z hz => by simp only [hz])
  exact ⟨h1.congr hdeg, h2, (integral_congr_ae hdeg).symm.trans h3⟩

/-- `‖g‖ = √(∫ ‖g‖²)` for an `L²` class. -/
private theorem norm_Lp_eq_sqrt_integral (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖g‖ = Real.sqrt (∫ z, ‖(g : ℂ → ℂ) z‖ ^ 2) := by
  rw [Lp.norm_def]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) (Lp.memLp g)]
  rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num

/-- `∫ ‖g‖² = ‖g‖²` for an `L²` class. -/
private theorem integral_normSq_Lp_eq_norm_sq (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ∫ z, ‖(g : ℂ → ℂ) z‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [norm_Lp_eq_sqrt_integral g, Real.sq_sqrt (integral_nonneg (fun z => sq_nonneg _))]

/-- A function that is a.e. bounded and supported in a closed ball belongs to `L²`. -/
private theorem memLp_two_of_ae_bound_of_support {f : ℂ → ℂ} {C S : ℝ}
    (hmeas : AEStronglyMeasurable f (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖f z‖ ≤ C)
    (hs : Function.support f ⊆ Metric.closedBall 0 S) : MemLp f 2 (volume : Measure ℂ) := by
  set B : Set ℂ := Metric.closedBall 0 (max S 0) with hB
  have hzero : ∀ z ∉ B, f z = 0 := by
    intro z hz
    by_contra hne
    have h1 : z ∈ Metric.closedBall 0 S := hs (Function.mem_support.mpr hne)
    have h2 : ‖z‖ ≤ S := by simpa [Metric.mem_closedBall, dist_zero_right] using h1
    refine hz ?_
    simp only [hB, Metric.mem_closedBall, dist_zero_right]
    have h3 : S ≤ max S 0 := le_max_left S 0
    linarith
  have heq : f = B.indicator f := by
    funext z
    by_cases hz : z ∈ B
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, hzero z hz]
  rw [heq, memLp_indicator_iff_restrict Metric.isClosed_closedBall.measurableSet]
  have hfin : IsFiniteMeasure ((volume : Measure ℂ).restrict B) := by
    rw [isFiniteMeasure_restrict]
    exact (isCompact_closedBall (0 : ℂ) (max S 0)).measure_lt_top.ne
  refine MemLp.of_bound hmeas.restrict (max C 0) ?_
  filter_upwards [ae_restrict_of_ae hb] with z hzb
  exact hzb.trans (le_max_left _ _)

/-- `‖μ‖_{L²}` is bounded by `k · √(vol (closedBall 0 R))` when `‖μ‖ ≤ k` a.e. and
`support μ ⊆ closedBall 0 R`. -/
private theorem norm_toLp_le_of_support {μ : ℂ → ℂ} {k R : ℝ} (hk0 : 0 ≤ k)
    (hμLp : MemLp μ 2 (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R) :
    ‖hμLp.toLp μ‖ ≤ k * Real.sqrt ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal := by
  have hint : ∫ z, ‖μ z‖ ^ 2
      ≤ k ^ 2 * ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal := by
    have hzero : ∀ z ∉ Metric.closedBall 0 R, ‖μ z‖ ^ 2 = 0 := by
      intro z hz
      have hz0 : μ z = 0 := by
        by_contra hne
        exact hz (hsupp (Function.mem_support.mpr hne))
      simp [hz0]
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm]
    have hIntVol : Integrable (fun z => ‖μ z‖ ^ 2) (volume : Measure ℂ) :=
      (memLp_two_iff_integrable_sq_norm hμLp.aestronglyMeasurable).mp hμLp
    have h1 : Integrable (fun z => ‖μ z‖ ^ 2)
        ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) :=
      hIntVol.mono_measure Measure.restrict_le_self
    have h2 : Integrable (fun _ : ℂ => k ^ 2)
        ((volume : Measure ℂ).restrict (Metric.closedBall 0 R)) :=
      integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
    have hb' : ∀ᵐ z ∂((volume : Measure ℂ).restrict (Metric.closedBall 0 R)),
        ‖μ z‖ ^ 2 ≤ k ^ 2 :=
      (ae_restrict_of_ae hb).mono (fun z hz => pow_le_pow_left₀ (norm_nonneg _) hz 2)
    have hmono := integral_mono_ae h1 h2 hb'
    rw [setIntegral_const] at hmono
    rw [smul_eq_mul] at hmono
    rw [mul_comm]
    exact hmono
  have hnormeq : ‖hμLp.toLp μ‖ = Real.sqrt (∫ z, ‖μ z‖ ^ 2) := by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae (MemLp.coeFn_toLp hμLp)]
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hμLp]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  rw [hnormeq]
  calc Real.sqrt (∫ z, ‖μ z‖ ^ 2)
      ≤ Real.sqrt (k ^ 2 * ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal) :=
        Real.sqrt_le_sqrt hint
    _ = k * Real.sqrt ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal := by
        rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk0]

/-! ## The uniform energy bound -/

/-- **Uniform energy bound for the deviation `D - 1`.**

If `D` is a weak `∂`-derivative of `φ` and `μ D` a weak `∂̄`-derivative, `D ∈ L²_loc`,
`‖μ‖ ≤ k < 1` a.e., `support μ ⊆ closedBall 0 R` and `φ z - z = O(1/‖z‖)`, then
`∫ ‖D - 1‖² ≤ (‖μ‖₂/(1 - k))²`. -/
private theorem energy_le_of_weakDeriv {φ D μ : ℂ → ℂ} {k R : ℝ} (hk1 : k < 1)
    (hAdm : Admissible μ) (hμLp : MemLp μ 2 (volume : Measure ℂ))
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hdec : ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖φ z - z‖ ≤ C / ‖z‖)
    (hDloc : MemL2Loc D) (hdz : Work.MRMT.IsDzDeriv φ D)
    (hdzbar : Work.MRMT.IsDbarDeriv φ (fun z => μ z * D z)) :
    ∫ z, ‖D z - 1‖ ^ 2 ≤ (‖hμLp.toLp μ‖ / (1 - k)) ^ 2 := by
  have h1k : 0 < 1 - k := by linarith
  -- `ω = μ D` is `L²` with compact support, hence integrable
  have hωmeas : AEStronglyMeasurable (fun z => μ z * D z) (volume : Measure ℂ) :=
    hdzbar.2.1.aestronglyMeasurable
  have hωLp : MemLp (fun z => μ z * D z) 2 (volume : Measure ℂ) :=
    memLp_two_mul_of_memL2Loc hωmeas hDloc hb hsupp
  have hsuppω : Function.support (fun z => μ z * D z) ⊆ Metric.closedBall 0 R :=
    support_mul_subset.trans hsupp
  have hωcs : HasCompactSupport (fun z => μ z * D z) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R) hsuppω
  have hωint : Integrable (fun z => μ z * D z) (volume : Measure ℂ) :=
    Work.MRMT.Sobolev.integrable_of_memLp_two_hasCompactSupport hωLp hωcs
  -- the weak derivatives of `φ - id`
  have hsubdb : Work.MRMT.IsDbarDeriv (fun z => φ z - z) (fun z => μ z * D z) :=
    Work.MRMT.Weyl.isDbarDeriv_congr
      (Work.MRMT.QC.IsDbarDeriv.sub hdzbar Work.MRMT.Sobolev.isDbarDeriv_id_zero_aux)
      (fun z => by simp)
  have hsubz : Work.MRMT.IsDzDeriv (fun z => φ z - z) (fun z => D z - 1) :=
    Work.MRMT.QC.IsDzDeriv.sub hdz Work.MRMT.Sobolev.isDzDeriv_id
  -- the Cauchy-transform representation `φ - id = C(μ D)`
  have hct : (fun z => φ z - z) =ᵐ[(volume : Measure ℂ)]
      Work.MRMT.cauchyTransform (fun z => μ z * D z) :=
    Work.MRMT.Found.ae_eq_cauchyTransform_of_isDbarDeriv hsubdb.1 hsubdb hωint hsuppω hdec
  -- the Ahlfors--Bers equation `∂(φ - id) = S(μ D)`, by uniqueness
  have hbeur : (fun z => D z - 1) =ᵐ[(volume : Measure ℂ)]
      (((Work.MRMT.beurlingL2 (hωLp.toLp (fun z => μ z * D z))) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by
    have hcts : Work.MRMT.IsDzDeriv (Work.MRMT.cauchyTransform (fun z => μ z * D z))
        (((Work.MRMT.beurlingL2 (hωLp.toLp (fun z => μ z * D z))) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
      Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2 hωLp hωcs
    exact Work.MRMT.QC.is_dz_deriv_unique hsubz (isDzDeriv_congr_ae_lhs' hcts hct.symm)
  -- the Ahlfors--Bers equation in the `L²`-solution form
  set g : Lp ℂ 2 (volume : Measure ℂ) :=
    Work.MRMT.beurlingL2 (hωLp.toLp (fun z => μ z * D z)) with hg
  have hAB : (fun z => μ z * D z) =ᵐ[(volume : Measure ℂ)]
      fun z => μ z * (1 + (g : ℂ → ℂ) z) := by
    filter_upwards [hbeur] with z hz
    show μ z * D z = μ z * (1 + (g : ℂ → ℂ) z)
    rw [← hz]
    ring
  have hsol_eq : (fun z => μ z * D z) =ᵐ[(volume : Measure ℂ)]
      ((hsolA μ hAdm hμLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) :=
    fw_ae_eq_hsolA_of_ae_eq_mul_one_add hk1 hAdm hμLp hωLp hb hAB
  -- the `L²` bound for `hsolA`
  have hnorm : ‖hωLp.toLp (fun z => μ z * D z)‖ ≤ (1 - k)⁻¹ * ‖hμLp.toLp μ‖ := by
    have hLpeq : hωLp.toLp (fun z => μ z * D z) = hsolA μ hAdm hμLp := by
      rw [Lp.ext_iff]
      filter_upwards [MemLp.coeFn_toLp hωLp, hsol_eq] with z h1 h2
      rw [h1, h2]
    rw [hLpeq]
    exact (hsolA_spec hAdm hμLp hk1 hb).2.1
  -- `∫ ‖D - 1‖² = ∫ ‖S(μD)‖² = ‖μD‖₂² ≤ ((1-k)⁻¹‖μ‖₂)²`
  calc ∫ z, ‖D z - 1‖ ^ 2
      = ∫ z, ‖(g : ℂ → ℂ) z‖ ^ 2 :=
        integral_congr_ae (hbeur.mono (fun z hz => congrArg (fun w : ℂ => ‖w‖ ^ 2) hz))
    _ = ‖g‖ ^ 2 := integral_normSq_Lp_eq_norm_sq g
    _ = ‖hωLp.toLp (fun z => μ z * D z)‖ ^ 2 := by rw [hg]; rw [Work.MRMT.norm_beurlingL2]
    _ ≤ ((1 - k)⁻¹ * ‖hμLp.toLp μ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (‖hμLp.toLp μ‖ / (1 - k)) ^ 2 := by rw [inv_mul_eq_div]

/-! ## The main theorem -/

theorem record_dev_energy (k R : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (hR : 0 ≤ R) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (μ : ℂ → ℂ) (hμ : Admissible μ) (d : PrincipalData μ),
      Function.support μ ⊆ Metric.closedBall 0 R →
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) →
      ∃ D : ℂ → ℂ, Work.MRMT.MemL2Loc D ∧ Work.MRMT.IsDzDeriv (d.φ : ℂ → ℂ) D ∧
        Work.MRMT.IsDbarDeriv (d.φ : ℂ → ℂ) (fun z => μ z * D z) ∧
        ∫ z, ‖D z - 1‖ ^ 2 ≤ E ^ 2 := by
  have h1k : 0 < 1 - k := by linarith
  refine ⟨k * Real.sqrt ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal / (1 - k),
    div_nonneg (mul_nonneg hk0 (Real.sqrt_nonneg _)) h1k.le, ?_⟩
  intro μ hμ d hsupp hb
  obtain ⟨hdz, hdzbar⟩ := recD_weakDeriv d
  refine ⟨recD d, memL2Loc_recD d, hdz, hdzbar, ?_⟩
  have hμLp : MemLp μ 2 (volume : Measure ℂ) :=
    memLp_two_of_ae_bound_of_support hμ.meas hb hsupp
  have hdec : ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖(d.φ : ℂ → ℂ) z - z‖ ≤ C / ‖z‖ :=
    ⟨d.C, d.R, fun z hz => d.decay z hz⟩
  have hkey := energy_le_of_weakDeriv hk1 hμ hμLp hb hsupp hdec (memL2Loc_recD d) hdz hdzbar
  have hbd : ‖hμLp.toLp μ‖
      ≤ k * Real.sqrt ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal :=
    norm_toLp_le_of_support hk0 hμLp hb hsupp
  have hstep : ‖hμLp.toLp μ‖ / (1 - k)
      ≤ k * Real.sqrt ((volume : Measure ℂ) (Metric.closedBall 0 R)).toReal / (1 - k) :=
    div_le_div_of_nonneg_right hbd h1k.le
  exact hkey.trans (pow_le_pow_left₀ (by positivity) hstep 2)

end Work.MRMT.Found
