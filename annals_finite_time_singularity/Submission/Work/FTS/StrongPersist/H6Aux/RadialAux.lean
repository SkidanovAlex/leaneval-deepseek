import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open Work.FTS.Nonlinear.RadialProd (smE smG)

set_option maxHeartbeats 1600000

/-! ## The level-`n` radial density -/

/-- `RintN n r z = Σ_{i ≤ n} (D_z^i r z)² w(z)²`: the radial density that the `θ`-integral of
the `ℋⁿ`-integrand of a product `a(θ)·r(z)` is bounded by.  (`Rint r` of
`Nonlinear.RadialProd` is the case `n = 4`.) -/
def RintN (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem RintN_nonneg (n : ℕ) (r : ℝ → ℝ) (z : ℝ) : 0 ≤ RintN n r z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The angular jet of `Γ`, with the sharp factor `α` -/

/-- **`|D_θ^i Γ(α,·)| ≤ 10^5·α·Γ(α,·)` for `1 ≤ i ≤ 4`.**  This is the `α`-carrying refinement
of `LocData.DthIter_Gam_abs_le`: since `D_θ^{j+1}Γ = α·Tfun j α·Γ` and `|Tfun j| ≤ 10^5` for
`j ≤ 3`, every one of the `D_θ`-iterates of `Γ` beyond order `0` gains a full factor `α`.
That factor is what makes the weighted `θ`-integrals of the heavy slots uniformly bounded as
`α → 0⁺`. -/
theorem DthIter_Gam_abs_le_alpha (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 100000 * α * Work.Spaces.Gam α θ := by
  have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (i - 1) α θ'| ≤ 100000 :=
    fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ'
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi α hα 100000 hT θ hθ
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]
  calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
    _ = 100000 * α * Work.Spaces.Gam α θ := by ring

/-! ## The heavy angular weight of the sharp profile, with its exponent combined -/

/-- **`(sin 2θ^{α/5})² · sin(2θ)^{-γ} = sin(2θ)^{2α/5-γ}` on `Iθ`.**  Folding the squared profile
`G θ = sin(2θ)^{α/5}` into the heavy weight `τ = sin(2θ)^{-γ}` produces the single `rpow`
`sin(2θ)^{2α/5-γ}` whose exponent `2α/5 - γ = -1 + 3α/10` lies in `(-1,0)` for `α ∈ (0,1]`, so
its `θ`-integral is finite and computable (`Spaces.sin_two_rpow`).  At the two endpoints
`θ ∈ {0, π/2}` both sides vanish. -/
theorem rpow_sq_smG_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
      = (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have hz1 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = 0 := by
      rw [← hs, Real.zero_rpow (by positivity : α / 5 ≠ 0)]
      norm_num
    have hz2 : smG α θ = 0 := by
      rw [smG, ← hs]
      exact Real.zero_rpow (by rw [Work.Spaces.gam]; linarith : -(Work.Spaces.gam α) ≠ 0)
    have hz3 : (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) = 0 := by
      rw [← hs]
      apply Real.zero_rpow
      rw [Work.Spaces.gam]
      intro h
      nlinarith [hα, hα1]
    rw [hz1, hz2, hz3]
    norm_num
  · have hpu : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      refine ((Real.rpow_natCast ((Real.sin (2 * θ)) ^ (α / 5)) 2).symm).trans ?_
      refine ((Real.rpow_mul (le_of_lt hs) (α / 5) 2).symm).trans ?_
      rw [show (α / 5) * 2 = 2 * (α / 5) by ring]
    rw [hpu, smG, ← Real.rpow_add hs,
      show 2 * (α / 5) + -(Work.Spaces.gam α) = 2 * (α / 5) - Work.Spaces.gam α by ring]

/-! ## The target -/

theorem gam_rad_integral_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ r : ℝ → ℝ,
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
          ≤ K * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  refine ⟨20000000000000, by norm_num, ?_⟩
  intro α hα hα1 n hn r z _hz
  have hB1pos : (0 : ℝ) < 100000 * α := by linarith
  -- the angular hypotheses for the level-`n` separation
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ (1 : ℝ) := fun θ hθ => by
    have h := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h.1]; exact h.2
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (100000 * α) * (fun θ' => (Real.sin (2 * θ')) ^ (α / 5)) θ := by
    intro i hi hin θ hθ
    have hi4 : i ≤ 4 := by omega
    refine (DthIter_Gam_abs_le_alpha i hi hi4 α hα hα1 hθ).trans ?_
    exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ) (le_of_lt hB1pos)
  -- the pointwise bound, with the two angular weights combined
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ
        ≤ RintN n r z * (smE θ
            + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    intro θ hθ
    have h := HkIntegrand_ang_rad_le_n (n := n) (by omega) (α := α)
      (a := fun θ => Work.Spaces.Gam α θ) (r := r) (G := fun θ' => (Real.sin (2 * θ')) ^ (α / 5))
      (B0 := 1) (B1 := 100000 * α) (z := z) (θ := θ) ha0 ha1 hθ
    refine h.trans ?_
    simp only [RintN]
    refine mul_le_mul_of_nonneg_left ?_
      (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hfac : (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
        = (4 : ℝ) * (100000 * α) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [show (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ
            = (4 : ℝ) * (100000 * α) ^ 2
              * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * smG α θ) from by ring,
        rpow_sq_smG_eq α hα hα1 hθ]
    have hone : (1 : ℝ) ^ 2 * smE θ = smE θ := by ring
    simpa only [hfac, hone] using le_rfl
  -- integrability of the two angular weights
  have hIe : IntegrableOn (fun θ : ℝ => smE θ) Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hIex : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow _ hp1 hp2).1
  have hdom : IntegrableOn (fun θ : ℝ => RintN n r z * (smE θ
      + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    (hIe.add (hIex.const_mul _)).const_mul _
  have hmono : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
          + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α n _ z θ)
      hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have hval : (∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
        + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
      = RintN n r z * ((∫ θ in Work.Spaces.Iθ, smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
  -- the two numerical bounds for the `θ`-integrals
  have hIe_le : (∫ θ in Work.Spaces.Iθ, smE θ) ≤ 10000 := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
    have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hexp] at h
    have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
    rw [h2] at h
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hIex_le : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
      ≤ 1000 / (3 * α) := by
    have h := (Work.Spaces.sin_two_rpow _ hp1 hp2).2
    have hexp : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hexp] at h
    have heq : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
      have h1 : (3 : ℝ) * α ≠ 0 := by positivity
      have h2 : (3 : ℝ) * α / 10 ≠ 0 := by positivity
      field_simp
      ring
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
        ≤ 100 / (3 * α / 10) := h
      _ = 1000 / (3 * α) := heq
  have hkey : 10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) ≤ 20000000000000 := by
    have heq : 4 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (40000000000000 / 3) * α := by
      have h1 : α ≠ 0 := ne_of_gt hα
      field_simp
      ring
    rw [heq]
    nlinarith [hα1]
  -- assemble
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n (fun z θ => Work.Spaces.Gam α θ * r z) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, RintN n r z * (smE θ
          + 4 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := hmono
    _ = RintN n r z * ((∫ θ in Work.Spaces.Iθ, smE θ)
          + 4 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) := hval
    _ ≤ RintN n r z * (10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (RintN_nonneg n r z)
        have h4 : (0 : ℝ) ≤ 4 * (100000 * α) ^ 2 := by positivity
        linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h4]
    _ ≤ 20000000000000 * RintN n r z := by
        calc RintN n r z * (10000 + 4 * (100000 * α) ^ 2 * (1000 / (3 * α)))
            ≤ RintN n r z * 20000000000000 :=
              mul_le_mul_of_nonneg_left hkey (RintN_nonneg n r z)
          _ = 20000000000000 * RintN n r z := by ring
    _ = 20000000000000 * (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        simp only [RintN]

end Work.FTS.CoercivityFix.Transfer.E2norm
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.psiSeriesUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `psiSeriesUniform` — the Weierstrass test for the mode series of the remainder source

Let `F = RemSource α ψ = α²·𝒜φ·ψ` be the separable remainder source of the `Φ_*` decomposition
and let `t_m(z,θ) = acoeff α m F z · eFam m θ` be the `m`-th mode term of the series
`R α ψ = psiSeries α F = Σ_m t_m`.  This file proves that the *single* pointwise majorant

  `|t_m(z,θ)| ≤ C (1 + 1/z) (m+1)^{-7/2}`   (`m ≥ 1`, `z > 0`, `θ ∈ Iθ`)

already gives everything the Weyl/weak-identity argument needs:

* `ContinuousOn (uncurry (R α ψ)) Q0` (the series is locally uniformly convergent on the open
  quadrant and each partial sum is continuous there);
* on every closed box `[a,b] × [c,d] ⊆ Q0` the partial sums are uniformly bounded by
  `C (1 + 1/a) Σ_m (m+1)^{-7/2}` and converge uniformly to `R α ψ`.

The only points not covered by `hb` are `m = 0` — where the term vanishes identically because
`AngModel.moment` forces `F_*(RemSource α ψ) ≡ 0` and hence `acoeff α 0 F ≡ 0`
(`acoeff_RemSource_zero`) — and the endpoints of `Iθ`, which are included in `Iθ` itself.

The continuity of the individual mode terms is reduced, via `acoeff_RemSource`
(`acoeff α m F z = (α²·bmode m ψ)·radGreen α m (𝒜φ) z`), to `radGreenContinuousOn`, whose
integrability hypothesis `IntegrableOn (𝒜φ)² (Ioi 0)` is proved here from the two explicit
regimes `|𝒜φ| ≤ 20z` on `(0,1]` and `|𝒜φ| ≤ 24/z` on `[1,∞)`.
-/

/-! ## Tails of a summable series tend to zero -/

/-- For a summable `G : ℕ → ℝ`, the tail `Σ_i G (i + k)` tends to `0` as `k → ∞`. -/
private lemma tail_tsum_tendsto_zero {G : ℕ → ℝ} (hG : Summable G) :
    Filter.Tendsto (fun k : ℕ => ∑' i : ℕ, G (i + k)) Filter.atTop (nhds 0) := by
  have hsum : Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, G i) Filter.atTop
      (nhds (∑' i : ℕ, G i)) := hG.hasSum.tendsto_sum_nat
  have heq : (fun k : ℕ => ∑' i : ℕ, G (i + k))
      = fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i := by
    funext k
    have h := hG.sum_add_tsum_nat_add k
    linarith
  rw [heq]
  have h2 : Filter.Tendsto (fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i)
      Filter.atTop (nhds ((∑' i : ℕ, G i) - (∑' i : ℕ, G i))) :=
    tendsto_const_nhds.sub hsum
  simpa using h2

/-! ## The square of the radial profile is integrable on the half-line -/

private lemma phiA_sq_integrableOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) :=
    (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α).pow 2
  -- the small-`z` piece: dominated by `400 z²` on `(0,1)`
  have hIoo : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    have hdom : Integrable (fun t : ℝ => (400 : ℝ) * t ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hpow : IntegrableOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Ioo (0 : ℝ) 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (2 : ℝ)) (t := 1) one_pos).mpr
          (by norm_num)
      simpa only [Real.rpow_two] using hpow.const_mul (400 : ℝ)
    have hsm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun t ht => ht.1
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo
    refine hdom.mono' hsm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_sq]
    have hb := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_small hα hα1 ht.1 ht.2.le
    have h3 : Work.FTS.VocabO.phiA α t ^ 2 ≤ (20 * t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.FTS.VocabO.phiA α t)) hb 2
      rwa [sq_abs] at h
    calc Work.FTS.VocabO.phiA α t ^ 2 ≤ (20 * t) ^ 2 := h3
      _ = 400 * t ^ 2 := by ring
  -- the large-`z` piece: dominated by `576 / z²` on `(1,∞)`
  have hIoi : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi (1 : ℝ)) := by
    have hdom : Integrable (fun t : ℝ => (576 : ℝ) * (t ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hpow : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_iff (s := -(2 : ℝ)) (t := 1) one_pos).mpr (by norm_num)
      have hk : IntegrableOn (fun t : ℝ => (576 : ℝ) * t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
        hpow.const_mul (576 : ℝ)
      refine hk.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      show (576 : ℝ) * t ^ (-(2 : ℝ)) = 576 * (t ^ 2)⁻¹
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
    have hsm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) :=
        fun t ht => lt_trans zero_lt_one (show (1 : ℝ) < t from ht)
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioi
    refine hdom.mono' hsm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_sq]
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hb := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_large hα hα1 ht.le
    have h3 : Work.FTS.VocabO.phiA α t ^ 2 ≤ (24 / t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.FTS.VocabO.phiA α t)) hb 2
      rwa [sq_abs] at h
    have h4 : (24 / t) ^ 2 = 576 * (t ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
      norm_num
    calc Work.FTS.VocabO.phiA α t ^ 2 ≤ (24 / t) ^ 2 := h3
      _ = 576 * (t ^ 2)⁻¹ := h4
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)
  have hIoc : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
      (a := (0 : ℝ)) (b := 1)).mpr hIoo
  rw [← hset]
  exact hIoc.union hIoi

/-! ## Every mode term is continuous on the quadrant -/

private lemma modeContinuous (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m
        (Work.FTS.PhiStar.RemSource α ψ) p.1
      * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Work.FTS.EllipticEst.Q0 := by
  have hphi := phiA_sq_integrableOn hα hα1
  have hcmode : ∀ t : ℝ, Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t
      = (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t := by
    intro t
    rw [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring
  have hc : IntegrableOn (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
      (Work.FTS.PhiStar.RemSource α ψ) t ^ 2) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) ^ 2)
        * Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) := hphi.const_mul _
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    show ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) ^ 2) * Work.FTS.VocabO.phiA α t ^ 2
      = Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t ^ 2
    rw [hcmode t]
    ring
  have hcm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
      (Work.FTS.PhiStar.RemSource α ψ) t) (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
        (Work.FTS.PhiStar.RemSource α ψ) t) (Set.Ioi 0) := by
      have h0 : ContinuousOn (fun t : ℝ =>
          (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t)
          (Set.Ioi 0) :=
        (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α).const_mul _
      have hfun : (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t)
          = fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
              * Work.FTS.VocabO.phiA α t :=
        funext fun t => hcmode t
      rw [hfun]
      exact h0
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hrad : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m
      (Work.FTS.PhiStar.RemSource α ψ) z) (Set.Ioi 0) := by
    show ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t))
      (Set.Ioi 0)
    exact Work.FTS.H2.ModalSolR.radGreenContinuousOn hα hα1 m hc hcm
  have hang : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      Work.FTS.EllipticEst.Q0 :=
    (continuous_eFam m).comp_continuousOn continuous_snd.continuousOn
  exact (hrad.comp continuous_fst.continuousOn (fun p hp =>
    (Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 from hp)).1)).mul
    hang

/-! ## The partial sums are continuous on the quadrant -/

private lemma psiTrunc_continuousOn (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
      (Work.FTS.PhiStar.RemSource α ψ) N)) Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
        (Work.FTS.PhiStar.RemSource α ψ) N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_finsetSum (Finset.range (N + 1))
    (fun m _ => modeContinuous α ψ hα hα1 hψ m)

/-! ## The Weierstrass estimate on a box -/

/-- On a closed box `[a,b] × [c,d] ⊆ Q0` the partial sums are uniformly bounded by
`C (1 + 1/a) Σ_m (m+1)^{-7/2}` and converge to the series uniformly. -/
private lemma box_estimate (α : ℝ) (ψ : ℝ → ℝ) {C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hψ : Work.FTS.PhiStar.AngModel α ψ) (hC : 0 < C)
    (hb : ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    (∀ (N : ℕ) (p : ℝ × ℝ), p ∈ box a b c d →
      |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
      p ∈ box a b c d →
      |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
        - R α ψ p.1 p.2| < ε) := by
  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(7 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hmaj_nn : ∀ m : ℕ, 0 ≤ ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
    fun m => Real.rpow_nonneg (by positivity) _
  -- the `m = 0` mode coefficient vanishes
  have hzero : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0
      (Work.FTS.PhiStar.RemSource α ψ) z = 0 :=
    Work.FTS.PhiStar.Series.acoeff_RemSource_zero α ψ (fun t _ => by
      rw [Work.FTS.PhiStar.Series.Fstar_RemSource, hψ.moment, mul_zero])
  -- the termwise majorant
  have hterm : ∀ (m : ℕ) {z θ : ℝ}, 0 < z → θ ∈ Work.Spaces.Iθ → a ≤ z →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
    intro m z θ hz hθ haz
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, hzero z hz, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hC) (by positivity)) (hmaj_nn 0)
    · have h1 := hb m hm z θ hz hθ
      have hg : 0 ≤ ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := hmaj_nn m
      have h2 : 1 + 1 / z ≤ 1 + 1 / a := by
        have := one_div_le_one_div_of_le ha haz
        linarith
      calc |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := h1
        _ ≤ C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (le_of_lt hC)) hg
  refine ⟨?_, ?_⟩
  · intro N p hp
    obtain ⟨hpz, hpθ⟩ := mem_box.mp hp
    have hz : 0 < p.1 := lt_of_lt_of_le ha hpz.1
    have hθ : p.2 ∈ Work.Spaces.Iθ :=
      ⟨(lt_of_lt_of_le hc hpθ.1).le, (lt_of_le_of_lt hpθ.2 hd).le⟩
    have h1 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ ∑ m ∈ Finset.range (N + 1), |Work.FTS.PhiStar.Series.acoeff α m
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2| := by
      rw [Work.FTS.PhiStar.Series.psiTrunc]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ m ∈ Finset.range (N + 1), |Work.FTS.PhiStar.Series.acoeff α m
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2|
        ≤ ∑ m ∈ Finset.range (N + 1),
            C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun m _ => hterm m hz hθ hpz.1)
    have h3 : ∑ m ∈ Finset.range (N + 1),
            C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))
        = C * (1 + 1 / a) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
    have h4 : ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))
        ≤ ∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
      hmaj.sum_le_tsum (Finset.range (N + 1)) (fun m _ => hmaj_nn m)
    have h5 : 0 ≤ C * (1 + 1 / a) := mul_nonneg (le_of_lt hC) (by positivity)
    calc |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ ∑ m ∈ Finset.range (N + 1), C * (1 + 1 / a)
            * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := le_trans h1 h2
      _ = C * (1 + 1 / a) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := h3
      _ ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 h5
  · intro ε hε
    have hmajK : Summable (fun m : ℕ => C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
      hmaj.mul_left _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tail_tsum_tendsto_zero hmajK) ε hε
    refine ⟨N, fun n hn p hp => ?_⟩
    obtain ⟨hpz, hpθ⟩ := mem_box.mp hp
    have hz : 0 < p.1 := lt_of_lt_of_le ha hpz.1
    have hθ : p.2 ∈ Work.Spaces.Iθ :=
      ⟨(lt_of_lt_of_le hc hpθ.1).le, (lt_of_le_of_lt hpθ.2 hd).le⟩
    have hsummable : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m
        (Work.FTS.PhiStar.RemSource α ψ) p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) :=
      Summable.of_norm_bounded hmajK (fun m => by
        rw [Real.norm_eq_abs]
        exact hterm m hz hθ hpz.1)
    have hsplit := hsummable.sum_add_tsum_nat_add (n + 1)
    have hdiff : Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
        - R α ψ p.1 p.2
        = -(∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
              (Work.FTS.PhiStar.RemSource α ψ) p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2) := by
      rw [R_apply, Work.FTS.PhiStar.Series.psiSeries, Work.FTS.PhiStar.Series.psiTrunc]
      linarith [hsplit]
    rw [hdiff, abs_neg]
    have hshift : Summable (fun i : ℕ => C * (1 + 1 / a)
        * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
      (summable_nat_add_iff (f := fun m : ℕ => C * (1 + 1 / a)
        * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) (n + 1)).mpr hmajK
    have hnorms : Summable (fun i : ℕ => ‖Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
        (Work.FTS.PhiStar.RemSource α ψ) p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
        rw [Real.norm_eq_abs]
        exact hterm (i + (n + 1)) hz hθ hpz.1) hshift
    have hlt : |∑' i : ℕ, C * (1 + 1 / a)
        * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ))| < ε := by
      have hk : N ≤ n + 1 := by omega
      simpa only [Real.dist_eq, sub_zero] using hN (n + 1) hk
    calc |∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2|
        = ‖∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' i : ℕ, ‖Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖ :=
          norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' i : ℕ, C * (1 + 1 / a) * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
          Summable.tsum_le_tsum (fun i => by
            rw [Real.norm_eq_abs]
            exact hterm (i + (n + 1)) hz hθ hpz.1) hnorms hshift
      _ < ε := lt_of_le_of_lt (le_abs_self _) hlt

/-! ## The theorem -/

theorem psiSeriesUniform (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) {C : ℝ} (hC : 0 < C)
    (hb : ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.Weil.R α ψ))
        Work.FTS.EllipticEst.Q0 ∧
    (∀ (a b c d : ℝ), 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 →
      (∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
          ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
        p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
          - Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2| ≤ ε)) := by
  refine ⟨?_, fun a b c d ha hab hc hcd hd => ?_⟩
  · -- continuity of the series, from local uniform convergence
    intro p hp
    have hp' : 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 :=
      Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 from hp)
    obtain ⟨hz, hθ0, hθ1⟩ := hp'
    have ha : 0 < p.1 / 2 := by linarith
    have hab : p.1 / 2 ≤ p.1 + 1 := by linarith
    have hc : 0 < p.2 / 2 := by linarith
    have hcd : p.2 / 2 ≤ (p.2 + π / 2) / 2 := by linarith [Real.pi_pos]
    have hd : (p.2 + π / 2) / 2 < π / 2 := by linarith
    obtain ⟨-, hunif⟩ := box_estimate α ψ hα hα1 hψ hC hb ha hab hc hcd hd
    have hconv : TendstoUniformlyOn
        (fun n : ℕ => Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
          (Work.FTS.PhiStar.RemSource α ψ) n))
        (Function.uncurry (R α ψ)) atTop (box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif ε hε
      filter_upwards [Filter.eventually_ge_atTop N] with n hn x hx
      simp only [Function.uncurry]
      rw [Real.dist_eq, abs_sub_comm]
      exact hN n hn x hx
    have hcontBox : ContinuousOn (Function.uncurry (R α ψ))
        (box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2)) :=
      hconv.continuousOn (Frequently.of_forall (fun n =>
        (psiTrunc_continuousOn α ψ hα hα1 hψ n).mono
          (box_subset_Q0 ha hab hc hcd hd)))
    have hmem : box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2) ∈ 𝓝 p := by
      refine Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        (show p ∈ Set.Ioo (p.1 / 2) (p.1 + 1) ×ˢ Set.Ioo (p.2 / 2) ((p.2 + π / 2) / 2) from
          ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)) ?_
      rintro q ⟨hq1, hq2⟩
      exact ⟨⟨le_of_lt hq1.1, le_of_lt hq1.2⟩, ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩⟩
    exact (hcontBox.continuousAt hmem).continuousWithinAt
  · obtain ⟨hbnd, hunif⟩ := box_estimate α ψ hα hα1 hψ hC hb ha hab hc hcd hd
    refine ⟨hbnd, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hunif ε hε
    exact ⟨N, fun n hn p hp => le_of_lt (hN n hn p hp)⟩

end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.telescoping =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-! ## Helpers for the telescoping identity

The three auxiliary facts below are the algebraic/regularity inputs of `telescoping`:

* `contDiffAt_uncurry_sep_mul`: a separable product `(z,θ) ↦ (c·A z)·v θ` is `C²` at `(z,θ)`
  as soon as `A` is `C²` at `z` and `v` is `C²` at `θ` (this is what `Work.Elliptic.bslOp_add`
  needs in order to split off a correction term);
* `bslOp_sep_const`: `bslOp` of a constant multiple of a separable product, obtained from the
  (unconditional) `Work.FTS.PhiStar.bslOp_sep` by pulling the constants
  `iteratedDeriv 2 (fun z => c * A z) = c · iteratedDeriv 2 A` and
  `deriv (fun z => c * A z) = c · deriv A` out of the operator;
* `telescoping_psi23_contDiffAt`: `C²`-regularity of the two telescoping iterates
  `ψ₂ = σ·LinvI ψ`, `ψ₃ = σ·LinvI ψ₂` (`σ = sin 2θ`) at interior points, deduced from the
  `Linv`-regularity `Work.FTS.PhiStar.linv23_smooth` by the product rule. -/





end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.RadialAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The projector constant at level six.**  `C₀f = L₁₂(Transport f)(0)` is bounded by
`HkNorm α 4 f` (`L3Aux.Transport_L12_zero_le`, which needs only `HkMem α 4 f`), hence by
`HkSq α 6 f` for `H6Adm` data with order-seven honesty. -/
theorem Alt_C0_sq_le_HkSq6 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C₀, hC₀, hb⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C₀ ^ 2, by positivity, ?_⟩
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have habs : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0|
      ≤ C₀ * Work.Spaces.HkNorm α 4 f := hb α f hα hα1 hmem4
  have hmono : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 6 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6
  have h4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      = |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ^ 2 := by rw [sq_abs]
    _ ≤ (C₀ * Work.Spaces.HkNorm α 4 f) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C₀ ^ 2 * Work.Spaces.HkSq α 4 f := by
        rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt h4]
    _ ≤ C₀ ^ 2 * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- **The radial block of the projector correction.**  `ampB α z = 2z²/(1+z)³ = bcoefRad z`, so
`D_z^q(ampB α/c α) = c(α)⁻¹·Zop^q bcoefRad`; the `j ≤ 6` weighted bound of `L6Aux.bcoefRad_zop_bound6`
and the block integral of `L6Aux.radSnorm6_int_le` therefore give a constant bound uniform in
`α ∈ (0,1]`. -/
theorem Alt_slotSum_ampB_div_le : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C := by
  obtain ⟨K, hKpos, hKbd⟩ := Work.FTS.StrongPersist.L6Aux.bcoefRad_zop_bound6
  refine ⟨140000 * K ^ 2, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hα hα1
  have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  -- the pointwise bound in the `Zop`-normalisation
  have hrb : ∀ j ≤ 6, ∀ z ∈ Set.Ici (0 : ℝ),
      |Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z|
        ≤ (10 * K) / (1 + z) := by
    intro j hj z hz
    have h1 := hKbd j hj z hz
    have h2 : 0 < 1 + z := by
      have : (0 : ℝ) ≤ z := hz
      linarith
    refine le_trans h1 (div_le_div_of_nonneg_right (by linarith) h2.le)
  obtain ⟨hInt, hBnd⟩ :=
    Work.FTS.StrongPersist.L6Aux.radSnorm6_int_le (K := 10 * K) (by positivity) hrb
  -- the two functions agree a.e. on `Iz`, with the extra factor `c(α)^{-2}`
  have hae : (fun z : ℝ => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      =ᵐ[volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => ((Work.Spaces.c α)⁻¹) ^ 2 *
          (∑ q ∈ Finset.range 7,
            (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
              * Work.Spaces.w z) ^ 2)) := by
    rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    have hpt : ∀ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
            Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        = ((Work.Spaces.c α)⁻¹) ^ 2
          * ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
              * Work.Spaces.w z) ^ 2) := by
      intro q _
      have hAB : Work.FTS.CoercivityFix.Transfer.ampB α
          = Work.FTS.StrongPersist.L3Aux.bcoefRad := rfl
      have hfun : (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
          = fun z' => (Work.Spaces.c α)⁻¹ * Work.FTS.StrongPersist.L3Aux.bcoefRad z' := by
        funext z'
        rw [hAB, div_eq_mul_inv, mul_comm]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter, hfun,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
      ring
    change (∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z'
          / Work.Spaces.c α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ((Work.Spaces.c α)⁻¹) ^ 2 *
        (∑ q ∈ Finset.range 7,
          (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
            * Work.Spaces.w z) ^ 2)
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  refine ⟨(hInt.const_mul (((Work.Spaces.c α)⁻¹) ^ 2)).congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
  have hnn : 0 ≤ ∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
      (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z * Work.Spaces.w z) ^ 2 :=
    integral_nonneg fun z => Finset.sum_nonneg fun q _ => sq_nonneg _
  have h1 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h0 : 0 ≤ (Work.Spaces.c α)⁻¹ := le_of_lt (inv_pos.mpr hcpos)
    nlinarith
  calc ((Work.Spaces.c α)⁻¹) ^ 2
        * (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
          (Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad z
            * Work.Spaces.w z) ^ 2)
      ≤ 100 * (14 * (10 * K) ^ 2) := mul_le_mul h1 hBnd hnn (by norm_num)
    _ = 140000 * K ^ 2 := by ring

end Work.FTS.StrongPersist.H6Aux
end
end
