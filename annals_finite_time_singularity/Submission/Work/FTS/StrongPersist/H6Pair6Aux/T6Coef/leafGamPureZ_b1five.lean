import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.midSlotSupLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.qDzLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.tracePi4_six
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveCore
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveArith
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.xProdIntLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## A.e. reductions on the product measure

The two elementary facts about the product measure
`μ = (volume.restrict Iz).prod (volume.restrict Iθ)` that every route to the crux case consumes —
the point is a.e. in the *open* quadrant, and the level-one mixed slot `D_θf` is a.e. bounded by
`C·Xn α f` — are `ae_mem_Q0_prod` and `ae_abs_mixed01_le_Xn` of
`T6Coef.leafGamPureZ_b1fiveAux` (imported here, same namespace). -/

/-- The crux case `(a,b,a₁,b₁) = (1,5,0,5)` of `T6Coef.leafGamPureZ` (the documented case
(E2) of `T6Coef/NOTES_mulTermLarge.md`; `b₁ = 5` forces `b = 5`, `a = 1`).

Routes that are known to *not* suffice, and the one piece of extra structure that is not used
by them:

* the naive pointwise weight split `leafGam α |X||W| = (σ^{-e₁}|X|)(σ^{-(γ-e₁)}|W|)` with
  `X := D_z⁵A` a *pure-`z`* slot (only `w²σ^{-η}X² ≤ HkIntegrand α 6 A` is available) is short by
  `σ^{-(γ-η)/2}`; so is the Hardy-improved version (`∫σ^{-(2-γ)}X²` from `thetaHardyA`).
* `X` has no pointwise (Agmon) bound: `PwOpen6.PwAny6` only covers slots of order `≤ 4`, while
  `D_z⁵A` has order `5`.
* the *mixed* slot `mixed 5 1 A = D_z⁵D_θA = sin(2θ)·∂_θ(D_z⁵A)` **is** available at the
  `σ^{-γ}` weight: `∫∫ w²σ^{-γ}(mixed 5 1 A)² ≤ HkSq α 6 A` (a summand of `HkIntegrand α 6 A`).
  Similarly the *f*-side slots at the `σ^{-γ}` weight are `mixed 0 1 f = D_θf` (order 1, so also
  pointwise bounded by `C·Xn α f ≤ C·M` via `T2SupB2.mixed_pointwise_le_Xn`) and
  `mixed 5 1 f = D_z⁵D_θf` (order 6, in `HkSq α 6 f`).
* a route that works for the `b₁ ≤ 4` sibling cases: `|D_z^{b₁}A| ≤ C α^{-1/2}HkNorm α 6 A`
  (`PwOpen6.PwAny6`, order `≤ 4`) + the matched-weight `f`-pair bound `slotCS_z`.
  For `b₁ = 5` one needs instead to turn `D_z⁵A` into its angular derivative: e.g. the
  `θ`-integration by parts identity (boundary term `σ^{2-γ}·X·∂_θ f·D_z⁵f → 0`)
  `∫_θ σ^{-γ}X(D_θh₁)(D_θh₂) = -∫_θ σ^{-γ}(D_θX)(D_θh₁)h₂ - (1-γ)∫_θσ^{-γ}σ'X(D_θh₁)h₂
      - ∫_θσ^{-γ}X(D_θ²h₁)h₂`
  in which the first term is priced by the mixed slot of `A`; the residual terms have the factor
  `(1-γ) = -α/10` or an extra `σ` and need care.
* the radial (`D_z`) integration by parts is also available: with `V := D_θf` (order 1, bounded),
  `X = D_z(D_z⁴A)`, the identity
  `∫_0^∞ w²(D_zv)W dz = [w²zvW]_0^∞ - ∫(w²+z∂_zw²)vW - ∫w²v(D_zW)`
  (boundary terms vanish a.e. in `θ` by `SixAux.trace_slot_ae6`/`N6Trans.SixAux`-style trace
  lemmas for the slots `D_z⁴A`, `D_z⁴D_θf`, `D_z⁵A`, `D_θf`) reduces to three terms in which
  `D_z⁴A` (order 4, hence `PwAny6`-bounded) occurs.
* the inequality is *sharp*: on product data `A(z,θ)=ζ(z)Ψ(θ)`, `f(z,θ)=φ(z)Φ(θ)` with `θ`-profiles
  concentrated at `sin 2θ ≍ δ` one has LHS `≍ m⁹δ^{-(γ-1)}` against RHS `≍ m^{12.5}δ^{-(γ-1)-0.05}`
  (`m` = radial frequency), i.e. bounded, so any proof must use the full `ℋ⁶`-slots (the `z`-side),
  not only the `θ`-slices.

The proof below exploits the *slicewise* Agmon inequality `xSliceAgmon5` for the pure-`z` slot
`D_z⁵A` (whose two `θ`-integrals are level-six summands), the same-weight angular Cauchy–Schwarz
`gamSliceCS` for the pair `(D_θf, D_z⁵D_θf)` (both carry the `σ^{-γ}` weight), and the
`z`-for-`θ` Agmon bound `vSliceSupLe` for `sup_z ∫_θ σ^{-γ}(D_θf)²` — which turns the remaining
three-factor `z`-product into a two-factor Cauchy–Schwarz.  The slicewise core is collected in
`leafGamPureZ_b1fiveCore`, the numerical bookkeeping in `leafGamPureZ_b1fiveArith`. -/
theorem leafGamPureZ_b1five : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 K6 M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed 5 0 A p.1 p.2
          * Work.Spaces.mixed 0 1 f p.1 p.2
          * Work.Spaces.mixed 5 1 f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed 5 0 A p.1 p.2
            * Work.Spaces.mixed 0 1 f p.1 p.2
            * Work.Spaces.mixed 5 1 f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C3, _hC3pos, hArith⟩ := b1fiveArith
  refine ⟨max 100 C3, lt_max_of_lt_left (by norm_num), ?_⟩
  intro α hα A f K0 K4 K6 M hCoef hDat
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 5 0 A p.1 p.2
      * Work.Spaces.mixed 0 1 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2 with hF
  set MX : ℝ → ℝ := fun z => (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
      + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
    with hMX
  set Qz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 5 1 f z θ) ^ 2 with hQz
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hwnn : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := Work.FTS.TransportS.SlotT2.supOpen_w_nonneg
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hCoef.n4
  have hK0nn : 0 ≤ K0 := by
    have h := hCoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  have hN6f_nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hgam1 : Work.Spaces.gam α - 1 = α / 10 := hgam_const
  -- ## the slicewise core (in `leafGamPureZ_b1fiveCore`)
  have hSliceInt := b1fiveSliceInt α A f hα0 hα1 hCoef.sm hDat.sm hCoef.h6 hDat.h6
  have hinner := b1fiveInner α A f M hαI hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIouter := b1fiveOuter α A f M hαI hCoef.sm hDat.sm hCoef.h6 hDat.h6 hDat.bdd
  have hIslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |F (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => |F (0, θ)|) = fun _ => (0 : ℝ) := by
        funext θ
        rw [hF]
        simp only [Work.FTS.TransportS.leafGam, Work.Spaces.w]
        norm_num
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · exact hSliceInt z hpos
  -- ## a.e. strong measurability of `F`, `|F|`, `√MX`, `√Qz`
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => F p) Work.FTS.EllipticEst.Q0 := by
    rw [hF]
    exact (((contOn_leafGam α).mul (smoothOpen_continuousOn (hCoef.sm.mixed 5 0))).mul
      (smoothOpen_continuousOn (hDat.sm.mixed 0 1))).mul
      (smoothOpen_continuousOn (hDat.sm.mixed 5 1))
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF
  have hIaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontF.abs
  have hMXnn : ∀ z : ℝ, 0 ≤ MX z := by
    intro z
    rw [hMX]
    refine add_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)))
      (mul_nonneg (div_nonneg (by norm_num) (by rw [hgam1]; linarith))
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))))
  have hQznn : ∀ z : ℝ, 0 ≤ Qz z := by
    intro z
    rw [hQz]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' hθ) _) (sq_nonneg _))
  have hMXaesm : MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (MX z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ, (Work.Spaces.DzIter 5 A z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      aesm_sliceIntegral ((smoothOpen_continuousOn (hCoef.sm.DzIter 5)).pow 2)
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 A z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      aesm_sliceIntegral (contOn_sig_mixed hCoef.sm (le_refl 1))
    have h3 : MeasureTheory.AEStronglyMeasurable MX
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [hMX]
      exact (h1.const_mul (4 / Real.pi)).add (h2.const_mul (200 / (Work.Spaces.gam α - 1)))
    exact Real.continuous_sqrt.comp_aestronglyMeasurable h3
  have hQzaesm : MeasureTheory.AEStronglyMeasurable (fun z => Real.sqrt (Qz z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 f z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      aesm_sliceIntegral (contOn_sig_mixed hDat.sm (le_refl 1))
    have h3 : MeasureTheory.AEStronglyMeasurable Qz
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [hQz]
      exact h2
    exact Real.continuous_sqrt.comp_aestronglyMeasurable h3
  -- ## the supplied integral bounds and the majorant
  have hMXint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * MX z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [hMX] using (xProdIntLe α A hα0 hα1 hCoef.sm hCoef.h6).1
  have hQint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * Qz z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [hQz] using (zProdIntLe α f hα0 hα1 hDat.sm hDat.h6).1
  have hMajAbs_int : MeasureTheory.Integrable (fun z => Real.sqrt 2 * M
      * (((Work.Spaces.w z) ^ 2 * MX z + (Work.Spaces.w z) ^ 2 * Qz z) / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((hMXint.add hQint).div_const 2).const_mul _
  have hAMall : ∀ z : ℝ,
      (Work.Spaces.w z * Real.sqrt (MX z)) * (Work.Spaces.w z * Real.sqrt (Qz z))
      ≤ ((Work.Spaces.w z) ^ 2 * MX z + (Work.Spaces.w z) ^ 2 * Qz z) / 2 := by
    intro z
    have ha : (Work.Spaces.w z * Real.sqrt (MX z)) ^ 2 = (Work.Spaces.w z) ^ 2 * MX z := by
      rw [mul_pow, Real.sq_sqrt (hMXnn z)]
    have hb : (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2 = (Work.Spaces.w z) ^ 2 * Qz z := by
      rw [mul_pow, Real.sq_sqrt (hQznn z)]
    nlinarith [sq_nonneg (Work.Spaces.w z * Real.sqrt (MX z) - Work.Spaces.w z * Real.sqrt (Qz z))]
  -- ## the radial Cauchy--Schwarz
  have hcsz' : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (MX z))
        * (Work.Spaces.w z * Real.sqrt (Qz z)))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * MX z)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z) := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts (s := Work.Spaces.Iz)
      (A := fun z => (Work.Spaces.w z * Real.sqrt (MX z)) ^ 2)
      (B := fun z => (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2)
      (hMXint.congr (Filter.Eventually.of_forall (fun z => by
        show (Work.Spaces.w z) ^ 2 * MX z = (Work.Spaces.w z * Real.sqrt (MX z)) ^ 2
        rw [mul_pow, Real.sq_sqrt (hMXnn z)])))
      (hQint.congr (Filter.Eventually.of_forall (fun z => by
        show (Work.Spaces.w z) ^ 2 * Qz z = (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2
        rw [mul_pow, Real.sq_sqrt (hQznn z)])))
      (fun z => sq_nonneg _) (fun z => sq_nonneg _)
    rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (MX z)) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * MX z from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [mul_pow, Real.sq_sqrt (hMXnn z)])),
      show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [mul_pow, Real.sq_sqrt (hQznn z)]))] at h
    have heqint : (∫ z in Work.Spaces.Iz,
          Real.sqrt ((Work.Spaces.w z * Real.sqrt (MX z)) ^ 2)
          * Real.sqrt ((Work.Spaces.w z * Real.sqrt (Qz z)) ^ 2))
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z * Real.sqrt (MX z))
          * (Work.Spaces.w z * Real.sqrt (Qz z)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        simp only [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))]))
    rwa [heqint] at h
  have hprod_int : MeasureTheory.Integrable (fun z => Real.sqrt 2 * M
      * ((Work.Spaces.w z * Real.sqrt (MX z)) * (Work.Spaces.w z * Real.sqrt (Qz z))))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hMajAbs_int ?_ ?_
    · exact ((aesm_w.mul hMXaesm).mul (aesm_w.mul hQzaesm)).const_mul _
    · filter_upwards with z
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hMnn)
        (mul_nonneg (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))
          (mul_nonneg (hwnn z) (Real.sqrt_nonneg _))))]
      exact mul_le_mul_of_nonneg_left (hAMall z) (mul_nonneg (Real.sqrt_nonneg 2) hMnn)
  -- ## Fubini
  obtain ⟨hFabs_int, hFabs_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => |F (z, θ)|)
    (fun z θ => abs_nonneg _) hIaesm hIslice hIouter
  -- ## the bound on the iterated integral
  have hbr : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
    add_nonneg (mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f]))
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have hIbound : (∫ z, (∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ max 100 C3 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
          + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
    have hArith' := hArith α hαI A f K0 K4 K6 M hCoef hDat
    simp only [b1fiveMX_apply, b1fiveQz_apply] at hArith'
    have e1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * MX z)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
              + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
                  (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 5 1 A z θ) ^ 2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [hMX]
    have e2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 f z θ) ^ 2) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [hQz]
    calc (∫ z, (∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, Real.sqrt 2 * M * ((Work.Spaces.w z * Real.sqrt (MX z))
            * (Work.Spaces.w z * Real.sqrt (Qz z)))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
          MeasureTheory.integral_mono_ae hIouter hprod_int hinner
      _ = Real.sqrt 2 * M * (∫ z, (Work.Spaces.w z * Real.sqrt (MX z))
            * (Work.Spaces.w z * Real.sqrt (Qz z))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Real.sqrt 2 * M
            * (Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * MX z)
              * Real.sqrt (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Qz z)) :=
          mul_le_mul_of_nonneg_left hcsz' (mul_nonneg (Real.sqrt_nonneg 2) hMnn)
      _ ≤ max 100 C3 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
            + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
          rw [e1, e2]
          refine le_trans hArith' ?_
          refine mul_le_mul_of_nonneg_right ?_ hbr
          exact mul_le_mul_of_nonneg_right (le_max_right 100 C3) (Real.rpow_nonneg hα0.le _)
  -- ## assembly
  have hF_int : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' hFabs_int hFaesm ?_
    filter_upwards with p
    exact le_of_eq (by rw [Real.norm_eq_abs]; rfl)
  refine ⟨hF_int, ?_⟩
  calc |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, ‖F p‖ ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
          (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) F
    _ = ∫ p, |F p| ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by simp only [Real.norm_eq_abs]
    _ ≤ max 100 C3 * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
          + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        rw [hFabs_val]
        exact hIbound

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
