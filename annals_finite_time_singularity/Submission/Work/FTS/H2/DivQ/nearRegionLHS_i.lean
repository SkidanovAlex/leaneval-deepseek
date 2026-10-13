import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.nearRegionLHS
import Submission.Work.FTS.H2.DivQ.NRI.LevelDefs
import Submission.Work.FTS.H2.DivQ.NRI.W_integrable_le
import Submission.Work.FTS.H2.DivQ.WDefs
import Submission.Work.FTS.H2.DivQ.Wide_le_Dom
import Submission.Work.FTS.H2.DivQ.hardyA_le_W
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.FTS.H2.DivQ.bCoeff_expansion
import Submission.Work.FTS.H2.DivQ.DthIter_sliceX
import Submission.Work.FTS.H2.DivQ.thetaOfSubst
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## Auxiliary facts about `thetaOf`, `sliceX` and `Gop`

These are (copies of) the *private*, hence unreachable, helpers of
`Submission/Work/FTS/H2/DivQ/nearRegionLHS.lean`, re-proved here so that its assembly can be
re-run with the variable-level data hypothesis: the only structural input that changes is the
provider of the `x`-side Hardy bound, which at level `i` is
`Work.FTS.H2.DivQ.NRI.W_integrable_le i` (data at levels `≤ i`) instead of
`Work.FTS.H2.DivQ.W_integrable` (data at levels `≤ 4`). -/

private lemma nri_contDiffOn_thetaOf :
    ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo (-1 : ℝ) 1) := by
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ ({-1, 1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) Real.arcsin (Set.Ioo (-1 : ℝ) 1) :=
    (Real.contDiffOn_arcsin (n := (⊤ : ℕ∞))).mono hsub
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.arcsin x / 2) (Set.Ioo (-1 : ℝ) 1) :=
    h1.div_const 2
  exact h2

private lemma nri_sin_two_thetaOf_Icc :
    ∀ x ∈ Set.Icc (0 : ℝ) xNear, Real.sin (2 * thetaOf x) = x := by
  intro x hx
  exact sin_two_thetaOf ⟨by linarith [hx.1], by linarith [hx.2, xNear_le_one]⟩

private lemma nri_contDiffOn_sliceX_Ioc {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioc 0 xNear) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => h (thetaOf x)) (Set.Ioc 0 xNear)
  refine hsm.comp (nri_contDiffOn_thetaOf.mono ?_) ?_
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx.1) (by norm_num)
    · rw [thetaOf]
      have h := (Real.arcsin_lt_pi_div_two).mpr (by linarith [hx.2, xNear_lt])
      linarith [h, Real.pi_pos]

private lemma nri_tendsto_sliceX {h : ℝ → ℝ}
    (hh : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (sliceX h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 : Filter.Tendsto thetaOf (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt thetaOf (0 : ℝ) := (Real.continuous_arcsin.div_const 2).continuousAt
      have hct := hc.tendsto
      simp only [thetaOf_zero] at hct
      exact hct.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx) (by norm_num)
  exact hh.comp h1

private lemma nri_Gop_congr_eqOn {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn u v s) : Set.EqOn (Gop u) (Gop v) s := by
  intro x hx
  have hev : u =ᶠ[nhds x] v := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, h⟩
  simp only [Gop]
  rw [hev.deriv_eq]

private lemma nri_Gop_iter_eqOn (i : ℕ) {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn u v s) : Set.EqOn ((Gop^[i]) u) ((Gop^[i]) v) s := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact nri_Gop_congr_eqOn hs ih hx

private lemma nri_sliceX_divSin_eqOn (h : ℝ → ℝ) :
    Set.EqOn (sliceX (fun θ : ℝ => h θ / Real.sin (2 * θ)))
      (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) := by
  intro x hx
  have hxI : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
  change h (thetaOf x) / Real.sin (2 * thetaOf x) = h (thetaOf x) / x
  rw [nri_sin_two_thetaOf_Icc x hxI]

private lemma nri_bCoeff_zero_of_pos : ∀ i : ℕ, 1 ≤ i → bCoeff i 0 = fun _ => (0 : ℝ) := by
  have key : ∀ k : ℕ, genCoeff (fun _ : ℝ => 1) (k + 1) 0 = fun _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero =>
        rw [genCoeff_succ_zero, genCoeff_init_zero]
        funext x
        simp
    | succ k ih =>
        rw [genCoeff_succ_zero, ih]
        funext x
        simp
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [bCoeff_eq_genCoeff]
  exact key k

/-! ## The variable-level data provider

The `x`-side Hardy bound used by the assembly is `Work.FTS.H2.DivQ.NRI.W_integrable_le`: for
**every** level `1 ≤ m ≤ N ≤ 4`, with the honest angular data given only at the levels `1 ≤ m ≤ N`,
it bounds `∫_0^{x₁} x^{2m-γ}(∂_x^{m+1}(sliceX h))²` by `C · nrSS α h m`.  A single constant
serving all four levels is obtained from the four instances (`N = 1,2,3,4`) by taking a maximum;
`nearRegionLHS_i_of_inversion` isolates the body of the assembly, which consumes the provider only
through its level-`i` instance. -/

/-- **The assembly of `nearRegionLHS_i` from the variable-level Hardy bound.**

This is the proof body of `nearRegionLHS` with `W_integrable` replaced by a provider `hW` that is
available at every level `N ≤ 4` with the data only at levels `≤ N`. -/
theorem nearRegionLHS_i_of_inversion
    (hW : ∃ CW : ℝ, 0 < CW ∧ ∀ (N : ℕ), N ≤ 4 → ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) →
      ∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) (Set.Ioc 0 xNear) ∧
        (∫ x in (0 : ℝ)..xNear, x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2)
          ≤ CW * NRI.nrSS α h m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (0 : ℝ)..(Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨CW, hCWpos, hWall⟩ := hW
  obtain ⟨CH, hCHpos, hH⟩ := hardyA_le_W
  obtain ⟨B₁, hB₁nn, hb₁⟩ := (aCoeff_bounds 1).1
  obtain ⟨B₂, hB₂nn, hb₂⟩ := (aCoeff_bounds 2).1
  obtain ⟨B₃, hB₃nn, hb₃⟩ := (aCoeff_bounds 3).1
  obtain ⟨B₄, hB₄nn, hb₄⟩ := (aCoeff_bounds 4).1
  refine ⟨(16 * (max B₁ (max B₂ (max B₃ B₄))) ^ 2 + 1) * CH * CW, by positivity, ?_⟩
  intro α h hα0 hα1 hsm h0h hDenη i hi hDenγ
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  have hgam_pos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα0
  have hgam_neg : -1 < Work.Spaces.gam α := by linarith [Work.Spaces.one_lt_gam hα0]
  -- the bound on the `bCoeff` coefficients
  set B : ℝ := max B₁ (max B₂ (max B₃ B₄)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact le_trans hB₁nn (le_max_left _ _)
  have hbB : ∀ j ≤ i, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |bCoeff i j x| ≤ B := by
    intro j hj x hx
    have h1 : B₁ ≤ B := by rw [hBdef]; exact le_max_left _ _
    have h2 : B₂ ≤ B := by
      rw [hBdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : B₃ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have h4 : B₄ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    interval_cases i
    · exact le_trans (hb₁ j hj x hx) h1
    · exact le_trans (hb₂ j hj x hx) h2
    · exact le_trans (hb₃ j hj x hx) h3
    · exact le_trans (hb₄ j hj x hx) h4
  -- the data functional, in the variable-level form `nrSS α h i`
  set data : ℕ → ℝ := NRI.nrSS α h with hdatadef
  have hdata_mono : ∀ m ≤ i, data m ≤ data i := by
    intro m hm
    rw [hdatadef]
    exact NRI.nrSS_mono α h hm
  have hdata_nonneg : 0 ≤ data i := by
    rw [hdatadef]
    exact NRI.nrSS_nonneg α h i
  have hdata_raw : data i
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [hdatadef]
    exact NRI.nrSS_eq α h i
  -- smoothness of the quotient slice `h/sin(2θ)` and of `(sliceX h)/x`
  have hsm_div : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsm.div (contDiffOn_const.mul contDiffOn_id).sin ?_
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) :=
    (contDiffOn_sliceX hsm).div contDiffOn_id (fun x hx => ne_of_gt hx.1)
  -- the change of variables `θ = thetaOf x`
  have hcont_th : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  have hderiv_th : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    exact hasDerivAt_thetaOf' ⟨by linarith [hx.1], by linarith [hx.2, xNear_le_one]⟩
  have hnn_th : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    have hk : 0 ≤ 2 * kappa x := by rw [kappa_eq_sqrt]; positivity
    exact div_nonneg zero_le_one hk
  have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := (0 : ℝ))
    (b := xNear) (f := thetaOf) (f' := fun x : ℝ => 1 / (2 * kappa x))
    (g := fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    hcont_th hderiv_th hnn_th
  rw [thetaOf_zero, thetaOf_xNear] at hcv
  -- the `x`-side integrand `Hx`
  set Hx : ℝ → ℝ := fun x => (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) with hHxdef
  -- the dominating function `P`
  set P : ℝ → ℝ := fun x => (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
    x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 with hPdef
  -- pointwise domination
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Hx x ≤ P x := by
    intro x hx
    have hpos : (0 : ℝ) < x := hx.1
    have hxIcc : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
    have hk1 : (1 : ℝ) ≤ 2 * kappa x := two_kappa_ge_one hxIcc
    have hknn : (0 : ℝ) ≤ 2 * kappa x := le_trans zero_le_one hk1
    have h0c : bCoeff i 0 = fun _ => (0 : ℝ) := nri_bCoeff_zero_of_pos i hi1
    have he : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x
        = ∑ j ∈ Finset.range i, bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) := by
      rw [bCoeff_expansion i hquot hx, Finset.sum_range_succ']
      rw [show bCoeff i 0 x
            * (x ^ 0 * iteratedDeriv 0 (fun y : ℝ => sliceX h y / y) x) = 0 by
        rw [h0c]
        simp]
      rw [add_zero]
    have hcs : ((Gop^[i] (fun y : ℝ => sliceX h y / y)) x) ^ 2
        ≤ (i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2 := by
      rw [he]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
        (f := fun j : ℕ => bCoeff i (j + 1) x
          * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x))
      simpa using h
    have hterm : ∀ j ∈ Finset.range i,
        (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))
        ≤ B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      intro j hj
      have hj1 : j + 1 ≤ i := by have := Finset.mem_range.mp hj; omega
      have hb : |bCoeff i (j + 1) x| ≤ B := hbB (j + 1) hj1 x hxIcc
      have hb2 : (bCoeff i (j + 1) x) ^ 2 ≤ B ^ 2 := by
        rw [show (bCoeff i (j + 1) x) ^ 2 = |bCoeff i (j + 1) x| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have hxsq : x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          = ((x ^ (j + 1)) ^ 2) * x ^ (-(Work.Spaces.gam α)) := by
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α
              = 2 * (((j + 1 : ℕ) : ℝ)) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hpos]
        congr 1
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) = ((2 * (j + 1) : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        rw [pow_mul]
        ring
      rw [show (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
            * x ^ (-(Work.Spaces.gam α))
          = (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 from by ring]
      have hnn : (0 : ℝ) ≤ (x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (pow_nonneg (pow_nonneg hpos.le (j + 1)) 2) (Real.rpow_nonneg hpos.le _)
      have hnn2 : (0 : ℝ) ≤ (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
        sq_nonneg _
      calc (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2
          ≤ B ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 hnn) hnn2
        _ = B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← hxsq]; ring
    have hstep1 : Hx x ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hpos.le _))
        (div_nonneg zero_le_one hknn)
    have hinv : 1 / (2 * kappa x) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < 2 * kappa x)]
      linarith
    have hstep2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) ≤ P x := by
      have h1 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
            * x ^ (-(Work.Spaces.gam α)) * 1 :=
        mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
            (Real.rpow_nonneg hpos.le _))
      refine h1.trans ?_
      rw [mul_one]
      have hPeq : P x = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
          x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by rw [hPdef]
      rw [hPeq]
      have h2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α))
          = (i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) := by
        rw [mul_assoc, Finset.sum_mul]
      rw [h2]
      have h3 : (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ ∑ j ∈ Finset.range i, B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      calc (i : ℝ) * (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ (i : ℝ) * (∑ j ∈ Finset.range i,
              B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
              x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← Finset.mul_sum]
            ring
    exact hstep1.trans hstep2
  -- the `A_j`-type and `W_j`-type integrability and bounds
  have hWint : ∀ j ∈ Finset.range i, MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) (Set.Ioc (0 : ℝ) xNear) := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hjmem : j + 1 ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (hWall i hi4 α h hα0 hα1 hsm hDenη hDenγ (j + 1) hjmem).1
  have hWbnd : ∀ j ∈ Finset.range i,
      (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) ≤ CW * data i := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hjle : j + 1 ≤ i := by omega
    have hjmem : j + 1 ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, hjle⟩
    refine ((hWall i hi4 α h hα0 hα1 hsm hDenη hDenγ (j + 1) hjmem).2).trans ?_
    have hSS : NRI.nrSS α h (j + 1) ≤ data i := by
      rw [hdatadef]
      exact NRI.nrSS_mono α h hjle
    exact mul_le_mul_of_nonneg_left hSS (le_of_lt hCWpos)
  have hAint : ∀ j ∈ Finset.range i, MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
      (Set.Ioc (0 : ℝ) xNear) := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    exact (hH (j + 1) (Work.Spaces.gam α) xNear xNear_pos hgam_neg (sliceX h)
      (nri_contDiffOn_sliceX_Ioc hsm) (nri_tendsto_sliceX h0h) (hWint j hj)).1
  have hAbnd : ∀ j ∈ Finset.range i,
      (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) ≤ CH * CW * data i := by
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    refine ((hH (j + 1) (Work.Spaces.gam α) xNear xNear_pos hgam_neg (sliceX h)
      (nri_contDiffOn_sliceX_Ioc hsm) (nri_tendsto_sliceX h0h) (hWint j hj)).2).trans ?_
    have hCHle : CH / (1 + Work.Spaces.gam α) ^ 2 ≤ CH := by
      have hγ1 : (1 : ℝ) < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
      have h1 : (1 : ℝ) ≤ (1 + Work.Spaces.gam α) ^ 2 := by nlinarith
      have h2 : (0 : ℝ) < (1 + Work.Spaces.gam α) ^ 2 := by linarith
      rw [div_le_iff₀ h2]
      calc CH = CH * 1 := (mul_one CH).symm
        _ ≤ CH * (1 + Work.Spaces.gam α) ^ 2 := mul_le_mul_of_nonneg_left h1 hCHpos.le
    have hWnn : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..xNear,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2 := by
      rw [intervalIntegral.integral_of_le xNear_pos.le]
      refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
      intro x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _)
    calc CH / (1 + Work.Spaces.gam α) ^ 2
            * (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2)
        ≤ CH * (∫ x in (0 : ℝ)..xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv ((j + 1) + 1) (sliceX h) x) ^ 2) :=
          mul_le_mul_of_nonneg_right hCHle hWnn
      _ ≤ CH * (CW * data i) := mul_le_mul_of_nonneg_left (hWbnd j hj) (le_of_lt hCHpos)
      _ = CH * CW * data i := by ring
  -- integrability of `P`
  have hPint : MeasureTheory.IntegrableOn P (Set.Ioc (0 : ℝ) xNear) := by
    have hSumInt : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
        (Set.Ioc (0 : ℝ) xNear) :=
      MeasureTheory.integrable_finsetSum _ (fun j hj => hAint j hj)
    have hconst := hSumInt.const_mul ((i : ℝ) * B ^ 2)
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq]
    exact hconst
  -- the comparison `∫ Hx ≤ ∫ P`
  have hHxnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) xNear)] Hx := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    have hk : (0 : ℝ) ≤ 1 / (2 * kappa x) := by
      have h2 : 0 ≤ 2 * kappa x := by rw [kappa_eq_sqrt]; positivity
      exact div_nonneg zero_le_one h2
    have hHxunfold : Hx x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := rfl
    rw [hHxunfold]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)) hk
  have hHxle : Hx ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) xNear)] P := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ xNear := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hnull] with x hne
    intro hx
    exact hpt x ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  have hmono : ∫ x in Set.Ioc (0 : ℝ) xNear, Hx x
      ≤ ∫ x in Set.Ioc (0 : ℝ) xNear, P x :=
    integral_mono_of_nonneg hHxnn hPint hHxle
  -- value of `∫ P`
  have hPval : (∫ x in Set.Ioc (0 : ℝ) xNear, P x)
      = (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
          (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq, MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum _ (fun j hj => hAint j hj)
  -- bound on `∫ P`
  have hPbound : (∫ x in Set.Ioc (0 : ℝ) xNear, P x)
      ≤ 16 * B ^ 2 * CH * CW * data i := by
    rw [hPval]
    have hsum : (∑ j ∈ Finset.range i,
          (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
        ≤ (i : ℝ) * (CH * CW * data i) := by
      calc (∑ j ∈ Finset.range i,
            (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
          ≤ ∑ _j ∈ Finset.range i, (CH * CW * data i) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [← intervalIntegral.integral_of_le xNear_pos.le]
            exact hAbnd j hj
        _ = (i : ℝ) * (CH * CW * data i) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
            (∫ x in Set.Ioc (0 : ℝ) xNear, x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2))
        ≤ (i : ℝ) * B ^ 2 * ((i : ℝ) * (CH * CW * data i)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 16 * B ^ 2 * CH * CW * data i := by
          have hi4' : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
          have hi2 : (i : ℝ) ^ 2 ≤ 16 := by nlinarith [hi4', hi1]
          have hnn : 0 ≤ B ^ 2 * CH * CW * data i := by positivity
          calc (i : ℝ) * B ^ 2 * ((i : ℝ) * (CH * CW * data i))
              = (i : ℝ) ^ 2 * (B ^ 2 * CH * CW * data i) := by ring
            _ ≤ 16 * (B ^ 2 * CH * CW * data i) := mul_le_mul_of_nonneg_right hi2 hnn
            _ = 16 * B ^ 2 * CH * CW * data i := by ring
  -- assembling the pieces
  have hfinal : (∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (16 * B ^ 2 + 1) * CH * CW * data i := by
    have hstepA : (∫ θ in (0 : ℝ)..(Real.pi / 8),
          (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = ∫ x in (0 : ℝ)..xNear,
            (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
      rw [← hcv]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le xNear_pos.le] at hx
      simp only [Function.comp_apply]
      rw [nri_sin_two_thetaOf_Icc x hx]
    have hstepB : (∫ x in (0 : ℝ)..xNear,
          (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
            * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        = ∫ x in Set.Ioc (0 : ℝ) xNear, Hx x := by
      have hR : (∫ x in Set.Ioc (0 : ℝ) xNear, Hx x)
          = ∫ x in Set.Ioo (0 : ℝ) xNear, Hx x := MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [intervalIntegral.integral_of_le xNear_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        hR]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
      intro x hx
      have h1 : Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)
          = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x :=
        (DthIter_sliceX i hsm_div hx).trans
          (nri_Gop_iter_eqOn i isOpen_Ioo (nri_sliceX_divSin_eqOn h) hx)
      have hHxunfold : Hx x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := rfl
      show Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) = Hx x
      rw [hHxunfold, h1]
    rw [hstepA, hstepB]
    refine hmono.trans (hPbound.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hdata_nonneg
    nlinarith [hBnn, sq_nonneg B, le_of_lt hCHpos, le_of_lt hCWpos]
  calc (∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (16 * B ^ 2 + 1) * CH * CW * data i := hfinal
    _ = (16 * B ^ 2 + 1) * CH * CW
          * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by rw [hdata_raw]

/-- **The near-region bound, with the data hypothesis at the level actually needed.**

This is `nearRegionLHS` with its hypothesis `∀ m ∈ Finset.Icc 1 4, IntegrableOn (Denγ m)`
*wakened* to `∀ m ∈ Finset.Icc 1 i` (the right-hand side already sums only over `m ≤ i`, and the
proof of `nearRegionLHS` applies its hypothesis only at levels `≤ i`).  The weakening matters: for
the slices `h_b = fun θ => DzIter b Φ z θ` with `b ≥ 1` only the data with `m + b ≤ 4` are
certified by `HkMem α 4 (pth Φ)`, while the assembly needs the bound at level `i ≤ 4 - b`, hence
only `m ≤ i`.

ROUTE.  The same as `nearRegionLHS` (`Submission/Work/FTS/H2/DivQ/nearRegionLHS.lean`), whose
proof body can be reused once its internal chain (`W_integrable`, `inversionNear`-applications,
`dom_integrable`) is re-run parametrically at the level `i` instead of uniformly at `4`: the
`bCoeff` sum runs over `j < i` and calls the helpers at level `j + 1 ≤ i`, and each helper consumes
`HonGam`/`hDenγ` only at levels `≤ j + 1`.  (Alternatively, re-prove it directly by the route of
`NOTES.md` §4.) -/
theorem nearRegionLHS_i :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (0 : ℝ)..(Real.pi / 8),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  -- the four instances of the variable-level inversion; a single constant is obtained by taking
  -- a maximum over the four levels
  obtain ⟨C₁, hC₁pos, hW₁⟩ := NRI.W_integrable_le 1 (by norm_num)
  obtain ⟨C₂, hC₂pos, hW₂⟩ := NRI.W_integrable_le 2 (by norm_num)
  obtain ⟨C₃, hC₃pos, hW₃⟩ := NRI.W_integrable_le 3 (by norm_num)
  obtain ⟨C₄, hC₄pos, hW₄⟩ := NRI.W_integrable_le 4 le_rfl
  have hle1 : C₁ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hle2 : C₂ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hle3 : C₃ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hle4 : C₄ ≤ max (max C₁ C₂) (max C₃ C₄) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine nearRegionLHS_i_of_inversion ⟨max (max C₁ C₂) (max C₃ C₄),
    lt_max_of_lt_left (lt_max_of_lt_left hC₁pos), ?_⟩
  intro N hN α h hα0 hα1 hsm hDenη hDenγ m hm
  have hNcase : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 := by omega
  rcases hNcase with rfl | rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨hm1', hm0'⟩ := Finset.mem_Icc.mp hm
    omega
  · have h1 := hW₁ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle1 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₂ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle2 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₃ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle3 (NRI.nrSS_nonneg α h m))⟩
  · have h1 := hW₄ α h hα0 hα1 hsm hDenη hDenγ m hm
    exact ⟨h1.1, h1.2.trans (mul_le_mul_of_nonneg_right hle4 (NRI.nrSS_nonneg α h m))⟩

end

end Work.FTS.H2.DivQ
