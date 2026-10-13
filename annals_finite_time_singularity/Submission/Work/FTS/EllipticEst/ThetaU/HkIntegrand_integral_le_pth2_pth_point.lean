import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceIdents
import Submission.Work.FTS.EllipticEst.ThetaU.OpenIntegrability
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2_pth
import Submission.Work.FTS.EllipticEst.SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary vocabulary for the proof

`Sfun` (the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`, together with `Sfun_nonneg`, `integrableOn_Sfun` and
`integral_Sfun_le`) is imported from `ThetaU.OpenIntegrability`; the dominating function
`Bdom` by which a single angular integrand (at a fixed radial level `z`, with a fixed value
`M` of the `H^k`-integral of `∂_θ² f`) is bounded is defined here. -/

/-- The angular weight `(u * w(z)/sin(2θ)^{η/2})²` is `w(z)²` times the `η`-weighted
square of `u`. -/
private lemma rad_term_eq_aux {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z u : ℝ) :
    (u * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (u ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθ z]
  ring

/-- The angular weight `(v * Wt α z θ)²` is `w(z)²` times the `γ`-weighted square of `v`. -/
private lemma mix_term_eq_aux {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (α z v : ℝ) :
    (v * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (v ^ 2 * Work.FTS.EllipticEst.thGam α θ) := by
  rw [mul_pow, Work.FTS.EllipticEst.Wt_sq hθ α z]
  ring

/-- The dominating function of the per-`z` estimate: the sum over the radial slices
`0 ≤ j ≤ k` of the `(k-j+1)`-fold multiple of `(max C2 0)` times the `j`-th slice group of
`∂_θ² f` together with the boundary weight `M · Sfun α`. -/
private def Bdom (α : ℝ) (k : ℕ) (C2 M : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (((k - j : ℕ) : ℝ) + 1) *
    (max C2 0 * (Work.FTS.EllipticEst.sliceGroup α k j f z θ + M * Sfun α θ))

/-- The per-`z` comparison of `∂_θ f` in the honest `C^∞` class: same statement as
`Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2_pth` (proved for
`Work.Spaces.SmoothNbhd f`, *analyticity* in this Mathlib) with the analytic class replaced by
`ThetaU.SmoothOpenθ f = C^∞` on the half-strip `(0,∞) × (-1, π/2+1)` and the slice hypothesis
`SliceSmooth u` by the honest `C^∞` class `SliceSmoothO u`.  `hC2` is exactly the interface
supplied by `ThetaU.slice_d_bound_open` (uniform in the level `K ≤ k`).

PROOF: copy `Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_integral_le_pth2_pth.lean`
verbatim.  The `SmoothNbhd`-based identities it invokes are replaced by the `C^∞` ones of
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceIdents.lean`
(`DzIter_pth_eq_deriv_open`, `LopIter_slice_DzIter_eq_mixed_open`,
`LopIter_deriv_DzIter_eq_mixed_open`, `sliceV_DzIter_open`,
`LopIter_sliceV_DzIter_eq_mixed_open`), the slice data integrability by
`ThetaU.slice_data_integrable_of_HkIntegrand_open`, the boundary vanishing by
`Work.FTS.EllipticEst.DzIter_boundary_zero`, and `Sfun` with its integrability by
`ThetaU.OpenIntegrability`.  As in the sibling `HkIntegrand_integral_le_pth2_point`, the
pointwise comparison is needed only at interior angles (`ThetaU.ae_eq_of_forall_Ioo`), and the
level `z = 0` is trivial (`Work.FTS.EllipticEst.HkIntegrand_zero_left`). -/
theorem HkIntegrand_integral_le_pth2_pth_point (k : ℕ) (C2 : ℝ)
    (hC2 : ∀ (K : ℕ), K ≤ k → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.ThetaU.SliceSmoothO u → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ C2 * Work.FTS.EllipticEst.slicePhi α K u θ) ∧
        (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
            ≤ C2 * Work.FTS.EllipticEst.slicePhi α K u θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.ThetaU.SmoothOpenθ f → Work.Spaces.VanishTheta f →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  classical
  refine ⟨((k : ℝ) + 1) ^ 2 * max C2 0 * ((k : ℝ) + 10001 + Real.pi) + 1, ?_, ?_⟩
  · positivity
  · intro α f hα0 hα1 hf hvan hInt z hz
    have hz0 : 0 ≤ z := hz
    rcases eq_or_lt_of_le hz0 with hzeq | hzpos
    · rw [← hzeq]
      simp [Work.FTS.EllipticEst.HkIntegrand_zero_left]
    · -- from now on `0 < z`
      set M : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ
        with hM
      have hM0 : 0 ≤ M := by
        rw [hM]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) z θ)
      have hterms := integrableOn_HkIntegrand_terms_open α k (Work.Spaces.pthIter 2 f)
        (fun i => (hf.pthIter 2).continuousOn_slice_DzIter i hzpos)
        (fun j i => (hf.pthIter 2).continuousOn_slice_mixed j i hzpos)
        (hInt z hz)
      have hSint : MeasureTheory.IntegrableOn (Sfun α) Work.Spaces.Iθ :=
        integrableOn_Sfun hα0 hα1
      have hSle : (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ 10000 + Real.pi :=
        integral_Sfun_le hα0 hα1
      -- integrability of the individual summands of the right-hand integrand
      have hterm_rad : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn (fun θ' =>
          (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ'
            * (Work.Spaces.w z / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2))) ^ 2)
          Work.Spaces.Iθ := fun j hj => hterms.1 j hj
      have hterm_mix : ∀ j m : ℕ, 1 ≤ m → m + j ≤ k → MeasureTheory.IntegrableOn (fun θ' =>
          (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ' * Work.Spaces.Wt α z θ') ^ 2)
          Work.Spaces.Iθ := fun j m hm hmj => hterms.2 m j hm hmj
      -- integrability of the slice groups of `∂_θ² f`
      have hintG : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
          (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z) Work.Spaces.Iθ := by
        intro j hjle
        have hmix : MeasureTheory.IntegrableOn (fun θ' => ∑ m ∈ Finset.Icc 1 (k - j),
            (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ' * Work.Spaces.Wt α z θ') ^ 2)
            Work.Spaces.Iθ :=
          MeasureTheory.integrable_finsetSum _ (fun m hm =>
            hterm_mix j m (Finset.mem_Icc.mp hm).1
              (by have h2 := (Finset.mem_Icc.mp hm).2; omega))
        unfold Work.FTS.EllipticEst.sliceGroup
        exact (hterm_rad j hjle).add hmix
      -- the hypotheses required by `hC2` for the slice `u_j`
      have hslice : ∀ j : ℕ, j ≤ k →
          SliceSmoothO (fun θ' => Work.Spaces.DzIter j f z θ') ∧
          (fun θ' => Work.Spaces.DzIter j f z θ') 0 = 0 ∧
          (fun θ' => Work.Spaces.DzIter j f z θ') (Real.pi / 2) = 0 ∧
          MeasureTheory.IntegrableOn (fun θ' =>
            (Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') ^ 2
              * Work.FTS.EllipticEst.thEta θ') Work.Spaces.Iθ ∧
          (∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ' =>
            (Work.FTS.EllipticEst.LopIter m
                (Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'')) θ') ^ 2
              * Work.FTS.EllipticEst.thGam α θ') Work.Spaces.Iθ) := by
        intro j hj
        have hz1 : (-1 : ℝ) < z := by linarith
        have hbnd := Work.FTS.EllipticEst.DzIter_boundary_zero hvan j
        have hdata := slice_data_integrable_of_HkIntegrand_open α k hf hzpos j hj (hInt z hz)
        exact ⟨(hf.DzIter j).sliceSmoothO hzpos, hbnd.1 z hz1, hbnd.2 z hz1,
          hdata.1, hdata.2⟩
      -- the pointwise comparison of the slice groups, at interior angles
      have hgroup : ∀ j ∈ Finset.range (k + 1),
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ
            ≤ (((k - j : ℕ) : ℝ) + 1)
              * (max C2 0 * (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)) := by
        intro j hj θ hθ
        have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
        have hθV : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := Iθ_subset_Ioo hθI
        set Y : ℝ := max C2 0 * (Work.FTS.EllipticEst.sliceGroup α k j
            (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ) with hY
        obtain ⟨hC2a, hC2b⟩ := hC2 (k - j) (Nat.sub_le k j) α
          (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
          (hslice j hjle).1 (hslice j hjle).2.1 (hslice j hjle).2.2.1
          (hslice j hjle).2.2.2.1 (hslice j hjle).2.2.2.2
        have hsliceA_nn : 0 ≤ Work.FTS.EllipticEst.sliceA
            (fun θ' => Work.Spaces.DzIter j f z θ') := by
          rw [Work.FTS.EllipticEst.sliceA]
          exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ' hθ' =>
            mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ'))
        have hPhi_nn : 0 ≤ Work.FTS.EllipticEst.slicePhi α (k - j)
            (fun θ' => Work.Spaces.DzIter j f z θ') θ := by
          rw [Work.FTS.EllipticEst.slicePhi]
          refine add_nonneg (add_nonneg
            (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθI)) ?_) ?_
          · exact Finset.sum_nonneg (fun m _ =>
              mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθI))
          · exact mul_nonneg hsliceA_nn (Sfun_nonneg hθI)
        -- the second-derivative slices are `≤ w(z)^{-2} M`
        have hA : (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sliceA
            (fun θ' => Work.Spaces.DzIter j f z θ') ≤ M := by
          rw [Work.FTS.EllipticEst.sliceA, hM, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg ?_ (hInt z hz) ?_
          · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' =>
              mul_nonneg (sq_nonneg _)
                (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ')))
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' => ?_)
            dsimp only
            rw [sliceV_DzIter_open hf j hzpos (Iθ_subset_Ioo hθ'),
              ← rad_term_eq_aux hθ' z (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ')]
            exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ' j hjle
        -- `slicePhi` of the slice is dominated by the slice group of `∂_θ² f`
        have hY' : (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
            (fun θ' => Work.Spaces.DzIter j f z θ') θ
            ≤ Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
              + M * Sfun α θ := by
          rw [Work.FTS.EllipticEst.slicePhi, Work.FTS.EllipticEst.sliceGroup]
          calc (Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ
                  + (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                        * Work.FTS.EllipticEst.thGam α θ)
                  + Work.FTS.EllipticEst.sliceA (fun θ' => Work.Spaces.DzIter j f z θ') * Sfun α θ)
              = (Work.Spaces.w z) ^ 2
                  * ((Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                      * Work.FTS.EllipticEst.thEta θ)
                + (Work.Spaces.w z) ^ 2 * (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                        * Work.FTS.EllipticEst.thGam α θ)
                + (Work.Spaces.w z) ^ 2
                    * (Work.FTS.EllipticEst.sliceA (fun θ' => Work.Spaces.DzIter j f z θ')
                        * Sfun α θ) := by ring
            _ ≤ (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
                + (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                        * Work.Spaces.Wt α z θ) ^ 2)
                + M * Sfun α θ := by
                  refine add_le_add (add_le_add ?_ ?_) ?_
                  · refine le_of_eq ?_
                    rw [sliceV_DzIter_open hf j hzpos hθV,
                      ← rad_term_eq_aux hθI z (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ)]
                  · rw [Finset.mul_sum]
                    refine Finset.sum_le_sum (fun m _ => le_of_eq ?_)
                    rw [← mix_term_eq_aux hθI α z (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ),
                      LopIter_sliceV_DzIter_eq_mixed_open hf j m hzpos hθ]
                  · rw [show (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sliceA
                          (fun θ' => Work.Spaces.DzIter j f z θ') * Sfun α θ)
                        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sliceA
                            (fun θ' => Work.Spaces.DzIter j f z θ')) * Sfun α θ from by ring]
                    exact mul_le_mul_of_nonneg_right hA (Sfun_nonneg hθI)
            _ = Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                + M * Sfun α θ := by
                  rw [Work.FTS.EllipticEst.sliceGroup]
        -- the pure `D_z` summand of the group of `f`
        have hrad_le : (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ Y := by
          rw [rad_term_eq_aux hθI z (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ),
            DzIter_pth_eq_deriv_open hf j hzpos hθV]
          calc (Work.Spaces.w z) ^ 2
                * ((deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ)
              ≤ (Work.Spaces.w z) ^ 2 * (C2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left (hC2a θ hθI) (sq_nonneg _)
            _ ≤ (Work.Spaces.w z) ^ 2 * (max C2 0 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (le_max_left C2 0) hPhi_nn) (sq_nonneg _)
            _ = max C2 0 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) := by ring
            _ ≤ Y := by
                rw [hY]
                exact mul_le_mul_of_nonneg_left hY' (le_max_right C2 0)
        -- the mixed summands of the group of `f`
        have hmix_le : ∀ i ∈ Finset.Icc 1 (k - j),
            (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ Y := by
          intro i hi
          have h1 := hC2b i hi θ hθI
          have e0 : (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ
              = (Work.FTS.EllipticEst.LopIter i
                    (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ := by
            rw [← LopIter_deriv_DzIter_eq_mixed_open hf j i hzpos hθ]
          rw [mix_term_eq_aux hθI α z (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ), e0]
          calc (Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.LopIter i
                      (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                    * Work.FTS.EllipticEst.thGam α θ)
              ≤ (Work.Spaces.w z) ^ 2 * (C2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            _ ≤ (Work.Spaces.w z) ^ 2 * (max C2 0 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (le_max_left C2 0) hPhi_nn) (sq_nonneg _)
            _ = max C2 0 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) := by ring
            _ ≤ Y := by
                rw [hY]
                exact mul_le_mul_of_nonneg_left hY' (le_max_right C2 0)
        have hdecomp : Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ
            = (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Work.FTS.EllipticEst.sliceGroup]
        rw [hdecomp]
        have hsum : (∑ i ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k - j : ℕ) : ℝ)) * Y := by
          calc (∑ i ∈ Finset.Icc 1 (k - j),
                (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2)
              ≤ ∑ i ∈ Finset.Icc 1 (k - j), Y := Finset.sum_le_sum (fun i hi => hmix_le i hi)
            _ = (Finset.Icc 1 (k - j)).card • Y := Finset.sum_const Y
            _ = (((k - j : ℕ) : ℝ)) * Y := by rw [Nat.card_Icc, nsmul_eq_mul]; simp
        calc (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + (∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ Y + (((k - j : ℕ) : ℝ)) * Y := add_le_add hrad_le hsum
          _ = (((k - j : ℕ) : ℝ) + 1) * Y := by ring
      -- the pointwise bound holds at every interior angle, hence a.e. on `Iθ`
      have hpoint : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ
            ≤ Bdom α k C2 M (Work.Spaces.pthIter 2 f) z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum, Bdom]
        exact Finset.sum_le_sum (fun j hj => hgroup j hj θ hθ)
      -- integrability of the dominating function
      have hBint : MeasureTheory.IntegrableOn
          (Bdom α k C2 M (Work.Spaces.pthIter 2 f) z) Work.Spaces.Iθ := by
        unfold Bdom
        refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
        have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hG1 : MeasureTheory.IntegrableOn (fun θ =>
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ)
            Work.Spaces.Iθ := (hintG j hjle).add (hSint.const_mul M)
        have hG2 : MeasureTheory.IntegrableOn (fun θ => max C2 0 *
            (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ))
            Work.Spaces.Iθ := hG1.const_mul (max C2 0)
        exact hG2.const_mul (((k - j : ℕ) : ℝ) + 1)
      have hstep1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Bdom α k C2 M (Work.Spaces.pthIter 2 f) z θ :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ)
          hBint hpoint
      -- the integral of a slice group is at most `(k-j+1) M`
      have hGint : ∀ j : ℕ, j ≤ k →
          (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
            ≤ (((k - j : ℕ) : ℝ) + 1) * M := by
        intro j hjle
        have hradM : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ M := by
          rw [hM]
          exact MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
            (hInt z hz) (Eventually.of_forall fun θ =>
              Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ j hjle)
        have hmixM : ∀ m ∈ Finset.Icc 1 (k - j),
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                * Work.Spaces.Wt α z θ) ^ 2) ≤ M := by
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmj : m + j ≤ k := by have h2 := (Finset.mem_Icc.mp hm).2; omega
          rw [hM]
          exact MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
            (hInt z hz) (Eventually.of_forall fun θ =>
              Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 f) z θ m j hm1 hmj)
        have hmixS : (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k - j : ℕ) : ℝ)) * M := by
          rw [MeasureTheory.integral_finsetSum (s := Finset.Icc 1 (k - j))
            (f := fun m θ =>
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            (hf := fun m hm => hterm_mix j m (Finset.mem_Icc.mp hm).1
              (by have h2 := (Finset.mem_Icc.mp hm).2; omega))]
          calc (∑ m ∈ Finset.Icc 1 (k - j),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2))
              ≤ ∑ m ∈ Finset.Icc 1 (k - j), M := Finset.sum_le_sum (fun m hm => hmixM m hm)
            _ = (Finset.Icc 1 (k - j)).card • M := Finset.sum_const M
            _ = (((k - j : ℕ) : ℝ)) * M := by rw [Nat.card_Icc, nsmul_eq_mul]; simp
        have hmix_int : MeasureTheory.IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            Work.Spaces.Iθ :=
          MeasureTheory.integrable_finsetSum _ (fun m hm => hterm_mix j m
            (Finset.mem_Icc.mp hm).1 (by have h2 := (Finset.mem_Icc.mp hm).2; omega))
        have hGsplit : (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
            = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2) := by
          unfold Work.FTS.EllipticEst.sliceGroup
          exact MeasureTheory.integral_add (hterm_rad j hjle) hmix_int
        rw [hGsplit]
        calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)
            ≤ M + (((k - j : ℕ) : ℝ)) * M := add_le_add hradM hmixS
          _ = (((k - j : ℕ) : ℝ) + 1) * M := by ring
      -- integral bound for the dominating function
      have hBval : (∫ θ in Work.Spaces.Iθ, Bdom α k C2 M (Work.Spaces.pthIter 2 f) z θ)
          ≤ (((k : ℝ) + 1) ^ 2 * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
        unfold Bdom
        have hsummand_int : ∀ j ∈ Finset.range (k + 1), MeasureTheory.Integrable
            (fun θ => (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
              (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                + M * Sfun α θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          intro j hj
          have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact (((hintG j hjle).add (hSint.const_mul M)).const_mul (max C2 0)).const_mul
            (((k - j : ℕ) : ℝ) + 1)
        rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := hsummand_int)]
        have hper : ∀ j ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ, (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)))
              ≤ (((k : ℝ) + 1) * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
          intro j hj
          have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hv : (∫ θ in Work.Spaces.Iθ, (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)))
              = (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                  ((∫ θ in Work.Spaces.Iθ,
                      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
                    + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ))) := by
            rw [MeasureTheory.integral_const_mul]
            congr 1
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add (hintG j hjle) (hSint.const_mul M),
              MeasureTheory.integral_const_mul]
          rw [hv]
          have hG := hGint j hjle
          have hb0 : (∫ θ in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
              + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ)
              ≤ M * (((k - j : ℕ) : ℝ) + 10001 + Real.pi) := by
            have h2 : M * (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ M * (10000 + Real.pi) :=
              mul_le_mul_of_nonneg_left hSle hM0
            nlinarith [hG, h2, hM0]
          have hmax0 : 0 ≤ max C2 0 := le_max_right _ _
          have hc : (((k - j : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 1 := by
            have h : ((k - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k j
            linarith
          have hK : (((k - j : ℕ) : ℝ) + 10001 + Real.pi) ≤ ((k : ℝ) + 10001 + Real.pi) := by
            have h : ((k - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k j
            linarith
          have hKj0 : 0 ≤ (((k - j : ℕ) : ℝ) + 10001 + Real.pi) := by
            have h : (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by positivity
            linarith [Real.pi_pos]
          calc (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                ((∫ θ in Work.Spaces.Iθ,
                    Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
                  + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ)))
              ≤ (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                  (M * (((k - j : ℕ) : ℝ) + 10001 + Real.pi))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb0 hmax0) (by positivity)
            _ ≤ ((k : ℝ) + 1) * (max C2 0 * (M * ((k : ℝ) + 10001 + Real.pi))) := by
                refine mul_le_mul hc ?_ ?_ ?_
                · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hM0) hmax0
                · exact mul_nonneg hmax0 (mul_nonneg hM0 hKj0)
                · positivity
            _ = (((k : ℝ) + 1) * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by ring
        calc (∑ j ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ,
              (((k - j : ℕ) : ℝ) + 1) * (max C2 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ))))
            ≤ ∑ j ∈ Finset.range (k + 1),
                ((((k : ℝ) + 1) * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M) :=
              Finset.sum_le_sum hper
          _ = ((k + 1 : ℕ) : ℝ) * ((((k : ℝ) + 1) * max C2 0
                * ((k : ℝ) + 10001 + Real.pi)) * M) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ = (((k : ℝ) + 1) ^ 2 * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
              push_cast; ring
      calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Bdom α k C2 M (Work.Spaces.pthIter 2 f) z θ := hstep1
        _ ≤ (((k : ℝ) + 1) ^ 2 * max C2 0 * ((k : ℝ) + 10001 + Real.pi)) * M := hBval
        _ ≤ (((k : ℝ) + 1) ^ 2 * max C2 0 * ((k : ℝ) + 10001 + Real.pi) + 1) * M := by
              nlinarith [hM0]

end Work.FTS.EllipticEst.ThetaU
