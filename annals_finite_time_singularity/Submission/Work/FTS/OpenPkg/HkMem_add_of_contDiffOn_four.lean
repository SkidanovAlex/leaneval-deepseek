import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.HkIntegrand_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## PRIVATE WORKSPACE — the finite-order subadditivity of `HkIntegrand`

The target of this module is the closure of `Work.Spaces.HkMem α 4` under addition for data which
are only `C^4` (not `C^∞`) on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  Two ingredients:

* the `ℋ^4`-integrand of `f + g` is *continuous on the open quadrant* (for measurability, via
  `HkMem_of_majorant`).  Its summands are the weighted derivatives of `f+g`, which are continuous
  as long as `f+g` is `C^4` there, and the weights `w`, `sin(2θ)^{-η/2}`, `W` are continuous for
  `z > 0`, `0 < θ < π/2`;
* the *pointwise* subadditivity `HkIntegrand α k (f+g) ≤ 2 (HkIntegrand α k f + HkIntegrand α k g)`
  on all of `Iz × Iθ`, which only needs the additivity of the iterated operators on the open
  quadrant (for `C^k`-data) and vanishing of both sides on the two boundary lines.

Everything is stated for a general pair `(k, n)` with `k ≤ n` so that the `Finset.range (k+1)`
bookkeeping of `HkIntegrand` matches the definition verbatim; the target is the instance
`k = n = 4`. -/

/-! ### The weights on the open quadrant -/

private lemma sin_two_pos_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Q0 hp.2)))

private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

private lemma continuousOn_wdivsin_Q0 :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Work.FTS.EllipticEst.Q0 :=
  continuousOn_w_Q0.div (continuousOn_sinpow_Q0 (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Q0 hp.2) _))

/-! ### Continuity of the integrand for finite-order data -/

/-- **The `ℋ^k`-integrand of a `C^n` function is continuous on the open quadrant** (`k ≤ n`).

Each `D_z`-slot `D_z^i f` with `i ≤ k` is `C^{n-i}` on `Q0` (`contDiffOn_DzIter_fin`), hence
continuous; each mixed slot `D_z^jD_θ^i f` with `i + j ≤ k` is obtained from the `C^{n-i}`
function `D_θ^i f` by `D_z^j` (`i + j ≤ n`), hence continuous as well.  The weights are the
previous lemmas. -/
theorem continuousOn_HkIntegrand_of_contDiffOn (α : ℝ) {n k : ℕ} (hkn : k ≤ n)
    {F : ℝ → ℝ → ℝ} (hF : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hDz : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    intro i hi
    exact (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hF i (by omega)).continuousOn
  have hMx : ∀ (j i : ℕ), i ≤ k → i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro j i hik hij
    have hDth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hF i (by omega)
    have hz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hDth j (by omega)
    exact hz.continuousOn
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact ((hDz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
      continuousOn_wdivsin_Q0).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1))
      (fun i hi => continuousOn_finsetSum (Finset.range (k + 1)) (fun j hj => ?_))
    split_ifs with hc
    · exact ((hMx j i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hc.2).mul
        (continuousOn_Wt_Q0 α)).pow 2
    · exact continuousOn_const

/-! ### Additivity of the iterated operators on the open quadrant

For `C^n`-data on `Q0` (with `n ≥ 1`) the operators `D_z^j` and `D_θ^i` are additive on `Q0`,
because `deriv` is additive at every point of the open set. -/

/-- Slices of a `C^k` (`k ≥ 1`) function on the open quadrant are differentiable in `z`. -/
private lemma slice_diffAt_fst {h : ℝ → ℝ → ℝ} {m n : ℕ}
    (hh : ContDiffOn ℝ (n - m) (Function.uncurry h) Work.FTS.EllipticEst.Q0) (hm : m < n)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z := by
  have hslice : ContDiffOn ℝ (n - m) (fun z' => h z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin (s := Set.Ioi 0)
      (t := Set.Ioo 0 (π / 2)) hh hθ
  have hne : ((n - m : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show n - m ≠ 0 by omega)
  exact (hslice.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- Slices of a `C^k` (`k ≥ 1`) function on the open quadrant are differentiable in `θ`. -/
private lemma slice_diffAt_snd {h : ℝ → ℝ → ℝ} {m n : ℕ}
    (hh : ContDiffOn ℝ (n - m) (Function.uncurry h) Work.FTS.EllipticEst.Q0) (hm : m < n)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ := by
  have hslice : ContDiffOn ℝ (n - m) (fun θ' => h z θ') (Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin (s := Set.Ioi 0)
      (t := Set.Ioo 0 (π / 2)) hh hz
  have hne : ((n - m : ℕ) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show n - m ≠ 0 by omega)
  exact (hslice.differentiableOn hne).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- Functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
private lemma DzIter_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => exact h
  | succ m ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter m F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter m G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

/-- The operators `D_z^j` are additive on the open quadrant for `C^n`-data. -/
private theorem DzIter_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j ≤ n, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro _ z θ _ _ _; rfl
  | succ m ih =>
      intro hm z θ hz h1 h2
      have hm' : m ≤ n := by omega
      have hlt : m < n := by omega
      have heq : (fun z' => Work.Spaces.DzIter m (fun z θ => f z θ + g z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter m f z' θ + Work.Spaces.DzIter m g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hm' z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter m f z' θ) z :=
        slice_diffAt_fst
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hf m hm') hlt hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter m g z' θ) z :=
        slice_diffAt_fst
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hg m hm') hlt hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter m f z' θ
            + Work.Spaces.DzIter m g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter m f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter m g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The operators `D_θ^i` are additive on the open quadrant for `C^n`-data. -/
private theorem DthIter_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i ≤ n, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  intro i
  induction i with
  | zero => intro _ z θ _ _ _; rfl
  | succ m ih =>
      intro hm z θ hz h1 h2
      have hm' : m ≤ n := by omega
      have hlt : m < n := by omega
      have heq : (fun θ' => Work.Spaces.DthIter m (fun z θ => f z θ + g z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter m f z θ' + Work.Spaces.DthIter m g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih hm' z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter m f z θ') θ :=
        slice_diffAt_snd
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hf m hm') hlt hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter m g z θ') θ :=
        slice_diffAt_snd
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
            Work.FTS.EllipticEst.isOpen_Q0 hg m hm') hlt hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter m f z θ'
            + Work.Spaces.DthIter m g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter m f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter m g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant for `C^n`-data
(`i + j ≤ n`). -/
private theorem mixed_add_of_contDiffOn {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hij : i + j ≤ n) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro z θ hz h1 h2
  have hDth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ :=
    DthIter_add_of_contDiffOn hf hg i (by omega)
  have hstep : Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter j (fun z θ => Work.Spaces.DthIter i f z θ
          + Work.Spaces.DthIter i g z θ) z θ := by
    simp only [Work.Spaces.mixed]
    exact DzIter_congr_Q0 (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
      (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
      hDth j z θ hz h1 h2
  rw [hstep]
  have hadd := DzIter_add_of_contDiffOn (n := n - i)
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hf i (by omega))
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
      Work.FTS.EllipticEst.isOpen_Q0 hg i (by omega))
    j (by omega)
  simpa only [Work.Spaces.mixed] using hadd z θ hz h1 h2

/-! ### Pointwise subadditivity of the integrand -/

/-- **Pointwise subadditivity of the `ℋ^k`-integrand for `C^n` (with `k ≤ n`) data on the open
quadrant.**  The two boundary lines contribute `0 ≤ 0`; in the interior every slot is split by
`(a+b)² ≤ 2a² + 2b²` using the additivity of the iterated operators. -/
private theorem HkIntegrand_add_le_of_contDiffOn {α : ℝ} {k n : ℕ} (hkn : k ≤ n)
    {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · subst hz0
    have hz0' : ∀ X : ℝ → ℝ → ℝ, Work.Spaces.HkIntegrand α k X 0 θ = 0 :=
      fun X => Work.FTS.LocData.HkIntegrand_zero_fst α k X θ
    simp only [hz0']
    norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · have hs' : ∀ X : ℝ → ℝ → ℝ, Work.Spaces.HkIntegrand α k X z θ = 0 :=
      fun X => Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts α k X hs z
    simp only [hs']
    norm_num
  · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := Set.mem_Icc.mp hθ
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
          Real.sin_pi]) hs
    have hDz : ∀ i : ℕ, i ≤ k → Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ :=
      fun i hi => DzIter_add_of_contDiffOn hf hg i (by omega) z θ hzpos hθ0 hθ1
    have hMixed : ∀ j i : ℕ, i + j ≤ k →
        Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
          = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ :=
      fun j i hij => mixed_add_of_contDiffOn hf hg j i (by omega) z θ hzpos hθ0 hθ1
    simp only [Work.Spaces.HkIntegrand]
    have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      calc (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1),
              (2 * (Work.Spaces.DzIter i f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
                + 2 * (Work.Spaces.DzIter i g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [hDz i hik, add_mul]
            nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              - Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
        _ = 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (2 * (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i hc.2, add_mul]
              nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
                - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
            · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
              norm_num
        _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
    linarith [hZ, hM]

/-- `HkMem` is closed under addition at order 4 for data that are `C^4` on the open quadrant `Q0 = (0,∞) × (0,π/2)` — the finite-order companion of `Work.FTS.EllipticEst.HkMem_add_smoothOpen`.

Proof recipe: `Work.FTS.LocData.HkMem_of_majorant` with `M := 2 * HkIntegrand α 4 f + 2 * HkIntegrand α 4 g` reduces to
(a) `ContinuousOn (fun p => HkIntegrand α 4 (f+g) p.1 p.2) Q0`, from `ContDiffOn ℝ 4 (uncurry (f+g)) Q0` via `RegQ.contDiffOn_DzIter_fin` / `RegQ.contDiffOn_DthIter_fin` (`Submission/Work/FTS/EllipticEst/RegQ/pthU_slot_alg.lean`) and the continuity of the weights `w`, `wTheta`, `Wt` on `Q0` (see `Submission/Work/Spaces/continuousOn_HkIntegrand_Qd.lean` for the pattern), and
(b) the pointwise bound `HkIntegrand α 4 (f+g) ≤ 2 * HkIntegrand α 4 f + 2 * HkIntegrand α 4 g` on `Iz × Iθ`, either by re-running the slot argument of `Work.FTS.EllipticEst.RegQ.HkIntegrand_slot_le` with coefficients `(1,1)`, or by instantiating `HkIntegrand_slot_le` (stated for `E = -3f - αg` and the *same* `α` as the weight exponent) at `E := f+g`, `f := fun z θ => -(f z θ)/3`, `g := fun z θ => -(g z θ)/α`: the identity `f+g = -3·(-f/3) - α·(-g/α)` holds for `α ≠ 0`, and `Work.FTS.LocData.HkIntegrand_const_mul` converts `18·I_{(-f/3)} + 2·I_{α·(-g/α)}` into `2·I_f + 2·I_g`. At `z = 0` and at `sin(2θ) = 0` both sides vanish (`Q2.HkIntegrand_zero_z_fts`, `Q2.HkIntegrand_zero_sin_fts`). -/
theorem HkMem_add_of_contDiffOn_four {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 4
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α 4 f z θ
      + Work.Spaces.HkIntegrand α 4 g z θ)) ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_of_contDiffOn (n := 4) (k := 4) α le_rfl
      ((hf.add hg).congr (fun p _ => by simp only [Function.uncurry]))
  · intro z hz
    exact ((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2
  · refine IntegrableOn.congr_fun ((hmf.2.add hmg.2).const_mul 2) ?_ measurableSet_Ici
    intro z hz
    show 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      = ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α 4 f z θ
          + Work.Spaces.HkIntegrand α 4 g z θ)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)]
  · exact HkIntegrand_add_le_of_contDiffOn (k := 4) (n := 4) le_rfl hf hg

end Work.FTS.OpenPkg
