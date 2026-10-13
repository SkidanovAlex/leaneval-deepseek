/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slice decomposition of the `ℋ^k` norm: shared vocabulary

The `ℋ^k`-norm of the paper (Elgindi, Annals 194 (3) 2021, §Notation, §H2) is
`Work.Spaces.HkSq α k f = ∫_z ∫_θ HkIntegrand α k f z θ`, where `HkIntegrand` is the sum of

* the squared *weighted radial* derivatives `(D_z^i f · w(z)/sin(2θ)^{η/2})²`, `0 ≤ i ≤ k`, and
* the squared *weighted mixed* derivatives `(D_z^j D_θ^i f · W(z,θ))²`, `1 ≤ i`, `i + j ≤ k`.

Because `D_z` acts only on the radial variable, the whole integral can be re-summed *by the
number `j` of radial derivatives*: the `j`-th *slice group* collects the radial term `D_z^j f`
together with all its angular derivatives, and each group integrates, in `z`, the radial weight
`w(z)²` times a purely one-dimensional angular functional of the slice `θ ↦ D_z^j f z θ`.

This module fixes that re-summation (`sliceGroup`, `HkIntegrand_eq_slice_sum`), the elementary
algebra of the two weight factors (`rad_term_eq`, `mix_term_eq`), and the identification of
`Work.Elliptic.Dth1Iter` (the iterate of `D_θ` on one-variable functions) with
`Work.FTS.EllipticEst.LopIter`.  It is the vocabulary of the siblings of
`Submission/Work/FTS/EllipticEst/SliceDecomp/`, which carry the decomposition through the two
integrals and end at the bridge `Work.FTS.EllipticEst.HkSq_slice_decomp`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.HkIntegrand_le_slice_sum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The two angular weights agree with the ones of `Ptheta` -/

/-- `Ptheta`'s first angular weight is the `sin(2θ)^{-η}` of the `H^k`-integrand. -/
theorem sEta_eq_thEta : sEta = thEta := rfl

/-- `Ptheta`'s second angular weight is the `sin(2θ)^{-γ}` of the `H^k`-integrand. -/
theorem sGam_eq_thGam (α : ℝ) : sGam α = thGam α := rfl

/-- The one-dimensional iterate `Dth1Iter` of `D_θ` is the iterate `LopIter` of `Lop`. -/
theorem Dth1Iter_eq_LopIter (i : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter i u = LopIter i u := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Elliptic.Dth1Iter_succ, LopIter_succ, ih]
      rfl

/-! ## The `θ`-slice groups of the `ℋ^k`-integrand -/

/-- The `j`-th *radial slice group* of the `ℋ^k`-integrand: the value
`(D_z^j f z θ · w(z)/sin(2θ)^{η/2})²` of the pure radial term together with the contributions
`(D_z^j D_θ^i f z θ · W(z,θ))²`, `1 ≤ i ≤ k - j`, of all the mixed terms carried by the
`j`-th radial derivative. -/
def sliceGroup (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter j f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    + ∑ i ∈ Finset.Icc 1 (k - j), (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- Each slice group is a sum of squares, hence nonnegative. -/
theorem sliceGroup_nonneg (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ sliceGroup α k j f z θ := by
  rw [sliceGroup]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- **The `ℋ^k`-integrand re-summed by radial slice.**  The `k+1` radial derivatives of `f`
and the mixed derivatives carried by them partition the `k+1` terms of the first sum and the
`{1 ≤ i, i + j ≤ k}` terms of the second sum of `HkIntegrand` into the slice groups. -/
theorem HkIntegrand_eq_slice_sum (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ
      = ∑ j ∈ Finset.range (k + 1), sliceGroup α k j f z θ := by
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∑ j ∈ Finset.range (k + 1), (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => sum_range_ite_eq_sum_Icc k j
      (fun i => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
  rw [Work.Spaces.HkIntegrand]
  simp only [sliceGroup]
  rw [Finset.sum_add_distrib, h1, h2]

/-! ## The weight algebra of a single summand -/

/-- The pure radial summand of the `ℋ^k`-integrand is `w(z)²` times the `η`-weighted square
of `u = D_z^j f z θ`. -/
theorem rad_term_eq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z u : ℝ) :
    (u * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (u ^ 2 * sEta θ) := by
  rw [mul_pow, w_div_sin_sq hθ z, sEta_eq_thEta]
  ring

/-- The mixed summand of the `ℋ^k`-integrand is `w(z)²` times the `γ`-weighted square of
`v = D_z^j D_θ^i f z θ`. -/
theorem mix_term_eq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (α z v : ℝ) :
    (v * Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * (v ^ 2 * sGam α θ) := by
  rw [mul_pow, Wt_sq hθ α z, sGam_eq_thGam]
  ring

/-- The pure radial summand of the `ℋ^k`-integrand is a summand of the `j`-th slice group. -/
theorem rad_le_sliceGroup (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ sliceGroup α k j f z θ := by
  rw [sliceGroup]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Each individual mixed summand of the `j`-th slice group is bounded by the group. -/
theorem mix_le_sliceGroup (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 (k - j)) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ sliceGroup α k j f z θ := by
  rw [sliceGroup]
  refine le_trans (Finset.single_le_sum
    (f := fun i => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
    (fun i _ => sq_nonneg _) hi) (le_add_of_nonneg_left (sq_nonneg _))

/-- Every slice group is a summand of the `ℋ^k`-integrand. -/
theorem sliceGroup_le_HkIntegrand (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hj : j ∈ Finset.range (k + 1)) :
    sliceGroup α k j f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [HkIntegrand_eq_slice_sum α k f z θ]
  exact Finset.single_le_sum (fun j _ => sliceGroup_nonneg α k j f z θ) hj

/-! ## `D_θ` commutes with every `D_z` on the open quadrant -/

/-- **Commutation of the mixed derivatives on the open quadrant.**

For a function which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` — the standing
smoothness hypothesis of the slice decomposition, and strictly weaker than `SmoothNbhd` — the
operators `D_z = z∂_z` and `D_θ = sin(2θ)∂_θ` commute at every point of the open quadrant:
`D_θ^i (D_z^j f) = D_z^j (D_θ^i f) = mixed j i f` there.  This is the open-quadrant
counterpart of `Work.FTS.EllipticEst.DthIter_DzIter`, which needs `C^∞` on a neighbourhood of
the *closed* quadrant; here the identity is only available on the open quadrant, which is
however all that is needed for the `θ`-integrals (a.e. in `θ`, for every `z > 0`). -/
theorem DthIter_DzIter_eq_mixed_open {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (j i : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j i f z θ := by
  have hV : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_infty.mpr hf
  -- `C²` at every point of the open quadrant, from smoothness there
  have hcd2 : ∀ {g : ℝ → ℝ → ℝ} {a b : ℝ}, (a, b) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
        : Set (ℝ × ℝ)) →
      ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ContDiffAt ℝ 2 (Function.uncurry g) (a, b) :=
    fun {g} {a b} hy hg => (hg.contDiffAt (hV.mem_nhds hy)).of_le (by simp)
  -- one `D_θ` moves across a single `D_z` (Clairaut)
  have hstep : ∀ {g : ℝ → ℝ → ℝ},
      ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ∀ {a b : ℝ}, (a, b) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) →
      Work.Spaces.Dth (Work.Spaces.Dz g) a b = Work.Spaces.Dz (Work.Spaces.Dth g) a b :=
    fun {g} hg {a b} hy => (Work.Spaces.Dz_Dth_comm (hcd2 hy hg)).symm
  -- one `D_θ` moves across `j` copies of `D_z`
  have hA : ∀ (g : ℝ → ℝ → ℝ),
      ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ∀ {a b : ℝ}, (a, b) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) →
      Work.Spaces.Dth (Work.Spaces.DzIter j g) a b
        = Work.Spaces.DzIter j (Work.Spaces.Dth g) a b := by
    intro g hg
    induction j with
    | zero => intro a b hy; rfl
    | succ j ih =>
        have hgj : ContDiffOn ℝ Work.Stability.smoothOrder
            (Function.uncurry (Work.Spaces.DzIter j g))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          Work.FTS.LocData.contDiffOn_DzIter hV hg j
        intro a b hy
        show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) a b
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dth g)) a b
        rw [hstep hgj hy]
        show a * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter j g)) a b
          = a * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.Dth g)) a b
        have hEq : ∀ y ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
            Work.Spaces.Dth (Work.Spaces.DzIter j g) y.1 y.2
              = Work.Spaces.DzIter j (Work.Spaces.Dth g) y.1 y.2 := fun y hy => ih hy
        rw [Work.Spaces.pz_congr_of_isOpen hV
          (f := Work.Spaces.Dth (Work.Spaces.DzIter j g))
          (f' := Work.Spaces.DzIter j (Work.Spaces.Dth g)) hEq hy]
  -- `i` copies of `D_θ` move across `j` copies of `D_z`
  have hB : ∀ {a b : ℝ}, (a, b) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) →
      Work.Spaces.DthIter i (Work.Spaces.DzIter j f) a b
        = Work.Spaces.DzIter j (Work.Spaces.DthIter i f) a b := by
    induction i with
    | zero => intro a b hy; rfl
    | succ i ih =>
        have hgi : ContDiffOn ℝ Work.Stability.smoothOrder
            (Function.uncurry (Work.Spaces.DthIter i f))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          Work.FTS.LocData.contDiffOn_DthIter hV hsm i
        intro a b hy
        show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter j f)) a b
          = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.DthIter i f)) a b
        have hcon : Work.Spaces.Dth
              (Work.Spaces.DthIter i (Work.Spaces.DzIter j f)) a b
            = Work.Spaces.Dth
              (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) a b := by
          show Real.sin (2 * b)
                * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.DzIter j f)) a b
              = Real.sin (2 * b)
                * Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) a b
          have hEq : ∀ y ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
              Work.Spaces.DthIter i (Work.Spaces.DzIter j f) y.1 y.2
                = Work.Spaces.DzIter j (Work.Spaces.DthIter i f) y.1 y.2 := fun y hy => ih hy
          rw [Work.Spaces.pth_congr_of_isOpen hV
            (f := Work.Spaces.DthIter i (Work.Spaces.DzIter j f))
            (f' := Work.Spaces.DzIter j (Work.Spaces.DthIter i f)) hEq hy]
        rw [hcon]
        exact hA (Work.Spaces.DthIter i f) hgi hy
  exact hB ⟨hz, hθ⟩

/-! ## Continuity on the open quadrant, and the `SmoothOpen` form of the commutation -/

/-- The product weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Q0 := by
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1))
  refine hw.mul ?_
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The uncurried `j`-th slice group is continuous on the open quadrant. -/
theorem continuousOn_sliceGroup_Q0 {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (α : ℝ) (k j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => sliceGroup α k j F p.1 p.2) Q0 := by
  have hrad : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j F p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
    (((hF.DzIter j).continuousOn).mul continuousOn_wdivsin_Q0).pow 2
  have hmix : ContinuousOn (fun p : ℝ × ℝ =>
      ∑ i ∈ Finset.Icc 1 (k - j),
        (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) Q0 :=
    continuousOn_finsetSum _ fun i _ =>
      (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
  have hfun : (fun p : ℝ × ℝ => sliceGroup α k j F p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.DzIter j F p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact hrad.add hmix

/-- The slice group vanishes at `z = 0`. -/
theorem sliceGroup_zero_left (α : ℝ) (k j : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    sliceGroup α k j F 0 θ = 0 := by
  rw [sliceGroup]
  simp [Work.FTS.EllipticEst.w_zero, Work.FTS.EllipticEst.Wt_zero]

/-- The `SmoothOpen` form of the open-quadrant commutation
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open`. -/
theorem SmoothOpen.DthIter_DzIter_eq_mixed {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (j i : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j F) z θ = Work.Spaces.mixed j i F z θ :=
  DthIter_DzIter_eq_mixed_open (fun n => hF.forall n) j i hz hθ

/-- **The mixed summand of the `ℋ^k`-integrand is integrable on the angular slice.**  For `F`
which is `C^∞` on the open quadrant (`SmoothOpen`) and in `ℋ^k` (`Work.Spaces.HkMem`), every
weighted mixed derivative `(D_z^j D_θ^i F · W)²` with `1 ≤ i`, `i + j ≤ k` is `θ`-integrable on
`Iθ`, for every `z ∈ Iz` (at `z = 0` the weight `Wt α 0 θ = 0` vanishes, so the summand is
identically `0`).  This is the open-quadrant analogue of
`Work.FTS.EllipticEst.integrableOn_zSummand` (the pure `D_z`-summand case). -/
theorem integrableOn_mixedSummand (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [show (fun θ : ℝ => (Work.Spaces.mixed j i F 0 θ * Work.Spaces.Wt α 0 θ) ^ 2)
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [Wt_zero]; simp]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmem.1 z hz) ?_ ?_
    · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
        (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hzpos).pow 2
    · rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij

/-! ## Two integration utilities on `Iθ` -/

/-- `Iθ = [0,π/2]` and the open interval differ by the two null endpoints. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2))).symm

/-- Two functions of `θ` which agree on the *open* interval have the same integral over `Iθ`. -/
theorem setIntegral_Iθ_congr_of_forall_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f θ = g θ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Work.Spaces.Iθ, g θ := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact MeasureTheory.integral_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h)

end Work.FTS.EllipticEst
