import ChallengeDeps
import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.residGn.BoxDefs
import Submission.Work.Diff.STE.Lead.GalTame.residMatEnergy
import Submission.Work.Diff.STE.Lead.GalTame.residPerEnergy
import Submission.Work.Diff.STE.Lead.GalTame.Level
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.jet_bound_of_tsupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `residInnerEnergy`: the `Hᵐ` energy of the two inner components of the residual

The state at which the outer function of the sharp residual estimate is evaluated is
`(z, Mper D h j z, Nper D h j z)`, where

* `Mper D h j z p q = ∑' k, boxChi D j (z + k) · mat j h p q (z + k)` is the **periodisation of the
  cut-off chart matrix**, and
* `Nper D h j z p q r = ∑' k, ∂_r (boxChi D j · mat j h p q) (z + k)` is the periodisation of its
  first jet.

This file proves that both are controlled, in the `Hᵐ` energy `ENormSq m` over the unit cube, by the
`H^{m+1}` energy `ENormB (m+1) h` of the section, with a single constant working for all sections
`h` with smooth chart data.

The proof is an assembly of already proved ingredients:

* `residPerEnergy`: for a smooth function supported in the open unit cube, `ENormSq m` of its
  periodisation is bounded by its centred-cube energy;
* `residMatEnergy`: the centred-cube energy of `φ · mat j h a b` is bounded by `1 + ENormB m h`
  (via a pointwise reconstruction of the chart matrix from the periodised components `Rper`), for any
  cut-off `φ` whose derivatives up to order `m` are bounded by a constant `Kφ`;
* `Work.Diff.STE.B3.jet_bound_of_tsupport`: such a `Kφ` exists for the box cut-off and is
  independent of `h`;
* `ENormSq_Rper_le_succ` (Poincaré, `Level`): `ENormB m h ≤ C · ENormB (m+1) h`.

Two structural facts about the periodisation are proved here:

* `gal_ofReal_tsum`: complexification commutes with the infinite sum (no summability needed: case
  split on summability);
* `gal_pdR_tmPer`: the first partial derivative of the real periodisation `tmPer f = ∑' k, f (·+k)` is
  the periodisation of the derivative.  At each point `z` the explicit finite index set
  `galIdxSet z` of lattice vectors that can contribute nearby is exhibited (`tsupport f ⊆ ball 0 R`
  with `R ≤ 1/2` forces two distinct lattice translates to be disjoint), the resulting finite sum is
  differentiated, and the result is re-identified with `tmPer (∂_r f)`.

For `Nper` the derivative identity is used as follows: `Nper` is the periodisation of
`∂_r (φ · mat)`, hence its complexification is `∂_r` of (the complexification of) `Mper`, so its
`Hᵐ` energy is bounded by the `H^{m+1}` energy of `Mper`, and `residPerEnergy` + `residMatEnergy` at
level `m+1` bound the latter by `1 + ENormB (m+1) h`.
-/

namespace Work.Diff.STE.Lead.GalTame

noncomputable section

set_option maxHeartbeats 200000

open MeasureTheory BigOperators Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Complexification and the periodisation -/

/-- The complexification commutes with an infinite sum.  No summability hypothesis is needed: if
the real family is summable this is `ContinuousLinearMap.map_tsum` for `Complex.ofRealCLM`, and if
it is not, then neither is its complexification, so both sides vanish. -/
theorem gal_ofReal_tsum {β : Type*} (g : β → ℝ) :
    ((∑' k, g k : ℝ) : ℂ) = ∑' k, ((g k : ℝ) : ℂ) := by
  by_cases hg : Summable g
  · simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.map_tsum hg
  · have hg' : ¬ Summable (fun k => ((g k : ℝ) : ℂ)) := fun h =>
      hg (by simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.summable h)
    rw [tsum_eq_zero_of_not_summable hg, tsum_eq_zero_of_not_summable hg', Complex.ofReal_zero]

/-- The real periodisation `tmPer` of `B3.transport_tame_defs` is the plain sum of the translates:
`tmPer` is the real part of the complex periodisation, and the real part commutes with the sum. -/
theorem gal_tmPer_eq_tsum {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    Work.Diff.STE.B3.tmPer f z = ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) := by
  show (∑' m : Fin n → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)).re
    = ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m)
  rw [← gal_ofReal_tsum (fun m : Fin n → ℤ => f (z + Work.Diff.STE.iVec m))]
  simp

/-- The periodisation of a real function, as a complex-valued function, is the complexification of
its `tmPer`. -/
theorem gal_perC_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, ((f (z + Work.Diff.STE.iVec k) : ℝ) : ℂ))
      = fun z : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f z : ℝ) : ℂ) := by
  funext z
  rw [gal_tmPer_eq_tsum (f := f) (z := z), gal_ofReal_tsum]

/-! ## 2. The explicit finite index set of the periodisation -/

/-- The lattice vectors that can contribute to the periodisation of a function supported in the
closed ball of radius `1/2` at a point `z`: the box of half-width `⌊‖z‖⌋ + 2` in every coordinate.
At most **one** of them can be active for a function supported in `ball 0 R`, `R ≤ 1/2`. -/
def galIdxSet {n : ℕ} (z : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(⌊|z i|⌋ + 2)) (⌊|z i|⌋ + 2))

/-- **Membership in `galIdxSet`.**  If `w` is within `1/2` of `z` in every coordinate and the
translate `w + m` meets the ball of radius `R ≤ 1/2` around the origin, then `m ∈ galIdxSet z`. -/
theorem gal_mem_galIdxSet {n : ℕ} {R : ℝ} (hR : R ≤ 1 / 2) {z w : Fin n → ℝ} {m : Fin n → ℤ}
    (hw : ∀ i, |w i - z i| < 1 / 2) (hmem : w + Work.Diff.STE.iVec m ∈ Metric.ball 0 R) :
    m ∈ galIdxSet z := by
  have hnorm : ‖w + Work.Diff.STE.iVec m‖ < R := by
    rwa [Metric.mem_ball, dist_zero_right] at hmem
  rw [galIdxSet, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : |(w + Work.Diff.STE.iVec m) i| ≤ ‖w + Work.Diff.STE.iVec m‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (w + Work.Diff.STE.iVec m) i
  have h2 : (w + Work.Diff.STE.iVec m) i = w i + (m i : ℝ) := by simp
  have h3 : |w i + (m i : ℝ)| < R := by
    rw [← h2]; exact lt_of_le_of_lt h1 hnorm
  have h4 : |w i| < |z i| + 1 / 2 := by
    have hw' := hw i
    have h5 : |w i| ≤ |w i - z i| + |z i| := by
      calc |w i| = |(w i - z i) + z i| := by ring_nf
        _ ≤ |w i - z i| + |z i| := abs_add_le _ _
    linarith
  have h5 : |(m i : ℝ)| < |z i| + 1 := by
    have h6 : |(m i : ℝ)| ≤ |w i + (m i : ℝ)| + |w i| := by
      simpa using abs_sub_le (w i + (m i : ℝ)) 0 (w i)
    linarith
  have h6 : |(m i : ℝ)| < ((⌊|z i|⌋ + 2 : ℤ) : ℝ) := by
    have h7 := Int.lt_floor_add_one (|z i|)
    push_cast
    linarith
  have h7 : |m i| < ⌊|z i|⌋ + 2 := by
    rw [← Int.cast_abs] at h6
    exact_mod_cast h6
  have h8 := abs_lt.mp h7
  constructor <;> omega

/-! ## 3. The first partial derivative of the periodisation -/

/-- **The derivative of the real periodisation.**  If `f` is smooth and its topological support is
contained in the ball of radius `R ≤ 1/2`, then the `r`-th partial derivative of `tmPer f` is the
periodisation of the `r`-th partial derivative of `f`. -/
theorem gal_pdR_tmPer {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {R : ℝ} (hR : R ≤ 1 / 2) (hts : tsupport f ⊆ Metric.ball 0 R) (r : Fin n) :
    Work.Diff.STE.pdR r (Work.Diff.STE.B3.tmPer f)
      = Work.Diff.STE.B3.tmPer (Work.Diff.STE.pdR r f) := by
  funext z
  -- on a neighbourhood of `z` the periodisation is the sum over the finite set `galIdxSet z`
  have hloc : ∀ w : Fin n → ℝ, (∀ i, |w i - z i| < 1 / 2) →
      Work.Diff.STE.B3.tmPer f w = ∑ m ∈ galIdxSet z, f (w + Work.Diff.STE.iVec m) := by
    intro w hw
    rw [gal_tmPer_eq_tsum (f := f) (z := w)]
    rw [tsum_eq_sum (s := galIdxSet z) (fun m hm => ?_)]
    by_contra hc
    exact hm (gal_mem_galIdxSet hR hw (hts (subset_tsupport f (Function.mem_support.mpr hc))))
  -- and so is the periodisation of the derivative, at `z` itself
  have hlocg : Work.Diff.STE.B3.tmPer (Work.Diff.STE.pdR r f) z
      = ∑ m ∈ galIdxSet z, Work.Diff.STE.pdR r f (z + Work.Diff.STE.iVec m) := by
    rw [gal_tmPer_eq_tsum (f := Work.Diff.STE.pdR r f) (z := z)]
    rw [tsum_eq_sum (s := galIdxSet z) (fun m hm => ?_)]
    by_contra hc
    have hmem : z + Work.Diff.STE.iVec m ∈ tsupport f := by
      by_contra hnb
      rw [notMem_tsupport_iff_eventuallyEq] at hnb
      refine hc ?_
      simp only [Work.Diff.STE.pdR]
      rw [hnb.fderiv_eq]
      simp
    exact hm (gal_mem_galIdxSet hR (fun i => by simp) (hts hmem))
  -- the derivative of the finite sum
  have hderiv : Work.Diff.STE.pdR r (Work.Diff.STE.B3.tmPer f) z
      = ∑ m ∈ galIdxSet z, Work.Diff.STE.pdR r f (z + Work.Diff.STE.iVec m) := by
    have hBopen : IsOpen (Set.pi Set.univ
        (fun i : Fin n => Set.Ioo (z i - 1 / 2) (z i + 1 / 2))) :=
      isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
    have hzB : z ∈ Set.pi Set.univ (fun i : Fin n => Set.Ioo (z i - 1 / 2) (z i + 1 / 2)) := by
      rw [Set.mem_pi]
      intro i _
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hev : (fun y => ∑ m ∈ galIdxSet z, f (y + Work.Diff.STE.iVec m))
        =ᶠ[nhds z] Work.Diff.STE.B3.tmPer f := by
      refine Filter.eventually_of_mem (hBopen.mem_nhds hzB) (fun y hy => ?_)
      exact (hloc y (fun i => by
        have h := Set.mem_pi.mp hy i (Set.mem_univ i)
        rw [Set.mem_Ioo] at h
        rw [abs_lt]
        exact ⟨by linarith [h.1], by linarith [h.2]⟩)).symm
    have hsum : (fun y => ∑ m ∈ galIdxSet z, f (y + Work.Diff.STE.iVec m))
        = ∑ m ∈ galIdxSet z, (fun y => f (y + Work.Diff.STE.iVec m)) := by
      funext y
      rw [Finset.sum_apply]
    have h2 : fderiv ℝ (Work.Diff.STE.B3.tmPer f) z
        = ∑ m ∈ galIdxSet z, fderiv ℝ (fun y => f (y + Work.Diff.STE.iVec m)) z := by
      rw [hev.symm.fderiv_eq, hsum]
      exact fderiv_sum (fun m _ => (hf.contDiffAt.differentiableAt (by simp)).comp z
        ((differentiable_id.differentiableAt).add_const _))
    have h3 : ∀ m, fderiv ℝ (fun y => f (y + Work.Diff.STE.iVec m)) z
        = fderiv ℝ f (z + Work.Diff.STE.iVec m) :=
      fun m => fderiv_comp_add_right (f := f) (x := z) (Work.Diff.STE.iVec m)
    simp only [Work.Diff.STE.pdR]
    rw [h2, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun m _ => by rw [h3 m])
  rw [hderiv, hlocg]

/-! ## 4. `∂_r` raises the level of the energy by one -/

/-- The complexified iterated partial derivative of order `m` following `∂_r` is the iterated
partial derivative of order `m + 1` along `Fin.snoc γ r`. -/
theorem gal_pdVec_pd_eq_pdVec_snoc {n : ℕ} (m : ℕ) (γ : Fin m → Fin n) (c : Fin n)
    (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdVec m γ (Work.Diff.STE.pd c (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)))
      = Work.Diff.STE.pdVec (m + 1) (Fin.snoc γ c) (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) := by
  funext z
  rw [Work.Diff.STE.Lead.Gal.pd_ofReal c f]
  rw [Work.Diff.STE.Lead.Gal.ofRealPdVecDict m γ (Work.Diff.STE.pdR c f)]
  show ((Work.Diff.STE.pdRVec m γ (Work.Diff.STE.pdR c f) z : ℝ) : ℂ)
    = Work.Diff.STE.pdVec (m + 1) (Fin.snoc γ c) (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z
  rw [Work.Diff.STE.B3.pdRVec_pdR_eq_pdRVec_snoc m γ c f z]
  exact (congrFun (Work.Diff.STE.Lead.Gal.ofRealPdVecDict (m + 1) (Fin.snoc γ c) f) z).symm

/-- **`∂_r` raises the energy level**: the `Hᵐ` energy of the complexified partial derivative of a
real function is bounded by its `H^{m+1}` energy.  (No periodicity is needed: the iterated
derivatives following `∂_r` are the order-`m+1` derivatives along `Fin.snoc _ r`, and the index set
`Fin m → ι` embeds into `Fin (m+1) → ι`.) -/
theorem gal_ENormSq_pd_le {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (r : Fin n) :
    Work.Diff.STE.ENormSq m (Work.Diff.STE.pd r (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)))
      ≤ Work.Diff.STE.ENormSq (m + 1) (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) := by
  rw [Work.Diff.STE.ENormSq, Work.Diff.STE.ENormSq]
  have hterm : ∀ l : Fin m → Fin n,
      (∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdVec m l
          (Work.Diff.STE.pd r (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))) x‖ ^ 2)
      = (fun l' : Fin (m + 1) → Fin n => ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec (m + 1) l' (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ^ 2)
          (Fin.snoc l r : Fin (m + 1) → Fin n) := by
    intro l
    simp only
    rw [gal_pdVec_pd_eq_pdVec_snoc m l r f]
  have hinj : Set.InjOn (fun l : Fin m → Fin n => (Fin.snoc l r : Fin (m + 1) → Fin n))
      ((Finset.univ : Finset (Fin m → Fin n)) : Set (Fin m → Fin n)) := by
    intro x _ y _ hxy
    funext i
    have := congrFun hxy i.castSucc
    simpa [Fin.snoc_castSucc] using this
  calc ∑ l : Fin m → Fin n,
        (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec m l
            (Work.Diff.STE.pd r (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))) x‖ ^ 2)
      = ∑ l : Fin m → Fin n,
          (fun l' : Fin (m + 1) → Fin n => ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec (m + 1) l' (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ^ 2)
            (Fin.snoc l r : Fin (m + 1) → Fin n) :=
        Finset.sum_congr rfl (fun l _ => hterm l)
    _ = ∑ l' ∈ (Finset.univ.image
          (fun l : Fin m → Fin n => (Fin.snoc l r : Fin (m + 1) → Fin n))),
          (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec (m + 1) l' (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ^ 2) :=
        (Finset.sum_image
          (f := fun l' : Fin (m + 1) → Fin n => ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec (m + 1) l' (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ^ 2)
          (s := Finset.univ)
          (g := fun l : Fin m → Fin n => (Fin.snoc l r : Fin (m + 1) → Fin n)) hinj).symm
    _ ≤ ∑ l' : Fin (m + 1) → Fin n,
          (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec (m + 1) l' (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr (fun l _ => Finset.mem_univ _))
          (fun l' _ _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))

/-! ## 5. Smoothness and support of the cut-off chart matrix -/

/-- The complexification does not change the topological support. -/
theorem gal_tsupport_ofReal_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    tsupport (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) = tsupport f := by
  have hsupp : Function.support (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) = Function.support f := by
    ext z
    simp only [Function.mem_support]
    exact not_congr Complex.ofReal_eq_zero
  rw [tsupport, tsupport, hsupp]

/-- **The cut-off chart matrix is globally smooth.**  The chart matrix `D.mat j h a b` is smooth at
every point whose flat coordinate lies in the chart target (`mat_contDiffAt_of_target`), in
particular on the closed `2σ_j`-ball; off the topological support of the box cut-off (that ball) the
product vanishes identically on a neighbourhood. -/
theorem gal_contDiff_boxChi_mul_mat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ResidGn.boxChi (I := I) (M := M) D j z
        * D.mat j h a b z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j)
  · have hzle : ‖z‖ ≤ 2 * D.σ j := by
      have h' : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) := by
        rw [← ResidGn.boxChi_tsupport (I := I) (M := M) D j]
        exact hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h'
    exact ((ResidGn.boxChi_contDiff (I := I) (M := M) D j).contDiffAt).mul
      (Work.Diff.STE.Lead.Gal.mat_contDiffAt_of_target D h hh j a b (D.htarget j z hzle))
  · have hnear : ∀ᶠ y in nhds z, y ∉ tsupport (ResidGn.boxChi (I := I) (M := M) D j) :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hz
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- The complexification of the cut-off chart matrix is smooth. -/
theorem gal_contDiff_ofReal_boxChi_mul_mat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h a b z : ℝ) : ℂ)) :=
  (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp
    (gal_contDiff_boxChi_mul_mat (I := I) (M := M) D h hh j a b)

/-- The topological support of the complexified cut-off chart matrix is contained in the open unit
cube: it sits in the closed ball of radius `2σ_j ≤ 1/4`, whose points have all coordinates of
modulus `< 1/2`. -/
theorem gal_tsupport_ofReal_boxChi_mul_mat_subset
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h a b z : ℝ) : ℂ))
      ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz
  have h1 : z ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j) := by
    rw [gal_tsupport_ofReal_eq
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h a b z)] at hz
    exact tsupport_mul_subset_left hz
  rw [ResidGn.boxChi_tsupport (I := I) (M := M) D j, Metric.mem_closedBall, dist_zero_right] at h1
  intro i _
  rw [Set.mem_Ioo]
  have h2 : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
  have h3 : 2 * D.σ j ≤ 1 / 4 := D.hσ2 j
  exact abs_lt.mp (by linarith)

/-- The topological support of the cut-off chart matrix is contained in the open ball of radius
`1/2` (since its radius `2σ_j` is at most `1/4`). -/
theorem gal_tsupport_boxChi_mul_mat_subset_ball
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h a b z)
      ⊆ Metric.ball 0 (1 / 2 : ℝ) := by
  intro z hz
  have h1 : z ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j) := tsupport_mul_subset_left hz
  rw [ResidGn.boxChi_tsupport (I := I) (M := M) D j, Metric.mem_closedBall, dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right]
  have h3 : 2 * D.σ j ≤ 1 / 4 := D.hσ2 j
  linarith

/-! ## 6. The two identifications with the periodisation -/

/-- `Mper` is the periodisation of the cut-off chart matrix. -/
theorem gal_Mper_eq_perC (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (p q : Fin (Module.finrank ℝ E)) :
    (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ))
      = fun z => ∑' k : Fin (Module.finrank ℝ E) → ℤ,
          (((fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)
            (z + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
  funext z
  have hM : ResidGn.Mper (I := I) (M := M) D h j z p q
      = ∑' k : Fin (Module.finrank ℝ E) → ℤ,
          ResidGn.boxChi (I := I) (M := M) D j (z + Work.Diff.STE.iVec k)
            * D.mat j h p q (z + Work.Diff.STE.iVec k) := rfl
  rw [hM, gal_ofReal_tsum]

/-- `Nper` is the periodisation of the first jet of the cut-off chart matrix. -/
theorem gal_Nper_eq_perC (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (p q r : Fin (Module.finrank ℝ E)) :
    (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ))
      = fun z => ∑' k : Fin (Module.finrank ℝ E) → ℤ,
          (((fun y => Work.Diff.STE.pdR r
              (fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) y)
            (z + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
  funext z
  have hN : ResidGn.Nper (I := I) (M := M) D h j z p q r
      = ∑' k : Fin (Module.finrank ℝ E) → ℤ,
          Work.Diff.STE.pdR r
            (fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)
            (z + Work.Diff.STE.iVec k) := rfl
  rw [hN, gal_ofReal_tsum]

/-! ## 7. The per-component energy bounds -/

/-- **The `Hᵐ` energy of the periodised cut-off chart matrix.** -/
theorem gal_Mper_ENormSq_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (p q : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ))
          ≤ C * (1 + D.ENormB m h) := by
  obtain ⟨Cper, hCper0, hCper⟩ :=
    residPerEnergy (n := Module.finrank ℝ E) (m := m)
  obtain ⟨Kφ, hKφ0, _, hKφ⟩ := Work.Diff.STE.B3.jet_bound_of_tsupport (N := m)
    (ResidGn.boxChi (I := I) (M := M) D j) (2 * D.σ j)
    (ResidGn.boxChi_contDiff (I := I) (M := M) D j)
    (ResidGn.boxChi_tsupport_subset (I := I) (M := M) D j)
  obtain ⟨CM, hCM0, hCM⟩ :=
    residMatEnergy (I := I) (M := M) D j m
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j))
      (isCompact_closedBall 0 (2 * D.σ j)) Kφ hKφ0
  refine ⟨Cper * CM, mul_nonneg hCper0 hCM0, ?_⟩
  intro h hsm p q
  have hCsm := gal_contDiff_ofReal_boxChi_mul_mat (I := I) (M := M) D h hsm j p q
  have hts := gal_tsupport_ofReal_boxChi_mul_mat_subset (I := I) (M := M) D h j p q
  calc Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ))
      = Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ∑' k : Fin (Module.finrank ℝ E) → ℤ,
            (((fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)
              (z + Work.Diff.STE.iVec k) : ℝ) : ℂ)) := by
          rw [gal_Mper_eq_perC]
    _ ≤ Cper * CENormSq m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y : ℝ) : ℂ)) :=
          hCper (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y : ℝ) : ℂ)) hCsm hts
    _ ≤ Cper * (CM * (1 + D.ENormB m h)) :=
          mul_le_mul_of_nonneg_left
            (hCM h hsm (ResidGn.boxChi (I := I) (M := M) D j)
              (ResidGn.boxChi_contDiff (I := I) (M := M) D j)
              (fun r hr γ z => hKφ r hr γ z)
              (ResidGn.boxChi_tsupport_subset (I := I) (M := M) D j)
              (fun z hz => D.htarget j z (by
                rw [Metric.mem_closedBall, dist_zero_right] at hz
                exact hz))
              p q)
            hCper0
    _ = Cper * CM * (1 + D.ENormB m h) := by ring

/-- **The `Hᵐ` energy of the periodised first jet of the cut-off chart matrix.** -/
theorem gal_Nper_ENormSq_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (p q r : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ))
          ≤ C * (1 + D.ENormB (m + 1) h) := by
  obtain ⟨Cper, hCper0, hCper⟩ :=
    residPerEnergy (n := Module.finrank ℝ E) (m := m + 1)
  obtain ⟨Kφ, hKφ0, _, hKφ⟩ := Work.Diff.STE.B3.jet_bound_of_tsupport (N := m + 1)
    (ResidGn.boxChi (I := I) (M := M) D j) (2 * D.σ j)
    (ResidGn.boxChi_contDiff (I := I) (M := M) D j)
    (ResidGn.boxChi_tsupport_subset (I := I) (M := M) D j)
  obtain ⟨CM, hCM0, hCM⟩ :=
    residMatEnergy (I := I) (M := M) D j (m + 1)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j))
      (isCompact_closedBall 0 (2 * D.σ j)) Kφ hKφ0
  refine ⟨Cper * CM, mul_nonneg hCper0 hCM0, ?_⟩
  intro h hsm p q r
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) :=
    gal_contDiff_boxChi_mul_mat (I := I) (M := M) D h hsm j p q
  have hWball := gal_tsupport_boxChi_mul_mat_subset_ball (I := I) (M := M) D h j p q
  have hCsm := gal_contDiff_ofReal_boxChi_mul_mat (I := I) (M := M) D h hsm j p q
  have hts := gal_tsupport_ofReal_boxChi_mul_mat_subset (I := I) (M := M) D h j p q
  -- `Nper` is (the complexification of) the derivative of the periodisation of the cut-off matrix
  have hkey : (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ))
      = Work.Diff.STE.pd r (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.tmPer (fun y =>
            ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) z : ℝ) : ℂ)) := by
    rw [gal_Nper_eq_perC]
    rw [gal_perC_eq (Work.Diff.STE.pdR r
      (fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y))]
    rw [← gal_pdR_tmPer hWsm le_rfl hWball r]
    rw [← Work.Diff.STE.Lead.Gal.pd_ofReal r (Work.Diff.STE.B3.tmPer
      (fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y))]
  calc Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ))
      = Work.Diff.STE.ENormSq m (Work.Diff.STE.pd r
          (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.tmPer (fun y =>
              ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) z : ℝ) : ℂ))) := by
          rw [hkey]
    _ ≤ Work.Diff.STE.ENormSq (m + 1) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.tmPer (fun y =>
            ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) z : ℝ) : ℂ)) :=
          gal_ENormSq_pd_le (n := Module.finrank ℝ E) (m := m)
            (Work.Diff.STE.B3.tmPer (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)) r
    _ = Work.Diff.STE.ENormSq (m + 1) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ∑' k : Fin (Module.finrank ℝ E) → ℤ,
            (((fun y => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)
              (z + Work.Diff.STE.iVec k) : ℝ) : ℂ)) := by
          rw [← gal_perC_eq (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)]
    _ ≤ Cper * CENormSq (m + 1)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y : ℝ) : ℂ)) :=
          hCper (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y : ℝ) : ℂ)) hCsm hts
    _ ≤ Cper * (CM * (1 + D.ENormB (m + 1) h)) :=
          mul_le_mul_of_nonneg_left
            (hCM h hsm (ResidGn.boxChi (I := I) (M := M) D j)
              (ResidGn.boxChi_contDiff (I := I) (M := M) D j)
              (fun r hr γ z => hKφ r hr γ z)
              (ResidGn.boxChi_tsupport_subset (I := I) (M := M) D j)
              (fun z hz => D.htarget j z (by
                rw [Metric.mem_closedBall, dist_zero_right] at hz
                exact hz))
              p q)
            hCper0
    _ = Cper * CM * (1 + D.ENormB (m + 1) h) := by ring

/-! ## 8. Level monotonicity of the energy `ENormB` -/

/-- **`ENormB m h ≤ C · ENormB (m+1) h`** — the Poincaré step of `Level.ENormSq_Rper_le_succ`
summed over the charts and frame indices. -/
theorem gal_ENormB_le_succ (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
      D.ENormB m h ≤ C * D.ENormB (m + 1) h := by
  obtain ⟨C, hC0, hC⟩ := ENormSq_Rper_le_succ (I := I) (M := M) D m
  refine ⟨C, hC0, fun h hsm => ?_⟩
  rw [Work.Diff.STE.B3Data.ENormB, Work.Diff.STE.B3Data.ENormB, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hC h hsm i a b

/-! ## 9. The target -/

theorem residInnerEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
        (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.Lead.GalTame.ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ)))
          ≤ C * (1 + D.ENormB (m + 1) h) ∧
        (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            ∑ r : Fin (Module.finrank ℝ E),
            Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.Lead.GalTame.ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ)))
          ≤ C * (1 + D.ENormB (m + 1) h) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsm
    constructor <;> simp [hn]
  · obtain ⟨C2, hC20, hC2⟩ := gal_Mper_ENormSq_le (I := I) (M := M) D j m
    obtain ⟨C3, hC30, hC3⟩ := gal_Nper_ENormSq_le (I := I) (M := M) D j m
    obtain ⟨Cp, hCp0, hCp⟩ := gal_ENormB_le_succ (I := I) (M := M) D m
    refine ⟨max 1 (max ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2 * (1 + Cp))
        ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E * C3)),
      le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro h hsm
    have hE1nn : 0 ≤ D.ENormB (m + 1) h := by
      rw [Work.Diff.STE.B3Data.ENormB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ENormSq_nonneg_gal (m + 1) _
    have h1E : 0 ≤ 1 + D.ENormB (m + 1) h := by linarith
    have hEm : D.ENormB m h ≤ Cp * D.ENormB (m + 1) h := hCp h hsm
    have hup : 1 + D.ENormB m h ≤ (1 + Cp) * (1 + D.ENormB (m + 1) h) := by
      nlinarith [hEm, hE1nn, hCp0]
    constructor
    · -- the `Mper` sum
      have hsum : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ((ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ)))
          ≤ (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * (C2 * (1 + D.ENormB m h)) := by
        calc ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ((ResidGn.Mper (I := I) (M := M) D h j z p q : ℝ) : ℂ))
            ≤ ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                (C2 * (1 + D.ENormB m h)) :=
              Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hC2 h hsm p q
          _ = (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E
                * (C2 * (1 + D.ENormB m h)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      have hA0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2 :=
        mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC20
      have hstep : (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * (C2 * (1 + D.ENormB m h))
          ≤ (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2 * (1 + Cp)
            * (1 + D.ENormB (m + 1) h) := by
        calc (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * (C2 * (1 + D.ENormB m h))
            = ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2) * (1 + D.ENormB m h) := by ring
          _ ≤ ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2)
                * ((1 + Cp) * (1 + D.ENormB (m + 1) h)) :=
              mul_le_mul_of_nonneg_left hup hA0
          _ = (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2 * (1 + Cp)
                * (1 + D.ENormB (m + 1) h) := by ring
      refine (hsum.trans hstep).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ h1E
      exact le_max_of_le_right (le_max_left _ _)
    · -- the `Nper` sum
      have hsum : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ∑ r : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ)))
          ≤ (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E
              * (C3 * (1 + D.ENormB (m + 1) h)) := by
        calc ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
              ∑ r : Fin (Module.finrank ℝ E),
              Work.Diff.STE.ENormSq m (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ((ResidGn.Nper (I := I) (M := M) D h j z p q r : ℝ) : ℂ))
            ≤ ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                ∑ r : Fin (Module.finrank ℝ E), (C3 * (1 + D.ENormB (m + 1) h)) :=
              Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
                Finset.sum_le_sum fun r _ => hC3 h hsm p q r
          _ = (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E
                * (C3 * (1 + D.ENormB (m + 1) h)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      refine hsum.trans ?_
      calc (Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E
            * (C3 * (1 + D.ENormB (m + 1) h))
          = ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E * C3)
              * (1 + D.ENormB (m + 1) h) := by ring
        _ ≤ (max 1 (max ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * C2 * (1 + Cp))
              ((Module.finrank ℝ E : ℝ) * Module.finrank ℝ E * Module.finrank ℝ E * C3)))
              * (1 + D.ENormB (m + 1) h) :=
            mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) h1E

end

end Work.Diff.STE.Lead.GalTame
