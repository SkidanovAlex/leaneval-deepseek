/-
Copyright: work module for the Elgindi finite-time singularity project.

# The slice/operator identifications of the angular Poincaré estimate in the `C^∞` class

The two per-`z` comparisons of `HkIntegrand_integral_le_pth2_open` need the operators
`D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` to commute *in the honest `C^∞` class*
(`SmoothOpenθ`, i.e. `ContDiffOn ℝ ∞` on the half-strip `(0,∞) × (-1, π/2+1)`): the older
identifications of `Submission/Work/FTS/EllipticEst/SliceAux.lean` and
`ThetaSliceIdent.lean` are stated with `Work.Spaces.SmoothNbhd`, which in this Mathlib is
*analyticity* (`⊤ = ω`), hence unusable for the cut-off data of the chapter.

This module provides, for `f : SmoothOpenθ` and every level `z > 0`:

* `pth_DzIter_open` — `∂_θ (D_z^j f) = D_z^j (∂_θ f)` (Clairaut; derived from the
  single-operator identity `pz_pth_comm` and the locality of `deriv`);
* `pthIter_two_DzIter_open`, `sliceV_DzIter_open` — the second `θ`-derivative commutes with
  `D_z^j`: `(θ ↦ D_z^j f z θ)'' = D_z^j (∂_θ² f) z ·`;
* `DzIter_pth_eq_deriv_open` — `D_z^j (∂_θ f) z θ = ∂_θ(θ' ↦ D_z^j f z θ')`;
* `LopIter_congr_of_isOpen` — the angular iterate `LopIter` respects agreement on an open set;
* `LopIter_slice_DzIter_eq_mixed_open`, `LopIter_sliceV_DzIter_eq_mixed_open`,
  `LopIter_deriv_DzIter_eq_mixed_open` — the identifications of the angular iterates of the
  slices `D_z^j f z ·`, `(D_z^j f z ·)''`, `∂_θ(D_z^j f z ·)` with the mixed derivatives of
  `f`, of `∂_θ² f` and of `∂_θ f` (via the existing open-quadrant commutation
  `Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

variable {f : ℝ → ℝ → ℝ}

/-! ## Differentiability of the angular slices of `C^∞` data -/

/-- The `θ`-slice of a function that is `C^∞` on an open set is differentiable at every point
of that set. -/
private lemma differentiableAt_slice_θ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ContDiffOn ℝ smoothOrder (Function.uncurry G) V) {z θ : ℝ} (hy : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ :=
  ((hG.contDiffAt (hV.mem_nhds hy)).comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by norm_num)

/-! ## Congruence of the angular iterate on an open set -/

/-- `LopIter` respects agreement on an open set: if `u = v` on an open `V`, then so do all the
angular iterates.  (The operator `L u = sin(2θ)·u'` is local, so this is the induction
`deriv_congr` step.) -/
theorem LopIter_congr_of_isOpen {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (h : Set.EqOn u v V) (i : ℕ) :
    Set.EqOn (Work.FTS.EllipticEst.LopIter i u) (Work.FTS.EllipticEst.LopIter i v) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      intro θ hθ
      have hev : Work.FTS.EllipticEst.LopIter i u =ᶠ[𝓝 θ]
          Work.FTS.EllipticEst.LopIter i v := by
        filter_upwards [hV.mem_nhds hθ] with θ' hθ'
        exact ih hθ'
      rw [Work.FTS.EllipticEst.LopIter_succ, Work.FTS.EllipticEst.LopIter_succ]
      show Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.LopIter i u) θ
        = Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.LopIter i v) θ
      rw [hev.deriv_eq]

/-! ## Clairaut: `∂_θ` commutes with every `D_z`-iterate -/

/-- **Clairaut for `∂_θ` and `D_z^j` in the `C^∞` class.**  On the half-strip the `θ`-derivative
commutes with every iterate of `D_z = z ∂_z`. -/
theorem pth_DzIter_open (hsm : SmoothOpenθ f) (j : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ]
      have hmem : (z, θ) ∈ halfStrip := ⟨hz, hθ⟩
      -- Step 1: `∂_θ (D_z g) = D_z (∂_θ g)` at the point, for `g = D_z^j f`.
      have hdiff : DifferentiableAt ℝ
          (fun θ' => Work.Spaces.pz (Work.Spaces.DzIter j f) z θ') θ :=
        differentiableAt_slice_θ isOpen_halfStrip
          (Work.FTS.LocData.contDiffOn_pz isOpen_halfStrip
            (contDiffOn_infty.mpr (hsm.DzIter j))) hmem
      have hDz : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ := by
        have e : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f)) z θ
            = z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.DzIter j f)) z θ := by
          show deriv (fun θ' => z * Work.Spaces.pz (Work.Spaces.DzIter j f) z θ') θ = _
          rw [deriv_const_mul z hdiff]
          rfl
        rw [e, (SmoothOpenθ.pz_pth_comm (hsm.DzIter j) hz hθ).symm]
        rfl
      -- Step 2: the two `∂_θ`-derivatives agree on the half-strip by the induction hypothesis,
      -- so their `z ∂_z` agree at the point.
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
          (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) halfStrip :=
        fun y hy => ih hy.1 hy.2
      rw [hDz]
      show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter j f)) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ
      rw [Work.Spaces.pz_congr_of_isOpen isOpen_halfStrip hEq hmem]

/-- The second `θ`-derivative commutes with `D_z^j` on the half-strip. -/
theorem pthIter_two_DzIter_open (hsm : SmoothOpenθ f) (j : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hmem : (z, θ) ∈ halfStrip := ⟨hz, hθ⟩
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) halfStrip :=
    fun y hy => pth_DzIter_open hsm j hy.1 hy.2
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [Work.Spaces.pth_congr_of_isOpen isOpen_halfStrip hEq hmem]
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using
    pth_DzIter_open (hsm.pthIter 1) j hz hθ

/-- The second derivative of the slice `θ' ↦ D_z^j f z θ'` is the slice of `D_z^j (∂_θ² f)`. -/
theorem sliceV_DzIter_open (hsm : SmoothOpenθ f) (j : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  show deriv (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ = _
  rw [show deriv (fun θ' => Work.Spaces.DzIter j f z θ')
      = fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ' from rfl]
  rw [show deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ from rfl]
  exact pthIter_two_DzIter_open hsm j hz hθ

/-- `D_z^j (∂_θ f)` is the `θ`-derivative of the slice `θ' ↦ D_z^j f z θ'`. -/
theorem DzIter_pth_eq_deriv_open (hsm : SmoothOpenθ f) (j : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
  (pth_DzIter_open hsm j hz hθ).symm

/-! ## The angular iterates of the slices -/

/-- The `i`-th angular iterate of the slice `θ' ↦ D_z^j f z θ'` is `D_z^j D_θ^i f`. -/
theorem LopIter_slice_DzIter_eq_mixed_open (hsm : SmoothOpenθ f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.mixed j i f z θ := by
  rw [Work.FTS.EllipticEst.LopIter_slice i (Work.Spaces.DzIter j f) z]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hsm.to_quad j i hz hθ

/-- The `i`-th angular iterate of the second derivative of the slice `θ' ↦ D_z^j f z θ'` is
`D_z^j D_θ^i (∂_θ² f)`. -/
theorem LopIter_sliceV_DzIter_eq_mixed_open (hsm : SmoothOpenθ f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter i
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j i (Work.Spaces.pthIter 2 f) z θ := by
  have hθV : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hEq : Set.EqOn (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))
      (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ')
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    fun θ' hθ' => sliceV_DzIter_open hsm j hz hθ'
  rw [LopIter_congr_of_isOpen isOpen_Ioo hEq i hθV]
  rw [Work.FTS.EllipticEst.LopIter_slice i
    (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)) z]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open (hsm.pthIter 2).to_quad j i hz hθ

/-- The `i`-th angular iterate of the first derivative of the slice `θ' ↦ D_z^j f z θ'` is
`D_z^j D_θ^i (∂_θ f)`. -/
theorem LopIter_deriv_DzIter_eq_mixed_open (hsm : SmoothOpenθ f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter i
        (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j i (Work.Spaces.pth f) z θ := by
  have hθV : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hEq : Set.EqOn (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
      (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ')
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    intro θ' hθ'
    show Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ'
    exact pth_DzIter_open hsm j hz hθ'
  rw [LopIter_congr_of_isOpen isOpen_Ioo hEq i hθV]
  rw [Work.FTS.EllipticEst.LopIter_slice i (Work.Spaces.DzIter j (Work.Spaces.pth f)) z]
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using
    Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open (hsm.pthIter 1).to_quad j i hz hθ

end Work.FTS.EllipticEst.ThetaU
