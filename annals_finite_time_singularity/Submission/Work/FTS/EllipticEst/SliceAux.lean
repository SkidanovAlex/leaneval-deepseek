/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice bookkeeping for the `θ`-Poincaré estimate `theta_poincare_Hk`

Auxiliary facts identifying the one-dimensional slices of the two-dimensional objects of
`Work.Spaces`: smoothness and vanishing of the slices, the commutation identities between the
operators `D_z`, `D_θ` and the plain partial derivatives, and the two weight identifications
`(w / sin(2θ)^{η/2})² = w²·sin(2θ)^{-η}`, `(Wt)² = w²·sin(2θ)^{-γ}`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.pth_DzIter
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

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

/-! ## Slices of a `SmoothNbhd` function -/

/-- The `θ`-slice of a function smooth on a neighbourhood of the closed quadrant is smooth on
an open neighbourhood of `Iθ`. -/
lemma sliceSmooth_of_SmoothNbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) : SliceSmooth (fun θ => g z θ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : Set.MapsTo (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := fun t ht => ⟨hz1, ht⟩
  have h := hg.comp hp hmap
  simpa [SliceSmooth, Function.comp_def, Function.uncurry] using h

/-- `D_z^j f` vanishes on the two angular boundary lines. -/
lemma DzIter_boundary_zero {f : ℝ → ℝ → ℝ} (hvan : Work.Spaces.VanishTheta f) (j : ℕ) :
    (∀ z : ℝ, -1 < z → Work.Spaces.DzIter j f z 0 = 0) ∧
      (∀ z : ℝ, -1 < z → Work.Spaces.DzIter j f z (Real.pi / 2) = 0) := by
  constructor
  · induction j with
    | zero => intro z _; simpa using hvan.1 z
    | succ j ih =>
        intro z hz
        have hev : (fun z' : ℝ => Work.Spaces.DzIter j f z' 0) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih z' hz'
        have hd : deriv (fun z' : ℝ => Work.Spaces.DzIter j f z' 0) z = 0 := by
          rw [hev.deriv_eq]; simp
        show z * Work.Spaces.pz (Work.Spaces.DzIter j f) z 0 = 0
        simp only [Work.Spaces.pz]
        rw [hd, mul_zero]
  · induction j with
    | zero => intro z _; simpa using hvan.2 z
    | succ j ih =>
        intro z hz
        have hev : (fun z' : ℝ => Work.Spaces.DzIter j f z' (Real.pi / 2))
            =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih z' hz'
        have hd : deriv (fun z' : ℝ => Work.Spaces.DzIter j f z' (Real.pi / 2)) z = 0 := by
          rw [hev.deriv_eq]; simp
        show z * Work.Spaces.pz (Work.Spaces.DzIter j f) z (Real.pi / 2) = 0
        simp only [Work.Spaces.pz]
        rw [hd, mul_zero]

/-! ## Identifications of the operators -/

/-- `D_θ^i (D_z^j f) = D_z^j D_θ^i f` at points of the closed quadrant. -/
lemma DthIter_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j i : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j i f z θ := by
  have h := Work.Spaces.mixed_comm f hsm 0 i j 0 z θ hz hθ
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, zero_add] at h
  exact h

/-- `LopIter` applied to a slice is the corresponding `D_θ`-iterate of the two-variable
function. -/
lemma LopIter_slice (i : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    LopIter i (fun θ => g z θ) = fun θ => Work.Spaces.DthIter i g z θ := by
  funext θ
  show (Work.Spaces.Lop^[i]) (fun θ => g z θ) θ = Work.Spaces.DthIter i g z θ
  rw [← Work.Spaces.DthIter_eq_iterate_Lop i g z]

/-- The second `θ`-derivative of the slice `θ ↦ D_z^j f z θ` is the slice of `D_z^j (∂_θ² f)`. -/
lemma sliceV_DzIter {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hsm1 : Work.Spaces.SmoothNbhd (Work.Spaces.pth f) := Work.Spaces.SmoothNbhd.pth hsm
  have hnb : ∀ θ' ∈ Set.Ioo (-1) (Real.pi / 2 + 1), (z, θ') ∈ Work.Spaces.nbhU :=
    fun θ' hθ' => ⟨Set.mem_Ioi.mpr (by linarith [hz0]), hθ'⟩
  have hU1 : ∀ θ' ∈ Set.Ioo (-1) (Real.pi / 2 + 1),
      Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ' :=
    fun θ' hθ' => Work.Elliptic.pth_DzIter_eqOn f hsm j (hnb θ' hθ')
  have hU2 : ∀ θ' ∈ Set.Ioo (-1) (Real.pi / 2 + 1),
      Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.pth f)) z θ' :=
    fun θ' hθ' => Work.Elliptic.pth_DzIter_eqOn (Work.Spaces.pth f) hsm1 j (hnb θ' hθ')
  have hθmem : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hev1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    exact hU1 θ' hθ'
  have h2 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
  rw [h2]
  have e1 : sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ := rfl
  rw [e1, hev1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [e2]
  exact hU2 θ hθmem

/-- `D_z^j (pth f)` is the `θ`-derivative of the `D_z^j`-slice. -/
lemma DzIter_pth_eq_deriv {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (j : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ := by
  have hθmem : θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hz0 : (0 : ℝ) ≤ z := hz
  have hnb : (z, θ) ∈ Work.Spaces.nbhU :=
    ⟨Set.mem_Ioi.mpr (by show (-1 : ℝ) < z; linarith [hz0]), hθmem⟩
  exact (Work.Elliptic.pth_DzIter_eqOn f hsm j hnb).symm

/-! ## The weight identifications -/

lemma w_div_sin_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z : ℝ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * thEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have h2 : (thEta θ)⁻¹ = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [thEta, Real.rpow_neg hs, inv_inv]
  rw [div_pow, h1, div_eq_mul_inv, ← h2, inv_inv]

lemma Wt_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (α z : ℝ) :
    (Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * thGam α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1, thGam]

/-- At `z = 0` the weight `w` vanishes, hence the whole `H^k`-integrand. -/
lemma w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]

lemma Wt_zero (α θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt, w_zero]

lemma HkIntegrand_zero_left (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k g 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand, w_zero, Wt_zero]
  simp

end Work.FTS.EllipticEst
