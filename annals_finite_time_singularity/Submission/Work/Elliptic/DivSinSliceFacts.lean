import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzIterSmoothOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Set

/-- The `θ`-slice of a function smooth on an open neighbourhood of the closed quadrant is
smooth on an open neighbourhood of `Iθ`. -/
theorem smoothSlice_of_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    Work.Elliptic.SmoothSlice (fun θ => f z θ) := by
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    rw [Set.mem_Ioi]
    linarith
  have huncurry : ContDiffOn ℝ ⊤ (Function.uncurry f)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hf
  have hg : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    ((contDiff_const (c := z)).prodMk contDiff_id).contDiffOn
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    fun θ hθ => ⟨hz', hθ⟩
  have hcomp := huncurry.comp hg hmap
  simpa [Work.Elliptic.SmoothSlice, Function.comp_def, Function.uncurry] using hcomp

/-- Iterated `D_z = z ∂_z` preserves the vanishing of a function on the angular boundary. -/
theorem vanish_DzIter {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.VanishTheta f) (n : ℕ) :
    Work.Spaces.VanishTheta (Work.Spaces.DzIter n f) := by
  induction n with
  | zero => exact hf
  | succ m ih =>
    refine ⟨fun z => ?_, fun z => ?_⟩
    · have hc : (fun z' : ℝ => Work.Spaces.DzIter m f z' 0) = fun _ => 0 :=
        funext fun z' => ih.1 z'
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hc, deriv_const,
        mul_zero]
    · have hc : (fun z' : ℝ => Work.Spaces.DzIter m f z' (Real.pi / 2)) = fun _ => 0 :=
        funext fun z' => ih.2 z'
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hc, deriv_const,
        mul_zero]

theorem DivSinSliceFacts (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ)
    (hv : Work.Spaces.VanishTheta Φ) (j : ℕ) (z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ) ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) 0 = 0 ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) (Real.pi / 2) = 0 := by
  have hV : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hsm : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j Φ) :=
    Work.Spaces.DzIterSmoothOn hV hΦ j
  have hvan := vanish_DzIter hv j
  exact ⟨smoothSlice_of_smoothNbhd hsm hz, hvan.1 z, hvan.2 z⟩

end Work.Elliptic
