import Mathlib
import Submission.Work.Horn.horn_chart
import Submission.Work.Horn.horn_section_deep
import Submission.Work.Horn.hornS_deriv_of_deep_section
import Submission.Work.Horn.bu_side_false

/-!
# `Work.Horn.horn_cl_im_pos` — the positivity of `Im cl`

The lower-end asymptotic constant `cl` of the lifted horn map `d.E` (`d.E w - w → cl` as
`Im w → -∞`) has positive imaginary part.  The toolbox (chart descents `hornS`/`hornDl'`, Cartan,
the section existence, the analytic germ and the upper-side contradiction) lives in
`Submission.Work.Horn.horn_chart` and the three modules imported below.
-/

noncomputable section

open MandelDim Filter Topology Metric Set
open scoped Topology

namespace Work.Horn

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-! ## The target theorem

Assembly (in progress).  The sections of `d.E` over the two components come from
`Work.L62.lift_section` (the components are simply connected by hypothesis);
`section_add_one_eq` above makes the lower-end section `T`-equivariant, so it descends to the
bounded cylinder domain; strict Schwarz-Cartan (`Work.L62.cartan`) then forces
`‖e^{2πi cl}‖ < 1`, i.e. `0 < cl.im`. -/
theorem horn_cl_im_pos (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (η : ℝ) (hη : 0 < η) (Bu Bl : Set ℂ) (v : ℂ)
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (hBuS : SimplyConnectedSpace Bu) (hBlS : SimplyConnectedSpace Bl)
    (htBu : MandelDim.IsTInvariant Bu) (htBl : MandelDim.IsTInvariant Bl) (hdisj : Disjoint Bu Bl)
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hcrit : ∀ w ∈ Bu ∪ Bl, deriv d.E w = 0 → ∃ k : ℤ, d.E w = v + k)
    (hcritpt : ∃ w ∈ Bu, deriv d.E w = 0 ∧ d.E w = v)
    (hcovu : IsCoveringMapOn (fun x : Bu => d.E x) {y | ∀ k : ℤ, y ≠ v + k})
    (hcovl : IsCoveringMapOn (fun x : Bl => d.E x) {y | ∀ k : ℤ, y ≠ v + k})
    (hinfu : ∀ y : ℂ, (MandelDim.piExp '' {w | w ∈ Bu ∧ d.E w = y}).Infinite)
    (hinfl : ∀ y : ℂ, (MandelDim.piExp '' {w | w ∈ Bl ∧ d.E w = y}).Infinite) :
    ∀ cl : ℂ, Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl) → 0 < cl.im := by
  intro cl hcl
  have hlow : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖d.E w - w - cl‖ < ε :=
    (tendsto_lowerEnd_iff (f := fun w : ℂ => d.E w - w) (cl := cl)).mp hcl
  have hhiL : ∀ w ∈ Bl, w.im ≤ η := fun w hw => by
    by_contra h
    rw [not_le] at h
    exact (Set.disjoint_left.mp hdisj) (hup h) hw
  have hhiU : ∀ w ∈ Bu, -η ≤ w.im := fun w hw => by
    by_contra h
    rw [not_le] at h
    exact (Set.disjoint_left.mp hdisj) hw (hlo h)
  rcases critvalue_avoid v htBu htBl hdisj with hnoBl | hnoBu
  · obtain ⟨x₀, s, hx₀, hplus, hminus, hsd, hsbase, hssect, hteq, hplus', hminus'⟩ :=
      horn_section_deep f₀ D₀ d Bl η cl v hBlO hBlS htBl hlo
        (fun w hw => hsub (Or.inr hw)) hcovl hnoBl hlow
    have hder := hornS_deriv_of_deep_section hBlO htBl hsd hteq
      (fun y hy => (hssect y hy).1) (fun y hy => (hssect y hy).2) hlo hhiL hlow
    exact cl_im_pos_of_section f₀ D₀ d hBuO htBu hup hBlO hBlS htBl hlo hdisj hsub hinfl
      hsd (fun y hy => (hssect y hy).1) (fun y hy => (hssect y hy).2) hteq hder.1 hder.2.2
  · exact (bu_side_false f₀ D₀ d Bu η v hη hBuO hBuS htBu hup hhiU
      (fun w hw => hsub (Or.inl hw)) hcovu hnoBu hinfu).elim

end Work.Horn