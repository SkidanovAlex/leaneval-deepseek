import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter

/-! ## The lower half-strip and reflection calculus

The target `BrNegFacts` concerns the reflected-negated function
`(w,θ) ↦ -P w (-θ)` on the lower half-strip `(0,∞) × (-π/2, 0)`, where `P` is only known
to be `C²` on the open quadrant `Qd = (0,∞) × (0,π/2)`.  Everything here is the
elementary calculus of the substitution `θ ↦ -θ` composed with the outer sign change. -/

/-- The lower half-strip `(0,∞) × (-π/2, 0)`. -/
private def Qdn : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) 0

private lemma isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma isOpen_Qdn : IsOpen Qdn := isOpen_Ioi.prod isOpen_Ioo

private lemma mem_Qdn {w θ : ℝ} : (w, θ) ∈ Qdn ↔ 0 < w ∧ -(Real.pi / 2) < θ ∧ θ < 0 := by
  simp only [Qdn, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private lemma mem_Qd_of_neg {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    (w, -θ) ∈ Work.Construction.Qd := by
  refine ⟨hw, ?_, ?_⟩
  · linarith
  · linarith

/-! ### First-order reflection identities (pure `deriv` calculus) -/

/-- The `z`-derivative of the reflection-negation only sees the reflection: no
differentiability is needed (the result is unconditional). -/
private lemma pz_neg_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ) :
    Work.Spaces.pz (fun w θ => -Q w (-θ)) w θ = -Work.Spaces.pz Q w (-θ) := by
  simp only [Work.Spaces.pz]
  exact deriv.neg

/-- The `θ`-derivative of the reflection, at the level of `deriv`. -/
private lemma deriv_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ)
    (h : DifferentiableAt ℝ (fun u => Q w u) (-θ)) :
    deriv (fun θ' => Q w (-θ')) θ = -deriv (fun u => Q w u) (-θ) := by
  change deriv ((fun u => Q w u) ∘ (fun θ' : ℝ => -θ')) θ = -deriv (fun u => Q w u) (-θ)
  have h1 : HasDerivAt (fun u => Q w u) (deriv (fun u => Q w u) (-θ)) (-θ) := h.hasDerivAt
  have h2 : HasDerivAt (fun θ' : ℝ => -θ') (-1) θ := hasDerivAt_neg θ
  rw [(h1.comp θ h2).deriv, mul_neg_one]

/-- The `θ`-derivative of the reflection (without the outer sign). -/
private lemma pth_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ)
    (h : DifferentiableAt ℝ (fun u => Q w u) (-θ)) :
    Work.Spaces.pth (fun w θ => Q w (-θ)) w θ = -Work.Spaces.pth Q w (-θ) := by
  simp only [Work.Spaces.pth]
  exact deriv_reflect Q w θ h

/-- The `θ`-derivative of the reflection-negation. -/
private lemma pth_neg_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ)
    (h : DifferentiableAt ℝ (fun u => Q w u) (-θ)) :
    Work.Spaces.pth (fun w θ => -Q w (-θ)) w θ = Work.Spaces.pth Q w (-θ) := by
  have h1 : deriv (fun θ' => -Q w (-θ')) θ = -deriv (fun θ' => Q w (-θ')) θ := deriv.neg
  simp only [Work.Spaces.pth]
  rw [h1, deriv_reflect Q w θ h, neg_neg]

/-! ### Differentiability of the slices, from `C²`-regularity on the open quadrant -/

section SliceDiff

variable {P : ℝ → ℝ → ℝ}

private lemma differentiableAt_uncurry_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry P) p :=
  (hP.differentiableOn (n := 2) (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_slice_P (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_of_Qd hP (mem_Qd_of_neg hw h1 h2))

private lemma differentiableAt_uncurry_pz_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz P)) p :=
  ((Work.Spaces.uncurry_partial_c1 isOpen_Qd hP).1.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_uncurry_pth_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) p :=
  ((Work.Spaces.uncurry_partial_c1 isOpen_Qd hP).2.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_slice_pz (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => Work.Spaces.pz P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_pz_of_Qd hP (mem_Qd_of_neg hw h1 h2))

private lemma differentiableAt_slice_pth (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => Work.Spaces.pth P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_pth_of_Qd hP (mem_Qd_of_neg hw h1 h2))

/-- The `θ`-derivative of `Pn` equals that of `P` at the reflected point, on the strip. -/
private lemma pth_neg_reflect_of_neg (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) :=
  pth_neg_reflect P w θ (differentiableAt_slice_P hP hw h1 h2)

/-- The function identity `pz Pn = fun w θ => -pz P w (-θ)` (unconditional). -/
private lemma pz_neg_reflect_funext (P : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun w θ => -P w (-θ)) = fun w θ => -Work.Spaces.pz P w (-θ) := by
  funext w θ
  exact pz_neg_reflect P w θ

end SliceDiff

theorem BrNegFacts {P : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) 0) ∧
    (∀ w θ, 0 < w → -(Real.pi / 2) < θ → θ < 0 →
      Work.Spaces.pz (fun w θ => -P w (-θ)) w θ = -Work.Spaces.pz P w (-θ) ∧
      Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) ∧
      Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
        = -Work.Spaces.pz (Work.Spaces.pz P) w (-θ) ∧
      Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
        = Work.Spaces.pth (Work.Spaces.pz P) w (-θ) ∧
      Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
        = Work.Spaces.pz (Work.Spaces.pth P) w (-θ) ∧
      Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ)) := by
  have hcont : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ))) Qdn := by
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2)) Qdn :=
      (by fun_prop : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2))).contDiffOn
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, -p.2)) Qdn Work.Construction.Qd := by
      rintro ⟨w, θ⟩ ⟨hw, h1, h2⟩
      exact mem_Qd_of_neg hw h1 h2
    have hcomp : ContDiffOn ℝ 2
        ((Function.uncurry P) ∘ (fun p : ℝ × ℝ => (p.1, -p.2))) Qdn :=
      hP.comp hR hmap
    have hneg := hcomp.neg
    refine hneg.congr ?_
    intro p _
    rfl
  refine ⟨hcont, ?_⟩
  intro w θ hw h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `∂_z (-P(w,-θ)) = -(∂_z P)(w,-θ)`
    exact pz_neg_reflect P w θ
  · -- `∂_θ (-P(w,-θ)) = (∂_θ P)(w,-θ)`
    exact pth_neg_reflect_of_neg hP hw h1 h2
  · -- `∂_z∂_z (-P(w,-θ)) = -(∂_z∂_z P)(w,-θ)`
    rw [pz_neg_reflect_funext P]
    exact pz_neg_reflect (Work.Spaces.pz P) w θ
  · -- `∂_θ∂_z (-P(w,-θ)) = (∂_θ∂_z P)(w,-θ)`
    rw [pz_neg_reflect_funext P]
    exact pth_neg_reflect (Work.Spaces.pz P) w θ (differentiableAt_slice_pz hP hw h1 h2)
  · -- `∂_z∂_θ (-P(w,-θ)) = (∂_z∂_θ P)(w,-θ)`
    have hev : (fun w' => Work.Spaces.pth (fun w θ => -P w (-θ)) w' θ)
        =ᶠ[𝓝 w] (fun w' => Work.Spaces.pth P w' (-θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
      exact pth_neg_reflect_of_neg hP hw' h1 h2
    simpa only [Work.Spaces.pz] using hev.deriv_eq
  · -- `∂_θ∂_θ (-P(w,-θ)) = -(∂_θ∂_θ P)(w,-θ)`
    have hev : (fun θ' => Work.Spaces.pth (fun w θ => -P w (-θ)) w θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth P w (-θ')) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with θ' hθ'
      exact pth_neg_reflect_of_neg hP hw hθ'.1 hθ'.2
    have hd : deriv (fun θ' => Work.Spaces.pth P w (-θ')) θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ) :=
      deriv_reflect (Work.Spaces.pth P) w θ (differentiableAt_slice_pth hP hw h1 h2)
    simpa only [Work.Spaces.pth] using hev.deriv_eq.trans hd

end Work.FTS_StreamBdry.SB2
