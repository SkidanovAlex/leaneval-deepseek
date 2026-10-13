import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 1. The one-variable slices of a family member -/

/-- The slice of a family member at a point `z = (l,x)` of `ℝ^{p+1}`, read as a function of
the variable, with the parameter `l = z ∘ Fin.castSucc` held fixed. -/
def sliceFun (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+1) → ℝ) : ℝ → ℝ :=
  fun y => famFun f (Function.update z (Fin.last p) y)

/-- `s` is the `x`-derivative of the family member `f` at `z`. -/
def IsSliceDeriv (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+1) → ℝ) (s : ℝ) : Prop :=
  HasDerivAt (sliceFun f z) s (z (Fin.last p))

/-- The `x`-derivative of the family member `f` at `z`. -/
def xDeriv (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+1) → ℝ) : ℝ :=
  deriv (sliceFun f z) (z (Fin.last p))

/-- The locus where the slice `x ↦ f(l,x)` is differentiable at `x`. -/
def sliceDiff (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+1) → ℝ) :=
  {z | DifferentiableAt ℝ (sliceFun f z) (z (Fin.last p))}

/-- The locus where the slice derivative of `f` is continuous, in the fibre direction. -/
def sliceDerivCont (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+1) → ℝ) :=
  {z | ∃ s : ℝ, IsSliceDeriv f z s ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - z (Fin.last p)| < δ →
        ∃ s' : ℝ, IsSliceDeriv f (Function.update z (Fin.last p) x) s' ∧ |s' - s| < ε}

/-- The comparison set `{|∂_x f| ≤ |∂_x g|}`. -/
def domSet (f g : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+1) → ℝ) :=
  {z | ∃ s t : ℝ, IsSliceDeriv f z s ∧ IsSliceDeriv g z t ∧ |s| ≤ |t|}

/-- The set where the slice derivative of `f` is positive. -/
def posSet (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+1) → ℝ) :=
  {z | ∃ s : ℝ, IsSliceDeriv f z s ∧ 0 < s}

/-- The set where the slice derivative of `f` is negative. -/
def negSet (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p+1) → ℝ) :=
  {z | ∃ s : ℝ, IsSliceDeriv f z s ∧ s < 0}

/-- A cell is *good* for the dominating index `i₁`: all family members are differentiable on
it with continuous slice derivatives, `|∂_x F j| ≤ |∂_x F i₁|` there, the derivative of the
dominating member has a constant sign, and its fibres are points or intervals. -/
def GoodCell (k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (i₁ : Fin k) : Prop :=
  (∀ j, κ ⊆ sliceDiff (F j)) ∧
  (∀ j, κ ⊆ sliceDerivCont (F j)) ∧
  (∀ j, κ ⊆ domSet (F j) (F i₁)) ∧
  (κ ⊆ posSet (F i₁) ∨ κ ⊆ negSet (F i₁)) ∧
  (∀ l, (fibre κ l).Subsingleton ∨ ∃ a b : ℝ, fibre κ l = Set.Ioo a b)

/-! ## 2. The image of a fibre and its end points -/

/-- The image of the fibre of `κ` over `l` under the family member `f`. -/
def imgFibre (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) : Set ℝ :=
  {s | ∃ y : ℝ, Fin.snoc l y ∈ κ ∧ f l y = s}

/-- The lower endpoint of the image of the fibre. -/
def Aend (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) : ℝ :=
  sInf (imgFibre κ f l)

/-- The upper endpoint of the image of the fibre. -/
def Bend (κ : Set (Fin (p+1) → ℝ)) (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) : ℝ :=
  sSup (imgFibre κ f l)

/-! ## 3. The chart -/

/-- The chart attached to a cell `κ` and a dominating member `f`: the branch of the inverse of
`f(l,·)` over the image interval, linearly reparametrised by `t`; the junk value `1/2` is used
when the fibre over `l` is empty. -/
def chart1 (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p+1) → ℝ)) : (Fin p → ℝ) → ℝ → ℝ :=
  fun l t => if h : ∃ y : ℝ, Fin.snoc l y ∈ κ ∧
      f l y = Aend κ f l + (Bend κ f l - Aend κ f l) * t
    then Classical.choose h else 1 / 2


/-! ## 4. The one-variable tameness inputs used by the decomposition -/

/-- The one-variable tameness input used in the cell decomposition: for every `Ω`-definable
family member `f` and every parameter `l`, the set of points `x` where the slice `y ↦ f l y`
fails to be differentiable with continuous derivative has empty interior.  This is the
fibre-wise form of the `n = 1` o-minimality theorem (the one-variable version of
`WilkiesDesign.CG.G1_generic_smooth`), applied to the slice, which is itself an `Ω`-definable
one-variable function after substituting `l`. -/
def SliceTame (S : WilkiesDesign.SOMin) (p F0 : ℕ) : Prop :=
  ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
    ∀ l : Fin p → ℝ,
      interior {x : ℝ | ¬ (DifferentiableAt ℝ (f l) x ∧
        ∃ s : ℝ, HasDerivAt (f l) s x ∧
          ∀ ε > 0, ∃ δ > 0, ∀ x' : ℝ, |x' - x| < δ →
            ∃ s' : ℝ, HasDerivAt (f l) s' x' ∧ |s' - s| < ε)} = ∅

/-- The `n = 1` o-minimality inputs, in the form in which they are proved in
`Work.WilG1.OneDim`: for every definable one-variable function, the non-differentiability
locus has empty interior and the function is discontinuous at only finitely many points. -/
def OneVarTame (S : WilkiesDesign.SOMin) : Prop :=
  (∀ {F D : ℕ} (g : (Fin 1 → ℝ) → ℝ), WilkiesDesign.graphOf g ∈ S.Ω F D 2 →
    interior {x : ℝ | ¬ DifferentiableAt ℝ (fun t : ℝ => g (fun _ => t)) x} = ∅) ∧
  (∀ {F D : ℕ} (g : (Fin 1 → ℝ) → ℝ), WilkiesDesign.graphOf g ∈ S.Ω F D 2 →
    {x : ℝ | ¬ ContinuousAt (fun t : ℝ => g (fun _ => t)) x}.Finite)

end Work.WilG4a
