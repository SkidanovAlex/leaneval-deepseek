/-
# Vocabulary for `Work.Mostow.gapA.screwShort3`

Setup for the study of the screw motion `g` translating the geodesic `geodSet a b` by `ℓ` and
the rotation `b₀` by `2π/M` about it, in the hyperboloid (Minkowski) model.

Write `A = (a,1)`, `B = (b,1)` for the two future null vectors of the endpoints, `s = ⟨A,B⟩`,
`m = 1 - ⟪a,b⟫ = -s > 0`, and `P = span{A,B}`.  Every `x` decomposes as `x = αA + βB + v` with
`v ⊥ A, B`; `prjN a b x` is that `v`, and `Nsub a b` is the normal space `P^⊥` (a 2-dimensional
positive definite subspace).  The geodesic itself is parametrised by
`axisV a b s = κ (e^s A + e^{-s} B)`, `κ = (2m)^{-1/2}`, with `axisPt a b s` its chart point.
-/
import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.nfDefs
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.minkAxisCompute
import Submission.Work.Mostow.StabLift

open scoped Matrix

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-- The sheet-preserving lift of `g` as a linear map on the Minkowski space `ℝ^{Fin 3 ⊕ Fin 1}`. -/
noncomputable def Phi (g : LeanEval.Geometry.MostowRigidity.PO 3 1) :
    (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin 3 ⊕ Fin 1 → ℝ) :=
  Work.Mostow.mulVecLin (Work.Mostow.LambdaMat g)

lemma Phi_apply (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    Phi g x = Work.Mostow.LambdaMat g *ᵥ x := rfl

/-- The lift is multiplicative. -/
lemma Phi_mul (hA : Submission.Mostow.POActionProp 3)
    (g h : LeanEval.Geometry.MostowRigidity.PO 3 1) : Phi (g * h) = (Phi g).comp (Phi h) := by
  have h1 : Work.Mostow.LambdaMat (g * h) = Work.Mostow.LambdaMat g * Work.Mostow.LambdaMat h :=
    Work.Mostow.LambdaMat_mul hA g h
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, Phi_apply, Phi_apply, Phi_apply, h1, _root_.Matrix.mulVec_mulVec]

lemma Phi_one (hA : Submission.Mostow.POActionProp 3)
    (x : Fin 3 ⊕ Fin 1 → ℝ) : Phi (1 : LeanEval.Geometry.MostowRigidity.PO 3 1) x = x := by
  rw [Phi_apply, Work.Mostow.LambdaMat_one hA, _root_.Matrix.one_mulVec]

lemma Phi_mul_apply (hA : Submission.Mostow.POActionProp 3)
    (g h : LeanEval.Geometry.MostowRigidity.PO 3 1) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    Phi (g * h) x = Phi g (Phi h x) := by
  have h1 := Phi_mul hA g h
  rw [h1, LinearMap.comp_apply]

lemma Phi_inv_apply (hA : Submission.Mostow.POActionProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    Phi g (Phi g⁻¹ x) = x := by
  have h : Phi (g * g⁻¹) x = Phi g (Phi g⁻¹ x) := Phi_mul_apply hA g g⁻¹ x
  rw [mul_inv_cancel] at h
  rw [← h, Phi_one hA x]

lemma Phi_comp_inv (hA : Submission.Mostow.POActionProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) : (Phi g).comp (Phi g⁻¹) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  exact Phi_inv_apply hA g x

/-- The lift preserves the Minkowski form. -/
lemma Phi_form (hA : Submission.Mostow.POActionProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (x y : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (Phi g x) (Phi g y) = Work.Mostow.mink x y := by
  rw [Phi_apply, Phi_apply, Work.Mostow.mink_eq_mform, Work.Mostow.mink_eq_mform]
  exact Work.Mostow.mform_mulVec (Work.Mostow.LambdaMat g) (Work.Mostow.LambdaMat_isJOrth g) x y

/-- The lift acts on the hyperboloid by the action of `g` in the chart. -/
lemma Phi_hlift (hA : Submission.Mostow.POActionProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (u : Submission.Mostow.E 3) :
    Phi g (Submission.Mostow.hlift u) = Submission.Mostow.hlift (g • u) := by
  rw [Phi_apply]
  exact (Work.Mostow.hlift_LambdaMat hA g u).symm

/-- The lift of `g⁻¹` is the adjoint of the lift of `g` for the Minkowski form. -/
lemma Phi_adjoint (hA : Submission.Mostow.POActionProp 3)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (x y : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (Phi g x) y = Work.Mostow.mink x (Phi g⁻¹ y) := by
  conv_lhs => rw [← Phi_inv_apply hA g y, Phi_form hA g x (Phi g⁻¹ y)]

/-- The future null vector `(a,1)` attached to the boundary point `a`. -/
def nullA (a : E 3) : Fin 3 ⊕ Fin 1 → ℝ := Work.Mostow.nvec a

/-- The future null vector `(b,1)` attached to the boundary point `b`. -/
def nullB (b : E 3) : Fin 3 ⊕ Fin 1 → ℝ := Work.Mostow.nvec b

/-- `m = 1 - ⟪a,b⟫`, positive for distinct boundary points. -/
def mmB (a b : E 3) : ℝ := 1 - inner ℝ a b

/-- `s = ⟨A,B⟩ = ⟪a,b⟫ - 1 = -m`. -/
def smB (a b : E 3) : ℝ := Work.Mostow.mink (nullA a) (nullB b)

lemma mink_smul_left3 (c : ℝ) (x y : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (c • x) y = c * Work.Mostow.mink x y := by
  have h := Work.Mostow.minkSeg_smul (n := 3) c 1 x y
  simpa using h

lemma mink_smul_right3 (c : ℝ) (x y : Fin 3 ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (c • y) = c * Work.Mostow.mink x y := by
  have h := Work.Mostow.minkSeg_smul (n := 3) 1 c x y
  simpa using h

/-- The normal component of `x` with respect to the plane `span{A,B}`: the unique `v` with
`x - v ∈ span{A,B}` and `v ⊥ A, B`. -/
def prjN (a b : E 3) (x : Fin 3 ⊕ Fin 1 → ℝ) : Fin 3 ⊕ Fin 1 → ℝ :=
  x - (Work.Mostow.mink x (nullB b) / smB a b) • nullA a
    - (Work.Mostow.mink x (nullA a) / smB a b) • nullB b

/-- The `A`-coefficient of `x` in the decomposition `x = α A + β B + v`. -/
def alC (a b : E 3) (x : Fin 3 ⊕ Fin 1 → ℝ) : ℝ :=
  Work.Mostow.mink x (nullB b) / smB a b

/-- The `B`-coefficient of `x` in the decomposition `x = α A + β B + v`. -/
def beC (a b : E 3) (x : Fin 3 ⊕ Fin 1 → ℝ) : ℝ :=
  Work.Mostow.mink x (nullA a) / smB a b

/-- The normal space at the geodesic `geodSet a b`. -/
def Nsub (a b : E 3) : Submodule ℝ (Fin 3 ⊕ Fin 1 → ℝ) where
  carrier := {x | Work.Mostow.mink x (nullA a) = 0 ∧ Work.Mostow.mink x (nullB b) = 0}
  zero_mem' := ⟨by simp [Work.Mostow.mink], by simp [Work.Mostow.mink]⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · rw [Work.Mostow.minkSeg_add_left, hx.1, hy.1, add_zero]
    · rw [Work.Mostow.minkSeg_add_left, hx.2, hy.2, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_⟩
    · rw [mink_smul_left3, hx.1, mul_zero]
    · rw [mink_smul_left3, hx.2, mul_zero]

/-- The Minkowski form restricted to the normal space. -/
def minkN (a b : E 3) (x y : Nsub a b) : ℝ :=
  Work.Mostow.mink (x : Fin 3 ⊕ Fin 1 → ℝ) (y : Fin 3 ⊕ Fin 1 → ℝ)

/-- `prjN` is the normal component of the decomposition. -/
lemma prjN_def (a b : E 3) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    prjN a b x = x - alC a b x • nullA a - beC a b x • nullB b := rfl

/-- The decomposition `x = α A + β B + v`. -/
lemma eq_decomp (a b : E 3) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    alC a b x • nullA a + beC a b x • nullB b + prjN a b x = x := by
  rw [prjN_def]; abel

lemma mem_Nsub {a b : E 3} {x : Fin 3 ⊕ Fin 1 → ℝ} :
    x ∈ Nsub a b ↔ Work.Mostow.mink x (nullA a) = 0 ∧ Work.Mostow.mink x (nullB b) = 0 :=
  Iff.rfl

/-- The normalising constant of the geodesic through `a` and `b`. -/
def kkB (a b : E 3) : ℝ := (Real.sqrt (2 * mmB a b))⁻¹

/-- The hyperboloid point of the geodesic with endpoints `a`, `b` at parameter `s`. -/
def axisV (a b : E 3) (s : ℝ) : Fin 3 ⊕ Fin 1 → ℝ :=
  kkB a b • (Real.exp s • nullA a + Real.exp (-s) • nullB b)

/-- The chart point of the geodesic with endpoints `a`, `b` at parameter `s`. -/
def axisPt (a b : E 3) (s : ℝ) : E 3 :=
  WithLp.toLp 2 (fun i : Fin 3 => axisV a b s (Sum.inl i))

end

end Work.Mostow.gapA
