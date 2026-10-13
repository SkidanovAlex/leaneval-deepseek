import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.RCLike.Basic
import Submission.Work.FTS.GalBasis.cc.CutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mixed derivatives of the cutoff `psiCut` factorise

`psiCut N z θ = cutA N z * cutB N θ` is a product of a function of `z` alone with a function
of `θ` alone.  The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` respect that splitting —
`D_z` differentiates only in `z`, so a factor depending on `θ` alone comes out, and dually for
`D_θ` — hence for every `j`, `i`

  `mixed j i (psiCut N) = DzIter j (cutA N) * DthIter i (cutB N)`.

The proof of `psiCut_mixed_factor` below goes through the "one-variable" versions `DzIter1`,
`DthIter1` of the two iterated operators (the `θ`-argument of a function of `z` alone is
irrelevant, and conversely), so that all the bookkeeping is about `ℝ → ℝ` functions.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-! ## The one-variable operators `z ∂_z` and `sin(2θ) ∂_θ` -/

/-- The operator `f ↦ (z ↦ z * f'(z))` on functions `ℝ → ℝ`. -/
def Dz1 (f : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv f z

/-- The operator `f ↦ (θ ↦ sin(2θ) * f'(θ))` on functions `ℝ → ℝ`. -/
def Dth1 (f : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv f θ

/-- The `j`-th iterate of `Dz1`. -/
def DzIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dz1 (DzIter1 n f)

/-- The `i`-th iterate of `Dth1`. -/
def DthIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth1 (DthIter1 n f)

@[simp] theorem DzIter1_zero (f : ℝ → ℝ) : DzIter1 0 f = f := rfl

@[simp] theorem DzIter1_succ (n : ℕ) (f : ℝ → ℝ) : DzIter1 (n + 1) f = Dz1 (DzIter1 n f) := rfl

@[simp] theorem DthIter1_zero (f : ℝ → ℝ) : DthIter1 0 f = f := rfl

@[simp] theorem DthIter1_succ (n : ℕ) (f : ℝ → ℝ) : DthIter1 (n + 1) f = Dth1 (DthIter1 n f) := rfl

/-! ## `DzIter` and `DthIter` of a function of a single variable -/

/-- `D_z^j` applied to a function of `z` alone is the one-variable iterate `DzIter1`. -/
theorem DzIter_const (j : ℕ) (a : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') = fun z _ => DzIter1 j a z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz, DzIter1_succ, Dz1]

/-- `D_θ^i` applied to a function of `θ` alone is the one-variable iterate `DthIter1`. -/
theorem DthIter_const (i : ℕ) (b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ' => b θ') = fun _ θ => DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth, DthIter1_succ, Dth1]

/-- Pointwise form of `DzIter_const`. -/
theorem DzIter_const_apply (j : ℕ) (a : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') z θ = DzIter1 j a z :=
  congrFun (congrFun (DzIter_const j a) z) θ

/-- Pointwise form of `DthIter_const`. -/
theorem DthIter_const_apply (i : ℕ) (b : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ' => b θ') z θ = DthIter1 i b θ :=
  congrFun (congrFun (DthIter_const i b) z) θ

/-! ## `DzIter` and `DthIter` of a separated product -/

/-- `D_z^j` of a separated product only differentiates the `z`-factor. -/
theorem DzIter_prod (j : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => a z * b θ) = fun z θ => DzIter1 j a z * b θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz, DzIter1_succ, Dz1]
    rw [deriv_mul_const_field']
    ring

/-- `D_θ^i` of a separated product only differentiates the `θ`-factor. -/
theorem DthIter_prod (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * b θ) = fun z θ => a z * DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth, DthIter1_succ, Dth1]
    rw [deriv_const_mul_field']
    ring

/-! ## The theorem -/

theorem psiCut_mixed_factor (N j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (psiCut N) z θ
      = Work.Spaces.DzIter j (fun z' (_ : ℝ) => cutA N z') z θ
        * Work.Spaces.DthIter i (fun (_ : ℝ) θ' => cutB N θ') z θ := by
  have hDth : Work.Spaces.DthIter i (psiCut N)
      = fun z θ => cutA N z * DthIter1 i (cutB N) θ := by
    change Work.Spaces.DthIter i (fun z θ => cutA N z * cutB N θ)
      = fun z θ => cutA N z * DthIter1 i (cutB N) θ
    exact DthIter_prod i (cutA N) (cutB N)
  have hDz : Work.Spaces.DzIter j (Work.Spaces.DthIter i (psiCut N))
      = fun z θ => DzIter1 j (cutA N) z * DthIter1 i (cutB N) θ := by
    rw [hDth]
    exact DzIter_prod j (cutA N) (DthIter1 i (cutB N))
  have h : Work.Spaces.mixed j i (psiCut N) z θ
      = DzIter1 j (cutA N) z * DthIter1 i (cutB N) θ := by
    simpa only [Work.Spaces.mixed] using congrFun (congrFun hDz z) θ
  rw [h, ← DzIter_const_apply j (cutA N) z θ, ← DthIter_const_apply i (cutB N) z θ]

end Work.FTS.GalBasis.cc
