/-
  WilE9G / Lagrange — **FIX-5**, the Morse-genericity (parametric Sard) step.

  See `Submission/Work/WilE9G/Lagrange/DegenSetup.lean` for the set-up.  This file proves
  `Work.WilE9G.Lagrange.exists_null_of_degenerate`:

  for a `Good` ambient stratum `S`, a weight `Φ` strictly positive on `S.X.set` and a direction
  `c`, for almost every `c` and then, for such a `c`, for almost every base point `x`, every
  Lagrange point of `log Φ + c·(y,t)` over the fibre of `S.X.set` at `x` is nondegenerate.

  The argument is the classical Morse genericity argument, in the `(z, (ν,ν₀), c)`-space of
  `DegenSetup`:

  * the "bad" set `Bad ⊆ ℝ^{n+(1+m)}` consists of the pairs `(x, c)` for which a *degenerate*
    Lagrange point over `x` exists;
  * `Bad ⊆ N₂ ∪ T` where
    - `N₂` is the union of the null sets produced by Sard-on-a-level-set (applied to
      `degenH`, whose differential is surjective at every Lagrange point with `ν₀ ≠ 0`, and to
      `degenF`, whose critical points in the level set are exactly the degenerate Lagrange
      points), and
    - `T` is the pre-image under the base projection of the null set `N₁` of the general Sard
      theorem `exists_null_of_Good_amb`: the `ν₀ = 0` Lagrange points can only occur over
      base-critical points of `S`;
  * since every slice of `T` is exactly `N₁`, and almost every slice of `N₂` is null, almost
    every slice of `Bad` is null, which is the statement.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Defs
import Submission.Work.WilE9G.Lagrange.DegenSetup
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.lagJacTrue_det
import Submission.Work.WilE9G.Lagrange.degenH_fderiv_surjective
import Submission.Work.WilE9G.Lagrange.degen_kernel_iff
import Submission.Work.WilE9G.Lagrange.not_isBaseSubmersiveAt_of_fibre_kernel
import Submission.Work.WilE9G.Lagrange.analyticAt_degenH
import Submission.Work.WilE9G.Sard.exists_null_of_Good_amb
import Submission.Work.WilE9G.Sard.sardOnLevelSet
import Submission.Work.WilE9G.Fubini.ae_null_slice_of_null
import Submission.Work.WilE9G.Amb

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## `degenF` is a continuous linear map -/

/-- `degenF` as a continuous linear map. -/
def degenFCLM (S : AmbStratum (n + (1 + m))) :
    (Fin (degenDim n m S.j) → ℝ) →L[ℝ] (Fin (n + (1 + m)) → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin (n + (1 + m)) =>
    Fin.addCases
      (fun a : Fin n =>
        ContinuousLinearMap.proj (⟨a.val, by simp only [degenDim]; omega⟩ : Fin (degenDim n m S.j)))
      (fun l : Fin (1 + m) =>
        ContinuousLinearMap.proj
          (⟨n + (1 + m) + (S.j + 1) + l.val, by simp only [degenDim]; omega⟩ :
            Fin (degenDim n m S.j)))
      i)

theorem degenF_eq_CLM (S : AmbStratum (n + (1 + m))) : degenF S = ⇑(degenFCLM S) := by
  funext p i
  rw [degenF, degenFCLM]
  revert i
  refine Fin.addCases ?_ ?_
  · intro a
    rw [Fin.append_left, ContinuousLinearMap.pi_apply, Fin.addCases_left,
      ContinuousLinearMap.proj_apply]
    rfl
  · intro l
    rw [Fin.append_right, ContinuousLinearMap.pi_apply, Fin.addCases_right,
      ContinuousLinearMap.proj_apply]
    rfl

theorem analyticAt_degenF (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) : AnalyticAt ℝ (degenF S) p := by
  rw [degenF_eq_CLM]
  exact (degenFCLM S).analyticAt p

/-! ## Splitting and reassembling the multiplier vector -/

/-- The `S.j` multipliers of `degenNu p`. -/
def degenNuA (S : AmbStratum (n + (1 + m))) (p : Fin (degenDim n m S.j) → ℝ) :
    Fin S.j → ℝ := fun a => degenNu p (Fin.castAdd 1 a)

/-- The normalising multiplier of `degenNu p`. -/
def degenNu0 (S : AmbStratum (n + (1 + m))) (p : Fin (degenDim n m S.j) → ℝ) : ℝ :=
  degenNu p (Fin.last S.j)

/-- The multiplier vector `(ν, ν₀)` assembled into an element of `Fin (S.j+1) → ℝ`. -/
def degenNuMk (S : AmbStratum (n + (1 + m))) (ν : Fin S.j → ℝ) (ν0 : ℝ) :
    Fin (S.j + 1) → ℝ :=
  Fin.addCases ν (fun _ : Fin 1 => ν0)

@[simp] theorem degenNuMk_castAdd (S : AmbStratum (n + (1 + m))) (ν : Fin S.j → ℝ) (ν0 : ℝ)
    (a : Fin S.j) : degenNuMk S ν ν0 (Fin.castAdd 1 a) = ν a :=
  Fin.addCases_left a

@[simp] theorem degenNuMk_last (S : AmbStratum (n + (1 + m))) (ν : Fin S.j → ℝ) (ν0 : ℝ) :
    degenNuMk S ν ν0 (Fin.last S.j) = ν0 := by
  have h : (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1) :=
    Fin.ext (by simp)
  rw [degenNuMk, h, Fin.addCases_right]

@[simp] theorem degenNuA_degenPt (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (ν : Fin S.j → ℝ) (ν0 : ℝ) (c : Fin (1 + m) → ℝ) :
    degenNuA S (degenPt z (degenNuMk S ν ν0) c) = ν := by
  funext a
  simp only [degenNuA, degenNu_degenPt, degenNuMk_castAdd]

@[simp] theorem degenNu0_degenPt (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (ν : Fin S.j → ℝ) (ν0 : ℝ) (c : Fin (1 + m) → ℝ) :
    degenNu0 S (degenPt z (degenNuMk S ν ν0) c) = ν0 := by
  simp only [degenNu0, degenNu_degenPt, degenNuMk_last]

/-! ## The components of `degenH` -/

theorem degenH_apply_h (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (a : Fin S.j) :
    degenH S Phi p (Fin.castAdd (1 + (1 + m)) a) = eaEval S.X.c (S.h a) (degenZ p) := by
  rw [degenH, Fin.append_left]

theorem degenH_apply_lam (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (u : Fin 1) :
    degenH S Phi p (Fin.natAdd S.j (Fin.castAdd (1 + m) u)) = degenLam S p := by
  rw [degenH, Fin.append_right, Fin.append_left]

theorem degenH_apply_psi (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    degenH S Phi p (Fin.natAdd S.j (Fin.natAdd 1 l)) = degenPsi S Phi p l := by
  rw [degenH, Fin.append_right, Fin.append_right]

/-- The vanishing of `degenH` is exactly `LagEq`, `LagNorm` and `z ∈ S.X.set`'s equation. -/
theorem lagEq_of_degenH_eq_zero (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (h : degenH S Phi p = 0) :
    LagEq S Phi (degenC p) (degenZ p) (degenNuA S p) (degenNu0 S p) := by
  intro l
  have hl : degenPsi S Phi p l = 0 := by
    have := congrFun h (Fin.natAdd S.j (Fin.natAdd 1 l))
    rwa [degenH_apply_psi] at this
  simp only [degenPsi, degenNuA, degenNu0] at hl ⊢
  linarith [hl]

theorem lagNorm_of_degenH_eq_zero (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (h : degenH S Phi p = 0) :
    LagNorm (degenNuA S p) (degenNu0 S p) := by
  have hl : degenLam S p = 0 := by
    have := congrFun h (Fin.natAdd S.j (Fin.castAdd (1 + m) (0 : Fin 1)))
    rwa [degenH_apply_lam] at this
  have hsum : (∑ a : Fin (S.j + 1), (degenNu p a) ^ 2) = 1 := by
    simp only [degenLam] at hl; linarith
  have hsplit : (∑ a : Fin (S.j + 1), (degenNu p a) ^ 2)
      = (∑ a : Fin S.j, (degenNuA S p a) ^ 2) + (degenNu0 S p) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    rfl
  simp only [LagNorm]
  rw [hsplit] at hsum
  exact hsum

end Work.WilE9G.Lagrange
