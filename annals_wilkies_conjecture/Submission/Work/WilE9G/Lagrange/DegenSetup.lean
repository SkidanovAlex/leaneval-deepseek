/-
  WilE9G / Lagrange — **the analytic set-up of FIX-5** (the Morse-genericity step).

  The construction of the Lagrange stratum needs the following input, isolated in
  `Work.WilE9G.Lagrange.exists_null_of_degenerate`: for a `Good` ambient stratum `S`, a weight `Φ`
  which is strictly positive on `S.X.set` and a direction `c`, for almost every `c` and then almost
  every `x` every Lagrange point of `log Φ + c·(y,t)` over the fibre of `S.X.set` at `x` is
  *nondegenerate* (`det (lagJac …) ≠ 0`).

  The mathematical content is a Morse-genericity (parametric Sard) statement.  This file fixes the
  set-up in which it is proved:

  * the ambient space is
    `degenDim n m j = (n + (1+m)) + (j+1) + (1+m)`, with coordinates
    `(z, (ν, ν₀), c) = (degenZ p, degenNu p, degenC p)`;
  * `degenPsi` is the rearranged Lagrange equation
    `ψ_l = ν₀ (Φ c_l + ∂_l Φ) - ∑_a ν_a ∂_l h_a`, so that `ψ = 0` is exactly `LagEq`, with `Φ`
    evaluated at `z`;
  * `degenLam` is the normalisation `∑ ν_a² + ν₀² - 1`;
  * `degenH = (h_a, degenLam, ψ_l)` is the system whose zero set is the Lagrange locus, and
    `degenF = (projBase z, c)` is the projection whose critical values are the bad `(x,c)` pairs.

  The two facts about this set-up that the proof consumes (and that are proved in the delegated
  modules next to this one) are:

  * `degenH_fderiv_surjective` — at a Lagrange point with `ν₀ ≠ 0` the differential of `degenH` is
    surjective (so that Sard-on-a-level-set applies);
  * `degen_kernel_iff` — for `v` with `degenF`-differential zero, `degenH`-differential zero is
    equivalent to `lagJacTrue · (v|fibre, v|ν, v|ν₀) = 0`.

  Together with `lagJacTrue_det` (`det lagJacTrue = det lagJac` at Lagrange points) these give:
  at a Lagrange point with `ν₀ ≠ 0`, the differential of `degenF` restricted to the level set of
  `degenH` is invertible exactly when `det (lagJac …) ≠ 0`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Defs
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Lagrange
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## The coordinates of the ambient space -/

/-- The dimension `(n + (1+m)) + (S.j + 1) + (1+m)` of the `(z, (ν,ν₀), c)`-space. -/
def degenDim (n m j : ℕ) : ℕ := (n + (1 + m)) + (j + 1) + (1 + m)

/-- The `z`-coordinates of a point of the `(z, (ν,ν₀), c)`-space. -/
def degenZ {j : ℕ} (p : Fin (degenDim n m j) → ℝ) : Fin (n + (1 + m)) → ℝ :=
  fun i => p ⟨i.val, by simp only [degenDim]; omega⟩

/-- The `(ν, ν₀)`-coordinates of a point of the `(z, (ν,ν₀), c)`-space. -/
def degenNu {j : ℕ} (p : Fin (degenDim n m j) → ℝ) : Fin (j + 1) → ℝ :=
  fun a => p ⟨n + (1 + m) + a.val, by simp only [degenDim]; omega⟩

/-- The `c`-coordinates of a point of the `(z, (ν,ν₀), c)`-space. -/
def degenC {j : ℕ} (p : Fin (degenDim n m j) → ℝ) : Fin (1 + m) → ℝ :=
  fun l => p ⟨n + (1 + m) + (j + 1) + l.val, by simp only [degenDim]; omega⟩

theorem degenZ_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (i : Fin (n + (1 + m))) :
    degenZ p i = p ⟨i.val, by simp only [degenDim]; omega⟩ := rfl

theorem degenNu_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (a : Fin (j + 1)) :
    degenNu p a = p ⟨n + (1 + m) + a.val, by simp only [degenDim]; omega⟩ := rfl

theorem degenC_apply {j : ℕ} (p : Fin (degenDim n m j) → ℝ) (l : Fin (1 + m)) :
    degenC p l = p ⟨n + (1 + m) + (j + 1) + l.val, by simp only [degenDim]; omega⟩ := rfl

/-! ## The system and the projection of the genericity step -/

/-- The `Φ`-value at the `z`-part of a point. -/
def degenPhiVal (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) : ℝ :=
  eaEval S.X.c Phi (degenZ p)

/-- The rearranged `l`-th Lagrange equation
`ψ_l = ν₀ (Φ c_l + ∂_l Φ) - ∑_a ν_a ∂_l h_a` (with `Φ` evaluated at the `z`-part).  The vanishing
of `ψ` is exactly `LagEq`. -/
def degenPsi (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) : Fin (1 + m) → ℝ :=
  fun l =>
    degenNu p (Fin.last S.j)
        * (eaEval S.X.c Phi (degenZ p) * degenC p l
            + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p))
      - ∑ a : Fin S.j, degenNu p (Fin.castAdd 1 a)
          * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)

/-- The normalisation equation `∑_a ν_a² + ν₀² - 1` (the sum over `Fin (S.j+1)` includes `ν₀`). -/
def degenLam (S : AmbStratum (n + (1 + m))) (p : Fin (degenDim n m S.j) → ℝ) : ℝ :=
  (∑ a : Fin (S.j + 1), (degenNu p a) ^ 2) - 1

/-- The system of the genericity step: the `S.j` equations `h_a` of `S`, then the normalisation,
then the `1+m` rearranged Lagrange equations. -/
def degenH (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) : Fin (S.j + (1 + (1 + m))) → ℝ :=
  Fin.append (fun a : Fin S.j => eaEval S.X.c (S.h a) (degenZ p))
    (Fin.append (fun _ : Fin 1 => degenLam S p)
      (fun l : Fin (1 + m) => degenPsi S Phi p l))

/-- The projection of the genericity step: the base coordinates of `z` together with `c`. -/
def degenF (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) : Fin (n + (1 + m)) → ℝ :=
  Fin.append (projBase (Nat.le_add_right n (1 + m)) (degenZ p)) (degenC p)

/-! ## The point with prescribed data -/

/-- The point of the `(z,(ν,ν₀),c)`-space with the prescribed `z`, `(ν,ν₀)` and `c`. -/
def degenPt {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) : Fin (degenDim n m j) → ℝ :=
  fun i =>
    if h : i.val < n + (1 + m) then z ⟨i.val, h⟩
    else if h2 : i.val < n + (1 + m) + (j + 1) then
      nu ⟨i.val - (n + (1 + m)), by omega⟩
    else
      c ⟨i.val - (n + (1 + m) + (j + 1)), by
        have := i.isLt; simp only [degenDim] at this; omega⟩

@[simp] theorem degenZ_degenPt {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) : degenZ (degenPt z nu c : Fin (degenDim n m j) → ℝ) = z := by
  funext i
  rw [degenZ_apply, degenPt]
  simp only [dif_pos i.isLt]

@[simp] theorem degenNu_degenPt {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) : degenNu (degenPt z nu c : Fin (degenDim n m j) → ℝ) = nu := by
  funext a
  rw [degenNu_apply, degenPt]
  have ha : ¬ (n + (1 + m) + a.val < n + (1 + m)) := by omega
  have ha2 : n + (1 + m) + a.val < n + (1 + m) + (j + 1) := by
    have := a.isLt; omega
  rw [dif_neg ha, dif_pos ha2]
  congr 1
  ext
  simp

@[simp] theorem degenC_degenPt {j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) : degenC (degenPt z nu c : Fin (degenDim n m j) → ℝ) = c := by
  funext l
  rw [degenC_apply, degenPt]
  have ha : ¬ (n + (1 + m) + (j + 1) + l.val < n + (1 + m)) := by omega
  have ha2 : ¬ (n + (1 + m) + (j + 1) + l.val < n + (1 + m) + (j + 1)) := by omega
  rw [dif_neg ha, dif_neg ha2]
  congr 1
  ext
  simp

/-! ## Evaluation of the system and the projection at `degenPt` -/

theorem degenPsi_degenPt {j : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (S.j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    degenPsi S Phi (degenPt z nu c) l =
      nu (Fin.last S.j) * (eaEval S.X.c Phi z * c l
        + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) z)
      - ∑ a : Fin S.j, nu (Fin.castAdd 1 a)
          * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z := by
  simp only [degenPsi, degenZ_degenPt, degenNu_degenPt, degenC_degenPt]

theorem degenLam_degenPt {j : ℕ} (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (S.j + 1) → ℝ) (c : Fin (1 + m) → ℝ) :
    degenLam S (degenPt z nu c) = (∑ a : Fin (S.j + 1), (nu a) ^ 2) - 1 := by
  simp only [degenLam, degenNu_degenPt]

theorem degenH_degenPt {j : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (S.j + 1) → ℝ)
    (c : Fin (1 + m) → ℝ) :
    degenH S Phi (degenPt z nu c) =
      Fin.append (fun a : Fin S.j => eaEval S.X.c (S.h a) z)
        (Fin.append (fun _ : Fin 1 => (∑ a : Fin (S.j + 1), (nu a) ^ 2) - 1)
          (fun l : Fin (1 + m) =>
            nu (Fin.last S.j) * (eaEval S.X.c Phi z * c l
              + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) z)
            - ∑ a : Fin S.j, nu (Fin.castAdd 1 a)
                * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z)) := by
  funext i
  rw [degenH]
  revert i
  refine Fin.addCases ?_ ?_
  · intro a
    simp only [Fin.append_left, degenZ_degenPt]
  · intro b
    revert b
    refine Fin.addCases ?_ ?_
    · intro u
      simp only [Fin.append_left, Fin.append_right, degenLam, degenNu_degenPt]
    · intro l
      simp only [Fin.append_left, Fin.append_right, degenPsi, degenNu_degenPt, degenC_degenPt,
        degenZ_degenPt]

theorem degenF_degenPt (S : AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (nu : Fin (S.j + 1) → ℝ) (c : Fin (1 + m) → ℝ) :
    degenF S (degenPt z nu c) =
      Fin.append (projBase (Nat.le_add_right n (1 + m)) z) c := by
  rw [degenF, degenZ_degenPt, degenC_degenPt]

end Work.WilE9G.Lagrange
