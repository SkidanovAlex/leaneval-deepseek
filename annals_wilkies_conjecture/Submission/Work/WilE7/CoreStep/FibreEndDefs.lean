/-
  `Work.WilE7.CoreStep.FibreEndDefs`: the vocabulary for the `Π_{K+1}` case of `CoreLT_succ`.

  For an absolute stratum `T : Stratum 0 (n + (m+1))` in the `(n, m+1)` split (base `ℝ^n`,
  fibre `ℝ^{m+1}`, vertical coordinate = the LAST fibre coordinate) and `x : Fin n → ℝ`:

  * `vertCoord` is the vertical coordinate on a fibre point;
  * `projTopLin` is the linear map underlying `projTop` (first `n` coordinates followed by the
    last fibre coordinate), `absPtLin` the linear reindexing `Fin (0+N) → Fin N` underlying
    `MainDesign.absPt`;
  * `vIm T x` is the vertical section of `π_{n+1}(T)` over `x`.

  The `Π_{K+1}` case of `CoreLT_succ` (BV `prop:main`, the pieces of dimension `k+1`) reduces to
  two facts:

  * `locSubmersion_of_finrank`: at a point of `T` where the differential of `projTop` is
    surjective on the tangent space `ker (jac T z)`, the image of `T` is *locally all* of
    `ℝ^{n+1}` (a local submersion);
  * `finrank_projTop_of_not_critSet` (the algebra): `z ∉ critSet S last` is *exactly* that
    surjectivity condition (the determinant of `[∂_y h ; e_last]` is `det` of the "middle block").

  With those two and the fact that the critical values of `vertCoord` are level values of the
  sheet family, the *band* cells over a base cell are compatible by a closed-and-open argument
  (`bandCell_subset_or_disjoint_of_interior`), and the *graph* cells are always inside
  `π_{n+1}(T)` since their level functions are sheet levels of pieces contained in `T`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.FiberCutDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The vertical coordinate on a fibre point of the `(n, m+1)` split: the LAST fibre
coordinate. -/
def vertCoord {m : ℕ} (y : Fin (m + 1) → ℝ) : ℝ := y (Fin.last m)

/-- The linear map underlying `projTop`: the first `n` coordinates followed by the last fibre
coordinate. -/
def projTopLin (n m : ℕ) : (Fin (n + (m + 1)) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.pi (fun i : Fin (n + 1) =>
    if h : (i : ℕ) < n then (LinearMap.proj (R := ℝ) ⟨i, by omega⟩)
    else (LinearMap.proj (R := ℝ) ⟨n + m, by omega⟩))

theorem projTopLin_apply (n m : ℕ) (z : Fin (n + (m + 1)) → ℝ) :
    projTopLin n m z = projTop n m z := by
  funext i
  rw [projTop_eq_ite]
  simp only [projTopLin, LinearMap.pi_apply, LinearMap.proj_apply]
  split_ifs with h
  · rfl
  · rfl

/-- The linear reindexing underlying `MainDesign.absPt`. -/
def absPtLin (N : ℕ) : (Fin (0 + N) → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i : Fin N => Fin.cast (Nat.zero_add N).symm i)

theorem absPtLin_apply (N : ℕ) (z : Fin (0 + N) → ℝ) :
    absPtLin N z = absPt z := rfl

/-- The vertical section of `π_{n+1}(T)` over `x`: the image of the vertical coordinate on the
fibre of `absSet T` over `x`. -/
def vIm {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (x : Fin n → ℝ) : Set ℝ :=
  vertCoord '' (WilkiesDesign.E.fiber (absSet T) x)

theorem mem_vIm {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (x : Fin n → ℝ)
    (t : ℝ) : t ∈ vIm T x ↔ ∃ y ∈ WilkiesDesign.E.fiber (absSet T) x, vertCoord y = t :=
  Iff.rfl

end Work.WilE7.CoreStep
