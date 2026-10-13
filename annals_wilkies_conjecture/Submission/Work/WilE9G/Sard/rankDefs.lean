/-
  `Work.WilE9G.Sard.rankDefs` — the vocabulary for the rank-positive reduction step of the
  local Morse–Sard argument (`Work.WilE9G.Sard.rankPosReduction`).

  Given `f : ℝ^{d+1} → ℝ^{m+1}` with `fderiv ℝ f x₀ ≠ 0`, one picks coordinates `i : Fin (m+1)`,
  `j : Fin (d+1)` with `∂_j f_i (x₀) ≠ 0`.  The *straightening chart*

      `chart f i j z = (crj j z, f z i)`

  (delete the `j`-th coordinate, keep the `i`-th component of `f`) has an invertible differential
  at `x₀`; it is the change of variables that turns `f` locally into the graph of a map
  `ℝ^d → ℝ^m`, which is what allows the induction step of Morse–Sard.
-/
import Mathlib

set_option autoImplicit false

noncomputable section

namespace Work.WilE9G.Sard

/-- Forget the `j`-th coordinate: `crj j z l = z (j.succAbove l)`. -/
def crj {d : ℕ} (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ) : Fin d → ℝ := fun l => z (j.succAbove l)

@[simp] theorem crj_apply {d : ℕ} (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ) (l : Fin d) :
    crj j z l = z (j.succAbove l) := rfl

/-- The continuous linear map underlying `crj`. -/
def kdrj {d : ℕ} (j : Fin (d + 1)) : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun l : Fin d => ContinuousLinearMap.proj (j.succAbove l))

theorem kdrj_apply {d : ℕ} (j : Fin (d + 1)) (v : Fin (d + 1) → ℝ) : kdrj j v = crj j v := by
  funext l
  rw [kdrj, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, crj_apply]

theorem kdrj_surjective {d : ℕ} (j : Fin (d + 1)) : Function.Surjective (kdrj j) := by
  intro v
  refine ⟨Fin.insertNth (α := fun _ => ℝ) j (0 : ℝ) v, ?_⟩
  rw [kdrj_apply]
  funext l
  rw [crj_apply, Fin.insertNth_apply_succAbove]

/-- The straightening chart of `f` at the pair of coordinates `(i, j)`. -/
def chart {d m : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin (m + 1))
    (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ) : (Fin d → ℝ) × ℝ := (crj j z, f z i)

@[simp] theorem chart_fst {d m : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ) :
    (chart f i j z).1 = crj j z := rfl

@[simp] theorem chart_snd {d m : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (j : Fin (d + 1)) (z : Fin (d + 1) → ℝ) :
    (chart f i j z).2 = f z i := rfl

/-- The differential of the chart at `x₀`. -/
def dchart {d m : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin (m + 1))
    (j : Fin (d + 1)) (x₀ : Fin (d + 1) → ℝ) : (Fin (d + 1) → ℝ) →L[ℝ] ((Fin d → ℝ) × ℝ) :=
  (kdrj j).prod ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x₀))

end Work.WilE9G.Sard
