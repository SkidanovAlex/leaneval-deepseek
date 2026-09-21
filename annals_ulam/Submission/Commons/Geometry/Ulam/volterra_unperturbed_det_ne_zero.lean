import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.Geometry.Ulam

lemma volterra_unperturbed_det_ne_zero (n : ℕ) (_hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    let profileX : ℝ → ℝ := fun s => 1 / Real.sqrt (1 + s ^ 2)
    let volterraC : ℕ → ℝ → ℝ → ℝ := fun n s a => (-2 : ℝ) ^ n * (n.factorial : ℝ) * (s * a ^ 2) ^ n
    let volterraD : ℕ → ℝ → ℝ → ℝ := fun n s a => (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) * (s * a ^ 2) ^ (n - 1)
    let volterraA : ℕ → ℝ → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun n s x y =>
      !![volterraC n s x, volterraC n s y; volterraD n s x * (-x), volterraD n s y * y]
    (volterraA n s (profileX s) (profileX s)).det ≠ 0 := by
  dsimp only
  set a : ℝ := 1 / Real.sqrt (1 + s ^ 2)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hdet :
      (!![(-2 : ℝ) ^ n * (n.factorial : ℝ) * (s * a ^ 2) ^ n,
            (-2 : ℝ) ^ n * (n.factorial : ℝ) * (s * a ^ 2) ^ n;
            (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) * (s * a ^ 2) ^ (n - 1) * (-a),
            (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) * (s * a ^ 2) ^ (n - 1) * a] : Matrix (Fin 2) (Fin 2) ℝ).det =
        2 * a * ((-2 : ℝ) ^ n * (n.factorial : ℝ) * (s * a ^ 2) ^ n) *
          ((-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) * (s * a ^ 2) ^ (n - 1)) := by
      rw [Matrix.det_fin_two_of]
      ring
  rw [hdet]
  positivity

end Commons.Geometry.Ulam