import Mathlib
import Submission.Work.MotAS.AsT.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Transport of the secant quintic `s` to AS (Artin–Schreier) Galois coordinates

`x = asM w · y`, i.e. `x_i = Σ_j y_j (w+i)^j`, is the Artin–Schreier change of coordinates.
`asXi y i` is the coefficient vector of `Σ_j y_j (w+i)^j` in the basis `1,w,w²,w³,w⁴` of
`R[w]/(w⁵-w-g)`, and `AsT.AX w y i` is the corresponding element `Σ_l (asXi y i) l w^l` of `R`.
The identity `s(asM w · y) = s^AS(y)` is the statement that `kleinSec` reduces to `kleinSecAS`
modulo `(w⁵-w-g, 5)`; the computation is in `Work.MotAS.AsT.Main` (each monomial of the quintic
is reduced with `redMul_spec`, and the terms are grouped by their `(a,b)`-monomial for the
reduction modulo `5`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

lemma zv0_eq_asXi (y : Fin 5 → R) : AsT.Zv0 y = asXi y 0 := by
  funext l; fin_cases l <;> simp [AsT.Zv0, asXi]

lemma zv1_eq_asXi (y : Fin 5 → R) : AsT.Zv1 y = asXi y 1 := by
  funext l; fin_cases l <;> simp [AsT.Zv1, asXi] <;> ring

lemma zv2_eq_asXi (y : Fin 5 → R) : AsT.Zv2 y = asXi y 2 := by
  funext l; fin_cases l <;> simp [AsT.Zv2, asXi] <;> ring

lemma zv3_eq_asXi (y : Fin 5 → R) : AsT.Zv3 y = asXi y 3 := by
  funext l; fin_cases l <;> simp [AsT.Zv3, asXi] <;> ring

lemma zv4_eq_asXi (y : Fin 5 → R) : AsT.Zv4 y = asXi y 4 := by
  funext l; fin_cases l <;> simp [AsT.Zv4, asXi] <;> ring

lemma AX_eq_asXi_0 (w : R) (y : Fin 5 → R) :
    AsT.AX w y 0 = ∑ l : Fin 5, asXi y 0 l * w ^ (l:ℕ) := by
  simp only [AsT.AX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zv0_eq_asXi]

lemma AX_eq_asXi_1 (w : R) (y : Fin 5 → R) :
    AsT.AX w y 1 = ∑ l : Fin 5, asXi y 1 l * w ^ (l:ℕ) := by
  simp only [AsT.AX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zv1_eq_asXi]

lemma AX_eq_asXi_2 (w : R) (y : Fin 5 → R) :
    AsT.AX w y 2 = ∑ l : Fin 5, asXi y 2 l * w ^ (l:ℕ) := by
  simp only [AsT.AX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zv2_eq_asXi]

lemma AX_eq_asXi_3 (w : R) (y : Fin 5 → R) :
    AsT.AX w y 3 = ∑ l : Fin 5, asXi y 3 l * w ^ (l:ℕ) := by
  simp only [AsT.AX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zv3_eq_asXi]

lemma AX_eq_asXi_4 (w : R) (y : Fin 5 → R) :
    AsT.AX w y 4 = ∑ l : Fin 5, asXi y 4 l * w ^ (l:ℕ) := by
  simp only [AsT.AX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zv4_eq_asXi]

/-- `AX w y i = Σ_l (asXi y i) l w^l`: the element of `R[w]` whose coefficients are the
coordinates of `Σ_j y_j (w+i)^j` in the basis `1,w,w²,w³,w⁴`. -/
lemma AX_eq_asXi (w : R) (y : Fin 5 → R) (i : Fin 5) :
    AsT.AX w y i = ∑ l : Fin 5, asXi y i l * w ^ (l:ℕ) := by
  fin_cases i <;>
    first
      | exact AX_eq_asXi_0 w y
      | exact AX_eq_asXi_1 w y
      | exact AX_eq_asXi_2 w y
      | exact AX_eq_asXi_3 w y
      | exact AX_eq_asXi_4 w y

theorem asTransportS {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinSec a b (fun i => ∑ j, Work.MotAS.asM w i j * y j)
      = Work.MotAS.kleinSecAS a b g y := by
  have hx : (fun i => ∑ j, Work.MotAS.asM w i j * y j)
      = (fun i => ∑ l : Fin 5, asXi y i l * w ^ (l:ℕ)) := by
    funext i
    exact (asXi_spec (R := R) w y i).symm
  rw [hx]
  rw [show (fun i => ∑ l : Fin 5, asXi y i l * w ^ (l:ℕ))
        = (fun i => AsT.AX w y i) from funext (fun i => (AX_eq_asXi w y i).symm)]
  exact AsT.kleinSec_AX a b g w h5 hw y

end Work.MotAS
