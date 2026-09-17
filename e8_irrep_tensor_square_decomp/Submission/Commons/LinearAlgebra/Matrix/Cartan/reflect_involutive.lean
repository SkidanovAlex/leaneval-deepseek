import Mathlib

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The simple reflection attached to a Cartan matrix at a node `i` (with `A i i = 2`) is an
involution on the space of weights `Fin n → R`:
`s_i(v)_j = v_j - v_i * A_{ij}`.

Suggested proof: `(s_i v)_i = v_i - v_i * A_{ii} = -v_i`, hence
`(s_i (s_i v))_j = (v_j - v_i A_{ij}) - (-v_i) A_{ij} = v_j`; this is a ring computation over any
commutative ring (use `funext`, the hypothesis `hii i`, and `ring`/`simp`). -/
theorem reflect_involutive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hii : ∀ i, A i i = 2)
    {R : Type*} [CommRing R] (i : Fin n) :
    Function.Involutive (fun v : Fin n → R => fun j => v j - v i * (A i j : R)) := by
  intro v
  funext j
  have h : (A i i : R) = 2 := by rw [hii i]; norm_num
  show v j - v i * (A i j : R) - (v i - v i * (A i i : R)) * (A i j : R) = v j
  rw [h]
  ring

end Commons.LinearAlgebra.Matrix.Cartan
