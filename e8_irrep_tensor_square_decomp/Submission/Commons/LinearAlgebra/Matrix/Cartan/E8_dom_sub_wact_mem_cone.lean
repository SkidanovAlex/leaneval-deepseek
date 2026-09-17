import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_sub_weyl_mem_cone

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- **The Weyl group action decreases dominant weights inside the positive cone.**  If `x` is
dominant (`0 ≤ x i` for all `i`), then for every word `L` of simple reflections the difference
`x - wact L x` lies in the cone `ℕΦ⁺` spanned by the positive roots: all its simple-root
coordinates `coords (x - wact L x) i` are nonnegative.

(Equivalently `wact L x ⪯ x` in the dominance order of the fundamental chamber.) -/
theorem E8_dom_sub_wact_mem_cone (L : List (Fin 8)) (x : Fin 8 → ℤ) (hx : ∀ i, 0 ≤ x i) (i : Fin 8) :
    0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (x - Commons.LinearAlgebra.Matrix.Cartan.wact L x) i := by
  have hw : wact L x = L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) x := rfl
  rw [coords_apply, hw]
  exact E8_coords_sub_weyl_mem_cone x hx L i

end Commons.LinearAlgebra.Matrix.Cartan
