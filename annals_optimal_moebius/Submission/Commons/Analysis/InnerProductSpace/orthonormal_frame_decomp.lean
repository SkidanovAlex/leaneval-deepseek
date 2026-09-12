import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Decomposition in an orthonormal frame of `EuclideanSpace ℝ (Fin 3)`

Let `a b c w : EuclideanSpace ℝ (Fin 3)` with `a, b, c` a unit, pairwise
orthogonal triple (an orthonormal frame) and `w` orthogonal to both `a` and
`b`.  Then `w` is a scalar multiple of `c`:

`w = inner ℝ w c • c`.

This is the frame-decomposition fact used when the second fundamental form of
a surface in `ℝ³` is shown to be pure-normal: anything orthogonal to both
tangent directions lies along the normal.  The proof needs that an
orthonormal triple in the 3-dimensional `EuclideanSpace ℝ (Fin 3)` spans the
whole space: orthonormality gives linear independence, and three independent
vectors in dimension three form a basis (`finrank` arguments are available in
Mathlib), after which expanding `w` in that basis and using `w ⊥ a`, `w ⊥ b`
leaves only the `c`-component.
-/

noncomputable section
open scoped BigOperators
namespace Commons.Analysis.InnerProductSpace

/-- In an orthonormal frame `(a, b, c)` of `ℝ³`, any vector orthogonal to
`a` and `b` lies along `c`. -/
theorem orthonormal_frame_decomp {a b c w : EuclideanSpace ℝ (Fin 3)}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (hwa : inner ℝ w a = 0) (hwb : inner ℝ w b = 0) :
    w = inner ℝ w c • c := by
  let v : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![a, b, c]
  have hv : Orthonormal ℝ v := by
    dsimp [v]
    rw [orthonormal_vecCons_iff]
    refine ⟨ha, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [hab, hac]
    · rw [orthonormal_vecCons_iff]
      refine ⟨hb, ?_, ?_⟩
      · intro i
        fin_cases i
        simp [hbc]
      · rw [orthonormal_vecCons_iff]
        refine ⟨hc, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · exact Orthonormal.of_isEmpty (Matrix.vecEmpty : Fin 0 → EuclideanSpace ℝ (Fin 3))
  let bE := basisOfOrthonormalOfCardEqFinrank (𝕜 := ℝ) hv (by simp)
  have hsum_b : (∑ j : Fin 3, bE.repr w j • v j) = w := by
    simpa [bE] using (Module.Basis.sum_repr bE w)
  have hrepr (i : Fin 3) : bE.repr w i = inner ℝ w (v i) := by
    have h_i : inner ℝ (v i) (∑ j : Fin 3, bE.repr w j • v j) = bE.repr w i :=
      Orthonormal.inner_right_fintype hv (fun j => bE.repr w j) i
    have h_i' : inner ℝ (v i) w = bE.repr w i := by
      simpa [hsum_b] using h_i
    exact ((real_inner_comm (v i) w).trans h_i').symm
  calc
    w = ∑ i : Fin 3, inner ℝ w (v i) • v i := by
      calc
        w = ∑ i : Fin 3, bE.repr w i • v i := hsum_b.symm
        _ = ∑ i : Fin 3, inner ℝ w (v i) • v i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hrepr i]
    _ = inner ℝ w c • c := by
      rw [Fin.sum_univ_three]
      simp [v, hwa, hwb]

end Commons.Analysis.InnerProductSpace