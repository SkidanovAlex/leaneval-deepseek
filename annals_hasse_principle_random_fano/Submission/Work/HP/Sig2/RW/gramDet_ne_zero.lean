import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.span_realify_latOrth_inf

/-!
# Nonvanishing of the two-vector Gram determinant

`Work.HP.Sig2.RW.gramDet_ne_zero`: for `ℤ`-linearly independent `x y : ℤ^{n+1}` the Gram
determinant `‖x‖²‖y‖² - ⟨x,y⟩²` of the realified vectors `toR x, toR y` is nonzero.  This is the
nondegeneracy hypothesis `hΔ` needed by `exists_span_add_orth`.

The proof is the standard Gram-matrix argument: `ℤ`-linear independence makes `toR x, toR y`
`ℝ`-linearly independent (`Work.HP.Vero.linInd_intCastPi`), and `Matrix.det_gram_ne_zero_iff_linearIndependent`
identifies the Gram determinant with the asserted expression, computed with `Matrix.det_fin_two`
and `EuclideanSpace.inner_toLp_toLp` (the Euclidean inner product is `Work.HP.dotR`).
-/

set_option autoImplicit false

namespace Work.HP.Sig2.RW

open Work.HP

/-- Symmetry of the Euclidean inner product `dotR`. -/
private lemma dotR_comm' {ι : Type*} [Fintype ι] (v w : ι → ℝ) : dotR v w = dotR w v := by
  simp only [dotR]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (v i) (w i))

/-- The Euclidean inner product of `WithLp.toLp 2`-lifts of real vectors is `dotR`. -/
private lemma inner_toLp_eq_dotR {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = dotR u v := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, dotR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mul_comm]

/-- For `ℤ`-linearly independent `x y : ℤ^{n+1}` the Gram determinant of the realified vectors `toR x, toR y` is nonzero. Witness identity: `2 (‖x‖²‖y‖² - ⟨x,y⟩²) = ∑_{i,j} (x_i y_j - x_j y_i)^2`. -/
theorem gramDet_ne_zero {n : ℕ} {x y : Fin (n + 1) → ℤ} (hxy : LinearIndependent ℤ ![x, y]) :
    Work.HP.dotR (Work.HP.toR x) (Work.HP.toR x) * Work.HP.dotR (Work.HP.toR y) (Work.HP.toR y)
      - Work.HP.dotR (Work.HP.toR x) (Work.HP.toR y) ^ 2 ≠ 0 := by
  classical
  -- `ℤ`-linear independence gives `ℝ`-linear independence of the realifications.
  have hli0 : LinearIndependent ℝ (fun j : Fin 2 => intCastPi (![x, y] j)) :=
    Vero.linInd_intCastPi (κ := Fin 2) hxy
  have hliR : LinearIndependent ℝ (fun j : Fin 2 => toR (![x, y] j)) := hli0
  -- transport to the `L²` Euclidean space
  let φ : (Fin (n + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  have hφ : φ.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.injective
  have hV : LinearIndependent ℝ (fun j : Fin 2 => WithLp.toLp 2 (toR (![x, y] j))) := by
    have hh := hliR.map' φ hφ
    have heq : (fun j : Fin 2 => WithLp.toLp 2 (toR (![x, y] j)))
        = (φ ∘ fun j => toR (![x, y] j)) := by
      funext j
      simp [φ]
    rw [heq]
    exact hh
  -- the Gram determinant is nonzero
  have hdet : (Matrix.gram ℝ (fun j : Fin 2 => WithLp.toLp 2 (toR (![x, y] j)))).det ≠ 0 :=
    (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr hV
  -- and it is exactly the asserted expression
  have hdet_eq : (Matrix.gram ℝ (fun j : Fin 2 => WithLp.toLp 2 (toR (![x, y] j)))).det
      = dotR (toR x) (toR x) * dotR (toR y) (toR y) - dotR (toR x) (toR y) ^ 2 := by
    have h0 : (![x, y] : Fin 2 → (Fin (n + 1) → ℤ)) 0 = x := by simp
    have h1 : (![x, y] : Fin 2 → (Fin (n + 1) → ℤ)) 1 = y := by simp
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, h0, h1, inner_toLp_eq_dotR]
    rw [dotR_comm' (toR y) (toR x)]
    ring
  rw [hdet_eq] at hdet
  exact hdet

end Work.HP.Sig2.RW
