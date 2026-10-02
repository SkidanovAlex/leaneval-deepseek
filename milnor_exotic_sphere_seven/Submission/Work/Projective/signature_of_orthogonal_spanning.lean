import Mathlib
import Submission.Work.SignatureBordism.Signature
import Submission.Work.SignatureBordism.signature_of_span_singleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Projective

open Finset

/-- **Signature of a quadratic form diagonal in a spanning family.**

Let `Q` be a quadratic form on a `𝕜`-vector space `V` and let `v : Fin n → V` span `V`.  If, in the
coordinates of the spanning family, `Q` is diagonal with *non-zero* weights `d i`,
`Q (∑ i, x i • v i) = ∑ i, (x i)^2 * d i`, then the family is in fact a basis and Sylvester's law of
inertia computes the signature of `Q`: it is the number of positive weights minus the number of
negative weights.

Indeed the hypotheses force `φ : (Fin n → 𝕜) →ₗ V`, `φ x = ∑ i, x i • v i`, to be injective: if
`φ z = 0` then the polar form `polar W z e_j` of the diagonal form `W` vanishes for every standard
basis vector `e_j`, i.e. `2 * z j * d j = 0`, whence `z j = 0` as `2 ≠ 0` and `d j ≠ 0`.  Together
with surjectivity (the spanning hypothesis) `φ` is a linear equivalence
`(Fin n → 𝕜) ≃ₗ V` transporting `Q` to `weightedSumSquares 𝕜 d`. -/
theorem signature_of_orthogonal_spanning {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (Q : QuadraticForm 𝕜 V) (v : Fin n → V) (d : Fin n → 𝕜)
    (hspan : Submodule.span 𝕜 (Set.range v) = ⊤)
    (hdiag : ∀ x : Fin n → 𝕜, Q (∑ i, x i • v i) = ∑ i, (x i) ^ 2 * d i)
    (hne : ∀ i, d i ≠ 0) :
    Work.SignatureBordism.signature Q =
      ((Finset.univ.filter (fun i => 0 < d i)).card : ℤ) -
        ((Finset.univ.filter (fun i => d i < 0)).card : ℤ) := by
  classical
  -- The linear map `φ : (Fin n → 𝕜) →ₗ V`, `x ↦ ∑ i, x i • v i`.
  let φ : (Fin n → 𝕜) →ₗ[𝕜] V := Fintype.linearCombination 𝕜 v
  have hφ : ∀ x : Fin n → 𝕜, φ x = ∑ i, x i • v i :=
    fun x => Fintype.linearCombination_apply 𝕜 v x
  -- The diagonal form on the coordinate space.
  let W : QuadraticForm 𝕜 (Fin n → 𝕜) := QuadraticMap.weightedSumSquares 𝕜 d
  have hWform : ∀ z : Fin n → 𝕜, W z = ∑ i, (z i) ^ 2 * d i := by
    intro z
    show (QuadraticMap.weightedSumSquares 𝕜 d) z = _
    rw [QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, sq]
    ring
  -- `W` is the pullback of `Q` along `φ`.
  have hWQ : ∀ z : Fin n → 𝕜, W z = Q (φ z) := by
    intro z
    rw [hWform z, ← hdiag z, hφ z]
  -- `φ` is surjective, since `v` spans.
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    show (Fintype.linearCombination 𝕜 v).range = ⊤
    rw [Fintype.range_linearCombination]
    exact hspan
  -- `φ` is injective: the hypothesis of diagonality in a spanning family makes it so.
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hker : ∀ z : Fin n → 𝕜, φ z = 0 → z = 0 := by
      intro z hz
      -- the polar form of the diagonal form.
      have hpolar : ∀ u y : Fin n → 𝕜,
          QuadraticMap.polar W u y = ∑ i, (2 * u i * y i) * d i := by
        intro u y
        rw [QuadraticMap.polar, hWform (u + y), hWform u, hWform y]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply]
        ring
      funext j
      let ej : Fin n → 𝕜 := Pi.single j (1 : 𝕜)
      have hejj : ej j = 1 := by simp [ej]
      have heji : ∀ i, i ≠ j → ej i = 0 := fun i hi => by simp [ej, Pi.single_eq_of_ne hi]
      -- `polar W z e_j` vanishes because `φ z = 0`.
      have hpolar0 : QuadraticMap.polar W z ej = 0 := by
        rw [QuadraticMap.polar]
        have hzW : W z = 0 := by rw [hWQ z, hz, QuadraticMap.map_zero]
        have hzeW : W (z + ej) = W ej := by
          rw [hWQ (z + ej), hWQ ej, map_add, hz, zero_add]
        rw [hzeW, hzW, sub_zero, sub_self]
      rw [hpolar z ej] at hpolar0
      -- evaluating the sum at `j` collapses it to `2 * z j * d j`.
      have hsum : ∑ i, (2 * z i * ej i) * d i = 2 * z j * d j := by
        rw [Finset.sum_eq_single j]
        · rw [hejj]; ring
        · intro i _ hij; rw [heji i hij]; ring
        · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [hsum] at hpolar0
      have h2 : (2 : 𝕜) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp hpolar0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h2
        · exact h'
      · exact absurd h (hne j)
    have : x - y = 0 := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  let e : (Fin n → 𝕜) ≃ₗ[𝕜] V := LinearEquiv.ofBijective φ hbij
  -- `Q` is isometric to the weighted sum of squares with weights `d`.
  have hisom : QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares 𝕜 d) := by
    refine ⟨QuadraticMap.IsometryEquiv.mk e.symm ?_⟩
    intro y
    have hy : φ (e.symm y) = y := e.apply_symm_apply y
    change W (e.symm y) = Q y
    rw [hWform (e.symm y), ← hdiag (e.symm y), ← hφ (e.symm y), hy]
  -- Sylvester's law of inertia.
  have hsigPos := QuadraticForm.sigPos_of_equiv_weightedSumSquares (Q := Q) (w := d) hisom
  have hsigNeg := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (Q := Q) (w := d) hisom
  show (sigPos Q : ℤ) - (sigNeg Q : ℤ) = _
  rw [hsigPos, hsigNeg]
  have hp : {i | 0 < d i}.ncard = (Finset.univ.filter (fun i => 0 < d i)).card := by
    rw [Set.ncard_eq_toFinset_card]; congr 1; ext i; simp
  have hm : {i | d i < 0}.ncard = (Finset.univ.filter (fun i => d i < 0)).card := by
    rw [Set.ncard_eq_toFinset_card]; congr 1; ext i; simp
  rw [hp, hm]

end Work.Projective
