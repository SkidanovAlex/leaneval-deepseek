import Mathlib
import Submission.Mostow.GapADefs

/-!
# Transfer of the weighted-chord domination bound (`Work.Mostow.dominationTransfer`)

Setting: `e : OrthonormalBasis (Fin (m/2) × Fin 2) ℝ (E m)` is an orthonormal basis of `E m` split into
`m/2` two-dimensional blocks `span {e (i,0), e (i,1)}`, and `rot b` acts on the `i`-th block by
rotation by the angle `b i` (hypothesis `hrot`).  Given a point `Wz` whose `i`-th block coordinate
`Pᵢ Wz = ⟨e (i,0), Wz⟩ • e (i,0) + ⟨e (i,1), Wz⟩ • e (i,1)` has norm at most `ρ i`, and given that the
weighted chord length `∑ᵢ ρᵢ² · chord (b i)²` is at most `δ²`, we must show `‖rot b Wz - Wz‖ ≤ δ`.

The proof is the block-diagonal computation:
* `Wz = ∑ᵢ Pᵢ Wz` (the orthonormal basis expansion),
* `rot b Wz - Wz = ∑ᵢ (rot b (Pᵢ Wz) - Pᵢ Wz)`, the summands of which lie in pairwise orthogonal
  blocks, so `‖rot b Wz - Wz‖² = ∑ᵢ ‖rot b (Pᵢ Wz) - Pᵢ Wz‖²`,
* for a rotation by `t`, `‖rot t v - v‖² = (2 - 2 cos t) ‖v‖² = chord (t)² ‖v‖²` (the chirality of the
  chord on `AddCircle (2π)`, `chord x = 2 sin (‖x‖/2)`, is exactly `chord (t)² = 2 - 2 cos t`),
* so `‖rot b Wz - Wz‖² ≤ ∑ᵢ ρᵢ² chord (b i)² ≤ δ²`.
-/

namespace Work.Mostow

/-- `2 sin²(y/2) = 1 - cos y`. -/
private lemma two_mul_sin_sq_half (z : ℝ) : 2 * Real.sin (z / 2) ^ 2 = 1 - Real.cos z := by
  have h1 := Real.sin_sq_add_cos_sq (z / 2)
  have h2 := Real.cos_two_mul' (z / 2)
  have h3 : 2 * (z / 2) = z := by ring
  rw [h3] at h2
  linarith

/-- The chord length squared of a circle angle is `2 - 2 cos` of any representative:
`chord (t : AddCircle (2π))² = 2 - 2 cos t`. -/
private lemma chord_coe_sq (t : ℝ) :
    (Submission.Mostow.chord ((t : ℝ) : AddCircle (2 * Real.pi))) ^ 2 = 2 - 2 * Real.cos t := by
  have hcos : Real.cos ‖((t : ℝ) : AddCircle (2 * Real.pi))‖ = Real.cos t := by
    rw [AddCircle.norm_eq (2 * Real.pi) (x := t), Real.cos_abs, Real.cos_sub_int_mul_two_pi t]
  have hsin := two_mul_sin_sq_half ‖((t : ℝ) : AddCircle (2 * Real.pi))‖
  rw [hcos] at hsin
  rw [Submission.Mostow.chord]
  nlinarith [hsin]

/-- Pythagoras for an orthonormal pair: `‖a • u + b • v‖² = a² + b²`. -/
private lemma norm_sq_smul_add_smul_of_orthonormal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (a b : ℝ) : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hu' : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hv' : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huv' : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hu', hv', huv, huv', mul_zero, mul_one, add_zero, zero_add, starRingEnd_apply, star_trivial]
  ring

/-- Displacement of a single rotation block: rotating `x • u₀ + y • u₁` by the angle `t` moves it by a
vector of squared length `(2 - 2 cos t) ‖x • u₀ + y • u₁‖²`. -/
private lemma block_displacement {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u0 u1 : V} (hu0 : ‖u0‖ = 1) (hu1 : ‖u1‖ = 1) (h01 : inner ℝ u0 u1 = 0)
    (x y t : ℝ) :
    ‖((Real.cos t * x - Real.sin t * y) • u0 + (Real.sin t * x + Real.cos t * y) • u1)
        - (x • u0 + y • u1)‖ ^ 2
      = (2 - 2 * Real.cos t) * ‖x • u0 + y • u1‖ ^ 2 := by
  have hsub : ((Real.cos t * x - Real.sin t * y) • u0 + (Real.sin t * x + Real.cos t * y) • u1)
        - (x • u0 + y • u1)
      = (Real.cos t * x - Real.sin t * y - x) • u0 + (Real.sin t * x + Real.cos t * y - y) • u1 := by
    module
  rw [hsub, norm_sq_smul_add_smul_of_orthonormal hu0 hu1 h01,
      norm_sq_smul_add_smul_of_orthonormal hu0 hu1 h01]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The norm of a sum of a pairwise-orthogonal family is the ℓ²-norm of the norms. -/
private lemma norm_sum_sq_of_pairwise_orthogonal {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → V)
    (h : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  have aux : ∀ s : Finset ι, (∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (f i) (f j) = 0) →
      ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hT : inner ℝ (f a) (∑ i ∈ s, f i) = 0 := by
        rw [inner_sum]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        exact hs a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun hEq => ha (hEq.symm ▸ hi))
      have hnorm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f a) (∑ i ∈ s, f i) hT
      have hnorm2 : ‖f a + ∑ i ∈ s, f i‖ ^ 2 = ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by
        rw [pow_two, pow_two, pow_two]; exact hnorm
      rw [hnorm2, ih (fun i hi j hj hij =>
        hs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
  simpa using aux Finset.univ (fun i _ j _ hij => h i j hij)

theorem dominationTransfer (m : ℕ) (hm : Even m)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (rot : (Fin (m / 2) → AddCircle (2 * Real.pi)) →
      (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (hrot : ∀ (b : Fin (m / 2) → AddCircle (2 * Real.pi)) (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = b i ∧
        rot b (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
          (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
            (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (Wz : Submission.Mostow.E m) (ρ : Fin (m / 2) → ℝ) (hρ : ∀ i, 0 < ρ i)
    (δ : ℝ) (hδ : 0 < δ) (b : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hdom : ∀ i : Fin (m / 2),
      ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ≤ ρ i)
    (hdisp : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 ≤ δ ^ 2) :
    ‖rot b Wz - Wz‖ ≤ δ := by
  classical
  -- orthonormality of the block basis
  have hnrm : ∀ p : Fin (m / 2) × Fin 2, ‖e p‖ = 1 := by
    intro p
    have h2 : ‖e p‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, OrthonormalBasis.inner_eq_ite e p p]
      simp
    nlinarith [norm_nonneg (e p)]
  have hort : ∀ p q : Fin (m / 2) × Fin 2, p ≠ q → inner ℝ (e p) (e q) = 0 := by
    intro p q hpq
    rw [OrthonormalBasis.inner_eq_ite e p q]
    simp [hpq]
  -- the `i`-th block coordinate of `Wz` and the rotation angles
  let x : Fin (m / 2) → ℝ := fun i => inner ℝ (e (i, Fin.castSucc 0)) Wz
  let y : Fin (m / 2) → ℝ := fun i => inner ℝ (e (i, 1)) Wz
  let v : Fin (m / 2) → Submission.Mostow.E m :=
    fun i => x i • e (i, Fin.castSucc 0) + y i • e (i, 1)
  choose t ht hrotblock using fun i : Fin (m / 2) => hrot b i (x i) (y i)
  have hv_rot : ∀ i, rot b (v i) =
      (Real.cos (t i) * x i - Real.sin (t i) * y i) • e (i, Fin.castSucc 0) +
        (Real.sin (t i) * x i + Real.cos (t i) * y i) • e (i, 1) := fun i => hrotblock i
  have hv_eq : ∀ i, v i = x i • e (i, Fin.castSucc 0) + y i • e (i, 1) := fun i => rfl
  have hvi_le : ∀ i, ‖v i‖ ≤ ρ i := fun i => hdom i
  -- per-block displacement
  have hblock : ∀ i, ‖rot b (v i) - v i‖ ^ 2 = (2 - 2 * Real.cos (t i)) * ‖v i‖ ^ 2 := by
    intro i
    have hne : (i, Fin.castSucc (0 : Fin 1)) ≠ (i, (1 : Fin 2)) := by
      intro h
      have h2 : Fin.castSucc (0 : Fin 1) = (1 : Fin 2) := congrArg Prod.snd h
      exact absurd h2 (by decide)
    rw [hv_rot i, hv_eq i]
    exact block_displacement (hnrm _) (hnrm _) (hort _ _ hne) (x i) (y i) (t i)
  -- `Wz` is the sum of its block coordinates
  have hvWz : Wz = ∑ i, v i := by
    have hsr := OrthonormalBasis.sum_repr e Wz
    rw [Fintype.sum_prod_type] at hsr
    simp only [OrthonormalBasis.repr_apply_apply] at hsr
    rw [← hsr]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Fin.sum_univ_two]
    rfl
  have hsub : rot b Wz - Wz = ∑ i, (rot b (v i) - v i) := by
    rw [hvWz, map_sum (rot b) v Finset.univ, ← Finset.sum_sub_distrib]
  -- the displacement vectors of distinct blocks are orthogonal
  have horth : ∀ i j, i ≠ j → inner ℝ (rot b (v i) - v i) (rot b (v j) - v j) = 0 := by
    intro i j hij
    have hi : rot b (v i) - v i =
        (Real.cos (t i) * x i - Real.sin (t i) * y i - x i) • e (i, Fin.castSucc 0) +
          (Real.sin (t i) * x i + Real.cos (t i) * y i - y i) • e (i, 1) := by
      rw [hv_rot i, hv_eq i]; module
    have hj : rot b (v j) - v j =
        (Real.cos (t j) * x j - Real.sin (t j) * y j - x j) • e (j, Fin.castSucc 0) +
          (Real.sin (t j) * x j + Real.cos (t j) * y j - y j) • e (j, 1) := by
      rw [hv_rot j, hv_eq j]; module
    rw [hi, hj]
    have h00 : inner ℝ (e (i, Fin.castSucc 0)) (e (j, Fin.castSucc 0)) = 0 :=
      hort _ _ (fun h => hij (congrArg Prod.fst h))
    have h01 : inner ℝ (e (i, Fin.castSucc 0)) (e (j, (1 : Fin 2))) = 0 :=
      hort _ _ (fun h => hij (congrArg Prod.fst h))
    have h10 : inner ℝ (e (i, (1 : Fin 2))) (e (j, Fin.castSucc 0)) = 0 :=
      hort _ _ (fun h => hij (congrArg Prod.fst h))
    have h11 : inner ℝ (e (i, (1 : Fin 2))) (e (j, (1 : Fin 2))) = 0 :=
      hort _ _ (fun h => hij (congrArg Prod.fst h))
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      h00, h01, h10, h11, starRingEnd_apply, star_trivial, mul_zero, add_zero]
  have hnorm : ‖rot b Wz - Wz‖ ^ 2 = ∑ i, ‖rot b (v i) - v i‖ ^ 2 := by
    rw [hsub, norm_sum_sq_of_pairwise_orthogonal (fun i => rot b (v i) - v i) horth]
  -- the domination estimate, termwise
  have hbound : ∑ i, ‖rot b (v i) - v i‖ ^ 2 ≤ δ ^ 2 := by
    have h1 : ∀ i, ‖rot b (v i) - v i‖ ^ 2 ≤ (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 := by
      intro i
      have hch : 2 - 2 * Real.cos (t i) = (Submission.Mostow.chord (b i)) ^ 2 := by
        rw [← chord_coe_sq (t i), ht i]
      have hv2 : ‖v i‖ ^ 2 ≤ (ρ i) ^ 2 := by
        nlinarith [hvi_le i, norm_nonneg (v i), hρ i]
      calc ‖rot b (v i) - v i‖ ^ 2
          = (Submission.Mostow.chord (b i)) ^ 2 * ‖v i‖ ^ 2 := by rw [hblock i, hch]
        _ ≤ (Submission.Mostow.chord (b i)) ^ 2 * (ρ i) ^ 2 :=
              mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
        _ = (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 := by ring
    calc ∑ i, ‖rot b (v i) - v i‖ ^ 2
        ≤ ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ ≤ δ ^ 2 := hdisp
  have hsq : ‖rot b Wz - Wz‖ ^ 2 ≤ δ ^ 2 := by rw [hnorm]; exact hbound
  have hle := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ] at hle

end Work.Mostow
