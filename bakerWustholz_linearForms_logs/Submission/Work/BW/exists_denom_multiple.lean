import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.gramDet_rat_ne_zero
import Submission.Work.BW.gramDet_natAbs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.BW

/-- If `b ≠ 0` lies in the `ℚ`-span of the `ℚ`-independent rows of `L : Fin r → Fin n → ℤ`, then
some integer multiple of `b` is an integral combination of the rows: there are `N ≠ 0`, `B ≠ 0`
with `∑_a B_a L_a j = N b_j` for all `j`, and `|N| ≤ r! · ∏_a (∑_i |L_a i|)²`.

*Proof:* `A := L * Lᵀ` is an invertible integer Gram matrix (rows independent), `N := A.det`,
`B := A.cramer (L *ᵥ b)` (or `adjugate`), so `A *ᵥ B = N • (L *ᵥ b)`; with `β` satisfying
`Lᵀβ = b` one has `A *ᵥ β = L *ᵥ b`, hence `B = N β` and `Lᵀ B = N b`. `B ≠ 0` since `β ≠ 0`
(`b ≠ 0`). Hadamard for the positive semidefinite `A` (or Leibniz on a nonzero minor) bounds
`|det A| ≤ ∏_a A_aa = ∏_a ∑_i (L_a i)² ≤ ∏_a (∑_i |L_a i|)² ≤ r! ∏_a (∑_i |L_a i|)²`. -/
theorem exists_denom_multiple {n r : ℕ} (hr : 1 ≤ r) (L : Fin r → Fin n → ℤ) (b : Fin n → ℤ)
    (hb0 : b ≠ 0) (hind : LinearIndependent ℚ (fun a i => (L a i : ℚ)))
    (hb : (fun i => (b i : ℚ)) ∈ Submodule.span ℚ (Set.range fun a i => (L a i : ℚ))) :
    ∃ (N : ℤ) (B : Fin r → ℤ), N ≠ 0 ∧ B ≠ 0 ∧
      (∀ j, ∑ a, B a * L a j = N * b j) ∧
      (N.natAbs : ℝ) ≤ (r.factorial : ℝ) * ∏ a, ((∑ i, |(L a i : ℝ)|)) ^ 2 := by
  have _ : 1 ≤ r := hr
  classical
  -- The family of rows, as vectors over `ℚ`, and the coordinates of `b` in their span.
  set f : Fin r → Fin n → ℚ := fun a i => (L a i : ℚ) with hf
  have hfind : LinearIndependent ℚ f := hind
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ (v := f)
    (x := fun i => (b i : ℚ))).mp hb
  have hcapp : ∀ i, ∑ a, c a * (L a i : ℚ) = (b i : ℚ) := by
    intro i
    have h := congrFun hc i
    simpa [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hcne : c ≠ 0 := by
    intro hc0
    apply hb0
    funext i
    have h := hcapp i
    rw [hc0] at h
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    exact_mod_cast h.symm
  -- The integral Gram matrix, its determinant, and the Cramer solution.
  set A : Matrix (Fin r) (Fin r) ℤ := Matrix.of (fun a a' => ∑ i, L a i * L a' i) with hA
  set N : ℤ := A.det with hN
  set y : Fin r → ℤ := fun a => ∑ i, L a i * b i with hy
  set B : Fin r → ℤ := A.adjugate *ᵥ y with hB
  -- `A` is nonsingular because the rows are independent over `ℚ`.
  have hmapdet : A.map (Int.castRingHom ℚ)
      = Matrix.of (fun a a' : Fin r => ∑ i, f a i * f a' i) := by
    ext a a'
    simp [hA, hf, Matrix.map_apply]
  have hAqdet : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [hmapdet]
    exact gramDet_rat_ne_zero f hfind
  have hNne : N ≠ 0 := by
    intro h
    have hAdet : A.det = 0 := by rw [← hN]; exact h
    refine hAqdet ?_
    have hmap := RingHom.map_det (Int.castRingHom ℚ) A
    rw [hAdet] at hmap
    simpa using hmap.symm
  -- Cramer's rule over `ℤ`: `A *ᵥ B = N • (L *ᵥ b)`.
  have hAB : A *ᵥ B = N • y := by
    rw [hB, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_cramer, hN]
  have hsum_cast : ∀ k,
      ∑ a, (A.map (Int.castRingHom ℚ)) k a * (B a : ℚ) = (N : ℚ) * (y k : ℚ) := by
    intro k
    have hk := congrFun hAB k
    have hz : ∑ a, A k a * B a = N * y k := by
      simpa [Matrix.mulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul] using hk
    have h2 : ∑ a, ((A k a : ℤ) : ℚ) * (B a : ℚ) = (N : ℚ) * (y k : ℚ) := by
      have h3 := congrArg (fun z : ℤ => (z : ℚ)) hz
      push_cast at h3
      exact h3
    convert h2 using 2 with a
    rw [Matrix.map_apply]
    rfl
  -- `A *ᵥ c = y` over `ℚ` (that is, `Lᵀ c = b`).
  have hAqc : ∀ k, ∑ a, (A.map (Int.castRingHom ℚ)) k a * c a = (y k : ℚ) := by
    intro k
    have h1 : ∀ a, (A.map (Int.castRingHom ℚ)) k a = ∑ i, (L k i : ℚ) * (L a i : ℚ) := by
      intro a
      simp [hA, Matrix.map_apply]
    simp only [h1]
    calc ∑ a, (∑ i, (L k i : ℚ) * (L a i : ℚ)) * c a
        = ∑ a, ∑ i, (L k i : ℚ) * ((L a i : ℚ) * c a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ i, ∑ a, (L k i : ℚ) * ((L a i : ℚ) * c a) := Finset.sum_comm
      _ = ∑ i, (L k i : ℚ) * ∑ a, (L a i : ℚ) * c a := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ = ∑ i, (L k i : ℚ) * (b i : ℚ) := by
            apply Finset.sum_congr rfl; intro i _
            congr 1
            rw [← hcapp i]
            apply Finset.sum_congr rfl; intro a _; ring
      _ = ((∑ i, L k i * b i : ℤ) : ℚ) := by push_cast; rfl
      _ = (y k : ℚ) := by rw [hy]
  -- Nonsingularity of `A` over `ℚ` gives `B = N · c`.
  have hBc : ∀ a, (B a : ℚ) = (N : ℚ) * c a := by
    have hinj : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hAqdet
    intro a
    have heq : (A.map (Int.castRingHom ℚ)) *ᵥ (fun a => (B a : ℚ))
        = (A.map (Int.castRingHom ℚ)) *ᵥ (fun a => (N : ℚ) * c a) := by
      funext k
      calc (A.map (Int.castRingHom ℚ) *ᵥ (fun a => (B a : ℚ))) k
          = ∑ a, (A.map (Int.castRingHom ℚ)) k a * (B a : ℚ) := rfl
        _ = (N : ℚ) * (y k : ℚ) := hsum_cast k
        _ = (N : ℚ) * ∑ a, (A.map (Int.castRingHom ℚ)) k a * c a := by rw [hAqc k]
        _ = ∑ a, (N : ℚ) * ((A.map (Int.castRingHom ℚ)) k a * c a) := by
              rw [Finset.mul_sum]
        _ = ∑ a, (A.map (Int.castRingHom ℚ)) k a * ((N : ℚ) * c a) := by
              apply Finset.sum_congr rfl; intro a _; ring
        _ = (A.map (Int.castRingHom ℚ) *ᵥ (fun a => (N : ℚ) * c a)) k := rfl
    exact congrFun (hinj heq) a
  have hBne : B ≠ 0 := by
    intro hB0'
    apply hcne
    funext a
    have h := hBc a
    rw [hB0'] at h
    simp only [Pi.zero_apply, Int.cast_zero] at h
    have hNq : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hNne
    exact (mul_eq_zero.mp h.symm).resolve_left hNq
  -- The integrality statement, `Lᵀ B = N b`.
  have hfinal : ∀ j, ∑ a, B a * L a j = N * b j := by
    intro j
    have hQ : ((∑ a, B a * L a j : ℤ) : ℚ) = ((N * b j : ℤ) : ℚ) := by
      push_cast
      calc ∑ a, (B a : ℚ) * (L a j : ℚ)
          = ∑ a, ((N : ℚ) * c a) * (L a j : ℚ) := by
              apply Finset.sum_congr rfl; intro a _; rw [hBc a]
        _ = (N : ℚ) * ∑ a, c a * (L a j : ℚ) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
        _ = (N : ℚ) * (b j : ℚ) := by rw [hcapp j]
    exact_mod_cast hQ
  -- The Hadamard bound for `|det A| = |N|`.
  have hbound : (N.natAbs : ℝ) ≤ (r.factorial : ℝ) * ∏ a, (∑ i, |(L a i : ℝ)|) ^ 2 := by
    have := gramDet_natAbs_le L
    simpa [hN, hA] using this
  exact ⟨N, B, hNne, hBne, hfinal, hbound⟩

end Work.BW
