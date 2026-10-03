import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs

namespace Work.FIArea2.R6

/-- **Integrality of parallel lattice vectors, primitive direction.**

If `Int.gcd z₁ z₂ = 1` (the integer vector `z` is primitive) and `v` is parallel to `z`
(`v₁ z₂ = v₂ z₁`), then `v = m • z` is an integral multiple of `z`.  Concretely the multiplier is
the Bézout combination `m = v₁ · gcdA + v₂ · gcdB` of the coprimality relation
`z₁ · gcdA + z₂ · gcdB = 1`. -/
lemma wc_exists_int_smul_of_parallel_primitive {z1 z2 v1 v2 : ℤ} (hgcd : Int.gcd z1 z2 = 1)
    (hpar : v1 * z2 = v2 * z1) :
    ∃ m : ℤ, v1 = m * z1 ∧ v2 = m * z2 := by
  have hbez : z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2 = 1 := by
    have h := Int.gcd_eq_gcd_ab z1 z2
    rw [hgcd] at h
    push_cast at h
    linarith
  have hz : z1 * v2 = z2 * v1 := by rw [mul_comm z1 v2, mul_comm z2 v1]; exact hpar.symm
  refine ⟨v1 * Int.gcdA z1 z2 + v2 * Int.gcdB z1 z2, ?_, ?_⟩
  · have h1 : v1 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2) = v1 := by rw [hbez, mul_one]
    have key : v1 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2)
        - (v1 * Int.gcdA z1 z2 + v2 * Int.gcdB z1 z2) * z1 = 0 := by
      have h2 : v1 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2)
          - (v1 * Int.gcdA z1 z2 + v2 * Int.gcdB z1 z2) * z1
          = Int.gcdB z1 z2 * (v1 * z2 - v2 * z1) := by ring
      rw [h2, hpar, sub_self, mul_zero]
    linarith
  · have h1 : v2 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2) = v2 := by rw [hbez, mul_one]
    have key : v2 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2)
        - (v1 * Int.gcdA z1 z2 + v2 * Int.gcdB z1 z2) * z2 = 0 := by
      have h2 : v2 * (z1 * Int.gcdA z1 z2 + z2 * Int.gcdB z1 z2)
          - (v1 * Int.gcdA z1 z2 + v2 * Int.gcdB z1 z2) * z2
          = Int.gcdA z1 z2 * (z1 * v2 - z2 * v1) := by ring
      rw [h2, hz, sub_self, mul_zero]
    linarith

/-- **The parallel part of the lattice consists of `±` the shortest vector.**

Let `v ∈ L` (`L = {w : c ∣ A w₁ - B w₂}`) be a nonzero vector of minimal sup-norm. If `z ∈ L` is
primitive (`Int.gcd z.1 z.2 = 1`) and parallel to `v` (`wcDet v z = 0`), then `z = v` or
`z = -v`.

PROOF ROUTE: minimality gives `z = k • v` for some `k : ℤ` (integrality of parallel lattice vectors,
see `wc_min_vec_and_parallel`). Then `1 = Int.gcd (k v₁) (k v₂) = |k| · Int.gcd v₁ v₂`, so `|k| = 1`
and `Int.gcd v₁ v₂ = 1`, i.e. `z = ±v`. -/
theorem wc_det_zero_primitive (c A B : ℕ) (hA : 1 ≤ A) (hc : 1 ≤ c) (v : ℤ × ℤ)
    (hvL : wcInL c A B v) (hv0 : v ≠ 0)
    (hmin : ∀ w : ℤ × ℤ, wcInL c A B w → w ≠ 0 → wcSup v ≤ wcSup w)
    (z : ℤ × ℤ) (hzL : wcInL c A B z) (hprim : Int.gcd z.1 z.2 = 1) (hdet : wcDet v z = 0) :
    z = v ∨ z = (-v.1, -v.2) := by
  -- `z ≠ 0`, since a primitive vector cannot vanish.
  have hz0 : z ≠ 0 := by
    intro h
    have h1 : z.1 = 0 := by rw [h]; rfl
    have h2 : z.2 = 0 := by rw [h]; rfl
    rw [h1, h2] at hprim
    simp [Int.gcd] at hprim
  -- Parallelism of `v` and the primitive `z` makes `v` an integral multiple of `z`.
  have hpar : v.1 * z.2 = v.2 * z.1 := by
    have hh : v.1 * z.2 - v.2 * z.1 = 0 := hdet
    linarith
  obtain ⟨m, hm1, hm2⟩ := wc_exists_int_smul_of_parallel_primitive hprim hpar
  have hv_eq : v = (m * z.1, m * z.2) := Prod.ext hm1 hm2
  -- Since `z` is a nonzero lattice vector, minimality of `v` bounds the multiplier.
  have hsup : wcSup v = m.natAbs * wcSup z := by
    rw [hv_eq]
    show max (m * z.1).natAbs (m * z.2).natAbs = m.natAbs * max z.1.natAbs z.2.natAbs
    rw [Int.natAbs_mul, Int.natAbs_mul, max_mul_mul_left]
  have hminz : wcSup v ≤ wcSup z := hmin z hzL hz0
  have hle : m.natAbs * wcSup z ≤ wcSup z := by rw [← hsup]; exact hminz
  have hsupz_ne : wcSup z ≠ 0 := by
    intro h
    apply hz0
    have hx : z.1.natAbs = 0 := le_antisymm (h ▸ le_max_left _ _) (Nat.zero_le _)
    have hy : z.2.natAbs = 0 := le_antisymm (h ▸ le_max_right _ _) (Nat.zero_le _)
    exact Prod.ext (Int.natAbs_eq_zero.mp hx) (Int.natAbs_eq_zero.mp hy)
  have hz1 : 1 ≤ wcSup z := Nat.one_le_iff_ne_zero.mpr hsupz_ne
  have hmabs : m.natAbs ≤ 1 := by
    have h : m.natAbs * wcSup z ≤ 1 * wcSup z := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right h (by omega)
  obtain h0 | h1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hmabs
  · -- `m = 0` forces `v = 0`, contradicting `hv0`.
    exfalso
    apply hv0
    have hm0 : m = 0 := Int.natAbs_eq_zero.mp h0
    rw [hv_eq, hm0]
    simp
  · rcases Int.natAbs_eq m with hpos | hneg
    · -- `m = 1`, so `v = z`.
      left
      have hz1v : z.1 = v.1 := by rw [hm1, hpos, h1]; ring
      have hz2v : z.2 = v.2 := by rw [hm2, hpos, h1]; ring
      exact Prod.ext hz1v hz2v
    · -- `m = -1`, so `v = -z`.
      right
      have hz1v : z.1 = -v.1 := by rw [hm1, hneg, h1]; ring
      have hz2v : z.2 = -v.2 := by rw [hm2, hneg, h1]; ring
      exact Prod.ext hz1v hz2v

end Work.FIArea2.R6
