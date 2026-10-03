/-
# `FIArea2/R6/wc_parallel_of_min`

**Lattice vectors parallel to a shortest vector are multiples of it.**

Let `L = {w : ℤ × ℤ // (c : ℤ) ∣ A w.1 - B w.2}` be the per-modulus lattice of `WCbasicDefs`
(`wcInL`), let `v ∈ L` be a nonzero vector of minimal sup-norm `wcSup v` among the nonzero
elements of `L` (`hmin`), and let `z ∈ L` be parallel to `v` (`wcDet v z = 0`).  Then `z = k • v`
for some `k : ℤ`.

This is the elementary "division" (Euclidean-descent) step behind `wcMinVec_and_parallel`: no
primitivity of `v` is needed, because minimality of `v` itself forces the multiplier to be an
integer.  Concretely, if `v.1` attains the sup-norm (the other case is reduced to this one by
swapping coordinates), put

`q = z.1 / v.1`,  `u = z - q • v = (z.1 % v.1, z.2 - q * v.2) ∈ L`.

Then `|u.1| = |z.1 % v.1| < |v.1| = wcSup v`, and `u` is still parallel to `v`
(`wcDet v u = wcDet v z - q * wcDet v v = 0`), whence `|u.2| ≤ |u.1|` and so
`wcSup u < wcSup v`.  Minimality of `v` forces `u = 0`, i.e. `z = q • v`.

The auxiliary lemma `wc_smul_of_parallel_of_coord_min` is the coordinate-`1` statement for an
arbitrary pair of vectors `a, b` (it never mentions the lattice `wcInL`); the main theorem derives
the general case from it by a coordinate swap, using the fact that `wcInL c A B` is closed under
`w ↦ w - q • v`.

Note that no hypothesis on `c, A, B` (`1 ≤ c`, `1 ≤ A`, …) is needed: `wcInL c A B` is an additive
subgroup of `ℤ²` for every `c, A, B`, and the argument only uses that plus minimality.
-/
import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs

namespace Work.FIArea2.R6

/-- **Euclidean descent in coordinate `1`.**

Let `a ≠ 0` be a nonzero integer vector whose first coordinate attains the sup-norm
(`a.1.natAbs = wcSup a`), let `b` be parallel to `a` (`wcDet a b = 0`), and suppose that every
nonzero vector of the shape `b - q • a` has sup-norm at least `wcSup a`
(a "minimality" hypothesis, satisfied by a shortest nonzero vector of any subgroup of `ℤ²`
containing `a` and `b`).  Then `b = k • a` for some `k : ℤ`.

The multiplier is produced explicitly as the Euclidean quotient `b.1 / a.1`: the remainder vector
`(b.1 % a.1, b.2 - q * a.2)` has strictly smaller sup-norm than `a`, hence must vanish. -/
lemma wc_smul_of_parallel_of_coord_min {a b : ℤ × ℤ} (ha0 : a ≠ 0)
    (hmax : a.1.natAbs = wcSup a) (hpar : wcDet a b = 0)
    (hmin : ∀ q : ℤ, (b.1 - q * a.1, b.2 - q * a.2) ≠ 0 →
        wcSup a ≤ wcSup (b.1 - q * a.1, b.2 - q * a.2)) :
    ∃ k : ℤ, b = (k * a.1, k * a.2) := by
  -- `a ≠ 0` makes its sup-norm positive, and `hmax` transfers this to the first coordinate.
  have hsup0 : wcSup a ≠ 0 := by
    intro h
    apply ha0
    have h1 : a.1.natAbs = 0 := le_antisymm (h ▸ le_max_left _ _) (Nat.zero_le _)
    have h2 : a.2.natAbs = 0 := le_antisymm (h ▸ le_max_right _ _) (Nat.zero_le _)
    exact Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2)
  have ha1pos : 0 < a.1.natAbs := by rw [hmax]; exact Nat.pos_of_ne_zero hsup0
  have ha1ne : a.1 ≠ 0 := by
    intro h; rw [h] at ha1pos; simp at ha1pos
  set q : ℤ := b.1 / a.1 with hq
  set u : ℤ × ℤ := (b.1 - q * a.1, b.2 - q * a.2) with hu
  -- The first coordinate of `u` is the Euclidean remainder of `b.1` modulo `a.1`.
  have hu1 : u.1 = b.1 % a.1 := by
    have h := Int.emod_add_mul_ediv b.1 a.1
    rw [mul_comm a.1 (b.1 / a.1)] at h
    simp only [hu, hq]
    linarith
  -- hence the first coordinate of `u` is strictly smaller than the sup-norm of `a`.
  have hu1lt : u.1.natAbs < a.1.natAbs := by
    rw [hu1]
    have h1 : 0 ≤ b.1 % a.1 := Int.emod_nonneg b.1 ha1ne
    have h2 : b.1 % a.1 < |a.1| := Int.emod_lt_abs b.1 ha1ne
    have h3 : |a.1| = (a.1.natAbs : ℤ) := Int.abs_eq_natAbs a.1
    omega
  -- `u` is still parallel to `a`.
  have hparu : a.1 * u.2 = a.2 * u.1 := by
    have h : wcDet a u = 0 := by
      show a.1 * u.2 - a.2 * u.1 = 0
      simp only [hu, hq]
      linear_combination hpar
    linarith
  -- so the second coordinate of `u` is bounded by the first one.
  have hu2le : u.2.natAbs ≤ u.1.natAbs := by
    have hnat : a.1.natAbs * u.2.natAbs = a.2.natAbs * u.1.natAbs := by
      have h := congrArg Int.natAbs hparu
      simpa [Int.natAbs_mul] using h
    have hle : a.2.natAbs ≤ a.1.natAbs := by rw [hmax]; exact le_max_right _ _
    have h : a.1.natAbs * u.2.natAbs ≤ a.1.natAbs * u.1.natAbs := by
      rw [hnat]; exact Nat.mul_le_mul hle le_rfl
    exact Nat.le_of_mul_le_mul_left h ha1pos
  -- consequently `wcSup u < wcSup a`.
  have hsupu : wcSup u < wcSup a := by
    have hmaxa : max a.1.natAbs a.2.natAbs = a.1.natAbs := hmax.symm
    show max u.1.natAbs u.2.natAbs < max a.1.natAbs a.2.natAbs
    rw [hmaxa]
    exact max_lt hu1lt (lt_of_le_of_lt hu2le hu1lt)
  -- minimality forces `u = 0`.
  have hu0 : u = 0 := by
    by_contra hne
    have h : wcSup a ≤ wcSup u := by
      have h2 := hmin q (by rwa [hu] at hne)
      rwa [← hu] at h2
    omega
  have hb1 : b.1 = q * a.1 := by
    have h := congrArg Prod.fst hu0
    rw [hu] at h
    simp at h
    linarith
  have hb2 : b.2 = q * a.2 := by
    have h := congrArg Prod.snd hu0
    rw [hu] at h
    simp at h
    linarith
  exact ⟨q, Prod.ext hb1 hb2⟩

/-- **Vectors of the lattice parallel to a shortest lattice vector are its integer multiples.**

If `v` is a nonzero vector of the lattice `L = wcInL c A B` of minimal sup-norm among the nonzero
vectors of `L`, and `z ∈ L` is parallel to `v` (`wcDet v z = 0`), then `z = k • v` for some `k : ℤ`.

The proof reduces to `wc_smul_of_parallel_of_coord_min` in the coordinate that attains
`wcSup v`; in the degenerate case `|v.1| ≤ |v.2|` one swaps the two coordinates of `v` and `z`
(which preserves `wcSup` and negates `wcDet`).  The vector `z - q • v` used in the division step
lies in `L` because `wcInL c A B` is an additive subgroup of `ℤ²`. -/
theorem wc_parallel_of_min (c A B : ℕ) (v z : ℤ × ℤ)
    (hvL : wcInL c A B v) (hv0 : v ≠ 0)
    (hmin : ∀ w : ℤ × ℤ, wcInL c A B w → w ≠ 0 → wcSup v ≤ wcSup w)
    (hzL : wcInL c A B z) (hdet : wcDet v z = 0) :
    ∃ k : ℤ, z = (k * v.1, k * v.2) := by
  -- `wcInL c A B` is closed under `w ↦ w - q • v`.
  have hmem : ∀ q : ℤ, wcInL c A B (z.1 - q * v.1, z.2 - q * v.2) := by
    intro q
    obtain ⟨m1, hm1⟩ := hvL
    obtain ⟨m2, hm2⟩ := hzL
    refine ⟨m2 - q * m1, ?_⟩
    have hgoal : (A : ℤ) * (z.1 - q * v.1) - (B : ℤ) * (z.2 - q * v.2)
        = ((A : ℤ) * z.1 - (B : ℤ) * z.2) - q * ((A : ℤ) * v.1 - (B : ℤ) * v.2) := by ring
    rw [hgoal, hm2, hm1]
    ring
  rcases le_total v.1.natAbs v.2.natAbs with hle | hle
  · -- `|v.1| ≤ |v.2|`: swap the coordinates and apply the coordinate-`1` lemma.
    have hmax : v.2.natAbs = wcSup v := (max_eq_right hle).symm
    have hv0' : (v.2, v.1) ≠ 0 := by
      intro h
      apply hv0
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    have hmax' : (v.2, v.1).1.natAbs = wcSup (v.2, v.1) := by
      show v.2.natAbs = max v.2.natAbs v.1.natAbs
      rw [max_comm]
      exact hmax
    have hpar' : wcDet (v.2, v.1) (z.2, z.1) = 0 := by
      show v.2 * z.1 - v.1 * z.2 = 0
      have h : v.1 * z.2 - v.2 * z.1 = 0 := hdet
      linarith
    have hmin' : ∀ q : ℤ,
        ((z.2, z.1).1 - q * (v.2, v.1).1, (z.2, z.1).2 - q * (v.2, v.1).2) ≠ 0 →
        wcSup (v.2, v.1)
          ≤ wcSup ((z.2, z.1).1 - q * (v.2, v.1).1, (z.2, z.1).2 - q * (v.2, v.1).2) := by
      intro q hq
      have hq' : (z.1 - q * v.1, z.2 - q * v.2) ≠ 0 := by
        intro h
        apply hq
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      have hthis := hmin _ (hmem q) hq'
      show max v.2.natAbs v.1.natAbs ≤ max (z.2 - q * v.2).natAbs (z.1 - q * v.1).natAbs
      have e1 : max v.2.natAbs v.1.natAbs = max v.1.natAbs v.2.natAbs := max_comm _ _
      have e2 : max (z.2 - q * v.2).natAbs (z.1 - q * v.1).natAbs
          = max (z.1 - q * v.1).natAbs (z.2 - q * v.2).natAbs := max_comm _ _
      rw [e1, e2]
      exact hthis
    obtain ⟨k, hk⟩ := wc_smul_of_parallel_of_coord_min hv0' hmax' hpar' hmin'
    refine ⟨k, ?_⟩
    have h1 : z.2 = k * v.2 := congrArg Prod.fst hk
    have h2 : z.1 = k * v.1 := congrArg Prod.snd hk
    exact Prod.ext h2 h1
  · -- `|v.2| ≤ |v.1|`: the first coordinate attains the sup-norm.
    have hmax : v.1.natAbs = wcSup v := (max_eq_left hle).symm
    obtain ⟨k, hk⟩ := wc_smul_of_parallel_of_coord_min hv0 hmax hdet
      (fun q hq => hmin _ (hmem q) hq)
    exact ⟨k, hk⟩

end Work.FIArea2.R6
