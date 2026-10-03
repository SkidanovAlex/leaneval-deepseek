import Mathlib
import Submission.Work.OROneRel.interval_defs

/-!
# The residue orbit `orb A B n = ((n : ℤ) * B) % A`

Let `A ≥ 2` and `B` be integers such that `p * A + q * B = 1` for some integers `p, q`
(i.e. `B` is invertible modulo `A`).  The *residue orbit*

`orb A B n = ((n : ℤ) * B) % A`

is the orbit of `0` under the map `x ↦ (x + B) % A`; equivalently it lists the residues
`n * B` in the interval `[0, A - 1]`.

The main result of this file, `orbit_arith`, collects the elementary combinatorial
properties of `orb` that are used in the connectivity argument for the interval graph
(`Submission/Work/OROneRel/interval_connected.lean`):

* every value `orb A B n` lies in `[0, A - 1]`;
* `orb` satisfies the recursion `orb A B (n + 1) = (orb A B n + B) % A`;
* `orb A B (A.toNat) = 0`, i.e. the orbit is `A`-periodic;
* the value `A - 1` is attained at a *unique* index `j0 ≤ A - 1`;
* conversely every residue `r ∈ [0, A - 1]` is attained by some index `n ≤ A - 1`
  (so `orb A B` restricts to a bijection of `{0, …, A - 1}` with itself).

The engine behind the last two statements is the arithmetic fact
`emod_mul_iff_modEq_bezout`: multiplication by `B` on residues modulo `A` is inverted by
multiplication by `q`, hence the map `n ↦ (n * B) % A` is a bijection of the residue
system `{0, …, A - 1}`.
-/

namespace Work.OROneRel

/-- **The arithmetic core.**  If `p * A + q * B = 1`, then `n * B` and `r` have the same
residue modulo `A` exactly when `n` and `r * q` do: multiplication by `B` is inverted
modulo `A` by multiplication by `q`.  (No hypothesis on `A` is needed; for `A = 0` the
relation `p * 0 + q * B = 1` forces `B = q = ±1` and the statement is still correct.) -/
lemma emod_mul_iff_modEq_bezout {A B p q : ℤ} (hbez : p * A + q * B = 1) (n r : ℤ) :
    (n * B) % A = r % A ↔ n ≡ r * q [ZMOD A] := by
  -- Both sides are equivalent to `A ∣ n - r * q`; the Bezout relation is exactly what
  -- makes multiplication by `q` invert multiplication by `B` modulo `A`.
  have hqB : q * B = 1 - p * A := by linarith
  have key1 : A ∣ n * B - r ↔ A ∣ n - r * q := by
    constructor
    · intro h
      have h1 : A ∣ q * (n * B - r) := dvd_mul_of_dvd_right h q
      have h2 : A ∣ (n * p) * A := dvd_mul_left A (n * p)
      have key : q * (n * B - r) = (n - r * q) - (n * p) * A := by
        calc q * (n * B - r) = n * (q * B) - q * r := by ring
          _ = n * (1 - p * A) - q * r := by rw [hqB]
          _ = (n - r * q) - (n * p) * A := by ring
      rw [key] at h1
      simpa using dvd_add h1 h2
    · intro h
      have h1 : A ∣ (n - r * q) * B := dvd_mul_of_dvd_left h B
      have h2 : A ∣ (r * p) * A := dvd_mul_left A (r * p)
      have key : (n - r * q) * B = (n * B - r) + (r * p) * A := by
        calc (n - r * q) * B = n * B - r * (q * B) := by ring
          _ = n * B - r * (1 - p * A) := by rw [hqB]
          _ = (n * B - r) + (r * p) * A := by ring
      rw [key] at h1
      simpa using dvd_sub h1 h2
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero, Int.modEq_iff_dvd]
  rw [key1]
  rw [show r * q - n = -(n - r * q) by ring, dvd_neg]

/-- **The orbit is inverted by `q`.**  For indices `n ≤ A - 1` and residues `r ∈ [0, A - 1]`,
the equation `orb A B n = r` is equivalent to the explicit congruence
`n ≡ r * q (mod A)`, i.e. to the equality `(n : ℤ) = (r * q) % A`. -/
lemma orb_eq_iff_bezout {A B p q : ℤ} (hbez : p * A + q * B = 1)
    {n : ℕ} {r : ℤ} (hn : (n : ℤ) ≤ A - 1) (hr0 : 0 ≤ r) (hr1 : r ≤ A - 1) :
    orb A B n = r ↔ (n : ℤ) = (r * q) % A := by
  -- Inside the ranges, `% A` is the identity, so the congruence of
  -- `emod_mul_iff_modEq_bezout` becomes an equality.
  have hrA : r % A = r := Int.emod_eq_of_lt hr0 (by linarith)
  have hnA : (n : ℤ) % A = (n : ℤ) := Int.emod_eq_of_lt (Int.natCast_nonneg n) (by linarith)
  have h1 : ((n : ℤ) * B) % A = r ↔ (n : ℤ) ≡ r * q [ZMOD A] := by
    have h0 := emod_mul_iff_modEq_bezout hbez (n : ℤ) r
    rwa [hrA] at h0
  show ((n : ℤ) * B) % A = r ↔ (n : ℤ) = (r * q) % A
  rw [h1]
  show (n : ℤ) % A = (r * q) % A ↔ (n : ℤ) = (r * q) % A
  rw [hnA]

/-- The orbit `orb A B n` lies in the interval `[0, A - 1]`, is obtained from the previous
value by adding `B` and reducing, is `A`-periodic, attains `A - 1` at a unique index `j0`,
and hits every residue `r ∈ [0, A - 1]` at some index `n ≤ A - 1`. -/
theorem orbit_arith {A B : ℤ} (hA : 2 ≤ A) {p q : ℤ} (hbez : p * A + q * B = 1) :
    (∀ n : ℕ, 0 ≤ orb A B n ∧ orb A B n < A) ∧
    (∀ n : ℕ, orb A B (n + 1) = (orb A B n + B) % A) ∧
    orb A B A.toNat = 0 ∧
    (∃ j0 : ℕ, (j0 : ℤ) ≤ A - 1 ∧ orb A B j0 = A - 1 ∧
      (∀ n : ℕ, (n : ℤ) ≤ A - 1 → orb A B n = A - 1 → n = j0)) ∧
    (∀ r : ℤ, 0 ≤ r → r ≤ A - 1 → ∃ n : ℕ, (n : ℤ) ≤ A - 1 ∧ orb A B n = r) := by
  have hApos : 0 < A := by linarith
  have hAne : A ≠ 0 := by linarith
  -- `% A` of an integer is a nonnegative integer below `A`, so its `toNat` is that integer
  -- and hence is `≤ A - 1`.
  have htoNat : ∀ z : ℤ, (((z % A).toNat : ℤ)) = z % A := fun z =>
    Int.toNat_of_nonneg (Int.emod_nonneg z hAne)
  have htoNat_le : ∀ z : ℤ, (((z % A).toNat : ℤ)) ≤ A - 1 := by
    intro z
    have h1 : (((z % A).toNat : ℤ)) = z % A := htoNat z
    have h2 : z % A < A := Int.emod_lt_of_pos z hApos
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- every value of the orbit lies in `[0, A - 1]`
    intro n
    exact ⟨Int.emod_nonneg _ hAne, Int.emod_lt_of_pos _ hApos⟩
  · -- the recursion `orb (n + 1) = (orb n + B) % A`
    intro n
    show ((((n + 1 : ℕ) : ℤ)) * B) % A = (((((n : ℕ) : ℤ)) * B) % A + B) % A
    rw [show (((n + 1 : ℕ) : ℤ)) = (((n : ℕ) : ℤ)) + 1 by push_cast; ring]
    rw [show ((((n : ℕ) : ℤ)) + 1) * B = (((n : ℕ) : ℤ)) * B + B by ring]
    exact (Int.emod_add_emod (((n : ℕ) : ℤ) * B) A B).symm
  · -- `A`-periodicity: `orb A B A.toNat = 0`
    show (((A.toNat : ℤ)) * B) % A = 0
    rw [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ A)]
    exact Int.mul_emod_right A B
  · -- `A - 1` is attained, at the unique index `j0 = ((A - 1) * q) % A`
    refine ⟨(((A - 1) * q) % A).toNat, htoNat_le ((A - 1) * q), ?_, ?_⟩
    · exact (orb_eq_iff_bezout hbez (n := (((A - 1) * q) % A).toNat) (r := A - 1)
        (htoNat_le ((A - 1) * q)) (by linarith) le_rfl).mpr (htoNat ((A - 1) * q))
    · intro n hn horb
      have h := (orb_eq_iff_bezout hbez (n := n) (r := A - 1) hn (by linarith) le_rfl).mp horb
      have h2 : (n : ℤ) = ((((A - 1) * q) % A).toNat : ℤ) := by rw [h, htoNat]
      exact_mod_cast h2
  · -- surjectivity onto `[0, A - 1]`
    intro r hr0 hr1
    refine ⟨((r * q) % A).toNat, htoNat_le (r * q), ?_⟩
    exact (orb_eq_iff_bezout hbez (n := ((r * q) % A).toNat) (r := r)
      (htoNat_le (r * q)) hr0 hr1).mpr (htoNat (r * q))

end Work.OROneRel
