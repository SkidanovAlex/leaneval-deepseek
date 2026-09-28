import Mathlib
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs

/-!
# The integer points of the rational spread are the saturation

For an integral lattice `L ⊆ ℤ^ι` we have

`castL b ∈ spread L ↔ b ∈ satLat L`,

i.e. an integer vector lies in the `ℚ`-span of the rational points of `L` exactly when one of
its non-zero integer multiples lies in `L`.

The proof is the general (and completely elementary) fact that for a `ℤ`-submodule `K` of a
`ℚ`-vector space `V`,

`x ∈ span_ℚ K ↔ ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ K`,

proved here as `exists_zsmul_mem_of_mem_span` (forward: clear the denominators of a rational
linear combination) and `mem_span_of_exists_zsmul_mem` (backward: divide by `m`).
-/

namespace Work.HP.numaux

/-- If `K` is a `ℤ`-submodule of a `ℚ`-vector space, then every element of the `ℚ`-span of `K`
has a non-zero integer multiple lying in `K` (clear the denominators of the coefficients). -/
lemma exists_zsmul_mem_of_mem_span {V : Type*} [AddCommGroup V] [Module ℚ V]
    (K : Submodule ℤ V) {x : V} (hx : x ∈ Submodule.span ℚ (K : Set V)) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ K := by
  refine Submodule.span_induction (p := fun x _ => ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ K) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact ⟨1, one_ne_zero, by simpa using hy⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  · intro y z hy hz ihy ihz
    obtain ⟨m, hm, hmy⟩ := ihy
    obtain ⟨n, hn, hnz⟩ := ihz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : (m * n) • (y + z) = n • (m • y) + m • (n • z) := by
      rw [mul_smul, smul_add, smul_add, smul_comm m n y, smul_comm m n z]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ n hmy) (Submodule.smul_mem _ m hnz)
  · intro c y hy ihy
    obtain ⟨m, hm, hmy⟩ := ihy
    refine ⟨m * (c.den : ℤ), mul_ne_zero hm (by exact_mod_cast c.den_nz), ?_⟩
    -- the denominator of `c` clears the rational scalar
    have h1 : (c.den : ℤ) • (c • y) = (c.num : ℤ) • y := by
      rw [← Int.cast_smul_eq_zsmul ℚ (c.den : ℤ) (c • y),
        ← Int.cast_smul_eq_zsmul ℚ c.num y]
      push_cast
      rw [← mul_smul, mul_comm, Rat.mul_den_eq_num]
    have h2 : (m * (c.den : ℤ)) • (c • y) = (c.num : ℤ) • (m • y) := by
      rw [mul_smul, h1, smul_comm]
    rw [h2]
    exact Submodule.smul_mem _ (c.num : ℤ) hmy

/-- Conversely, a vector with a non-zero integer multiple in the `ℤ`-submodule `K` lies in the
`ℚ`-span of `K`. -/
lemma mem_span_of_exists_zsmul_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (K : Submodule ℤ V) {x : V} (h : ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ K) :
    x ∈ Submodule.span ℚ (K : Set V) := by
  obtain ⟨m, hm, hmx⟩ := h
  have h0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hthis : ((m : ℚ))⁻¹ • (m • x) = x := by
    rw [← Int.cast_smul_eq_zsmul ℚ m x, smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [← hthis]
  exact Submodule.smul_mem _ ((m : ℚ))⁻¹ (Submodule.subset_span hmx)

theorem castL_mem_spread_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    (b : ι → ℤ) : castL b ∈ spread L ↔ b ∈ satLat L := by
  constructor
  · intro hb
    rw [spread] at hb
    obtain ⟨m, hm, hmK⟩ := exists_zsmul_mem_of_mem_span (L.map (castL (ι := ι))) hb
    obtain ⟨l, hl, hlK⟩ := Submodule.mem_map.mp hmK
    refine ⟨m, hm, ?_⟩
    have h2 : castL l = castL (m • b) := by rw [hlK, map_smul]
    exact (castL_injective (ι := ι) h2) ▸ hl
  · rintro ⟨m, hm, hmb⟩
    rw [spread]
    refine mem_span_of_exists_zsmul_mem (L.map (castL (ι := ι))) ⟨m, hm, ?_⟩
    rw [← map_smul]
    exact Submodule.mem_map.mpr ⟨m • b, hmb, rfl⟩

end Work.HP.numaux
