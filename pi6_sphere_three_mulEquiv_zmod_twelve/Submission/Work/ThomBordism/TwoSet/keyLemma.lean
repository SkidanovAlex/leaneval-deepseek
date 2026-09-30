import Mathlib
import Submission.Work.ThomBordism.TwoSet.Cells

/-!
# The corrected key combinatorial lemma

`keyLemma`: if every coordinate of `x : I^j` is within `1/(4N)` of the coordinate interval of the
grid cell `c` (the satisfiable closeness condition, the same one as in
`Work.ThomBordism.TwoSet.clampCell_mem_cOf`), and the clamp of `x` onto `c` does not lie on the
relative boundary of `c`, then `cOf N x` contains `c`, and if `x ∉ cellSet c` then
`cellDim (cOf N x) > cellDim c`.

This is the tool for the value analysis of the cell-by-cell compression proof: for `x` in the
support of the modification of `c` with `cellDim (cOf N x) ≤ cellDim c` and `x ∉ cellSet c`, the
clamp of `x` lies on the relative boundary of `c`, so the push applied there is the identity on
`g`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

theorem keyLemma {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N) {x : IC j}
    (hclose : ∀ i : Fin j, (c.lo i : ℝ) - 1/4 < (N:ℝ) * (x i : ℝ) ∧
        (N:ℝ) * (x i : ℝ) < (c.hi i : ℝ) + 1/4)
    (hclamp : clampCell c hN x ∉ cellRelbd c) :
    (∀ i, (cOf N x).lo i ≤ c.lo i) ∧ (∀ i, c.hi i ≤ (cOf N x).hi i) ∧
      (x ∉ cellSet c → cellDim c < cellDim (cOf N x)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hzx : ∀ i, (0:ℝ) ≤ (N:ℝ) * (x i : ℝ) :=
    fun i => mul_nonneg (le_of_lt hNpos) (x i).2.1
  -- the clamp is never at an endpoint of an interval coordinate
  have hnotR : ∀ i, c.lo i < c.hi i →
      clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.lo i : ℝ) / N ∧
      clampR N (c.lo i) (c.hi i) (x i : ℝ) ≠ (c.hi i : ℝ) / N := by
    intro i hlt
    constructor
    · intro hcon
      exact hclamp (by rw [mem_cellRelbd]; exact ⟨i, hlt, Or.inl (by rw [clampCell_val]; exact hcon)⟩)
    · intro hcon
      exact hclamp (by rw [mem_cellRelbd]; exact ⟨i, hlt, Or.inr (by rw [clampCell_val]; exact hcon)⟩)
  -- on an interval coordinate the point is strictly interior
  have hstrict : ∀ i, c.lo i < c.hi i →
      (c.lo i : ℝ) < (N:ℝ) * (x i : ℝ) ∧ (N:ℝ) * (x i : ℝ) < (c.hi i : ℝ) := by
    intro i hlt
    obtain ⟨h1, h2⟩ := hnotR i hlt
    obtain ⟨hlo, hhi⟩ := clampR_inl_interior hN hlt (c.hhi i) (x i).2 h1 h2
    rw [div_lt_iff₀ hNpos] at hlo
    rw [lt_div_iff₀ hNpos] at hhi
    exact ⟨by linarith, by linarith⟩
  have key1 : ∀ i, (cOf N x).lo i ≤ c.lo i := by
    intro i
    rw [cOf_lo]
    by_cases hlt : c.lo i < c.hi i
    · have hs := hstrict i hlt
      have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
      have hcast : (c.hi i : ℝ) = (c.lo i : ℝ) + 1 := by rw [hstep]; push_cast; ring
      have h1 : ⌊(N:ℝ) * (x i : ℝ)⌋₊ < c.lo i + 1 := by
        refine (Nat.floor_lt (hzx i)).mpr ?_
        push_cast
        linarith [hs.2, hcast]
      omega
    · have hpt : c.hi i = c.lo i := by have := c.hle i; omega
      have h1 : ⌊(N:ℝ) * (x i : ℝ)⌋₊ < c.lo i + 1 := by
        refine (Nat.floor_lt (hzx i)).mpr ?_
        push_cast
        have h := (hclose i).2
        rw [hpt] at h
        linarith
      omega
  have key2 : ∀ i, c.hi i ≤ (cOf N x).hi i := by
    intro i
    rw [cOf_hi]
    by_cases hlt : c.lo i < c.hi i
    · have hs := hstrict i hlt
      have hup : (N:ℝ) * (x i : ℝ) ≤ ((⌈(N:ℝ) * (x i : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((c.lo i : ℕ) : ℝ) < ((⌈(N:ℝ) * (x i : ℝ)⌉₊ : ℕ) : ℝ) := by linarith [hs.1, hup]
      have h1 : c.lo i < ⌈(N:ℝ) * (x i : ℝ)⌉₊ := by exact_mod_cast h3
      have hstep : c.hi i = c.lo i + 1 := by have := c.hstep i; omega
      omega
    · have hpt : c.hi i = c.lo i := by have := c.hle i; omega
      by_cases h0 : c.lo i = 0
      · omega
      · have hone : 1 ≤ c.lo i := Nat.one_le_iff_ne_zero.mpr h0
        have h1 : c.lo i - 1 < ⌈(N:ℝ) * (x i : ℝ)⌉₊ := by
          refine (Nat.lt_ceil).mpr ?_
          have h2 : (((c.lo i - 1 : ℕ)) : ℝ) = (c.lo i : ℝ) - 1 := by
            push_cast [Nat.cast_sub hone]; ring
          have h := (hclose i).1
          rw [h2]
          linarith
        omega
  refine ⟨key1, key2, fun hx => ?_⟩
  -- a coordinate of `x` outside `c` must be a point coordinate of `c`
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ∉ coordInterval c i := by
    by_contra hcon
    push_neg at hcon
    exact hx (mem_cellSet.mpr hcon)
  have hpt : c.lo i₀ = c.hi i₀ := by
    by_contra hne
    have hlt : c.lo i₀ < c.hi i₀ := lt_of_le_of_ne (c.hle i₀) hne
    have hs := hstrict i₀ hlt
    have hNpos' := hNpos
    have h1 : (c.lo i₀ : ℝ) / N < (x i₀ : ℝ) := by
      rw [div_lt_iff₀ hNpos']; linarith [hs.1]
    have h2 : (x i₀ : ℝ) < (c.hi i₀ : ℝ) / N := by
      rw [lt_div_iff₀ hNpos']; linarith [hs.2]
    exact hi₀ ⟨le_of_lt h1, le_of_lt h2⟩
  have hne : (N : ℝ) * (x i₀ : ℝ) ≠ (c.lo i₀ : ℝ) := by
    intro hcon
    apply hi₀
    have hx_eq : (x i₀ : ℝ) = (c.lo i₀ : ℝ) / N := by rw [← hcon]; field_simp
    refine (mem_coordInterval).mpr ⟨?_, ?_⟩ <;> (rw [hx_eq, hpt]) <;> rfl
  have hnonInt : ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ ≠ ⌈(N : ℝ) * (x i₀ : ℝ)⌉₊ := by
    intro hcon
    have hfl : ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) * (x i₀ : ℝ) := Nat.floor_le (hzx i₀)
    have hce : (N : ℝ) * (x i₀ : ℝ) ≤ ((⌈(N : ℝ) * (x i₀ : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hconv : ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) = ((⌈(N : ℝ) * (x i₀ : ℝ)⌉₊ : ℕ) : ℝ) := by
      rw [hcon]
    have heq : (N : ℝ) * (x i₀ : ℝ) = ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [hconv]
      exact le_antisymm hce (hconv ▸ hfl)
    have hcast : (c.hi i₀ : ℝ) = (c.lo i₀ : ℝ) := by rw [hpt]
    have hlt : ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) < (c.lo i₀ : ℝ) + 1 / 4 := by
      rw [← heq]
      have h := (hclose i₀).2
      linarith
    have hgt : (c.lo i₀ : ℝ) - 1 / 4 < ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [← heq]
      exact (hclose i₀).1
    have hh1 : ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ ≤ c.lo i₀ := by
      by_contra hc
      push_neg at hc
      have h2 : (((c.lo i₀ : ℕ) : ℝ)) + 1 ≤ ((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
        have hcast : (((c.lo i₀ : ℕ) : ℝ)) + 1 = (((c.lo i₀ + 1 : ℕ)) : ℝ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast hc
      linarith
    have hh2 : c.lo i₀ ≤ ⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ := by
      by_contra hc
      push_neg at hc
      have h2 : (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ)) + 1 ≤ (c.lo i₀ : ℝ) := by
        have hcast : (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ : ℕ) : ℝ)) + 1 =
            (((⌊(N : ℝ) * (x i₀ : ℝ)⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast hc
      linarith
    exact hne (by rw [heq, le_antisymm hh1 hh2])
  have hsub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊆
      (Finset.univ.filter (fun i : Fin j =>
        ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h1 := key1 i
    have h2 := key2 i
    rw [cOf_lo] at h1
    rw [cOf_hi] at h2
    omega
  have hmemB : i₀ ∈ (Finset.univ.filter (fun i : Fin j =>
      ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne (Nat.floor_le_ceil _) hnonInt
  have hnotmemA : i₀ ∉ (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hssub : (Finset.univ.filter (fun i : Fin j => c.lo i < c.hi i)) ⊂
      (Finset.univ.filter (fun i : Fin j =>
        ⌊(N : ℝ) * (x i : ℝ)⌋₊ < ⌈(N : ℝ) * (x i : ℝ)⌉₊)) :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨i₀, hmemB, hnotmemA⟩
  have hcard := Finset.card_lt_card hssub
  rw [cellDim, cellDim]
  exact hcard

end Work.ThomBordism.TwoSet
