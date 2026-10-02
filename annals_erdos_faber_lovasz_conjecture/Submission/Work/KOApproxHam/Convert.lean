import Submission.Work.KOApproxHam.Defs
import Submission.Work.Deep.GKO.KOInputs

/-!
# The two formulations of the approximate Hamilton decomposition

`Work.Deep.GKO.ApproxHamDecompStatement` states Osthus–Staden's Theorem 1.3 in the "regular
leftover" form: `G = G₁ ⊔ H₀` with `G₁` Hamilton-decomposable and `H₀` regular of degree
`≤ η r`.  The paper states it in the "cycle packing" form: `G` contains at least `(1-η)r`
edge-disjoint Hamilton cycles.  In an `r`-regular graph the two are equivalent, and this module
proves both directions:

* `approxHamDecompStatement_of_packing` — a packing of `t` edge-disjoint Hamilton cycles gives the
  split with `G₁ := ⋃ C i` and `H₀ := G \ G₁`, which is `(r - 2t)`-regular;
* `approxHamPackingStatement_of_decomp`, `approxHamPackingStatement_iff_decomp` — conversely a
  split gives the packing of the cycles of the Hamilton decomposition of `G₁`.

(Note the standard convention, from Mathlib's `SimpleGraph.IsHamiltonian`: the empty graph is
*not* Hamiltonian.  Consequently `n₀` in the packing statement is genuinely needed at least `1`;
the proof takes `max n₀ 1`.  This is invisible at the level of the target statement, whose
leftover formulation *is* satisfiable at `n = 0` with the zero-cycle decomposition of `⊥`.)

The bookkeeping is the one already available in `Work.Deep.GKO.KOAssembly`
(`isRegularOf_finsetSup`, `isRegularOf_sdiff`, `sup_sdiff_of_le`, `edgeSet_finsetSup`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KOApproxHam

open Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## A packing is a decomposition with a regular leftover -/

theorem approxHamDecompStatement_of_packing (h : ApproxHamPackingStatement) :
    ApproxHamDecompStatement := by
  intro α hα
  obtain ⟨τ, hτpos, hτ⟩ := h α hα
  refine ⟨τ, hτpos, ?_⟩
  intro ν η hν hη hντ
  obtain ⟨n₀, hn₀⟩ := hτ ν η hν hη hντ
  refine ⟨n₀, ?_⟩
  intro n hn G hG r hr hrn
  obtain ⟨t, hpack, hineq⟩ := hn₀ n hn G hG r hr hrn
  simp only [HamiltonCyclePacking] at hpack
  obtain ⟨C, hCle, hCcyc, hCdisj⟩ := hpack
  refine ⟨packingUnion C, G \ packingUnion C, r - 2 * t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact packingUnion_le hCle
  · exact sdiff_le
  · -- edge-disjointness of a subgraph and its complement
    rw [SimpleGraph.edgeSet_sdiff]
    exact disjoint_sdiff_self_right
  · exact sup_sdiff_of_le (packingUnion_le hCle)
  · -- the union of the packing has a Hamilton decomposition
    refine ⟨t, C, fun i => ?_, hCcyc, hCdisj, ?_⟩
    · exact Finset.le_sup (Finset.mem_univ i)
    · intro e he
      rw [edgeSet_packingUnion] at he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact ⟨i, hi⟩
  · exact isRegularOf_sdiff (packingUnion_le hCle) hr (isRegularOf_packingUnion hCcyc hCdisj)
  · -- the leftover degree is small
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    by_cases h2 : 2 * t ≤ r
    · have hcast : (((r - 2 * t : ℕ)) : ℝ) = (r : ℝ) - ((2 * t : ℕ) : ℝ) :=
        Nat.cast_sub h2
      have h2t : ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
      rw [hcast, h2t]
      exact hineq
    · have hz : r - 2 * t = 0 := by omega
      rw [hz]
      push_cast
      nlinarith [mul_nonneg hη.le hr0]

/-! ## A decomposition gives a packing -/

theorem approxHamPackingStatement_of_decomp (h : ApproxHamDecompStatement) :
    ApproxHamPackingStatement := by
  intro α hα
  obtain ⟨τ, hτpos, hτ⟩ := h α hα
  refine ⟨τ, hτpos, ?_⟩
  intro ν η hν hη hντ
  obtain ⟨n₀, hn₀⟩ := hτ ν η hν hη hντ
  refine ⟨max n₀ 1, ?_⟩
  intro n hn G hG r hr hrn
  have hnpos : 0 < n := by omega
  obtain ⟨G₁, H₀, d, hG₁le, hH₀le, hdisj, hsup, hdec, hH₀reg, hH₀d⟩ :=
    hn₀ n (le_trans (le_max_left _ _) hn) G hG r hr hrn
  obtain ⟨k, C, hle, hcyc, hdisjC, hcov⟩ := hdec
  have hsplit : IsDecompSplit G G₁ H₀ := ⟨hG₁le, hH₀le, hdisj, hsup⟩
  have hreg₁ : IsRegularOf G₁ (2 * k) := by
    have h := isRegularOf_packingUnion (C := C) hcyc hdisjC
    have hsup_eq : packingUnion C = G₁ := by
      rw [packingUnion_def]
      ext u v
      rw [SimpleGraph.iSup_adj]
      constructor
      · rintro ⟨i, hadj⟩
        exact SimpleGraph.le_iff_adj.mp (hle i) u v hadj
      · intro huv
        obtain ⟨i, hi⟩ := hcov (s(u, v)) ((SimpleGraph.mem_edgeSet G₁).mpr huv)
        exact ⟨i, (SimpleGraph.mem_edgeSet (C i)).mp hi⟩
    rw [hsup_eq] at h
    exact h
  refine ⟨k, ?_, ?_⟩
  · exact ⟨C, fun i => le_trans (hle i) hG₁le, hcyc, hdisjC⟩
  · -- the leftover degree, read off from `H₀`
    have hreg_sdiff : IsRegularOf (G \ G₁) (r - 2 * k) := isRegularOf_sdiff hG₁le hr hreg₁
    have hH₀reg' : IsRegularOf H₀ (r - 2 * k) := hsplit.sdiff_eq ▸ hreg_sdiff
    have hd_eq : d = r - 2 * k := by
      have h1 := hH₀reg (⟨0, hnpos⟩ : Fin n)
      have h2 := hH₀reg' (⟨0, hnpos⟩ : Fin n)
      rw [h1] at h2
      exact h2
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    by_cases h2 : 2 * k ≤ r
    · have hcast : ((r - 2 * k : ℕ) : ℝ) = (r : ℝ) - ((2 * k : ℕ) : ℝ) := Nat.cast_sub h2
      have h2k : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      rw [hd_eq, hcast, h2k] at hH₀d
      exact hH₀d
    · have h2' : (r : ℝ) < 2 * (k : ℝ) := by
        have hrk : r < 2 * k := by omega
        exact_mod_cast hrk
      nlinarith [mul_nonneg hη.le hr0]

/-- **The two formulations of Theorem 1.3 are equivalent** (in the undirected setting used by
this development). -/
theorem approxHamPackingStatement_iff_decomp :
    ApproxHamPackingStatement ↔ ApproxHamDecompStatement :=
  ⟨approxHamDecompStatement_of_packing, approxHamPackingStatement_of_decomp⟩

end

end Work.KOApproxHam
