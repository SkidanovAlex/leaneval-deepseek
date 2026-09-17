import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_simple_root_weightSpace_finrank_compat

namespace Commons.Algebra.Lie.SerreConstruction

noncomputable section

open scoped BigOperators

/-- **Any weight space of `e₈` whose weight is neither `0` nor a nonnegative integral combination
of the simple roots lies in the `F`-side `n⁻ = Msub`.**

The Serre-constructed `e₈` splits as `L8 = Hsub + Psub + Msub` (`span_H_P_M_top`); every element
of `Hsub` is a weight vector of weight `0`, every element of `Psub` is a finite sum of weight
vectors whose weights are nonnegative integral combinations `∑ᵢ mᵢαᵢ` of the simple roots
(`Psub_le_iSup_Pm`), and every element of `Msub` is a finite sum of weight vectors of weights
`-∑ᵢ mᵢαᵢ` (`Msub_le_iSup_Mm`).

So write `x ∈ W ν` as `x = a + b + z` with `a ∈ Hsub`, `b ∈ Psub`, `z ∈ Msub` and expand `b` and
`z` into weight components.  By hypothesis none of the weights occurring in the `H`- and
`P`-parts equals `ν`, so the "killer" extraction `killer_extract` exhibits `x` as the sum of the
weight components of weight exactly `ν`.  Those can only come from `n⁻`-summands, each of which
lies in `Msub`; hence `x ∈ Msub`. -/
theorem W_le_Msub_of_ne_zero_of_ne_NWtSum {ν : Fin 8 → ℂ} (hν0 : ν ≠ 0)
    (hpos : ∀ m : Fin 8 → ℕ, NWtSum m ≠ ν) :
    (W ν : Submodule ℂ L8) ≤ (Msub : Submodule ℂ L8) := by
  classical
  intro x hx
  -- triangular decomposition of `x`
  have hxmem : x ∈ (Hsub : Submodule ℂ L8) ⊔ (Psub : Submodule ℂ L8) ⊔
      (Msub : Submodule ℂ L8) := by rw [span_H_P_M_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
  have hxabc : x = a + b + z := by rw [← hyz, ← hab]
  -- weight decompositions of the `n⁺`- and `n⁻`-parts
  obtain ⟨sb, hsb⟩ := Submodule.mem_iSup_iff_exists_finset.mp (Psub_le_iSup_Pm hb)
  obtain ⟨fb, hfb, hbsum⟩ := mem_iSup_finset_iff.mp hsb
  obtain ⟨sc, hsc⟩ := Submodule.mem_iSup_iff_exists_finset.mp (Msub_le_iSup_Mm hz)
  obtain ⟨fc, hfc, hcsum⟩ := mem_iSup_finset_iff.mp hsc
  have hb' : b = ∑ m ∈ sb, fb m := hbsum
  have hc' : z = ∑ m ∈ sc, fc m := hcsum
  -- index the three parts (`H`, `n⁺`, `n⁻`) by a single type
  set wt : Option ((Fin 8 → ℕ) ⊕ (Fin 8 → ℕ)) → (Fin 8 → ℂ) :=
    (fun i => match i with
      | none => 0
      | some (Sum.inl m) => NWtSum m
      | some (Sum.inr m) => -(NWtSum m)) with hwt
  set yv : Option ((Fin 8 → ℕ) ⊕ (Fin 8 → ℕ)) → L8 :=
    (fun i => match i with
      | none => a
      | some (Sum.inl m) => fb m
      | some (Sum.inr m) => fc m) with hyv
  set s : Finset (Option ((Fin 8 → ℕ) ⊕ (Fin 8 → ℕ))) :=
    insert none ((sb.image (fun m => some (Sum.inl m))) ∪
      (sc.image (fun m => some (Sum.inr m)))) with hs
  -- the indexed sum is `a + b + z = x`
  have hsum : (∑ i ∈ s, yv i) = x := by
    rw [hs, Finset.sum_insert (by simp),
      Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hiA
        obtain ⟨m', -, hm'⟩ := Finset.mem_image.mp hiB
        simp at hm'),
      Finset.sum_image (by intro m _ m' _ h; simpa using h),
      Finset.sum_image (by intro m _ m' _ h; simpa using h)]
    simp only [hyv, hb', hc', hxabc]
    abel
  -- each indexed term is a weight vector
  have hy_mem : ∀ i ∈ s, yv i ∈ W (wt i) := by
    intro i hi
    rw [hs] at hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp only [hyv, hwt]
      exact Hsub_le_W_zero ha
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
      simp only [hyv, hwt]
      exact (hfb m hm).2
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
      simp only [hyv, hwt]
      exact (hfc m hm).2
  -- extract the component of weight `ν`
  have hext := killer_extract (μ := ν) s wt yv hy_mem (by rw [hsum]; exact hx)
  rw [hsum] at hext
  rw [hext]
  -- that component lies in `Msub`
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Finset.mem_filter] at hi
  obtain ⟨his, hwtν⟩ := hi
  rw [hs] at his
  rcases Finset.mem_insert.mp his with rfl | his
  · simp only [hwt] at hwtν
    exact absurd hwtν.symm hν0
  rcases Finset.mem_union.mp his with his | his
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp his
    simp only [hwt] at hwtν
    exact absurd hwtν (hpos m)
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp his
    simp only [hyv]
    exact (hfc m hm).1

/-- **A weight space of `e₈` whose weight is a nonzero negative nonnegative combination of simple
roots lies in the `F`-side `n⁻ = Msub`.**  Immediate from
`W_le_Msub_of_ne_zero_of_ne_NWtSum`, since `∑ᵢ mᵢαᵢ = -(∑ᵢ nᵢαᵢ)` with `m, n ≥ 0` forces
`m + n = 0`, so `m = n = 0` whenever `n ≠ 0`. -/
theorem e8_W_le_Msub {n : Fin 8 → ℕ} (hn : n ≠ 0) :
    (Commons.Algebra.Lie.SerreConstruction.W (-(Commons.Algebra.Lie.SerreConstruction.NWtSum n)) :
      Submodule ℂ Commons.Algebra.Lie.SerreConstruction.L8) ≤
      (Commons.Algebra.Lie.SerreConstruction.Msub : Submodule ℂ Commons.Algebra.Lie.SerreConstruction.L8) := by
  refine W_le_Msub_of_ne_zero_of_ne_NWtSum ?_ ?_
  · -- the weight `-(∑ᵢ nᵢαᵢ)` is nonzero
    intro h
    exact hn (NWtSum_eq_zero (neg_eq_zero.mp h))
  · -- the weight `-(∑ᵢ nᵢαᵢ)` is not a nonnegative weight
    intro m hm
    have h2 : NWtSum (m + n) = 0 := by
      rw [NWtSum_add, hm]; simp
    have h3 : m + n = 0 := NWtSum_eq_zero h2
    refine hn ?_
    funext i
    have hh := congrFun h3 i
    simp only [Pi.add_apply, Pi.zero_apply] at hh
    exact Nat.eq_zero_of_add_eq_zero_left hh

end

end Commons.Algebra.Lie.SerreConstruction
