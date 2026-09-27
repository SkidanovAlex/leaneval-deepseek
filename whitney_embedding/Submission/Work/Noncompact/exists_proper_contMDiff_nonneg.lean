import Mathlib

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Set Function

/-- A σ-compact smooth manifold admits a nonnegative proper smooth function.  Same proof as
`Work.Noncompact.exists_proper_contMDiff`: the function built there is the locally finite sum
`∑ᶠ n, ρ n x • (n : ℝ)` of nonnegative terms, hence nonnegative (`finsum_nonneg`). -/
theorem exists_proper_contMDiff_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ IsProperMap f ∧ ∀ x, 0 ≤ f x := by
  -- The model space `H`, and hence `M`, is locally compact.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- A compact exhaustion whose first term is empty.
  let L : CompactExhaustion M := (CompactExhaustion.choice M).shiftr
  have hL0 : L 0 = ∅ := rfl
  -- The locally finite open cover of `M` consisting of the "annuli" `U n`.
  let U : ℕ → Set M := fun n => interior (L (n + 1)) \ L (n - 1)
  have hUopen : ∀ n, IsOpen (U n) := fun n =>
    isOpen_interior.sdiff (L.isCompact (n - 1)).isClosed
  have hcover : (univ : Set M) ⊆ ⋃ n, U n := by
    intro x _
    have hpos : 0 < L.find x := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      have : x ∈ L 0 := by rw [L.mem_iff_find_le, h]
      rw [hL0] at this
      exact this
    refine mem_iUnion.mpr ⟨L.find x, L.subset_interior_succ _ (L.mem_find x), ?_⟩
    intro hx
    rw [L.mem_iff_find_le] at hx
    exact absurd hx (not_le.mpr (Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hpos)))
  -- A smooth partition of unity subordinate to `U`.
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUopen hcover
  -- The candidate proper function.
  let g : M → ℝ := fun x => ∑ᶠ n, ρ n x • (n : ℝ)
  have hgsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := by
    have h := ρ.contMDiff_finsum_smul (n := ⊤)
      (g := fun (n : ℕ) (_ : M) => (n : ℝ)) (fun i _ _ => contMDiffAt_const)
    simpa only [g] using h
  -- Nonnegativity: every term of the locally finite sum is nonnegative.
  have hgnonneg : ∀ x, 0 ≤ g x := by
    intro x
    change 0 ≤ ∑ᶠ n, ρ n x • (n : ℝ)
    exact finsum_nonneg fun n => smul_nonneg (ρ.nonneg n x) (Nat.cast_nonneg n)
  refine ⟨g, hgsmooth, ?_, hgnonneg⟩
  have hcont : Continuous g := hgsmooth.continuous
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, fun K hK => ?_⟩
  obtain ⟨a, ha⟩ := hK.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt a
  -- Main estimate: outside `L N`, the function `g` is at least `N`.
  have key : ∀ x : M, x ∉ L N → (N : ℝ) ≤ g x := by
    intro x hxL
    change (N : ℝ) ≤ ∑ᶠ n, ρ n x • (n : ℝ)
    rw [← ρ.sum_finsupport_smul_eq_finsum x (fun (n : ℕ) (_ : M) => (n : ℝ))]
    simp only [smul_eq_mul]
    have hmem : ∀ i ∈ ρ.finsupport x, N ≤ i := by
      intro i hi
      by_contra h
      have hiN : i < N := Nat.lt_of_not_le h
      have hρi : ρ i x ≠ 0 := by
        rw [ρ.mem_finsupport x] at hi
        exact Function.mem_support.mp hi
      have hx_supp : x ∈ Function.support (ρ i) := Function.mem_support.mpr hρi
      have hx_tsupp : x ∈ tsupport (ρ i) := subset_closure hx_supp
      have hxU : x ∈ interior (L (i + 1)) \ L (i - 1) := hρ i hx_tsupp
      exact hxL (L.subset (by omega) (interior_subset hxU.1))
    have hsum : ∑ i ∈ ρ.finsupport x, ρ i x = 1 := ρ.sum_finsupport x (mem_univ x)
    calc (N : ℝ) = (N : ℝ) * 1 := (mul_one _).symm
      _ = (N : ℝ) * ∑ i ∈ ρ.finsupport x, ρ i x := by rw [hsum]
      _ = ∑ i ∈ ρ.finsupport x, (N : ℝ) * ρ i x := by rw [Finset.mul_sum]
      _ = ∑ i ∈ ρ.finsupport x, ρ i x * (N : ℝ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
      _ ≤ ∑ i ∈ ρ.finsupport x, ρ i x * (i : ℝ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmem i hi) (ρ.nonneg i x)
  refine (L.isCompact N).of_isClosed_subset (hK.isClosed.preimage hcont) ?_
  intro x hx
  have hxK : g x ∈ K := hx
  by_contra hxL
  have h1 : (N : ℝ) ≤ g x := key x hxL
  have h2 : g x ≤ a := ha hxK
  linarith

end Work.Noncompact
