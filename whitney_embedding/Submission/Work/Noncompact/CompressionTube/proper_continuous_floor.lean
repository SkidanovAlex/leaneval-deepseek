import Mathlib

/-!
# A continuous proper function bounded below by `1`

On a charted space over `EuclideanSpace ℝ (Fin n)` that is Hausdorff and second countable there is
a continuous proper real function taking values `≥ 1`.  This is the "floor" used in the construction
of `Work.Noncompact.CompressionTube.proper_no_localMax`.
-/

namespace Work.Noncompact.CompressionTube

open Topology Set Filter

theorem proper_continuous_floor {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ F : M → ℝ, Continuous F ∧ IsProperMap F ∧ (∀ x, 1 ≤ F x) := by
  haveI : LocallyCompactSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : NormalSpace M := inferInstance
  -- A compact exhaustion.
  let K : CompactExhaustion M := (CompactExhaustion.choice M).shiftr
  have hmono : ∀ {a b : ℕ}, a ≤ b → K a ⊆ K b := fun {a b} h => K.subset h
  -- Urysohn functions `φ m`, equal to `1` on `K m` and vanishing off `interior (K (m+1))`.
  have hφ : ∀ m : ℕ, ∃ g : C(M, ℝ),
      EqOn g 0 ((interior (K (m + 1)))ᶜ) ∧ EqOn g 1 (K m) ∧ ∀ x, g x ∈ Icc 0 1 := by
    intro m
    refine exists_continuous_zero_one_of_isClosed
      (isClosed_compl_iff.mpr isOpen_interior) (K.isCompact m).isClosed ?_
    exact Set.disjoint_compl_left_iff_subset.mpr (K.subset_interior_succ m)
  choose φ hφzero hφone hφI using hφ
  have hterm_zero : ∀ (m : ℕ) (x : M), x ∉ K (m + 1) → φ m x = 0 := by
    intro m x hx
    refine hφzero m ?_
    intro hmem
    exact hx (interior_subset hmem)
  have hterm_one : ∀ (m : ℕ) (x : M), x ∈ K m → φ m x = 1 := fun m x hx => hφone m hx
  -- the candidate function
  let F : M → ℝ := fun x => 1 + ∑' m, ((1 : ℝ) - φ m x)
  -- the sum is finitely supported at every point
  have hsum_zero : ∀ (x : M) (m : ℕ), K.find x + 1 ≤ m → ((1 : ℝ) - φ m x) = 0 := by
    intro x m hm
    have hle : K.find x ≤ m := by omega
    have : φ m x = 1 := hterm_one m x (K.subset hle (K.mem_find x))
    simp [this]
  have htsum_eq : ∀ (x : M) (N : ℕ), K.find x ≤ N →
      (∑' m, ((1 : ℝ) - φ m x)) = ∑ m ∈ Finset.range (N + 1), ((1 : ℝ) - φ m x) := by
    intro x N hN
    refine tsum_eq_sum (s := Finset.range (N + 1)) fun m hm => ?_
    have hm' : N + 1 ≤ m := by simpa [Finset.mem_range, not_lt] using hm
    exact hsum_zero x m (le_trans (by omega) hm')
  -- continuity
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    have hxN : x ∈ K (K.find x) := K.mem_find x
    have hU : interior (K (K.find x + 1)) ∈ 𝓝 x :=
      isOpen_interior.mem_nhds (K.subset_interior_succ _ hxN)
    have hcont_fin : Continuous fun y : M =>
        1 + ∑ m ∈ Finset.range (K.find x + 2), ((1 : ℝ) - φ m y) :=
      continuous_const.add (continuous_finset_sum _ fun m _ =>
        continuous_const.sub (map_continuous (φ m)))
    refine hcont_fin.continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    have hyN : y ∈ K (K.find x + 1) := interior_subset hy
    have hyb : K.find y ≤ K.find x + 1 := K.mem_iff_find_le.mp hyN
    simp only [F]
    rw [htsum_eq y (K.find x + 1) hyb]
  -- the lower bound
  have hbound : ∀ x : M, 1 ≤ F x := by
    intro x
    have hnonneg : 0 ≤ ∑' m, ((1 : ℝ) - φ m x) := by
      refine tsum_nonneg fun m => ?_
      have := hφI m x
      simp only [mem_Icc] at this
      linarith [this.2]
    simp only [F]
    linarith
  -- properness
  have hproper : IsProperMap F := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hcont, fun C hC => ?_⟩
    obtain ⟨a, ha⟩ := hC.bddAbove
    obtain ⟨N, hN⟩ := exists_nat_gt a
    have key : ∀ x : M, x ∉ K (N + 1) → (N : ℝ) + 2 ≤ F x := by
      intro x hxK
      have hpart : (∑ m ∈ Finset.range (N + 1), ((1 : ℝ) - φ m x)) = ((N : ℝ) + 1) := by
        have hone : ∀ m ∈ Finset.range (N + 1), ((1 : ℝ) - φ m x) = 1 := by
          intro m hm
          have hm' : m ≤ N := by have := Finset.mem_range.mp hm; omega
          have hzero : φ m x = 0 := by
            refine hterm_zero m x ?_
            intro hmem
            have hle : m + 1 ≤ N + 1 := by omega
            exact hxK (K.subset hle hmem)
          simp [hzero]
        rw [Finset.sum_congr rfl hone]
        simp
      have hsub : Finset.range (N + 1) ⊆ Finset.range (max (N + 1) (K.find x) + 1) := by
        intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      have hle : (∑ m ∈ Finset.range (N + 1), ((1 : ℝ) - φ m x)) ≤
          ∑ m ∈ Finset.range (max (N + 1) (K.find x) + 1), ((1 : ℝ) - φ m x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by
          have := hφI m x
          simp only [mem_Icc] at this
          linarith [this.2]
      have hts : (∑' m, ((1 : ℝ) - φ m x)) =
          ∑ m ∈ Finset.range (max (N + 1) (K.find x) + 1), ((1 : ℝ) - φ m x) :=
        htsum_eq x (max (N + 1) (K.find x)) (le_max_right _ _)
      simp only [F]
      rw [hts]
      linarith
    refine (K.isCompact (N + 1)).of_isClosed_subset (hC.isClosed.preimage hcont) ?_
    intro x hx
    by_contra hxK
    have h1 : (N : ℝ) + 2 ≤ F x := key x hxK
    have h2 : F x ≤ a := ha hx
    have h3 : a < (N : ℝ) := hN
    linarith
  exact ⟨F, hcont, hproper, hbound⟩

end Work.Noncompact.CompressionTube
