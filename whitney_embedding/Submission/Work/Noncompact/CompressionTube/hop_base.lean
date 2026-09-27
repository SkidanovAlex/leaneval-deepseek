import Mathlib
import Submission.Work.Noncompact.CompressionTube.chartBall_union_around
import Submission.Work.Noncompact.CompressionTube.SpineDefs

/-!
# The pre-fixed family `Base` of the hop architecture

This file builds the *base* family `Base : ℕ → Set M` of the hop architecture (see
`hop_L.lean` for the level sets `L` and `NOTES_S32_hop_v3.md` for the design), from the given
compact exhaustion `K`:

  `Base (2i) := S1 i`, `Base (2i+1) := S2 i`,

where, writing `hB` for the local finiteness of the base points `B`,

* `S1 i` is the compact chart-ball union with `K i ⊆ interior (S1 i)`, `S1 i ⊆ interior (K (i+1))`
  and `S1 i ∩ (B ∖ K i) ∩ interior (K (i+1)) = ∅` (the engulfing step `chartBall_union_around`
  applied with the *relative* avoidance set `B ∖ K i`),
* `S2 i` is the same with `S1 i` in the role of `A`.

The relative avoidance set matters: the engulfing lemma can only avoid the points of `B` that are
*not* in the set being engulfed (a point of `B ∩ K i` is forced into any engulfing of `K i`).

Consequences (all proved below):

* `Monotone Base`;
* the `K`-interleaving data
  `K i ⊆ Base (2i)`, `Base (2i+1) ⊆ K (i+1)`, `K (i+1) ⊆ Base (2i+2)`;
* every `Base m` is compact (hence closed);
* **the base points miss their own level**: with `kLevel K hK b` the index with `b ∉ K (lv b)` and
  `b ∈ K (lv b + 1)`, one has `(b : M) ∉ Base (2 * kLevel K hK b)`.

The last point is what makes `SpineData`'s `lev_notMem` for the level sets `L`
(`b ∉ L (2 · lv b)`) reachable: since `Base (2i) ⊆ interior (K (i+1))`, a base point
`b ∈ B` lies in `Base (2 · lv b)` only if `b ∈ interior (K (lv b + 1))` and `b ∉ K (lv b)`, and then
the relative avoidance of `S1 (lv b)` excludes it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **The `K`-level of a point**: `kLevel K hK x` is the index with `x ∉ K (kLevel …)` and
`x ∈ K (kLevel … + 1)`. -/
noncomputable def kLevel (K : ℕ → Set M) (hK : ∀ x : M, ∃ i, x ∈ K i) (x : M) : ℕ := by
  classical
  exact Nat.find (hK x) - 1

theorem kLevel_notMem {K : ℕ → Set M} (hK : ∀ x : M, ∃ i, x ∈ K i) (hK0 : K 0 = ∅) {x : M} :
    x ∉ K (kLevel K hK x) := by
  classical
  have hmin : ∀ i < Nat.find (hK x), x ∉ K i := fun i hi => Nat.find_min (hK x) hi
  have hNpos : 0 < Nat.find (hK x) := by
    rcases Nat.eq_zero_or_pos (Nat.find (hK x)) with h | h
    · exfalso
      have : x ∈ K 0 := h ▸ Nat.find_spec (hK x)
      rw [hK0] at this
      exact this
    · exact h
  have hlt : Nat.find (hK x) - 1 < Nat.find (hK x) := by omega
  rw [kLevel]
  exact hmin _ hlt

theorem kLevel_mem {K : ℕ → Set M} (hK : ∀ x : M, ∃ i, x ∈ K i) (hK0 : K 0 = ∅) {x : M} :
    x ∈ K (kLevel K hK x + 1) := by
  classical
  have hspec : x ∈ K (Nat.find (hK x)) := Nat.find_spec (hK x)
  have hNpos : 0 < Nat.find (hK x) := by
    rcases Nat.eq_zero_or_pos (Nat.find (hK x)) with h | h
    · exfalso
      have : x ∈ K 0 := h ▸ hspec
      rw [hK0] at this
      exact this
    · exact h
  rw [kLevel, Nat.sub_add_cancel hNpos]
  exact hspec

/-- The existence of `∃ i, x ∈ K i` from the covering hypothesis. -/
theorem exists_mem_of_iUnion_eq_univ {K : ℕ → Set M} (hKuniv : (⋃ i, K i) = (univ : Set M))
    (x : M) : ∃ i, x ∈ K i := by
  have : x ∈ (⋃ i, K i) := by rw [hKuniv]; trivial
  simpa only [mem_iUnion] using this

/-- **The two engulfing families of the hop architecture.** -/
theorem exists_base_family {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : ℕ → Set M) (hKc : ∀ i, IsCompact (K i)) (hKsub : ∀ i, K i ⊆ interior (K (i+1)))
    (B : Set M) (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite) :
    ∃ S1 S2 : ℕ → Set M,
      (∀ i, IsCompact (S1 i)) ∧ (∀ i, IsCompact (S2 i)) ∧
      (∀ i, K i ⊆ interior (S1 i)) ∧ (∀ i, S1 i ⊆ interior (K (i + 1))) ∧
      (∀ i, S1 i ⊆ interior (S2 i)) ∧ (∀ i, S2 i ⊆ interior (K (i + 1))) ∧
      (∀ (i : ℕ) (b : M), b ∈ B → b ∉ K i → b ∈ interior (K (i + 1)) → b ∉ S1 i) ∧
      (∀ (i : ℕ) (b : M), b ∈ B → b ∉ K i → b ∈ interior (K (i + 1)) → b ∉ S2 i) := by
  have key : ∀ i, ∃ S : Set M, IsCompact S ∧ K i ⊆ interior S ∧ S ⊆ interior (K (i + 1)) ∧
      (∀ (b : M), b ∈ B → b ∉ K i → b ∈ interior (K (i + 1)) → b ∉ S) := by
    intro i
    obtain ⟨S, hSc, hKS, hSN, _, hSB⟩ :=
      chartBall_union_around (n := n) (A := K i) (N := K (i + 1)) (B := B \ K i)
        (hKc i) (hKsub i)
        (fun K' hK' => (hB K' hK').subset (fun x hx => ⟨hx.1.1, hx.2⟩))
        (fun b hb _ => hb.2)
    exact ⟨S, hSc, hKS, hSN, fun b hbB hbK hbN => hSB b ⟨hbB, hbK⟩ hbN⟩
  choose S1 hS1c hKS1 hS1N hS1B using key
  have key2 : ∀ i, ∃ S : Set M, IsCompact S ∧ S1 i ⊆ interior S ∧ S ⊆ interior (K (i + 1)) ∧
      (∀ (b : M), b ∈ B → b ∉ K i → b ∈ interior (K (i + 1)) → b ∉ S) := by
    intro i
    obtain ⟨S, hSc, hSS, hSN, _, hSB⟩ :=
      chartBall_union_around (n := n) (A := S1 i) (N := K (i + 1)) (B := B \ K i)
        (hS1c i) (hS1N i)
        (fun K' hK' => (hB K' hK').subset (fun x hx => ⟨hx.1.1, hx.2⟩))
        (fun b hb hbN => hS1B i b hb.1 hb.2 hbN)
    exact ⟨S, hSc, hSS, hSN, fun b hbB hbK hbN => hSB b ⟨hbB, hbK⟩ hbN⟩
  choose S2 hS2c hS1S2 hS2N hS2B using key2
  exact ⟨S1, S2, hS1c, hS2c, hKS1, hS1N, hS1S2, hS2N,
    fun i b hbB hbK hbN => hS1B i b hbB hbK hbN,
    fun i b hbB hbK hbN => hS2B i b hbB hbK hbN⟩

/-! ## The base family and its properties -/

/-- **The base family** of the hop architecture: the even levels are the tight engulfings `S1 i` of
`K i`, the odd ones the slightly larger engulfings `S2 i`. -/
noncomputable def HopBase {M : Type*} (S1 S2 : ℕ → Set M) : ℕ → Set M :=
  fun m => if m % 2 = 0 then S1 (m / 2) else S2 (m / 2)

theorem hopBase_even (S1 S2 : ℕ → Set M) (i : ℕ) : HopBase S1 S2 (2 * i) = S1 i := by
  have h1 : (2 * i) % 2 = 0 := by omega
  have h2 : (2 * i) / 2 = i := by omega
  rw [HopBase, h1, h2, if_pos rfl]

theorem hopBase_odd (S1 S2 : ℕ → Set M) (i : ℕ) : HopBase S1 S2 (2 * i + 1) = S2 i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  rw [HopBase, h2, h1, if_neg (by norm_num)]

theorem isCompact_hopBase {S1 S2 : ℕ → Set M} (h1 : ∀ i, IsCompact (S1 i))
    (h2 : ∀ i, IsCompact (S2 i)) : ∀ m, IsCompact (HopBase S1 S2 m) := by
  intro m
  rw [HopBase]
  split
  · exact h1 _
  · exact h2 _

theorem monotone_hopBase {S1 S2 : ℕ → Set M} (h12 : ∀ i, S1 i ⊆ S2 i)
    (h21 : ∀ i, S2 i ⊆ S1 (i + 1)) : Monotone (HopBase S1 S2) := by
  have hsucc : ∀ m, HopBase S1 S2 m ⊆ HopBase S1 S2 (m + 1) := by
    intro m
    rcases Nat.even_or_odd m with ⟨i, hi⟩ | ⟨i, hi⟩
    · have hm : m = 2 * i := by omega
      rw [hm, hopBase_even, hopBase_odd]
      exact h12 i
    · have hm : m = 2 * i + 1 := by omega
      rw [hm, hopBase_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, hopBase_even]
      exact h21 i
  exact fun a b hab => monotone_nat_of_le_succ hsucc hab

/-- The three `K`-interleaving properties of the base family. -/
theorem hopBase_chain {K : ℕ → Set M} {S1 S2 : ℕ → Set M} (hKS1 : ∀ i, K i ⊆ S1 i)
    (hS2K : ∀ i, S2 i ⊆ K (i + 1)) :
    (∀ i, K i ⊆ HopBase S1 S2 (2 * i)) ∧ (∀ i, HopBase S1 S2 (2 * i + 1) ⊆ K (i + 1)) ∧
      (∀ i, K (i + 1) ⊆ HopBase S1 S2 (2 * (i + 1))) :=
  ⟨fun i => (hKS1 i).trans (le_of_eq (hopBase_even S1 S2 i).symm),
    fun i => (le_of_eq (hopBase_odd S1 S2 i)).trans (hS2K i),
    fun i => (hKS1 (i + 1)).trans (le_of_eq (hopBase_even S1 S2 (i + 1)).symm)⟩

/-- **The base points miss their own level.** -/
theorem notMem_hopBase_kLevel {M : Type*} [TopologicalSpace M] {K : ℕ → Set M}
    {hK : ∀ x : M, ∃ i, x ∈ K i} {hK0 : K 0 = ∅} {S1 S2 : ℕ → Set M} {B : Set M}
    (hS1N : ∀ i, S1 i ⊆ interior (K (i + 1)))
    (hS1B : ∀ (i : ℕ) (b : M), b ∈ B → b ∉ K i → b ∈ interior (K (i + 1)) → b ∉ S1 i)
    {b : B} : (b : M) ∉ HopBase S1 S2 (2 * kLevel K hK b) := by
  classical
  rw [hopBase_even]
  by_cases hb : (b : M) ∈ interior (K (kLevel K hK b + 1))
  · exact hS1B (kLevel K hK b) b b.2 (kLevel_notMem hK hK0) hb
  · intro hmem
    exact hb (hS1N (kLevel K hK b) hmem)

/-- **The base family of the hop architecture.**  From the compact exhaustion `K` and the locally
finite set `B` of base points one gets `Base : ℕ → Set M` with all the properties the level sets `L`
of `hop_L.lean` require of their pre-fixed part: monotonicity, compactness, the `K`-interleaving and
`b ∉ Base (2 · lv b)` for every base point. -/
theorem exists_base {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : ℕ → Set M) (hKc : ∀ i, IsCompact (K i)) (hK0 : K 0 = ∅)
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hKuniv : (⋃ i, K i) = (univ : Set M))
    (B : Set M) (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite) :
    ∃ Base : ℕ → Set M, Monotone Base ∧ (∀ m, IsCompact (Base m)) ∧
      (∀ i, K i ⊆ Base (2 * i)) ∧ (∀ i, Base (2 * i + 1) ⊆ K (i + 1)) ∧
      (∀ i, K (i + 1) ⊆ Base (2 * i + 2)) ∧
      (∀ b : B, (b : M) ∉ Base (2 * kLevel K (exists_mem_of_iUnion_eq_univ hKuniv) b)) := by
  obtain ⟨S1, S2, hS1c, hS2c, hKS1, hS1N, hS1S2, hS2N, hS1B, hS2B⟩ :=
    exists_base_family (n := n) K hKc hKsub B hB
  have h12 : ∀ i, S1 i ⊆ S2 i := fun i => (hS1S2 i).trans interior_subset
  have h21 : ∀ i, S2 i ⊆ S1 (i + 1) := fun i => by
    have h1 : interior (K (i + 1)) ⊆ interior (S1 (i + 1)) := by
      rw [← interior_interior (s := S1 (i + 1))]
      exact interior_mono (hKS1 (i + 1))
    exact (hS2N i).trans (h1.trans interior_subset)
  have hKS1' : ∀ i, K i ⊆ S1 i := fun i => (hKS1 i).trans interior_subset
  have hS2N' : ∀ i, S2 i ⊆ K (i + 1) := fun i => (hS2N i).trans interior_subset
  obtain ⟨hch1, hch2, hch3⟩ := hopBase_chain (K := K) (S1 := S1) (S2 := S2) hKS1' hS2N'
  refine ⟨HopBase S1 S2, monotone_hopBase h12 h21, isCompact_hopBase hS1c hS2c,
    hch1, hch2, fun i => ?_, fun b => ?_⟩
  · have := hch3 i
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  · exact notMem_hopBase_kLevel (hK := exists_mem_of_iUnion_eq_univ hKuniv) (hK0 := hK0)
      (S1 := S1) (S2 := S2) (B := B) hS1N hS1B

end Work.Noncompact.CompressionTube
