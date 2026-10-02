import Submission.EFL.LowerReg
import Submission.EFL.DeepInputs
import Submission.EFL.Pow2Edges

/-!
# Corollary 10.13 (`cor:optcol`) of the paper

The paper derives, from Glock–Kühn–Osthus (Theorem 10.8), a corollary on
optimal edge-colourings of dense pseudorandom graphs: if `G` is lower
`(p,ε)`-regular, `Δ(G) - δ(G) ≤ ηn`, and at least `Δ(G)` vertices have degree
less than `Δ(G)`, then `χ'(G) = Δ(G)`.

This module records Theorem 10.8 as the deep input `GKOStatement` and proves
Corollary 10.13 from it (both the even and the odd case of `n`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The maximum degree of a family of `2`-edges -/

/-- For a family of 2-edges, `Δ(𝓖)` is the maximum of the vertex degrees. -/
theorem hypergraphMaxDegree_eq_sup (𝓖 : Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) :
    hypergraphMaxDegree 𝓖 = (Finset.univ : Finset (Fin n)).sup (fun v => degAt 𝓖 v) := by
  unfold hypergraphMaxDegree
  exact Finset.sup_congr rfl (fun v _ => (ncard_nbrs_eq_hypergraphDegree h2 v).symm)

/-- Every degree is at most `Δ(𝓖)`. -/
theorem degAt_le_maxDegree (𝓖 : Hypergraph (Fin n)) (h2 : ∀ e ∈ 𝓖, edgeSize e = 2)
    (v : Fin n) : degAt 𝓖 v ≤ hypergraphMaxDegree 𝓖 := by
  rw [hypergraphMaxDegree_eq_sup 𝓖 h2]
  exact Finset.le_sup (Finset.mem_univ v)

/-- `edgeCount` is symmetric in the two vertex sets. -/
theorem edgeCount_comm (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T = edgeCount R T S := by
  classical
  rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
  refine Set.ncard_congr (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    exact ⟨hp.2.1, hp.1, by rw [Set.pair_comm]; exact hp.2.2⟩
  · intro p hp q hq hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.2 hpq.1
  · intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    exact ⟨(q.2, q.1), ⟨hq.2.1, hq.1, by rw [Set.pair_comm]; exact hq.2.2⟩, rfl⟩

/-- The number of edges between `S` and `T` is at most the sum of the degrees
over `S`. -/
theorem edgeCount_le_sum_degAt_left (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) :
    edgeCount R S T ≤ ∑ s ∈ S, degAt R s := by
  rw [edgeCount_comm R S T]
  exact edgeCount_le_sum_degAt R T S

/-! **The shape of this input (switched 2026-09-23, the CONE SWITCH).**

`GKOStatement` is now the *faithful* form of Theorem 10.8: for every `p ∈ (0,1)` there are
thresholds `ν₀(p), ε₀(p) > 0` such that the conclusion holds whenever `ν ≤ ν₀(p)` and
`ε ≤ ε₀(p)`.  This is exactly `Work.Deep.GKO.GKOStatementFixed`, the target of the `Deep/GKO`
subproject, and it is what the paper's Corollary 10.13 needs, since its thresholds depend on
`p`.

The earlier *linear* hierarchy `10^10 * (ν + ε) ≤ p` was stronger than what the Kühn–Osthus
proof yields, and it pinned `p` (hence the density) *before* the regularity parameters `ρ, ε` —
an unsolvable fixed-point condition once §12 has to read the thresholds off the input.  §12 is
now parametric in `(ρ, ε)`: `ρ` is chosen first and `ε` afterwards, below the threshold
`ε₀(ρ/4)` read off this input.  See `Submission/EFL/S12Assembly.lean`,
`Submission/Work/ConeSwitch/Assembly.lean` and `Submission/EFL/OptColOdd.lean`.

The linear form is kept below as `GKOStatementLinear`, because the conditional lemmas
`optcol_corollary_core`/`optcol_corollary_even`/`optcol_corollary_odd` are still proved from it
(they are no longer on the critical path of §12).
-/

/-- **Theorem 10.8 (Glock–Kühn–Osthus)**, faithful form: for every `p ∈ (0,1)` there are
thresholds `ν₀, ε₀ > 0` with `ε₀ ≤ p` such that a lower `(p,ε)`-regular 2-uniform hypergraph
on an even number `n` of vertices with `Δ - δ ≤ νn`, `ε ≤ ε₀`, `ν ≤ ν₀`, and a minimum-degree
vertex `w` satisfying the paper's `(def_ineq)` condition has `χ'(G) = Δ(G)` (here expressed as
`Δ(G)`-colourability, which together with the trivial lower bound is the assertion of the
theorem), for all sufficiently large `n`.

The body below is *verbatim* the body of `Work.Deep.GKO.GKOStatementFixed` (`Deep/GKO`), so
the two `Prop`s are definitionally equal and the chapters' results apply to this input without
a conversion lemma.  (The definition cannot be written as an `abbrev` of that one: the `GKO`
chapter imports this module, so the import would be a cycle.) -/
def GKOStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∃ ν₀ ε₀ : ℝ, 0 < ν₀ ∧ 0 < ε₀ ∧ ε₀ ≤ p ∧
    (∀ ν ε : ℝ, 0 < ν → ν ≤ ν₀ → 0 < ε → ε ≤ ε₀ → ∃ N₀ : ℕ,
      ∀ n ≥ N₀, ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
      Even n →
      (∃ w : Fin n, (∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v) ∧
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ.erase w),
            ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖))

/-- **Theorem 10.8 (Glock–Kühn–Osthus)** with the *linear* hierarchy
`10^10 * (ν + ε) ≤ p`.

This is the form in which the input was first recorded.  It is *stronger* than what the
Kühn–Osthus proof yields (the proof only gives `ε'' ≲ p·τ(p/2)` with `ε'' ≈ 2√(24ν/p)`, which
under the linear hierarchy is the `p`-independent constant `≈ 3·10⁻⁵`: bigger than `p·τ(p/2)`
for small `p`), so whether it is true is open.  It is retained only for the conditional lemmas
`optcol_corollary_core`/`_even`/`_odd` below, which are no longer used by §12.

It *was* false without the hierarchy (found 2026-09-22 by the `Deep/GKO` subproject): for
`ε > 1/2` the lower-regularity hypothesis is vacuous (two disjoint sets of size `≥ εn` cannot
exist), so with `ν = 1`, `ε = 3/5`, `p = 9/10` and `𝓖` the triangle on three vertices plus
isolated vertices (even `n`), all other hypotheses hold while `χ'(𝓖) = 3 > 2 = Δ(𝓖)`. -/
def GKOStatementLinear : Prop :=
  ∀ ν ε p : ℝ, 0 < ν → 0 < ε → ε < p → p < 1 → 10 ^ 10 * (ν + ε) ≤ p → ∃ N₀ : ℕ,
    ∀ n ≥ N₀, ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
    SelfLowerRegular 𝓖 Set.univ p ε →
    (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ ν * (n : ℝ)) →
    Even n →
    (∃ w : Fin n, (∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v) ∧
      ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
        ∑ v ∈ (Finset.univ.erase w), ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) →
    𝓖.Colorable (hypergraphMaxDegree 𝓖)

/-! ## Auxiliary estimates -/

/-- The total `Δ - d(v)` is at least `Δ` when at least `Δ` vertices have
degree less than `Δ`. -/
theorem maxDegree_le_sum_sub (𝓖 : Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2)
    (h : (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ)) ≥
      (hypergraphMaxDegree 𝓖 : ℝ)) :
    (hypergraphMaxDegree 𝓖 : ℝ) ≤ ∑ v ∈ (Finset.univ : Finset (Fin n)),
      ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
  classical
  set L : Finset (Fin n) := Finset.univ.filter
    (fun v => degAt 𝓖 v < hypergraphMaxDegree 𝓖) with hL
  have hLcoe : (L : Set (Fin n)) = {v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖} := by
    ext v
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe,
      Set.mem_setOf_eq]
  have hLcard : (L.card : ℝ) = (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard) : ℝ) := by
    rw [← Set.ncard_coe_finset (s := L), hLcoe]
  have h1 : (L.card : ℝ) ≤ ∑ v ∈ L,
      ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
    have hsum : (∑ v ∈ L, (1 : ℝ)) ≤ ∑ v ∈ L,
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
      refine Finset.sum_le_sum (fun v hv => ?_)
      have hv' : degAt 𝓖 v < hypergraphMaxDegree 𝓖 := by
        rw [hL] at hv
        exact (Finset.mem_filter.mp hv).2
      have hle : (degAt 𝓖 v : ℝ) + 1 ≤ (hypergraphMaxDegree 𝓖 : ℝ) := by exact_mod_cast hv'
      linarith
    have hc : (∑ v ∈ L, (1 : ℝ)) = (L.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hc] at hsum
    exact hsum
  have h3 : ∑ v ∈ L, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin n)),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro v hv
      rw [hL] at hv
      exact (Finset.mem_filter.mp hv).1
    · intro v _ _
      have hle : (degAt 𝓖 v : ℝ) ≤ (hypergraphMaxDegree 𝓖 : ℝ) := by
        exact_mod_cast degAt_le_maxDegree 𝓖 h2 v
      linarith
  rw [hLcard] at h1
  linarith

/-- **Lower regularity gives `Δ ≥ (p - 3ε)n`.** -/
theorem maxDegree_ge_of_selfLowerRegular (𝓖 : Hypergraph (Fin n)) {p ε : ℝ}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (hlr : SelfLowerRegular 𝓖 Set.univ p ε)
    (hεn : 1 ≤ ε * (n : ℝ)) (hε1 : ε ≤ 1 / 3) (hεp : ε ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) :
    (p - 3 * ε) * (n : ℝ) ≤ (hypergraphMaxDegree 𝓖 : ℝ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hεn0 : (0 : ℝ) < ε * n := lt_of_lt_of_le zero_lt_one hεn
  have hfloor : ⌈ε * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith [hε1, hnR])
  obtain ⟨V₁, -, hV₁card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := ⌈ε * (n : ℝ)⌉₊)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hfloor)
  set V₂ : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ V₁ with hV₂
  have hV₁subuniv : ∀ v ∈ V₁, v ∈ (Set.univ : Set (Fin n)) := fun v _ => Set.mem_univ v
  have hV₂subuniv : ∀ v ∈ V₂, v ∈ (Set.univ : Set (Fin n)) := fun v _ => Set.mem_univ v
  have hdisj : Disjoint V₁ V₂ := by
    rw [hV₂, Finset.disjoint_left]
    intro v hv1 hv2
    exact (Finset.mem_sdiff.mp hv2).2 hv1
  have hV₁ge : ε * (n : ℝ) ≤ (V₁.card : ℝ) := by
    rw [hV₁card]; exact_mod_cast Nat.le_ceil (ε * (n : ℝ))
  have hceil_lt : ((⌈ε * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤ ε * (n : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt hεn0)
    push_cast at h
    linarith
  have hV₂card : (V₂.card : ℝ) = (n : ℝ) - ((⌈ε * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h1 : V₂.card = n - ⌈ε * (n : ℝ)⌉₊ := by
      rw [hV₂, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        hV₁card]
    rw [h1, Nat.cast_sub hfloor]
  have hV₂ge : ε * (n : ℝ) ≤ (V₂.card : ℝ) := by
    rw [hV₂card]
    have h3 : (2 : ℝ) * (ε * n) + 1 ≤ (n : ℝ) := by nlinarith [hε1, hεn, hnR]
    linarith
  have hV₁ge' : ε * (((Set.univ : Set (Fin n))).ncard : ℝ) ≤ (V₁.card : ℝ) := by
    rw [Set.ncard_univ, Nat.card_fin]; exact hV₁ge
  have hV₂ge' : ε * (((Set.univ : Set (Fin n))).ncard : ℝ) ≤ (V₂.card : ℝ) := by
    rw [Set.ncard_univ, Nat.card_fin]; exact hV₂ge
  have hlrA := hlr V₁ V₂ hV₁subuniv hV₂subuniv hdisj hV₁ge' hV₂ge'
  have hsum := edgeCount_le_sum_degAt_left 𝓖 V₁ V₂
  have hbound : (edgeCount 𝓖 V₁ V₂ : ℝ) ≤ (V₁.card : ℝ) * (hypergraphMaxDegree 𝓖 : ℝ) := by
    have h3 : ((∑ v ∈ V₁, degAt 𝓖 v : ℕ) : ℝ) ≤ (V₁.card : ℝ) * (hypergraphMaxDegree 𝓖 : ℝ) := by
      have h4 : (∑ v ∈ V₁, degAt 𝓖 v) ≤ V₁.card * hypergraphMaxDegree 𝓖 := by
        calc (∑ v ∈ V₁, degAt 𝓖 v) ≤ ∑ _v ∈ V₁, hypergraphMaxDegree 𝓖 :=
              Finset.sum_le_sum (fun v _ => degAt_le_maxDegree 𝓖 h2 v)
          _ = V₁.card * hypergraphMaxDegree 𝓖 := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      exact_mod_cast h4
    have h5 : (edgeCount 𝓖 V₁ V₂ : ℝ) ≤ ((∑ v ∈ V₁, degAt 𝓖 v : ℕ) : ℝ) := by
      exact_mod_cast hsum
    linarith
  have hV₁pos : (0 : ℝ) < (V₁.card : ℝ) := lt_of_lt_of_le hεn0 hV₁ge
  have hΔ : (p - ε) * (V₂.card : ℝ) ≤ (hypergraphMaxDegree 𝓖 : ℝ) := by
    have h6a : (V₁.card : ℝ) * ((p - ε) * (V₂.card : ℝ)) =
        (p - ε) * (V₁.card : ℝ) * (V₂.card : ℝ) := by ring
    have h6 : (V₁.card : ℝ) * ((p - ε) * (V₂.card : ℝ)) ≤
        (V₁.card : ℝ) * (hypergraphMaxDegree 𝓖 : ℝ) := by
      rw [h6a]; exact le_trans hlrA hbound
    exact le_of_mul_le_mul_left h6 hV₁pos
  have hpε : 0 ≤ p - ε := by linarith
  have hV₂big : (1 - 2 * ε) * (n : ℝ) ≤ (V₂.card : ℝ) := by
    rw [hV₂card]
    linarith [hceil_lt, hεn]
  have h7 : (p - ε) * ((1 - 2 * ε) * (n : ℝ)) ≤ (p - ε) * (V₂.card : ℝ) :=
    mul_le_mul_of_nonneg_left hV₂big hpε
  have h8 : (p - 3 * ε) * (n : ℝ) ≤ (p - ε) * ((1 - 2 * ε) * (n : ℝ)) := by
    have h9 : 0 ≤ ε * (n : ℝ) := le_of_lt hεn0
    have hε0 : 0 ≤ ε := by nlinarith [h9, hnR]
    have hkey : 0 ≤ (n : ℝ) * (2 * ε * (1 - p + ε)) :=
      mul_nonneg (Nat.cast_nonneg n)
        (mul_nonneg (by linarith) (by linarith))
    nlinarith [hkey]
  exact le_trans h8 (le_trans h7 hΔ)

/-! ## Corollary 10.13 -/

/-- **Corollary 10.13 (`cor:optcol`), core form.**  If `𝓖` is a lower
`(p,ε)`-regular graph on an even number of vertices, `Δ - d(v) ≤ ηn` for all
`v`, and there is a minimum-degree vertex `w` satisfying the paper's
`(def_ineq₂)` condition `2(Δ - d(w)) ≤ Σ_v (Δ - d(v))`, then `χ'(𝓖) = Δ`. -/
theorem optcol_corollary_core (hGKO : GKOStatementLinear) {η ε p : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hεp : ε < p) (hp : p < 1) (hsmall : 10 ^ 10 * (η + ε) ≤ p) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, Even n → ∀ 𝓖 : Hypergraph (Fin n),
      (∀ e ∈ 𝓖, edgeSize e = 2) → SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
      (∃ w : Fin n, (∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v) ∧
        2 * ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
          ∑ v ∈ (Finset.univ : Finset (Fin n)),
            ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖) := by
  have hηp : 2 * η ≤ p - 3 * ε := by nlinarith [hsmall, hη, hε]
  obtain ⟨N₁, hN₁⟩ := hGKO η ε p hη hε hεp hp hsmall
  refine ⟨max N₁ (max 4 (max ⌈(1 : ℝ) / ε⌉₊ ⌈(1 : ℝ) / η⌉₊)), ?_⟩
  intro n hn hev 𝓖 h2 hlr hdeg hw
  obtain ⟨w, hwle, hsum2⟩ := hw
  have hN₁le : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hsplit : (∑ v ∈ (Finset.univ : Finset (Fin n)),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) =
      ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) +
      ∑ v ∈ (Finset.univ.erase w),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
    have := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun v => ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ))) (Finset.mem_univ w)
    linarith
  have hcond : ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
      ∑ v ∈ (Finset.univ.erase w),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) := by
    linarith [hsum2, hsplit]
  exact hN₁ n hN₁le 𝓖 h2 hlr hdeg hev ⟨w, hwle, hcond⟩

/-- **Corollary 10.13 (`cor:optcol`), even case.**  If `𝓖` is a lower
`(p,ε)`-regular graph on an even number of vertices, `Δ - d(v) ≤ ηn` for all
`v`, and at least `Δ` vertices have degree less than `Δ`, then `χ'(𝓖) = Δ`. -/
theorem optcol_corollary_even (hGKO : GKOStatementLinear) {η ε p : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hεp : ε < p) (hp : p < 1) (hsmall : 10 ^ 10 * (η + ε) ≤ p) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, Even n → ∀ 𝓖 : Hypergraph (Fin n),
      (∀ e ∈ 𝓖, edgeSize e = 2) → SelfLowerRegular 𝓖 Set.univ p ε →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
      (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
        (hypergraphMaxDegree 𝓖 : ℝ)) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖) := by
  have hηp : 2 * η ≤ p - 3 * ε := by nlinarith [hsmall, hη, hε]
  obtain ⟨N₀, hN₀⟩ := optcol_corollary_core hGKO hη hε hεp hp hsmall
  refine ⟨max N₀ (max 4 (max ⌈(1 : ℝ) / ε⌉₊ ⌈(1 : ℝ) / η⌉₊)), ?_⟩
  intro n hn hev 𝓖 h2 hlr hdeg hlow
  have hN₀le : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hεle : ⌈(1 : ℝ) / ε⌉₊ ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn1 : 1 ≤ n := by
    have : (4 : ℕ) ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    omega
  have hεn : 1 ≤ ε * (n : ℝ) := by
    have h1 : (1 : ℝ) / ε ≤ (n : ℝ) := Nat.ceil_le.mp hεle
    have h2 : 1 ≤ ε * ((1 : ℝ) / ε) := by
      rw [mul_one_div, div_self (ne_of_gt hε)]
    have h3 : ε * ((1 : ℝ) / ε) ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  have hε1 : ε ≤ 1 / 3 := by nlinarith [hεp, hηp, hη, hp]
  have hΔ : (p - 3 * ε) * (n : ℝ) ≤ (hypergraphMaxDegree 𝓖 : ℝ) :=
    maxDegree_ge_of_selfLowerRegular 𝓖 h2 hlr hεn hε1 hεp.le hp.le hn1
  have hsum : (hypergraphMaxDegree 𝓖 : ℝ) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin n)),
        ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) :=
    maxDegree_le_sum_sub 𝓖 h2 hlow
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, hn1⟩⟩
  obtain ⟨w, -, hw⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun v => degAt 𝓖 v) hne
  have hwle : ∀ v : Fin n, degAt 𝓖 w ≤ degAt 𝓖 v := fun v => hw v (Finset.mem_univ v)
  have hδ : (hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ) ≤ η * (n : ℝ) := hdeg w
  have hΔδ : 2 * ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 w : ℝ)) ≤
      (p - 3 * ε) * (n : ℝ) := by
    have h1 : 2 * (η * (n : ℝ)) ≤ (p - 3 * ε) * (n : ℝ) := by nlinarith [hηp, hη.le]
    linarith [h1, hδ]
  refine hN₀ n hN₀le hev 𝓖 h2 hlr hdeg ⟨w, hwle, ?_⟩
  linarith [hΔ, hΔδ, hsum]

end

end ErdosFaberLovaszConjecture
