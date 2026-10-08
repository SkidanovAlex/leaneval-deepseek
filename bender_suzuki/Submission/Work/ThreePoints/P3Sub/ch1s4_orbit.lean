import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `N`-orbit of `H` inside `Ω_X`

Let `H` be a strongly embedded subgroup of a finite group `G`, `X ≤ H`, and `N ≤ N_G(X)` with
`N ⊓ H` strongly embedded in `N`.  Writing `Ω_X = fixedPts H X` for the set of conjugates of `H`
containing `X`, this file proves that **`N` is transitive on `Ω_X`**: every `ω ∈ Ω_X` is
`n • pt H` for some `n ∈ N`.

The proof is Ch. I §2 Lemma 2 (`Work.ThreePoints.ch1_lem2`) applied with `F = N`:

* `pt H ∈ Ω_X` because `X ≤ H`;
* for `ω = mk g ∈ Ω_X`, put `M = H^g`; then `X ≤ M`, so by `heven` the group
  `M ⊓ C_G(X)` has even order, and it contains an involution `u`; `u` lies in `N` by `hInv`,
  so `N ⊓ M` has even order;
* `N ⊓ H` has even order by `hSE`;
* `ch1_lem2` (with `H₁ = H`, `H₂ = M`) then produces an involution `t ∈ N` with
  `t H t⁻¹ = M`, whence `t • pt H = mk t = mk g = ω` (if `M = H`, take `t = 1`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3Sub

open Submission.Blueprint

theorem ch1s4_orbit {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {X N : Subgroup G} (hXH : X ≤ H)
    (hNN : N ≤ Subgroup.normalizer (X : Set G))
    (hInv : Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ N)
    (heven : ∀ M : Subgroup G, (∃ g : G, M = Submission.Blueprint.conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    (hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((N ⊓ H).subgroupOf N)) :
    ∀ ω ∈ Submission.Blueprint.fixedPts H X,
      ∃ n : N, (n : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = ω := by
  classical
  -- an involution in a subgroup of even order
  have key : ∀ K : Subgroup G, Even (Nat.card (K ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) →
      ∃ u : G, u ∈ K ∧ u ∈ Subgroup.centralizer (X : Set G) ∧ orderOf u = 2 := by
    intro K hK
    haveI : Fintype ↥(K ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
      Fintype.ofFinite ↥(K ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)
    have hdvd : 2 ∣ Fintype.card ↥(K ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp hK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    exact ⟨(x : G), x.2.1, x.2.2, (Subgroup.orderOf_coe x).trans hx⟩
  -- `N ⊓ H` has even order
  have hNHeven : Even (Nat.card (N ⊓ H : Subgroup G)) :=
    even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hSE.2.1)
      (Subgroup.card_comap_dvd_of_injective (N ⊓ H) N.subtype Subtype.coe_injective))
  intro ω hω
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk] at hω
  by_cases hsame : Submission.Blueprint.conj g H = H
  · -- `ω = pt H`
    refine ⟨1, ?_⟩
    have hgH : g ∈ H := by
      have h1 : g ∈ Subgroup.normalizer (H : Set G) :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g H).mp hsame
      rwa [IsStronglyEmbedded.normalizer_eq hH] at h1
    show ((1 : N) : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk g
    rw [Subgroup.coe_one, one_smul]
    exact (Work.DoubleTransitivity.mk_one_eq_iff.mpr hgH).symm
  · -- `M = H^g ≠ H`: apply Ch. I §2 Lemma 2 with `F = N`
    have hne : Submission.Blueprint.conj (1 : G) H ≠ Submission.Blueprint.conj g H := by
      rw [Work.DoubleTransitivity.conj_one]
      exact fun h => hsame h.symm
    have hMeven : Even (Nat.card (N ⊓ Submission.Blueprint.conj g H : Subgroup G)) := by
      obtain ⟨u, huM, huC, hu2⟩ :=
        key (Submission.Blueprint.conj g H) (heven _ ⟨g, rfl⟩ hω)
      have huN : u ∈ N := hInv ⟨huC, hu2⟩
      have hmem : u ∈ N ⊓ Submission.Blueprint.conj g H := ⟨huN, huM⟩
      have hdvd : 2 ∣ Nat.card (N ⊓ Submission.Blueprint.conj g H : Subgroup G) := by
        have h2 : Nat.card ↥(Subgroup.zpowers u) ∣
            Nat.card (N ⊓ Submission.Blueprint.conj g H : Subgroup G) :=
          Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hmem)
        rwa [Nat.card_zpowers u, hu2] at h2
      exact even_iff_two_dvd.mpr hdvd
    have hNHeven' : Even (Nat.card (N ⊓ Submission.Blueprint.conj (1 : G) H : Subgroup G)) := by
      rw [Work.DoubleTransitivity.conj_one]; exact hNHeven
    obtain ⟨⟨t, ht_inv, ht_conj⟩, -, -⟩ :=
      Work.ThreePoints.ch1_lem2 hH (F := N) (g₁ := 1) (g₂ := g) hne hNHeven' hMeven
    refine ⟨⟨t, ht_inv.1⟩, ?_⟩
    show (t : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk g
    rw [Work.DoubleTransitivity.smul_mk, mul_one]
    refine Work.ThreePoints.mk_eq_of_conj_eq (H := H) hH ?_
    rw [Work.DoubleTransitivity.conj_one] at ht_conj
    exact ht_conj

end Work.ThreePoints.P3Sub
