import Mathlib
import Submission.Work.ThreePoints.ThmC.Prop2h2t

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

/-- **Peterfalvi I Ch. II §2 Lemma 1 (b) (p. 164).**  Given part (a) (`IsMaxP3 H p P`), the
normaliser `M = N_G(P)` acts `2`-transitively on the fixed points `Ω_P` of `P`, and for every
fixed point `H₁ = conj g₁ H` of `P` the subgroup `M ⊓ H₁` is strongly embedded in `M` (i.e. a
proper Bender group of `M`).

Proof sketch.  `P ≤ H` and `P` is maximal among the `p`-subgroups of `H` with `≥ 3` fixed points
(immediate from part (a)), so App. II (6) (`Work.ThreePoints.app2_6_uniform`) gives both the
`2`-transitivity of `M` on `Ω_P` and the maximality of `P` among the `p`-subgroups of `G` with
`≥ 3` fixed points.  For the strong embedding of `M ⊓ H₁`: Ch. I §4 Prop. 2
(`Work.ThreePoints.ThmC.even_card_normalizer_h2t` applied to `H` and `Q = P`) gives
`Even |N_H(P)| = Even |H ⊓ M|`, and the transitivity of `M` on `Ω_P` transfers this to
`Even |M ⊓ K|` for every `K ∈ Ω_P` (if `n ∈ M` with `conj n H = K` then
`M ⊓ K = conj n (M ⊓ H)`, since `n M n⁻¹ = M`).  Properness of `M ⊓ H₁` in `M` again follows from
transitivity and `3 ≤ |Ω_P|` (a transitive action on `≥ 3` points has no subgroup strictly above
a point stabiliser fixing a point).  Ch. I §1 (6)
(`Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf`) then concludes. -/
theorem ch2_sec2_lem1_partB {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hA : Work.ThreePoints.ThmC.IsMaxP3 H p P) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
      (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G))) := by
  classical
  -- `P` lies in `H`, hence is a `p`-subgroup of `H`, maximal among those with `≥ 3` fixed points
  have htwo_le_H : Submission.Blueprint.twoPoint H g ≤ H := by
    rw [Work.ThreePoints.twoPoint_eq]; exact inf_le_left
  have hPH : P ≤ H := hP.1.trans (le_trans inf_le_left htwo_le_H)
  have hPp : IsPGroup p P := hA.1
  have hP3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := hA.2.1
  have hPmax : ∀ R : Subgroup G, P ≤ R → R ≤ H → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard → R = P :=
    fun R hR _ hRp hR3 => hA.2.2 R hR hRp hR3
  -- App. II (6): `M = N_G(P)` acts `2`-transitively on the fixed points of `P`
  obtain ⟨_, ht2⟩ := Work.ThreePoints.app2_6_uniform h2t hp hPH hPp hP3 hPmax
  refine ⟨ht2, ?_⟩
  intro g₁ hg₁P
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hMdef
  set K : Subgroup G := Submission.Blueprint.conj g₁ H with hKdef
  have hKstrong : IsStronglyEmbedded K := Work.ThreePoints.conj_stronglyEmbedded hH g₁
  have htrans := ht2.isTransitiveOnSub
  -- the two points of `Ω_P` cut out by `H` and by `K = conj g₁ H`
  have hstab0 : MulAction.stabilizer G (((1 : G) : G ⧸ H)) = H := by
    rw [Work.ThreePoints.stabilizer_mk H 1, Work.ThreePoints.conj_one]
  have hω₀ : (((1 : G) : G ⧸ H)) ∈ Submission.Blueprint.fixedPts H P :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by rw [hstab0]; exact hPH)
  have hstab1 : MulAction.stabilizer G ((g₁ : G) : G ⧸ H) = K := by
    rw [Work.ThreePoints.stabilizer_mk H g₁, hKdef]
  have hω₁ : ((g₁ : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by rw [hstab1]; exact hg₁P)
  -- some `n ∈ M` moves the point `H` to the point `K`
  obtain ⟨n, hnM, hnω⟩ := htrans (((1 : G) : G ⧸ H)) hω₀ ((g₁ : G) : G ⧸ H) hω₁
  have hconjH : Submission.Blueprint.conj n H = K := by
    have h1 := Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : G) : G ⧸ H))
    rw [hnω, hstab1, hstab0] at h1
    exact h1.symm
  -- Ch. I §4 Prop. 2: `|N_H(P)| = |M ⊓ H|` is even
  have hevH : Even (Nat.card (M ⊓ H : Subgroup G)) := by
    have h := even_card_normalizer_h2t hH h2t hBrSz hp hpodd hPH hPp hP3 hPmax
    rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hPH] at h
    rwa [inf_comm] at h
  -- conjugation by `n ∈ M` preserves `M`
  have hMconj : Submission.Blueprint.conj n M = M := by
    have hstep : ∀ u ∈ M, Submission.Blueprint.conj u M ≤ M := by
      intro u hu m hm
      rw [Work.ThreePoints.mem_conj_iff] at hm
      have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
      rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
    refine le_antisymm (hstep n hnM) ?_
    calc M = Submission.Blueprint.conj n (Submission.Blueprint.conj n⁻¹ M) := by
          rw [← Work.ThreePoints.conj_mul, mul_inv_cancel, Work.ThreePoints.conj_one]
      _ ≤ Submission.Blueprint.conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM))
  -- so `|M ⊓ K| = |M ⊓ H|` is even as well
  have hevK : Even (Nat.card (M ⊓ K : Subgroup G)) := by
    have hconj : Submission.Blueprint.conj n (M ⊓ H) = M ⊓ K := by
      rw [Work.ThreePoints.conj_inf, hMconj, hconjH]
    rw [← hconj, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hevH
  -- `M ⊓ K` is a proper subgroup of `M`: otherwise the transitive `M` would fix every point of
  -- `Ω_P`, contradicting `3 ≤ |Ω_P|`
  have hproper : (M ⊓ K).subgroupOf M ≠ ⊤ := by
    intro htop
    have hle : M ≤ K := by
      intro m hm
      have hmem : (⟨m, hm⟩ : M) ∈ (M ⊓ K).subgroupOf M := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp hmem).2
    have hfix1 : ∀ m ∈ M, m • (((g₁ : G) : G ⧸ H)) = (((g₁ : G) : G ⧸ H)) := by
      intro m hm
      have hmem : m ∈ MulAction.stabilizer G (((g₁ : G) : G ⧸ H)) := by
        rw [hstab1]; exact hle hm
      exact MulAction.mem_stabilizer_iff.mp hmem
    have hall : ∀ ω ∈ Submission.Blueprint.fixedPts H P, ω = ((g₁ : G) : G ⧸ H) := by
      intro ω hω
      obtain ⟨m, hm, hmω⟩ := htrans ((g₁ : G) : G ⧸ H) hω₁ ω hω
      rw [← hmω]
      exact hfix1 m hm
    have h2 : 1 < (Submission.Blueprint.fixedPts H P).ncard := by omega
    obtain ⟨ω, hω, hne⟩ := Set.exists_ne_of_one_lt_ncard h2 (((1 : G) : G ⧸ H))
    exact hne ((hall ω hω).trans (hall _ hω₀).symm)
  -- Ch. I §1 (6)
  exact IsStronglyEmbedded.subgroupOf_inf hKstrong hproper hevK

end Work.ThreePoints.ThmC
