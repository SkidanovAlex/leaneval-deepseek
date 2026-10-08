import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.ThreePoints.EvenCardSource.lemma2_propagation_uncond
import Submission.Work.ThreePoints.EvenCardSource.lemma2_part1_uncond
import Submission.Work.ThreePoints.EvenCardSource.not_rp_twoTransitive_uncond
import Submission.Work.ThreePoints.EvenCardSource.rp_no_two_fixed_pts_uncond
import Submission.Work.ThreePoints.EvenCardSource.sec3_prop1_exists_uncond
import Submission.Work.DoubleTransitivity.App2.app2_6
import Submission.Work.DoubleTransitivity.App2.app2_3
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.EvenCardSource.prop2_uncond`

Peterfalvi I Ch. I §4 Prop. 2 (p. 156–157), with the Brauer–Suzuki hypothesis removed: for a finite
group `G`, a strongly embedded subgroup `H ≤ G`, `p ≠ 2` a prime and `P` maximal among the
`p`-subgroups of `H` with at least three fixed points of `Ω = G ⧸ H`, the subgroup `P` is maximal
among the `p`-subgroups of `G` with at least three fixed points and `|N_G(P) ⊓ H|` is even.

This is a transcription of `Work.DoubleTransitivity.Sec4.prop2_aux` / `prop2` with `hBrSz` deleted;
the only use of `hBrSz` in that argument is Ch. I §3 Prop. 1
(`Work.DoubleTransitivity.Sec3.prop1`), replaced here by the Brauer–Suzuki-free
`sec3_prop1_exists_uncond`, and Ch. I §4 Prop. 1(a),(b), replaced by
`not_rp_twoTransitive_uncond` and `rp_no_two_fixed_pts_uncond` (built on the Brauer–Suzuki-free
Ch. I §4 Lemma 2 `sec4_lemma2_of_part1_uncond`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.DoubleTransitivity
open Work.DoubleTransitivity.Sec4
open scoped Pointwise

namespace Work.ThreePoints.EvenCardSource

variable {G : Type} [Group G] [Finite G]

/-- Conjugating the normaliser inside a point stabiliser by an element `g` which normalises the
subgroup `Q` and moves `ω₁` to `ω₂` preserves the order. -/
theorem ncard_normalizer_inf_stabilizer_eq_of_smul {H Q : Subgroup G} {ω₁ ω₂ : Omega H} {g : G}
    (hgQ : conj g Q = Q) (h : g • ω₁ = ω₂) :
    Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁) =
      Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₂) := by
  have hconjN : conj g (Subgroup.normalizer (Q : Set G)) = Subgroup.normalizer (Q : Set G) := by
    have hmap := Subgroup.map_normalizer_eq_of_bijective (Q : Subgroup G)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective
    rw [show conj g (Subgroup.normalizer (Q : Set G)) =
          (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom from rfl, hmap]
    rw [show (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = conj g Q from rfl, hgQ]
  have hstep : conj g (Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁) =
      Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₂ := by
    rw [Work.ThreePoints.conj_inf, hconjN,
      ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj g ω₁, h]
  rw [← hstep]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).symm

/-- The assembly step of Ch. I §4 Prop. 2, with the two `𝓡_p`-dichotomy inputs isolated:
`hNoTwo` is the content of Ch. I §4 Prop. 1(b) on the `𝓡_p ≠ ∅` side, and `h2tr` that of
Prop. 1(a) on the `𝓡_p = ∅` side. -/
theorem prop2_aux_uncond
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThreeIn p H P)
    (hNoTwo : Rp p H → ∀ T : Subgroup G, IsPGroup p T → (fixedPts H T).ncard ≠ 2)
    (h2tr : ¬ Rp p H → MulAction.IsMultiplyPretransitive G (Omega H) 2) :
    Work.DoubleTransitivity.MaxFixesThree p H P ∧
    Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (Omega H) := Fintype.ofFinite _
  obtain ⟨hPp, hPH, hP3, hPmax⟩ := hP
  have hP3' : 3 ≤ (fixedPts H P).ncard := hP3
  have hstabH : MulAction.stabilizer G (pt H) = H := stabilizer_pt_eq H
  have hptP : (pt H) ∈ fixedPts H P := mem_fixedPts_iff_le_stabilizer_aux.mpr (by rw [hstabH]; exact hPH)
  by_cases hRp : Rp p H
  · -- ## Case 1: `𝓡_p ≠ ∅`
    have hno2 : ∀ T : Subgroup G, IsPGroup p T → (fixedPts H T).ncard ≠ 2 := hNoTwo hRp
    -- **(A) `P` is maximal among the `p`-subgroups of `G` with three fixed points**
    have hmax : ∀ Q : Subgroup G, IsPGroup p Q → FixesThree H Q → P ≤ Q → Q ≤ P := by
      intro Q hQp hQ3 hPQ
      have hQ3' : 3 ≤ (fixedPts H Q).ncard := hQ3
      -- a fixed point `K` of `Q` different from `pt H`
      obtain ⟨K, hK, hKne⟩ : ∃ K : Omega H, K ∈ fixedPts H Q ∧ K ≠ pt H := by
        have hgt : 1 < (fixedPts H Q).ncard := by omega
        obtain ⟨K, hK, hKne⟩ := Set.exists_ne_of_one_lt_ncard hgt (pt H)
        exact ⟨K, hK, hKne⟩
      -- `S`: a `p`-Sylow of `Stab (pt H) ⊓ Stab K` containing `P`
      have hQK : Q ≤ MulAction.stabilizer G K :=
        (mem_fixedPts_iff_le_stabilizer_aux (X := Q)).mp hK
      have hPle : P ≤ MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G K :=
        le_inf (by rw [hstabH]; exact hPH) (le_trans hPQ hQK)
      obtain ⟨S, hPS, hSsyl⟩ := exists_isSylowSubgroupOf_le hPp hPle
      have hSH : S ≤ H := by
        rw [← hstabH]; exact le_trans hSsyl.1 inf_le_left
      have hS3 : 3 ≤ (fixedPts H S).ncard := by
        have h2 : 2 ≤ (fixedPts H S).ncard := by
          have hsub : ({(pt H), K} : Set (Omega H)) ⊆ fixedPts H S := by
            intro ω hω
            rcases hω with rfl | rfl
            · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hSsyl.1 inf_le_left)
            · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hSsyl.1 inf_le_right)
          have hle := Set.ncard_le_ncard hsub
          rw [Set.ncard_pair hKne.symm] at hle
          exact hle
        have hne2 : (fixedPts H S).ncard ≠ 2 := hno2 S hSsyl.2.1
        omega
      have hSP : S = P := le_antisymm (hPmax S hSsyl.2.1 hSH hS3 hPS) hPS
      have hPsyl : IsSylowSubgroupOf p P
          (MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G K) := hSP ▸ hSsyl
      -- Ch. I §3 Lemma 1
      obtain ⟨u, hu2, huP, huK⟩ :=
        Work.ThreePoints.sec3_lemma1 hH hp (fun h => hKne h.symm) hPsyl
      have huusq : u * u = 1 :=
        Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two hu2
      have hstabK : MulAction.stabilizer G K = conj u H := by
        have h1 := Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj u (pt H)
        rw [huK, hstabH] at h1
        exact h1
      have hQuH : conj u Q ≤ H := by
        calc conj u Q ≤ conj u (conj u H) := Subgroup.map_mono (hstabK ▸ hQK)
          _ = H := by rw [← conj_mul, huusq, conj_one]
      have hQconj3 : 3 ≤ (fixedPts H (conj u Q)).ncard := by
        rw [ncard_fixedPts_conj]; exact hQ3'
      have hPQconj : P ≤ conj u Q := by
        have h1 : conj u P ≤ conj u Q := Subgroup.map_mono hPQ
        rwa [huP] at h1
      have hconjQ : conj u Q = P :=
        le_antisymm (hPmax (conj u Q) (hQp.map _) hQuH hQconj3 hPQconj) hPQconj
      have hQeq : Q = P := by
        calc Q = conj (u * u) Q := by rw [huusq, conj_one]
          _ = conj u (conj u Q) := by rw [conj_mul]
          _ = conj u P := by rw [hconjQ]
          _ = P := huP
      exact hQeq.le
    refine ⟨⟨hPp, hP3, hmax⟩, ?_⟩
    -- **(B) the normaliser of `P` in `H` has even order**
    obtain ⟨ω, hωP, hωEven⟩ :=
      sec3_prop1_exists_uncond hH hp hp2 hPp hP3
        (fun R hPR hRp hR3 => le_antisymm (hmax R hRp hR3 hPR) hPR)
    have hωP' : P ≤ MulAction.stabilizer G ω := mem_fixedPts_iff_le_stabilizer.mp hωP
    have hωEven' : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓
        MulAction.stabilizer G ω)) := by
      rw [inf_comm]; exact hωEven
    by_cases hω : ω = pt H
    · rw [hω, hstabH] at hωEven'
      exact hωEven'
    · have hPle : P ≤ MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G ω :=
        le_inf (by rw [hstabH]; exact hPH) hωP'
      obtain ⟨S, hPS, hSsyl⟩ := exists_isSylowSubgroupOf_le hPp hPle
      have hS3 : 3 ≤ (fixedPts H S).ncard := by
        have h2 : 2 ≤ (fixedPts H S).ncard := by
          have hsub : ({(pt H), ω} : Set (Omega H)) ⊆ fixedPts H S := by
            intro y hy
            rcases hy with rfl | rfl
            · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hSsyl.1 inf_le_left)
            · exact mem_fixedPts_iff_le_stabilizer_aux.mpr (le_trans hSsyl.1 inf_le_right)
          have hle := Set.ncard_le_ncard hsub
          rw [Set.ncard_pair (fun h => hω h.symm)] at hle
          exact hle
        have hne2 : (fixedPts H S).ncard ≠ 2 := hno2 S hSsyl.2.1
        omega
      have hSP : S = P := le_antisymm (hmax S hSsyl.2.1 hS3 hPS) hPS
      have hPsyl : IsSylowSubgroupOf p P
          (MulAction.stabilizer G (pt H) ⊓ MulAction.stabilizer G ω) := hSP ▸ hSsyl
      obtain ⟨u, _hu2, huP, huω⟩ :=
        Work.ThreePoints.sec3_lemma1 hH hp (fun h => hω h.symm) hPsyl
      have hcard := ncard_normalizer_inf_stabilizer_eq_of_smul (H := H) (Q := P)
        (ω₁ := pt H) (ω₂ := ω) huP huω
      rw [hstabH] at hcard
      rw [hcard]
      exact hωEven'
  · -- ## Case 2: `𝓡_p = ∅`
    have htr : MulAction.IsMultiplyPretransitive G (Omega H) 2 := h2tr hRp
    obtain ⟨b, hb, hbne⟩ :=
      Set.exists_ne_of_one_lt_ncard (s := fixedPts H P) (by omega) (pt H)
    obtain ⟨hmax, h2trN⟩ := Work.DoubleTransitivity.App2.app2_6 (a := pt H) (b := b)
      (fun h => hbne h.symm) htr hPp (by rw [hstabH]; exact hPH) hP3'
      (fun Q hQp hQH hQ3 hPQ => hPmax Q hQp (by rw [← hstabH]; exact hQH) hQ3 hPQ)
    refine ⟨⟨hPp, hP3, hmax⟩, ?_⟩
    obtain ⟨ω, hωP, hωEven⟩ :=
      sec3_prop1_exists_uncond hH hp hp2 hPp hP3
        (fun R hPR hRp hR3 => le_antisymm (hmax R hRp hR3 hPR) hPR)
    have hωP' : P ≤ MulAction.stabilizer G ω := mem_fixedPts_iff_le_stabilizer.mp hωP
    have hωEven' : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓
        MulAction.stabilizer G ω)) := by
      rw [inf_comm]; exact hωEven
    by_cases hω : ω = pt H
    · rw [hω, hstabH] at hωEven'
      exact hωEven'
    · -- a third point of `Ω_P`
      have hex : ∃ ω' : Omega H, ω' ∈ fixedPts H P ∧ ω' ≠ pt H ∧ ω' ≠ ω := by
        by_contra hc
        rw [not_exists] at hc
        have hsub : fixedPts H P ⊆ ({(pt H), ω} : Set (Omega H)) := by
          intro y hy
          by_cases hy1 : y = pt H
          · exact Or.inl hy1
          · refine Or.inr ?_
            by_contra hy2
            exact hc y ⟨hy, hy1, hy2⟩
        have hle : (fixedPts H P).ncard ≤ ({(pt H), ω} : Set (Omega H)).ncard :=
          Set.ncard_le_ncard hsub
        rw [Set.ncard_pair (fun h => hω h.symm)] at hle
        omega
      obtain ⟨ω', hω', hω'ne, hω'neω⟩ := hex
      obtain ⟨m, hmN, hmω, -⟩ := h2trN (pt H) hptP ω' hω' (fun h => hω'ne h.symm)
        ω hωP' ω' hω' (fun h => hω'neω h.symm)
      have hmQ : conj m P = P := (conj_eq_self_iff_mem_normalizer m P).mpr hmN
      have hcard := ncard_normalizer_inf_stabilizer_eq_of_smul (H := H) (Q := P)
        (ω₁ := pt H) (ω₂ := ω) hmQ hmω
      rw [hstabH] at hcard
      rw [hcard]
      exact hωEven'

/-- Peterfalvi I Ch. I §4 Prop. 2 (p. 156–157), without the Brauer–Suzuki hypothesis: `P` is
maximal among the `p`-subgroups of `G` with at least three fixed points and `|N_G(P) ⊓ H|` is
even.  Assembly of `prop2_aux_uncond` with Ch. I §4 Prop. 1(a),(b) in their Brauer–Suzuki-free
forms. -/
theorem prop2_uncond {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.MaxFixesThreeIn p H P) :
    Work.DoubleTransitivity.MaxFixesThree p H P ∧
    Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ H)) := by
  have h1 : Sec4Lemma2Part1 p H := lemma2_part1_uncond hH hp hp2
  exact prop2_aux_uncond hH hp hp2 hP
    (rp_no_two_fixed_pts_uncond hH hp hp2 h1)
    (not_rp_twoTransitive_uncond hH hp hp2 h1)

end Work.ThreePoints.EvenCardSource
