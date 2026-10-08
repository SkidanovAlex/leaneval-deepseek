import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.ThreePoints.sec4_prop2b
import Submission.Work.ThreePoints.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2c_sylow` — the Sylow 2-subgroup clause of Peterfalvi II Ch. V §2
Lemma 2 (c)

With `H = Q ⋊ D` a split rank-one datum (`h : IsSplitRankOne H Q t`), `D = H ⊓ Hᵗ`,
`V = C_D(t) = centD H t`, and `X ≠ 1` a subgroup of `V` whose centraliser `C_G(X)` has 2-rank
`≥ 2` (`hB3X`), there is a 2-subgroup `S` of `H ⊓ N_G(X)` of odd index such that

`H ⊓ N_G(X) = S ⋊ (D ⊓ N_G(X))`.

Mathematically `S` is `C_{Q}(X)`, the Sylow 2-subgroup of `C_H(X)`: this is the first assertion
of Lemma 2 (c).  The proof here goes through Ch. II §4 Prop. 3 (the `P3` clause of
`ChIIFourProp`), whose hypothesis `N_K(X) ≠ 1` is furnished by
`Work.ThmF.ChV12.exists_k_normalizing` (using `3 ≤ |Ω_X|`, obtained from the two-point
stabiliser together with the fixed point of `t`, and `hB3X`).

The `S` returned by `P3` lives in `O^{2'}(C_G(X)) ⊓ H`, whence `S ≤ C_G(X) ≤ N_G(X)`; the only
arithmetic left is that `H ⊓ N_G(X) = S · (D ⊓ N_G(X))` is a semidirect product (the second
factor normalises `S` by `P3`, and the intersection is trivial), so
`[H ⊓ N_G(X) : S] = |D ⊓ N_G(X)|`, which is odd because `|D|` is odd (`t ∉ H` and `H` strongly
embedded).
-/

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem lemma2c_sylow {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (X : Subgroup G) (hXV : X ≤ centD H t) (hXne : X ≠ ⊥) (hB3X : HasFourGroup (Subgroup.centralizer (X : Set G))) (hnil : Group.IsNilpotent ↥Q) : ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ⊓ Subgroup.normalizer (X : Set G) ∧ ¬ 2 ∣ (S.subgroupOf (H ⊓ Subgroup.normalizer (X : Set G))).index ∧ S ⊓ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ ∧ S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = H ⊓ Subgroup.normalizer (X : Set G) := by
  -- The two clauses of `ChIIFourProp` used below: Prop. 1 (b) and Prop. 3.
  have hP1b := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).1
  have hP3 := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.2.1
  -- `X ≤ V = C_D(t)` fixes at least the three points `H`, `tH` and the fixed point of `t`.
  have hX3 : 3 ≤ (fixedPts H X).ncard :=
    le_trans (Work.ThreePoints.three_le_ncard_fixedPts_centD h.stronglyEmbedded h.invol h.not_mem)
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hXV))
  -- The hypothesis `N_K(X) ≠ 1` of Ch. II §4 Prop. 3.
  obtain ⟨k, hkK, hk1, hkN⟩ :=
    exists_k_normalizing h.stronglyEmbedded h.invol h.not_mem hXV hX3 hB3X hP1b
  -- Ch. II §4 Prop. 3 applied to `X` and `k`.
  have hP3c := hP3 X hXne hXV ⟨k, hkK, hk1, hkN⟩
  dsimp only at hP3c
  obtain ⟨S, hSp, hSFH, _hIdx, hNGXS, hSD, hSsup⟩ := hP3c.2.1
  -- `S ≤ C_G(X)` (it lies in `O^{2'}(C_G(X))`), hence `S ≤ N_G(X)`.
  have hSC : S ≤ Subgroup.centralizer (X : Set G) := by
    intro s hs
    have hmem : s ∈ (oddResidual (Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype := (Subgroup.mem_inf.mp (hSFH hs)).1
    obtain ⟨c, _hc, hcs⟩ := Subgroup.mem_map.mp hmem
    rw [← hcs]
    exact c.2
  have hSH : S ≤ H := fun s hs => (Subgroup.mem_inf.mp (hSFH hs)).2
  have hSX : S ≤ Subgroup.normalizer (X : Set G) :=
    hSC.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hSU : S ≤ H ⊓ Subgroup.normalizer (X : Set G) := le_inf hSH hSX
  -- The intersection is trivial, because `S ⊓ D = ⊥`.
  have hST : S ⊓ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxT⟩ := Subgroup.mem_inf.mp hx
    have hxD : x ∈ twoPoint H t := (Subgroup.mem_inf.mp hxT).1
    exact (le_of_eq hSD) (Subgroup.mem_inf.mpr ⟨hxS, hxD⟩)
  -- `T := D ⊓ N_G(X)` is contained in `H ⊓ N_G(X)` and hence normalises `S`.
  have hDH : twoPoint H t ≤ H := inf_le_left
  have hTS : twoPoint H t ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) :=
    le_trans (le_inf (le_trans inf_le_left hDH) inf_le_right) hNGXS
  -- Hence `|H ⊓ N_G(X)| = |S| · |T|`.
  have hcardU : Nat.card ↥(H ⊓ Subgroup.normalizer (X : Set G)) =
      Nat.card ↥S * Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
    have hc := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := S)
      (K := twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) hTS
    rw [hSsup, hST] at hc
    simpa [Subgroup.card_bot] using hc
  -- so the index of `S` in `H ⊓ N_G(X)` is `|T|`.
  have hindex : (S.subgroupOf (H ⊓ Subgroup.normalizer (X : Set G))).index =
      Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf (H ⊓ Subgroup.normalizer (X : Set G)))
    have h2 : Nat.card ↥(S.subgroupOf (H ⊓ Subgroup.normalizer (X : Set G))) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv
    rw [h2, hcardU] at h1
    haveI : Nonempty ↥S := ⟨⟨1, S.one_mem⟩⟩
    exact Nat.mul_left_cancel Nat.card_pos h1
  -- `|T|` is odd: it divides `|D|`, and `|D|` is odd as `t ∉ H` and `H` is strongly embedded.
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := h.stronglyEmbedded.2.2 t h.not_mem
  have hTnot2 : ¬ 2 ∣ Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :=
    fun h2 => (Nat.not_even_iff_odd.mpr hDodd)
      (even_iff_two_dvd.mpr (dvd_trans h2 (Subgroup.card_dvd_of_le inf_le_left)))
  exact ⟨S, hSp, hSU, by rw [hindex]; exact hTnot2, hST, hSsup⟩

end Work.ThmF.ChV12
