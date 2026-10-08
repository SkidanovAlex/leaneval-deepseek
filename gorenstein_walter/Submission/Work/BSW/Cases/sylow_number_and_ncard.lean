import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Cases.sylow_two_structure
import Submission.Work.BSW.Cases.normalizer_centralizer_card

/-!
# The number of Sylow `2`-subgroups in the `|K| = 2` case

Hypotheses `Work.GW2.BSWHyps2 G t s K` with `|K| = 2` (Bender 1974, §1) pin down the Sylow
`2`-structure of `G`: `H = C_G(t)` has order `4`, every Sylow `2`-subgroup has order `4`
(`Work.BSW.Cases.sylow_two_structure`), and the normalizer `N = N_G(H)` has order `12`
(`Work.BSW.Cases.normalizer_centralizer_card`).  Consequently, writing `n₂ = Nat.card (Sylow 2 G)`,

* `12 * n₂ = |G|`, since `n₂` is the index of `N_G(H)`;
* `n₂ ≡ 1 (mod 4)`:  `H` acts by conjugation on the set of Sylow `2`-subgroups other than `H`,
  and this action is free — if `1 ≠ u ∈ H` normalized a Sylow `Q ≠ H` then `Q` and `u` would
  generate a `2`-subgroup of order `8`, but every `2`-subgroup of `G` has order dividing `4`
  (all Sylow `2`-subgroups have order `4`).  Hence all orbits have size `|H| = 4`, so
  `4 ∣ n₂ - 1` — the classical `n_p ≡ 1 (mod |P|)` for a TI Sylow subgroup;
* `n₂ ≥ 5`:  `n₂ ≡ 1 (mod 4)` and `n₂ ≠ 1` (otherwise the unique Sylow `2`-subgroup, of order
  `4`, would be normal, hence equal to `G` by simplicity, contradicting `12 * n₂ = |G|`).

This is the `3`-part of the Sylow-`2` counting that `Work.BSW.Cases.three_not_dvd_sylow_two`
consumes (it needs `n₂ ≡ 1 mod 4` and `n₂ ≥ 5` for `Work.BSW.Char.no_bad_arithmetic_two`).
-/

namespace Work.BSW.Cases

open Subgroup

/-- A `MulAction` restricted to a subtype which is stable under the action. -/
def mulActionSubtype {M : Type*} [Monoid M] {α : Type*} [MulAction M α]
    (p : α → Prop) (hp : ∀ (m : M) {a : α}, p a → p (m • a)) : MulAction M {a : α // p a} where
  smul m a := ⟨m • (a : α), hp m a.2⟩
  one_smul a := Subtype.ext (one_smul M (a : α))
  mul_smul m n a := Subtype.ext (mul_smul m n (a : α))

section

variable {G : Type} [Group G] {p : ℕ}

/-- A Sylow `p`-subgroup acts by conjugation on the subtree of Sylow `p`-subgroups different from
it: `P ≤ N_G(P)`, so the conjugation action of `P` fixes `P`. -/
private instance sylowNeMulAction (P : Sylow p G) :
    MulAction ↥(P : Subgroup G) {Q : Sylow p G // Q ≠ P} :=
  mulActionSubtype (fun Q : Sylow p G => Q ≠ P) (by
    intro g Q hQ heq
    refine hQ ?_
    have h2 : Q = (g : ↥(P : Subgroup G))⁻¹ • (g • Q) := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [h2, heq]
    exact Sylow.smul_eq_iff_mem_normalizer.mpr
      (Subgroup.inv_mem _ (Subgroup.le_normalizer g.2)))

end

/-- **Sylow `2` counting in the `|K| = 2` case.**  `n₂ = Nat.card (Sylow 2 G)` satisfies
`12 * n₂ = |G|`, `n₂ % 4 = 1` and `5 ≤ n₂`. -/
theorem sylow_number_and_ncard {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    (12 * Nat.card (Sylow 2 G) = Nat.card G) ∧ (Nat.card (Sylow 2 G) % 4 = 1) ∧
      (5 ≤ Nat.card (Sylow 2 G)) := by
  classical
  obtain ⟨hP4, _, _, hTI⟩ := Work.BSW.Cases.sylow_two_structure t s K h hk
  -- a Sylow `2`-subgroup whose underlying subgroup is `C_G(t) = H`
  obtain ⟨P₀, hP₀⟩ := Work.BSW.Cases.ncc_centralizer_isSylow h hk (Work.BSW.orderOf_t h)
  have hN12 : Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) = 12 :=
    Work.BSW.Cases.normalizer_centralizer_card hsimple hnab t s K h hk
  -- `n₂` is the index of `N_G(H)`
  have hidx : Nat.card (Sylow 2 G)
      = (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)).index := by
    rw [← hP₀]
    exact Sylow.card_eq_index_normalizer P₀
  have hcardG' : Nat.card (Sylow 2 G) * 12 = Nat.card G := by
    rw [hidx, ← hN12]
    exact Subgroup.index_mul_card _
  have hcardG : 12 * Nat.card (Sylow 2 G) = Nat.card G := by
    rw [Nat.mul_comm 12]
    exact hcardG'
  -- `4 ∣ n₂ - 1`
  have h4dvd : 4 ∣ Nat.card (Sylow 2 G) - 1 := by
    -- `H` acts on the Sylow `2`-subgroups other than `H`; the action is free
    have hstab : ∀ Q : {Q : Sylow 2 G // Q ≠ P₀},
        MulAction.stabilizer ↥(P₀ : Subgroup G) Q = ⊥ := by
      intro Q
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg
      have hgG : (g : G) • (Q : Sylow 2 G) = (Q : Sylow 2 G) := congrArg Subtype.val hg
      have hmem : (g : G) ∈ Subgroup.normalizer (((Q : Sylow 2 G) : Subgroup G) : Set G) :=
        Sylow.smul_eq_iff_mem_normalizer.mp hgG
      have hgP : (g : G) ∈ (P₀ : Subgroup G) := g.2
      have hinf : (P₀ : Subgroup G) ⊓
          Subgroup.normalizer (((Q : Sylow 2 G) : Subgroup G) : Set G) = ⊥ :=
        (IsPGroup.inf_normalizer_sylow (p := 2) (P := (P₀ : Subgroup G)) P₀.isPGroup'
          (Q : Sylow 2 G)).trans (hTI P₀ (Q : Sylow 2 G) (Ne.symm Q.2))
      have hmem' : (g : G) ∈ (⊥ : Subgroup G) := hinf ▸ Subgroup.mem_inf.mpr ⟨hgP, hmem⟩
      exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem')
    have hequiv := MulAction.selfEquivOrbitsQuotientProd (G := ↥(P₀ : Subgroup G))
      (X := {Q : Sylow 2 G // Q ≠ P₀}) hstab
    have hcardX : Nat.card {Q : Sylow 2 G // Q ≠ P₀} =
        Nat.card (Quotient (MulAction.orbitRel ↥(P₀ : Subgroup G) {Q : Sylow 2 G // Q ≠ P₀})) *
          Nat.card ↥(P₀ : Subgroup G) := by
      rw [Nat.card_congr hequiv, Nat.card_prod]
    have hcardX' : Nat.card {Q : Sylow 2 G // Q ≠ P₀} = Nat.card (Sylow 2 G) - 1 := by
      haveI : Fintype (Sylow 2 G) := Fintype.ofFinite _
      haveI : Fintype {Q : Sylow 2 G // Q = P₀} := Fintype.ofFinite _
      haveI : Fintype {Q : Sylow 2 G // ¬(Q = P₀)} := Fintype.ofFinite _
      have h1 := Fintype.card_subtype_compl (fun Q : Sylow 2 G => Q = P₀)
      rw [Fintype.card_subtype_eq P₀] at h1
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
      exact h1
    rw [← hcardX', hcardX, hP4 P₀]
    exact dvd_mul_left 4 _
  have hmod4 : Nat.card (Sylow 2 G) % 4 = 1 := by
    have hnpos : 1 ≤ Nat.card (Sylow 2 G) := by
      haveI : Nonempty (Sylow 2 G) := Sylow.nonempty
      exact Nat.card_pos
    obtain ⟨k, hk4⟩ := h4dvd
    have hk' : Nat.card (Sylow 2 G) = 4 * k + 1 := by omega
    rw [hk']
    omega
  -- `n₂ ≠ 1`
  have hne1 : Nat.card (Sylow 2 G) ≠ 1 := by
    intro h1
    haveI : Subsingleton (Sylow 2 G) := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := G)
    have hPeq : ∀ g : G, g • P = P := fun _ => Subsingleton.elim _ _
    have hnorm : Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact Sylow.smul_eq_iff_mem_normalizer.mp (hPeq g)
    haveI hPnorm : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal (P : Subgroup G) with hbot | htop
    · have hpt : Nat.card ↥(P : Subgroup G) = 1 := by rw [hbot, Subgroup.card_bot]
      have h4 := hP4 P
      omega
    · have hG4 : Nat.card G = 4 := by
        rw [← Subgroup.card_top, ← htop]
        exact hP4 P
      omega
  have hge5 : 5 ≤ Nat.card (Sylow 2 G) := by omega
  exact ⟨hcardG, hmod4, hge5⟩

end Work.BSW.Cases
