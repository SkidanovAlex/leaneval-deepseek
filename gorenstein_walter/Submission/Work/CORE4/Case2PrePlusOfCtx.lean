import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.Case2KOddCommutator
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2PrePlusOfCommutator
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open Subgroup
open scoped commutatorElement

/-- Bender 1981, §4 (1)–(2) for the **given** setup `B`, i.e. `Case2PrePlus B h.D` as an
unconditional consequence of the §4 configuration.

This is the piece that lets the design-pass-9 leaves (`Case2SevenImpl`, `Case2EightImpl`) be applied
to the *given* `B` and `D` rather than to an `H`-conjugate.

*Sylow conjunct.*  §4 (9) (`Case2Ctx.nine`) gives `S ≤ E(M) ≤ M`, so `S ⊓ M = S` is a Sylow
2-subgroup of `M` and `2 ∤ |M : S|` (three lines: `Subgroup.relIndex_mul_card` twice,
`Subgroup.index_mul_card` twice, cancel `|S|`, then `Sylow.not_dvd_index`).

*Conjunct (1): `K = [S ⊓ E(M), U ⊓ M]`.*  Since `S ≤ E(M)`, `S ⊓ E(M) = S` and the claim reads
`K = [S, U ⊓ M]`.  The inclusion `K ≤ [S, U ⊓ M]` is `Case2KOddCommutator` (no extra hypotheses).
For the converse, `S ≤ E ⊓ H` and `U ⊓ M ≤ M ⊓ H`, while `E ⊓ H ⊴ M ⊓ H` because `E ⊴ M`; hence
`[S, U ⊓ M] ≤ [E ⊓ H, M ⊓ H] ≤ E ⊓ H`, and also `[S, U ⊓ M] ≤ U ⊓ M` because `U ⊓ M ⊴ M ⊓ H`
and `S ≤ M ⊓ H`.  So `[S, U ⊓ M] ≤ (E ⊓ H) ⊓ (U ⊓ M) = U ⊓ E = K`, the last equality being the
proved `Work.CORE4.U_inf_layerIn_le_K` / `K_le_layerIn` pair (`K = U ⊓ E(M)`).

*Conjunct (2): `B₀ = C_{U⊓M}(S ⊓ E(M))`.*  Since `S ≤ E(M)` this reads `B₀ = C_{U⊓M}(S)`.
`C_{U⊓M}(S) ≤ B₀ = C_{U⊓M}(s)` because `s ∈ S`.  For the converse, the coprime action input
`I.toolkit.c11i` (applied to the 2-group `S` acting coprimely on the odd-order group `U ⊓ M`, with
`S ≤ N(U ⊓ M)`) gives `[S, U ⊓ M] ⊔ (U ⊓ M ⊓ C_G(S)) = U ⊓ M`, i.e. (using conjunct (1))
`K ⊔ C_{U⊓M}(S) = U ⊓ M`; also `K ⊓ C_{U⊓M}(S) = ⊥` because an element inverted and fixed by `s`
satisfies `x = x⁻¹` in the odd-order group `U ⊓ M`.  Comparing `|K| · |C_{U⊓M}(S)| = |U ⊓ M|`
(`Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot`, using `B₀ ≤ N(K)`) with
`|K| · |B₀| = |U ⊓ M|` (`Case2KB0_card`) gives `|C_{U⊓M}(S)| = |B₀|`, whence the equality. -/
theorem Case2PrePlusOfCtx :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.Case2PrePlus B h.D := by
  intro G _ _ I hbc B h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## `S ≤ E(M)`, `S ⊓ E(M) = S`, and `K = U ⊓ E(M)`
  have hSE : (B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M = (B.S : Subgroup G) :=
    inf_eq_left.mpr (S_le_layerIn h)
  have hUKE : B.U ⊓ Work.GW2.layerIn h.D.M = h.D.K :=
    le_antisymm (U_inf_layerIn_le_K I hbc B h) (le_inf (h.D.K_le_U B) (K_le_layerIn B h))
  -- ## The Sylow conjunct (1) of `Case2PrePlus`
  have hsylow : ¬ 2 ∣ ((B.S : Subgroup G) ⊓ h.D.M).relIndex h.D.M := by
    have hSleM : (B.S : Subgroup G) ≤ h.D.M := h.S_le_M
    rw [inf_eq_left.mpr hSleM]
    have h1 : (B.S : Subgroup G).relIndex h.D.M * Nat.card ↥(B.S : Subgroup G) =
        Nat.card ↥h.D.M := by
      have hh := Subgroup.relIndex_mul_card (B.S : Subgroup G) h.D.M
      rwa [inf_eq_left.mpr hSleM] at hh
    have h2 := Subgroup.index_mul_card h.D.M
    have h3 := Subgroup.index_mul_card (B.S : Subgroup G)
    have hmul : h.D.M.index * ((B.S : Subgroup G).relIndex h.D.M *
          Nat.card ↥(B.S : Subgroup G)) =
        (B.S : Subgroup G).index * Nat.card ↥(B.S : Subgroup G) := by
      rw [h1, h2, h3]
    have hkey : h.D.M.index * (B.S : Subgroup G).relIndex h.D.M =
        (B.S : Subgroup G).index :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [mul_assoc]; exact hmul)
    intro hcon
    obtain ⟨d, hd⟩ := hcon
    refine Sylow.not_dvd_index B.S ⟨h.D.M.index * d, ?_⟩
    rw [← hkey, hd]
    ring
  -- ## Bender's (1): `K = [S ⊓ E(M), U ⊓ M]`
  have hKE : h.D.K = ⁅(B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M, B.U ⊓ h.D.M⁆ := by
    have hKle : h.D.K ≤ ⁅(B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M, B.U ⊓ h.D.M⁆ := by
      rw [hSE]
      exact Case2KOddCommutator B h
    refine le_antisymm hKle ?_
    rw [hSE]
    -- membership bookkeeping for the two normal subgroups of `M ⊓ H`
    have hUMleMH : B.U ⊓ h.D.M ≤ h.D.M ⊓ B.H :=
      le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
    have hEHleMH : Work.GW2.layerIn h.D.M ⊓ B.H ≤ h.D.M ⊓ B.H :=
      le_inf (le_trans inf_le_left (layerIn_le h.D.M)) inf_le_right
    have hEHnorm : ((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf (h.D.M ⊓ B.H)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hEHleMH]
      intro a b ha hb
      obtain ⟨haE, haH⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨hbM, hbH⟩ := Subgroup.mem_inf.mp hb
      have hbaE : b * a * b⁻¹ ∈ Work.GW2.layerIn h.D.M :=
        (Subgroup.normal_subgroupOf_iff (layerIn_le h.D.M)).mp h.layerIn_subgroupOf_normal
          a b haE hbM
      exact Subgroup.mem_inf.mpr ⟨hbaE, B.H.mul_mem (B.H.mul_mem hbH haH) (B.H.inv_mem hbH)⟩
    have hEHconj : ∀ n ∈ h.D.M ⊓ B.H, ∀ y ∈ Work.GW2.layerIn h.D.M ⊓ B.H,
        n * y * n⁻¹ ∈ Work.GW2.layerIn h.D.M ⊓ B.H := fun n hn y hy =>
      (Subgroup.normal_subgroupOf_iff hEHleMH).mp hEHnorm y n hy hn
    have hUMconj : ∀ n ∈ h.D.M ⊓ B.H, ∀ y ∈ B.U ⊓ h.D.M,
        n * y * n⁻¹ ∈ B.U ⊓ h.D.M := fun n hn y hy =>
      (Subgroup.normal_subgroupOf_iff hUMleMH).mp h.U_inf_M_normal y n hy hn
    -- `[S, U ⊓ M] ≤ E ⊓ H`
    have hcommEH : ⁅(B.S : Subgroup G), B.U ⊓ h.D.M⁆ ≤ Work.GW2.layerIn h.D.M ⊓ B.H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haEH : a ∈ Work.GW2.layerIn h.D.M ⊓ B.H :=
        ⟨S_le_layerIn h ha, B.S_le_H ha⟩
      have hbMH : b ∈ h.D.M ⊓ B.H :=
        ⟨(Subgroup.mem_inf.mp hb).2, B.U_le_H (Subgroup.mem_inf.mp hb).1⟩
      have h1 : b * a⁻¹ * b⁻¹ ∈ Work.GW2.layerIn h.D.M ⊓ B.H :=
        hEHconj b hbMH a⁻¹ (Subgroup.inv_mem _ haEH)
      rw [commutatorElement_def,
        show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) from by group]
      exact (Work.GW2.layerIn h.D.M ⊓ B.H).mul_mem haEH h1
    -- `[S, U ⊓ M] ≤ U ⊓ M`
    have hcommUM : ⁅(B.S : Subgroup G), B.U ⊓ h.D.M⁆ ≤ B.U ⊓ h.D.M := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haMH : a ∈ h.D.M ⊓ B.H := ⟨h.S_le_M ha, B.S_le_H ha⟩
      have h1 : a * b * a⁻¹ ∈ B.U ⊓ h.D.M := hUMconj a haMH b hb
      rw [commutatorElement_def,
        show a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹) * b⁻¹ from by group]
      exact (B.U ⊓ h.D.M).mul_mem h1 (Subgroup.inv_mem _ hb)
    -- `(E ⊓ H) ⊓ (U ⊓ M) = U ⊓ E(M) = K`
    have hinter : (Work.GW2.layerIn h.D.M ⊓ B.H) ⊓ (B.U ⊓ h.D.M) = h.D.K := by
      rw [← hUKE]
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨hxE, _⟩, hxU, _⟩
        exact ⟨hxU, hxE⟩
      · rintro ⟨hxU, hxE⟩
        exact ⟨⟨hxE, B.U_le_H hxU⟩, hxU, layerIn_le h.D.M hxE⟩
    exact le_trans (le_inf hcommEH hcommUM) (le_of_eq hinter)
  -- ## Bender's (2): `B₀ = C_{U ⊓ M}(S ⊓ E(M))`
  have hB0 : h.D.B0 = (B.U ⊓ h.D.M) ⊓
      Subgroup.centralizer ((((B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M : Subgroup G)) : Set G) := by
    rw [hSE]
    have hsS : h.D.s ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp h.D.s_mem).1
    have hUModd : Odd (Nat.card ↥(B.U ⊓ h.D.M)) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
    set Y : Subgroup G := (B.U ⊓ h.D.M) ⊓
      Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hYdef
    have hYleB0 : Y ≤ h.D.B0 := by
      rw [h.D.B0_def]
      exact le_inf inf_le_left
        (le_trans inf_le_right (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsS)))
    have hYnorm : Y ≤ Subgroup.normalizer (h.D.K : Set G) :=
      le_trans hYleB0 (Case2KB0_b0_le_normalizer B h)
    have hKYbot : h.D.K ⊓ Y = ⊥ :=
      le_bot_iff.mp (le_trans (inf_le_inf_left h.D.K hYleB0)
        (le_of_eq (Case2KB0_inf B h)))
    -- coprime action of the `2`-group `S` on the odd-order group `U ⊓ M`
    have hc11i := I.toolkit.c11i G 2 (B.S : Subgroup G) (B.U ⊓ h.D.M) (B.S).isPGroup'
      (Nat.coprime_two_left.mpr hUModd) (Case2SLeNormUinfM B h)
    have hsup : h.D.K ⊔ Y = B.U ⊓ h.D.M := by
      have hKcomm : h.D.K = ⁅(B.S : Subgroup G), B.U ⊓ h.D.M⁆ := by
        simpa only [hSE] using hKE
      rw [hKcomm]
      exact hc11i.2
    have hcard_sup : Nat.card ↥(h.D.K ⊔ Y) = Nat.card ↥h.D.K * Nat.card ↥Y :=
      Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hYnorm hKYbot
    have hcard : Nat.card ↥Y = Nat.card ↥h.D.B0 := by
      have h2 : Nat.card ↥h.D.K * Nat.card ↥Y =
          Nat.card ↥h.D.K * Nat.card ↥h.D.B0 := by
        rw [← hcard_sup, hsup, Case2KB0_card B h]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    exact (Subgroup.eq_of_le_of_card_ge hYleB0 (le_of_eq hcard.symm)).symm
  exact ⟨hsylow, hKE, hB0⟩

end Work.CORE4
