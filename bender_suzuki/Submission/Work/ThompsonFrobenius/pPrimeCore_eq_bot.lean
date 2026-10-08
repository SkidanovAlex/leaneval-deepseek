import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot
import Submission.Work.ThompsonFrobenius.ZJ_le
import Submission.Work.ThompsonFrobenius.Prelim
import Submission.Work.ThompsonFrobenius.normalizer_sup_of_coprime
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-2: `O_{p'}(G) = 1` (area `ThompsonFrobenius`)

Step GT-2 of `NOTES_LEAD_bs_thompson.md` (Farris §3.4 Step Two, second half).  Suppose that the
minimal counterexample `G` has `U := O_{p'}(G) ≠ 1`, and put `Ḡ = G ⧸ U`, `P̄ = P U / U`.

* `|U|` is coprime to `p`, so `U ⊓ P = 1` and `Z(J(P̄)) = (Z(J(P))).map π` (Z3, transport of `ZJ`
  along a homomorphism injective on `P`).
* Frattini (`normalizer_sup_of_coprime`, using `Z(J(P)) ≤ P` a `p`-group and `U ⊴ G`):
  `N_G(Z(J(P))U) = N_G(Z(J(P))) · U`, whence `N_Ḡ(Z(J(P̄))) = (N_G(Z(J(P)))).map π`
  (a `MulEquiv`/surjection argument, `Subgroup.comap_normalizer_eq_of_le_range`).
* Hence `N_Ḡ(Z(J(P̄)))` has a normal `p`-complement (`hasNormalPComplement_of_surjective`), and by
  minimality so does `Ḡ`; lifting along the normal `p'`-subgroup `U`
  (`hasNormalPComplement_of_normal_pPrime_quotient`) makes `G` `p`-nilpotent, a contradiction.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem pPrimeCore_eq_bot {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) : Submission.Blueprint.pPrimeCore p G = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_contra hne
  let U : Subgroup G := Submission.Blueprint.pPrimeCore p G
  have hUeq : U = Work.Fitting.pPrimeCore p G :=
    Work.GlaubermanZJ.pPrimeCore_eq_fitting p h.prime
  haveI hUnormal : U.Normal := by rw [hUeq]; infer_instance
  have hUcop : (Nat.card ↥U).Coprime p := by
    rw [hUeq]
    exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime h.prime).mp
      (Work.Fitting.piCore_isPiNat G (· ≠ p))
  -- the quotient is smaller
  have hcardQ : Nat.card (G ⧸ U) < Nat.card G := by
    have hmul : Nat.card (G ⧸ U) * Nat.card ↥U = Nat.card G := by
      rw [← Subgroup.index_eq_card]
      exact Subgroup.index_mul_card U
    have h1 : 1 < Nat.card ↥U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hne
    have h2 : 0 < Nat.card (G ⧸ U) := Nat.card_pos
    calc Nat.card (G ⧸ U) < Nat.card (G ⧸ U) * Nat.card ↥U := lt_mul_of_one_lt_right h2 h1
      _ = Nat.card G := hmul
  -- the quotient map
  let π : G →* G ⧸ U := QuotientGroup.mk' U
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective U
  have hker : π.ker = U := QuotientGroup.ker_mk' U
  let Pbar : Sylow p (G ⧸ U) := P.mapSurjective hπsurj
  -- `P` meets `U` trivially
  have hPU_bot : (P : Subgroup G) ⊓ U = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact hUcop.symm.pow_left k
  have hkerP : π.ker ⊓ (P : Subgroup G) = ⊥ := by
    rw [hker, inf_comm]
    exact hPU_bot
  -- Z3: `Z(J(P̄))` is the image of `Z(J(P))`
  have hZJ : (Submission.Blueprint.ZJ (P : Subgroup G)).map π
      = Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) :=
    ZJ_map_of_ker_inf_eq_bot π (P : Subgroup G) hkerP
  -- the normalizer of `Z(J(P̄))` is the image of `N_G(Z(J(P)))`
  have hnorm : Subgroup.normalizer
        (Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) : Set (G ⧸ U))
      = (Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G)).map π := by
    have hfratt : Subgroup.normalizer
          ((Submission.Blueprint.ZJ (P : Subgroup G) ⊔ U : Subgroup G) : Set G)
        = Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G) ⊔ U :=
      normalizer_sup_of_coprime hUnormal hUcop (isPGroup_of_le P.isPGroup' (ZJ_le (P : Subgroup G)))
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hUnormal]; exact le_top)
    have h1 : (Subgroup.normalizer
          (Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) : Set (G ⧸ U))).comap π
        = Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G) ⊔ U := by
      rw [Subgroup.comap_normalizer_eq_of_le_range (f := π)
        (by rw [MonoidHom.range_eq_top.mpr hπsurj]; exact le_top),
        ← hZJ, Subgroup.comap_map_eq, hker]
      exact hfratt
    have h2 : Subgroup.map π ((Subgroup.normalizer
          (Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) : Set (G ⧸ U))).comap π)
        = Subgroup.normalizer
          (Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) : Set (G ⧸ U)) := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπsurj, top_inf_eq]
    rw [← h2, h1, Subgroup.map_sup, (Subgroup.map_eq_bot_iff U).mpr (le_of_eq hker.symm), sup_bot_eq]
  -- the normalizer in the quotient has a normal `p`-complement
  have hNPC : Work.NPC.HasNormalPComplement p
      ↥(Subgroup.normalizer (Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ U)) : Set (G ⧸ U))) := by
    rw [hnorm]
    exact Work.NPC.Basic.hasNormalPComplement_of_surjective
      (MonoidHom.subgroupMap π (Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G)))
      (MonoidHom.subgroupMap_surjective π _) h.hyp
  -- minimality and lifting
  exact h.not_npc (Work.NPC.Basic.hasNormalPComplement_of_normal_pPrime_quotient hUcop
    (h.ih (G ⧸ U) hcardQ Pbar hNPC))

end Work.ThompsonFrobenius
