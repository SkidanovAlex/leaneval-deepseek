import Mathlib
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2RelIndexMH
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.PSL2.Card

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

set_option linter.style.haveILetI false

/-- The involution centralizer `C_E(t)` of the §4 configuration, for `E = E(M) ≅ L₂(q)`,
computed through an *explicit* isomorphism `φ : E ≃* PSL(2, q)`:

`|E ⊓ C_G(t)| = 2 n` where `2 n = q ∓ 1` and `q = p ^ k`.

This is the `l2cent` computation of `Case2Parity`/`Case2RelIndexMH`, isolated so that the
target can use the isomorphism supplied by its own hypotheses rather than the one produced
internally by `Case2Ctx.nine`. -/
theorem card_layerIn_inter_H_of_iso {G : Type} [Group G] [Finite G]
    (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {p k : ℕ} (hp : Fact p.Prime) (hpodd : Odd p) (h5 : 5 ≤ p ^ k)
    (φ : Work.GW2.layerIn h.D.M ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :
    ∃ n : ℕ, (2 * n = p ^ k - 1 ∨ 2 * n = p ^ k + 1) ∧
      Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) = 2 * n := by
  classical
  haveI := hp
  have htE : B.t ∈ Work.GW2.layerIn h.D.M := h.D.t_mem
  have htE2 : orderOf (⟨B.t, htE⟩ : ↥(Work.GW2.layerIn h.D.M)) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht' : orderOf (φ ⟨B.t, htE⟩) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact htE2
  obtain ⟨n, hn, ⟨ψ⟩⟩ :=
    I.toolkit.l2cent p k hpodd h5 (φ ⟨B.t, htE⟩) ht'
  refine ⟨n, hn, ?_⟩
  have h1 : Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf (Work.GW2.layerIn h.D.M)) =
      Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
        Set ↥(Work.GW2.layerIn h.D.M))) := by
    rw [subgroupOf_inf_centralizer (Work.GW2.layerIn h.D.M) B.t htE]
  have h2 : Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
        Set ↥(Work.GW2.layerIn h.D.M))) =
      Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
        Set (PSL(2, GaloisField p k)))) :=
    card_centralizer_singleton_map φ ⟨B.t, htE⟩
  have h3 : Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
        Set (PSL(2, GaloisField p k)))) = 2 * n := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  calc Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H)
      = Nat.card ↥((Work.GW2.layerIn h.D.M ⊓ B.H).subgroupOf
          (Work.GW2.layerIn h.D.M)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    _ = Nat.card ↥(Subgroup.centralizer ({⟨B.t, htE⟩} :
          Set ↥(Work.GW2.layerIn h.D.M))) := h1
    _ = Nat.card ↥(Subgroup.centralizer ({φ ⟨B.t, htE⟩} :
          Set (PSL(2, GaloisField p k)))) := h2
    _ = 2 * n := h3

theorem KmulS0Tied {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {pF kF : ℕ} (hpF : Fact pF.Prime) (hpFodd : Odd pF) (h7 : 7 ≤ pF ^ kF)
    (φ : Work.GW2.layerIn h.D.M ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) :
    (2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) = pF ^ kF + 1) ∨
      (2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) = pF ^ kF - 1) := by
  classical
  haveI := hpF
  have h5 : 5 ≤ pF ^ kF := le_trans (by norm_num) h7
  -- `|C_E(t)| = 2n` with `2n = q ∓ 1`, computed through the given isomorphism `φ`.
  obtain ⟨n, hn, hcardC⟩ := card_layerIn_inter_H_of_iso I h hpF hpFodd h5 φ
  -- Bender §4, p. 227: `|C_E(t)| = 2 |K| |S₀|`.
  have hEH := Case2EHcard G I hbc B h
  have h2 : 2 * (Nat.card ↥h.D.K * Nat.card ↥B.S0) = 2 * n := by rw [← hEH, hcardC]
  rcases hn with hn | hn
  · right; omega
  · left; omega

end Work.CORE4
