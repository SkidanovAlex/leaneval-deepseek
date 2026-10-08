import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.piCore_isPiNat
import Submission.Work.HallHigman.isPSolvable_quotient_prime
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.HallHigman.GLCore.exists_normal_pGroup_le
import Submission.Work.HallHigman.GLCore.exists_characteristic_pGroup_of_quotient_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.HallHigman.GLCore

open Classical

/-- **L15 of the GL-core design** (the entry point of the proof of the order-`p` form of
Hall--Higman B, see `NOTES_LEAD_ft_hallhigman.md` §2.1): in a finite `p`-solvable group with
`O_p(G) = 1`, the centralizer of `O_{p'}(G)` is contained in `O_{p'}(G)`.

Proof: let `C = C_G(O_{p'}(G))` and suppose `C ⊄ O_{p'}(G)`.  Then `C·O_{p'}/O_{p'}` is a nontrivial
normal subgroup of `G/O_{p'}`, and `O_{p'}(G/O_{p'}) = 1`; walking up the `p`-solvable series of
`G/O_{p'}`, the first term meeting `C·O_{p'}/O_{p'}` nontrivially is a nontrivial normal `p`-subgroup
of `G/O_{p'}` there.  Its preimage has the form `M = O_{p'}(G)·(M ∩ C)`, where `M ∩ C` has central
`p'`-subgroup `O_{p'}(G) ∩ C` and `p`-group quotient, so its Sylow `p`-subgroup is normal, hence
characteristic in `M ∩ C`, hence normal in `G` — and nontrivial, contradicting `O_p(G) = 1`. -/
lemma centralizer_opCore_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hps : Work.HallHigman.IsPSolvable p G) (hOp : Work.HallHigman.pCore p G = ⊥) :
    Subgroup.centralizer (Work.HallHigman.opCore p G : Set G) ≤ Work.HallHigman.opCore p G := by
  classical
  have hp : p.Prime := Fact.out
  set Q : Subgroup G := Work.HallHigman.opCore p G with hQdef
  set C : Subgroup G := Subgroup.centralizer (Q : Set G) with hCdef
  haveI hQnorm : Q.Normal := Work.HallHigman.opCore_normal
  haveI hCnorm : C.Normal := Subgroup.normal_centralizer (H := Q)
  by_contra hcon
  -- The image of `C ⊔ Q = C_G(Q)·O_{p'}(G)` in `G ⧸ O_{p'}(G)` is a nontrivial normal subgroup
  let Gq := G ⧸ Q
  let Nbar : Subgroup Gq := (C ⊔ Q).map (QuotientGroup.mk' Q)
  have hNbar_normal : Nbar.Normal := by
    have : (C ⊔ Q).Normal := inferInstance
    exact this.map _ (QuotientGroup.mk'_surjective Q)
  have hNbar_ne : Nbar ≠ ⊥ := by
    intro hh
    apply hcon
    have h2 : C ⊔ Q ≤ (QuotientGroup.mk' Q).ker := (Subgroup.map_eq_bot_iff (C ⊔ Q)).mp hh
    rw [QuotientGroup.ker_mk'] at h2
    exact le_sup_left.trans h2
  have hpsq : Work.HallHigman.IsPSolvable p Gq :=
    Work.HallHigman.isPSolvable_quotient_prime hp Q hps
  have hopq : Work.HallHigman.opCore p Gq = ⊥ :=
    Work.Fitting.piCore_quotient_eq_bot (fun q => q ≠ p) G
  -- L15a: a nontrivial normal `p`-subgroup inside that image
  obtain ⟨Mbar, hMbar_norm, hMbar_le, hMbar_ne, hMbar_pi⟩ :=
    exists_normal_pGroup_le (N := Nbar) hpsq hopq hNbar_normal hNbar_ne
  -- lift it back to `G`
  let M : Subgroup G := Mbar.comap (QuotientGroup.mk' Q)
  haveI hMnorm : M.Normal := Subgroup.normal_comap _
  have hQleM : Q ≤ M := by
    intro q hq
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff q).mpr hq]
    exact Mbar.one_mem
  have hMleD : M ≤ C ⊔ Q := by
    intro m hm
    have h1 : m ∈ Subgroup.comap (QuotientGroup.mk' Q)
        (Subgroup.map (QuotientGroup.mk' Q) (C ⊔ Q)) :=
      Subgroup.mem_comap.mpr (hMbar_le (Subgroup.mem_comap.mp hm))
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_assoc, sup_idem] at h1
  -- `X = M ∩ C_G(Q)`, so that `M = X ⊔ Q`
  let X : Subgroup G := M ⊓ C
  haveI hXnorm : X.Normal := inferInstance
  have hM_eq : M = X ⊔ Q := by
    refine le_antisymm ?_ (sup_le inf_le_left hQleM)
    intro m hm
    obtain ⟨c, hc, q, hq, hcq⟩ := (Subgroup.mem_sup_of_normal_right (s := C) (t := Q)).mp (hMleD hm)
    have hcM : c ∈ M := by
      have : c = m * q⁻¹ := by rw [← hcq]; group
      rw [this]
      exact M.mul_mem hm (M.inv_mem (hQleM hq))
    rw [← hcq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hcM, hc⟩) hq
  -- `X` has central `p'`-subgroup `Z = X ∩ Q` and `p`-group quotient `X/(X∩Q) ≅ M̄`
  let Z : Subgroup ↥X := Q.subgroupOf X
  haveI hZnorm : Z.Normal := hQnorm.subgroupOf X
  have hZc : Z ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : (w : G) ∈ C := (Subgroup.mem_inf.mp w.2).2
    have hzq : (z : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz
    exact (Subgroup.mem_centralizer_iff.mp hw (z : G) hzq).symm
  have hZp : Work.HallHigman.IsPiNat (· ≠ p) (Nat.card ↥Z) := by
    refine Work.HallHigman.IsPiNat.of_dvd
      (Work.HallHigman.piCore_isPiNat (π := (· ≠ p)) (G := G)) ?_
    have heq : Nat.card ↥(Q.subgroupOf X) = Nat.card ↥(Q ⊓ X) := by
      rw [← Subgroup.inf_subgroupOf_right Q X]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Q ⊓ X) (K := X) inf_le_right).toEquiv
    rw [heq]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hq : IsPGroup p (↥X ⧸ Z) := by
    let φ : ↥X →* Gq := (QuotientGroup.mk' Q).comp X.subtype
    have hker : φ.ker = Z := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    have hrange : φ.range = Mbar := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map (g := QuotientGroup.mk' Q)
        (f := X.subtype) (K := ⊤), Subgroup.map_top, Subgroup.range_subtype]
      have hMmap : Subgroup.map (QuotientGroup.mk' Q) M = Mbar :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) Mbar
      rw [← hMmap, hM_eq, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff Q).mpr (le_of_eq (QuotientGroup.ker_mk' Q).symm), sup_bot_eq]
    have hMbar_pGroup : IsPGroup p ↥Mbar :=
      (Work.Fitting.isPiNat_prime_iff_isPGroup hp Mbar).mp hMbar_pi
    have hquot : IsPGroup p (↥X ⧸ φ.ker) :=
      IsPGroup.of_equiv (by rw [hrange]; exact hMbar_pGroup)
        (QuotientGroup.quotientKerEquivRange φ).symm
    exact IsPGroup.of_equiv hquot (QuotientGroup.quotientMulEquivOfEq hker)
  have hne : Z ≠ ⊤ := by
    intro htop
    apply hMbar_ne
    have hXleQ : X ≤ Q := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥X) ∈ Z := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
    have hMQ : M ≤ Q := by rw [hM_eq]; exact sup_le hXleQ le_rfl
    have hMbar_bot : Mbar = ⊥ := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) Mbar,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hMQ
    exact hMbar_bot
  -- a nontrivial normal `p`-subgroup of `X`
  obtain ⟨P, hPchar, hPp, hPne⟩ :=
    exists_characteristic_pGroup_of_quotient_isPGroup (X := ↥X) (Z := Z) hZc hZp hq hne
  -- characteristic in the normal subgroup `X`, hence normal in `G`
  have hPmap_normal : (P.map X.subtype).Normal := Work.Fitting.map_characteristic_normal hXnorm hPchar
  have hPmap_ne : P.map X.subtype ≠ ⊥ := by
    intro hh
    apply hPne
    have hle : P ≤ X.subtype.ker := (Subgroup.map_eq_bot_iff P).mp hh
    rw [Subgroup.ker_subtype] at hle
    exact le_bot_iff.mp hle
  have hPmap_pi : Work.HallHigman.IsPiNat (· = p) (Nat.card ↥(P.map X.subtype)) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact (Work.Fitting.isPiNat_prime_iff_isPGroup hp P).mpr hPp
  have hle := Work.HallHigman.le_pCore hPmap_normal hPmap_pi
  rw [hOp] at hle
  exact hPmap_ne (le_bot_iff.mp hle)

end Work.HallHigman.GLCore
