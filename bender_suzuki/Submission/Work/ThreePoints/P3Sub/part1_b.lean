import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.Reductions.OddResidual
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf
import Submission.Work.ThreePoints.P3Sub.p3F_subgroupOf_normalizer_normal
import Submission.Work.ThreePoints.P3Sub.modelSplitB
import Submission.Work.ThreePoints.p3cd_gen_by_involutions
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.ThreePoints.p3cd_oddCore_eq_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3Sub

open Submission.Blueprint
open Work.ThreePoints

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Elementary helpers -/

/-- An element whose square is `1` and which is not `1` has order `2`. -/
theorem orderOf_eq_two_of_ne_one_mul_self {x : G} (h1 : x ≠ 1) (h2 : x * x = 1) :
    orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-- A subgroup containing an involution has even order. -/
theorem even_card_of_mem_involution {K : Subgroup G} {u : G} (hu : u ∈ K)
    (h2 : orderOf u = 2) : Even (Nat.card K) := by
  rw [even_iff_two_dvd]
  have h := Subgroup.orderOf_dvd_natCard K hu
  rwa [h2] at h

/-- `F = O^{2'}(C_G(X))` is contained in `N_G(X)`. -/
theorem p3F_le_normalizer (X : Subgroup G) :
    Work.ThreePoints.p3F X ≤ Subgroup.normalizer (X : Set G) :=
  (Work.ThreePoints.p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))

/-- `N_G(X) ≤ N_G(O^{2'}(C_G(X)))`. -/
theorem normalizer_le_normalizer_p3F (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer ((Work.ThreePoints.p3F X) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (p3F_le_normalizer X)).mp
    (Work.ThreePoints.p3F_subgroupOf_normalizer_normal X)

/-- Conjugation by `f ∈ O^{2'}(C_G(X))` fixes `O^{2'}(C_G(X))`. -/
theorem conj_eq_self_of_mem_p3F {X : Subgroup G} {f : G} (hf : f ∈ Work.ThreePoints.p3F X) :
    Submission.Blueprint.conj f (Work.ThreePoints.p3F X) = Work.ThreePoints.p3F X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_p3F X
    (p3F_le_normalizer X hf))

/-! ## 1. `Even |O^{2'}(C_G(X)) ⊓ H|`

The four-group in `F = O^{2'}(C_G(X))` (`hfour`) contains an involution `u`; if `u ∈ H` we are
done.  Otherwise the involution `u ∉ H` has a unique fixed point `ω` on `Ω = G ⧸ H`, and because
the elements of the four-group commute pairwise, all of the four-group fixes `ω` (and
`ω ∈ Ω_X`).  Since `F` is transitive on `Ω_X`, the point stabiliser `F ⊓ Stab(ω)` is conjugate in
`F` to `F ⊓ H`, so the latter contains a four-group, in particular has even order. -/

theorem even_card_p3F_inf_H {H X : Subgroup G} (hH : IsStronglyEmbedded H) (hXH : X ≤ H)
    (htr : Work.DoubleTransitivity.IsTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X))
    (hfour : Submission.Blueprint.HasFourGroup (Work.ThreePoints.p3F X)) :
    Even (Nat.card (Work.ThreePoints.p3F X ⊓ H : Subgroup G)) := by
  classical
  obtain ⟨a, b, ha2, hb2, hab_ne, hab_comm⟩ := hfour
  have hcoa : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha2
  have hcob : orderOf (b : G) = 2 := (Subgroup.orderOf_coe b).trans hb2
  have haa : (a : G) * (a : G) = 1 := mul_self_eq_one_of_orderOf_eq_two hcoa
  have hbb : (b : G) * (b : G) = 1 := mul_self_eq_one_of_orderOf_eq_two hcob
  have hcommG : (a : G) * (b : G) = (b : G) * (a : G) := by
    have h := congrArg (fun x : ↥(Work.ThreePoints.p3F X) => (x : G)) hab_comm
    simpa using h
  have hab_sq : ((a : G) * (b : G)) * ((a : G) * (b : G)) = 1 := by
    have hcommG' : (b : G) * (a : G) = (a : G) * (b : G) := hcommG.symm
    rw [show ((a : G) * (b : G)) * ((a : G) * (b : G))
          = (a : G) * ((b : G) * (a : G)) * (b : G) from by group, hcommG']
    rw [show (a : G) * ((a : G) * (b : G)) * (b : G)
          = ((a : G) * (a : G)) * ((b : G) * (b : G)) from by group, haa, hbb, one_mul]
  have hab_ne' : (a : G) * (b : G) ≠ 1 := by
    intro h
    apply hab_ne
    have h1 : (b : G) = (a : G) * ((a : G) * (b : G)) := by
      rw [← mul_assoc, haa, one_mul]
    rw [h, mul_one] at h1
    exact Subtype.ext h1.symm
  have hab2 : orderOf ((a : G) * (b : G)) = 2 :=
    orderOf_eq_two_of_ne_one_mul_self hab_ne' hab_sq
  by_cases haH : (a : G) ∈ H
  · exact even_card_of_mem_involution ⟨a.2, haH⟩ hcoa
  by_cases hbH : (b : G) ∈ H
  · exact even_card_of_mem_involution ⟨b.2, hbH⟩ hcob
  by_cases habH : (a : G) * (b : G) ∈ H
  · exact even_card_of_mem_involution ⟨(Work.ThreePoints.p3F X).mul_mem a.2 b.2, habH⟩ hab2
  · -- all three non-trivial elements lie outside `H`
    have hbender : Work.DoubleTransitivity.IsBender H :=
      ((Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH).2
    obtain ⟨ω, hωfix, hωuniq⟩ := Work.DoubleTransitivity.Sec1.unique_fixed hbender hcoa
    have hωX : ω ∈ Submission.Blueprint.fixedPts H X := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      intro x hx
      rw [MulAction.mem_stabilizer_iff]
      have hxa : (a : G) * x = x * (a : G) :=
        (Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer X a.2) x hx).symm
      have h1 : (a : G) • (x • ω) = x • ω := by
        rw [← mul_smul, hxa, mul_smul, hωfix]
      exact hωuniq (x • ω) h1
    have h1X : Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
      (Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH
    obtain ⟨f, hfF, hf⟩ := htr (Work.DoubleTransitivity.pt H) h1X ω hωX
    have hstab : MulAction.stabilizer G ω = Submission.Blueprint.conj f H := by
      have h1 : f • Work.DoubleTransitivity.pt H = (f : G ⧸ H) :=
        Work.DoubleTransitivity.smul_pt f H
      rw [← hf, h1, Work.ThreePoints.stabilizer_mk]
    have hbω : (b : G) • ω = ω := by
      have h1 : (a : G) • ((b : G) • ω) = (b : G) • ω := by
        rw [← mul_smul, hcommG, mul_smul, hωfix]
      exact hωuniq ((b : G) • ω) h1
    have hconjF : Submission.Blueprint.conj f (Work.ThreePoints.p3F X) =
        Work.ThreePoints.p3F X := conj_eq_self_of_mem_p3F hfF
    have hstab_eq : (Work.ThreePoints.p3F X ⊓ MulAction.stabilizer G ω : Subgroup G)
        = Submission.Blueprint.conj f (Work.ThreePoints.p3F X ⊓ H) := by
      rw [hstab, Work.ThreePoints.conj_inf, hconjF]
    have hcard : Nat.card ↥(Submission.Blueprint.conj f (Work.ThreePoints.p3F X ⊓ H))
        = Nat.card ↥(Work.ThreePoints.p3F X ⊓ H) :=
      Subgroup.card_map_of_injective (MulAut.conj f).injective
    have hmain : Even (Nat.card (Work.ThreePoints.p3F X ⊓ MulAction.stabilizer G ω : Subgroup G)) :=
      even_card_of_mem_involution
        ⟨a.2, MulAction.mem_stabilizer_iff.mpr hωfix⟩ hcoa
    rwa [hstab_eq, hcard] at hmain

/-- `Even |F ⊓ M|` for `F = O^{2'}(C_G(X))` and every point `M = H^f` with `f ∈ F` (the point
stabilisers of `Ω_X` are conjugate in the transitive group `F`). -/
theorem even_card_p3F_inf_conj_of_mem {H X : Subgroup G} (hH : IsStronglyEmbedded H)
    (hXH : X ≤ H)
    (htr : Work.DoubleTransitivity.IsTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X))
    (hfour : Submission.Blueprint.HasFourGroup (Work.ThreePoints.p3F X))
    {f : G} (hfF : f ∈ Work.ThreePoints.p3F X) :
    Even (Nat.card (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H : Subgroup G)) := by
  have heq : (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H : Subgroup G)
      = Submission.Blueprint.conj f (Work.ThreePoints.p3F X ⊓ H) := by
    rw [Work.ThreePoints.conj_inf, conj_eq_self_of_mem_p3F hfF]
  rw [heq, Subgroup.card_map_of_injective (MulAut.conj f).injective]
  exact even_card_p3F_inf_H hH hXH htr hfour

/-- `F ⊓ M` is strongly embedded in `F = O^{2'}(C_G(X))` for every `M = H^f` with `f ∈ F`. -/
theorem stronglyEmbedded_p3F_inf_conj_of_mem {H X : Subgroup G} (hH : IsStronglyEmbedded H)
    (hXH : X ≤ H)
    (htr : Work.DoubleTransitivity.IsTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X))
    (hfour : Submission.Blueprint.HasFourGroup (Work.ThreePoints.p3F X))
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ Submission.Blueprint.centD H t)
    {f : G} (hfF : f ∈ Work.ThreePoints.p3F X) :
    IsStronglyEmbedded ((Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H).subgroupOf
      (Work.ThreePoints.p3F X)) := by
  have heven := even_card_p3F_inf_conj_of_mem hH hXH htr hfour hfF
  have htF : t ∈ Work.ThreePoints.p3F X := Work.ThreePoints.mem_p3F_t ht hX
  have heq : (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H : Subgroup G)
      = Submission.Blueprint.conj f (Work.ThreePoints.p3F X ⊓ H) := by
    rw [Work.ThreePoints.conj_inf, conj_eq_self_of_mem_p3F hfF]
  have hcard1 : Nat.card ↥(Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H)
      = Nat.card ↥(Work.ThreePoints.p3F X ⊓ H) := by
    rw [heq, Subgroup.card_map_of_injective (MulAut.conj f).injective]
  have hne : (Submission.Blueprint.conj f H ⊓ Work.ThreePoints.p3F X : Subgroup G)
      ≠ Work.ThreePoints.p3F X := by
    intro hEq0
    have hEq : (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H : Subgroup G)
        = Work.ThreePoints.p3F X := by rwa [inf_comm] at hEq0
    have hsub : (Work.ThreePoints.p3F X ⊓ H : Subgroup G) = Work.ThreePoints.p3F X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [← hcard1, hEq])
    exact htH ((show Work.ThreePoints.p3F X ≤ H by rw [← hsub]; exact inf_le_right) htF)
  rw [show (Work.ThreePoints.p3F X ⊓ Submission.Blueprint.conj f H : Subgroup G)
      = (Submission.Blueprint.conj f H ⊓ Work.ThreePoints.p3F X) from inf_comm _ _]
  refine Work.Reductions.stronglyEmbedded_subgroupOf
    (Work.ThreePoints.conj_stronglyEmbedded hH f) hne ?_
  rw [inf_comm]
  exact heven

/-- Every point of `Ω_X` is conjugate to `pt H` by an element of `F = O^{2'}(C_G(X))`. -/
theorem exists_mem_p3F_conj_eq {H X : Subgroup G} (hXH : X ≤ H)
    (htr : Work.DoubleTransitivity.IsTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X))
    {g : G} (hg : X ≤ Submission.Blueprint.conj g H) :
    ∃ f ∈ Work.ThreePoints.p3F X, Submission.Blueprint.conj g H = Submission.Blueprint.conj f H := by
  have hωX : ((g : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X :=
    (Work.DoubleTransitivity.mk_mem_fixedPts_iff X H g).mpr hg
  have h1X : Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
    (Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH
  obtain ⟨f, hfF, hf⟩ := htr (Work.DoubleTransitivity.pt H) h1X ((g : G) : G ⧸ H) hωX
  refine ⟨f, hfF, ?_⟩
  have hfg : ((f : G) : G ⧸ H) = ((g : G) : G ⧸ H) := by
    rw [← Work.DoubleTransitivity.smul_pt f H]; exact hf
  rw [← Work.ThreePoints.stabilizer_mk H g, ← Work.ThreePoints.stabilizer_mk H f, hfg]

/-! ## 2. `O^{2'}(O^{2'}(C_G(X))) = O^{2'}(C_G(X))` and the quotient by `O_{2'}` -/

/-- `O^{2'}` is transported by a group isomorphism. -/
theorem map_oddResidual_mulEquiv_b {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) :
    (Submission.Blueprint.oddResidual A).map (e : A →* B) = Submission.Blueprint.oddResidual B := by
  apply le_antisymm
  · have hN : ((Submission.Blueprint.oddResidual B).comap (e : A →* B)).Normal :=
      (Work.Reductions.oddResidual_basic (G := B)).1.comap _
    have hidx : ((Submission.Blueprint.oddResidual B).comap (e : A →* B)).index =
        (Submission.Blueprint.oddResidual B).index :=
      Subgroup.index_comap_of_surjective _ e.surjective
    have hle : Submission.Blueprint.oddResidual A ≤
        (Submission.Blueprint.oddResidual B).comap (e : A →* B) :=
      (Work.Reductions.oddResidual_basic (G := A)).2.2.1 _
        hN (hidx ▸ (Work.Reductions.oddResidual_basic (G := B)).2.1)
    rintro _ ⟨a, ha, rfl⟩
    exact hle ha
  · have hN : ((Submission.Blueprint.oddResidual A).map (e : A →* B)).Normal :=
      (Work.Reductions.oddResidual_basic (G := A)).1.map (e : A →* B) e.surjective
    have hidx : ((Submission.Blueprint.oddResidual A).map (e : A →* B)).index =
        (Submission.Blueprint.oddResidual A).index := Subgroup.index_map_equiv _ e
    exact (Work.Reductions.oddResidual_basic (G := B)).2.2.1 _
      hN (hidx ▸ (Work.Reductions.oddResidual_basic (G := A)).2.1)

/-- `O^{2'}(O^{2'}(C_G(X))) = O^{2'}(C_G(X))`: the group `F` of Prop. 3 has no proper normal
subgroup of odd index. -/
theorem oddResidual_p3F_eq_top_b (X : Subgroup G) :
    Submission.Blueprint.oddResidual ↥(Work.ThreePoints.p3F X) = ⊤ := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  have he : ↥(Submission.Blueprint.oddResidual C) ≃*
      ↥((Submission.Blueprint.oddResidual C).map C.subtype) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  have key := map_oddResidual_mulEquiv_b he
  rw [Work.Reductions.oddResidual_self_eq_top (G := ↥C)] at key
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr he.surjective] at key
  exact key.symm

/-- A group with `O^{2'}(G) = G`: the `L` of `BenderConclusion G` is `G` itself, so Theorem B
gives `G/O_{2'}(G) ≅ Y` for a simple Bender group `Y`. -/
theorem benderConclusion_quotient_of_oddResidual_eq_top_b {F : Type} [Group F] [Finite F]
    (hBC : Submission.Blueprint.BenderConclusion F)
    (hres : Submission.Blueprint.oddResidual F = ⊤) :
    ∃ (Y : Type) (_ : Group Y) (φ : F →* Y), Function.Surjective φ ∧
      φ.ker = Submission.Blueprint.oddCore F ∧
      LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y := by
  obtain ⟨L, hLn, _hcore, hLidx, Y, hYgrp, φ, hφsurj, hφker, hY⟩ := hBC
  letI : Group Y := hYgrp
  have hLtop : L = ⊤ := by
    have hle : Submission.Blueprint.oddResidual F ≤ L :=
      (Work.Reductions.oddResidual_basic (G := F)).2.2.1 L hLn hLidx
    rw [hres] at hle
    exact top_le_iff.mp hle
  subst hLtop
  refine ⟨Y, hYgrp, φ.comp ((Subgroup.topEquiv (G := F)).symm : F →* ↥(⊤ : Subgroup F)),
    hφsurj.comp (Subgroup.topEquiv (G := F)).symm.surjective, ?_, hY⟩
  rw [← MonoidHom.comap_ker φ ((Subgroup.topEquiv (G := F)).symm : F →* ↥(⊤ : Subgroup F)),
    hφker]
  ext x
  show (((Subgroup.topEquiv (G := F)).symm x : ↥(⊤ : Subgroup F)) : F) ∈
    Submission.Blueprint.oddCore F ↔ x ∈ Submission.Blueprint.oddCore F
  rw [Subgroup.topEquiv_symm_apply_coe]

/-! ## 3. `S ◁ B` and `S` is the unique Sylow `2`-subgroup of `B` -/

/-- If `S ≤ B` is a normal Sylow `2`-subgroup of `B` and `h` normalises `B`, then `h` normalises
`S`: every `2`-subgroup of `B` is contained in `S`. -/
theorem conj_eq_self_of_le_normalizer_of_odd_index {B S : Subgroup G} (hSB : S ≤ B)
    (hS2 : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf B).index)
    (hSnorm : B ≤ Subgroup.normalizer (S : Set G))
    {h : G} (hhB : Submission.Blueprint.conj h B = B) :
    Submission.Blueprint.conj h S = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hSnorm
  have hle : Submission.Blueprint.conj h S ≤ B :=
    (Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hSB).trans (le_of_eq hhB)
  have hS'2 : IsPGroup 2 ↥((Submission.Blueprint.conj h S).subgroupOf B) :=
    (hS2.map (MulAut.conj h).toMonoidHom).of_equiv
      ((Subgroup.subgroupOfEquivOfLe hle).symm)
  have hS2' : IsPGroup 2 ↥(S.subgroupOf B) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  have hidx' : ¬ 2 ∣ ((Submission.Blueprint.conj h S).subgroupOf B).index := by
    have hcard1 : Nat.card ↥(S.subgroupOf B) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
    have hcard2 : Nat.card ↥((Submission.Blueprint.conj h S).subgroupOf B) =
        Nat.card ↥(Submission.Blueprint.conj h S) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hcard3 : Nat.card ↥(Submission.Blueprint.conj h S) = Nat.card ↥S :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    have e1 : Nat.card ↥S * (S.subgroupOf B).index = Nat.card ↥B := by
      have h := Subgroup.card_mul_index (S.subgroupOf B)
      rwa [hcard1] at h
    have e2 : Nat.card ↥S * ((Submission.Blueprint.conj h S).subgroupOf B).index =
        Nat.card ↥B := by
      have h := Subgroup.card_mul_index ((Submission.Blueprint.conj h S).subgroupOf B)
      rwa [hcard2, hcard3] at h
    have hthis : (S.subgroupOf B).index =
        ((Submission.Blueprint.conj h S).subgroupOf B).index :=
      Nat.mul_left_cancel (Nat.card_pos (α := ↥S)) (e1.trans e2.symm)
    rw [← hthis]
    exact hidx
  have hle' : S.subgroupOf B ≤ (Submission.Blueprint.conj h S).subgroupOf B :=
    (IsPGroup.le_sylow_of_normal hS2' (hS'2.toSylow hidx')).trans_eq
      (IsPGroup.toSylow_coe hS'2 hidx')
  have heq : S.subgroupOf B = (Submission.Blueprint.conj h S).subgroupOf B :=
    Subgroup.eq_of_le_of_card_ge hle' (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        Subgroup.card_map_of_injective (MulAut.conj h).injective])
  calc Submission.Blueprint.conj h S
      = Subgroup.map B.subtype ((Submission.Blueprint.conj h S).subgroupOf B) :=
        (Subgroup.map_subgroupOf_eq_of_le hle).symm
    _ = Subgroup.map B.subtype (S.subgroupOf B) := by rw [heq]
    _ = S := Subgroup.map_subgroupOf_eq_of_le hSB

theorem part1_b {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G}
    (hX : X ≤ Submission.Blueprint.centD H t) (hXne : X ≠ ⊥)
    (hNK : Work.ThreePoints.HasNonTrivialNK H t X)
    (hfour : Submission.Blueprint.HasFourGroup (Work.ThreePoints.p3F X))
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.ThreePoints.p3F X)
        (Submission.Blueprint.fixedPts H X)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Work.ThreePoints.p3F X ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have htr : Work.DoubleTransitivity.IsTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X) := h2t.isTransitiveOnSub
  have htF : t ∈ Work.ThreePoints.p3F X := Work.ThreePoints.mem_p3F_t ht hX
  -- ## 1. `F ⊓ M` is strongly embedded in `F` for every conjugate `M` of `H` containing `X`
  have hSE : ∀ M : Subgroup G, X ≤ M → (∃ g : G, M = Submission.Blueprint.conj g H) →
      IsStronglyEmbedded ((Work.ThreePoints.p3F X ⊓ M).subgroupOf (Work.ThreePoints.p3F X)) := by
    intro M hXM hM
    obtain ⟨g, rfl⟩ := hM
    obtain ⟨f, hfF, hfg⟩ := exists_mem_p3F_conj_eq hXH htr hXM
    rw [hfg]
    exact stronglyEmbedded_p3F_inf_conj_of_mem hH hXH htr hfour ht htH hX hfF
  -- ## 2. Theorem B for `F = O^{2'}(C_G(X))`: `O_{2'}(F) = Z(F)` and `F/Z(F)` a model
  have hlt : Nat.card ↥(Work.ThreePoints.p3F X) < Nat.card G :=
    Work.ThreePoints.card_p3F_lt hS hH htH hXne hX
  have hBH : Submission.Blueprint.BenderHyp ↥(Work.ThreePoints.p3F X) :=
    ⟨hfour, (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X),
      hSE H hXH ⟨1, (Work.ThreePoints.conj_one H).symm⟩⟩
  have hres : Submission.Blueprint.oddResidual ↥(Work.ThreePoints.p3F X) = ⊤ :=
    oddResidual_p3F_eq_top_b X
  obtain ⟨Y, hYgrp, φ, hφsurj, hφker, hYbender⟩ :=
    benderConclusion_quotient_of_oddResidual_eq_top_b (hS.2.1 _ hlt hBH) hres
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hYsimple : IsSimpleGroup Y := (hMod Y hYbender).1
  have hBC' : ∃ (Y : Type) (_ : Group Y) (φ : ↥(Work.ThreePoints.p3F X) →* Y),
      Function.Surjective φ ∧
        φ.ker = Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ∧ IsSimpleGroup Y :=
    ⟨Y, hYgrp, φ, hφsurj, hφker, hYsimple⟩
  have hgen : Subgroup.closure (Submission.Blueprint.involutions
      ((⊤ : Subgroup ↥(Work.ThreePoints.p3F X)) : Set ↥(Work.ThreePoints.p3F X))) = ⊤ := by
    obtain ⟨v, -, hv, -, -, -⟩ := (hMod Y hYbender).2.1
    exact Work.ThreePoints.closure_involutions_eq_top_of_quotient φ hφsurj hφker hYsimple
      ⟨v, hv⟩ hres
  have hcenter : Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) =
      Subgroup.center ↥(Work.ThreePoints.p3F X) :=
    Work.ThreePoints.p3cd_oddCore_eq_center hC hS hH ht htH X hXne hX hfour hSE
      (fun g hg => exists_mem_p3F_conj_eq hXH htr hg) hgen hBC'
  have hmodel : ∃ (Y : Type) (_ : Group Y) (φ : ↥(Work.ThreePoints.p3F X) →* Y),
      Function.Surjective φ ∧ φ.ker = Subgroup.center ↥(Work.ThreePoints.p3F X) ∧
      LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y :=
    ⟨Y, hYgrp, φ, hφsurj, hφker.trans hcenter, hYbender⟩
  -- ## 3. The model split inside `F`
  have hKstrong : IsStronglyEmbedded
      ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
    hSE H hXH ⟨1, (Work.ThreePoints.conj_one H).symm⟩
  have ht2' : orderOf (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X)) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))]; exact ht
  have htne : (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X)) ∉
      (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X) := fun hmem =>
    htH (Subgroup.mem_subgroupOf.mp hmem).2
  obtain ⟨S₀, hS0pg, hS0le, hS0idx, hS0norm, hS0inf, hS0sup⟩ :=
    model_split_b hMod hKstrong ht2' htne hcenter hmodel
  let S : Subgroup G := S₀.map (Work.ThreePoints.p3F X).subtype
  -- ## 4. Transfer to `G`
  have hS2 : IsPGroup 2 S := hS0pg.map (Work.ThreePoints.p3F X).subtype
  have hSB : S ≤ Work.ThreePoints.p3F X ⊓ H := by
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hS0le hx)
  have hSidx : ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index := by
    have hcardS : Nat.card ↥S = Nat.card ↥S₀ :=
      Subgroup.card_map_of_injective (K := S₀) (f := (Work.ThreePoints.p3F X).subtype)
        (Work.ThreePoints.p3F X).subtype_injective
    have hcardB : Nat.card ↥(Work.ThreePoints.p3F X ⊓ H) =
        Nat.card ↥((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Work.ThreePoints.p3F X ⊓ H ≤ Work.ThreePoints.p3F X)).toEquiv).symm
    have e1 : Nat.card ↥S₀ *
        (S₀.subgroupOf ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X))).index
        = Nat.card ↥(Work.ThreePoints.p3F X ⊓ H) := by
      have h := Subgroup.card_mul_index
        (S₀.subgroupOf ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0le).toEquiv, ← hcardB] at h
      exact h
    have e2 : Nat.card ↥S₀ * (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index
        = Nat.card ↥(Work.ThreePoints.p3F X ⊓ H) := by
      have h := Subgroup.card_mul_index (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv, hcardS] at h
      exact h
    have hidx : (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index =
        (S₀.subgroupOf
          ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X))).index :=
      Nat.mul_left_cancel (Nat.card_pos (α := ↥S₀)) (e2.trans e1.symm)
    intro h2
    rw [hidx] at h2
    exact hS0idx h2
  have hBnormS : Work.ThreePoints.p3F X ⊓ H ≤ Subgroup.normalizer (S : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hbK : (⟨b, hb.1⟩ : ↥(Work.ThreePoints.p3F X)) ∈
        (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X) :=
      Subgroup.mem_subgroupOf.mpr hb
    have h1 := hS0norm hbK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1
    have hcomp : (MulAut.conj b : MulAut G).toMonoidHom.comp (Work.ThreePoints.p3F X).subtype =
        (Work.ThreePoints.p3F X).subtype.comp
          ((MulAut.conj (⟨b, hb.1⟩ : ↥(Work.ThreePoints.p3F X)) :
            MulAut ↥(Work.ThreePoints.p3F X)) : ↥(Work.ThreePoints.p3F X) →*
            ↥(Work.ThreePoints.p3F X)) := by
      ext x
      simp [MulAut.conj_apply]
    calc S.map (MulAut.conj b).toMonoidHom
        = (S₀.map (Work.ThreePoints.p3F X).subtype).map (MulAut.conj b).toMonoidHom := rfl
      _ = S₀.map ((MulAut.conj b).toMonoidHom.comp (Work.ThreePoints.p3F X).subtype) := by
            rw [Subgroup.map_map]
      _ = S₀.map ((Work.ThreePoints.p3F X).subtype.comp
            ((MulAut.conj (⟨b, hb.1⟩ : ↥(Work.ThreePoints.p3F X)) :
              MulAut ↥(Work.ThreePoints.p3F X)) : ↥(Work.ThreePoints.p3F X) →*
              ↥(Work.ThreePoints.p3F X))) := by rw [hcomp]
      _ = (S₀.map ((MulAut.conj (⟨b, hb.1⟩ : ↥(Work.ThreePoints.p3F X)) :
              MulAut ↥(Work.ThreePoints.p3F X)) : ↥(Work.ThreePoints.p3F X) →*
              ↥(Work.ThreePoints.p3F X))).map (Work.ThreePoints.p3F X).subtype := by
            rw [Subgroup.map_map]
      _ = S₀.map (Work.ThreePoints.p3F X).subtype := by rw [h1]
      _ = S := rfl
  have hSnormT : H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    intro h hh
    have hhH : h ∈ H := hh.1
    have hhN : h ∈ Subgroup.normalizer (X : Set G) := hh.2
    have hconjF : Submission.Blueprint.conj h (Work.ThreePoints.p3F X) = Work.ThreePoints.p3F X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_p3F X hhN)
    have hconjH : Submission.Blueprint.conj h H = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hhH)
    have hconjB : Submission.Blueprint.conj h (Work.ThreePoints.p3F X ⊓ H) =
        Work.ThreePoints.p3F X ⊓ H := by
      rw [Work.ThreePoints.conj_inf, hconjF, hconjH]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (conj_eq_self_of_le_normalizer_of_odd_index hSB hS2 hSidx hBnormS hconjB)
  have hSinf : S ⊓ Submission.Blueprint.twoPoint H t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyS, hyD⟩
    obtain ⟨x, hxS0, rfl⟩ := Subgroup.mem_map.mp hyS
    have hxK : x ∈ (Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X) :=
      hS0le hxS0
    have hxconj : x ∈ Submission.Blueprint.conj (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))
        ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) := by
      rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_subgroupOf]
      refine ⟨?_, ?_⟩
      · have h1 : (↑((⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))⁻¹ * x *
            (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))) : G) = t⁻¹ * (x : G) * t := by simp
        rw [h1]
        exact (Work.ThreePoints.p3F X).mul_mem ((Work.ThreePoints.p3F X).mul_mem
          ((Work.ThreePoints.p3F X).inv_mem htF) x.2) htF
      · have h1 : (↑((⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))⁻¹ * x *
            (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))) : G) = t⁻¹ * (x : G) * t := by simp
        rw [h1]
        exact (Work.ThreePoints.mem_twoPoint.mp hyD).2
    have hxbot : x ∈ S₀ ⊓ Submission.Blueprint.twoPoint
        ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X))
        (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X)) := ⟨hxS0, ⟨hxK, hxconj⟩⟩
    rw [hS0inf, Subgroup.mem_bot] at hxbot
    rw [Subgroup.mem_bot]
    simpa using congrArg (fun z : ↥(Work.ThreePoints.p3F X) => (z : G)) hxbot
  have htwoPoint_le : ((Submission.Blueprint.twoPoint
        ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X))
        (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))).map (Work.ThreePoints.p3F X).subtype :
          Subgroup G) ≤ Work.ThreePoints.p3F X ⊓ Submission.Blueprint.twoPoint H t := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxK, hxconj⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxconj
    have hkH : (k : G) ∈ H := (Subgroup.mem_subgroupOf.mp hkK).2
    have hkx' : t * (k : G) * t⁻¹ = (x : G) := by
      have h := congrArg (fun z : ↥(Work.ThreePoints.p3F X) => (z : G)) hkx
      simpa [MulAut.conj_apply] using h
    have hkey : t⁻¹ * (x : G) * t ∈ H := by
      have h1 : t⁻¹ * (x : G) * t = (k : G) := by
        calc t⁻¹ * (x : G) * t = t⁻¹ * (t * (k : G) * t⁻¹) * t := by rw [← hkx']
          _ = (k : G) := by group
      rw [h1]; exact hkH
    exact ⟨(Subgroup.mem_subgroupOf.mp hxK).1, Work.ThreePoints.mem_twoPoint.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hxK).2, hkey⟩⟩
  have hBsup : Work.ThreePoints.p3F X ⊓ H ≤
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
    have hB : (Work.ThreePoints.p3F X ⊓ H : Subgroup G) =
        S ⊔ ((Submission.Blueprint.twoPoint
          ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X))
          (⟨t, htF⟩ : ↥(Work.ThreePoints.p3F X))).map (Work.ThreePoints.p3F X).subtype) := by
      rw [show S = S₀.map (Work.ThreePoints.p3F X).subtype from rfl, ← Subgroup.map_sup,
        hS0sup,
        Subgroup.map_subgroupOf_eq_of_le
          (inf_le_left : Work.ThreePoints.p3F X ⊓ H ≤ Work.ThreePoints.p3F X)]
    rw [hB]
    exact sup_le le_sup_left (le_sup_of_le_right (le_inf (htwoPoint_le.trans inf_le_right)
      ((htwoPoint_le.trans inf_le_left).trans (p3F_le_normalizer X))))
  have hSsup : S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
      H ⊓ Subgroup.normalizer (X : Set G) := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_inf (hSB.trans inf_le_right)
          ((hSB.trans inf_le_left).trans (p3F_le_normalizer X))
      · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · intro h hh
      have hhH : h ∈ H := hh.1
      have hhN : h ∈ Subgroup.normalizer (X : Set G) := hh.2
      have htX : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X :=
        (Work.DoubleTransitivity.mk_mem_fixedPts_iff X H t).mpr
          ((Work.ThreePoints.le_twoPoint_of_le_centD hX).trans inf_le_right)
      have h1X : Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X :=
        (Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH
      have hhtX : h • ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
        rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
        intro x hx
        rw [MulAction.mem_stabilizer_iff]
        have hxX : h⁻¹ * x * h ∈ X := by
          have h := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (X : Set G)).inv_mem hhN) x).mp hx
          simpa using h
        have hfix := (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp htX) hxX
        rw [MulAction.mem_stabilizer_iff] at hfix
        calc x • (h • ((t : G) : G ⧸ H)) = (x * h) • ((t : G) : G ⧸ H) := by rw [mul_smul]
          _ = (h * (h⁻¹ * x * h)) • ((t : G) : G ⧸ H) := by
                rw [show x * h = h * (h⁻¹ * x * h) from by group]
          _ = h • ((h⁻¹ * x * h) • ((t : G) : G ⧸ H)) := by rw [mul_smul]
          _ = h • ((t : G) : G ⧸ H) := by rw [hfix]
      have hne1 : Work.DoubleTransitivity.pt H ≠ ((t : G) : G ⧸ H) := by
        intro hcon
        exact htH ((Work.DoubleTransitivity.mk_one_eq_iff).mp hcon.symm)
      have hne2 : Work.DoubleTransitivity.pt H ≠ h • ((t : G) : G ⧸ H) := by
        intro hcon
        have h1 : h⁻¹ • Work.DoubleTransitivity.pt H = ((t : G) : G ⧸ H) := by
          rw [hcon, ← mul_smul, inv_mul_cancel, one_smul]
        have h2 : Work.DoubleTransitivity.pt H = ((t : G) : G ⧸ H) := by
          rw [← h1, Work.DoubleTransitivity.smul_pt]
          exact (Work.DoubleTransitivity.mk_one_eq_iff.mpr (H.inv_mem hhH)).symm
        exact hne1 h2
      obtain ⟨f, hfF, hf1, hf2⟩ :=
        h2t (Work.DoubleTransitivity.pt H) h1X ((t : G) : G ⧸ H) htX hne1
          (Work.DoubleTransitivity.pt H) h1X (h • ((t : G) : G ⧸ H)) hhtX hne2
      have hfH : f ∈ H := by
        have h1 : f • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := hf1
        rw [Work.DoubleTransitivity.smul_pt] at h1
        exact Work.DoubleTransitivity.mk_one_eq_iff.mp h1
      have hvN : f⁻¹ * h ∈ Subgroup.normalizer (X : Set G) :=
        Subgroup.mul_mem _
          ((Subgroup.normalizer (X : Set G)).inv_mem (p3F_le_normalizer X hfF)) hhN
      have hvD : f⁻¹ * h ∈ Submission.Blueprint.twoPoint H t := by
        rw [Work.ThreePoints.mem_twoPoint]
        refine ⟨H.mul_mem (H.inv_mem hfH) hhH, ?_⟩
        have h1 : (f⁻¹ * h) • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
          rw [mul_smul, ← hf2, ← mul_smul, inv_mul_cancel, one_smul]
        have h2 : f⁻¹ * h ∈ Submission.Blueprint.conj t H :=
          Work.DoubleTransitivity.mem_conj_iff_smul_fixed.mpr h1
        rwa [Work.ThreePoints.mem_conj_iff] at h2
      have hdecomp : h = f * (f⁻¹ * h) := by group
      rw [hdecomp]
      have hDle : (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ≤
          S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :=
        le_sup_of_le_right le_rfl
      exact Subgroup.mul_mem _ (hBsup ⟨hfF, hfH⟩) (hDle ⟨hvD, hvN⟩)
  exact ⟨S, hS2, hSB, hSidx, hSnormT, hSinf, hSsup⟩

end Work.ThreePoints.P3Sub
