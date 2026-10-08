import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.p3_appI_one
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.Reductions.OddResidual
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.F1EqF.prop2c_of_even

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 0. `F₁ = ⟨Inv C_G(X)⟩` is normal in `C_G(X)` and in `N_G(X)` -/

/-- Conjugation by an element `c ∈ C_G(X)` carries the involutions of `C_G(X)` to involutions of
`C_G(X)`. -/
theorem mem_involutions_conj_of_mem_centralizer {X : Subgroup G} {c u : G}
    (hc : c ∈ Subgroup.centralizer (X : Set G))
    (hu : u ∈ involutions (Subgroup.centralizer (X : Set G) : Set G)) :
    (MulAut.conj c) u ∈ involutions (Subgroup.centralizer (X : Set G) : Set G) := by
  obtain ⟨huC, hu2⟩ := mem_involutions.mp hu
  refine mem_involutions.mpr ⟨?_, ?_⟩
  · rw [MulAut.conj_apply]
    exact (Subgroup.centralizer (X : Set G)).mul_mem
      ((Subgroup.centralizer (X : Set G)).mul_mem hc huC)
      ((Subgroup.centralizer (X : Set G)).inv_mem hc)
  · have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective u
    rwa [hu2] at h

/-- Conjugation by an element `g ∈ N_G(X)` carries the involutions of `C_G(X)` to involutions of
`C_G(X)` (the centraliser of `X` is normalised by `N_G(X)`). -/
theorem mem_involutions_conj_of_mem_normalizer {X : Subgroup G} {g u : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hu : u ∈ involutions (Subgroup.centralizer (X : Set G) : Set G)) :
    (MulAut.conj g) u ∈ involutions (Subgroup.centralizer (X : Set G) : Set G) := by
  obtain ⟨huC, hu2⟩ := mem_involutions.mp hu
  have hu' := Subgroup.mem_centralizer_iff.mp huC
  refine mem_involutions.mpr ⟨?_, ?_⟩
  · rw [MulAut.conj_apply]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    have hxg : g⁻¹ * x * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [hu' _ hxg]
      _ = (g * u * g⁻¹) * x := by group
  · have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
    rwa [hu2] at h

/-- `F₁ = ⟨Inv C_G(X)⟩` is invariant under conjugation by `C_G(X)`. -/
theorem map_conj_p3F1_eq_self {X : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    Subgroup.map (MulAut.conj c).toMonoidHom (p3F1 X) = p3F1 X := by
  rw [p3F1, MonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mem_involutions_conj_of_mem_centralizer hc hu
  · intro hv
    refine ⟨(MulAut.conj c⁻¹) v, mem_involutions_conj_of_mem_centralizer
      ((Subgroup.centralizer (X : Set G)).inv_mem hc) hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

/-- `F₁ = ⟨Inv C_G(X)⟩` is invariant under conjugation by `N_G(X)`. -/
theorem map_conj_p3F1_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.map (MulAut.conj g).toMonoidHom (p3F1 X) = p3F1 X := by
  rw [p3F1, MonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mem_involutions_conj_of_mem_normalizer hg hu
  · intro hv
    refine ⟨(MulAut.conj g⁻¹) v, mem_involutions_conj_of_mem_normalizer
      ((Subgroup.normalizer (X : Set G)).inv_mem hg) hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

/-- `F₁` is normal in `C_G(X)`. -/
theorem p3F1_normal_subgroupOf_centralizer (X : Subgroup G) :
    ((p3F1 X).subgroupOf (Subgroup.centralizer (X : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (p3F1_le_centralizer X)]
  intro h k hh hk
  have hmap := map_conj_p3F1_eq_self (X := X) hk
  have hmem : (MulAut.conj k) h ∈ Subgroup.map (MulAut.conj k).toMonoidHom (p3F1 X) :=
    Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  rw [hmap] at hmem
  rw [MulAut.conj_apply] at hmem
  exact hmem

/-- `F₁` is normal in `N_G(X)`. -/
theorem p3F1_normal_subgroupOf_normalizer (X : Subgroup G) :
    ((p3F1 X).subgroupOf (Subgroup.normalizer (X : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (p3F1_le_normalizer X)]
  intro h k hh hk
  have hmap := map_conj_p3F1_eq_self_of_mem_normalizer (X := X) hk
  have hmem : (MulAut.conj k) h ∈ Subgroup.map (MulAut.conj k).toMonoidHom (p3F1 X) :=
    Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  rw [hmap] at hmem
  rw [MulAut.conj_apply] at hmem
  exact hmem

/-- `F₁` is normal in `F = O^{2'}(C_G(X))`: `F ≤ C_G(X)` and `F₁ ⊴ C_G(X)`. -/
theorem p3F1_normal_subgroupOf_p3F (X : Subgroup G) :
    ((p3F1 X).subgroupOf (p3F X)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (p3F1_le_p3F X)]
  intro h k hh hk
  have hkC : k ∈ Subgroup.centralizer (X : Set G) := p3F_le_centralizer X hk
  have hmap := map_conj_p3F1_eq_self (X := X) hkC
  have hmem : (MulAut.conj k) h ∈ Subgroup.map (MulAut.conj k).toMonoidHom (p3F1 X) :=
    Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  rw [hmap] at hmem
  rw [MulAut.conj_apply] at hmem
  exact hmem

/-- `O^{2'}` is transported by a group isomorphism: `O^{2'}(B) = (O^{2'}(A)).map e`. -/
theorem map_oddResidual_equiv {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
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

/-- `O^{2'}(F) = F` for `F = O^{2'}(C_G(X))`: idempotency of `O^{2'}`. -/
theorem oddResidual_p3F_eq_top' (X : Subgroup G) :
    Submission.Blueprint.oddResidual ↥(p3F X) = ⊤ := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  have he : ↥(Submission.Blueprint.oddResidual C) ≃*
      ↥((Submission.Blueprint.oddResidual C).map C.subtype) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  have key := map_oddResidual_equiv he
  rw [Work.Reductions.oddResidual_self_eq_top (G := ↥C)] at key
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr he.surjective] at key
  exact key.symm

/-! ## 1. The two-transitivity input forces `N_G(X) = F₁ · N_D(X)` -/

/-- **Source, Ch. II §4 Prop. 3 (a), first step.**  If `F₁ = ⟨Inv C_G(X)⟩` acts `2`-transitively
on `Ω_X`, then `N_G(X) = F₁ · N_D(X)`: for `g ∈ N_G(X)` there is `f ∈ F₁` with `f g` fixing both
`H` and `H^t`. -/
theorem normalizer_le_sup_of_twoTransitive {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F1 X) (fixedPts H X)) :
    Subgroup.normalizer (X : Set G) ≤
      p3F1 X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left (le_trans inf_le_left le_rfl))
  have hXtH : X ≤ conj t H := hX.trans (le_trans inf_le_left inf_le_right)
  intro g hg
  have hmem1 : (g • ((1 : G) : G ⧸ H)) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer]
    have hstab : MulAction.stabilizer G (g • ((1 : G) : G ⧸ H)) = conj g H := by
      rw [show g • ((1 : G) : G ⧸ H) = ((g : G) : G ⧸ H) from by
        rw [DoubleTransitivity.smul_mk, mul_one], stabilizer_mk]
    rw [hstab]
    calc X = conj g X := (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg).symm
      _ ≤ conj g H := Subgroup.map_mono hXH
  have hmem2 : (g • (t • ((1 : G) : G ⧸ H))) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer]
    have hstab : MulAction.stabilizer G (g • (t • ((1 : G) : G ⧸ H))) = conj (g * t) H := by
      rw [show g • (t • ((1 : G) : G ⧸ H)) = ((g * t : G) : G ⧸ H) from by
        rw [DoubleTransitivity.smul_mk, DoubleTransitivity.smul_mk, mul_one], stabilizer_mk]
    rw [hstab]
    calc X = conj g X := (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg).symm
      _ ≤ conj g (conj t H) := Subgroup.map_mono hXtH
      _ = conj (g * t) H := by rw [← conj_mul]
  have hmem1' : ((1 : G) : G ⧸ H) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer,
      show MulAction.stabilizer G ((1 : G) : G ⧸ H) = H from by
        rw [stabilizer_mk, conj_one]]
    exact hXH
  have hmem2' : (t • ((1 : G) : G ⧸ H)) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer,
      show MulAction.stabilizer G (t • ((1 : G) : G ⧸ H)) = conj t H from by
        rw [DoubleTransitivity.smul_mk, mul_one, stabilizer_mk]]
    exact hXtH
  have htne : t • ((1 : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
    intro hcon
    rw [show t • ((1 : G) : G ⧸ H) = ((t : G) : G ⧸ H) from by
        rw [DoubleTransitivity.smul_mk, mul_one]] at hcon
    exact htH (DoubleTransitivity.mk_one_eq_iff.mp hcon)
  have hne : g • ((1 : G) : G ⧸ H) ≠ g • (t • ((1 : G) : G ⧸ H)) := by
    intro hcon
    exact htne ((MulAction.injective g) hcon.symm)
  have hne' : ((1 : G) : G ⧸ H) ≠ t • ((1 : G) : G ⧸ H) := fun h => htne h.symm
  obtain ⟨f, hfF1, hf1, hf2⟩ := h2t _ hmem1 _ hmem2 hne _ hmem1' _ hmem2' hne'
  have hfgH : f * g ∈ H := by
    have h : (f * g) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      rw [mul_smul]; exact hf1
    rw [show (f * g) • ((1 : G) : G ⧸ H) = ((f * g : G) : G ⧸ H) from by
        rw [DoubleTransitivity.smul_mk, mul_one]] at h
    exact DoubleTransitivity.mk_one_eq_iff.mp h
  have hfgtH : f * g ∈ conj t H := by
    have h : (f * g) • (t • ((1 : G) : G ⧸ H)) = t • ((1 : G) : G ⧸ H) := by
      rw [mul_smul]; exact hf2
    have h' : (f * g) ∈ MulAction.stabilizer G (t • ((1 : G) : G ⧸ H)) :=
      MulAction.mem_stabilizer_iff.mpr h
    rwa [show MulAction.stabilizer G (t • ((1 : G) : G ⧸ H)) = conj t H from by
        rw [DoubleTransitivity.smul_mk, mul_one, stabilizer_mk]] at h'
  have hfg : f * g ∈ twoPoint H t ⊓ Subgroup.normalizer (X : Set G) :=
    ⟨⟨hfgH, hfgtH⟩, (Subgroup.normalizer (X : Set G)).mul_mem (p3F1_le_normalizer X hfF1) hg⟩
  have hmem : f⁻¹ * (f * g) ∈ p3F1 X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :=
    Subgroup.mul_mem _
      ((le_sup_left : p3F1 X ≤ p3F1 X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)))
        ((p3F1 X).inv_mem hfF1))
      ((le_sup_right : (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ≤
        p3F1 X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))) hfg)
  rwa [inv_mul_cancel_left] at hmem

/-! ## 2. The Dedekind step and the oddness of `[F : F₁]` -/

/-- **Dedekind step.**  If `N_G(X) = F₁ · K` with `K ≤ N_G(X)`, then
`F = F₁ · (F ⊓ K)`, i.e. `F ≤ F₁ ⊔ (F ⊓ K)`. -/
theorem p3F_le_sup_inf {X : Subgroup G} {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (X : Set G))
    (hsup : Subgroup.normalizer (X : Set G) ≤ p3F1 X ⊔ K) :
    p3F X ≤ p3F1 X ⊔ (p3F X ⊓ K) := by
  intro x hxF
  have hxN : x ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le_normalizer (X : Set G)) (p3F_le_centralizer X hxF)
  have hxK : x ∈ p3F1 X ⊔ K := hsup hxN
  haveI : ((p3F1 X).subgroupOf (Subgroup.normalizer (X : Set G))).Normal :=
    p3F1_normal_subgroupOf_normalizer X
  have hsub : (p3F1 X ⊔ K).subgroupOf (Subgroup.normalizer (X : Set G)) =
      (p3F1 X).subgroupOf (Subgroup.normalizer (X : Set G)) ⊔
        K.subgroupOf (Subgroup.normalizer (X : Set G)) :=
    Subgroup.subgroupOf_sup (p3F1_le_normalizer X) hK
  have hmem : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (X : Set G))) ∈
      (p3F1 X).subgroupOf (Subgroup.normalizer (X : Set G)) ⊔
        K.subgroupOf (Subgroup.normalizer (X : Set G)) := by
    rw [← hsub]
    exact hxK
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (p3F1 X).subgroupOf (Subgroup.normalizer (X : Set G)))
      (t := K.subgroupOf (Subgroup.normalizer (X : Set G)))).mp hmem
  have haG : (a : G) ∈ p3F1 X := Subgroup.mem_subgroupOf.mp ha
  have hbG : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
  have hxab : (a : G) * (b : G) = x := by
    have h1 := congrArg (fun z : ↥(Subgroup.normalizer (X : Set G)) => (z : G)) hab
    simpa using h1
  have hbF : (b : G) ∈ p3F X := by
    have hb_eq : (b : G) = (a : G)⁻¹ * x := by
      rw [← hxab]; group
    rw [hb_eq]
    exact (p3F X).mul_mem ((p3F X).inv_mem (p3F1_le_p3F X haG)) hxF
  rw [← hxab]
  exact Subgroup.mul_mem _
    ((le_sup_left : p3F1 X ≤ p3F1 X ⊔ (p3F X ⊓ K)) haG)
    ((le_sup_right : p3F X ⊓ K ≤ p3F1 X ⊔ (p3F X ⊓ K)) ⟨hbF, hbG⟩)

/-- **The index of `F₁` in `F` is odd.**  Given `F = F₁ · (F ⊓ K)` with `|K|` odd, the index
`[F : F₁]` divides `|F ⊓ K| ∣ |K|`, hence is odd. -/
theorem odd_index_p3F1_in_p3F {X : Subgroup G} {K : Subgroup G}
    (hKodd : Odd (Nat.card ↥K)) (hle : p3F X ≤ p3F1 X ⊔ (p3F X ⊓ K)) :
    Odd ((p3F1 X).subgroupOf (p3F X)).index := by
  haveI : ((p3F1 X).subgroupOf (p3F X)).Normal := p3F1_normal_subgroupOf_p3F X
  have hsup : (p3F1 X).subgroupOf (p3F X) ⊔ ((p3F X ⊓ K).subgroupOf (p3F X)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (p3F1_le_p3F X) inf_le_left, Subgroup.subgroupOf_eq_top]
    exact hle
  have hrel := Subgroup.relIndex_sup_left (H := (p3F X ⊓ K).subgroupOf (p3F X))
    (K := (p3F1 X).subgroupOf (p3F X))
  rw [hsup, Subgroup.relIndex_top_right] at hrel
  have hdiv : ((p3F1 X).subgroupOf (p3F X)).index ∣ Nat.card ↥(p3F X ⊓ K) := by
    rw [hrel]
    refine dvd_trans (Subgroup.index_dvd_card _) ?_
    have hmap := Subgroup.map_subgroupOf_eq_of_le (H := p3F X ⊓ K) (K := p3F X) inf_le_left
    have hcard := Subgroup.card_map_of_injective
      (K := (p3F X ⊓ K).subgroupOf (p3F X)) (f := (p3F X).subtype) Subtype.coe_injective
    rw [hmap] at hcard
    rw [← hcard]
  exact Odd.of_dvd_nat (Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_right)) hdiv

/-- **The assembly.**  If `F₁ = ⟨Inv C_G(X)⟩` acts `2`-transitively on `Ω_X`, then `F₁ = F`. -/
theorem p3F1_eq_p3F_of_twoTransitive {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F1 X) (fixedPts H X)) :
    p3F1 X = p3F X := by
  refine le_antisymm (p3F1_le_p3F X) ?_
  have hKodd : Odd (Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G))) :=
    Odd.of_dvd_nat (IsStronglyEmbedded.odd_card_inf_conj hH htH)
      (Subgroup.card_dvd_of_le inf_le_left)
  have hsup := normalizer_le_sup_of_twoTransitive hH ht htH hX h2t
  have hle := p3F_le_sup_inf (X := X) inf_le_right hsup
  have hodd := odd_index_p3F1_in_p3F (X := X) hKodd hle
  have htop := oddResidual_p3F_eq_top' X
  have hmin := (Work.Reductions.oddResidual_basic (G := ↥(p3F X))).2.2.1
    ((p3F1 X).subgroupOf (p3F X)) (p3F1_normal_subgroupOf_p3F X) hodd
  rw [htop] at hmin
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hmin (Subgroup.mem_top ⟨x, hx⟩))

/-! ## 3. Ch. I §4 Prop. 2 and Ch. II §4 Prop. 1 (a), both with the Brauer–Suzuki hypothesis -/

/-- **Ch. I §4 Prop. 2** (p. 156) with the Brauer–Suzuki hypothesis, reduced to the `2`-rank-`1`
input `hNO2` (no `p`-subgroup of a group without a four-group, `p` odd, has exactly two fixed
points).  The `2`-rank `≥ 2` case is `even_card_normalizer_of_maximal_p_subgroup`. -/
theorem even_card_normalizer_of_maximal_p_subgroup_hbrsz {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hA : Submission.Blueprint.ThmAProp)
    (hNO2 : ∀ (E : Type) [Group E] [Finite E] {K : Subgroup E},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K → ∀ (p : ℕ), p.Prime → p ≠ 2 →
        ∀ P : Subgroup E, IsPGroup p P → ¬ Submission.Blueprint.HasFourGroup E →
        (Submission.Blueprint.fixedPts K P).ncard ≠ 2)
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K) (hQp : IsPGroup p Q)
    (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  by_cases hfour : Submission.Blueprint.HasFourGroup F
  · exact Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup hBrSz hA hfour hK hp hp2
      hQK hQp hQ3 hQmax
  · exact Work.ThreePoints.even_card_normalizer_nofour_of_no_two_fixed hK hp hp2 hQK hQp hQ3 hQmax
      (fun P hPp => hNO2 F hK p hp hp2 P hPp hfour) hBrSz

/-- **Peterfalvi I Ch. II §4 Prop. 1 (a)** with the Brauer–Suzuki hypothesis: if `X` fixes at
least three points of `Ω = G ⧸ H` and `M = H^g` is one of them, then `C_M(X)` has even order.
This is `Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz` with Ch. I §4 Prop. 2 supplied by
`even_card_normalizer_of_maximal_p_subgroup_hbrsz`. -/
theorem even_card_centralizer_of_fixes_three_hbrsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hNO2 : ∀ (E : Type) [Group E] [Finite E] {K : Subgroup E},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K → ∀ (p : ℕ), p.Prime → p ≠ 2 →
        ∀ P : Subgroup E, IsPGroup p P → ¬ Submission.Blueprint.HasFourGroup E →
        (Submission.Blueprint.fixedPts K P).ncard ≠ 2)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC
    (fun F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax =>
      even_card_normalizer_of_maximal_p_subgroup_hbrsz hBrSz hA hNO2 hK hp hp2 hQK hQp hQ3 hQmax)
    hS hH hX3 hM hXM

/-! ## 4. `F₁ = F` in Ch. II §4 Prop. 3 -/

/-- **Ch. II §4 Prop. 3, part 3), conclusion (a)**: under (B0)–(B2), with `X ≠ ⊥`,
`X ≤ V = C_D(t)` and `N_K(X) ≠ 1`, one has `F₁ = ⟨Inv C_G(X)⟩ = F = O^{2'}(C_G(X))`.

`Work.ThreePoints.P3NeBot.p3_twoTransitive` (Ch. II §4 Prop. 3 (a), the `2`-transitivity of `F₁`
on `Ω_X`) supplies the hypothesis of `p3F1_eq_p3F_of_twoTransitive` above, which carries out the
source's argument. -/
theorem p3cd_F1_eq_F {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Work.ThreePoints.p3F1 X = Work.ThreePoints.p3F X :=
  p3F1_eq_p3F_of_twoTransitive hH ht htH hX
    (Work.ThreePoints.P3NeBot.p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX)

end Work.ThreePoints
