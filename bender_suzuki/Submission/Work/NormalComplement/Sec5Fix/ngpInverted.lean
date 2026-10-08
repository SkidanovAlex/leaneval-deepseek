/-
# `Work.NormalComplement.Sec5Fix.ngpInverted`

Let `h : Setup5 G H t W p P A r`, let `u` be the involution of `C_H(V)` (`V = centD H t`), and let
`x ∈ N_G(P)` be an element of odd order inverted by `u` (`u * x * u⁻¹ = x⁻¹`).  Then
`orderOf x ∣ orderOf (u * t)`.

This is the fact used in Peterfalvi I Ch. III §5 Prop. 2 (d): with `F = N_G(P)/P`, App. III
(2),(4) gives a normal subgroup `Q` of `F` with `F = Q ⋊ N_H(P)/P`, `Q` elementary abelian of
exponent `f`, and `Q` exactly the set of odd-order elements of `F` inverted by an involution.
Since `x` maps into `Q`, `x ^ f` lies in the kernel `K₀` of the action of `N_G(P)` on `Ω_P`,
which is contained in `V = centD H t`; as `u` centralises `V` and inverts `x`, this forces
`x ^ (2f) = 1`, hence `orderOf x ∣ f`, and `f = orderOf (ū t̄) ∣ orderOf (u * t)`.

NOTE: `Submission.Work.NormalComplement.Sec5Fix.prop2c` is currently part of an import cycle
(`prop2c` → `sec5_prop2` → `sec5_clause_c` → `prop2c`), so it cannot be imported here; the few
facts used from it are re-derived below.
-/
import Mathlib
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appIII
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.Hering.Perm.appII5
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.DoubleTransitivity.App2.app2_5
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThreePoints.Omega
import Submission.Work.Models.fm1src.Submission.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-! ## The action of `N_G(P)/K` on `Ω_P` -/

/-- `N_G(P)`, the normaliser of `P`. -/
abbrev NGP (P : Subgroup G) : Subgroup G := Subgroup.normalizer (P : Set G)

/-- `Ω_P`, the set of fixed points of `P` on `G ⧸ H`. -/
abbrev OmP (H P : Subgroup G) : Type _ := ↥(fixedPts H P)

/-- `N_G(P)` preserves `Ω_P`. -/
theorem smul_mem_omP {g : G} (hg : g ∈ NGP P) {ω : G ⧸ H} (hω : ω ∈ fixedPts H P) :
    g • ω ∈ fixedPts H P :=
  Work.ThreePoints.P3NeBot.smul_mem_fixedPts_of_mem_normalizer hg hω

instance instSMulOmP : SMul ↥(NGP P) (OmP H P) where
  smul g ω := ⟨(g : G) • (ω : G ⧸ H), smul_mem_omP g.2 ω.2⟩

@[simp] theorem coe_smul_omP (g : ↥(NGP P)) (ω : OmP H P) :
    ((g • ω : OmP H P) : G ⧸ H) = (g : G) • (ω : G ⧸ H) := rfl

instance instMulActionOmP : MulAction ↥(NGP P) (OmP H P) where
  one_smul ω := Subtype.ext (by
    show (((1 : ↥(NGP P)) : G)) • (ω : G ⧸ H) = (ω : G ⧸ H)
    rw [Subgroup.coe_one, one_smul])
  mul_smul g h ω := Subtype.ext (by
    show (((g * h : ↥(NGP P)) : G)) • (ω : G ⧸ H) =
      (g : G) • ((h : G) • (ω : G ⧸ H))
    rw [Subgroup.coe_mul, mul_smul])

/-- The base point `H` of `Ω_P`. -/
noncomputable def ptOmP (hPH : P ≤ H) : OmP H P :=
  ⟨QuotientGroup.mk (1 : G), by
    intro x hx
    rw [Work.DoubleTransitivity.smul_mk, QuotientGroup.eq]
    simpa using H.inv_mem (hPH hx)⟩

@[simp] theorem coe_ptOmP (hPH : P ≤ H) :
    ((ptOmP hPH : OmP H P) : G ⧸ H) = QuotientGroup.mk 1 := rfl

/-- The stabiliser of the base point of `Ω_P` is `N_H(P)`. -/
theorem smul_ptOmP_eq_iff (hPH : P ≤ H) (g : ↥(NGP P)) :
    g • ptOmP hPH = ptOmP hPH ↔ (g : G) ∈ H := by
  rw [Subtype.ext_iff, coe_smul_omP, coe_ptOmP]
  exact Work.ThreePoints.P3NeBot.smul_pt_eq_pt_iff

/-- The kernel `K₀` of the action of `N_G(P)` on `Ω_P`. -/
noncomputable def KerP (H P : Subgroup G) : Subgroup ↥(NGP P) :=
  (MulAction.toPermHom ↥(NGP P) (OmP H P)).ker

instance instKerPNormal (H P : Subgroup G) : (KerP H P).Normal := MonoidHom.normal_ker _

noncomputable instance instMulActionQuotOmP (H P : Subgroup G) :
    MulAction (↥(NGP P) ⧸ KerP H P) (OmP H P) :=
  MulAction.compHom (OmP H P) (QuotientGroup.lift (KerP H P)
    (MulAction.toPermHom ↥(NGP P) (OmP H P)) (le_refl _))

@[simp] theorem quotient_smul_mk_omP (g : ↥(NGP P)) (ω : OmP H P) :
    (QuotientGroup.mk' (KerP H P) g) • ω = g • ω := rfl

/-- Membership in `KerP` is "acts trivially on `Ω_P`". -/
theorem mem_KerP_iff (γ : ↥(NGP P)) :
    γ ∈ KerP H P ↔ ∀ ω : OmP H P, γ • ω = ω := by
  change γ ∈ (MulAction.toPermHom ↥(NGP P) (OmP H P)).ker ↔ _
  rw [MonoidHom.mem_ker, MulAction.toPermHom_apply]
  constructor
  · intro h ω
    have h' : (MulAction.toPerm γ) ω = ω := by rw [h]; rfl
    rwa [MulAction.toPerm_apply] at h'
  · intro h
    refine Equiv.ext (fun ω => ?_)
    rw [MulAction.toPerm_apply]
    show γ • ω = ω
    exact h ω

/-! ## Elementary facts about `N_G(P)` -/

/-- `t` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(t)`. -/
lemma commute_t_of_mem_P (h : Design.Setup5 G H t W p P A r) {x : G} (hx : x ∈ P) :
    t * x * t⁻¹ = x := by
  have hxV : x ∈ centD H t := (h.P_le hx).2
  have hxct : x ∈ Subgroup.centralizer ({t} : Set G) := hxV.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxct
  rw [← hxct]
  group

/-- `u` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(u)`. -/
lemma commute_u_of_mem_P (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (centD H t : Set G)) {x : G}
    (hx : x ∈ P) : u * x * u⁻¹ = x := by
  have hxV : x ∈ centD H t := (h.P_le hx).2
  have hux : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x hxV
  rw [← hux]
  group

/-- `t` lies in `N_G(P)`. -/
lemma mem_normalizer_t (h : Design.Setup5 G H t W p P A r) : t ∈ NGP P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change t * x * t⁻¹ ∈ P
    rw [commute_t_of_mem_P h hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, commute_t_of_mem_P h hy]⟩

/-- `u` lies in `N_G(P)`. -/
lemma mem_normalizer_u (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (centD H t : Set G)) : u ∈ NGP P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change u * x * u⁻¹ ∈ P
    rw [commute_u_of_mem_P h hu hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, commute_u_of_mem_P h hu hy]⟩

/-- `p ≠ 2`: `p ∣ |E : E'|` divides `|E|`, which divides the odd number `|D|`. -/
lemma setup5_p_ne_two (h : Design.Setup5 G H t W p P A r) : p ≠ 2 := by
  intro hp
  have hdvd : p ∣ Nat.card ↥(Design.Egrp H t W) :=
    h.dvd.trans (Subgroup.relIndex_dvd_card _ _)
  have h2 : 2 ∣ Nat.card ↥(Design.Egrp H t W) := hp ▸ hdvd
  have hodd : Odd (Nat.card ↥(Design.Egrp H t W)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_right)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

/-- Every element of `(A ⊓ C_G(P)) ⊔ P` of order dividing `2` is `1`: the group
`C_A(P) · P = C_A(P) × P` has odd order (`A ⊓ P = ⊥`). -/
lemma eq_one_of_mem_sup_of_sq_eq_one (h : Design.Setup5 G H t W p P A r) {x : G}
    (hx : x ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G))
    (hx2 : x * x = 1) : x = 1 := by
  classical
  set C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCnorm : C ≤ Subgroup.normalizer (P : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G))
  have hprod : ((P : Set G) * (C : Set G)) = (((C ⊔ P : Subgroup G)) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.coe_mul_of_right_le_normalizer_left P C hCnorm).symm
  have hx' : x ∈ (P : Set G) * (C : Set G) := by
    rw [hprod]; exact hx
  obtain ⟨q, hqP, a, haC, hqa⟩ := Set.mem_mul.mp hx'
  have haA : a ∈ A := (Subgroup.mem_inf.mp (hC ▸ haC)).1
  have haC : a ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp (hC ▸ haC)).2
  have hcomm : a * q = q * a := ((Subgroup.mem_centralizer_iff.mp haC) q hqP).symm
  have hsq : q * q * (a * a) = 1 := by
    have h6 : (q * a) * (q * a) = 1 := by rw [hqa]; exact hx2
    rw [show q * a * (q * a) = q * q * (a * a) from by
      rw [mul_assoc, ← mul_assoc a q a, hcomm]; group] at h6
    exact h6
  have hkey : q * q = (a * a)⁻¹ := mul_eq_one_iff_eq_inv.mp hsq
  have haaA : a * a ∈ A := A.mul_mem haA haA
  have hqqA : q * q ∈ A := by rw [hkey]; exact A.inv_mem haaA
  have hqqP : q * q ∈ P := P.mul_mem hqP hqP
  have hqq1 : q * q = 1 := by
    have h7 : q * q ∈ A ⊓ P := ⟨hqqA, hqqP⟩
    rw [h.A_inf] at h7
    simpa using h7
  have haa1 : a * a = 1 := by
    have h8 := hkey
    rw [hqq1] at h8
    exact inv_eq_one.mp h8.symm
  have hq1 : q = 1 := by
    have h1 : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have h2 : orderOf q ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hqP
    rw [h.P_card] at h2
    have hcop : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two (setup5_p_ne_two h))
    have h3 : orderOf q ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 2 p = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have haT : a ∈ twoPoint H t :=
      (inf_le_left : centD H t ≤ twoPoint H t) (h.A_le haA)
    have h2 : orderOf a ∣ Nat.card ↥(twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ haT
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
    have hgcd : Nat.gcd 2 (Nat.card ↥(twoPoint H t)) = 1 :=
      Nat.coprime_two_left.mpr hodd
    have h3 : orderOf a ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hgcd] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [← hqa, hq1, ha1, one_mul]

/-! ## `N_H(P)` is strongly embedded in `N_G(P)` -/

/-- `N_H(P) = H ⊓ N_G(P)` is a strongly embedded subgroup of `N_G(P)` (`ChIIFourProp` P1 (b)
applied to `X = P`). -/
theorem stronglyEmbedded_normalizer (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) :
    IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  obtain ⟨hP1b, -⟩ := hC4 G h.sit H h.se t h.invol h.notMem
  have hPleV : P ≤ centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have hinv : involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆ 𝒢 := by
    intro x hx
    rw [Work.ThreePoints.mem_involutions] at hx
    exact Subgroup.centralizer_le_normalizer _ hx.1
  have h1 := hP1b P 𝒢 h3 hinv (by rw [h𝒢]) (1 : G)
    (by rw [Work.DoubleTransitivity.conj_one]; exact hPleH)
  rw [Work.DoubleTransitivity.conj_one] at h1
  rw [h𝒢, inf_comm] at h1
  exact h1

/-! ## The involution of `N_H(P)` is unique -/

/-- The `J`-set of the pair `(N_H(P), t)` inside `N_G(P)` is trivial. -/
theorem kset_inf_normalizer_trivial (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : Design.Setup5 G H t W p P A r) :
    (Work.ThmF.Kset ((H ⊓ NGP P).subgroupOf (NGP P)) ⟨t, mem_normalizer_t h⟩).ncard = 1 := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  set H₁ : Subgroup G := H ⊓ 𝒢 with hH₁
  have ht𝒢 : t ∈ 𝒢 := mem_normalizer_t h
  rw [Set.ncard_eq_one]
  refine ⟨1, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · unfold Work.ThmF.Kset
    rw [Work.ThreePoints.mem_invertedBy]
    exact ⟨Subgroup.one_mem _, by simp⟩
  · intro x hx
    unfold Work.ThmF.Kset at hx
    rw [Work.ThreePoints.mem_invertedBy] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hxH1, hxH2⟩ := Subgroup.mem_inf.mp hx1
    have hxH₁ : (x : G) ∈ H₁ := Subgroup.mem_subgroupOf.mp hxH1
    have hxG : (x : G) ∈ NGP P := hxH₁.2
    have h2 : t * (x : G) * t⁻¹ = (x : G)⁻¹ := by
      have h4 := congrArg (fun y : ↥𝒢 => (y : G)) hx2
      simpa using h4
    have hxconj : (x : G) ∈ Submission.Blueprint.conj t H := by
      rw [Work.ThreePoints.mem_conj_iff]
      have h3' : (↑(⟨t, ht𝒢⟩⁻¹ * x * ⟨t, ht𝒢⟩) : G) ∈ H₁ :=
        Subgroup.mem_subgroupOf.mp ((Work.ThreePoints.mem_conj_iff).mp hxH2)
      have h1 : H₁ ≤ H := by rw [hH₁]; exact inf_le_left
      exact h1 (by simpa using h3')
    have hxD : (x : G) ∈ Submission.Blueprint.twoPoint H t := ⟨hxH₁.1, hxconj⟩
    have hxAP : (x : G) ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G) := by
      rw [← (Work.NormalComplement.sec4_one_c hFT h.toSetup45A).1]
      exact ⟨hxD, hxG⟩
    have hx2' : (x : G) * (x : G) = 1 := by
      have hxct : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := by
        have hle1 : (A ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≤
            Subgroup.centralizer ({t} : Set G) := by
          refine le_trans inf_le_left ?_
          intro y hy
          exact (Subgroup.mem_inf.mp (h.A_le hy)).2
        have hsup : ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) ≤
            Subgroup.centralizer ({t} : Set G) := by
          refine sup_le hle1 ?_
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hyc := commute_t_of_mem_P h hy
          calc y * t = (t * y * t⁻¹) * t := by rw [hyc]
            _ = t * y := by group
        exact hsup hxAP
      rw [Subgroup.mem_centralizer_singleton_iff] at hxct
      rw [← hxct, mul_assoc, mul_inv_cancel, mul_one] at h2
      exact mul_eq_one_iff_eq_inv.mpr h2
    have hx1' : (x : G) = 1 := eq_one_of_mem_sup_of_sq_eq_one h hxAP hx2'
    exact Subtype.ext (by simpa using hx1')

/-- The involutions of `N_H(P) = H ⊓ N_G(P)`, viewed inside `N_G(P)`, are exactly `u`
(§5 Prop. 2 (c), `|Inv N_H(P)| = 1`). -/
theorem invNormalizer (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (centD H t : Set G)) :
    (involutions (((H ⊓ NGP P).subgroupOf (NGP P)) : Set ↥(NGP P))).ncard = 1 := by
  classical
  have hse : IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) :=
    stronglyEmbedded_normalizer hC4 h
  have ht𝒢 : t ∈ NGP P := mem_normalizer_t h
  have ht'H : (⟨t, ht𝒢⟩ : ↥(NGP P)) ∉ (H ⊓ NGP P).subgroupOf (NGP P) := fun hmem =>
    h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (H := (H ⊓ NGP P).subgroupOf (NGP P)) hse
    (by rw [← Subgroup.orderOf_coe]; exact h.invol) ht'H
  have hDK := kset_inf_normalizer_trivial hFT h
  have hDK' : (Work.ThmF.Kset ((H ⊓ NGP P).subgroupOf (NGP P)) (⟨t, ht𝒢⟩ : ↥(NGP P))).ncard = 1 :=
    hDK
  exact hcard ▸ hDK'

/-! ## `N_G(P)` has 2-rank `1` -/

/-- `N_G(P)` has no four-group: it has a strongly embedded subgroup `N_H(P)` with a unique
involution, so a four-group in `N_G(P)` would give `N_H(P)` at least two involutions
(`cardInvGeTwo`). -/
theorem not_hasFourGroup_normalizer (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (centD H t : Set G)) :
    ¬ Submission.Blueprint.HasFourGroup ↥(NGP P) := by
  intro h4
  have hse : IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) :=
    stronglyEmbedded_normalizer hC4 h
  have h2 := Work.ThmF.Bender.cardInvGeTwo (H := (H ⊓ NGP P).subgroupOf (NGP P)) hse h4
  have h1 := invNormalizer hFT hC4 h u hu
  omega

/-! ## `N_G(P)` acts 2-transitively on `Ω_P` -/

/-- Peterfalvi I Ch. III §5 Prop. 2 (c): `N_G(P)` acts 2-transitively on the set `Ω_P` of fixed
points of `P`, by App. II(5) (`app2_5`) applied to the 2-transitive action of `G` on `G ⧸ H`
(Theorem A, `ThmAProp`). -/
theorem normalizerTwoTransitive (hA : Submission.Blueprint.ThmAProp)
    (h : Design.Setup5 G H t W p P A r) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (NGP P) (fixedPts H P) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have h2 : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hA G h.sit.1.1 H h.se
  have hab : (Work.DoubleTransitivity.pt H : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
    intro hcon
    exact h.notMem ((Work.DoubleTransitivity.mk_one_eq_iff (H := H)).mp hcon.symm)
  have hstab : MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
      MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = twoPoint H t := by
    rw [show (Work.DoubleTransitivity.pt H : G ⧸ H) = QuotientGroup.mk (1 : G) from rfl]
    rw [Work.ThreePoints.stabilizer_mk H 1, Work.ThreePoints.stabilizer_mk H t,
      Work.DoubleTransitivity.conj_one]
  have hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P
      (MulAction.stabilizer G (Work.DoubleTransitivity.pt H) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H)) := by
    rw [hstab]
    exact ⟨h.P_syl.2.1, h.P_syl.1, h.P_syl.2.2⟩
  exact Work.DoubleTransitivity.App2.app2_5 (X := G) (E := G ⧸ H) (a :=
    Work.DoubleTransitivity.pt H) (b := (QuotientGroup.mk t : G ⧸ H)) hab h2 hP

/-! ## The point stabiliser `N_H(P)/K` is a coatom -/

/-- `N_H(P)` is a maximal subgroup of `N_G(P)` (`maximal_of_twoTransitive` applied to the
2-transitive action of `N_G(P)` on `Ω_P`). -/
theorem isCoatom_normalizer (hA : Submission.Blueprint.ThmAProp)
    (h : Design.Setup5 G H t W p P A r) :
    IsCoatom ((H ⊓ NGP P).subgroupOf (NGP P)) := by
  classical
  set 𝒢 : Subgroup G := NGP P with h𝒢
  have hPleV : P ≤ centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have h2t := normalizerTwoTransitive hA h
  have h2t' : Work.DoubleTransitivity.IsTwoTransitiveOnSub 𝒢 (fixedPts H P) := by
    rw [h𝒢]; exact h2t
  rw [isCoatom_iff_ge_of_le]
  constructor
  · intro htop
    have hle : 𝒢 ≤ H := by
      intro g hg
      have h1 : (⟨g, hg⟩ : ↥𝒢) ∈ (H ⊓ 𝒢).subgroupOf 𝒢 := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h1).1
    exact h.notMem (hle (mem_normalizer_t h))
  · intro M hMne hHM
    have hHM' : 𝒢 ⊓ H ≤ M.map (Subgroup.subtype 𝒢) := by
      intro y hy
      obtain ⟨hy𝒢, hyH⟩ := Subgroup.mem_inf.mp hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy𝒢⟩,
        hHM (Subgroup.mem_subgroupOf.mpr (show y ∈ H ⊓ 𝒢 from ⟨hyH, hy𝒢⟩)), rfl⟩
    have hMF' : M.map (Subgroup.subtype 𝒢) ≤ 𝒢 := Subgroup.map_subtype_le M
    rcases Work.ThreePoints.P3NeBot.maximal_of_twoTransitive (H := H) (F := 𝒢)
        (M := M.map (Subgroup.subtype 𝒢)) (X := P) hPleH le_rfl h3 h2t' hHM' hMF' with h | h
    · intro z hz
      have h1 : (z : G) ∈ 𝒢 ⊓ H := le_of_eq h (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
      exact Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_inf.mp h1).2, (Subgroup.mem_inf.mp h1).1⟩
    · exact absurd (by
        refine le_antisymm le_top fun z _ => ?_
        have hz' : (z : G) ∈ M.map (Subgroup.subtype 𝒢) := le_of_eq h.symm z.2
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz'
        rwa [Subtype.ext hwz] at hw) hMne

/-! ## Main theorem -/

theorem ngpInverted (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    {x : G} (hxN : x ∈ Subgroup.normalizer (P : Set G)) (hxodd : Odd (orderOf x))
    (hinv : u * x * u⁻¹ = x⁻¹) :
    orderOf x ∣ orderOf (u * t) := by
  classical
  have hPleH : P ≤ H := (h.P_le.trans inf_le_right).trans (inf_le_left.trans inf_le_left)
  have hu𝒢 : u ∈ NGP P := mem_normalizer_u h hu
  have ht𝒢 : t ∈ NGP P := mem_normalizer_t h
  have hx𝒢 : x ∈ NGP P := hxN
  have hut𝒢 : u * t ∈ NGP P := (NGP P).mul_mem hu𝒢 ht𝒢
  -- ## the kernel `K₀` of the action on `Ω_P` is contained in `V = centD H t`, hence odd
  have hKleV : (KerP H P).map (Subgroup.subtype (NGP P)) ≤ centD H t := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hy
    have hfix : ∀ ω : OmP H P, γ • ω = ω := fun ω =>
      congrArg (fun e : Equiv.Perm (OmP H P) => e ω) (MonoidHom.mem_ker.mp hγ)
    have hγH : (γ : G) ∈ H := by
      have h1 : (γ : G) • (Work.DoubleTransitivity.pt H) = Work.DoubleTransitivity.pt H := by
        have h2 := congrArg (fun ω : OmP H P => (ω : G ⧸ H)) (hfix (ptOmP hPleH))
        simpa [ptOmP] using h2
      exact Work.ThreePoints.P3NeBot.smul_pt_eq_pt_iff.mp h1
    have hγt : (γ : G) ∈ Submission.Blueprint.conj t H := by
      have hmem0 : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H P := by
        intro z hz
        rw [Work.DoubleTransitivity.smul_mk, QuotientGroup.eq]
        simpa using H.inv_mem (hPleH hz)
      have hmemt : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H P := by
        have hh : (t : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H P :=
          smul_mem_omP ht𝒢 hmem0
        simpa using hh
      have h3 := congrArg (fun ω : OmP H P => (ω : G ⧸ H))
        (hfix (⟨QuotientGroup.mk t, hmemt⟩ : OmP H P))
      have h4 : (γ : G) • (QuotientGroup.mk t : G ⧸ H) = QuotientGroup.mk t := by
        simpa using h3
      exact (Work.DoubleTransitivity.smul_mk_eq_mk_iff).mp h4
    have hxD : (γ : G) ∈ twoPoint H t := ⟨hγH, hγt⟩
    have hxAP : (γ : G) ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G) := by
      rw [← (Work.NormalComplement.sec4_one_c hFT h.toSetup45A).1]
      exact ⟨hxD, γ.2⟩
    have hle : ((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) ≤ centD H t := by
      rw [← h.A_sup]
      exact sup_le_sup_right inf_le_left P
    exact hle hxAP
  have hoddV : Odd (Nat.card ↥(centD H t)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  have hoddK : Odd (Nat.card ↥(KerP H P)) := by
    have hcard : Nat.card ↥(KerP H P) =
        Nat.card ↥((KerP H P).map (Subgroup.subtype (NGP P))) :=
      (Subgroup.card_map_of_injective (K := KerP H P)
        (f := Subgroup.subtype (NGP P)) Subtype.coe_injective).symm
    rw [hcard]
    exact Odd.of_dvd_nat hoddV (Subgroup.card_dvd_of_le hKleV)
  -- ## the hypotheses of App. III
  have hse𝒢 : IsStronglyEmbedded ((H ⊓ NGP P).subgroupOf (NGP P)) :=
    stronglyEmbedded_normalizer hC4 h
  have hKleH' : KerP H P ≤ (H ⊓ NGP P).subgroupOf (NGP P) := by
    intro γ hγ
    have hmem : (γ : G) ∈ centD H t := hKleV (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
    exact Subgroup.mem_subgroupOf.mpr
      ⟨(show centD H t ≤ H from inf_le_left.trans inf_le_left) hmem, γ.2⟩
  have hstab : MulAction.stabilizer (↥(NGP P) ⧸ KerP H P) (ptOmP hPleH) =
      ((H ⊓ NGP P).subgroupOf (NGP P)).map (QuotientGroup.mk' (KerP H P)) := by
    ext z
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (KerP H P) z
    rw [Subgroup.mem_map]
    constructor
    · intro hz
      rw [MulAction.mem_stabilizer_iff] at hz
      rw [quotient_smul_mk_omP] at hz
      exact ⟨γ, Subgroup.mem_subgroupOf.mpr ⟨(smul_ptOmP_eq_iff hPleH γ).mp hz, γ.2⟩, rfl⟩
    · rintro ⟨γ, hγ, hγz⟩
      rw [← hγz, MulAction.mem_stabilizer_iff, quotient_smul_mk_omP]
      exact (smul_ptOmP_eq_iff hPleH γ).mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hγ)).1
  have hfaith : ∀ g : ↥(NGP P) ⧸ KerP H P, (∀ ω : OmP H P, g • ω = ω) → g = 1 := by
    intro g hg
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (KerP H P) g
    rw [QuotientGroup.mk'_apply]
    refine (QuotientGroup.eq_one_iff γ).mpr ((mem_KerP_iff γ).mpr ?_)
    intro ω
    rw [← quotient_smul_mk_omP]
    exact hg ω
  have hpre : MulAction.IsPretransitive (↥(NGP P) ⧸ KerP H P) (OmP H P) := by
    refine ⟨fun ω ω' => ?_⟩
    by_cases hd : (ω : G ⧸ H) = (ω' : G ⧸ H)
    · exact ⟨1, by rw [one_smul]; exact Subtype.ext hd⟩
    · obtain ⟨y, hy, hyc, -⟩ := (normalizerTwoTransitive hA h)
        (ω : G ⧸ H) ω.2 (ω' : G ⧸ H) ω'.2 hd (ω' : G ⧸ H) ω'.2 (ω : G ⧸ H) ω.2 (fun h => hd h.symm)
      exact ⟨QuotientGroup.mk' (KerP H P) ⟨y, hy⟩, by
        rw [quotient_smul_mk_omP]; exact Subtype.ext hyc⟩
  have hrank : ¬ Submission.Blueprint.HasFourGroup (↥(NGP P) ⧸ KerP H P) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient (KerP H P) hoddK
      (not_hasFourGroup_normalizer hFT hC4 h u hu)
  have hSE : IsStronglyEmbedded
      (MulAction.stabilizer (↥(NGP P) ⧸ KerP H P) (ptOmP hPleH)) := by
    have h1 := Work.ThreePoints.isStronglyEmbedded_map_quotient (KerP H P) hoddK hKleH' hse𝒢
    rwa [← hstab] at h1
  have hCoat : IsCoatom (MulAction.stabilizer (↥(NGP P) ⧸ KerP H P) (ptOmP hPleH)) := by
    have h1 := Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le
      (QuotientGroup.mk'_surjective (KerP H P)) (isCoatom_normalizer hA h)
      (by rw [QuotientGroup.ker_mk']; exact hKleH')
    rwa [← hstab] at h1
  -- ## App. III
  obtain ⟨f, Q, hfp, hQn, hQne, hQab, hQexp, hQinf, hQsup, huniqFT, hprod, hinvQ, -⟩ :=
    hIII (↥(NGP P) ⧸ KerP H P) (OmP H P) (ptOmP hPleH) hpre hfaith hrank hSE hCoat
  -- ## the images of `u`, `t`, `x` in `F = N_G(P)/K₀`
  have hu2bar : orderOf (QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩) = 2 := by
    have hu_ord : orderOf (⟨u, hu𝒢⟩ : ↥(NGP P)) = 2 := by simpa using hu.2.1
    have hdvd : orderOf (QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩) ∣ 2 := by
      rw [← hu_ord]
      exact orderOf_map_dvd _ _
    have hne1 : QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩ ≠ 1 := by
      intro hcon
      have h1 : (⟨u, hu𝒢⟩ : ↥(NGP P)) ∈ KerP H P := (QuotientGroup.eq_one_iff _).mp hcon
      have h2 : u ∈ centD H t := hKleV (Subgroup.mem_map.mpr ⟨_, h1, rfl⟩)
      have hcom : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp h2.2).symm
      have h4 : u * u = 1 := by
        have := pow_orderOf_eq_one u; rw [hu.2.1] at this; simpa [pow_two] using this
      have h5 : t * t = 1 := by
        have := pow_orderOf_eq_one t; rw [h.invol] at this; simpa [pow_two] using this
      have h3 : (u * t) * (u * t) = 1 := by
        calc (u * t) * (u * t) = u * (t * u) * t := by group
          _ = u * (u * t) * t := by rw [hcom]
          _ = (u * u) * (t * t) := by group
          _ = 1 := by rw [h4, h5, one_mul]
      have h6 : Odd (orderOf (u * t)) :=
        Work.ThmF.Bender.twoInvolutionsOdd h.se hu.1 hu.2.1 h.invol h.notMem
      have h7 : orderOf (u * t) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h3)
      have h8 : orderOf (u * t) ≠ 1 := by
        intro h9
        have h10 : u * t = 1 := orderOf_eq_one_iff.mp h9
        exact h.notMem (by
          have h11 : t = u⁻¹ := (mul_eq_one_iff_inv_eq.mp h10).symm
          rw [h11]
          exact H.inv_mem hu.1)
      rcases (Nat.dvd_prime Nat.prime_two).mp h7 with h | h
      · exact h8 h
      · exact (Nat.not_even_iff_odd.mpr h6) (by rw [h]; norm_num)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · exact h
  have ht2bar : orderOf (QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩) = 2 := by
    have ht_ord : orderOf (⟨t, ht𝒢⟩ : ↥(NGP P)) = 2 := by simpa using h.invol
    have hdvd : orderOf (QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩) ∣ 2 := by
      rw [← ht_ord]
      exact orderOf_map_dvd _ _
    have hne1 : QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩ ≠ 1 := by
      intro hcon
      have h1 : (⟨t, ht𝒢⟩ : ↥(NGP P)) ∈ KerP H P := (QuotientGroup.eq_one_iff _).mp hcon
      have h2 : t ∈ centD H t := hKleV (Subgroup.mem_map.mpr ⟨_, h1, rfl⟩)
      exact h.notMem ((show centD H t ≤ H from inf_le_left.trans inf_le_left) h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · exact h
  have hne : QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩ ≠
      QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩ := by
    intro hcon
    have h1 : QuotientGroup.mk' (KerP H P) ((⟨u, hu𝒢⟩ : ↥(NGP P))⁻¹ * ⟨t, ht𝒢⟩) = 1 := by
      rw [map_mul, map_inv, hcon, inv_mul_cancel]
    have h2 : ((⟨u, hu𝒢⟩ : ↥(NGP P))⁻¹ * ⟨t, ht𝒢⟩) ∈ KerP H P :=
      (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at h1)
    have h3 : (((⟨u, hu𝒢⟩ : ↥(NGP P))⁻¹ * ⟨t, ht𝒢⟩ : ↥(NGP P)) : G) ∈ centD H t :=
      hKleV (Subgroup.mem_map.mpr ⟨_, h2, rfl⟩)
    have h4 : (((⟨u, hu𝒢⟩ : ↥(NGP P))⁻¹ * ⟨t, ht𝒢⟩ : ↥(NGP P)) : G) ∈ H :=
      (show centD H t ≤ H from inf_le_left.trans inf_le_left) h3
    have h5 : u⁻¹ * t ∈ H := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h4
    exact h.notMem (by
      have h6 : t = u * (u⁻¹ * t) := by group
      rw [h6]; exact H.mul_mem hu.1 h5)
  -- ## `f = orderOf (ū t̄)` divides `orderOf (u * t)`
  have hkey := hprod (QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩)
    (QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩) hu2bar ht2bar hne
  have hf_eq : f = orderOf (QuotientGroup.mk' (KerP H P) ⟨u * t, hut𝒢⟩) := by
    have h1 : (QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩) *
        (QuotientGroup.mk' (KerP H P) ⟨t, ht𝒢⟩) =
        QuotientGroup.mk' (KerP H P) ⟨u * t, hut𝒢⟩ := by
      rw [← map_mul]
      exact congrArg _ (Subtype.ext rfl)
    rw [← hkey.2, h1]
  have hf_dvd : f ∣ orderOf (u * t) := by
    have hut_ord : orderOf (⟨u * t, hut𝒢⟩ : ↥(NGP P)) = orderOf (u * t) :=
      (Subgroup.orderOf_coe _).symm
    rw [hf_eq, ← hut_ord]
    exact orderOf_map_dvd _ _
  -- ## `x` maps into `Q`, so `x ^ f ∈ K₀`
  have hxodd' : Odd (orderOf (QuotientGroup.mk' (KerP H P) ⟨x, hx𝒢⟩)) := by
    have hdvd : orderOf (QuotientGroup.mk' (KerP H P) ⟨x, hx𝒢⟩) ∣ orderOf x := by
      have := orderOf_map_dvd (QuotientGroup.mk' (KerP H P)) (⟨x, hx𝒢⟩ : ↥(NGP P))
      rwa [← Subgroup.orderOf_coe (⟨x, hx𝒢⟩ : ↥(NGP P))] at this
    exact Odd.of_dvd_nat hxodd hdvd
  have hinv' : QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩ * QuotientGroup.mk' (KerP H P) ⟨x, hx𝒢⟩ *
      (QuotientGroup.mk' (KerP H P) ⟨u, hu𝒢⟩)⁻¹ =
        (QuotientGroup.mk' (KerP H P) ⟨x, hx𝒢⟩)⁻¹ := by
    have h1 : (⟨u, hu𝒢⟩ : ↥(NGP P)) * ⟨x, hx𝒢⟩ * ⟨u, hu𝒢⟩⁻¹ = ⟨x, hx𝒢⟩⁻¹ :=
      Subtype.ext hinv
    have h2 := congrArg (QuotientGroup.mk' (KerP H P)) h1
    simp only [map_mul, map_inv] at h2
    exact h2
  have hxmem : QuotientGroup.mk' (KerP H P) ⟨x, hx𝒢⟩ ∈ Q := hinvQ _ hu2bar _ hxodd' hinv'
  have hxf : (⟨x, hx𝒢⟩ : ↥(NGP P)) ^ f ∈ KerP H P := by
    have h1 : QuotientGroup.mk' (KerP H P) ((⟨x, hx𝒢⟩ : ↥(NGP P)) ^ f) = 1 := by
      rw [map_pow]; exact hQexp _ hxmem
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hxfV : (x : G) ^ f ∈ centD H t := by
    have h1 : (((⟨x, hx𝒢⟩ : ↥(NGP P)) ^ f : ↥(NGP P)) : G) ∈ centD H t :=
      hKleV (Subgroup.mem_map.mpr ⟨_, hxf, rfl⟩)
    simpa [Subgroup.coe_pow] using h1
  -- ## `u` centralises and inverts `x ^ f`
  have hu_cent : u * x ^ f * u⁻¹ = x ^ f := by
    have h := (Subgroup.mem_centralizer_iff.mp hu.2.2) (x ^ f) hxfV
    rw [← h]; group
  have hu_inv : u * x ^ f * u⁻¹ = (x ^ f)⁻¹ := by
    have h2 : (MulAut.conj u) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hinv
    have h3 : (MulAut.conj u) (x ^ f) = (x ^ f)⁻¹ := by rw [map_pow, h2, inv_pow]
    rw [← MulAut.conj_apply u (x ^ f)]
    exact h3
  have hx2f : x ^ (2 * f) = 1 := by
    have h1 : x ^ f = (x ^ f)⁻¹ := hu_cent.symm.trans hu_inv
    have h2 : x ^ f * x ^ f = 1 := by
      nth_rewrite 1 [h1]
      rw [inv_mul_cancel]
    rw [mul_comm 2 f, pow_mul, pow_two, h2]
  have hdvd2f : orderOf x ∣ 2 * f := orderOf_dvd_iff_pow_eq_one.mpr hx2f
  have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hxodd
  exact dvd_trans (hcop.dvd_of_dvd_mul_left hdvd2f) hf_dvd

end Work.NormalComplement.Sec5Fix
