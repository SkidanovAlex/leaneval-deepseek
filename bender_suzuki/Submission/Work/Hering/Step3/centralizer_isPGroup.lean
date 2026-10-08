import Mathlib
import Submission.Work.Hering.Perm.Defs
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.V.card_eq_two_pow
import Submission.Work.Hering.Perm.appII5
import Submission.Work.Hering.Step3.Defs
import Submission.Work.Hering.Step3.NormalizerQuotient
import Submission.Work.Hering.Step3.pow_orderOf_sq_is_involution
import Submission.Work.Hering.Step3.mem_centralizer_of_mem_invSubgroup_of_mem_normalizer
import Submission.Work.Hering.Step3.isTwoTransitiveAction_involutions
import Submission.Work.Hering.Step3.stabilizer_inf_eq_centralizer
import Submission.Work.Hering.Step3.exists_pair_of_le_invSubgroup
import Submission.Work.Hering.Step3.exists_isSylowSubgroup_of_isPGroup_le
import Submission.Work.Hering.Step3.orderOf_fixedToQuot
import Submission.Work.Hering.Step3.fixedToQuot_mul_comm
import Submission.Work.Hering.Step3.isPGroup_zpowers_of_orderOf_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I Chapter IV §2, Step 3: `C_G(U)` is a `2`-group

Let `G` be a finite group of 2-rank `≥ 2` acting doubly transitively by conjugation on its
involutions (`DTInv G`, `HasFourGroup G`), minimal among such groups for the induction
hypothesis `(E2)` (`hE2`), and let `U ≤ V = Inv(G) ∪ {1}` be a subgroup of order `4`.  Peterfalvi
I, Chapter IV §2 Step 3 (p. 191) then states that `C_G(U)` is a `2`-group.

The proof follows the source.  Let `P` be an odd `p`-Sylow subgroup of `C_G(U)`; `P` is a Sylow
`p`-subgroup of a two-point stabiliser of the conjugation action of `G` on `Inv(G)`, so by
Appendix II(5) (`Work.Hering.Perm.appII5`) the normaliser `N_G(P)` is doubly transitive on the
set `F = C_G(P) ∩ V^#` of involutions fixed by `P`.  Every involution of `N_G(P)/P` is the image
of such a fixed involution (lifting `x` with `x² ∈ P` to the involution `x ^ |x²|`, which is fixed
by `P` by §2 Step 2), so `N_G(P)/P` acts doubly transitively on its involutions and has 2-rank
`≥ 2` (it contains the image of `U`).  Applying `(E2)` to `N_G(P)/P` and comparing cardinalities
(`|N_G(P)/P| · |P| = |N_G(P)| ≤ |G| ≤ |N_G(P)/P|`) forces `P = 1`; hence every odd `p`-subgroup of
`C_G(U)` is trivial and `C_G(U)` is a `2`-group.

## Universes

`Work.Hering.Step3.centralizer_isPGroup` is universe-polymorphic, while both the given
hypothesis `hAppII5 : AppII5Prop` and the minimality hypothesis `hE2` are pinned to particular
universes (`AppII5Prop.{u,v}` and `Type 0` respectively).  Since `AppII5Prop` is a theorem of the
workspace at *all* universes (`Work.Hering.Perm.appII5`), the argument is carried out with that
theorem in place of `hAppII5`, and the Type-`0`-only hypothesis `hE2` is transferred to arbitrary
universes by `not_hasFourGroup_of_lt` (replace a finite group by an isomorphic group in `Type 0`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Hering.Step3

open LeanEval.GroupTheory.Defs
open Work.Hering

private lemma orderOf_symm_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : H) :
    orderOf (e.symm x) = orderOf x :=
  orderOf_injective (e.symm : H →* G) e.symm.injective x

private lemma orderOf_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    orderOf (e x) = orderOf x :=
  orderOf_injective (e : G →* H) e.injective x

/-- `DTInv` is preserved by group isomorphisms. -/
private theorem dtInv_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : DTInv G) :
    DTInv H := by
  intro a b c d ha hb hc hd hab hcd
  have ha' : orderOf (e.symm a) = 2 := by rw [orderOf_symm_mulEquiv e a, ha]
  have hb' : orderOf (e.symm b) = 2 := by rw [orderOf_symm_mulEquiv e b, hb]
  have hc' : orderOf (e.symm c) = 2 := by rw [orderOf_symm_mulEquiv e c, hc]
  have hd' : orderOf (e.symm d) = 2 := by rw [orderOf_symm_mulEquiv e d, hd]
  have hab' : e.symm a ≠ e.symm b := fun hh => hab (e.symm.injective hh)
  have hcd' : e.symm c ≠ e.symm d := fun hh => hcd (e.symm.injective hh)
  obtain ⟨g, hg1, hg2⟩ := h (e.symm a) (e.symm b) (e.symm c) (e.symm d) ha' hb' hc' hd' hab' hcd'
  refine ⟨e g, ?_, ?_⟩
  · have h1 : a = e (e.symm a) := (e.apply_symm_apply a).symm
    rw [h1, ← map_mul, ← map_inv, ← map_mul, hg1, e.apply_symm_apply]
  · have h1 : b = e (e.symm b) := (e.apply_symm_apply b).symm
    rw [h1, ← map_mul, ← map_inv, ← map_mul, hg2, e.apply_symm_apply]

/-- `HasFourGroup` is preserved by group isomorphisms. -/
private theorem hasFourGroup_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : HasFourGroup G) : HasFourGroup H := by
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ := h
  refine ⟨e a, e b, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_mulEquiv e a, ha]
  · rw [orderOf_mulEquiv e b, hb]
  · exact fun hh => hab (e.injective hh)
  · rw [← map_mul, ← map_mul, hcomm]

/-- The minimality hypothesis `(E2)` is stated only for groups in `Type 0`, but it propagates to
arbitrary universes: any finite group of smaller cardinality can be replaced, up to isomorphism,
by one in `Type 0` (`Finite.exists_type_univ_nonempty_mulEquiv`). -/
private theorem not_hasFourGroup_of_lt {G : Type*} [Group G] [Finite G]
    (hE2 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      Even (Nat.card F) → DTInv F → ¬ HasFourGroup F)
    {F : Type*} [Group F] [Finite F] (hlt : Nat.card F < Nat.card G)
    (heven : Even (Nat.card F)) (hdt : DTInv F) : ¬ HasFourGroup F := by
  obtain ⟨F₀, instF₀, finF₀, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} F
  letI : Group F₀ := instF₀
  letI : Fintype F₀ := finF₀
  have hcard : Nat.card F₀ = Nat.card F := (Nat.card_congr e.toEquiv).symm
  intro h4
  exact (hE2 F₀ (by rw [hcard]; exact hlt) (by rw [hcard]; exact heven)
    (dtInv_of_mulEquiv e hdt)) (hasFourGroup_of_mulEquiv e h4)

private theorem inf_with_invSubgroup_eq_bot {G : Type*} [Group G] (hDT : DTInv G)
    (h4 : HasFourGroup G) {P : Subgroup G} (hPodd : Odd (Nat.card P)) :
    P ⊓ invSubgroup hDT h4 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyP, hyV⟩ := hy
  by_contra hy1
  have h2 : y * y = 1 := pow_two_eq_one_of_mem_invSubgroup hDT h4 hyV
  have hord : orderOf y = 2 := orderOf_eq_two_of_sq_eq_one h2 hy1
  have hdvd : orderOf y ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hyP
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr hdvd)

private theorem fixedToQuot_injective {G : Type*} [Group G] (hDT : DTInv G) (h4 : HasFourGroup G)
    {P : Subgroup G} (hPodd : Odd (Nat.card P)) {s t : {x : G // x ∈ involutions G}}
    (hs : s ∈ involutionsFixedBy P) (ht : t ∈ involutionsFixedBy P)
    (h : fixedToQuot P s hs = fixedToQuot P t ht) : s = t := by
  have hmem : (⟨(s : G), mem_normalizer_of_mem_involutionsFixedBy hs⟩ :
        ↥(Subgroup.normalizer (P : Set G)))⁻¹ *
      ⟨(t : G), mem_normalizer_of_mem_involutionsFixedBy ht⟩ ∈
        P.subgroupOf (Subgroup.normalizer (P : Set G)) := by
    apply (QuotientGroup.eq (s := P.subgroupOf (Subgroup.normalizer (P : Set G)))).mp
    simpa only [fixedToQuot, QuotientGroup.mk'_apply] using h
  have hmemP : (s : G)⁻¹ * (t : G) ∈ P := by
    have h3 := (Subgroup.mem_subgroupOf (H := P)
      (K := Subgroup.normalizer (P : Set G))).mp hmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using h3
  have hst : (s : G) * (t : G) ∈ P := by
    have hsi : (s : G)⁻¹ = (s : G) := eq_inv_of_mem_involutions s.2
    rwa [hsi] at hmemP
  have hstV : (s : G) * (t : G) ∈ invSubgroup hDT h4 :=
    Subgroup.mul_mem _ (involutions_subset_invSubgroup hDT h4 s.2)
      (involutions_subset_invSubgroup hDT h4 t.2)
  have hbot : (s : G) * (t : G) ∈ (⊥ : Subgroup G) := by
    rw [← inf_with_invSubgroup_eq_bot hDT h4 hPodd]
    exact Subgroup.mem_inf.mpr ⟨hst, hstV⟩
  have hone : (s : G) * (t : G) = 1 := by simpa using hbot
  refine Subtype.ext ?_
  have h4' : (t : G)⁻¹ = (s : G) := inv_eq_of_mul_eq_one_left hone
  rw [eq_inv_of_mem_involutions (x := (t : G)) t.2] at h4'
  exact h4'.symm

private theorem exists_fixedToQuot_eq {G : Type*} [Group G] [Finite G] (hDT : DTInv G)
    (h4 : HasFourGroup G) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (z : ↥(Subgroup.normalizer (P : Set G)) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)))
    (hz : orderOf z = 2) :
    ∃ (s : {x : G // x ∈ involutions G}) (hs : s ∈ involutionsFixedBy P),
      fixedToQuot P s hs = z := by
  classical
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (P.subgroupOf (Subgroup.normalizer (P : Set G))) z
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hxP : (x : G) ∉ P := by
    intro hmem
    have hxmem : x ∈ (QuotientGroup.mk'
        (P.subgroupOf (Subgroup.normalizer (P : Set G)))).ker := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.mem_subgroupOf.mpr hmem
    have hx1 : QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) x = 1 :=
      MonoidHom.mem_ker.mp hxmem
    rw [hx] at hx1
    rw [hx1] at hz
    simp at hz
  have hx2P : (x : G) ^ 2 ∈ P := by
    have h1 : (QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) x) ^ 2 = 1 := by
      rw [hx]; exact hz2
    have h2 : QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G)))
        (x ^ 2) = 1 := by
      rw [map_pow]; exact h1
    have h3 : x ^ 2 ∈ (QuotientGroup.mk'
        (P.subgroupOf (Subgroup.normalizer (P : Set G)))).ker :=
      MonoidHom.mem_ker.mpr h2
    rw [QuotientGroup.ker_mk'] at h3
    have h4 := (Subgroup.mem_subgroupOf (H := P)
      (K := Subgroup.normalizer (P : Set G))).mp h3
    simpa only [Subgroup.coe_pow, Subtype.coe_mk] using h4
  obtain ⟨hyord, hymem⟩ :=
    pow_orderOf_sq_is_involution (x := (x : G)) hxP hx2P hPodd
  have hyV : (x : G) ^ orderOf ((x : G) ^ 2) ∈ invSubgroup hDT h4 :=
    (mem_invSubgroup hDT h4).mpr (Or.inl hyord)
  have hyN : (x : G) ^ orderOf ((x : G) ^ 2) ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.pow_mem (Subgroup.normalizer (P : Set G)) x.2 _
  have hyC : (x : G) ^ orderOf ((x : G) ^ 2) ∈ Subgroup.centralizer (P : Set G) :=
    mem_centralizer_of_mem_invSubgroup_of_mem_normalizer hDT h4 hPodd hyV hyN
  refine ⟨⟨(x : G) ^ orderOf ((x : G) ^ 2), hyord⟩, ?_, ?_⟩
  · exact mem_involutionsFixedBy_iff.mpr hyC
  · rw [fixedToQuot, ← hx]
    apply (QuotientGroup.eq (s := P.subgroupOf (Subgroup.normalizer (P : Set G)))).mpr
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using hymem

theorem dtInv_quotient_normalizer {G : Type*} [Group G] [Finite G] (hDT : DTInv G)
    (h4 : HasFourGroup G) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (h2 : IsTwoTransitiveOnFixed G {x : G // x ∈ involutions G}
      (Subgroup.normalizer (P : Set G)) P) :
    DTInv (↥(Subgroup.normalizer (P : Set G)) ⧸
      P.subgroupOf (Subgroup.normalizer (P : Set G))) := by
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨sa, hsa, hsa'⟩ := exists_fixedToQuot_eq hDT h4 hPodd a ha
  obtain ⟨sb, hsb, hsb'⟩ := exists_fixedToQuot_eq hDT h4 hPodd b hb
  obtain ⟨sc, hsc, hsc'⟩ := exists_fixedToQuot_eq hDT h4 hPodd c hc
  obtain ⟨sd, hsd, hsd'⟩ := exists_fixedToQuot_eq hDT h4 hPodd d hd
  have hsab : sa ≠ sb := by
    intro h
    subst sa
    exact hab (hsa'.symm.trans hsb')
  have hscd : sc ≠ sd := by
    intro h
    subst sc
    exact hcd (hsc'.symm.trans hsd')
  obtain ⟨n, hnN, hna, hnb⟩ := h2 sa sb sc sd hsa hsb hsc hsd hsab hscd
  refine ⟨QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) ⟨n, hnN⟩, ?_, ?_⟩
  · rw [← hsa', ← hsc']
    simp only [fixedToQuot]
    simp only [← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    have h1 := congrArg (fun t : {x : G // x ∈ involutions G} => (t : G)) hna
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, coe_smul_involutions] using h1
  · rw [← hsb', ← hsd']
    simp only [fixedToQuot]
    simp only [← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    have h1 := congrArg (fun t : {x : G // x ∈ involutions G} => (t : G)) hnb
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk, coe_smul_involutions] using h1

private theorem hasFourGroup_normalizer_quotient {G : Type*} [Group G] (hDT : DTInv G)
    (h4 : HasFourGroup G) {P : Subgroup G} (hPodd : Odd (Nat.card P))
    {s t : {x : G // x ∈ involutions G}} (hs : s ∈ involutionsFixedBy P)
    (ht : t ∈ involutionsFixedBy P) (hst : s ≠ t)
    (hcomm : (s : G) * (t : G) = (t : G) * (s : G)) :
    HasFourGroup (↥(Subgroup.normalizer (P : Set G)) ⧸
      P.subgroupOf (Subgroup.normalizer (P : Set G))) := by
  refine ⟨fixedToQuot P s hs, fixedToQuot P t ht, orderOf_fixedToQuot hPodd s hs,
    orderOf_fixedToQuot hPodd t ht, ?_, fixedToQuot_mul_comm hs ht hcomm⟩
  intro h
  exact hst (fixedToQuot_injective hDT h4 hPodd hs ht h)


open LeanEval.GroupTheory.Defs
open Work.Hering

private theorem sylow_odd_eq_bot {G : Type*} [Group G] [Finite G] (hAppII5 : AppII5Prop)
    (hDT : DTInv G) (h4 : HasFourGroup G)
    (hE2 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      Even (Nat.card F) → DTInv F → ¬ HasFourGroup F)
    {U : Subgroup G} (hU : U ≤ invSubgroup hDT h4) (hUcard : Nat.card U = 4)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQ : IsSylowSubgroup p Q (Subgroup.centralizer (U : Set G))) : Q = ⊥ := by
  classical
  haveI hfact : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hfinG : Fintype G := Fintype.ofFinite G
  obtain ⟨a, b, haU, hbU, ha2, hb2, hab, hUeq⟩ :=
    exists_pair_of_le_invSubgroup hDT h4 hU hUcard
  have hstab : MulAction.stabilizer G (⟨a, ha2⟩ : {x : G // x ∈ involutions G}) ⊓
      MulAction.stabilizer G (⟨b, hb2⟩ : {x : G // x ∈ involutions G}) =
      Subgroup.centralizer (U : Set G) :=
    stabilizer_inf_eq_centralizer ha2 hb2 hUeq
  have hQsyl : IsSylowSubgroup p Q (MulAction.stabilizer G (⟨a, ha2⟩ : {x : G // x ∈ involutions G}) ⊓
      MulAction.stabilizer G (⟨b, hb2⟩ : {x : G // x ∈ involutions G})) := by
    rw [hstab]; exact hQ
  have hab' : (⟨a, ha2⟩ : {x : G // x ∈ involutions G}) ≠ ⟨b, hb2⟩ := by
    intro h; exact hab (congrArg Subtype.val h)
  have h2trans : IsTwoTransitiveOnFixed G {x : G // x ∈ involutions G}
      (Subgroup.normalizer (Q : Set G)) Q :=
    Work.Hering.Perm.appII5 (X := G) (E := {x : G // x ∈ involutions G})
      (h2 := isTwoTransitiveAction_involutions hDT) (hp := hp)
      (a := (⟨a, ha2⟩ : {x : G // x ∈ involutions G}))
      (b := (⟨b, hb2⟩ : {x : G // x ∈ involutions G})) (hab := hab') (P := Q) (hP := hQsyl)
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥Q)).mp hQ.2.1
    rw [hn]
    exact Odd.pow (hp.odd_of_ne_two hp2)
  have hQleC : Q ≤ Subgroup.centralizer (U : Set G) := hQ.1
  have hfixed_a : (⟨a, ha2⟩ : {x : G // x ∈ involutions G}) ∈ involutionsFixedBy Q := by
    rw [mem_involutionsFixedBy_iff, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hQleC hy)) a haU).symm
  have hfixed_b : (⟨b, hb2⟩ : {x : G // x ∈ involutions G}) ∈ involutionsFixedBy Q := by
    rw [mem_involutionsFixedBy_iff, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hQleC hy)) b hbU).symm
  have hcomm : a * b = b * a := comm_of_dtinv hDT h4 a b ha2 hb2
  have h4Q : HasFourGroup (↥(Subgroup.normalizer (Q : Set G)) ⧸
      Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :=
    hasFourGroup_normalizer_quotient hDT h4 hQodd hfixed_a hfixed_b hab' hcomm
  have heven : Even (Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
      Q.subgroupOf (Subgroup.normalizer (Q : Set G)))) := by
    obtain ⟨z1, z2, hz1, hz2, hz12, hzc⟩ := h4Q
    have hdvd : orderOf z1 ∣ Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
        Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
      have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (↥(Subgroup.normalizer (Q : Set G)) ⧸
        Q.subgroupOf (Subgroup.normalizer (Q : Set G)))) (Subgroup.mem_top z1)
      rwa [Subgroup.card_top] at h
    rw [hz1] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  have hle : Nat.card G ≤ Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
      Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
    by_contra hlt
    push_neg at hlt
    exact not_hasFourGroup_of_lt hE2 hlt heven
      (dtInv_quotient_normalizer hDT h4 hQodd h2trans) h4Q
  have hcard_eq : Nat.card ↥(Subgroup.normalizer (Q : Set G)) =
      Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
        Q.subgroupOf (Subgroup.normalizer (Q : Set G))) *
      Nat.card ↥(Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcard_sub : Nat.card ↥(Q.subgroupOf (Subgroup.normalizer (Q : Set G))) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := Q))).toEquiv
  have hcardN : Nat.card ↥(Subgroup.normalizer (Q : Set G)) ≤ Nat.card G :=
    Subgroup.card_le_card_group _
  have h1 : Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
      Q.subgroupOf (Subgroup.normalizer (Q : Set G))) * Nat.card Q ≤
      Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
        Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by
    calc Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
            Q.subgroupOf (Subgroup.normalizer (Q : Set G))) * Nat.card Q
        = Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
            Q.subgroupOf (Subgroup.normalizer (Q : Set G))) *
          Nat.card ↥(Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := by rw [hcard_sub]
      _ = Nat.card ↥(Subgroup.normalizer (Q : Set G)) := hcard_eq.symm
      _ ≤ Nat.card G := hcardN
      _ ≤ Nat.card (↥(Subgroup.normalizer (Q : Set G)) ⧸
            Q.subgroupOf (Subgroup.normalizer (Q : Set G))) := hle
  have hQ1 : Nat.card Q ≤ 1 :=
    Nat.le_of_mul_le_mul_left (b := 1) (by simpa using h1)
      (Nat.card_pos (α := ↥(Subgroup.normalizer (Q : Set G)) ⧸
        Q.subgroupOf (Subgroup.normalizer (Q : Set G))))
  exact Subgroup.card_eq_one.mp (le_antisymm hQ1 (Nat.card_pos))

theorem centralizer_isPGroup {G : Type*} [Group G] [Finite G] (hAppII5 : AppII5Prop)
    (hDT : DTInv G) (h4 : HasFourGroup G)
    (hE2 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      Even (Nat.card F) → DTInv F → ¬ HasFourGroup F)
    {U : Subgroup G} (hU : U ≤ invSubgroup hDT h4) (hUcard : Nat.card U = 4) :
    IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)) := by
  classical
  haveI hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinG : Fintype G := Fintype.ofFinite G
  haveI hfinC : Fintype ↥(Subgroup.centralizer (U : Set G)) := Fintype.ofFinite _
  have hmain : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      P ≤ Subgroup.centralizer (U : Set G) → IsPGroup p ↥P → P = ⊥ := by
    intro p hp hp2 P hPC hPp
    obtain ⟨Q, hPQ, hQC, hQsyl⟩ := exists_isSylowSubgroup_of_isPGroup_le hp hPC hPp
    have hQbot : Q = ⊥ := sylow_odd_eq_bot hAppII5 hDT h4 hE2 hU hUcard hp hp2 hQsyl
    rw [hQbot] at hPQ
    exact le_bot_iff.mp hPQ
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card ↥(Subgroup.centralizer (U : Set G))).primeFactorsList.length, ?_⟩
  have hne : Nat.card ↥(Subgroup.centralizer (U : Set G)) ≠ 0 :=
    ne_of_gt (Nat.card_pos (α := ↥(Subgroup.centralizer (U : Set G))))
  have huniq : ∀ {d : ℕ}, Nat.Prime d →
      d ∣ Nat.card ↥(Subgroup.centralizer (U : Set G)) → d = 2 := by
    intro d hd hdn
    by_contra hd2
    haveI hfactd : Fact (Nat.Prime d) := ⟨hd⟩
    have hdn' : d ∣ Fintype.card ↥(Subgroup.centralizer (U : Set G)) := by
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card d hdn'
    let P : Subgroup G := Subgroup.zpowers (x : G)
    have hPC : P ≤ Subgroup.centralizer (U : Set G) := Subgroup.zpowers_le.mpr x.2
    have hPp : IsPGroup d ↥P :=
      isPGroup_zpowers_of_orderOf_prime hd (by rw [Subgroup.orderOf_coe, hxord])
    have hPbot := hmain d hd hd2 P hPC hPp
    have hx1 : (x : G) = 1 := by
      have hxm : (x : G) ∈ P := Subgroup.mem_zpowers _
      rw [hPbot] at hxm
      simpa using hxm
    have hxone : x = 1 := Subtype.ext hx1
    rw [hxone] at hxord
    have h1 : (1 : ℕ) = d := by simpa using hxord
    have h2 : 2 ≤ d := hd.two_le
    omega
  exact Nat.eq_prime_pow_of_unique_prime_dvd hne huniq


end Work.Hering.Step3
