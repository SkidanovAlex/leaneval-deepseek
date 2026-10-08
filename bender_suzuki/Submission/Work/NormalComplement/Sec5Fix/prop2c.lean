import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_lemma1
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.burnsideClassProp
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.Sec5Fix.prop2a_given
import Submission.Work.NormalComplement.Sec5Fix.msetAbelianOdd
import Submission.Work.NormalComplement.Sec5Fix.prop2c_kappa

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix

open Submission.Blueprint
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `t` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(t)`. -/
lemma prop2c_commute_t_of_mem_P (h : Design.Setup5 G H t W p P A r) {x : G} (hx : x ∈ P) :
    t * x * t⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hxct : x ∈ Subgroup.centralizer ({t} : Set G) := hxV.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxct
  rw [← hxct]
  group

/-- `u` commutes with every element of `P`: `P ≤ centD H t ≤ C_G(u)`. -/
lemma prop2c_commute_u_of_mem_P (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) {x : G}
    (hx : x ∈ P) : u * x * u⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hux : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x hxV
  rw [← hux]
  group

/-- `t` lies in `N_G(P)`. -/
lemma prop2c_mem_normalizer_t (h : Design.Setup5 G H t W p P A r) :
    t ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change t * x * t⁻¹ ∈ P
    rw [prop2c_commute_t_of_mem_P h hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, prop2c_commute_t_of_mem_P h hy]⟩

/-- `u` lies in `N_G(P)`. -/
lemma prop2c_mem_normalizer_u (h : Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    u ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change u * x * u⁻¹ ∈ P
    rw [prop2c_commute_u_of_mem_P h hu hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, prop2c_commute_u_of_mem_P h hu hy]⟩

/-- Every element of `(A ⊓ C_G(P)) ⊔ P` of order dividing `2` is `1`: the group
`C_A(P) · P = C_A(P) × P` has odd order (`A ⊓ P = ⊥`). -/
lemma prop2c_eq_one_of_mem_sup_of_sq_eq_one (h : Design.Setup5 G H t W p P A r) {x : G}
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
      Nat.coprime_two_left.mpr (h.prime.odd_of_ne_two (p_ne_two' h))
    have h3 : orderOf q ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 2 p = 1 from hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have haT : a ∈ Submission.Blueprint.twoPoint H t :=
      (inf_le_left : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t)
        (h.A_le haA)
    have h2 : orderOf a ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ haT
    have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
    have hgcd : Nat.gcd 2 (Nat.card ↥(Submission.Blueprint.twoPoint H t)) = 1 :=
      Nat.coprime_two_left.mpr hodd
    have h3 : orderOf a ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hgcd] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  rw [← hqa, hq1, ha1, one_mul]


/-- The involutions of `N_H(P) = H ⊓ N_G(P)` are exactly `u`; in particular `N_H(P) ≤ C_G(u)`. -/
theorem prop2c_inv_involutions_normalizer
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  set 𝒢 : Subgroup G := Subgroup.normalizer (P : Set G) with h𝒢
  set H₁ : Subgroup G := H ⊓ 𝒢 with hH₁
  have ht𝒢 : t ∈ 𝒢 := prop2c_mem_normalizer_t h
  have hu𝒢 : u ∈ 𝒢 := prop2c_mem_normalizer_u h hu
  have huH₁ : u ∈ H₁ := ⟨hu.1, hu𝒢⟩
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t
    rw [h.invol] at h'
    simpa [pow_two] using h'
  -- ## `N_H(P)` is strongly embedded in `N_G(P)`
  obtain ⟨hP1b, -⟩ := hC4 G h.sit H h.se t h.invol h.notMem
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (fixedPts H P).ncard := by
    have h3' : 3 ≤ (fixedPts H (Submission.Blueprint.centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have hinv : Submission.Blueprint.involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆ 𝒢 := by
    intro x hx
    rw [Work.ThreePoints.mem_involutions] at hx
    exact Subgroup.centralizer_le_normalizer _ hx.1
  have hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H₁.subgroupOf 𝒢) := by
    have h1 := hP1b P 𝒢 h3 hinv (by rw [h𝒢]) (1 : G)
      (by rw [Work.DoubleTransitivity.conj_one]; exact hPleH)
    rw [Work.DoubleTransitivity.conj_one] at h1
    simpa [hH₁, h𝒢, inf_comm] using h1
  -- ## the `J`-set of the pair `(N_H(P), t)` inside `N_G(P)` is trivial
  have hDK : (Work.ThmF.Kset (H₁.subgroupOf 𝒢) (⟨t, ht𝒢⟩ : ↥𝒢)).ncard = 1 := by
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
      have hxG : (x : G) ∈ 𝒢 := hxH₁.2
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
            have hyc := prop2c_commute_t_of_mem_P h hy
            calc y * t = (t * y * t⁻¹) * t := by rw [hyc]
              _ = t * y := by group
          exact hsup hxAP
        rw [Subgroup.mem_centralizer_singleton_iff] at hxct
        rw [← hxct, mul_assoc, mul_inv_cancel, mul_one] at h2
        exact mul_eq_one_iff_eq_inv.mpr h2
      have hx1' : (x : G) = 1 := prop2c_eq_one_of_mem_sup_of_sq_eq_one h hxAP hx2'
      exact Subtype.ext (by simpa using hx1')
  -- ## `|Inv N_H(P)| = 1`
  have ht'H₁ : (⟨t, ht𝒢⟩ : ↥𝒢) ∉ H₁.subgroupOf 𝒢 := fun hmem =>
    h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (H := H₁.subgroupOf 𝒢) hse
    (by rw [← Subgroup.orderOf_coe]; exact h.invol) ht'H₁
  have hInv : (Submission.Blueprint.involutions
      ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢)).ncard = 1 := hcard ▸ hDK
  -- ## every involution of `N_H(P)` is `u`
  have huniq : ∀ z : G, z ∈ H₁ → orderOf z = 2 → z = u := by
    intro z hzH₁ hz2
    have hzmem : (⟨z, hzH₁.2⟩ : ↥𝒢) ∈ Submission.Blueprint.involutions
        ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢) :=
      ⟨Subgroup.mem_subgroupOf.mpr hzH₁, by rw [← Subgroup.orderOf_coe]; exact hz2⟩
    have humem : (⟨u, hu𝒢⟩ : ↥𝒢) ∈ Submission.Blueprint.involutions
        ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢) :=
      ⟨Subgroup.mem_subgroupOf.mpr huH₁, by rw [← Subgroup.orderOf_coe]; exact hu.2.1⟩
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hInv
    have h1 : (⟨z, hzH₁.2⟩ : ↥𝒢) = a := by
      have := ha ▸ hzmem
      simpa using this
    have h2 : (⟨u, hu𝒢⟩ : ↥𝒢) = a := by
      have := ha ▸ humem
      simpa using this
    exact Subtype.ext_iff.mp (h1.trans h2.symm)
  -- ## conclude
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzH₁ : z ∈ H₁ := ⟨(Subgroup.mem_inf.mp hz).1, (Subgroup.mem_inf.mp hz).2⟩
  have hzu_mem : z * u * z⁻¹ ∈ H₁ := H₁.mul_mem (H₁.mul_mem hzH₁ huH₁) (H₁.inv_mem hzH₁)
  have hzu_ord : orderOf (z * u * z⁻¹) = 2 := by
    rw [show z * u * z⁻¹ = MulAut.conj z u from by rw [MulAut.conj_apply]]
    rw [orderOf_conj_eq']
    exact hu.2.1
  have hzu : z * u * z⁻¹ = u := huniq _ hzu_mem hzu_ord
  calc z * u = (z * u * z⁻¹) * z := by group
    _ = u * z := by rw [hzu]


/-- **Assembly.** If `Mset u t` is abelian, if `κ ≤ Mset u t` is a subgroup containing `u * t`
and normalised by `N_G(P)`, and if `N_H(P) ≤ C_G(u)`, then `N_H(P)` normalises every subgroup `M`
with underlying set `Mset u t`. -/
theorem prop2c_assembly (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    {M : Subgroup G} (hM : (M : Set G) = Design.Mset u t)
    (hMab : ∀ x ∈ Design.Mset u t, ∀ y ∈ Design.Mset u t, x * y = y * x)
    (hκ : ∃ κ : Subgroup G, (κ : Set G) ⊆ Design.Mset u t ∧ u * t ∈ κ ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (κ : Set G))
    (hCu : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({u} : Set G)) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  classical
  obtain ⟨κ, hκsub, hκut, hκnorm⟩ := hκ
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t
    rw [h.invol] at h'
    simpa [pow_two] using h'
  have hu2 : u * u = 1 := by
    have h' := pow_orderOf_eq_one u
    rw [hu.2.1] at h'
    simpa [pow_two] using h'
  -- ## `M = C_G(κ) ∩ {x | u x u⁻¹ = x⁻¹}`
  have hMeq : (M : Set G) =
      {x : G | x ∈ Subgroup.centralizer (κ : Set G) ∧ u * x * u⁻¹ = x⁻¹} := by
    ext x
    constructor
    · intro hxM
      have hxM' : x ∈ Design.Mset u t := hM ▸ hxM
      have hxcomm : x * (u * t) = (u * t) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxM'.1
      have hxinv : t * x * t⁻¹ = x⁻¹ := hxM'.2
      have hconj : (u * t) * x * (u * t)⁻¹ = x := by rw [← hxcomm]; group
      have hconj' : (u * t) * x⁻¹ * (u * t)⁻¹ = x⁻¹ := by
        calc (u * t) * x⁻¹ * (u * t)⁻¹ = ((u * t) * x * (u * t)⁻¹)⁻¹ := by group
          _ = x⁻¹ := by rw [hconj]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hMab x hxM' y (hκsub hy)).symm
      · have h1 : MulAut.conj u = MulAut.conj (u * t) * MulAut.conj t := by
          rw [← map_mul]
          congr 1
          rw [mul_assoc, ht2, mul_one]
        have hux : u * x * u⁻¹ = (u * t) * (t * x * t⁻¹) * (u * t)⁻¹ := by
          rw [show u * x * u⁻¹ = (MulAut.conj u) x from (MulAut.conj_apply u x).symm]
          rw [h1, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
        rw [hux, hxinv, hconj']
    · rintro ⟨hxcent, hxinv⟩
      have hxcomm : x * (u * t) = (u * t) * x :=
        ((Subgroup.mem_centralizer_iff.mp hxcent) (u * t) hκut).symm
      have hconj : (u * t) * x * (u * t)⁻¹ = x := by rw [← hxcomm]; group
      refine hM ▸ ⟨?_, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
      · have h1 : MulAut.conj t = MulAut.conj u * MulAut.conj (u * t) := by
          rw [← map_mul]
          congr 1
          rw [← mul_assoc, hu2, one_mul]
        have htx : t * x * t⁻¹ = u * ((u * t) * x * (u * t)⁻¹) * u⁻¹ := by
          rw [show t * x * t⁻¹ = (MulAut.conj t) x from (MulAut.conj_apply t x).symm]
          rw [h1, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
        rw [htx, hconj, hxinv]
  -- ## `N_H(P)` normalises `M`
  intro g hg
  obtain ⟨-, hgN⟩ := Subgroup.mem_inf.mp hg
  have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp (hCu hg)
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ y : G, (y ∈ (M : Set G)) ↔
      (y ∈ Subgroup.centralizer (κ : Set G) ∧ u * y * u⁻¹ = y⁻¹) :=
    fun y => by rw [hMeq]; simp
  intro x
  change x ∈ (M : Set G) ↔ g * x * g⁻¹ ∈ (M : Set G)
  rw [key x, key (g * x * g⁻¹)]
  have hgκiff : ∀ y : G, y ∈ κ ↔ g * y * g⁻¹ ∈ κ :=
    Subgroup.mem_normalizer_iff.mp (hκnorm hgN)
  have huconj : u * (g * x * g⁻¹) * u⁻¹ = g * (u * x * u⁻¹) * g⁻¹ := by
    have h2 : MulAut.conj u * MulAut.conj g = MulAut.conj g * MulAut.conj u := by
      rw [← map_mul, ← map_mul, hgu]
    have h3 := congrArg (fun f : MulAut G => f x) h2
    simpa [MulAut.mul_apply, MulAut.conj_apply] using h3
  constructor
  · rintro ⟨hxcent, hxinv⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ κ := (hgκiff (g⁻¹ * y * g)).mpr (by
        rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group])
      have h := hxcent (g⁻¹ * y * g) hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = (g * x * g⁻¹) * y := by group
    · rw [huconj, hxinv]
      group
  · rintro ⟨hxcent, hxinv⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
      intro y hy
      have hy' : g * y * g⁻¹ ∈ κ := (hgκiff y).mp hy
      have h := hxcent (g * y * g⁻¹) hy'
      calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
        _ = x * y := by group
    · rw [huconj] at hxinv
      rw [show u * x * u⁻¹ = g⁻¹ * (g * (u * x * u⁻¹) * g⁻¹) * g from by group, hxinv]
      group

/-! ## §5 Prop. 2 (c), assembled

With `M` the (abelian, by `Sec5Fix.prop2b`) subgroup with underlying set `Mset u t` and `κ ⊴ N_G(P)`
the subgroup produced by `Sec5Fix.prop2c_kappa`, one has `M = C_G(κ) ∩ {x | u x u⁻¹ = x⁻¹}`;
since `N_H(P) ≤ C_G(u)` and `N_H(P)` normalises `κ`, it normalises `M`. -/
theorem prop2c (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t) :
    H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  have hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 :=
    prop2a_given hFT hC hC4 hP3 hIII hMF2 h u hu
  have hMabM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x :=
    (msetAbelianOdd hFT hA hC hC4 hP3 hIII hMF2 hCor1
      Work.NormalComplement.burnsideClassProp Work.NormalComplement.bender_prelim h u hu hf
      M hM).1
  have hMab : ∀ x ∈ Work.NormalComplement.Design.Mset u t,
      ∀ y ∈ Work.NormalComplement.Design.Mset u t, x * y = y * x := by
    intro x hx y hy
    refine hMabM x ?_ y ?_
    · change x ∈ (M : Set G); rw [hM]; exact hx
    · change y ∈ (M : Set G); rw [hM]; exact hy
  exact prop2c_assembly h u hu hM hMab
    (prop2c_kappa hFT hA hC hC4 hP3 hIII hMF2 hCor1 h u hu)
    (prop2c_inv_involutions_normalizer hFT hC4 h u hu)

end Work.NormalComplement.Sec5Fix
