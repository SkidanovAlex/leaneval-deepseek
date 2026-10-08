import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sec5Fix.lemma1
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.Hering.Perm.appII5
import Submission.Work.NormalComplement.Sec5Fix.prop2c_kernel_P
import Submission.Work.NormalComplement.sec5c_kappa
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-! ## Basic conjugation facts about `P`, `t`, `u` -/

theorem orderOf_conj_eq' (g x : G) : orderOf (MulAut.conj g x) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem localQ_commute_t_of_mem_P (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) {x : G}
    (hx : x ∈ P) : t * x * t⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hxct : x ∈ Subgroup.centralizer ({t} : Set G) := hxV.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hxct
  rw [← hxct]
  group

theorem localQ_commute_u_of_mem_P (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) {x : G}
    (hx : x ∈ P) : u * x * u⁻¹ = x := by
  have hxV : x ∈ Submission.Blueprint.centD H t := (h.P_le hx).2
  have hux : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x hxV
  rw [← hux]
  group

theorem localQ_mem_normalizer_t (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    t ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change t * x * t⁻¹ ∈ P
    rw [localQ_commute_t_of_mem_P h hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, localQ_commute_t_of_mem_P h hy]⟩

theorem localQ_mem_normalizer_u (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) {u : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    u ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    change u * x * u⁻¹ ∈ P
    rw [localQ_commute_u_of_mem_P h hu hx]
    exact hx
  · intro y hy
    exact ⟨y, hy, by simp [MulAut.conj_apply, localQ_commute_u_of_mem_P h hu hy]⟩

theorem p_ne_two' (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) : p ≠ 2 := by
  intro hp2
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  have hdvd : p ∣ Nat.card ↥(Submission.Blueprint.centD H t) := by
    rw [← h.P_card]
    exact Subgroup.card_dvd_of_le (h.P_le.trans inf_le_right)
  rw [hp2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

/-- `(A ⊓ C_G(P)) · P = C_A(P) × P` has odd order, so it contains no involution. -/
theorem localQ_eq_one_of_mem_sup_of_sq_eq_one (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    {x : G} (hx : x ∈ (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G))
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

/-- `N_H(P) = H ⊓ N_G(P)` has a unique involution, namely `u`. -/
theorem ngp_unique_involution (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∀ z ∈ H ⊓ Subgroup.normalizer (P : Set G), orderOf z = 2 → z = u := by
  classical
  set 𝒢 : Subgroup G := Subgroup.normalizer (P : Set G) with h𝒢
  set H₁ : Subgroup G := H ⊓ 𝒢 with hH₁
  have ht𝒢 : t ∈ 𝒢 := localQ_mem_normalizer_t h
  have hu𝒢 : u ∈ 𝒢 := localQ_mem_normalizer_u h hu
  have huH₁ : u ∈ H₁ := ⟨hu.1, hu𝒢⟩
  obtain ⟨hP1b, -⟩ := hC4 G h.sit H h.se t h.invol h.notMem
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hPleH : P ≤ H := hPleV.trans (inf_le_left.trans inf_le_left)
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard := by
    have h3' : 3 ≤ (Submission.Blueprint.fixedPts H
        (Submission.Blueprint.centD H t)).ncard :=
      Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
    exact le_trans h3'
      (Set.ncard_le_ncard (Work.ThreePoints.fixedPts_mono hPleV) (Set.toFinite _))
  have hinv : Submission.Blueprint.involutions
      (Subgroup.centralizer (P : Set G) : Set G) ⊆ 𝒢 := by
    intro x hx
    rw [Work.ThreePoints.mem_involutions] at hx
    exact Subgroup.centralizer_le_normalizer (P : Set G) hx.1
  have hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H₁.subgroupOf 𝒢) := by
    have h1 := hP1b P 𝒢 h3 hinv (by rw [h𝒢]) (1 : G)
      (by rw [Work.DoubleTransitivity.conj_one]; exact hPleH)
    rw [Work.DoubleTransitivity.conj_one] at h1
    simpa [hH₁, h𝒢, inf_comm] using h1
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
      have hxAP : (x : G) ∈
          (((A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P : Subgroup G) : Set G) := by
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
            have hyc := localQ_commute_t_of_mem_P h hy
            calc y * t = (t * y * t⁻¹) * t := by rw [hyc]
              _ = t * y := by group
          exact hsup hxAP
        rw [Subgroup.mem_centralizer_singleton_iff] at hxct
        rw [← hxct, mul_assoc, mul_inv_cancel, mul_one] at h2
        exact mul_eq_one_iff_eq_inv.mpr h2
      have hx1' : (x : G) = 1 := localQ_eq_one_of_mem_sup_of_sq_eq_one h hxAP hx2'
      exact Subtype.ext (by simpa using hx1')
  have ht'H₁ : (⟨t, ht𝒢⟩ : ↥𝒢) ∉ H₁.subgroupOf 𝒢 := fun hmem =>
    h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (H := H₁.subgroupOf 𝒢) hse
    (by rw [← Subgroup.orderOf_coe]; exact h.invol) ht'H₁
  have hInv : (Submission.Blueprint.involutions
      ((H₁.subgroupOf 𝒢 : Subgroup ↥𝒢) : Set ↥𝒢)).ncard = 1 := hcard ▸ hDK
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

/-- In a finite group with a strongly embedded subgroup `K` containing a unique involution `u`,
every element of a normal abelian subgroup `Q` with `Q ⊓ K = ⊥` is inverted by `u`. -/
theorem invert_of_stronglyEmbedded {F : Type} [Group F] [Finite F] {Q K : Subgroup F} {u : F}
    (hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    (hu : u ∈ K) (hu2 : orderOf u = 2)
    (hQn : Q.Normal) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQK : Q ⊓ K = ⊥) :
    ∀ x ∈ Q, u * x * u⁻¹ = x⁻¹ := by
  intro x hx
  have hu2m : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu2] at h; simpa [pow_two] using h
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2m
  have huxu : u * x * u⁻¹ ∈ Q := hQn.conj_mem x hx u
  set y : F := x * (u * x * u⁻¹) with hydef
  have hyQ : y ∈ Q := Q.mul_mem hx huxu
  have hyfix : u * y * u⁻¹ = y := by
    rw [hydef]
    have hcomm : x * (u * x * u⁻¹) = (u * x * u⁻¹) * x := hQab x hx _ huxu
    calc u * (x * (u * x * u⁻¹)) * u⁻¹
        = (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹) := by group
      _ = (u * x * u⁻¹) * x := by
            rw [show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) from by group,
              hu2m, huinv, hu2m, one_mul, mul_one]
      _ = x * (u * x * u⁻¹) := hcomm.symm
  by_cases hy1 : y = 1
  · have h2 : x * (u * x * u⁻¹) = 1 := hydef ▸ hy1
    have h3 : (u * x * u⁻¹) * x = 1 := by
      rw [← hQab x hx (u * x * u⁻¹) huxu, h2]
    exact mul_eq_one_iff_eq_inv.mp h3
  · exfalso
    have hyK : y ∉ K := by
      intro hmem
      have h : y ∈ Q ⊓ K := ⟨hyQ, hmem⟩
      rw [hQK] at h
      exact hy1 (Subgroup.mem_bot.mp h)
    have hcomm_uy : u * y = y * u := by
      calc u * y = (u * y * u⁻¹) * u := by group
        _ = y * u := by rw [hyfix]
    have huconj : u ∈ Submission.Blueprint.conj y K := by
      rw [Work.ThreePoints.mem_conj_iff]
      rw [show y⁻¹ * u * y = u from by rw [mul_assoc, hcomm_uy]; group]
      exact hu
    have humem : u ∈ K ⊓ Submission.Blueprint.conj y K := ⟨hu, huconj⟩
    have hodd := Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hse hyK
    have h2dvd : 2 ∣ Nat.card ↥(K ⊓ Submission.Blueprint.conj y K) := by
      rw [← hu2]; exact Subgroup.orderOf_dvd_natCard _ humem
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

theorem prop2c_local_Q (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∃ (f : ℕ) (Q : Subgroup G), f.Prime ∧ f ≠ p ∧ P ≤ Q ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G) ∧
      u * t ∈ Q ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧
      (∀ x ∈ Q, x ^ f ∈ P) ∧ (∀ x ∈ Q, u * x * u⁻¹ * x ∈ P) := by
  have hL1 : ∀ X : Subgroup G, P ≤ X → X ≤ Submission.Blueprint.centD H t →
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) → X = P :=
    fun X hPX hXV hN => lemma1 hFT hP3 h X hPX hXV hN
  have huniq : ∀ w ∈ H ⊓ Subgroup.normalizer (P : Set G), orderOf w = 2 → w = u :=
    ngp_unique_involution hFT hC4 h u hu
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hM
  set S : Set (G ⧸ H) := Submission.Blueprint.fixedPts H P with hS
  have hPleH : P ≤ H := (h.P_le.trans inf_le_right).trans (le_trans inf_le_left inf_le_left)
  have hPleT : P ≤ Submission.Blueprint.twoPoint H t :=
    (h.P_le.trans inf_le_right).trans inf_le_left
  have hPMH : P ≤ M ⊓ H := le_inf (Subgroup.le_normalizer (H := P)) hPleH
  have hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ S := by
    rw [hS, Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
    rw [show MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H from by
      rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]]
    exact hPleH
  let a0 : ↥S := ⟨(QuotientGroup.mk (1 : G) : G ⧸ H), hpt⟩
  have hpodd : p ≠ 2 := by
    intro hp2
    have hdvd : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [← h.P_card]; exact Subgroup.card_dvd_of_le hPleT
    rw [hp2] at hdvd
    exact Nat.not_even_iff_odd.mpr (h.se.2.2 t h.notMem) (even_iff_two_dvd.mpr hdvd)
  have huM : u ∈ M := by
    have hcomm : ∀ x ∈ P, u * x * u⁻¹ = x := by
      intro x hx
      have hc : x * u = u * x := (Subgroup.mem_centralizer_iff.mp hu.2.2) x (h.P_le hx).2
      rw [← hc]; group
    rw [hM, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; rw [hcomm x hx]; exact hx
    · intro hx
      have hu2 : u * u = 1 := by
        have h' := pow_orderOf_eq_one u; rw [hu.2.1] at h'; simpa [pow_two] using h'
      have h2 : u * (u * x * u⁻¹) * u⁻¹ = u * x * u⁻¹ := hcomm _ hx
      have h3 : u * (u * x * u⁻¹) * u⁻¹ = x := by
        have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
        rw [hui, show u * (u * x * u) * u = (u * u) * x * (u * u) from by group, hu2]
        simp
      rw [h3] at h2; rw [h2.symm] at hx; exact hx
  have htM : t ∈ M := by
    rw [hM, Subgroup.mem_normalizer_iff]
    intro x
    have ht2 : t * t = 1 := by
      have h' := pow_orderOf_eq_one t; rw [h.invol] at h'; simpa [pow_two] using h'
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hconj : ∀ y ∈ P, t * y * t⁻¹ = y := fun y hy => by
      have hct : y * t = t * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h.P_le hy).2).2
      rw [← hct]; group
    constructor
    · intro hx; rw [hconj x hx]; exact hx
    · intro hx
      have h5 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [hti, show t * (t * x * t) * t = (t * t) * x * (t * t) from by group, ht2]
        simp
      have h6 : t * (t * x * t⁻¹) * t⁻¹ = t * x * t⁻¹ := hconj _ hx
      rw [h5] at h6
      rwa [← h6] at hx
  -- Ch. II §2 Lemma 1 with `g = t`
  have hMdata := Work.NormalComplement.kappa_M_data hA hFT h u hu
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub M S := hMdata.1
  have hseL : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((M ⊓ H).subgroupOf M) := hMdata.2
  have h3 : 3 ≤ S.ncard := by
    rw [hS]
    exact Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem
      (h.P_le.trans inf_le_right)
  have hodd : Odd (Nat.card (P.subgroupOf M)) := by
    have h1 : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := P))).toEquiv
    rw [h1, h.P_card]
    exact h.prime.odd_of_ne_two hpodd
  -- the App. III inputs
  have hse_stab : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (MulAction.stabilizer (M ⧸ P.subgroupOf M) a0) :=
    Work.NormalComplement.kappa_quot_stronglyEmbedded hseL hPMH hodd hpt
  have hcoat : IsCoatom (MulAction.stabilizer (M ⧸ P.subgroupOf M) a0) :=
    Work.NormalComplement.kappa_coatom h2t h3 a0
  have hfaith : ∀ g : M ⧸ P.subgroupOf M, (∀ x : ↥S, g • x = x) → g = 1 := by
    intro g hg
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf M) g
    have hmK : (m : G) ∈ Work.NormalComplement.kappaKernel (H := H) (P := P) := by
      rw [Work.NormalComplement.mem_kappaKernel_iff]
      refine ⟨m.2, fun ω hω => ?_⟩
      have h1 := congrArg (fun z : ↥S => (z : G ⧸ H)) (hg ⟨ω, hω⟩)
      rwa [Work.NormalComplement.kappa_quot_smul_mk,
        Work.NormalComplement.kappa_smul_val] at h1
    have hmP : (m : G) ∈ P := by
      rw [Work.NormalComplement.kappaKernel_eq_P hFT h hL1] at hmK; exact hmK
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr hmP)
  have hpre : MulAction.IsPretransitive (M ⧸ P.subgroupOf M) ↥S :=
    ⟨fun c d => by
      obtain ⟨y, hy, hyd⟩ := h2t.isTransitiveOnSub c.1 c.2 d.1 d.2
      exact ⟨QuotientGroup.mk' (P.subgroupOf M) ⟨y, hy⟩,
        Subtype.ext (by rw [Work.NormalComplement.kappa_quot_smul_mk,
          Work.NormalComplement.kappa_smul_val]; exact hyd)⟩⟩
  have hfour : ¬ Submission.Blueprint.HasFourGroup (M ⧸ P.subgroupOf M) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient (P.subgroupOf M) hodd
      (Work.NormalComplement.kappa_noFour_M h.se u hu.1 hu.2.1 huM hPleH huniq h2t hseL)
  -- Appendix III
  obtain ⟨f, Qbar, hfprime, hQbarN, hQbar_ne, hQbar_ab, hQbar_exp, hQbar_inf, hQbar_sup,
    huuniq, hinv_mul, hinv_odd, hlast⟩ :=
    hIII (M ⧸ P.subgroupOf M) ↥S a0 hpre hfaith hfour hse_stab hcoat
  -- ## the images of `u` and `t` in `M/P`, and the element `u * t`
  have huM2 : orderOf (⟨u, huM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hu.2.1
  have htM2 : orderOf (⟨t, htM⟩ : ↥M) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact h.invol
  have hneUt : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ ≠
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ := by
    intro h1
    have h2 : QuotientGroup.mk' (P.subgroupOf M) (⟨u, huM⟩ * ⟨t, htM⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [QuotientGroup.mk'_apply] at h2
    have h3 : (u : G) * t⁻¹ ∈ P :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨u, huM⟩ * ⟨t, htM⟩⁻¹)).mp h2)
    have h4 : u * t⁻¹ ∈ H := hPleH h3
    have h5 : t ∈ H := by
      have ht : t = (u * t⁻¹)⁻¹ * u := by group
      rw [ht]; exact H.mul_mem (H.inv_mem h4) hu.1
    exact h.notMem h5
  have huhat2 : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show (⟨u, huM⟩ : ↥M) ^ 2 = 1 from by
        rw [← huM2]; exact pow_orderOf_eq_one _, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply] at h1
      have h3 : (u : G) ∈ P :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨u, huM⟩).mp h1)
      have h2p : 2 ∣ p := by
        rw [← h.P_card, ← hu.2.1]; exact Subgroup.orderOf_dvd_natCard P h3
      exact hpodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp h2p).symm
  have hthat2 : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, show (⟨t, htM⟩ : ↥M) ^ 2 = 1 from by
        rw [← htM2]; exact pow_orderOf_eq_one _, map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply] at h1
      have h3 : (t : G) ∈ P :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨t, htM⟩).mp h1)
      exact h.notMem (hPleH h3)
  have hQbar_ut : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ ∈ Qbar :=
    (hinv_mul _ _ huhat2 hthat2 hneUt).1
  have hf_eq : orderOf (QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
      QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩) = f :=
    (hinv_mul _ _ huhat2 hthat2 hneUt).2
  -- ## transport `Qbar` to a subgroup of `G`
  let Q : Subgroup G := (Qbar.comap (QuotientGroup.mk' (P.subgroupOf M))).map (Subgroup.subtype M)
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hQmem : ∀ x : G, x ∈ Q ↔ ∃ (hxM : x ∈ M),
      QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ ∈ Qbar := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      exact ⟨hyx ▸ y.2, hyx ▸ hy⟩
    · rintro ⟨hxM, hx⟩
      exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hx, rfl⟩
  have hPQ : P ≤ Q := by
    intro x hx
    rw [hQmem]
    refine ⟨Subgroup.le_normalizer (H := P) hx, ?_⟩
    have h1 : QuotientGroup.mk' (P.subgroupOf M) ⟨x, Subgroup.le_normalizer (H := P) hx⟩ = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff ⟨x, Subgroup.le_normalizer (H := P) hx⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1]; exact Qbar.one_mem
  have hconjQ : ∀ mm ∈ M, ∀ x ∈ Q, mm * x * mm⁻¹ ∈ Q := by
    intro mm hmm x hx
    obtain ⟨hxM, hxq⟩ := (hQmem x).mp hx
    rw [hQmem]
    refine ⟨M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm), ?_⟩
    have h2 : QuotientGroup.mk' (P.subgroupOf M)
          (⟨mm * x * mm⁻¹, M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm)⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) ⟨mm, hmm⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ *
          (QuotientGroup.mk' (P.subgroupOf M) ⟨mm, hmm⟩)⁻¹ := by
      rw [show (⟨mm * x * mm⁻¹, M.mul_mem (M.mul_mem hmm hxM) (M.inv_mem hmm)⟩ : ↥M) =
        ⟨mm, hmm⟩ * ⟨x, hxM⟩ * ⟨mm, hmm⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [h2]
    exact hQbarN.conj_mem _ hxq _
  have hQN : M ≤ Subgroup.normalizer (Q : Set G) := by
    intro mm hmm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconjQ mm hmm x, fun hx => by
      have h2 := hconjQ mm⁻¹ (M.inv_mem hmm) (mm * x * mm⁻¹) hx
      rwa [show mm⁻¹ * (mm * x * mm⁻¹) * (mm⁻¹)⁻¹ = x from by group] at h2⟩
  have hutQ : u * t ∈ Q := by
    rw [hQmem]
    refine ⟨M.mul_mem huM htM, ?_⟩
    have h1 : QuotientGroup.mk' (P.subgroupOf M) (⟨u * t, M.mul_mem huM htM⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨t, htM⟩ := by
      rw [show (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = ⟨u, huM⟩ * ⟨t, htM⟩ from Subtype.ext rfl,
        map_mul]
    rw [h1]; exact hQbar_ut
  -- ## the canonical surjection `Q ↠ Qbar`
  let ψ : ↥Q →* M ⧸ P.subgroupOf M :=
    (QuotientGroup.mk' (P.subgroupOf M)).comp (Subgroup.inclusion hQM)
  have hψrange : ∀ y : ↥Q, ψ y ∈ Qbar := by
    intro y
    obtain ⟨hxM, hxq⟩ := (hQmem (y : G)).mp y.2
    have h2 : QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hQM y.2⟩ : ↥M) =
        QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hxM⟩ : ↥M) := by
      rw [show (⟨(y : G), hQM y.2⟩ : ↥M) = ⟨(y : G), hxM⟩ from Subtype.ext rfl]
    show ψ y ∈ Qbar
    rw [show ψ y = QuotientGroup.mk' (P.subgroupOf M) (⟨(y : G), hQM y.2⟩ : ↥M) from rfl, h2]
    exact hxq
  let φ : ↥Q →* ↥Qbar := ψ.codRestrict Qbar hψrange
  have hφcoe : ∀ y : ↥Q, ((φ y : ↥Qbar) : M ⧸ P.subgroupOf M) =
      QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ := fun y => rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (P.subgroupOf M) (y : M ⧸ P.subgroupOf M)
    have hxq : (m : G) ∈ Q := by
      rw [hQmem]
      exact ⟨m.2, hm ▸ y.2⟩
    refine ⟨⟨(m : G), hxq⟩, Subtype.ext ?_⟩
    rw [hφcoe,
      show (⟨(m : G), hQM hxq⟩ : ↥M) = m from Subtype.ext rfl]
    exact hm
  have hφker : φ.ker = P.subgroupOf Q := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      have hy' : QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ = 1 := by
        have h2 := congrArg (fun z : ↥Qbar => (z : M ⧸ P.subgroupOf M)) hy
        rwa [hφcoe] at h2
      rw [QuotientGroup.mk'_apply] at hy'
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (⟨(y : G), hQM y.2⟩ : ↥M)).mp hy')
    · intro hy
      apply Subtype.ext
      show ((φ y : ↥Qbar) : M ⧸ P.subgroupOf M) = ((1 : ↥Qbar) : M ⧸ P.subgroupOf M)
      rw [hφcoe]
      show QuotientGroup.mk' (P.subgroupOf M) ⟨(y : G), hQM y.2⟩ = 1
      refine (QuotientGroup.eq_one_iff (⟨(y : G), hQM y.2⟩ : ↥M)).mpr ?_
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy)
  -- ## `Qbar` is an `f`-group of odd order; `Q` has odd order
  have hQbar_pg : IsPGroup f ↥Qbar := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro y
    exact ⟨1, by rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hQbar_exp _ y.2))⟩
  have hf35 : f = 3 ∨ f = 5 := by
    have hf_dvd : f ∣ orderOf (u * t) := by
      have h1 : orderOf (QuotientGroup.mk' (P.subgroupOf M)
          (⟨u * t, M.mul_mem huM htM⟩ : ↥M)) = f := by
        rw [show (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = ⟨u, huM⟩ * ⟨t, htM⟩ from Subtype.ext rfl,
          map_mul]
        exact hf_eq
      have h2 := orderOf_map_dvd (QuotientGroup.mk' (P.subgroupOf M))
        (⟨u * t, M.mul_mem huM htM⟩ : ↥M)
      have h3 : orderOf (⟨u * t, M.mul_mem huM htM⟩ : ↥M) = orderOf (u * t) :=
        (Subgroup.orderOf_coe (⟨u * t, M.mul_mem huM htM⟩ : ↥M)).symm
      rw [h3] at h2
      rw [h1] at h2
      exact h2
    have hres := Work.NormalComplement.Sec5CKappa.prop2a_orderof hFT hC hC4 hP3 hIII hMF2 h u hu
    rcases hres with h3 | h5
    · left
      rw [h3] at hf_dvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hf_dvd with h1 | h1
      · exact absurd h1 hfprime.ne_one
      · exact h1
    · right
      rw [h5] at hf_dvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hf_dvd with h1 | h1
      · exact absurd h1 hfprime.ne_one
      · exact h1
  have hfodd : Odd f :=
    hf35.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)
  have hp7 : 7 ≤ p := sec5_prop1 hFT hC4 Work.NormalComplement.bender_prelim
    Work.NormalComplement.burnsideClassProp h
  have hf_ne_p : f ≠ p := by rcases hf35 with h | h <;> rw [h] at * <;> omega
  have hQbar_odd : Odd (Nat.card ↥Qbar) := by
    haveI : Fact f.Prime := ⟨hfprime⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := f)).mp hQbar_pg
    rw [hk]; exact hfodd.pow
  have hkerodd : Odd (Nat.card ↥(φ.ker)) := by
    rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show P ≤ Q from hPQ)).toEquiv,
      h.P_card]
    exact h.prime.odd_of_ne_two hpodd
  have hQodd : Odd (Nat.card ↥Q) := by
    have h1 : Nat.card ↥Q = Nat.card ↥(φ.ker) * Nat.card ↥Qbar := by
      rw [← Subgroup.card_mul_index (φ.ker), Subgroup.index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    rw [h1]; exact hkerodd.mul hQbar_odd
  -- ## `C_{Qbar}(û) = 1`
  have huhat_stab : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ ∈
      MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := by
    rw [Work.NormalComplement.kappa_stabilizer_eq hpt]
    exact Subgroup.mem_map.mpr ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr ⟨huM, hu.1⟩, rfl⟩
  have hCQbar : ∀ y ∈ Qbar, QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ * y =
      y * QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ → y = 1 := by
    intro y hy hcomm
    have h2 : ((y • a0 : ↥S) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      have h3 : (⟨u, huM⟩ : ↥M) • (y • a0) = y • a0 := by
        rw [← Work.NormalComplement.kappa_quot_smul_mk (H := H) (P := P) ⟨u, huM⟩ (y • a0)]
        rw [← mul_smul, hcomm, mul_smul, MulAction.mem_stabilizer_iff.mp huhat_stab]
      exact Work.NormalComplement.kappa_u_fix h.se u hu.1 hu.2.1 huM (y • a0) h3
    have hy_stab : y ∈ MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := by
      rw [MulAction.mem_stabilizer_iff]
      exact Subtype.ext h2
    have hmem : y ∈ Qbar ⊓ MulAction.stabilizer (M ⧸ P.subgroupOf M) a0 := ⟨hy, hy_stab⟩
    rw [hQbar_inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- ## `C_Q(u) = P`
  have hCQ : Subgroup.centralizer ({u} : Set G) ⊓ Q = P := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxC, hxQ⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxM, hxq⟩ := (hQmem x).mp hxQ
      have hcomm : QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ *
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ =
          QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ *
            QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
      have hxq1 : QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ = 1 := hCQbar _ hxq hcomm
      rw [QuotientGroup.mk'_apply] at hxq1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨x, hxM⟩).mp hxq1)
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, hPQ hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hu.2.2) x (h.P_le hx).2
  -- ## `Q/P` is abelian, i.e. `[Q,Q] ≤ P`
  have hqq : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ P := by
    intro a ha b hb
    obtain ⟨haM, haq⟩ := (hQmem a).mp ha
    obtain ⟨hbM, hbq⟩ := (hQmem b).mp hb
    have h1 : (QuotientGroup.mk' (P.subgroupOf M) ⟨a, haM⟩) *
        (QuotientGroup.mk' (P.subgroupOf M) ⟨b, hbM⟩) =
        (QuotientGroup.mk' (P.subgroupOf M) ⟨b, hbM⟩) *
          (QuotientGroup.mk' (P.subgroupOf M) ⟨a, haM⟩) :=
      hQbar_ab _ haq _ hbq
    have hcommQ : ⁅a, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    obtain ⟨habM, -⟩ := (hQmem ⁅a, b⁆).mp hcommQ
    have h2 : QuotientGroup.mk' (P.subgroupOf M) ⟨⁅a, b⁆, habM⟩ = 1 := by
      have h3 : (⟨⁅a, b⁆, habM⟩ : ↥M) =
          ⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ :=
        Subtype.ext (commutatorElement_def a b)
      rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    rw [QuotientGroup.mk'_apply] at h2
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨⁅a, b⁆, habM⟩).mp h2)
  -- ## the coprimality hypothesis of App. I (5)(b)
  have huXn : Work.NormalComplement.NormalizedBy u Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hQN huM) x).mp hx
  have hu2cop : Nat.Coprime (Nat.card Q) 2 := Nat.coprime_two_right.mpr hQodd
  have hQsolv : Group.IsSolvable ↥Q := hFT ↥Q hQodd
  have hKappKset : Work.NormalComplement.Kapp u Q = Work.NormalComplement.Kset Q u :=
    ((appI_one (d := 2) Nat.prime_two hu.2.1 huXn hu2cop).2 rfl).1
  have hKapp : (Work.NormalComplement.Kapp u Q).ncard = (P.subgroupOf Q).index := by
    have h1 := (appI_one (d := 2) Nat.prime_two hu.2.1 huXn hu2cop).1
    rwa [hCQ] at h1
  have hcop : Nat.Coprime (Work.NormalComplement.Kapp u Q).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({u} : Set G) ⊓ Q))) := by
    rw [hKapp, ← hφker, Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
    refine Nat.coprime_of_dvd' (fun q hq hqK hqF => ?_)
    have hqFp : q ∣ p := by
      have h2 := Subgroup.card_dvd_of_le (le_top :
        Work.Fitting.fitting ↥(Subgroup.centralizer ({u} : Set G) ⊓ Q) ≤ ⊤)
      rw [Subgroup.card_top] at h2
      rw [hCQ] at hqF
      rw [hCQ, h.P_card] at h2
      exact hqF.trans h2
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq h.prime).mp hqFp
    rw [hqp] at hqK
    haveI : Fact f.Prime := ⟨hfprime⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := f)).mp hQbar_pg
    rw [hk] at hqK
    have hpf : p = f := (Nat.prime_dvd_prime_iff_eq h.prime hfprime).mp (h.prime.dvd_of_dvd_pow hqK)
    exact absurd hpf.symm hf_ne_p
  -- ## App. I (5)(b)
  obtain ⟨K, hKset, hKcomp⟩ :=
    appI_five_b (d := 2) Nat.prime_two hu.2.1 huXn hu2cop hQsolv hcop
  have hKle : K ≤ Q := hKcomp.1
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hKcomp.2.1
  have hKinf : K ⊓ (Subgroup.centralizer ({u} : Set G) ⊓ Q) = ⊥ := hKcomp.2.2.1
  have hKP : K ⊓ P = ⊥ := by rw [← hCQ]; exact hKinf
  have hKset' : (K : Set G) = Work.NormalComplement.Kset Q u := hKset.trans hKappKset
  -- ## the point stabiliser is `N_H(P)`, and `û` inverts `Qbar`
  have hQbar_inv : ∀ y ∈ Qbar, QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩ * y *
      (QuotientGroup.mk' (P.subgroupOf M) ⟨u, huM⟩)⁻¹ = y⁻¹ :=
    invert_of_stronglyEmbedded hse_stab huhat_stab huhat2 hQbarN hQbar_ab hQbar_inf
  -- ## `K` is inverted by `u`; `K` and `P` commute; `Q` is abelian
  have hKu : ∀ k ∈ K, u * k * u⁻¹ = k⁻¹ := by
    intro k hk
    have hk' : k ∈ Work.NormalComplement.Kset Q u := hKset' ▸ hk
    exact hk'.2
  have hPu : ∀ a ∈ P, u * a * u⁻¹ = a := fun a ha => (Subgroup.mem_centralizer_iff.mp hu.2.2)
    a (h.P_le ha).2 |> fun hc => by rw [← hc]; group
  have hKPcomm : ∀ k ∈ K, ∀ a ∈ P, k * a = a * k := by
    intro k hk a ha
    have hkQ : k ∈ Q := hKle hk
    have hcP : k * a * k⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hQM hkQ) a).mp ha
    have hcu : u * (k * a * k⁻¹) * u⁻¹ = k * a * k⁻¹ := hPu _ hcP
    have h2 : k * a * k⁻¹ = k⁻¹ * a * k := by
      have h3 : u * (k * a * k⁻¹) * u⁻¹ = k⁻¹ * a * k := by
        rw [show u * (k * a * k⁻¹) * u⁻¹ =
          (u * k * u⁻¹) * (u * a * u⁻¹) * (u * k * u⁻¹)⁻¹ from by group]
        rw [hKu k hk, hPu a ha]
        group
      exact hcu.symm.trans h3
    have hsq : (k * k) * a = a * (k * k) := by
      have h4 : a = k⁻¹ * k⁻¹ * a * (k * k) := by
        calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
          _ = k⁻¹ * (k⁻¹ * a * k) * k := by rw [h2]
          _ = k⁻¹ * k⁻¹ * a * (k * k) := by group
      calc (k * k) * a = (k * k) * (k⁻¹ * k⁻¹ * a * (k * k)) := by rw [← h4]
        _ = a * (k * k) := by group
    have hkodd : Odd (orderOf k) := Odd.of_dvd_nat hQodd (Subgroup.orderOf_dvd_natCard Q hkQ)
    obtain ⟨t', ht'⟩ := hkodd
    have hk_eq : k = (k ^ 2) ^ (t' + 1) := by
      have hone : k ^ (2 * t' + 1) = 1 := by rw [← ht']; exact pow_orderOf_eq_one k
      have h1 : k ^ (2 * t' + 2) = k := by
        rw [show 2 * t' + 2 = 2 * t' + 1 + 1 from by ring, pow_succ, hone, one_mul]
      calc k = k ^ (2 * t' + 2) := h1.symm
        _ = (k ^ 2) ^ (t' + 1) := by
              rw [show 2 * t' + 2 = 2 * (t' + 1) from by ring, pow_mul]
    have h5 : Commute (k ^ 2) a := by rw [pow_two]; exact hsq
    have h6 : Commute ((k ^ 2) ^ (t' + 1)) a := Commute.pow_left h5 (t' + 1)
    rwa [← hk_eq] at h6
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    haveI : Fact p.Prime := ⟨h.prime⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card h.P_card
    haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
    intro a ha b hb
    have hc : (⟨a, ha⟩ : ↥P) * ⟨b, hb⟩ = (⟨b, hb⟩ : ↥P) * ⟨a, ha⟩ :=
      isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥P) _ _
    simpa using congrArg Subtype.val hc
  have hKKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ P := hqq a (hKle ha) b (hKle hb)
    have h2 : ⁅a, b⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    have h3 : ⁅a, b⁆ ∈ K ⊓ P := ⟨h2, h1⟩
    rw [hKP] at h3
    have h4 : ⁅a, b⁆ = 1 := Subgroup.mem_bot.mp h3
    rw [commutatorElement_def] at h4
    have h6 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h4
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h6]
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    have hKPsup : K ⊔ P = Q := by rw [← hCQ]; exact hKcomp.2.2.2
    have hPK : P ≤ Subgroup.normalizer (K : Set G) := hPQ.trans hQK
    have hKmulP : (K : Set G) * (P : Set G) = (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K P hPK]
      exact congrArg (fun (X : Subgroup G) => (X : Set G)) hKPsup
    intro x hx y hy
    have hxKP : x ∈ (K : Set G) * (P : Set G) := by rw [hKmulP]; exact hx
    have hyKP : y ∈ (K : Set G) * (P : Set G) := by rw [hKmulP]; exact hy
    obtain ⟨k, hk, a, ha, hkax⟩ := Set.mem_mul.mp hxKP
    obtain ⟨k', hk', a', ha', hkay⟩ := Set.mem_mul.mp hyKP
    rw [← hkax, ← hkay]
    have e1 : k * a * (k' * a') = (k * k') * (a * a') := by
      calc k * a * (k' * a') = k * (a * (k' * a')) := by group
        _ = k * ((a * k') * a') := by group
        _ = k * ((k' * a) * a') := by rw [← hKPcomm k' hk' a ha]
        _ = (k * k') * (a * a') := by group
    have e2 : k' * a' * (k * a) = (k' * k) * (a' * a) := by
      calc k' * a' * (k * a) = k' * (a' * (k * a)) := by group
        _ = k' * ((a' * k) * a) := by group
        _ = k' * ((k * a') * a) := by rw [← hKPcomm k hk a' ha']
        _ = (k' * k) * (a' * a) := by group
    rw [e1, e2, hKKcomm k hk k' hk', hPab a ha a' ha']
  -- ## `x ^ f ∈ P` and `u * x * u⁻¹ * x ∈ P` for `x ∈ Q`
  have hQexp : ∀ x ∈ Q, x ^ f ∈ P := by
    intro x hx
    have h1 : φ (⟨x, hx⟩ ^ f) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hQbar_exp _ (φ ⟨x, hx⟩).2)
    have h2 : (⟨x, hx⟩ : ↥Q) ^ f ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hφker] at h2
    have h3 : ((↑((⟨x, hx⟩ : ↥Q) ^ f)) : G) ∈ P := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  have hinv : ∀ x ∈ Q, u * x * u⁻¹ * x ∈ P := by
    intro x hx
    have hxM : x ∈ M := hQM hx
    have huxuQ : u * x * u⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQN huM) x).mp hx
    have hmem : u * x * u⁻¹ * x ∈ Q := Q.mul_mem huxuQ hx
    have h1 : QuotientGroup.mk' (P.subgroupOf M)
        (⟨u * x * u⁻¹ * x, hQM hmem⟩ : ↥M) = 1 := by
      have heq : (⟨u * x * u⁻¹ * x, hQM hmem⟩ : ↥M) =
          ⟨u, huM⟩ * ⟨x, hxM⟩ * ⟨u, huM⟩⁻¹ * ⟨x, hxM⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
      rw [heq, map_mul, map_mul, map_mul, map_inv]
      have h2 : QuotientGroup.mk' (P.subgroupOf M) ⟨x, hxM⟩ =
          ((φ ⟨x, hx⟩ : ↥Qbar) : M ⧸ P.subgroupOf M) := by
        rw [hφcoe]
      rw [h2, hQbar_inv _ (φ ⟨x, hx⟩).2]
      group
    have h2 : (⟨u * x * u⁻¹ * x, hQM hmem⟩ : ↥M) ∈
        (QuotientGroup.mk' (P.subgroupOf M)).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk'] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  exact ⟨f, Q, hfprime, hf_ne_p, hPQ, hQN, hutQ, hQab, hQexp, hinv⟩

end Work.NormalComplement.Sec5Fix
