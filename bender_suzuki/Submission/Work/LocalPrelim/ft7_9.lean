import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.Fitting.Defs
import Submission.Work.LocalPrelim.centralizer_scn
import Submission.Work.PStable.pstable_representation
import Submission.Work.Fitting.pCoreSeries_two
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.isPSolvable_of_hallHigman
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.Fitting.subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot
import Submission.Work.Fitting.fitting_eq_pCore_of_pPrimeCore_eq_bot
import Submission.Work.Fitting.pCore_le_sylow
import Submission.Work.Fitting.le_pPrimePCore_of_map_isPiNat
import Submission.Work.PGroup.All
import Submission.Work.Coprime.All
import Submission.Work.HallHigman.Lemma71
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.isPSolvable_quotient_prime
import Submission.Work.LocalPrelim.Ft72Rep
import Submission.Work.LocalPrelim.Ft72Util
import Submission.Work.LocalPrelim.frattiniQuotRep_sub_one_sq_eq_zero
import Submission.Work.LocalPrelim.mem_pCore_of_frattiniQuotRep_eq_one
import Submission.Work.LocalPrelim.ft7_2_psolvable_bridge
import Submission.Work.LocalPrelim.exists_invariant_index_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement IsMulCommutative

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.LocalPrelim

lemma sylow_two_abelian_quotient {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (h : ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G)) :
    ∀ Q : Sylow 2 (G ⧸ N), IsMulCommutative ↥(Q : Subgroup (G ⧸ N)) := by
  have hall : ∀ S : Subgroup G, IsPGroup 2 ↥S → IsMulCommutative ↥S :=
    fun S hS => Work.PStable.Quad.isMulCommutative_of_isPGroup_two_of_sylow (H := G) h hS
  have hall' : ∀ S' : Subgroup (G ⧸ N), IsPGroup 2 ↥S' → IsMulCommutative ↥S' :=
    fun S' hS' => Work.PStable.Quad.isMulCommutative_of_isPGroup_two_of_surjective
      (QuotientGroup.mk'_surjective N) hall hS'
  intro Q
  exact hall' (Q : Subgroup (G ⧸ N)) Q.isPGroup'

theorem ft7_2_cond3_pstable_core {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hsol : Work.HallHigman.IsPSolvable p X)
    (h2 : 5 ≤ p ∨ ∀ Q : Sylow 2 X, IsMulCommutative ↥(Q : Subgroup X))
    (hcore : Work.Fitting.pPrimeCore p X = ⊥) {A : Subgroup X} (hA : IsPGroup p A)
    {P : Sylow p X} (hcomm : ⁅⁅(P : Subgroup X), A⁆, A⁆ = ⊥) :
    A ≤ Work.Fitting.pCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hpsF : Work.Fitting.IsPSolvable p X := Work.Fitting.isPSolvable_of_hallHigman hp hsol
  by_cases hFbot : Work.Fitting.pCore p X = ⊥
  · haveI : Subsingleton X :=
      Work.Fitting.subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot p X hFbot hcore
    rw [hFbot]
    exact le_bot_iff.mpr ((Subgroup.eq_bot_iff_forall _).mpr fun x _ => Subsingleton.elim x 1)
  · have hFp : IsPGroup p ↥(Work.Fitting.pCore p X) := Work.HallHigman.isPGroup_pCore
    haveI hFn : (Work.Fitting.pCore p X).Normal := inferInstance
    have hfr := Work.PGroup.frattini_quotient_elementary hp (Work.Fitting.pCore p X) hFp
    haveI hcommQ : IsMulCommutative
        (↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X)) := hfr.1
    haveI hexpQ : Fact (∀ x : ↥(Work.Fitting.pCore p X) ⧸ frattini ↥(Work.Fitting.pCore p X),
        x ^ p = 1) := fact_pow_eq_one_of_exponent_dvd hfr.2
    have hker : Work.Fitting.pCore p X ≤
        (frattiniQuotRep p (Work.Fitting.pCore p X)).ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact frattiniQuotRep_eq_one_of_frattiniQuotConj_eq_one p _ (frattiniQuotConj_eq_one_of_mem hp hFp hy)
    have hsurjF : Function.Surjective
        (QuotientGroup.mk' (Work.Fitting.pCore p X)) := QuotientGroup.mk'_surjective _
    haveI : Finite (X ⧸ Work.Fitting.pCore p X) := Finite.of_surjective _ hsurjF
    let ρ' : X ⧸ Work.Fitting.pCore p X →*
        Module.End (ZMod p) (Additive (↥(Work.Fitting.pCore p X) ⧸
          frattini ↥(Work.Fitting.pCore p X))) :=
      QuotientGroup.lift _ _ hker
    have hρ'inj : Function.Injective ρ' := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      exact mem_pCore_of_frattiniQuotRep_eq_one hp hpsF hcore hy
    have hpsQ : Work.HallHigman.IsPSolvable p (X ⧸ Work.Fitting.pCore p X) :=
      Work.HallHigman.isPSolvable_quotient_prime hp _ hsol
    have hOpQ : Work.HallHigman.pCore p (X ⧸ Work.Fitting.pCore p X) = ⊥ := by
      rw [show Work.HallHigman.pCore p (X ⧸ Work.Fitting.pCore p X) =
        Work.Fitting.pCore p (X ⧸ Work.Fitting.pCore p X) from rfl]
      exact Work.Fitting.piCore_quotient_eq_bot (fun q => q = p) X
    have h2Q : p ≥ 5 ∨ ∀ Q : Sylow 2 (X ⧸ Work.Fitting.pCore p X),
        IsMulCommutative ↥(Q : Subgroup (X ⧸ Work.Fitting.pCore p X)) := by
      rcases h2 with h5 | hab
      · exact Or.inl h5
      · exact Or.inr (sylow_two_abelian_quotient (Work.Fitting.pCore p X) hab)
    have hcommF : ⁅⁅Work.Fitting.pCore p X, A⁆, A⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅Work.Fitting.pCore p X, A⁆, A⁆
          ≤ ⁅⁅(P : Subgroup X), A⁆, A⁆ :=
            Subgroup.commutator_mono_left
              (Subgroup.commutator_mono_left (Work.Fitting.pCore_le_sylow P))
        _ = ⊥ := hcomm
    have hA' : IsPGroup p (A.map (QuotientGroup.mk' (Work.Fitting.pCore p X))) := hA.map _
    have hquad : ∀ b ∈ A.map (QuotientGroup.mk' (Work.Fitting.pCore p X)),
        (ρ' b - 1) ^ 2 = 0 := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      rw [show ρ' (QuotientGroup.mk' (Work.Fitting.pCore p X) a) =
        frattiniQuotRep p (Work.Fitting.pCore p X) a from QuotientGroup.lift_mk' _ _ _]
      exact frattiniQuotRep_sub_one_sq_eq_zero hcommF ha
    have hAmap : A.map (QuotientGroup.mk' (Work.Fitting.pCore p X)) = ⊥ :=
      Work.PStable.pstable_representation hp hpodd hpsQ h2Q ρ' hρ'inj hOpQ _ hA' hquad
    have hle : A ≤ (QuotientGroup.mk' (Work.Fitting.pCore p X)).ker :=
      (Subgroup.map_eq_bot_iff A).mp hAmap
    rwa [QuotientGroup.ker_mk'] at hle

theorem ft7_2_cond3_pstable {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hsol : Work.HallHigman.IsPSolvable p X)
    (h2 : 5 ≤ p ∨ ∀ Q : Sylow 2 X, IsMulCommutative ↥(Q : Subgroup X))
    {A : Subgroup X} (hA : IsPGroup p A) {P : Sylow p X}
    (hcomm : ⁅⁅(P : Subgroup X), A⁆, A⁆ = ⊥) :
    A ≤ Work.Fitting.pPrimePCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsol' : Work.HallHigman.IsPSolvable p (X ⧸ Work.Fitting.pPrimeCore p X) :=
    Work.HallHigman.isPSolvable_quotient_prime hp (Work.Fitting.pPrimeCore p X) hsol
  have hcore' : Work.Fitting.pPrimeCore p (X ⧸ Work.Fitting.pPrimeCore p X) = ⊥ :=
    Work.Fitting.piCore_quotient_eq_bot (fun q => q ≠ p) X
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X)) :=
    QuotientGroup.mk'_surjective _
  haveI : Finite (X ⧸ Work.Fitting.pPrimeCore p X) := Finite.of_surjective _ hsurj
  have hA' : IsPGroup p (A.map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X))) := hA.map _
  let P' : Sylow p (X ⧸ Work.Fitting.pPrimeCore p X) := Sylow.mapSurjective hsurj P
  have hP'coe : (P' : Subgroup (X ⧸ Work.Fitting.pPrimeCore p X)) =
      (P : Subgroup X).map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X)) :=
    Sylow.coe_mapSurjective hsurj P
  have h2' : 5 ≤ p ∨ ∀ Q : Sylow 2 (X ⧸ Work.Fitting.pPrimeCore p X),
      IsMulCommutative ↥(Q : Subgroup (X ⧸ Work.Fitting.pPrimeCore p X)) := by
    rcases h2 with h5 | hab
    · exact Or.inl h5
    · exact Or.inr (sylow_two_abelian_quotient (Work.Fitting.pPrimeCore p X) hab)
  have hcomm' : ⁅⁅(P' : Subgroup (X ⧸ Work.Fitting.pPrimeCore p X)),
        A.map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X))⁆,
        A.map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X))⁆ = ⊥ := by
    rw [hP'coe, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hcomm,
      Subgroup.map_bot]
  have hmain : A.map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p X)) ≤
      Work.Fitting.pCore p (X ⧸ Work.Fitting.pPrimeCore p X) :=
    ft7_2_cond3_pstable_core hp hpodd hsol' h2' hcore' hA' hcomm'
  exact Subgroup.map_le_iff_le_comap.mp hmain

/-- Construct a Sylow `p`-subgroup of `↥H` from a `p`-subgroup of `p'`-index of `H`. -/
noncomputable def sylow_of_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P H : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup p P)
    (hnd : ¬ p ∣ (P.subgroupOf H).index) : Sylow p ↥H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPsh : IsPGroup p (P.subgroupOf H) :=
    hPp.comap_of_injective H.subtype Subtype.coe_injective
  refine Sylow.mk (P.subgroupOf H) hPsh ?_
  intro Q hQ hle
  have hidx : (P.subgroupOf H).relIndex Q * Q.index = (P.subgroupOf H).index :=
    Subgroup.relIndex_mul_index hle
  have hdvd : (P.subgroupOf H).relIndex Q ∣ (P.subgroupOf H).index := ⟨Q.index, hidx.symm⟩
  have hrel_nd : ¬ p ∣ (P.subgroupOf H).relIndex Q := fun h => hnd (h.trans hdvd)
  have hrel1 : (P.subgroupOf H).relIndex Q = 1 := by
    change ((P.subgroupOf H).subgroupOf Q).index = 1
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
    have hdvdpow : ((P.subgroupOf H).subgroupOf Q).index ∣ p ^ m := by
      rw [← hm]; exact Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvdpow
    have hrel_nd' : ¬ p ∣ p ^ k := by rw [← hk]; exact hrel_nd
    rw [hk]
    have hk0 : k = 0 := by
      by_contra hk0
      exact hrel_nd' (dvd_pow_self p hk0)
    rw [hk0, pow_zero]
  have hQle : Q ≤ P.subgroupOf H := Subgroup.relIndex_eq_one.mp hrel1
  exact le_antisymm hQle hle

end Work.LocalPrelim

namespace Work.LocalPrelim

lemma le_normalizer_of_normal_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (h : (H.subgroupOf K).Normal) : K ≤ Subgroup.normalizer (H : Set G) := by
  have hf := (Subgroup.normal_subgroupOf_iff hHK).mp h
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro a
  exact ⟨fun ha => hf a x ha hx,
    fun hax => by
      have h2 := hf (x * a * x⁻¹) x⁻¹ hax (K.inv_mem hx)
      simpa [mul_assoc] using h2⟩

theorem ft7_9 {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {H P P0 Pstar : Subgroup X} (hH : Work.Fitting.IsPSolvable p ↥H)
    (hcond : Odd (Nat.card X) ∨ 5 ≤ p ∨
      (p = 3 ∧ ∀ Q : Sylow 2 ↥H, IsMulCommutative ↥(Q : Subgroup ↥H)))
    (hP : IsSylowIn p P H) (hP0 : P0 = pPrimePCoreIn p H ⊓ P)
    (hPstar : P ≤ Pstar) (hPstarp : IsPGroup p Pstar)
    (hPn : IsSylowIn p P (Subgroup.normalizer (P0 : Set X))) :
    ∀ A : Subgroup X, IsSCN Pstar A → A ≤ P0 := by
  intro A hA
  obtain ⟨hAle, hAnorm, hAcomm, hASC⟩ := hA
  obtain ⟨hPH, hPp, hPnd⟩ := hP
  by_cases hpodd : Odd p
  · -- ---- main case ----
    have hAnormPstar : Pstar ≤ Subgroup.normalizer (A : Set X) :=
      le_normalizer_of_normal_subgroupOf hAle hAnorm
    have hAp : IsPGroup p A := hPstarp.to_le hAle
    have h2H : 5 ≤ p ∨ ∀ Q : Sylow 2 ↥H, IsMulCommutative ↥(Q : Subgroup ↥H) := by
      rcases hcond with h | h | h
      · exact Or.inr fun Q =>
          isMulCommutative_sylow_two_of_odd_card
            (Odd.of_dvd_nat h (Subgroup.card_subgroup_dvd_card H)) Q
      · exact Or.inl h
      · exact Or.inr h.2
    have hpsH : Work.HallHigman.IsPSolvable p ↥H := ft7_2_psolvable_bridge hp hH
    let PH : Sylow p ↥H := sylow_of_le_of_not_dvd_index hp hPH hPp hPnd
    set B : Subgroup X := A ⊓ P with hBdef
    have hBleA : B ≤ A := by rw [hBdef]; exact inf_le_left
    have hBleP : B ≤ P := by rw [hBdef]; exact inf_le_right
    have hBH : B ≤ H := hBleP.trans hPH
    have hBcomm : IsMulCommutative ↥B := by
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      have hxy : (⟨(x : X), hBleA x.2⟩ : ↥A) * ⟨(y : X), hBleA y.2⟩ =
          ⟨(y : X), hBleA y.2⟩ * ⟨(x : X), hBleA x.2⟩ := hAcomm.is_comm.comm _ _
      have h2 := congrArg (fun z : ↥A => (z : X)) hxy
      simpa using h2
    have hcommX : ⁅⁅P, B⁆, B⁆ = ⊥ := by
      have h1 : ⁅P, B⁆ ≤ B := by
        rw [hBdef]
        refine le_inf ?_ ?_
        · calc ⁅P, A ⊓ P⁆ ≤ ⁅Pstar, A ⊓ P⁆ := Subgroup.commutator_mono_left hPstar
            _ ≤ ⁅Pstar, A⁆ := Subgroup.commutator_mono_right inf_le_left
            _ ≤ A := by
                rw [Subgroup.commutator_comm]
                exact Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormPstar
        · rw [Subgroup.commutator_le]
          intro x hx y hy
          obtain ⟨-, hyP⟩ := Subgroup.mem_inf.mp hy
          rw [commutatorElement_def]
          exact P.mul_mem (P.mul_mem (P.mul_mem hx hyP) (P.inv_mem hx)) (P.inv_mem hyP)
      refine le_bot_iff.mp ?_
      have hBB : ⁅B, B⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxy : (⟨y, hy⟩ : ↥B) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hy⟩ :=
          hBcomm.is_comm.comm _ _
        have h2 := congrArg (fun z : ↥B => (z : X)) hxy
        simpa using h2
      calc ⁅⁅P, B⁆, B⁆ ≤ ⁅B, B⁆ := Subgroup.commutator_mono_left h1
        _ = ⊥ := hBB
    have hcommH : ⁅⁅(PH : Subgroup ↥H), B.subgroupOf H⁆, B.subgroupOf H⁆ = ⊥ := by
      have hmap : Subgroup.map H.subtype
          ⁅⁅(PH : Subgroup ↥H), B.subgroupOf H⁆, B.subgroupOf H⁆ = ⊥ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator]
        rw [show Subgroup.map H.subtype (PH : Subgroup ↥H) = P from
              Subgroup.map_subgroupOf_eq_of_le hPH,
            show Subgroup.map H.subtype (B.subgroupOf H) = B from
              Subgroup.map_subgroupOf_eq_of_le hBH]
        exact hcommX
      have hle := (Subgroup.map_eq_bot_iff _).mp hmap
      rw [Subgroup.ker_subtype] at hle
      exact le_bot_iff.mp hle
    have hPsh : IsPGroup p (P.subgroupOf H) :=
      hPp.comap_of_injective H.subtype Subtype.coe_injective
    have hBsubp : IsPGroup p (B.subgroupOf H) :=
      hPsh.to_le (Subgroup.comap_mono hBleP)
    have hcore := ft7_2_cond3_pstable hp hpodd hpsH h2H hBsubp hcommH
    have hBleR0 : B ≤ pPrimePCoreIn p H := by
      have hmapm := Subgroup.map_mono (f := H.subtype) hcore
      rwa [Subgroup.map_subgroupOf_eq_of_le hBH] at hmapm
    have hBleP0 : B ≤ P0 := by
      rw [hP0]; exact le_inf hBleR0 hBleP
    by_cases hAP0 : A ≤ P0
    · exact hAP0
    · exfalso
      have hP0leP : P0 ≤ P := by rw [hP0]; exact inf_le_right
      have hBeq : B = A ⊓ P0 := by
        refine le_antisymm (le_inf hBleA hBleP0) ?_
        rw [hBdef]
        exact le_inf inf_le_left (inf_le_right.trans hP0leP)
      have hlt : B < A := by
        refine lt_of_le_of_ne hBleA ?_
        intro hBA
        exact hAP0 (hBA ▸ hBleP0)
      have hP0p : IsPGroup p P0 := hPp.to_le hP0leP
      have hP0NA : P0 ≤ Subgroup.normalizer (A : Set X) :=
        hP0leP.trans (hPstar.trans hAnormPstar)
      have hPP_le : ⁅P, P⁆ ≤ P := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
      have hP0NB : P0 ≤ Subgroup.normalizer (B : Set X) := by
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        rw [hBdef]
        refine le_inf ?_ ?_
        · calc ⁅A ⊓ P, P0⁆ ≤ ⁅A, P0⁆ := Subgroup.commutator_mono_left inf_le_left
            _ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hP0NA
        · calc ⁅A ⊓ P, P0⁆ ≤ ⁅P, P0⁆ := Subgroup.commutator_mono_left inf_le_right
            _ ≤ P := (Subgroup.commutator_mono_right hP0leP).trans hPP_le
      obtain ⟨B', hBB', hB'A, hidx, hcommQ⟩ :=
        exists_invariant_index_prime hp hP0p hAp hP0NA hP0NB hBleA hlt
      have hB'lt : B < B' := by
        refine lt_of_le_of_ne hBB' ?_
        intro hEq
        have h1 : (B.subgroupOf B').index = 1 := by
          rw [hEq, Subgroup.subgroupOf_self, Subgroup.index_top]
        rw [h1] at hidx
        exact hp.ne_one hidx.symm
      have hB'leN : B' ≤ Subgroup.normalizer (P0 : Set X) := by
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        exact hcommQ.trans hBleP0
      have hR0leH : pPrimePCoreIn p H ≤ H := Subgroup.map_subtype_le _
      have hR0sub : ((pPrimePCoreIn p H).subgroupOf H).Normal := by
        have hEq : (pPrimePCoreIn p H).subgroupOf H = Work.Fitting.pPrimePCore p ↥H := by
          show (((Work.Fitting.pPrimePCore p ↥H).map H.subtype).comap H.subtype) = _
          rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
        rw [hEq]; infer_instance
      have hPleNR0 : P ≤ Subgroup.normalizer (pPrimePCoreIn p H : Set X) :=
        hPH.trans (le_normalizer_of_normal_subgroupOf hR0leH hR0sub)
      have hPleN : P ≤ Subgroup.normalizer (P0 : Set X) := by
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        rw [hP0]
        refine le_inf ?_ ?_
        · calc ⁅pPrimePCoreIn p H ⊓ P, P⁆ ≤ ⁅pPrimePCoreIn p H, P⁆ :=
                Subgroup.commutator_mono_left inf_le_left
            _ ≤ pPrimePCoreIn p H :=
                Subgroup.le_normalizer_iff_commutator_le_left.mp hPleNR0
        · calc ⁅pPrimePCoreIn p H ⊓ P, P⁆ ≤ ⁅P, P⁆ :=
                Subgroup.commutator_mono_left inf_le_right
            _ ≤ P := hPP_le
      have hB'leP : B' ≤ P := by
        let NX : Subgroup X := Subgroup.normalizer (P0 : Set X)
        have hPN : P ≤ NX := hPleN
        have hndN : ¬ p ∣ (P.subgroupOf NX).index := hPn.2.2
        let NS : Sylow p ↥NX := sylow_of_le_of_not_dvd_index hp hPN hPp hndN
        have hKN : B' ⊔ P ≤ NX := sup_le hB'leN hPleN
        have hKp : IsPGroup p ↥(B' ⊔ P) :=
          hPstarp.to_le (sup_le (hB'A.trans hAle) hPstar)
        have hK'p : IsPGroup p ((B' ⊔ P).subgroupOf NX) :=
          hKp.comap_of_injective NX.subtype Subtype.coe_injective
        have hle_sub : P.subgroupOf NX ≤ (B' ⊔ P).subgroupOf NX :=
          Subgroup.comap_mono le_sup_right
        have hmax : (B' ⊔ P).subgroupOf NX = P.subgroupOf NX := NS.is_maximal' hK'p hle_sub
        have hthis : B' ⊔ P = P := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hKN, hmax,
            Subgroup.map_subgroupOf_eq_of_le hPN]
        exact hthis ▸ le_sup_left
      have hB'leB : B' ≤ B := by
        rw [hBdef]
        exact le_inf hB'A hB'leP
      exact absurd hB'leB (not_le_of_gt hB'lt)
  · -- ---- `p = 2` ----
    have hp_eq2 : p = 2 := by
      rcases hp.eq_two_or_odd with h | h
      · exact h
      · rw [Nat.odd_iff] at hpodd
        exact absurd h hpodd
    subst hp_eq2
    have hoddX : Odd (Nat.card X) := by
      rcases hcond with h | h | h
      · exact h
      · omega
      · exact absurd h.1 (by norm_num)
    have hcard : Nat.card ↥Pstar = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPstarp
      have hodd : Odd (2 ^ k) :=
        hk ▸ Odd.of_dvd_nat hoddX (Subgroup.card_subgroup_dvd_card Pstar)
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0))
      rw [hk, hk0, pow_zero]
    have hbot : Pstar = ⊥ := Subgroup.card_eq_one.mp hcard
    rw [hbot] at hAle
    exact hAle.trans bot_le

end Work.LocalPrelim
