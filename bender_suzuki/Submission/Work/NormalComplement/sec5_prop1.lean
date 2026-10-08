import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.two_pow_ne_prime_pow_succ_add_one
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.Coprime.All
import Submission.Work.GlaubermanZJ.frattini_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-!
# Peterfalvi I Ch. III §5 Proposition 1: `p ≥ 7`

The route (steps 1 and 2 of Peterfalvi I Ch. III §5, p.182):

* `U = ⟨Inv H⟩`;
* (step 1) `U ⊓ E' ≠ ⊥`;
* (step 2) `W = U`;
* `Ω = Inv H = u^W` is a single conjugacy class of `W` of prime power size `r^(a+1)`, so
  Burnside's class theorem (`Design.BurnsideClassProp`) produces `N ⊴ W`, `N ≠ ⊤` with
  `Ω ⊆ uN`; then `W = ⟨Ω⟩` forces `|W/N| = 2` and `N` odd, so `4 ∤ |W|`; but `W` contains a
  four-group, so `4 ∣ |W|`, a contradiction.
-/

variable {G : Type} [Group G] [Finite G]

/-! ## §0  The subgroup `U = ⟨Inv H⟩` -/

/-- The involutions of `⟨Inv H⟩` are exactly the involutions of `H`. -/
theorem involutions_closure_involutions {H : Subgroup G} :
    involutions ((Subgroup.closure (involutions (H : Set G)) : Subgroup G) : Set G) =
      involutions (H : Set G) := by
  ext x
  rw [Work.ThreePoints.mem_involutions, Work.ThreePoints.mem_involutions]
  constructor
  · rintro ⟨hx, hx2⟩
    have hxH : x ∈ H :=
      (Subgroup.closure_le H).mpr (fun y hy => (Work.ThreePoints.mem_involutions.mp hy).1) hx
    exact ⟨hxH, hx2⟩
  · rintro ⟨hx, hx2⟩
    exact ⟨Subgroup.subset_closure ⟨hx, hx2⟩, hx2⟩

/-- `⟨Inv H⟩ ≤ H`. -/
theorem closure_involutions_le (H : Subgroup G) :
    Subgroup.closure (involutions (H : Set G)) ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hy => (Work.ThreePoints.mem_involutions.mp hy).1

/-- `⟨Inv H⟩ ⊴ H`: `H` permutes its involutions by conjugation. -/
theorem normalizer_closure_involutions (H : Subgroup G) :
    H ≤ Subgroup.normalizer (Subgroup.closure (involutions (H : Set G)) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  have hgen : ∀ z ∈ involutions (H : Set G),
      x * z * x⁻¹ ∈ Subgroup.closure (involutions (H : Set G)) := by
    intro z hz
    refine Subgroup.subset_closure ?_
    rw [Work.ThreePoints.mem_involutions] at hz ⊢
    refine ⟨H.mul_mem (H.mul_mem hx hz.1) (H.inv_mem hx), ?_⟩
    rw [show x * z * x⁻¹ = MulAut.conj x z by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, hz.2]
  have hmap : (Subgroup.closure (involutions (H : Set G))).map (MulAut.conj x).toMonoidHom ≤
      Subgroup.closure (involutions (H : Set G)) := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro z hz
    exact hgen z hz
  refine hmap (Subgroup.mem_map.mpr ⟨y, hy, ?_⟩)
  simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-! ## §1  `⟨J(D,t)⟩` is transitive on `Inv H` -/

section Trans

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- **Peterfalvi I Ch. II §4 Prop. 2 (c)**, transitivity form: `⟨J(D,t)⟩` is transitive on the
involutions of `H`. -/
theorem kapp_transitive (hC4 : ChIIFourProp) (hBP : BenderPrelimProp)
    (h : Design.Setup5 G H t W p P A r) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G),
      ∃ k ∈ Kgrp (twoPoint H t) t, k * u * k⁻¹ = v := by
  obtain ⟨u₀, hu₀, hVeq⟩ := (hC4 G h.sit H h.se t h.invol h.notMem).2.1
  have hnormD : NormalizedBy t (twoPoint H t) := normalizedBy_twoPoint h.invol
  have hoddD : Odd (Nat.card (twoPoint H t)) := h.se.2.2 t h.notMem
  have hcopD : Nat.Coprime (Nat.card (twoPoint H t)) 2 := Nat.coprime_two_right.mpr hoddD
  obtain ⟨-, -, hDnorm, hDsup, -, -, -⟩ :=
    appI_four (d := 2) Nat.prime_two h.invol hnormD hcopD
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol hnormD hcopD).2 rfl).1
  have hKgrp_eq : Subgroup.closure (Kapp t (twoPoint H t)) = Kgrp (twoPoint H t) t := by
    rw [hKappKset]; rfl
  have hVD : centD H t ≤ twoPoint H t := inf_le_left
  have hVN : centD H t ≤ Subgroup.normalizer (Kgrp (twoPoint H t) t : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv k hk
    have hk' : k ∈ Subgroup.closure (Kapp t (twoPoint H t)) := by rw [hKgrp_eq]; exact hk
    have hres := hDnorm v (hVD hv) k hk'
    rwa [hKgrp_eq] at hres
  have hDV : centD H t ⊔ Kgrp (twoPoint H t) t = twoPoint H t := by
    have hcent : centD H t = Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
      show twoPoint H t ⊓ Subgroup.centralizer ({t} : Set G) = _
      rw [inf_comm]
    rw [hcent, ← hKgrp_eq, sup_comm, hDsup]
  have hDVset : ((twoPoint H t : Subgroup G) : Set G) =
      ((centD H t : Subgroup G) : Set G) * ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN, hDV]
  have hVcomm : ∀ v ∈ (centD H t : Set G), v * u₀ * v⁻¹ = u₀ := by
    intro v hv
    have hvC : v ∈ Subgroup.centralizer ({u₀} : Set G) := by
      have hle : centD H t ≤ Subgroup.centralizer ({u₀} : Set G) := by
        rw [hVeq]; exact inf_le_right
      exact hle hv
    rw [Subgroup.mem_centralizer_singleton_iff] at hvC
    rw [hvC, mul_assoc, mul_inv_cancel, mul_one]
  have hkey : ∀ d ∈ (twoPoint H t : Set G),
      ∃ k ∈ (Kgrp (twoPoint H t) t : Set G), d * u₀ * d⁻¹ = k * u₀ * k⁻¹ := by
    intro d hd
    have hdmem : d ∈ ((centD H t : Subgroup G) : Set G) *
        ((Kgrp (twoPoint H t) t : Subgroup G) : Set G) := hDVset ▸ hd
    rw [Set.mem_mul] at hdmem
    obtain ⟨v, hv, k, hk, rfl⟩ := hdmem
    have hv2 : v⁻¹ * u₀ * v = u₀ := by
      simpa using hVcomm v⁻¹ ((centD H t).inv_mem hv)
    refine ⟨v * k * v⁻¹, ?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp hVN) v hv k hk
    · calc (v * k) * u₀ * (v * k)⁻¹ = v * k * (v⁻¹ * u₀ * v) * k⁻¹ * v⁻¹ := by
            rw [hv2]; group
        _ = (v * k * v⁻¹) * u₀ * (v * k * v⁻¹)⁻¹ := by group
  have hInv_eq : ∀ y ∈ involutions (H : Set G),
      ∃ k ∈ (Kgrp (twoPoint H t) t : Set G), k * u₀ * k⁻¹ = y := by
    intro y hy
    obtain ⟨d, hdD, hd⟩ := hBP G h.sit H h.se t h.invol h.notMem u₀ hu₀ y hy
    obtain ⟨k, hk, hky⟩ := hkey d hdD
    exact ⟨k, hk, hky ▸ hd⟩
  intro u hu v hv
  obtain ⟨k₁, hk₁, hk₁eq⟩ := hInv_eq u hu
  obtain ⟨k₂, hk₂, hk₂eq⟩ := hInv_eq v hv
  refine ⟨k₂ * k₁⁻¹, (Kgrp (twoPoint H t) t).mul_mem hk₂ ((Kgrp (twoPoint H t) t).inv_mem hk₁), ?_⟩
  rw [← hk₁eq, ← hk₂eq]
  group

end Trans

/-! ## §2  Order-theoretic facts about `E'` and `⟨K⟩` -/

section Order

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- For `p ∈ {3,5}`, `|J(D,t)| = r^(a+1)` with `a ≥ 1`. -/
theorem setup5_Kset_card (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5) :
    ∃ m : ℕ, 1 ≤ m ∧ (Kset (twoPoint H t) t).ncard = r ^ m := by
  obtain ⟨a, ha1, hKa⟩ := h.K_card
  have h2p : (2 ^ p - 1).Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
  have hr : r = 2 ^ p - 1 := by
    rcases (Nat.dvd_prime h2p).mp h.r_dvd with h1 | h2
    · exact absurd h1 h.r_prime.ne_one
    · exact h2
  exact ⟨a + 1, by omega, by rw [hKa, ← hr, pow_succ]⟩

/-- `E' = [E,E]` is nontrivial. -/
theorem ecomm_ne_bot (h : Design.Setup5 G H t W p P A r) : Design.Ecomm H t W ≠ ⊥ := by
  intro hbot
  apply h.fitV_ne
  rw [h.fitV]
  rw [hbot]
  simp

/-- `E' ≤ D ≤ H`. -/
theorem ecomm_le_H (h : Design.Setup5 G H t W p P A r) : Design.Ecomm H t W ≤ H := by
  have h1 : Design.Ecomm H t W ≤ Design.Egrp H t W := by
    simpa using Subgroup.commutator_le_sup (Design.Egrp H t W) (Design.Egrp H t W)
  have h2 : Design.Egrp H t W ≤ H :=
    le_trans (inf_le_right : Design.Egrp H t W ≤ twoPoint H t) inf_le_left
  exact le_trans h1 h2

/-- For `p ∈ {3,5}`, `E'` is an `r`-group. -/
theorem ecomm_isPGroup (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5) :
    IsPGroup r ↥(Design.Ecomm H t W) := by
  obtain ⟨m, -, hKm⟩ := setup5_Kset_card h hp
  refine IsPGroup.of_card (n := (Nat.card ↥(Design.Ecomm H t W)).primeFactorsList.length) ?_
  refine Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_ne_zero.mpr ⟨Nonempty.intro (1 : ↥(Design.Ecomm H t W)), inferInstance⟩) ?_
  intro d hd hdvd
  have h1 : d ∣ (Kset (twoPoint H t) t).ncard := (h.E'_primes d hd).mp hdvd
  rw [hKm] at h1
  rcases (Nat.dvd_prime h.r_prime).mp (Nat.Prime.dvd_of_dvd_pow hd h1) with h3 | h3
  · exact absurd h3 hd.ne_one
  · exact h3

/-- For `p ∈ {3,5}`, `r ∤ |H : E'|`: `E'` is the Sylow `r`-subgroup of `H`. -/
theorem ecomm_relIndex_not_dvd (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5) :
    ¬ r ∣ (Design.Ecomm H t W).relIndex H := by
  obtain ⟨m, hm1, hKm⟩ := setup5_Kset_card h hp
  have hrdvd : r ∣ Nat.card ↥(Design.Ecomm H t W) :=
    (h.E'_primes r h.r_prime).mpr (by rw [hKm]; exact dvd_pow_self r (by omega))
  have hidx : ¬ r ∣ (Design.Ecomm H t W).index := by
    intro hdvd
    have hg : Nat.gcd (Nat.card ↥(Design.Ecomm H t W)) (Design.Ecomm H t W).index = 1 :=
      h.E'_hall
    have h1 : r ∣ Nat.gcd (Nat.card ↥(Design.Ecomm H t W)) (Design.Ecomm H t W).index :=
      Nat.dvd_gcd hrdvd hdvd
    exact h.r_prime.not_dvd_one (hg ▸ h1)
  intro hrel
  refine hidx ?_
  rw [← Subgroup.relIndex_mul_index (ecomm_le_H h)]
  exact dvd_mul_of_dvd_left hrel _

/-- If `U ≤ H` is `H`-normal and `U ⊓ E' = ⊥`, then `r ∤ |U|`. -/
theorem not_dvd_card_of_inf_eq_bot {U : Subgroup G} (h : Design.Setup5 G H t W p P A r)
    (hp : p = 3 ∨ p = 5) (hUH : U ≤ H) (hUn : H ≤ Subgroup.normalizer (U : Set G))
    (hUE : U ⊓ Design.Ecomm H t W = ⊥) : ¬ r ∣ Nat.card ↥U := by
  have hE'H : Design.Ecomm H t W ≤ H := ecomm_le_H h
  have hE'U : Design.Ecomm H t W ≤ Subgroup.normalizer (U : Set G) := le_trans hE'H hUn
  have hcard : Nat.card ↥(U ⊔ Design.Ecomm H t W) * Nat.card ↥(U ⊓ Design.Ecomm H t W) =
      Nat.card ↥U * Nat.card ↥(Design.Ecomm H t W) := card_sup_mul_card_inf hE'U
  rw [hUE] at hcard
  have hcard' : Nat.card ↥(U ⊔ Design.Ecomm H t W) =
      Nat.card ↥U * Nat.card ↥(Design.Ecomm H t W) := by
    simpa using hcard
  have hrel : (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) = Nat.card ↥U := by
    have h1 : (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) *
        Nat.card ↥(Design.Ecomm H t W) = Nat.card ↥(U ⊔ Design.Ecomm H t W) :=
      relIndex_mul_card_of_le' le_sup_right
    rw [hcard'] at h1
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos_iff.mpr ⟨Nonempty.intro (1 : ↥(Design.Ecomm H t W)), inferInstance⟩) h1
  have hnot : ¬ r ∣ (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) := by
    intro hdvd
    have hprod : (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) *
        (U ⊔ Design.Ecomm H t W).relIndex H = (Design.Ecomm H t W).relIndex H :=
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hUH hE'H)
    exact ecomm_relIndex_not_dvd h hp (hprod ▸ dvd_mul_of_dvd_left hdvd _)
  rwa [hrel] at hnot

/-- `⟨K⟩ ≤ H`. -/
theorem kgrp_le_H {H : Subgroup G} {t : G} : Kgrp (twoPoint H t) t ≤ H :=
  le_trans ((Subgroup.closure_le (twoPoint H t)).mpr fun _ hx => hx.1) inf_le_left

/-- For `p ∈ {3,5}`, `⟨K⟩` is an `r`-group. -/
theorem kgrp_isPGroup (hFT : FeitThompsonProp) (h : Design.Setup5 G H t W p P A r)
    (hp : p = 3 ∨ p = 5) : IsPGroup r ↥(Kgrp (twoPoint H t) t) := by
  obtain ⟨m, -, hKm⟩ := setup5_Kset_card h hp
  have hnormD : NormalizedBy t (twoPoint H t) := normalizedBy_twoPoint h.invol
  have hcopD : Nat.Coprime (Nat.card (twoPoint H t)) 2 :=
    Nat.coprime_two_right.mpr (h.se.2.2 t h.notMem)
  have hsolv : Group.IsSolvable ↥(twoPoint H t) := hFT _ (h.se.2.2 t h.notMem)
  have hq := appI_five_a (d := 2) Nat.prime_two h.invol hnormD hcopD hsolv
  have hKappKset : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two h.invol hnormD hcopD).2 rfl).1
  have hKgrp_eq : Subgroup.closure (Kapp t (twoPoint H t)) = Kgrp (twoPoint H t) t := by
    rw [hKappKset]; rfl
  refine IsPGroup.of_card (n := (Nat.card ↥(Kgrp (twoPoint H t) t)).primeFactorsList.length) ?_
  refine Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_ne_zero.mpr ⟨Nonempty.intro (1 : ↥(Kgrp (twoPoint H t) t)), inferInstance⟩) ?_
  intro d hd hdvd
  have hdvd' : d ∣ Nat.card ↥(Subgroup.closure (Kapp t (twoPoint H t))) := by
    rw [hKgrp_eq]; exact hdvd
  have h1 : d ∣ (Kset (twoPoint H t) t).ncard := by
    have h2 := (hq d hd).mp hdvd'
    rwa [hKappKset] at h2
  rw [hKm] at h1
  rcases (Nat.dvd_prime h.r_prime).mp (Nat.Prime.dvd_of_dvd_pow hd h1) with h3 | h3
  · exact absurd h3 hd.ne_one
  · exact h3

end Order

/-! ## §3  Step 1: `U ⊓ E' ≠ ⊥` -/

section Step1

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- For `p ∈ {3,5}`, `|J(D,t)| = r^(a+1)` with `a ≥ 1`. -/
theorem setup5_Kset_card' (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5) :
    ∃ a : ℕ, 1 ≤ a ∧ (Kset (twoPoint H t) t).ncard = r ^ (a + 1) := by
  obtain ⟨a, ha1, hKa⟩ := h.K_card
  have h2p : (2 ^ p - 1).Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
  have hr : r = 2 ^ p - 1 := by
    rcases (Nat.dvd_prime h2p).mp h.r_dvd with h1 | h2
    · exact absurd h1 h.r_prime.ne_one
    · exact h2
  exact ⟨a, ha1, by rw [hKa, ← hr, pow_succ]⟩

/-- A nontrivial finite `2`-group has an involution in its centre. -/
theorem exists_orderOf_two_mem_center {X : Type} [Group X] [Finite X]
    (h : IsPGroup 2 X) (hne : Subgroup.center X ≠ ⊥) :
    ∃ w : X, w ∈ Subgroup.center X ∧ orderOf w = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype ↥(Subgroup.center X) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  have hdvd : Nat.card ↥(Subgroup.center X) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hlt : 1 < Nat.card ↥(Subgroup.center X) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hm; omega
    · exact h0
  have h2dvd : 2 ∣ Fintype.card ↥(Subgroup.center X) := by
    rw [Fintype.card_eq_nat_card, hm]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center X)) 2 h2dvd
  refine ⟨(z : X), z.2, ?_⟩
  rw [show ((z : Subgroup.center X) : X) = Subgroup.subtype (Subgroup.center X) z from rfl]
  rw [← hz]
  exact orderOf_injective _ (Subgroup.subtype_injective _) z

/-- **Peterfalvi I Ch. III §5 Prop. 1, step 1.**  For `p ∈ {3,5}`, `⟨Inv H⟩ ⊓ E' ≠ ⊥`. -/
theorem step1 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hBP : BenderPrelimProp)
    (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5) :
    Subgroup.closure (involutions (H : Set G)) ⊓ Design.Ecomm H t W ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨h.r_prime⟩
  set U : Subgroup G := Subgroup.closure (involutions (H : Set G)) with hUdef
  by_contra hne
  have hUE : U ⊓ Design.Ecomm H t W = ⊥ := hne
  have hUH : U ≤ H := closure_involutions_le H
  have hUn : H ≤ Subgroup.normalizer (U : Set G) := normalizer_closure_involutions H
  have hnotdvd : ¬ r ∣ Nat.card ↥U := not_dvd_card_of_inf_eq_bot h hp hUH hUn hUE
  have hKp : IsPGroup r ↥(Kgrp (twoPoint H t) t) := kgrp_isPGroup hFT h hp
  have hKleH : Kgrp (twoPoint H t) t ≤ H := kgrp_le_H
  have hKleD : Kgrp (twoPoint H t) t ≤ twoPoint H t :=
    (Subgroup.closure_le (twoPoint H t)).mpr fun _ hx => hx.1
  have hKodd : Odd (Nat.card ↥(Kgrp (twoPoint H t) t)) :=
    Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le hKleD)
  have hsolvK : Group.IsSolvable ↥(Kgrp (twoPoint H t) t) := hFT _ hKodd
  haveI : FT.Normalizes (Kgrp (twoPoint H t) t) U := ⟨le_trans hKleH hUn⟩
  have hcop : Nat.Coprime (Nat.card ↥(Kgrp (twoPoint H t) t)) (Nat.card ↥U) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp
    rw [hn]
    exact ((h.r_prime.coprime_iff_not_dvd).mpr hnotdvd).pow_left n
  obtain ⟨Sy, hSy⟩ := Work.Coprime.exists_invariant_sylow (↥(Kgrp (twoPoint H t) t)) hcop
    (Or.inl hsolvK) 2
  set S : Subgroup G := (Sy : Subgroup ↥U).map U.subtype with hSdef
  have hSU : S ≤ U := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 ↥S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Sy.isPGroup'
    refine IsPGroup.of_card (n := n) ?_
    rw [hSdef, Subgroup.card_map_of_injective U.subtype_injective]
    exact hn
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hSy1 : Nat.card ↥(Sy : Subgroup ↥U) = 1 := by
      have h1 : Nat.card ↥(S : Subgroup G) = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hSdef, Subgroup.card_map_of_injective U.subtype_injective] at h1
      exact h1
    obtain ⟨u₀, hu₀, -⟩ := (hC4 G h.sit H h.se t h.invol h.notMem).2.1
    have hu₀U : u₀ ∈ U := Subgroup.subset_closure hu₀
    have hu2 : orderOf u₀ = 2 := (Work.ThreePoints.mem_involutions.mp hu₀).2
    have h2dvd : 2 ∣ Nat.card ↥U := by
      have := Subgroup.orderOf_dvd_natCard U hu₀U
      rwa [hu2] at this
    rw [← Subgroup.card_mul_index (Sy : Subgroup ↥U), hSy1, one_mul] at h2dvd
    exact (Sylow.not_dvd_index Sy) h2dvd
  -- `S` is `⟨K⟩`-invariant
  have hSinv : ∀ k ∈ (Kgrp (twoPoint H t) t : Set G), ∀ z ∈ S, k * z * k⁻¹ ∈ S := by
    intro k hk z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hfix' : (⟨k, hk⟩ : ↥(Kgrp (twoPoint H t) t)) • (Sy : Subgroup ↥U) =
        (Sy : Subgroup ↥U) := by
      have h1 := Sylow.pointwise_smul_def (g := (⟨k, hk⟩ : ↥(Kgrp (twoPoint H t) t))) (P := Sy)
      rw [← h1, hSy ⟨k, hk⟩]
    refine Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : ↥(Kgrp (twoPoint H t) t)) • y, ?_, ?_⟩
    · rw [← hfix']
      exact Subgroup.smul_mem_pointwise_smul y _ _ hy
    · exact FT.conj_smul_coe (Kgrp (twoPoint H t) t) U ⟨k, hk⟩ y
  have hSUinv : involutions (S : Set G) ⊆ involutions (H : Set G) := by
    intro z hz
    rw [Work.ThreePoints.mem_involutions] at hz ⊢
    exact ⟨hUH (hSU hz.1), hz.2⟩
  have hSinv2 : ∀ k ∈ (Kgrp (twoPoint H t) t : Set G),
      ∀ z ∈ involutions (S : Set G), k * z * k⁻¹ ∈ involutions (S : Set G) := by
    intro k hk z hz
    rw [Work.ThreePoints.mem_involutions] at hz ⊢
    refine ⟨hSinv k hk z hz.1, ?_⟩
    rw [show k * z * k⁻¹ = MulAut.conj k z by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, hz.2]
  have hSinvne : (involutions (S : Set G)).Nonempty := by
    haveI : Fintype ↥S := Fintype.ofFinite _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero] at hn
        exact absurd (Subgroup.card_eq_one.mp hn) hSne
      · exact h0
    have h2dvd : 2 ∣ Fintype.card ↥S := by
      rw [Fintype.card_eq_nat_card, hn]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := ↥S) 2 h2dvd
    exact ⟨(z : G), ⟨z.2, by rw [← hz]; exact orderOf_injective _ (Subgroup.subtype_injective _) z⟩⟩
  have hSeq : involutions (S : Set G) = involutions (H : Set G) := by
    refine Set.Subset.antisymm hSUinv ?_
    intro x hx
    obtain ⟨y, hy⟩ := hSinvne
    obtain ⟨k, hk, hkxy⟩ := kapp_transitive hC4 hBP h y (hSUinv hy) x hx
    rw [← hkxy]
    exact hSinv2 k hk y hy
  have hUS : U ≤ S := by
    rw [hUdef]
    refine (Subgroup.closure_le S).mpr ?_
    intro x hx
    have hxS : x ∈ involutions (S : Set G) := hSeq.symm ▸ hx
    exact (Work.ThreePoints.mem_involutions.mp hxS).1
  have hUSeq : U = S := le_antisymm hUS hSU
  have hU2 : IsPGroup 2 ↥U := hUSeq.symm ▸ hS2
  -- the central involutions of `U` are all of `Inv H`
  have hUnontriv : Nontrivial ↥U := by
    obtain ⟨u₀, hu₀, -⟩ := (hC4 G h.sit H h.se t h.invol h.notMem).2.1
    have hu₀U : u₀ ∈ U := Subgroup.subset_closure hu₀
    have hu₂ : orderOf u₀ = 2 := (Work.ThreePoints.mem_involutions.mp hu₀).2
    refine ⟨⟨u₀, hu₀U⟩, 1, ?_⟩
    intro h
    have h1 : u₀ = 1 := congrArg (fun z : ↥U => (z : G)) h
    rw [h1, orderOf_one] at hu₂
    exact absurd hu₂ (by norm_num)
  have hZbot : ⊥ < Subgroup.center ↥U := IsPGroup.bot_lt_center (p := 2) hU2
  have hZne : Subgroup.center ↥U ≠ ⊥ := bot_lt_iff_ne_bot.mp hZbot
  obtain ⟨w, hwZ, hw2⟩ := exists_orderOf_two_mem_center hU2 hZne
  have hcent : ∀ z ∈ involutions (H : Set G), ∀ y ∈ (U : Set G), z * y = y * z := by
    intro z hz y hy
    have hwInv : (w : G) ∈ involutions (H : Set G) := by
      refine ⟨hUH w.2, ?_⟩
      rw [← hw2]
      exact orderOf_injective _ (Subgroup.subtype_injective _) w
    obtain ⟨k, hk, hkwz⟩ := kapp_transitive hC4 hBP h (w : G) hwInv z hz
    have hkU : k ∈ Subgroup.normalizer (U : Set G) := le_trans hKleH hUn hk
    have hy' : k⁻¹ * y * k ∈ U := (Subgroup.mem_normalizer_iff''.mp hkU y).mp hy
    have hwy : (w : G) * (k⁻¹ * y * k) = (k⁻¹ * y * k) * (w : G) := by
      have h1 := (Subgroup.mem_center_iff.mp hwZ) (⟨k⁻¹ * y * k, hy'⟩ : ↥U)
      simpa using (congrArg (fun t : ↥U => (t : G)) h1).symm
    calc z * y = (k * (w : G) * k⁻¹) * y := by rw [hkwz]
      _ = k * ((w : G) * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * (w : G)) * k⁻¹ := by rw [hwy]
      _ = y * (k * (w : G) * k⁻¹) := by group
      _ = y * z := by rw [← hkwz]
  have hcomm : ∀ x ∈ (U : Set G), ∀ y ∈ (U : Set G), x * y = y * x := by
    intro x hx
    rw [hUdef] at hx
    refine Subgroup.closure_induction (p := fun a _ => ∀ y ∈ (U : Set G), a * y = y * a)
      ?_ ?_ ?_ ?_ hx
    · intro z hz y hy
      exact hcent z hz y hy
    · intro y _
      rw [one_mul, mul_one]
    · intro a b ha hb iha ihb y hy
      calc a * b * y = a * (b * y) := by group
        _ = a * (y * b) := by rw [ihb y hy]
        _ = a * y * b := by group
        _ = y * a * b := by rw [iha y hy]
        _ = y * (a * b) := by group
    · intro a ha iha y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [← iha y hy]
        _ = y * a⁻¹ := by group
  have hone : ∀ y : ↥U, y * y = 1 := by
    intro y
    have hy : (y : G) ∈ Subgroup.closure (involutions (H : Set G)) := by
      rw [← hUdef]; exact y.2
    have hmain : (y : G) * (y : G) = 1 := by
      refine Subgroup.closure_induction (p := fun a _ => a * a = 1) ?_ ?_ ?_ ?_ hy
      · intro z hz
        have hz2 : orderOf z = 2 := (Work.ThreePoints.mem_involutions.mp hz).2
        have h1 := pow_orderOf_eq_one z
        rw [hz2] at h1
        simpa [pow_two] using h1
      · exact one_mul 1
      · intro a b ha hb iha ihb
        have hab : a * b = b * a := hcomm a ha b hb
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [iha, ihb, mul_one]
      · intro a ha iha
        calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          _ = 1 := by rw [iha]; simp
    refine Subtype.ext ?_
    simpa using hmain
  have hUeq : (U : Set G) = insert 1 (involutions (H : Set G)) := by
    ext z
    constructor
    · intro hz
      by_cases h1 : z = 1
      · rw [h1]; exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ ?_
        rw [Work.ThreePoints.mem_involutions]
        refine ⟨hUH hz, ?_⟩
        have hzz : (⟨z, hz⟩ : ↥U) * ⟨z, hz⟩ = 1 := hone ⟨z, hz⟩
        have hzz' : z * z = 1 := by
          have h1' := congrArg (fun t : ↥U => (t : G)) hzz
          simpa using h1'
        have hdvd : orderOf z ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]
          exact hzz'
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · rw [orderOf_eq_one_iff] at h
          exact absurd h h1
        · exact h
    · intro hz
      rcases Set.mem_insert_iff.mp hz with h | h
      · rw [h]; exact U.one_mem
      · exact Subgroup.subset_closure h
  have h1notmem : (1 : G) ∉ involutions (H : Set G) := by
    intro h1
    have h2 := (Work.ThreePoints.mem_involutions.mp h1).2
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hcardU : Nat.card ↥U = (involutions (H : Set G)).ncard + 1 := by
    have h1 : (U : Set G).ncard = (involutions (H : Set G)).ncard + 1 := by
      rw [hUeq, Set.ncard_insert_of_notMem h1notmem]
    have h2 : Nat.card ↥U = (U : Set G).ncard :=
      (Set.ncard_univ ↥U).symm.trans (Set.ncard_coe (U : Set G))
    rw [h2, h1]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
  obtain ⟨a, ha1, hKa⟩ := setup5_Kset_card' h hp
  have hInv : (involutions (H : Set G)).ncard = r ^ (a + 1) := by
    rw [← Work.ThmF.Bender.cardKsetEqInv h.se h.invol h.notMem]
    exact hKa
  have hcontr : 2 ^ n = r ^ (a + 1) + 1 := by
    rw [← hn, hcardU, hInv]
  have hr2 : r ≠ 2 := by
    intro hr
    have hdvd : r ∣ 2 ^ p - 1 := h.r_dvd
    rcases hp with h' | h'
    · rw [h'] at hdvd; rw [hr] at hdvd; norm_num at hdvd
    · rw [h'] at hdvd; rw [hr] at hdvd; norm_num at hdvd
  exact (two_pow_ne_prime_pow_succ_add_one r a n h.r_prime hr2 ha1) hcontr

end Step1

/-! ## §4  Step 2: `W = ⟨Inv H⟩` -/

section Step2

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `E' ≤ D`. -/
theorem ecomm_le_D (h : Design.Setup5 G H t W p P A r) :
    Design.Ecomm H t W ≤ twoPoint H t := by
  have h1 : Design.Ecomm H t W ≤ Design.Egrp H t W := by
    simpa using Subgroup.commutator_le_sup (Design.Egrp H t W) (Design.Egrp H t W)
  exact le_trans h1 inf_le_right

/-- **Peterfalvi I Ch. III §5 Prop. 1, step 2.**  For `p ∈ {3,5}`, `W = ⟨Inv H⟩`. -/
theorem step2 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hBP : BenderPrelimProp)
    (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5)
    (hstep1 : Subgroup.closure (involutions (H : Set G)) ⊓ Design.Ecomm H t W ≠ ⊥) :
    W = Subgroup.closure (involutions (H : Set G)) := by
  classical
  haveI : Fact r.Prime := ⟨h.r_prime⟩
  set U : Subgroup G := Subgroup.closure (involutions (H : Set G)) with hUdef
  set X : Subgroup G := U ⊓ Design.Ecomm H t W with hXdef
  have hUH : U ≤ H := closure_involutions_le H
  have hUn : H ≤ Subgroup.normalizer (U : Set G) := normalizer_closure_involutions H
  have hE'H : Design.Ecomm H t W ≤ H := ecomm_le_H h
  have hE'D : Design.Ecomm H t W ≤ twoPoint H t := ecomm_le_D h
  have hDodd : Odd (Nat.card (twoPoint H t)) := h.se.2.2 t h.notMem
  have hXne : X ≠ ⊥ := by rw [hXdef]; exact hstep1
  have hXU : X ≤ U := inf_le_left
  have hXD : X ≤ twoPoint H t := le_trans inf_le_right hE'D
  have hXH : X ≤ H := le_trans hXU hUH
  have hXp : IsPGroup r ↥X := (ecomm_isPGroup h hp).to_le inf_le_right
  -- ## `E'` is `D`-invariant
  have hDnorm : ∀ d ∈ (twoPoint H t : Set G), ∀ x ∈ (twoPoint H t : Set G),
      d * x * d⁻¹ ∈ twoPoint H t := by
    intro d hd x hx
    exact ⟨H.mul_mem (H.mul_mem hd.1 hx.1) (H.inv_mem hd.1),
      (conj t H).mul_mem ((conj t H).mul_mem hd.2 hx.2) ((conj t H).inv_mem hd.2)⟩
  have hEgrp_d : ∀ d ∈ (twoPoint H t : Set G),
      (Design.Egrp H t W).map (MulAut.conj d).toMonoidHom = Design.Egrp H t W := by
    intro d hd
    show (W ⊓ twoPoint H t).map (MulAut.conj d).toMonoidHom = W ⊓ twoPoint H t
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      rw [show (MulAut.conj d).toMonoidHom y = d * y * d⁻¹ by simp [MulAut.conj_apply]]
      exact ⟨(Subgroup.le_normalizer_iff.mp h.normal) d hd.1 y hy.1, hDnorm d hd y hy.2⟩
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨d⁻¹ * x * d, ⟨?_, ?_⟩, ?_⟩
      · have h := (Subgroup.le_normalizer_iff.mp h.normal) d⁻¹ (H.inv_mem hd.1) x hx.1
        simpa using h
      · have h := hDnorm d⁻¹ ((twoPoint H t).inv_mem hd) x hx.2
        simpa using h
      · rw [show (MulAut.conj d).toMonoidHom (d⁻¹ * x * d) = d * (d⁻¹ * x * d) * d⁻¹ by
            simp [MulAut.conj_apply]]
        group
  have hE'Dn : twoPoint H t ≤ Subgroup.normalizer (Design.Ecomm H t W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd x hx
    have h1 : (MulAut.conj d).toMonoidHom x ∈
        (Design.Ecomm H t W).map (MulAut.conj d).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_commutator, hEgrp_d d hd] at h1
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have hXn : twoPoint H t ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd x hx
    rw [hXdef, Subgroup.mem_inf] at hx ⊢
    exact ⟨(Subgroup.le_normalizer_iff.mp hUn) d hd.1 x hx.1,
      (Subgroup.le_normalizer_iff.mp hE'Dn) d hd x hx.2⟩
  -- ## `X` is a Sylow `r`-subgroup of `U`
  have hE'U : Design.Ecomm H t W ≤ Subgroup.normalizer (U : Set G) := le_trans hE'H hUn
  have hXrel : X.relIndex U = (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) := by
    have h1 : (U ⊓ Design.Ecomm H t W).relIndex U =
        (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) :=
      Work.Transitivity.API.relIndex_inf_eq_relIndex_sup (fun z hz => by
        have hz' : z ∈ (↑(U ⊔ Design.Ecomm H t W) : Set G) := hz
        rw [Subgroup.coe_mul_of_right_le_normalizer_left U (Design.Ecomm H t W) hE'U] at hz'
        rw [Set.mem_mul] at hz'
        obtain ⟨c, hc, j, hj, rfl⟩ := hz'
        exact ⟨c, hc, j, hj, rfl⟩)
    rw [hXdef]
    exact h1
  have hXsyl : ¬ r ∣ X.relIndex U := by
    rw [hXrel]
    intro hdvd
    have hprod : (Design.Ecomm H t W).relIndex (U ⊔ Design.Ecomm H t W) *
        (U ⊔ Design.Ecomm H t W).relIndex H = (Design.Ecomm H t W).relIndex H :=
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hUH hE'H)
    exact ecomm_relIndex_not_dvd h hp (hprod ▸ dvd_mul_of_dvd_left hdvd _)
  -- ## the fixed-point dichotomy: `N_H(X) = D`
  have hpt : Work.DoubleTransitivity.pt H ∈ fixedPts H X :=
    (Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr (le_trans hXD inf_le_left)
  have htpt : ((t : G) : G ⧸ H) ∈ fixedPts H X :=
    (Work.DoubleTransitivity.mk_mem_fixedPts_iff X H t).mpr (le_trans hXD inf_le_right)
  have hpt_ne : Work.DoubleTransitivity.pt H ≠ ((t : G) : G ⧸ H) :=
    fun hh => h.notMem (Work.DoubleTransitivity.mk_one_eq_iff.mp hh.symm)
  have h2le : 2 ≤ (fixedPts H X).ncard := by
    have hsub : ({Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆
        fixedPts H X :=
      Set.insert_subset_iff.mpr ⟨hpt, Set.singleton_subset_iff.mpr htpt⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair hpt_ne] at hle
  have hNHD : H ⊓ Subgroup.normalizer (X : Set G) ≤ twoPoint H t := by
    by_contra hcon
    have h2not : (fixedPts H X).ncard ≠ 2 := by
      intro h2
      apply hcon
      intro n hn
      obtain ⟨hnH, hnN⟩ := Subgroup.mem_inf.mp hn
      have hfixeq : fixedPts H X = {Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)} := by
        refine (Set.eq_of_subset_of_ncard_le
          (Set.insert_subset_iff.mpr ⟨hpt, Set.singleton_subset_iff.mpr htpt⟩) ?_).symm
        rw [h2, Set.ncard_pair hpt_ne]
      have hmem : n • ((t : G) : G ⧸ H) ∈ fixedPts H X :=
        normalizer_smul_mem_fixedPts htpt hnN
      rw [hfixeq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hmem | hmem
      · exfalso
        have hfixpt : n • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := by
          refine MulAction.mem_stabilizer_iff.mp ?_
          rw [Work.ThreePoints.stabilizer_mk H 1, Work.DoubleTransitivity.conj_one]
          exact hnH
        have h2' : n • ((t : G) : G ⧸ H) = n • Work.DoubleTransitivity.pt H := by rw [hmem, hfixpt]
        have h3' := congrArg (fun ω : G ⧸ H => n⁻¹ • ω) h2'
        have h4 : ((t : G) : G ⧸ H) = Work.DoubleTransitivity.pt H := by
          simpa [smul_smul] using h3'
        exact h.notMem (Work.DoubleTransitivity.mk_one_eq_iff.mp h4)
      · rw [Subgroup.mem_inf]
        exact ⟨hnH, by
          rw [← Work.ThreePoints.stabilizer_mk H t]
          exact MulAction.mem_stabilizer_iff.mpr hmem⟩
    have h3 : 3 ≤ (fixedPts H X).ncard := by
      by_contra hlt
      push_neg at hlt
      exact h2not (le_antisymm (Nat.lt_succ_iff.mp hlt) h2le)
    -- `X` has ≥ 3 fixed points: `X^d ≤ V` for some `d ∈ D`
    obtain ⟨d, hdD, hdX⟩ :=
      prop2b_conj_into_centD G h.sit hBP hC4 h.se h.invol h.notMem hXD h3
    have hXmap : X.map (MulAut.conj d).toMonoidHom = X := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro x ⟨y, hy, rfl⟩
        rw [show (MulAut.conj d).toMonoidHom y = d * y * d⁻¹ by simp [MulAut.conj_apply]]
        exact (Subgroup.le_normalizer_iff.mp hXn) d hdD y hy
      · rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]
    have hXV : X ≤ centD H t := by
      rw [← hXmap]; exact hdX
    -- P3 with `X`
    have hKleD : Kgrp (twoPoint H t) t ≤ twoPoint H t :=
      (Subgroup.closure_le (twoPoint H t)).mpr fun _ hx => hx.1
    have hKsub : Kset (twoPoint H t) t ⊆ Subgroup.normalizer (X : Set G) :=
      fun y hy => hXn (hKleD (Subgroup.subset_closure hy))
    obtain ⟨k₀, hk₀K, hk₀ne, hk₀N⟩ :
        ∃ k ∈ Kset (twoPoint H t) t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := by
      obtain ⟨a, ha1, hKa⟩ := setup5_Kset_card' h hp
      have h2 : 2 ≤ (Kset (twoPoint H t) t).ncard := by
        rw [hKa]
        calc 2 ≤ r := h.r_prime.two_le
          _ = r ^ 1 := (pow_one r).symm
          _ ≤ r ^ (a + 1) := Nat.pow_le_pow_right h.r_prime.pos (by omega)
      by_contra hcon2
      push_neg at hcon2
      have hsub : Kset (twoPoint H t) t ⊆ ({1} : Set G) := by
        intro y hy
        rw [Set.mem_singleton_iff]
        by_contra hy1
        exact hcon2 y hy hy1 (hKsub hy)
      have hcontra : (Kset (twoPoint H t) t).ncard ≤ 1 := by
        have h := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
        rwa [Set.ncard_singleton] at h
      omega
    obtain ⟨-, -, -, hN⟩ :=
      (hC4 G h.sit H h.se t h.invol h.notMem).2.2.2.1 X hXne hXV ⟨k₀, hk₀K, hk₀ne, hk₀N⟩
    obtain ⟨N', hN'eq, hN'C, -⟩ := hN
    have hXcent : X ≤ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) := by
      rw [← Subgroup.centralizer_closure, Subgroup.le_centralizer_iff]
      refine le_trans ?_ hN'C
      refine (Subgroup.closure_le N').mpr ?_
      intro y hy
      rw [hN'eq]
      exact ⟨hy, hKsub hy⟩
    have hXbot : X ≤ ⊥ := by
      have h1 : X ≤ centD H t ⊓ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) :=
        le_inf hXV hXcent
      rw [h.d2.2.1] at h1
      exact h1
    exact hXne (le_bot_iff.mp hXbot)
  have hNHD' : H ⊓ Subgroup.normalizer (X : Set G) = twoPoint H t :=
    le_antisymm hNHD (le_inf inf_le_left hXn)
  -- ## Frattini: `H ≤ U ⊔ N_H(X)`
  have hnormalU : (U.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn
  let hequi : ↥(U.subgroupOf H) ≃* ↥U :=
    { toFun := fun w => ⟨(w.1 : G), Subgroup.mem_subgroupOf.mp w.2⟩
      invFun := fun u => ⟨⟨(u.1 : G), hUH u.2⟩, Subgroup.mem_subgroupOf.mpr u.2⟩
      left_inv := fun w => Subtype.ext (Subtype.ext rfl)
      right_inv := fun u => Subtype.ext rfl
      map_mul' := fun w w' => Subtype.ext rfl }
  have hXUsub : IsPGroup r ↥(X.subgroupOf U) := by
    have h1 := hXp.comap_of_injective U.subtype U.subtype_injective
    rwa [show Subgroup.comap U.subtype X = X.subgroupOf U from rfl] at h1
  have hXsylU : ¬ r ∣ (X.subgroupOf U).index := hXsyl
  have hP2 : IsPGroup r ↥((X.subgroupOf U).comap hequi.toMonoidHom) :=
    hXUsub.comap_of_injective hequi.toMonoidHom hequi.injective
  have hidx2 : ¬ r ∣ ((X.subgroupOf U).comap hequi.toMonoidHom).index := by
    rw [Subgroup.index_comap_of_surjective _ hequi.surjective]
    exact hXsylU
  let Pxy : Sylow r ↥(U.subgroupOf H) := hP2.toSylow hidx2
  have hPxycoe : (Pxy : Subgroup ↥(U.subgroupOf H)).map (U.subgroupOf H).subtype = X.subgroupOf H := by
    have h1 : (Pxy : Subgroup ↥(U.subgroupOf H)) =
        (X.subgroupOf U).comap hequi.toMonoidHom := hP2.toSylow_coe hidx2
    rw [h1]
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      rw [Subgroup.mem_comap] at hw
      rw [Subgroup.mem_subgroupOf]
      rw [← hwz]
      show ((w : ↥(U.subgroupOf H)) : G) ∈ X
      exact Subgroup.mem_subgroupOf.mp hw
    · intro hz
      have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
      refine Subgroup.mem_map.mpr ⟨⟨z, Subgroup.mem_subgroupOf.mpr (hXU hzX)⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_subgroupOf.mpr hzX
  have hfr := Work.GlaubermanZJ.frattini_sylow (G := ↥H) (H := U.subgroupOf H) (p := r) Pxy
  have hfr' : (⊤ : Subgroup ↥H) = U.subgroupOf H ⊔ Subgroup.normalizer (X.subgroupOf H) := by
    rw [hPxycoe] at hfr
    exact hfr
  -- the normalizer of `X.subgroupOf H` maps to `H ⊓ N_G(X)`
  have hnormmap : (Subgroup.normalizer (X.subgroupOf H)).map H.subtype =
      H ⊓ Subgroup.normalizer (X : Set G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxH : x ∈ H := hXH hx
        have hx' : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
        have h2 : g * (⟨x, hxH⟩ : ↥H) * g⁻¹ ∈ X.subgroupOf H :=
          (Subgroup.mem_normalizer_iff.mp hg) (⟨x, hxH⟩ : ↥H) |>.mp hx'
        have h3 := Subgroup.mem_subgroupOf.mp h2
        simpa using h3
      · intro hx
        have hxH : x ∈ H := by
          have h4 : g * x * g⁻¹ ∈ H := hXH hx
          have h5 : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) ∈ H :=
            H.mul_mem (H.mul_mem (H.inv_mem g.2) h4) g.2
          rwa [show (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) = x from by group] at h5
        have hx' : g * (⟨x, hxH⟩ : ↥H) * g⁻¹ ∈ X.subgroupOf H := by
          refine Subgroup.mem_subgroupOf.mpr ?_
          simpa using hx
        have h2 : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H :=
          (Subgroup.mem_normalizer_iff.mp hg) (⟨x, hxH⟩ : ↥H) |>.mpr hx'
        exact Subgroup.mem_subgroupOf.mp h2
    · intro hy
      obtain ⟨hyH, hyN⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
        refine Subgroup.mem_subgroupOf.mpr ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp hyN) (z : G)
        simpa using (h1.mp hzX)
      · intro hz
        have hzX : ((⟨y, hyH⟩ : ↥H) * z * (⟨y, hyH⟩ : ↥H)⁻¹ : G) ∈ X :=
          Subgroup.mem_subgroupOf.mp hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hyN) (z : G)
        exact Subgroup.mem_subgroupOf.mpr (h1.mpr (by simpa using hzX))
  have hmap := congrArg (Subgroup.map H.subtype) hfr'
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hUH, hnormmap] at hmap
  have hFratt : H ≤ U ⊔ (H ⊓ Subgroup.normalizer (X : Set G)) := hmap.le
  -- ## conclusion
  have hHUD : U ⊔ twoPoint H t = H :=
    le_antisymm (sup_le hUH inf_le_left) (le_trans hFratt (sup_le_sup_left hNHD U))
  have hWle : Nat.card ↥W ≤ Nat.card ↥U := h.minW.2.2.2 U hUH hUn hHUD
  have hUW : U ≤ W := by
    rw [hUdef]
    exact (Subgroup.closure_le W).mpr (involutions_subset_of_sup_eq h.le h.sup inf_le_left h.normal hDodd)
  have hUelemW : Nat.card ↥U ≤ Nat.card ↥W := Subgroup.card_le_of_le hUW
  exact (Subgroup.eq_of_le_of_card_ge hUW (by omega)).symm

end Step2

section Final

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `E' ≤ W`. -/
theorem ecomm_le_W (h : Design.Setup5 G H t W p P A r) : Design.Ecomm H t W ≤ W := by
  have h1 : Design.Ecomm H t W ≤ Design.Egrp H t W := by
    simpa using Subgroup.commutator_le_sup (Design.Egrp H t W) (Design.Egrp H t W)
  exact le_trans h1 inf_le_left

/-- **Peterfalvi I Ch. III §5 Prop. 1, final step.**  With `W = ⟨Inv H⟩`, Burnside's class theorem
and a four-group in `W` give a contradiction. -/
theorem final_contra (hBC : Design.BurnsideClassProp) (hC4 : ChIIFourProp)
    (hBP : BenderPrelimProp) (h : Design.Setup5 G H t W p P A r) (hp : p = 3 ∨ p = 5)
    (hWU : W = Subgroup.closure (involutions (H : Set G))) : False := by
  classical
  have hDodd : Odd (Nat.card (twoPoint H t)) := h.se.2.2 t h.notMem
  have hInvW : involutions (H : Set G) ⊆ (W : Set G) :=
    involutions_subset_of_sup_eq h.le h.sup inf_le_left h.normal hDodd
  have hKW : Kgrp (twoPoint H t) t ≤ W :=
    le_trans (by rw [h.E'_eq]; exact le_sup_left) (ecomm_le_W h)
  obtain ⟨a, ha1, hKa⟩ := setup5_Kset_card' h hp
  have hInvcard : (involutions (H : Set G)).ncard = r ^ (a + 1) := by
    rw [← Work.ThmF.Bender.cardKsetEqInv h.se h.invol h.notMem]
    exact hKa
  obtain ⟨u, hu, -⟩ := (hC4 G h.sit H h.se t h.invol h.notMem).2.1
  have huW : u ∈ W := hInvW hu
  have hu2 : orderOf u = 2 := (Work.ThreePoints.mem_involutions.mp hu).2
  set x : ↥W := ⟨u, huW⟩ with hxdef
  have hx2 : orderOf x = 2 :=
    (orderOf_injective W.subtype W.subtype_injective x).symm.trans hu2
  have hxx : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rw [hx2] at h1
    simpa [pow_two] using h1
  have horbit : ∀ v ∈ involutions (H : Set G), ∃ g : ↥W, (g : G) * u * (g : G)⁻¹ = v := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := kapp_transitive hC4 hBP h u hu v hv
    exact ⟨⟨k, hKW hk⟩, hkv⟩
  have hcarrier : ∀ y : ↥W, y ∈ (ConjClasses.mk x).carrier ↔
      (y : G) ∈ involutions (H : Set G) := by
    intro y
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hcG : (c : G) * (y : G) * (c : G)⁻¹ = u := by
        have h1 := congrArg (fun z : ↥W => (z : G)) hc
        simpa [hxdef] using h1
      refine ⟨?_, ?_⟩
      · have hy : (y : G) = (c : G)⁻¹ * u * (c : G) := by rw [← hcG]; group
        rw [hy]
        exact H.mul_mem (H.mul_mem (H.inv_mem (h.le c.2)) (h.le huW)) (h.le c.2)
      · rw [← MulEquiv.orderOf_eq (MulAut.conj (c : G)) (y : G), MulAut.conj_apply, hcG]
        exact hu2
    · intro hy
      obtain ⟨k, hk, hkv⟩ := kapp_transitive hC4 hBP h u hu y hy
      refine ⟨(⟨k, hKW hk⟩ : ↥W)⁻¹, ?_⟩
      apply Subtype.ext
      change (k : G)⁻¹ * (y : G) * ((k : G)⁻¹)⁻¹ = u
      rw [inv_inv, ← hkv]
      group
  have hclass : Nat.card (ConjClasses.mk x).carrier = r ^ (a + 1) := by
    have hcard0 : ((ConjClasses.mk x).carrier : Set ↥W).ncard =
        (involutions (H : Set G)).ncard :=
      Set.ncard_congr (fun y _ => (y : G))
        (fun y hy => (hcarrier y).mp hy)
        (fun y z hy hz h => Subtype.ext h)
        (fun v hv => ⟨⟨v, hInvW hv⟩, (hcarrier _).mpr hv, rfl⟩)
    have hcard1 : Nat.card (ConjClasses.mk x).carrier =
        ((ConjClasses.mk x).carrier : Set ↥W).ncard :=
      (Set.ncard_univ ↥(ConjClasses.mk x).carrier).symm.trans
        (Set.ncard_coe ((ConjClasses.mk x).carrier : Set ↥W))
    exact hcard1.trans (hcard0.trans hInvcard)
  obtain ⟨N, hNnorm, hNne, hNcent⟩ := hBC ↥W x r (a + 1) h.r_prime (by omega) hclass
  set N' : Subgroup G := N.map W.subtype with hN'def
  have hN'le : N' ≤ W := Subgroup.map_subtype_le N
  have hN'ne : N' ≠ W := by
    intro hN'W
    refine hNne ?_
    have h1 : N = Subgroup.comap W.subtype N' := by
      rw [hN'def]
      exact (Subgroup.comap_map_eq_self (f := W.subtype) (H := N) (by simp)).symm
    have h2 : Subgroup.comap W.subtype (W : Subgroup G) = ⊤ := by
      have h3 := Subgroup.comap_map_eq_self (f := W.subtype) (H := (⊤ : Subgroup ↥W)) (by simp)
      rw [Subgroup.map_top, Subgroup.range_subtype] at h3
      exact h3
    rw [hN'W, h2] at h1
    exact h1
  have hN'conj : ∀ w ∈ (W : Set G), ∀ x ∈ (N' : Set G), w * x * w⁻¹ ∈ N' := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨w, hw⟩ * y * ⟨w, hw⟩⁻¹, hNnorm.conj_mem y hy ⟨w, hw⟩, ?_⟩
    simp
  have huN' : u ∉ N' := by
    intro hux
    have hsub : involutions (H : Set G) ⊆ (N' : Set G) := by
      intro v hv
      obtain ⟨g, hg⟩ := horbit v hv
      rw [← hg]
      exact hN'conj g g.2 u hux
    have hUN' : Subgroup.closure (involutions (H : Set G)) ≤ N' :=
      (Subgroup.closure_le N').mpr hsub
    rw [← hWU] at hUN'
    exact hN'ne (le_antisymm hN'le hUN')
  obtain ⟨A, B, hA2, hB2, hABne, hABcomm⟩ :=
    hasFourGroup_subgroupOf h.se h.sit.1.1 h.le h.sup inf_le_left h.normal hDodd
  have hA1 : A * A = 1 := by
    have h1 := pow_orderOf_eq_one A
    rw [hA2] at h1
    simpa [pow_two] using h1
  have hB1 : B * B = 1 := by
    have h1 := pow_orderOf_eq_one B
    rw [hB2] at h1
    simpa [pow_two] using h1
  have hAΩ : (A : G) ∈ involutions (H : Set G) :=
    ⟨h.le A.2, (orderOf_injective W.subtype W.subtype_injective A).trans hA2⟩
  have hBΩ : (B : G) ∈ involutions (H : Set G) :=
    ⟨h.le B.2, (orderOf_injective W.subtype W.subtype_injective B).trans hB2⟩
  obtain ⟨gA, hgA⟩ := horbit (A : G) hAΩ
  obtain ⟨gB, hgB⟩ := horbit (B : G) hBΩ
  have hα : gA * x * gA⁻¹ * x⁻¹ ∈ N := by
    have h1 := N.inv_mem (hNcent gA)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h1
  have hβ : gB * x * gB⁻¹ * x⁻¹ ∈ N := by
    have h1 := N.inv_mem (hNcent gB)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h1
  have hAeq : A = (gA * x * gA⁻¹ * x⁻¹) * x := by
    apply Subtype.ext
    change (A : G) = ((gA : G) * u * (gA : G)⁻¹ * u⁻¹) * u
    rw [← hgA]
    group
  have hBeq : B = (gB * x * gB⁻¹ * x⁻¹) * x := by
    apply Subtype.ext
    change (B : G) = ((gB : G) * u * (gB : G)⁻¹ * u⁻¹) * u
    rw [← hgB]
    group
  have hABeq : A * B = (gA * x * gA⁻¹ * x⁻¹) *
      (x * (gB * x * gB⁻¹ * x⁻¹) * x⁻¹) := by
    rw [hAeq, hBeq]
    calc (gA * x * gA⁻¹ * x⁻¹) * x * ((gB * x * gB⁻¹ * x⁻¹) * x)
        = (gA * x * gA⁻¹ * x⁻¹) * (x * (gB * x * gB⁻¹ * x⁻¹) * x⁻¹) * (x * x) := by
          group
      _ = (gA * x * gA⁻¹ * x⁻¹) * (x * (gB * x * gB⁻¹ * x⁻¹) * x⁻¹) := by
          rw [hxx, mul_one]
  have hABN : A * B ∈ N := by
    rw [hABeq]
    exact N.mul_mem hα (hNnorm.conj_mem (gB * x * gB⁻¹ * x⁻¹) hβ x)
  have hABs : (A * B) * (A * B) = 1 := by
    calc (A * B) * (A * B) = A * (B * A) * B := by group
      _ = A * (A * B) * B := by rw [hABcomm]
      _ = (A * A) * (B * B) := by group
      _ = 1 := by rw [hA1, hB1, mul_one]
  have hABne1 : (A * B : ↥W) ≠ 1 := by
    intro h1
    apply hABne
    have hB : B = A⁻¹ := by
      have h2 := congrArg (fun z : ↥W => A⁻¹ * z) h1
      rw [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h2
      exact h2
    have hAinv : A⁻¹ = A := mul_eq_one_iff_inv_eq.mp hA1
    rw [hAinv] at hB
    exact hB.symm
  have hab2 : orderOf (A * B) = 2 := by
    have hsq : (A * B) ^ 2 = 1 := by simpa [pow_two] using hABs
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hsq) with hh | hh
    · exact absurd (orderOf_eq_one_iff.mp hh) hABne1
    · exact hh
  have hABΩ : (A : G) * (B : G) ∈ involutions (H : Set G) := by
    refine ⟨h.le (W.mul_mem A.2 B.2), ?_⟩
    rw [← Subgroup.coe_mul]
    exact (orderOf_injective W.subtype W.subtype_injective (A * B)).trans hab2
  obtain ⟨g, hg⟩ := horbit ((A : G) * (B : G)) hABΩ
  have hABN' : (A : G) * (B : G) ∈ N' :=
    Subgroup.mem_map.mpr ⟨A * B, hABN, by simp⟩
  have h1 := hN'conj ((g : G)⁻¹) (W.inv_mem g.2) ((A : G) * (B : G)) hABN'
  have h3 : (g : G)⁻¹ * ((A : G) * (B : G)) * ((g : G)⁻¹)⁻¹ = u := by
    rw [← hg]
    group
  rw [h3] at h1
  exact huN' h1

end Final

/-- **Peterfalvi I Ch. III §5 Proposition 1** (p.182): `p ≥ 7`. -/
theorem sec5_prop1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hBP : Work.NormalComplement.BenderPrelimProp)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) : 7 ≤ p := by
  by_contra hlt
  push_neg at hlt
  have hp2 : p = 2 ∨ p = 3 ∨ p = 5 := by
    have h2b : 2 ≤ p := h.prime.two_le
    have hp := h.prime
    interval_cases p
    · left; rfl
    · right; left; rfl
    · exfalso; norm_num at hp
    · right; right; rfl
    · exfalso; norm_num at hp
  rcases hp2 with h2 | h35
  · exfalso
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
    have hdvd : 2 ∣ Nat.card ↥(twoPoint H t) := by
      rw [← h2]
      exact dvd_trans h.dvd (dvd_trans (Subgroup.relIndex_dvd_card _ _)
        (Subgroup.card_dvd_of_le inf_le_right))
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)
  · exact (final_contra hBC hC4 hBP h h35
      (step2 hFT hC4 hBP h h35 (step1 hFT hC4 hBP h h35))).elim

end Work.NormalComplement
