import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers
import Submission.Work.NormalComplement.appI_two
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.NormalComplement.sec5_clause_c
import Submission.Work.NormalComplement.sec5_clause_d
import Submission.Work.NormalComplement.sec5_prereq_f
import Submission.Work.NormalComplement.sec5_prereq_l1

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

namespace Work.NormalComplement

/-! ## Elementary consequences of `Setup5`, and the arithmetic of `f ∈ {3,5}` -/

section Basic

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `D = twoPoint H t = H ⊓ H^t` has odd order. -/
lemma setup5_twoPoint_odd (h : Design.Setup5 G H t W p P A r) :
    Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem

/-- `E = Egrp H t W = W ⊓ D` has odd order. -/
lemma setup5_Egrp_odd (h : Design.Setup5 G H t W p P A r) :
    Odd (Nat.card ↥(Design.Egrp H t W)) :=
  Odd.of_dvd_nat (setup5_twoPoint_odd h) (Subgroup.card_dvd_of_le inf_le_right)

/-- `p ≠ 2`: `p ∣ |E : E'|` divides `|E|`, which divides the odd number `|D|`. -/
lemma setup5_p_ne_two (h : Design.Setup5 G H t W p P A r) : p ≠ 2 := by
  intro hp
  have hdvd : p ∣ Nat.card ↥(Design.Egrp H t W) :=
    h.dvd.trans (Subgroup.relIndex_dvd_card _ _)
  have h2 : 2 ∣ Nat.card ↥(Design.Egrp H t W) := hp ▸ hdvd
  exact (Nat.not_even_iff_odd.mpr (setup5_Egrp_odd h)) (even_iff_two_dvd.mpr h2)

/-- `p` is odd. -/
lemma setup5_odd_p (h : Design.Setup5 G H t W p P A r) : Odd p :=
  h.prime.odd_of_ne_two (setup5_p_ne_two h)

/-- `3 ∤ 2^p - 1` for odd `p`. -/
lemma three_not_dvd_two_pow_sub_one {p : ℕ} (hp : Odd p) : ¬ 3 ∣ 2 ^ p - 1 := by
  intro hd
  have hle : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hzero : ((2 ^ p - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hone : (2 : ZMod 3) ^ p = 1 := by
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at hzero
    exact hzero
  have hdvd : orderOf (2 : ZMod 3) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hone
  have hord : orderOf (2 : ZMod 3) = 2 := by
    have hd2 : orderOf (2 : ZMod 3) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by decide)
    have hne1 : orderOf (2 : ZMod 3) ≠ 1 := by
      intro h1
      exact (by decide : (2 : ZMod 3) ≠ 1) (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact absurd h hne1
    · exact h
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hp) (even_iff_two_dvd.mpr hdvd)

/-- `5 ∤ 2^p - 1` for odd `p`. -/
lemma five_not_dvd_two_pow_sub_one {p : ℕ} (hp : Odd p) : ¬ 5 ∣ 2 ^ p - 1 := by
  intro hd
  have hle : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hzero : ((2 ^ p - 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hone : (2 : ZMod 5) ^ p = 1 := by
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero] at hzero
    exact hzero
  have hdvd : orderOf (2 : ZMod 5) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hone
  have hord : orderOf (2 : ZMod 5) = 4 := by
    have hd4 : orderOf (2 : ZMod 5) ∣ 4 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by decide)
    have hne1 : orderOf (2 : ZMod 5) ≠ 1 := by
      intro h1
      exact (by decide : (2 : ZMod 5) ≠ 1) (orderOf_eq_one_iff.mp h1)
    have hne2 : orderOf (2 : ZMod 5) ≠ 2 := by
      intro h1
      have h2pow : (2 : ZMod 5) ^ 2 = 1 := by rw [← h1, pow_orderOf_eq_one]
      exact (by decide : (2 : ZMod 5) ^ 2 ≠ 1) h2pow
    have hle4 : orderOf (2 : ZMod 5) ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    interval_cases orderOf (2 : ZMod 5) <;> simp_all
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hp) (even_iff_two_dvd.mpr (dvd_trans (by norm_num) hdvd))

/-- If `f ∈ {3,5}` then `f ∤ 2^p - 1` for odd `p`. -/
lemma f_not_dvd_two_pow_sub_one {p f : ℕ} (hp : Odd p) (hf : f = 3 ∨ f = 5) :
    ¬ f ∣ 2 ^ p - 1 := by
  rcases hf with rfl | rfl
  · exact three_not_dvd_two_pow_sub_one hp
  · exact five_not_dvd_two_pow_sub_one hp

end Basic

/-! ## Conjugates of a strongly embedded subgroup -/

section ConjInfra

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G}

/-- `N_G(H) = H` for a strongly embedded subgroup `H`. -/
lemma normalizer_eq_self_of_stronglyEmbedded (hH : IsStronglyEmbedded H) :
    Subgroup.normalizer (H : Set G) = H := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro g hg
  by_contra hgH
  have hconj : conj g H = H :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g H).mpr hg
  have hodd : Odd (Nat.card ↥(H ⊓ conj g H)) := hH.2.2 g hgH
  rw [hconj, inf_idem] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hH.2.1

/-- Two distinct conjugates of a strongly embedded subgroup meet in odd order. -/
lemma odd_card_inf_conj_of_ne (hH : IsStronglyEmbedded H) {g₁ g₂ : G}
    (hne : conj g₁ H ≠ conj g₂ H) : Odd (Nat.card ↥(conj g₁ H ⊓ conj g₂ H)) := by
  have h0 : conj g₂ H = conj g₁ (conj (g₁⁻¹ * g₂) H) := by
    rw [← Work.DoubleTransitivity.conj_mul]
    congr 1
    group
  have hker : g₁⁻¹ * g₂ ∉ H := by
    intro hk
    apply hne
    have h2 : conj (g₁⁻¹ * g₂) H = H :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer _ H).mpr
        (by rw [normalizer_eq_self_of_stronglyEmbedded hH]; exact hk)
    rw [h0, h2]
  rw [h0, ← Subgroup.map_inf H (conj (g₁⁻¹ * g₂) H) (MulAut.conj g₁).toMonoidHom
    (MulAut.conj g₁).injective, Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
  exact hH.2.2 (g₁⁻¹ * g₂) hker

/-- Conjugation invariance of the number of fixed points of a cyclic subgroup. -/
lemma ncard_fixedPts_zpowers_conj (g x : G) :
    (fixedPts H (Subgroup.zpowers (MulAut.conj g x))).ncard
      = (fixedPts H (Subgroup.zpowers x)).ncard := by
  rw [← Work.DoubleTransitivity.conj_zpowers g x]
  exact Work.DoubleTransitivity.Sec4.ncard_fixedPts_conj H g (Subgroup.zpowers x)

/-- A point fixed by `⟨x⟩` is `mk g` for some `g` whose conjugate fixes it and contains `x`. -/
lemma exists_conj_of_mem_fixedPts' {x : G} {ω : G ⧸ H}
    (hω : ω ∈ fixedPts H (Subgroup.zpowers x)) :
    ∃ g : G, ω = QuotientGroup.mk g ∧ x ∈ conj g H := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ω
  have hω' : (QuotientGroup.mk g : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers x) := by
    rw [hg]; exact hω
  exact ⟨g, hg.symm,
    (Work.DoubleTransitivity.mk_mem_fixedPts_iff (Subgroup.zpowers x) H g).mp hω'
      (Subgroup.mem_zpowers x)⟩

/-- A point fixed by `⟨x⟩` has a stabiliser conjugate containing `x`. -/
lemma exists_conj_of_mem_fixedPts {x : G} {ω : G ⧸ H}
    (hω : ω ∈ fixedPts H (Subgroup.zpowers x)) : ∃ g : G, x ∈ conj g H := by
  obtain ⟨g, -, hg⟩ := exists_conj_of_mem_fixedPts' (H := H) hω
  exact ⟨g, hg⟩

/-- `orderOf` is invariant under conjugation. -/
lemma orderOf_conj_eq (g x : G) : orderOf (MulAut.conj g x) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd (MulAut.conj g).toMonoidHom x) ?_
  have h := orderOf_map_dvd (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g x)
  have hx : (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g x) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at h
  exact h

end ConjInfra

/-! ## §5 Prop. 2 (b), step 1: `ut` fixes no point of `Ω` -/

section OmegaUt

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `orderOf (u*t)` is prime when it is `3` or `5`. -/
lemma prime_orderOf_mul_of (u t : G)
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) : (orderOf (u * t)).Prime := by
  rcases hf with h | h <;> rw [h] <;> norm_num

/-- **Ch. I §6 Cor. 1 route**: if `u*t` lies in a conjugate of `H` not containing `t`, then
`orderOf (u*t)` divides `2^p - 1`. -/
lemma orderOf_mul_dvd_two_pow_sub_one (hCor1 : Design.ChISixCor1Prop)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧ u ∈ Subgroup.centralizer (centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) {g : G}
    (hut : u * t ∈ conj g H) (htn : t ∉ conj g H) :
    orderOf (u * t) ∣ 2 ^ p - 1 := by
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u
    rw [hu.2.1] at hh
    simpa [pow_two] using hh
  have hconv : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
    calc t * (u * t) * t = (t * u) * (t * t) := by group
      _ = t * u := by rw [ht2, mul_one]
  obtain ⟨y, hy⟩ :=
    hCor1 G h.sit H h.se t h.invol h.notMem g (u * t) hut htn hconv
  have hzorder : orderOf (y * (u * t) * y⁻¹) = orderOf (u * t) := by
    rw [show y * (u * t) * y⁻¹ = MulAut.conj y (u * t) from by rw [MulAut.conj_apply],
      orderOf_conj_eq]
  have hdvdK : orderOf (u * t) ∣ Nat.card ↥(Kgrp (twoPoint H t) t) := by
    have h1 := Subgroup.orderOf_dvd_natCard (Kgrp (twoPoint H t) t)
      (Subgroup.subset_closure hy)
    rwa [hzorder] at h1
  have hdvdE : orderOf (u * t) ∣ Nat.card ↥(Design.Ecomm H t W) :=
    hdvdK.trans (Subgroup.card_dvd_of_le (by rw [h.E'_eq]; exact le_sup_left))
  have hfK : orderOf (u * t) ∣ (Kset (twoPoint H t) t).ncard :=
    (h.E'_primes _ (prime_orderOf_mul_of u t hf)).mp hdvdE
  obtain ⟨a, ha1, haeq⟩ := h.K_card
  rw [haeq] at hfK
  rcases (Nat.Prime.dvd_mul (prime_orderOf_mul_of u t hf)).mp hfK with hfr | hf2
  · -- `f ∣ r^a`, so `f = r`, and `r ∣ 2^p - 1`
    have hfr' : orderOf (u * t) = r :=
      (Nat.prime_dvd_prime_iff_eq (prime_orderOf_mul_of u t hf) h.r_prime).mp
        ((prime_orderOf_mul_of u t hf).dvd_of_dvd_pow hfr)
    rw [hfr']
    exact h.r_dvd
  · exact hf2

/-- **§5 Prop. 2 (b), first assertion**: `ut` fixes no point of `Ω = G ⧸ H`. -/
lemma fixedPts_mul_eq_empty (hCor1 : Design.ChISixCor1Prop)
    (h : Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧ u ∈ Subgroup.centralizer (centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) :
    fixedPts H (Subgroup.zpowers (u * t)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω hω
  obtain ⟨g, hut⟩ := exists_conj_of_mem_fixedPts hω
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  have htn : t ∉ conj g H := by
    intro ht
    have huconj : u ∈ conj g H := by
      have hmem := (conj g H).mul_mem hut ((conj g H).inv_mem ht)
      have heq : u = (u * t) * t⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right ht2, mul_assoc, ht2, mul_one]
      rwa [← heq] at hmem
    have hEq : conj g H = H := by
      by_contra hne
      have hne' : conj g H ≠ conj (1 : G) H := by
        rwa [Work.DoubleTransitivity.conj_one]
      have hodd := odd_card_inf_conj_of_ne h.se hne'
      rw [Work.DoubleTransitivity.conj_one] at hodd
      have h2dvd : 2 ∣ Nat.card ↥(conj g H ⊓ H) := by
        have h1 := Subgroup.orderOf_dvd_natCard (conj g H ⊓ H) ⟨huconj, hu.1⟩
        rwa [hu.2.1] at h1
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
    rw [hEq] at hut
    have htmem : t ∈ H := by
      have hu2 : u * u = 1 := by
        have hh := pow_orderOf_eq_one u
        rw [hu.2.1] at hh
        simpa [pow_two] using hh
      have hh := H.mul_mem (H.inv_mem hu.1) hut
      have heq : u⁻¹ * (u * t) = t := by
        rw [inv_eq_of_mul_eq_one_right hu2, ← mul_assoc, hu2, one_mul]
      rwa [heq] at hh
    exact h.notMem htmem
  exact f_not_dvd_two_pow_sub_one (setup5_odd_p h) hf
    (orderOf_mul_dvd_two_pow_sub_one hCor1 h u hu hf hut htn)

end OmegaUt

/-! ## §5 Prop. 2 (b), step 2: elements of `M#` fix at most two points -/

section MsetBound

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- **§5 Prop. 2 (b)**: an element of `M#` fixes at most two points of `Ω`. -/
lemma ncard_fixedPts_le_two_of_mem_Mset (hCor1 : Design.ChISixCor1Prop)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) {u x : G}
    (hx : x ∈ Design.Mset u t) (hx1 : x ≠ 1) :
    (fixedPts H (Subgroup.zpowers x)).ncard ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  have hfin : (fixedPts H (Subgroup.zpowers x)).Finite := Set.toFinite _
  obtain ⟨ω₁, hω₁⟩ := (Set.ncard_pos hfin).mp (by omega)
  obtain ⟨ω₂, hω₂, hne₁₂⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := fixedPts H (Subgroup.zpowers x)) (by omega) ω₁
  obtain ⟨g₁, hg₁, hx₁⟩ := exists_conj_of_mem_fixedPts' (H := H) hω₁
  obtain ⟨g₂, hg₂, hx₂⟩ := exists_conj_of_mem_fixedPts' (H := H) hω₂
  have hneconj : conj g₁ H ≠ conj g₂ H := by
    intro heqc
    apply hne₁₂.symm
    have hk : conj (g₁⁻¹ * g₂) H = H := by
      have h2 : conj g₁ (conj (g₁⁻¹ * g₂) H) = conj g₁ H := by
        rw [← Work.DoubleTransitivity.conj_mul,
          show g₁ * (g₁⁻¹ * g₂) = g₂ from by group]
        exact heqc.symm
      exact Work.DoubleTransitivity.conj_injective g₁ h2
    have hkH : g₁⁻¹ * g₂ ∈ H := by
      rw [← normalizer_eq_self_of_stronglyEmbedded h.se]
      exact (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer _ H).mp hk
    rw [hg₁, hg₂]
    exact Work.DoubleTransitivity.mk_eq_mk_iff.mpr hkH
  have hxor : t ∉ conj g₁ H ∨ t ∉ conj g₂ H := by
    by_contra hcon
    push_neg at hcon
    have hodd := odd_card_inf_conj_of_ne h.se hneconj
    have h2dvd : 2 ∣ Nat.card ↥(conj g₁ H ⊓ conj g₂ H) := by
      have hh := Subgroup.orderOf_dvd_natCard (conj g₁ H ⊓ conj g₂ H) ⟨hcon.1, hcon.2⟩
      rwa [h.invol] at hh
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  obtain ⟨g, hxconj, htn⟩ : ∃ g : G, x ∈ conj g H ∧ t ∉ conj g H := by
    rcases hxor with h1 | h2
    · exact ⟨g₁, hx₁, h1⟩
    · exact ⟨g₂, hx₂, h2⟩
  obtain ⟨y, hy⟩ := hCor1 G h.sit H h.se t h.invol h.notMem g x hxconj htn hx.2
  have hy1 : y * x * y⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have hh := congrArg (fun z => y⁻¹ * z * y) h1
    simpa [mul_assoc] using hh
  have hcard2 : (fixedPts H (Subgroup.zpowers (y * x * y⁻¹))).ncard = 2 :=
    (hC4 G h.sit H h.se t h.invol h.notMem).2.2.1 (y * x * y⁻¹) hy hy1
  have heqcard : (fixedPts H (Subgroup.zpowers (y * x * y⁻¹))).ncard
      = (fixedPts H (Subgroup.zpowers x)).ncard := by
    rw [show y * x * y⁻¹ = MulAut.conj y x from by rw [MulAut.conj_apply]]
    exact ncard_fixedPts_zpowers_conj y x
  omega

end MsetBound

/-! ## §5 Prop. 2 (b), step 3: elements of `M#` fix no point of `Ω` -/

section MsetEmpty

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- A finite set of `ncard ≤ 2` containing two distinct points is that pair. -/
lemma set_eq_pair_of_ncard_le_two {α : Type*} {s : Set α} {a b : α} (hsf : s.Finite)
    (hs : s.ncard ≤ 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  have hsub : ({a, b} : Set α) ⊆ s := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    exacts [ha, hb]
  have hle : s.ncard ≤ ({a, b} : Set α).ncard := by rw [Set.ncard_pair hab]; exact hs
  exact (Set.eq_of_subset_of_ncard_le hsub hle hsf).symm

/-- **§5 Prop. 2 (b)**: an element of `M#` fixes no point of `Ω`. -/
lemma fixedPts_zpowers_eq_empty_of_mem_Mset (hCor1 : Design.ChISixCor1Prop)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Design.Setup5 G H t W p P A r) {u x : G}
    (hu : u ∈ H ∧ orderOf u = 2 ∧ u ∈ Subgroup.centralizer (centD H t : Set G))
    (hx : x ∈ Design.Mset u t) (hx1 : x ≠ 1)
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) :
    fixedPts H (Subgroup.zpowers x) = ∅ := by
  have hut_empty := fixedPts_mul_eq_empty hCor1 h u hu hf
  have hbound := ncard_fixedPts_le_two_of_mem_Mset hCor1 hC4 h hx hx1
  have hodd : Odd (orderOf (u * t)) := by rcases hf with h' | h' <;> rw [h'] <;> norm_num
  have hxc : Commute x (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hsmul_mem : ∀ z ∈ fixedPts H (Subgroup.zpowers x),
      (u * t) • z ∈ fixedPts H (Subgroup.zpowers x) := by
    intro z hz
    rw [Work.ThreePoints.mem_fixedPts] at hz ⊢
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : x ^ k * (u * t) = (u * t) * x ^ k := hxc.zpow_left k
    rw [← mul_smul, hcomm, mul_smul, hz (x ^ k) hw]
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω hω
  have hfix : (u * t) • ω = ω := by
    by_contra hne
    have hω' : (u * t) • ω ∈ fixedPts H (Subgroup.zpowers x) := hsmul_mem ω hω
    have hpair : fixedPts H (Subgroup.zpowers x) = {ω, (u * t) • ω} :=
      set_eq_pair_of_ncard_le_two (Set.toFinite _) hbound hω hω' (fun h => hne h.symm)
    have hmem : (u * t) • ((u * t) • ω) ∈ fixedPts H (Subgroup.zpowers x) :=
      hsmul_mem _ hω'
    rw [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h2 | h2
    · have hfix2 : ((u * t) * (u * t)) • ω = ω := by rw [mul_smul, h2]
      have hfix3 : ((u * t) * (u * t)) • ((u * t) • ω) = (u * t) • ω := by
        rw [mul_smul, h2]
      obtain ⟨k, hk⟩ := hodd
      have hpow1 : ((u * t) ^ (2 * k + 1)) • ω = ω := by
        rw [← hk, pow_orderOf_eq_one]; exact one_smul _ _
      have hsplit : (u * t) ^ (2 * k + 1) = ((u * t) * (u * t)) ^ k * (u * t) := by
        rw [pow_succ]
        congr 1
        exact (pow_mul (u * t) 2 k).trans (by rw [pow_two])
      rw [hsplit, mul_smul] at hpow1
      have hkfix' : ∀ j : ℕ, ((u * t) * (u * t)) ^ j • ((u * t) • ω) = (u * t) • ω := by
        intro j
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ, mul_smul, hfix3, ih]
      rw [hkfix' k] at hpow1
      exact hne hpow1
    · exact absurd (MulAction.injective (u * t) h2) hne
  have : ω ∈ fixedPts H (Subgroup.zpowers (u * t)) := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
    exact Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hfix)
  rw [hut_empty] at this
  exact this

end MsetEmpty

/-! ## §5 Prop. 2 (b), step 4: `(|M|, |F(V)|) = 1` -/

section CoprimeStep

variable {G : Type} [Group G] [Finite G]
  {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}

/-- `g * g = 1` from `orderOf g = 2`. -/
lemma mul_self_eq_one_of_orderOf_eq_two {g : G} (h : orderOf g = 2) : g * g = 1 := by
  have hh := pow_orderOf_eq_one g
  rw [h] at hh
  simpa [pow_two] using hh

/-- `C_G(u) ≤ H` for an involution `u` of a strongly embedded `H`. -/
lemma le_of_centralizer_mem_involutions {H : Subgroup G} (hH : IsStronglyEmbedded H) {u y : G}
    (huH : u ∈ H) (hu2 : orderOf u = 2) (hy : y * u = u * y) : y ∈ H := by
  have hu2' : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have huy : u ∈ conj y H := by
    rw [Work.DoubleTransitivity.mem_conj]
    rw [show y⁻¹ * u * y = u from by
      rw [mul_assoc, ← hy, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact huH
  have hEq : conj y H = H := by
    by_contra hne
    have hne' : conj y H ≠ conj (1 : G) H := by rwa [Work.DoubleTransitivity.conj_one]
    have hodd := odd_card_inf_conj_of_ne hH hne'
    rw [Work.DoubleTransitivity.conj_one] at hodd
    have h2dvd : 2 ∣ Nat.card ↥(conj y H ⊓ H) := by
      have h1 := Subgroup.orderOf_dvd_natCard (conj y H ⊓ H) ⟨huy, huH⟩
      rwa [hu2] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hmem : y ∈ Subgroup.normalizer (H : Set G) :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer y H).mp hEq
  rwa [normalizer_eq_self_of_stronglyEmbedded hH] at hmem

/-- `t` normalizes `C_G(ut)` when `u`, `t` are involutions. -/
lemma conj_mem_centralizer_mul {u t x : G} (hu2 : u * u = 1) (ht2 : t * t = 1)
    (hx : x ∈ Subgroup.centralizer ({u * t} : Set G)) :
    t * x * t⁻¹ ∈ Subgroup.centralizer ({u * t} : Set G) := by
  have htu : (u * t)⁻¹ = t * u := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
  have htu' : (t * u)⁻¹ = u * t := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
  have hcomm_inv : (t * u) * x = x * (t * u) := by
    have hinv : x⁻¹ ∈ Subgroup.centralizer ({u * t} : Set G) := Subgroup.inv_mem _ hx
    have h4 : x⁻¹ * (u * t) = (u * t) * x⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp hinv
    have h5 := congrArg (fun z => z⁻¹) h4
    simpa [mul_inv_rev, htu] using h5
  have hxt : x * t = t * u * x * u := by
    have htu2 : (t * u) * u = t := by rw [mul_assoc, hu2, mul_one]
    calc x * t = x * ((t * u) * u) := by rw [htu2]
      _ = (x * (t * u)) * u := by rw [← mul_assoc]
      _ = ((t * u) * x) * u := by rw [hcomm_inv]
      _ = t * u * x * u := rfl
  have hkey : t * x * t⁻¹ = u * x * u := by
    have hx1 : x = (t * u) * x * (u * t) := by
      rw [← htu', show (t * u) * x * (t * u)⁻¹ = x from by
        rw [hcomm_inv, mul_assoc, mul_inv_cancel, mul_one]]
    conv_lhs => rw [hx1]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [show t * (t * (u * (x * u))) = u * (x * u) from by rw [← mul_assoc, ht2, one_mul]]
  rw [Subgroup.mem_centralizer_singleton_iff, hkey]
  have hl : (u * x * u) * (u * t) = u * (x * t) := by
    simp only [mul_assoc]
    rw [show u * (u * t) = t from by rw [← mul_assoc, hu2, one_mul]]
  have hr : (u * t) * (u * x * u) = u * (t * u * x * u) := by simp only [mul_assoc]
  rw [hl, hr, hxt]

end CoprimeStep

/-! ## §5 Prop. 2 (b): ported from `Sec5Fix/prop2b.lean` (same team), in a private namespace -/

namespace Sec5P2

/-- App. I (1): if the involution `t` normalises `X` and the fixed points `X ⊓ C_G(t)` of the
conjugation action are odd, then `|X|` is odd. -/
theorem odd_card_inf_centralizer {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hodd : Odd (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)))) :
    Odd (Nat.card ↥X) := by
  classical
  haveI hN : FT.Normalizes (Subgroup.zpowers t) X := ⟨Subgroup.zpowers_le.mpr htX⟩
  have hcent : Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    refine le_antisymm ?_ ?_
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers t))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right hxt n).eq.symm
  have hmap := FT.map_fixedPoints_conjAction (Subgroup.zpowers t) X
  rw [hcent, inf_comm] at hmap
  have h1 : Nat.card ↥(FT.fixedPoints (Subgroup.zpowers t) X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective X)]
  have hcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers t) ↥X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [← h1]
    rfl
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, ht]; norm_num⟩
  have hmod := hpg.card_modEq_card_fixedPoints ↥X
  rw [hcard] at hmod
  refine Nat.odd_iff.mpr ?_
  rw [hmod]
  exact Nat.odd_iff.mp hodd

/-- If `u`, `t` are involutions, then `t` inverts `u * t`. -/
theorem conj_mul_inv {G : Type*} [Group G] {u t : G} (ht : orderOf t = 2) (hu : orderOf u = 2) :
    t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu] at h; simpa [pow_two] using h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
  calc t * (u * t) * t = t * u * (t * t) := by group
    _ = t * u := by rw [ht2, mul_one]

/-- Conjugation by an involution normalises the centraliser of the product with another
involution. -/
theorem normalizedBy_centralizer_mul {G : Type*} [Group G] {u t : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) :
    NormalizedBy t (Subgroup.centralizer ({u * t} : Set G)) := by
  intro x hx
  have hxc : Commute x (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hkey : t * (u * t) * t⁻¹ = (u * t)⁻¹ := conj_mul_inv ht hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm1 : Commute (t * x * t⁻¹) (t * (u * t) * t⁻¹) := by
    have h1 : (t * x * t⁻¹) * (t * (u * t) * t⁻¹) = t * (x * (u * t)) * t⁻¹ := by group
    have h2 : (t * (u * t) * t⁻¹) * (t * x * t⁻¹) = t * ((u * t) * x) * t⁻¹ := by group
    show (t * x * t⁻¹) * (t * (u * t) * t⁻¹) = (t * (u * t) * t⁻¹) * (t * x * t⁻¹)
    rw [h1, h2, hxc]
  have hcomm2 : Commute (t * x * t⁻¹) (u * t) := by
    have h := hcomm1.inv_right
    rw [hkey, inv_inv] at h
    exact h
  exact hcomm2

/-- `V = C_D(t)` is the intersection of `C_G(t)` with `C_G(ut)`, when `u ∈ H` is an involution
centralising `V`. -/
theorem centD_eq_inf_centralizer_mul {G : Type} [Group G] [Finite G] {H : Subgroup G} {t u : G}
    (hse : IsStronglyEmbedded H) (huH : u ∈ H) (hu2 : orderOf u = 2)
    (huC : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    Submission.Blueprint.centD H t =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({u * t} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hvt : Commute v t :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2
    have hvu : Commute v u := (Subgroup.mem_centralizer_iff.mp huC) v hv
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hvt,
        Subgroup.mem_centralizer_singleton_iff.mpr (hvu.mul_right hvt)⟩
  · intro y hy
    obtain ⟨hyt, hyut⟩ := Subgroup.mem_inf.mp hy
    have hytc : Commute y t := Subgroup.mem_centralizer_singleton_iff.mp hyt
    have hyutc : Commute y (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hyut
    have hyu : Commute y u := by
      have h := hyutc.mul_right (Commute.inv_right hytc)
      rwa [show (u * t) * t⁻¹ = u from by group] at h
    have hyC : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyu
    have h2u : 2 ∣ orderOf u := by rw [hu2]
    have hle := Work.ThreePoints.IsStronglyEmbedded.centralizer_le (H := H) (x := u) hse huH h2u
    have hyH : y ∈ H := hle hyC
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyH, ?_⟩, hyt⟩
    rw [Work.ThreePoints.mem_conj_iff]
    have hconv : t⁻¹ * y * t = y := by
      calc t⁻¹ * y * t = t⁻¹ * (y * t) := by group
        _ = t⁻¹ * (t * y) := by rw [hytc.eq]
        _ = y := by group
    rw [hconv]
    exact hyH

/-- Sylow conjugacy: if a subgroup `S ≤ H` is a Sylow `r`-subgroup of `G` then every `r`-element
of `G` lies in a conjugate of `H`. -/
theorem exists_conj_mem_of_isPGroup {G : Type*} [Group G] [Finite G]
    {H S : Subgroup G} {r : ℕ} (hr : r.Prime) (hSH : S ≤ H) (hSp : IsPGroup r S)
    (hidx : ¬ r ∣ S.index) {x : G} (hx : IsPGroup r (Subgroup.zpowers x)) :
    ∃ g : G, x ∈ H.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hSs : ((hSp.toSylow hidx : Sylow r G) : Subgroup G) = S := IsPGroup.toSylow_coe hSp hidx
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hSp.toSylow hidx : Sylow r G) T
  have hxT : x ∈ (T : Subgroup G) := hT (Subgroup.mem_zpowers x)
  have hTS : (T : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    have h1 : (T : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul, hSs]
    rw [h1, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, Subgroup.map_mono hSH ?_⟩
  rwa [← hTS]

/-- `Mset u t = J(C_G(ut), t)`. -/
theorem mset_eq_kset {G : Type*} [Group G] {u t : G} :
    Work.NormalComplement.Design.Mset u t =
      Kset (Subgroup.centralizer ({u * t} : Set G)) t := rfl

/-- App. I (1)(b) with `d = 2`: `Kapp t X = J(X,t)` for `X` of odd order normalised by `t`. -/
theorem kapp_eq_mset {G : Type*} [Group G] [Finite G] {u t : G} (ht : orderOf t = 2)
    (htX : NormalizedBy t (Subgroup.centralizer ({u * t} : Set G)))
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({u * t} : Set G)))) :
    Kapp t (Subgroup.centralizer ({u * t} : Set G)) = Work.NormalComplement.Design.Mset u t :=
  (appI_one (d := 2) Nat.prime_two ht htX (Nat.coprime_two_right.mpr hodd)).2 rfl |>.1

/-- App. I (5)(b) with `d = 2`: if `(|K+|, |F(C_X(t))|) = 1` then `Kapp t X` is the underlying
set of an abelian subgroup of `G`. -/
theorem exists_abelian_subgroup_of_coprime {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (ht : orderOf t = 2) (htX : NormalizedBy t X)
    (hodd : Odd (Nat.card ↥X)) (hsolv : Group.IsSolvable ↥X)
    (hcop : Nat.Coprime (Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)))) :
    ∃ K : Subgroup G, (K : Set G) = Kapp t X ∧
      ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  classical
  have hdX : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hodd
  have hKm : Kapp t X = Kset X t :=
    (appI_one (d := 2) Nat.prime_two ht htX hdX).2 rfl |>.1
  obtain ⟨K, hKset, _⟩ := appI_five_b (d := 2) Nat.prime_two ht htX hdX hsolv hcop
  refine ⟨K, hKset, ?_⟩
  have hmem : ∀ x : G, x ∈ K ↔ x ∈ Kset X t := by
    intro x
    show x ∈ (K : Set G) ↔ x ∈ Kset X t
    rw [hKset, hKm]
  intro x hx y hy
  have hxy : x * y ∈ K := K.mul_mem hx hy
  have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := ((hmem (x * y)).mp hxy).2
  have h2 : (x * y)⁻¹ = (y * x)⁻¹ := by
    rw [← h1]
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [((hmem x).mp hx).2, ((hmem y).mp hy).2]
      _ = (y * x)⁻¹ := by group
  exact inv_injective h2

/-- **§5 Prop. 2 (b)**: `M#` fixes no point of `Ω`, `(|M|, |F(V)|) = 1`, and `M` is abelian. -/
theorem helper_prop2b (hFT : Submission.Blueprint.FeitThompsonProp)
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
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) :
    (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) ∧
      ∃ M : Subgroup G, (M : Set G) = Work.NormalComplement.Design.Mset u t ∧
        (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) := by
  classical
  haveI : Fact r.Prime := ⟨h.r_prime⟩
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t; rw [h.invol] at hh; simpa [pow_two] using hh
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u; rw [hu.2.1] at hh; simpa [pow_two] using hh
  set X : Subgroup G := Subgroup.centralizer ({u * t} : Set G) with hXdef
  set V : Subgroup G := Subgroup.centralizer ({t} : Set G) ⊓ X with hVdef
  have htX : NormalizedBy t X := by
    rw [hXdef]
    exact normalizedBy_centralizer_mul h.invol hu.2.1
  have hVeq : V = Submission.Blueprint.centD H t := by
    rw [hVdef, hXdef]
    exact (centD_eq_inf_centralizer_mul h.se hu.1 hu.2.1 hu.2.2).symm
  have hVodd : Odd (Nat.card ↥V) := by
    rw [hVeq]
    exact Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  have hoddX : Odd (Nat.card ↥X) :=
    odd_card_inf_centralizer h.invol (mem_normalizer_of_normalizedBy htX) (by
      rw [inf_comm, ← hVdef]; exact hVodd)
  have hsolvX : Group.IsSolvable ↥X := hFT ↥X hoddX
  have hcopX : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hoddX
  have hKappMset : Kapp t X = Work.NormalComplement.Design.Mset u t := by
    rw [hXdef]
    exact kapp_eq_mset h.invol (hXdef ▸ htX) (hXdef ▸ hoddX)
  have hMcard : (Work.NormalComplement.Design.Mset u t).ncard = (V.subgroupOf X).index := by
    have h := (appI_one (d := 2) Nat.prime_two h.invol htX hcopX).1
    rw [← hKappMset]
    exact h
  have hfix : ∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
      Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅ :=
    fun x hx hx1 => fixedPts_zpowers_eq_empty_of_mem_Mset hCor1 hC4 h hu hx hx1 hf
  have hFpow : ∀ q : ℕ, q.Prime →
      q ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) →
      q = r := by
    intro q hq hdvd
    have hpg : IsPGroup r (Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t)) := h.fitV_syl.1
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq h.r_prime).mp (hq.dvd_of_dvd_pow hdvd)
  have hr_not : ¬ r ∣ (Work.NormalComplement.Design.Mset u t).ncard := by
    intro hrdvd
    have hidx : r ∣ V.relIndex X := by
      rw [hMcard] at hrdvd
      exact hrdvd
    obtain ⟨⟨R, hRsyl, hRn⟩, -, -⟩ :=
      appI_two (d := 2) Nat.prime_two h.invol htX hcopX (p := r) h.r_prime
    have hRnotV : ¬ R ≤ V := by
      intro hRV
      have hdiv : r ∣ R.relIndex X := by
        have hprod : R.relIndex V * V.relIndex X = R.relIndex X :=
          Subgroup.relIndex_mul_relIndex R V X hRV inf_le_right
        rw [← hprod]
        exact dvd_mul_of_dvd_right hidx _
      exact hRsyl.2.2 hdiv
    have hRodd : Odd (Nat.card ↥R) :=
      Odd.of_dvd_nat hoddX (Subgroup.card_dvd_of_le hRsyl.2.1)
    have hcopR : Nat.Coprime (Nat.card R) 2 := Nat.coprime_two_right.mpr hRodd
    obtain ⟨-, hRcomp⟩ := appI_one (d := 2) Nat.prime_two h.invol hRn hcopR
    obtain ⟨hRKset, hRdecomp⟩ := hRcomp rfl
    obtain ⟨z, hzR, hzV⟩ := Set.not_subset.mp hRnotV
    obtain ⟨⟨c, k⟩, ⟨hcC, hcR, hkKapp, hck⟩, -⟩ := hRdecomp z hzR
    have hkKsetR : k ∈ Kset R t := by rw [hRKset] at hkKapp; exact hkKapp
    have hkne : k ≠ 1 := by
      intro hk1
      apply hzV
      have hzc : z = c := by rw [← hck, hk1, mul_one]
      rw [hzc]
      exact ⟨hcC, hRsyl.2.1 hcR⟩
    have hkR : k ∈ R := hkKsetR.1
    have hkX : k ∈ Kset X t := Kset_mono hRsyl.2.1 hkKsetR
    have hkM : k ∈ Work.NormalComplement.Design.Mset u t := by
      rw [hXdef] at hkX
      exact hkX
    have hfixk : Submission.Blueprint.fixedPts H (Subgroup.zpowers k) = ∅ := hfix k hkM hkne
    have hrK : r ∣ (Kset (twoPoint H t) t).ncard := by
      obtain ⟨a, ha1, haeq⟩ := h.K_card
      rw [haeq]
      exact dvd_mul_of_dvd_left (dvd_pow_self r (by omega)) _
    obtain ⟨Rg, hRgD, hRgp, hRgidx⟩ :=
      sec4_P2d (H := H) (t := t) hC4 h.sit h.se h.invol h.notMem r h.r_prime hrK
    have hkpg : IsPGroup r (Subgroup.zpowers k) :=
      IsPGroup.to_le hRsyl.1 (Subgroup.zpowers_le.mpr hkR)
    obtain ⟨g, hg⟩ :=
      exists_conj_mem_of_isPGroup h.r_prime (hRgD.trans inf_le_left) hRgp hRgidx hkpg
    have hmem : (QuotientGroup.mk g : G ⧸ H) ∈
        Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
      rw [Work.DoubleTransitivity.mk_mem_fixedPts_iff]
      exact Subgroup.zpowers_le.mpr hg
    rw [hfixk] at hmem
    exact hmem
  have hcopM : Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
      (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) := by
    refine Nat.coprime_of_dvd' ?_
    intro q hq hqM hqF
    rw [hFpow q hq hqF] at hqM
    exact absurd hqM hr_not
  have hcopK : Nat.Coprime (Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X))) := by
    have h1 : Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)) =
        Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
      rw [show Subgroup.centralizer ({t} : Set G) ⊓ X = V from rfl, hVeq,
        Work.NormalComplement.Design.fitSub,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [hKappMset, h1]
    exact hcopM
  have habM : ∃ M : Subgroup G, (M : Set G) = Work.NormalComplement.Design.Mset u t ∧
      (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) := by
    obtain ⟨K, hK, hab⟩ := exists_abelian_subgroup_of_coprime h.invol htX hoddX hsolvX hcopK
    exact ⟨K, by rw [hK, hKappMset], hab⟩
  exact ⟨hfix, hcopM, habM⟩

end Sec5P2

/-- **Peterfalvi I Ch. III §5 Proposition 2 (b), (c), (d)** (pp. 184–185), merged into the single
datum §5 Prop. 3 and the final contradiction consume.  With `u ∈ H` the unique involution
centralising `V = centD H t`, `ut` has order `f ∈ {3,5}` (from `sec5_prop2a`), `M = Mset u t`, and:

* (b) every `x ∈ M#` fixes no point of `Ω = G ⧸ H`; `(|M|, |F(V)|) = 1`; `M` is an abelian
  subgroup (`∃ M : Subgroup G, (M : Set G) = Mset u t ∧ ∀ x y ∈ M, x*y = y*x`);
* (c) `N_H(P) ≤ N_G(M)`;
* (d) `N = O_{f'}(M) ≠ 1` and `P` is fixed-point-free on `N`.

Route in `_design/Sec5.lean` (`sec5_prop2b`, `sec5_prop2c`, `sec5_prop2d`): `Ω_{ut} = ∅` else
`ut ∈ J(H₁,t)` is conjugate into `K` by `Design.ChISixCor1Prop` and `f ∣ |⟨K⟩| ∣ 2^p - 1`, so
`f ≡ 1 (mod p)` with `f ≤ 5 < 7 ≤ p` (from `sec5_prop1`); then Ch. II §4 P2 (c),
App. I (5)(b), App. III (2),(4) and `Design.BurnsideClassProp`,
`Submission.Blueprint.BenderModelFacts2Prop` (2°) as in the design.  The clause asserting that
`Mset u t` is an abelian subgroup is genuine source content (Prop. 2 (b)), not a formality. -/
theorem sec5_prop2 (hFT : Submission.Blueprint.FeitThompsonProp)
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
    (hu : u ∈ H ∧ orderOf u = 2 ∧ u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) ∧
      ∃ M : Subgroup G, (M : Set G) = Work.NormalComplement.Design.Mset u t ∧
        (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
        H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G) ∧
        Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
        Work.NormalComplement.Design.FpfOn P
          (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G) := by
  -- The Bender-group datum of §5 Prop. 2 (a), from Ch. II §4 Prop. 3
  obtain ⟨hun, ub, hub, hdatb⟩ := sec5_setup (G := G) hFT hC4 hP3 h
  obtain ⟨w, hw, huniq'⟩ := hun
  have hun2 : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) := ⟨w, hw, huniq'⟩
  have huniq : ∀ y : G, y ∈ H → orderOf y = 2 →
      y ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) → y = w :=
    fun y h1 h2 h3 => huniq' y ⟨h1, h2, h3⟩
  -- `orderOf (u*t) ∈ {3,5}`
  have hbd : ∀ v : G, v ∈ H → orderOf v = 2 →
      v ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) →
      (let C : Subgroup G := Subgroup.centralizer (A : Set G)
       let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
       ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (HY : Subgroup Y),
         Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
         LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
         LeanEval.GroupTheory.Defs.IsStronglyEmbedded HY ∧
         Submission.Blueprint.IsZassenhaus HY ∧
         (Submission.Blueprint.involutions (HY : Set Y)).ncard = 2 ^ p - 1 ∧
         ∃ (hu0 : v ∈ F₀) (ht0 : t ∈ F₀),
           φ ⟨v, hu0⟩ ∈ HY ∧ orderOf (φ ⟨v, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ HY ∧
           orderOf (φ ⟨t, ht0⟩) = 2 ∧
           ∀ x : F₀, (x : G) ∈ H → φ x ∈ HY) := by
    intro v hv1 hv2 hv3
    have hveq : ub = v :=
      (huniq ub hub.1 hub.2.1 hub.2.2).trans ((huniq v hv1 hv2 hv3).symm)
    subst hveq
    exact hdatb
  have hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 :=
    sec5_prereq_f (G := G) hFT hC hC4 hP3 hIII hMF2 h hun2 hbd u hu.1 hu.2.1 hu.2.2
  have hp7 : 7 ≤ p := sec5_prop1 (G := G) hFT hC4 hBP hBC h
  -- (b)
  obtain ⟨hb1, hb2, hb3⟩ :=
    Sec5P2.helper_prop2b (G := G) hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hf
  -- (c)
  obtain ⟨M, hM, habM⟩ := hb3
  have hL1 : ∀ X : Subgroup G, P ≤ X → X ≤ Submission.Blueprint.centD H t →
      H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G) → X = P :=
    fun X hPX hXV hN => sec5_prereq_l1 (G := G) hFT hP3 h X hPX hXV hN
  have hc := sec5_clause_c (G := G) hFT hA hC hC4 hP3 hIII hMF2 hCor1 h u hu hL1 M hM
  -- (d)
  have hd := sec5_clause_d (G := G) hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu M hM
    hp7 hf (hbd u hu.1 hu.2.1 hu.2.2)
  exact ⟨hb1, hb2, ⟨M, hM, habM, hc, hd.1, hd.2⟩⟩

end Work.NormalComplement
