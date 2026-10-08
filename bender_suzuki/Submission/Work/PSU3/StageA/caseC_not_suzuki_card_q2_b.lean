import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.W_centralizes_Q0sub
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.Higman.AType_isSuzukiTwoGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseC_not_suzuki_card_q2_b`

Peterfalvi II, Ch. VI §1, case b) is impossible: if `Q` is a Suzuki 2-group with
`|Q| = |Q₀sub H|²` (so `Q` is of *type A* in Higman's classification, `|Q| = |Z(Q)|²`),
then `W = C_V(K) = ⊥`, contradicting `W ≠ ⊥`.

The proof here avoids the case trichotomy of Ch. VI §1 entirely.  The mathematical point is:

* `Q₀sub H = ⟨Inv H⟩ = Z(Q)` (the involutions of `H` are exactly those of `Q`, since `Q` is the
  unique Sylow `2`-subgroup of `H = Q ⋊ D` with `|D|` odd, and by Ch. V §1 Prop. 1 c) they are
  central in the nilpotent group `Q`); hence `|Q| = |Z(Q)|²` and Higman's classification
  (via `Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup`) exhibits `Q ≅ A(F,θ) = SzA F θ` with
  `θ ≠ 1` of odd order.
* In a Suzuki 2-group of type `A` the map `x ↦ x²` is, on `Q/Z(Q)`, a *bijection* onto `Z(Q)`
  (`x² = y² ⟹ x y⁻¹ ∈ Z(Q)`, which for `SzA F θ` is the field fact `a·θa = c·θc ⟹ a = c`,
  `Work.Higman.mul_theta_self_eq_one`).  Consequently an automorphism `α` of `Q` fixing `Z(Q)`
  pointwise induces the identity on `Q/Z(Q)`, so `x ↦ α x · x⁻¹` is a homomorphism `Q → Z(Q)`
  and `α = 1` on `Z(Q)` forces `α² = 1` (`caseC_q2b_mulAut_eq_one_of_sq_isTypeA`).
* An element `w ∈ W#` has odd order and induces on `Q` an automorphism centralising `Z(Q)`
  (`W_centralizes_Q0sub`); by the previous point that automorphism is trivial, so `w`
  centralises `Q ⊆ H` and `t` (`w ∈ V = C_D(t)`), hence `w ∈ Z(G) = ⊥` by simplicity, since
  `G = ⟨Q, t⟩` (`Work.RankOneUniqueness.closure_Q_t_eq_top`). -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Conjugation by an element normalising a subgroup -/

/-- The conjugation automorphism of `Q` induced by an element of `N_G(Q)`. -/
noncomputable def caseC_q2b_conjAutQ {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : MulAut ↥Q where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem hg) (x : G)).mp x.2
    simpa using h⟩
  left_inv x := by ext; group
  right_inv x := by ext; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

theorem caseC_q2b_conjAutQ_coe {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    ((caseC_q2b_conjAutQ g hg x : ↥Q) : G) = g * (x : G) * g⁻¹ := rfl

theorem caseC_q2b_conjAutQ_pow_coe {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (k : ℕ) (x : ↥Q) :
    (((caseC_q2b_conjAutQ g hg) ^ k) x : G) = g ^ k * (x : G) * (g ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, caseC_q2b_conjAutQ_coe, ih, pow_succ]
      group

/-! ## The abstract criterion -/

/-- **Odd-order automorphisms of a type-`A` `2`-group fixing `Ω₁` are trivial.**

Let `Z ≤ P` be a subgroup such that every element of `Z` is an involution, every square lies in
`Z`, and `x² = y² ⟹ x y⁻¹ ∈ Z` (the "type `A`" behaviour of the squaring map, where `Z` plays
the role of `Ω₁ = Z(P)` and of the centre).  Then an automorphism `α` of `P` of odd order fixing
`Z` pointwise is trivial.

Indeed every `α x · x⁻¹` lies in `Z`, so `x ↦ α x · x⁻¹` is a homomorphism `P → Z`; consequently
`α²` is the identity, and an element of odd order squaring to `1` is `1`. -/
theorem caseC_q2b_mulAut_eq_one_of_sq_isTypeA {P : Type} [Group P] (Z : Subgroup P)
    (hZsq : ∀ z ∈ Z, z * z = 1)
    (hsqmem : ∀ x : P, x * x ∈ Z)
    (hlinj : ∀ x y : P, x * x = y * y → x * y⁻¹ ∈ Z)
    (α : MulAut P) (hα : ∀ z ∈ Z, α z = z) (hodd : Odd (orderOf α)) : α = 1 := by
  have hmem : ∀ x : P, α x * x⁻¹ ∈ Z := by
    intro x
    refine hlinj (α x) x ?_
    rw [← map_mul, hα (x * x) (hsqmem x)]
  have key : ∀ x : P, α (α x) = x := by
    intro x
    have hmemx : α x * x⁻¹ ∈ Z := hmem x
    have aux : (α x * x⁻¹) * x = α x := by group
    calc α (α x) = α ((α x * x⁻¹) * x) := by rw [aux]
      _ = α (α x * x⁻¹) * α x := map_mul α _ _
      _ = (α x * x⁻¹) * α x := by rw [hα _ hmemx]
      _ = (α x * x⁻¹) * ((α x * x⁻¹) * x) := by rw [aux]
      _ = ((α x * x⁻¹) * (α x * x⁻¹)) * x := by group
      _ = x := by rw [hZsq _ hmemx, one_mul]
  have h2 : α ^ 2 = 1 := by
    rw [pow_two]
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    exact key x
  have hdvd : orderOf α ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h2
  have h1 : orderOf α = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
  exact orderOf_eq_one_iff.mp h1

/-! ## The model computation -/

/-- **Equal squares in Higman's group `A(K,θ)`** (`θ` of odd order): `x * x = y * y` implies
`x * y⁻¹ ∈ Z(A(K,θ))`.

In coordinates `x = (a,b)`, `y = (c,d)` and `x * x = (0, a·θa)`, `y * y = (0, c·θc)`
(`SzA.sq_eq`), so `a·θa = c·θc`; if `a ≠ 0` then `(a/c)·θ(a/c) = 1`, whence `a = c` by
`Work.Higman.mul_theta_self_eq_one`, and if `a = 0` then `c = 0`.  In both cases the first
coordinate of `x * y⁻¹` vanishes, i.e. `x * y⁻¹` is central (`SzA.mem_center_iff`). -/
theorem caseC_q2b_SzA_sq_eq_imp_mul_inv_mem_center {K : Type} [Field K] [CharP K 2]
    (θ : K ≃+* K) (hθ : θ ≠ 1) (hodd : Odd (orderOf θ))
    {x y : Work.ZassenhausSuzuki.SzA K θ} (h : x * x = y * y) :
    x * y⁻¹ ∈ Subgroup.center (Work.ZassenhausSuzuki.SzA K θ) := by
  have hb : x.a * θ x.a = y.a * θ y.a := by
    have h1 := congrArg Work.ZassenhausSuzuki.SzA.b h
    rw [Work.ZassenhausSuzuki.SzA.sq_eq θ x, Work.ZassenhausSuzuki.SzA.sq_eq θ y] at h1
    simpa using h1
  have hxy : x.a = y.a := by
    rcases eq_or_ne x.a 0 with h0 | h0
    · have hy : y.a * θ y.a = 0 := by rw [← hb, h0]; simp
      have hy0 : y.a = 0 := by
        rcases mul_eq_zero.mp hy with h' | h'
        · exact h'
        · exact (RingEquiv.map_eq_zero_iff θ).mp h'
      rw [h0, hy0]
    · have hy0 : y.a ≠ 0 := by
        intro hy
        have hb' : x.a * θ x.a = 0 := by rw [hb, hy]; simp
        rcases mul_eq_zero.mp hb' with h' | h'
        · exact h0 h'
        · exact h0 ((RingEquiv.map_eq_zero_iff θ).mp h')
      have hu : (x.a / y.a) * θ (x.a / y.a) = 1 := by
        rw [map_div₀, div_mul_div_comm, hb,
          div_self (mul_ne_zero hy0 ((RingEquiv.map_ne_zero_iff θ).mpr hy0))]
      exact (div_eq_one_iff_eq hy0).mp (Work.Higman.mul_theta_self_eq_one θ hodd hu)
  rw [Work.ZassenhausSuzuki.SzA.mem_center_iff θ hθ]
  rw [Work.ZassenhausSuzuki.SzA.mul_a, Work.ZassenhausSuzuki.SzA.inv_a, hxy]
  simp

/-- Membership in the centre is preserved by a multiplicative equivalence. -/
theorem caseC_q2b_map_mem_center_iff {P R : Type} [Group P] [Group R] (φ : P ≃* R) (z : P) :
    φ z ∈ Subgroup.center R ↔ z ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h a
    apply φ.injective
    rw [map_mul, map_mul, h (φ a)]
  · intro h b
    obtain ⟨a, rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, h a]

/-! ## `Q₀sub H = Z(Q)` -/

private lemma exists_ne_one_of_ne_bot {P : Type} [Group P] {W : Subgroup P} (h : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

/-- Peterfalvi II Ch. V §1 Prop. 1 c): the involutions of `H` are central in the nilpotent
group `Q`; hence `Q₀sub H = ⟨Inv H⟩` is central in `Q`. -/
theorem caseC_q2b_Q0sub_le_centerOf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) :
    Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q := by
  have hsplit := hS.split
  have hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hS.two
  have hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G),
      ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hcent : involutions (H : Set G) ⊆ (Work.ThmF.centerOf Q : Set G) :=
    fun u hu => Work.ThmF.ChV12.prop1c hS.situation H Q t hsplit hD hnil u hu
  rw [Work.ThmF.Q0sub, Subgroup.closure_le]
  intro a ha
  rcases Work.ThmF.mem_Q0_iff.mp ha with ⟨haH, haord⟩ | ha1
  · exact hcent ⟨haH, haord⟩
  · rw [ha1]; exact (Work.ThmF.centerOf Q).one_mem

/-! ## The main theorem -/

theorem caseC_not_suzuki_card_q2_b {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hW : Work.ThmF.W H t ≠ ⊥)
    (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2) : False := by
  classical
  have hsplit := hS.split
  have hQ0leQ : Work.ThmF.Q0sub H ≤ Q := Q0sub_le_Q hsplit
  have hQ0central : Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q := caseC_q2b_Q0sub_le_centerOf hS
  -- ### `Q₀sub H = Z(Q)`
  have hcenter : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Subgroup.mem_subgroupOf]
      by_cases hz1 : (z : ↥Q) = 1
      · rw [show (z : G) = 1 from congrArg Subtype.val hz1]
        exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
      · have hzsq : z * z = 1 := by
          have h := ((hHig ↥Q hSuz).1 z).mp hz
          simpa [pow_two] using h
        have ho : orderOf (z : G) = 2 := by
          rw [Subgroup.orderOf_coe]
          exact orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
        exact Work.ThmF.Q0_le_Q0sub H
          (Work.ThmF.involutions_subset_Q0 H ⟨hsplit.le z.2, ho⟩)
    · intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      rw [Subgroup.mem_center_iff]
      intro a
      have h := (Work.ThmF.mem_centerOf.mp (hQ0central hz)).2 (a : G) a.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact h.symm
  have hcenterCard : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hcenter]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0leQ).toEquiv
  have hcardZ : Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2 := by
    rw [hcenterCard]
    exact hcard
  -- ### Higman's classification: `Q ≅ A(F,θ)` of type `A`
  obtain ⟨n, θ, hθ, hθodd, -, ⟨φ⟩⟩ :=
    Work.ZassenhausSuzuki.szA_of_isSuzukiTwoGroup hHig hSuz hcardZ
  -- ### the "type A" squaring structure on `↥Q`
  have hsqmemQ : ∀ x : ↥Q, x * x ∈ Subgroup.center ↥Q := by
    intro x
    have h := (hHig ↥Q hSuz).2.1 x
    simpa [pow_two] using h
  have hZsqQ : ∀ z ∈ Subgroup.center ↥Q, z * z = 1 := by
    intro z hz
    have h := ((hHig ↥Q hSuz).1 z).mp hz
    simpa [pow_two] using h
  have hlinjQ : ∀ x y : ↥Q, x * x = y * y → x * y⁻¹ ∈ Subgroup.center ↥Q := by
    intro x y hxy
    have h2 : φ x * φ x = φ y * φ y := by rw [← map_mul, ← map_mul, hxy]
    have h3 : φ (x * y⁻¹) ∈ Subgroup.center (Work.ZassenhausSuzuki.SzA (GaloisField 2 n) θ) := by
      rw [map_mul, map_inv]
      exact caseC_q2b_SzA_sq_eq_imp_mul_inv_mem_center θ hθ hθodd h2
    exact (caseC_q2b_map_mem_center_iff φ (x * y⁻¹)).mp h3
  -- ### an element `1 ≠ w ∈ W`
  obtain ⟨w, hwW, hw1⟩ := exists_ne_one_of_ne_bot hW
  have hwD : w ∈ twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t (Work.ThmF.W_le_centD H t hwW)
  have hwN : w ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal (Subgroup.mem_inf.mp hwD).1
  have hoddw : Odd (orderOf w) :=
    Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint hsplit)
      (Subgroup.orderOf_dvd_natCard (twoPoint H t) hwD)
  have hdvdα : orderOf (caseC_q2b_conjAutQ w hwN) ∣ orderOf w := by
    rw [orderOf_dvd_iff_pow_eq_one]
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    rw [caseC_q2b_conjAutQ_pow_coe, pow_orderOf_eq_one]
    simp
  have hoddα : Odd (orderOf (caseC_q2b_conjAutQ w hwN)) := Odd.of_dvd_nat hoddw hdvdα
  -- ### it fixes `Z(Q) = Q₀sub H` pointwise
  have hfixα : ∀ z ∈ Subgroup.center ↥Q, caseC_q2b_conjAutQ w hwN z = z := by
    intro z hz
    have hzQ0 : (z : G) ∈ Work.ThmF.Q0sub H := by
      rw [← Subgroup.mem_subgroupOf]
      rw [← hcenter]
      exact hz
    have hcomm := Work.PSU3.StageA.W_centralizes_Q0sub hS hC4 w hwW (z : G) hzQ0
    apply Subtype.ext
    rw [caseC_q2b_conjAutQ_coe]
    calc w * (z : G) * w⁻¹ = (z : G) * w * w⁻¹ := by rw [hcomm]
      _ = (z : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  -- ### hence `w` centralises `Q`
  have hα1 : caseC_q2b_conjAutQ w hwN = 1 :=
    caseC_q2b_mulAut_eq_one_of_sq_isTypeA (Subgroup.center ↥Q) hZsqQ hsqmemQ hlinjQ
      (caseC_q2b_conjAutQ w hwN) hfixα hoddα
  have hwQ : ∀ q ∈ Q, w * q * w⁻¹ = q := by
    intro q hq
    have h := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : G)) hα1
    simp only [MulAut.one_apply] at h
    rw [caseC_q2b_conjAutQ_coe] at h
    exact h
  -- ### `w` centralises `t` as well, so `w ∈ Z(G) = ⊥`
  have hwt : w * t = t * w :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hwW)).2
  haveI : IsSimpleGroup G := hS.simple
  have htop : Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ :=
    Work.RankOneUniqueness.closure_Q_t_eq_top hsplit
  have hmemZ : w ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← htop]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y (hy | hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          have h := hwQ y hy
          calc y * w = (w * y * w⁻¹) * w := by rw [h]
            _ = w * y := by group)
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hZbot : Subgroup.center G = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple (Subgroup.center G) (inferInstance) with h | h
    · exact h
    · exfalso
      have hHcenter : H ≤ Subgroup.center G := by rw [h]; exact le_top
      have hHnorm : H.Normal := ⟨fun a ha b => by
        have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact ha⟩
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS.simple H hHnorm with hb | ht
      · have heven : Even (Nat.card H) := hsplit.stronglyEmbedded.2.1
        rw [hb, Subgroup.card_bot] at heven
        exact absurd heven (by norm_num)
      · exact hsplit.stronglyEmbedded.1 ht
  exact hw1 (Subgroup.mem_bot.mp (hZbot ▸ hmemZ))

end Work.PSU3.StageA
