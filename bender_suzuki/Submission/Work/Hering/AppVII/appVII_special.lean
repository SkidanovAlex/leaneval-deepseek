import Mathlib
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Coprime.All
import Submission.Work.Hering.AppVII.orbit_sum
import Submission.Work.Hering.AppVII.special_centralizer_data
import Submission.Work.Hering.AppVII.special_abelian
import Submission.Work.NormalComplement.appVIIProp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `appVII_special`: the special configuration of Peterfalvi's Appendix VII

This file assembles the contradiction in the "special configuration" of Appendix VII, given the
pieces proved by the fleet:

* `special_group_structure` — the group theory of `A = Q ⋊ P`: `⁅P,Q⁆ = Q`, `Q` is a `q`-group,
  `Φ(Q) ≤ Z(Q)`, and either `Q` is abelian or `Z(Q) = [Q,Q]` is centralised by `P`;
* `special_centralizer_data` — `C_Q(P) = 1` in the abelian case and `C_Q(P) = Z(Q)` otherwise;
* `special_extraspecial_data` — in the non-abelian case `Q` is extraspecial of order `q^(2m+1)`
  with `q` odd;
* `special_abelian` / `special_nonabelian` — the two contradiction arguments;
* `appVII_special_two` (below) — the case `p = 2`, where `C_K(P) = 1` forces `P` to be central,
  contradicting `⁅P,Q⁆ = Q ≠ ⊥`.
-/

open scoped Pointwise
open scoped commutatorElement
open scoped IsMulCommutative

namespace Work.Hering.AppVII

section Setup

variable {A : Type*} [Group A] (P Q : Subgroup A)

theorem bot_ne_top_of_nontrivial {K : Type*} [Group K] [Nontrivial K] :
    (⊥ : Subgroup K) ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  have hmem : x ∈ (⊥ : Subgroup K) := by rw [h]; exact Subgroup.mem_top x
  exact hx (by simpa using hmem)

/-- `C_K(Q) = 1` from `C_K(⁅P,Q⁆) = 1` and `⁅P,Q⁆ = Q`. -/
theorem hQfix_of_hNfix {K : Type*} [Group K] [MulDistribMulAction A K]
    (hcomm : ⁅P, Q⁆ = Q) (hNfix : appVIIF1 A P Q K = ⊥) :
    ∀ k : K, (∀ a ∈ Q, a • k = k) → k = 1 := by
  intro k hk
  have h : k ∈ appVIIF1 A P Q K := by
    change ∀ y ∈ ⁅P, Q⁆, y • k = k
    rw [hcomm]
    exact hk
  rw [hNfix] at h
  simpa using h

/-- `C_K(P) = 1` in the `∀` form, from `appVIIFx A P Q K 1 = ⊥`. -/
theorem hPfpf_of_bot {K : Type*} [Group K] [MulDistribMulAction A K]
    (hPfpf : appVIIFx A P Q K 1 = ⊥) :
    ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1 := by
  intro k hk
  have hmap : P.map (MulAut.conj (((1 : ↥Q) : A))).toMonoidHom = P := by
    have h1 : ((1 : ↥Q) : A) = 1 := rfl
    rw [h1, map_one]
    exact Subgroup.map_id P
  have h : k ∈ appVIIFx A P Q K 1 := by
    change ∀ y ∈ P.map (MulAut.conj (((1 : ↥Q) : A))).toMonoidHom, y • k = k
    rw [hmap]
    exact hk
  rw [hPfpf] at h
  simpa using h

/-- `Q ≠ ⊥` from `C_K(⁅P,Q⁆) = 1` and `K` nontrivial. -/
theorem Q_ne_bot_of_hNfix {K : Type*} [Group K] [MulDistribMulAction A K]
    (hKne : Nontrivial K) (hNfix : appVIIF1 A P Q K = ⊥) : Q ≠ ⊥ := by
  intro hbot
  have htop : appVIIF1 A P Q K = ⊤ := by
    ext k
    constructor
    · intro _; exact Subgroup.mem_top k
    · intro _
      change ∀ y ∈ ⁅P, Q⁆, y • k = k
      rw [hbot]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1, one_smul]
  rw [htop] at hNfix
  exact bot_ne_top_of_nontrivial (K := K) hNfix.symm

/-- `⁅P,Q⁆ ≠ ⊥` from `C_K(⁅P,Q⁆) = 1` and `K` nontrivial. -/
theorem commutator_ne_bot_of_hNfix {K : Type*} [Group K] [MulDistribMulAction A K]
    (hKne : Nontrivial K) (hNfix : appVIIF1 A P Q K = ⊥) : ⁅P, Q⁆ ≠ ⊥ := by
  intro hbot
  have htop : appVIIF1 A P Q K = ⊤ := by
    ext k
    constructor
    · intro _; exact Subgroup.mem_top k
    · intro _
      change ∀ y ∈ ⁅P, Q⁆, y • k = k
      rw [hbot]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1, one_smul]
  rw [htop] at hNfix
  exact bot_ne_top_of_nontrivial (K := K) hNfix.symm

/-- **The case `p = 2`.**  If `|P| = 2`, then `C_K(P) = 1` forces every `x ∈ K` to satisfy
`σ • x = x⁻¹` for the generator `σ` of `P`; hence `σ` is central in the action, so (as the
action is faithful) `σ ∈ Z(A)`, whence `⁅P,Q⁆ = ⊥ ≠ Q`. -/
theorem appVII_special_two [Finite A] (hcardP : Nat.card ↥P = 2) (hcomm : ⁅P, Q⁆ = Q)
    (hQne : Q ≠ ⊥)
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hKcomm : IsMulCommutative K)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hKne : Nontrivial K) : False := by
  haveI : IsMulCommutative K := hKcomm
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hcardP
  have hmem1 : (1 : ↥P) = x ∨ (1 : ↥P) = y := by
    have h : (1 : ↥P) ∈ ({x, y} : Set ↥P) := by rw [hset]; exact Set.mem_univ _
    simpa using h
  obtain ⟨σ, hσne, hσall⟩ : ∃ σ : ↥P, σ ≠ 1 ∧ ∀ z : ↥P, z = 1 ∨ z = σ := by
    rcases hmem1 with h1 | h1
    · refine ⟨y, fun hy => hxy (by rw [← h1, ← hy]), fun z => ?_⟩
      have hz : z ∈ ({x, y} : Set ↥P) := by rw [hset]; exact Set.mem_univ z
      rcases (by simpa using hz : z = x ∨ z = y) with h | h
      · exact Or.inl (by rw [h, h1])
      · exact Or.inr h
    · refine ⟨x, fun hx => hxy (by rw [hx, h1]), fun z => ?_⟩
      have hz : z ∈ ({x, y} : Set ↥P) := by rw [hset]; exact Set.mem_univ z
      rcases (by simpa using hz : z = x ∨ z = y) with h | h
      · exact Or.inr h
      · exact Or.inl (by rw [h, h1])
  have hσ2 : σ * σ = 1 := by
    rcases hσall (σ * σ) with h | h
    · exact h
    · exfalso
      exact hσne (mul_left_cancel (by rw [h, mul_one] : σ * σ = σ * 1))
  have hσ2A : (σ : A) * (σ : A) = 1 := by
    have h := congrArg (fun z : ↥P => (z : A)) hσ2
    simpa using h
  have hσinv : (σ : A)⁻¹ = (σ : A) := inv_eq_of_mul_eq_one_right hσ2A
  have hinv : ∀ t : K, (σ : A) • t = t⁻¹ := by
    intro t
    have hstep : (σ : A) • ((σ : A) • t) = t := by
      rw [← mul_smul, hσ2A]
      exact one_smul A t
    have hfix : (σ : A) • (t * ((σ : A) • t)) = t * ((σ : A) • t) := by
      rw [smul_mul', hstep]
      exact mul_comm _ _
    have h1 : t * ((σ : A) • t) = 1 := by
      apply hPfpf
      intro a ha
      have hcoe : (⟨a, ha⟩ : ↥P) = 1 ∨ (⟨a, ha⟩ : ↥P) = σ := hσall ⟨a, ha⟩
      rcases hcoe with h | h
      · have ha1 : a = 1 := by simpa using congrArg (fun z : ↥P => (z : A)) h
        rw [ha1, one_smul]
      · have ha1 : a = (σ : A) := by simpa using congrArg (fun z : ↥P => (z : A)) h
        rw [ha1]; exact hfix
    exact eq_inv_of_mul_eq_one_right h1
  have hact : ∀ a : A, ∀ t : K, (a * (σ : A) * a⁻¹) • t = (σ : A) • t := by
    intro a t
    calc (a * (σ : A) * a⁻¹) • t
        = a • ((σ : A) • (a⁻¹ • t)) := by rw [mul_smul, mul_smul]
      _ = a • ((a⁻¹ • t)⁻¹) := by rw [hinv]
      _ = (a • (a⁻¹ • t))⁻¹ := by rw [smul_inv']
      _ = ((a * a⁻¹) • t)⁻¹ := by rw [← mul_smul]
      _ = ((1 : A) • t)⁻¹ := by rw [mul_inv_cancel]
      _ = t⁻¹ := by rw [one_smul]
      _ = (σ : A) • t := by rw [hinv]
  have hcen : (σ : A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro a
    have h1 : a * (σ : A) * a⁻¹ * (σ : A)⁻¹ = 1 := by
      apply hfaith
      intro t
      calc (a * (σ : A) * a⁻¹ * (σ : A)⁻¹) • t
          = (a * (σ : A) * a⁻¹) • ((σ : A)⁻¹ • t) := by rw [mul_smul]
        _ = (a * (σ : A) * a⁻¹) • ((σ : A) • t) := by rw [hσinv]
        _ = (σ : A) • ((σ : A) • t) := by rw [hact a ((σ : A) • t)]
        _ = ((σ : A) * (σ : A)) • t := by rw [mul_smul]
        _ = t := by rw [hσ2A]; exact one_smul A t
    have h2 : a * (σ : A) * a⁻¹ = σ := mul_inv_eq_one.mp h1
    calc a * (σ : A) = a * (σ : A) * a⁻¹ * a := by group
      _ = (σ : A) * a := by rw [h2]
  have hPcen : P ≤ Subgroup.center A := by
    intro z hz
    rcases hσall ⟨z, hz⟩ with h | h
    · have hz1 : z = 1 := by simpa using congrArg (fun w : ↥P => (w : A)) h
      rw [hz1]; exact Subgroup.one_mem _
    · have hzσ : z = (σ : A) := by simpa using congrArg (fun w : ↥P => (w : A)) h
      rw [hzσ]; exact hcen
  have hcomm' : ⁅P, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q _
    have hz' := hPcen hz
    rw [Subgroup.mem_center_iff] at hz'
    exact hz' q
  rw [hcomm'] at hcomm
  exact hQne hcomm.symm

end Setup

section Main

theorem appVII_special {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) {r : ℕ} (hr : r.Prime)
    (hKexp : ∀ x : K, x ^ r = 1) (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : appVIIFx A P Q K 1 = ⊥) (hNfix : appVIIF1 A P Q K = ⊥)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    False := by
  have hPfpf' := hPfpf_of_bot P Q hPfpf
  have hQne := Q_ne_bot_of_hNfix P Q hKne hNfix
  have hnotbot := commutator_ne_bot_of_hNfix P Q hKne hNfix
  obtain ⟨hcomm, hqgrp, hPhi, hcases⟩ :=
    Work.NormalComplement.AppVII.GroupStructure P Q hQn hinf hsup hp hcardP hpQ hnotbot hcent
  have hQfix := hQfix_of_hNfix P Q hcomm hNfix
  have hdata := special_centralizer_data P Q hQn hinf hsup hp hcardP hpQ hcomm hPhi hcent
  rcases hp.eq_two_or_odd with h2 | _hoddp
  · exact appVII_special_two P Q (hcardP.trans h2) hcomm hQne hKcomm hfaith hPfpf' hKne
  · by_cases hab : IsMulCommutative ↥Q
    · exact special_abelian P Q hQn hinf hsup hp hcardP hpQ hcomm hab (hdata.1 hab)
        hcop hr hKexp hKcomm hKne hirr hfaith hPfpf' hQfix
    · have hZdata : Subgroup.center ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ := by
        rcases hcases with h | h
        · exact absurd h hab
        · exact h.1
      obtain ⟨q, hq, hQp⟩ := hqgrp
      obtain ⟨hqodd, m, hm, hcardQ, hQext⟩ :=
        Work.NormalComplement.AppVII.ExtraspecialData P Q hQn hinf hsup hp hq hcardP hpQ hQp
          hcomm hab hZdata hPhi (hdata.2 hab) hodd hcop hr hKexp hKcomm hKne hirr hfaith
      exact Work.NormalComplement.corner_extraspecial Q P hQn hinf hsup hp hq hcardP hpQ
        hcardQ hm hqodd hQext (hdata.2 hab) hcomm hcop hr hKexp hKcomm hKne hirr hfaith
        hPfpf' hQfix

end Main

end Work.Hering.AppVII
