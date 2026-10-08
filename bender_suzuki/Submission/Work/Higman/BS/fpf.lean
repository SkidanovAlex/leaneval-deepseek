/-
Copyright (c) 2024. All rights reserved.

# Fixed-point-freeness of `ξ` on `P ⧸ Z(P)`

If `ξ ∈ Aut(P)` has odd order and `C_P(ξ ^ k) = 1` (fixed-point-freeness on `P`), then `ξ ^ k` has
no non-zero fixed point on `P ⧸ Z(P)` either.  A fixed point `x ∉ Z(P)` with `x⁻¹ ξ ^ k x ∈ Z(P)`
gives a `1`-cocycle `f (i) = x⁻¹ (ξ ^ k) ^ i x` on the cyclic group `⟨ξ ^ k⟩` with values in the
abelian group `Z(P)`; its norm vanishes (the cocycle identity at `i = orderOf (ξ ^ k)`), and since
`|⟨ξ ^ k⟩|` is coprime to `|Z(P)|` the norm map has kernel `im (σ - 1)`
(`Work.Higman.mulAut_norm_im`).  Adjusting `x` by the resulting coboundary makes it fixed by
`ξ ^ k`, hence `x ∈ Z(P)`.
-/

import Mathlib
import Submission.Work.Higman.BS.Defs
import Submission.Work.Higman.mulAut_norm_im

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

theorem mem_center_map (ξ : MulAut P) {z : P} (hz : z ∈ Subgroup.center P) :
    ξ z ∈ Subgroup.center P := by
  rw [← map_center_eq ξ]
  exact Subgroup.mem_map_of_mem _ hz

theorem mem_center_map_symm (ξ : MulAut P) {z : P} (hz : z ∈ Subgroup.center P) :
    ξ.symm z ∈ Subgroup.center P := by
  rw [← map_center_eq ξ.symm]
  exact Subgroup.mem_map_of_mem _ hz

/-- The restriction of `ξ ^ k` to the centre of `P`. -/
noncomputable def xiOnCenter (ξ : MulAut P) (k : ℕ) : MulAut ↥(Subgroup.center P) :=
  { toFun := fun z => ⟨(ξ ^ k) (z : P), mem_center_map (ξ ^ k) z.2⟩
    invFun := fun z => ⟨(ξ ^ k).symm (z : P), mem_center_map_symm (ξ ^ k) z.2⟩
    left_inv := fun z => Subtype.ext (by simp)
    right_inv := fun z => Subtype.ext (by simp)
    map_mul' := fun z w => Subtype.ext (by simp [map_mul]) }

theorem xiOnCenter_coe (ξ : MulAut P) (k : ℕ) (z : ↥(Subgroup.center P)) :
    ((xiOnCenter ξ k z : ↥(Subgroup.center P)) : P) = (ξ ^ k) (z : P) := rfl

theorem xiOnCenter_pow_coe (ξ : MulAut P) (k : ℕ) :
    ∀ (i : ℕ) (z : ↥(Subgroup.center P)),
      (((xiOnCenter ξ k) ^ i) z : P) = ((ξ ^ k) ^ i) (z : P) := by
  intro i
  induction i with
  | zero => intro z; simp
  | succ i ih =>
      intro z
      rw [pow_succ, MulAut.mul_apply, ih, xiOnCenter_coe, pow_succ, MulAut.mul_apply]

/-- **`ξ ^ k` has no non-trivial fixed point on `P ⧸ Z(P)`.**
If `x⁻¹ · ξ ^ k x ∈ Z(P)` and `ξ ^ k ≠ 1`, then `x ∈ Z(P)`. -/
theorem mem_center_of_mul_mem_center (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ)
    {k : ℕ} (hk : ξ ^ k ≠ 1) {x : P} (hx : x⁻¹ * (ξ ^ k) x ∈ Subgroup.center P) :
    x ∈ Subgroup.center P := by
  classical
  letI : CommGroup ↥(Subgroup.center P) :=
    { (inferInstance : Group ↥(Subgroup.center P)) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp b.2) (a : P)) }
  set z : ↥(Subgroup.center P) := ⟨x⁻¹ * (ξ ^ k) x, hx⟩ with hz
  -- ## Step 1: the cocycle identity and the vanishing norm
  have hzP : (z : P) = x⁻¹ * (ξ ^ k) x := rfl
  have hxz : (ξ ^ k) x = x * (z : P) := by rw [hzP]; group
  have hmemZ : ∀ i : ℕ, x⁻¹ * ((ξ ^ k) ^ i) x ∈ Subgroup.center P := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        have h1 : ((ξ ^ k) ^ (i + 1)) x = ((ξ ^ k) ^ i) x * ((ξ ^ k) ^ i) (z : P) := by
          rw [pow_succ, MulAut.mul_apply, hxz, map_mul]
        rw [h1, ← mul_assoc]
        exact (Subgroup.center P).mul_mem ih (mem_center_map ((ξ ^ k) ^ i) z.2)
  let ζ : ℕ → ↥(Subgroup.center P) := fun i => ⟨x⁻¹ * ((ξ ^ k) ^ i) x, hmemZ i⟩
  have hζsucc : ∀ i : ℕ,
      ζ (i + 1) = ζ i * (⟨((ξ ^ k) ^ i) (z : P), mem_center_map ((ξ ^ k) ^ i) z.2⟩ :
        ↥(Subgroup.center P)) := by
    intro i
    refine Subtype.ext ?_
    show x⁻¹ * ((ξ ^ k) ^ (i + 1)) x =
      (x⁻¹ * ((ξ ^ k) ^ i) x) * ((ξ ^ k) ^ i) (z : P)
    rw [show ((ξ ^ k) ^ (i + 1)) x = ((ξ ^ k) ^ i) x * ((ξ ^ k) ^ i) (z : P) from by
      rw [pow_succ, MulAut.mul_apply, hxz, map_mul]]
    group
  have hζprod : ∀ i : ℕ, ζ i = ∏ j ∈ Finset.range i,
      (⟨((ξ ^ k) ^ j) (z : P), mem_center_map ((ξ ^ k) ^ j) z.2⟩ : ↥(Subgroup.center P)) := by
    intro i
    induction i with
    | zero => refine Subtype.ext ?_; simp [ζ]
    | succ i ih => rw [hζsucc, ih, Finset.prod_range_succ]
  have hζM : ζ (orderOf (ξ ^ k)) = 1 := by
    refine Subtype.ext ?_
    show x⁻¹ * ((ξ ^ k) ^ (orderOf (ξ ^ k))) x = 1
    rw [pow_orderOf_eq_one]
    simp
  have hnormM : ∏ j ∈ Finset.range (orderOf (ξ ^ k)),
      (⟨((ξ ^ k) ^ j) (z : P), mem_center_map ((ξ ^ k) ^ j) z.2⟩ : ↥(Subgroup.center P)) = 1 := by
    rw [← hζprod, hζM]
  -- ## Step 2: replace the norm over `orderOf (ξ ^ k)` by the norm over `orderOf σ`
  set σ : MulAut ↥(Subgroup.center P) := xiOnCenter ξ k with hσ
  have hσcoe : ∀ a : ↥(Subgroup.center P), ((σ a : ↥(Subgroup.center P)) : P) = (ξ ^ k) (a : P) := by
    intro a; rw [hσ]; exact xiOnCenter_coe ξ k a
  have hσpow : ∀ (i : ℕ) (a : ↥(Subgroup.center P)), ((σ ^ i) a : P) = ((ξ ^ k) ^ i) (a : P) := by
    intro i a; rw [hσ]; exact xiOnCenter_pow_coe ξ k i a
  have hnormMσ : ∏ j ∈ Finset.range (orderOf (ξ ^ k)), (σ ^ j) z = 1 := by
    rw [← hnormM]
    exact Finset.prod_congr rfl (fun j _ => Subtype.ext (by rw [hσpow]))
  have hdvd : orderOf σ ∣ orderOf (ξ ^ k) := by
    have hpow : σ ^ orderOf (ξ ^ k) = 1 := by
      ext a
      show (((σ ^ orderOf (ξ ^ k)) a : ↥(Subgroup.center P)) : P) =
        ((a : ↥(Subgroup.center P)) : P)
      rw [hσpow, pow_orderOf_eq_one]
      simp
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  set t : ℕ := orderOf (ξ ^ k) / orderOf σ with htdef
  have ht : orderOf (ξ ^ k) = orderOf σ * t := by
    rw [htdef, Nat.mul_div_cancel' hdvd]
  have hper : ∀ j : ℕ, (σ ^ (orderOf σ + j)) z = (σ ^ j) z := by
    intro j
    rw [pow_add, MulAut.mul_apply, pow_orderOf_eq_one]
    rfl
  have hgp : ∀ m : ℕ, ∏ j ∈ Finset.range (orderOf σ * m), (σ ^ j) z =
      (∏ j ∈ Finset.range (orderOf σ), (σ ^ j) z) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hsplit : orderOf σ * (m + 1) = orderOf σ + orderOf σ * m := by ring
        have hshift : ∏ j ∈ Finset.range (orderOf σ * m), (σ ^ (orderOf σ + j)) z =
            ∏ j ∈ Finset.range (orderOf σ * m), (σ ^ j) z :=
          Finset.prod_congr rfl (fun j _ => hper j)
        rw [hsplit, Finset.prod_range_add, hshift, ih, pow_succ']
  have hnormσ : (∏ j ∈ Finset.range (orderOf σ), (σ ^ j) z) ^ t = 1 := by
    rw [ht, hgp t] at hnormMσ
    exact hnormMσ
  -- ## Step 3: the coprimality input and the norm lemma
  have hZ2 : ∃ n : ℕ, Nat.card ↥(Subgroup.center P) = 2 ^ n :=
    (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup (Subgroup.center P))
  have hcopM : (orderOf (ξ ^ k)).Coprime (Nat.card ↥(Subgroup.center P)) := by
    obtain ⟨n, hn⟩ := hZ2
    rw [hn]
    have h1 : orderOf (ξ ^ k) ∣ 2 ^ n - 1 := by
      have h3 : Nat.card ↥(Subgroup.center P) - 1 = 2 ^ n - 1 := by rw [hn]
      rw [← h3, ← hξ.order]
      exact orderOf_pow_dvd k
    have h2 : (2 ^ n - 1).Coprime (2 ^ n) :=
      (Nat.coprime_self_sub_left (Nat.one_le_two_pow (n := n))).mpr (Nat.coprime_one_left _)
    exact h2.coprime_dvd_left h1
  have hcopt : t.Coprime (Nat.card ↥(Subgroup.center P)) :=
    hcopM.coprime_dvd_left ⟨orderOf σ, by rw [mul_comm, ← ht]⟩
  have hcopσ : (orderOf σ).Coprime (Nat.card ↥(Subgroup.center P)) :=
    hcopM.coprime_dvd_left hdvd
  -- the norm over `orderOf σ` vanishes, hence `z` is a coboundary
  have hnormσ1 : ∏ j ∈ Finset.range (orderOf σ), (σ ^ j) z = 1 := by
    have hinj := hcopt.symm.pow_left_bijective.injective
    refine hinj ?_
    show (∏ j ∈ Finset.range (orderOf σ), (σ ^ j) z) ^ t = 1 ^ t
    rw [hnormσ, one_pow]
  obtain ⟨n, hn⟩ := mulAut_norm_im σ hcopσ z hnormσ1
  -- ## Step 4: conclude
  have hnP : (ξ ^ k) (n : P) = (z : P) * (n : P) := by
    have h2 := congrArg (fun u : ↥(Subgroup.center P) => (u : P)) hn
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσcoe] at h2
    calc (ξ ^ k) (n : P) = ((ξ ^ k) (n : P) * (n : P)⁻¹) * (n : P) := by group
      _ = (z : P) * (n : P) := by rw [h2]
  have hfix : (ξ ^ k) (x * (n : P)⁻¹) = x * (n : P)⁻¹ := by
    have hc : ∀ y : P, (z : P) * y = y * (z : P) :=
      fun y => (Subgroup.mem_center_iff.mp z.2 y).symm
    calc (ξ ^ k) (x * (n : P)⁻¹)
        = (ξ ^ k) x * ((ξ ^ k) (n : P))⁻¹ := by rw [map_mul, map_inv]
      _ = x * (z : P) * ((z : P) * (n : P))⁻¹ := by rw [hxz, hnP]
      _ = x * (n : P)⁻¹ := by
          rw [mul_inv_rev]
          calc x * (z : P) * ((n : P)⁻¹ * (z : P)⁻¹)
              = x * ((z : P) * (n : P)⁻¹) * (z : P)⁻¹ := by group
            _ = x * ((n : P)⁻¹ * (z : P)) * (z : P)⁻¹ := by rw [hc (n : P)⁻¹]
            _ = x * (n : P)⁻¹ := by group
  have h1 : x * (n : P)⁻¹ = 1 := hξ.fpf k hk (x * (n : P)⁻¹) hfix
  have hxeq : x = (n : P) := by
    calc x = x * (n : P)⁻¹ * (n : P) := by group
      _ = 1 * (n : P) := by rw [h1]
      _ = (n : P) := by simp
  rw [hxeq]
  exact n.2

end Work.Higman
