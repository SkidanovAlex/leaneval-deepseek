import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.coprimeInner

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Work.FIArea4

/-- Support of the scaled array inside the box `2⌈R/ρ⌉`. -/
lemma shiftCoef_support' {ρ R : ℕ} (hρ : 1 ≤ ρ) {α : ℕ → ℕ → ℂ}
    (hα : ∀ r s, α r s ≠ 0 → r ≤ 2*R) :
    ∀ r s, shiftCoef ρ α r s ≠ 0 → r ≤ 2*((R+ρ-1)/ρ) := by
  intro r s h
  rw [shiftCoef_apply] at h
  have h1 : ρ * r ≤ 2*R := hα (ρ*r) s h
  have h2 : R ≤ ((R+ρ-1)/ρ) * ρ := by
    have h6 : (R+ρ-1)/ρ * ρ + (R+ρ-1)%ρ = R+ρ-1 := by
      rw [mul_comm]; exact Nat.div_add_mod _ _
    have h7 : (R+ρ-1)%ρ ≤ ρ-1 := by
      have := Nat.mod_lt (R+ρ-1) (show 0 < ρ by omega); omega
    omega
  have h3 : r * ρ ≤ 2 * ((R+ρ-1)/ρ) * ρ := by nlinarith [h1, h2]
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- The class sum depends only on the values of `α` inside the box: shrinking the box (staying
above the support) does not change it. -/
lemma clsSum_support_eq {R R' S d a : ℕ} (hRR' : R' ≤ R) {α : ℕ → ℕ → ℂ}
    (h : ∀ r s, α r s ≠ 0 → r ≤ 2*R') :
    clsSum R S d α a = clsSum R' S d α a := by
  have hmain : (∑ x ∈ EvarCls R' S d a, α x.1 x.2 * jw d x.1)
      = ∑ x ∈ EvarCls R S d a, α x.1 x.2 * jw d x.1 := by
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      rw [mem_EvarCls] at hp ⊢
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hpIcc, hcop⟩ := mem_EvarR.mp hp1
      exact ⟨mem_EvarR.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hpIcc).1, by have := (Finset.mem_Icc.mp hpIcc).2; omega⟩,
        hcop⟩, hp2, hp3⟩
    · intro p hp hnp
      rw [mem_EvarCls] at hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hpIcc, hcop⟩ := mem_EvarR.mp hp1
      have hnpR : p.1 ∉ Finset.Icc 1 (2*R') := by
        intro hc
        exact hnp (mem_EvarCls.mpr ⟨mem_EvarR.mpr ⟨hc, hcop⟩, hp2, hp3⟩)
      have hbig : 2*R' < p.1 :=
        Nat.lt_of_not_le (fun hc => hnpR (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpIcc).1, hc⟩))
      have hz : α p.1 p.2 = 0 := by by_contra hc; exact absurd (h p.1 p.2 hc) (by omega)
      rw [hz, zero_mul]
  rw [clsSum, clsSum, hmain]

/-- `Evar` depends only on the values of `α` inside the box. -/
lemma Evar_support_eq {R R' S d : ℕ} (hRR' : R' ≤ R) {α : ℕ → ℕ → ℂ}
    (h : ∀ r s, α r s ≠ 0 → r ≤ 2*R') :
    Work.FIPlan.Evar R S d α = Work.FIPlan.Evar R' S d α := by
  rw [Evar_eq_sum_normSq_clsSum, Evar_eq_sum_normSq_clsSum]
  exact Finset.sum_congr rfl (fun a _ => by rw [clsSum_support_eq hRR' h])

/-- `p14L2` depends only on the values of `α` inside the box. -/
lemma L2_support_eq {R R' S : ℕ} (hRR' : R' ≤ R) {α : ℕ → ℕ → ℂ}
    (h : ∀ r s, α r s ≠ 0 → r ≤ 2*R') :
    p14L2 R S α = p14L2 R' S α := by
  rw [p14L2, p14L2]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · intro x hx hnx
    rw [Finset.mem_Icc] at hx
    refine Finset.sum_eq_zero (fun s _ => ?_)
    have hle : 2*R' < x := by
      by_contra hc
      exact hnx (by simp only [Finset.mem_Icc]; exact ⟨hx.1, by omega⟩)
    have hz : α x s = 0 := by by_contra hc; exact absurd (h x s hc) (by omega)
    rw [hz, Complex.normSq_zero]

/-- The `Evar`-sum over the dyadic range of `q` is bounded by `h11` applied to the scaled array. -/
lemma Evar_sum_le (h11 : p14Prop111All) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m Q R S ρ : ℕ) (β : ℕ → ℕ → ℂ),
      1 ≤ m → 1 ≤ Q → 1 ≤ R → 1 ≤ S → 1 ≤ ρ →
      (∀ r s, β r s ≠ 0 → r ≤ 2*R) →
      ∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β)
        ≤ C * p14T11 (m*Q) ((R+ρ-1)/ρ) S ε * p14L2 R S (shiftCoef ρ β) := by
  obtain ⟨C11, hC11pos, hC11⟩ := h11 ε hε
  refine ⟨C11, hC11pos, ?_⟩
  intro m Q R S ρ β hm hQ hR hS hρ hβ
  have hsupp : ∀ r s, shiftCoef ρ β r s ≠ 0 → r ≤ 2*((R+ρ-1)/ρ) :=
    shiftCoef_support' hρ hβ
  have hRR : (R+ρ-1)/ρ ≤ R := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < ρ)]
    have : R ≤ ρ * R := Nat.le_mul_of_pos_left R (by omega)
    omega
  have hRp : 1 ≤ (R+ρ-1)/ρ := by
    rw [Nat.one_le_div_iff (by omega)]
    omega
  have hstep1 : ∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β)
      = ∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar ((R+ρ-1)/ρ) S (m*q) (shiftCoef ρ β) :=
    Finset.sum_congr rfl (fun q _ => Evar_support_eq hRR hsupp)
  rw [hstep1]
  have hsub : (Finset.Ioc Q (2*Q)).image (fun q => m*q) ⊆ Finset.Ioc (m*Q) (2*(m*Q)) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    rw [Finset.mem_Ioc] at hq ⊢
    exact ⟨by nlinarith, by nlinarith⟩
  calc ∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar ((R+ρ-1)/ρ) S (m*q) (shiftCoef ρ β)
      = ∑ d ∈ (Finset.Ioc Q (2*Q)).image (fun q => m*q),
          Work.FIPlan.Evar ((R+ρ-1)/ρ) S d (shiftCoef ρ β) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Nat.mul_left_cancel (by omega) hab
    _ ≤ ∑ d ∈ Finset.Ioc (m*Q) (2*(m*Q)),
          Work.FIPlan.Evar ((R+ρ-1)/ρ) S d (shiftCoef ρ β) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun d _ _ => Evar_nonneg ((R+ρ-1)/ρ) S d (shiftCoef ρ β))
    _ = Work.FIPlan.Vvar ((R+ρ-1)/ρ) S (m*Q) (shiftCoef ρ β) := by rw [Work.FIPlan.Vvar]
    _ ≤ C11 * p14T11 (m*Q) ((R+ρ-1)/ρ) S ε
          * p14L2 ((R+ρ-1)/ρ) S (shiftCoef ρ β) :=
        hC11 (m*Q) ((R+ρ-1)/ρ) S (shiftCoef ρ β)
          (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hRp hS
    _ = C11 * p14T11 (m*Q) ((R+ρ-1)/ρ) S ε * p14L2 R S (shiftCoef ρ β) := by
        rw [L2_support_eq hRR hsupp]

end

end Work.FIArea4.Vflip.Vfd
