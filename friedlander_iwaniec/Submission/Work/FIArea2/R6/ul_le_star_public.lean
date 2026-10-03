import Mathlib
import Submission.Work.FIArea2.R6.rect_quad_defs

namespace Work.FIArea2.R6
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## The reduction `UL ≤ (S/D)·Star` -/

private def gfun (v : ℤ × ℤ) : ℕ := Nat.gcd v.1.natAbs v.2.natAbs

private def wfun (v : ℤ × ℤ) : ℤ × ℤ := (v.1 / (gfun v : ℤ), v.2 / (gfun v : ℤ))

private lemma ite_split5 (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s]
    (t : Prop) [Decidable t] :
    (if p ∧ q ∧ r ∧ s ∧ t then (1:ℝ) else 0)
      = (if p ∧ q ∧ r ∧ s then (if t then (1:ℝ) else 0) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    by_cases ht : t <;> simp_all

private lemma ite_nest4 (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s]
    (g : ℝ) :
    (if p ∧ q ∧ r ∧ s then g else 0)
      = (if p then (if q then (if r then (if s then g else 0) else 0) else 0) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;> simp_all

private lemma ite_and' (p q : Prop) [Decidable p] [Decidable q] (a : ℝ) :
    (if p ∧ q then a else 0) = (if p then (if q then a else 0) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

private lemma sum_prod_eq (s t : Finset ℤ) (g : ℤ → ℤ → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, g x y) = ∑ p ∈ s.product t, g p.1 p.2 :=
  (Finset.sum_product (s := s) (t := t) (f := fun p : ℤ × ℤ => g p.1 p.2)).symm

private lemma sum4_reorder (s1 s2 s3 s4 : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, f a b c d)
      = ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, f a b c d := by
  have h1 : (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, f a b c d)
      = ∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, ∑ d ∈ s4, f a b c d := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : (∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, ∑ d ∈ s4, f a b c d)
      = ∑ c ∈ s3, ∑ a ∈ s1, ∑ b ∈ s2, ∑ d ∈ s4, f a b c d := Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]

private lemma ext1 (s1 s2 s3 s4 : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, (if a ≠ 0 then f a b c d else 0))
      = ∑ a ∈ s1.filter (fun x => x ≠ 0), ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, f a b c d := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : a ≠ 0
  · rw [if_pos h]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact Finset.sum_congr rfl (fun d _ => by rw [if_pos h])
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    refine Finset.sum_eq_zero (fun c _ => ?_)
    exact Finset.sum_eq_zero (fun d _ => by rw [if_neg h])

private lemma ext2 (s1 s2 s3 s4 : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, (if b ≠ 0 then f a b c d else 0))
      = ∑ a ∈ s1, ∑ b ∈ s2.filter (fun x => x ≠ 0), ∑ c ∈ s3, ∑ d ∈ s4, f a b c d := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases h : b ≠ 0
  · rw [if_pos h]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact Finset.sum_congr rfl (fun d _ => by rw [if_pos h])
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    exact Finset.sum_eq_zero (fun d _ => by rw [if_neg h])

private lemma ext3 (s1 s2 s3 s4 : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, (if c ≠ 0 then f a b c d else 0))
      = ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3.filter (fun x => x ≠ 0), ∑ d ∈ s4, f a b c d := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h : c ≠ 0
  · rw [if_pos h]
    exact Finset.sum_congr rfl (fun d _ => by rw [if_pos h])
  · rw [if_neg h]
    exact Finset.sum_eq_zero (fun d _ => by rw [if_neg h])

private lemma ext4 (s1 s2 s3 s4 : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, (if d ≠ 0 then f a b c d else 0))
      = ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4.filter (fun x => x ≠ 0), f a b c d := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_filter]

private lemma gfun_pos {v : ℤ × ℤ} (h : v.1 ≠ 0) : 0 < gfun v := by
  unfold gfun
  exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr h)

private lemma gfun_dvd_fst (v : ℤ × ℤ) : (gfun v : ℤ) ∣ v.1 := by
  rw [← Int.dvd_natAbs]
  exact Nat.cast_dvd_cast (Nat.gcd_dvd_left v.1.natAbs v.2.natAbs)

private lemma gfun_dvd_snd (v : ℤ × ℤ) : (gfun v : ℤ) ∣ v.2 := by
  rw [← Int.dvd_natAbs]
  exact Nat.cast_dvd_cast (Nat.gcd_dvd_right v.1.natAbs v.2.natAbs)

private lemma gmul_wfst (v : ℤ × ℤ) : (gfun v : ℤ) * (wfun v).1 = v.1 := by
  unfold wfun
  exact Int.mul_ediv_cancel' (gfun_dvd_fst v)

private lemma gmul_wsnd (v : ℤ × ℤ) : (gfun v : ℤ) * (wfun v).2 = v.2 := by
  unfold wfun
  exact Int.mul_ediv_cancel' (gfun_dvd_snd v)

private lemma wfun_fst_ne {v : ℤ × ℤ} (h : v.1 ≠ 0) : (wfun v).1 ≠ 0 := by
  intro h0
  have h1 := gmul_wfst v
  rw [h0, mul_zero] at h1
  exact h h1.symm

private lemma wfun_snd_ne {v : ℤ × ℤ} (h : v.2 ≠ 0) : (wfun v).2 ≠ 0 := by
  intro h0
  have h1 := gmul_wsnd v
  rw [h0, mul_zero] at h1
  exact h h1.symm

private lemma gfun_ne_zero {v : ℤ × ℤ} (h : v.1 ≠ 0) : (gfun v : ℤ) ≠ 0 := by
  have hg := gfun_pos h
  exact_mod_cast (Nat.pos_iff_ne_zero.mp hg)

private lemma wfun_prim {v : ℤ × ℤ} (h : v.1 ≠ 0) :
    Nat.gcd (wfun v).1.natAbs (wfun v).2.natAbs = 1 := by
  have hg : 0 < gfun v := gfun_pos h
  have h1 : (wfun v).1.natAbs = v.1.natAbs / gfun v := by
    unfold wfun gfun
    exact Int.natAbs_ediv_of_dvd (gfun_dvd_fst v)
  have h2 : (wfun v).2.natAbs = v.2.natAbs / gfun v := by
    unfold wfun gfun
    exact Int.natAbs_ediv_of_dvd (gfun_dvd_snd v)
  rw [h1, h2]
  unfold gfun at hg
  exact (Nat.coprime_div_gcd_div_gcd hg).gcd_eq_one

private lemma mem_nzB_le {S : ℕ} {x : ℤ} (hx : x ∈ nzB S) : x.natAbs ≤ S := by
  rw [nzB, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨ha, hb⟩, _⟩ := hx
  have h : |x| ≤ (S : ℤ) := abs_le.mpr ⟨ha, hb⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

private lemma nzB_ne {S : ℕ} {y : ℤ} (hy : y ∈ nzB S) : y ≠ 0 :=
  (Finset.mem_filter.mp hy).2

private lemma mem_nzB_of_natAbs_le {S : ℕ} {x : ℤ} (h : x.natAbs ≤ S) (hx : x ≠ 0) :
    x ∈ nzB S := by
  have h' : |x| ≤ (S : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h
  obtain ⟨ha, hb⟩ := abs_le.mp h'
  rw [nzB, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨ha, hb⟩, hx⟩

private lemma wfun_natAbs_le {S : ℕ} {v : ℤ × ℤ} (hv1 : v.1 ∈ nzB S) (hv2 : v.2 ∈ nzB S) :
    (wfun v).1.natAbs ≤ S ∧ (wfun v).2.natAbs ≤ S := by
  have hv1n : v.1 ≠ 0 := nzB_ne hv1
  have g1 : 1 ≤ gfun v := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (gfun_pos hv1n))
  have hnat1 : gfun v * (wfun v).1.natAbs = v.1.natAbs := by
    have h := congrArg Int.natAbs (gmul_wfst v)
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h
  have hnat2 : gfun v * (wfun v).2.natAbs = v.2.natAbs := by
    have h := congrArg Int.natAbs (gmul_wsnd v)
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h
  constructor
  · calc (wfun v).1.natAbs ≤ gfun v * (wfun v).1.natAbs := by
          simpa using Nat.mul_le_mul_right ((wfun v).1.natAbs) g1
      _ = v.1.natAbs := hnat1
      _ ≤ S := mem_nzB_le hv1
  · calc (wfun v).2.natAbs ≤ gfun v * (wfun v).2.natAbs := by
          simpa using Nat.mul_le_mul_right ((wfun v).2.natAbs) g1
      _ = v.2.natAbs := hnat2
      _ ≤ S := mem_nzB_le hv2

private lemma gfun_mul_le {S : ℕ} {v : ℤ × ℤ} (hv1 : v.1 ∈ nzB S) (hv2 : v.2 ∈ nzB S) :
    gfun v * max (wfun v).1.natAbs (wfun v).2.natAbs ≤ S := by
  have ha : gfun v * (wfun v).1.natAbs = v.1.natAbs := by
    have h := congrArg Int.natAbs (gmul_wfst v)
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h
  have hb : gfun v * (wfun v).2.natAbs = v.2.natAbs := by
    have h := congrArg Int.natAbs (gmul_wsnd v)
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h
  rw [mul_max, ha, hb]
  exact max_le (mem_nzB_le hv1) (mem_nzB_le hv2)

private lemma Q_wfun (h1 h2 : ℤ) (v : ℤ × ℤ) (hv : v.1 ≠ 0) :
    (wfun v).1 * h1^2 - (wfun v).2 * h2^2 = (h1^2 * v.1 - h2^2 * v.2) / (gfun v : ℤ) := by
  have hg : (gfun v : ℤ) ≠ 0 := gfun_ne_zero hv
  have hdvd : (gfun v : ℤ) ∣ (h1^2 * v.1 - h2^2 * v.2) :=
    ⟨(wfun v).1 * h1^2 - (wfun v).2 * h2^2, by rw [← gmul_wfst v, ← gmul_wsnd v]; ring⟩
  have hprod : (gfun v : ℤ) * ((wfun v).1 * h1^2 - (wfun v).2 * h2^2)
      = h1^2 * v.1 - h2^2 * v.2 := by
    rw [← gmul_wfst v, ← gmul_wsnd v]; ring
  exact mul_left_cancel₀ hg (by rw [hprod, Int.mul_ediv_cancel' hdvd])

private lemma wfun_Q_ne {h1 h2 : ℤ} {v : ℤ × ℤ} (hv : v.1 ≠ 0)
    (h : h1^2 * v.1 - h2^2 * v.2 ≠ 0) :
    (wfun v).1 * h1^2 - (wfun v).2 * h2^2 ≠ 0 := by
  intro h0
  have hdvd : (gfun v : ℤ) ∣ (h1^2 * v.1 - h2^2 * v.2) :=
    ⟨(wfun v).1 * h1^2 - (wfun v).2 * h2^2, by rw [← gmul_wfst v, ← gmul_wsnd v]; ring⟩
  have hprod : (gfun v : ℤ) * ((wfun v).1 * h1^2 - (wfun v).2 * h2^2)
      = h1^2 * v.1 - h2^2 * v.2 := by
    rw [← gmul_wfst v, ← gmul_wsnd v]; ring
  refine h ?_
  rw [← hprod, h0, mul_zero]

set_option maxHeartbeats 1000000 in
private lemma UL_eq (D S X Y : ℕ) :
    UL D S X Y
      = ∑ h1 ∈ nzB X, ∑ h2 ∈ nzB Y, ∑ v1 ∈ nzB S, ∑ v2 ∈ nzB S,
          (if (D : ℤ) ∣ h1 ^ 2 * v1 - h2 ^ 2 * v2 ∧ h1 ^ 2 * v1 - h2 ^ 2 * v2 ≠ 0
            then (1 : ℝ) else 0) := by
  unfold UL nzB
  have e : ∀ v1 v2 h1 h2 : ℤ,
      (if v1 ≠ 0 ∧ v2 ≠ 0 ∧ h1 ≠ 0 ∧ h2 ≠ 0
            ∧ ((D : ℤ) ∣ h1 ^ 2 * v1 - h2 ^ 2 * v2 ∧ h1 ^ 2 * v1 - h2 ^ 2 * v2 ≠ 0)
          then (1 : ℝ) else 0)
        = (if v1 ≠ 0 then (if v2 ≠ 0 then (if h1 ≠ 0 then (if h2 ≠ 0 then
            (if ((D : ℤ) ∣ h1 ^ 2 * v1 - h2 ^ 2 * v2 ∧ h1 ^ 2 * v1 - h2 ^ 2 * v2 ≠ 0)
              then (1 : ℝ) else 0) else 0) else 0) else 0) else 0) := by
    intro v1 v2 h1 h2
    rw [ite_split5 (v1 ≠ 0) (v2 ≠ 0) (h1 ≠ 0) (h2 ≠ 0)
      ((D : ℤ) ∣ h1 ^ 2 * v1 - h2 ^ 2 * v2 ∧ h1 ^ 2 * v1 - h2 ^ 2 * v2 ≠ 0)]
    exact ite_nest4 (v1 ≠ 0) (v2 ≠ 0) (h1 ≠ 0) (h2 ≠ 0) _
  simp_rw [e]
  set SS : Finset ℤ := Finset.Icc (-(S:ℤ)) (S:ℤ) with hSS
  set SX : Finset ℤ := Finset.Icc (-(X:ℤ)) (X:ℤ) with hSX
  set SY : Finset ℤ := Finset.Icc (-(Y:ℤ)) (Y:ℤ) with hSY
  set SS' : Finset ℤ := SS.filter (fun x => x ≠ 0) with hSS'
  set SX' : Finset ℤ := SX.filter (fun x => x ≠ 0) with hSX'
  set SY' : Finset ℤ := SY.filter (fun x => x ≠ 0) with hSY'
  set G : ℤ → ℤ → ℤ → ℤ → ℝ :=
    (fun v1 v2 h1 h2 => (if (D : ℤ) ∣ h1 ^ 2 * v1 - h2 ^ 2 * v2 ∧ h1 ^ 2 * v1 - h2 ^ 2 * v2 ≠ 0
      then (1 : ℝ) else 0)) with hG
  rw [ext1 SS SS SX SY (fun v1 v2 h1 h2 => (if v2 ≠ 0 then (if h1 ≠ 0 then (if h2 ≠ 0 then
        G v1 v2 h1 h2 else 0) else 0) else 0))]
  rw [ext2 SS' SS SX SY (fun v1 v2 h1 h2 => (if h1 ≠ 0 then (if h2 ≠ 0 then
        G v1 v2 h1 h2 else 0) else 0))]
  rw [ext3 SS' SS' SX SY (fun v1 v2 h1 h2 => (if h2 ≠ 0 then G v1 v2 h1 h2 else 0))]
  rw [ext4 SS' SS' SX' SY G]
  rw [sum4_reorder SS' SS' SX' (SY.filter (fun x => x ≠ 0)) G]

private lemma dvd_of_dvd_mul_gcd {D Q g : ℕ} (hD : 0 < D) (h : D ∣ g * Q) :
    D / Nat.gcd D Q ∣ g := by
  set c := Nat.gcd D Q with hc
  have hcd : c ∣ D := Nat.gcd_dvd_left _ _
  have hcq : c ∣ Q := Nat.gcd_dvd_right _ _
  have hcpos : 0 < c := Nat.gcd_pos_of_pos_left Q hD
  obtain ⟨k, hk⟩ := h
  have h3 : c * (D / c) ∣ c * (g * (Q / c)) := by
    refine ⟨k, ?_⟩
    have hD' : c * (D / c) = D := Nat.mul_div_cancel' hcd
    have hQ' : c * (Q / c) = Q := Nat.mul_div_cancel' hcq
    rw [hD', show c * (g * (Q / c)) = g * (c * (Q / c)) from by ring, hQ']
    exact hk
  have h2 : D / c ∣ g * (Q / c) := (Nat.mul_dvd_mul_iff_left hcpos).mp h3
  have hcop : Nat.Coprime (D / c) (Q / c) := by
    rw [hc]; exact Nat.coprime_div_gcd_div_gcd hcpos
  exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h2)

private lemma dvd_of_dvd_mul_gcd' {D Q g : ℕ} (hD : 0 < D) (h : D ∣ g * Q) :
    D / Nat.gcd D Q ∣ g := dvd_of_dvd_mul_gcd hD h

/-- Per-`(h₁,h₂)` fiber bound. -/
private lemma fiber_bound (D : ℕ) (hD : 1 ≤ D) (S : ℕ) (h1 h2 : ℤ) :
    (∑ v1 ∈ nzB S, ∑ v2 ∈ nzB S,
        (if (D:ℤ) ∣ h1^2 * v1 - h2^2 * v2 ∧ h1^2 * v1 - h2^2 * v2 ≠ 0 then (1:ℝ) else 0))
      ≤ (S:ℝ)/(D:ℝ) * (∑ w1 ∈ nzB S, ∑ w2 ∈ nzB S,
          (if Nat.gcd w1.natAbs w2.natAbs = 1 ∧ w1*h1^2 - w2*h2^2 ≠ 0
            then (1:ℝ)/((max w1.natAbs w2.natAbs:ℕ):ℝ)
              * (Nat.gcd D (w1*h1^2 - w2*h2^2).natAbs : ℝ)
            else 0)) := by
  classical
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  set V : Finset (ℤ × ℤ) := ((nzB S).product (nzB S)).filter
      (fun v : ℤ × ℤ => (D:ℤ) ∣ h1^2*v.1 - h2^2*v.2 ∧ h1^2*v.1 - h2^2*v.2 ≠ 0) with hV
  set W : Finset (ℤ × ℤ) := ((nzB S).product (nzB S)).filter
      (fun w : ℤ × ℤ => Nat.gcd w.1.natAbs w.2.natAbs = 1) with hW
  have hLHS : (∑ v1 ∈ nzB S, ∑ v2 ∈ nzB S,
        (if (D:ℤ) ∣ h1^2*v1 - h2^2*v2 ∧ h1^2*v1 - h2^2*v2 ≠ 0 then (1:ℝ) else 0))
      = (V.card : ℝ) := by
    rw [sum_prod_eq, Finset.sum_boole]
  have hRHS : (∑ w1 ∈ nzB S, ∑ w2 ∈ nzB S,
          (if Nat.gcd w1.natAbs w2.natAbs = 1 ∧ w1*h1^2 - w2*h2^2 ≠ 0
            then (1:ℝ)/((max w1.natAbs w2.natAbs:ℕ):ℝ)
              * (Nat.gcd D (w1*h1^2 - w2*h2^2).natAbs : ℝ)
            else 0))
      = ∑ w ∈ W, (if w.1*h1^2 - w.2*h2^2 ≠ 0
            then (1:ℝ)/((max w.1.natAbs w.2.natAbs:ℕ):ℝ)
              * (Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℝ)
            else 0) := by
    rw [sum_prod_eq]
    simp_rw [ite_and']
    rw [← Finset.sum_filter]
  rw [hLHS, hRHS]
  have hVmem : ∀ v ∈ V, v.1 ∈ nzB S ∧ v.2 ∈ nzB S := by
    intro v hv
    rw [hV, Finset.mem_filter] at hv
    exact Finset.mem_product.mp hv.1
  have hWmem : ∀ w ∈ W, w.1 ∈ nzB S ∧ w.2 ∈ nzB S := by
    intro w hw
    rw [hW, Finset.mem_filter] at hw
    exact Finset.mem_product.mp hw.1
  have hmap : Set.MapsTo wfun ↑V ↑W := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hVmem v hv
    have hv1n : v.1 ≠ 0 := nzB_ne hv1
    have hv2n : v.2 ≠ 0 := nzB_ne hv2
    have hle := wfun_natAbs_le hv1 hv2
    rw [hW, Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr
      ⟨mem_nzB_of_natAbs_le hle.1 (wfun_fst_ne hv1n),
       mem_nzB_of_natAbs_le hle.2 (wfun_snd_ne hv2n)⟩, wfun_prim hv1n⟩
  have hcard : V.card = ∑ w ∈ W, (V.filter (fun v => wfun v = w)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  rw [hcard]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun w hw => ?_)
  obtain ⟨hw1, hw2⟩ := hWmem w hw
  by_cases hQ : w.1 * h1^2 - w.2 * h2^2 = 0
  · have hcard0 : (V.filter (fun v => wfun v = w)).card = 0 := by
      have hsub : V.filter (fun v => wfun v = w) ⊆ (∅ : Finset (ℤ × ℤ)) := by
        intro v hv
        exfalso
        rw [Finset.mem_filter] at hv
        obtain ⟨hvV, hvw⟩ := hv
        have hne : h1^2*v.1 - h2^2*v.2 ≠ 0 :=
          (Finset.mem_filter.mp hvV).2.2
        have hv1n : v.1 ≠ 0 := nzB_ne (hVmem v hvV).1
        have hq := wfun_Q_ne hv1n hne
        rw [hvw] at hq
        exact hq hQ
      exact Nat.eq_zero_of_le_zero (by simpa using Finset.card_le_card hsub)
    rw [hcard0]
    have hne' : ¬ (w.1 * h1^2 - w.2 * h2^2 ≠ 0) := by rw [hQ]; simp
    rw [if_neg hne']
    simp
  · rw [if_pos hQ]
    set K := S / max w.1.natAbs w.2.natAbs with hK
    set dstar := D / Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs with hds
    have hmaxpos : 0 < max w.1.natAbs w.2.natAbs := by
      have h1n : w.1 ≠ 0 := nzB_ne hw1
      have : 0 < w.1.natAbs := Int.natAbs_pos.mpr h1n
      exact lt_of_lt_of_le this (le_max_left _ _)
    have hQnat : 0 < (w.1*h1^2 - w.2*h2^2).natAbs := Int.natAbs_pos.mpr hQ
    have hdstarpos : 0 < dstar := by
      rw [hds]
      exact Nat.div_pos (Nat.gcd_le_left _ hDpos) (Nat.gcd_pos_of_pos_left _ hDpos)
    have hbnd : (V.filter (fun v => wfun v = w)).card
        ≤ ((Finset.Icc 1 K).filter (fun g => dstar ∣ g)).card := by
      refine Finset.card_le_card_of_injOn (fun v => gfun v) ?_ ?_
      · intro v hv
        rw [Finset.mem_coe, Finset.mem_filter] at hv
        obtain ⟨hvV, hvw⟩ := hv
        obtain ⟨hv1, hv2⟩ := hVmem v hvV
        have hv1n : v.1 ≠ 0 := nzB_ne hv1
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (gfun_pos hv1n)), ?_⟩, ?_⟩
        · rw [hK, Nat.le_div_iff_mul_le hmaxpos]
          have hgl := gfun_mul_le hv1 hv2
          rwa [hvw] at hgl
        · rw [hds]
          apply dvd_of_dvd_mul_gcd hDpos
          have hvV' : v ∈ ((nzB S).product (nzB S)).filter
              (fun v : ℤ × ℤ => (D:ℤ) ∣ h1^2*v.1 - h2^2*v.2 ∧ h1^2*v.1 - h2^2*v.2 ≠ 0) := by
            rw [hV] at hvV; exact hvV
          have hdvd : (D:ℤ) ∣ h1^2*v.1 - h2^2*v.2 := (Finset.mem_filter.mp hvV').2.1
          have hnat : D ∣ (h1^2*v.1 - h2^2*v.2).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
          have hfac : (h1^2*v.1 - h2^2*v.2).natAbs
              = gfun v * ((wfun v).1 * h1^2 - (wfun v).2 * h2^2).natAbs := by
            have h2'' : h1^2*v.1 - h2^2*v.2
                = (gfun v : ℤ) * ((wfun v).1 * h1^2 - (wfun v).2 * h2^2) := by
              rw [← gmul_wfst v, ← gmul_wsnd v]; ring
            rw [h2'', Int.natAbs_mul, Int.natAbs_natCast]
          rw [hfac] at hnat
          rwa [hvw] at hnat
      · intro v hv v' hv' hgg
        rw [Finset.mem_coe, Finset.mem_filter] at hv hv'
        obtain ⟨hvV, hvw⟩ := hv
        obtain ⟨hv'V, hv'w⟩ := hv'
        have e1a : v.1 = (gfun v : ℤ) * w.1 := by rw [← gmul_wfst v, hvw]
        have e1b : (gfun v : ℤ) * w.1 = (gfun v' : ℤ) * w.1 := congrArg (fun k : ℕ => (k:ℤ) * w.1) hgg
        have e1c : (gfun v' : ℤ) * w.1 = (gfun v' : ℤ) * (wfun v').1 := by rw [← hv'w]
        have e1 : v.1 = v'.1 := e1a.trans (e1b.trans (e1c.trans (gmul_wfst v')))
        have e2a : v.2 = (gfun v : ℤ) * w.2 := by rw [← gmul_wsnd v, hvw]
        have e2b : (gfun v : ℤ) * w.2 = (gfun v' : ℤ) * w.2 := congrArg (fun k : ℕ => (k:ℤ) * w.2) hgg
        have e2c : (gfun v' : ℤ) * w.2 = (gfun v' : ℤ) * (wfun v').2 := by rw [← hv'w]
        have e2 : v.2 = v'.2 := e2a.trans (e2b.trans (e2c.trans (gmul_wsnd v')))
        exact Prod.ext e1 e2
    have hcount : ((Finset.Icc 1 K).filter (fun g => dstar ∣ g)).card = K / dstar := by
      have himg : (Finset.Icc 1 K).filter (fun g => dstar ∣ g)
          = (Finset.Icc 1 (K / dstar)).image (fun t => dstar * t) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hg1, hg2⟩, hmul⟩
          obtain ⟨t, ht⟩ := hmul
          have ht1 : 1 ≤ t := by
            rcases Nat.eq_zero_or_pos t with h | h
            · subst h; rw [mul_zero] at ht; omega
            · exact h
          refine ⟨t, ⟨ht1, ?_⟩, ht.symm⟩
          have hK' : dstar * t ≤ K := by rw [← ht]; exact hg2
          have h2' : t * dstar ≤ K := by rwa [mul_comm] at hK'
          rwa [Nat.le_div_iff_mul_le hdstarpos]
        · rintro ⟨t, ⟨ht1, ht2⟩, ht⟩
          rw [← ht]
          refine ⟨⟨?_, ?_⟩, ⟨t, rfl⟩⟩
          · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
              (Nat.pos_iff_ne_zero.mp hdstarpos) (Nat.pos_iff_ne_zero.mp ht1))
          · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hdstarpos).mp ht2
      rw [himg, Finset.card_image_of_injective _
        (fun a b h => Nat.mul_left_cancel hdstarpos h), Nat.card_Icc, Nat.add_sub_cancel]
    have hdsteq : ((dstar:ℕ):ℝ)
        = (D:ℝ)/((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs:ℕ):ℝ) := by
      rw [hds]
      exact Nat.cast_div (Nat.gcd_dvd_left _ _) (by
        have := Nat.gcd_pos_of_pos_left (w.1*h1^2 - w.2*h2^2).natAbs hDpos
        exact_mod_cast this.ne')
    have step1 : ((V.filter (fun v => wfun v = w)).card : ℝ)
        ≤ (((Finset.Icc 1 K).filter (fun g => dstar ∣ g)).card : ℝ) := by
      exact_mod_cast hbnd
    have step2 : (((Finset.Icc 1 K).filter (fun g => dstar ∣ g)).card : ℝ)
        ≤ (K:ℝ) * ((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ) / (D:ℝ) := by
      rw [hcount]
      calc (((K / dstar : ℕ) : ℝ)) ≤ (K:ℝ)/(dstar:ℝ) := Nat.cast_div_le
        _ = (K:ℝ) * ((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ) / (D:ℝ) := by
            rw [hdsteq]; field_simp
    refine le_trans step1 (le_trans step2 ?_)
    have hKle : (K:ℝ) ≤ (S:ℝ)/((max w.1.natAbs w.2.natAbs:ℕ):ℝ) := by
      rw [hK]; exact Nat.cast_div_le
    have hnn : (0:ℝ) ≤ ((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ)/(D:ℝ) := by
      positivity
    calc (K:ℝ) * ((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ) / (D:ℝ)
        = (K:ℝ) * (((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ)/(D:ℝ)) := by ring
      _ ≤ (S:ℝ)/((max w.1.natAbs w.2.natAbs:ℕ):ℝ)
            * (((Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℕ):ℝ)/(D:ℝ)) :=
          mul_le_mul_of_nonneg_right hKle hnn
      _ = (S:ℝ)/(D:ℝ) * (((1:ℝ)/(max ((w.1.natAbs:ℕ):ℝ) ((w.2.natAbs:ℕ):ℝ)))
            * (Nat.gcd D (w.1*h1^2 - w.2*h2^2).natAbs : ℝ)) := by
          rw [Nat.cast_max]; ring

theorem ul_le_star_public (D S X Y : ℕ) (hD : 1 ≤ D) :
    Work.FIArea2.R6.UL D S X Y ≤ (S : ℝ) / (D : ℝ) * Work.FIArea2.R6.Star D S X Y := by
  rw [UL_eq]
  unfold Star
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun h1 _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun h2 _ => fiber_bound D hD S h1 h2)


end
end Work.FIArea2.R6
