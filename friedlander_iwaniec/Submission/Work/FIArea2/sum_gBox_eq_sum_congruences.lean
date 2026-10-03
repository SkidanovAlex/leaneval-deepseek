import Mathlib
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea2.exists_cForm_eq_iff

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary lemmas for the re-parametrisation (6.7)

The square indicator `Zint b` counts the integer roots of `c² = b`; we need this counting form,
the multiplicativity of the count, and the evaluation of the `w`-sum with `w ↦ (c₁², c₂²)` fixed. -/

/-- `Zb m ≠ 0` iff `m` is a perfect square. -/
lemma Zb_ne_zero_iff (m : ℕ) : Work.FIPlan.Zb m ≠ 0 ↔ Nat.sqrt m ^ 2 = m := by
  unfold Work.FIPlan.Zb
  split_ifs with h1 h2 <;> simp_all

/-- `Nat.sqrt m ^ 2 = m` iff `m` is a perfect square. -/
lemma sqrt_sq_eq_iff (m : ℕ) : Nat.sqrt m ^ 2 = m ↔ ∃ k, k^2 = m := by
  constructor
  · intro h; exact ⟨Nat.sqrt m, h⟩
  · rintro ⟨k, hk⟩
    have h1 : k ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by nlinarith [hk])
    have h2 : Nat.sqrt m ≤ k := by
      rw [← Nat.lt_succ_iff, Nat.sqrt_lt']; nlinarith [hk]
    rw [le_antisymm h2 h1, hk]

/-- `Z(b) ≠ 0` iff `b` is a non-negative perfect square (with `Z(0) = 1`). -/
lemma Zint_ne_zero_iff (d : ℤ) : Work.FIPlan.Zint d ≠ 0 ↔ ∃ c : ℤ, c ^ 2 = d := by
  have hZint : Work.FIPlan.Zint d ≠ 0 ↔ 0 ≤ d ∧ Work.FIPlan.Zb d.natAbs ≠ 0 := by
    unfold Work.FIPlan.Zint
    by_cases h : d < 0
    · simp [h]
    · simp [h, not_lt.mp h]
  rw [hZint]
  constructor
  · rintro ⟨hge, hb⟩
    rw [Zb_ne_zero_iff, sqrt_sq_eq_iff] at hb
    obtain ⟨k, hk⟩ := hb
    refine ⟨(k:ℤ), ?_⟩
    have hcast : ((k:ℤ))^2 = ((k^2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, hk, Int.natAbs_of_nonneg hge]
  · rintro ⟨c, hc⟩
    have hge : 0 ≤ d := by nlinarith [sq_nonneg c, hc]
    refine ⟨hge, ?_⟩
    rw [Zb_ne_zero_iff, sqrt_sq_eq_iff]
    refine ⟨c.natAbs, ?_⟩
    have hc' : (c.natAbs : ℤ) ^ 2 = (d.natAbs : ℤ) := by
      rw [Int.natAbs_sq, hc, Int.natAbs_of_nonneg hge]
    exact_mod_cast hc'

/-- **Counting form of `Zint`.**  If every integer root of `c² = b` lies in `Icc (-K) K`, then
`Zint b` is the number of roots in that interval. -/
lemma Zint_eq_card_roots (K : ℕ) (b : ℤ)
    (hroot : ∀ c : ℤ, c ^ 2 = b → c ∈ Finset.Icc (-(K:ℤ)) (K:ℤ)) :
    Work.FIPlan.Zint b
      = ((Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun c => c ^ 2 = b)).card := by
  by_cases hb : b < 0
  · rw [Work.FIPlan.Zint_eq_zero_of_neg hb]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hc
    nlinarith [sq_nonneg c]
  · push Not at hb
    set m : ℕ := b.natAbs with hm
    have hmb : (m : ℤ) = b := by rw [hm]; exact Int.natAbs_of_nonneg hb
    rw [← hmb] at hroot ⊢
    have hZ : Work.FIPlan.Zint ((m:ℤ)) = Work.FIPlan.Zb m := by
      rw [Work.FIPlan.Zint, if_neg (by omega : ¬ (((m:ℤ)) < 0))]; rfl
    rw [hZ]
    by_cases hm0 : m = 0
    · rw [hm0, Work.FIPlan.Zb_zero]
      have hf : (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun c : ℤ => c ^ 2 = ((0:ℕ):ℤ)) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hc⟩; exact sq_eq_zero_iff.mp hc
        · intro hc; subst hc; exact ⟨by simp, by norm_num⟩
      rw [hf, Finset.card_singleton]
    · set s : ℕ := Nat.sqrt m with hs
      by_cases hsq : s ^ 2 = m
      · have hZb : Work.FIPlan.Zb m = 2 := by
          simp only [Work.FIPlan.Zb]; rw [if_neg hm0, if_pos (by rw [hs] at hsq; exact hsq)]
        rw [hZb]
        have hs2 : ((s:ℤ))^2 = (m:ℤ) := by
          have : ((s^2 : ℕ) : ℤ) = (m:ℤ) := by rw [hsq]
          simpa using this
        have hf : (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun c => c ^ 2 = (m:ℤ)) = {(s:ℤ), -(s:ℤ)} := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hc⟩
            have hcc : c^2 = ((s:ℤ))^2 := by rw [hc, hs2]
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcc with h | h
            · exact Or.inl h
            · exact Or.inr h
          · rintro (h | h)
            · subst h
              exact ⟨hroot (s:ℤ) (by rw [hs2]), by rw [hs2]⟩
            · subst h
              exact ⟨hroot (-(s:ℤ)) (by rw [neg_sq, hs2]), by rw [neg_sq, hs2]⟩
        rw [hf]
        have hsne : s ≠ 0 := by
          intro h; rw [h] at hsq; simp at hsq; exact hm0 hsq.symm
        have hne : (s:ℤ) ≠ -(s:ℤ) := by omega
        rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
      · have hZb : Work.FIPlan.Zb m = 0 := by
          simp only [Work.FIPlan.Zb]; rw [if_neg hm0, if_neg (by rw [hs] at hsq; exact hsq)]
        rw [hZb]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c _ hc
        have hc2 : c.natAbs ^ 2 = m := by
          have h := congrArg Int.natAbs hc
          rw [Int.natAbs_pow, Int.natAbs_natCast] at h
          simpa using h
        have hsqrt : Nat.sqrt m = c.natAbs := by
          rw [← hc2, pow_two, Nat.sqrt_eq]
        rw [hs] at hsq
        exact hsq (by rw [hsqrt, hc2])

/-- The number of roots of `c² = b` lying in `Icc (-K) K`, as a real sum of indicators. -/
def gBoxCnt (K : ℕ) (b : ℤ) : ℝ :=
  ∑ c ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), (if c^2 = b then (1:ℝ) else 0)

/-- The sum form of the counting lemma. -/
lemma Zint_eq_Cnt (K : ℕ) (b : ℤ)
    (hroot : ∀ c : ℤ, c ^ 2 = b → c ∈ Finset.Icc (-(K:ℤ)) (K:ℤ)) :
    (Work.FIPlan.Zint b : ℝ) = gBoxCnt K b := by
  rw [gBoxCnt, Finset.sum_boole, Zint_eq_card_roots K b hroot]

/-- If `b` is not a square then `gBoxCnt K b = 0`. -/
lemma Cnt_eq_zero_of_Zint_eq_zero (K : ℕ) (b : ℤ) (h : Work.FIPlan.Zint b = 0) :
    gBoxCnt K b = 0 := by
  rw [gBoxCnt]
  apply Finset.sum_eq_zero
  intro c _
  have hc : ¬ (c^2 = b) := fun hc => (Zint_ne_zero_iff b).mpr ⟨c, hc⟩ h
  rw [if_neg hc]

/-- **Multiplication of the square indicators.**  If the roots of both `b₁` and `b₂` are within
`Icc (-K) K` (as they are in the theorem, by `hK`), then `Z(b₁)Z(b₂)` equals the product of the
truncated root counts. -/
lemma Zint_mul_Cnt (K : ℕ) (b1 b2 : ℤ)
    (h : ∀ c1 c2 : ℤ, c1 ^ 2 = b1 → c2 ^ 2 = b2 →
      c1 ∈ Finset.Icc (-(K:ℤ)) (K:ℤ) ∧ c2 ∈ Finset.Icc (-(K:ℤ)) (K:ℤ)) :
    (Work.FIPlan.Zint b1 : ℝ) * (Work.FIPlan.Zint b2 : ℝ) = gBoxCnt K b1 * gBoxCnt K b2 := by
  by_cases h1 : Work.FIPlan.Zint b1 = 0
  · rw [h1, Cnt_eq_zero_of_Zint_eq_zero K b1 h1]; simp
  · by_cases h2 : Work.FIPlan.Zint b2 = 0
    · rw [h2, Cnt_eq_zero_of_Zint_eq_zero K b2 h2]; simp
    · obtain ⟨w1, hw1⟩ := (Zint_ne_zero_iff b1).mp h1
      obtain ⟨w2, hw2⟩ := (Zint_ne_zero_iff b2).mp h2
      rw [Zint_eq_Cnt K b1 (fun c hc => (h c w2 hc hw2).1),
          Zint_eq_Cnt K b2 (fun c hc => (h w1 c hw1 hc).2)]

/-- **The inner `w`-sum of (6.7) at a fixed square pair.**  Summing `f(|w|²)` over the `w` of the
box with `Re(wz₁) = c₁²`, `Re(wz₂) = c₂²` is summing over the unique `wOf z₁ z₂ c₁ c₂` — provided
the congruence `Δ ∣ c₁²z₂ − c₂²z₁` holds and that point lies in the box; otherwise the sum is `0`. -/
lemma sum_ite_cForm (R : ℤ) (f : ℤ → ℝ) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (c1 c2 : ℤ) :
    (∑ w ∈ Work.FIPlan.gBox R,
        (if Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2
          then f (Work.FIPlan.gnorm w) else 0))
      = if ((Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (c1 : GaussianInt) ^ 2 * z2
              - (c2 : GaussianInt) ^ 2 * z1) ∧ wOf z1 z2 c1 c2 ∈ Work.FIPlan.gBox R
        then f (Work.FIPlan.gnorm (wOf z1 z2 c1 c2)) else 0 := by
  by_cases hc : (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (c1 : GaussianInt) ^ 2 * z2
              - (c2 : GaussianInt) ^ 2 * z1
  · obtain ⟨h1, h2⟩ := cForm_wOf ((exists_cForm_eq_iff z1 z2 hΔ c1 c2).mpr hc)
    have hiff : ∀ w : GaussianInt,
        (Work.FIPlan.cForm w z1 = c1*c1 ∧ Work.FIPlan.cForm w z2 = c2*c2)
          ↔ w = wOf z1 z2 c1 c2 := by
      intro w; constructor
      · rintro ⟨hw1, hw2⟩; exact wOf_unique hΔ hw1 hw2
      · rintro rfl; exact ⟨h1, h2⟩
    rw [show (∑ w ∈ Work.FIPlan.gBox R,
          (if Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2
            then f (Work.FIPlan.gnorm w) else 0))
        = ∑ w ∈ Work.FIPlan.gBox R,
          (if w = wOf z1 z2 c1 c2 then f (Work.FIPlan.gnorm w) else 0) from
        Finset.sum_congr rfl (fun w _ => by simp only [hiff w])]
    rw [Finset.sum_ite_eq']
    simp [hc]
  · have hno : ∀ w ∈ Work.FIPlan.gBox R,
        ¬ (Work.FIPlan.cForm w z1 = c1 * c1 ∧ Work.FIPlan.cForm w z2 = c2 * c2) := by
      rintro w _ ⟨hw1, hw2⟩
      exact hc ((exists_cForm_eq_iff z1 z2 hΔ c1 c2).mp ⟨w, hw1, hw2⟩)
    rw [Finset.sum_eq_zero (fun w hw => by rw [if_neg (hno w hw)])]
    simp [hc]

/-- **(*FI* (6.7)): the re-parametrisation of the `w`-sum by the congruence classes.**  For
`Δ(z₁,z₂) ≠ 0`, `S` the set of square pairs `(c₁,c₂)` of (6.3) with `|c_i| ≤ K` whose `Δ`-congruence
holds and whose `w` lies in the box (the hypothesis `hS`), the `w`-sum of (5.27) equals the sum
over `S`: on the left each `w` contributes `Z(Re wz₁)Z(Re wz₂)` (its `Z`-many choices of the two
square roots), and on the right the *pairs* `(c₁,c₂)` do — the congruence
`Δ ∣ c₁²z₂ − c₂²z₁` is exactly the statement that the `w` of (6.3) is a Gaussian integer
(`Work.FIArea2.exists_cForm_eq_iff`), and it is unique (`Work.FIArea2.cForm_pair_injective`,
through `Work.FIArea2.wOf_unique`).  The hypothesis `hK` only says that `K` contains the roots of
the finitely many squares that occur; with `w ∈ gBox R` one has `|c_i| ≤ (√2 R |z_i|)^{1/2}`, so
e.g. `K = ⌈(√2(R+1)(|z₁|+|z₂|+1))^{1/2}⌉` works.  This is the identity to which the two-dimensional
Poisson summation (6.8)–(6.11) is applied. -/
theorem sum_gBox_eq_sum_congruences (R : ℤ) (f : ℤ → ℝ) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (K : ℕ) (S : Finset (ℤ × ℤ))
    (hK : ∀ w ∈ Work.FIPlan.gBox R, ∀ c1 c2 : ℤ, Work.FIPlan.cForm w z1 = c1 * c1 →
      Work.FIPlan.cForm w z2 = c2 * c2 →
      -(K : ℤ) ≤ c1 ∧ c1 ≤ K ∧ -(K : ℤ) ≤ c2 ∧ c2 ≤ K)
    (hS : ∀ p : ℤ × ℤ, p ∈ S ↔ p.1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧
      p.2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧
      (Work.FIPlan.Delta z1 z2 : GaussianInt)
          ∣ (p.1 : GaussianInt) ^ 2 * z2 - (p.2 : GaussianInt) ^ 2 * z1 ∧
      wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox R) :
    (∑ w ∈ Work.FIPlan.gBox R, f (Work.FIPlan.gnorm w)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))
      = ∑ p ∈ S, f (Work.FIPlan.gnorm (wOf z1 z2 p.1 p.2)) := by
  classical
  have hST : S = (Finset.Icc (-(K:ℤ)) (K:ℤ) ×ˢ Finset.Icc (-(K:ℤ)) (K:ℤ)).filter
      (fun p : ℤ × ℤ => (Work.FIPlan.Delta z1 z2 : GaussianInt)
          ∣ (p.1 : GaussianInt) ^ 2 * z2 - (p.2 : GaussianInt) ^ 2 * z1
        ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox R) := by
    ext p
    rw [Finset.mem_filter, hS p, Finset.mem_product]
    tauto
  have hA : (∑ w ∈ Work.FIPlan.gBox R, f (Work.FIPlan.gnorm w)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))
      = ∑ w ∈ Work.FIPlan.gBox R,
          ∑ p ∈ Finset.Icc (-(K:ℤ)) (K:ℤ) ×ˢ Finset.Icc (-(K:ℤ)) (K:ℤ),
          f (Work.FIPlan.gnorm w) * ((if p.1^2 = Work.FIPlan.cForm w z1 then (1:ℝ) else 0)
            * (if p.2^2 = Work.FIPlan.cForm w z2 then (1:ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro w hw
    conv_lhs => rw [mul_assoc]
    rw [Zint_mul_Cnt K (Work.FIPlan.cForm w z1) (Work.FIPlan.cForm w z2) (by
      intro c1 c2 h1 h2
      obtain ⟨a,b,c,d⟩ := hK w hw c1 c2 (by rw [← h1]; ring) (by rw [← h2]; ring)
      exact ⟨Finset.mem_Icc.mpr ⟨a,b⟩, Finset.mem_Icc.mpr ⟨c,d⟩⟩)]
    rw [gBoxCnt, gBoxCnt, Finset.sum_product]
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
  have hC : (∑ w ∈ Work.FIPlan.gBox R,
        ∑ p ∈ Finset.Icc (-(K:ℤ)) (K:ℤ) ×ˢ Finset.Icc (-(K:ℤ)) (K:ℤ),
          f (Work.FIPlan.gnorm w) * ((if p.1^2 = Work.FIPlan.cForm w z1 then (1:ℝ) else 0)
            * (if p.2^2 = Work.FIPlan.cForm w z2 then (1:ℝ) else 0)))
      = ∑ p ∈ Finset.Icc (-(K:ℤ)) (K:ℤ) ×ˢ Finset.Icc (-(K:ℤ)) (K:ℤ),
        ∑ w ∈ Work.FIPlan.gBox R,
          f (Work.FIPlan.gnorm w) * ((if p.1^2 = Work.FIPlan.cForm w z1 then (1:ℝ) else 0)
            * (if p.2^2 = Work.FIPlan.cForm w z2 then (1:ℝ) else 0)) := Finset.sum_comm
  have hD : ∀ p : ℤ × ℤ,
      (∑ w ∈ Work.FIPlan.gBox R,
          f (Work.FIPlan.gnorm w) * ((if p.1^2 = Work.FIPlan.cForm w z1 then (1:ℝ) else 0)
            * (if p.2^2 = Work.FIPlan.cForm w z2 then (1:ℝ) else 0)))
      = if ((Work.FIPlan.Delta z1 z2 : GaussianInt)
            ∣ (p.1 : GaussianInt) ^ 2 * z2 - (p.2 : GaussianInt) ^ 2 * z1
          ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox R)
        then f (Work.FIPlan.gnorm (wOf z1 z2 p.1 p.2)) else 0 := by
    intro p
    have hcong : ∀ w : GaussianInt,
        f (Work.FIPlan.gnorm w) * ((if p.1^2 = Work.FIPlan.cForm w z1 then (1:ℝ) else 0)
          * (if p.2^2 = Work.FIPlan.cForm w z2 then (1:ℝ) else 0))
        = (if Work.FIPlan.cForm w z1 = p.1 * p.1 ∧ Work.FIPlan.cForm w z2 = p.2 * p.2
            then f (Work.FIPlan.gnorm w) else 0) := by
      intro w
      have e1 : (p.1^2 = Work.FIPlan.cForm w z1) ↔ (Work.FIPlan.cForm w z1 = p.1 * p.1) := by
        rw [pow_two, eq_comm]
      have e2 : (p.2^2 = Work.FIPlan.cForm w z2) ↔ (Work.FIPlan.cForm w z2 = p.2 * p.2) := by
        rw [pow_two, eq_comm]
      simp only [e1, e2]
      by_cases hc1 : Work.FIPlan.cForm w z1 = p.1 * p.1
      · by_cases hc2 : Work.FIPlan.cForm w z2 = p.2 * p.2
        · simp [hc1, hc2]
        · simp [hc1, hc2]
      · simp [hc1]
    rw [Finset.sum_congr rfl (fun w _ => hcong w), sum_ite_cForm R f z1 z2 hΔ p.1 p.2]
  rw [hA, hC]
  rw [Finset.sum_congr rfl (fun p _ => hD p)]
  rw [hST, Finset.sum_filter]

end

end Work.FIArea2
