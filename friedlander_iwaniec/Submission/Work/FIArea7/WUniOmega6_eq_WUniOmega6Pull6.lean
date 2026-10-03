import Mathlib
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.WBOmega6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Möbius weight `μ(b)/b` of (17.9) as a complex number. -/
private def muw (b : ℕ) : ℂ := (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)

/-- The `ω`-weight of (17.9) at a fixed `(b,e)`, without the Möbius factor. -/
private def T6 (β : GaussianInt → ℂ) (b e : ℕ) (z1 z2 : GaussianInt) : ℂ :=
  (Work.FIArea7.reflSign z1 z2 : ℂ)
    * omegaDetect (4 * b * e) e z1 z2
    * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
    * (betaPrime β z1 * star (betaPrime β z2))
    * (Work.FITop4.logFac6 z1 z2 : ℂ)

/-- `WUniOmega6Inner` is the `(b,e)`-sum of `muw b * T6` over the pair-dependent index set
`{(b,e) : 4be ∣ |Δ|, e ≤ X}` with `b ≤ |Δ|/4+1`. -/
private lemma WUniOmega6Inner_eq (X : ℕ) (z1 z2 : GaussianInt) (β : GaussianInt → ℂ) :
    WUniOmega6Inner X z1 z2 β
      = ∑ b ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1),
          ∑ e ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
              (fun e => 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 ∧ e ≤ X),
            muw b * T6 β b e z1 z2 := by
  unfold WUniOmega6Inner
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [muw, T6]
  ring

/-- **The per-pair `(b,e)`-sum is the pulled-out `(b,e)`-sum.**  The index set
`{(b,e) : 4be ∣ |Δ|, e ≤ X}` of the `ω`-form of the uniform cut, with the pair-dependent
`b`-bound `|Δ|/4+1`, is the same as the uniform box `b ≤ U`, `e ≤ X` restricted to `4be ∣ |Δ|`:
every contributing `b` is `≤ |Δ|/4 ≤ U` and every contributing `e` is `≤ |Δ|/4+1`. -/
private lemma sum_bi_eq (D U X : ℕ) (hD : 0 < D)
    (hU : ∀ b e : ℕ, 1 ≤ e → e ≤ X → 4 * b * e ∣ D → b ≤ U)
    (f : ℕ → ℕ → ℂ) :
    (∑ b ∈ Finset.Icc 1 (D / 4 + 1),
        ∑ e ∈ (Finset.Icc 1 (D / 4 + 1)).filter (fun e => 4 * b * e ∣ D ∧ e ≤ X),
          f b e)
      = ∑ b ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 X,
          (if 4 * b * e ∣ D then f b e else 0) := by
  have h4 : 0 < (4 : ℕ) := by norm_num
  -- every contributing `b` is `≤ D/4`
  have hbD : ∀ b e : ℕ, 1 ≤ e → 4 * b * e ∣ D → b ≤ D / 4 := by
    intro b e he1 h4be
    rw [Nat.le_div_iff_mul_le h4]
    have h1 : 4 * b * e ≤ D := Nat.le_of_dvd hD h4be
    nlinarith [h1, he1]
  -- every contributing `e` is `≤ D/4`
  have heD : ∀ b e : ℕ, 1 ≤ b → 4 * b * e ∣ D → e ≤ D / 4 := by
    intro b e hb1 h4be
    rw [Nat.le_div_iff_mul_le h4]
    have h1 : 4 * b * e ≤ D := Nat.le_of_dvd hD h4be
    nlinarith [h1, hb1]
  -- the `e`-filter is the uniform `Icc 1 X` filter
  have hfilter : ∀ b : ℕ, 1 ≤ b →
      (Finset.Icc 1 (D / 4 + 1)).filter (fun e => 4 * b * e ∣ D ∧ e ≤ X)
        = (Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ D) := by
    intro b hb
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨he1, _⟩, h4be, heX⟩
      exact ⟨⟨he1, heX⟩, h4be⟩
    · rintro ⟨⟨he1, heX⟩, h4be⟩
      exact ⟨⟨he1, by have := heD b e hb h4be; omega⟩, h4be, heX⟩
  have hb1_of_mem : ∀ b ∈ Finset.Icc 1 (D / 4 + 1) ∪ Finset.Icc 1 U, 1 ≤ b := by
    intro b hb
    rcases Finset.mem_union.mp hb with h | h
    · exact (Finset.mem_Icc.mp h).1
    · exact (Finset.mem_Icc.mp h).1
  -- the range `b ≤ D/4+1` may be dropped for `b > U`
  have hzeroA : ∀ b ∈ Finset.Icc 1 (D / 4 + 1) ∪ Finset.Icc 1 U,
      b ∉ Finset.Icc 1 (D / 4 + 1) →
      (∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0)) = 0 := by
    intro b hb hbnA
    have hbgt : D / 4 + 1 < b := by
      by_contra hcon
      exact hbnA (Finset.mem_Icc.mpr ⟨hb1_of_mem b hb, not_lt.mp hcon⟩)
    refine Finset.sum_eq_zero fun e he => ?_
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    rw [if_neg]
    intro h4be
    have := hbD b e he1 h4be
    omega
  -- the range `b ≤ U` may be dropped for `b > D/4+1`
  have hzeroB : ∀ b ∈ Finset.Icc 1 (D / 4 + 1) ∪ Finset.Icc 1 U,
      b ∉ Finset.Icc 1 U →
      (∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0)) = 0 := by
    intro b hb hbnB
    have hbgt : U < b := by
      by_contra hcon
      exact hbnB (Finset.mem_Icc.mpr ⟨hb1_of_mem b hb, not_lt.mp hcon⟩)
    refine Finset.sum_eq_zero fun e he => ?_
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heX : e ≤ X := (Finset.mem_Icc.mp he).2
    rw [if_neg]
    intro h4be
    exact absurd (hU b e he1 heX h4be) (not_le.mpr hbgt)
  calc (∑ b ∈ Finset.Icc 1 (D / 4 + 1),
        ∑ e ∈ (Finset.Icc 1 (D / 4 + 1)).filter (fun e => 4 * b * e ∣ D ∧ e ≤ X),
          f b e)
      = ∑ b ∈ Finset.Icc 1 (D / 4 + 1),
          ∑ e ∈ (Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ D), f b e := by
        refine Finset.sum_congr rfl fun b hb => Finset.sum_congr ?_ fun e _ => rfl
        exact hfilter b (Finset.mem_Icc.mp hb).1
    _ = ∑ b ∈ Finset.Icc 1 (D / 4 + 1),
          ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ b ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0) := by
        have hA : (∑ b ∈ Finset.Icc 1 (D / 4 + 1),
              ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0))
            = ∑ b ∈ Finset.Icc 1 (D / 4 + 1) ∪ Finset.Icc 1 U,
              ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0) :=
          Finset.sum_subset Finset.subset_union_left hzeroA
        have hB : (∑ b ∈ Finset.Icc 1 U,
              ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0))
            = ∑ b ∈ Finset.Icc 1 (D / 4 + 1) ∪ Finset.Icc 1 U,
              ∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ D then f b e else 0) :=
          Finset.sum_subset Finset.subset_union_right hzeroB
        exact hA.trans hB.symm

/-- **The per-pair identity of the two forms.**  For a pair `(z₁,z₂)` the `ω`-form of (17.9)
(with the pair-dependent index set) equals the `(b,e)`-sum with the uniform ranges
`b ≤ uniB Pa`, `e ≤ X` and the explicit congruence condition `4be ∣ |Δ|`.  Both sides vanish
unless `β z₁ ≠ 0`, `β z₂ ≠ 0` and `|Δ| ≠ 0`; on that support the pair-dependent `b`-bound
`|Δ|/4+1` is replaced by the uniform `uniB Pa` through `le_uniB_of_four_mul_le_absDelta`. -/
private lemma pair_eq (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (_hX : 1 ≤ X)
    (z1 z2 : GaussianInt) :
    (if Work.FIPlan.GaussCoprime z1 z2 then WUniOmega6Inner X z1 z2 β else 0)
      = ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          muw b * (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0) := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc]
    by_cases hcase : β z1 ≠ 0 ∧ β z2 ≠ 0 ∧ 0 < Work.FIPlan.absDelta z1 z2
    · obtain ⟨hz1, hz2, hD⟩ := hcase
      rw [WUniOmega6Inner_eq]
      rw [sum_bi_eq (Work.FIPlan.absDelta z1 z2) (uniB Pa) X hD
        (fun b e he1 _ h4 => le_uniB_of_four_mul_le_absDelta
          (Work.FITop4.IsBetaCoeff6.support hβ hz1)
          (Work.FITop4.IsBetaCoeff6.support hβ hz2) he1 (Nat.le_of_dvd hD h4))
        (fun b e => muw b * T6 β b e z1 z2)]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
      by_cases h4 : 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 <;> simp [h4, hc]
    · have hterm : ∀ b e : ℕ, T6 β b e z1 z2 = 0 := by
        intro b e
        by_cases hD0 : Work.FIPlan.absDelta z1 z2 = 0
        · simp [T6, Work.FITop4.logFac6, hD0]
        · have hz : β z1 = 0 ∨ β z2 = 0 := by
            by_contra hcon
            push Not at hcon
            exact hcase ⟨hcon.1, hcon.2, Nat.pos_of_ne_zero hD0⟩
          rcases hz with h | h <;> simp [T6, betaPrime, h]
      rw [WUniOmega6Inner_eq]
      rw [Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun e _ => by
        rw [hterm b e, mul_zero]))]
      refine (Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_).symm
      by_cases h4 : 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
      · rw [if_pos ⟨hc, h4⟩, hterm b e, mul_zero]
      · rw [if_neg (fun h => h4 h.2), mul_zero]
  · rw [if_neg hc]
    refine (Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_).symm
    rw [if_neg (fun h => hc h.1), mul_zero]

theorem WUniOmega6_eq_WUniOmega6Pull6 (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ)
    (z0 : GaussianInt) (β : GaussianInt → ℂ)
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X) :
    Work.FIArea7.WUniOmega6 Pa X β = Work.FIArea7.WUniOmega6Pull6 Pa X β := by
  unfold Work.FIArea7.WUniOmega6 Work.FIArea7.WUniOmega6Pull6
  set B : Finset GaussianInt := Work.FIPlan.gBox (Work.FITop.radN Pa) with hB
  set Sb : Finset ℕ := Finset.Icc 1 (uniB Pa) with hSb
  set Se : Finset ℕ := Finset.Icc 1 X with hSe
  congr 1
  have hexp : (∑ z1 ∈ B, ∑ z2 ∈ B,
        (if Work.FIPlan.GaussCoprime z1 z2 then WUniOmega6Inner X z1 z2 β else 0))
      = ∑ z1 ∈ B, ∑ z2 ∈ B, ∑ b ∈ Sb, ∑ e ∈ Se,
          muw b * (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0) := by
    refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
    exact pair_eq Pa X φ z0 β hβ hX z1 z2
  have hswap : (∑ z1 ∈ B, ∑ z2 ∈ B, ∑ b ∈ Sb, ∑ e ∈ Se,
          muw b * (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0))
      = ∑ b ∈ Sb, ∑ e ∈ Se, ∑ z1 ∈ B, ∑ z2 ∈ B,
          muw b * (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0) := by
    have h := Finset.sum_comm (s := B ×ˢ B) (t := Sb ×ˢ Se)
      (f := fun p q => muw q.1 * (if Work.FIPlan.GaussCoprime p.1 p.2
          ∧ 4 * q.1 * q.2 ∣ Work.FIPlan.absDelta p.1 p.2 then T6 β q.1 q.2 p.1 p.2 else 0))
    simp only [Finset.sum_product] at h
    exact h
  have hpush : (∑ b ∈ Sb, ∑ e ∈ Se, muw b * ∑ z1 ∈ B, ∑ z2 ∈ B,
          (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0))
      = ∑ b ∈ Sb, ∑ e ∈ Se, ∑ z1 ∈ B, ∑ z2 ∈ B,
          muw b * (if Work.FIPlan.GaussCoprime z1 z2
              ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then T6 β b e z1 z2 else 0) := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [Finset.mul_sum]
  exact hexp.trans (hswap.trans hpush.symm)

end

end Work.FIArea7
