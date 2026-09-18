/-
# The Beresnevich–Velani lower bound for Corollary 3

Given the mass transference principle `massTransferencePrincipleOne` (proved in
`Submission/Work/MassTransference/`), this file derives the lower bound of Corollary 3:

    dimH (𝒜 ψ) ≥ min (s_inf ψ) 1      for ψ ≤ 1/2,

in two steps:

* for `0 < d < 1` with divergent `d`-series, run the mass transference principle on the
  Duffin–Schaeffer system: the `d`-th power radii `(ψ(q)/q)^d` are the radii of the
  function `theta ψ d`, whose set `𝒜 (theta ψ d)` has full Lebesgue measure by Theorem 1,
  so the hypothesis of the mass transference principle holds and
  `μH[d] (𝒜 ψ) = ∞`;
* upgrade `μH[d] (𝒜 ψ) = ∞` for all `0 < d < min (s_inf ψ) 1` to
  `min (s_inf ψ) 1 ≤ dimH (𝒜 ψ)`.
-/

import Submission.Main.BVDefs
import Submission.DS.Coro3Main
import Submission.DS.DimH

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open MeasureTheory.Measure
open DuffinSchaefferConjecture

namespace Submission.Main

/-- `theta ψ d` has the radii of `ψ` raised to the power `d`. -/
lemma theta_mul_div (ψ : ℕ+ → ℝ≥0) (d : ℝ) (q : ℕ+) :
    (theta ψ d q * φ q) / q = (φ q : ℝ≥0) * ((ψ q / q : ℝ≥0) ^ d) := by
  apply NNReal.coe_injective
  rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_mul, theta, NNReal.coe_mul, NNReal.coe_rpow,
    NNReal.coe_div]
  have hq : ((q : ℝ≥0) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
    simpa using this.ne'
  field_simp

/-- The `theta`-series is the `d`-series of `ψ`. -/
lemma summable_theta_iff (ψ : ℕ+ → ℝ≥0) (d : ℝ) :
    Summable (fun q : ℕ+ => (theta ψ d q * φ q) / q) ↔
      Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ d)) :=
  summable_congr (fun q => theta_mul_div ψ d q)

/-- `𝒜 (theta ψ d)` is the limsup of the intervals of the truncated index set. -/
theorem A_eq_Icc_LS_theta (ψ : ℕ+ → ℝ≥0) (d : ℝ) :
    𝒜 (theta ψ d) = Set.Icc (0 : ℝ) 1 ∩
      {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ rrP (theta ψ d) p.1}.Infinite} := by
  rw [A_eq_Icc_pairs (theta ψ d)]
  ext z
  constructor
  · rintro ⟨hz01, hzinf⟩
    refine ⟨hz01, ?_⟩
    refine (infinite_subtype_iff (P := fun p : ℕ × ℕ+ => Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2)
      (Q := fun p => |z - ctrP p| ≤ rrP (theta ψ d) p)).mpr ?_
    refine hzinf.mono ?_
    rintro p ⟨hc, hi⟩
    exact ⟨⟨hc, mem_numBound_of_theta_witness hz01.2 hi⟩, hi⟩
  · rintro ⟨hz01, hzinf⟩
    refine ⟨hz01, ?_⟩
    have hplain : ({p : ℕ × ℕ+ | (Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2) ∧ |z - ctrP p| ≤ rrP (theta ψ d) p}).Infinite :=
      (infinite_subtype_iff (P := fun p : ℕ × ℕ+ => Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2)
        (Q := fun p => |z - ctrP p| ≤ rrP (theta ψ d) p)).mp hzinf
    refine hplain.mono ?_
    rintro p ⟨⟨hc, -⟩, hi⟩
    exact ⟨hc, hi⟩

/-- The mass transference principle of Beresnevich–Velani, `k = 1`, `f(r) = r^d`,
localised to `[0,1]`. -/
abbrev MTPStatement : Prop :=
  ∀ (d : ℝ), 0 < d → d < 1 → ∀ (ι : Type) [Countable ι] (c : ι → ℝ) (ρ : ι → ℝ),
    (∀ i, 0 ≤ ρ i) → (∀ ε : ℝ, 0 < ε → {i | ε ≤ ρ i}.Finite) →
    (∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ {z : ℝ | {i | |z - c i| ≤ (ρ i) ^ d}.Infinite})
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y)) →
    MeasureTheory.Measure.hausdorffMeasure d
      (Set.Icc (0 : ℝ) 1 ∩ {z : ℝ | {i | |z - c i| ≤ ρ i}.Infinite}) = ⊤

/-- **The Beresnevich–Velani lower bound, one exponent.**  If the `d`-series of `ψ`
(radii `ψ(q)/q`) diverges, then `μH[d] (𝒜 ψ) = ∞`. -/
theorem hausdorff_A_eq_top_of_MTP (hMTP : MTPStatement) (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q : ℕ+, ψ q ≤ 1 / 2) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (hfin : ∀ ε : ℝ, 0 < ε → ({p : Idx ψ d | ε ≤ rrP ψ p.1}.Finite))
    (hdiv : ¬ Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ d))) :
    μH[d] (𝒜 ψ) = ∞ := by
  classical
  -- the `theta`-series diverges
  have hdivθ : ¬ Summable (fun q : ℕ+ => (theta ψ d q * φ q) / q) :=
    fun hs => hdiv ((summable_theta_iff ψ d).mp hs)
  -- so `𝒜 (theta ψ d)` has full Lebesgue measure
  have hvolθ : volume (𝒜 (theta ψ d)) = 1 := volume_A_eq_one_of_divergence (theta ψ d) hdivθ
  -- hence the `d`-shrunk family satisfies the mass-transference hypothesis
  have hfull : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1
        (Set.Icc x y ∩ {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ (rrP ψ p.1) ^ d}.Infinite})
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc x y) := by
    intro x y hx hy
    set L1 : Set ℝ := {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ (rrP ψ p.1) ^ d}.Infinite} with hL1
    set L2 : Set ℝ := {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ rrP (theta ψ d) p.1}.Infinite} with hL2
    have hL12 : L1 = L2 := by
      rw [hL1, hL2]
      congr 1 with z
      have hseteq : {p : Idx ψ d | |z - ctrP p.1| ≤ (rrP ψ p.1) ^ d} =
          {p : Idx ψ d | |z - ctrP p.1| ≤ rrP (theta ψ d) p.1} := by
        ext p
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← rrP_theta]
      rw [hseteq]
    rw [hL12, hausdorffMeasure_real]
    have hsub : Set.Icc x y ⊆ Set.Icc (0 : ℝ) 1 := fun z hz => ⟨le_trans hx hz.1, le_trans hz.2 hy⟩
    have hA : L2 ∩ Set.Icc (0 : ℝ) 1 = 𝒜 (theta ψ d) := by
      rw [hL2, A_eq_Icc_LS_theta ψ d, Set.inter_comm]
    have hset2 : Set.Icc x y ∩ L2 = Set.Icc x y ∩ 𝒜 (theta ψ d) := by
      rw [← hA]
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hz2, hsub hz1⟩
      · rintro ⟨hz1, hz2, -⟩
        exact ⟨hz1, hz2⟩
    rw [hset2]
    have hsubA : 𝒜 (theta ψ d) ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [A_eq_Icc_LS_theta ψ d]
      exact Set.inter_subset_left
    have hnull0 : volume (Set.Icc (0 : ℝ) 1 \ 𝒜 (theta ψ d)) = 0 := by
      rw [measure_sdiff hsubA (Submission.DS.measurableSet_A (theta ψ d)).nullMeasurableSet
        (by rw [hvolθ]; norm_num), hvolθ, Real.volume_Icc]
      norm_num
    have hnullxy : volume (Set.Icc x y \ 𝒜 (theta ψ d)) = 0 := by
      refine measure_mono_null ?_ hnull0
      rintro z ⟨hz1, hz2⟩
      exact ⟨⟨le_trans hx hz1.1, le_trans hz1.2 hy⟩, hz2⟩
    have hadd : volume (Set.Icc x y ∩ 𝒜 (theta ψ d)) + volume (Set.Icc x y \ 𝒜 (theta ψ d))
        = volume (Set.Icc x y) :=
      measure_inter_add_sdiff _ (Submission.DS.measurableSet_A (theta ψ d))
    rw [hnullxy, add_zero] at hadd
    exact hadd
  -- the mass transference principle
  have hMTPapp : MeasureTheory.Measure.hausdorffMeasure d (Set.Icc (0 : ℝ) 1 ∩
      {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ rrP ψ p.1}.Infinite}) = ⊤ :=
    hMTP d hd0 hd1 (Idx ψ d) (fun p : Idx ψ d => ctrP p.1) (fun p : Idx ψ d => rrP ψ p.1)
      (fun p => rrP_nonneg ψ p.1) (fun ε hε => hfin ε hε) hfull
  rwa [← A_eq_Icc_LS ψ d hψ] at hMTPapp

/-- Dimension from below along exponents that are strictly positive. -/
lemma le_dimH_of_forall_pos_lt {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} {m : ℝ≥0} (h : ∀ d : ℝ≥0, 0 < d → d < m → μH[(d : ℝ)] s = ∞) :
    (m : ℝ≥0∞) ≤ dimH s := by
  by_contra hc
  have hlt : dimH s < (m : ℝ≥0∞) := lt_of_not_ge hc
  have hne : dimH s ≠ (⊤ : ℝ≥0∞) := ne_of_lt (lt_trans hlt (ENNReal.coe_lt_top))
  let x : ℝ≥0 := (dimH s).toNNReal
  have hx : (x : ℝ≥0∞) = dimH s := ENNReal.coe_toNNReal hne
  have hxm : x < m := by
    rw [← hx] at hlt
    exact ENNReal.coe_lt_coe.mp hlt
  obtain ⟨d, hxd, hdm⟩ := exists_between hxm
  have hd0 : 0 < d := by
    have hx0 : (0 : ℝ≥0) ≤ x := by simp
    exact lt_of_le_of_lt hx0 hxd
  have htop : μH[(d : ℝ)] s = ∞ := h d hd0 hdm
  have hge : (d : ℝ≥0∞) ≤ dimH s := le_dimH_of_hausdorffMeasure_eq_top htop
  have hxd' : dimH s < (d : ℝ≥0∞) := by
    rw [← hx]
    exact ENNReal.coe_lt_coe.mpr hxd
  exact (not_lt_of_ge hge) hxd'

/-- **Corollary 3, lower bound**: for `ψ ≤ 1/2` and every `0 < d < min (s_inf ψ) 1` with
divergent `d`-series, `μH[d] (𝒜 ψ) = ∞` entails `min (s_inf ψ) 1 ≤ dimH (𝒜 ψ)`. -/
theorem dimH_A_ge_min_of_BV (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n : ℕ+, ψ n ∈ Set.Icc 0 (1 / 2 : ℝ≥0))
    (hBV : ∀ d : ℝ, 0 < d → d < 1 →
      ¬ Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ d)) →
      μH[d] (𝒜 ψ) = ∞) :
    ((min (s_inf ψ) 1 : ℝ≥0) : ℝ≥0∞) ≤ dimH (𝒜 ψ) := by
  classical
  have hhalf : ∀ q : ℕ+, ψ q ≤ (1 / 2 : ℝ≥0) := fun q => (hψ q).2
  let m : ℝ≥0 := min (s_inf ψ) 1
  have hne : (Submission.DS.sumSet ψ).Nonempty := ⟨4, Submission.DS.four_mem_sumSet ψ hhalf⟩
  have hbdd : BddBelow (Submission.DS.sumSet ψ) := ⟨0, by intro x hx; exact bot_le (α := NNReal)⟩
  have hdivBelow : ∀ d : ℝ≥0, d < s_inf ψ → d ∉ Submission.DS.sumSet ψ := by
    intro d hds hmem
    have hle : sInf (Submission.DS.sumSet ψ) ≤ d := csInf_le hbdd hmem
    have hle' : s_inf ψ ≤ d := by
      rw [Submission.DS.s_inf_eq_sInf ψ]
      exact hle
    exact (not_le_of_gt hds) hle'
  have hinf : ∀ d : ℝ≥0, 0 < d → d < m → μH[(d : ℝ)] (𝒜 ψ) = ∞ := by
    intro d hd0 hdm
    have hd1 : d < 1 := lt_of_lt_of_le hdm (min_le_right (s_inf ψ) 1)
    have hds : d < s_inf ψ := lt_of_lt_of_le hdm (min_le_left (s_inf ψ) 1)
    have hnot : ¬ Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ (d : ℝ))) :=
      fun hs => hdivBelow d hds (by simpa [Submission.DS.sumSet] using hs)
    have hd1R : (d : ℝ) < 1 := by exact_mod_cast hd1
    have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
    exact hBV (d : ℝ) hd0R hd1R hnot
  simpa [m] using le_dimH_of_forall_pos_lt (s := 𝒜 ψ) (m := m) hinf

end Submission.Main
