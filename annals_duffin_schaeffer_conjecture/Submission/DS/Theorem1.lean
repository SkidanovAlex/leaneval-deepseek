import Submission.DS.Structure
import Submission.DS.Measure
import Submission.DS.Totient
import Submission.DS.Bound

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# The Duffin-Schaeffer theorem (Koukoulopoulos-Maynard) — target statement and opening layer

## The statement (fixed by `ChallengeDeps`)

For `ψ : ℕ+ → ℝ≥0` the set of points well approximable by *reduced* fractions is

    𝒜 ψ = {α ∈ [0,1] |  {(a,q) : ℕ × ℕ+ | Nat.Coprime a q ∧ |α − a/q| ≤ ψ(q)/q}.Infinite }

(the "measure space" is the Lebesgue measure `volume` on ℝ; no rational set appears in
`theorem_1` itself).  The theorem:

    theorem theorem_1_KM (ψ) (hdiv : ¬ Summable (fun q => (ψ q * φ q) / q)) :
        MeasurableSet (𝒜 ψ) ∧ volume (𝒜 ψ) = 1

## This file

The opening structural layer of its proof:

* per-denominator coprime solution sets `Acopr ψ q` and the finiteness of their numerator
  fibres (`Acopr_fib_finite`), which gives the limsup decomposition
  `𝒜 ψ = [0,1] ∩ limsup_q Acopr ψ q`;
* measurability of `𝒜 ψ` (the `MeasurableSet` conjunct of the theorem);
* monotonicity of `𝒜` in `ψ`.
-/

namespace Submission.DS


/-- The set of points within `ψ(q)/q` of a reduced fraction with denominator `q`. -/
def Acopr (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : Set ℝ :=
  {x | ∃ a : ℕ, Nat.Coprime a q ∧ inequality_1_7 ψ x a q}

/-- For a fixed `x` and denominator `q`, the numerator fibre is finite (Dirichlet-type
bound: a solution forces `a ≤ q·(x + ψ(q)/q)`). -/
lemma Acopr_fib_finite (ψ : ℕ+ → ℝ≥0) (x : ℝ) (q : ℕ+) :
    ({a : ℕ | Nat.Coprime a q ∧ inequality_1_7 ψ x a q}).Finite := by
  let r : ℝ := ((ψ q / q : NNReal) : ℝ)
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hbound : ∀ a ∈ ({a : ℕ | Nat.Coprime a q ∧ inequality_1_7 ψ x a q} : Set ℕ),
      (a : ℝ) ≤ (q : ℝ) * (x + r) := by
    intro a ha
    have hineq : inequality_1_7 ψ x a q := ha.2
    unfold inequality_1_7 at hineq
    have hmain : |x - (a : ℝ) / (q : ℝ)| ≤ r := by
      simpa [r] using hineq
    have hlt : (a : ℝ) / (q : ℝ) ≤ x + r := by
      rw [abs_le] at hmain
      nlinarith [hmain.1]
    have h1 : (a : ℝ) / (q : ℝ) * (q : ℝ) ≤ (x + r) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hlt (le_of_lt hq0)
    have h2 : (a : ℝ) / (q : ℝ) * (q : ℝ) = (a : ℝ) := by field_simp [hq0.ne']
    rw [h2] at h1
    nlinarith
  rcases exists_nat_gt ((q : ℝ) * (x + r)) with ⟨N, hN⟩
  refine (Set.finite_lt_nat N).subset ?_
  intro a ha
  have hle := hbound a ha
  have hlt : (a : ℝ) < (N : ℝ) := lt_of_le_of_lt hle hN
  exact_mod_cast hlt

/-- `𝒜 ψ` is the `[0,1]`-part of the set of points lying in infinitely many `Acopr ψ q`. -/
lemma A_eq_Icc_inter_limsup (ψ : ℕ+ → ℝ≥0) :
    𝒜 ψ = Set.Icc (0 : ℝ) 1 ∩ limsupDenoms (Acopr ψ) := by
  classical
  ext x
  constructor
  · intro hx
    have hx01 : x ∈ Set.Icc 0 1 := ((show x ∈ 𝒜 ψ from hx) : x ∈ {α ∈ Set.Icc 0 1 | _}).1
    have hP : ({(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 ψ x a q}).Infinite :=
      ((show x ∈ 𝒜 ψ from hx) : x ∈ {α ∈ Set.Icc 0 1 | _}).2
    refine ⟨hx01, ?_⟩
    -- pair-infinite ⟺ infinitely many q with a coprime solution
    let fib : ℕ+ → Set ℕ := fun q => {a | Nat.Coprime a q ∧ inequality_1_7 ψ x a q}
    have hEq : pairSet fib = {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 ψ x a q} := by
      ext p
      simp [pairSet, fib]
    have hD : (denomSet fib).Infinite :=
      (infinite_pairs_iff_infinite_denoms fib (Acopr_fib_finite ψ x)).1 (by simpa [hEq] using hP)
    change {q : ℕ+ | x ∈ Acopr ψ q}.Infinite
    have hEq2 : denomSet fib = {q : ℕ+ | x ∈ Acopr ψ q} := by
      ext q
      change (∃ a : ℕ, Nat.Coprime a q ∧ inequality_1_7 ψ x a q) ↔
        (∃ a : ℕ, Nat.Coprime a q ∧ inequality_1_7 ψ x a q)
      rfl
    rwa [← hEq2]
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hq : {q : ℕ+ | x ∈ Acopr ψ q}.Infinite := by
      simpa [limsupDenoms] using hx.2
    let fib : ℕ+ → Set ℕ := fun q => {a | Nat.Coprime a q ∧ inequality_1_7 ψ x a q}
    have hEq : pairSet fib = {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 ψ x a q} := by
      ext p
      simp [pairSet, fib]
    have hD : (denomSet fib).Infinite := by
      have hEq2 : denomSet fib = {q : ℕ+ | x ∈ Acopr ψ q} := by
        ext q
        change (∃ a : ℕ, Nat.Coprime a q ∧ inequality_1_7 ψ x a q) ↔
          (∃ a : ℕ, Nat.Coprime a q ∧ inequality_1_7 ψ x a q)
        rfl
      rwa [hEq2]
    exact (infinite_pairs_iff_infinite_denoms fib (Acopr_fib_finite ψ x)).2 hD

/-- Per-denominator coprime solution sets are measurable. -/
lemma measurableSet_Acopr (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : MeasurableSet (Acopr ψ q) := by
  classical
  have hEq : Acopr ψ q = ⋃ i : {a : ℕ // Nat.Coprime a (q : ℕ)},
      {x : ℝ | inequality_1_7 ψ x i.1 q} := by
    ext x
    constructor
    · intro hx
      simp [Acopr] at hx
      rcases hx with ⟨a, hc, hi⟩
      exact mem_iUnion.mpr ⟨⟨a, hc⟩, hi⟩
    · intro hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      exact ⟨i.1, i.2, by simpa using hi⟩
  rw [hEq]
  exact MeasurableSet.iUnion (fun i : {a : ℕ // Nat.Coprime a (q : ℕ)} =>
    measurableSet_solInterval ψ i.1 q)

/-- `𝒜 ψ` is measurable (the `MeasurableSet` conjunct of `theorem_1`). -/
lemma measurableSet_A (ψ : ℕ+ → ℝ≥0) : MeasurableSet (𝒜 ψ) := by
  rw [A_eq_Icc_inter_limsup]
  exact (isClosed_Icc.measurableSet).inter (measurableSet_limsupDenoms (measurableSet_Acopr ψ))

/-- `𝒜` is monotone in `ψ`. -/
lemma A_mono {ψ χ : ℕ+ → ℝ≥0} (h : ∀ q, ψ q ≤ χ q) : 𝒜 ψ ⊆ 𝒜 χ := by
  intro x hx
  rw [A_eq_Icc_inter_limsup] at hx ⊢
  rcases hx with ⟨hx01, hxlim⟩
  refine ⟨hx01, ?_⟩
  have hq : {q : ℕ+ | x ∈ Acopr ψ q}.Infinite := by
    simpa [limsupDenoms] using hxlim
  change {q : ℕ+ | x ∈ Acopr χ q}.Infinite
  apply Set.Infinite.mono (fun q hqmem => ?_) hq
  rcases hqmem with ⟨a, hc, hineq⟩
  refine ⟨a, hc, ?_⟩
  unfold inequality_1_7 at hineq ⊢
  have hR : ((ψ q / q : NNReal) : ℝ) ≤ ((χ q / q : NNReal) : ℝ) := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    simpa [NNReal.coe_div] using
      (div_le_div_of_nonneg_right (by exact_mod_cast h q : (ψ q : ℝ) ≤ (χ q : ℝ)) hq0)
  exact le_trans hineq hR



section measure_one

/-- The Duffin-Schaeffer approximable set in limsup form. -/
def W (ψ : ℕ+ → ℝ≥0) : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ limsupDenoms (Acopr ψ)

/-- `𝒜 ψ = W ψ` (measurability-ready identification). -/
lemma A_eq_W (ψ : ℕ+ → ℝ≥0) : 𝒜 ψ = W ψ := by
  unfold W
  exact A_eq_Icc_inter_limsup ψ

/-- A numerator solving `|x - a/q| ≤ ψ(q)/q` with `ψ(q) ≤ 1/2` and `x ≤ 1` is at most
`q` (the interval `a/q ± ψ(q)/q` cannot reach past `[0,1]`). -/
lemma num_le_q_of_half_radius {ψ : ℕ+ → ℝ≥0} {q : ℕ+} (hle : ψ q ≤ (1 / 2 : ℝ≥0))
    {x : ℝ} {a : ℕ} (hx1 : x ≤ 1) (hineq : inequality_1_7 ψ x a q) : a ≤ (q : ℕ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hleR : ((ψ q / q : NNReal) : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) := by
    have hψR : (ψ q : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hle
    have hb : (ψ q : ℝ) / (q : ℝ) ≤ (1 / 2 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hψR (le_of_lt hq0)
    simpa [NNReal.coe_div] using hb
  unfold inequality_1_7 at hineq
  have habs : |x - (a : ℝ) / (q : ℝ)| ≤ (1 / 2 : ℝ) / (q : ℝ) := le_trans hineq hleR
  have haq : (a : ℝ) / (q : ℝ) ≤ x + (1 / 2 : ℝ) / (q : ℝ) := by
    rw [abs_le] at habs
    nlinarith [habs.1]
  have ha : (a : ℝ) ≤ (q : ℝ) * x + 1 / 2 := by
    have h1 : (a : ℝ) / (q : ℝ) * (q : ℝ) ≤ (x + (1 / 2 : ℝ) / (q : ℝ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right haq (le_of_lt hq0)
    have h2 : (a : ℝ) / (q : ℝ) * (q : ℝ) = (a : ℝ) := by field_simp [hq0.ne']
    have h3 : (x + (1 / 2 : ℝ) / (q : ℝ)) * (q : ℝ) = x * (q : ℝ) + 1 / 2 := by
      rw [add_mul]
      field_simp [hq0.ne']
    rw [h2, h3] at h1
    nlinarith
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have ha' : (a : ℝ) < (q : ℝ) + 1 := by
    nlinarith [hx1, hhalf, hq0]
  have haN : a < (q : ℕ) + 1 := by exact_mod_cast ha'
  omega

/-- The `[0,1]`-part of the coprime solution set is covered by the coprime fractions
with numerator `≤ q`. -/
lemma Acopr_Icc_subset_union_coprime {ψ : ℕ+ → ℝ≥0} {q : ℕ+}
    (hle : ψ q ≤ (1 / 2 : ℝ≥0)) :
    Acopr ψ q ∩ Set.Icc 0 1 ⊆
      (⋃ a ∈ (Finset.Icc 0 (q : ℕ)).filter (fun a => Nat.Coprime a (q : ℕ)),
        ({x : ℝ | inequality_1_7 ψ x a q} : Set ℝ)) := by
  intro x hx
  have hx01 : x ∈ Set.Icc 0 1 := hx.2
  rcases hx.1 with ⟨a, hc, hineq⟩
  have haq : a ≤ (q : ℕ) := num_le_q_of_half_radius hle hx01.2 hineq
  refine mem_iUnion₂.mpr ⟨a,
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le a, haq⟩, hc⟩, hineq⟩

/-- Identity of the `[0,1]`-restricted solution intervals with the absolute-value form. -/
lemma Acopr_interval_eq_abs (ψ : ℕ+ → ℝ≥0) (a : ℕ) (q : ℕ+) :
    ({x : ℝ | inequality_1_7 ψ x a q} : Set ℝ) =
      {x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤ ((ψ q / q : NNReal) : ℝ)} := by
  ext x
  unfold inequality_1_7
  rfl

/-- **Per-denominator mass bound** (divergence block): the measure of the coprime
solution set inside `[0,1]` is controlled by `4·φ(q)·ψ(q)/q`. -/
lemma measure_Acopr_Icc_le (ψ : ℕ+ → ℝ≥0) {q : ℕ+} (hle : ψ q ≤ (1 / 2 : ℝ≥0)) :
    volume (Acopr ψ q ∩ Set.Icc 0 1) ≤
      (4 : ℝ≥0∞) * ((((φ q : NNReal) * (ψ q / q : NNReal)) : NNReal) : ℝ≥0∞) := by
  let I : Finset ℕ := (Finset.Icc 0 (q : ℕ)).filter (fun a => Nat.Coprime a (q : ℕ))
  have hcard : I.card ≤ φ q + 1 := by
    simpa [I, Nat.coprime_comm] using (card_coprime_Icc_zero_le q)
  have hsub : Acopr ψ q ∩ Set.Icc 0 1 ⊆
      (⋃ a ∈ I, ({x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤ ((ψ q / q : NNReal) : ℝ)} : Set ℝ)) ∩
        Set.Icc 0 1 := by
    intro x hx
    refine ⟨?_, hx.2⟩
    rw [show (⋃ a ∈ I, ({x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤ ((ψ q / q : NNReal) : ℝ)} : Set ℝ))
        = (⋃ a ∈ I, ({x : ℝ | inequality_1_7 ψ x a q} : Set ℝ)) by
      apply iUnion₂_congr
      intro a ha
      exact Acopr_interval_eq_abs ψ a q]
    exact Acopr_Icc_subset_union_coprime hle hx
  have hvol := volume_biUnion_interval_le I (fun a : ℕ => (a : ℝ) / (q : ℝ)) (ψ q / q)
  have hb1 : volume (Acopr ψ q ∩ Set.Icc 0 1) ≤
      (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * (((ψ q / q : NNReal)) : ℝ)) :=
    (measure_mono hsub).trans hvol
  have hb2 : (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * (((ψ q / q : NNReal)) : ℝ)) ≤
      (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * (((ψ q / q : NNReal)) : ℝ)) := by
    exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
  have hb3 : (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * (((ψ q / q : NNReal)) : ℝ)) ≤
      (4 : ℝ≥0∞) * (((φ q : NNReal) * (ψ q / q : NNReal)) : ℝ≥0∞) := by
    rw [ofReal_two_mul (ψ q / q)]
    rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num,
      show (4 : ℝ≥0∞) = ((4 : ℝ≥0) : ℝ≥0∞) by norm_num,
      show (((φ q + 1 : ℕ) : ℝ≥0∞)) = ((((φ q + 1 : ℕ) : ℝ≥0) : ℝ≥0∞)) by norm_num]
    simp only [← ENNReal.coe_mul]
    rw [ENNReal.coe_le_coe]
    convert nn_ineq q (ψ q / q) using 1 <;> norm_num
  calc
    volume (Acopr ψ q ∩ Set.Icc 0 1) ≤
        (((φ q + 1 : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (2 * (((ψ q / q : NNReal)) : ℝ)) := hb1.trans hb2
    _ ≤ (4 : ℝ≥0∞) * (((φ q : NNReal) * (ψ q / q : NNReal)) : ℝ≥0∞) := hb3

end measure_one


end Submission.DS
