/-
`aux_single_vector`: the row-block small-ball estimate (Tikhomirov 2020,
Lemma l:aux single vector), derived from per-row small-ball hypotheses via
row independence (from flat independence) and the tensorization lemma
(Commons, integer form).

Given an (n−1)×n family `B` of independent Bernoulli(p) entries and a weight
vector `x`, the per-row random values `ζ_k := Σ_j (B k j + s)·x_j` are
independent (Lemma `iIndepFun_rows_affineSum`).  If each row satisfies the
small-ball bound `P{|ζ_k| ≤ η} ≤ 1−p` (which will follow from the eq-aux /
Littlewood–Offord bound for unit `x` and suitable η ≤ r(p)), then tensorization
gives the Euclidean small-ball bound at scale η·√(ε(n−1)) (equivalently
γ·√(εn) with γ := η·√((n−1)/n)).
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.Prelim
import Submission.Commons.Probability.Independence.tensorization_int
import ChallengeDeps

set_option autoImplicit false

namespace Submission.AuxSingleVector

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

/-- The Lévy concentration function is monotone in the interval radius. -/
theorem levyConcentration_mono_t {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    Submission.Helpers.levyConcentration P ξ t₁ ≤
      Submission.Helpers.levyConcentration P ξ t₂ := by
  classical
  let A₁ : Set ENNReal := {a | ∃ l : ℝ, a = P {x : Ω | |ξ x - l| ≤ t₁}}
  let A₂ : Set ENNReal := {a | ∃ l : ℝ, a = P {x : Ω | |ξ x - l| ≤ t₂}}
  have hbdd₂ : BddAbove A₂ := by
    refine ⟨(1 : ENNReal), ?_⟩
    intro b hb
    rcases hb with ⟨l, rfl⟩
    calc
      P {x : Ω | |ξ x - l| ≤ t₂} ≤ P Set.univ := measure_mono (by intro x hx; trivial)
      _ = 1 := measure_univ
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  rintro a ha
  rcases ha with ⟨l, rfl⟩
  calc
    P {x : Ω | |ξ x - l| ≤ t₁} ≤ P {x : Ω | |ξ x - l| ≤ t₂} := by
      exact measure_mono (by
        intro x hx
        exact le_trans hx ht)
    _ ≤ sSup A₂ := le_csSup hbdd₂ ⟨l, rfl⟩

/-- The per-row small-ball estimate: independent Bernoulli(p) rows of an
(n−1)×n family, with each row value `Σ_j (B k j ω + s)·x_j` bounded in
small-ball probability by `1−p` at scale `η`, concentrate their Euclidean
norm at scale `η·√(ε(n−1))`.

Concretely: for a unit weight vector `x` (any vector with `Σ x_j² = 1`),
`P { ‖(B + s·1·1ᵀ)·x‖₂ ≤ η·√(ε·(n−1)) } ≤ (e·(n−1)/r)^r · (1−p)^{(n−1)−r}`
where `r` is an integer with `ε·(n−1) ≤ r ≤ n−1` (take `r = ⌈ε(n−1)⌉`). -/
theorem aux_single_vector {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (B : Fin (n - 1) → Fin n → Ω → ℝ)
    (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
    (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
    {x : Fin n → ℝ} (_hx : (∑ j : Fin n, (x j) ^ 2) = 1)
    (s : ℝ) {η : ℝ} (hη0 : 0 ≤ η) {ε : ℝ} (_hε0 : 0 < ε)
    {r : ℕ} (hr0 : 0 < r) (hrm : r ≤ n - 1)
    (hεr : ε * ((n - 1 : ℕ) : ℝ) ≤ (r : ℝ))
    (hrow : ∀ k : Fin (n - 1),
      P.real {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η} ≤ (1 - (p : ℝ))) :
    P.real {ω : Ω |
      (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
        η ^ 2 * ε * ((n - 1 : ℕ) : ℝ)} ≤
      (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r : ℝ)) ^ r *
        (1 - (p : ℝ)) ^ ((n - 1) - r) := by
  classical
  -- rows as affine statistics of the flat-independent entry family
  let ζ : Fin (n - 1) → Ω → ℝ :=
    fun k ω => (∑ j : Fin n, B k j ω * x j) + s * (∑ j : Fin n, x j)
  have hζind : ProbabilityTheory.iIndepFun ζ P := by
    dsimp [ζ]
    exact Submission.Prelim.iIndepFun_rows_affineSum (X := B) (mX := hBmeas)
      (hflat := hBind) (x := x) (c := s * (∑ j : Fin n, x j))
  -- pointwise identity between the explicit row value and ζ
  have hrowζ : ∀ k : Fin (n - 1), ∀ ω : Ω,
      (∑ j : Fin n, (B k j ω + s) * x j) = ζ k ω := by
    intro k ω
    dsimp [ζ]
    calc
      (∑ j : Fin n, (B k j ω + s) * x j)
          = ∑ j : Fin n, (B k j ω * x j + s * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j : Fin n, B k j ω * x j) + ∑ j : Fin n, (s * x j) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, B k j ω * x j) + s * (∑ j : Fin n, x j) := by
              congr 1
              rw [← Finset.mul_sum]
  -- the per-row small-ball hypothesis, re-expressed through ζ
  have hsmall : ∀ k : Fin (n - 1),
      P.real {ω : Ω | |ζ k ω| ≤ η} ≤ (1 - (p : ℝ)) := by
    intro k
    have hset : {ω : Ω | |ζ k ω| ≤ η} = {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η} := by
      ext ω
      change |ζ k ω| ≤ η ↔ |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η
      rw [← hrowζ k ω]
    rw [hset]
    exact hrow k
  -- apply tensorization to the independent rows
  have hτ0 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
  have hτ1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.property.1]
  have htens : P.real {ω : Ω | (∑ k : Fin (n - 1), (ζ k ω) ^ 2) ≤ η ^ 2 * (r : ℝ)} ≤
      (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r : ℝ)) ^ r * (1 - (p : ℝ)) ^ ((n - 1) - r) := by
    simpa [ζ] using
      (Commons.Probability.Independence.tensorization_int (m := n - 1) (r := r) (P := P)
        (ξ := ζ) hζind (η := η) (τ := 1 - (p : ℝ)) hη0 hτ0 hτ1 hr0 hrm hsmall)
  -- target event ⊆ tensorization event
  let S : Set Ω := {ω : Ω |
    (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
      η ^ 2 * ε * ((n - 1 : ℕ) : ℝ)}
  let T : Set Ω := {ω : Ω | (∑ k : Fin (n - 1), (ζ k ω) ^ 2) ≤ η ^ 2 * (r : ℝ)}
  have hST : S ⊆ T := by
    intro ω hω
    dsimp [T]
    have hrewrite : (∑ k : Fin (n - 1), (ζ k ω) ^ 2) =
        (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hrowζ k ω]
    rw [hrewrite]
    dsimp [S] at hω
    have hη2 : 0 ≤ η ^ 2 := by positivity
    nlinarith [hεr]
  have hmono : P.real S ≤ P.real T :=
    Submission.Helpers.measureReal_le_of_subset hST (measure_ne_top P T)
  exact le_trans hmono htens

/-- Bridge: a per-row Lévy-concentration bound at scale `R` (eq-aux style, for the
*unshifted* rows) implies the small-ball bound at any smaller scale `η ≤ R` needed
by `aux_single_vector`, the shift `s·Σ_j x_j` being absorbed by the interval centre. -/
lemma row_smallBall_of_cf {p : I} (hp₁ : (p : ℝ) ≤ 1 / 2) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {n : ℕ} (B : Fin (n - 1) → Fin n → Ω → ℝ) {x : Fin n → ℝ} (s : ℝ)
    {R η : ℝ} (hηR : η ≤ R)
    (hEq : ∀ (k : Fin (n - 1)) (l : ℝ),
      P.real {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l| ≤ R} ≤ (1 - (p : ℝ))) :
    ∀ k : Fin (n - 1),
      P.real {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η} ≤ (1 - (p : ℝ)) := by
  classical
  intro k
  let l₀ : ℝ := -s * (∑ j : Fin n, x j)
  have hid : ∀ ω : Ω, (∑ j : Fin n, (B k j ω + s) * x j) = (∑ j : Fin n, B k j ω * x j) - l₀ := by
    intro ω
    calc
      (∑ j : Fin n, (B k j ω + s) * x j)
          = ∑ j : Fin n, (B k j ω * x j + s * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j : Fin n, B k j ω * x j) + ∑ j : Fin n, (s * x j) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, B k j ω * x j) + s * (∑ j : Fin n, x j) := by
              congr 1
              rw [← Finset.mul_sum]
      _ = (∑ j : Fin n, B k j ω * x j) - l₀ := by
              dsimp [l₀]
              ring
  have hset : {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η} =
      {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ η} := by
    ext ω
    change |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η ↔
           |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ η
    rw [hid ω]
  have hmono : {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ η} ⊆
      {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ R} := by
    intro ω hω
    exact le_trans hω hηR
  calc
    P.real {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η}
        = P.real {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ η} := by rw [hset]
    _ ≤ P.real {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l₀| ≤ R} := by
          exact MeasureTheory.measureReal_mono hmono (measure_ne_top P _)
    _ ≤ (1 - (p : ℝ)) := hEq k l₀

end

end Submission.AuxSingleVector
