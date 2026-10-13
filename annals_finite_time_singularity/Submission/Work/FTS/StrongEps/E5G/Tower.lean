/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/Tower.lean` — the two-index tower of `ε`-solutions

`EpsUniformMem` provides, for every horizon `Tn n = n + 1`, a threshold `ε₁(n) > 0` such that the
scheme has a solution on `[0, Tn n]` for every datum `ε ≤ ε₁(n)`, with the full interface list.

For the *global* limit family of `exists_limG` we need one sequence of data `e k ↓ 0` which is below
*every* threshold: with the running minimum `mseq u k = min_{i ≤ k} u i` (antitone) one may take

  `dataSeq u k = min 1 (mseq u (k+1)) / (k+1)`,

which is positive, bounded by `1`, tends to `0` (it is squeezed by `1/(k+1)`), and satisfies
`dataSeq u k ≤ mseq u (k+1) ≤ mseq u n ≤ u n` for every `n ≤ k`.  The two-index family `G n k` of
tower solutions (`TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k)` for `n ≤ k`) is then read off the
interface.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsUniformMem_seq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The running minimum -/

/-- The running minimum of a real sequence:
`mseq u 0 = u 0`, `mseq u (k+1) = min (mseq u k) (u (k+1))`. -/
def mseq (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | (k + 1) => min (mseq u k) (u (k + 1))

theorem mseq_succ (u : ℕ → ℝ) (k : ℕ) :
    mseq u (k + 1) = min (mseq u k) (u (k + 1)) := rfl

/-- The running minimum is antitone. -/
theorem mseq_antitone (u : ℕ → ℝ) : Antitone (mseq u) := by
  intro m n hmn
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]
  | succ n ih =>
      rw [mseq_succ]
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact le_trans (min_le_left _ _) (ih (Nat.lt_succ_iff.mp h))
      · have hm : m = n + 1 := le_antisymm hmn h
        subst hm
        exact le_rfl

/-- The running minimum is below every earlier term. -/
theorem mseq_le (u : ℕ → ℝ) : ∀ k i : ℕ, i ≤ k → mseq u k ≤ u i := by
  intro k
  induction k with
  | zero =>
      intro i hi
      rw [Nat.le_zero.mp hi]
      exact le_rfl
  | succ k ih =>
      intro i hi
      rw [mseq_succ]
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact le_trans (min_le_left _ _) (ih i (Nat.lt_succ_iff.mp h))
      · subst h
        exact min_le_right _ _

/-- The running minimum of a positive sequence is positive. -/
theorem mseq_pos {u : ℕ → ℝ} (hu : ∀ k, 0 < u k) : ∀ k, 0 < mseq u k := by
  intro k
  induction k with
  | zero => exact hu 0
  | succ k ih => rw [mseq_succ]; exact lt_min ih (hu (k + 1))

/-! ## The datum sequence of the tower -/

/-- The positive sequence below every threshold: `dataSeq u k = min 1 (mseq u (k+1)) / (k+1)`. -/
def dataSeq (u : ℕ → ℝ) (k : ℕ) : ℝ := min 1 (mseq u (k + 1)) / ((k : ℝ) + 1)

theorem dataSeq_key (u : ℕ → ℝ) (k : ℕ) :
    dataSeq u k * ((k : ℝ) + 1) = min 1 (mseq u (k + 1)) := by
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  show min 1 (mseq u (k + 1)) / ((k : ℝ) + 1) * ((k : ℝ) + 1) = min 1 (mseq u (k + 1))
  exact div_mul_cancel₀ _ (ne_of_gt hd)

/-- The datum sequence is positive where the input is. -/
theorem dataSeq_pos {u : ℕ → ℝ} (hu : ∀ k, 0 < u k) (k : ℕ) : 0 < dataSeq u k :=
  div_pos (lt_min one_pos (mseq_pos hu (k + 1))) (by positivity)

/-- The running minimum of a non-negative sequence is non-negative. -/
theorem mseq_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) : ∀ k, 0 ≤ mseq u k := by
  intro k
  induction k with
  | zero => exact hu 0
  | succ k ih => rw [mseq_succ]; exact le_min ih (hu (k + 1))

/-- The datum sequence is non-negative over a non-negative input. -/
theorem dataSeq_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (k : ℕ) : 0 ≤ dataSeq u k :=
  div_nonneg (le_min zero_le_one (mseq_nonneg hu (k + 1))) (by positivity)

/-- The datum sequence is bounded by `1 / (k+1)`. -/
theorem dataSeq_bound (u : ℕ → ℝ) (k : ℕ) : dataSeq u k ≤ 1 / ((k : ℝ) + 1) := by
  have hnum : min 1 (mseq u (k + 1)) ≤ 1 := min_le_left _ _
  show min 1 (mseq u (k + 1)) / ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1)
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- The datum sequence is bounded by `1`. -/
theorem dataSeq_le_one (u : ℕ → ℝ) {k : ℕ} : dataSeq u k ≤ 1 := by
  have hb : dataSeq u k ≤ 1 / ((k : ℝ) + 1) := dataSeq_bound u k
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ hd]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  exact le_trans hb h2

/-- The datum sequence is below every threshold: `dataSeq u k ≤ u n` for `n ≤ k`. -/
theorem dataSeq_le {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) {n k : ℕ} (hnk : n ≤ k) :
    dataSeq u k ≤ u n := by
  have hnum : min 1 (mseq u (k + 1)) ≤ mseq u (k + 1) := min_le_right _ _
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ mseq u (k + 1) := mseq_nonneg hu (k + 1)
  have h1 : dataSeq u k ≤ mseq u (k + 1) := by
    show min 1 (mseq u (k + 1)) / ((k : ℝ) + 1) ≤ mseq u (k + 1)
    rw [div_le_iff₀ hd]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    nlinarith [hnum, hk, hnonneg]
  refine le_trans h1 (le_trans (mseq_antitone u (Nat.le_succ_of_le hnk)) ?_)
  exact mseq_le u n n le_rfl

/-- The datum sequence tends to zero. -/
theorem dataSeq_tendsto {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) : Tendsto (dataSeq u) atTop (nhds 0) := by
  refine squeeze_zero (fun k => dataSeq_nonneg hu k) (fun k => dataSeq_bound u k) ?_
  simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-! ## The tower -/

/-- **The tower of `ε`-solutions.**  From `EpsUniformMem` there are a positive sequence `e ↓ 0`
bounded by `1`, a level-`6` bound `K'` for every horizon, and a two-index family of solutions
`G n k` solving the scheme at horizon `Tn n` with datum `e k`, with the whole interface list, for
every `n ≤ k`. -/
theorem tower_exists {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) :
    ∃ (e : ℕ → ℝ) (G : ℕ → ℕ → Fam) (K' : ℕ → ℝ),
      (∀ k : ℕ, e k ∈ Set.Ioc 0 1) ∧ Tendsto e atTop (nhds 0) ∧
      (∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k)) := by
  classical
  -- the per-horizon interface data
  have hper : ∀ n : ℕ, ∃ K' ε₁ : ℝ, K ≤ K' ∧ 0 < ε₁ ∧
      ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam, TowerAt α C₀ ρ Φs E g₀ n ε K' g := by
    intro n
    obtain ⟨K', hK', ε₁, hε₁, Maj, _hMaj, hg⟩ := hU.2.2 (Tn n) (Tn_pos n)
    refine ⟨K', ε₁, hK', hε₁, fun ε hε => ?_⟩
    obtain ⟨g, hsol, hcl⟩ := hg ε hε
    have h0 := hcl 0 ⟨le_rfl, (Tn_pos n).le⟩
    exact ⟨g, ⟨hsol, fun τ hτ => (hcl τ hτ).1, fun τ hτ => (hcl τ hτ).2.1,
      fun τ hτ => (hcl τ hτ).2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.1,
      fun τ hτ => (hcl τ hτ).2.2.2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.2.2.1,
      h0.2.2.2.2.2.2.1⟩⟩
  let K' : ℕ → ℝ := fun n => Classical.choose (hper n)
  let ε₁ : ℕ → ℝ := fun n => Classical.choose (Classical.choose_spec (hper n))
  have hε₁pos : ∀ n : ℕ, 0 < ε₁ n := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hper n))).2.1
  have hg : ∀ n : ℕ, ∀ ε ∈ Set.Ioc 0 (ε₁ n), ∃ g : Fam,
      TowerAt α C₀ ρ Φs E g₀ n ε (K' n) g := fun n =>
    (Classical.choose_spec (Classical.choose_spec (hper n))).2.2
  -- the global datum sequence
  refine ⟨dataSeq ε₁, fun n k => if h : n ≤ k then
      Classical.choose (hg n (dataSeq ε₁ k)
        ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) h⟩)
      else fun z θ _ => g₀ z θ,
    K', ⟨fun k => ⟨dataSeq_pos hε₁pos k, dataSeq_le_one ε₁⟩,
      dataSeq_tendsto (fun k => (hε₁pos k).le), ?_⟩⟩
  intro n k hnk
  have h := Classical.choose_spec (hg n (dataSeq ε₁ k)
    ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) hnk⟩)
  simpa only [dif_pos hnk] using h

end Work.FTS.StrongEps.E5G
