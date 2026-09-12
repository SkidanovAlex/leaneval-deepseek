import Submission.Work.UncDiagonal

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Sequential-continuity assembly at degenerate heights: the splitting layer

WORK IN PROGRESS — the subsequence-splitting machinery (GREEN so far).

An arbitrary sequence of heights `zₙ → y₀` at a degenerate height mixes
the four `height_case` regions (U / flat-interior / covered / uncovered)
arbitrarily.  To conclude `leafSlope zₙ → leafSlope y₀` from the
per-region convergence theorems, one shows: if `leafSlope∘z` did NOT
converge, a bad subsequence (`ε ≤ |·−L|`) exists; by infinite pigeonhole
that subsequence has a further subsequence lying entirely in ONE region
(splitting lemma below); the corresponding region theorem contradicts the
badness.  This file supplies the index bookkeeping:

* `Set.infinite_iff_exists_strictMono` — a subset of ℕ is infinite iff it
  contains the range of a strictly increasing sequence;
* `exists_bad_subseq_of_not_tendsto` — a real sequence not converging to
  `L` has a subsequence bounded away from `L` by a positive `ε`;
* **`refine_four_regions`** — the splitting lemma: every subsequence of a
  height sequence has a further subsequence lying entirely in one of the
  four `height_case` regions (U / FI / Cov / Unc);
* `region_case_of_height` — the exclusive four-way decomposition of a
  single height.

Next (later sessions): restrict each region to its fine sub-class (FI
below/above the frontier, etc.) with eventual trimming, instantiate the
six per-region convergence theorems, and assemble
`leafSlope_tendsto_of_tendsto` at degenerate heights → `ContinuousAt` of
`leafSlope`/`spliceA1`/`spliceB1`.

Build: `lake build Submission.Work.SequentialContinuityDegenerate` rc=0,
zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-! ## 1. Infinite subsets of ℕ are enumerated by strict monotone maps -/

/-- A subset `S ⊆ ℕ` is infinite iff it contains the range of a strictly
increasing sequence. -/
lemma Set.infinite_iff_exists_strictMono {S : Set ℕ} :
    S.Infinite ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, φ n ∈ S := by
  constructor
  · intro hS
    have hgt : ∀ a : ℕ, ∃ b : ℕ, b ∈ S ∧ a < b := by
      intro a
      exact (Set.infinite_iff_exists_gt.mp hS) a
    let g : ℕ → ℕ := fun a => Classical.choose (hgt a)
    have hg : ∀ a : ℕ, g a ∈ S ∧ a < g a := fun a => Classical.choose_spec (hgt a)
    let φ : ℕ → ℕ := fun n => Nat.recOn n (g 0) (fun m acc => g (acc + 1))
    refine ⟨φ, ?_, ?_⟩
    · refine strictMono_nat_of_lt_succ ?_
      intro m
      have hred : φ (m + 1) = g (φ m + 1) := rfl
      have hlt1 : φ m < φ m + 1 := by omega
      have h2 : φ m + 1 ≤ g (φ m + 1) := le_of_lt (hg (φ m + 1)).2
      rw [hred]
      omega
    · intro n
      induction n with
      | zero =>
        dsimp [φ]
        exact (hg 0).1
      | succ m ih =>
        dsimp [φ]
        exact (hg (φ m + 1)).1
  · rintro ⟨φ, hφ, hφS⟩
  -- the range of a strict monotone map is infinite, and it lies in S
    have hinf : (Set.range φ).Infinite := by
      have hinj : Function.Injective φ := hφ.injective
      exact Set.infinite_range_of_injective hinj
    exact hinf.mono (by rintro x ⟨m, rfl⟩; exact hφS m)

/-! ## 2. Bad subsequences of non-convergent sequences -/

/-- A real sequence that does not converge to `L` has a subsequence whose
terms stay `ε`-away from `L`. -/
lemma exists_bad_subseq_of_not_tendsto {u : ℕ → ℝ} {L : ℝ}
    (h : ¬ Tendsto u atTop (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, ε ≤ |u (φ n) - L| := by
  classical
  have hε0 : ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |u n - L| := by
    by_contra hn
    apply h
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_contra hnε
    push_neg at hnε
    have hb' : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ |u n - L| := by
      intro N
      rcases hnε N with ⟨n, hN, hd⟩
      refine ⟨n, hN, ?_⟩
      simpa [Real.dist_eq] using hd
    exact hn ⟨ε, hε, hb'⟩
  rcases hε0 with ⟨ε, hε, hb⟩
  refine ⟨ε, hε, ?_⟩
  let g : ℕ → ℕ := fun N => Classical.choose (hb N)
  have hg : ∀ N : ℕ, N ≤ g N ∧ ε ≤ |u (g N) - L| := fun N => Classical.choose_spec (hb N)
  let φ : ℕ → ℕ := fun n => Nat.recOn n (g 0) (fun m acc => g (acc + 1))
  refine ⟨φ, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ ?_
    intro m
    have h1 : φ m < φ m + 1 := by omega
    have h2 : φ m + 1 ≤ g (φ m + 1) := (hg (φ m + 1)).1
    have h2' : φ m + 1 ≤ g (φ m + 1) := h2
    have h3 : φ m + 1 ≤ φ (m + 1) := by
      dsimp [φ]
      exact h2'
    omega
  · intro n
    induction n with
    | zero =>
      dsimp [φ]
      exact (hg 0).2
    | succ m ih =>
      dsimp [φ]
      exact (hg (φ m + 1)).2

/-! ## 3. The four-region splitting lemma -/

/-- The exclusive four-way `height_case` decomposition of a single height
(restated for convenient use). -/
lemma region_case_of_height {a : ℝ} {f : ℝ² → ℝ³} (y : ℝ) :
    y ∈ UHeight a f ∨ IsFlatInterior f (centrePoint y) ∨
      CoveredDegenerate (a := a) (f := f) y ∨ UncoveredDegenerate (a := a) (f := f) y :=
  height_case y

/-- **The splitting lemma**: every subsequence of a height sequence has a
further subsequence lying entirely in one of the four `height_case`
regions. -/
theorem refine_four_regions {a : ℝ} {f : ℝ² → ℝ³} {z : ℕ → ℝ} {φ : ℕ → ℕ} :
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ m : ℕ, z (φ (ψ m)) ∈ UHeight a f) ∨
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ m : ℕ, IsFlatInterior f (centrePoint (z (φ (ψ m))))) ∨
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ m : ℕ, CoveredDegenerate (a := a) (f := f) (z (φ (ψ m)))) ∨
    (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ m : ℕ, UncoveredDegenerate (a := a) (f := f) (z (φ (ψ m)))) := by
  classical
  let S₁ : Set ℕ := {m : ℕ | z (φ m) ∈ UHeight a f}
  let S₂ : Set ℕ := {m : ℕ | IsFlatInterior f (centrePoint (z (φ m)))}
  let S₃ : Set ℕ := {m : ℕ | CoveredDegenerate (a := a) (f := f) (z (φ m))}
  let S₄ : Set ℕ := {m : ℕ | UncoveredDegenerate (a := a) (f := f) (z (φ m))}
  have hcov : (S₁ ∪ S₂ ∪ S₃ ∪ S₄ : Set ℕ) = Set.univ := by
    ext m
    constructor
    · intro hm
      trivial
    · intro hm
      have hc := height_case (a := a) (f := f) (z (φ m))
      simp [S₁, S₂, S₃, S₄] at hc ⊢
      tauto
  have hinf : (S₁.Infinite ∨ S₂.Infinite ∨ S₃.Infinite ∨ S₄.Infinite) := by
    by_contra hnone
    push_neg at hnone
    have hfin₁ : S₁.Finite := hnone.1
    have hfin₂ : S₂.Finite := hnone.2.1
    have hfin₃ : S₃.Finite := hnone.2.2.1
    have hfin₄ : S₄.Finite := hnone.2.2.2
    have hfinU : (S₁ ∪ S₂ ∪ S₃ ∪ S₄).Finite := by
      have hA : (S₁ ∪ S₂).Finite := hfin₁.union hfin₂
      have hB : (S₃ ∪ S₄).Finite := hfin₃.union hfin₄
      have hAB : ((S₁ ∪ S₂) ∪ (S₃ ∪ S₄)).Finite := hA.union hB
      simpa [Set.union_assoc] using hAB
    have : (Set.univ : Set ℕ).Finite := by rwa [← hcov]
    exact Set.infinite_univ this
  rcases hinf with h₁ | h₂ | h₃ | h₄
  · left
    rcases (Set.infinite_iff_exists_strictMono.mp h₁) with ⟨ψ, hψ, hψS⟩
    refine ⟨ψ, hψ, ?_⟩
    intro m
    have hm : ψ m ∈ S₁ := hψS m
    dsimp [S₁] at hm
    exact hm
  · right; left
    rcases (Set.infinite_iff_exists_strictMono.mp h₂) with ⟨ψ, hψ, hψS⟩
    refine ⟨ψ, hψ, ?_⟩
    intro m
    have hm : ψ m ∈ S₂ := hψS m
    dsimp [S₂] at hm
    exact hm
  · right; right; left
    rcases (Set.infinite_iff_exists_strictMono.mp h₃) with ⟨ψ, hψ, hψS⟩
    refine ⟨ψ, hψ, ?_⟩
    intro m
    have hm : ψ m ∈ S₃ := hψS m
    dsimp [S₃] at hm
    exact hm
  · right; right; right
    rcases (Set.infinite_iff_exists_strictMono.mp h₄) with ⟨ψ, hψ, hψS⟩
    refine ⟨ψ, hψ, ?_⟩
    intro m
    have hm : ψ m ∈ S₄ := hψS m
    dsimp [S₄] at hm
    exact hm

end Submission
