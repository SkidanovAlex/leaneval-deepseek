import Submission.Work.SequentialContinuityDegenerate

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Fine sub-classes of the height regions at a covered upper frontier

The sequential-continuity assembly at a covered height `y₀ = bw₂ p₀ hp₀`
(upper frontier of the component `C₀`) splits approaching heights by
region AND by side of the frontier.  This file fixes the fine sub-classes
and proves the eventual-trimming facts that turn "eventually in the
sub-class" into the ∀-index hypotheses of the per-region convergence
theorems (`DegenerateLimit`/`OuterSqueeze`/`UncDiagonal`).

Fine sub-classes (predicates on a height `y`, relative to `p₀,hp₀`):
* `FiBelow` — flat-interior and below the frontier (`y < bw₂`): near
  `y₀` these lie in `C₀`'s own centre interval `(bw₁,bw₂)`;
* `FiAbove` — flat-interior and above the frontier (`bw₂ < y`): other
  components' interior heights (the `above(Γ₂)` case);
* `CovAbove` — covered and above the frontier (frontier heights of other
  components; covered heights cannot approach from inside `C₀`);
* (U and Unc classes need no side split.)

Key lemmas (GREEN):
* **`fi_below_eventually_interval`** — the eventual trimming lemma: a
  height sequence converging to `bw₂`, at flat-interior heights below
  `bw₂`, is EVENTUALLY inside `(bw₁,bw₂)` (the interior heights of `C₀`
  are exactly its centre interval; the trimming only uses
  `zₙ → bw₂` and `zₙ < bw₂`);
* `fi_below_sub` / `fi_above_sub` — the sub-classes imply their defining
  conditions.

Build: `lake build Submission.Work.FrontierFine` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- Flat-interior height BELOW the upper frontier height `bw₂` of a
component (near `bw₂` these lie in the component's own centre interval). -/
def FiBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  IsFlatInterior f (centrePoint y) ∧ y < bw₂ hf ha hp₀

/-- Flat-interior height ABOVE the upper frontier height `bw₂` of a
component (interior heights of OTHER components on the outer side). -/
def FiAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  IsFlatInterior f (centrePoint y) ∧ bw₂ hf ha hp₀ < y

/-- Covered height ABOVE the upper frontier height `bw₂` (frontier heights
of other components; covered heights cannot approach `bw₂` from inside). -/
def CovAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  CoveredHeight (f := f) y ∧ bw₂ hf ha hp₀ < y

/-- The flat-interior component of `FiBelow`. -/
lemma FiBelow_fi {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiBelow hf ha hp₀ y) : IsFlatInterior f (centrePoint y) := h.1

/-- `FiBelow` heights are below the frontier. -/
lemma FiBelow_lt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiBelow hf ha hp₀ y) : y < bw₂ hf ha hp₀ := h.2

/-- The flat-interior component of `FiAbove`. -/
lemma FiAbove_fi {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiAbove hf ha hp₀ y) : IsFlatInterior f (centrePoint y) := h.1

/-- `FiAbove` heights are above the frontier. -/
lemma FiAbove_gt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiAbove hf ha hp₀ y) : bw₂ hf ha hp₀ < y := h.2

/-- The covered component of `CovAbove`. -/
lemma CovAbove_cov {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : CovAbove hf ha hp₀ y) : CoveredHeight (f := f) y := h.1

/-- `CovAbove` heights are above the frontier. -/
lemma CovAbove_gt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : CovAbove hf ha hp₀ y) : bw₂ hf ha hp₀ < y := h.2

/-- **The eventual-trimming lemma (FI below)**: heights converging to the
upper frontier height `bw₂` of a component, flat-interior and below it,
are EVENTUALLY inside the component's own centre interval
`(bw₁,bw₂)` — the hypothesis domain of
`leafSlope_tendsto_of_interval_to_upper`. -/
theorem fi_below_eventually_interval {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ∀ᶠ n in atTop, FiBelow hf ha hp₀ (z n) →
      z n ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
  have hδ : 0 < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := sub_pos.mpr (bwlt hf ha hp₀)
  rcases (Metric.tendsto_atTop.mp hz) (bw₂ hf ha hp₀ - bw₁ hf ha hp₀) hδ with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn hcl
  have hclose : |z n - bw₂ hf ha hp₀| < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := by
    simpa [Real.dist_eq] using hN n hn
  rw [Set.mem_Ioo]
  constructor
  · -- bw₁ < z n
    have hz' : z n - bw₂ hf ha hp₀ > bw₁ hf ha hp₀ - bw₂ hf ha hp₀ := by
      rw [abs_lt] at hclose
      have hlo := hclose.1
      linarith
    linarith
  · exact FiBelow_lt hf ha hp₀ hcl

/-- The `FiAbove` class implies the outer-FI theorem hypotheses (flat-
interior and strictly above the frontier). -/
lemma fi_above_hyps {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiAbove hf ha hp₀ y) :
    IsFlatInterior f (centrePoint y) ∧ bw₂ hf ha hp₀ < y :=
  ⟨FiAbove_fi hf ha hp₀ h, FiAbove_gt hf ha hp₀ h⟩


/-! ## Restricted class-convergence (ε-form) and the inner-FI case -/

/-- A sequence converges to `L` ON the class `C`: indices whose values lie
in the class eventually have values ε-close to `L`. -/
def ConvergesOnClass (u : ℕ → ℝ) (L : ℝ) (C : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C n → |u n - L| < ε

/-- A "bad" hypothesis on the class: from every `N` an index `n ≥ N` in
the class with value ε-away from `L`. -/
lemma exists_bad_in_class {u : ℕ → ℝ} {L : ℝ} {C : ℕ → Prop} (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ C n ∧ ε ≤ |u n - L|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ m : ℕ, C (φ m)) ∧ ∀ m : ℕ, ε ≤ |u (φ m) - L| := by
  classical
  let g : ℕ → ℕ := fun N => Classical.choose (hbad N)
  have hg : ∀ N : ℕ, N ≤ g N ∧ C (g N) ∧ ε ≤ |u (g N) - L| := fun N =>
    Classical.choose_spec (hbad N)
  let φ : ℕ → ℕ := fun n => Nat.recOn n (g 0) (fun m acc => g (acc + 1))
  refine ⟨φ, ?_, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ ?_
    intro m
    have hred : φ (m + 1) = g (φ m + 1) := rfl
    have hlt1 : φ m < φ m + 1 := by omega
    have h2 : φ m + 1 ≤ g (φ m + 1) := (hg (φ m + 1)).1
    rw [hred]
    omega
  · intro m
    induction m with
    | zero =>
      dsimp [φ]
      exact (hg 0).2.1
    | succ m ih =>
      dsimp [φ]
      exact (hg (φ m + 1)).2.1
  · intro m
    induction m with
    | zero =>
      dsimp [φ]
      exact (hg 0).2.2
    | succ m ih =>
      dsimp [φ]
      exact (hg (φ m + 1)).2.2

/-- If the index set splits into four classes and the sequence converges
to `L` on each class, it converges to `L` on all of `ℕ`. -/
lemma tendsto_of_classwise {u : ℕ → ℝ} {L : ℝ} {C₁ C₂ C₃ C₄ : ℕ → Prop}
    (hsplit : ∀ n : ℕ, C₁ n ∨ C₂ n ∨ C₃ n ∨ C₄ n)
    (h₁ : ConvergesOnClass u L C₁) (h₂ : ConvergesOnClass u L C₂)
    (h₃ : ConvergesOnClass u L C₃) (h₄ : ConvergesOnClass u L C₄) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases h₁ ε hε with ⟨N₁, hN₁⟩
  rcases h₂ ε hε with ⟨N₂, hN₂⟩
  rcases h₃ ε hε with ⟨N₃, hN₃⟩
  rcases h₄ ε hε with ⟨N₄, hN₄⟩
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro n hn
  rcases hsplit n with hc₁ | hc₂ | hc₃ | hc₄
  · have hn₁ : N₁ ≤ n := by omega
    simpa [Real.dist_eq] using hN₁ n hn₁ hc₁
  · have hn₂ : N₂ ≤ n := by omega
    simpa [Real.dist_eq] using hN₂ n hn₂ hc₂
  · have hn₃ : N₃ ≤ n := by omega
    simpa [Real.dist_eq] using hN₃ n hn₃ hc₃
  · have hn₄ : N₄ ≤ n := by omega
    simpa [Real.dist_eq] using hN₄ n hn₄ hc₄

/-- **Inner-FI restricted convergence**: among the indices whose heights
are flat-interior BELOW the upper frontier (the `FiBelow` class), the leaf
slopes converge to the frontier slope.  (Trimming puts the class values
eventually into `(bw₁,bw₂)`; a bad class subsequence then contradicts
`leafSlope_tendsto_of_interval_to_upper`.) -/
theorem leafSlope_converges_fiBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀)) (fun n : ℕ => FiBelow hf ha hp₀ (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ FiBelow hf ha hp₀ (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₂ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hIntE : ∀ᶠ m in atTop,
      z (φ m) ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
    have htrim := fi_below_eventually_interval hf ha hp₀ (z := fun m : ℕ => z (φ m)) hzφ
    filter_upwards [htrim] with m hm
    exact hm (hφC m)
  rcases Filter.eventually_atTop.mp hIntE with ⟨M, hM⟩
  let w : ℕ → ℝ := fun m : ℕ => z (φ (m + M))
  have hwI : ∀ m : ℕ, w m ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
    intro m
    dsimp [w]
    have hm' : M ≤ m + M := by omega
    exact hM (m + M) hm'
  have hw : Tendsto w atTop (𝓝 (bw₂ hf ha hp₀)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rcases (Metric.tendsto_atTop.mp hzφ) δ hδ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    dsimp [w]
    have hge : N ≤ m + M := by omega
    simpa [Real.dist_eq] using hN (m + M) hge
  have hlim := leafSlope_tendsto_of_interval_to_upper hf ha hp₀ (z := w) hwI hw
  have hbadW : ∀ m : ℕ, ε ≤ |leafSlope hf ha (w m) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro m
    dsimp [w]
    exact hφbad (m + M)
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₂ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb := hbadW N₂
  linarith



/-- **Outer-FI restricted convergence**: among indices whose heights are
flat-interior ABOVE the upper frontier (the `FiAbove` class), leaf slopes
converge to the frontier slope. -/
theorem leafSlope_converges_fiAbove {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀)) (fun n : ℕ => FiAbove hf ha hp₀ (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ FiAbove hf ha hp₀ (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₂ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hzF : ∀ m : ℕ, IsFlatInterior f (centrePoint (z (φ m))) := fun m =>
    (hφC m).1
  have hgt : ∀ m : ℕ, bw₂ hf ha hp₀ < z (φ m) := fun m => (hφC m).2
  have hlim := leafSlope_tendsto_fi_outer_upper hf ha hp₀ (z := fun m => z (φ m))
    hzF hgt hzφ
  have hbadφ : ∀ m : ℕ,
      ε ≤ |leafSlope hf ha (z (φ m)) - leafSlope hf ha (bw₂ hf ha hp₀)| := hφbad
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc : |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| := hφbad N
  linarith

/-- The `UHeight` class restricted convergence at a covered height. -/
theorem leafSlope_converges_uHeight_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀)) (fun n : ℕ => z n ∈ UHeight a f) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ z n ∈ UHeight a f ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₂ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hc0 : CoveredHeight (f := f) (bw₂ hf ha hp₀) :=
    ⟨p₀, hp₀, bwhh₂ hf ha hp₀⟩
  have hlim := leafSlope_tendsto_uHeight_of_covered hf ha hc0
    (z := fun m => z (φ m)) (hzU := hφC) hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc : |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| := hφbad N
  linarith

/-- An `UncoveredDegenerate` height is flat (in `FlatHeight`). -/
lemma UncoveredDegenerate_mem_FlatHeight {a : ℝ} {f : ℝ² → ℝ³} {y : ℝ}
    (hu : UncoveredDegenerate (a := a) (f := f) y) : y ∈ FlatHeight a f := by
  have hyU : y ∉ UHeight a f := hu.1
  by_contra hyF
  exact hyU ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr hyF)

/-- The UNCOVERED class restricted convergence at a covered height. -/
theorem leafSlope_converges_unc_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀))
      (fun n : ℕ => UncoveredDegenerate (a := a) (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UncoveredDegenerate (a := a) (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₂ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have huF : ∀ m : ℕ, z (φ m) ∈ FlatHeight a f := fun m =>
    UncoveredDegenerate_mem_FlatHeight (hφC m)
  have huni : ∀ m : ℕ, ¬ IsFlatInterior f (centrePoint (z (φ m))) := fun m =>
    (hφC m).2.1
  have huunc : ∀ m : ℕ, ¬ CoveredHeight (f := f) (z (φ m)) := fun m =>
    (hφC m).2.2
  have hc0 : CoveredHeight (f := f) (bw₂ hf ha hp₀) :=
    ⟨p₀, hp₀, bwhh₂ hf ha hp₀⟩
  have hlim := leafSlope_tendsto_uncovered_of_covered hf ha hc0 huF huni huunc hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc : |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₂ hf ha hp₀)| := hφbad N
  linarith



/-- A covered height in `(bw₁,bw₂]` cannot be strictly below `bw₂` (the
open interval consists of flat-INTERIOR heights); hence a bad covered
sequence (values ε-away from the frontier slope) is eventually strictly
ABOVE `bw₂`. -/
lemma cov_class_eventually_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {w : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hw : Tendsto w atTop (𝓝 (bw₂ hf ha hp₀)))
    (hwcov : ∀ m : ℕ, CoveredHeight (f := f) (w m))
    (hwbad : ∀ m : ℕ,
      ε ≤ |leafSlope hf ha (w m) - leafSlope hf ha (bw₂ hf ha hp₀)|) :
    ∀ᶠ m in atTop, bw₂ hf ha hp₀ < w m := by
  classical
  have hδ : 0 < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := sub_pos.mpr (bwlt hf ha hp₀)
  rcases (Metric.tendsto_atTop.mp hw) (bw₂ hf ha hp₀ - bw₁ hf ha hp₀) hδ with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  by_contra hle
  have hle' : w n ≤ bw₂ hf ha hp₀ := le_of_not_gt hle
  have hclose : |w n - bw₂ hf ha hp₀| < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := by
    simpa [Real.dist_eq] using hN n hn
  have hgtbw1 : bw₁ hf ha hp₀ < w n := by
    rw [abs_lt] at hclose
    linarith
  by_cases heq : w n = bw₂ hf ha hp₀
  · have hval : leafSlope hf ha (w n) = leafSlope hf ha (bw₂ hf ha hp₀) := by rw [heq]
    have hb := hwbad n
    rw [hval] at hb
    have hzero : |leafSlope hf ha (bw₂ hf ha hp₀) - leafSlope hf ha (bw₂ hf ha hp₀)| = 0 := by simp
    rw [hzero] at hb
    linarith
  · have hltbw2 : w n < bw₂ hf ha hp₀ := lt_of_le_of_ne hle' heq
    have hin : w n ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
      rw [Set.mem_Ioo]
      exact ⟨hgtbw1, hltbw2⟩
    have hfi : IsFlatInterior f (centrePoint (w n)) :=
      flatInterior_of_mem_centreInterval hf ha hp₀ hin
    exact (covered_not_flatInterior (hwcov n)) hfi

/-- **Cov-class restricted convergence**: among indices whose heights are
COVERED, leaf slopes converge to the frontier slope at the covered height
`bw₂`.  (A bad covered subsequence is eventually strictly above `bw₂` by
`cov_class_eventually_above`, then contradicts
`leafSlope_tendsto_cov_outer_upper`.) -/
theorem leafSlope_converges_cov_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀)) (fun n : ℕ => CoveredHeight (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ CoveredHeight (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₂ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have haboveE := cov_class_eventually_above hf ha hp₀ (ε := ε) hε hzφ hφC hφbad
  rcases Filter.eventually_atTop.mp haboveE with ⟨M, hM⟩
  let w : ℕ → ℝ := fun m : ℕ => z (φ (m + M))
  have hwgt : ∀ m : ℕ, bw₂ hf ha hp₀ < w m := by
    intro m
    dsimp [w]
    have hm' : M ≤ m + M := by omega
    exact hM (m + M) hm'
  have hwcov : ∀ m : ℕ, CoveredHeight (f := f) (w m) := by
    intro m
    dsimp [w]
    exact hφC (m + M)
  have hw : Tendsto w atTop (𝓝 (bw₂ hf ha hp₀)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rcases (Metric.tendsto_atTop.mp hzφ) δ hδ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    dsimp [w]
    have hge : N ≤ m + M := by omega
    simpa [Real.dist_eq] using hN (m + M) hge
  have hlim := leafSlope_tendsto_cov_outer_upper hf ha hp₀ (c := w) hwcov hwgt hw
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₂ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₂ hf ha hp₀)| := by
    dsimp [w]
    exact hφbad (N₂ + M)
  linarith



/-! ## Merging classes and the FULL sequential continuity at the upper
frontier height -/

/-- Convergence on a class transfers to a smaller class. -/
lemma ConvergesOnClass.mono {u : ℕ → ℝ} {L : ℝ} {C D : ℕ → Prop}
    (h : ConvergesOnClass u L D) (hsub : ∀ n : ℕ, C n → D n) :
    ConvergesOnClass u L C := by
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hC
  exact hN n hn (hsub n hC)

/-- Flat-interior heights are never the covered frontier height `bw₂`
(the frontier chord is flat NON-interior). -/
lemma not_fi_at_bw₂ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) :
    ¬ IsFlatInterior f (centrePoint (bw₂ hf ha hp₀)) := by
  exact covered_not_flatInterior
    (⟨p₀, hp₀, bwhh₂ hf ha hp₀⟩ : CoveredHeight (f := f) (bw₂ hf ha hp₀))

/-- The FLAT-INTERIOR class restricted convergence (all interior heights,
below or above the frontier; the `= bw₂` case is impossible). -/
theorem leafSlope_converges_fi_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀))
      (fun n : ℕ => IsFlatInterior f (centrePoint (z n))) := by
  classical
  intro ε hε
  have hlow := leafSlope_converges_fiBelow hf ha hp₀ hz ε hε
  have hhigh := leafSlope_converges_fiAbove hf ha hp₀ hz ε hε
  rcases hlow with ⟨N₁, hN₁⟩
  rcases hhigh with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn hfi
  have hne : z n ≠ bw₂ hf ha hp₀ := by
    intro hz₀
    have : IsFlatInterior f (centrePoint (bw₂ hf ha hp₀)) := by
      rwa [← hz₀]
    exact (not_fi_at_bw₂ hf ha hp₀) this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn₁ : N₁ ≤ n := by omega
    exact hN₁ n hn₁ ⟨hfi, hlt⟩
  · have hn₂ : N₂ ≤ n := by omega
    exact hN₂ n hn₂ ⟨hfi, hgt⟩

/-- The COVERED-DEGENERATE class restricted convergence (subset of the
covered class). -/
theorem leafSlope_converges_covDegenerate_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₂ hf ha hp₀))
      (fun n : ℕ => CoveredDegenerate (a := a) (f := f) (z n)) := by
  apply ConvergesOnClass.mono (leafSlope_converges_cov_of_covered hf ha hp₀ hz)
  intro n hc
  exact hc.2.2

/-- **FULL sequential continuity of `leafSlope` at the upper frontier
height**: ANY height sequence converging to `bw₂` of a component has leaf
slopes converging to the spliced leaf slope there (split into the four
`height_case` classes, each converging by the restricted theorems). -/
theorem leafSlope_tendsto_at_upper {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₂ hf ha hp₀))) := by
  apply tendsto_of_classwise (u := fun n : ℕ => leafSlope hf ha (z n))
    (L := leafSlope hf ha (bw₂ hf ha hp₀))
    (C₁ := fun n : ℕ => z n ∈ UHeight a f)
    (C₂ := fun n : ℕ => IsFlatInterior f (centrePoint (z n)))
    (C₃ := fun n : ℕ => CoveredDegenerate (a := a) (f := f) (z n))
    (C₄ := fun n : ℕ => UncoveredDegenerate (a := a) (f := f) (z n))
  · intro n
    exact height_case (a := a) (f := f) (z n)
  · exact leafSlope_converges_uHeight_of_covered hf ha hp₀ hz
  · exact leafSlope_converges_fi_of_covered hf ha hp₀ hz
  · exact leafSlope_converges_covDegenerate_of_covered hf ha hp₀ hz
  · exact leafSlope_converges_unc_of_covered hf ha hp₀ hz



/-! ## Lower-frontier fine classes and trimming (mirror of the upper) -/

/-- Flat-interior height ABOVE the lower frontier height `bw₁` of a
component (near `bw₁` these lie in the component's own centre interval
`(bw₁,bw₂)`). -/
def FiInnerLower {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  IsFlatInterior f (centrePoint y) ∧ bw₁ hf ha hp₀ < y

/-- Flat-interior height BELOW the lower frontier height `bw₁` of a
component (interior heights of OTHER components on the outer side). -/
def FiOuterLower {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  IsFlatInterior f (centrePoint y) ∧ y < bw₁ hf ha hp₀

/-- Covered height BELOW the lower frontier height `bw₁` (frontier
heights of other components on the outer side). -/
def CovBelow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) (y : ℝ) : Prop :=
  CoveredHeight (f := f) y ∧ y < bw₁ hf ha hp₀

/-- The flat-interior component of `FiInnerLower`. -/
lemma FiInnerLower_fi {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiInnerLower hf ha hp₀ y) : IsFlatInterior f (centrePoint y) := h.1

/-- `FiInnerLower` heights are above the lower frontier. -/
lemma FiInnerLower_gt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiInnerLower hf ha hp₀ y) : bw₁ hf ha hp₀ < y := h.2

/-- The flat-interior component of `FiOuterLower`. -/
lemma FiOuterLower_fi {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiOuterLower hf ha hp₀ y) : IsFlatInterior f (centrePoint y) := h.1

/-- `FiOuterLower` heights are below the lower frontier. -/
lemma FiOuterLower_lt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : FiOuterLower hf ha hp₀ y) : y < bw₁ hf ha hp₀ := h.2

/-- The covered component of `CovBelow`. -/
lemma CovBelow_cov {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : CovBelow hf ha hp₀ y) : CoveredHeight (f := f) y := h.1

/-- `CovBelow` heights are below the lower frontier. -/
lemma CovBelow_lt {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {y : ℝ}
    (h : CovBelow hf ha hp₀ y) : y < bw₁ hf ha hp₀ := h.2

/-- **The eventual-trimming lemma (lower, inner)**: heights converging to
the lower frontier height `bw₁` of a component, flat-interior and above
it, are EVENTUALLY inside the component's centre interval
`(bw₁,bw₂)` — the hypothesis domain of
`leafSlope_tendsto_of_interval_to_lower`. -/
theorem fi_inner_lower_eventually_interval {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ∀ᶠ n in atTop, FiInnerLower hf ha hp₀ (z n) →
      z n ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
  have hδ : 0 < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := sub_pos.mpr (bwlt hf ha hp₀)
  rcases (Metric.tendsto_atTop.mp hz) (bw₂ hf ha hp₀ - bw₁ hf ha hp₀) hδ with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn hcl
  have hclose : |z n - bw₁ hf ha hp₀| < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := by
    simpa [Real.dist_eq] using hN n hn
  rw [Set.mem_Ioo]
  constructor
  · exact FiInnerLower_gt hf ha hp₀ hcl
  · have hz' : z n - bw₁ hf ha hp₀ < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := by
      rw [abs_lt] at hclose
      exact hclose.2
    linarith

/-- A covered height in `[bw₁,bw₂)` cannot be strictly above `bw₁` (the
open interval `(bw₁,bw₂)` consists of flat-INTERIOR heights); hence a bad
covered sequence (values ε-away from the lower frontier slope) is
eventually strictly BELOW `bw₁`. -/
lemma cov_class_eventually_below {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {w : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hw : Tendsto w atTop (𝓝 (bw₁ hf ha hp₀)))
    (hwcov : ∀ m : ℕ, CoveredHeight (f := f) (w m))
    (hwbad : ∀ m : ℕ,
      ε ≤ |leafSlope hf ha (w m) - leafSlope hf ha (bw₁ hf ha hp₀)|) :
    ∀ᶠ m in atTop, w m < bw₁ hf ha hp₀ := by
  classical
  have hδ : 0 < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := sub_pos.mpr (bwlt hf ha hp₀)
  rcases (Metric.tendsto_atTop.mp hw) (bw₂ hf ha hp₀ - bw₁ hf ha hp₀) hδ with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  by_contra hge
  have hge' : bw₁ hf ha hp₀ ≤ w n := le_of_not_gt hge
  have hclose : |w n - bw₁ hf ha hp₀| < bw₂ hf ha hp₀ - bw₁ hf ha hp₀ := by
    simpa [Real.dist_eq] using hN n hn
  have hltbw2 : w n < bw₂ hf ha hp₀ := by
    rw [abs_lt] at hclose
    linarith
  by_cases heq : w n = bw₁ hf ha hp₀
  · have hval : leafSlope hf ha (w n) = leafSlope hf ha (bw₁ hf ha hp₀) := by rw [heq]
    have hb := hwbad n
    rw [hval] at hb
    have hzero : |leafSlope hf ha (bw₁ hf ha hp₀) - leafSlope hf ha (bw₁ hf ha hp₀)| = 0 := by simp
    rw [hzero] at hb
    linarith
  · have hgtbw1 : bw₁ hf ha hp₀ < w n := lt_of_le_of_ne hge' (by intro h; exact heq h.symm)
    have hin : w n ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
      rw [Set.mem_Ioo]
      exact ⟨hgtbw1, hltbw2⟩
    have hfi : IsFlatInterior f (centrePoint (w n)) :=
      flatInterior_of_mem_centreInterval hf ha hp₀ hin
    exact (covered_not_flatInterior (hwcov n)) hfi



/-! ## Lower-frontier restricted class convergence -/

/-- **Inner-FI restricted convergence at the LOWER frontier**: among the
indices whose heights are flat-interior ABOVE `bw₁` (the `FiInnerLower`
class), leaf slopes converge to the lower frontier slope. -/
theorem leafSlope_converges_fiInnerLower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₁ hf ha hp₀)) (fun n : ℕ => FiInnerLower hf ha hp₀ (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ FiInnerLower hf ha hp₀ (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₁ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₁ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hIntE : ∀ᶠ m in atTop,
      z (φ m) ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
    have htrim := fi_inner_lower_eventually_interval hf ha hp₀ (z := fun m : ℕ => z (φ m)) hzφ
    filter_upwards [htrim] with m hm
    exact hm (hφC m)
  rcases Filter.eventually_atTop.mp hIntE with ⟨M, hM⟩
  let w : ℕ → ℝ := fun m : ℕ => z (φ (m + M))
  have hwI : ∀ m : ℕ, w m ∈ Set.Ioo (bw₁ hf ha hp₀) (bw₂ hf ha hp₀) := by
    intro m
    dsimp [w]
    have hm' : M ≤ m + M := by omega
    exact hM (m + M) hm'
  have hw : Tendsto w atTop (𝓝 (bw₁ hf ha hp₀)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rcases (Metric.tendsto_atTop.mp hzφ) δ hδ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    dsimp [w]
    have hge : N ≤ m + M := by omega
    simpa [Real.dist_eq] using hN (m + M) hge
  have hlim := leafSlope_tendsto_of_interval_to_lower hf ha hp₀ (z := w) hwI hw
  have hbadW : ∀ m : ℕ, ε ≤ |leafSlope hf ha (w m) - leafSlope hf ha (bw₁ hf ha hp₀)| := by
    intro m
    dsimp [w]
    exact hφbad (m + M)
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₁ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb := hbadW N₂
  linarith

/-- **Outer-FI restricted convergence at the LOWER frontier**: among the
indices whose heights are flat-interior BELOW `bw₁` (the `FiOuterLower`
class), leaf slopes converge to the lower frontier slope. -/
theorem leafSlope_converges_fiOuterLower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₁ hf ha hp₀)) (fun n : ℕ => FiOuterLower hf ha hp₀ (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ FiOuterLower hf ha hp₀ (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₁ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₁ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hzF : ∀ m : ℕ, IsFlatInterior f (centrePoint (z (φ m))) := fun m => (hφC m).1
  have hlt : ∀ m : ℕ, z (φ m) < bw₁ hf ha hp₀ := fun m => (hφC m).2
  have hlim := leafSlope_tendsto_fi_outer_lower hf ha hp₀ (z := fun m => z (φ m)) hzF hlt hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc : |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₁ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha (bw₁ hf ha hp₀)| := hφbad N
  linarith



/-- **Cov-class restricted convergence at the LOWER frontier**: among the
indices whose heights are COVERED, leaf slopes converge to the lower
frontier slope. -/
theorem leafSlope_converges_cov_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₁ hf ha hp₀)) (fun n : ℕ => CoveredHeight (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ CoveredHeight (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha (bw₁ hf ha hp₀)| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 (bw₁ hf ha hp₀)) :=
    hz.comp hφ.tendsto_atTop
  have hbelowE := cov_class_eventually_below hf ha hp₀ (ε := ε) hε hzφ hφC hφbad
  rcases Filter.eventually_atTop.mp hbelowE with ⟨M, hM⟩
  let w : ℕ → ℝ := fun m : ℕ => z (φ (m + M))
  have hwlt : ∀ m : ℕ, w m < bw₁ hf ha hp₀ := by
    intro m
    dsimp [w]
    have hm' : M ≤ m + M := by omega
    exact hM (m + M) hm'
  have hwcov : ∀ m : ℕ, CoveredHeight (f := f) (w m) := by
    intro m
    dsimp [w]
    exact hφC (m + M)
  have hw : Tendsto w atTop (𝓝 (bw₁ hf ha hp₀)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    rcases (Metric.tendsto_atTop.mp hzφ) δ hδ with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm
    dsimp [w]
    have hge : N ≤ m + M := by omega
    simpa [Real.dist_eq] using hN (m + M) hge
  have hlim := leafSlope_tendsto_cov_outer_lower hf ha hp₀ (c := w) hwcov hwlt hw
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₁ hf ha hp₀)| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (w N₂) - leafSlope hf ha (bw₁ hf ha hp₀)| := by
    dsimp [w]
    exact hφbad (N₂ + M)
  linarith

/-- Flat-interior heights are never the covered frontier height `bw₁`. -/
lemma not_fi_at_bw₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) :
    ¬ IsFlatInterior f (centrePoint (bw₁ hf ha hp₀)) := by
  exact covered_not_flatInterior
    (⟨p₀, hp₀, bwhh₁ hf ha hp₀⟩ : CoveredHeight (f := f) (bw₁ hf ha hp₀))

/-- The FLAT-INTERIOR class restricted convergence at the LOWER frontier
(all interior heights, above or below `bw₁`; `= bw₁` impossible). -/
theorem leafSlope_converges_fi_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₁ hf ha hp₀))
      (fun n : ℕ => IsFlatInterior f (centrePoint (z n))) := by
  classical
  intro ε hε
  have hinner := leafSlope_converges_fiInnerLower hf ha hp₀ hz ε hε
  have houter := leafSlope_converges_fiOuterLower hf ha hp₀ hz ε hε
  rcases hinner with ⟨N₁, hN₁⟩
  rcases houter with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn hfi
  have hne : z n ≠ bw₁ hf ha hp₀ := by
    intro hz₀
    have : IsFlatInterior f (centrePoint (bw₁ hf ha hp₀)) := by
      rwa [← hz₀]
    exact (not_fi_at_bw₁ hf ha hp₀) this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn₂ : N₂ ≤ n := by omega
    exact hN₂ n hn₂ ⟨hfi, hlt⟩
  · have hn₁ : N₁ ≤ n := by omega
    exact hN₁ n hn₁ ⟨hfi, hgt⟩

/-- The COVERED-DEGENERATE class restricted convergence at the LOWER
frontier (subset of the covered class). -/
theorem leafSlope_converges_covDegenerate_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha (bw₁ hf ha hp₀))
      (fun n : ℕ => CoveredDegenerate (a := a) (f := f) (z n)) := by
  apply ConvergesOnClass.mono (leafSlope_converges_cov_lower hf ha hp₀ hz)
  intro n hc
  exact hc.2.2



/-! ## Generic U/Unc classes at an arbitrary covered height, and the FULL
lower-frontier assembly -/

/-- The `UHeight` class restricted convergence at an arbitrary COVERED
height `y₀`. -/
theorem leafSlope_converges_uHeight_at {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha y₀) (fun n : ℕ => z n ∈ UHeight a f) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ z n ∈ UHeight a f ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha y₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have hlim := leafSlope_tendsto_uHeight_of_covered hf ha hc
    (z := fun m => z (φ m)) (hzU := hφC) hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc' : |leafSlope hf ha (z (φ N)) - leafSlope hf ha y₀| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha y₀| := hφbad N
  linarith

/-- The UNCOVERED class restricted convergence at an arbitrary COVERED
height `y₀`. -/
theorem leafSlope_converges_unc_at {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (leafSlope hf ha y₀)
      (fun n : ℕ => UncoveredDegenerate (a := a) (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UncoveredDegenerate (a := a) (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - leafSlope hf ha y₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    refine ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have huF : ∀ m : ℕ, z (φ m) ∈ FlatHeight a f := fun m =>
    UncoveredDegenerate_mem_FlatHeight (hφC m)
  have huni : ∀ m : ℕ, ¬ IsFlatInterior f (centrePoint (z (φ m))) := fun m => (hφC m).2.1
  have huunc : ∀ m : ℕ, ¬ CoveredHeight (f := f) (z (φ m)) := fun m => (hφC m).2.2
  have hlim := leafSlope_tendsto_uncovered_of_covered hf ha hc huF huni huunc hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N, hN⟩
  have hc' : |leafSlope hf ha (z (φ N)) - leafSlope hf ha y₀| < ε := by
    simpa [Real.dist_eq] using hN N le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N)) - leafSlope hf ha y₀| := hφbad N
  linarith

/-- **FULL sequential continuity of `leafSlope` at the LOWER frontier
height**: ANY height sequence converging to `bw₁` of a component has leaf
slopes converging to the spliced leaf slope there. -/
theorem leafSlope_tendsto_at_lower {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₁ hf ha hp₀))) := by
  apply tendsto_of_classwise (u := fun n : ℕ => leafSlope hf ha (z n))
    (L := leafSlope hf ha (bw₁ hf ha hp₀))
    (C₁ := fun n : ℕ => z n ∈ UHeight a f)
    (C₂ := fun n : ℕ => IsFlatInterior f (centrePoint (z n)))
    (C₃ := fun n : ℕ => CoveredDegenerate (a := a) (f := f) (z n))
    (C₄ := fun n : ℕ => UncoveredDegenerate (a := a) (f := f) (z n))
  · intro n
    exact height_case (a := a) (f := f) (z n)
  · have hc₁ : CoveredHeight (f := f) (bw₁ hf ha hp₀) := ⟨p₀, hp₀, bwhh₁ hf ha hp₀⟩
    exact leafSlope_converges_uHeight_at hf ha hc₁ hz
  · exact leafSlope_converges_fi_lower hf ha hp₀ hz
  · exact leafSlope_converges_covDegenerate_lower hf ha hp₀ hz
  · have hc₁ : CoveredHeight (f := f) (bw₁ hf ha hp₀) := ⟨p₀, hp₀, bwhh₁ hf ha hp₀⟩
    exact leafSlope_converges_unc_at hf ha hc₁ hz



/-! ## The metric bridge: sequential continuity ⟹ `ContinuousAt` at covered
heights -/

/-- A real function that is sequentially continuous at `x₀` is continuous
at `x₀` (contrapositive: failing the ε–δ condition yields a sequence
approaching `x₀` whose values stay ε-away). -/
lemma continuousAt_of_seq_tendsto {f : ℝ → ℝ} {x₀ : ℝ}
    (h : ∀ z : ℕ → ℝ, Tendsto z atTop (𝓝 x₀) →
      Tendsto (fun n : ℕ => f (z n)) atTop (𝓝 (f x₀))) :
    ContinuousAt f x₀ := by
  classical
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_contra hnot
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ x : ℝ, dist x x₀ < δ ∧ ε ≤ dist (f x) (f x₀) := by
    intro δ hδ
    push_neg at hnot
    rcases hnot δ hδ with ⟨x, hx1, hx2⟩
    refine ⟨x, hx1, hx2⟩
  let z : ℕ → ℝ := fun n => Classical.choose (hbad (1 / (n + 1)) (by positivity))
  have hz₁ : ∀ n : ℕ, ε ≤ dist (f (z n)) (f x₀) := fun n =>
    (Classical.choose_spec (hbad (1 / (n + 1)) (by positivity))).2
  have hzd : ∀ n : ℕ, dist (z n) x₀ < 1 / (n + 1) := fun n =>
    (Classical.choose_spec (hbad (1 / (n + 1)) (by positivity))).1
  have hz : Tendsto z atTop (𝓝 x₀) := by
    have hle : ∀ n : ℕ, dist (z n) x₀ ≤ 1 / (n + 1) := fun n => le_of_lt (hzd n)
    have habs : Tendsto (fun n : ℕ => dist (z n) x₀) atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun n => dist_nonneg) hle tendsto_one_div_add_atTop_nhds_zero_nat
    exact (tendsto_iff_dist_tendsto_zero.mpr habs)
  have hf := h z hz
  rcases (Metric.tendsto_atTop.mp hf) ε hε with ⟨N, hN⟩
  have hc := hN N le_rfl
  have hb := hz₁ N
  linarith

/-- `leafSlope` is continuous at the UPPER frontier height of a
component. -/
theorem continuousAt_leafSlope_at_upper {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) :
    ContinuousAt (fun y : ℝ => leafSlope hf ha y) (bw₂ hf ha hp₀) := by
  exact continuousAt_of_seq_tendsto (fun z hz => leafSlope_tendsto_at_upper hf ha hp₀ hz)

/-- `leafSlope` is continuous at the LOWER frontier height of a
component. -/
theorem continuousAt_leafSlope_at_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) :
    ContinuousAt (fun y : ℝ => leafSlope hf ha y) (bw₁ hf ha hp₀) := by
  exact continuousAt_of_seq_tendsto (fun z hz => leafSlope_tendsto_at_lower hf ha hp₀ hz)

/-- **`leafSlope` is continuous at every COVERED height** (the height is
`bw₁` or `bw₂` of its covering component). -/
theorem continuousAt_leafSlope_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => leafSlope hf ha y) y₀ := by
  let p : ℝ² := covPoint y₀ hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp (y := y₀) hc
  rcases covered_eq_bw hf ha hc with hy₁ | hy₂
  · rw [hy₁]
    exact continuousAt_leafSlope_at_lower hf ha hp
  · rw [hy₂]
    exact continuousAt_leafSlope_at_upper hf ha hp

/-- The left endpoint height function `spliceA1` is continuous at every
COVERED height. -/
theorem continuousAt_spliceA1_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => spliceA1 hf ha y) y₀ := by
  have hcont : ContinuousAt (fun y : ℝ => y - leafSlope hf ha y / 2) y₀ := by
    have hc2 : ContinuousAt (fun y : ℝ => leafSlope hf ha y / 2) y₀ :=
      (continuousAt_leafSlope_of_covered hf ha hc).div continuousAt_const (by norm_num)
    exact continuousAt_id.sub hc2
  have hfun : (fun y : ℝ => spliceA1 hf ha y) = fun y : ℝ => y - leafSlope hf ha y / 2 := by
    funext y
    exact spliceA1_eq_sub_half hf ha y
  rwa [hfun]

/-- The right endpoint height function `spliceB1` is continuous at every
COVERED height. -/
theorem continuousAt_spliceB1_of_covered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => spliceB1 hf ha y) y₀ := by
  have hcont : ContinuousAt (fun y : ℝ => y + leafSlope hf ha y / 2) y₀ := by
    have hc2 : ContinuousAt (fun y : ℝ => leafSlope hf ha y / 2) y₀ :=
      (continuousAt_leafSlope_of_covered hf ha hc).div continuousAt_const (by norm_num)
    exact continuousAt_id.add hc2
  have hfun : (fun y : ℝ => spliceB1 hf ha y) = fun y : ℝ => y + leafSlope hf ha y / 2 := by
    funext y
    exact spliceB1_eq_add_half hf ha y
  rwa [hfun]




end Submission
