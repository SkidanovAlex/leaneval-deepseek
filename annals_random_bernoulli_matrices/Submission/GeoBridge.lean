import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.Compress
import Submission.CompressProp
import Submission.Commons.LinearAlgebra.Net.compress_slice_net
import ChallengeDeps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
# Layer 4 bridge: from the `σ_min` event of an `n×n` Bernoulli matrix to
function-level row events.

This module connects Theorem A's `σ_min`-small-ball event to (i) "there is a
unit vector with small image" (via attainment of `σ_min` on the unit sphere),
(ii) function-level `Fin n → ℝ` row-sum events over the full matrix, and
(iii) the `(n−1)×n` top-row events which the compress machinery of
`Submission.CompressProp` bounds.

Also contains the clamping glue: entries with law `Ber(1,0,p)` are replaced by
pointwise values in `{0,1}` (so that the pointwise bound `|B − p| ≤ 1` of
`compress_theorem` holds), without changing any probability of an event that
only depends on the matrix entries through a pointwise function.
-/

namespace Submission.GeoBridge

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

noncomputable section

universe u

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## 1. `σ_min` attainment and the unit-vector event bridge -/

/-- A unit vector exists in `EuclideanSpace ℝ (Fin n)` for `1 ≤ n`. -/
lemma exists_unit_vector {n : ℕ} (hn : 1 ≤ n) : ∃ x : E n, ‖x‖ = 1 := by
  let i : Fin n := ⟨0, by omega⟩
  refine ⟨EuclideanSpace.single i (1 : ℝ), ?_⟩
  simp [PiLp.norm_single]

/-- `σ_min M` is attained at a unit vector. -/
theorem sigma_min_attained {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ x : E n, ‖x‖ = 1 ∧ ‖M.toEuclideanLin x‖ = RandomBernoulliMatrices.σ_min M := by
  let S : Set (E n) := {x : E n | ‖x‖ = 1}
  have hS : S = Metric.sphere (0 : E n) 1 := by
    ext x
    simp [S, Metric.sphere]
  have hc : IsCompact S := by
    rw [hS]
    exact isCompact_sphere (0 : E n) 1
  rcases exists_unit_vector hn with ⟨x0, hx0⟩
  have hne : S.Nonempty := ⟨x0, hx0⟩
  have hcont : ContinuousOn (fun x : E n => ‖M.toEuclideanLin x‖) S := by
    exact Continuous.continuousOn (by fun_prop)
  rcases hc.exists_isMinOn hne hcont with ⟨xmin, hxminS, hmin⟩
  have hxmin : ‖xmin‖ = 1 := hxminS
  refine ⟨xmin, hxmin, ?_⟩
  unfold RandomBernoulliMatrices.σ_min
  apply le_antisymm
  · change ‖M.toEuclideanLin xmin‖ ≤ (⨅ x : {x : E n // ‖x‖ = 1}, ‖M.toEuclideanLin x.1‖)
    haveI : Nonempty {x : E n // ‖x‖ = 1} := ⟨⟨xmin, hxmin⟩⟩
    exact le_ciInf (fun x => hmin x.property)
  · change (⨅ x : {x : E n // ‖x‖ = 1}, ‖M.toEuclideanLin x.1‖) ≤ ‖M.toEuclideanLin xmin‖
    have hbdd : BddBelow (Set.range fun x : {x : E n // ‖x‖ = 1} => ‖M.toEuclideanLin x.1‖) := by
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨xmin, hxmin⟩

/-- `σ_min M ≤ u` iff there is a unit vector whose image has norm `≤ u`. -/
theorem sigma_min_le_iff {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    RandomBernoulliMatrices.σ_min M ≤ u ↔
      ∃ x : E n, ‖x‖ = 1 ∧ ‖M.toEuclideanLin x‖ ≤ u := by
  constructor
  · intro h
    rcases sigma_min_attained hn M with ⟨x, hx, hval⟩
    exact ⟨x, hx, by rwa [hval]⟩
  · rintro ⟨x, hx, hxle⟩
    unfold RandomBernoulliMatrices.σ_min
    exact le_trans (ciInf_le
      (show BddBelow (Set.range (fun x : {x : E n // ‖x‖ = 1} => ‖M.toEuclideanLin x.1‖)) from
        ⟨0, by
          rintro y ⟨x, rfl⟩
          exact norm_nonneg _⟩) ⟨x, hx⟩) hxle

/-- The real part of the `σ_min`-event is at most that of the
"exists a unit vector with small image" event. -/
theorem measureReal_sigma_min_le_exists_unit {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hn : 1 ≤ n) (u : ℝ) :
    P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω) ≤ u} ≤
      P.real {ω : Ω | ∃ x : E n, ‖x‖ = 1 ∧ ‖(B ω).toEuclideanLin x‖ ≤ u} := by
  refine MeasureTheory.measureReal_mono ?_ ?_
  · intro ω hω
    exact (sigma_min_le_iff hn (B ω) u).1 hω
  · have hle : P {ω : Ω | ∃ x : E n, ‖x‖ = 1 ∧ ‖(B ω).toEuclideanLin x‖ ≤ u} ≤ (1 : ℝ≥0∞) := by
      have hmono : P {ω : Ω | ∃ x : E n, ‖x‖ = 1 ∧ ‖(B ω).toEuclideanLin x‖ ≤ u} ≤ P Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      simpa using hmono
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle

/-! ## 2. Function-level `Fin n → ℝ` events -/

open Submission.Compress (sqNorm actSq)

/-- The full row-squared norm of a square matrix acting on `f`. -/
noncomputable def actSqFull {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (∑ j : Fin n, M i j * f j) ^ 2

lemma sq_norm_ofLp_coord {n : ℕ} (x : E n) : ‖x‖ ^ 2 = ∑ i : Fin n, (x.ofLp i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sq]

lemma toLp_ofLp_id {n : ℕ} (x : E n) : (WithLp.toLp 2 (x.ofLp) : E n) = x := by
  rfl

lemma coeff_toEuclideanLin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : E n) (i : Fin n) :
    (M.toEuclideanLin x).ofLp i = ∑ j : Fin n, M i j * x.ofLp j := by
  rw [Matrix.toEuclideanLin_apply]
  simp [Matrix.mulVec_apply_eq_sum]

/-- Norm-squared of the matrix action equals the full row-squared sum. -/
lemma sqnorm_toEuclideanLin_eq_actSqFull {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    ‖M.toEuclideanLin (WithLp.toLp 2 f : E n)‖ ^ 2 = actSqFull M f := by
  rw [sq_norm_ofLp_coord (M.toEuclideanLin (WithLp.toLp 2 f : E n))]
  dsimp [actSqFull]
  simp [Matrix.mulVec_apply_eq_sum]

/-- `sqNorm` of the coefficient function of a unit vector is one. -/
lemma sqNorm_ofLp_of_unit {n : ℕ} {x : E n} (hx : ‖x‖ = 1) : sqNorm (fun j : Fin n => x.ofLp j) = 1 := by
  have h := sq_norm_ofLp_coord x
  rw [show sqNorm (fun j : Fin n => x.ofLp j) = ∑ i : Fin n, (x.ofLp i) ^ 2 by
    simp [sqNorm]]
  rw [← h]
  rw [hx]
  norm_num

/-- Small image of a unit (euclidean) vector gives a unit function with full
row-squared image at most `u²`. -/
lemma exists_function_of_sigma_min {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    (∃ x : E n, ‖x‖ = 1 ∧ ‖M.toEuclideanLin x‖ ≤ u) →
      ∃ f : Fin n → ℝ, sqNorm f = 1 ∧ actSqFull M f ≤ u ^ 2 := by
  rintro ⟨x, hx, hxle⟩
  refine ⟨fun j : Fin n => x.ofLp j, sqNorm_ofLp_of_unit hx, ?_⟩
  have heq : actSqFull M (fun j : Fin n => x.ofLp j) = ‖M.toEuclideanLin x‖ ^ 2 := by
    have hxid : (WithLp.toLp 2 (x.ofLp) : E n) = x := rfl
    calc
      actSqFull M (fun j : Fin n => x.ofLp j)
          = ‖M.toEuclideanLin (WithLp.toLp 2 (fun j : Fin n => x.ofLp j) : E n)‖ ^ 2 := by
              rw [sqnorm_toEuclideanLin_eq_actSqFull]
      _ = ‖M.toEuclideanLin x‖ ^ 2 := by rw [hxid]
  rw [heq]
  nlinarith [sq_nonneg (‖M.toEuclideanLin x‖), norm_nonneg (M.toEuclideanLin x), hxle]

/-- The real `σ_min` event is at most the real "exists unit function with full
row-squared norm at most `u²`" event. -/
theorem measureReal_sigma_min_le_fullActSq {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω) ≤ u} ≤
      P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧ actSqFull (B ω) f ≤ u ^ 2} := by
  refine MeasureTheory.measureReal_mono ?_ ?_
  · intro ω hω
    exact exists_function_of_sigma_min hn (B ω) hu ((sigma_min_le_iff hn (B ω) u).1 hω)
  · have hle : P {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧ actSqFull (B ω) f ≤ u ^ 2} ≤
        (1 : ℝ≥0∞) := by
      have hmono : P {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧ actSqFull (B ω) f ≤ u ^ 2} ≤
          P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      simpa using hmono
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle

/-! ## 3. Top-row partial sums are at most the full sum -/

/-- Embedding of the first `n−1` row indices into `Fin n`. -/
def emb {n : ℕ} (k : Fin (n - 1)) : Fin n := Fin.castLE (Nat.sub_le n 1) k

lemma emb_injective {n : ℕ} : Function.Injective (emb : Fin (n - 1) → Fin n) := by
  unfold emb
  exact Fin.castLE_injective (Nat.sub_le n 1)

/-- A sum over the injective image is at most the sum over everything
(for non-negative summands). -/
lemma sum_comp_injective_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (g : β → α) (hg : Function.Injective g) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ b : β, f (g b)) ≤ (∑ a : α, f a) := by
  classical
  let Img : Finset α := (Finset.univ : Finset β).image g
  have hEq : (∑ b : β, f (g b)) = (∑ a ∈ Img, f a) := by
    have h1 : (∑ b : β, f (g b)) = (∑ b ∈ (Finset.univ : Finset β), f (g b)) := by simp
    have h2 : (∑ a ∈ Img, f a) = (∑ b ∈ (Finset.univ : Finset β), f (g b)) := by
      have hinj : Set.InjOn g (↑(Finset.univ : Finset β) : Set β) :=
        Set.injOn_of_injective hg
      exact Finset.sum_image (f := f) (s := (Finset.univ : Finset β)) (g := g) hinj
    rw [h1, ← h2]
  calc
    (∑ b : β, f (g b)) = (∑ a ∈ Img, f a) := hEq
    _ ≤ (∑ a : α, f a) := by
      have hle : (∑ a ∈ Img, f a) ≤ (∑ a ∈ (Finset.univ : Finset α), f a) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (s := Img) (t := Finset.univ)
          (by intro a ha; exact Finset.mem_univ a) (fun a ha hI => hf a)
      simpa using hle

/-- The row-squared sum over the first `n−1` rows is at most the full row-squared
sum over all `n` rows. -/
lemma partial_actSq_le_full {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    Submission.Compress.actSq (fun k : Fin (n - 1) => fun j : Fin n => M (emb k) j) f ≤
      actSqFull M f := by
  let rowSq : Fin n → ℝ := fun i => (∑ j : Fin n, M i j * f j) ^ 2
  have hnonneg : ∀ i : Fin n, 0 ≤ rowSq i := by
    intro i
    dsimp [rowSq]
    positivity
  calc
    Submission.Compress.actSq (fun k : Fin (n - 1) => fun j : Fin n => M (emb k) j) f
        = (∑ k : Fin (n - 1), rowSq (emb k)) := by
          simp [Submission.Compress.actSq, Submission.Compress.rowAct, rowSq]
    _ ≤ (∑ i : Fin n, rowSq i) := sum_comp_injective_le (g := emb) emb_injective rowSq hnonneg
    _ = actSqFull M f := by
      dsimp [actSqFull, rowSq]

/-- If the full row-squared sum is at most `u²`, so is the partial one. -/
lemma partial_actSq_le_of_full_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (h : actSqFull M f ≤ u ^ 2) :
    Submission.Compress.actSq (fun k : Fin (n - 1) => fun j : Fin n => M (emb k) j) f ≤ u ^ 2 := by
  exact le_trans (partial_actSq_le_full M f) h

/-- Function-level version of `actSqFull` (rows of a function `Fin n → Fin n → ℝ`). -/
noncomputable def actSqFullFn {n : ℕ} (M : Fin n → Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (∑ j : Fin n, M i j * f j) ^ 2

/-- The matrix version and the function version of the full row-squared sum agree. -/
lemma actSqFullFn_of_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    actSqFullFn (fun i j => M i j) f = actSqFull M f := by
  rfl

/-- Function-level partial row-squared sum is at most the full one. -/
lemma partial_actSqFn_le_fullFn {n : ℕ} (M : Fin n → Fin n → ℝ) (f : Fin n → ℝ) :
    Submission.Compress.actSq (fun k : Fin (n - 1) => fun j : Fin n => M (emb k) j) f ≤
      actSqFullFn M f := by
  let rowSq : Fin n → ℝ := fun i => (∑ j : Fin n, M i j * f j) ^ 2
  have hnonneg : ∀ i : Fin n, 0 ≤ rowSq i := by
    intro i
    dsimp [rowSq]
    positivity
  calc
    Submission.Compress.actSq (fun k : Fin (n - 1) => fun j : Fin n => M (emb k) j) f
        = (∑ k : Fin (n - 1), rowSq (emb k)) := by
          simp [Submission.Compress.actSq, Submission.Compress.rowAct, rowSq]
    _ ≤ (∑ i : Fin n, rowSq i) := sum_comp_injective_le (g := emb) emb_injective rowSq hnonneg
    _ = actSqFullFn M f := by
      dsimp [actSqFullFn, rowSq]

/-! ## 4. The compress side of Theorem A: an `n×n` matrix bound

The event "some compressible unit vector has full row-squared image at most
`u²`" (for the full `n×n` matrix) is at most `(1−p+ε)ⁿ` whenever
`u ≤ γ₀·√n`, uniformly over the shift `s` (with `s+p ≠ 0`).  The proof goes
through `compress_theorem` (which bounds the corresponding top-`(n−1)`-row
event) via `partial_actSq_le_of_full_le` and the scale monotonicity of the
small-ball events.
-/

/-- Top `(n−1)`-row family of an `n×n` matrix-valued random family. -/
def rowFamily {n : ℕ} {Ω : Type u} (B : Ω → Matrix (Fin n) (Fin n) ℝ) :
    Fin (n - 1) → Fin n → Ω → ℝ :=
  fun k j ω => B ω (emb k) j

/-- The compress side of Theorem A, in full-`n×n`-matrix form: the event that
some `(δ,ν)`-compressible unit vector `f` has full row-squared image at most
`u²` (entries `B ω i j + s`) has probability at most `(1−p+ε)ⁿ`, uniformly for
`u ≤ γ₀·√n`.  The hypothesis set mirrors `compress_theorem` (measurability,
independence, Bernoulli law, pointwise bound); the `s+p ≠ 0` condition is the
non-degeneracy of the shift. -/
theorem compress_side_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ s : ℝ, s + (p : ℝ) ≠ 0 → ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | ∃ f : Fin n → ℝ,
            Commons.LinearAlgebra.Net.compressible δ ν f ∧
            actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
            ≤ (1 - (p : ℝ) + ε) ^ n := by
  rcases Submission.CompressProp.compress_theorem hp₀ hp₁ hε₀
    with ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hmain⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt s hss u hu0 hule
  let T : Fin (n - 1) → Fin n → Ω → ℝ := rowFamily B
  have hTmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (T k j) := by
    intro k j
    dsimp [T, rowFamily]
    exact hBmeas (emb k) j
  have hTind : ProbabilityTheory.iIndepFun
      (fun kj : Fin (n - 1) × Fin n => T kj.1 kj.2) P := by
    have hg : Function.Injective (fun kj : Fin (n - 1) × Fin n => (emb kj.1, kj.2)) := by
      intro a b hab
      have h1 : emb a.1 = emb b.1 := by simpa using congrArg Prod.fst hab
      have h2 : a.2 = b.2 := by simpa using congrArg Prod.snd hab
      apply Prod.ext
      · exact emb_injective h1
      · exact h2
    have hind := ProbabilityTheory.iIndepFun.precomp hg hBind
    exact hind
  have hTlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (T k j) (bernoulliMeasure 1 0 p) P := by
    intro k j
    dsimp [T, rowFamily]
    change HasLaw (fun ω : Ω => B ω (emb k) j) (bernoulliMeasure 1 0 p) P
    exact hBlaw (emb k) j
  have hTpt : ∀ k : Fin (n - 1), ∀ j : Fin n, ∀ ω : Ω, |T k j ω - (p : ℝ)| ≤ 1 := by
    intro k j ω
    dsimp [T, rowFamily]
    exact hBpt (emb k) j ω
  have hmain' := hmain n hn (Ω := Ω) P T hTmeas hTind hTlaw hTpt s hss
  -- the target event is a subset of the compress event at scale γ₀·√n
  let E : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  let F : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω + s) f ≤ γ₀ ^ 2 * (n : ℝ)}
  have hEF : E ⊆ F := by
    intro ω hω
    rcases hω with ⟨f, hfc, hfull⟩
    refine ⟨f, hfc, ?_⟩
    have hpart : actSq (fun k : Fin (n - 1) => fun j : Fin n => B ω (emb k) j + s) f ≤ u ^ 2 := by
      have hpl := partial_actSqFn_le_fullFn (fun i j : Fin n => B ω i j + s) f
      simpa using (le_trans hpl hfull)
    have hsame : actSq (fun k : Fin (n - 1) => fun j : Fin n => B ω (emb k) j + s) f =
        actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω + s) f := by
      apply congrArg (fun A => actSq A f)
      funext k j
      rfl
    have hu2 : u ^ 2 ≤ γ₀ ^ 2 * (n : ℝ) := by
      have hmul : u * u ≤ (γ₀ * Real.sqrt (n : ℝ)) * (γ₀ * Real.sqrt (n : ℝ)) := by
        exact mul_le_mul hule hule (le_of_lt hu0) (le_trans (le_of_lt hu0) hule)
      have h0 : 0 ≤ (n : ℝ) := by positivity
      have hsq : (γ₀ * Real.sqrt (n : ℝ)) ^ 2 = γ₀ ^ 2 * (n : ℝ) := by
        rw [mul_pow]
        rw [Real.sq_sqrt h0]
      calc
        u ^ 2 = u * u := by ring
        _ ≤ (γ₀ * Real.sqrt (n : ℝ)) * (γ₀ * Real.sqrt (n : ℝ)) := hmul
        _ = (γ₀ * Real.sqrt (n : ℝ)) ^ 2 := by ring
        _ = γ₀ ^ 2 * (n : ℝ) := hsq
    have hfin : actSq (fun k : Fin (n - 1) => fun j : Fin n => T k j ω + s) f ≤
        γ₀ ^ 2 * (n : ℝ) := by
      rw [← hsame]
      exact le_trans hpart hu2
    exact hfin
  have hFmeas : P F ≠ ⊤ := by
    have hle : P F ≤ (1 : ℝ≥0∞) := by
      have hmono : P F ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      simpa using hmono
    exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle
  have hPF : P.real F ≤ (1 - (p : ℝ) + ε) ^ n := hmain'
  have hmono' : P.real E ≤ P.real F := MeasureTheory.measureReal_mono hEF hFmeas
  exact le_trans hmono' hPF

/-! ## 5. The `σ_min` event splits into a compressible part (bounded) and an
incompressible part (open, to be bounded by the averaging machinery). -/

/-- Decomposition theorem: the `σ_min`-small-ball event of the shifted matrix
`B ω + s·11ᵀ` (entries `B ω i j + s`) is at most `(1−p+ε)ⁿ` (compressible
part, bounded by `compress_side_bound`) plus the incompressible small-ball
part, which the later averaging layer will bound. -/
theorem sigma_min_decomp {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
        (hBpt : ∀ i j : Fin n, ∀ ω : Ω, |B ω i j - (p : ℝ)| ≤ 1),
        ∀ s : ℝ, s + (p : ℝ) ≠ 0 → ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  rcases compress_side_bound hp₀ hp₁ hε₀ with ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hcsb⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBmeas hBind hBlaw hBpt s hss u hu0 hule
  -- shifted full matrix event (function level)
  let Es : Set Ω := {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
  let Ef : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  let Ec : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ,
      Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  let Ei : Set Ω := {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2}
  -- Ef ⊆ Ec ∪ Ei
  have hEf : Ef ⊆ Ec ∪ Ei := by
    intro ω hω
    rcases hω with ⟨f, hf1, hfball⟩
    by_cases hc : Commons.LinearAlgebra.Net.compressible δ ν f
    · exact Or.inl ⟨f, hc, hfball⟩
    · exact Or.inr ⟨f, hf1, hc, hfball⟩
  -- Es ⊆ Ef
  have hEsEf : Es ⊆ Ef := by
    intro ω hω
    have hn1 : 1 ≤ n := by omega
    -- use the euclidean bridge: σ_min ≤ u gives a unit euclidean x; then function
    have hx := (sigma_min_le_iff hn1 (B ω + Matrix.of (fun _ _ : Fin n => s)) u).1 hω
    rcases exists_function_of_sigma_min hn1 (B ω + Matrix.of (fun _ _ : Fin n => s)) (le_of_lt hu0) hx with
      ⟨f, hf1, hfballM⟩
    refine ⟨f, hf1, ?_⟩
    -- hfballM : actSqFull (Bω + of s) f ≤ u²  (matrix version); convert to Fn version
    have heq : actSqFull (B ω + Matrix.of (fun _ _ : Fin n => s)) f =
        actSqFullFn (fun i j : Fin n => B ω i j + s) f := by
      dsimp [actSqFull, actSqFullFn]
    rwa [heq] at hfballM
  have hEs : Es ⊆ Ec ∪ Ei := Set.Subset.trans hEsEf hEf
  -- measure bounds
  have hEi : P.real Es ≤ P.real Ec + P.real Ei := by
    have hmono : P.real Es ≤ P.real (Ec ∪ Ei) := MeasureTheory.measureReal_mono hEs (by
      have hle : P (Ec ∪ Ei) ≤ (1 : ℝ≥0∞) := by
        have hmono' : P (Ec ∪ Ei) ≤ P Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        simpa using hmono'
      exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle)
    exact le_trans hmono (MeasureTheory.measureReal_union_le Ec Ei)
  have hEc : P.real Ec ≤ (1 - (p : ℝ) + ε) ^ n := by
    exact hcsb n hn (Ω := Ω) P B hBmeas hBind hBlaw hBpt s hss u hu0 hule
  have hfinal : P.real Es ≤ (1 - (p : ℝ) + ε) ^ n + P.real Ei := by
    have hEc2 : P.real Ec + P.real Ei ≤ (1 - (p : ℝ) + ε) ^ n + P.real Ei := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hEc (P.real Ei)
    exact le_trans hEi hEc2
  simpa [Es, Ei] using hfinal

/-! ## 6. Clamping: pointwise `{0,1}`-valued representatives and event transfer

Theorem A's hypotheses give only laws (`HasLaw ... (Ber(1,0,p))`) and
independence of `n×n` Bernoulli entries.  Compress machinery additionally
needs *measurable* entries with the *pointwise* bound `|B−p| ≤ 1`.  This
section provides the standard repair: replace each entry by its value clamped
to `[0,1]` (which is `a.e.` unchanged, since a `Ber(1,0,p)` variable is
`0` or `1` a.s.) and then by a measurable version.  The events built from the
matrix change only on a null set. -/

/-- Clamp a real number into `[0,1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := min 1 (max 0 t)

lemma clamp01_continuous : Continuous clamp01 := by
  unfold clamp01
  fun_prop

lemma clamp01_mem (t : ℝ) : 0 ≤ clamp01 t ∧ clamp01 t ≤ 1 := by
  unfold clamp01
  constructor <;> simp

lemma clamp01_id {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp01 t = t := by
  unfold clamp01
  rw [max_eq_right h0, min_eq_right h1]

lemma clamp01_fix (t : ℝ) (ht : t = 0 ∨ t = 1) : clamp01 t = t := by
  rcases ht with rfl | rfl <;> simp [clamp01]

/-- The clamped value is within distance 1 of any `p ∈ [0,1]`. -/
lemma clamp01_abs_le_one {p : I} (t : ℝ) : |clamp01 t - (p : ℝ)| ≤ 1 := by
  have hm := clamp01_mem t
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  rw [abs_sub_le_iff]
  constructor
  · linarith [hm.2, hp0]
  · linarith [hm.1, hp1]

/-- A Bernoulli(`1,0,p`)-law variable takes values in `{0,1}` a.s. -/
lemma bernoulli_law_mem_two_ae {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I} {X : Ω → ℝ}
    (hX : HasLaw X (bernoulliMeasure 1 0 p) P) :
    ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
  have hs : MeasurableSet ({0,1} : Set ℝ) :=
    Set.Finite.measurableSet (by norm_num : ({0,1} : Set ℝ).Finite)
  have hset : (X ⁻¹' ({0, 1} : Set ℝ)) = {ω | X ω ∈ ({0, 1} : Set ℝ)} := by
    ext ω
    simp
  have hm : P {ω | X ω ∈ ({0, 1} : Set ℝ)} = 1 := by
    have hber : (bernoulliMeasure 1 0 p : Measure ℝ) ({0, 1} : Set ℝ) = 1 := by
      classical
      exact bernoulliMeasure_apply_of_mem_of_mem p hs (by simp) (by simp)
    calc
      P {ω | X ω ∈ ({0, 1} : Set ℝ)} = P (X ⁻¹' ({0, 1} : Set ℝ)) := by rw [hset]
      _ = (P.map X) ({0, 1} : Set ℝ) := by
        rw [Measure.map_apply_of_aemeasurable hX.aemeasurable hs]
      _ = 1 := by
        rw [hX.map_eq]
        exact hber
  have hzero : P {ω | ¬(X ω = 0 ∨ X ω = 1)} = 0 := by
    have hsub : {ω | ¬(X ω = 0 ∨ X ω = 1)} ⊆ {ω | X ω ∉ ({0,1} : Set ℝ)} := by
      intro ω hω
      simp at hω ⊢
      exact hω
    have hcompl : P {ω | X ω ∉ ({0,1} : Set ℝ)} = 0 := by
      have hsetc : (X ⁻¹' (({0,1} : Set ℝ)ᶜ)) = {ω | X ω ∉ ({0,1} : Set ℝ)} := by
        ext ω
        simp
      calc
        P {ω | X ω ∉ ({0,1} : Set ℝ)} = P (X ⁻¹' (({0,1} : Set ℝ)ᶜ)) := by rw [hsetc]
        _ = (P.map X) (({0,1} : Set ℝ)ᶜ) := by
          rw [Measure.map_apply_of_aemeasurable hX.aemeasurable hs.compl]
        _ = 0 := by
          rw [hX.map_eq]
          classical
          exact bernoulliMeasure_apply_of_notMem_of_notMem p hs.compl (by simp) (by simp)
    exact measure_mono_null hsub hcompl
  rw [MeasureTheory.ae_iff]
  simpa using hzero

/-- Clamping a Bernoulli law variable changes it only a.e. -/
lemma clamp01_ae_eq_of_law {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I} {X : Ω → ℝ}
    (hX : HasLaw X (bernoulliMeasure 1 0 p) P) :
    (fun ω => clamp01 (X ω)) =ᵐ[P] X := by
  filter_upwards [bernoulli_law_mem_two_ae P hX] with ω hω
  exact clamp01_fix (X ω) hω

/-- Clamping preserves the Bernoulli(`1,0,p`) law. -/
lemma law_clamp01 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I} {X : Ω → ℝ}
    (hX : HasLaw X (bernoulliMeasure 1 0 p) P) :
    HasLaw (fun ω => clamp01 (X ω)) (bernoulliMeasure 1 0 p) P := by
  refine ⟨?_, ?_⟩
  · exact (clamp01_continuous.measurable.comp_aemeasurable hX.aemeasurable)
  · have hcongr := Measure.map_congr (mβ := (inferInstance : MeasurableSpace ℝ))
      (clamp01_ae_eq_of_law P hX)
    rw [hcongr]
    exact hX.map_eq

/-- A measurable representative in `[0,1]`, equal to `X` a.e., with the same
Bernoulli law, and the pointwise bound.  (Uses `AEMeasurable.mk`.) -/
lemma exists_measurable_clamped_entry {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : I}
    {X : Ω → ℝ} (hX : HasLaw X (bernoulliMeasure 1 0 p) P) :
    ∃ Y : Ω → ℝ,
      Measurable Y ∧
      HasLaw Y (bernoulliMeasure 1 0 p) P ∧
      (∀ ω, |Y ω - (p : ℝ)| ≤ 1) ∧
      Y =ᵐ[P] X := by
  let Y : Ω → ℝ := fun ω => clamp01 (X ω)
  have haeY : AEMeasurable Y P :=
    (clamp01_continuous.measurable.comp_aemeasurable hX.aemeasurable)
  let Yc : Ω → ℝ := clamp01 ∘ (haeY.mk Y)
  have hYc : Yc =ᵐ[P] Y := by
    filter_upwards [haeY.ae_eq_mk] with ω hω
    -- hω : Y ω = haeY.mk Y ω
    have hbX := clamp01_mem (X ω)
    have hYb : 0 ≤ Y ω ∧ Y ω ≤ 1 := by
      dsimp [Y]
      exact hbX
    dsimp [Yc]
    rw [← hω]
    exact clamp01_id hYb.1 hYb.2
  have hY : Y =ᵐ[P] X := clamp01_ae_eq_of_law P hX
  have hYcX : Yc =ᵐ[P] X := hYc.trans hY
  refine ⟨Yc, ?_, ?_, ?_, hYcX⟩
  · -- measurable
    exact (clamp01_continuous.measurable.comp haeY.measurable_mk)
  · -- law
    refine ⟨(clamp01_continuous.measurable.comp haeY.measurable_mk).aemeasurable, ?_⟩
    have hcongr := Measure.map_congr (mβ := (inferInstance : MeasurableSpace ℝ)) hYcX
    rw [hcongr]
    exact hX.map_eq
  · -- pointwise bound
    intro ω
    dsimp [Yc]
    exact clamp01_abs_le_one (haeY.mk Y ω)
/-! ## 7. Matrix-level clamped representative and law-only `σ_min` bound

From a family `B : Ω → Matrix (Fin n) (Fin n) ℝ` whose entries satisfy only
`iIndepFun` and Bernoulli laws, produce a matrix `B̂` with *measurable*
entries, pointwise bound `|B̂ − p| ≤ 1`, the same independence and laws, and
with `B̂ =ᵐ B` entrywise.  Then (by the transfer lemma) every event that
depends pointwise on the matrix has the same real measure for `B̂` and `B`,
so the compress-side bounds (which require measurability and the pointwise
bound) transfer to the law-only hypothesis set of Theorem A.
-/

/-- Pointwise-`a.e.`-equal matrix families give equal real measures for all
pointwise events. -/
lemma measureReal_matrix_event_eq_of_ae {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (B C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hae : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => C ω i j))
    (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    P.real {ω : Ω | B ω ∈ S} = P.real {ω : Ω | C ω ∈ S} := by
  let Nij : Fin n → Fin n → Set Ω := fun i j => {ω : Ω | B ω i j ≠ C ω i j}
  have hNnull : ∀ i j : Fin n, P (Nij i j) = 0 := by
    intro i j
    have h := hae i j
    have hz : P {ω : Ω | ¬ (B ω i j = C ω i j)} = 0 := (MeasureTheory.ae_iff (μ := P)).1 h
    simpa [Nij] using hz
  let N : Set Ω := {ω : Ω | B ω ≠ C ω}
  have hNle : N ⊆ ⋃ p : Fin n × Fin n, Nij p.1 p.2 := by
    intro ω hω
    rw [Set.mem_iUnion]
    by_contra hnot
    have hEq : B ω = C ω := by
      funext i j
      by_contra hij
      exact hnot (Exists.intro (i, j) (by simpa [Nij] using hij))
    exact hω hEq
  have hunion0 : P (⋃ p : Fin n × Fin n, Nij p.1 p.2) = 0 := by
    have hle : P (⋃ p : Fin n × Fin n, Nij p.1 p.2) ≤ ∑ p : Fin n × Fin n, P (Nij p.1 p.2) := by
      have h := measure_biUnion_finset_le (μ := P) (Finset.univ : Finset (Fin n × Fin n))
        (fun p => Nij p.1 p.2)
      simpa using h
    have hsum : (∑ p : Fin n × Fin n, P (Nij p.1 p.2)) = 0 := by
      simp [hNnull]
    apply le_antisymm
    · exact le_trans hle (le_of_eq hsum)
    · exact bot_le
  have hN0 : P N = 0 := measure_mono_null hNle hunion0
  have hNreal : P.real N = 0 := by
    rw [Measure.real_def, hN0]
    simp
  apply le_antisymm
  · have hle1 : {ω : Ω | B ω ∈ S} ⊆ {ω : Ω | C ω ∈ S} ∪ N := by
      intro ω hω
      by_cases hB : B ω = C ω
      · exact Or.inl (by simpa [hB] using hω)
      · exact Or.inr hB
    have h1 : P.real {ω : Ω | B ω ∈ S} ≤ P.real ({ω : Ω | C ω ∈ S} ∪ N) := by
      exact MeasureTheory.measureReal_mono hle1 (by
        have hle : P ({ω : Ω | C ω ∈ S} ∪ N) ≤ (1 : ℝ≥0∞) := by
          have hmono : P ({ω : Ω | C ω ∈ S} ∪ N) ≤ P Set.univ :=
            MeasureTheory.measure_mono (Set.subset_univ _)
          simpa using hmono
        exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle)
    have h2 := MeasureTheory.measureReal_union_le (μ := P) {ω : Ω | C ω ∈ S} N
    calc
      P.real {ω : Ω | B ω ∈ S} ≤ P.real ({ω : Ω | C ω ∈ S} ∪ N) := h1
      _ ≤ P.real {ω : Ω | C ω ∈ S} + P.real N := h2
      _ = P.real {ω : Ω | C ω ∈ S} := by simp [hNreal]
  · have hle2 : {ω : Ω | C ω ∈ S} ⊆ {ω : Ω | B ω ∈ S} ∪ N := by
      intro ω hω
      by_cases hB : B ω = C ω
      · exact Or.inl (by simpa [hB] using hω)
      · exact Or.inr hB
    have h1 : P.real {ω : Ω | C ω ∈ S} ≤ P.real ({ω : Ω | B ω ∈ S} ∪ N) := by
      exact MeasureTheory.measureReal_mono hle2 (by
        have hle : P ({ω : Ω | B ω ∈ S} ∪ N) ≤ (1 : ℝ≥0∞) := by
          have hmono : P ({ω : Ω | B ω ∈ S} ∪ N) ≤ P Set.univ :=
            MeasureTheory.measure_mono (Set.subset_univ _)
          simpa using hmono
        exact ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle)
    have h2 := MeasureTheory.measureReal_union_le (μ := P) {ω : Ω | B ω ∈ S} N
    calc
      P.real {ω : Ω | C ω ∈ S} ≤ P.real ({ω : Ω | B ω ∈ S} ∪ N) := h1
      _ ≤ P.real {ω : Ω | B ω ∈ S} + P.real N := h2
      _ = P.real {ω : Ω | B ω ∈ S} := by simp [hNreal]
/-- Matrix-level clamped representative: from a family `B : Ω → Matrix` whose
entries are only known to be `iIndepFun` with Bernoulli laws, produce a matrix
`Bc` with measurable entries, the pointwise bound `|Bc−p| ≤ 1`, the same
independence and laws, and entries `a.e.`-equal to those of `B`. -/
theorem exists_measurable_clamped_matrix {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {p : I} (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P) :
    ∃ Bc : Ω → Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, Measurable (fun ω => Bc ω i j)) ∧
      ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (Bc · x.1 x.2)) P ∧
      (∀ i j : Fin n, HasLaw (Bc · i j) (bernoulliMeasure 1 0 p) P) ∧
      (∀ i j : Fin n, ∀ ω : Ω, |Bc ω i j - (p : ℝ)| ≤ 1) ∧
      (∀ i j : Fin n, (fun ω => Bc ω i j) =ᵐ[P] (fun ω => B ω i j)) := by
  classical
  let Y : Fin n → Fin n → Ω → ℝ := fun i j =>
    Classical.choose (exists_measurable_clamped_entry P (hBlaw i j))
  have hY : ∀ i j : Fin n,
      Measurable (Y i j) ∧ HasLaw (Y i j) (bernoulliMeasure 1 0 p) P ∧
      (∀ ω : Ω, |Y i j ω - (p : ℝ)| ≤ 1) ∧ Y i j =ᵐ[P] (fun ω => B ω i j) := by
    intro i j
    exact Classical.choose_spec (exists_measurable_clamped_entry P (hBlaw i j))
  let Bc : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => Matrix.of (fun i j => Y i j ω)
  have hBcij : ∀ i j : Fin n, (fun ω => Bc ω i j) = Y i j := by
    intro i j
    funext ω
    simp [Bc]
  have ae_of_eq : ∀ {F G : Ω → ℝ}, F = G → F =ᵐ[P] G := by
    intro F G h
    rw [h]
  refine ⟨Bc, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurable entries
    intro i j
    rw [hBcij i j]
    exact (hY i j).1
  · -- iIndepFun
    have hcongr : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (Bc · x.1 x.2)) P ↔
        ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P := by
      apply ProbabilityTheory.iIndepFun_congr
      intro x
      calc
        (Bc · x.1 x.2) =ᵐ[P] Y x.1 x.2 := by
          exact ae_of_eq (hBcij x.1 x.2)
        _ =ᵐ[P] (B · x.1 x.2) := (hY x.1 x.2).2.2.2
    exact hcongr.2 hBind
  · -- laws
    intro i j
    rw [hBcij i j]
    exact (hY i j).2.1
  · -- pointwise bound
    intro i j ω
    have hv : Bc ω i j = Y i j ω := congrFun (hBcij i j) ω
    rw [hv]
    exact (hY i j).2.2.1 ω
  · -- ae equal to B
    intro i j
    calc
      (fun ω => Bc ω i j) =ᵐ[P] Y i j := ae_of_eq (hBcij i j)
      _ =ᵐ[P] (fun ω => B ω i j) := (hY i j).2.2.2

/-- Law-only version of `sigma_min_decomp`: Theorem A's hypothesis set
(`iIndepFun` + Bernoulli laws, no measurability, no pointwise bound) suffices
for the compress-side bound; the clamped representative transfers events. -/
theorem sigma_min_decomp_law_only {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ν : ℝ, 0 < ν ∧ ν < 1 ∧
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, s + (p : ℝ) ≠ 0 → ∀ u : ℝ, 0 < u →
          u ≤ γ₀ * Real.sqrt (n : ℝ) →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
            ≤ (1 - (p : ℝ) + ε) ^ n
              + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
                  ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
                  actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
  rcases sigma_min_decomp hp₀ hp₁ hε₀ with ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, hdec⟩
  refine ⟨n₀, hn₀2, γ₀, hγ₀, δ, hδ0, hδ1, ν, hν0, hν1, ?_⟩
  intro n hn Ω mΩ P hP B hBind hBlaw s hss u hu0 hule
  rcases exists_measurable_clamped_matrix (P := P) B hBind hBlaw with
    ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩
  have hdecBc := hdec n hn (Ω := Ω) P Bc hcm hcind hclaw hcpt s hss u hu0 hule
  -- transfer of the sigma_min event
  let Sσ : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | RandomBernoulliMatrices.σ_min (M + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
  have htr1 : P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} =
      P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} := by
    exact (measureReal_matrix_event_eq_of_ae (P := P) Bc B hcae Sσ).symm
  -- transfer of the incompressible event
  let Sin : Set (Matrix (Fin n) (Fin n) ℝ) := {M | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => M i j + s) f ≤ u ^ 2}
  have htr2 : P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} =
      P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
      ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
      actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by
    exact measureReal_matrix_event_eq_of_ae (P := P) Bc B hcae Sin
  have hmain : P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
      ≤ (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} := hdecBc
  calc
    P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u}
        = P.real {ω : Ω | RandomBernoulliMatrices.σ_min (Bc ω + Matrix.of (fun _ _ : Fin n => s)) ≤ u} := htr1
    _ ≤ (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => Bc ω i j + s) f ≤ u ^ 2} := hmain
    _ = (1 - (p : ℝ) + ε) ^ n + P.real {ω : Ω | ∃ f : Fin n → ℝ, sqNorm f = 1 ∧
        ¬ Commons.LinearAlgebra.Net.compressible δ ν f ∧
        actSqFullFn (fun i j : Fin n => B ω i j + s) f ≤ u ^ 2} := by rw [htr2]


end
end Submission.GeoBridge
