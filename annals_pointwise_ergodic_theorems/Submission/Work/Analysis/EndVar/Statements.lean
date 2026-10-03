import Submission.Work.Analysis.EndVar.Defs
import Submission.Port.Aesm

/-!
# The two inputs of the §5 assembly

The §5 reduction of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals 195 (2022), shows that the paper's variational estimate `end-var`
follows from two estimates about a family `R : ℝ≥0 → (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)` of
"major-arc parts" of the halved averages `Ã_N`:

* `MajorArcVarEstimate` — **(A)**: the variational estimate for the major arc parts;
* `MajorArcApproximation` — **(B)**: the halved averages are approximated by their major arc
  parts with a summable `ℓ^p` error `Cerr`.

This module states the two properties and records the elementary variational-norm lemmas used by
the assembly `varEstHalfFin_of_majorArc` (see `Assembly.lean`).  The two properties are exactly
the targets named in the assignment of the `EndVar` area; they are supplied by

* **(A)** the paraproduct analysis of §4/§7--§10, through Theorem `varp`
  (`majorArcVarEstimate_of_varp`, see `Varp.lean`);
* **(B)** the single-scale minor arc estimate `improv` of §5 together with the Ionescu--Wainger
  projection properties `iw-prop` (`majorArcApproximation_of_improv`, see `Approx.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-! ## The two inputs -/

/-- **(A) The major-arc variational estimate.**  For a family `R` of major-arc parts, the
variational estimate `(vrb)` holds with a constant `Cv Λ` depending only on the lacunarity
parameter.  This is the estimate obtained from the paper's Theorem `varp` by the dyadic
decompositions of §5 (see `majorArcVarEstimate_of_varp`). -/
def MajorArcVarEstimate (R : ℝ≥0 → (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (f g : ℤ → ℂ),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x : ℤ => variationalNorm r (fun n => R (a n) f g x)) p Measure.count
      ≤ (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- The clamped form of `MajorArcVarEstimate`: for every `K` the same estimate holds for the
clamped family `n ↦ R (a (min n K))`, by `variationalNorm_comp_min_le`. -/
theorem MajorArcVarEstimate.clamped {R p₁ p₂ p r Cv}
    (h : MajorArcVarEstimate R p₁ p₂ p r Cv) :
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (K : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n => R (a (min n K)) f g x)) p Measure.count
        ≤ (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
  intro a Λ K f g hΛ ha ha1
  exact (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x =>
    variationalNorm_comp_min_le r (fun n => R (a n) f g x) K)).trans (h a Λ f g hΛ ha ha1)

/-- **(B) The summable major-arc approximation.**  The halved averages `Ã_{a n}` and their
major-arc parts `R (a n)` differ by an error whose `ℓ^p`-norm is bounded by `Cerr Λ n ‖f‖ ‖g‖`,
with `∑_{n < K} Cerr Λ n ≤ C Λ` uniformly in `K` (so that the error is summable over the lacunary
set of scales).  This is the consequence of Theorem `improv` established in §5 (see
`majorArcApproximation_of_improv`).

The error weight necessarily depends on the lacunarity parameter `Λ`: for a `Λ`-lacunary sequence
`a` with `a 0 ≥ 1` one has `a n ≥ Λ ^ n`, so the largest possible error at index `n` occurs at the
smallest admissible scale `≈ Λ ^ n`.  The paper's weight `(Log (a n))^{-10}` is therefore summable
in `n` with a bound depending on `Λ`, but there is no `Λ`-independent error weight: as `Λ → 1⁺` one
has `Λ ^ n → 1` for every fixed `n`, so no summable `Λ`-independent weight can dominate the error.
Hence `Cerr : ℝ≥0 → ℕ → ℝ≥0` and `C : ℝ≥0 → ℝ≥0`. -/
def MajorArcApproximation (P : ℤ[X]) (R : ℝ≥0 → (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (p₁ p₂ p : ℝ≥0∞) (Cerr : ℝ≥0 → ℕ → ℝ≥0) (C : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (f g : ℤ → ℂ),
    1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
    (∀ n : ℕ, eLpNorm (fun x : ℤ =>
        AhalfR TZ (a n) X P f g x - R (a n) f g x) p Measure.count
      ≤ (Cerr Λ n : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) ∧
    (∀ K : ℕ, ∑ n ∈ Finset.range K, Cerr Λ n ≤ C Λ)

/-- The clamped form of the pointwise approximation hypothesis of `MajorArcApproximation`: at the
clamped scale `a (min n K)` the error is bounded by `Cerr (min n K)`. -/
theorem MajorArcApproximation.min_le {P R p₁ p₂ p Cerr C}
    (h : MajorArcApproximation P R p₁ p₂ p Cerr C)
    {a : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : 1 < Λ) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (f g : ℤ → ℂ) (K n : ℕ) :
    eLpNorm (fun x : ℤ =>
        AhalfR TZ (a (min n K)) X P f g x - R (a (min n K)) f g x) p Measure.count
      ≤ (Cerr Λ (min n K) : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
  (h a Λ f g hΛ ha ha1).1 (min n K)

/-! ## Elementary variational-norm lemmas -/

/-- The variation part of a "right step" sequence `n ↦ if n < m then 0 else z` is at most
`‖z‖` (mirror of `varPart_step_le`). -/
lemma varPart_step_right_le {r : ℝ≥0} (hr : 1 ≤ r) (m : ℕ) (z : ℂ) :
    varPart r (fun n => if n < m then (0 : ℂ) else z) ≤ ‖z‖ₑ := by
  have : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  set w : Fin J → ℂ := fun i =>
    (if N ((i : ℕ) + 1) < m then (0 : ℂ) else z) - (if N (i : ℕ) < m then (0 : ℂ) else z)
    with hw
  have hspec : ∀ i, w i ≠ 0 → N (i : ℕ) < m ∧ m ≤ N ((i : ℕ) + 1) := by
    intro i hi
    by_cases h1 : N (i : ℕ) < m
    · by_cases h2 : N ((i : ℕ) + 1) < m
      · exact absurd (by simp [hw, h1, h2]) hi
      · exact ⟨h1, le_of_not_gt h2⟩
    · have h2' : ¬ (N ((i : ℕ) + 1) < m) :=
        Nat.not_lt.mpr (le_trans (le_of_not_gt h1) (hN (Nat.le_succ (i : ℕ))))
      exact absurd (by simp [hw, h1, h2']) hi
  have hwle : ∀ i, ‖w i‖ ≤ ‖z‖ := by
    intro i
    rcases lt_or_ge (N (i : ℕ)) m with h | h
    · rcases lt_or_ge (N ((i : ℕ) + 1)) m with h2 | h2
      · have : w i = 0 := by simp [hw, h, h2]
        rw [this]; simp
      · have : w i = z := by simp [hw, h, h2]
        rw [this]
    · have h2 : ¬ (N ((i : ℕ) + 1) < m) :=
        Nat.not_lt.mpr (le_trans h (hN (Nat.le_succ (i : ℕ))))
      have hlt : ¬ (N (i : ℕ) < m) := Nat.not_lt.mpr h
      have : w i = 0 := by simp [hw, hlt, h2]
      rw [this]; simp
  have hcard : (Finset.univ.filter (fun i : Fin J => w i ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨ha1, ha2⟩ := hspec a ha
    obtain ⟨hb1, hb2⟩ := hspec b hb
    rcases le_total (a : ℕ) (b : ℕ) with h | h
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact Fin.ext heq
      · exfalso
        have : N ((a : ℕ) + 1) ≤ N (b : ℕ) := hN (by omega)
        omega
    · rcases eq_or_lt_of_le h with heq | hlt
      · exact Fin.ext heq.symm
      · exfalso
        have : N ((b : ℕ) + 1) ≤ N (a : ℕ) := hN (by omega)
        omega
  have hsum : ∑ i : Fin J, ‖w i‖ ≤ ‖z‖ := by
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖w i‖ = ∑ i : Fin J, ‖w i‖ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : w i ≠ 0
      · simp [h]
      · rw [if_neg h, not_not.mp h]; simp
    rw [← h1]
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖w i‖
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin J => w i ≠ 0), ‖z‖ :=
          Finset.sum_le_sum (fun i _ => hwle i)
      _ = ((Finset.univ.filter (fun i : Fin J => w i ≠ 0)).card : ℝ) * ‖z‖ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
          exact_mod_cast hcard
      _ = ‖z‖ := one_mul _
  calc ENNReal.ofReal ‖WithLp.toLp r w‖
      ≤ ENNReal.ofReal (∑ i : Fin J, ‖w i‖) := ENNReal.ofReal_le_ofReal (norm_toLp_le_sum_norm hr w)
    _ ≤ ENNReal.ofReal ‖z‖ := ENNReal.ofReal_le_ofReal hsum
    _ = ‖z‖ₑ := ofReal_norm z

/-- The variational norm of the "right step" sequence `n ↦ if n < K then 0 else c` is at most
`2‖c‖`, independently of `K`. -/
lemma variationalNorm_step_right_le {r : ℝ≥0} (hr : 1 ≤ r) (K : ℕ) (c : ℂ) :
    variationalNorm r (fun n : ℕ => if n < K then (0 : ℂ) else c) ≤ 2 * ‖c‖ₑ := by
  rw [variationalNorm_eq_add, two_mul]
  refine add_le_add ?_ (varPart_step_right_le hr K c)
  refine iSup_le (fun n => ?_)
  by_cases h : n < K <;> simp [h]

/-- The variational norm of the clamped difference `n ↦ u (min n K) - v (min n K)` of two
families which are constant after `K` is controlled by the sum of the errors before `K` and the
error at `K` — with **no** factor of `K` on the last term. -/
lemma variationalNorm_clamp_sub_le {r : ℝ≥0} (hr : 1 ≤ r) (u v : ℕ → ℂ) (K : ℕ)
    (hu : ∀ n, K ≤ n → u n = u K) (hv : ∀ n, K ≤ n → v n = v K) :
    variationalNorm r (fun n => u n - v n)
      ≤ ∑ n ∈ Finset.range K, 4 * ‖u n - v n‖ₑ + 2 * ‖u K - v K‖ₑ := by
  have hdecomp : (fun n => u n - v n)
      = (fun n => if n < K then u n - v n else 0)
        + (fun n => if n < K then 0 else u K - v K) := by
    funext n
    by_cases h : n < K
    · simp [h]
    · have hu' := hu n (by omega)
      have hv' := hv n (by omega)
      simp [h, hu', hv']
  rw [hdecomp]
  refine (variationalNorm_add_le hr _ _).trans
    (add_le_add ?_ (variationalNorm_step_right_le hr K (u K - v K)))
  refine (variationalNorm_le_sum_enorm (r := r) (hr := hr)
    (u := fun n => if n < K then u n - v n else 0) (s := Finset.range K) ?_).trans
    (le_of_eq ?_)
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [hn]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_range] at hn
    rw [if_pos hn]

end

end Work.Analysis.EndVar
