import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

open Work.BourgainPlan.IonescuWainger

/-- **The reduced representative of a fraction.**  Writing `d = gcd a q`, the fractions `a/q` and
`(a/d)/(q/d)` are the same real number, hence the same point of the circle. -/
lemma arcPt_reduce_gcd {q a : ℕ} (hq : 0 < q) :
    arcPt q (a : ℤ) = arcPt (q / Nat.gcd a q) ((a / Nat.gcd a q : ℕ) : ℤ) := by
  have hd0 : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hq
  have hdR : ((Nat.gcd a q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  have haR : ((a : ℕ) : ℝ)
      = ((a / Nat.gcd a q : ℕ) : ℝ) * ((Nat.gcd a q : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left a q)]
  have hqR : ((q : ℕ) : ℝ)
      = ((q / Nat.gcd a q : ℕ) : ℝ) * ((Nat.gcd a q : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.gcd_dvd_right a q)]
  have hreal : ((a : ℝ) / (q : ℝ))
      = (((a / Nat.gcd a q : ℕ) : ℝ) / ((q / Nat.gcd a q : ℕ) : ℝ)) := by
    rw [haR, hqR, mul_div_mul_right _ _ hdR]
  unfold arcPt
  push_cast
  exact congrArg (fun t : ℝ => (t : AddCircle (1 : ℝ))) hreal

/-- **Reduction of a rational point to lowest terms**, with the denominator controlled by the
denominator of any representative: if `0 < q` and `0 ≤ a < q`, the point `a/q ∈ 𝕋` has a reduced
representative `a'/q'` (`0 < q'`, `0 ≤ a' < q'`, `gcd a' q' = 1`) with `q' ≤ q`. -/
lemma exists_reduced_arcPt_rep {q : ℕ} (hq : 0 < q) (a : ℕ) (ha : a < q) :
    ∃ (q' : ℕ) (a' : ℤ), 0 < q' ∧ 0 ≤ a' ∧ a' < q' ∧ Int.gcd a' (q' : ℤ) = 1 ∧
      arcPt q' a' = arcPt q (a : ℤ) ∧ q' ≤ q := by
  have hdpos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hq
  have hdle : Nat.gcd a q ≤ q := Nat.gcd_le_right a hq
  have hq'pos : 0 < q / Nat.gcd a q := Nat.div_pos hdle hdpos
  refine ⟨q / Nat.gcd a q, ((a / Nat.gcd a q : ℕ) : ℤ),
    hq'pos, Int.natCast_nonneg _, ?_, ?_, (arcPt_reduce_gcd hq).symm, Nat.div_le_self q _⟩
  · have h1 : (a / Nat.gcd a q) * Nat.gcd a q = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a q)
    have h2 : (q / Nat.gcd a q) * Nat.gcd a q = q := Nat.div_mul_cancel (Nat.gcd_dvd_right a q)
    have h3 : (a / Nat.gcd a q) * Nat.gcd a q < (q / Nat.gcd a q) * Nat.gcd a q := by
      rw [h1, h2]; exact ha
    have h4 : a / Nat.gcd a q < q / Nat.gcd a q := lt_of_mul_lt_mul_right h3 (Nat.zero_le _)
    exact_mod_cast h4
  · have hcop : Nat.Coprime (a / Nat.gcd a q) (q / Nat.gcd a q) :=
      Nat.coprime_div_gcd_div_gcd hdpos
    have hg : Nat.gcd (a / Nat.gcd a q) (q / Nat.gcd a q) = 1 := hcop
    rw [Int.gcd_natCast_natCast, hg]

/-- Every point of the level set `mstU l n = iwSigma (mstRho l) (n^l)` has a reduced representative `arcPt q a` with `0 < q`, `0 ≤ a < q`, `gcd a q = 1`, for all large `n`, with the denominator bounded by `exp((n^l)^{1/(10l)})`.

Route: `mstU l n = sigmaLeFinset (taoSetS (mstRho l) (n^l)) (iwK (mstRho l))` is a union of `sigmaSubAFinset B`, and `sigmaSubAFinset B = (Finset.range (QA B)).image (arcPt (QA B))`, so `β = arcPt (QA B) a` for some `1 ≤ QA B` and `a ∈ range (QA B)`; cancelling the common divisor `g = gcd a (QA B)` gives a reduced representative with the same point (use that `arcPt Q b = arcPt (Q/g) (b/g)` when `g ∣ Q`), still of denominator `≤ QA B`; and `QA B ≤ exp((n^l)^{1/(10l)})` for large `n` by `sigmaN_QA_le_exp_quarter` (which gives `Q_A ≤ exp(N^ρ/4)`, `N = n^l`, `ρ = mstRho l`, `N^ρ = n^{1/10}`), with `∅ ⊆ B ⊆ A`.  The largeness hypothesis `(hl : 1 ≤ l)` gives `mstRho l > 0`; the `∃ n₀` absorbs the threshold of `sigmaN_QA_le_exp_quarter`.  Hints: the map `arcPt` and the arithmetic helpers `arcPt_add`, `arcPt_sub_denom`, `arcPt_mem_sigmaSubAFinset_of_dvd` are in `IonescuWainger/ArcDefs.lean`, `IonescuWainger/ArcSep.lean` and `Maximal/sigmaN_farey_helpers.lean`. -/
theorem mstU_rep (l : ℕ) (hl : 1 ≤ l) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ β : Work.BourgainPlan.IonescuWainger.Circle,
      β ∈ Work.BourgainPlan.Maximal.mstU l n →
      ∃ (q : ℕ) (a : ℤ), 0 < q ∧ 0 ≤ a ∧ a < q ∧ Int.gcd a (q : ℤ) = 1 ∧
        Work.BourgainPlan.IonescuWainger.arcPt q a = β ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (Work.BourgainPlan.Maximal.mstRho l)) := by
  have hρ : 0 < mstRho l := by
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    unfold mstRho
    positivity
  obtain ⟨N₁, hN₁⟩ := sigmaN_QA_le_exp_quarter (mstRho l) hρ
  refine ⟨max N₁ 1, ?_⟩
  intro n hn β hβ
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN₁le : N₁ ≤ n ^ l := by
    have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) hn
    calc N₁ ≤ n := hN₁n
      _ = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ l := Nat.pow_le_pow_right (by omega) hl
  rw [mstU_apply, iwSigma, sigmaLeFinset] at hβ
  rw [Finset.mem_biUnion] at hβ
  obtain ⟨A, hA, hβA⟩ := hβ
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, hAcard⟩ := hA
  rw [sigmaSubAFinset, Finset.mem_image] at hβA
  obtain ⟨a₀, ha₀mem, hβeq⟩ := hβA
  rw [Finset.mem_range] at ha₀mem
  have hQpos : 0 < QA A := lt_of_le_of_lt (Nat.zero_le a₀) ha₀mem
  have hAcard' : A.card ≤ ⌊2 / mstRho l⌋₊ + 1 := by simpa [iwK] using hAcard
  have hQAbound : (QA A : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ mstRho l) := by
    have h := hN₁ (n ^ l) hN₁le A hAsub hAcard'
    rw [Nat.cast_pow] at h
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    have hnn : 0 ≤ ((n : ℝ) ^ l) ^ mstRho l :=
      Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg n) l) _
    linarith
  obtain ⟨q', a', hq'pos, ha'nn, ha'lt, hgcd', harc', hq'le⟩ :=
    exists_reduced_arcPt_rep hQpos a₀ ha₀mem
  refine ⟨q', a', hq'pos, ha'nn, ha'lt, hgcd', harc'.trans hβeq, ?_⟩
  exact le_trans (by exact_mod_cast hq'le) hQAbound

end Work.BourgainPlan.Maximal
