import Mathlib
import Submission.GenProc
import Submission.OpNorm
import Submission.Contact
import Submission.Commons.MeasureTheory.Pi.pi_map_restrict_fin
import Submission.Commons.Probability.Reflection.fin_maximal_tail_Phi_of_map_pi

set_option synthInstance.maxHeartbeats 1000000

/-!
# The per-time contact estimate

`Submission/ContactBound.lean` bounds, for a single vector `y`, the probability that `y` is
violated *at some time* `k ≤ K`, i.e. it uses the maximal inequality with the full horizon `K`.
That costs a factor `K ≈ 16 d² log d` in the final bookkeeping, which is fatal: the drift gain is
only `≈ 4 log d`.

This file provides the *per-time* version: for every `k ≤ K` and every `W` with `‖W‖ ≤ 1`,

    P( r ≤ |∑_{j<k} ε ⟪incr_j, W⟫| )  ≤  8 · tailG (r / (ε √k)) ,

obtained by restricting the Gaussian sample to the first `k` coordinates (the marginalisation
`Commons.MeasureTheory.Pi.pi_map_restrict_fin`) and then applying the *sharp* maximal tail
`Commons.Probability.Reflection.fin_maximal_tail_Phi_of_map_pi`.
-/

namespace Submission.ContactSharp

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.OpNorm
open Submission.Contact

noncomputable section

variable {d : ℕ}

/-- The one-sided standard Gaussian upper tail. -/
def tailG (z : ℝ) : ℝ := (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | z ≤ y}

lemma tailG_nonneg (z : ℝ) : 0 ≤ tailG z := measureReal_nonneg

lemma tailG_mono {a b : ℝ} (hab : a ≤ b) : tailG b ≤ tailG a :=
  Commons.Probability.Reflection.stdGaussian_real_tail_antitone hab

lemma stdGaussian_real_univ : (ProbabilityTheory.stdGaussian ℝ).real Set.univ = 1 := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.measure_univ, ENNReal.toReal_one]

lemma tailG_le_one (z : ℝ) : tailG z ≤ 1 := by
  have h := MeasureTheory.measureReal_mono (μ := ProbabilityTheory.stdGaussian ℝ)
    (Set.subset_univ {y : ℝ | z ≤ y}) (by simp)
  rwa [stdGaussian_real_univ] at h

variable (pl : MatV d → MatV d →L[ℝ] MatV d) (a₀ ε : ℝ)

/-- Restricting the `η`-walk to the first `k` coordinates gives the product law. -/
theorem law_eta_restrict {K k : ℕ} (hk : k ≤ K) (hpl : Measurable pl)
    (hG : ∀ A : MatV d, Good (pl A)) :
    (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d =>
        fun i : Fin k => etaAt pl a₀ ε K ω (Fin.castLE hk i))
      = MeasureTheory.Measure.pi (fun _ : Fin k => ProbabilityTheory.stdGaussian (MatV d)) := by
  have h1 : (fun ω : Fin K → MatV d × MatV d => fun i : Fin k => etaAt pl a₀ ε K ω (Fin.castLE hk i))
      = (fun x : Fin K → MatV d => fun i : Fin k => x (Fin.castLE hk i))
        ∘ (fun ω : Fin K → MatV d × MatV d => fun j : Fin K => etaAt pl a₀ ε K ω j) := rfl
  rw [h1, ← Measure.map_map]
  · rw [law_eta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG,
      Commons.MeasureTheory.Pi.pi_map_restrict_fin hk (ProbabilityTheory.stdGaussian (MatV d))]
  · exact Measurable.of_eval (fun i => measurable_pi_apply (Fin.castLE hk i))
  · exact Measurable.of_eval (fun j => measurable_etaAt (pl := pl) (a₀ := a₀) (ε := ε)
      (K := K) hpl j)

/-- Restricting the `ζ`-walk to the first `k` coordinates gives the product law. -/
theorem law_zeta_restrict {K k : ℕ} (hk : k ≤ K) (hpl : Measurable pl)
    (hG : ∀ A : MatV d, Good (pl A)) :
    (sampleLaw d K).map (fun ω : Fin K → MatV d × MatV d =>
        fun i : Fin k => zetaAt pl a₀ ε K ω (Fin.castLE hk i))
      = MeasureTheory.Measure.pi (fun _ : Fin k => ProbabilityTheory.stdGaussian (MatV d)) := by
  have h1 : (fun ω : Fin K → MatV d × MatV d => fun i : Fin k => zetaAt pl a₀ ε K ω (Fin.castLE hk i))
      = (fun x : Fin K → MatV d => fun i : Fin k => x (Fin.castLE hk i))
        ∘ (fun ω : Fin K → MatV d × MatV d => fun j : Fin K => zetaAt pl a₀ ε K ω j) := rfl
  rw [h1, ← Measure.map_map]
  · rw [law_zeta (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl hG,
      Commons.MeasureTheory.Pi.pi_map_restrict_fin hk (ProbabilityTheory.stdGaussian (MatV d))]
  · exact Measurable.of_eval (fun i => measurable_pi_apply (Fin.castLE hk i))
  · exact Measurable.of_eval (fun j => by
      have hp : Measurable fun ω : Fin K → MatV d × MatV d =>
          (projAt pl a₀ ε K ω j, (ω j).1, (ω j).2) :=
        Measurable.prodMk (measurable_projAt_ω (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
          (Measurable.prodMk (measurable_pi_apply j).fst (measurable_pi_apply j).snd)
      have hcont : Measurable fun q : (MatV d →L[ℝ] MatV d) × (MatV d × MatV d) =>
          q.1 q.2.1 - (ContinuousLinearMap.id ℝ (MatV d) - q.1) q.2.2 := by
        fun_prop
      exact hcont.comp hp)

/-- Sums over the first `k` coordinates of the `K`-indexed family equal sums over `Fin k`. -/
lemma sum_filter_castLE {K m : ℕ} (hm : m ≤ K) {α : Type*} [AddCommMonoid α] (f : Fin K → α) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < m), f (Fin.castLE hm i))
      = ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < m), f j := by
  classical
  have hset : (Finset.univ.filter (fun j : Fin K => (j : ℕ) < m))
      = (Finset.univ.filter (fun i : Fin m => (i : ℕ) < m)).map
          ⟨Fin.castLE hm, Fin.castLE_injective hm⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hj
      refine ⟨⟨j.val, by omega⟩, by simpa using hj, ?_⟩
      exact Fin.ext rfl
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [hset, Finset.sum_map]
  rfl

/-- Measurability of the `ζ`-increment. -/
lemma measurable_zetaAt_aux {K : ℕ} (hpl : Measurable pl) (j : Fin K) :
    Measurable fun ω : Fin K → MatV d × MatV d => zetaAt pl a₀ ε K ω j := by
  have hp : Measurable fun ω : Fin K → MatV d × MatV d =>
      (projAt pl a₀ ε K ω j, (ω j).1, (ω j).2) :=
    Measurable.prodMk (measurable_projAt_ω (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl j)
      (Measurable.prodMk (measurable_pi_apply j).fst (measurable_pi_apply j).snd)
  have hcont : Measurable fun q : (MatV d →L[ℝ] MatV d) × (MatV d × MatV d) =>
      q.1 q.2.1 - (ContinuousLinearMap.id ℝ (MatV d) - q.1) q.2.2 := by fun_prop
  exact hcont.comp hp

/-- **Scalar maximal tail along the first `k` steps of the `η` walk.** -/
theorem maximal_tail_eta_k {K k : ℕ} (hk : k ≤ K) (hpl : Measurable pl)
    (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d) (hW : ‖W‖ ≤ 1) {r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    (sampleLaw d K).real {ω | ∃ m ≤ k, r ≤ |∑ i ∈ Finset.univ.filter
        (fun i : Fin k => (i : ℕ) < m),
          ε * inner ℝ (etaAt pl a₀ ε K ω (Fin.castLE hk i)) W|}
      ≤ 4 * tailG (r / (ε * Real.sqrt k)) :=
  Commons.Probability.Reflection.fin_maximal_tail_Phi_of_map_pi
    (fun i (ω : Fin K → MatV d × MatV d) => etaAt pl a₀ ε K ω (Fin.castLE hk i))
    (fun i => measurable_etaAt (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl (Fin.castLE hk i))
    (law_eta_restrict pl a₀ ε hk hpl hG) W hW hε hr

/-- **Scalar maximal tail along the first `k` steps of the `ζ` walk.** -/
theorem maximal_tail_zeta_k {K k : ℕ} (hk : k ≤ K) (hpl : Measurable pl)
    (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d) (hW : ‖W‖ ≤ 1) {r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    (sampleLaw d K).real {ω | ∃ m ≤ k, r ≤ |∑ i ∈ Finset.univ.filter
        (fun i : Fin k => (i : ℕ) < m),
          ε * inner ℝ (zetaAt pl a₀ ε K ω (Fin.castLE hk i)) W|}
      ≤ 4 * tailG (r / (ε * Real.sqrt k)) :=
  Commons.Probability.Reflection.fin_maximal_tail_Phi_of_map_pi
    (fun i (ω : Fin K → MatV d × MatV d) => zetaAt pl a₀ ε K ω (Fin.castLE hk i))
    (fun i => measurable_zetaAt_aux (pl := pl) (a₀ := a₀) (ε := ε) (K := K) hpl (Fin.castLE hk i))
    (law_zeta_restrict pl a₀ ε hk hpl hG) W hW hε hr
/-- Sums over the first `m` coordinates of the `K`-indexed family equal sums over `Fin k`. -/
lemma sum_filter_castLE' {K k m : ℕ} (hk : k ≤ K) (hm : m ≤ k) {α : Type*} [AddCommMonoid α]
    (f : Fin K → α) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < m), f (Fin.castLE hk i))
      = ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < m), f j := by
  classical
  have hset : (Finset.univ.filter (fun j : Fin K => (j : ℕ) < m))
      = (Finset.univ.filter (fun i : Fin k => (i : ℕ) < m)).map
          ⟨Fin.castLE hk, Fin.castLE_injective hk⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hj
      exact ⟨⟨j.val, by omega⟩, by simpa using hj, Fin.ext rfl⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [hset, Finset.sum_map]
  rfl
/-- **Per-time two-sided maximal tail for a linear functional.**  For every `k ≤ K` and every
`W` with `‖W‖ ≤ 1`, the probability that the increment sum up to time `k` exceeds `r` in modulus
is at most `8 · tailG (r / (ε √k))`.  This is the sharp per-time bound; using the horizon-`K`
maximal inequality instead would cost a factor `K`. -/
theorem maximal_tail_incr_k {K k : ℕ} (hk : k ≤ K) (hpl : Measurable pl)
    (hG : ∀ A : MatV d, Good (pl A)) (W : MatV d) (hW : ‖W‖ ≤ 1) {r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    (sampleLaw d K).real {ω | r ≤ |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) W|}
      ≤ 8 * tailG (r / (ε * Real.sqrt k)) := by
  classical
  set A : Set (Fin K → MatV d × MatV d) := {ω | ∃ m ≤ k, r ≤ |∑ i ∈ Finset.univ.filter
      (fun i : Fin k => (i : ℕ) < m),
        ε * inner ℝ (etaAt pl a₀ ε K ω (Fin.castLE hk i)) W|} with hA
  set B : Set (Fin K → MatV d × MatV d) := {ω | ∃ m ≤ k, r ≤ |∑ i ∈ Finset.univ.filter
      (fun i : Fin k => (i : ℕ) < m),
        ε * inner ℝ (zetaAt pl a₀ ε K ω (Fin.castLE hk i)) W|} with hB
  have hkey : ∀ ω : Fin K → MatV d × MatV d,
      (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) W)
      = (2 : ℝ)⁻¹ * ((∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (etaAt pl a₀ ε K ω j) W)
          + (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (zetaAt pl a₀ ε K ω j) W)) := by
    intro ω
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [incrAt_eq_half (pl := pl) (a₀ := a₀) (ε := ε) (K := K) ω j, inner_smul_left,
      inner_add_left]
    simp only [conj_trivial]
    ring
  have hsub : {ω | r ≤ |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) W|} ⊆ A ∪ B := by
    intro ω hle
    let S₁ : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
      ε * inner ℝ (etaAt pl a₀ ε K ω j) W
    let S₂ : ℝ := ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
      ε * inner ℝ (zetaAt pl a₀ ε K ω j) W
    have hX : (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt pl a₀ ε K ω j) W) = (2 : ℝ)⁻¹ * (S₁ + S₂) := hkey ω
    have hle' : r ≤ |(2 : ℝ)⁻¹ * (S₁ + S₂)| := by rw [← hX]; exact hle
    have hmax : r ≤ max |S₁| |S₂| := by
      have hb : |(2 : ℝ)⁻¹ * (S₁ + S₂)| ≤ max |S₁| |S₂| := by
        rw [abs_mul, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have h1 : |S₁ + S₂| ≤ |S₁| + |S₂| := abs_add_le _ _
        have h2 : |S₁| + |S₂| ≤ 2 * max |S₁| |S₂| := by
          linarith [le_max_left |S₁| |S₂|, le_max_right |S₁| |S₂|]
        have h3 : (2 : ℝ)⁻¹ * |S₁ + S₂| = |S₁ + S₂| / 2 := by ring
        linarith
      linarith
    have hconvη : S₁ = ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k),
        ε * inner ℝ (etaAt pl a₀ ε K ω (Fin.castLE hk i)) W :=
      (sum_filter_castLE' (K := K) (k := k) (m := k) hk le_rfl
        (fun j => ε * inner ℝ (etaAt pl a₀ ε K ω j) W)).symm
    have hconvζ : S₂ = ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k),
        ε * inner ℝ (zetaAt pl a₀ ε K ω (Fin.castLE hk i)) W :=
      (sum_filter_castLE' (K := K) (k := k) (m := k) hk le_rfl
        (fun j => ε * inner ℝ (zetaAt pl a₀ ε K ω j) W)).symm
    rcases le_max_iff.mp hmax with h | h
    · exact Or.inl ⟨k, le_rfl, by rw [← hconvη]; exact h⟩
    · exact Or.inr ⟨k, le_rfl, by rw [← hconvζ]; exact h⟩
  calc (sampleLaw d K).real _
      ≤ (sampleLaw d K).real (A ∪ B) :=
        MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
    _ ≤ (sampleLaw d K).real A + (sampleLaw d K).real B :=
        MeasureTheory.measureReal_union_le _ _
    _ ≤ 4 * tailG (r / (ε * Real.sqrt k)) + 4 * tailG (r / (ε * Real.sqrt k)) :=
        add_le_add (hA ▸ maximal_tail_eta_k (pl := pl) (a₀ := a₀) (ε := ε) hk hpl hG W hW hε hr)
          (hB ▸ maximal_tail_zeta_k (pl := pl) (a₀ := a₀) (ε := ε) hk hpl hG W hW hε hr)
    _ = 8 * tailG (r / (ε * Real.sqrt k)) := by ring
/-- **Per-time, per-vector contact probability.**  For a fixed nonzero vector `y` with
`a₀‖y‖² > 1` and every `k ≤ K`, the probability that `y` is violated *at time* `k` is at most
`8 · tailG ((a₀ - 1/‖y‖²)/(ε√k))`.  Compare `Submission.ContactBound.measureReal_quadFormV_le`,
which uses the full horizon `K` and is therefore off by a factor `K`. -/
theorem perTime_contact {m : ℕ} (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) {K k : ℕ} (hk : k ≤ K)
    {y : Vec d} (hy : y ≠ 0) (hε : 0 < ε) (ha₀ : 1 < a₀ * ‖y‖ ^ 2) :
    (sampleLaw d K).real {ω : Fin K → MatV d × MatV d |
        quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y ≤ 1 - a₀ * ‖y‖ ^ 2}
      ≤ 8 * tailG ((a₀ - 1 / ‖y‖ ^ 2) / (ε * Real.sqrt k)) := by
  set W : MatV d := (‖y‖ ^ 2)⁻¹ • tensorV y with hWdef
  have hyn : (‖y‖ ^ 2) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hynpos : 0 < ‖y‖ ^ 2 := by positivity
  have hW : ‖W‖ ≤ 1 := by
    rw [hWdef, norm_smul, Real.norm_of_nonneg (by positivity), norm_tensorV,
      inv_mul_cancel₀ hyn]
  have hrnn : 0 < (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2 := div_pos (by linarith) hynpos
  have hsub : {ω : Fin K → MatV d × MatV d |
        quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y ≤ 1 - a₀ * ‖y‖ ^ 2}
      ⊆ {ω : Fin K → MatV d × MatV d |
          (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2 ≤ |∑ j ∈ Finset.univ.filter
            (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W|} := by
    rintro ω hle
    simp only [Set.mem_setOf_eq] at hle ⊢
    have hsum := quadFormV_state_sub (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K) hk ω y
    rw [hsum] at hle
    have hkey : (a₀ * ‖y‖ ^ 2 - 1) ≤ -(∑ j ∈ Finset.univ.filter
        (fun j : Fin K => (j : ℕ) < k),
          ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y)) := by linarith
    have hneg := hkey.trans (neg_le_abs _)
    have hscale : (∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W)
        = (‖y‖ ^ 2)⁻¹ * ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hWdef, real_inner_smul_right]
      ring
    have habs : |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) W|
        = (‖y‖ ^ 2)⁻¹ * |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
            ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV y)| := by
      rw [hscale, abs_mul, abs_of_nonneg (by positivity)]
    rw [habs, show (a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2
        = (‖y‖ ^ 2)⁻¹ * (a₀ * ‖y‖ ^ 2 - 1) from by rw [div_eq_inv_mul, mul_comm]]
    exact mul_le_mul_of_nonneg_left hneg (by positivity)
  refine le_trans (MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)) ?_
  have hmain := maximal_tail_incr_k (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K) (k := k) hk
    (measurable_projL R BoxL) (fun A => good_projL R BoxL A) W hW hε hrnn
  refine le_trans hmain ?_
  have hexp : ((a₀ * ‖y‖ ^ 2 - 1) / ‖y‖ ^ 2) / (ε * Real.sqrt k)
      = (a₀ - 1 / ‖y‖ ^ 2) / (ε * Real.sqrt k) := by
    congr 1
    field_simp
  rw [hexp]

end

end Submission.ContactSharp
