import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.LatRiemann.farCellsBound
import Submission.Work.BoseRowsFS.LatRiemann.nearCellsBound
import Submission.Work.BoseRowsFS.LatRiemann.radialDecay4
import Submission.Work.BoseRowsFS.LatRiemann.radialNear2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.lattice_riemann_core`

The lattice-versus-continuum Riemann comparison for the kernel quotient that the
honest gate's integral row (`Work.BoseRowsFS.RowIntOne`, FS §11
`lem:EstimateIntegral`) needs: the integral `∫ Φ(p)/‖p‖² dp` over `ℝ³` is
approximated by the Riemann sum over the lattice `h·ℤ³` cut at `2Λ`, with an
error `O((h + (1+Λ)^{-3})(A+B)(1+C4))`.

The proof decomposes the difference over the *half-open* cells `hbox h m`
(`Submission/Work/BoseRowsFS/LatRiemann/Geom.lean`), which are pairwise
disjoint, and estimates

* the complement of the union of cells (where `‖p‖ ≳ Λ`, `p ∈ ⋃ cells` or `p`
  is in the central cell) — `UcBound`, using the radial bounds `radialDecay4`,
  `radialNear2`;
* the far cells `2√3 h ≤ ‖latPt h m‖` — `farCellsBound` (first-order difference
  of `Φ` against the Lipschitz row, and the second-order expansion of
  `1/‖p‖²`, whose linear term integrates to zero on a centred cell);
* the near cells `‖zvec m‖ < 2√3` — `nearCellsBound` (there are at most `343`
  of them and they lie in a ball of radius `≲ h`).

Everything is elementary; all constants are loose.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)



/-- `Φ` is continuous: the Lipschitz bound with the (bounded) weights gives
`|Φ p - Φ q| ≤ 2B‖p-q‖`. -/
lemma phi_continuous {B : ℝ} (hB : 0 ≤ B) {Φ : ℝ³ → ℝ}
    (hlip : ∀ p q, |Φ p - Φ q| ≤ B * ‖p - q‖ * (1/(1+‖p‖)^2 + 1/(1+‖q‖)^2)) :
    Continuous Φ := by
  have hd : ∀ p q : ℝ³, dist (Φ p) (Φ q) ≤ (2 * B) * dist p q := by
    intro p q
    rw [Real.dist_eq, dist_eq_norm]
    have h1 : 1/(1+‖p‖)^2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [norm_nonneg p]
    have h2 : 1/(1+‖q‖)^2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [norm_nonneg q]
    have hsum : 1/(1+‖p‖)^2 + 1/(1+‖q‖)^2 ≤ 2 := by linarith
    calc |Φ p - Φ q| ≤ B * ‖p - q‖ * (1/(1+‖p‖)^2 + 1/(1+‖q‖)^2) := hlip p q
      _ ≤ B * ‖p - q‖ * 2 := mul_le_mul_of_nonneg_left hsum (mul_nonneg hB (norm_nonneg _))
      _ = 2 * B * ‖p - q‖ := by ring
  rw [Metric.continuous_iff]
  intro p ε hε
  have hden : (0:ℝ) < 2 * B + 1 := by linarith
  refine ⟨ε / (2 * B + 1), div_pos hε hden, fun q hq => ?_⟩
  have h2 : (2 * B) * dist q p ≤ (2 * B) * (ε / (2 * B + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hq) (by linarith)
  have h3 : (2 * B) * (ε / (2 * B + 1)) < ε := by
    have hmul : (2 * B) * (ε / (2 * B + 1)) = (2 * B / (2 * B + 1)) * ε := by
      rw [← mul_div_assoc, div_mul_eq_mul_div]
    rw [hmul]
    have h4 : 2 * B / (2 * B + 1) < 1 := by rw [div_lt_one hden]; linarith
    simpa using mul_lt_mul_of_pos_right h4 hε
  linarith [hd q p, h2, h3]

/-- Pointwise domination of `Φ p/‖p‖²` by the radial majorant. -/
lemma norm_div_sq_le {A : ℝ} {Φ : ℝ³ → ℝ} (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4) (p : ℝ³) :
    ‖Φ p / ‖p‖ ^ 2‖ ≤ A * (1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2)) := by
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖ ^ 2)]
  have h := hΦ p
  have hbridge : A / (1 + ‖p‖) ^ 4 / ‖p‖ ^ 2 = A * (1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2)) := by
    rw [div_div, div_eq_mul_inv, div_eq_mul_inv, one_mul]
  rw [← hbridge]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- `p ↦ Φ p / ‖p‖²` is integrable. -/
lemma integrable_div_sq {A : ℝ} (hA : 0 ≤ A) {Φ : ℝ³ → ℝ}
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (hcont : Continuous Φ) :
    Integrable (fun p : ℝ³ => Φ p / ‖p‖ ^ 2) := by
  have hmaj : Integrable (fun p : ℝ³ => A * (1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2))) := by
    have h0 := (radialDecay4 0 le_rfl).1
    have heq' : (fun p : ℝ³ => A * (1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2)))
        = (fun p : ℝ³ => A * (if (0:ℝ) ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0)) := by
      ext p
      rw [if_pos (norm_nonneg p)]
    rw [heq']
    exact h0.const_mul A
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => Φ p / ‖p‖ ^ 2) volume :=
    ((hcont.measurable).div (measurable_norm.pow_const 2)).aestronglyMeasurable
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards with p
  exact norm_div_sq_le hΦ p

/-- The elementary inequality `1/((1+‖p‖)^4 ‖p‖^2) ≤ 1/‖p‖^2`. -/
lemma inv_pow4_mul_le_inv_sq (p : ℝ³) :
    1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) ≤ 1 / ‖p‖ ^ 2 := by
  rcases eq_or_lt_of_le (norm_nonneg p) with h | h
  · rw [← h]; simp
  · refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : (1:ℝ) ≤ (1 + ‖p‖) ^ 2 := by nlinarith [norm_nonneg p]
    have h2 : (1:ℝ) ≤ (1 + ‖p‖) ^ 4 := by
      have hXn : (0:ℝ) ≤ (1 + ‖p‖) ^ 2 := by positivity
      nlinarith [h1, hXn, sq_nonneg ((1 + ‖p‖) ^ 2 - 1)]
    nlinarith [h2, sq_nonneg ‖p‖]

/-- **The contribution of the complement of the union of cells.** -/
lemma UcBound {h Λ A : ℝ} (hh : 0 < h) (hΛ : 0 < Λ) (hΛh : h * Real.sqrt 3 ≤ Λ)
    (hA : 0 ≤ A) {Φ : ℝ³ → ℝ} (hcont : Continuous Φ)
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (K : Finset (Fin 3 → ℤ))
    (hKmem : ∀ m, m ∈ K ↔ (m ≠ 0 ∧ ‖Work.BoseRowsFS.latPt h m‖ < 2 * Λ)) :
    ‖∫ p in (⋃ m ∈ K, hbox h m)ᶜ, Φ p / ‖p‖ ^ 2‖
      ≤ A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2)) := by
  let F : ℝ³ → ℝ := fun p => Φ p / ‖p‖ ^ 2
  change ‖∫ p in (⋃ m ∈ K, hbox h m)ᶜ, F p‖
      ≤ A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2))
  have hUmeas : MeasurableSet (⋃ m ∈ K, hbox h m) :=
    Finset.measurableSet_biUnion K (fun m _ => measurableSet_hbox h m)
  have hFint : Integrable F := integrable_div_sq hA hΦ hcont
  have hFbd : ∀ p, ‖F p‖ ≤ A * (1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2)) := fun p => norm_div_sq_le hΦ p
  let g1 : ℝ³ → ℝ := fun p => if Λ ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0
  let g2 : ℝ³ → ℝ := fun p => if ‖p‖ ≤ h * Real.sqrt 3 / 2 then 1 / ‖p‖ ^ 2 else 0
  have hg1int : Integrable g1 := (radialDecay4 Λ (le_of_lt hΛ)).1
  have hg2int : Integrable g2 := (radialNear2 (h * Real.sqrt 3 / 2) (by positivity)).1
  have hpt : ∀ p, (⋃ m ∈ K, hbox h m)ᶜ.indicator (fun p => ‖F p‖) p ≤ A * g1 p + A * g2 p := by
    intro p
    by_cases hp : p ∈ (⋃ m ∈ K, hbox h m)ᶜ
    · rw [Set.indicator_of_mem hp]
      have hpU : p ∉ ⋃ m ∈ K, hbox h m := by simpa using hp
      have hpm : p ∈ hbox h (rnd h p) := mem_hbox_rnd hh p
      have hmK : rnd h p ∉ K := fun hm => hpU (Set.mem_biUnion hm hpm)
      have hb := hFbd p
      by_cases hΛle : Λ ≤ ‖p‖
      · have hg1v : g1 p = 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) := by
          simp only [g1, if_pos hΛle]
        have h2 : 0 ≤ A * g2 p := by
          simp only [g2]
          by_cases h : ‖p‖ ≤ h * Real.sqrt 3 / 2
          · rw [if_pos h]; positivity
          · rw [if_neg h]; positivity
        rw [hg1v]
        linarith
      · push_neg at hΛle
        have hm0 : rnd h p = 0 := by
          by_contra hne
          have hk : ‖Work.BoseRowsFS.latPt h (rnd h p)‖ < 2 * Λ := by
            by_contra hcon
            push_neg at hcon
            have hnorm : ‖Work.BoseRowsFS.latPt h (rnd h p)‖ ≤ ‖p‖ + ‖p - Work.BoseRowsFS.latPt h (rnd h p)‖ := by
              have := norm_sub_le p (p - Work.BoseRowsFS.latPt h (rnd h p))
              simpa using this
            have h2 : ‖p - Work.BoseRowsFS.latPt h (rnd h p)‖ ≤ h * Real.sqrt 3 / 2 :=
              norm_sub_latPt_le hh hpm
            linarith
          exact hmK ((hKmem (rnd h p)).mpr ⟨hne, hk⟩)
        have hpm0 : p ∈ hbox h 0 := by rw [← hm0]; exact hpm
        have hle : ‖p‖ ≤ h * Real.sqrt 3 / 2 := hbox_zero_subset hh hpm0
        have hg2v : g2 p = 1 / ‖p‖ ^ 2 := by simp only [g2, if_pos hle]
        have h1 : 0 ≤ A * g1 p := by
          simp only [g1]
          by_cases h : Λ ≤ ‖p‖
          · rw [if_pos h]; positivity
          · rw [if_neg h]; positivity
        have hle2 : 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) ≤ 1 / ‖p‖ ^ 2 := inv_pow4_mul_le_inv_sq p
        have := mul_le_mul_of_nonneg_left hle2 hA
        rw [hg2v]
        linarith
    · rw [Set.indicator_of_notMem hp]
      have h1 : 0 ≤ A * g1 p := by
        simp only [g1]
        by_cases h : Λ ≤ ‖p‖
        · rw [if_pos h]; positivity
        · rw [if_neg h]; positivity
      have h2 : 0 ≤ A * g2 p := by
        simp only [g2]
        by_cases h : ‖p‖ ≤ h * Real.sqrt 3 / 2
        · rw [if_pos h]; positivity
        · rw [if_neg h]; positivity
      linarith
  have hmajint : Integrable (fun p => A * g1 p + A * g2 p) :=
    (hg1int.const_mul A).add (hg2int.const_mul A)
  have hindint : Integrable ((⋃ m ∈ K, hbox h m)ᶜ.indicator (fun p => ‖F p‖)) :=
    Integrable.indicator hFint.norm hUmeas.compl
  calc ‖∫ p in (⋃ m ∈ K, hbox h m)ᶜ, F p‖
      ≤ ∫ p in (⋃ m ∈ K, hbox h m)ᶜ, ‖F p‖ := norm_integral_le_integral_norm _
    _ = ∫ p, (⋃ m ∈ K, hbox h m)ᶜ.indicator (fun p => ‖F p‖) p :=
        (integral_indicator hUmeas.compl).symm
    _ ≤ ∫ p, (A * g1 p + A * g2 p) := integral_mono hindint hmajint (fun p => hpt p)
    _ = A * (∫ p, g1 p) + A * (∫ p, g2 p) := by
        rw [integral_add (hg1int.const_mul A) (hg2int.const_mul A), integral_const_mul,
          integral_const_mul]
    _ ≤ A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2)) := by
        have h1 : (∫ p, g1 p) ≤ 4 * Real.pi / (1 + Λ) ^ 3 := (radialDecay4 Λ (le_of_lt hΛ)).2
        have h2 : (∫ p, g2 p) ≤ 4 * Real.pi * (h * Real.sqrt 3 / 2) :=
          (radialNear2 (h * Real.sqrt 3 / 2) (by positivity)).2
        have hA1 := mul_le_mul_of_nonneg_left h1 hA
        have hA2 := mul_le_mul_of_nonneg_left h2 hA
        linarith

theorem lattice_riemann_core
    {h Λ A B C4 : ℝ} (hh : 0 < h) (hΛ : 0 < Λ) (hΛh : h * Real.sqrt 3 ≤ Λ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC4 : 0 ≤ C4)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (hlip : ∀ p q, |Φ p - Φ q|
      ≤ B * ‖p - q‖ * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖q‖) ^ 2))
    (hC4b : ∀ S : Finset (Fin 3 → ℤ), (∀ m ∈ S, m ≠ 0) →
      ∑ m ∈ S, (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ ≤ C4)
    (K : Finset (Fin 3 → ℤ))
    (hKmem : ∀ m, m ∈ K ↔ (m ≠ 0 ∧ ‖Work.BoseRowsFS.latPt h m‖ < 2 * Λ)) :
    |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
      - ∑ m ∈ K, h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ 1000 * (1 + C4) * (A + B) * (h + 1 / (1 + Λ) ^ 3) := by
  let F : ℝ³ → ℝ := fun p => Φ p / ‖p‖ ^ 2
  let U : Set ℝ³ := ⋃ m ∈ K, hbox h m
  let Kf : Finset (Fin 3 → ℤ) :=
    K.filter fun m => 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖
  let Kn : Finset (Fin 3 → ℤ) :=
    K.filter fun m => ¬ (2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)
  have hΦcont : Continuous Φ := phi_continuous hB hlip
  have hFint : Integrable F := integrable_div_sq hA hΦ hΦcont
  have hvolne : ∀ m : Fin 3 → ℤ, volume (hbox h m) ≠ ⊤ := by
    intro m
    rw [volume_hbox]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hUmeas : MeasurableSet U := by
    simp only [U]
    exact Finset.measurableSet_biUnion K (fun m _ => measurableSet_hbox h m)
  have hdisj : Set.Pairwise (↑K : Set (Fin 3 → ℤ)) (fun m m' => Disjoint (hbox h m) (hbox h m')) :=
    fun m _ m' _ hne => disjoint_hbox hh hne
  have hUint : (∫ p in U, F p) = ∑ m ∈ K, ∫ p in hbox h m, F p := by
    simp only [U]
    exact integral_biUnion_finset K (fun m _ => measurableSet_hbox h m) hdisj
      (fun m _ => hFint.integrableOn)
  have hsplit : (∫ p : ℝ³, F p) = (∫ p in U, F p) + ∫ p in Uᶜ, F p :=
    (integral_add_compl hUmeas hFint).symm
  have hconst : ∀ m ∈ K, (∫ p in hbox h m, F (Work.BoseRowsFS.latPt h m))
      = h ^ 3 * F (Work.BoseRowsFS.latPt h m) := by
    intro m _
    rw [setIntegral_const, real_volume_hbox (le_of_lt hh) m, smul_eq_mul]
  have hE : (∫ p : ℝ³, F p) - ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m)
      = (∫ p in Uᶜ, F p)
        + ∑ m ∈ K, ((∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)) := by
    rw [hsplit, hUint]
    rw [show ∑ m ∈ K, ((∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m))
        = (∑ m ∈ K, ∫ p in hbox h m, F p)
          - ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m) from
        Finset.sum_sub_distrib (s := K) (f := fun m => ∫ p in hbox h m, F p)
          (g := fun m => h ^ 3 * F (Work.BoseRowsFS.latPt h m))]
    ring
  have htri : |(∫ p : ℝ³, F p) - ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
      ≤ ‖∫ p in Uᶜ, F p‖
        + ∑ m ∈ K, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)| := by
    have h1 : |(∫ p : ℝ³, F p) - ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
        ≤ |∫ p in Uᶜ, F p|
          + |∑ m ∈ K, ((∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m))| := by
      rw [hE]
      exact abs_add_le _ _
    have h2 : |∑ m ∈ K, ((∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m))|
        ≤ ∑ m ∈ K, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h3 : |∫ p in Uᶜ, F p| ≤ ‖∫ p in Uᶜ, F p‖ := by rw [Real.norm_eq_abs]
    linarith
  have hring : ∀ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m)
      = h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2 := by
    intro m _
    simp only [F]
    ring
  have hKsplit : ∑ m ∈ K, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
      = ∑ m ∈ Kf, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
        + ∑ m ∈ Kn, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)| := by
    rw [← Finset.sum_filter_add_sum_filter_not K
      (fun m => 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)
      (fun m => |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|)]
  have hfar : ∑ m ∈ Kf, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
      ≤ 200 * B * h + 16 * C4 * A * h := by
    have h1 : ∀ m ∈ Kf, 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖ := by
      intro m hm
      simp only [Kf, Finset.mem_filter] at hm
      exact hm.2
    have h2 : ∀ m ∈ Kf, m ∈ K := by
      intro m hm
      simp only [Kf, Finset.mem_filter] at hm
      exact hm.1
    have hcongr : ∑ m ∈ Kf, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
        = ∑ m ∈ Kf, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
            - h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2| := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hring m (h2 m hm)]
    rw [hcongr]
    exact farCellsBound hh hA hB hC4 hΦcont hΦ hlip Kf h1 hC4b
  have hnear : ∑ m ∈ Kn, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
      ≤ 500 * A * h := by
    have h1 : ∀ m ∈ Kn, m ≠ 0 ∧ ¬ (2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖) := by
      intro m hm
      simp only [Kn, Finset.mem_filter] at hm
      exact ⟨((hKmem m).mp hm.1).1, hm.2⟩
    have h2 : ∀ m ∈ Kn, m ∈ K := by
      intro m hm
      simp only [Kn, Finset.mem_filter] at hm
      exact hm.1
    have hcongr : ∑ m ∈ Kn, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
        = ∑ m ∈ Kn, |(∫ p in hbox h m, Φ p / ‖p‖ ^ 2)
            - h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2| := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hring m (h2 m hm)]
    rw [hcongr]
    exact nearCellsBound hh hA hΦcont hΦ Kn h1
  have hUcb := UcBound hh hΛ hΛh hA hΦcont hΦ K hKmem
  have harith : A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2))
        + (200 * B * h + 16 * C4 * A * h) + 500 * A * h
      ≤ 1000 * (1 + C4) * (A + B) * (h + 1 / (1 + Λ) ^ 3) := by
    have ht : (0:ℝ) ≤ 1 / (1 + Λ) ^ 3 := by positivity
    have hh0 : (0:ℝ) ≤ h := le_of_lt hh
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h1 : 4 * A * Real.pi ≤ 1000 * (1 + C4) * (A + B) := by
      nlinarith [hA, hB, hC4, Real.pi_pos, Real.pi_lt_four]
    have hsp : 2 * Real.sqrt 3 * Real.pi ≤ 500 := by
      have hp3 : Real.sqrt 3 * Real.pi ≤ 2 * 4 :=
        mul_le_mul hs3 (le_of_lt Real.pi_lt_four) (le_of_lt Real.pi_pos) (by norm_num)
      linarith
    have h2 : 2 * Real.sqrt 3 * Real.pi * A + 200 * B + 16 * C4 * A + 500 * A
        ≤ 1000 * (1 + C4) * (A + B) := by
      nlinarith [hsp, hA, hB, hC4]
    have ha := mul_le_mul_of_nonneg_right h1 ht
    have hb := mul_le_mul_of_nonneg_right h2 hh0
    have hkey : A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2))
          + (200 * B * h + 16 * C4 * A * h) + 500 * A * h
        = 4 * A * Real.pi * (1 / (1 + Λ) ^ 3)
          + (2 * Real.sqrt 3 * Real.pi * A + 200 * B + 16 * C4 * A + 500 * A) * h := by
      ring
    have hR : 1000 * (1 + C4) * (A + B) * (h + 1 / (1 + Λ) ^ 3)
        = 1000 * (1 + C4) * (A + B) * (1 / (1 + Λ) ^ 3)
          + 1000 * (1 + C4) * (A + B) * h := by
      ring
    rw [hkey, hR]
    linarith
  have htot : |(∫ p : ℝ³, F p) - ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
      ≤ 1000 * (1 + C4) * (A + B) * (h + 1 / (1 + Λ) ^ 3) := by
    have h3 : ‖∫ p in Uᶜ, F p‖
        ≤ A * (4 * Real.pi / (1 + Λ) ^ 3) + A * (4 * Real.pi * (h * Real.sqrt 3 / 2)) := by
      simpa only [U, F] using hUcb
    have h4 : ∑ m ∈ K, |(∫ p in hbox h m, F p) - h ^ 3 * F (Work.BoseRowsFS.latPt h m)|
        ≤ (200 * B * h + 16 * C4 * A * h) + 500 * A * h := by
      rw [hKsplit]
      linarith
    linarith [htri, h3, h4, harith]
  have hbridge : (∑ m ∈ K, h ^ 3 * Φ (Work.BoseRowsFS.latPt h m)
        / ‖Work.BoseRowsFS.latPt h m‖ ^ 2)
      = ∑ m ∈ K, h ^ 3 * F (Work.BoseRowsFS.latPt h m) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [F]
    ring
  rw [hbridge]
  exact htot

end Work.BoseRowsFS.LatRiemann
