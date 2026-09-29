import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.fstats
import Submission.Work.Holonomy3.sum_abs_mul_sub_le
import Submission.Work.Holonomy3.sum_sum_fiber

/-!
# The exact expectation of `Σ_{a,b} max(v_a(t_a), v_b(t_b))` (STEP 5 of the holonomy bound)

We prove that the expectation over `t : Fin d → ℝ` (uniform on `[0,1]ᵈ`) of
`Σ_{a,b} max(g_{k a}(t a), g_{k b}(t b))` is `d² · rearrInt w φ + O((l+1)² d G₀)`, where
`g_p = circleLog (φ p)`, `n p = #{a | k a = p}`, `w` is within `2/d` of `n p/d`, and
`|g_p| ≤ G₀` on `[0,1]`.

The proof is the paper's STEP 5: Fubini splits the expectation into the double integrals
`X p q = ∬ max(g_p, g_q)` (off-diagonal, `a ≠ b`) and the single integrals `Y p = ∫ g_p`
(diagonal, `a = b`); the off-diagonal part is grouped by the fibres of `k`, which produces the
`n p · n q` weights compared with the `d w p · d w q` of `d² · rearrInt`; the `(l+1)² d G₀` slack
absorbs the count discrepancy `|n p - d w p| ≤ 2` and the `2d G₀` diagonal correction.
-/

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- `volume.restrict (Icc 0 1)` is a probability measure. -/
instance instIsProbabilityMeasureRestrictIcc01 :
    IsProbabilityMeasure (volume.restrict (Icc (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩

/-- Abbreviation for the uniform measure on `[0,1]`. -/
local notation "ν₁" => MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)

/-! ## Measure-theoretic lemmas -/

/-- The pushforward of a product of probability measures under a pair of evaluations is the
product measure. -/
lemma map_evalPair_eq_prod {d : ℕ} (μ : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {a b : Fin d} (hab : a ≠ b) :
    (Measure.pi μ).map (fun t : Fin d → ℝ => (t a, t b)) = (μ a).prod (μ b) := by
  rw [eq_comm]
  refine Measure.prod_eq (fun s t hs ht => ?_)
  rw [Measure.map_apply (by fun_prop) (hs.prod ht)]
  have hpre : (fun t : Fin d → ℝ => (t a, t b)) ⁻¹' (s ×ˢ t)
      = Set.pi Set.univ (fun i => if i = a then s else if i = b then t else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hia : i = a
      · rw [if_pos hia]; rwa [hia]
      · by_cases hib : i = b
        · rw [if_neg hia, if_pos hib]; rwa [hib]
        · rw [if_neg hia, if_neg hib]; exact Set.mem_univ _
    · intro h
      exact ⟨by have := h a; rw [if_pos rfl] at this; exact this,
             by have := h b; rw [if_neg (Ne.symm hab), if_pos rfl] at this; exact this⟩
  rw [hpre, Measure.pi_pi]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin d))
        (fun i => μ i (if i = a then s else if i = b then t else Set.univ)) (Finset.mem_univ a)]
  have hFb : b ∈ (Finset.univ : Finset (Fin d)).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  rw [← Finset.mul_prod_erase ((Finset.univ : Finset (Fin d)).erase a)
        (fun i => μ i (if i = a then s else if i = b then t else Set.univ)) hFb]
  have h1 : μ a (if (a : Fin d) = a then s else if a = b then t else Set.univ) = μ a s := by
    rw [if_pos rfl]
  have h2 : μ b (if (b : Fin d) = a then s else if b = b then t else Set.univ) = μ b t := by
    rw [if_neg (Ne.symm hab), if_pos rfl]
  rw [h1, h2]
  have h3 : ∏ x ∈ ((Finset.univ : Finset (Fin d)).erase a).erase b,
      μ x (if x = a then s else if x = b then t else Set.univ) = 1 := by
    rw [Finset.prod_eq_one]
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxb, hxa, -⟩ := hx
    rw [if_neg hxa, if_neg hxb, measure_univ]
  rw [h3, mul_one]

/-- Fubini for a pair of distinct coordinates of a product of probability measures (here all
factors are `volume.restrict (Icc 0 1)`, so that `ContinuousOn` hypotheses give the needed
measurability and integrability). -/
lemma integral_pair_eval {d : ℕ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    {a b : Fin d} (hab : a ≠ b) :
    ∫ t : Fin d → ℝ, max (f (t a)) (g (t b)) ∂(Measure.pi (fun _ : Fin d => ν₁))
      = ∫ s, ∫ u, max (f s) (g u) ∂ν₁ ∂ν₁ := by
  have hmap := map_evalPair_eq_prod (fun _ : Fin d => (ν₁ : Measure ℝ)) hab
  let F : ℝ × ℝ → ℝ := fun p => max (f p.1) (g p.2)
  have hbox : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hcontF : ContinuousOn F (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    refine ContinuousOn.sup ?_ ?_
    · exact hf.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · exact hg.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hAES : AEStronglyMeasurable F ((ν₁ : Measure ℝ).prod ν₁) := by
    rw [Measure.prod_restrict]
    exact hcontF.aestronglyMeasurable hbox
  have hInt : Integrable F ((ν₁ : Measure ℝ).prod ν₁) := by
    rw [Measure.prod_restrict]
    exact (hcontF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).integrable
  have hAES' : AEStronglyMeasurable F
      ((Measure.pi (fun _ : Fin d => ν₁)).map (fun t : Fin d → ℝ => (t a, t b))) := by
    rw [hmap]; exact hAES
  rw [show (fun t : Fin d → ℝ => max (f (t a)) (g (t b))) = fun t => F (t a, t b) from rfl]
  rw [← MeasureTheory.integral_map (φ := fun t : Fin d → ℝ => (t a, t b))
        ((measurable_pi_apply a).prodMk (measurable_pi_apply b) |>.aemeasurable) hAES', hmap]
  simpa [F] using MeasureTheory.integral_prod F hInt

/-- Fubini for a single coordinate of a product of probability measures. -/
lemma integral_single_eval {d : ℕ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (a : Fin d) :
    ∫ t : Fin d → ℝ, f (t a) ∂(Measure.pi (fun _ : Fin d => ν₁)) = ∫ x, f x ∂ν₁ :=
  MeasureTheory.integral_comp_eval ((hf.aemeasurable measurableSet_Icc).aestronglyMeasurable)

/-- The interval integral over `0..1` is the integral against `volume.restrict (Icc 0 1)`. -/
lemma intervalIntegral_eq_integral_Icc (f : ℝ → ℝ) :
    (∫ s in (0:ℝ)..1, f s) = ∫ s, f s ∂ν₁ := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- `|max a b| ≤ C` when `|a| ≤ C` and `|b| ≤ C`. -/
lemma abs_max_le {a b C : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ C) : |max a b| ≤ C := by
  rw [abs_le] at *
  exact ⟨le_trans ha.1 (le_max_left _ _), max_le ha.2 hb.2⟩

/-- A single integral of a function bounded by `C` on `[0,1]` is bounded by `C`. -/
lemma abs_integral_le_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ t ∈ Icc (0:ℝ) 1, |f t| ≤ C) : |∫ x, f x ∂ν₁| ≤ C := by
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := ν₁) (f := f) (C := C) ?_
  · simpa [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc] using h
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
    simpa [Real.norm_eq_abs] using hC x hx

/-- The double integral of `max (f s) (g u)` over `[0,1]²` is bounded by `C`. -/
lemma abs_pair_integral_le_of_bound {f g : ℝ → ℝ} {C : ℝ}
    (hC : ∀ t ∈ Icc (0:ℝ) 1, |f t| ≤ C) (hC' : ∀ t ∈ Icc (0:ℝ) 1, |g t| ≤ C) :
    |∫ s, ∫ u, max (f s) (g u) ∂ν₁ ∂ν₁| ≤ C := by
  refine abs_integral_le_of_bound (f := fun s => ∫ u, max (f s) (g u) ∂ν₁) ?_
  intro s hs
  exact abs_integral_le_of_bound (f := fun u => max (f s) (g u))
    (fun u hu => abs_max_le (hC s hs) (hC' u hu))

/-- Coordinates of the product of uniform measures on `[0,1]` lie in `[0,1]` almost everywhere. -/
lemma ae_eval_mem_Icc {d : ℕ} (a : Fin d) :
    ∀ᵐ t ∂(Measure.pi (fun _ : Fin d => ν₁)), t a ∈ Icc (0:ℝ) 1 := by
  have hmap : Measure.map (Function.eval a) (Measure.pi (fun _ : Fin d => ν₁)) = ν₁ :=
    (MeasureTheory.measurePreserving_eval (fun _ : Fin d => ν₁) a).map_eq
  have hμae : ∀ᵐ x ∂ν₁, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have h' : ∀ᵐ y ∂(Measure.map (Function.eval a) (Measure.pi (fun _ : Fin d => ν₁))),
      y ∈ Icc (0:ℝ) 1 := by rw [hmap]; exact hμae
  exact (MeasureTheory.ae_map_iff (measurable_pi_apply a).aemeasurable measurableSet_Icc).1 h'

/-- `t ↦ max (f (t a)) (g (t b))` is a.e. strongly measurable for the product measure. -/
lemma ae_stronglyMeasurable_max_comp_eval {d : ℕ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) (a b : Fin d) :
    AEStronglyMeasurable (fun t : Fin d → ℝ => max (f (t a)) (g (t b)))
      (Measure.pi (fun _ : Fin d => ν₁)) := by
  have aux : ∀ {h : ℝ → ℝ}, ContinuousOn h (Icc (0:ℝ) 1) → ∀ c : Fin d,
      AEMeasurable (fun t : Fin d → ℝ => h (t c)) (Measure.pi (fun _ : Fin d => ν₁)) := by
    intro h hh c
    have hmap : Measure.map (Function.eval c) (Measure.pi (fun _ : Fin d => ν₁)) = ν₁ :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => ν₁) c).map_eq
    have h1 : AEMeasurable h (Measure.map (Function.eval c) (Measure.pi (fun _ : Fin d => ν₁))) := by
      rw [hmap]; exact hh.aemeasurable measurableSet_Icc
    exact h1.comp_aemeasurable (measurable_pi_apply c).aemeasurable
  exact ((aux hf a).max (aux hg b)).aestronglyMeasurable

/-! ## The main theorem -/

theorem expectation_max_blocked {l d : ℕ} (hd : 0 < d) (w : Fin (l + 1) → ℝ)
    (φ : Fin (l + 1) → ℂ → ℂ) (k : Fin d → Fin (l + 1)) {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hcont : ∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1))
    (hG : ∀ p t, t ∈ Set.Icc 0 1 → |Submission.CDTPlan.circleLog (φ p) t| ≤ G₀)
    (hc : ∀ p, |((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) / (d : ℝ) - w p|
      ≤ 2 / (d : ℝ)) :
    ∫ t : Fin d → ℝ,
        (∑ a, ∑ b, max (Submission.CDTPlan.circleLog (φ (k a)) (t a))
          (Submission.CDTPlan.circleLog (φ (k b)) (t b)))
        ∂(MeasureTheory.Measure.pi (fun _ : Fin d =>
            MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)))
      ≤ (d : ℝ) ^ 2 * Submission.CDTPlan.rearrInt w φ
        + (8 * ((l + 1 : ℝ) ^ 2) * (d : ℝ) + 8 * ((l + 1 : ℝ) ^ 2)) * G₀ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  set n : Fin (l + 1) → ℕ := fun p => (Finset.univ.filter (fun a : Fin d => k a = p)).card with hn
  set X : Fin (l + 1) → Fin (l + 1) → ℝ := fun p q =>
      ∫ s, ∫ u, max (circleLog (φ p) s) (circleLog (φ q) u) ∂ν₁ ∂ν₁ with hX
  set Y : Fin (l + 1) → ℝ := fun p => ∫ s, circleLog (φ p) s ∂ν₁ with hY
  -- 0. integrability of the summands
  have hint : ∀ a b : Fin d, Integrable
      (fun t : Fin d → ℝ => max (circleLog (φ (k a)) (t a)) (circleLog (φ (k b)) (t b)))
      (Measure.pi (fun _ : Fin d => ν₁)) := by
    intro a b
    refine Integrable.of_bound ?_ G₀ ?_
    · exact ae_stronglyMeasurable_max_comp_eval (hcont (k a)) (hcont (k b)) a b
    · filter_upwards [ae_eval_mem_Icc a, ae_eval_mem_Icc b] with t ha hb
      rw [Real.norm_eq_abs]
      exact abs_max_le (hG (k a) (t a) ha) (hG (k b) (t b) hb)
  -- 1. the integral of the sum is the sum of the integrals
  have hLHS : (∫ t : Fin d → ℝ, (∑ a, ∑ b, max (circleLog (φ (k a)) (t a))
        (circleLog (φ (k b)) (t b))) ∂(Measure.pi (fun _ : Fin d => ν₁)))
      = ∑ a : Fin d, ∑ b : Fin d, ∫ t : Fin d → ℝ,
          max (circleLog (φ (k a)) (t a)) (circleLog (φ (k b)) (t b))
          ∂(Measure.pi (fun _ : Fin d => ν₁)) := by
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (f := fun a (t : Fin d → ℝ) => ∑ b, max (circleLog (φ (k a)) (t a))
        (circleLog (φ (k b)) (t b)))
      (fun a _ => MeasureTheory.integrable_finsetSum Finset.univ (fun b _ => hint a b))]
    exact Finset.sum_congr rfl (fun a _ => MeasureTheory.integral_finsetSum Finset.univ
      (f := fun b (t : Fin d → ℝ) => max (circleLog (φ (k a)) (t a))
        (circleLog (φ (k b)) (t b)))
      (fun b _ => hint a b))
  -- 2. each summand
  have hterm : ∀ a b : Fin d,
      (∫ t : Fin d → ℝ, max (circleLog (φ (k a)) (t a)) (circleLog (φ (k b)) (t b))
        ∂(Measure.pi (fun _ : Fin d => ν₁)))
      = X (k a) (k b) + (if a = b then Y (k a) - X (k a) (k a) else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have h1 : (∫ t : Fin d → ℝ, max (circleLog (φ (k a)) (t a)) (circleLog (φ (k a)) (t a))
            ∂(Measure.pi (fun _ : Fin d => ν₁))) = Y (k a) := by
        rw [show (fun t : Fin d → ℝ => max (circleLog (φ (k a)) (t a))
              (circleLog (φ (k a)) (t a)))
            = (fun t => circleLog (φ (k a)) (t a)) from by funext t; exact max_self _, hY]
        exact integral_single_eval (hcont (k a)) a
      rw [h1, if_pos rfl]
      ring
    · have h1 : (∫ t : Fin d → ℝ, max (circleLog (φ (k a)) (t a)) (circleLog (φ (k b)) (t b))
            ∂(Measure.pi (fun _ : Fin d => ν₁))) = X (k a) (k b) := by
        rw [hX]
        exact integral_pair_eval (hcont (k a)) (hcont (k b)) hab
      rw [h1, if_neg hab, add_zero]
  -- 3. split the double sum
  have hinner : ∀ a : Fin d, (∑ b : Fin d, (X (k a) (k b)
        + (if a = b then Y (k a) - X (k a) (k a) else 0)))
      = (∑ b : Fin d, X (k a) (k b)) + (Y (k a) - X (k a) (k a)) := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  have hsplit : (∑ a : Fin d, ∑ b : Fin d, (X (k a) (k b)
        + (if a = b then Y (k a) - X (k a) (k a) else 0)))
      = (∑ a : Fin d, ∑ b : Fin d, X (k a) (k b))
        + ∑ a : Fin d, (Y (k a) - X (k a) (k a)) := by
    simp only [hinner]
    rw [Finset.sum_add_distrib]
  -- 4. reindex the off-diagonal double sum by the fibres of `k`
  have hXsum : (∑ a : Fin d, ∑ b : Fin d, X (k a) (k b))
      = ∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (n p : ℝ) * (n q : ℝ) * X p q := by
    rw [sum_sum_fiber k X]
  have hYsum : (∑ a : Fin d, (Y (k a) - X (k a) (k a)))
      = ∑ p : Fin (l + 1), (n p : ℝ) * (Y p - X p p) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin d)) k
      (fun a => Y (k a) - X (k a) (k a))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have h1 : (∑ a ∈ Finset.univ.filter (fun a : Fin d => k a = p),
          (Y (k a) - X (k a) (k a)))
        = ∑ _a ∈ Finset.univ.filter (fun a : Fin d => k a = p), (Y p - X p p) := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [Finset.mem_filter] at ha
      rw [ha.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul, hn]
  -- 5. `rearrInt` in terms of `X`
  have hrearr : rearrInt w φ
      = ∑ p : Fin (l + 1), ∑ q : Fin (l + 1), w p * w q * X p q := by
    unfold rearrInt
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [hX]
    congr 1
    rw [intervalIntegral_eq_integral_Icc
      (fun s => ∫ u in (0:ℝ)..1, max (circleLog (φ p) s) (circleLog (φ q) u))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    exact intervalIntegral_eq_integral_Icc (fun u => max (circleLog (φ p) s) (circleLog (φ q) u))
  -- 6. bounds on `X` and `Y`
  have hXb : ∀ p q, |X p q| ≤ G₀ := by
    intro p q
    rw [hX]
    exact abs_pair_integral_le_of_bound (hG p) (hG q)
  have hYb : ∀ p, |Y p| ≤ G₀ := by
    intro p
    rw [hY]
    exact abs_integral_le_of_bound (hG p)
  -- 7. counting facts
  have hn_sum : ∑ p : Fin (l + 1), (n p : ℝ) = (d : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := k) (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin (l + 1)))) (fun a _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have h2 : ∑ p : Fin (l + 1), n p = d := by
      rw [h]
    rw [← h2, Nat.cast_sum]
  have hn_abs : ∀ p : Fin (l + 1), |(n p : ℝ) - (d : ℝ) * w p| ≤ 2 := by
    intro p
    have h := hc p
    have hstep := mul_le_mul_of_nonneg_right h hd0.le
    rw [div_mul_cancel₀ (2 : ℝ) hdne] at hstep
    have hx : (n p : ℝ) - (d : ℝ) * w p
        = (((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) / (d : ℝ) - w p)
            * (d : ℝ) := by
      change ((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) - (d : ℝ) * w p
          = (((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) / (d : ℝ) - w p) * (d : ℝ)
      rw [sub_mul, div_mul_cancel₀ _ hdne]
      ring
    calc |(n p : ℝ) - (d : ℝ) * w p|
        = |(((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) / (d : ℝ) - w p)
            * (d : ℝ)| := by rw [hx]
      _ = |((Finset.univ.filter (fun a : Fin d => k a = p)).card : ℝ) / (d : ℝ) - w p|
            * (d : ℝ) := by rw [abs_mul, abs_of_pos hd0]
      _ ≤ 2 := hstep
  -- 8. the difference of the two double sums
  have hbound1 : (∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (n p : ℝ) * (n q : ℝ) * X p q)
      - (∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (d : ℝ) * w p * ((d : ℝ) * w q) * X p q)
      ≤ (4 * (l + 1 : ℝ) * d + 4 * (l + 1 : ℝ) ^ 2) * G₀ := by
    have hdiff : (∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (n p : ℝ) * (n q : ℝ) * X p q)
        - (∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (d : ℝ) * w p * ((d : ℝ) * w q) * X p q)
        = ∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
            ((n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)) * X p q := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [hdiff]
    have hle : ∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
          ((n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)) * X p q
        ≤ ∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
            |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)| * G₀ := by
      refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
      calc ((n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)) * X p q
          ≤ |((n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)) * X p q| :=
            le_abs_self _
        _ = |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)| * |X p q| := abs_mul _ _
        _ ≤ |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)| * G₀ :=
            mul_le_mul_of_nonneg_left (hXb p q) (abs_nonneg _)
    have hfact : ∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
            |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)| * G₀
        = (∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
            |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)|) * G₀ := by
      simp only [← Finset.sum_mul]
    have hcount : ∑ p : Fin (l + 1), ∑ q : Fin (l + 1),
          |(n p : ℝ) * (n q : ℝ) - (d : ℝ) * w p * ((d : ℝ) * w q)|
        ≤ 4 * (l + 1 : ℝ) * d + 4 * (l + 1 : ℝ) ^ 2 := by
      have h := sum_abs_mul_sub_le (N := l + 1) (a := fun p => (d : ℝ) * w p)
        (b := fun p => (n p : ℝ)) (D := (d : ℝ))
        (fun p => Nat.cast_nonneg _) hn_sum hn_abs
      simpa using h
    refine le_trans hle ?_
    rw [hfact]
    exact mul_le_mul_of_nonneg_right hcount hG0
  -- 9. the diagonal correction
  have hbound2 : ∑ p : Fin (l + 1), (n p : ℝ) * (Y p - X p p) ≤ 2 * d * G₀ := by
    have h1 : ∑ p : Fin (l + 1), (n p : ℝ) * (Y p - X p p)
        ≤ ∑ p : Fin (l + 1), (n p : ℝ) * (2 * G₀) := by
      refine Finset.sum_le_sum (fun p _ => ?_)
      have hYp : Y p ≤ G₀ := (abs_le.mp (hYb p)).2
      have hXp : -G₀ ≤ X p p := (abs_le.mp (hXb p p)).1
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have h2 : ∑ p : Fin (l + 1), (n p : ℝ) * (2 * G₀) = 2 * d * G₀ := by
      rw [← Finset.sum_mul, hn_sum]; ring
    linarith
  -- 10. `d² · rearrInt` in terms of the double sum
  have hrearr2 : (d : ℝ) ^ 2 * rearrInt w φ
      = ∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (d : ℝ) * w p * ((d : ℝ) * w q) * X p q := by
    rw [hrearr, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  -- 11. final arithmetic
  have hmain : (∫ t : Fin d → ℝ, (∑ a, ∑ b, max (circleLog (φ (k a)) (t a))
        (circleLog (φ (k b)) (t b))) ∂(Measure.pi (fun _ : Fin d => ν₁)))
      = (∑ p : Fin (l + 1), ∑ q : Fin (l + 1), (n p : ℝ) * (n q : ℝ) * X p q)
        + ∑ p : Fin (l + 1), (n p : ℝ) * (Y p - X p p) := by
    rw [hLHS]
    rw [show (∑ a : Fin d, ∑ b : Fin d, ∫ t : Fin d → ℝ,
          max (circleLog (φ (k a)) (t a)) (circleLog (φ (k b)) (t b))
          ∂(Measure.pi (fun _ : Fin d => ν₁)))
        = ∑ a : Fin d, ∑ b : Fin d, (X (k a) (k b)
          + (if a = b then Y (k a) - X (k a) (k a) else 0)) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
    rw [hsplit, hXsum, hYsum]
  have hnum : 4 * (l + 1 : ℝ) * d + 4 * (l + 1 : ℝ) ^ 2 + 2 * d
      ≤ 8 * (l + 1 : ℝ) ^ 2 * d + 8 * (l + 1 : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (l + 1 : ℝ) := by
      have : (0:ℝ) ≤ l := Nat.cast_nonneg _; linarith
    have h2 : (l + 1 : ℝ) ≤ (l + 1 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((l + 1 : ℝ) - 1)]
    have h3 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  rw [hmain, hrearr2]
  have hCG : (4 * (l + 1 : ℝ) * d + 4 * (l + 1 : ℝ) ^ 2) * G₀ + 2 * d * G₀
      ≤ (8 * (l + 1 : ℝ) ^ 2 * d + 8 * (l + 1 : ℝ) ^ 2) * G₀ := by
    have := mul_le_mul_of_nonneg_right hnum hG0
    nlinarith [this]
  linarith [hbound1, hbound2, hCG]

end

end Work.Holonomy3
