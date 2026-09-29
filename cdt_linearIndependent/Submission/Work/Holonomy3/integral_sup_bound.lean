import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.pointwise_rearrangement_bound
import Submission.Work.Holonomy3.expectation_max_blocked
import Submission.Work.Holonomy3.integral_double_sum_le

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Set
open scoped BigOperators

noncomputable section

/-!
# The integral of the sup over the low-discrepancy box (Area H, the fine holonomy bound)

This module proves `Work.Holonomy3.integral_sup_bound`: the average over the torus parameter cube
`[0,1]^d` of the *sup* over a finset `K` of low-discrepancy exponent vectors `k` of the linear form
`∑_s k_s · log|φ_{κ s}(e^{2πi t_s})|` is bounded by the rearrangement integral `rearrInt w φ` plus
an error term.

The proof has two ingredients:

* the *pointwise* rearrangement bound (`Work.Holonomy3.pointwise_rearrangement_bound`, applied to
  `u_s = k_s / D` and `v_s = log|φ_{κ s}(e^{2πi t_s})|`, with the sorting permutations
  `Tuple.sort`): for every `k ∈ K` and every `t ∈ [0,1]^d`,
  `∑_s (k_s/D) v_s ≤ (1/(2d))·(∑_{a,b} max(v_a,v_b) − ∑_a v_a) + (ε+1/d)·d·G₀`;
* the *integrated* expectation estimate `Work.Holonomy3.expectation_max_blocked` (plus the diagonal
  correction `d·G₀` removing `∑_a v_a`), giving
  `∫ ∑_{a,b} max − ∫ ∑_a v_a ≤ d² rearrInt w φ + (8(l+1)²(d+1) + d)·G₀` — this is
  `Work.Holonomy3.integral_double_sum_le`.
-/

private lemma aemeasurable_comp_eval {d : ℕ} {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc 0 1))
    (c : Fin d) : AEMeasurable (fun t : Fin d → ℝ => h (t c)) (torMeasure d) := by
  have hmap : Measure.map (Function.eval c) (torMeasure d)
      = (volume : Measure ℝ).restrict (Set.Icc 0 1) :=
    (MeasureTheory.measurePreserving_eval
      (fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc 0 1)) c).map_eq
  have h1 : AEMeasurable h (Measure.map (Function.eval c) (torMeasure d)) := by
    rw [hmap]; exact hh.aemeasurable measurableSet_Icc
  exact h1.comp_aemeasurable (measurable_pi_apply c).aemeasurable

/-- Almost every point of the parameter cube `[0,1]^d` has all coordinates in `[0,1]`. -/
private lemma ae_box_mem (d : ℕ) :
    ∀ᵐ t ∂(torMeasure d), ∀ s : Fin d, t s ∈ Set.Icc (0:ℝ) 1 :=
  MeasureTheory.ae_all_iff.2 (fun s => ae_eval_mem_Icc s)

/-- The pointwise rearrangement bound for a single low-discrepancy exponent vector `k` with
`k j < D`: pairing `k/D` against `v` costs at most the comonotone pairing. -/
private lemma pointwise_rearr_of_scale {d : ℕ} (hd : 0 < d) {D : ℕ} (hD : 0 < D)
    (k : Fin d →₀ ℕ) (hk : ∀ j, k j < D) (v : Fin d → ℝ) {ε G₀ : ℝ}
    (hε : 0 ≤ ε) (hG0 : 0 ≤ G₀)
    (hdisc : Submission.CDT.Discrepancy.disc (fun j => (k j : ℝ) / D) ≤ ε)
    (hG : ∀ j, |v j| ≤ G₀) :
    ∑ j, (k j : ℝ) * v j ≤
      (D:ℝ) * ((1 / (2 * (d:ℝ))) * ((∑ a, ∑ b, max (v a) (v b)) - ∑ a, v a)
        + (ε + 1 / (d:ℝ)) * (d:ℝ) * G₀) := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  set u : Fin d → ℝ := fun j => (k j : ℝ) / D with hu
  have huIco : ∀ j, u j ∈ Set.Ico 0 1 := by
    intro j
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD0.le, ?_⟩
    rw [div_lt_one hD0]
    exact_mod_cast hk j
  have hmain := pointwise_rearrangement_bound hd u v (Tuple.sort u) (Tuple.sort v)
    (Tuple.monotone_sort u) (Tuple.monotone_sort v) hε hG0 huIco (by simpa [hu] using hdisc) hG
  rw [show (∑ j, (k j : ℝ) * v j) = D * ∑ j, u j * v j from ?_]
  · exact mul_le_mul_of_nonneg_left hmain hD0.le
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hu]
    field_simp

/-- **The measure-theoretic core.** Given the integrated bound `hX` on
`∫ ∑_{a,b} max(v_a,v_b) − ∫ ∑_a v_a`, the integral of the sup over `K` is bounded. -/
private theorem integral_sup_bound_aux {l d : ℕ} (hd : 0 < d) (K : Finset (Fin d →₀ ℕ))
    (hKne : K.Nonempty) (D : ℕ) (hD : 0 < D) (hKdeg : ∀ k ∈ K, ∀ j : Fin d, k j < D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hKdisc : ∀ k ∈ K, Submission.CDT.Discrepancy.disc (fun j : Fin d => (k j : ℝ) / D) ≤ ε)
    (g : Fin (l + 1) → ℝ → ℝ) (κ : Fin d → Fin (l + 1))
    {G₀ X : ℝ} (hG0 : 0 ≤ G₀)
    (hcont : ∀ p, ContinuousOn (g p) (Set.Icc 0 1))
    (hg : ∀ p t, t ∈ Set.Icc 0 1 → |g p t| ≤ G₀)
    (hX : (∫ t, (∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b))) ∂(torMeasure d))
            - (∫ t, ∑ a, g (κ a) (t a) ∂(torMeasure d)) ≤ X) :
    ∫ t, K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)) ∂(torMeasure d)
      ≤ (D:ℝ)/(2*(d:ℝ)) * X + (D:ℝ) * (ε + 1/(d:ℝ)) * (d:ℝ) * G₀ := by
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  -- (1) the a.e. pointwise bound: the sup over `K` of the linear forms
  have hpoint : ∀ᵐ t ∂(torMeasure d),
      K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s))
        ≤ (D:ℝ) * ((1/(2*(d:ℝ))) * ((∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
              - ∑ a, g (κ a) (t a)) + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) := by
    filter_upwards [ae_box_mem d] with t ht
    refine Finset.sup'_le hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)) (fun k hk => ?_)
    exact pointwise_rearr_of_scale hd hD k (hKdeg k hk) (fun j => g (κ j) (t j)) hε hG0
      (hKdisc k hk) (fun j => hg (κ j) (t j) (ht j))
  -- (2) a.e. strong measurability of the three integrands
  have hmeas1 : AEStronglyMeasurable
      (fun t : Fin d → ℝ => ∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b))) (torMeasure d) := by
    have h := (Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
      (fun a _ => Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
        (fun b _ => (aemeasurable_comp_eval (hcont (κ a)) a).max
          (aemeasurable_comp_eval (hcont (κ b)) b)))).aestronglyMeasurable
    have h2 : (∑ i : Fin d, ∑ i_1 : Fin d,
          fun a : Fin d → ℝ => max (g (κ i) (a i)) (g (κ i_1) (a i_1)))
        = fun t => ∑ i, ∑ i_1, max (g (κ i) (t i)) (g (κ i_1) (t i_1)) := by ext t; simp
    rwa [h2] at h
  have hmeas2 : AEStronglyMeasurable
      (fun t : Fin d → ℝ => ∑ a, g (κ a) (t a)) (torMeasure d) := by
    have h := (Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
      (fun a _ => aemeasurable_comp_eval (hcont (κ a)) a)).aestronglyMeasurable
    have h2 : (∑ i : Fin d, fun t : Fin d → ℝ => g (κ i) (t i))
        = fun t => ∑ i, g (κ i) (t i) := by ext t; simp
    rwa [h2] at h
  have hmeasF : AEStronglyMeasurable
      (fun t : Fin d → ℝ => K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)))
      (torMeasure d) := by
    have hfun : ∀ k ∈ K, AEStronglyMeasurable
        (fun t : Fin d → ℝ => ∑ s, (k s : ℝ) * g (κ s) (t s)) (torMeasure d) := by
      intro k _
      have h' := (Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
        (fun s _ => (aemeasurable_comp_eval (hcont (κ s)) s).const_mul (k s : ℝ))).aestronglyMeasurable
      have h2 : (∑ i : Fin d, fun x : Fin d → ℝ => (k i : ℝ) * g (κ i) (x i))
          = fun t => ∑ i, (k i : ℝ) * g (κ i) (t i) := by ext t; simp
      rwa [h2] at h'
    have h := Finset.sup'_induction (s := K) hKne
      (f := fun k => fun t : Fin d → ℝ => ∑ s, (k s : ℝ) * g (κ s) (t s))
      (p := fun F => AEStronglyMeasurable F (torMeasure d))
      (fun a1 ha1 a2 ha2 => ha1.sup ha2) hfun
    have h2 : (K.sup' hKne fun k => fun t : Fin d → ℝ => ∑ s, (k s : ℝ) * g (κ s) (t s))
        = fun t => K.sup' hKne fun k => ∑ s, (k s : ℝ) * g (κ s) (t s) := by
      ext t; rw [Finset.sup'_apply]
    rwa [h2] at h
  -- (3) a.e. bounds
  have hbound1 : ∀ᵐ t ∂(torMeasure d),
      ‖∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b))‖ ≤ (d:ℝ)*(d:ℝ)*G₀ := by
    filter_upwards [ae_box_mem d] with t ht
    rw [Real.norm_eq_abs]
    calc |∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b))|
        ≤ ∑ a, ∑ b, |max (g (κ a) (t a)) (g (κ b) (t b))| :=
          le_trans (Finset.abs_sum_le_sum_abs _ _)
            (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ a, ∑ b, G₀ := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
          abs_max_le (hg (κ a) (t a) (ht a)) (hg (κ b) (t b) (ht b))))
      _ = (d:ℝ)*(d:ℝ)*G₀ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hbound2 : ∀ᵐ t ∂(torMeasure d), ‖∑ a, g (κ a) (t a)‖ ≤ (d:ℝ)*G₀ := by
    filter_upwards [ae_box_mem d] with t ht
    rw [Real.norm_eq_abs]
    calc |∑ a, g (κ a) (t a)| ≤ ∑ a, |g (κ a) (t a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin d, G₀ := Finset.sum_le_sum (fun a _ => hg (κ a) (t a) (ht a))
      _ = (d:ℝ)*G₀ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hboundF : ∀ᵐ t ∂(torMeasure d),
      ‖K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s))‖ ≤ (d:ℝ)*(D:ℝ)*G₀ := by
    filter_upwards [ae_box_mem d] with t ht
    rw [Real.norm_eq_abs]
    have hbd : ∀ k ∈ K, |∑ s, (k s : ℝ) * g (κ s) (t s)| ≤ (d:ℝ)*(D:ℝ)*G₀ := by
      intro k hk
      have h1 : |∑ s, (k s : ℝ) * g (κ s) (t s)| ≤ ∑ s, (k s : ℝ) * |g (κ s) (t s)| := by
        calc |∑ s, (k s : ℝ) * g (κ s) (t s)| ≤ ∑ s, |(k s : ℝ) * g (κ s) (t s)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s, (k s : ℝ) * |g (κ s) (t s)| := by
              refine Finset.sum_congr rfl (fun s _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have h2 : ∑ s, (k s : ℝ) * |g (κ s) (t s)| ≤ ∑ _s : Fin d, (D:ℝ)*G₀ :=
        Finset.sum_le_sum (fun s _ => mul_le_mul (le_of_lt (by exact_mod_cast hKdeg k hk s))
          (hg (κ s) (t s) (ht s)) (abs_nonneg _) (Nat.cast_nonneg _))
      have h3 : ∑ _s : Fin d, (D:ℝ)*G₀ = (d:ℝ)*(D:ℝ)*G₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      linarith
    rw [abs_le]
    refine ⟨?_, Finset.sup'_le hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s))
      (fun k hk => (abs_le.mp (hbd k hk)).2)⟩
    obtain ⟨k0, hk0⟩ := hKne
    exact le_trans (abs_le.mp (hbd k0 hk0)).1
      (Finset.le_sup' (f := fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)) hk0)
  -- (4) integrability
  have hint1 := Integrable.of_bound hmeas1 ((d:ℝ)*(d:ℝ)*G₀) hbound1
  have hint2 := Integrable.of_bound hmeas2 ((d:ℝ)*G₀) hbound2
  have hintF := Integrable.of_bound hmeasF ((d:ℝ)*(D:ℝ)*G₀) hboundF
  have hintM : Integrable (fun t : Fin d → ℝ => (∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
      - ∑ a, g (κ a) (t a)) (torMeasure d) := hint1.sub hint2
  have hBint : Integrable (fun t : Fin d → ℝ => (D:ℝ) * ((1/(2*(d:ℝ)))
      * ((∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b))) - ∑ a, g (κ a) (t a))
      + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀)) (torMeasure d) :=
    (((hintM.const_mul (1/(2*(d:ℝ)))).add
      (integrable_const ((ε + 1/(d:ℝ)) * (d:ℝ) * G₀))).const_mul (D:ℝ))
  -- (5) monotonicity of the integral
  have hmono : (∫ t, K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)) ∂(torMeasure d))
      ≤ ∫ t, (D:ℝ) * ((1/(2*(d:ℝ))) * ((∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
          - ∑ a, g (κ a) (t a)) + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) ∂(torMeasure d) :=
    integral_mono_ae hintF hBint hpoint
  have hcalc : (∫ t, (D:ℝ) * ((1/(2*(d:ℝ))) * ((∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
        - ∑ a, g (κ a) (t a)) + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) ∂(torMeasure d))
      = (D:ℝ) * ((1/(2*(d:ℝ))) * ((∫ t, (∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
            ∂(torMeasure d))
          - (∫ t, ∑ a, g (κ a) (t a) ∂(torMeasure d)))
        + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add (hintM.const_mul _) (integrable_const _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hint1 hint2,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  -- (6) final arithmetic
  have hstep : (1/(2*(d:ℝ))) * ((∫ t, (∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
        ∂(torMeasure d))
      - (∫ t, ∑ a, g (κ a) (t a) ∂(torMeasure d))) ≤ (1/(2*(d:ℝ))) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  calc (∫ t, K.sup' hKne (fun k => ∑ s, (k s : ℝ) * g (κ s) (t s)) ∂(torMeasure d))
      ≤ ∫ t, (D:ℝ) * ((1/(2*(d:ℝ))) * ((∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
          - ∑ a, g (κ a) (t a)) + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) ∂(torMeasure d) := hmono
    _ = (D:ℝ) * ((1/(2*(d:ℝ))) * ((∫ t, (∑ a, ∑ b, max (g (κ a) (t a)) (g (κ b) (t b)))
            ∂(torMeasure d))
          - (∫ t, ∑ a, g (κ a) (t a) ∂(torMeasure d)))
        + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) := hcalc
    _ ≤ (D:ℝ) * ((1/(2*(d:ℝ))) * X + (ε + 1/(d:ℝ)) * (d:ℝ) * G₀) := by
        apply mul_le_mul_of_nonneg_left _ hD0.le
        linarith [hstep]
    _ = (D:ℝ)/(2*(d:ℝ)) * X + (D:ℝ) * (ε + 1/(d:ℝ)) * (d:ℝ) * G₀ := by
        rw [mul_add, ← mul_assoc]
        congr 1
        · congr 1; field_simp
        · ring

theorem integral_sup_bound {l d : ℕ} (hd : 0 < d) (K : Finset (Fin d →₀ ℕ)) (hKne : K.Nonempty)
    (D : ℕ) (hD : 0 < D) (hKdeg : ∀ k ∈ K, ∀ j : Fin d, k j < D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hKdisc : ∀ k ∈ K,
      Submission.CDT.Discrepancy.disc (fun j : Fin d => (k j : ℝ) / D) ≤ ε)
    (φ : Fin (l + 1) → ℂ → ℂ) (κ : Fin d → Fin (l + 1)) (w : Fin (l + 1) → ℝ)
    (hc : ∀ p, |((Finset.univ.filter (fun a : Fin d => κ a = p)).card : ℝ) / d - w p| ≤ 2 / d)
    {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hcont : ∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1))
    (hg : ∀ p t, t ∈ Set.Icc 0 1 → |Submission.CDTPlan.circleLog (φ p) t| ≤ G₀) :
    ∫ t : Fin d → ℝ,
        K.sup' hKne (fun k : Fin d →₀ ℕ =>
          ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))
        ∂(torMeasure d)
      ≤ (D : ℝ) / (2 * d) * ((d : ℝ) ^ 2 * Submission.CDTPlan.rearrInt w φ
          + (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + d) * G₀)
        + (D : ℝ) * (ε + 1 / d) * d * G₀ := by
  have hX := integral_double_sum_le hd φ κ w hc hG0 hcont hg
  have hmain := integral_sup_bound_aux (l := l) (d := d) hd K hKne D hD hKdeg ε hε hKdisc
    (fun p => Submission.CDTPlan.circleLog (φ p)) κ hG0 hcont hg hX
  simpa using hmain

end

end Work.Holonomy3
