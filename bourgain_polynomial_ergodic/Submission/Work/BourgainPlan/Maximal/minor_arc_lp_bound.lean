import Mathlib
import Submission.Work.BourgainPlan.Maximal.minor_arc_lp
import Submission.Work.BourgainPlan.Maximal.canonical_arcs

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The `ℓ^q` contraction of the `ℤ`-average in the form of an `eLpNorm` bound: for `q ≥ 1`,
`‖A_N g‖_{ℓ^q} ≤ ‖g‖_{ℓ^q}`.  This is `discAvgZC_contraction` (an inequality of lintegrals of
`‖·‖ₑ^q`) with the `q`-th root taken. -/
lemma eLpNorm_discAvgZC_le (P : Polynomial ℤ) (N : ℕ) {q : ℝ} (hq : 1 ≤ q) (g : ℤ → ℂ) :
    eLpNorm (discAvgZC P N g) (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq0)
        ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hq0)
        ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_le_rpow (discAvgZC_contraction P N hq g) (by positivity)

/-- The elementary root identity `(ofReal (A^p))^{1/p} = ofReal A` for `A ≥ 0`, `p > 0` used to
convert the `ℓᵖ` Ionescu–Wainger projection bound (which is stated multiplicatively in the
`p`-th powers of the `ℓᵖ` integrals) into an `eLpNorm` bound. -/
lemma ofReal_rpow_root {A p : ℝ} (hA : 0 ≤ A) (hp0 : 0 < p) :
    (ENNReal.ofReal (A ^ p)) ^ (1 / p) = ENNReal.ofReal A := by
  rw [ENNReal.ofReal_rpow_of_nonneg (x := A ^ p) (Real.rpow_nonneg hA p) (by positivity)]
  congr 1
  rw [← Real.rpow_mul hA, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-- **KMSZ (6.12): the minor-arc `ℓᵖ` bound for the polynomial density averages**, in the form
supplied by the `ℓᵖ` Ionescu–Wainger projection bound `IWProjectionBound` (= KMSZ (6.11)).

For every `p ∈ (1,∞)` and every `γ > 0` there are `C > 0` and a small `α > 0` such that for every
window `N`, every `l` with `2^l ≤ N^α`, every `m` in the (6.11) range
`m ≤ -6 max{p, p/(p-1)} (l+1)`, every bump `φ` of scale `2^{m-1}` (i.e. `‖φ‖ ≤ 1` and `φ` supported
in the ball of radius `2^{m-1}`) and every `f` with `Memℓp f 2`,

`‖A_N (f - Π_{≤l,≤m} f)‖_{ℓᵖ} ≤ C N^γ ‖f‖_{ℓᵖ}`,

where `A_N g (n) = N⁻¹ Σ_{i<N} g (n + P (i))` is the `ℤ`-average (`discAvgZC`, in
`Maximal/minor_arc_lp`) and `Π_{≤l,≤m} f = opArc φ hφ (canonicalFinset (2^l)) f hf` is the dyadic
Ionescu–Wainger projection (`Maximal/canonical_arcs`).  For the KMSZ parameters `l = l(N) = α Log N`
and `m = -d L(N)` this is exactly KMSZ (6.12) for `p = p₀`, because then the (6.11) loss
`D·2^{C_p γ l(N)} ≤ D·N^{C_p γ α} ≤ D·N^γ` for `α ≤ 1/C_p`.

Route (all in `ℝ≥0∞`, with `P' := ENNReal.ofReal p`):

1. `discAvgZC_sub` splits `A_N (f - Π f) = A_N f - A_N (Π f)`; then the triangle inequality
   `eLpNorm_sub_le` gives `‖A_N(f-Πf)‖ ≤ ‖A_N f‖ + ‖A_N (Π f)‖` at the exponent `P'` (this needs
   `1 ≤ P'`, i.e. `1 ≤ p`) — on `ℤ` with counting measure every function is a.e. strongly
   measurable (`by measurability`).
2. `eLpNorm_discAvgZC_le` (`discAvgZC_contraction`) gives `‖A_N u‖ ≤ ‖u‖` for `u = f` and
   `u = Π f`.
3. `IWProjectionBound p hp` gives `C_p`, and `IWProjectionBound p hp C_p _ γ hγ` gives the constant
   `D` with `∫⁻ ‖Π f‖ₑ^p ≤ ofReal ((D · 2^{C_p γ l})^p) * ∫⁻ ‖f‖ₑ^p`; taking `1/p`-th roots
   (`ENNReal.mul_rpow_of_nonneg`, and the elementary identity
   `(ofReal (A^p))^(1/p) = ofReal A`, helper `ofReal_rpow_root`) turns it into
   `‖Π f‖ ≤ ofReal (D · 2^{C_p γ l}) ‖f‖`.
4. Hence `‖A_N(f-Πf)‖ ≤ (1 + D·2^{C_p γ l})‖f‖`, and it remains to choose `α := 1/(C_p+1)` so that
   `2^{C_p γ l} ≤ N^γ`: from `2^l ≤ N^α`,
   `2^{C_p γ l} = (2^l)^{C_p γ} ≤ (N^α)^{C_p γ} = N^{α C_p γ} ≤ N^γ` since `α C_p ≤ 1`.  Provide
   `C = 1 + D`. -/
theorem minor_arc_lp_bound (hIW : Work.BourgainPlan.Maximal.IWProjectionBound) (P : Polynomial ℤ) :
    ∀ p : ℝ, 1 < p → ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧
      ∀ (N : ℕ) (l : ℕ) (m : ℤ) (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
        (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
        (hφbd : ∀ ξ, ‖φ ξ‖ ≤ 1) (hφsupp : ∀ ξ, (2 : ℝ) ^ (m - 1) < ‖ξ‖ → φ ξ = 0)
        (hm : (m : ℝ) ≤ -(6 * max p (p / (p - 1)) * ((l : ℝ) + 1)))
        (hlα : ((2 : ℝ) ^ l) ≤ (N : ℝ) ^ α)
        (f : ℤ → ℂ) (hf : Memℓp f 2),
      MeasureTheory.eLpNorm (fun n : ℤ => Work.BourgainPlan.Maximal.discAvgZC P N
          (fun m' => f m' - Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.Maximal.canonicalFinset (2 ^ l)) f hf m') n)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ γ)
            * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  intro p hp γ hγ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hIW p hp
  obtain ⟨D, hDpos, hD⟩ := hC₀ γ hγ
  refine ⟨1 + D, by positivity, 1 / (C₀ + 1), by positivity, ?_⟩
  intro N l m φ hφ hφbd hφsupp hm hlα f hf
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hane0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hanetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  -- the `A_N (f - Π f) = A_N f - A_N (Π f)` split
  have hsub : (fun n : ℤ => discAvgZC P N
        (fun m' => f m' - opArc φ hφ (canonicalFinset (2 ^ l)) f hf m') n)
      = fun n : ℤ => discAvgZC P N f n
          - discAvgZC P N (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m') n := by
    funext n
    exact congrFun (discAvgZC_sub P N f
      (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m')) n
  -- step 3: the `ℓᵖ` bound for the projection
  set K : ℝ := D * (2 : ℝ) ^ (C₀ * γ * (l : ℝ)) with hKdef
  have hKpos : 0 < K := by positivity
  have hproj : eLpNorm (fun n : ℤ => opArc φ hφ (canonicalFinset (2 ^ l)) f hf n)
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) Measure.count := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hane0 hanetop AEStronglyMeasurable.of_discrete,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hane0 hanetop AEStronglyMeasurable.of_discrete,
        ENNReal.toReal_ofReal hp0.le]
    calc (∫⁻ n : ℤ, ‖opArc φ hφ (canonicalFinset (2 ^ l)) f hf n‖ₑ ^ p
            ∂Measure.count) ^ (1 / p)
        ≤ (ENNReal.ofReal (K ^ p)
            * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (hD l m hm φ hφ hφbd hφsupp f hf) (by positivity)
      _ = (ENNReal.ofReal (K ^ p)) ^ (1 / p)
            * (∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count) ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = ENNReal.ofReal K * (∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count) ^ (1 / p) := by
          rw [ofReal_rpow_root (A := K) (by positivity) hp0]
  -- step 2: the `ℓᵖ` contraction of `A_N`, in the two places it is used
  have hAf : eLpNorm (discAvgZC P N f) (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm f (ENNReal.ofReal p) Measure.count :=
    eLpNorm_discAvgZC_le P N hp.le f
  have hAproj : eLpNorm (discAvgZC P N
        (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m'))
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) Measure.count :=
    le_trans (eLpNorm_discAvgZC_le P N hp.le
      (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m')) hproj
  -- step 4: the arithmetic, `α = 1/(C₀+1)` gives `2^{C₀ γ l} ≤ N^γ`
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (C₀ + 1)) := le_trans h1 hlα
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN, Nat.cast_zero,
        Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (C₀ + 1)))] at h2
      exact absurd h2 (by norm_num)
    · exact_mod_cast hN
  have hAle : (2 : ℝ) ^ (C₀ * γ * (l : ℝ)) ≤ (N : ℝ) ^ γ := by
    have hαC0 : (1 / (C₀ + 1)) * C₀ ≤ 1 := by
      rw [one_div, inv_mul_eq_div]
      rw [div_le_one (by linarith : (0 : ℝ) < C₀ + 1)]
      linarith
    have hexp : (1 / (C₀ + 1)) * (C₀ * γ) ≤ γ := by
      calc (1 / (C₀ + 1)) * (C₀ * γ) = ((1 / (C₀ + 1)) * C₀) * γ := by ring
        _ ≤ 1 * γ := mul_le_mul_of_nonneg_right hαC0 hγ.le
        _ = γ := one_mul γ
    have h2l : ((2 : ℝ) ^ (l : ℝ)) ≤ (N : ℝ) ^ (1 / (C₀ + 1)) := by
      rw [Real.rpow_natCast]; exact hlα
    calc (2 : ℝ) ^ (C₀ * γ * (l : ℝ))
        = ((2 : ℝ) ^ (l : ℝ)) ^ (C₀ * γ) := by
          rw [show C₀ * γ * (l : ℝ) = (l : ℝ) * (C₀ * γ) by ring]
          exact Real.rpow_mul (by norm_num) (l : ℝ) (C₀ * γ)
      _ ≤ ((N : ℝ) ^ (1 / (C₀ + 1))) ^ (C₀ * γ) :=
          Real.rpow_le_rpow (by positivity) h2l (by positivity)
      _ = (N : ℝ) ^ ((1 / (C₀ + 1)) * (C₀ * γ)) :=
          (Real.rpow_mul (Nat.cast_nonneg N) (1 / (C₀ + 1)) (C₀ * γ)).symm
      _ ≤ (N : ℝ) ^ γ := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  -- step 1 + assembly
  rw [hsub]
  calc eLpNorm (fun n : ℤ => discAvgZC P N f n
          - discAvgZC P N (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m') n)
        (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (discAvgZC P N f) (ENNReal.ofReal p) Measure.count
        + eLpNorm (discAvgZC P N (fun m' => opArc φ hφ (canonicalFinset (2 ^ l)) f hf m'))
            (ENNReal.ofReal p) Measure.count :=
        eLpNorm_sub_le hP1
    _ ≤ eLpNorm f (ENNReal.ofReal p) Measure.count
        + ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) Measure.count :=
        add_le_add hAf hAproj
    _ = (1 + ENNReal.ofReal K) * eLpNorm f (ENNReal.ofReal p) Measure.count := by
        rw [add_mul, one_mul]
    _ ≤ ENNReal.ofReal ((1 + D) * (N : ℝ) ^ γ)
          * eLpNorm f (ENNReal.ofReal p) Measure.count := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        have hNγ1 : (1 : ℝ) ≤ (N : ℝ) ^ γ := Real.one_le_rpow hN1 hγ.le
        have hsum : (1 : ℝ) + K ≤ (1 + D) * (N : ℝ) ^ γ := by
          have h2 : K ≤ D * (N : ℝ) ^ γ := mul_le_mul_of_nonneg_left hAle hDpos.le
          nlinarith [hNγ1, h2]
        calc 1 + ENNReal.ofReal K
            = ENNReal.ofReal (1 + K) := by
              rw [← ENNReal.ofReal_one]
              exact (ENNReal.ofReal_add zero_le_one (by positivity)).symm
          _ ≤ ENNReal.ofReal ((1 + D) * (N : ℝ) ^ γ) := ENNReal.ofReal_le_ofReal hsum

end

end Work.BourgainPlan.Maximal
