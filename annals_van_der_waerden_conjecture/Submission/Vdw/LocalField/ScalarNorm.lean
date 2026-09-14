import Mathlib
import Submission.Vdw.LocalField.AdicComplete
import Submission.Vdw.LocalField.QpAlgebra
import Submission.Vdw.LocalField.QpPadic

open Classical
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, (b2)): the scalar norm iff `‖algebraMap c‖ ≤ 1 ↔ ‖c‖ ≤ 1`

This module proves that the scalar embedding `ℚ_p → K_P`
(`algebraMap (QpAdic p) (kpAdic p P)`, the completed `ℚ ↪ K` map) preserves
integrality:

    scalar_norm_le_one_iff : ‖algebraMap c‖ ≤ 1 ↔ ‖c‖ ≤ 1   (c ∈ ℚ_p)

This is the norm-lemma that the `e(W)=1` coefficient arguments need: a
coefficient `c_i ∈ QpAdic` of the `{1,…,ζ^{f−1}}`-decomposition of an
integral element of `W` is p-integral iff its image in `K_P` is integral, so
integrality/divisibility can be decided on either side.

Structure of the proof (no exact rational-norm arithmetic — only the
order-compatible facts):
* rational compat `rat_norm_le_one_kp_iff_qp`: for `q ∈ ℚ`, `‖q‖_{K_P} ≤ 1
  ↔ ‖q‖_{ℚ_p} ≤ 1`.  Both sides are `Valued.v ≤ 1` (`norm_le_one_iff_val`),
  rational values are the ℤᵐ⁰-valuations (`adicCompletion.valued_coe`), and
  `v_P(q) = (v_p q)^{e_P}` (`valuation_rat_pow_ramificationIdx`); on ℤᵐ⁰,
  `a ≤ 1 ↔ a^e ≤ 1` for `e ≥ 1` (`pow_le_one_iff`).
* `norm_eq_of_sub_lt_norm` — generic ultrametric lemma: `‖y − x‖ < ‖x‖ ⟹
  ‖y‖ = ‖x‖` (via `IsUltrametricDist.dist_eq_max_of_dist_ne_dist`), used to
  keep the norm constant when approximating by rationals.
* `norm_gt_one_ge_inv_uniformizer` — DVR discreteness of `K_P`: a
  non-integral element has `‖y‖ ≥ ‖ϖ‖⁻¹` (`y⁻¹ ∈ 𝔪 = (ϖ)`, `‖v‖ ≤ 1`).
* the main theorem: rational-integral points are dense in the unit ball of
  ℚ_p (`denseRange_qp` + the ultrametric equality) and map into the closed
  unit ball of K_P (`rat_norm_le_one_kp_iff_qp` + tower); conversely
  non-integral scalars are limits of non-integral rationals, whose images
  have norm `≥ ‖ϖ‖⁻¹` (a closed condition), so the image is non-integral.
  Uses `Metric.mem_closure_iff` + `closure_minimal` throughout.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- rational embedded into ℚ_p. -/
abbrev qpQ (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) : QpAdic p := algebraMap ℚ (QpAdic p) q

/-- rational embedded into K_P. -/
abbrev kpQ (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) : kpAdic p P :=
  algebraMap ℚ (kpAdic p P) q

/-- tower: the ℚ_p-scalar embedding sends a rational to the embedded rational. -/
theorem phi_qpQ_eq_kpQ (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) :
    algebraMap (QpAdic p) (kpAdic p P) (qpQ p q) = kpQ p P q := by
  rw [algebraMap_eq_qpToKp]
  exact qpToKp_algebraMap_rat p P q

/-- norm ≤ 1 ↔ valuation ≤ 1 on ℚ_p. -/
lemma norm_le_one_iff_val_qp (p : ℕ) [Fact (Nat.Prime p)] (x : QpAdic p) :
    ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff (L := QpAdic p) (Γ₀ := ℤᵐ⁰) (x := x)

/-- the ℚ_p-valuation of a rational equals its (p)-adic valuation. -/
lemma valued_coe_qp (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) :
    Valued.v (qpQ p q) = (qprime p).valuation ℚ q := by
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe (K := ℚ) (v := qprime p) q

/-- the K_P-valuation of a rational equals its P-adic valuation (as element of K). -/
lemma valued_coe_kp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) :
    Valued.v (kpQ p P q) = (kprime p P).valuation K ((q : K)) := by
  calc
    Valued.v (kpQ p P q)
        = Valued.v (algebraMap K (kpAdic p P) (algebraMap ℚ K q)) := by
          rw [show kpQ p P q = algebraMap K (kpAdic p P) (algebraMap ℚ K q) by rfl]
    _ = (kprime p P).valuation K (algebraMap ℚ K q) := by
          exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
            (K := K) (v := kprime p P) (algebraMap ℚ K q)
    _ = (kprime p P).valuation K ((q : K)) := by rfl

/-- power ≤ 1 on ℤᵐ⁰ is unchanged under positive powers (e ≥ 1). -/
lemma pow_le_one_iff (a : ℤᵐ⁰) (e : ℕ) (he : 1 ≤ e) : a ≤ 1 ↔ a ^ e ≤ 1 := by
  constructor
  · intro h
    exact pow_le_pow_left₀ (zero_le : (0 : ℤᵐ⁰) ≤ a) h e
  · intro h
    by_contra hnot
    have h1 : 1 < a := lt_of_not_ge hnot
    have he0 : e ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one he)
    have hp := pow_lt_pow_left₀ h1 (zero_le : (0 : ℤᵐ⁰) ≤ (1 : ℤᵐ⁰)) he0
    have : (1 : ℤᵐ⁰) ^ e = 1 := by simp
    rw [this] at hp
    exact not_le_of_gt hp h

/-- rational integrality is the same in ℚ_p and K_P (valuation e-power compatibility). -/
theorem rat_norm_le_one_kp_iff_qp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) :
    ‖kpQ p P q‖ ≤ 1 ↔ ‖qpQ p q‖ ≤ 1 := by
  classical
  let w : ℤᵐ⁰ := (qprime p).valuation ℚ q
  have hkp : ‖kpQ p P q‖ ≤ 1 ↔ w ^ P.ramificationIdx ℤ ≤ 1 := by
    rw [norm_le_one_iff_val (p := p) (P := P) (x := kpQ p P q)]
    rw [valued_coe_kp (p := p) (P := P) q]
    have hv := valuation_rat_pow_ramificationIdx (K := K) p P q
    -- hv : (kprime p P).valuation K (q : K) = ((qprime p).valuation ℚ q) ^ P.ramificationIdx ℤ
    rw [hv]
  have hqp : ‖qpQ p q‖ ≤ 1 ↔ w ≤ 1 := by
    rw [norm_le_one_iff_val_qp]
    rw [valued_coe_qp]
  rw [hkp, hqp]
  exact (pow_le_one_iff w (P.ramificationIdx ℤ) (Ideal.ramificationIdx_pos P ℤ)).symm

/-- generic ultrametric equality: close elements have equal norm. -/
lemma norm_eq_of_sub_lt_norm {S : Type*} [SeminormedAddCommGroup S] [IsUltrametricDist S]
    (x y : S) (h : ‖y - x‖ < ‖x‖) : ‖y‖ = ‖x‖ := by
  have hne : dist y x ≠ dist x (0 : S) := by
    rw [dist_eq_norm, dist_eq_norm]
    simpa using (ne_of_lt h)
  have hmax := IsUltrametricDist.dist_eq_max_of_dist_ne_dist (X := S) (x := y) (y := x)
    (z := (0 : S)) hne
  calc
    ‖y‖ = dist y (0 : S) := by rw [dist_eq_norm]; simp
    _ = max (dist y x) (dist x (0 : S)) := hmax
    _ = max ‖y - x‖ ‖x‖ := by
          rw [dist_eq_norm]; congr 1; rw [dist_eq_norm]; simp
    _ = ‖x‖ := max_eq_right (le_of_lt h)

/-- DVR discreteness in K_P: a non-integral element has norm ≥ ‖ϖ‖⁻¹
(`ϖ` the uniformizer of `kpInt`, so the unit ball of `kpAdic` sits at least
one power of `‖ϖ‖` away from 1 on the outside). -/
theorem norm_gt_one_ge_inv_uniformizer (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (y : kpAdic p P) (hy : 1 < ‖y‖) :
    ‖(uniformizer p P : kpAdic p P)‖⁻¹ ≤ ‖y‖ := by
  classical
  let ϖ : kpInt p P := uniformizer p P
  have hz0 : y ≠ 0 := by
    intro hz; rw [hz] at hy; norm_num at hy
  have hz1 : ‖y⁻¹‖ < 1 := by
    rw [norm_inv]
    rw [inv_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hy
  have hvlt : Valued.v y⁻¹ < 1 :=
    (Valued.toNormedField.norm_lt_one_iff (L := kpAdic p P) (Γ₀ := ℤᵐ⁰) (x := y⁻¹)).mp hz1
  let zi : kpInt p P :=
    ⟨y⁻¹, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (R := 𝓞 K) K (kprime p P)).mpr hvlt.le⟩
  have hzi : ((zi : kpInt p P) : kpAdic p P) = y⁻¹ := rfl
  have hzmem : zi ∈ IsLocalRing.maximalIdeal (kpInt p P) := by
    rw [mem_maximalIdeal_iff_val_lt_one]
    rw [hzi]
    exact hvlt
  have hspan : zi ∈ Ideal.span ({(ϖ : kpInt p P)} : Set (kpInt p P)) := by
    rw [maximalIdeal_eq_span_uniformizer] at hzmem
    simpa [ϖ] using hzmem
  rcases (Ideal.mem_span_singleton.mp hspan) with ⟨v, hv⟩
  have hv0 : (v : kpAdic p P) ≠ 0 := by
    intro hvz
    have hzmem0 : (zi : kpAdic p P) = 0 := by
      calc
        (zi : kpAdic p P) = ((ϖ : kpInt p P) : kpAdic p P) * ((v : kpInt p P) : kpAdic p P) := by
          rw [hv]
          rfl
        _ = 0 := by rw [hvz]; simp
    exact (inv_ne_zero hz0) (by simpa [hzi] using hzmem0)
  have hiv : ‖y⁻¹‖ ≤ ‖(uniformizer p P : kpAdic p P)‖ := by
    rw [← hzi]
    calc
      ‖(zi : kpAdic p P)‖
          = ‖((uniformizer p P : kpAdic p P) * (v : kpAdic p P))‖ := by
            congr 1
            rw [hv]
            rfl
      _ = ‖(uniformizer p P : kpAdic p P)‖ * ‖(v : kpAdic p P)‖ := by rw [norm_mul]
      _ ≤ ‖(uniformizer p P : kpAdic p P)‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (norm_le_one p P v) (le_of_lt (uniformizer_norm_pos p P))
      _ = ‖(uniformizer p P : kpAdic p P)‖ := by simp
  have h1 : (1 : ℝ) ≤ ‖y‖ * ‖(uniformizer p P : kpAdic p P)‖ := by
    have hstep : ‖y‖ * ‖y⁻¹‖ ≤ ‖y‖ * ‖(uniformizer p P : kpAdic p P)‖ :=
      mul_le_mul_of_nonneg_left hiv (le_of_lt (norm_pos_iff.mpr hz0))
    -- LHS: ‖y‖ * ‖y⁻¹‖ = 1 (norm_inv): ‖y‖ * ‖y‖⁻¹ = 1
    have hcancel : ‖y‖ * ‖y⁻¹‖ = 1 := by
      rw [norm_inv]
      exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0)
    rwa [hcancel] at hstep
  have hϖne : (uniformizer p P : kpAdic p P) ≠ 0 := by
    exact_mod_cast (uniformizer_ne_zero p P)
  have hϖpos : 0 < ‖(uniformizer p P : kpAdic p P)‖ := norm_pos_iff.mpr hϖne
  rw [← one_div]
  rw [div_le_iff₀ hϖpos]
  exact h1

/-- the scalar embedding ℚ_p → K_P is continuous. -/
lemma continuous_scalar_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (fun x : QpAdic p => algebraMap (QpAdic p) (kpAdic p P) x) := by
  rw [algebraMap_eq_qpToKp]
  exact continuous_qpToKp p P
/-- rationals are dense in ℚ_p. -/
lemma denseRange_qp (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange (fun q : ℚ => qpQ p q) := by
  change DenseRange (fun q : ℚ =>
    (algebraMap ℚ ((qprime p).adicCompletion ℚ) q : (qprime p).adicCompletion ℚ))
  exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := ℤ) (K := ℚ) (v := qprime p)

/-- **The scalar norm iff**: for a scalar `c ∈ ℚ_p`, integrality is preserved
by the embedding `ℚ_p → K_P`: `‖algebraMap c‖ ≤ 1 ↔ ‖c‖ ≤ 1`.  Proof:
rational-integral points are dense in the unit ball of ℚ_p (ultrametric
equality + density), their images are integral in K_P (rational compat), and
the unit ball of K_P is closed (continuity).  The reverse direction uses the
DVR discreteness of K_P for the uniform separation. -/
theorem scalar_norm_le_one_iff (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (c : QpAdic p) :
    ‖algebraMap (QpAdic p) (kpAdic p P) c‖ ≤ 1 ↔ ‖c‖ ≤ 1 := by
  classical
  let S : Set (QpAdic p) := {x : QpAdic p |
    ∃ q : ℚ, ‖qpQ p q‖ ≤ 1 ∧ qpQ p q = x}
  let T : Set (QpAdic p) := {x : QpAdic p |
    ∃ q : ℚ, 1 < ‖qpQ p q‖ ∧ qpQ p q = x}
  let A : Set (QpAdic p) := {x : QpAdic p | ‖algebraMap (QpAdic p) (kpAdic p P) x‖ ≤ 1}
  let C : Set (QpAdic p) := {x : QpAdic p |
    ‖(uniformizer p P : kpAdic p P)‖⁻¹ ≤ ‖algebraMap (QpAdic p) (kpAdic p P) x‖}
  have hcont : Continuous (fun x : QpAdic p => algebraMap (QpAdic p) (kpAdic p P) x) :=
    continuous_scalar_algebraMap p P
  have hAclosed : IsClosed A := by
    dsimp [A]
    exact isClosed_le (continuous_norm.comp hcont) continuous_const
  have hCclosed : IsClosed C := by
    dsimp [C]
    exact isClosed_le continuous_const (continuous_norm.comp hcont)
  have hSA : S ⊆ A := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    dsimp [A]
    rw [phi_qpQ_eq_kpQ p P q]
    exact (rat_norm_le_one_kp_iff_qp p P q).mpr hq
  have hTC : T ⊆ C := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    dsimp [C]
    rw [phi_qpQ_eq_kpQ p P q]
    have hqk : 1 < ‖kpQ p P q‖ := by
      have hnle : ¬ ‖kpQ p P q‖ ≤ 1 := by
        rw [rat_norm_le_one_kp_iff_qp p P q]
        exact not_le_of_gt hq
      exact lt_of_not_ge hnle
    exact norm_gt_one_ge_inv_uniformizer p P (kpQ p P q) hqk
  have hDense : DenseRange (fun q : ℚ => qpQ p q) := denseRange_qp p
  have hBclS : ∀ x : QpAdic p, ‖x‖ ≤ 1 → x ∈ closure S := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases hx0 : x = 0
    · subst x
      refine ⟨0, ?_, ?_⟩
      · refine ⟨0, ?_, ?_⟩
        · simp [qpQ]
        · simp [qpQ]
      · simpa [dist_eq_norm]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      let δ : ℝ := min ε (‖x‖ / 2)
      have hδ0 : 0 < δ := lt_min hε (by positivity)
      have hs : Metric.ball x δ ∈ nhds x := Metric.ball_mem_nhds x hδ0
      rcases (hDense.mem_nhds (s := Metric.ball x δ) hs) with ⟨q, hq⟩
      refine ⟨qpQ p q, ?_, ?_⟩
      · refine ⟨q, ?_, rfl⟩
        have hdx : dist (qpQ p q) x < δ := (Metric.mem_ball.mp hq)
        have hd : ‖qpQ p q - x‖ < δ := by
          simpa [dist_eq_norm] using hdx
        have hδx : δ < ‖x‖ := by
          exact lt_of_le_of_lt (min_le_right ε (‖x‖ / 2)) (half_lt_self hxn)
        have hlt : ‖qpQ p q - x‖ < ‖x‖ := lt_trans hd hδx
        have hnorm : ‖qpQ p q‖ = ‖x‖ :=
          norm_eq_of_sub_lt_norm (S := QpAdic p) (x := x) (y := qpQ p q) hlt
        rw [hnorm]
        exact hx
      · have hdx : dist (qpQ p q) x < δ := (Metric.mem_ball.mp hq)
        have hd : ‖qpQ p q - x‖ < δ := by
          simpa [dist_eq_norm] using hdx
        rw [dist_eq_norm]
        rw [norm_sub_rev x (qpQ p q)]
        exact lt_of_lt_of_le hd (min_le_left ε (‖x‖ / 2))
  have hOutT : ∀ x : QpAdic p, 1 < ‖x‖ → x ∈ closure T := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hxn : 0 < ‖x‖ := lt_trans zero_lt_one hx
    let δ : ℝ := min ε (‖x‖ / 2)
    have hδ0 : 0 < δ := lt_min hε (by positivity)
    have hs : Metric.ball x δ ∈ nhds x := Metric.ball_mem_nhds x hδ0
    rcases (hDense.mem_nhds (s := Metric.ball x δ) hs) with ⟨q, hq⟩
    refine ⟨qpQ p q, ?_, ?_⟩
    · refine ⟨q, ?_, rfl⟩
      have hdx : dist (qpQ p q) x < δ := (Metric.mem_ball.mp hq)
      have hd : ‖qpQ p q - x‖ < δ := by
        simpa [dist_eq_norm] using hdx
      have hδx : δ < ‖x‖ := by
        exact lt_of_le_of_lt (min_le_right ε (‖x‖ / 2)) (half_lt_self hxn)
      have hlt : ‖qpQ p q - x‖ < ‖x‖ := lt_trans hd hδx
      have hnorm : ‖qpQ p q‖ = ‖x‖ :=
        norm_eq_of_sub_lt_norm (S := QpAdic p) (x := x) (y := qpQ p q) hlt
      rw [hnorm]
      exact hx
    · have hdx : dist (qpQ p q) x < δ := (Metric.mem_ball.mp hq)
      have hd : ‖qpQ p q - x‖ < δ := by
        simpa [dist_eq_norm] using hdx
      rw [dist_eq_norm]
      rw [norm_sub_rev x (qpQ p q)]
      exact lt_of_lt_of_le hd (min_le_left ε (‖x‖ / 2))
  constructor
  · intro hfc
    by_contra hnot
    have hcgt : 1 < ‖c‖ := lt_of_not_ge hnot
    have hmemC : c ∈ C := closure_minimal hTC hCclosed (hOutT c hcgt)
    have hϖgt1 : 1 < ‖(uniformizer p P : kpAdic p P)‖⁻¹ := by
      have hϖlt1 : ‖(uniformizer p P : kpAdic p P)‖ < 1 := uniformizer_norm_lt_one p P
      have hϖpos : 0 < ‖(uniformizer p P : kpAdic p P)‖ := norm_pos_iff.mpr (by
        exact_mod_cast (uniformizer_ne_zero p P))
      exact (one_lt_inv₀ hϖpos).mpr hϖlt1
    have hineq : ‖(uniformizer p P : kpAdic p P)‖⁻¹ ≤
        ‖algebraMap (QpAdic p) (kpAdic p P) c‖ := by
      simpa [C] using hmemC
    exact (not_le_of_gt (lt_of_lt_of_le hϖgt1 hineq)) hfc
  · intro hc
    have hmemA : c ∈ A := closure_minimal hSA hAclosed (hBclS c hc)
    simpa [A] using hmemA

end
end Submission.Vdw.LocalField
