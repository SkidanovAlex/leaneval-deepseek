import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.ppc_aux
import Submission.Work.A14D.pullback_B2_hasSum
import Submission.Work.A14D.pullback_B3_hasSum
import Submission.Work.A14D.pullback_B4_hasSum
import Submission.Work.A14D.pullback_B5_hasSum
import Submission.Work.A14D.deriv_twoLi2_log_sq
import Submission.Work.A14D.deriv_evp_Jps
import Submission.Work.A14D.deriv_evp_pureB5
import Submission.Work.A14D.deriv_evp_pureB6

namespace Work.A14D

open Complex Metric
open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## Convenience: the individual pure series -/

lemma pureB_val_zero : Submission.CDTPlan.pureB 0 = Submission.CDTPlan.B1 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_one : Submission.CDTPlan.pureB 1 = Submission.CDTPlan.B2 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_two : Submission.CDTPlan.pureB 2 = Submission.CDTPlan.B3 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_three : Submission.CDTPlan.pureB 3 = Submission.CDTPlan.B4 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_four : Submission.CDTPlan.pureB 4 = Submission.CDTPlan.B5 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_five : Submission.CDTPlan.pureB 5 = Submission.CDTPlan.B6 := by
  simp [Submission.CDTPlan.pureB]
lemma pureB_val_six : Submission.CDTPlan.pureB 6 = Submission.CDTPlan.B7 := by
  simp [Submission.CDTPlan.pureB]

/-! ## Differentiability of the coefficient functions -/

lemma differentiableOn_inv_of {S : Set ℂ} {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g S)
    (hne : ∀ z ∈ S, g z ≠ 0) : DifferentiableOn ℂ (fun z => (g z)⁻¹) S := by
  have h : DifferentiableOn ℂ (fun z => 1 / g z) S :=
    DifferentiableOn.div (differentiableOn_const 1) hg (fun z hz h => hne z hz h)
  exact h.congr (fun z _ => by rw [one_div])

lemma differentiableOn_inv_sub_one {S : Set ℂ} (h1 : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1)⁻¹) S :=
  differentiableOn_inv_of (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz h => h1 (by rw [sub_eq_zero.mp h] at hz; exact hz))

lemma differentiableOn_inv_self {S : Set ℂ} (h0 : (0 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) S :=
  differentiableOn_inv_of differentiableOn_id (fun z hz h => h0 (by rwa [h] at hz))

lemma differentiableOn_inv_mul_sub_one {S : Set ℂ} (h0 : (0 : ℂ) ∉ S) (h1 : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => (z * (z - 1))⁻¹) S := by
  refine differentiableOn_inv_of
    (differentiableOn_id.mul (differentiableOn_id.sub (differentiableOn_const 1))) ?_
  intro z hz h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h0 (by rwa [h'] at hz)
  · exact h1 (by rw [sub_eq_zero.mp h'] at hz; exact hz)

lemma differentiableOn_inv_sub_one_sq {S : Set ℂ} (h1 : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun z : ℂ => ((z - 1) ^ 2)⁻¹) S := by
  refine differentiableOn_inv_of ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz h => ?_)
  rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)] at h
  exact h1 (by rw [sub_eq_zero.mp h] at hz; exact hz)

lemma differentiableOn_div_z_mul_sub_one {S : Set ℂ} (h0 : (0 : ℂ) ∉ S) (h1 : (1 : ℂ) ∉ S)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => f z / (z * (z - 1))) S := by
  refine (hf.mul (differentiableOn_inv_mul_sub_one h0 h1)).congr (fun z _ => ?_)
  rw [Pi.mul_apply, div_eq_mul_inv]

lemma differentiableOn_div_sub_one {S : Set ℂ} (h1 : (1 : ℂ) ∉ S) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => f z / (z - 1)) S := by
  refine (hf.mul (differentiableOn_inv_sub_one h1)).congr (fun z _ => ?_)
  rw [Pi.mul_apply, div_eq_mul_inv]

lemma differentiableOn_div_self {S : Set ℂ} (h0 : (0 : ℂ) ∉ S) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun z => f z / z) S := by
  refine (hf.mul (differentiableOn_inv_self h0)).congr (fun z _ => ?_)
  rw [Pi.mul_apply, div_eq_mul_inv]

/-! ## The continuation on a convex half-plane avoiding `0` and `1` -/

/-- For a convex open set `S` with `0, 1 ∉ S`, each of the seven pullback series
`Σ_k [x^k]((pureB j).subst sympY)·z^k` (holomorphic on the unit disc) extends to a holomorphic
function on `S` agreeing with it on `S ∩ ball 0 1`. -/
theorem cont_half {S : Set ℂ} (hSo : IsOpen S) (hSc : Convex ℝ S)
    (h1 : (1 : ℂ) ∉ S) (h0 : (0 : ℂ) ∉ S) {z₀ : ℂ} (hz₀ : z₀ ∈ S ∩ Metric.ball 0 1)
    (j : Fin 7) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F S ∧ ∀ z ∈ S ∩ Metric.ball 0 1,
      F z = ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ)
          * z ^ k := by
  obtain ⟨𝓛, h𝓛d, h𝓛₀, h𝓛', h𝓛eq⟩ := exists_log_branch hSo hSc hz₀ h1
  have hz0ne : ∀ z ∈ S, z ≠ 0 := fun z hz h => h0 (by rwa [h] at hz)
  have hz1ne : ∀ z ∈ S, z ≠ 1 := fun z hz h => h1 (by rwa [h] at hz)
  -- `w = z(z-2)/(z-1)` is holomorphic on `S`
  have hwd : DifferentiableOn ℂ (fun z : ℂ => z * (z - 2) / (z - 1)) S := by
    refine DifferentiableOn.div (differentiableOn_id.mul (differentiableOn_id.sub
      (differentiableOn_const 2))) (differentiableOn_id.sub (differentiableOn_const 1)) ?_
    intro z hz h
    exact hz1ne z hz (sub_eq_zero.mp h)
  -- ## the dilogarithm combination `M = 2Li₂ + ½log²` and its continuation
  have hMserd : DifferentiableOn ℂ
      (fun w : ℂ => 2 * Work.CPull.evp Work.C7.Li2ps w
        + (1 / 2) * (Complex.log (1 - w)) ^ 2) (S ∩ Metric.ball 0 1) := by
    obtain ⟨C, hC, k, hk⟩ := poly_growth_Li2ps
    have h1' : DifferentiableOn ℂ (fun w : ℂ => 2 * Work.CPull.evp Work.C7.Li2ps w)
        (S ∩ Metric.ball 0 1) :=
      ((differentiableOn_evp_of_poly_growth hC hk).mono Set.inter_subset_right).const_mul 2
    have h2' : DifferentiableOn ℂ (fun w : ℂ => (1 / 2) * (Complex.log (1 - w)) ^ 2)
        (S ∩ Metric.ball 0 1) :=
      ((differentiableOn_log_one_sub.mono Set.inter_subset_right).pow 2).const_mul (1 / 2)
    exact h1'.add h2'
  have hbMd : DifferentiableOn ℂ (fun z : ℂ => -(z - 2) * 𝓛 z / (z * (z - 1))) S :=
    differentiableOn_div_z_mul_sub_one h0 h1
      ((differentiableOn_id.sub (differentiableOn_const 2)).neg.mul h𝓛d)
  have hodeM : ∀ z ∈ S ∩ Metric.ball 0 1,
      HasDerivAt (fun w : ℂ => 2 * Work.CPull.evp Work.C7.Li2ps w
          + (1 / 2) * (Complex.log (1 - w)) ^ 2)
        ((0 : ℂ) * (2 * Work.CPull.evp Work.C7.Li2ps z
            + (1 / 2) * (Complex.log (1 - z)) ^ 2) + (-(z - 2) * 𝓛 z / (z * (z - 1)))) z := by
    intro z hz
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    have h := deriv_twoLi2_log_sq z hzlt (hz0ne z hz.1)
    refine h.congr_deriv ?_
    rw [h𝓛eq z hz]
    ring
  obtain ⟨M, hMd, hMode, hMeq⟩ :=
    cont_of_convex_ode hSc hSo (differentiableOn_const 0) hbMd hMserd hodeM hz₀
  -- ## the `J`-function and its continuation
  have hAjd : DifferentiableOn ℂ (fun z : ℂ => 1 / (2 * (z - 1))) S := by
    have hinv : DifferentiableOn ℂ (fun z : ℂ => (2 * (z - 1))⁻¹) S :=
      differentiableOn_inv_of
        ((differentiableOn_const 2).mul (differentiableOn_id.sub (differentiableOn_const 1)))
        (fun z hz h => by
          rcases mul_eq_zero.mp h with h' | h'
          · norm_num at h'
          · exact hz1ne z hz (sub_eq_zero.mp h'))
    exact hinv.congr (fun z _ => by rw [one_div])
  have hbJd : DifferentiableOn ℂ (fun z : ℂ => -𝓛 z / z) S :=
    differentiableOn_div_self h0 h𝓛d.neg
  have hJserd : DifferentiableOn ℂ (fun w : ℂ => Work.CPull.evp Work.C7.Jps w)
      (S ∩ Metric.ball 0 1) := by
    obtain ⟨C, hC, k, hk⟩ := poly_growth_Jps
    exact (differentiableOn_evp_of_poly_growth hC hk).mono Set.inter_subset_right
  have hodeJ : ∀ z ∈ S ∩ Metric.ball 0 1,
      HasDerivAt (fun w : ℂ => Work.CPull.evp Work.C7.Jps w)
        ((1 / (2 * (z - 1))) * Work.CPull.evp Work.C7.Jps z + (-𝓛 z / z)) z := by
    intro z hz
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    have h := deriv_evp_Jps z hzlt (hz0ne z hz.1)
    refine h.congr_deriv ?_
    rw [h𝓛eq z hz]
    ring
  obtain ⟨J, hJd, hJode, hJeq⟩ :=
    cont_of_convex_ode hSc hSo hAjd hbJd hJserd hodeJ hz₀
  have hfac : ∀ z : ℂ, z ≠ 1 → z * (z - 2) / (z - 1) = z - z / (z - 1) := by
    intro z hz
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    field_simp
    ring
  fin_cases j
  · -- ## `B₁ ∘ y = 1`
    refine ⟨fun _ => 1, differentiableOn_const 1, fun z hz => ?_⟩
    show (1 : ℂ) = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB 0).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k
    rw [pureB_val_zero]
    have hB1 : Submission.CDTPlan.B1 = PowerSeries.C (1 : ℚ) := rfl
    have hsub : (Submission.CDTPlan.B1).subst Submission.CDT.sympY = 1 := by
      rw [hB1, PowerSeries.subst_C]
      simp
    rw [hsub]
    exact (Work.CPull.evp_one z).symm
  · -- ## `B₂ ∘ y = 2y − w·log(1−x)`
    refine ⟨fun z => 2 * (z ^ 2 / (z - 1)) - (z * (z - 2) / (z - 1)) * 𝓛 z,
      ((differentiableOn_const 2).mul
        (differentiableOn_div_sub_one h1 (differentiableOn_id.pow 2))).sub (hwd.mul h𝓛d),
      fun z hz => ?_⟩
    show 2 * (z ^ 2 / (z - 1)) - (z * (z - 2) / (z - 1)) * 𝓛 z = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB 1).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    rw [pureB_val_one, h𝓛eq z hz]
    exact (pullback_B2_hasSum z hzlt).tsum_eq.symm
  · -- ## `B₃ ∘ y = −½log(1−x)²`
    refine ⟨fun z => -(𝓛 z) ^ 2 / 2, (h𝓛d.pow 2).neg.div_const 2, fun z hz => ?_⟩
    show -(𝓛 z) ^ 2 / 2 = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB 2).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    rw [pureB_val_two, h𝓛eq z hz]
    exact (pullback_B3_hasSum z hzlt).tsum_eq.symm
  · -- ## `B₄ ∘ y = w·(2Li₂ + ½log²)`
    refine ⟨fun z => (z * (z - 2) / (z - 1)) * M z, hwd.mul hMd, fun z hz => ?_⟩
    show (z * (z - 2) / (z - 1)) * M z = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB 3).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    rw [pureB_val_three, hMeq z hz]
    simp only [Work.CPull.evp]
    rw [hfac z (hz1ne z hz.1), ← (pullback_B4_hasSum z hzlt).tsum_eq]
  · -- ## `B₅ ∘ y = (x/(x−1))·J`
    refine ⟨fun z => (z / (z - 1)) * J z,
      (differentiableOn_div_sub_one h1 differentiableOn_id).mul hJd, fun z hz => ?_⟩
    show (z / (z - 1)) * J z = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB 4).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k
    have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
    rw [pureB_val_four, hJeq z hz]
    simp only [Work.CPull.evp]
    rw [← (pullback_B5_hasSum z hzlt).tsum_eq]
  · -- ## `B₆ ∘ y = ∫ (B₃∘y)·y'/y`
    have hcoef5 : DifferentiableOn ℂ
        (fun z : ℂ => -(𝓛 z) ^ 2 / 2 * ((z - 2) / (z * (z - 1)))) S := by
      refine (differentiableOn_div_z_mul_sub_one h0 h1
        (f := fun z : ℂ => -(𝓛 z) ^ 2 / 2 * (z - 2)) ?_).congr (fun z _ => ?_)
      · exact ((h𝓛d.pow 2).neg.div_const 2).mul
          (differentiableOn_id.sub (differentiableOn_const 2))
      · rw [mul_div_assoc]
    have hser5d : DifferentiableOn ℂ
        (fun w : ℂ => Work.CPull.evp ((Submission.CDTPlan.pureB 5).subst Submission.CDT.sympY) w)
        (S ∩ Metric.ball 0 1) := by
      obtain ⟨C, hC, k, hk⟩ := pureB_subst_poly_growth 5
      exact (differentiableOn_evp_of_poly_growth hC hk).mono Set.inter_subset_right
    have hode5 : ∀ z ∈ S ∩ Metric.ball 0 1,
        HasDerivAt (fun w : ℂ => Work.CPull.evp
            ((Submission.CDTPlan.pureB 5).subst Submission.CDT.sympY) w)
          ((0 : ℂ) * (Work.CPull.evp
              ((Submission.CDTPlan.pureB 5).subst Submission.CDT.sympY) z)
            + (-(𝓛 z) ^ 2 / 2 * ((z - 2) / (z * (z - 1))))) z := by
      intro z hz
      have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
      have h := deriv_evp_pureB5 z hzlt (hz0ne z hz.1)
      refine h.congr_deriv ?_
      rw [h𝓛eq z hz]
      ring
    obtain ⟨F, hFd, -, hFeq⟩ := cont_of_convex_ode hSc hSo (differentiableOn_const 0) hcoef5
      hser5d hode5 hz₀
    exact ⟨F, hFd, fun z hz => by
      show F z = ∑' k : ℕ, ((PowerSeries.coeff k
          ((Submission.CDTPlan.pureB 5).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k
      exact hFeq z hz⟩
  · -- ## `B₇ ∘ y = ∫ (B₄∘y)·y'/y`
    have hcoef6 : DifferentiableOn ℂ
        (fun z : ℂ => ((z - 2) ^ 2 / (z - 1) ^ 2) * M z) S := by
      have hnum : DifferentiableOn ℂ (fun z : ℂ => (z - 2) ^ 2 * M z) S :=
        ((differentiableOn_id.sub (differentiableOn_const 2)).pow 2).mul hMd
      have hinv : DifferentiableOn ℂ (fun z : ℂ => ((z - 1) ^ 2)⁻¹) S :=
        differentiableOn_inv_sub_one_sq h1
      refine (hnum.mul hinv).congr (fun z _ => ?_)
      rw [Pi.mul_apply, div_eq_mul_inv]
      ring
    have hser6d : DifferentiableOn ℂ
        (fun w : ℂ => Work.CPull.evp ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) w)
        (S ∩ Metric.ball 0 1) := by
      obtain ⟨C, hC, k, hk⟩ := pureB_subst_poly_growth 6
      exact (differentiableOn_evp_of_poly_growth hC hk).mono Set.inter_subset_right
    have hode6 : ∀ z ∈ S ∩ Metric.ball 0 1,
        HasDerivAt (fun w : ℂ => Work.CPull.evp
            ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) w)
          ((0 : ℂ) * (Work.CPull.evp
              ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) z)
            + ((z - 2) ^ 2 / (z - 1) ^ 2) * M z) z := by
      intro z hz
      have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.2
      have h := deriv_evp_pureB6 z hzlt (hz0ne z hz.1)
      refine h.congr_deriv ?_
      rw [hMeq z hz]
      ring
    obtain ⟨F, hFd, -, hFeq⟩ := cont_of_convex_ode hSc hSo (differentiableOn_const 0) hcoef6
      hser6d hode6 hz₀
    exact ⟨F, hFd, fun z hz => by
      show F z = ∑' k : ℕ, ((PowerSeries.coeff k
          ((Submission.CDTPlan.pureB 6).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k
      exact hFeq z hz⟩

/-- The seven pure pullbacks extend analytically from the unit disc to the two half-planes `SU`
and `SL` (minus the point `2`, which lies in `SU` and is the apparent singularity of the underlying
first-order equations).  Concretely: for each `j : Fin 7` there is a function holomorphic on
`SU \ {2}` (resp. `SL \ {2}`) that agrees with the sum `Σ_k [x^k]((pureB j).subst sympY) · z^k`
of the substituted series (`Work.C17.Bsubst_differentiableOn`: holomorphic on `Metric.ball 0 1`)
wherever both are defined.

Route: the seven substituted series satisfy explicit first-order equations in `x`
(`Work.C7.B2sub_ode`, `Work.C7.B3sub_ode`, `Work.C7.B4sub_ode`, `Work.C7.J_ode`, and the
`B6_deriv`/`B7_deriv` companions), whose leading coefficients vanish at `0` and `2` and whose
other singularities are `1` (none of these lie in `SU ∪ SL` except `2`); the practical route is the
explicit closed forms (`Work.C7.g_form`: `B₂∘y = 2y − w·log(1−x)`, `B₃∘y = −log(1−x)²/2`,
`B₄∘y = (x−φ)(2Li₂ + ½log(1−x)²)`, `B₅∘y = (x/(x−1))·J`) together with the continuation of the
elementary functions involved.  `2` is in fact an apparent singularity (a `y`-exponent `1/2` at
`y = 4` becomes `(x−2)^{2α}` with `2α` an odd integer, hence single-valued), so extending across
`2` as well is enough for the stated claim.  Helpers: `Work.C17g.linear_ode_convex`,
`Work.A14D.convex_SU`, `Work.A14D.convex_SL`, `Work.A14D.PZ_ne_zero_of_mem_SU`. -/
theorem pure_pullback_cont (j : Fin 7) :
    (∃ F : ℂ → ℂ, DifferentiableOn ℂ F (SU \ ({2} : Set ℂ)) ∧
      ∀ z ∈ (SU \ ({2} : Set ℂ)) ∩ Metric.ball 0 1, F z = ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k) ∧
    (∃ F : ℂ → ℂ, DifferentiableOn ℂ F (SL \ ({2} : Set ℂ)) ∧
      ∀ z ∈ (SL \ ({2} : Set ℂ)) ∩ Metric.ball 0 1, F z = ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k) := by
  constructor
  · obtain ⟨F, hFd, hFeq⟩ :=
      cont_half isOpen_SU_H_cont convex_SU one_notMem_SU zero_notMem_SU I_half_mem_SU j
    exact ⟨F, hFd.mono Set.sdiff_subset, fun z hz => hFeq z ⟨hz.1.1, hz.2⟩⟩
  · obtain ⟨F, hFd, hFeq⟩ :=
      cont_half isOpen_SL_H_cont convex_SL one_notMem_SL zero_notMem_SL neg_I_half_mem_SL j
    exact ⟨F, hFd.mono Set.sdiff_subset, fun z hz => hFeq z ⟨hz.1.1, hz.2⟩⟩

end

end Work.A14D
