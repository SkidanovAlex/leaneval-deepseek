import Mathlib
import Submission.Work.BourgainPlan.Maximal.dilation_hl
import Submission.Work.BourgainPlan.Maximal.deriv_weight_ge_one
import Submission.Work.BourgainPlan.Maximal.strictMonoOn_eval_of_deriv_lower
import Submission.Work.BourgainPlan.Maximal.dilation_const_bound

open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-- The substitution estimate for the polynomial average.  Under the growth bounds of
`tail_le_hlMax`, the integral of `ψ (x - q u)` over `(U,N]` is dominated by the constant
`C₀^((d-1)/d)/c` times the integral of `ψ (x - v) v^(1/d - 1)` over `(0, q N]`.

This is the change of variables `v = q u`: on `(U,N]` the polynomial `q` is strictly increasing,
`q u > 0`, and its derivative dominates `c (q u / C₀)^((d-1)/d)`, which is exactly the reciprocal
of the substitution density `v ↦ v^(1/d-1)` up to the constant displayed. -/
private theorem poly_weight_substitution
    (q : Polynomial ℝ) {U c C₀ : ℝ} (hU : 1 ≤ U) (hc : 0 < c) (hC₀ : 0 < C₀)
    (hd : 0 < q.natDegree)
    (hderiv : ∀ u : ℝ, U ≤ u → c * u ^ (q.natDegree - 1) ≤ q.derivative.eval u)
    (hupper : ∀ u : ℝ, U ≤ u → q.eval u ≤ C₀ * u ^ q.natDegree)
    (hnn : ∀ u : ℝ, U ≤ u → 0 ≤ q.eval u)
    {N : ℝ} (hUN : U ≤ N) (ψ : ℝ → ℝ≥0∞) (x : ℝ) :
    ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
      ≤ ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * ∫⁻ v in Set.Ioc 0 (q.eval N),
              ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v) := by
  have hmono : StrictMonoOn (fun u : ℝ => q.eval u) (Set.Ici U) :=
    strictMonoOn_eval_of_deriv_lower q hU hc hderiv
  have hq'pos : ∀ u : ℝ, U ≤ u → 0 < q.derivative.eval u := by
    intro u hu
    have h1 : (1:ℝ) ≤ u ^ (q.natDegree - 1) := one_le_pow₀ (le_trans hU hu)
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    linarith [hderiv u hu]
  have hA : ∀ u : ℝ, U ≤ u → 0 < q.eval u →
      1 ≤ q.derivative.eval u * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1) :=
    fun u hu hqu => deriv_weight_ge_one q hU hc hC₀ hd hderiv hupper hu hqu
  have hInj : Set.InjOn (fun u : ℝ => q.eval u) (Set.Ioc U N) :=
    hmono.injOn.mono (fun u hu => Set.mem_Ici.mpr (le_of_lt hu.1))
  have hderivWithin : ∀ u ∈ Set.Ioc U N,
      HasDerivWithinAt (fun u : ℝ => q.eval u) (q.derivative.eval u) (Set.Ioc U N) u :=
    fun u _ => (Polynomial.hasDerivAt q u).hasDerivWithinAt
  have himg : (fun u : ℝ => q.eval u) '' Set.Ioc U N ⊆ Set.Ioc 0 (q.eval N) := by
    rintro v ⟨u, hu, rfl⟩
    have huU : U ≤ u := le_of_lt hu.1
    refine ⟨?_, ?_⟩
    · have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr huU) hu.1
      have h0 := hnn U le_rfl
      linarith
    · exact hmono.monotoneOn (Set.mem_Ici.mpr huU) (Set.mem_Ici.mpr hUN) hu.2
  have hpt : ∀ u ∈ Set.Ioc U N, ψ (x - q.eval u) ≤ ENNReal.ofReal |q.derivative.eval u|
      * (ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * (ENNReal.ofReal ((q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - q.eval u))) := by
    intro u hu
    have huU : U ≤ u := le_of_lt hu.1
    have hqu : 0 < q.eval u := by
      have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr huU) hu.1
      have h0 := hnn U le_rfl
      linarith
    have hKpos : 0 < C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c := by
      apply div_pos _ hc; exact Real.rpow_pos_of_pos hC₀ _
    have hkey : 1 ≤ |q.derivative.eval u|
        * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
        * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1) := by
      rw [abs_of_pos (hq'pos u huU)]
      exact hA u huU hqu
    have hofA : ENNReal.ofReal
          (|q.derivative.eval u| * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1))
        = ENNReal.ofReal |q.derivative.eval u|
            * ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * ENNReal.ofReal ((q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hKpos.le), ENNReal.ofReal_mul (abs_nonneg _)]
    have hreassoc : ENNReal.ofReal |q.derivative.eval u|
        * (ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * (ENNReal.ofReal ((q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - q.eval u)))
        = ENNReal.ofReal |q.derivative.eval u|
          * ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * ENNReal.ofReal ((q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - q.eval u) := by
      ring
    have h1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal (|q.derivative.eval u|
        * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
        * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hkey
    rw [hreassoc, ← hofA]
    calc ψ (x - q.eval u) = 1 * ψ (x - q.eval u) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (|q.derivative.eval u|
            * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - q.eval u) :=
          mul_le_mul_left h1 _
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Ioc U N) measurableSet_Ioc
      hderivWithin hInj (fun v : ℝ =>
        ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * (ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v)))
  calc ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
      ≤ ∫⁻ u in Set.Ioc U N, ENNReal.ofReal |q.derivative.eval u|
          * (ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
              * (ENNReal.ofReal ((q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - q.eval u))) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ∫⁻ v in (fun u : ℝ => q.eval u) '' Set.Ioc U N,
          ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * (ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v)) := hchange.symm
    _ ≤ ∫⁻ v in Set.Ioc 0 (q.eval N),
          ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
            * (ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v)) :=
        lintegral_mono_set himg
    _ = ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * ∫⁻ v in Set.Ioc 0 (q.eval N),
              ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The tail of the polynomial average: if `q` is nonnegative on `[U,∞)` and its derivative grows at least like `c * u^(d-1)` while `q u ≤ C₀ * u^d` there, then the integral over `(U,N]` is at most `C * N` times the Hardy–Littlewood maximal function at `x` (i.e. of the size of the number of terms, no logarithmic loss).  HINT: decompose `(U,N]` into the dyadic blocks `(2^k, 2^(k+1)] ∩ (U,N]`; on such a block `q' ≥ c*2^(k(d-1))`, so the change of variables (`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) bounds the block integral by `(1/(c*2^(k(d-1)))) * ∫⁻ v in (0, q(2^(k+1))], ψ (x-v)`, and the latter is at most `q (2^(k+1)) * hlMax ψ x ≤ C₀ * 2^((k+1)d) * hlMax ψ x` using the definition of `Commons.Analysis.Maximal.hlMax` (or `Commons.Analysis.Maximal.hlMax_le_of_mem` from `Submission.Commons.Analysis.Maximal.real_maximal_strong_type`); the geometric sum over the blocks is `≤ C * N`. -/
theorem tail_le_hlMax (q : Polynomial ℝ) {U c C₀ : ℝ} (hU : 1 ≤ U) (hc : 0 < c)
    (hC₀ : 0 < C₀)
    (hderiv : ∀ u : ℝ, U ≤ u → c * u ^ (q.natDegree - 1) ≤ q.derivative.eval u)
    (hupper : ∀ u : ℝ, U ≤ u → q.eval u ≤ C₀ * u ^ q.natDegree)
    (hnn : ∀ u : ℝ, U ≤ u → 0 ≤ q.eval u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ENNReal), Measurable ψ → ∀ N x : ℝ, U ≤ N →
      ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
        ≤ ENNReal.ofReal (C * N) * Commons.Analysis.Maximal.hlMax ψ x := by
  by_cases hd0 : q.natDegree = 0
  · exfalso
    have hder : q.derivative = 0 := Polynomial.derivative_eq_zero.mpr hd0
    have h := hderiv U le_rfl
    rw [hder] at h
    simp only [Polynomial.eval_zero] at h
    rw [hd0] at h
    simp at h
    linarith
  · have hd : 0 < q.natDegree := Nat.pos_of_ne_zero hd0
    refine ⟨2 * (q.natDegree : ℝ) * C₀ / c, by positivity, ?_⟩
    intro ψ hψ N x hUN
    have hmono : StrictMonoOn (fun u : ℝ => q.eval u) (Set.Ici U) :=
      strictMonoOn_eval_of_deriv_lower q hU hc hderiv
    have hNpos : 0 < N := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hU) hUN
    by_cases hNU : N = U
    · subst hNU
      rw [Set.Ioc_self]
      simp
    · have hNU' : U < N := lt_of_le_of_ne hUN (Ne.symm hNU)
      have hqNpos : 0 < q.eval N := by
        have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hUN) hNU'
        have h0 := hnn U le_rfl
        linarith
      have hconst := dilation_const_bound q hc hC₀ hd hNpos (hupper N hUN) hqNpos
      have hKnn : 0 ≤ C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c :=
        (div_pos (Real.rpow_pos_of_pos hC₀ _) hc).le
      calc ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
          ≤ ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
              * ∫⁻ v in Set.Ioc 0 (q.eval N),
                  ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) * ψ (x - v) :=
              poly_weight_substitution q hU hc hC₀ hd hderiv hupper hnn hUN ψ x
        _ = ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
              * ∫⁻ v in Set.Ioc 0 (q.eval N),
                  ψ (x - v) * ENNReal.ofReal (v ^ ((q.natDegree : ℝ)⁻¹ - 1)) := by
              congr 1
              apply lintegral_congr
              intro v
              ring
        _ ≤ ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
              * (ENNReal.ofReal (2 * ((q.natDegree : ℝ) * (q.eval N) ^ ((q.natDegree : ℝ)⁻¹)))
                  * Commons.Analysis.Maximal.hlMax ψ x) :=
              mul_le_mul_right (dilation_weight_le_hlMax q.natDegree hd ψ hψ hqNpos x) _
        _ = ENNReal.ofReal (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c
              * (2 * ((q.natDegree : ℝ) * (q.eval N) ^ ((q.natDegree : ℝ)⁻¹))))
              * Commons.Analysis.Maximal.hlMax ψ x := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hKnn]
        _ ≤ ENNReal.ofReal (2 * (q.natDegree : ℝ) * C₀ / c * N)
              * Commons.Analysis.Maximal.hlMax ψ x :=
              mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) (Commons.Analysis.Maximal.hlMax ψ x)

end Work.BourgainPlan.Maximal
