import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelJacobi
import Submission.ModelJacLin
import Submission.ModelVarConv
import Submission.ModelVarFrechet
import Mathlib

/-!
# The Fréchet derivative of the flow equals the linearized solution

Task: prove the final theorem `flow_deriv_eq_linearized`.

## Statement (in words)

Around `(x₀,v₀)` let `Φ` be the local flow (from `ModelFlowCont.flow_lipschitz` /
`ModelVarConv.variation_gateaux`), with `z₀ := (x₀,v₀)`.  From
`ModelVarFrechet.variation_frechet`, for every `t ∈ Icc (-T) T` there is a continuous linear map
`L t` with `HasFDerivAt (fun z => Φ z t) (L t) z₀`.  On the other hand, for any direction
`w : E × E`, the linearized equation along `t ↦ Φ z₀ t` with initial data `w` has a unique
solution `J` (`ModelJacobi.linearized_exists`, `ModelJacLin.linearized_unique`).

**Conclusion:** `(L t) w = J t` for all `t` where both are defined.

## Proof route

The construction in `variation_frechet` builds the derivative as the *canonical* family
`J : (E × E) → ℝ → (E × E)` of solutions of the linearized (Jacobi) equation
(`canonical_solutions` + `uniform_lin_est`): for every `t` in the (common) time window and
every direction `w`, `HasFDerivAt (fun z => Φ z t) L t z₀` with `L t w = J w t`.  Since a
`HasFDerivAt` determines the `fderiv`, we get `(fderiv ℝ (fun z => Φ z t) z₀) w = J w t`.
Finally, an arbitrary solution `J` of the linearized equation with `J 0 = w` agrees with
`J w` on the common interval by uniqueness (`linearized_unique`), so
`(fderiv ℝ (fun z => Φ z t) z₀) w = J t`.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- The Fréchet derivative of the flow w.r.t. the initial data at `z₀` is the canonical
family `J` of solutions of the linearized equation: for each time `t` (in a common window),
`HasFDerivAt (fun z => Φ z t) L z₀` where `L w = J w t`. -/
lemma flow_fderiv_canonical (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1))
    (Tj : ℝ) (hTj : 0 < Tj) (hTjTf : Tj < Tf)
    (J : (E × E) → ℝ → (E × E))
    (hJ0 : ∀ w : E × E, J w 0 = w)
    (hJd : ∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ z₀ t) (J w t)) t)
    (hJadd : ∀ t : ℝ, ∀ (a b : E × E), J (a + b) t = J a t + J b t)
    (hJsmul : ∀ t : ℝ, ∀ (a : E × E) (c : ℝ), J (c • a) t = c • J a t) :
    ∃ T > 0, T < Tf ∧ ∀ t ∈ Icc (-T) T,
      ∃ L : E × E →L[ℝ] E × E,
        HasFDerivAt (fun z => Φ z t) L z₀ ∧ ∀ w : E × E, L w = J w t := by
  rcases uniform_lin_est g hg hinv z₀ Tf hTf Lf Φ hΦ₀ hLip Tj hTj hTjTf J hJ0 hJd with
    ⟨T, hT0, hTltTf, hEst⟩
  refine ⟨T, hT0, hTltTf, ?_⟩
  intro t ht
  let L : (E × E) →ₗ[ℝ] (E × E) :=
    { toFun := fun w => J w t
      map_add' := fun a b => hJadd t a b
      map_smul' := fun c a => hJsmul t a c }
  let Lclm : (E × E) →L[ℝ] (E × E) := LinearMap.toContinuousLinearMap L
  refine ⟨Lclm, ?_, ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    rcases hEst c hc with ⟨h₀, hh₀, hEst'⟩
    let ρ : ℝ := min h₀ 1
    have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hh₀ zero_lt_one
    filter_upwards [Metric.ball_mem_nhds (0 : E × E) hρ] with v hv
    have hv_lt : ‖v‖ < ρ := by
      simpa [Real.dist_eq] using (mem_ball.mp hv)
    by_cases hv0 : v = 0
    · subst v
      have hL0 : Lclm 0 = 0 := by
        dsimp [Lclm]
        exact (L : (E × E) →ₗ[ℝ] (E × E)).map_zero
      simp [hL0]
    · have hnorm_ne : ‖v‖ ≠ 0 := by
        intro h
        exact hv0 (norm_eq_zero.mp h)
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      let w : E × E := (‖v‖⁻¹) • v
      have hw_norm : ‖w‖ ≤ 1 := by
        dsimp [w]
        have hnw : ‖(‖v‖⁻¹) • v‖ = ‖v‖⁻¹ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_of_lt hpos)]
        rw [hnw]
        have hc' : ‖v‖⁻¹ * ‖v‖ = 1 := by field_simp [hnorm_ne]
        simpa [hc']
      have hvs : v = (‖v‖ : ℝ) • w := by
        dsimp [w]
        rw [smul_smul]
        have hmul : (‖v‖ : ℝ) * (‖v‖⁻¹) = 1 := by field_simp [hnorm_ne]
        rw [hmul, one_smul]
      have hhlt : |‖v‖| < h₀ := by
        have hle : ‖v‖ < h₀ := by
          exact lt_of_lt_of_le hv_lt (min_le_left h₀ 1)
        simpa [abs_of_nonneg (le_of_lt hpos)] using hle
      have hmem : z₀ + (‖v‖ : ℝ) • w ∈ closedBall z₀ 1 := by
        rw [mem_closedBall, dist_eq_norm]
        have hle1 : ‖(‖v‖ : ℝ) • w‖ ≤ 1 := by
          have hnw : ‖(‖v‖ : ℝ) • w‖ = ‖v‖ * ‖w‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
          rw [hnw]
          have hm : ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left hw_norm (le_of_lt hpos)
          have hle2 : ‖v‖ ≤ 1 := by
            exact le_trans (le_of_lt hv_lt) (min_le_right h₀ 1)
          calc
            ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := hm
            _ = ‖v‖ := by ring
            _ ≤ 1 := hle2
        calc
          ‖(z₀ + (‖v‖ : ℝ) • w) - z₀‖ = ‖(‖v‖ : ℝ) • w‖ := by simp
          _ ≤ 1 := hle1
      have hb := hEst' w hw_norm (‖v‖) hnorm_ne hhlt hmem t ht
      have hb0 : ‖(‖v‖⁻¹) • (Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) - J w t‖ ≤ c := by
        simpa [one_div] using hb
      have hb' : ‖Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t - (‖v‖ : ℝ) • (J w t)‖ ≤ ‖v‖ * c :=
        norm_unscale_le (X := Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) (Y := J w t)
          (r := ‖v‖) (c := c) hpos hb0
      have hJv : (‖v‖ : ℝ) • (J w t) = J v t := by
        rw [← hJsmul t w (‖v‖)]
        congr 1
        exact hvs.symm
      have hb'' : ‖Φ (z₀ + v) t - Φ z₀ t - J v t‖ ≤ c * ‖v‖ := by
        rw [← hvs] at hb'
        rw [hJv] at hb'
        have hmul : ‖v‖ * c = c * ‖v‖ := by ring
        rwa [hmul] at hb'
      have hLv : Lclm v = J v t := by
        dsimp [Lclm, L]
      simpa [hLv] using hb''
  · intro u
    dsimp [Lclm, L]

/-- Uniqueness of the linearized (Jacobi) initial value problem when the base trajectory is a
solution of the geodesic first-order system directly (no `(c, vel)` splitting needed). -/
lemma jacobi_unique_along_flow (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε) (z : ℝ → E × E)
    (hz : ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (odeField g (z t)) t)
    {J₁ J₂ : ℝ → E × E} {w : E × E}
    (hJ₁ : J₁ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt J₁ ((fderiv ℝ (odeField g)) (z t) (J₁ t)) t)
    (hJ₂ : J₂ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt J₂ ((fderiv ℝ (odeField g)) (z t) (J₂ t)) t) :
    ∀ t ∈ Ioo (-ε) ε, J₁ t = J₂ t := by
  let c : ℝ → E := fun t => (z t).1
  let vel : ℝ → E := fun t => (z t).2
  have hc (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : HasDerivAt c (vel t) t := by
    have hzt := hz t ht
    have h1 : HasDerivAt (fun s => (z s).1) (odeField g (z t)).1 t := by
      have hf := hzt.hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h1
  have hv (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t := by
    have hzt := hz t ht
    have h2 : HasDerivAt (fun s => (z s).2) (odeField g (z t)).2 t := by
      have hf := hzt.hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h2
  have hJ₁' : J₁ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₁ ((fderiv ℝ (odeField g)) (c t, vel t) (J₁ t)) t := by
    constructor
    · exact hJ₁.1
    · intro t ht
      convert hJ₁.2 t ht
  have hJ₂' : J₂ 0 = w ∧ ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J₂ ((fderiv ℝ (odeField g)) (c t, vel t) (J₂ t)) t := by
    constructor
    · exact hJ₂.1
    · intro t ht
      convert hJ₂.2 t ht
  exact linearized_unique g hg hinv hε (c := c) (vel := vel) hc hv (J₁ := J₁) (J₂ := J₂)
    (w := w) hJ₁' hJ₂'

/-- The Fréchet derivative of the flow in the initial data is the solution of the linearized
equation. -/
theorem flow_deriv_eq_linearized (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) (w : E × E) :
    ∃ T > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, v₀) 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Ioo (-T) T,
         ∀ J : ℝ → E × E,
           J 0 = w →
           (∀ s ∈ Ioo (-T) T,
             HasDerivAt J ((fderiv ℝ (odeField g)) (Φ (x₀,v₀) s) (J s)) s) →
           (fderiv ℝ (fun z => Φ z t) (x₀,v₀)) w = J t) := by
  classical
  let z₀ : E × E := (x₀, v₀)
  rcases flowOnUnitBall g hg hinv z₀ with ⟨Tf, hTf, Lf, Φ, hΦF, hLipF⟩
  rcases canonical_solutions g hg hinv z₀ Tf hTf Φ hΦF with
    ⟨Tj, hTj0, hTjTf, Jc, hJc0, hJcd, hJcadd, hJcsmul⟩
  rcases flow_fderiv_canonical g hg hinv z₀ Tf hTf Lf Φ hΦF hLipF Tj hTj0 hTjTf
    Jc hJc0 hJcd hJcadd hJcsmul with ⟨T1, hT10, hT1Tf, hFd⟩
  let T : ℝ := min T1 (Tj / 2)
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_min hT10 (by positivity)
  have hTT1 : T ≤ T1 := by dsimp [T]; exact min_le_left _ _
  have hTTj2 : T ≤ Tj / 2 := by dsimp [T]; exact min_le_right _ _
  have hTltTj : T < Tj := by
    have : Tj / 2 < Tj := by linarith
    exact lt_of_le_of_lt hTTj2 this
  have hTltTf : T < Tf := lt_of_le_of_lt hTT1 hT1Tf
  have hΦ₀T : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    constructor
    · exact (hΦF z hz).1
    · intro t ht
      exact (hΦF z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
        · exact le_trans ht.2 (le_of_lt hTltTf))
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  -- for every time in the window the fderiv is given by the canonical family
  have hfderiv : ∀ t ∈ Ioo (-T) T, ∀ u : E × E,
      (fderiv ℝ (fun z => Φ z t) z₀) u = Jc u t := by
    intro t ht u
    have ht1 : t ∈ Icc (-T1) T1 := by
      constructor
      · exact le_trans (neg_le_neg hTT1) (le_of_lt ht.1)
      · exact le_trans (le_of_lt ht.2) hTT1
    rcases hFd t ht1 with ⟨L, hLfd, hLval⟩
    have h : fderiv ℝ (fun z => Φ z t) z₀ = L := hLfd.fderiv
    rw [h]
    exact hLval u
  refine ⟨T, hTpos, Φ, ?_, ?_⟩
  · -- the flow property, restated on the (smaller) window Icc (-T) T
    simpa [z₀] using hΦ₀T
  · intro t ht J hJ0' hJ'
    have hfdval : (fderiv ℝ (fun z => Φ z t) z₀) w = Jc w t := hfderiv t ht w
    -- the canonical solution agrees with J (both solve the linearized IVP with data w)
    have hbase (s : ℝ) (hs : s ∈ Ioo (-T) T) :
        HasDerivAt (fun u => Φ z₀ u) (odeField g (Φ z₀ s)) s := by
      have hsI : s ∈ Icc (-T) T := Ioo_subset_Icc_self hs
      exact (hΦ₀T z₀ hz₀mem).2 s hsI
    have hJc_w : Jc w 0 = w ∧ ∀ s ∈ Ioo (-T) T,
        HasDerivAt (Jc w) ((fderiv ℝ (odeField g)) (Φ z₀ s) (Jc w s)) s := by
      constructor
      · exact hJc0 w
      · intro s hs
        have hsj : s ∈ Ioo (-Tj) Tj := by
          constructor
          · exact lt_trans (neg_lt_neg hTltTj) hs.1
          · exact lt_trans hs.2 hTltTj
        exact hJcd w s hsj
    have hJ'z : J 0 = w ∧ ∀ s ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (Φ z₀ s) (J s)) s := by
      constructor
      · exact hJ0'
      · intro s hs
        convert hJ' s hs
    have huniq := jacobi_unique_along_flow g hg hinv (ε := T) hTpos (z := fun u => Φ z₀ u)
      (hz := hbase) (J₁ := Jc w) (J₂ := J) (w := w) hJc_w hJ'z
    have hsame : Jc w t = J t := huniq t ht
    calc
      (fderiv ℝ (fun z => Φ z t) (x₀, v₀)) w = Jc w t := by
        simpa [z₀] using hfdval
      _ = J t := hsame

end

end Submission.Model
