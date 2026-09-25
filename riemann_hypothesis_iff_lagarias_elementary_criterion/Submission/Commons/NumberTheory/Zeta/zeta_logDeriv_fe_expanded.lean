import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.LogDeriv

open scoped Real Topology
open Complex Filter

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- `1 - s ≠ 1` is equivalent to `s ≠ 0`. -/
private lemma one_sub_ne_one_iff (s : ℂ) : (1 : ℂ) - s ≠ 1 ↔ s ≠ 0 := by
  constructor
  · intro h hs0
    apply h
    rw [hs0]
    simp
  · intro hs0 h
    apply hs0
    have h2 : (1 : ℂ) - s - 1 = 0 := by rw [h]; simp
    have hs' : -s = 0 := by simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2
    exact neg_eq_zero.mp hs'

/-- The functional equation `ζ(s) = 2 (2π)^(-(1-s)) Γ(1-s) cos(π(1-s)/2) ζ(1-s)`
at a single point (a specialisation of `riemannZeta_one_sub`). -/
private lemma zeta_fe_point {s : ℂ} (hΓ : ∀ n : ℕ, 1 - s ≠ -↑n) (hs0 : s ≠ 0) :
    riemannZeta s = 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) * Gamma (1 - s) *
      cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) := by
  have hF := riemannZeta_one_sub (s := (1 : ℂ) - s) hΓ ((one_sub_ne_one_iff s).mpr hs0)
  have harg : (1 : ℂ) - ((1 : ℂ) - s) = s := by ring
  rw [harg] at hF
  simpa using hF

theorem zeta_logDeriv_fe_expanded {s : ℂ}
    (hζs : riemannZeta s ≠ 0) (hζw : riemannZeta (1 - s) ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓ : ∀ n : ℕ, 1 - s ≠ -↑n)
    (hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
  let A : ℂ → ℂ := fun t => 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - t))) * Gamma (1 - t) *
      cos (↑Real.pi * (1 - t) / 2) * riemannZeta (1 - t)
  -- (0) zeta agrees with A on a neighbourhood of s
  have hΓd : DifferentiableAt ℂ (fun t : ℂ => Gamma (1 - t)) s := by
    exact (Complex.differentiableAt_Gamma (1 - s) hΓ).comp s (by fun_prop)
  have hΓne0 : Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hΓ
  have hΓev : ∀ᶠ t in 𝓝 s, ∀ n : ℕ, (1 : ℂ) - t ≠ -↑n := by
    have hne : ∀ᶠ z in 𝓝 s, Gamma (1 - z) ≠ 0 := hΓd.continuousAt.eventually_ne hΓne0
    refine hne.mono ?_
    intro t ht n hn
    exact ht (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n)
  have ht0ev : ∀ᶠ t in 𝓝 s, t ≠ 0 := by
    exact (isOpen_ne.eventually_mem hs0)
  have hζA : riemannZeta =ᶠ[𝓝 s] A := by
    filter_upwards [hΓev, ht0ev] with t hΓt ht0
    have hF := riemannZeta_one_sub (s := (1 : ℂ) - t) hΓt ((one_sub_ne_one_iff t).mpr ht0)
    have harg : (1 : ℂ) - ((1 : ℂ) - t) = t := by ring
    rw [harg] at hF
    simpa [A] using hF
  -- (1) derivative and value of zeta equal those of A at s
  have hdζA : deriv riemannZeta s = deriv A s := hζA.deriv_eq
  have hζsA : riemannZeta s = A s := by
    have hF := zeta_fe_point (s := s) hΓ hs0
    simpa [A] using hF
  -- (2) factor functions
  let p : ℂ → ℂ := fun t => (((2 * Real.pi : ℝ) : ℂ)) ^ (-(1 - t))
  let G : ℂ → ℂ := fun t => Gamma (1 - t)
  let Cfun : ℂ → ℂ := fun t => cos (↑Real.pi * (1 - t) / 2)
  let Z : ℂ → ℂ := fun t => riemannZeta (1 - t)
  have hbase0 : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact ofReal_ne_zero.mpr (by positivity)
  have h1sw : (1 : ℂ) - s ≠ 1 := (one_sub_ne_one_iff s).mpr hs0
  have hps0 : p s ≠ 0 := by
    dsimp [p]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hbase0)
  have hGs0 : G s ≠ 0 := by
    dsimp [G]
    exact Complex.Gamma_ne_zero hΓ
  have hCs0 : Cfun s ≠ 0 := by simpa [Cfun] using hcos
  have hZs0 : Z s ≠ 0 := by
    dsimp [Z]
    exact hζw
  have hdp : DifferentiableAt ℂ p s := by
    dsimp [p]
    exact DifferentiableAt.const_cpow (f := fun t : ℂ => -(1 - t)) (by fun_prop) (Or.inl hbase0)
  have hdG : DifferentiableAt ℂ G s := by
    dsimp [G]
    exact (Complex.differentiableAt_Gamma (1 - s) hΓ).comp s (by fun_prop)
  have hdC : DifferentiableAt ℂ Cfun s := by
    dsimp [Cfun]
    fun_prop
  have hdZ : DifferentiableAt ℂ Z s := by
    dsimp [Z]
    exact (differentiableAt_riemannZeta h1sw).comp s (by fun_prop)
  -- (3) individual log-derivatives
  have hldp : logDeriv p s = Complex.log (((2 * Real.pi : ℝ) : ℂ)) := by
    have hde1 : deriv (fun t : ℂ => -(1 - t)) s = 1 := by
      have h₁ : (fun t : ℂ => -(1 - t)) = (fun t : ℂ => t - 1) := by
        funext t; ring
      rw [h₁]
      simp
    have hderiv : deriv p s =
        Complex.log (((2 * Real.pi : ℝ) : ℂ)) * deriv (fun t : ℂ => -(1 - t)) s * p s := by
      dsimp [p]
      have hd := Complex.deriv_const_cpow (f := fun t : ℂ => -(1 - t)) (x := s)
        (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => -(1 - t)) s)
        (((2 * Real.pi : ℝ) : ℂ))
      simpa using hd
    calc
      logDeriv p s = deriv p s / p s := by simp [logDeriv_apply]
      _ = (Complex.log (((2 * Real.pi : ℝ) : ℂ)) * 1 * p s) / p s := by rw [hderiv, hde1]
      _ = Complex.log (((2 * Real.pi : ℝ) : ℂ)) := by field_simp [hps0]
  have hldG : logDeriv G s = -Complex.digamma (1 - s) := by
    have hdg' : deriv (fun t : ℂ => 1 - t) s = -1 := by simp [deriv_const_sub_id]
    have hld := logDeriv_comp (f := Gamma) (g := fun t : ℂ => 1 - t) (x := s)
      (Complex.differentiableAt_Gamma (1 - s) hΓ)
      (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => 1 - t) s)
    calc
      logDeriv G s = logDeriv Gamma (1 - s) * deriv (fun t : ℂ => 1 - t) s := by
        simpa only [G, Function.comp_def, Function.comp_apply] using hld
      _ = logDeriv Gamma (1 - s) * -1 := by rw [hdg']
      _ = -Complex.digamma (1 - s) := by simp [Complex.digamma_def]
  have hldC : logDeriv Cfun s = ((Real.pi / 2 : ℝ) : ℂ) * tan (↑Real.pi * (1 - s) / 2) := by
    let g : ℂ → ℂ := fun t => ↑Real.pi * (1 - t) / 2
    have hg : Cfun = cos ∘ g := by
      funext t
      simp [Cfun, g]
    have hgderiv : deriv g s = -((Real.pi : ℝ) : ℂ) / 2 := by
      have h₁ : (fun t : ℂ => ↑Real.pi * (1 - t) / 2) =
          (fun t : ℂ => (((Real.pi : ℝ) : ℂ) / 2) * (1 - t)) := by
        funext t; ring
      dsimp [g]
      rw [h₁]
      simp [deriv_const_sub_id]
      rw [neg_div]
    have hldcos : logDeriv cos (g s) = -tan (g s) := by
      have hcos' : cos (g s) ≠ 0 := by
        dsimp [g]
        simpa using hcos
      calc
        logDeriv cos (g s) = deriv cos (g s) / cos (g s) := by simp [logDeriv_apply]
        _ = (-sin (g s)) / cos (g s) := by rw [Complex.deriv_cos]
        _ = -tan (g s) := by
          rw [Complex.tan_eq_sin_div_cos]
          field_simp [hcos']
    have hld := logDeriv_comp (f := cos) (g := g) (x := s)
      (by fun_prop : DifferentiableAt ℂ cos (g s)) (by dsimp [g]; fun_prop)
    calc
      logDeriv Cfun s = logDeriv (cos ∘ g) s := by rw [hg]
      _ = logDeriv cos (g s) * deriv g s := hld
      _ = (-tan (g s)) * (-((Real.pi : ℝ) : ℂ) / 2) := by rw [hldcos, hgderiv]
      _ = ((Real.pi / 2 : ℝ) : ℂ) * tan (↑Real.pi * (1 - s) / 2) := by
        have hpi : ((Real.pi / 2 : ℝ) : ℂ) = (↑Real.pi : ℂ) / 2 := by
          norm_num [div_eq_mul_inv]
        dsimp [g]
        rw [hpi]
        ring
  have hldZ : logDeriv Z s = -(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) := by
    have hdg' : deriv (fun t : ℂ => 1 - t) s = -1 := by simp [deriv_const_sub_id]
    have hld := logDeriv_comp (f := riemannZeta) (g := fun t : ℂ => 1 - t) (x := s)
      (differentiableAt_riemannZeta h1sw)
      (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => 1 - t) s)
    calc
      logDeriv Z s = logDeriv riemannZeta (1 - s) * deriv (fun t : ℂ => 1 - t) s := by
        simpa only [Z, Function.comp_def, Function.comp_apply] using hld
      _ = logDeriv riemannZeta (1 - s) * -1 := by rw [hdg']
      _ = -(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) := by
        simp [logDeriv_apply]
  -- (4) product-rule assembly
  have hAeq : A = (fun t => (2 : ℂ) * p t * G t * Cfun t * Z t) := by
    funext t
    dsimp [A, p, G, Cfun, Z]
  have hlogA : logDeriv A s =
      Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s) := by
    let L : ℂ → ℂ := fun t => (2 : ℂ) * p t
    let N : ℂ → ℂ := fun t => L t * G t
    let M : ℂ → ℂ := fun t => N t * Cfun t
    have hLs0 : L s ≠ 0 := by
      dsimp [L]
      exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hps0
    have hNs0 : N s ≠ 0 := by
      dsimp [N]
      exact mul_ne_zero hLs0 hGs0
    have hMs0 : M s ≠ 0 := by
      dsimp [M]
      exact mul_ne_zero hNs0 hCs0
    have hdL : DifferentiableAt ℂ L s := by
      dsimp [L]
      exact (differentiableAt_const (2 : ℂ)).mul hdp
    have hdN : DifferentiableAt ℂ N s := by
      dsimp [N]
      exact hdL.mul hdG
    have hdM : DifferentiableAt ℂ M s := by
      dsimp [M]
      exact hdN.mul hdC
    have hAeq2 : A = (fun t => M t * Z t) := by
      funext t
      dsimp [A, M, N, L, p, G, Cfun, Z]
    have hchain : logDeriv A s = logDeriv p s + logDeriv G s + logDeriv Cfun s + logDeriv Z s := by
      rw [hAeq2]
      have hmul3 := logDeriv_mul (x := s) (f := M) (g := Z) hMs0 hZs0 hdM hdZ
      simp only [Pi.mul_def] at hmul3
      have hmul2 := logDeriv_mul (x := s) (f := N) (g := Cfun) hNs0 hCs0 hdN hdC
      simp only [Pi.mul_def] at hmul2
      have hmul1 := logDeriv_mul (x := s) (f := L) (g := G) hLs0 hGs0 hdL hdG
      simp only [Pi.mul_def] at hmul1
      have hconst : logDeriv (fun t : ℂ => (2 : ℂ) * p t) s = logDeriv p s := by
        exact logDeriv_const_mul s (2 : ℂ) (by norm_num)
      rw [hmul3, hmul2, hmul1, hconst]
    rw [hchain, hldp, hldG, hldC, hldZ]
    ring
  -- (5) conclusion
  calc
    deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta s := by simp [logDeriv_apply]
    _ = logDeriv A s := by
      simp [logDeriv_apply]
      rw [hdζA, hζsA]
    _ = Complex.log ((2 * Real.pi : ℝ) : ℂ) - Complex.digamma (1 - s) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan (↑Real.pi * (1 - s) / 2) -
          deriv riemannZeta (1 - s) / riemannZeta (1 - s) := hlogA

end

end Commons.NumberTheory.Zeta
