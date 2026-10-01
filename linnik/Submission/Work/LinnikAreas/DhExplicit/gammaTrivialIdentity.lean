import Mathlib
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

namespace Work.LinnikAreas.DhExplicit

open Filter
open scoped Topology

set_option maxHeartbeats 0

/-! ## Auxiliary lemmas for the `Γ`-part of the differentiated explicit formula -/

/-- `logDeriv Γ_ℝ s = -(1/2) log π + (1/2) ψ(s/2)` on the right half-plane, where `ψ = digamma`.
Follows from `logDeriv_GammaR_off_pole` (the `Γ_ℝ` is the "real" archimedean factor
`π^{-s/2} Γ(s/2)`). -/
private lemma aux_logDeriv_GammaR_eq {z : ℂ} (hz : 0 < z.re) :
    logDeriv Complex.Gammaℝ z
      = -(1/2 : ℂ) * Complex.log (Real.pi : ℂ) + (1/2 : ℂ) * Complex.digamma (z / 2) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z (fun m hm => by
    have h1 : (z / 2).re = -((m : ℝ)) := by rw [hm]; simp
    have h2 : 0 < (z / 2).re := by rw [Complex.div_re]; simp; linarith
    rw [h1] at h2
    have hm' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)
  rw [h]; ring

/-- The halving chain rule for the iterated derivatives of `ψ = Complex.digamma`:
`(ψ(·/2))^{(n)}(s) = 2^{-n} ψ^{(n)}(s/2)` for `Re s > 0`. -/
private lemma aux_chain (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv n (fun z : ℂ => Complex.digamma (z / 2)) s
      = (1/2 : ℂ)^n * iteratedDeriv n Complex.digamma (s / 2) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hU : IsOpen U := by rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hs
  have huniq : UniqueDiffOn ℂ U := hU.uniqueDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => (1/2) * x) U U := by
    intro x hx
    rw [hUdef] at hx ⊢
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Complex.mul_re]
    norm_num
    linarith
  have hdG : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    rw [hUdef] at hz
    simp only [Set.mem_setOf_eq] at hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre : z.re = -((m:ℝ)) := by have := congrArg Complex.re hm; simpa using this
    have hlt : (0:ℝ) < -((m:ℝ)) := by rw [← hre]; exact hz
    have hle : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hdD : DifferentiableOn ℂ (deriv Complex.Gamma) U := hdG.deriv hU
  have hne : ∀ z ∈ U, Complex.Gamma z ≠ 0 := by
    intro z hz; rw [hUdef] at hz; simp only [Set.mem_setOf_eq] at hz
    exact Complex.Gamma_ne_zero_of_re_pos hz
  have hquot : DifferentiableOn ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) U :=
    hdD.div hdG hne
  have hdig : DifferentiableOn ℂ Complex.digamma U :=
    hquot.congr (fun z hz => by simp [Complex.digamma_def, logDeriv_apply])
  have hcont : ContDiffOn ℂ (↑n) Complex.digamma U := DifferentiableOn.contDiffOn hdig hU
  have hcomp := iteratedDerivWithin_comp_const_smul (s := U) (x := s) hsU huniq
    (f := Complex.digamma) hcont (1/2 : ℂ) hmaps
  have hfun : Set.EqOn (fun z : ℂ => Complex.digamma (z/2))
      (fun x : ℂ => Complex.digamma ((1/2) * x)) U :=
    fun z hz => by congr 1; ring_nf
  rw [← iteratedDerivWithin_of_isOpen hU hsU (n := n) (f := fun z : ℂ => Complex.digamma (z/2))]
  rw [(iteratedDerivWithin_congr hfun) hsU]
  rw [hcomp]
  rw [show (1/2 : ℂ) * s = s/2 by ring_nf]
  have hs2U : s/2 ∈ U := by
    rw [hUdef]; simp only [Set.mem_setOf_eq]; rw [Complex.div_re]; simp; linarith
  rw [iteratedDerivWithin_of_isOpen hU hs2U (n := n) (f := Complex.digamma)]
  rw [smul_eq_mul]

/-- Termwise rescaling `(1/(s/2+n))^{2j} = 2^{2j} (1/(s+2n))^{2j}` for `Re s > 0`. -/
private lemma aux_term (j : ℕ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (1 / (s/2 + (n:ℂ)))^(2*j) = 2^(2*j) * (1 / (s + ((2*n:ℕ):ℂ)))^(2*j) := by
  have h2n : ((2*n:ℕ):ℂ) = 2 * (n:ℂ) := by push_cast; ring
  rw [h2n]
  have hb : s + 2 * (n:ℂ) ≠ 0 := by
    intro h
    have hr : (s + 2 * (n:ℂ)).re = 0 := by rw [h]; simp
    have hpos : 0 < (s + 2 * (n:ℂ)).re := by
      rw [Complex.add_re]
      have h2 : (2 * (n:ℂ)).re = 2 * (n:ℝ) := by simp
      rw [h2]; positivity
    linarith
  have h1 : 1 / (s/2 + (n:ℂ)) = 2 * (1 / (s + 2*(n:ℂ))) := by
    rw [show s/2 + (n:ℂ) = (s + 2*(n:ℂ))/2 by ring]
    field_simp
  rw [h1, mul_pow]

/-- The `tsum` form of the rescaling. -/
private lemma aux_tsum (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∑' n : ℕ, (1 / (s/2 + (n:ℂ)))^(2*j))
      = 2^(2*j) * ∑' n : ℕ, (1 / (s + ((2*n:ℕ):ℂ)))^(2*j) := by
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => aux_term j hs n)

/-- The digamma recurrence in the form needed: `1/z + logDeriv Γ_ℝ z = logDeriv Γ_ℝ (z+2)`. -/
private lemma aux_rec {z : ℂ} (hz : 0 < z.re) :
    1 / z + logDeriv Complex.Gammaℝ z = logDeriv Complex.Gammaℝ (z + 2) := by
  have hz2 : (0:ℝ) < (z+2).re := by rw [Complex.add_re]; norm_num; linarith
  rw [aux_logDeriv_GammaR_eq hz, aux_logDeriv_GammaR_eq hz2]
  have hrec := Complex.digamma_apply_add_one (z/2) (by
    intro m hm
    have hre : (z/2).re = -((m:ℝ)) := by have := congrArg Complex.re hm; simpa using this
    have h2 : 0 < (z/2).re := by rw [Complex.div_re]; simp; linarith
    rw [hre] at h2
    have hm' : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith)
  have harg : (z+2)/2 = z/2 + 1 := by ring
  rw [harg, hrec]
  field_simp
  ring

/-! ## The theorem -/

/-- The `Γ`-part of the differentiated explicit formula, in the form needed for the
Deuring--Heilbronn argument: for `j ≥ 1`, `Re s > 0` and `k = 2j-1`,

* `Σ'_n (s+2n)^{-2j}` and `Σ'_n (s+2+2n)^{-2j}` are summable;
* `(logDeriv Γ_ℝ)^{(k)}(s) = k! · Σ'_n (s+2n)^{-2j}`;
* `(1/· + logDeriv Γ_ℝ)^{(k)}(s) = k! · Σ'_n (s+2+2n)^{-2j}`.

PROOF ROUTE: (i) `logDeriv Γ_ℝ s = -(1/2) log π + (1/2) ψ(s/2)` where `ψ = Complex.digamma`
(from `Complex.Gammaℝ_def : Γ_ℝ s = π^{-s/2} Γ(s/2)`, `logDeriv_mul`, `logDeriv_exp`,
`Complex.cpow_def_of_ne_zero`, `Complex.digamma_def : digamma = logDeriv Gamma`).
(ii) `iteratedDeriv n (fun z => ψ (z/2)) s = (1/2)^n * ψ^{(n)}(s/2)`: apply the Mathlib lemma
`iteratedDerivWithin_comp_const_smul` on the open right half-plane `U = {Re > 0}` (with
`ContDiffOn` from `DifferentiableOn.contDiffOn`, `AnalyticAt.contDiffAt`,
`Complex.Gamma_ne_zero_of_re_pos`, `AnalyticAt.deriv`) and transfer with
`iteratedDerivWithin_of_isOpen`.
(iii) the *proved* Hurwitz series `Work.LinnikAreas.FarRepel.digammaDerivSeries (m := 2j-1)` at
`w = s/2` (it is a `HasSum`, and `m` is odd so the sign is `+1`), followed by the reindexing
`(s/2+n)^{-2j} = 2^{2j}(s+2n)^{-2j}` (via `tsum_mul_left`).  (The constants work out because
`(1/2)·(1/2)^{2j-1}·2^{2j} = 1`.)
(iv) the third identity: `1/z + logDeriv Γ_ℝ z = logDeriv Γ_ℝ (z+2)`.  Indeed, by the digamma
recurrence `Complex.digamma_apply_add_one` at `w = z/2` one has `ψ(z/2+1) = ψ(z/2) + 2/z`, i.e.
`(1/2)ψ((z+2)/2) = (1/2)ψ(z/2) + 1/z`, and `logDeriv Γ_ℝ (z+2) = -(1/2)log π + (1/2)ψ((z+2)/2)`.
Combined with the second identity evaluated at `s+2` (or with `iteratedDeriv_comp_add_const`),
this gives the stated series `Σ'_n (s+2+2n)^{-2j}`. -/
theorem gammaTrivialIdentity (j : ℕ) (hj : 1 ≤ j) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (2 * j)) ∧
    Summable (fun n : ℕ => (1 / (s + 2 + ((2 * n : ℕ) : ℂ))) ^ (2 * j)) ∧
    iteratedDeriv (2 * j - 1) (logDeriv Complex.Gammaℝ) s
      = ((2 * j - 1).factorial : ℂ) * ∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (2 * j) ∧
    iteratedDeriv (2 * j - 1) (fun z : ℂ => 1 / z + logDeriv Complex.Gammaℝ z) s
      = ((2 * j - 1).factorial : ℂ) * ∑' n : ℕ, (1 / (s + 2 + ((2 * n : ℕ) : ℂ))) ^ (2 * j) := by
  have hk : 1 ≤ 2 * j - 1 := by omega
  have hk1 : 2 * j - 1 + 1 = 2 * j := by omega
  -- the statement for an arbitrary right-half-plane point `w`
  have key : ∀ {w : ℂ}, 0 < w.re →
      Summable (fun n : ℕ => (1 / (w + ((2 * n : ℕ) : ℂ))) ^ (2 * j)) ∧
      iteratedDeriv (2 * j - 1) (logDeriv Complex.Gammaℝ) w
        = ((2 * j - 1).factorial : ℂ) * ∑' n : ℕ, (1 / (w + ((2 * n : ℕ) : ℂ))) ^ (2 * j) := by
    intro w hw
    have hw2 : 0 < (w / 2).re := by rw [Complex.div_re]; simp; linarith
    have hser := Work.LinnikAreas.FarRepel.digammaDerivSeries (2 * j - 1) hk hw2
    set T : ℂ := ∑' n : ℕ, (1 / (w + ((2 * n : ℕ) : ℂ))) ^ (2 * j) with hT
    have hpow : (-1 : ℂ) ^ (2 * j - 1 + 1) = 1 := by
      rw [hk1, Even.neg_one_pow (even_two_mul j)]
    have hfac : ((2 * j - 1).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j - 1)
    -- summability of `∑ (1/(w/2+n))^{2j}`
    have hs1 : Summable (fun n : ℕ =>
        ((2 * j - 1).factorial : ℂ) * (1 / (w / 2 + (n : ℂ))) ^ (2 * j)) :=
      hser.summable.congr (fun n => by rw [hpow, hk1, one_mul])
    have hs2 : Summable (fun n : ℕ => (1 / (w / 2 + (n : ℂ))) ^ (2 * j)) :=
      (hs1.mul_left (((2 * j - 1).factorial : ℂ))⁻¹).congr
        (fun n => by rw [← mul_assoc, inv_mul_cancel₀ hfac, one_mul])
    have hsummable : Summable (fun n : ℕ => (1 / (w + ((2 * n : ℕ) : ℂ))) ^ (2 * j)) :=
      ((hs2.congr (fun n => aux_term j hw n)).mul_left ((2 : ℂ) ^ (2 * j))⁻¹).congr
        (fun n => by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℂ) ≠ 0)), one_mul])
    -- the value of the series
    have hdig : iteratedDeriv (2 * j - 1) Complex.digamma (w / 2)
        = ((2 * j - 1).factorial : ℂ) * 2 ^ (2 * j) * T := by
      rw [← hser.tsum_eq]
      rw [tsum_congr (fun n => by rw [hpow, hk1, one_mul])]
      rw [tsum_mul_left, aux_tsum j hw, ← hT]
      ring
    have hchain : iteratedDeriv (2 * j - 1) (fun z : ℂ => Complex.digamma (z / 2)) w
        = (1 / 2 : ℂ) ^ (2 * j - 1) * iteratedDeriv (2 * j - 1) Complex.digamma (w / 2) :=
      aux_chain (2 * j - 1) hw
    have hev : logDeriv Complex.Gammaℝ =ᶠ[𝓝 w]
        (fun z : ℂ => -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)
          + (1 / 2 : ℂ) * Complex.digamma (z / 2)) := by
      have hop : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hop.mem_nhds hw] with z hz
      exact aux_logDeriv_GammaR_eq hz
    have hstep : iteratedDeriv (2 * j - 1) (logDeriv Complex.Gammaℝ) w
        = (1 / 2 : ℂ) * iteratedDeriv (2 * j - 1)
            (fun z : ℂ => Complex.digamma (z / 2)) w := by
      rw [hev.iteratedDeriv_eq (2 * j - 1)]
      rw [iteratedDeriv_const_add (c := -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ))
        (by omega : 0 < 2 * j - 1)]
      rw [iteratedDeriv_const_mul_field]
    refine ⟨hsummable, ?_⟩
    rw [hstep, hchain, hdig]
    have hA : (1 / 2 : ℂ) * (1 / 2) ^ (2 * j - 1) = (1 / 2) ^ (2 * j) := by
      rw [mul_comm, ← pow_succ, hk1]
    have hB : (1 / 2 : ℂ) ^ (2 * j) * (2 : ℂ) ^ (2 * j) = 1 := by
      rw [← mul_pow]; norm_num
    calc (1 / 2 : ℂ) * ((1 / 2) ^ (2 * j - 1) *
            (((2 * j - 1).factorial : ℂ) * (2 : ℂ) ^ (2 * j) * T))
        = ((1 / 2) * (1 / 2) ^ (2 * j - 1)) *
            (((2 * j - 1).factorial : ℂ) * (2 : ℂ) ^ (2 * j) * T) := by ring
      _ = (1 / 2) ^ (2 * j) * (((2 * j - 1).factorial : ℂ) * (2 : ℂ) ^ (2 * j) * T) := by
            rw [hA]
      _ = ((2 * j - 1).factorial : ℂ) *
            (((1 / 2) ^ (2 * j) * (2 : ℂ) ^ (2 * j)) * T) := by ring
      _ = ((2 * j - 1).factorial : ℂ) * (1 * T) := by rw [hB]
      _ = ((2 * j - 1).factorial : ℂ) * T := by ring
  obtain ⟨hsum1, hident1⟩ := key hs
  have hs2pos : (0:ℝ) < (s + 2).re := by rw [Complex.add_re]; norm_num; linarith
  obtain ⟨hsum2, hident2⟩ := key hs2pos
  refine ⟨hsum1, hsum2, hident1, ?_⟩
  have hev2 : (fun z : ℂ => 1 / z + logDeriv Complex.Gammaℝ z)
      =ᶠ[𝓝 s] (fun z : ℂ => logDeriv Complex.Gammaℝ (z + 2)) := by
    have hop : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hop.mem_nhds hs] with z hz
    exact aux_rec hz
  rw [hev2.iteratedDeriv_eq (2 * j - 1),
    iteratedDeriv_comp_add_const (2 * j - 1) (logDeriv Complex.Gammaℝ) 2]
  exact hident2

end Work.LinnikAreas.DhExplicit
