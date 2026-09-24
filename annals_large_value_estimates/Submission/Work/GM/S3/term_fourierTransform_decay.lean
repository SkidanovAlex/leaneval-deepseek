import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.hhat_defs
import Submission.Work.GM.S3.fourier_decay_explicit
import Submission.Work.GM.S3.phi_iteratedDeriv
import Submission.Work.GM.S3.hfun_contDiff_compactSupport

/-!
# Fourier decay of `u ↦ ψ₁ (u + w) ψ₂ u · u^{iτ}`

GM's Proposition 10.1 (and its use in §7) needs the Fourier transform of the "term"
`f_{w,τ}(u) = ψ₁(u+w) ψ₂(u) u^{iτ}` (`ψᵢ` smooth non-negative bumps, `u^{iτ} = e^{iτ log u}`) to
decay faster than any power of `1/|ξ|`, uniformly in the shift `w`:

`‖𝓕 f_{w,τ}(ξ)‖ ≤_j (1+|τ|)^j / |ξ|^j`.

Since `ψ₂` is supported in `[1/C₀, C₀]` (with `C₀ ≥ 1`), so is `f_{w,τ}`; all derivatives of the
amplitude `ψ₁(·+w) ψ₂` are bounded *uniformly in `w`* (translation does not change the successive
derivatives), and the derivatives of `u^{iτ}` are bounded by `C_j (1+|τ|)^j` on `[1/C₀,C₀]`, so the
`j`-th derivative of `f_{w,τ}` is bounded by `C_j (1+|τ|)^j`, giving the stated decay through
`Real.fourier_iteratedDeriv`.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators Topology

/-! ## The amplitude and the term -/

/-- The amplitude `u ↦ ψ₁ (u + w) * ψ₂ u`, viewed in `ℂ`. -/
noncomputable def ampC (ψ₁ ψ₂ : ℝ → ℝ) (w : ℝ) : ℝ → ℂ :=
  fun u => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ)

/-- The full term `u ↦ ψ₁ (u + w) ψ₂ u · φ_τ(u)` (`φ_τ(u) = u^{iτ}`). -/
noncomputable def term (ψ₁ ψ₂ : ℝ → ℝ) (w τ : ℝ) : ℝ → ℂ :=
  ampC ψ₁ ψ₂ w * phi τ

/-- The Leibniz constant bounding the `i`-th derivative of the amplitude. -/
noncomputable def ampBound (c₁ c₂ : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * c₁ k * c₂ (i - k)

/-- `∏_{i<k}(1+i)`, the constant coming from the derivatives of `u^{iτ}` on `u ≥ 1`. -/
noncomputable def phifact (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 + (i : ℝ))

/-- The overall constant in the pointwise derivative bound for the `j`-th derivative of the term. -/
noncomputable def Gconst (C₀ : ℝ) (c₁ c₂ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * ampBound c₁ c₂ i * (phifact (j - i) * C₀ ^ (j - i))

/-- The constant `K j` of the decay estimate. -/
noncomputable def Kconst (C₀ : ℝ) (c₁ c₂ : ℕ → ℝ) (j : ℕ) : ℝ :=
  C₀ * Gconst C₀ c₁ c₂ j / (2 * Real.pi) ^ j

/-! ## Non-negativity of the constants -/

lemma ampBound_nonneg {c₁ c₂ : ℕ → ℝ} (hc₁ : ∀ k, 0 ≤ c₁ k) (hc₂ : ∀ k, 0 ≤ c₂ k) (i : ℕ) :
    0 ≤ ampBound c₁ c₂ i := by
  rw [ampBound]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (by positivity) (hc₁ k)) (hc₂ (i - k))

lemma phifact_nonneg (k : ℕ) : 0 ≤ phifact k := by
  rw [phifact]
  exact Finset.prod_nonneg fun i _ => by positivity

lemma Gconst_nonneg {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {c₁ c₂ : ℕ → ℝ} (hc₁ : ∀ k, 0 ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k) (j : ℕ) : 0 ≤ Gconst C₀ c₁ c₂ j := by
  rw [Gconst]
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
  have h2 : 0 ≤ ampBound c₁ c₂ i := ampBound_nonneg hc₁ hc₂ i
  have h3 : 0 ≤ phifact (j - i) := phifact_nonneg _
  have h4 : (0 : ℝ) ≤ C₀ ^ (j - i) := by
    exact pow_nonneg (le_trans zero_le_one hC₀) _
  exact mul_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 h4)

lemma Kconst_nonneg {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {c₁ c₂ : ℕ → ℝ} (hc₁ : ∀ k, 0 ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k) (j : ℕ) : 0 ≤ Kconst C₀ c₁ c₂ j := by
  rw [Kconst]
  exact div_nonneg (mul_nonneg (le_trans zero_le_one hC₀) (Gconst_nonneg hC₀ hc₁ hc₂ j))
    (by positivity)

/-! ## The amplitude: smoothness, support, derivative bounds -/

/-- Successive derivatives of `u ↦ ψ₁ (u + w) ψ₂ u` are bounded uniformly in the shift `w`. -/
private lemma exists_shift_deriv_bound {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (w x : ℝ), |iteratedDeriv k (fun u : ℝ => ψ (u + w)) x| ≤ c := by
  obtain ⟨c, hc, hcb⟩ := h.2.2.2.2 k
  exact ⟨c, hc, fun w x => by
    rw [iteratedDeriv_comp_add_const k ψ w]
    exact hcb (x + w)⟩

/-- Successive derivatives of `ψ` are bounded. -/
private lemma exists_deriv_bound {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv k ψ x| ≤ c :=
  h.2.2.2.2 k

private lemma contDiff_ampC {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₁ : IsBumpAtOne ψ₁ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (w : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ampC ψ₁ ψ₂ w) := by
  have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ψ₁ (u + w) * ψ₂ u) :=
    (h₁.1.comp (contDiff_id.add contDiff_const)).mul h₂.1
  exact Complex.ofRealCLM.contDiff.comp hmul

private lemma ampC_zero_of_notMem {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₂ : IsBumpAtOne ψ₂ C₀)
    (w : ℝ) {u : ℝ} (hu : u ∉ Set.Icc (1 / C₀) C₀) : ampC ψ₁ ψ₂ w u = 0 := by
  have hz : ψ₂ u = 0 := by
    by_contra hne
    exact hu (h₂.2.2.1 u hne)
  simp [ampC, hz]

/-- Derivative bound for the amplitude, uniform in the shift. -/
private lemma norm_iteratedDeriv_ampC_le {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ}
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w : ℝ) {c₁ c₂ : ℕ → ℝ}
    (hc₁ : ∀ k, 0 ≤ c₁ k ∧ ∀ x, |iteratedDeriv k (fun u : ℝ => ψ₁ (u + w)) x| ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k ∧ ∀ x, |iteratedDeriv k ψ₂ x| ≤ c₂ k) (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (ampC ψ₁ ψ₂ w) x‖ ≤ ampBound c₁ c₂ i := by
  have hampCons : ampC ψ₁ ψ₂ w = fun y : ℝ => (((fun u : ℝ => ψ₁ (u + w) * ψ₂ u) y : ℝ) : ℂ) :=
    rfl
  rw [hampCons, iteratedDeriv_ofReal_comp i (fun u : ℝ => ψ₁ (u + w) * ψ₂ u),
    Complex.norm_real, Real.norm_eq_abs]
  have hfC : ContDiffAt ℝ ((i : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ψ₁ (u + w)) x :=
    ((h₁.1.comp (contDiff_id.add contDiff_const)).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hgC : ContDiffAt ℝ ((i : ℕ∞) : WithTop ℕ∞) ψ₂ x :=
    (h₂.1.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsplit : (fun u : ℝ => ψ₁ (u + w) * ψ₂ u) = (fun u : ℝ => ψ₁ (u + w)) * ψ₂ := rfl
  rw [hsplit, iteratedDeriv_mul hfC hgC, ampBound]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i.choose k : ℝ))]
  have h1 : |iteratedDeriv k (fun u : ℝ => ψ₁ (u + w)) x| ≤ c₁ k := (hc₁ k).2 x
  have h2 : |iteratedDeriv (i - k) ψ₂ x| ≤ c₂ (i - k) := (hc₂ (i - k)).2 x
  have hA : (0 : ℝ) ≤ (i.choose k : ℝ) := by positivity
  have hAc : (0 : ℝ) ≤ (i.choose k : ℝ) * c₁ k := mul_nonneg hA (hc₁ k).1
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (abs_nonneg _) hAc

/-! ## The oscillatory factor: derivative bound on `[1/C₀, ∞)` -/

private lemma norm_iteratedDeriv_phi_le {C₀ τ : ℝ} (hC₀ : 1 ≤ C₀) (k : ℕ) {x : ℝ}
    (hx : 1 / C₀ ≤ x) :
    ‖iteratedDeriv k (phi τ) x‖ ≤ phifact k * C₀ ^ k * (1 + |τ|) ^ k := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hxpos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hC₀pos) hx
  rw [phi_iteratedDeriv τ k hxpos, norm_mul]
  have hprod : ‖∏ i ∈ Finset.range k, (Complex.I * (τ : ℂ) - (i : ℂ))‖
      ≤ phifact k * (1 + |τ|) ^ k := by
    rw [phifact]
    refine (Finset.norm_prod_le _ _).trans ?_
    have hb : ∀ i ∈ Finset.range k,
        ‖Complex.I * (τ : ℂ) - (i : ℂ)‖ ≤ (1 + |τ|) * (1 + (i : ℝ)) := by
      intro i _
      calc ‖Complex.I * (τ : ℂ) - (i : ℂ)‖ ≤ ‖Complex.I * (τ : ℂ)‖ + ‖(i : ℂ)‖ := norm_sub_le _ _
        _ = |τ| + (i : ℝ) := by simp
        _ ≤ (1 + |τ|) * (1 + (i : ℝ)) := by
            nlinarith [abs_nonneg τ, (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
    refine (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hb).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    ring
  have hexp : ‖Complex.exp ((Complex.I * (τ : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖ ≤ C₀ ^ k := by
    rw [Complex.norm_exp]
    have hre : ((Complex.I * (τ : ℂ) - (k : ℂ)) * (Real.log x : ℂ)).re
        = -(k : ℝ) * Real.log x := by
      simp [Complex.mul_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]
    have hle : -(k : ℝ) * Real.log x ≤ (k : ℝ) * Real.log C₀ := by
      have h1 : Real.log (1 / C₀) ≤ Real.log x := Real.log_le_log (one_div_pos.mpr hC₀pos) hx
      have h1' : -Real.log C₀ ≤ Real.log x := by
        simpa [one_div, Real.log_inv] using h1
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [h1', hk, Real.log_nonneg hC₀]
    calc Real.exp (-(k : ℝ) * Real.log x) ≤ Real.exp ((k : ℝ) * Real.log C₀) :=
          Real.exp_le_exp.mpr hle
      _ = C₀ ^ k := by rw [Real.exp_nat_mul, Real.exp_log hC₀pos]
  calc ‖∏ i ∈ Finset.range k, (Complex.I * (τ : ℂ) - (i : ℂ))‖ *
        ‖Complex.exp ((Complex.I * (τ : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖
      ≤ (phifact k * (1 + |τ|) ^ k) * C₀ ^ k :=
        mul_le_mul hprod hexp (norm_nonneg _)
          (mul_nonneg (phifact_nonneg k) (by positivity))
    _ = phifact k * C₀ ^ k * (1 + |τ|) ^ k := by ring

/-! ## Vanishing of the term off the support -/

private lemma term_eventuallyEq_zero {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₂ : IsBumpAtOne ψ₂ C₀)
    (w τ : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (1 / C₀) C₀) :
    term ψ₁ ψ₂ w τ =ᶠ[𝓝 x] (0 : ℝ → ℂ) := by
  have hx' : x < 1 / C₀ ∨ C₀ < x := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    exact hx
  rcases hx' with hx | hx
  · filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hy' : y ∉ Set.Icc (1 / C₀) C₀ := fun h => absurd h.1 (not_le.mpr hy)
    simp only [Pi.zero_apply, term, Pi.mul_apply]
    rw [ampC_zero_of_notMem h₂ w hy', zero_mul]
  · filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hy' : y ∉ Set.Icc (1 / C₀) C₀ := fun h => absurd h.2 (not_le.mpr hy)
    simp only [Pi.zero_apply, term, Pi.mul_apply]
    rw [ampC_zero_of_notMem h₂ w hy', zero_mul]

private lemma iteratedDeriv_term_eq_zero {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₂ : IsBumpAtOne ψ₂ C₀)
    (w τ : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (1 / C₀) C₀) (j : ℕ) :
    iteratedDeriv j (term ψ₁ ψ₂ w τ) x = 0 := by
  have h := Filter.EventuallyEq.iteratedDeriv (term_eventuallyEq_zero (ψ₁ := ψ₁) h₂ w τ hx) j
  have h2 : iteratedDeriv j (0 : ℝ → ℂ) x = 0 := by simp
  exact (h.eq_of_nhds).trans h2

private lemma hasCompactSupport_term {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₂ : IsBumpAtOne ψ₂ C₀)
    (w τ : ℝ) : HasCompactSupport (term ψ₁ ψ₂ w τ) := by
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc (fun x hx => ?_)
  simp only [term, Pi.mul_apply]
  rw [ampC_zero_of_notMem h₂ w hx, zero_mul]

/-- `term ψ₁ ψ₂ w τ` is `C^∞`. -/
private lemma contDiff_term {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term ψ₁ ψ₂ w τ) := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 1 / C₀
  · have hx' : x ∉ Set.Icc (1 / C₀) C₀ := fun h => absurd h.1 (not_le.mpr hx)
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const (term_eventuallyEq_zero h₂ w τ hx')
  · have hx : 1 / C₀ ≤ x := not_lt.mp hx
    by_cases hx2 : x ≤ C₀
    · have hxpos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hC₀pos) hx
      exact (contDiff_ampC h₁ h₂ w).contDiffAt.mul (contDiffAt_phi τ hxpos)
    · have hx2 : C₀ < x := not_le.mp hx2
      have hx' : x ∉ Set.Icc (1 / C₀) C₀ := fun h => absurd h.2 (not_le.mpr hx2)
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const (term_eventuallyEq_zero h₂ w τ hx')

private lemma integrable_iteratedDeriv_term {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (term ψ₁ ψ₂ w τ)) := by
  have hcs := hasCompactSupport_term (ψ₁ := ψ₁) h₂ w τ
  have hsupp : HasCompactSupport (iteratedDeriv n (term ψ₁ ψ₂ w τ)) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
  exact ((contDiff_term hC₀ h₁ h₂ w τ).continuous_iteratedDeriv n (by exact_mod_cast le_top))
    |>.integrable_of_hasCompactSupport hsupp

/-! ## The pointwise derivative bound for the term -/

private lemma norm_iteratedDeriv_term_le {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ : ℝ) {c₁ c₂ : ℕ → ℝ}
    (hc₁ : ∀ k, 0 ≤ c₁ k ∧ ∀ x, |iteratedDeriv k (fun u : ℝ => ψ₁ (u + w)) x| ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k ∧ ∀ x, |iteratedDeriv k ψ₂ x| ≤ c₂ k) (j : ℕ) :
    ∀ x, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖ ≤ Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by
  intro x
  rcases le_or_gt (1 / C₀) x with hx | hx
  · have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
    have hxpos : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hC₀pos) hx
    have hAC : ContDiffAt ℝ ((j : ℕ∞) : WithTop ℕ∞) (ampC ψ₁ ψ₂ w) x :=
      ((contDiff_ampC h₁ h₂ w).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
    have hpC : ContDiffAt ℝ ((j : ℕ∞) : WithTop ℕ∞) (phi τ) x :=
      (contDiffAt_phi τ hxpos).of_le (WithTop.coe_le_coe.mpr le_top)
    have hsplit : term ψ₁ ψ₂ w τ = ampC ψ₁ ψ₂ w * phi τ := rfl
    rw [hsplit, iteratedDeriv_mul hAC hpC]
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ‖((j.choose i : ℕ) : ℂ) * iteratedDeriv i (ampC ψ₁ ψ₂ w) x *
            iteratedDeriv (j - i) (phi τ) x‖
          ≤ ((j.choose i : ℝ) * ampBound c₁ c₂ i * (phifact (j - i) * C₀ ^ (j - i))) *
              (1 + |τ|) ^ j := by
      intro i _
      rw [norm_mul, norm_mul, RCLike.norm_natCast]
      have h1 : ‖iteratedDeriv i (ampC ψ₁ ψ₂ w) x‖ ≤ ampBound c₁ c₂ i :=
        norm_iteratedDeriv_ampC_le h₁ h₂ w hc₁ hc₂ i x
      have h2 : ‖iteratedDeriv (j - i) (phi τ) x‖
          ≤ phifact (j - i) * C₀ ^ (j - i) * (1 + |τ|) ^ (j - i) :=
        norm_iteratedDeriv_phi_le hC₀ (j - i) hx
      have hp : (1 : ℝ) ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      have hpow : (1 + |τ|) ^ (j - i) ≤ (1 + |τ|) ^ j :=
        pow_le_pow_right₀ hp (Nat.sub_le j i)
      have hA : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
      have hAn : (0 : ℝ) ≤ (j.choose i : ℝ) * ampBound c₁ c₂ i :=
        mul_nonneg hA (ampBound_nonneg (fun k => (hc₁ k).1) (fun k => (hc₂ k).1) i)
      have hAnp : (0 : ℝ) ≤ (j.choose i : ℝ) * ampBound c₁ c₂ i * phifact (j - i) :=
        mul_nonneg hAn (phifact_nonneg _)
      have hmiddle : phifact (j - i) * C₀ ^ (j - i) * (1 + |τ|) ^ (j - i)
          ≤ phifact (j - i) * C₀ ^ (j - i) * (1 + |τ|) ^ j :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (phifact_nonneg _) (pow_nonneg (le_trans zero_le_one hC₀) _))
      calc (j.choose i : ℝ) * ‖iteratedDeriv i (ampC ψ₁ ψ₂ w) x‖ *
              ‖iteratedDeriv (j - i) (phi τ) x‖
          ≤ (j.choose i : ℝ) * ampBound c₁ c₂ i *
              (phifact (j - i) * C₀ ^ (j - i) * (1 + |τ|) ^ (j - i)) :=
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA)
              (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left h2 hAn)
        _ ≤ (j.choose i : ℝ) * ampBound c₁ c₂ i *
              (phifact (j - i) * C₀ ^ (j - i) * (1 + |τ|) ^ j) :=
            mul_le_mul_of_nonneg_left hmiddle hAn
        _ = ((j.choose i : ℝ) * ampBound c₁ c₂ i * (phifact (j - i) * C₀ ^ (j - i))) *
              (1 + |τ|) ^ j := by ring
    calc ‖∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℂ) * iteratedDeriv i (ampC ψ₁ ψ₂ w) x *
            iteratedDeriv (j - i) (phi τ) x‖
        ≤ ∑ i ∈ Finset.range (j + 1),
            ‖((j.choose i : ℕ) : ℂ) * iteratedDeriv i (ampC ψ₁ ψ₂ w) x *
              iteratedDeriv (j - i) (phi τ) x‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            ((j.choose i : ℝ) * ampBound c₁ c₂ i * (phifact (j - i) * C₀ ^ (j - i))) *
              (1 + |τ|) ^ j := Finset.sum_le_sum hterm
      _ = Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by rw [Gconst, Finset.sum_mul]
  · have hx' : x ∉ Set.Icc (1 / C₀) C₀ := fun h => absurd h.1 (not_le.mpr hx)
    rw [iteratedDeriv_term_eq_zero h₂ w τ hx' j, norm_zero]
    exact mul_nonneg (Gconst_nonneg hC₀ (fun k => (hc₁ k).1) (fun k => (hc₂ k).1) j)
      (by positivity)

/-! ## The integral bound -/

private lemma integral_iteratedDeriv_term_le {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ : ℝ) {c₁ c₂ : ℕ → ℝ}
    (hc₁ : ∀ k, 0 ≤ c₁ k ∧ ∀ x, |iteratedDeriv k (fun u : ℝ => ψ₁ (u + w)) x| ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k ∧ ∀ x, |iteratedDeriv k ψ₂ x| ≤ c₂ k) (j : ℕ) :
    ∫ x, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖ ≤ C₀ * Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by
  set B : ℝ := Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j with hBdef
  have hBnn : 0 ≤ B := mul_nonneg
    (Gconst_nonneg hC₀ (fun k => (hc₁ k).1) (fun k => (hc₂ k).1) j) (by positivity)
  have hzero : ∀ x ∉ Set.Icc (1 / C₀) C₀,
      ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖ = 0 := by
    intro x hx
    rw [iteratedDeriv_term_eq_zero h₂ w τ hx j, norm_zero]
  have hmono : ∫ x in Set.Icc (1 / C₀) C₀, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖
      ≤ ∫ _x in Set.Icc (1 / C₀) C₀, B := by
    refine setIntegral_mono ?_ ?_ ?_
    · exact (integrable_iteratedDeriv_term hC₀ h₁ h₂ w τ j).norm.integrableOn
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
    · intro x
      exact norm_iteratedDeriv_term_le hC₀ h₁ h₂ w τ hc₁ hc₂ j x
  have hvol : max (C₀ - 1 / C₀) 0 ≤ C₀ := by
    rw [max_le_iff]
    exact ⟨by
      have h : 0 < 1 / C₀ := one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hC₀)
      linarith, le_trans zero_le_one hC₀⟩
  calc ∫ x, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖
      = ∫ x in Set.Icc (1 / C₀) C₀, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖ := by
        rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
        exact hzero
    _ ≤ ∫ _x in Set.Icc (1 / C₀) C₀, B := hmono
    _ = volume.real (Set.Icc (1 / C₀) C₀) * B := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ = max (C₀ - 1 / C₀) 0 * B := by rw [Real.volume_real_Icc]
    _ ≤ C₀ * B := mul_le_mul_of_nonneg_right hvol hBnn
    _ = C₀ * Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by rw [hBdef]; ring

/-! ## Decay of the Fourier transform -/

private lemma norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

private lemma fourier_term_le {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ ξ : ℝ) {c₁ c₂ : ℕ → ℝ}
    (hc₁ : ∀ k, 0 ≤ c₁ k ∧ ∀ x, |iteratedDeriv k (fun u : ℝ => ψ₁ (u + w)) x| ≤ c₁ k)
    (hc₂ : ∀ k, 0 ≤ c₂ k ∧ ∀ x, |iteratedDeriv k ψ₂ x| ≤ c₂ k) (j : ℕ) (hξ : ξ ≠ 0) :
    ‖FourierTransform.fourier (term ψ₁ ψ₂ w τ) ξ‖
      ≤ Kconst C₀ c₁ c₂ j * (1 + |τ|) ^ j / |ξ| ^ j := by
  have hfour := Real.fourier_iteratedDeriv (f := term ψ₁ ψ₂ w τ) (N := (j : ℕ∞)) (n := j)
    ((contDiff_term hC₀ h₁ h₂ w τ).of_le (by exact_mod_cast le_top))
    (fun n _ => integrable_iteratedDeriv_term hC₀ h₁ h₂ w τ n) (le_refl _)
  have hpi : ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ = (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow, norm_two_pi_I_mul]
  have h1 : ‖FourierTransform.fourier (iteratedDeriv j (term ψ₁ ψ₂ w τ)) ξ‖
      ≤ ∫ x, ‖iteratedDeriv j (term ψ₁ ψ₂ w τ) x‖ := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [Circle.norm_smul]
  have hbound : ‖FourierTransform.fourier (term ψ₁ ψ₂ w τ) ξ‖ * (2 * Real.pi * |ξ|) ^ j
      ≤ C₀ * Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by
    have h3 : ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j •
          FourierTransform.fourier (term ψ₁ ψ₂ w τ) ξ‖
        ≤ C₀ * Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j := by
      rw [← congrFun hfour ξ]
      exact h1.trans (integral_iteratedDeriv_term_le hC₀ h₁ h₂ w τ hc₁ hc₂ j)
    rw [norm_smul, hpi] at h3
    rwa [mul_comm] at h3
  have hpos : 0 < (2 * Real.pi * |ξ|) ^ j := by positivity
  have h4 : ‖FourierTransform.fourier (term ψ₁ ψ₂ w τ) ξ‖
      ≤ (C₀ * Gconst C₀ c₁ c₂ j * (1 + |τ|) ^ j) / (2 * Real.pi * |ξ|) ^ j :=
    (le_div_iff₀ hpos).mpr hbound
  refine h4.trans (le_of_eq ?_)
  rw [Kconst, mul_pow]
  have hpi0 : (2 * Real.pi) ^ j ≠ 0 := by positivity
  have hξ0 : |ξ| ^ j ≠ 0 := ne_of_gt (pow_pos (abs_pos.mpr hξ) j)
  field_simp

/-! ## The target theorem -/

theorem term_fourierTransform_decay (ψ₁ ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (w τ ξ : ℝ) (j : ℕ), ξ ≠ 0 →
        ‖FourierTransform.fourier
            (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u) ξ‖
          ≤ K j * (1 + |τ|) ^ j / |ξ| ^ j := by
  choose c₁ hc₁ using exists_shift_deriv_bound (ψ := ψ₁) h₁
  choose c₂ hc₂ using exists_deriv_bound h₂
  refine ⟨fun j => Kconst C₀ c₁ c₂ j,
    fun j => Kconst_nonneg hC₀ (fun k => (hc₁ k).1) (fun k => (hc₂ k).1) j, ?_⟩
  intro w τ ξ j hξ
  rw [show (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u) = term ψ₁ ψ₂ w τ from by
    funext u; simp only [term, Pi.mul_apply, ampC]]
  exact fourier_term_le hC₀ h₁ h₂ w τ ξ
    (fun k => ⟨(hc₁ k).1, fun x => (hc₁ k).2 w x⟩) hc₂ j hξ

end Work.GM.S3
