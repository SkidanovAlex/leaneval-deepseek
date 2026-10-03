import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Data.Int.Star
import Submission.Lib.Unif2.Commons.Analysis.Complex.zeroFactor_g

noncomputable section

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology BigOperators

namespace Commons.Analysis.Complex

/-- **Partial factorization.**  If `f` is meromorphic on `U` with finite orders everywhere, analytic
on `U`, and the divisor of `f` on a subset `V ⊆ U` has finite support, then we can factor out the
zeros recorded in that divisor:  there is `g`, analytic on `U`, nonzero at every point of `V`, such
that `f z = (∏ᶠ u, (z-u)^(divisor f V u)) · g z` on `U`. -/
lemma factor_subBall_divisor {U V : Set ℂ} {f : ℂ → ℂ}
    (hVU : V ⊆ U)
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (h₄f : AnalyticOnNhd ℂ f U)
    (h₃f : (MeromorphicOn.divisor f V).support.Finite) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g U ∧
      (∀ u ∈ V, g u ≠ 0) ∧
      (∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f V) u : ℤ)) * g z) := by
  let D : Function.locallyFinsuppWithin V ℤ := MeromorphicOn.divisor f V
  let d : ℂ → ℤ := fun u ↦ (D u : ℤ)
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ d u
  let ψ : ℂ → ℂ := φ⁻¹ * f
  let g : ℂ → ℂ := toMeromorphicNFOn ψ U
  have h₁fV : MeromorphicOn f V := fun z hz ↦ h₁f z (hVU hz)
  have hd : d.HasFiniteSupport := by
    simpa [d, D, Function.HasFiniteSupport] using h₃f
  have hφ_mNFOn : MeromorphicNFOn φ univ := by
    simpa [φ, d] using (Function.FactorizedRational.meromorphicNFOn_univ d)
  have hφ_mOn : MeromorphicOn φ U := fun z hz ↦ (hφ_mNFOn (by trivial : z ∈ univ)).meromorphicAt
  have h₂φ : ∀ z ∈ U, meromorphicOrderAt φ z ≠ ⊤ := by
    intro z hz
    exact (Function.FactorizedRational.meromorphicOrderAt_ne_top d)
  have hψ_mOn : MeromorphicOn ψ U := by
    intro z hz
    unfold ψ
    exact (hφ_mOn z hz).inv.mul (h₁f z hz)
  have hg_mNFOn : MeromorphicNFOn g U := by
    exact meromorphicNFOn_toMeromorphicNFOn ψ U
  have hdiv_nonneg : 0 ≤ MeromorphicOn.divisor f U :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg h₄f
  have hdivψ_nonneg : 0 ≤ MeromorphicOn.divisor ψ U := by
    have hφinv : MeromorphicOn φ⁻¹ U := hφ_mOn.inv
    have h₂φinv : ∀ z ∈ U, meromorphicOrderAt φ⁻¹ z ≠ ⊤ := by
      intro z hz
      rw [meromorphicOrderAt_inv]
      simpa using (h₂φ z hz)
    have hdivψ : MeromorphicOn.divisor ψ U =
        MeromorphicOn.divisor φ⁻¹ U + MeromorphicOn.divisor f U := by
      calc
        MeromorphicOn.divisor ψ U = MeromorphicOn.divisor (φ⁻¹ * f) U := by rfl
        _ = MeromorphicOn.divisor φ⁻¹ U + MeromorphicOn.divisor f U := by
          exact MeromorphicOn.divisor_mul hφinv h₁f h₂φinv h₂f
    intro z
    by_cases hz : z ∈ U
    · have hφz : (divisor φ U) z = d z := by
        rw [divisor_apply hφ_mOn hz]
        rw [Function.FactorizedRational.meromorphicOrderAt_eq d hd]
        simp
      have hle : (divisor φ U) z ≤ (divisor f U) z := by
        rw [hφz]
        by_cases hzV : z ∈ V
        · have hdfV : (divisor f V) z = (divisor f U) z := by
            rw [divisor_apply h₁fV hzV, divisor_apply h₁f hz]
          have hdV : d z = (divisor f V) z := by simpa [d, D]
          rw [hdV, hdfV]
        · have hd0 : d z = 0 := by
            dsimp [d, D]
            rw [divisor_def]
            simp [hzV]
          rw [hd0]
          exact hdiv_nonneg z
      -- 0 ≤ (divisor ψ U) z
      rw [hdivψ]
      have hdivφinv : MeromorphicOn.divisor φ⁻¹ U = - MeromorphicOn.divisor φ U := divisor_inv
      rw [hdivφinv]
      simp only [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg,
        Function.locallyFinsuppWithin.coe_zero, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      linarith
    · rw [divisor_def]
      simp [hz]
  have hg_an : AnalyticOnNhd ℂ g U := by
    rw [← (meromorphicNFOn_toMeromorphicNFOn ψ U).divisor_nonneg_iff_analyticOnNhd]
    rw [MeromorphicOn.divisor_of_toMeromorphicNFOn hψ_mOn]
    exact hdivψ_nonneg
  have hg_nz : ∀ u ∈ V, g u ≠ 0 := by
    intro u hu
    rw [← (hg_mNFOn (hVU hu)).meromorphicOrderAt_eq_zero_iff]
    calc
      meromorphicOrderAt g u = meromorphicOrderAt ψ u := by
        exact meromorphicOrderAt_toMeromorphicNFOn hψ_mOn (hVU hu)
      _ = meromorphicOrderAt φ⁻¹ u + meromorphicOrderAt f u := by
        exact meromorphicOrderAt_mul (hφ_mOn u (hVU hu)).inv (h₁f u (hVU hu))
      _ = -meromorphicOrderAt φ u + meromorphicOrderAt f u := by
        rw [meromorphicOrderAt_inv]
      _ = -(d u : WithTop ℤ) + meromorphicOrderAt f u := by
        rw [Function.FactorizedRational.meromorphicOrderAt_eq d hd]
      _ = -(d u : WithTop ℤ) + (d u : WithTop ℤ) := by
        congr 1
        have h₂u : meromorphicOrderAt f u ≠ ⊤ := h₂f u (hVU hu)
        rw [← WithTop.coe_untop₀_of_ne_top h₂u]
        congr 1
        simpa [d, D] using (divisor_apply h₁fV hu).symm
      _ = 0 := by
        simp [d]
  have hprod_eq : ∀ z : ℂ, (∏ᶠ u : ℂ, (z - u) ^ (D u : ℤ)) = φ z := by
    intro z
    change (∏ᶠ u : ℂ, (z - u) ^ d u) = φ z
    dsimp [φ]
    rw [Function.FactorizedRational.finprod_eq_fun hd]
  have h_point : ∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f V) u : ℤ)) * g z := by
    intro z hz
    by_cases hD0 : (D z : ℤ) = 0
    · have hd0 : d z = 0 := by simpa [d] using hD0
      have hφz_ne : φ z ≠ 0 := by
        simpa [φ] using (Function.FactorizedRational.ne_zero hd0)
      have hφ_an : AnalyticAt ℂ φ z := by
        simpa [φ] using (Function.FactorizedRational.analyticAt (d := d) (x := z) (by simp [hd0]))
      have hψ_an : AnalyticAt ℂ ψ z := by
        unfold ψ
        exact ((hφ_an.inv hφz_ne)).mul (h₄f z hz)
      have hgz : g z = ψ z := by
        calc g z = toMeromorphicNFAt ψ z z := by
              exact toMeromorphicNFOn_eq_toMeromorphicNFAt hψ_mOn hz
          _ = ψ z := by
              exact congrFun (toMeromorphicNFAt_eq_self.2 hψ_an.meromorphicNFAt) z
      rw [hprod_eq z, hgz]
      unfold ψ
      change f z = φ z * ((φ z)⁻¹ * f z)
      field_simp [hφz_ne]
    · have hzV : z ∈ V := by
        by_contra hznot
        have hD0' : (D z : ℤ) = 0 := by
          dsimp [D]
          rw [divisor_def]
          simp [hznot]
        exact hD0 hD0'
      have hord_f : meromorphicOrderAt f z = (D z : WithTop ℤ) := by
        have h₂z : meromorphicOrderAt f z ≠ ⊤ := h₂f z hz
        rw [← WithTop.coe_untop₀_of_ne_top h₂z]
        congr 1
        simpa [D] using (divisor_apply h₁fV hzV).symm
      have hord_ne_zero : meromorphicOrderAt f z ≠ 0 := by
        intro h
        have hD : (D z : WithTop ℤ) = 0 := by rwa [← hord_f]
        exact hD0 (WithTop.coe_eq_zero.mp hD)
      have hfz0 : f z = 0 := by
        by_contra hz'
        have hord0 : meromorphicOrderAt f z = 0 := meromorphicOrderAt_eq_zero_of_ne_zero (h₄f z hz) hz'
        exact hord_ne_zero hord0
      have hφz0 : φ z = 0 := by
        have hd0 : d z ≠ 0 := by simpa [d] using hD0
        dsimp [φ]
        rw [Function.FactorizedRational.extractFactor (d := d) (u₀ := z) hd]
        simp [Pi.mul_apply, Pi.pow_apply, sub_self, zero_zpow (d z) hd0]
      have hprod0 : (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f V) u : ℤ)) = 0 := by
        rw [hprod_eq z]
        exact hφz0
      rw [hfz0, hprod0]
      simp
  refine ⟨g, hg_an, hg_nz, ?_⟩
  intro z hz
  exact h_point z hz

/-- Monotonicity of integer powers on the nonnegative reals. -/
lemma zpow_le_zpow_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℤ} (hn : 0 ≤ n) :
    a ^ n ≤ b ^ n := by
  rw [← Int.toNat_of_nonneg hn]
  rw [zpow_natCast, zpow_natCast]
  exact pow_le_pow_left₀ ha hab n.toNat

theorem divisor_subBall_factor {f : ℂ → ℂ} {c : ℂ} {R A : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfc : f c ≠ 0)
    (hcirc_out : ∀ w : ℂ, ‖w - c‖ = R → f w ≠ 0)
    (hcirc_in : ∀ w : ℂ, ‖w - c‖ = R / 2 → f w ≠ 0)
    (hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖f w‖ ≤ A * ‖f c‖) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ z ∈ Metric.closedBall c R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall c (R / 2))) u : ℤ)) * g z) ∧
      (∀ z ∈ Metric.closedBall c (R / 2), g z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall c R, ‖g z‖ ≤ A * ‖g c‖) ∧
      g c ≠ 0 := by
  classical
  let U : Set ℂ := Metric.closedBall c R
  let V : Set ℂ := Metric.closedBall c (R / 2)
  have hR0 : 0 ≤ R := le_of_lt hR
  have hR2pos : 0 < R / 2 := by positivity
  have hR2_0 : 0 ≤ R / 2 := le_of_lt hR2pos
  have hVU : V ⊆ U := by
    intro z hz
    have hzd : dist z c ≤ R / 2 := by simpa [V] using hz
    have hzle : ‖z - c‖ ≤ R / 2 := by simpa [dist_eq_norm] using hzd
    have : ‖z - c‖ ≤ R := by linarith
    have hzU : dist z c ≤ R := by simpa [dist_eq_norm] using this
    simpa [U] using hzU
  have hfU : AnalyticOnNhd ℂ f U := by simpa [U] using hf
  have hfV : AnalyticOnNhd ℂ f V := by
    intro z hz
    exact hfU z (hVU hz)
  have h₂f : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    exact order_ne_top_on_closedBall (a := c) (R := R) hR0 hf hfc z hz
  have h₃f : (MeromorphicOn.divisor f V).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hfU.meromorphicOn (isCompact_closedBall c R) hVU
  rcases factor_subBall_divisor (U := U) (V := V) hVU hfU.meromorphicOn h₂f hfU h₃f with ⟨g, hg_an, hg_nz, hg_eq⟩
  have hcU : c ∈ U := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hR0
  have hcV : c ∈ V := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hR2_0
  let D : Function.locallyFinsuppWithin V ℤ := MeromorphicOn.divisor f V
  let d : ℂ → ℤ := fun u ↦ (D u : ℤ)
  have hd : d.HasFiniteSupport := by
    simpa [d, D, Function.HasFiniteSupport] using h₃f
  have hsupp : (support d).Finite := by
    simpa [d, D] using h₃f
  let S : Finset ℂ := hsupp.toFinset
  have hS_coe : (S : Set ℂ) = support d := by
    exact hsupp.coe_toFinset
  let φ : ℂ → ℂ := fun z : ℂ => ∏ᶠ u : ℂ, (z - u) ^ (d u)
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfV) u
  have hφz_eq : ∀ z : ℂ, φ z = ∏ u ∈ S, (z - u) ^ (d u) := by
    intro z
    have hsub2 : mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ (S : Set ℂ) := by
      intro u hu
      have hd_ne : d u ≠ 0 := by
        intro hd0
        have : (z - u) ^ (d u) = 1 := by simp [hd0]
        exact hu this
      exact hsupp.mem_toFinset.mpr hd_ne
    dsimp [φ]
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (d u)) hsub2]
  have hnormφ : ∀ z : ℂ, ‖φ z‖ = ∏ u ∈ S, ‖z - u‖ ^ (d u) := by
    intro z
    rw [hφz_eq z]
    simp [norm_prod]
  have hfac : ∀ z : ℂ, z ∈ U → f z = φ z * g z := by
    intro z hzU
    rw [hg_eq z hzU]
  have hd_ne_of_mem : ∀ u : ℂ, u ∈ S → d u ≠ 0 := by
    intro u hu
    have huS : u ∈ (S : Set ℂ) := by simpa using hu
    rw [hS_coe] at huS
    exact huS
  have hS_lt : ∀ u : ℂ, u ∈ S → ‖u - c‖ < R / 2 := by
    intro u hu
    have huV : u ∈ V := D.supportWithinDomain (by simpa [d] using hd_ne_of_mem u hu)
    have hord_ne : meromorphicOrderAt f u ≠ 0 := by
      intro hord0
      have hdu : (D u : ℤ) = 0 := by
        dsimp [D]
        rw [divisor_apply hfV.meromorphicOn huV, hord0]
        simp
      exact hd_ne_of_mem u hu (by simpa [d] using hdu)
    have hfu0 : f u = 0 := by
      by_contra hfune
      have hord0 : meromorphicOrderAt f u = 0 :=
        meromorphicOrderAt_eq_zero_of_ne_zero (hfV u huV) hfune
      exact hord_ne hord0
    have hle : ‖u - c‖ ≤ R / 2 := by
      have hduV : dist u c ≤ R / 2 := by simpa [V] using huV
      simpa [dist_eq_norm] using hduV
    have hne_circ : ‖u - c‖ ≠ R / 2 := by
      intro hEq
      exact hcirc_in u hEq hfu0
    exact lt_of_le_of_ne hle hne_circ
  have hfu0_of_mem : ∀ u : ℂ, u ∈ S → f u = 0 := by
    intro u hu
    have huV : u ∈ V := D.supportWithinDomain (by simpa [d] using hd_ne_of_mem u hu)
    by_contra hfune
    have hord0 : meromorphicOrderAt f u = 0 :=
      meromorphicOrderAt_eq_zero_of_ne_zero (hfV u huV) hfune
    have hdu : (D u : ℤ) = 0 := by
      dsimp [D]
      rw [divisor_apply hfV.meromorphicOn huV, hord0]
      simp
    exact hd_ne_of_mem u hu (by simpa [d] using hdu)
  have hgc_ne : g c ≠ 0 := by
    exact hg_nz c hcV
  have hA0 : 0 < A := by nlinarith
  have hgsphere : ∀ w : ℂ, ‖w - c‖ = R → ‖g w‖ ≤ A * ‖g c‖ := by
    intro w hw
    have hwU : w ∈ U := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_eq hw
    have hw_ne_u : ∀ u : ℂ, u ∈ S → w ≠ u := by
      intro u hu
      intro hEq
      have hu_lt := hS_lt u hu
      have : ‖u - c‖ = R := by simpa [hEq] using hw
      linarith
    have hφw_ne : φ w ≠ 0 := by
      intro h0
      rw [hφz_eq w] at h0
      have hprod_ne : (∏ u ∈ S, (w - u) ^ (d u)) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (fun u hu =>
          zpow_ne_zero (d u) (sub_ne_zero.mpr (hw_ne_u u hu)))
      exact hprod_ne h0
    have hφc_ne : φ c ≠ 0 := by
      intro h0
      rw [hφz_eq c] at h0
      have hprod_ne : (∏ u ∈ S, (c - u) ^ (d u)) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (fun u hu =>
          zpow_ne_zero (d u) (sub_ne_zero.mpr (by
            intro hEq
            have : f c = 0 := by simpa [hEq] using hfu0_of_mem u hu
            exact hfc this)))
      exact hprod_ne h0
    have hφw_pos : 0 < ‖φ w‖ := norm_pos_iff.mpr hφw_ne
    have hφc_pos : 0 < ‖φ c‖ := norm_pos_iff.mpr hφc_ne
    have hfactor_le : ‖φ c‖ ≤ ‖φ w‖ := by
      rw [hnormφ c, hnormφ w]
      apply Finset.prod_le_prod₀
      · intro u hu
        exact zpow_nonneg (norm_nonneg _) (d u)
      · intro u hu
        have hu_lt := hS_lt u hu
        have htr : ‖w - c‖ ≤ ‖w - u‖ + ‖u - c‖ := by
          simpa [dist_eq_norm] using (dist_triangle w u c)
        have hge : ‖c - u‖ ≤ ‖w - u‖ := by
          have h1 : ‖u - c‖ < R - ‖u - c‖ := by nlinarith
          have h2 : R - ‖u - c‖ ≤ ‖w - u‖ := by linarith
          have h3 : ‖c - u‖ = ‖u - c‖ := norm_sub_rev c u
          rw [h3]
          exact le_trans (le_of_lt h1) h2
        exact zpow_le_zpow_of_nonneg (norm_nonneg _) hge (hd_nonneg u)
    have hnorm_w : ‖f w‖ = ‖φ w‖ * ‖g w‖ := by
      have hfw := hfac w hwU
      rw [hfw, norm_mul]
    have hnorm_c : ‖f c‖ = ‖φ c‖ * ‖g c‖ := by
      have hfc_eq := hfac c hcU
      rw [hfc_eq, norm_mul]
    calc
      ‖g w‖ = ‖f w‖ / ‖φ w‖ := by
        rw [hnorm_w]
        field_simp [ne_of_gt hφw_pos]
      _ ≤ (A * ‖f c‖) / ‖φ w‖ := by
        exact div_le_div_of_nonneg_right (hAb w hw) (norm_nonneg _)
      _ = A * ‖g c‖ * (‖φ c‖ / ‖φ w‖) := by
        rw [hnorm_c]
        field_simp [ne_of_gt hφw_pos]
      _ ≤ A * ‖g c‖ := by
        have hratio : ‖φ c‖ / ‖φ w‖ ≤ 1 := by
          exact div_le_one_of_le₀ hfactor_le (le_of_lt hφw_pos)
        have hpos : 0 ≤ A * ‖g c‖ := mul_nonneg (le_of_lt hA0) (norm_nonneg _)
        simpa using (mul_le_mul_of_nonneg_left hratio hpos)
  have hg_an_cl : AnalyticOnNhd ℂ g (Metric.closedBall c R) := by
    simpa [U] using hg_an
  have hDiffBall : DifferentiableOn ℂ g (Metric.ball c R) :=
    (hg_an_cl.differentiableOn).mono Metric.ball_subset_closedBall
  have hContCl : ContinuousOn g (Metric.closedBall c R) := hg_an_cl.continuousOn
  have hDiffCl : DiffContOnCl ℂ g (Metric.ball c R) := DiffContOnCl.mk_ball hDiffBall hContCl
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [U] using hg_an
  · intro z hz
    have hzU : z ∈ U := by simpa [U] using hz
    simpa [V] using hg_eq z hzU
  · intro z hz
    have hzV : z ∈ V := by simpa [V] using hz
    exact hg_nz z hzV
  · intro z hz
    have hzCl : z ∈ closure (Metric.ball c R) := by
      rw [closure_ball c (ne_of_gt hR)]
      simpa [U] using hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball (x := c) (r := R)) hDiffCl
      (fun w hwfront => by
        have hws : ‖w - c‖ = R := by
          rw [frontier_ball c (ne_of_gt hR)] at hwfront
          exact mem_sphere_iff_norm.mp hwfront
        exact hgsphere w hws)
      hzCl
  · exact hg_nz c hcV

end Commons.Analysis.Complex