import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.sum_divisor_le_circleAvg

noncomputable section

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology

namespace Commons.Analysis.Complex

lemma meromorphicOrderAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hfz : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
  have hord : analyticOrderAt f z = 0 := (hf.analyticOrderAt_eq_zero).2 hfz
  rw [hf.meromorphicOrderAt_eq, hord]
  simp

lemma meromorphicOrderAt_ne_top_of_analytic_ne_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0) : meromorphicOrderAt f z ≠ ⊤ := by
  rw [meromorphicOrderAt_eq_zero_of_ne_zero hf hfz]
  simp

/-- For an analytic function on the closed ball that is nonzero at the center, all orders are
finite. -/
lemma order_ne_top_on_closedBall {a : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall a R)) (hfa : f a ≠ 0) :
    ∀ z ∈ closedBall a R, meromorphicOrderAt f z ≠ ⊤ := by
  have h₁f : MeromorphicOn f (closedBall a R) := hf.meromorphicOn
  have hU : IsConnected (closedBall a R) := Metric.isConnected_closedBall hR
  have ha : a ∈ closedBall a R := Metric.mem_closedBall_self hR
  have htop_a : meromorphicOrderAt f a ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_analytic_ne_zero (hf a ha) hfa
  have : (∃ u : closedBall a R, meromorphicOrderAt f (u : ℂ) ≠ ⊤) ↔
      ∀ u : closedBall a R, meromorphicOrderAt f (u : ℂ) ≠ ⊤ :=
    MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall h₁f hU
  intro z hz
  exact (this.1 ⟨⟨a, ha⟩, htop_a⟩) ⟨z, hz⟩

/-- Core factorization with pointwise equality (analytic case). -/
lemma factor_pointwise {U : Set ℂ} {f : ℂ → ℂ}
    (h₁f : MeromorphicOn f U)
    (h₂f : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (h₃f : (MeromorphicOn.divisor f U).support.Finite)
    (h₄f : AnalyticOnNhd ℂ f U) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g U ∧ (∀ u ∈ U, g u ≠ 0) ∧
      (∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f U) u : ℤ)) * g z) := by
  let D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  let d : ℂ → ℤ := fun u ↦ (D u : ℤ)
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ d u
  let ψ : ℂ → ℂ := φ⁻¹ * f
  let g : ℂ → ℂ := toMeromorphicNFOn ψ U
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
  have hdivψ : MeromorphicOn.divisor ψ U = 0 := by
    have hφinv : MeromorphicOn φ⁻¹ U := hφ_mOn.inv
    have h₂φinv : ∀ z ∈ U, meromorphicOrderAt φ⁻¹ z ≠ ⊤ := by
      intro z hz
      rw [meromorphicOrderAt_inv]
      simpa using (h₂φ z hz)
    calc
      MeromorphicOn.divisor ψ U
          = MeromorphicOn.divisor (φ⁻¹ * f) U := by rfl
      _ = MeromorphicOn.divisor φ⁻¹ U + MeromorphicOn.divisor f U := by
            exact MeromorphicOn.divisor_mul hφinv h₁f h₂φinv h₂f
      _ = 0 := by
        rw [divisor_inv]
        have hφdiv : MeromorphicOn.divisor φ U = D := by
          simpa [φ, d, D] using (Function.FactorizedRational.divisor h₃f)
        simp [hφdiv, D]
  have hg_an : AnalyticOnNhd ℂ g U := by
    rw [← (meromorphicNFOn_toMeromorphicNFOn ψ U).divisor_nonneg_iff_analyticOnNhd]
    rw [MeromorphicOn.divisor_of_toMeromorphicNFOn hψ_mOn]
    simp [hdivψ]
  have hg_nz : ∀ u ∈ U, g u ≠ 0 := by
    intro u hu
    rw [← (hg_mNFOn hu).meromorphicOrderAt_eq_zero_iff]
    calc
      meromorphicOrderAt g u = meromorphicOrderAt ψ u := by
        exact meromorphicOrderAt_toMeromorphicNFOn hψ_mOn hu
      _ = meromorphicOrderAt φ⁻¹ u + meromorphicOrderAt f u := by
        exact meromorphicOrderAt_mul (hφ_mOn u hu).inv (h₁f u hu)
      _ = -meromorphicOrderAt φ u + meromorphicOrderAt f u := by
        rw [meromorphicOrderAt_inv]
      _ = -(d u : WithTop ℤ) + meromorphicOrderAt f u := by
        rw [Function.FactorizedRational.meromorphicOrderAt_eq d hd]
      _ = -(d u : WithTop ℤ) + (D u : WithTop ℤ) := by
        congr 1
        have h₂u : meromorphicOrderAt f u ≠ ⊤ := h₂f u hu
        rw [← WithTop.coe_untop₀_of_ne_top h₂u]
        congr 1
        simpa [D] using (divisor_apply h₁f hu).symm
      _ = 0 := by
        simp [d]
  have hprod_eq : ∀ z : ℂ, (∏ᶠ u : ℂ, (z - u) ^ (D u : ℤ)) = φ z := by
    intro z
    change (∏ᶠ u : ℂ, (z - u) ^ d u) = φ z
    dsimp [φ]
    rw [Function.FactorizedRational.finprod_eq_fun hd]
  have h_point : ∀ z ∈ U, f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f U) u : ℤ)) * g z := by
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
    · have hord_f : meromorphicOrderAt f z = (D z : WithTop ℤ) := by
        have h₂z : meromorphicOrderAt f z ≠ ⊤ := h₂f z hz
        rw [← WithTop.coe_untop₀_of_ne_top h₂z]
        congr 1
        simpa [D] using (divisor_apply h₁f hz).symm
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
      have hprod0 : (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f U) u : ℤ)) = 0 := by
        rw [hprod_eq z]
        exact hφz0
      rw [hfz0, hprod0]
      simp
  refine ⟨g, hg_an, hg_nz, ?_⟩
  intro z hz
  exact h_point z hz

lemma proj_mem_sphere (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (z : ℂ) (hzR : R < ‖z - a‖) :
    a + (R / ‖z - a‖) • (z - a) ∈ sphere a R := by
  have hpos : 0 < ‖z - a‖ := lt_of_le_of_lt hR hzR
  have ht : 0 ≤ R / ‖z - a‖ := div_nonneg hR (le_of_lt hpos)
  rw [mem_sphere_iff_norm]
  calc
    ‖(a + (R / ‖z - a‖) • (z - a)) - a‖ = ‖(R / ‖z - a‖) • (z - a)‖ := by simp
    _ = ‖z - a‖ * (R / ‖z - a‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        ring
    _ = R := by
        field_simp [ne_of_gt hpos]

lemma dist_to_proj (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (z : ℂ) (hzR : R ≤ ‖z - a‖) (hz0 : z ≠ a) :
    ‖z - (a + (R / ‖z - a‖) • (z - a))‖ = ‖z - a‖ - R := by
  have hv0 : ‖z - a‖ ≠ 0 := by simpa [norm_eq_zero, sub_eq_zero] using hz0
  have hle : R / ‖z - a‖ ≤ 1 := by
    rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0))]
    exact hzR
  have hvec : z - (a + (R / ‖z - a‖) • (z - a)) = (1 - R / ‖z - a‖) • (z - a) := by
    calc z - (a + (R / ‖z - a‖) • (z - a)) = (z - a) - (R / ‖z - a‖) • (z - a) := by abel
      _ = (1 - R / ‖z - a‖) • (z - a) := by
        rw [sub_smul, one_smul]
  rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
  field_simp [hv0]

/-- If ε ≤ δ, the closed ball of radius R+ε around a is contained in the δ-thickening of the
closed ball of radius R. -/
lemma closedBall_subset_cthickening_closedBall (a : ℂ) {R ε δ : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hεδ : ε ≤ δ) : closedBall a (R + ε) ⊆ cthickening δ (closedBall a R) := by
  intro z hz
  have hzmem : ‖z - a‖ ≤ R + ε := by simpa [dist_eq_norm] using (mem_closedBall_iff_norm.mp hz)
  by_cases hzR : ‖z - a‖ ≤ R
  · have hzK : z ∈ closedBall a R := by simpa [dist_eq_norm] using hzR
    have hδ : 0 ≤ δ := le_trans hε hεδ
    exact (closedBall_subset_cthickening (E := closedBall a R) hzK δ) (by simpa [hδ])
  · have hRlt : R < ‖z - a‖ := lt_of_not_ge hzR
    have hz0 : z ≠ a := by
      intro h
      have : ‖z - a‖ = 0 := by simpa [h]
      linarith
    let y : ℂ := a + (R / ‖z - a‖) • (z - a)
    have hyK : y ∈ closedBall a R := by
      exact sphere_subset_closedBall (proj_mem_sphere a hR z hRlt)
    have hdy : dist z y ≤ δ := by
      rw [dist_eq_norm]
      calc ‖z - y‖ = ‖z - a‖ - R := by simpa [y] using dist_to_proj a hR z (le_of_lt hRlt) hz0
        _ ≤ ε := by linarith
        _ ≤ δ := hεδ
    exact (closedBall_subset_cthickening (E := closedBall a R) hyK δ) (by simpa [dist_comm] using hdy)

/-- Shell around the sphere inside cthickening. -/
lemma mem_cthickening_sphere_of_mem_closedBall (a : ℂ) {R ε δ : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hεδ : ε ≤ δ) {z : ℂ} (hzR : R < ‖z - a‖) (hz : ‖z - a‖ ≤ R + ε) :
    z ∈ cthickening δ (sphere a R) := by
  have hz0 : z ≠ a := by
    intro h
    have : ‖z - a‖ = 0 := by simpa [h]
    linarith
  let y : ℂ := a + (R / ‖z - a‖) • (z - a)
  have hyS : y ∈ sphere a R := proj_mem_sphere a hR z hzR
  have hdy : dist z y ≤ δ := by
    rw [dist_eq_norm]
    calc ‖z - y‖ = ‖z - a‖ - R := by simpa [y] using dist_to_proj a hR z (le_of_lt hzR) hz0
      _ ≤ ε := by linarith
      _ ≤ δ := hεδ
  exact (closedBall_subset_cthickening (E := sphere a R) hyS δ) (by simpa [dist_comm] using hdy)

/-- The set of points where a function is analytic is open. -/
lemma isOpen_setOf_analyticAt (f : ℂ → ℂ) : IsOpen {z : ℂ | AnalyticAt ℂ f z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact hz.eventually_analyticAt

theorem zeroFactor_g {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a R))
    (hfa : f a ≠ 0)
    (hfc : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0) :
    ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      AnalyticOnNhd ℂ g (Metric.ball a (R + ε)) ∧
      (∀ z ∈ Metric.ball a (R + ε), g z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall a R,
        f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a R)) u : ℤ)) *
          g z) := by
  let U1 : Set ℂ := closedBall a R
  let W : Set ℂ := {z | AnalyticAt ℂ f z}
  have hW_open : IsOpen W := isOpen_setOf_analyticAt f
  have hU1W : U1 ⊆ W := by intro z hz; exact hf z (by simpa [U1] using hz)
  have hK : IsCompact U1 := by simpa [U1] using (isCompact_closedBall a R)
  rcases hK.exists_cthickening_subset_open hW_open hU1W with ⟨δ₁, hδ₁_pos, hδ₁⟩
  let V : Set ℂ := {z | z ∈ W ∧ f z ≠ 0}
  have hV_open : IsOpen V := by
    have hcont : ContinuousOn f W := fun z hz => (hz : AnalyticAt ℂ f z).continuousAt.continuousWithinAt
    have hpre : IsOpen (W ∩ f ⁻¹' ({0}ᶜ)) :=
      hcont.isOpen_inter_preimage hW_open (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set ℂ))
    convert hpre using 1
    ext z
    simp [V]
  have hS_V : sphere a R ⊆ V := by
    intro z hz
    have hzmem : z ∈ U1 := by
      exact (sphere_subset_closedBall : sphere a R ⊆ closedBall a R) hz
    exact ⟨hf z (by simpa [U1] using hzmem), hfc z (mem_sphere_iff_norm.mp hz)⟩
  rcases (isCompact_sphere a R).exists_cthickening_subset_open hV_open hS_V with ⟨δ₂, hδ₂_pos, hδ₂⟩
  let ε : ℝ := min δ₁ δ₂ / 2
  have hε_pos : 0 < ε := by
    have : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    positivity
  have hε_le1 : ε ≤ δ₁ := by
    have hmin : min δ₁ δ₂ ≤ δ₁ := min_le_left δ₁ δ₂
    have hmin0 : 0 ≤ min δ₁ δ₂ := (lt_min hδ₁_pos hδ₂_pos).le
    exact le_trans (half_le_self hmin0) hmin
  have hε_le2 : ε ≤ δ₂ := by
    have hmin : min δ₁ δ₂ ≤ δ₂ := min_le_right δ₁ δ₂
    have hmin0 : 0 ≤ min δ₁ δ₂ := (lt_min hδ₁_pos hδ₂_pos).le
    exact le_trans (half_le_self hmin0) hmin
  let U2 : Set ℂ := closedBall a (R + ε)
  have hU1U2 : U1 ⊆ U2 := by
    intro z hz
    have h1 : ‖z - a‖ ≤ R := by simpa [U1, dist_eq_norm] using hz
    have h2 : ‖z - a‖ ≤ R + ε := by linarith
    simpa [U2, dist_eq_norm] using h2
  -- f is analytic on the closed ball of radius R + ε
  have hf2 : AnalyticOnNhd ℂ f U2 := by
    intro z hz
    have hzW : z ∈ W := hδ₁ (closedBall_subset_cthickening_closedBall a (le_of_lt hR) hε_pos.le hε_le1 (by simpa [U2] using hz))
    exact hzW
  -- f is nonzero on the shell of U2 outside U1
  have hshell : ∀ z ∈ U2, z ∉ U1 → f z ≠ 0 := by
    intro z hzU2 hzU1
    have hzmem : ‖z - a‖ ≤ R + ε := by simpa [U2, dist_eq_norm] using (mem_closedBall_iff_norm.mp hzU2)
    have hzR : R < ‖z - a‖ := by
      have : ¬ ‖z - a‖ ≤ R := by
        intro h
        apply hzU1
        simpa [U1, dist_eq_norm] using h
      exact lt_of_not_ge this
    have hzV : z ∈ V := hδ₂ (mem_cthickening_sphere_of_mem_closedBall a (le_of_lt hR) hε_pos.le hε_le2 hzR hzmem)
    exact hzV.2
  have h₁f2 : MeromorphicOn f U2 := hf2.meromorphicOn
  have h₂f2 : ∀ z ∈ U2, meromorphicOrderAt f z ≠ ⊤ := by
    exact order_ne_top_on_closedBall (by positivity : 0 ≤ R + ε) hf2 hfa
  have h₃f2 : (MeromorphicOn.divisor f U2).support.Finite := by
    exact MeromorphicOn.divisor_support_finite_of_subset h₁f2 (by simpa [U2] using (isCompact_closedBall a (R + ε))) (by simp [U2])
  rcases factor_pointwise h₁f2 h₂f2 h₃f2 hf2 with ⟨g, hg_an2, hg_nz2, hg_eq2⟩
  refine ⟨g, ε, hε_pos, ?_, ?_, ?_⟩
  · intro z hz
    have hzU2 : z ∈ U2 := by
      have hzmem : ‖z - a‖ < R + ε := by simpa [dist_eq_norm] using (mem_ball_iff_norm.mp hz)
      simpa [U2, dist_eq_norm] using (le_of_lt hzmem)
    exact hg_an2 z hzU2
  · intro z hz
    have hzU2 : z ∈ U2 := by
      have hzmem : ‖z - a‖ < R + ε := by simpa [dist_eq_norm] using (mem_ball_iff_norm.mp hz)
      simpa [U2, dist_eq_norm] using (le_of_lt hzmem)
    exact hg_nz2 z hzU2
  · intro z hzU1
    have hzU2 : z ∈ U2 := hU1U2 hzU1
    have hdiv_eq : ∀ u : ℂ, (MeromorphicOn.divisor f U2) u = (MeromorphicOn.divisor f U1) u := by
      intro u
      by_cases hu2 : u ∈ U2
      · by_cases hu1 : u ∈ U1
        · simp [U1, U2, MeromorphicOn.divisor_apply h₁f2 hu2, MeromorphicOn.divisor_apply hf.meromorphicOn hu1]
        · have hfu : f u ≠ 0 := hshell u hu2 hu1
          have hD2 : (MeromorphicOn.divisor f U2) u = 0 := by
            rw [MeromorphicOn.divisor_apply h₁f2 hu2]
            rw [meromorphicOrderAt_eq_zero_of_ne_zero (hf2 u hu2) hfu]
            simp
          have hD1 : (MeromorphicOn.divisor f U1) u = 0 := by
            rw [MeromorphicOn.divisor_def]
            simp [hu1]
          rw [hD2, hD1]
      · have hu1 : u ∉ U1 := fun h => hu2 (hU1U2 h)
        have hD2 : (MeromorphicOn.divisor f U2) u = 0 := by
          rw [MeromorphicOn.divisor_def]
          simp [hu2]
        have hD1 : (MeromorphicOn.divisor f U1) u = 0 := by
          rw [MeromorphicOn.divisor_def]
          simp [hu1]
        rw [hD2, hD1]
    have heq : f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f U2) u : ℤ)) * g z := hg_eq2 z hzU2
    rw [heq]
    congr 1
    apply finprod_congr
    intro u
    rw [hdiv_eq u]

end Commons.Analysis.Complex