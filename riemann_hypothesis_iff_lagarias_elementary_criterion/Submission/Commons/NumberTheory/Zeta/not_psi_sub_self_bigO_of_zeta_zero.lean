import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Order
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_mellin_analytic
import Submission.Commons.NumberTheory.Zeta.logDeriv_zeta_eq_mellin_psi_sub_id
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff

open Complex Filter Set
open scoped Topology

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- Local analytic-order contradiction: a non-identically-zero analytic germ with a zero at `z₀`
cannot satisfy the differential equation `deriv f = -(A · f)` near `z₀` when `A` is analytic there. -/
lemma order_contra_of_deriv_eq_neg_mul {f A : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hA : AnalyticAt ℂ A z₀) (hfz₀ : f z₀ = 0)
    (hfne : ¬ ∀ᶠ z in nhds z₀, f z = 0)
    (hderiv : ∀ᶠ z in nhds z₀, deriv f z = -(A z * f z)) : False := by
  let o : ℕ∞ := analyticOrderAt f z₀
  have hftop : o ≠ ⊤ := by
    intro htop
    exact hfne (analyticOrderAt_eq_top.mp (by simpa [o] using htop))
  have hf0 : o ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf, hfz₀⟩
  let m : ℕ := analyticOrderNatAt f z₀
  have hom : (m : ℕ∞) = o := by
    simpa [m, o, analyticOrderNatAt, ENat.natCast_toNat hftop]
  have hmpos : 0 < m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    apply hf0
    simpa [hm0] using hom.symm
  have hd_fin : analyticOrderAt (deriv f) z₀ ≠ ⊤ := by
    intro htop
    apply hfne
    have hord := AnalyticAt.analyticOrderAt_deriv_add_one (𝕜 := ℂ) (f := f) (x := z₀) hf
    have hord' : analyticOrderAt (fun z : ℂ => f z - f z₀) z₀ = ⊤ := by
      simpa [htop] using hord.symm
    have hloc : ∀ᶠ z in nhds z₀, f z - f z₀ = 0 := analyticOrderAt_eq_top.mp hord'
    filter_upwards [hloc] with z hz
    simpa [hfz₀] using hz
  have hderiv_add : analyticOrderAt (deriv f) z₀ + 1 = o := by
    have h := AnalyticAt.analyticOrderAt_deriv_add_one (𝕜 := ℂ) (f := f) (x := z₀) hf
    simpa [hfz₀, o] using h
  have hod_eq : analyticOrderAt (deriv f) z₀ = analyticOrderAt A z₀ + o := by
    calc
      analyticOrderAt (deriv f) z₀ = analyticOrderAt (fun w : ℂ => -(A w * f w)) z₀ :=
        analyticOrderAt_congr hderiv
      _ = analyticOrderAt (A * f) z₀ := by
        exact analyticOrderAt_neg (f := A * f) (z₀ := z₀)
      _ = analyticOrderAt A z₀ + analyticOrderAt f z₀ := analyticOrderAt_mul hA hf
      _ = analyticOrderAt A z₀ + o := by rfl
  have hA_fin : analyticOrderAt A z₀ ≠ ⊤ := by
    intro htopA
    apply hd_fin
    simpa [htopA] using hod_eq
  have hsumA : (analyticOrderNatAt A z₀ : ℕ∞) + o + 1 = o := by
    calc
      (analyticOrderNatAt A z₀ : ℕ∞) + o + 1
          = analyticOrderAt A z₀ + o + 1 := by rw [Nat.cast_analyticOrderNatAt hA_fin]
      _ = analyticOrderAt (deriv f) z₀ + 1 := by rw [hod_eq]
      _ = o := hderiv_add
  have hsumA' : (analyticOrderNatAt A z₀ : ℕ∞) + (m : ℕ∞) + 1 = (m : ℕ∞) := by
    simpa [hom] using hsumA
  have hnat : analyticOrderNatAt A z₀ + m + 1 = m := by
    exact_mod_cast hsumA'
  omega

end

/-- If `ψ(x) - x = O(x ^ θ)` as `x → ∞`, then the Riemann zeta function has no zero with real
part strictly greater than `θ`.  (Classical zero-free region argument via the Mellin transform of
`ψ - id`.) -/
theorem zeta_ne_zero_of_bigO_psi_sub_self {θ : ℝ}
    (hO : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ) :
    ∀ z : ℂ, θ < z.re → riemannZeta z ≠ 0 := by
  rcases hO with ⟨C, hC, hbig⟩
  -- Analyticity of the Mellin integral of the correlation function ψ - id on {θ < re}.
  have hF_an : AnalyticOnNhd ℂ
      (fun w : ℂ => w * mellin
        (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w))
      {w : ℂ | θ < w.re} := by
    exact psi_sub_id_mellin_analytic (θ := θ) (C := C) hC hbig
  intro z hz hz0
  have hz1 : z ≠ 1 := by
    intro hz1
    exact riemannZeta_one_ne_zero (by simpa [hz1] using hz0)
  have hzlt : z.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz0
  have hθ1 : θ < 1 := lt_trans hz hzlt
  let D : Set ℂ := {w : ℂ | θ < w.re}
  let U : Set ℂ := {w : ℂ | θ < w.re ∧ w ≠ 1}
  have hUo : IsOpen U := by
    have h1 : IsOpen {z : ℂ | θ < z.re} := Complex.isOpen_re_gt θ
    have h2 : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    rw [show U = ({z : ℂ | θ < z.re} ∩ ({1}ᶜ : Set ℂ)) by ext w; simp [U]]
    exact h1.inter h2
  have hU_sub_D : U ⊆ D := by intro w hw; exact hw.1
  have hU_sub_compl1 : U ⊆ ({1}ᶜ : Set ℂ) := by intro w hw; exact hw.2
  let F : ℂ → ℂ := fun w : ℂ => w * mellin
        (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w)
  let A : ℂ → ℂ := fun w : ℂ => w / (w - 1) + F w
  let P : ℂ → ℂ := fun w : ℂ => deriv riemannZeta w + A w * riemannZeta w
  have hF_U : AnalyticOnNhd ℂ F U := by
    exact hF_an.mono hU_sub_D
  have hg_div : DifferentiableOn ℂ (fun w : ℂ => w / (w - 1)) U := by
    intro w hw
    apply (DifferentiableAt.div differentiableAt_id
      (differentiableAt_id.sub_const (1 : ℂ))
      (by simpa using (sub_ne_zero.mpr hw.2))).differentiableWithinAt
  have hg_div_an : AnalyticOnNhd ℂ (fun w : ℂ => w / (w - 1)) U :=
    (analyticOnNhd_iff_differentiableOn hUo).mpr hg_div
  have hζ_U : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hU_sub_compl1
  have hP : AnalyticOnNhd ℂ P U := by
    unfold P A
    exact ((hζ_U.deriv).add ((hg_div_an.add hF_U).mul hζ_U))
  have hV_sub_U : {w : ℂ | 1 < w.re} ⊆ U := by
    intro w hw
    refine ⟨lt_trans hθ1 hw, ?_⟩
    intro hw1
    rw [hw1] at hw
    norm_num at hw
  have hP_zero_V : ∀ w : ℂ, 1 < w.re → P w = 0 := by
    intro w hw1
    have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hw1)
    have hb := logDeriv_zeta_eq_mellin_psi_sub_id (w := w) hw1
    have hb1 : -(deriv riemannZeta w) / riemannZeta w =
        w * mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w)
          + w / (w - 1) := sub_eq_iff_eq_add.mp hb
    have hb' : -(deriv riemannZeta w) / riemannZeta w = w / (w - 1) + F w := by
      unfold F
      exact hb1.trans (add_comm _ _)
    have hmul : -(deriv riemannZeta w) = A w * riemannZeta w := by
      unfold A
      calc
        -(deriv riemannZeta w)
            = (-(deriv riemannZeta w) / riemannZeta w) * riemannZeta w := by
                rw [div_mul_cancel₀ _ hζw]
        _ = (w / (w - 1) + F w) * riemannZeta w := by rw [hb']
    unfold P
    rw [← hmul]
    ring
  have hPeq0 : EqOn P 0 U := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (z₀ := (2 : ℂ)) hP ?_ ?_ ?_
    · exact isPreconnected_re_gt_sdiff hθ1
    · exact ⟨lt_trans hθ1 (by norm_num : (1 : ℝ) < (2 : ℂ).re), by norm_num⟩
    · refine eventually_of_mem (U := {w : ℂ | 1 < w.re}) ?_ ?_
      · exact (Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)
      · intro w hw
        exact hP_zero_V w hw
  have hzU : z ∈ U := ⟨hz, hz1⟩
  have hPz : P z = 0 := hPeq0 hzU
  have hzer : riemannZeta z = 0 := hz0
  have htwo : (2 : ℂ) ≠ 1 := by norm_num
  have hA_an : AnalyticAt ℂ A z := by
    have hg_at : AnalyticAt ℂ (fun w : ℂ => w / (w - 1)) z := hg_div_an z hzU
    have hF_at : AnalyticAt ℂ F z := hF_U z hzU
    exact hg_at.add hF_at
  refine order_contra_of_deriv_eq_neg_mul (f := riemannZeta) (A := A) (z₀ := z) ?_ hA_an hzer ?_ ?_
  · exact analyticOn_riemannZeta z (by simpa using hz1)
  · intro hloc
    have hζeq : EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) := by
      refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero analyticOn_riemannZeta ?_ ?_ hloc
      · exact (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
      · simpa using hz1
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) (hζeq htwo)
  · filter_upwards [hUo.mem_nhds hzU] with w hwU
    have hPw : P w = 0 := hPeq0 hwU
    unfold P at hPw
    exact eq_neg_of_add_eq_zero_left hPw

theorem not_psi_sub_self_bigO_of_zeta_zero {s : ℂ} (hs : riemannZeta s = 0) {θ : ℝ}
    (hθ : θ < s.re) :
    ¬ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ C * x ^ θ := by
  intro hO
  exact zeta_ne_zero_of_bigO_psi_sub_self hO s hθ hs

end Commons.NumberTheory.Zeta