import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.contDiff_primitive_intervalIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory Set
open scoped Topology

/-- A smooth compactly supported test function with zero integral admits a smooth compactly
supported primitive whose topological support stays inside the same open interval as the
support of the original function. -/
theorem exists_primitive_tsupport_subset {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Set.Ioo a b) (hint : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Set.Ioo a b ∧ deriv ψ = φ := by
  rcases le_or_gt b a with hba | hab
  · -- Degenerate case: `(a, b)` is empty, so `φ` is the zero function.
    have hIoo : Set.Ioo a b = ∅ := Set.Ioo_eq_empty (not_lt.mpr hba)
    have hts : tsupport φ = ∅ := by
      rw [hIoo] at hφs
      exact Set.eq_empty_iff_forall_notMem.2 fun x hx => hφs hx
    have hφ0 : φ = 0 := by
      funext x
      by_contra hx
      have hmem : x ∈ tsupport φ :=
        subset_tsupport φ (by simpa [Function.mem_support] using hx)
      rw [hts] at hmem
      exact hmem
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · rw [tsupport_zero]; exact Set.empty_subset _
    · rw [hφ0]; funext x; exact deriv_const x 0
  · -- Main case `a < b`.
    have hφcont : Continuous φ := hφ.continuous
    have hφzero_off : ∀ x, x ∉ Set.Ioo a b → φ x = 0 :=
      fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφs h)
    have ha_not : a ∉ tsupport φ := fun h => (lt_irrefl a) (hφs h).1
    have hb_not : b ∉ tsupport φ := fun h => (lt_irrefl b) (hφs h).2
    have ha_nhds : (tsupport φ)ᶜ ∈ 𝓝 a :=
      (isClosed_tsupport φ).isOpen_compl.mem_nhds ha_not
    have hb_nhds : (tsupport φ)ᶜ ∈ 𝓝 b :=
      (isClosed_tsupport φ).isOpen_compl.mem_nhds hb_not
    obtain ⟨εa, hεa_pos, hεa_sub⟩ := Metric.mem_nhds_iff.mp ha_nhds
    obtain ⟨εb, hεb_pos, hεb_sub⟩ := Metric.mem_nhds_iff.mp hb_nhds
    have hεa : ∀ y, dist y a < εa → φ y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (hεa_sub (Metric.mem_ball.mpr hy))
    have hεb : ∀ y, dist y b < εb → φ y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (hεb_sub (Metric.mem_ball.mpr hy))
    -- The integral of `φ` over `a..b` vanishes.
    have hintAB : ∫ t in a..b, φ t = 0 := by
      have h1 : ∫ t in a..b, φ t = ∫ t, φ t := by
        rw [intervalIntegral.integral_of_le hab.le,
          ← setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hφzero_off x hx
      rw [h1, hint]
    -- The primitive vanishes on a left-neighbourhood of `a` and a right-neighbourhood of `b`.
    have hleft : ∀ y, y < a + εa → (∫ t in a..y, φ t) = 0 := by
      intro y hy
      have hzero : Set.EqOn φ 0 (Set.uIcc a y) := by
        intro t ht
        simp only [Pi.zero_apply]
        rcases le_or_gt t a with hta | hta
        · exact hφzero_off t (fun ht' => absurd (Set.mem_Ioo.mp ht').1 (not_lt_of_ge hta))
        · have hty : t ≤ y := by
            rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h2
            · exact absurd h2 (not_le.mpr hta)
          have hdist : dist t a < εa := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            linarith
          exact hεa t hdist
      calc (∫ t in a..y, φ t) = ∫ t in a..y, (0 : ℝ) := intervalIntegral.integral_congr hzero
        _ = 0 := intervalIntegral.integral_zero
    have hright : ∀ y, b - εb < y → (∫ t in a..y, φ t) = 0 := by
      intro y hy
      have hby : (∫ t in b..y, φ t) = 0 := by
        have hzero : Set.EqOn φ 0 (Set.uIcc b y) := by
          intro t ht
          simp only [Pi.zero_apply]
          rcases lt_or_ge t b with htb | htb
          · have hyt : y ≤ t := by
              rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact absurd h1 (not_le.mpr htb)
              · exact h1
            have hdist : dist t b < εb := by
              rw [Real.dist_eq, abs_of_neg (by linarith)]
              linarith
            exact hεb t hdist
          · exact hφzero_off t (fun ht' => absurd (Set.mem_Ioo.mp ht').2 (not_lt_of_ge htb))
        calc (∫ t in b..y, φ t) = ∫ t in b..y, (0 : ℝ) := intervalIntegral.integral_congr hzero
          _ = 0 := intervalIntegral.integral_zero
      have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hφcont.intervalIntegrable a b) (hφcont.intervalIntegrable b y)
      rw [hintAB, hby, zero_add] at hsum
      exact hsum.symm
    -- The topological support of the primitive is contained in `(a, b)`.
    have hsupp_sub : Function.support (fun x => ∫ t in a..x, φ t) ⊆
        Set.Icc (a + εa) (b - εb) := by
      intro x hx
      rw [Function.mem_support] at hx
      rw [Set.mem_Icc]
      constructor
      · by_contra h
        rw [not_le] at h
        exact hx (hleft x h)
      · by_contra h
        rw [not_le] at h
        exact hx (hright x h)
    have hts_sub : tsupport (fun x => ∫ t in a..x, φ t) ⊆ Set.Ioo a b :=
      (closure_minimal hsupp_sub isClosed_Icc).trans fun x hx => by
        rw [Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1, hεa_pos], by linarith [hx.2, hεb_pos]⟩
    obtain ⟨hψC, hψderiv⟩ :=
      contDiff_primitive_intervalIntegral (f := φ) (a := a) hφ
    exact ⟨fun x => ∫ t in a..x, φ t, hψC,
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
        (hts_sub.trans Set.Ioo_subset_Icc_self),
      hts_sub, hψderiv⟩

end Commons.Analysis.Calculus