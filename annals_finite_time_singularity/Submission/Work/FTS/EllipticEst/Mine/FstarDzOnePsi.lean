import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Mine.sinCos2_cs_sEta
import Submission.Work.FTS.EllipticEst.Mine.integrable_hkIntegrand_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` on the *open* angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

/-- The angular weight `sin θ cos²θ` of the solvability condition is nonnegative on `Iθ`. -/
theorem sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- `w z > 0` for `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by rw [Work.Spaces.w, ← div_pow]
  rw [h]
  have : 0 < (1 + z) / z := div_pos (by linarith) hz
  positivity

/-- `w` is decreasing on `(0,∞)`, in the form used below. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have h2 : 0 ≤ 1 / b := by positivity
  have hbw : Work.Spaces.w b = (1 + 1 / b) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt hb)]
    ring
  have haw : Work.Spaces.w a = (1 + 1 / a) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow, add_div, div_self (ne_of_gt ha)]
    ring
  rw [hbw, haw]
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-! ## The pointwise slice domination -/

/-- **Pointwise slice domination.**  For `z₀ < s < 2z₀` and `θ ∈ Iθ`, the weighted slice of
`∂_z²Ψ` is bounded by the `ℋ^k`-integrand of `z ↦ z²∂_z²Ψ` at the same point. -/
theorem pzIter2_sq_sEta_le_HkIntegrand_pt {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    {z₀ : ℝ} (hz₀ : 0 < z₀) {s : ℝ} (hs : s ∈ Set.Ioo z₀ (2 * z₀)) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
        * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have hspos : 0 < s := lt_trans hz₀ hs.1
  have hsle : s ≤ 2 * z₀ := le_of_lt hs.2
  have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hkey : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
        * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = s ^ 4 * (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * Work.FTS.EllipticEst.sEta θ := by
    have hxx : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
      congr 1
      ring
    have hmid : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        = (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)))⁻¹ := by
      have h := Real.rpow_neg hx (-(Work.Spaces.eta / 2))
      rwa [neg_neg] at h
    rw [div_eq_mul_inv, hmid, inv_inv]
    simp only [mul_pow]
    rw [hxx]
    ring
  have hle1 : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
      * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
    Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ 0 (by omega)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
    Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
  have hcoef : 0 < 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) :=
    one_div_pos.mpr (mul_pos (by positivity) (pow_pos (w_pos hspos) 2))
  have hconst : 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) ≤ 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) := by
    have hws2 : (Work.Spaces.w (2 * z₀)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
      pow_le_pow_left₀ (w_pos (by linarith : (0:ℝ) < 2 * z₀)).le (w_antitone hspos hsle) 2
    have hz4 : z₀ ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (le_of_lt hz₀) (le_of_lt hs.1) 4
    have hden : z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 ≤ s ^ 4 * (Work.Spaces.w s) ^ 2 :=
      mul_le_mul hz4 hws2 (by positivity) (by positivity)
    have hpos : 0 < z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 :=
      mul_pos (by positivity) (pow_pos (w_pos (by linarith : (0:ℝ) < 2 * z₀)) 2)
    exact one_div_le_one_div_of_le hpos hden
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hwsne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos hspos)
  calc (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
          * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
              * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [hkey]
        field_simp
    _ ≤ (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
          * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
        mul_le_mul_of_nonneg_left hle1 hcoef.le
    _ ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
          * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
        mul_le_mul_of_nonneg_right hconst hHnn

/-! ## The slice domination by the `ℋ^k`-integrand -/

/-- **Slice domination.**  For `z₀ < s < 2z₀`, the weighted `L²`-slice of `∂_z²Ψ` against the
angular weight `sEta` is bounded by the `ℋ^k`-integrand of `z ↦ z²∂_z²Ψ`, with the explicit
constant `1/(z₀⁴·w(2z₀)²)`. -/
theorem pzIter2_sq_sEta_le_HkIntegrand {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemA : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    {z₀ : ℝ} (hz₀ : 0 < z₀) {s : ℝ} (hs : s ∈ Set.Ioo z₀ (2 * z₀)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ (1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2))
            * ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
  have hspos : 0 < s := lt_trans hz₀ hs.1
  have hsle : s ≤ 2 * z₀ := le_of_lt hs.2
  have h2pos : 0 < 2 * z₀ := by linarith
  have hsIz : s ∈ Work.Spaces.Iz := le_of_lt hspos
  set M : ℝ := 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) with hMdef
  -- the `ℋ^k`-integrand is integrable on the slice
  have hHk : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ) Work.Spaces.Iθ := hmemA.1 s hsIz
  -- the constant comparison
  have hconst : 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) ≤ M := by
    have hws2 : (Work.Spaces.w (2 * z₀)) ^ 2 ≤ (Work.Spaces.w s) ^ 2 :=
      pow_le_pow_left₀ (w_pos h2pos).le (w_antitone hspos hsle) 2
    have hz4 : z₀ ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (le_of_lt hz₀) (le_of_lt hs.1) 4
    have hden : z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 ≤ s ^ 4 * (Work.Spaces.w s) ^ 2 :=
      mul_le_mul hz4 hws2 (by positivity) (by positivity)
    have hpos : 0 < z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2 :=
      mul_pos (by positivity) (pow_pos (w_pos h2pos) 2)
    exact one_div_le_one_div_of_le hpos hden
  -- the pointwise bound
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ M * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    intro θ hθ
    have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    have hkey : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
          * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = s ^ 4 * (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ := by
      have hxx : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = Work.FTS.EllipticEst.sEta θ := by
        rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
        congr 1
        ring
      have hmid : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
          = (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)))⁻¹ := by
        have h := Real.rpow_neg hx (-(Work.Spaces.eta / 2))
        rwa [neg_neg] at h
      rw [div_eq_mul_inv, hmid, inv_inv]
      simp only [mul_pow]
      rw [hxx]
      ring
    have hle1 : ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
        * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
      Work.Spaces.sq_le_HkIntegrand_z α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ 0 (by omega)
    have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
    have hcoef : 0 < 1 / (s ^ 4 * (Work.Spaces.w s) ^ 2) :=
      one_div_pos.mpr (mul_pos (by positivity) (pow_pos (w_pos hspos) 2))
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hwsne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos hspos)
    calc (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
            * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ
                * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [hkey]
          field_simp
      _ ≤ (1 / (s ^ 4 * (Work.Spaces.w s) ^ 2))
            * Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
          mul_le_mul_of_nonneg_left hle1 hcoef.le
      _ ≤ M * Work.Spaces.HkIntegrand α k
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ :=
          mul_le_mul_of_nonneg_right hconst hHnn
  -- measurability of the integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hsin : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_snd)
      refine ContinuousOn.rpow_const hsin.continuousOn ?_
      intro p hp
      exact Or.inl (ne_of_gt (sin_two_pos_Ioo ⟨hp.2.1, hp.2.2⟩))
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).pow 2 |>.mul hsEta) hspos
  have hInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hHk.const_mul M) hmeas ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    filter_upwards with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
    exact hpt θ hθ
  refine ⟨hInt, ?_⟩
  have hmono : ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ M * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
    have hle_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ M * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ := by
      rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
      exact Eventually.of_forall (fun θ hθ => hpt θ hθ)
    have h := MeasureTheory.integral_mono_ae hInt (hHk.const_mul M) hle_ae
    rw [← MeasureTheory.integral_const_mul]
    exact h
  exact hmono

/-! ## Integrals over shrinking intervals -/

/-- **Absolute continuity of the Lebesgue integral, sequence form.**  If `g` is integrable on
`Ioc c (c+A)` with `A > 0`, the integrals over the shrinking sets `Ioc c (c + A/(n+1))` tend to
`0`. -/
theorem tendsto_integral_Ioc_shrink {g : ℝ → ℝ} {c A : ℝ} (hA : 0 < A)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioc c (c + A))) :
    Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc c (c + A / (n + 1 : ℝ)), g x)
      Filter.atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (Set.Ioc c (c + A / (n + 1 : ℝ))) :=
    fun _ => measurableSet_Ioc
  have hanti : Antitone (fun n : ℕ => Set.Ioc c (c + A / (n + 1 : ℝ))) := by
    intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have h1 : (0 : ℝ) < (m + 1 : ℝ) := by positivity
    have h3 : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hmn
    simpa using div_le_div_of_nonneg_left hA.le h1 h3
  have hfin : ∃ i : ℕ, MeasureTheory.IntegrableOn g (Set.Ioc c (c + A / (i + 1 : ℝ))) := by
    refine ⟨0, ?_⟩
    have h0 : c + A / ((0 : ℕ) + 1 : ℝ) = c + A := by norm_num
    rw [h0]; exact hg
  have hmain := MeasureTheory.tendsto_setIntegral_of_antitone hmeas hanti hfin
  have hempty : (⋂ n : ℕ, Set.Ioc c (c + A / (n + 1 : ℝ))) = ∅ := by
    have hmempty : ∀ x, x ∉ (⋂ n : ℕ, Set.Ioc c (c + A / (n + 1 : ℝ))) := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hxc : c < x := (hx 0).1
      have hpos : 0 < x - c := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (A / (x - c))
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos hA hpos) hn
      have hA_lt : A < (n : ℝ) * (x - c) := (div_lt_iff₀ hpos).mp hn
      have hlt : A / (n : ℝ) < x - c := by
        rw [div_lt_iff₀ hnpos]; linarith [hA_lt]
      have hle : A / ((n : ℝ) + 1) ≤ A / (n : ℝ) :=
        div_le_div_of_nonneg_left hA.le hnpos (by linarith)
      have : A / ((n : ℕ) + 1 : ℝ) < x - c := by
        push_cast
        linarith [hle, hlt]
      exact absurd (hx n).2 (not_le.mpr (by linarith))
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hmempty x
  rw [hempty, MeasureTheory.setIntegral_empty] at hmain
  exact hmain

/-! ## The main estimate -/

/-- The angular interval is, up to a null set, the open interval. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hfin : MeasureTheory.volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have h1 : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [h1, MeasureTheory.measure_union_null_iff]
    exact ⟨MeasureTheory.measure_singleton 0, MeasureTheory.measure_singleton _⟩
  rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hfin
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ
  push_neg at hθ
  obtain ⟨hI, hnot⟩ := hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h0 : θ = 0
  · exact Or.inl h0
  · refine Or.inr (le_antisymm hI.2 ?_)
    by_contra hlt
    push_neg at hlt
    exact hnot ⟨lt_of_le_of_ne hI.1 (Ne.symm h0), hlt⟩

/-- **The angular moment of `∂_zΨ` vanishes.**  For a datum of the weak class, the radial
derivative of the angular moment `F_*(Ψ)` is `F_*(∂_zΨ)`; since `F_*(Ψ) ≡ 0`, that moment
vanishes.  This is the `Ψ`-half of the moment chain. -/
theorem pz_moment_of_integrable {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ = 0 := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hZsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2)
  set L : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ with hLdef
  -- (1) the slices of `Ψ` are integrable against the angular weight
  have hΨslice : ∀ z : ℝ, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have habs : MeasureTheory.Integrable (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable hk h z hz).integrable
    have hnorm : MeasureTheory.Integrable (fun θ : ℝ => ‖Ψ z θ * Work.Elliptic.sinCos2 θ‖)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine habs.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hc1 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
        hsm.continuousOn
      have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
          Work.FTS.EllipticEst.Q0 := by
        show ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
          Work.FTS.EllipticEst.Q0
        fun_prop
      refine (Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) (hc1.mul hc2) hz).congr ?_
      filter_upwards with θ
      rfl
    exact (MeasureTheory.integrable_norm_iff hmeas).mp hnorm
  -- (2) the constants and the slice functional
  set C₂ : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ with hC₂def
  set M : ℝ := 1 / (z₀ ^ 4 * (Work.Spaces.w (2 * z₀)) ^ 2) with hMdef
  set Hki : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ with hHkidef
  have hzero : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (0 : ℝ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine (integrableOn_const (s := Work.Spaces.Iθ) (C := (0 : ℝ)) (by
      rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).congr ?_
    filter_upwards with θ
    simp
  obtain ⟨hC₂int, hC₂nn, -⟩ :=
    sinCos2_cs_sEta (u := fun _ : ℝ => (0 : ℝ)) hzero MeasureTheory.aestronglyMeasurable_const
  have hMnni : 0 ≤ M := by
    rw [hMdef]
    exact (one_div_pos.mpr (mul_pos (by positivity)
      (pow_pos (w_pos (by linarith : (0:ℝ) < 2 * z₀)) 2))).le
  -- (3) the estimate for every `hh ∈ (0, z₀)`
  have key : ∀ hh : ℝ, 0 < hh → hh < z₀ →
      |L| ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) := by
    intro hh hhpos hhlt
    have hhle : hh ≤ z₀ := le_of_lt hhlt
    have hzle : z₀ ≤ z₀ + hh := by linarith
    set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)) with hμdef
    set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hνdef
    have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hsEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        Work.FTS.EllipticEst.Q0 := by
      have hsin : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_snd)
      refine ContinuousOn.rpow_const hsin.continuousOn ?_
      intro p hp
      exact Or.inl (ne_of_gt (sin_two_pos_Ioo ⟨hp.2.1, hp.2.2⟩))
    have hbox_le : μ.prod ν ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Measure.prod_mono ?_ le_rfl
      rw [hμdef]
      exact MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
    have hbox_meas : MeasurableSet (Set.Ioc z₀ (z₀ + hh) ×ˢ Work.Spaces.Iθ) :=
      measurableSet_Ioc.prod hIθ_meas
    -- joint integrability of the `ℋ^k`-integrand on the slab
    have hHkbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) (μ.prod ν) :=
      (integrable_hkIntegrand_prod
        (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hZsm α k) h.memA).mono_measure hbox_le
    -- the quadratic slice function
    have hφaesm : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun z θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        (μ.prod ν) := by
      refine (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
        (((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).pow 2 |>.mul hsEta)).mono_measure hbox_le
    have hφbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        (μ.prod ν) := by
      refine MeasureTheory.Integrable.mono' (hHkbox.const_mul M) hφaesm ?_
      rw [hμdef, hνdef, MeasureTheory.Measure.prod_restrict,
        MeasureTheory.ae_restrict_iff' hbox_meas]
      filter_upwards with p hp
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hp.2))]
      exact pzIter2_sq_sEta_le_HkIntegrand_pt hz₀ ⟨hp.1.1, by linarith [hp.1.2, hhle]⟩ hp.2
    -- the `θ`-only weight
    have hone : MeasureTheory.Integrable
        (Function.uncurry (fun _ : ℝ => fun θ : ℝ =>
          (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) (μ.prod ν) := by
      have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const (1 : ℝ)
      refine (MeasureTheory.Integrable.mul_prod h1 hC₂int).congr ?_
      filter_upwards with p
      show (1 : ℝ) * ((Work.Elliptic.sinCos2 p.2) ^ 2 / Work.FTS.EllipticEst.sEta p.2)
        = (Work.Elliptic.sinCos2 p.2) ^ 2 / Work.FTS.EllipticEst.sEta p.2
      ring
    -- joint integrability of `|∂_z²Ψ|` against the angular weight
    have hιbox : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
        (μ.prod ν) := by
      have hv2 : ∀ θ ∈ Work.Spaces.Iθ,
          (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2 = Work.FTS.EllipticEst.sEta θ := by
        intro θ hθ
        have hx : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
        rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx]
        congr 1
        ring
      have hιaesm : MeasureTheory.AEStronglyMeasurable
          (Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ))
          (μ.prod ν) := by
        have hc1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2|)
            Work.FTS.EllipticEst.Q0 :=
          ((Work.FTS.EllipticEst.SmoothOpen.pzIter hsm 2).continuousOn).abs
        have hc2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
            Work.FTS.EllipticEst.Q0 := by
          show ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
            Work.FTS.EllipticEst.Q0
          fun_prop
        refine (Work.Spaces.aesm_of_continuousOn_Qd
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          (hc1.mul hc2)).mono_measure hbox_le
      refine MeasureTheory.Integrable.mono'
        ((hφbox.const_mul (1/2)).add (hone.const_mul (1/2))) hιaesm ?_
      rw [hμdef, hνdef, MeasureTheory.Measure.prod_restrict,
        MeasureTheory.ae_restrict_iff' hbox_meas]
      filter_upwards with p hp
      obtain ⟨a, b⟩ := p
      have hw0 : 0 ≤ Work.Elliptic.sinCos2 b := sinCos2_nonneg hp.2
      have hnorm : ‖Function.uncurry (fun z θ => |Work.Spaces.pzIter 2 Ψ z θ|
            * Work.Elliptic.sinCos2 θ) (a, b)‖
          = |Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b := by
        rw [Function.uncurry_apply_pair, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hw0)]
      rw [hnorm]
      change |Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b
        ≤ (1/2) * ((Work.Spaces.pzIter 2 Ψ a b) ^ 2 * Work.FTS.EllipticEst.sEta b)
          + (1/2) * ((Work.Elliptic.sinCos2 b) ^ 2 / Work.FTS.EllipticEst.sEta b)
      by_cases hv : Real.sin (2 * b) = 0
      · have hwz : Work.Elliptic.sinCos2 b = 0 := by
          obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hv
          have h2 : 2 * b = (k : ℝ) * Real.pi := hk.symm
          have hk0 : (0 : ℤ) ≤ k := by
            by_contra hc
            push_neg at hc
            have hk1 : k ≤ -1 := by omega
            have hk2 : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
            have h3 : (k : ℝ) * Real.pi ≤ -Real.pi := by nlinarith [Real.pi_pos]
            rw [← h2] at h3
            linarith [hp.2.1, Real.pi_pos]
          have hk1' : k ≤ 1 := by
            by_contra hc
            push_neg at hc
            have hk2 : (2 : ℤ) ≤ k := by omega
            have hk3 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
            have h3 : 2 * Real.pi ≤ (k : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
            rw [← h2] at h3
            linarith [hp.2.2, Real.pi_pos]
          interval_cases k
          · have hp0 : b = 0 := by
              have h2' : 2 * b = 0 := by simpa using h2
              linarith
            rw [Work.Elliptic.sinCos2, hp0]; simp
          · have hpp : b = Real.pi / 2 := by
              have h2' : 2 * b = Real.pi := by simpa using h2
              linarith
            rw [Work.Elliptic.sinCos2, hpp, Real.cos_pi_div_two]; simp
        rw [hwz, mul_zero]
        have hz0 : (0 : ℝ) ^ 2 / Work.FTS.EllipticEst.sEta b = 0 := by simp
        rw [hz0, mul_zero, add_zero]
        exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sEta_nonneg hp.2))
      · have hvpos : 0 < Real.sin (2 * b) := lt_of_le_of_ne (sin_two_nonneg_Iθ hp.2) (Ne.symm hv)
        set v : ℝ := Real.sin (2 * b) ^ (-(Work.Spaces.eta / 2)) with hvdef
        have hvne : v ≠ 0 := by
          rw [hvdef]
          exact ne_of_gt (Real.rpow_pos_of_pos hvpos _)
        have hv2p : v ^ 2 = Work.FTS.EllipticEst.sEta b := hv2 b hp.2
        have hamgm := two_mul_le_add_sq (|Work.Spaces.pzIter 2 Ψ a b| * v)
          (Work.Elliptic.sinCos2 b * v⁻¹)
        have hleft : 2 * (|Work.Spaces.pzIter 2 Ψ a b| * v) * (Work.Elliptic.sinCos2 b * v⁻¹)
            = 2 * (|Work.Spaces.pzIter 2 Ψ a b| * Work.Elliptic.sinCos2 b) := by
          have hvne' : v ≠ 0 := hvne
          field_simp
        have hright : (|Work.Spaces.pzIter 2 Ψ a b| * v) ^ 2 + (Work.Elliptic.sinCos2 b * v⁻¹) ^ 2
            = (Work.Spaces.pzIter 2 Ψ a b) ^ 2 * Work.FTS.EllipticEst.sEta b
              + (Work.Elliptic.sinCos2 b) ^ 2 / Work.FTS.EllipticEst.sEta b := by
          rw [mul_pow, mul_pow, sq_abs, hv2p, inv_pow, ← hv2p]
          ring
        rw [hleft, hright] at hamgm
        linarith [hamgm]
    -- the moment identity
    have hmom : ∫ θ in Work.Spaces.Iθ,
        (Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ = 0 := by
      rw [show (fun θ : ℝ => (Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
          = fun θ : ℝ => Ψ (z₀ + hh) θ * Work.Elliptic.sinCos2 θ
              - Ψ z₀ θ * Work.Elliptic.sinCos2 θ from by funext θ; ring]
      rw [MeasureTheory.integral_sub (hΨslice (z₀ + hh) (by linarith)) (hΨslice z₀ hz₀)]
      rw [show (∫ θ in Work.Spaces.Iθ, Ψ (z₀ + hh) θ * Work.Elliptic.sinCos2 θ) = 0 from
            h.orthPsi (z₀ + hh) (by linarith),
          show (∫ θ in Work.Spaces.Iθ, Ψ z₀ θ * Work.Elliptic.sinCos2 θ) = 0 from h.orthPsi z₀ hz₀]
      ring
    -- the difference quotient and the `z`-integral of the second derivative
    set Afun : ℝ → ℝ := fun θ => (1/hh) * ((Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
      with hAdef
    set Gfun : ℝ → ℝ := fun θ => ∫ z in z₀..(z₀ + hh),
        (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) with hGdef
    have hAint : MeasureTheory.Integrable Afun (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine ((MeasureTheory.Integrable.sub (hΨslice (z₀ + hh) (by linarith))
        (hΨslice z₀ hz₀)).const_mul (1/hh)).congr ?_
      filter_upwards with θ
      simp only [hAdef, Pi.sub_apply]
      ring
    have hAzero : ∫ θ in Work.Spaces.Iθ, Afun θ = 0 := by
      rw [hAdef]
      rw [MeasureTheory.integral_const_mul, hmom, mul_zero]
    have hAG : ∀ θ ∈ Set.Ioo 0 (π/2),
        Afun θ = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          + Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ := by
      intro θ hθi
      have hInt1 : IntervalIntegrable (fun z => Work.Spaces.pz Ψ z θ) volume z₀ (z₀ + hh) := by
        have hc : ContinuousOn (fun z : ℝ => Work.Spaces.pz Ψ z θ) (Set.uIcc z₀ (z₀ + hh)) := by
          refine ((hsm.pz.curry_z hθi).continuousOn).mono ?_
          intro z hz
          rw [Set.uIcc_of_le hzle] at hz
          exact lt_of_lt_of_le hz₀ hz.1
        exact hc.intervalIntegrable
      have hderiv : ∀ z ∈ Set.uIcc z₀ (z₀ + hh),
          HasDerivAt (fun z' : ℝ => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z := by
        intro z hz
        rw [Set.uIcc_of_le hzle] at hz
        exact hsm.hasDerivAt_slice hθi (lt_of_lt_of_le hz₀ hz.1)
      have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt1
      have hdiff : IntervalIntegrable (fun z => Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
          volume z₀ (z₀ + hh) := hInt1.sub intervalIntegrable_const
      have hftc : Ψ (z₀ + hh) θ - Ψ z₀ θ = hh * Work.Spaces.pz Ψ z₀ θ + Gfun θ := by
        rw [hGdef, ← hftc0]
        rw [show (fun z : ℝ => Work.Spaces.pz Ψ z θ)
            = fun z : ℝ => Work.Spaces.pz Ψ z₀ θ
              + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) from by funext z; ring]
        rw [intervalIntegral.integral_add intervalIntegrable_const hdiff,
          intervalIntegral.integral_const]
        ring
      change (1/hh) * ((Ψ (z₀ + hh) θ - Ψ z₀ θ) * Work.Elliptic.sinCos2 θ)
        = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          + Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
      rw [hftc]
      field_simp
      ring
    have hGint : MeasureTheory.Integrable (fun θ : ℝ => (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hf : MeasureTheory.Integrable
          (fun θ : ℝ => Afun θ - Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := MeasureTheory.Integrable.sub hAint hint
      refine hf.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas, ae_mem_Ioo_Iθ] with θ hθ hθi
      show Afun θ - Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
        = (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
      rw [hAG θ hθi]
      ring
    have hval : L = -∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ) := by
      have h1 := MeasureTheory.integral_sub hAint hint
      have h2 : ∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)
          = (∫ θ in Work.Spaces.Iθ, Afun θ)
            - ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ := by
        rw [← h1]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas, ae_mem_Ioo_Iθ] with θ hθ hθi
        rw [hAG θ hθi]
        ring
      have h3 : L = -((∫ θ in Work.Spaces.Iθ, Afun θ)
            - ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ) := by
        rw [hLdef, hAzero]
        ring
      rw [h3, h2]
    -- the pointwise bound on the difference quotient
    have hGbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Gfun θ| ≤ hh * ∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ| := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθi
      have hcont2 : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Icc z₀ (z₀ + hh)) := by
        refine ((hsm.pzIter 2).curry_z hθi).continuousOn.mono ?_
        intro z hz
        exact lt_of_lt_of_le hz₀ hz.1
      have hslice_int : MeasureTheory.IntegrableOn (fun z : ℝ => |Work.Spaces.pzIter 2 Ψ z θ|)
          (Set.Ioc z₀ (z₀ + hh)) := by
        have h0 : MeasureTheory.IntegrableOn (fun z : ℝ => Work.Spaces.pzIter 2 Ψ z θ)
            (Set.Icc z₀ (z₀ + hh)) := hcont2.integrableOn_Icc
        exact MeasureTheory.IntegrableOn.mono_set h0.abs
          (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
      have hzb : ∀ z ∈ Set.Ioc z₀ (z₀ + hh),
          |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
        intro z hz
        have hzle' : z₀ ≤ z := le_of_lt hz.1
        have hcontz : ContinuousOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) (Set.Icc z₀ z) := by
          refine ((hsm.pzIter 2).curry_z hθi).continuousOn.mono ?_
          intro z' hz'
          exact lt_of_lt_of_le hz₀ hz'.1
        have hcontu : ContinuousOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ) (Set.uIcc z₀ z) := by
          rw [Set.uIcc_of_le hzle']; exact hcontz
        have hderiv : ∀ z' ∈ Set.uIcc z₀ z,
            HasDerivAt (fun z'' : ℝ => Work.Spaces.pzIter 1 Ψ z'' θ)
              (Work.Spaces.pzIter 2 Ψ z' θ) z' := by
          intro z' hz'
          rw [Set.uIcc_of_le hzle'] at hz'
          exact hsm.hasDerivAt_slice_pzIter 1 hθi (lt_of_lt_of_le hz₀ hz'.1)
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcontu.intervalIntegrable
        have hftc' : ∫ y in z₀..z, Work.Spaces.pzIter 2 Ψ y θ
            = Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ := by
          simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hftc
        have e1 : Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ
            = ∫ z' in Set.Ioc z₀ z, Work.Spaces.pzIter 2 Ψ z' θ := by
          rw [← hftc', intervalIntegral.integral_of_le hzle']
        rw [e1]
        have hIntg : MeasureTheory.IntegrableOn (fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
            (Set.Ioc z₀ z) :=
          MeasureTheory.IntegrableOn.mono_set hcontz.integrableOn_Icc
            (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
        have hstep1 : |∫ z' in Set.Ioc z₀ z, Work.Spaces.pzIter 2 Ψ z' θ|
            ≤ ∫ z' in Set.Ioc z₀ z, |Work.Spaces.pzIter 2 Ψ z' θ| := by
          have := MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict (Set.Ioc z₀ z))
            (f := fun z' : ℝ => Work.Spaces.pzIter 2 Ψ z' θ)
          simpa only [Real.norm_eq_abs] using this
        have hsub : MeasureTheory.volume.restrict (Set.Ioc z₀ z)
            ≤ MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)) :=
          MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
            (fun x hx => ⟨hx.1, le_trans hx.2 hz.2⟩)
        have hstep2 : ∫ z' in Set.Ioc z₀ z, |Work.Spaces.pzIter 2 Ψ z' θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
          have := MeasureTheory.integral_mono_measure hsub
            (Eventually.of_forall (fun x => abs_nonneg _)) hslice_int
          simpa only [Real.norm_eq_abs] using this
        exact hstep1.trans hstep2
      have hGfac : Gfun θ = ∫ z in Set.Ioc z₀ (z₀ + hh),
          (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) := by
        rw [hGdef]
        exact intervalIntegral.integral_of_le hzle
      rw [hGfac]
      have hc : ContinuousOn (fun z : ℝ => Work.Spaces.pz Ψ z θ) (Set.Icc z₀ (z₀ + hh)) := by
        refine ((hsm.pz.curry_z hθi).continuousOn).mono ?_
        intro z hz
        exact lt_of_lt_of_le hz₀ hz.1
      have hf_int : MeasureTheory.IntegrableOn (fun z : ℝ =>
          Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) (Set.Ioc z₀ (z₀ + hh)) := by
        have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ =>
            Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ) (Set.Icc z₀ (z₀ + hh)) :=
          MeasureTheory.IntegrableOn.sub hc.integrableOn_Icc
            (MeasureTheory.integrableOn_const (s := Set.Icc z₀ (z₀ + hh)) (C := Work.Spaces.pz Ψ z₀ θ)
              (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        exact MeasureTheory.IntegrableOn.mono_set hIcc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
      have hstep1 : |∫ z in Set.Ioc z₀ (z₀ + hh),
            (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)|
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| := by
        have := MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh)))
          (f := fun z : ℝ => Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
        simpa only [Real.norm_eq_abs] using this
      refine hstep1.trans ?_
      have hInt2 : MeasureTheory.IntegrableOn (fun _ : ℝ =>
          ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ|)
          (Set.Ioc z₀ (z₀ + hh)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
          |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ|
            ≤ ∫ z' in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z' θ| := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall (fun z hz => hzb z hz)
      refine (MeasureTheory.integral_mono_ae hf_int.abs hInt2 hle_ae).trans ?_
      · have hstep : ∫ z in Set.Ioc z₀ (z₀ + hh), (∫ z' in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z' θ|) = hh * ∫ z' in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z' θ| := by
          rw [← intervalIntegral.integral_of_le hzle, intervalIntegral.integral_const]
          ring
        rw [hstep]
    -- Cauchy–Schwarz on the slab
    have hB : ∀ z ∈ Set.Ioc z₀ (z₀ + hh),
        (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
      intro z hz
      have hzpos : 0 < z := lt_trans hz₀ hz.1
      have hzIoo : z ∈ Set.Ioo z₀ (2 * z₀) := ⟨hz.1, by linarith [hz.2, hhle]⟩
      obtain ⟨hAint, hAle⟩ := pzIter2_sq_sEta_le_HkIntegrand hsm h.memA hz₀ hzIoo
      obtain ⟨-, hC₂nn', -, hCSineq⟩ := sinCos2_cs_sEta hAint (hsm.aesm_slice_pzIter 2 hzpos)
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ hθ => mul_nonneg (abs_nonneg _) (sinCos2_nonneg hθ))
      have hHknn : 0 ≤ Hki z := by
        rw [hHkidef]
        exact MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg _ _ _ _ _)
      have hsq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (C₂ * M) * Hki z := by
        refine le_trans hCSineq ?_
        have h1 : ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ ≤ M * Hki z := by
          rw [hMdef, hHkidef]
          exact hAle
        calc C₂ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ C₂ * (M * Hki z) := mul_le_mul_of_nonneg_left h1 hC₂nn
          _ = (C₂ * M) * Hki z := by ring
      calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ|
              * Work.Elliptic.sinCos2 θ) ^ 2) := (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt ((C₂ * M) * Hki z) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := Real.sqrt_mul (mul_nonneg hC₂nn hMnni) _
    -- swapping the two integrals
    have hKle : ∀ θ : ℝ, (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
        * Work.Elliptic.sinCos2 θ
        = ∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ := by
      intro θ
      rw [MeasureTheory.integral_mul_const]
    have hswap : ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
          |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ
        = ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) := by
      have h1 : ∫ θ, (∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ) ∂ν
          = ∫ z, (∫ θ, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂ν) ∂μ :=
        (MeasureTheory.integral_integral_swap hιbox).symm
      have h2 : ∫ θ, (∫ z, (|Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) ∂μ) ∂ν
          = ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
              |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with θ
        rw [← hKle θ]
      rw [← h2, h1]
    have hole : ∫ z in Set.Ioc z₀ (z₀ + hh),
          (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) := by
      have hHki_nn : ∀ z : ℝ, 0 ≤ Hki z := by
        intro z
        rw [hHkidef]
        exact MeasureTheory.setIntegral_nonneg hIθ_meas
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg _ _ _ _ _)
      have hHkIloc : MeasureTheory.IntegrableOn Hki (Set.Ioc z₀ (z₀ + hh)) :=
        h.memA.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
      have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc z₀ (z₀ + hh)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      have hsqrt : MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt (Hki z))
          (Set.Ioc z₀ (z₀ + hh)) := by
        refine MeasureTheory.Integrable.mono' (hone.add hHkIloc)
          (Real.continuous_sqrt.comp_aestronglyMeasurable
            (MeasureTheory.Integrable.aestronglyMeasurable hHkIloc)) ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with z hz
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_iff]
        refine ⟨?_, ?_⟩
        · show (0 : ℝ) ≤ 1 + Hki z
          linarith [hHki_nn z]
        · show Hki z ≤ ((1 : ℝ) + Hki z) ^ 2
          nlinarith [hHki_nn z, sq_nonneg (Hki z)]
      have hBint : MeasureTheory.IntegrableOn (fun z : ℝ =>
          ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          (Set.Ioc z₀ (z₀ + hh)) := hιbox.integral_prod_left
      have h2int : MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt (C₂ * M) * Real.sqrt (Hki z))
          (Set.Ioc z₀ (z₀ + hh)) := hsqrt.const_mul _
      have hmono : ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
        have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
              ≤ Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := by
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall (fun z hz => hB z hz)
        exact MeasureTheory.integral_mono_ae hBint h2int hle_ae
      have h3 : ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z)
          ≤ hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z := by
        have h4 : MeasureTheory.IntegrableOn (fun z : ℝ => (1 : ℝ) + Hki z)
            (Set.Ioc z₀ (z₀ + hh)) := hone.add hHkIloc
        have h6 : ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z)
            ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), ((1 : ℝ) + Hki z) := by
          have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
              Real.sqrt (Hki z) ≤ (1 : ℝ) + Hki z := by
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
            filter_upwards with z hz
            rw [Real.sqrt_le_iff]
            refine ⟨?_, ?_⟩
            · show (0 : ℝ) ≤ 1 + Hki z
              linarith [hHki_nn z]
            · show Hki z ≤ ((1 : ℝ) + Hki z) ^ 2
              nlinarith [hHki_nn z, sq_nonneg (Hki z)]
          exact MeasureTheory.integral_mono_ae hsqrt h4 hle_ae
        have h7 : ∫ z in Set.Ioc z₀ (z₀ + hh), ((1 : ℝ) + Hki z)
            = hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z := by
          rw [MeasureTheory.integral_add hone hHkIloc]
          congr 1
          rw [← intervalIntegral.integral_of_le hzle, intervalIntegral.integral_const]
          ring
        rw [h7] at h6
        exact h6
      calc ∫ z in Set.Ioc z₀ (z₀ + hh),
            (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
          ≤ ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (C₂ * M) * Real.sqrt (Hki z) := hmono
        _ = Real.sqrt (C₂ * M) * ∫ z in Set.Ioc z₀ (z₀ + hh), Real.sqrt (Hki z) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Real.sqrt (C₂ * M) * (hh + ∫ z in Set.Ioc z₀ (z₀ + hh), Hki z) :=
            mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    -- the final estimate
    have h1 : |L| = |∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)| := by
      rw [hval, abs_neg]
    have h2 : |∫ θ in Work.Spaces.Iθ, (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)| := by
      have := MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ : ℝ => (1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ))
      simpa only [Real.norm_eq_abs] using this
    have h3 : ∫ θ in Work.Spaces.Iθ, |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, (∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ := by
      have h4 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|) Work.Spaces.Iθ := hGint.abs
      have h5 : MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ z in Set.Ioc z₀ (z₀ + hh),
            |Work.Spaces.pzIter 2 Ψ z θ|) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
        refine (hιbox.integral_prod_right).congr ?_
        filter_upwards with θ
        exact (hKle θ).symm
      have hle_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          |(1/hh) * (Gfun θ * Work.Elliptic.sinCos2 θ)|
            ≤ (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
              * Work.Elliptic.sinCos2 θ := by
        filter_upwards [hGbound, MeasureTheory.ae_restrict_mem hIθ_meas] with θ hgb hθ
        rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hhpos), abs_of_nonneg (sinCos2_nonneg hθ)]
        calc (1 / hh) * (|Gfun θ| * Work.Elliptic.sinCos2 θ)
          ≤ (1 / hh) * ((hh * ∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
            * Work.Elliptic.sinCos2 θ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hgb (sinCos2_nonneg hθ))
              (by positivity)
        _ = (∫ z in Set.Ioc z₀ (z₀ + hh), |Work.Spaces.pzIter 2 Ψ z θ|)
            * Work.Elliptic.sinCos2 θ := by
            field_simp
      exact MeasureTheory.integral_mono_ae h4 h5 hle_ae
    exact h1 ▸ h2.trans (h3.trans (hswap ▸ hole))
  -- (4) the limit
  have hbound' : ∀ n : ℕ,
      |L| ≤ Real.sqrt (C₂ * M) * (z₀ / (n + 2 : ℝ)
        + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) := by
    intro n
    refine key (z₀ / (n + 2 : ℝ)) (by positivity) ?_
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ((n : ℝ) + 2))]
    nlinarith [hz₀]
  have hki_int : MeasureTheory.IntegrableOn Hki (Set.Ioc z₀ (z₀ + z₀)) :=
    h.memA.2.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le hz₀ (le_of_lt hx.1)))
  have hlimHki : Filter.Tendsto (fun n : ℕ =>
      ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) Filter.atTop (nhds 0) := by
    refine (tendsto_integral_Ioc_shrink hz₀ hki_int).comp
      (tendsto_add_atTop_nat 1) |>.congr' ?_
    filter_upwards with n
    show (∫ x in Set.Ioc z₀ (z₀ + z₀ / (((n + 1 : ℕ) : ℝ) + 1)), Hki x)
      = ∫ x in Set.Ioc z₀ (z₀ + z₀ / ((n : ℝ) + 2)), Hki x
    congr 2
    push_cast
    ring
  have hlimh : Filter.Tendsto (fun n : ℕ => z₀ / (n + 2 : ℝ)) Filter.atTop (nhds 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (z₀)).comp
      (tendsto_add_atTop_nat 2) |>.congr' ?_
    filter_upwards with n
    show z₀ / (((n + 2 : ℕ)) : ℝ) = z₀ / ((n : ℝ) + 2)
    congr 1
    push_cast
    ring
  have hlim : Filter.Tendsto (fun n : ℕ => Real.sqrt (C₂ * M) * (z₀ / (n + 2 : ℝ)
      + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z)) Filter.atTop (nhds 0) := by
    have hh : Filter.Tendsto (fun n : ℕ => z₀ / (n + 2 : ℝ)
        + ∫ z in Set.Ioc z₀ (z₀ + z₀ / (n + 2 : ℝ)), Hki z) Filter.atTop (nhds 0) := by
      simpa using hlimh.add hlimHki
    simpa using hh.const_mul (Real.sqrt (C₂ * M))
  have hLle : |L| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound')
  have hL0 : L = 0 := abs_eq_zero.mp (le_antisymm hLle (abs_nonneg L))
  exact hL0

theorem pz_moment_eq_zero {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z : ℝ, 0 < z → ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ = 0 := by
  intro z hz
  by_cases hint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · exact pz_moment_of_integrable hk h hz hint
  · exact MeasureTheory.integral_undef hint

theorem FstarDzOnePsi : ∀ (α : ℝ) {k : ℕ}, 1 ≤ k → ∀ (F Ψ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
  intro α k hk F Ψ h z hz
  rw [Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) from by
    funext θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring]
  rw [MeasureTheory.integral_const_mul, pz_moment_eq_zero hk h z hz, mul_zero]

end Work.FTS.EllipticEst.Mine
