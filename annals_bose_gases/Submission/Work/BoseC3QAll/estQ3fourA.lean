import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.sum_abs_kA1_le
import Submission.Work.BoseC3QAll.sum_abs_kA2_le
import Submission.Work.BoseC3QAll.sum_abs_kA3_le
import Submission.Work.BoseC3QAll.sum_sq_kA4_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.estQ3fourA` — FS `eq:EstimateQ3Tilde4`, absolute

The fourth estimate of FS `lem:EstimatesOnQ3-js` (FS ll. 2790-2870): the
commutator piece `Q₃⁽⁴⁾` together with the linear term
`ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds` and the kinetic reserve `(b/100)ℓ⁻²n₊`
is bounded below by `-e4A·‖Φ‖²` on FS's window.

The definitions and the reduction to the four coefficient sums `kA1 … kA4` are in
`Submission.Work.BoseB7AK.estQ3fourADefs`; the four coefficient bounds are the
modules `sum_abs_kA1_le`, `sum_abs_kA2_le`, `sum_abs_kA3_le`, `sum_sq_kA4_le`.
-/

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

theorem estQ3fourA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Work.BoseC3QAll.EstQ3fourA K₀ b₀ hb₀ := by
  obtain ⟨tK, htKpos, hKb⟩ := kernel_basic K₀ b₀ hb₀
  set Cα : ℝ := 12 * (64 * K₀) ^ 2 + 4 * (64 * K₀) ^ 4 with hCα
  set Ca : ℝ := 4 * K₀ ^ 2 + 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8)
      + 16 * (1 + (64 * K₀) ^ 2) * (max K₀ 0) ^ 3 * Real.sqrt (max K₀ 0) with hCa
  have hCann : 0 ≤ Ca := by
    rw [hCa]
    have h1 : 0 ≤ (max K₀ 0) ^ 3 := by positivity
    have h2 : 0 ≤ Real.sqrt (max K₀ 0) := Real.sqrt_nonneg _
    positivity
  refine ⟨Ca, min tK ((1 / 4 : ℝ) ^ 36), hCann, lt_min htKpos (by norm_num), ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK Φ hΦ
  -- ### thresholds and the hypotheses derived from the kernel and the parameters
  have htK : hv.t ≤ tK := le_trans htle (min_le_left _ _)
  have htq : hv.t ≤ (1 / 4 : ℝ) ^ 36 := le_trans htle (min_le_right _ _)
  obtain ⟨hαeven, hAB, hhalf, hαsmall, _hD⟩ := hKb F T E hv htK hb hK
  have hPHq : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i :=
    fun i hi => PH_subset_PHq F E hv i hi
  have hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k) :=
    fun s k hfL hk hW => sub_mem_PHq F E hv (ratio_small8 E hv htq)
      (fun a b hf hk' hW' => hK.kmom_subW a b hf hk' hW')
      (fun s hf => hK.fL_supp2 s hf) hfL hk hW
  have hsubst : SubstHypG F T E :=
    substHypG_of_kernel hK hαeven fun s k hfL hk hW => ⟨by
        have h1 := hhalf k (hPHq k (Finset.mem_filter.mp hk).2)
        intro hc
        linarith,
      by
        have h1 := hhalf (s - k) (hsub s k hfL hk hW)
        intro hc
        linarith⟩
  -- ### scalar facts
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hK₀ : 0 ≤ K₀ := K0_nonneg_of_kernel K₀ F T E hv hK
  have hη1 : eta E ≤ 1 := eta_le_one E hv
  have hη0 : 0 ≤ eta E := eta_nonneg E hv
  have hMnn : 0 ≤ E.bigM := Work.BoseB7.bigM_nonneg E hv
  have hnom : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
  have hρ0 : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hμ0 : 0 < E.mu := Work.BoseB7.mu_pos E hv
  have ha0 : 0 < E.aScat := hv.a_pos
  have h𝓁0 : 0 ≤ E.lille := lille_nonneg E hv
  -- ### the four coefficient bounds
  have hT1 := sum_abs_kA1_le K₀ F T E hK hv
  have hT2 := sum_abs_kA2_le K₀ F T E hK hv
  have hT3 := sum_abs_kA3_le K₀ F T E hK hv hK₀ hhalf hαsmall hsub
  have hT4 := sum_sq_kA4_le K₀ F T E hK hv hK₀ hhalf hαsmall hsub
  -- ### the four `e4A` terms
  have heta := e4A_ge_eta E hv hbpos
  have hKH := e4A_ge_KH E hv hbpos
  have htail := e4A_ge_tail E hv hbpos
  have hE0 := e4A_ge_E0 E hv hbpos
  -- ### splitting `Q₃⁽⁴⁾ + linOpT` into its four words
  set Z : ℝ := E.z / E.ell ^ 3 with hZ
  have hZabs : |Z| * E.ell ^ 3 = |E.z| := by
    rw [hZ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < E.ell ^ 3)]
    field_simp
  have hword : T.Q3fourT E + T.linOpT E
      = ∑ s ∈ excited Mode, (q3fourCoefA F E s) • (T.taDag s + T.ta s) :=
    Q3fourT_add_linOpT F T E hsubst
  have hsplit : (∑ s ∈ excited Mode, (q3fourCoefA F E s) • (T.taDag s + T.ta s))
      = (∑ s ∈ excited Mode, (Z * kA1 F E s) • (T.taDag s + T.ta s))
        + (∑ s ∈ excited Mode, (Z * kA2 F E s) • (T.taDag s + T.ta s))
        + (∑ s ∈ excited Mode, (Z * kA3 F E s) • (T.taDag s + T.ta s))
        + (∑ s ∈ excited Mode, (Z * kA4 F E s) • (T.taDag s + T.ta s)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [q3fourCoefA_eq F E s (ne_of_gt hℓ), ← hZ, mul_add, mul_add, mul_add,
      add_smul, add_smul, add_smul]
  -- ### the form bounds for the four words
  have hq1 := linear_word_bound F T hMnn hΦ (fun s => Z * kA1 F E s)
  have hq2 := linear_word_bound F T hMnn hΦ (fun s => Z * kA2 F E s)
  have hq3 := linear_word_bound F T hMnn hΦ (fun s => Z * kA3 F E s)
  have hq4 := linear_word_bound F T hMnn hΦ (fun s => Z * kA4 F E s)
  have hs1 := sqrt_sum_sq_mul_le Z (fun s => kA1 F E s)
  have hs2 := sqrt_sum_sq_mul_le Z (fun s => kA2 F E s)
  have hs4 : Real.sqrt (∑ s ∈ excited Mode, (Z * kA4 F E s) ^ 2)
      = |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2) :=
    sqrt_sum_sq_mul Z (fun s => kA4 F E s)
  -- ### the `kA3` word, absorbed in the kinetic reserve
  set Kr3 : ℝ := K₀ * (Cα * E.lille ^ 2 * (2 * E.rho * K₀ * E.aScat) * E.ell ^ 3) with hKr3
  have hKr3nn : 0 ≤ Kr3 := by
    rw [hKr3]
    have h1 : 0 ≤ E.lille ^ 2 := sq_nonneg _
    have h3 : 0 ≤ E.ell ^ 3 := by positivity
    have h4 : 0 ≤ Cα := by rw [hCα]; positivity
    have h5 : 0 ≤ 2 * E.rho * K₀ * E.aScat :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) hK₀) ha0.le
    exact mul_nonneg hK₀ (mul_nonneg (mul_nonneg (mul_nonneg h4 h1) h5) h3)
  have hkA3le : ∀ s ∈ excited Mode, (|kA3 F E s| : ℝ) ≤ Kr3 := by
    intro s hs
    rw [hKr3, hCα]
    have h1 : (|kA3 F E s| : ℝ) ≤ ∑ t ∈ excited Mode, (|kA3 F E t| : ℝ) :=
      Finset.single_le_sum (f := fun t => (|kA3 F E t| : ℝ))
        (fun t _ => abs_nonneg (kA3 F E t)) hs
    exact le_trans h1 (by simpa using hT3)
  have hM₀ : ∀ s ∈ excited Mode, (|Z * kA3 F E s| : ℝ) ≤ |Z| * Kr3 := by
    intro s hs
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hkA3le s hs) (abs_nonneg Z)
  have hsum3 : (∑ s ∈ excited Mode, |Z * kA3 F E s|) ≤ |Z| * Kr3 := by
    have h : (∑ s ∈ excited Mode, |Z * kA3 F E s|)
        = |Z| * (∑ s ∈ excited Mode, |kA3 F E s|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [abs_mul]
    rw [h]
    exact mul_le_mul_of_nonneg_left hT3 (abs_nonneg Z)
  have hgap := qw_gap_absorb F T E hbpos hℓ (excited Mode)
    (fun s hs => (Finset.mem_erase.mp hs).1) (mul_nonneg (abs_nonneg Z) hKr3nn) hM₀ Φ
  -- ### the five scalar estimates
  have hS1 : 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA1 F E s|)
      ≤ 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat
          * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) := by
    have h1 : |Z| * (∑ s ∈ excited Mode, |kA1 F E s|)
        ≤ |Z| * (E.rho * E.ell ^ 3 * (K₀ * E.aScat)
          * (K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)))) :=
      mul_le_mul_of_nonneg_left hT1 (abs_nonneg Z)
    have h2 : |Z| * (E.rho * E.ell ^ 3 * (K₀ * E.aScat)
          * (K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))))
        = K₀ ^ 2 * (|E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) := by
      rw [← hZabs]; ring
    rw [h2] at h1
    rw [show 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA1 F E s|)
        = 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA1 F E s|)) by ring]
    calc 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA1 F E s|))
        ≤ 2 * Real.sqrt E.bigM * (K₀ ^ 2 * (|E.z| * E.rho * E.aScat
            * (E.Kl * E.KL) ^ (-(E.intM : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat
            * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) := by ring
  have hS2 : 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA2 F E s|)
      ≤ 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * E.KH⁻¹) := by
    have h1 : |Z| * (∑ s ∈ excited Mode, |kA2 F E s|)
        ≤ |Z| * (K₀ ^ 2 * E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3) :=
      mul_le_mul_of_nonneg_left hT2 (abs_nonneg Z)
    have h2 : |Z| * (K₀ ^ 2 * E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3) = |Z| * (K₀ ^ 2 * (E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3)) := by ring
    rw [h2] at h1
    have h3 : |Z| * (E.ell ^ 3) * (K₀ ^ 2 * (E.rho * E.aScat * E.KH⁻¹)) = |Z| * (K₀ ^ 2 * (E.rho * E.aScat * E.KH⁻¹ * E.ell ^ 3)) := by ring
    rw [← h3] at h1
    rw [show 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA2 F E s|)
        = 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA2 F E s|)) by ring]
    calc 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA2 F E s|))
        ≤ 2 * Real.sqrt E.bigM * (|Z| * E.ell ^ 3 * (K₀ ^ 2 * (E.rho * E.aScat * E.KH⁻¹))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * E.KH⁻¹) := by
          rw [← hZabs]; ring
  have hS4 : 2 * Real.sqrt E.bigM * |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2)
      ≤ 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀
        * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (3 / 2 : ℝ)
            * eta E) := by
    have hC4nn : 0 ≤ 8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3
        * eta E := by
      have h2 : 0 ≤ E.rho * E.aScat * E.ell ^ 3 * eta E :=
        mul_nonneg (mul_nonneg (mul_nonneg hρ0 ha0.le) (by positivity)) hη0
      have h3 : 0 ≤ 8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 := by positivity
      nlinarith [h2, h3]
    have hK3nn : 0 ≤ K₀ * (E.Kl * E.KL) ^ 3 :=
      mul_nonneg hK₀ (pow_nonneg (mul_nonneg
        (le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_Kl))
        (le_of_lt (lt_of_lt_of_le zero_lt_one hv.one_le_KL))) 3)
    have hs : Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2)
        ≤ Real.sqrt (K₀ * (E.Kl * E.KL) ^ 3)
          * (8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3 * eta E) := by
      have h := Real.sqrt_le_sqrt hT4
      rw [Real.sqrt_mul hK3nn, Real.sqrt_sq hC4nn] at h
      exact h
    have hsqK : Real.sqrt (K₀ * (E.Kl * E.KL) ^ 3)
        = Real.sqrt K₀ * (E.Kl * E.KL) ^ (3 / 2 : ℝ) := by
      have hKLnn : (0 : ℝ) < E.Kl * E.KL :=
        mul_pos (lt_of_lt_of_le zero_lt_one hv.one_le_Kl)
          (lt_of_lt_of_le zero_lt_one hv.one_le_KL)
      rw [Real.sqrt_mul hK₀]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hKLnn.le]
      norm_num
    rw [hsqK] at hs
    calc 2 * Real.sqrt E.bigM * |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2)
        ≤ 2 * Real.sqrt E.bigM * |Z| * (Real.sqrt K₀ * (E.Kl * E.KL) ^ (3 / 2 : ℝ)
            * (8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3 * eta E)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀
            * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (3 / 2 : ℝ)
                * eta E) := by
          rw [← hZabs]; ring
  -- ### the four bounds in the form `B ≤ C e4A`
  have hD1 : 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat
        * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) ≤ 2 * K₀ ^ 2 * e4A E :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hD2 : 2 * K₀ ^ 2 * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * E.KH⁻¹)
      ≤ 2 * K₀ ^ 2 * e4A E :=
    mul_le_mul_of_nonneg_left hKH (by positivity)
  have hD4 : 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀
        * (Real.sqrt E.bigM * |E.z| * E.rho * E.aScat * (E.Kl * E.KL) ^ (3 / 2 : ℝ)
            * eta E)
      ≤ 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀ * e4A E :=
    mul_le_mul_of_nonneg_left heta (by positivity)
  -- ### the `kA3` constant
  have hD3 : (|Z| * Kr3) * (100 / E.b) * E.ell ^ 2 * (∑ s ∈ excited Mode, |Z * kA3 F E s|)
      ≤ 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8) * (E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b) := by
    have hZ2 : Z ^ 2 = E.rho / E.ell ^ 3 := by
      rw [hZ, div_pow, Work.BoseB7.zsq_eq E hv]
      field_simp
    have hid : (|Z| * Kr3) * (100 / E.b) * E.ell ^ 2 * (|Z| * Kr3)
        = 400 * K₀ ^ 4 * Cα ^ 2 * E.rho ^ 3 * E.aScat ^ 2 * E.ell ^ 5 * E.lille ^ 4
            / E.b := by
      rw [show (|Z| * Kr3) * (100 / E.b) * E.ell ^ 2 * (|Z| * Kr3)
          = Z ^ 2 * Kr3 ^ 2 * (100 / E.b) * E.ell ^ 2 by rw [← sq_abs Z]; ring]
      rw [hZ2, hKr3]
      field_simp
      ring
    calc (|Z| * Kr3) * (100 / E.b) * E.ell ^ 2 * (∑ s ∈ excited Mode, |Z * kA3 F E s|)
        ≤ (|Z| * Kr3) * (100 / E.b) * E.ell ^ 2 * (|Z| * Kr3) := by
          refine mul_le_mul_of_nonneg_left hsum3 ?_
          have h1 : 0 ≤ |Z| * Kr3 := mul_nonneg (abs_nonneg Z) hKr3nn
          have h2 : 0 ≤ 100 / E.b := div_nonneg (by norm_num) hbpos.le
          have h3 : 0 ≤ E.ell ^ 2 := sq_nonneg _
          exact mul_nonneg (mul_nonneg h1 h2) h3
      _ = 400 * K₀ ^ 4 * Cα ^ 2 * E.rho ^ 3 * E.aScat ^ 2 * E.ell ^ 5 * E.lille ^ 4
            / E.b := hid
      _ ≤ 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8)
          * (E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b) := by
          rw [Kl_sq_eq E hv, E0]
          have hρ3 : E.rho ^ 3 ≤ (3 * E.mu / 2) ^ 3 :=
            pow_le_pow_left₀ hρ0 (Work.BoseB7.rho_le E hv) 3
          rw [show (3 * E.mu / 2) ^ 3 = 27 / 8 * E.mu ^ 3 by ring] at hρ3
          have hfac : 0 ≤ 400 * K₀ ^ 4 * Cα ^ 2 * E.aScat ^ 2 * E.ell ^ 5 * E.lille ^ 4
              / E.b := by positivity
          have hmain := mul_le_mul_of_nonneg_right hρ3 hfac
          calc 400 * K₀ ^ 4 * Cα ^ 2 * E.rho ^ 3 * E.aScat ^ 2 * E.ell ^ 5 * E.lille ^ 4
                / E.b
              = E.rho ^ 3 * (400 * K₀ ^ 4 * Cα ^ 2 * E.aScat ^ 2 * E.ell ^ 5
                  * E.lille ^ 4 / E.b) := by ring
            _ ≤ (27 / 8) * E.mu ^ 3 * (400 * K₀ ^ 4 * Cα ^ 2 * E.aScat ^ 2 * E.ell ^ 5
                  * E.lille ^ 4 / E.b) := hmain
            _ = 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8)
                * (E.mu ^ 2 * E.aScat * E.ell ^ 3 * (E.ell ^ 2 * (E.mu * E.aScat))
                  * E.lille ^ 4 / E.b) := by ring
  -- ### the four `e4A`-scaled bounds
  have hS1n := mul_le_mul_of_nonneg_right hS1 hnom
  have hS2n := mul_le_mul_of_nonneg_right hS2 hnom
  have hS4n := mul_le_mul_of_nonneg_right hS4 hnom
  have hD1n := mul_le_mul_of_nonneg_right hD1 hnom
  have hD2n := mul_le_mul_of_nonneg_right hD2 hnom
  have hD4n := mul_le_mul_of_nonneg_right hD4 hnom
  have hD3n := mul_le_mul_of_nonneg_right hD3 hnom
  -- ### the form bounds for the four words
  have hform1 : -(2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA1 F E s|))
        * F.normSq Φ
      ≤ F.qw Φ (∑ s ∈ excited Mode, (Z * kA1 F E s) • (T.taDag s + T.ta s)) := by
    have h2 : |F.qw Φ (∑ s ∈ excited Mode, (Z * kA1 F E s) • (T.taDag s + T.ta s))|
        ≤ 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA1 F E s|) * F.normSq Φ := by
      calc |F.qw Φ (∑ s ∈ excited Mode, (Z * kA1 F E s) • (T.taDag s + T.ta s))|
          ≤ 2 * Real.sqrt E.bigM * Real.sqrt (∑ s ∈ excited Mode, (Z * kA1 F E s) ^ 2)
              * F.normSq Φ := hq1
        _ ≤ 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA1 F E s|)) * F.normSq Φ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 (by positivity)) hnom
        _ = 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA1 F E s|) * F.normSq Φ := by
            ring
    refine le_trans ?_ (neg_abs_le _)
    rw [neg_mul]
    exact neg_le_neg h2
  have hform2 : -(2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA2 F E s|))
        * F.normSq Φ
      ≤ F.qw Φ (∑ s ∈ excited Mode, (Z * kA2 F E s) • (T.taDag s + T.ta s)) := by
    have h2 : |F.qw Φ (∑ s ∈ excited Mode, (Z * kA2 F E s) • (T.taDag s + T.ta s))|
        ≤ 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA2 F E s|) * F.normSq Φ := by
      calc |F.qw Φ (∑ s ∈ excited Mode, (Z * kA2 F E s) • (T.taDag s + T.ta s))|
          ≤ 2 * Real.sqrt E.bigM * Real.sqrt (∑ s ∈ excited Mode, (Z * kA2 F E s) ^ 2)
              * F.normSq Φ := hq2
        _ ≤ 2 * Real.sqrt E.bigM * (|Z| * (∑ s ∈ excited Mode, |kA2 F E s|)) * F.normSq Φ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity)) hnom
        _ = 2 * Real.sqrt E.bigM * |Z| * (∑ s ∈ excited Mode, |kA2 F E s|) * F.normSq Φ := by
            ring
    refine le_trans ?_ (neg_abs_le _)
    rw [neg_mul]
    exact neg_le_neg h2
  have hform4 : -(2 * Real.sqrt E.bigM * |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2))
        * F.normSq Φ
      ≤ F.qw Φ (∑ s ∈ excited Mode, (Z * kA4 F E s) • (T.taDag s + T.ta s)) := by
    have h2 : |F.qw Φ (∑ s ∈ excited Mode, (Z * kA4 F E s) • (T.taDag s + T.ta s))|
        ≤ 2 * Real.sqrt E.bigM * |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2)
            * F.normSq Φ := by
      rw [hs4] at hq4
      calc |F.qw Φ (∑ s ∈ excited Mode, (Z * kA4 F E s) • (T.taDag s + T.ta s))|
          ≤ 2 * Real.sqrt E.bigM * (|Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2))
              * F.normSq Φ := hq4
        _ = 2 * Real.sqrt E.bigM * |Z| * Real.sqrt (∑ s ∈ excited Mode, (kA4 F E s) ^ 2)
              * F.normSq Φ := by ring
    refine le_trans ?_ (neg_abs_le _)
    rw [neg_mul]
    exact neg_le_neg h2
  have hreseq : F.qw Φ ((E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)
      = (E.b / 100 * E.ell ^ (-(2 : ℝ))) * F.bp (T.N Φ) Φ := by
    simp only [FockData.qw, LinearMap.smul_apply, map_smul, smul_eq_mul]
  have hCe4 : 2 * K₀ ^ 2 * e4A E + 2 * K₀ ^ 2 * e4A E
        + 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8) * (E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b)
        + 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀ * e4A E
      ≤ Ca * e4A E := by
    rw [hCa]
    have h4 : 16 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * Real.sqrt K₀
        ≤ 16 * (1 + (64 * K₀) ^ 2) * (max K₀ 0) ^ 3 * Real.sqrt (max K₀ 0) := by
      rw [max_eq_left hK₀]
    have hE0' := mul_le_mul_of_nonneg_left hE0
      (by positivity : (0 : ℝ) ≤ 400 * K₀ ^ 4 * Cα ^ 2 * (27 / 8))
    have h4' := mul_le_mul_of_nonneg_right h4 (e4A_nonneg E hv hbpos)
    nlinarith [hE0', h4']
  have hCe4n := mul_le_mul_of_nonneg_right hCe4 hnom
  -- ### the final assembly
  have hgoal : F.qw Φ (T.Q3fourT E + T.linOpT E + (E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N)
      = F.qw Φ (∑ s ∈ excited Mode, (Z * kA1 F E s) • (T.taDag s + T.ta s))
        + F.qw Φ (∑ s ∈ excited Mode, (Z * kA2 F E s) • (T.taDag s + T.ta s))
        + F.qw Φ (∑ s ∈ excited Mode, (Z * kA3 F E s) • (T.taDag s + T.ta s))
        + F.qw Φ (∑ s ∈ excited Mode, (Z * kA4 F E s) • (T.taDag s + T.ta s))
        + F.qw Φ ((E.b / 100 * E.ell ^ (-(2 : ℝ))) • T.N) := by
    rw [FockData.qw_add, hword, hsplit, FockData.qw_add, FockData.qw_add, FockData.qw_add]
    try ring
  rw [hgoal, hreseq]
  linarith [hform1, hform2, hform4, hgap, hS1n, hS2n, hS4n, hD1n, hD2n, hD4n, hD3n,
    hCe4n, hnom, e4A_nonneg E hv hbpos]

end Work.BoseC3QAll
