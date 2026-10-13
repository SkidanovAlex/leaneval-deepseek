import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS.StrongEps.LocUnif.mixed_sq_le_HkIntegrand
import Submission.Work.FTS.StrongEps.LocUnif.sin_two_lower_bound_rect
import Submission.Work.FTS.StrongEps.LocUnif.rect_integral_le_of_pointwise
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Arithmetic helpers

The seven rectangle integrals of `mixed_rect_L2_bounds` are bounded by rewriting each
integrand with `mixed_partials_of_smoothOpen` into a quotient of mixed derivatives (by
`z`, `sin 2θ`, `z²`, `sin²2θ`), and then comparing, on the rectangle, the reciprocals of
those factors with the constants `a^{-2}`, `m^{-2}`, `a^{-4}`, `(am)^{-2}`, `m^{-4}`
(`m` a positive lower bound for `sin 2θ` on `[c,d]`).  The three lemmas below are the
purely numerical steps. -/

/-- `(X / y)² ≤ (1 / p) · H` as soon as `X² ≤ H`, `0 ≤ H` and `0 < p ≤ y²`. -/
private lemma div_sq_le_one_div_mul {X H y p : ℝ} (hX : X ^ 2 ≤ H) (hH : 0 ≤ H) (hp : 0 < p)
    (hpy : p ≤ y ^ 2) : (X / y) ^ 2 ≤ (1 / p) * H := by
  have hy2 : 0 < y ^ 2 := lt_of_lt_of_le hp hpy
  have h1 : (X / y) ^ 2 = X ^ 2 / y ^ 2 := by rw [div_pow]
  rw [h1]
  calc X ^ 2 / y ^ 2 ≤ H / y ^ 2 := div_le_div_of_nonneg_right hX (le_of_lt hy2)
    _ ≤ H / p := div_le_div_of_nonneg_left hH hp hpy
    _ = (1 / p) * H := by ring

/-- `((A - B) / z²)² ≤ (4 / a⁴) · H` as soon as `A² ≤ H`, `B² ≤ H` and `0 < a ≤ z`. -/
private lemma div_sq_pow4_le {A B H z a : ℝ} (hz : a ≤ z) (ha : 0 < a)
    (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) : ((A - B) / z ^ 2) ^ 2 ≤ (4 / a ^ 4) * H := by
  have hzpos : 0 < z := lt_of_lt_of_le ha hz
  have hz4 : 0 < z ^ 4 := by positivity
  have ha4 : 0 < a ^ 4 := by positivity
  have h1 : ((A - B) / z ^ 2) ^ 2 = (A - B) ^ 2 / z ^ 4 := by rw [div_pow]; ring_nf
  rw [h1]
  have hAB : (A - B) ^ 2 ≤ 4 * H := by nlinarith [sq_nonneg (A - B), hA, hB]
  have hz4' : a ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ ha.le hz 4
  calc (A - B) ^ 2 / z ^ 4 ≤ (4 * H) / z ^ 4 := div_le_div_of_nonneg_right hAB (le_of_lt hz4)
    _ ≤ (4 * H) / a ^ 4 :=
        div_le_div_of_nonneg_left (by nlinarith [sq_nonneg (A - B)]) ha4 hz4'
    _ = (4 / a ^ 4) * H := by ring

/-- `((A - 2cB) / s²)² ≤ (12 / m⁴) · H` as soon as `A² ≤ H`, `B² ≤ H`, `|c| ≤ 1` and
`0 < m ≤ s`. -/
private lemma div_sq_pow4_cos_le {A B H s m c : ℝ} (hm : 0 < m) (hms : m ≤ s)
    (hc : |c| ≤ 1) (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) :
    ((A - 2 * c * B) / s ^ 2) ^ 2 ≤ (12 / m ^ 4) * H := by
  have hs : 0 < s := lt_of_lt_of_le hm hms
  have hm4 : 0 < m ^ 4 := by positivity
  have h1 : ((A - 2 * c * B) / s ^ 2) ^ 2 = (A - 2 * c * B) ^ 2 / s ^ 4 := by
    rw [div_pow]; ring_nf
  rw [h1]
  have hnum : (A - 2 * c * B) ^ 2 ≤ 6 * (A ^ 2 + B ^ 2) := by
    have h2 : |A - 2 * c * B| ≤ |A| + |2 * c * B| := by
      simpa [sub_eq_add_neg] using abs_add_le A (-(2 * c * B))
    have h3 : |2 * c * B| = 2 * |c| * |B| := by rw [abs_mul, abs_mul]; ring
    have h4 : 2 * |c| * |B| ≤ 2 * |B| := by nlinarith [abs_nonneg B]
    have h5 : |A - 2 * c * B| ≤ |A| + 2 * |B| := by rw [h3] at h2; linarith
    have h6 : (A - 2 * c * B) ^ 2 = |A - 2 * c * B| ^ 2 := by rw [sq_abs]
    rw [h6]
    nlinarith [abs_nonneg A, abs_nonneg B, abs_nonneg (A - 2 * c * B),
      sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
  have hs4 : m ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hm.le hms 4
  have hnn : 0 ≤ 6 * (A ^ 2 + B ^ 2) := by nlinarith [sq_nonneg A, sq_nonneg B]
  have hfinal : (6 * (A ^ 2 + B ^ 2)) / m ^ 4 ≤ (12 / m ^ 4) * H := by
    rw [div_le_iff₀ hm4]
    have he : (12 / m ^ 4) * H * m ^ 4 = 12 * H := by field_simp
    rw [he]
    nlinarith [hA, hB]
  calc (A - 2 * c * B) ^ 2 / s ^ 4 ≤ (6 * (A ^ 2 + B ^ 2)) / s ^ 4 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (6 * (A ^ 2 + B ^ 2)) / m ^ 4 := div_le_div_of_nonneg_left hnn hm4 hs4
    _ ≤ (12 / m ^ 4) * H := hfinal

theorem mixed_rect_L2_bounds {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hd : d < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ (F : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 6 F →
      ∀ (j i : ℕ), j + i ≤ 4 →
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) := by
  classical
  -- a positive lower bound for `sin 2θ` on `[c,d]`
  obtain ⟨m, hmpos, hmle⟩ := sin_two_lower_bound_rect (c := c) (d := d) hc hd
  -- the constant: the sum of the seven individual constants
  refine ⟨1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4,
    by positivity, ?_⟩
  have hKa : (0 : ℝ) ≤ 1 / a ^ 2 := by positivity
  have hKm : (0 : ℝ) ≤ 1 / m ^ 2 := by positivity
  have hKa4 : (0 : ℝ) ≤ 4 / a ^ 4 := by positivity
  have hKam : (0 : ℝ) ≤ 2 * (1 / (a ^ 2 * m ^ 2)) := by positivity
  have hKm4 : (0 : ℝ) ≤ 12 / m ^ 4 := by positivity
  have hKC1 : (1 : ℝ) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC2 : 1 / a ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC3 : 1 / m ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC4 : 4 / a ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC5 : 1 / (a ^ 2 * m ^ 2) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4
      + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4 := by linarith
  have hKC7 : 12 / m ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  intro α hα F hF hmem j i hji
  have hji6 : j + i ≤ 6 := by omega
  -- the six identities of `mixed_partials_of_smoothOpen`
  obtain ⟨hid1, hid2, hid3, hid4, hid5, hid6⟩ := mixed_partials_of_smoothOpen j i hF
  -- congruence of `pz`/`pth` on the open quadrant: replace `∂_z pz (mixed j i F)` by the
  -- quotient functions for which the identities are stated
  have hEqz : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed (j + 1) i F z θ / z)
      Work.FTS.EllipticEst.Q0 := fun p hp => hid1 p.1 p.2 hp
  have hEqθ : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ))
      Work.FTS.EllipticEst.Q0 := fun p hp => hid2 p.1 p.2 hp
  have hpzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have htzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have hpθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  have htθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  -- the pointwise facts on the rectangle
  have hmQ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    intro z hz θ hθ
    exact ⟨lt_of_lt_of_le ha hz.1, ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩⟩
  have hsinp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < Real.sin (2 * θ) := by
    intro z hz θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, hθ.1])
      (by linarith [hθ.2, hd, Real.pi_pos])
  have hHnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ
  -- (P1) the mixed slot itself
  have p1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.mixed j i F z θ) ^ 2 ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have h := mixed_sq_le_HkIntegrand (F := F) α hα j i hji6 (lt_of_lt_of_le ha hz.1) (hsinp z hz θ hθ)
    simpa using h
  -- (P2) `∂_z`
  have p2 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / a ^ 2) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < a ^ 2 := by positivity
    have hy2 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    rw [hid1 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P3) `∂_θ`
  have p3 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / m ^ 2) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < m ^ 2 := by positivity
    have hy2 : m ^ 2 ≤ Real.sin (2 * θ) ^ 2 := pow_le_pow_left₀ hmpos.le (hmle θ hθ) 2
    rw [hid2 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P4) `∂_z∂_z`
  have p4 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (4 / a ^ 4) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand (F := F) α hα (j + 2) i (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    rw [hpzz z θ hQ, hid3 z θ hQ]
    exact div_sq_pow4_le hz.1 ha hA hB
  -- (P5) `∂_z∂_θ`
  have p5 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [hpθθ z θ hQ, hid4 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P6) `∂_θ∂_z`
  have p6 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [htzz z θ hQ, hid5 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P7) `∂_θ∂_θ`
  have p7 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (12 / m ^ 4) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 2) (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    rw [htθθ z θ hQ, hid6 z θ hQ]
    rw [show Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ / (Real.sin (2 * θ)) ^ 2
        = (Work.Spaces.mixed j (i + 2) F z θ
            - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ)
          / (Real.sin (2 * θ)) ^ 2 from by ring]
    exact div_sq_pow4_cos_le hmpos (hmle θ hθ) (Real.abs_cos_le_one (2 * θ)) hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rect_integral_le_of_pointwise (K := 1) (α := α) (F := F)
      (g := Work.Spaces.mixed j i F) ha hab hc hd hmem (by norm_num) p1).trans
      (mul_le_mul_of_nonneg_right hKC1 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / a ^ 2) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.mixed j i F)) ha hab hc hd hmem hKa p2).trans
      (mul_le_mul_of_nonneg_right hKC2 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / m ^ 2) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.mixed j i F)) ha hab hc hd hmem hKm p3).trans
      (mul_le_mul_of_nonneg_right hKC3 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 4 / a ^ 4) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p4).trans
      (mul_le_mul_of_nonneg_right hKC4 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / (a ^ 2 * m ^ 2)) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p5).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / (a ^ 2 * m ^ 2)) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p6).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 12 / m ^ 4) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p7).trans
      (mul_le_mul_of_nonneg_right hKC7 (Work.Spaces.HkSq_nonneg α 6 F))

end Work.FTS.StrongEps.LocUnif
