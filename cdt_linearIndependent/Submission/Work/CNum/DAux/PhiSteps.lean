import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.AlpBound
import Submission.Work.CNum.phi_strictMono
import Submission.Work.CNum.DAux.SinGrid256
import Submission.Work.CNum.DAux.ArcsinLip

/-!
# `Work.CNum.DAux.PhiSteps`

Elementary "small step" bounds for the `C₁`-arc angle `φ = phiR`.

`phiR θ = θ/2 + π + arctan (QR θ / PR θ)` is the argument of the contour map on the
unit-circle arc `(-α, α)`.  Writing `√(2·A·(1-γ)) = 429/50` (an exact computation with
`A = (1+c²)²`, `γ = 8c²/A - 1`, `c = 23/10`) and `QR θ = (629/50)·sin(θ/2)`, we obtain

`phiR θ = θ/2 + π + arcsin (K · sin (θ/2))`,   `K = 629/429`,

on the arc.  The two claims are then:

* for `0 ≤ θ ≤ θ' ≤ 2π·244/1024` with `θ' - θ ≤ 2π/1024`, the increment of `phiR` is
  at most `1`: split `phiR θ' - phiR θ = (θ'-θ)/2 + (arcsin t' - arcsin t)`, use the
  Lipschitz bound `ArcsinLip` for `arcsin` on `[0, 9999/10000]`
  (`√(1-(9999/10000)²) ≥ 0.0141`) and `|sin x - sin y| ≤ |x - y|`;
* `alpR/2 + 3π/2 - phiR (2π·244/1024) ≤ 1`: since `t = K·sin(61π/256) ≥ 19/20`
  (by `SinGrid256`), `arcsin t ≥ 3/5`, and the remaining inequality is a rational
  bound using `1.4973 < alpR < 1.5031` and `π < 3.1416`.
-/

namespace Work.CNum.DAux

open Work.CNum

/-- `K = 629/429 = 2(1+c²)/√(2A(1-γ))`. -/
noncomputable def K : ℝ := 629 / 429

/-- `√(2·A·(1-γ)) = 429/50` exactly. -/
lemma sqrt_rad : Real.sqrt (2 * AR * (1 - gamR)) = (429 / 50 : ℝ) := by
  have h : 2 * AR * (1 - gamR) = (429 / 50 : ℝ) ^ 2 := by norm_num [AR, gamR, cR]
  rw [h]; exact Real.sqrt_sq (by norm_num)

/-- `QR θ = (629/50)·sin(θ/2)`. -/
lemma QR_eq (θ : ℝ) : QR θ = (629 / 50) * Real.sin (θ / 2) := by
  unfold QR cR; norm_num

/-- On the arc, `phiR` is the manifestly-analytic expression `θ/2 + π + arcsin (K sin (θ/2))`. -/
lemma phiR_eq {θ : ℝ} (hθ : θ ∈ Set.Ioo (-alpR) alpR) :
    phiR θ = θ / 2 + Real.pi + Real.arcsin (K * Real.sin (θ / 2)) := by
  rw [phiR, arctan_QR_div_PR hθ, sqrt_rad]
  have h : QR θ / (429 / 50) = K * Real.sin (θ / 2) := by rw [QR_eq]; unfold K; ring
  rw [h]

/-- `2π·244/1024 < alpR`. -/
lemma theta_max_lt : 2 * Real.pi * 244 / 1024 < alpR := by
  have h1 := AlpBound.1
  have h2 : 2 * Real.pi * 244 / 1024 < (1.4973 : ℝ) := by
    have h := Real.pi_lt_d4
    rw [show 2 * Real.pi * 244 / 1024 = 61 * Real.pi / 128 by ring]
    nlinarith
  linarith

/-- `θ ∈ (-α, α)` whenever `0 ≤ θ ≤ 2π·244/1024`. -/
lemma onearc_mem {θ : ℝ} (h0 : 0 ≤ θ) (hle : θ ≤ 2 * Real.pi * 244 / 1024) :
    θ ∈ Set.Ioo (-alpR) alpR :=
  ⟨by linarith [alpR_pos_phi_strictMono], lt_of_le_of_lt hle theta_max_lt⟩

lemma K_nonneg : (0 : ℝ) ≤ K := by unfold K; norm_num

/-- `K · 0.6812 ≤ 9999/10000`. -/
lemma K_upper : K * (0.6812 : ℝ) ≤ 9999 / 10000 := by unfold K; norm_num

/-- `19/20 ≤ K · 0.678`. -/
lemma K_lower : (19 / 20 : ℝ) ≤ K * (0.678 : ℝ) := by unfold K; norm_num

/-- `√(1 - (9999/10000)²) ≥ 0.0141`. -/
lemma sqrt_one_sub_T2 : (0.0141 : ℝ) ≤ Real.sqrt (1 - (9999 / 10000 : ℝ) ^ 2) := by
  have h2 : (0.0141 : ℝ) ^ 2 ≤ 1 - (9999 / 10000 : ℝ) ^ 2 := by norm_num
  calc (0.0141 : ℝ) = Real.sqrt ((0.0141 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (1 - (9999 / 10000 : ℝ) ^ 2) := Real.sqrt_le_sqrt h2

/-- `1/2 + π·K/(4·0.0141) ≤ 100`. -/
lemma C_bound : (1 : ℝ) / 2 + Real.pi * K / (4 * (0.0141 : ℝ)) ≤ 100 := by
  have hdiv : Real.pi * K / (4 * (0.0141 : ℝ)) ≤ 99 := by
    unfold K
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4 * 0.0141)]
    have h := Real.pi_lt_d4
    nlinarith
  linarith

theorem PhiSteps : (∀ θ θ' : ℝ, 0 ≤ θ → θ ≤ θ' → θ' ≤ 2 * Real.pi * 244 / 1024 → θ' - θ ≤ 2 * Real.pi / 1024 → Work.CNum.phiR θ' - Work.CNum.phiR θ ≤ 1) ∧ (Work.CNum.alpR / 2 + 3 * Real.pi / 2 - Work.CNum.phiR (2 * Real.pi * 244 / 1024) ≤ 1) := by
  constructor
  · intro θ θ' h0 hle hle' hstep
    have hmem := onearc_mem h0 (le_trans hle hle')
    have hmem' := onearc_mem (le_trans h0 hle) hle'
    rw [phiR_eq hmem', phiR_eq hmem]
    have hhalf : 61 * Real.pi / 256 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have hle'' : θ' ≤ 61 * Real.pi / 128 := by
      calc θ' ≤ 2 * Real.pi * 244 / 1024 := hle'
        _ = 61 * Real.pi / 128 := by ring
    have hstep'' : θ' - θ ≤ Real.pi / 512 := by
      calc θ' - θ ≤ 2 * Real.pi / 1024 := hstep
        _ = Real.pi / 512 := by ring
    have hhalf' : θ' / 2 ≤ Real.pi / 2 := by linarith
    have hhalf0 : -(Real.pi / 2) ≤ θ / 2 := by linarith [Real.pi_pos]
    have ht'T : K * Real.sin (θ' / 2) ≤ 9999 / 10000 := by
      have hs : Real.sin (θ' / 2) ≤ (0.6812 : ℝ) := by
        have h2 : Real.sin (θ' / 2) ≤ Real.sin (61 * Real.pi / 256) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ' / 2) (y := 61 * Real.pi / 256)
            (by linarith [Real.pi_pos]) hhalf (by linarith)
        exact h2.trans SinGrid256.2
      calc K * Real.sin (θ' / 2) ≤ K * (0.6812 : ℝ) := mul_le_mul_of_nonneg_left hs K_nonneg
        _ ≤ 9999 / 10000 := K_upper
    have ht0 : 0 ≤ K * Real.sin (θ / 2) :=
      mul_nonneg K_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
    have htt' : K * Real.sin (θ / 2) ≤ K * Real.sin (θ' / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ / 2) (y := θ' / 2)
          hhalf0 hhalf' (by linarith)) K_nonneg
    have hArc := ArcsinLip ht0 htt' ht'T (by norm_num : (9999 / 10000 : ℝ) < 1)
    have hArc' : Real.arcsin (K * Real.sin (θ' / 2)) - Real.arcsin (K * Real.sin (θ / 2))
        ≤ Real.pi * (K * Real.sin (θ' / 2) - K * Real.sin (θ / 2)) / (2 * (0.0141 : ℝ)) := by
      refine hArc.trans ?_
      have hnum : 0 ≤ Real.pi * (K * Real.sin (θ' / 2) - K * Real.sin (θ / 2)) :=
        mul_nonneg Real.pi_pos.le (by linarith)
      have hden : 2 * (0.0141 : ℝ) ≤ 2 * Real.sqrt (1 - (9999 / 10000 : ℝ) ^ 2) := by
        linarith [sqrt_one_sub_T2]
      exact div_le_div_of_nonneg_left hnum (by norm_num) hden
    have hsinLip : K * Real.sin (θ' / 2) - K * Real.sin (θ / 2) ≤ K * ((θ' - θ) / 2) := by
      have h := Real.abs_sin_sub_sin_le (θ' / 2) (θ / 2)
      have h2 : |θ' / 2 - θ / 2| = (θ' - θ) / 2 := by rw [abs_of_nonneg (by linarith)]; ring
      rw [h2] at h
      have h3 : Real.sin (θ' / 2) - Real.sin (θ / 2) ≤ (θ' - θ) / 2 := le_trans (le_abs_self _) h
      have := mul_le_mul_of_nonneg_left h3 K_nonneg
      linarith
    have hmain : Real.arcsin (K * Real.sin (θ' / 2)) - Real.arcsin (K * Real.sin (θ / 2))
        ≤ (θ' - θ) * (Real.pi * K / (4 * (0.0141 : ℝ))) := by
      have hmono : Real.pi * (K * Real.sin (θ' / 2) - K * Real.sin (θ / 2)) / (2 * (0.0141 : ℝ))
          ≤ Real.pi * (K * ((θ' - θ) / 2)) / (2 * (0.0141 : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hsinLip Real.pi_pos.le
      have heq : Real.pi * (K * ((θ' - θ) / 2)) / (2 * (0.0141 : ℝ))
          = (θ' - θ) * (Real.pi * K / (4 * (0.0141 : ℝ))) := by ring
      linarith [hArc', hmono, heq.le, heq.ge]
    have hfinal : (θ' - θ) * (1 / 2 + Real.pi * K / (4 * (0.0141 : ℝ))) ≤ 1 := by
      have hb : θ' - θ ≤ 3.1416 / 512 := by linarith [hstep'', Real.pi_lt_d4]
      have hC := C_bound
      have h2 : 0 ≤ (1 / 2 + Real.pi * K / (4 * (0.0141 : ℝ))) :=
        add_nonneg (by norm_num) (div_nonneg (mul_nonneg Real.pi_pos.le K_nonneg) (by norm_num))
      have h3 : 0 ≤ (3.1416 : ℝ) / 512 := by norm_num
      have := mul_le_mul hb hC h2 h3
      linarith
    have hexp : θ' / 2 + Real.pi + Real.arcsin (K * Real.sin (θ' / 2)) -
        (θ / 2 + Real.pi + Real.arcsin (K * Real.sin (θ / 2)))
        = (θ' - θ) / 2 + (Real.arcsin (K * Real.sin (θ' / 2)) - Real.arcsin (K * Real.sin (θ / 2))) := by ring
    rw [hexp]
    have : (θ' - θ) / 2 + (Real.arcsin (K * Real.sin (θ' / 2)) - Real.arcsin (K * Real.sin (θ / 2)))
        ≤ (θ' - θ) * (1 / 2 + Real.pi * K / (4 * (0.0141 : ℝ))) := by nlinarith [hmain]
    linarith
  · have hmem : (2 * Real.pi * 244 / 1024) ∈ Set.Ioo (-alpR) alpR :=
      onearc_mem (by positivity) le_rfl
    rw [phiR_eq hmem]
    have ht : (19 / 20 : ℝ) ≤ K * Real.sin ((2 * Real.pi * 244 / 1024) / 2) := by
      have hs : (0.678 : ℝ) ≤ Real.sin ((2 * Real.pi * 244 / 1024) / 2) := by
        rw [show 2 * Real.pi * 244 / 1024 / 2 = 61 * Real.pi / 256 by ring]
        exact SinGrid256.1
      calc (19 / 20 : ℝ) ≤ K * (0.678 : ℝ) := K_lower
        _ ≤ K * Real.sin ((2 * Real.pi * 244 / 1024) / 2) := mul_le_mul_of_nonneg_left hs K_nonneg
    have harc : (3 / 5 : ℝ) ≤ Real.arcsin (K * Real.sin ((2 * Real.pi * 244 / 1024) / 2)) := by
      have hsin35 : Real.sin (3 / 5) ≤ (19 / 20 : ℝ) := by
        have := Real.sin_le (x := (3 / 5 : ℝ)) (by norm_num)
        linarith
      have h19 : (3 / 5 : ℝ) ≤ Real.arcsin (19 / 20) := by
        have h := Real.arcsin_le_arcsin hsin35
        rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])] at h
      exact h19.trans (Real.arcsin_le_arcsin ht)
    have hAlp := AlpBound.2
    have hpi := Real.pi_lt_d4
    nlinarith [harc, hAlp, hpi, Real.pi_pos]

end Work.CNum.DAux
