import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.Gen.S30g_le_cauchy
import Submission.Work.GM.S3.Gen.S32g_le_cauchy
import Submission.Work.GM.S3.Gen.S33g_le_affine
import Submission.Work.GM.S3.Gen.S34g_le_affine
import Submission.Work.GM.S3.prop101_integral_testfun_le
import Submission.Work.GM.S3.prop101_integral_testfun_sq_le
import Submission.Work.GM.S3.bumpAtOne_majorant
import Submission.Work.GM.S3.R_l2_interval
import Submission.Work.GM.S3.R_l4_interval

/-!
# The per-cell bound `S30g_le_cell` (GM Prop 10.1 for a single cell of the §7 decomposition)

This file proves the estimate

`S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤ C N^ε (Mbig³ |W|^{3/2} + Mbig² |W|^{1/2} E(W)^{1/2})`

for the *three-scale* §10 object `S30g` (`Submission/Work/GM/S3/gen_defs.lean`), valid whenever the
smoothing satisfies `32 ≤ N B` and the three cell scales obey `0 < Mᵢ ≤ Mbig`.  It is the
per-cell input of the cell decomposition of GM 7.2 (`NOTES_cell_route.md`).

The proof is the one of `prop101_relaxed` / `prop101_clashfree`, with the single-scale objects
`S30, S32, S33, S34` replaced by their three-scale analogues: two Cauchy–Schwarz steps
(`S30g_le_cauchy`, `S32g_le_cauchy`), the two recognitions of the §10 objects as `affineSum`
integrals (`S33g_le_affine`, `S34g_le_affine`), GM Prop 9.1 (`hAff`) applied twice to the test
function `γ·R̃²`, the `L²`/`L⁴` integral bounds `R_l2_interval`/`R_l4_interval`, and the explicit
test-function mass bounds.  Everything is assembled by the isolated arithmetic lemma
`S30cell.cell_arith`.

All helper declarations live in the fresh namespace `Work.GM.S3.Gen.S30cell`.
-/

namespace Work.GM.S3.Gen

set_option maxHeartbeats 4000000

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun energy affineSum Separated)

namespace S30cell

/-- `IsBumpAtZero` is monotone in the support constant. -/
lemma IsBumpAtZero.mono_bump {ψ : ℝ → ℝ} {C C' : ℝ} (h : Work.GM.S3.IsBumpAtZero ψ C)
    (hCC : C ≤ C') : Work.GM.S3.IsBumpAtZero ψ C' :=
  ⟨h.1, h.2.1, fun x hx => le_trans (h.2.2.1 x hx) hCC, h.2.2.2.1, h.2.2.2.2⟩

/-- `IsBumpAtOne` is monotone in the support constant (for `C ≥ 1`). -/
lemma IsBumpAtOne.mono_bump {ψ : ℝ → ℝ} {C C' : ℝ} (h : Work.GM.S3.IsBumpAtOne ψ C)
    (hCC : C ≤ C') : Work.GM.S3.IsBumpAtOne ψ C' := by
  have hne : ψ 1 ≠ 0 := by rw [h.2.2.2.1]; norm_num
  have hC1 : 1 ≤ C := (Set.mem_Icc.mp (h.2.2.1 1 hne)).2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨h.1, h.2.1, fun x hx => ?_, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨ha, hb⟩ := Set.mem_Icc.mp (h.2.2.1 x hx)
  exact Set.mem_Icc.mpr ⟨le_trans (one_div_le_one_div_of_le hCpos hCC) ha, le_trans hb hCC⟩

/-- Support of `RtildeSq` inside `[1/8, 33/8]` when `32 ≤ N B` and the bumps are
`IsBumpAtZero ψ₁ 4`, `IsBumpAtOne ψ₂ 4`. -/
theorem RtildeSq_supp (W : Finset ℝ) (N : ℕ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 4) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 4)
    (hNB : 32 ≤ (N : ℝ) * B) :
    ∀ x, Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
  intro x hx
  by_contra hcon
  refine hx (Work.GM.S3.RtildeSq_eq_zero_of_notMem (c := 4) (a := 1 / 4) (b := 4) (by norm_num)
    (fun y hy => hψ₁.2.2.1 y hy) (fun y hy => hψ₂.2.2.1 y hy) ?_ ?_)
  · exact lt_of_lt_of_le (by norm_num) hNB
  · intro hmem
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hmem
    have hNBpos : (0 : ℝ) < (N : ℝ) * B := lt_of_lt_of_le (by norm_num) hNB
    have h4 : 4 / ((N : ℝ) * B) ≤ 1 / 8 := by
      rw [div_le_iff₀ hNBpos]
      nlinarith
    exact hcon (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)

/-- `∫_{1/2}^{2} ‖R v‖² ≤ ∫_{1/16}^{16} ‖R v‖²`. -/
theorem interval_le_16_16 (W : Finset ℝ) :
    ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ ^ 2 ≤ ∫ v in (1 / 16 : ℝ)..16, ‖Rfun W v‖ ^ 2 := by
  refine intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : x ≠ 0 := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact (Work.GM.S3.continuousAt_normSq_Rfun W hx0).continuousWithinAt

/-- `√(x^r) = x^(r/2)` for `x ≥ 0`. -/
private lemma sqrt_rpow_eq {x r : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ r) = x ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx r (1/2), show r * (1/2) = r / 2 by ring]

/-- `√w * √E = w^(1/2) * E^(1/2)`. -/
private lemma sqrt_mul_sqrt_eq {w E : ℝ} (_hw : 0 ≤ w) (_hE : 0 ≤ E) :
    Real.sqrt w * Real.sqrt E = w ^ (1/2:ℝ) * E ^ (1/2:ℝ) := by
  rw [Real.sqrt_eq_rpow w, Real.sqrt_eq_rpow E]

/-- `w * √w = w^(3/2)` for `w ≥ 0`. -/
private lemma mul_sqrt_eq_rpow {w : ℝ} (hw : 0 ≤ w) : w * Real.sqrt w = w ^ (3/2:ℝ) := by
  rcases eq_or_lt_of_le hw with h | h
  · rw [← h, Real.sqrt_zero, mul_zero, Real.zero_rpow (by norm_num : (3:ℝ)/2 ≠ 0)]
  · have key : w * w ^ (1/2:ℝ) = w ^ (1 + 1/2 : ℝ) := by
      rw [Real.rpow_add h 1 (1/2), Real.rpow_one]
    rw [Real.sqrt_eq_rpow, key, show (1:ℝ) + 1/2 = 3/2 by norm_num]

/-- **The arithmetic core of the cell bound.**  With
`A1 = Cf (C₂ Nn^ε' w)`, `A2 = Cf2 (C₄ Nn^ε' E)` and `0 ≤ 5ε'/2 ≤ ε`, `0 < T`, `T^{ε'/2} ≤ Nn^{ε'}`,

`√(C₂ Nn^ε' w) · √8 · √(Caff T^{ε'} (Mbig⁶ A1² + Mbig⁴ A2))`
`  ≤ (√C₂ (√8 √Caff) max (Cf C₂) (√Cf2 √C₄)) Nn^ε (Mbig³ w√w + Mbig² √w√E)`. -/
private lemma cell_arith
    {C₂ C₄ Caff Cf Cf2 Nn T Mbig w E ε ε' : ℝ}
    (hC₂ : 0 < C₂) (hC₄ : 0 < C₄) (hCaff : 0 < Caff) (hCf : 0 < Cf) (hCf2 : 0 < Cf2)
    (hNn : 1 ≤ Nn) (hε' : 0 < ε') (hexp1 : 5 * ε' / 2 ≤ ε)
    (hTle : T ^ (ε' / 2) ≤ Nn ^ ε') (hTnn : 0 ≤ T)
    (hMbig : 0 ≤ Mbig) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    Real.sqrt (C₂ * Nn ^ ε' * w) *
      (Real.sqrt 8 * Real.sqrt (Caff * T ^ ε' *
        (Mbig ^ 6 * (Cf * (C₂ * Nn ^ ε' * w)) ^ 2 +
          Mbig ^ 4 * (Cf2 * (C₄ * Nn ^ ε' * E))))) ≤
    (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff) *
        max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄)) *
      Nn ^ ε * (Mbig ^ 3 * (w * Real.sqrt w) + Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) := by
  have hNnpos : 0 < Nn := lt_of_lt_of_le zero_lt_one hNn
  have hNnn : 0 ≤ Nn := le_of_lt hNnpos
  set A1 : ℝ := Cf * (C₂ * Nn ^ ε' * w) with hA1def
  set A2 : ℝ := Cf2 * (C₄ * Nn ^ ε' * E) with hA2def
  have hA1nn : 0 ≤ A1 := by
    rw [hA1def]
    exact mul_nonneg (le_of_lt hCf)
      (mul_nonneg (mul_nonneg (le_of_lt hC₂) (Real.rpow_nonneg hNnn ε')) hw)
  have hA2nn : 0 ≤ A2 := by
    rw [hA2def]
    exact mul_nonneg (le_of_lt hCf2)
      (mul_nonneg (mul_nonneg (le_of_lt hC₄) (Real.rpow_nonneg hNnn ε')) hE)
  have hsqA2 : Real.sqrt A2 ^ 2 = A2 := Real.sq_sqrt hA2nn
  have hsqrtA2 : Real.sqrt A2 = Real.sqrt Cf2 * Real.sqrt C₄ * Nn ^ (ε' / 2) * Real.sqrt E := by
    rw [hA2def, show Cf2 * (C₄ * Nn ^ ε' * E) = Cf2 * (C₄ * (Nn ^ ε' * E)) by ring,
      Real.sqrt_mul (le_of_lt hCf2), Real.sqrt_mul (le_of_lt hC₄),
      Real.sqrt_mul (Real.rpow_nonneg hNnn ε'), sqrt_rpow_eq hNnn]
    ring
  have hInner_le : Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2 ≤
      (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2) ^ 2 := by
    have hprod : 0 ≤ Mbig ^ 5 * A1 * Real.sqrt A2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hMbig 5) hA1nn) (Real.sqrt_nonneg A2)
    have hkey : (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2) ^ 2 =
        Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2 + 2 * (Mbig ^ 5 * A1 * Real.sqrt A2) := by
      ring_nf
      rw [hsqA2]
    rw [hkey]
    linarith [hprod]
  have hsqrtInner : Real.sqrt (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2) ≤
      Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2 := by
    refine le_trans (Real.sqrt_le_sqrt hInner_le) ?_
    rw [Real.sqrt_sq]
    exact add_nonneg (mul_nonneg (pow_nonneg hMbig 3) hA1nn)
      (mul_nonneg (pow_nonneg hMbig 2) (Real.sqrt_nonneg A2))
  have hstepA : Real.sqrt (C₂ * Nn ^ ε' * w) = Real.sqrt C₂ * (Nn ^ (ε' / 2) * Real.sqrt w) := by
    rw [show C₂ * Nn ^ ε' * w = C₂ * (Nn ^ ε' * w) by ring,
      Real.sqrt_mul (le_of_lt hC₂), Real.sqrt_mul (Real.rpow_nonneg hNnn ε'),
      sqrt_rpow_eq hNnn]
  have hCTnn : 0 ≤ Caff * T ^ ε' := mul_nonneg (le_of_lt hCaff) (Real.rpow_nonneg hTnn ε')
  have hstepC : Real.sqrt (Caff * T ^ ε' * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2)) ≤
      Real.sqrt Caff * T ^ (ε' / 2) * (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2) := by
    rw [show Caff * T ^ ε' * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2)
        = (Caff * T ^ ε') * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2) by ring,
      Real.sqrt_mul hCTnn, Real.sqrt_mul (le_of_lt hCaff), sqrt_rpow_eq hTnn]
    exact mul_le_mul_of_nonneg_left hsqrtInner
      (mul_nonneg (Real.sqrt_nonneg Caff) (Real.rpow_nonneg hTnn (ε' / 2)))
  have hTA2 : T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ ε') ≤ Nn ^ ε := by
    have h1 : T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ ε') ≤
        Nn ^ ε' * (Nn ^ (ε' / 2) * Nn ^ ε') :=
      mul_le_mul_of_nonneg_right hTle
        (mul_nonneg (Real.rpow_nonneg hNnn _) (Real.rpow_nonneg hNnn _))
    have h2 : Nn ^ ε' * (Nn ^ (ε' / 2) * Nn ^ ε') = Nn ^ ε' * Nn ^ (ε' / 2 + ε') := by
      rw [← Real.rpow_add hNnpos (ε' / 2) ε']
    have h3 : Nn ^ ε' * Nn ^ (ε' / 2 + ε') ≤ Nn ^ ε := by
      rw [← Real.rpow_add hNnpos ε' (ε' / 2 + ε')]
      exact Real.rpow_le_rpow_of_exponent_le hNn (by linarith)
    exact le_trans (h2 ▸ h1) h3
  have hTB2 : T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)) ≤ Nn ^ ε := by
    have h1 : T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)) ≤
        Nn ^ ε' * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)) :=
      mul_le_mul_of_nonneg_right hTle
        (mul_nonneg (Real.rpow_nonneg hNnn _) (Real.rpow_nonneg hNnn _))
    have h4 : Nn ^ (ε' / 2 + ε' / 2) = Nn ^ ε' := by rw [show ε' / 2 + ε' / 2 = ε' by ring]
    have h2 : Nn ^ ε' * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)) = Nn ^ ε' * Nn ^ (ε' / 2 + ε' / 2) := by
      rw [← Real.rpow_add hNnpos (ε' / 2) (ε' / 2)]
    have h3 : Nn ^ ε' * Nn ^ (ε' / 2 + ε' / 2) ≤ Nn ^ ε := by
      rw [h4, ← Real.rpow_add hNnpos ε' ε']
      exact Real.rpow_le_rpow_of_exponent_le hNn (by linarith)
    exact le_trans (h2 ▸ h1) h3
  have hPnn : 0 ≤ Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff) :=
    mul_nonneg (Real.sqrt_nonneg C₂) (mul_nonneg (Real.sqrt_nonneg 8) (Real.sqrt_nonneg Caff))
  have hT1nn : 0 ≤ Mbig ^ 3 * (w * Real.sqrt w) :=
    mul_nonneg (pow_nonneg hMbig 3) (mul_nonneg hw (Real.sqrt_nonneg w))
  have hT2nn : 0 ≤ Mbig ^ 2 * (Real.sqrt w * Real.sqrt E) :=
    mul_nonneg (pow_nonneg hMbig 2) (mul_nonneg (Real.sqrt_nonneg w) (Real.sqrt_nonneg E))
  have hNnεnn : 0 ≤ Nn ^ ε := Real.rpow_nonneg hNnn ε
  have hQ1 : Cf * C₂ ≤ max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) := le_max_left _ _
  have hQ2 : Real.sqrt Cf2 * Real.sqrt C₄ ≤ max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) :=
    le_max_right _ _
  have hstepAB : Real.sqrt (C₂ * Nn ^ ε' * w) *
      (Real.sqrt 8 * Real.sqrt (Caff * T ^ ε' *
        (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2))) ≤
      (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff)) *
        ((Nn ^ (ε' / 2) * Real.sqrt w) * T ^ (ε' / 2) *
          (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2)) := by
    calc Real.sqrt (C₂ * Nn ^ ε' * w) *
          (Real.sqrt 8 * Real.sqrt (Caff * T ^ ε' * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2)))
        = Real.sqrt C₂ * (Nn ^ (ε' / 2) * Real.sqrt w) *
            (Real.sqrt 8 * Real.sqrt (Caff * T ^ ε' * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2))) :=
          by rw [hstepA]
      _ ≤ Real.sqrt C₂ * (Nn ^ (ε' / 2) * Real.sqrt w) *
            (Real.sqrt 8 * (Real.sqrt Caff * T ^ (ε' / 2) *
              (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstepC (Real.sqrt_nonneg 8))
            (mul_nonneg (Real.sqrt_nonneg C₂)
              (mul_nonneg (Real.rpow_nonneg hNnn (ε' / 2)) (Real.sqrt_nonneg w)))
      _ = (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff)) *
            ((Nn ^ (ε' / 2) * Real.sqrt w) * T ^ (ε' / 2) *
              (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2)) := by ring
  have hfinal : (Nn ^ (ε' / 2) * Real.sqrt w) * T ^ (ε' / 2) *
      (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2) ≤
      max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) * Nn ^ ε *
        (Mbig ^ 3 * (w * Real.sqrt w) + Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) := by
    have e1 : (Nn ^ (ε' / 2) * Real.sqrt w) * T ^ (ε' / 2) *
        (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2)
        = (Cf * C₂) * (Mbig ^ 3 * (w * Real.sqrt w)) *
            (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ ε'))
          + (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) *
              (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2))) := by
      rw [hA1def, hsqrtA2]
      ring
    rw [e1]
    have b1 : (Cf * C₂) * (Mbig ^ 3 * (w * Real.sqrt w)) *
        (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ ε'))
        ≤ (Cf * C₂) * (Mbig ^ 3 * (w * Real.sqrt w)) * Nn ^ ε :=
      mul_le_mul_of_nonneg_left hTA2
        (mul_nonneg (mul_nonneg (le_of_lt hCf) (le_of_lt hC₂)) hT1nn)
    have b2 : (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) *
        (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)))
        ≤ (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) * Nn ^ ε :=
      mul_le_mul_of_nonneg_left hTB2
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg Cf2) (Real.sqrt_nonneg C₄)) hT2nn)
    calc (Cf * C₂) * (Mbig ^ 3 * (w * Real.sqrt w)) *
            (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ ε'))
          + (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) *
              (T ^ (ε' / 2) * (Nn ^ (ε' / 2) * Nn ^ (ε' / 2)))
        ≤ (Cf * C₂) * (Mbig ^ 3 * (w * Real.sqrt w)) * Nn ^ ε
          + (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) * Nn ^ ε :=
          add_le_add b1 b2
      _ ≤ max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 3 * (w * Real.sqrt w)) * Nn ^ ε
          + max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) * (Mbig ^ 2 * (Real.sqrt w * Real.sqrt E))
              * Nn ^ ε := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ1 hT1nn) hNnεnn
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ2 hT2nn) hNnεnn
      _ = max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) * Nn ^ ε *
            (Mbig ^ 3 * (w * Real.sqrt w) + Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) := by ring
  calc Real.sqrt (C₂ * Nn ^ ε' * w) *
        (Real.sqrt 8 * Real.sqrt (Caff * T ^ ε' * (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2)))
      ≤ (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff)) *
          ((Nn ^ (ε' / 2) * Real.sqrt w) * T ^ (ε' / 2) *
            (Mbig ^ 3 * A1 + Mbig ^ 2 * Real.sqrt A2)) := hstepAB
    _ ≤ (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff)) *
          (max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) * Nn ^ ε *
            (Mbig ^ 3 * (w * Real.sqrt w) + Mbig ^ 2 * (Real.sqrt w * Real.sqrt E))) :=
        mul_le_mul_of_nonneg_left hfinal hPnn
    _ = (Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff) *
          max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄)) * Nn ^ ε *
          (Mbig ^ 3 * (w * Real.sqrt w) + Mbig ^ 2 * (Real.sqrt w * Real.sqrt E)) := by ring

end S30cell

/-- **The per-cell bound of the §10 pipeline.**  For bumps `ψ₁, ψ₂` with `IsBumpAtZero ψ₁ 4` and
`IsBumpAtOne ψ₂ 4`, every `ε > 0` admits `C > 0`, `N₀` such that for `N ≥ N₀`, every
`(M N)^ε`-separated `W ⊆ [0, M N]`, and every smoothing `B` with `32 ≤ N B` and cell scales
`0 < M₁, M₂, M₃ ≤ Mbig`,

`S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤ C N^ε (Mbig³ |W|^{3/2} + Mbig² |W|^{1/2} E(W)^{1/2})`.

(GM Prop 10.1 for a single cell of GM 7.2; the `C` depends on `ψ₁, ψ₂` through the Fourier-decay
constant fed to GM 9.1, hence the bumps are arguments of the statement.) -/
theorem S30g_le_cell (hAff : Submission.GM.AffineStatement)
    (hL84 : Work.GM.S3.Lemma84RelaxedStatement)
    (ψ₁ ψ₂ : ℝ → ℝ) (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 4) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 4) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ (B M₁ M₂ M₃ Mbig : ℝ), 32 ≤ (N : ℝ) * B →
      0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig →
      Work.GM.S3.Gen.S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
        C * (N : ℝ) ^ ε * (Mbig ^ 3 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
          Mbig ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) *
            (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ)) := by
  intro ε hε
  set η₀ : ℝ := min ε 1 with hη₀def
  have hη₀leε : η₀ ≤ ε := min_le_left _ _
  set ε' : ℝ := η₀ / 64 with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  have hε'le : ε' ≤ ε / 64 := by rw [hε'def]; linarith
  have hexp1 : 5 * ε' / 2 ≤ ε := by linarith
  -- the bumps at level 16
  have hψ₁16 : Work.GM.S3.IsBumpAtZero ψ₁ 16 := S30cell.IsBumpAtZero.mono_bump hψ₁ (by norm_num)
  have hψ₂16 : Work.GM.S3.IsBumpAtOne ψ₂ 16 := S30cell.IsBumpAtOne.mono_bump hψ₂ (by norm_num)
  -- the fixed majorising bump
  obtain ⟨γ, hγ16, hγone⟩ := Work.GM.S3.bumpAtOne_majorant
  -- GM 8.4 (relaxed) for `γ · R̃²`
  obtain ⟨c, hcdecay⟩ := hL84 ε' hε'pos 16 (by norm_num) γ ψ₂ ψ₁ hγ16 hψ₂16 hψ₁16
  -- GM 9.1
  obtain ⟨Caff, hCaffpos, hAffmain⟩ := hAff 16 2 (by norm_num) (by norm_num) c ε' hε'pos
  -- GM 8.2 / 8.3 on `[1/16, 16]`
  obtain ⟨C₂, hC₂pos, N₀₂, hL2int⟩ := Work.GM.S3.R_l2_interval 16 (by norm_num) ε' hε'pos
  obtain ⟨C₄, hC₄pos, N₀₄, hL4int⟩ := Work.GM.S3.R_l4_interval 16 (by norm_num) ε' hε'pos
  -- the test-function mass bounds
  obtain ⟨Cf, hCfpos, hCfint⟩ := Work.GM.S3.prop101_integral_testfun_le ψ₁ ψ₂ γ hψ₁16 hψ₂16 hγ16
  obtain ⟨Cf2, hCf2pos, hCf2int⟩ := Work.GM.S3.prop101_integral_testfun_sq_le ψ₁ ψ₂ γ hψ₁16 hψ₂16 hγ16
  refine ⟨Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff) *
      max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄), ?_, max (max N₀₂ N₀₄) 1, ?_⟩
  · -- positivity of the constant
    have hP : 0 < Real.sqrt C₂ * (Real.sqrt 8 * Real.sqrt Caff) :=
      mul_pos (Real.sqrt_pos.mpr hC₂pos)
        (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hCaffpos))
    have hQ : 0 < max (Cf * C₂) (Real.sqrt Cf2 * Real.sqrt C₄) :=
      lt_of_lt_of_le (mul_pos hCfpos hC₂pos) (le_max_left _ _)
    exact mul_pos hP hQ
  · intro N hN W hWsub hWsep B M₁ M₂ M₃ Mbig hNB32 hM₁ hM₁big hM₂ hM₂big hM₃ hM₃big
    have hε'leε : ε' ≤ ε := by linarith
    have hN2 : N₀₂ ≤ N := le_trans (le_trans (le_max_left N₀₂ N₀₄) (le_max_left _ _)) hN
    have hN4 : N₀₄ ≤ N := le_trans (le_trans (le_max_right N₀₂ N₀₄) (le_max_left _ _)) hN
    have hNge1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNge1)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge1
    have hNnn : 0 ≤ (N : ℝ) := le_of_lt hNpos
    have hT1 : (1 : ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hNge1
    have hTpos : (0 : ℝ) < Submission.LargeValues.M N := Submission.LargeValues.M_pos hNge1
    have hTnn : 0 ≤ Submission.LargeValues.M N := le_of_lt hTpos
    have hNBpos : (0 : ℝ) < (N : ℝ) * B := lt_of_lt_of_le (by norm_num) hNB32
    have hNBnn : 0 ≤ (N : ℝ) * B := le_of_lt hNBpos
    have hNB1 : 1 ≤ (N : ℝ) * B := le_trans (by norm_num) hNB32
    have hBpos : 0 < B := by nlinarith [hNBpos, hNpos]
    have hw : 0 ≤ (W.card : ℝ) := by positivity
    have hE0 : 0 ≤ (Submission.GM.energy W : ℝ) := by positivity
    have hMbignn : 0 ≤ Mbig := le_trans (le_of_lt hM₁) hM₁big
    have hwsep' : Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε') := by
      intro t ht s hs hts
      have h := hWsep t ht s hs hts
      have h2 : (Submission.LargeValues.M N) ^ ε' ≤ (Submission.LargeValues.M N) ^ ε :=
        Real.rpow_le_rpow_of_exponent_le hT1 hε'leε
      linarith
    have hRsupp : ∀ x, Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1/8:ℝ) (33/8) :=
      S30cell.RtildeSq_supp W N B ψ₁ ψ₂ hψ₁ hψ₂ hNB32
    have hTle : (Submission.LargeValues.M N) ^ (ε'/2) ≤ (N:ℝ) ^ ε' := by
      have hMt : Submission.LargeValues.M N ≤ (N:ℝ) ^ (2:ℝ) := by
        rw [Submission.LargeValues.M]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      calc (Submission.LargeValues.M N) ^ (ε'/2)
          ≤ ((N:ℝ) ^ (2:ℝ)) ^ (ε'/2) :=
            Real.rpow_le_rpow hTnn hMt (div_nonneg (le_of_lt hε'pos) (by norm_num))
        _ = (N:ℝ) ^ ((2:ℝ) * (ε'/2)) := (Real.rpow_mul hNnn 2 (ε'/2)).symm
        _ = (N:ℝ) ^ ε' := by rw [show (2:ℝ) * (ε'/2) = ε' by ring]
    -- the test function `γ · R̃²`
    have hfcont : Continuous (fun u => Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u) := by
      rw [show (fun u => Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u)
        = fun u => γ u * Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ u from rfl]
      exact hγ16.1.continuous.mul (Work.GM.S3.RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁16 hψ₂16)
    have htestnn : ∀ u, 0 ≤ Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u := fun u => by
      simp only [Work.GM.S3.testfun]
      exact mul_nonneg (hγ16.2.1 u)
        (Work.GM.S3.RtildeSq_nonneg W N B ψ₁ ψ₂ u hψ₁16.2.1 hψ₂16.2.1 (le_of_lt hBpos))
    have hfsupp : ∀ u, Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u ≠ 0 → u ∈ Set.Icc (1/16:ℝ) 16 := by
      intro u hu
      refine hγ16.2.2.1 u (fun h0 => hu ?_)
      simp only [Work.GM.S3.testfun, h0, zero_mul]
    have hfdecay : ∀ (j : ℕ) (η : ℝ), 0 < η → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun u => (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u : ℂ)) ξ‖ ≤
          c j η * (Submission.LargeValues.M N) ^ η *
            (Submission.LargeValues.M N / |ξ|) ^ j *
              sSup (Set.range (fun u => Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u)) := by
      intro j η hη ξ hξ
      simpa only [Work.GM.S3.testfun] using hcdecay N hNge1 W hWsub hwsep' B hNB1 j η hη ξ hξ
    -- abbreviations
    set A1 : ℝ := Cf * (C₂ * (N:ℝ) ^ ε' * (W.card:ℝ)) with hA1def
    set A2 : ℝ := Cf2 * (C₄ * (N:ℝ) ^ ε' * (Submission.GM.energy W : ℝ)) with hA2def
    set Areff : ℝ := Caff * (Submission.LargeValues.M N) ^ ε' *
      (Mbig ^ 6 * A1 ^ 2 + Mbig ^ 4 * A2) with hAreffdef
    have hA1nn : 0 ≤ A1 := by
      rw [hA1def]
      exact mul_nonneg (le_of_lt hCfpos)
        (mul_nonneg (mul_nonneg (le_of_lt hC₂pos) (Real.rpow_nonneg hNnn ε')) hw)
    have hA2nn : 0 ≤ A2 := by
      rw [hA2def]
      exact mul_nonneg (le_of_lt hCf2pos)
        (mul_nonneg (mul_nonneg (le_of_lt hC₄pos) (Real.rpow_nonneg hNnn ε')) hE0)
    have hAreffnn : 0 ≤ Areff := by
      rw [hAreffdef]
      exact mul_nonneg (mul_nonneg (le_of_lt hCaffpos) (Real.rpow_nonneg hTnn ε'))
        (add_nonneg (mul_nonneg (pow_nonneg hMbignn 6) (sq_nonneg A1))
          (mul_nonneg (pow_nonneg hMbignn 4) hA2nn))
    -- the `L²`/`L⁴` bounds on `[1/16,16]`
    have hint2 : ∫ v in (1/16:ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 2 ≤
        C₂ * (N:ℝ) ^ ε' * (W.card:ℝ) := hL2int N hN2 W hWsub hwsep'
    have hint4 : ∫ v in (1/16:ℝ)..16, ‖Submission.GM.Rfun W v‖ ^ 4 ≤
        C₄ * (N:ℝ) ^ ε' * (Submission.GM.energy W : ℝ) := hL4int N hN4 W hWsub hwsep'
    have hI2 : ∫ v in (1/2:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤
        C₂ * (N:ℝ) ^ ε' * (W.card:ℝ) := le_trans (S30cell.interval_le_16_16 W) hint2
    have hp_int : ∫ u, Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u ≤ A1 := by
      rw [hA1def]
      exact hCfint N W B (C₂ * (N:ℝ) ^ ε' * (W.card:ℝ)) hNBnn hint2
    have hq_int : ∫ u, (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u) ^ 2 ≤ A2 := by
      rw [hA2def]
      exact hCf2int N W B (C₄ * (N:ℝ) ^ ε' * (Submission.GM.energy W : ℝ)) hNBnn hint4
    -- GM 9.1 applied to `affineSum 2 M₃ M₂ M₁` and `affineSum 2 M₁ M₂ M₃`
    have hA33 : (∫ u, (Submission.GM.affineSum 2 M₃ M₂ M₁
        (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ) u) ^ 2) ≤ Areff := by
      rw [hAreffdef]
      refine le_trans (hAffmain (Submission.LargeValues.M N) hT1
        (fun u => Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u) hfcont htestnn hfsupp hfdecay
        Mbig M₃ M₂ M₁ hM₃ hM₃big hM₂ hM₂big hM₁ hM₁big) ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (le_of_lt hCaffpos) (Real.rpow_nonneg hTnn ε'))
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (integral_nonneg htestnn) hp_int 2)
          (pow_nonneg hMbignn 6))
        (mul_le_mul_of_nonneg_left hq_int (pow_nonneg hMbignn 4))
    have hA34 : (∫ u, (Submission.GM.affineSum 2 M₁ M₂ M₃
        (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ) u) ^ 2) ≤ Areff := by
      rw [hAreffdef]
      refine le_trans (hAffmain (Submission.LargeValues.M N) hT1
        (fun u => Work.GM.S3.testfun N W B ψ₁ ψ₂ γ u) hfcont htestnn hfsupp hfdecay
        Mbig M₁ M₂ M₃ hM₁ hM₁big hM₂ hM₂big hM₃ hM₃big) ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (le_of_lt hCaffpos) (Real.rpow_nonneg hTnn ε'))
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (integral_nonneg htestnn) hp_int 2)
          (pow_nonneg hMbignn 6))
        (mul_le_mul_of_nonneg_left hq_int (pow_nonneg hMbignn 4))
    -- the two recognitions
    have hS33g : S33g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
        16 * ∫ u, (Submission.GM.affineSum 2 M₃ M₂ M₁
          (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ) u) ^ 2 :=
      S33g_le_affine N W B M₁ M₂ M₃ ψ₁ ψ₂ γ hNBnn hM₁ hM₂ hM₃ hψ₁16 hψ₂16 hγ16 hγone hRsupp
    have hS34g : S34g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
        4 * ∫ u, (Submission.GM.affineSum 2 M₁ M₂ M₃
          (Work.GM.S3.testfun N W B ψ₁ ψ₂ γ) u) ^ 2 :=
      S34g_le_affine N W B M₁ M₂ M₃ ψ₁ ψ₂ γ hNBnn hM₁ hM₂ hM₃ hψ₁16 hψ₂16 hγ16 hγone hRsupp
    have hS33b : S33g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤ 16 * Areff :=
      le_trans hS33g (mul_le_mul_of_nonneg_left hA33 (by norm_num))
    have hS34b : S34g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤ 4 * Areff :=
      le_trans hS34g (mul_le_mul_of_nonneg_left hA34 (by norm_num))
    -- second Cauchy--Schwarz step
    have hS32b : S32g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤ 8 * Areff := by
      have h := S32g_le_cauchy N W B M₁ M₂ M₃ ψ₁ ψ₂ hψ₁16 hψ₂16 hNBnn
      have h1 : Real.sqrt (S33g N W B M₁ M₂ M₃ ψ₁ ψ₂) ≤ Real.sqrt (16 * Areff) :=
        Real.sqrt_le_sqrt hS33b
      have h2 : Real.sqrt (S34g N W B M₁ M₂ M₃ ψ₁ ψ₂) ≤ Real.sqrt (4 * Areff) :=
        Real.sqrt_le_sqrt hS34b
      refine le_trans h (le_trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      rw [show Real.sqrt (16:ℝ) = 4 by
            rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)],
          show Real.sqrt (4:ℝ) = 2 by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      nlinarith [Real.sq_sqrt hAreffnn]
    -- first Cauchy--Schwarz step
    have hS30b : S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
        Real.sqrt (C₂ * (N:ℝ) ^ ε' * (W.card:ℝ)) * (Real.sqrt 8 * Real.sqrt Areff) := by
      have h := S30g_le_cauchy N W B M₁ M₂ M₃ ψ₁ ψ₂ hψ₁16 hψ₂16
      have h1 : Real.sqrt (∫ v in (1/2:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) ≤
          Real.sqrt (C₂ * (N:ℝ) ^ ε' * (W.card:ℝ)) := Real.sqrt_le_sqrt hI2
      have h2 : Real.sqrt (S32g N W B M₁ M₂ M₃ ψ₁ ψ₂) ≤ Real.sqrt 8 * Real.sqrt Areff :=
        le_trans (Real.sqrt_le_sqrt hS32b) (le_of_eq (Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8) Areff))
      exact le_trans h (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    -- the arithmetic core
    have hcell := S30cell.cell_arith (C₂ := C₂) (C₄ := C₄) (Caff := Caff) (Cf := Cf) (Cf2 := Cf2)
      (Nn := (N:ℝ)) (T := Submission.LargeValues.M N) (Mbig := Mbig) (w := (W.card:ℝ))
      (E := (Submission.GM.energy W : ℝ)) (ε := ε) (ε' := ε')
      hC₂pos hC₄pos hCaffpos hCfpos hCf2pos hN1 hε'pos hexp1 hTle hTnn hMbignn hw hE0
    refine le_trans hS30b (le_trans hcell ?_)
    have hconv : Mbig ^ 3 * ((W.card:ℝ) * Real.sqrt (W.card:ℝ)) +
          Mbig ^ 2 * (Real.sqrt (W.card:ℝ) * Real.sqrt (Submission.GM.energy W : ℝ))
        = Mbig ^ 3 * (W.card:ℝ) ^ (3/2:ℝ) +
          Mbig ^ 2 * (W.card:ℝ) ^ (1/2:ℝ) * (Submission.GM.energy W : ℝ) ^ (1/2:ℝ) := by
      rw [S30cell.mul_sqrt_eq_rpow hw, S30cell.sqrt_mul_sqrt_eq hw hE0]
      ring
    refine le_of_eq ?_
    rw [hconv]

end Work.GM.S3.Gen
