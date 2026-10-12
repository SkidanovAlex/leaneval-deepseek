import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.Q3oneT_shift
import Submission.Work.BoseC3QAll.Est1.compSquare_sum
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.Assembly` — the assembly of `EstQ3oneA`

This module assembles FS `eq:EstimateQ3Tilde1` (`Work.BoseC3QAll.EstQ3oneA`) from

* **piece A** (`Est1.Q3oneT_shift`, proved): `Q₃⁽¹⁾ = Σ_{k∈P_H}(b_k†Y_k + Y_k†b_k) + R1`;
* **piece D** (`Est1.compSquare_sum`, proved): the summed completing-the-square
  `-Σ_k c_k⟨b_k†b_k⟩ - Σ_k c_k⁻¹⟨Y_k†Y_k⟩ ≤ ⟨Σ_k(b_k†Y_k + Y_k†b_k)⟩`;
* **piece B** (`Est1.estT2`, delegated): the quartic part `Σ_k c_k⁻¹‖Y_kΦ‖²`
  against `⟨Q₂^ex⟩`, the `P_H^q` reserve and the energy gap;
* **piece C** (`Est1.estR1`, delegated): the linear leftover `R1`;
* **the substitution hypothesis** (`Glue.substHyp_of_kernel`): `Q3KernelFSAll` at
  small `t` gives `SubstHypG` (which `Q3oneT_shift` needs).

## The bookkeeping

Write `R_p = ⟨Φ, (∫_{P_H}𝒟b†b)Φ⟩`, `R_q = ⟨Φ, (∫_{P_H^q}𝒟b†b)Φ⟩`,
`G = ⟨Φ, gapOpT Φ⟩` and `T = Σ_{k∈P_H} c_k⁻¹‖Y_kΦ‖²`, `c_k = (1-𝓁²)𝒟_k > 0`.
The target is the quadratic form of

`Q₃⁽¹⁾ + (1-𝓁²)∫_{P_H}𝒟b†b + (𝓁²/2)∫_{P_H^q}𝒟b†b + Q₂^ex + (b/100)gapOpT`,

which by pieces A and D is at least

`R1 - T + (1-𝓁²)R_p + (𝓁²/2)R_q + Q₂^ex + (b/100)G`

(the reserve uses `Σ_{k∈P_H} c_k⟨b_k†b_k⟩ = (1-𝓁²)R_p`, which cancels the
`-(1-𝓁²)R_p` of the completing the square).  Piece **B** is delegated in the
*sum form*

`T ≤ (𝓁²/4)R_q + 2ρŴ₁ω(0)⟨Gop⟩ + C_B e1A‖Φ‖² + (b/200)G`

(FS's `T₂,op` + `T₂,comm` estimate: the `b†b` part is absorbed by the `P_H^q`
reserve, and the `χ̂²` main part `2ρŴ₁ω(0)⟨Gop⟩` is FS's `eq:EstimT2comm` main
term), and the assembly itself performs the `Q₂^ex` cancellation: with
`Q3KernelFSAll.q2exLower`, `2ρŴ₁ω(0)⟨Gop⟩ ≤ ⟨Q₂^ex⟩ + (b/400)G`, we get

* `B`: `Q₂^ex - T ≥ -(C_B e1A)‖Φ‖² - (𝓁²/4)R_q - (3b/400)G`,
* `C`: `R1 ≥ -(C_C e1A)‖Φ‖² - (𝓁²/4)R_q - (b/800)G`,

so the whole is at least

`-((C_B+C_C)e1A)‖Φ‖² + (𝓁²/2 - 𝓁²/4 - 𝓁²/4)R_q + (b/100 - 3b/400 - b/800)G`,

whose last two terms are `0` and `(b/800)G ≥ 0`.

## Why the gap shares are `3b/400` (piece B) and `b/800` (piece C)

`Q3KernelFSAll`'s only hypothesis on `Q₂^ex` is `q2exLower`,
`2ρŴ₁ω(0)⟨G⟩ ≤ ⟨Q₂^ex⟩ + (b/400)⟨gapOpT⟩`, so the interface allows `⟨Q₂^ex⟩` to
be as negative as `-(b/400)G`; piece B must absorb that deficit (see
`Est1.estT2_false`, the machine-checked refutation of the earlier version with
the total share `b/800`).  Inside piece B the `b/200` is a *free* slack term
(the corrections of the `T₂` estimate beyond the reserve and `2ρŴ₁ω(0)⟨Gop⟩`),
and the budget `b/100 - 3b/400 - b/800 = b/800` stays nonnegative.

The proofs of the pieces are delegated; the file `Est1/estT2.lean` /
`Est1/estR1.lean` hold their exact statements.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

universe u v

/-! ## 1. The small scalar/positivity facts -/

/-- `𝓁 < 1` at FS's parameter point when `t < 1`.  This is the strictness of
`1 - 𝓁² > 0` needed for the reserve weight `c_k = (1-𝓁²)𝒟_k` to be positive on
`P_H` (the completing-the-square of piece D). -/
theorem lille_lt_one {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (h : FSParamsView E) (ht : h.t < 1) : E.lille < 1 := by
  have h1 : (0 : ℝ) < 97 / 2 / 323 := by norm_num
  have := (Real.rpow_lt_one_iff_of_pos h.t_pos).mpr (Or.inr ⟨ht, h1⟩)
  simpa only [Work.BoseB7.lille_val E h, Work.BoseBox.fsXp] using this

/-- The energy gap `G = ⟨Φ, gapOpT Φ⟩` is nonnegative: `gapOpT` is the sum of
the positive operators `ℓ⁻²n₊` and `ε_T(dℓ)⁻²n₊^H`. -/
theorem gapOpT_qw_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (hv : FSParamsView E) (Φ : F.H) :
    0 ≤ F.qw Φ (T.gapOpT E) := by
  have heT : 0 ≤ E.eT := eT_nonneg E hv
  have hell : 0 ≤ E.ell := le_of_lt (ell_pos E hv)
  have hd : 0 ≤ E.d := by
    rw [hv.d_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have h1 : 0 ≤ E.ell ^ (-(2 : ℝ)) := Real.rpow_nonneg hell _
  have h2 : 0 ≤ E.eT * (E.d * E.ell) ^ (-(2 : ℝ)) :=
    mul_nonneg heT (Real.rpow_nonneg (mul_nonneg hd hell) _)
  have hN := T.N_nonneg Φ
  have hNH := T.NH_nonneg Φ
  simp only [FockData.qw, Work.BoseB7A.TildeData.gapOpT, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg h1 hN) (mul_nonneg h2 hNH)

/-- **Positivity of the reserve weight** `c_k = (1-𝓁²)𝒟_k` on `P_H`: `𝓁 < 1` and
`𝒟_k ≥ ‖k‖²/4 > 0` there. -/
theorem cD_pos {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    (hPHq : ∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i)
    (hD : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 4 ≤ E.D q)
    (hlil : E.lille < 1) {k : Mode} (hk : k ∈ F.PHset E) : 0 < cD E k := by
  have hkPH : F.PH E.KH E.aScat k :=
    (Finset.mem_filter.mp (by simpa only [FockData.PHset] using hk)).2
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hcutpos : 0 < 1 / (2 * E.KH * E.aScat) := by positivity
  have hnorm : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcutpos hkPH
  have hDk : 0 < E.D k :=
    lt_of_lt_of_le (by positivity) (hD k (hPHq k hkPH))
  have hl : 0 < 1 - E.lille ^ 2 := by nlinarith [hlil, lille_pos E hv]
  rw [cD]
  exact mul_pos hl hDk

/-! ## 2. The reserve identification -/

/-- `Σ_{k∈P_H} c_k⟨b_k†b_k⟩ = (1-𝓁²)⟨Φ, (∫_{P_H}𝒟_kb_k†b_k)Φ⟩`, i.e. the PSD
weights `c_k = (1-𝓁²)𝒟_k` sum to `(1-𝓁²)` times the `P_H` reserve. -/
theorem sum_cD_mul_bp_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (Φ : F.H) :
    (∑ k ∈ F.PHset E, cD E k * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ))
      = (1 - E.lille ^ 2) * F.qw Φ (F.dNumOpR E (F.PH E.KH E.aScat)) := by
  have hstep : ∀ k ∈ F.PHset E,
      cD E k * F.bp (F.bOp E.alpha k Φ) (F.bOp E.alpha k Φ)
        = (1 - E.lille ^ 2) * (E.D k * F.bp (F.bNumOp E.alpha k Φ) Φ) := by
    intro k _
    rw [cD, FockData.bNumOp, LinearMap.comp_apply, bp_bOpDag]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  congr 1
  rw [FockData.qw, bp_dNumOpR F E (F.PH E.KH E.aScat) Φ]
  rfl

/-! ## 3. The assembly -/

/-- **The assembly of `EstQ3oneA` from the two analytic pieces and the
substitution hypothesis.**  See the module docstring for the bookkeeping. -/
theorem estQ3oneA_of_pieces (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (hB : ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (cD E k)⁻¹ * F.bp (shift F T E k Φ) (shift F T E k Φ)
            ≤ (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              + 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * e1A E * F.normSq Φ
              + (E.b / 200) * F.qw Φ (T.gapOpT E))
    (hC : ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          -(C * e1A E) * F.normSq Φ
              - (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              - (E.b / 800) * F.qw Φ (T.gapOpT E)
            ≤ F.qw Φ (R1 F T E))
    (hS : ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E → SubstHypG F T E) :
    EstQ3oneA.{u, v} K₀ b₀ hb₀ := by
  obtain ⟨CB, tB, hCB, htB, HB⟩ := hB
  obtain ⟨CC, tC, hCC, htC, HC⟩ := hC
  obtain ⟨tS, htS, HS⟩ := hS
  obtain ⟨t₁, ht₁, H₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, H₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨CB + CC, min (min tB (min tC tS)) (min t₁ (min t₂ (1 / 2))),
    add_nonneg hCB hCC, ?_, ?_⟩
  · exact lt_min (lt_min htB (lt_min htC htS)) (lt_min ht₁ (lt_min ht₂ (by norm_num)))
  intro Mode _ _ _ F T E hv ht hb hK Φ hΦ
  -- the thresholds
  have hA : hv.t ≤ min tB (min tC tS) := le_trans ht (min_le_left _ _)
  have hB12 : hv.t ≤ min t₁ (min t₂ (1 / 2)) := le_trans ht (min_le_right _ _)
  have htB' : hv.t ≤ tB := le_trans hA (min_le_left _ _)
  have htA' : hv.t ≤ min tC tS := le_trans hA (min_le_right _ _)
  have htC' : hv.t ≤ tC := le_trans htA' (min_le_left _ _)
  have htS' : hv.t ≤ tS := le_trans htA' (min_le_right _ _)
  have ht₁' : hv.t ≤ t₁ := le_trans hB12 (min_le_left _ _)
  have ht₂' : hv.t ≤ min t₂ (1 / 2) := le_trans hB12 (min_le_right _ _)
  have ht2'' : hv.t ≤ t₂ := le_trans ht₂' (min_le_left _ _)
  have hthalf : hv.t ≤ 1 / 2 := le_trans ht₂' (min_le_right _ _)
  -- the substitution hypothesis and the kernel basics
  have hsub : SubstHypG F T E := HS F T E hv htS' hb hK
  have hkern := H₁ F T E hv ht₁' hb hK
  have hkern2 := H₂ F T E hv ht2'' hb hK
  obtain ⟨-, -, -, -, hDq⟩ := hkern
  obtain ⟨hPHq, -⟩ := hkern2
  have hlil : E.lille < 1 := lille_lt_one E hv (by linarith)
  have hpos : ∀ k ∈ F.PHset E, 0 < cD E k := fun k hk => cD_pos F E hv hPHq hDq hlil hk
  -- the nonnegativity of `b` and of the gap form
  have hbnn : 0 ≤ E.b := le_trans (le_of_lt hb₀) hb
  have hGnn : 0 ≤ F.qw Φ (T.gapOpT E) := gapOpT_qw_nonneg F T E hv Φ
  have hnn : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
  -- piece A: the shift decomposition
  have hshift := Q3oneT_shift T E hsub hK.fL_even hK.W1_even
  -- piece D: the summed completing the square
  have hcs := compSquare_sum F T E hpos Φ
  -- the reserve identification
  have hres := sum_cD_mul_bp_eq F E Φ
  -- the two analytic pieces
  have hsumB := HB F T E hv htB' hb hK Φ hΦ
  have hC' := HC F T E hv htC' hb hK Φ hΦ
  -- the `Q₂^ex` cancellation: `q2exLower` and the `T₂` sum bound together give
  -- piece B's conclusion with the gap share `b/200 + b/400 = 3b/400`
  have hB' : -((CB * e1A E) * F.normSq Φ)
      - (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
      - (3 * E.b / 400) * F.qw Φ (T.gapOpT E)
      - ((1 / 2 : ℝ)) * F.qw Φ (F.dNumOpR E
          (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k))
      ≤ F.qw Φ (F.Q2exAll E)
        - ∑ k ∈ F.PHset E, (cD E k)⁻¹ *
          F.bp (shift F T E k Φ) (shift F T E k Φ) := by
    have hq2 := hK.q2exLowerR Φ hΦ
    -- the reserve on `RHi ∖ P_H^q` is a positive form
    have hres : 0 ≤ F.qw Φ (F.dNumOpR E
        (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k)) := by
      rw [FockData.qw, bp_dNumOpR F E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k) Φ]
      exact Finset.sum_nonneg fun q _ =>
        mul_nonneg (FockData.Dcoef_nonneg (hK.AB q))
          (bp_bNumOp_nonneg F E.alpha q Φ)
    linarith [hsumB, hq2, hres]
  -- the split of the target form
  have hsplit : F.qw Φ (T.Q3oneT E + (1 - E.lille ^ 2) • F.dNumOpR E (F.PH E.KH E.aScat) +
        (E.lille ^ 2 / 2) • F.dNumOpR E (F.PHq E.KH E.aScat) +
        ((1 / 2 : ℝ)) • F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k) +
        F.Q2exAll E + (E.b / 100) • T.gapOpT E)
      = F.qw Φ (T.Q3oneT E) + (1 - E.lille ^ 2) * F.qw Φ (F.dNumOpR E (F.PH E.KH E.aScat)) +
        (E.lille ^ 2 / 2) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) +
        ((1 / 2 : ℝ)) * F.qw Φ (F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k)) +
        F.qw Φ (F.Q2exAll E) + (E.b / 100) * F.qw Φ (T.gapOpT E) := by
    simp only [FockData.qw_add, FockData.qw_smul]
  -- the shift split
  have hq3 : F.qw Φ (T.Q3oneT E)
      = F.qw Φ (∑ k ∈ F.PHset E, (F.bOpDag E.alpha k ∘ₗ shift F T E k +
          shiftDag F T E k ∘ₗ F.bOp E.alpha k)) + F.qw Φ (R1 F T E) := by
    rw [hshift, FockData.qw_add]
  -- the leftover gap budget
  have hleft : 0 ≤ (E.b / 100 - 3 * E.b / 400 - E.b / 800) * F.qw Φ (T.gapOpT E) :=
    mul_nonneg (by linarith) hGnn
  linarith [hcs, hres, hsplit, hq3, hB', hC', hleft, hnn]

end Est1

end Work.BoseC3QAll
