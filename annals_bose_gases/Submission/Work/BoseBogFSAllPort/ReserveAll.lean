import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.AllDefs
import Submission.Work.BoseFixR.pairOp_shift_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFSAllPort.ReserveAll` — the `hRes` rewire around the `𝒞`-form

`Work.BoseBogFS.bogOpBound_at` consumes the *reserve* row

```
⟨f, dNumOpR_{RHi} f⟩ ≤ ⟨f, 𝒦^Bog f⟩ + (Σ_k ½(𝒵_k+κ_k) + Res)·‖f‖² .
```

The frozen derivation (`Work.BoseBogFS.qw_dNumOpR_le_res`) obtains it from the Cauchy–Schwarz
comparison of the *unshifted* `b_k` with the shifted `b_k+c_k`, at the price of the window
constant `winKbar` (which grows like `N⁵` and is unusable at the honest cube).  Here the
comparison is done **exactly**: the two operators differ by the 𝒞-linear form

```
Cform = Σ_{k ∈ RHi} (½ 𝒞_k) • (a_k + a_k† + a_{−k} + a_{−k}†)
```

and a scalar, so the reserve row holds with `Res =` any bound for the quadratic form of
`Cform` — which is exactly what `Work.BoseBogFS.honest_linHi` supplies (`≤ C·errBracket·‖f‖²`).
No window state beyond `T.NWindow` is used, and no `winKbar`/`Dsup`/`G` occurs.

## The algebra

With `𝒟_k = bogD`, `c_k = bogGamma`, `α_k = bogAlpha`, `b_k = a_k + α_k a_{−k}†`:

* `(b_k+c_k)†(b_k+c_k) = b_k†b_k + c_k(b_k†+b_k) + c_k²·1` (`bogBShift_mul`);
* `qw f (b_k†b_k) = ‖b_k f‖²` and `qw f ((b_k+c_k)†(b_k+c_k)) = ‖(b_k+c_k) f‖²`;
* `(b_k†+b_k) + (b_{−k}†+b_{−k}) = (1+α_k)(a_k+a_k†+a_{−k}+a_{−k}†)`
  (`Work.BoseFixR.pairOp_lin_sum`);
* `𝒟_k c_k (1+α_k) = 𝒞_k` (`Submission.BoseGases.fms_lin_coeff`).

Hence, on a `k ↦ −k`-symmetric index set,

```
Σ_{k∈s} 𝒟_k (b_k+c_k)†(b_k+c_k) = Σ_{k∈s} 𝒟_k b_k†b_k + 𝒬 + (Σ_{k∈s} 𝒟_kc_k²)·1 ,   𝒬 = Σ_{k∈s}(½𝒞_k)•(…),
```

i.e. the shifted diagonal is the unshifted one **plus** the `𝒞`-form.  With
`qw_dNumOpShifted_le` (`shifted diagonal ≤ 𝒦^Bog + Σ½(𝒵+κ)‖f‖²`) this gives the reserve row.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFSAllPort

open Work.BoseB7 Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 0. Two abbreviations -/

/-- The linear part `b_k† + b_k` of the shifted squeezing operator. -/
def bogLin (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.bOpDag (bogAlpha E ρ) k + F.bOp (bogAlpha E ρ) k

/-- FS's four-term linear combination `a_k + a_k† + a_{−k} + a_{−k}†` (the operator whose
coefficient in `𝒦^Bog` is `𝒞_k`). -/
def bogV (F : Work.BoseB7.FockData Mode) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.a k + F.aDag k + F.a (-k) + F.aDag (-k)

/-- The `𝒞`-form of the reserve: `Σ_{k∈s} (½𝒞_k) • (a_k + a_k† + a_{−k} + a_{−k}†)`. -/
def bogCform (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (s : Finset Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ k ∈ s, ((1 / 2 : ℝ) * bogC E ρ k) • bogV F k

/-! ## 1. Elementary quadratic-form lemmas -/

theorem qw_add_of (F : Work.BoseB7.FockData Mode) (f : F.H)
    (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw f (X + Y) = F.qw f X + F.qw f Y := by
  simp only [FockData.qw, LinearMap.add_apply, map_add]

theorem qw_smul_of (F : Work.BoseB7.FockData Mode) (f : F.H) (c : ℝ)
    (X : F.H →ₗ[ℝ] F.H) :
    F.qw f (c • X) = c * F.qw f X := by
  simp only [FockData.qw, LinearMap.smul_apply, map_smul, smul_eq_mul]

theorem qw_one_of (F : Work.BoseB7.FockData Mode) (f : F.H) :
    F.qw f (1 : F.H →ₗ[ℝ] F.H) = F.normSq f := by
  simp only [FockData.qw, FockData.normSq, Module.End.one_eq_id, LinearMap.id_apply]

/-! ## 2. Reindexing a `k ↦ −k`-symmetric finset -/

theorem sum_neg_of_symm (s : Finset Mode) (hs : ∀ k : Mode, k ∈ s ↔ -k ∈ s) (g : Mode → ℝ) :
    (∑ k ∈ s, g (-k)) = ∑ k ∈ s, g k := by
  refine Finset.sum_bij (fun k _ => -k) (fun a ha => (hs a).mp ha)
    (fun a₁ _ a₂ _ h => by simpa using h) ?_ (fun a _ => rfl)
  intro b hb
  exact ⟨-b, (hs b).mp hb, by simp⟩

/-! ## 3. Evenness of the per-mode coefficients -/

theorem bogAlpha_even (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (hAe : ∀ k : Mode, bogA E ρ k = bogA E ρ (-k))
    (hBe : ∀ k : Mode, bogB E ρ k = bogB E ρ (-k)) (k : Mode) :
    bogAlpha E ρ (-k) = bogAlpha E ρ k := by
  simp only [bogAlpha, hAe k, hBe k]

theorem bogGamma_even (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (hAe : ∀ k : Mode, bogA E ρ k = bogA E ρ (-k))
    (hBe : ∀ k : Mode, bogB E ρ k = bogB E ρ (-k))
    (hCe : ∀ k : Mode, bogC E ρ k = bogC E ρ (-k)) (k : Mode) :
    bogGamma E ρ (-k) = bogGamma E ρ k := by
  simp only [bogGamma, hAe k, hBe k, hCe k]

/-- The coefficient identity `𝒟_k c_k (1+α_k) = 𝒞_k` of FS `eq:Defb_k`. -/
theorem bogD_mul_gamma_mul_one_add_alpha (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : 0 < bogA E ρ k + bogB E ρ k) :
    bogD E ρ k * bogGamma E ρ k * (1 + bogAlpha E ρ k) = bogC E ρ k := by
  simpa only [bogD, bogGamma, bogAlpha, bogC] using
    Submission.BoseGases.fms_lin_coeff (A := bogA E ρ k) (B := bogB E ρ k) (L := bogC E ρ k)
      hA hB hAB

/-! ## 4. The pointwise shift identity -/

/-- The shift expansion of the honest shifted squeezing operator:
`(b_k+c_k)†(b_k+c_k) = b_k†b_k + c_k(b_k†+b_k) + c_k²·1`. -/
theorem bogBShift_mul (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) :
    (bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)
      = (F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)
        + (bogGamma E ρ k) • bogLin F E ρ k
        + ((bogGamma E ρ k) ^ 2) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h := Work.BoseFixR.pairShift_mul F (bogA E ρ) (bogB E ρ) (bogC E ρ) k
  rw [show Work.BoseFixR.pairShiftDag F (bogA E ρ) (bogB E ρ) (bogC E ρ) k
        = bogBShiftDag F E ρ k from rfl,
      show Work.BoseFixR.pairShift F (bogA E ρ) (bogB E ρ) (bogC E ρ) k
        = bogBShift F E ρ k from rfl,
      show Work.BoseFixR.pairAlpha (bogA E ρ) (bogB E ρ) = bogAlpha E ρ from rfl,
      show Work.BoseFixR.pairGamma (bogA E ρ) (bogB E ρ) (bogC E ρ) = bogGamma E ρ from rfl]
    at h
  simpa only [bogLin] using h

/-- `qw f (b_k†b_k) = ‖b_k f‖²` at the honest squeezing parameter. -/
theorem qw_bNumOp (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) (f : F.H) :
    F.qw f ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k))
      = F.normSq ((F.bOp (bogAlpha E ρ) k) f) := by
  rw [FockData.qw, LinearMap.comp_apply, Work.BoseB7.bOpDag_bp, FockData.normSq]

/-- The pairing identity: `(b_k†+b_k) + (b_{−k}†+b_{−k}) = (1+α_k)(a_k+a_k†+a_{−k}+a_{−k}†)`. -/
theorem bogLin_add (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (k : Mode) (hα : bogAlpha E ρ (-k) = bogAlpha E ρ k) :
    bogLin F E ρ k + bogLin F E ρ (-k) = (1 + bogAlpha E ρ k) • bogV F k := by
  have h := Work.BoseFixR.pairOp_lin_sum F (bogAlpha E ρ) k hα
  simp only [bogLin, bogV]
  rw [h]
  abel

/-! ## 5. The `𝒞`-form is the shift correction -/

/-- **The middle term of the shift identity.**  On a `k ↦ −k`-symmetric index set `s`, the
`c_k(b_k†+b_k)`-sum is the quadratic form of the `𝒞`-form. -/
theorem sum_gamma_lin_eq_qw_cform (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (s : Finset Mode) (hs : ∀ k : Mode, k ∈ s ↔ -k ∈ s) (f : F.H)
    (hnum : BogNumeric F E ρ) :
    (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ k))
      = F.qw f (bogCform F E ρ s) := by
  have hα := bogAlpha_even E ρ hnum.hAe hnum.hBe
  have hD := bogD_even E ρ hnum.hAe hnum.hBe
  have hγ := bogGamma_even E ρ hnum.hAe hnum.hBe hnum.hCe
  -- the two half-sums agree
  have hhalf : (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ (-k)))
      = (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ k)) := by
    have hB : (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ (-k)))
        = (∑ k ∈ s, (bogD E ρ (-k) * bogGamma E ρ (-k)) * F.qw f (bogLin F E ρ (-k))) :=
      Finset.sum_congr rfl (fun k _ => by rw [hD k, hγ k])
    rw [hB]
    exact sum_neg_of_symm s hs
      (fun j => (bogD E ρ j * bogGamma E ρ j) * F.qw f (bogLin F E ρ j))
  have hstep : ∀ k : Mode, ((1 / 2 : ℝ) * bogC E ρ k) * F.qw f (bogV F k)
      = (1 / 2 : ℝ) * ((bogD E ρ k * bogGamma E ρ k) *
          (F.qw f (bogLin F E ρ k) + F.qw f (bogLin F E ρ (-k)))) := by
    intro k
    have hp : F.qw f (bogLin F E ρ k) + F.qw f (bogLin F E ρ (-k))
        = (1 + bogAlpha E ρ k) * F.qw f (bogV F k) := by
      rw [← qw_add_of, bogLin_add F E ρ k (hα k), qw_smul_of]
    rw [hp, ← bogD_mul_gamma_mul_one_add_alpha E ρ k (hnum.hA k) (hnum.hB k) (hnum.hAB k)]
    ring
  have hsum2 : (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) *
        (F.qw f (bogLin F E ρ k) + F.qw f (bogLin F E ρ (-k))))
      = (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ k))
        + (∑ k ∈ s, (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ k)) := by
    rw [Finset.sum_congr rfl (fun k _ => mul_add _ _ _), Finset.sum_add_distrib, hhalf]
  rw [bogCform, qw_sum_finset]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [← Finset.mul_sum, hsum2]
  ring

/-! ## 6. The two index-set bridges -/

/-- `RHi` is even: `kmom (-k) = -kmom k`. -/
theorem RHi_neg_iff (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (k : Mode) :
    RHi F E (-k) ↔ RHi F E k := by
  simp only [RHi, F.kmom_neg, norm_neg]

/-- The `RHi`-filtered *excited* set is `k ↦ −k`-symmetric. -/
theorem symm_excited_filter_RHi (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) :
    ∀ k : Mode, k ∈ (Work.BoseB7.excited Mode).filter (RHi F E)
      ↔ -k ∈ (Work.BoseB7.excited Mode).filter (RHi F E) := by
  intro k
  simp only [Finset.mem_filter, Work.BoseB7.excited, Finset.mem_erase, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hk0, hk⟩
    exact ⟨by simpa using hk0, (RHi_neg_iff F E k).mpr hk⟩
  · rintro ⟨hk0, hk⟩
    exact ⟨by simpa using hk0, (RHi_neg_iff F E k).mp hk⟩

/-- For `¬RHi E 0` the `RHi`-filter over `univ` is the `RHi`-filter over the excited modes. -/
theorem filter_RHi_eq (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (h0 : ¬ RHi F E 0) :
    Finset.univ.filter (RHi F E) = (Work.BoseB7.excited Mode).filter (RHi F E) := by
  rw [show Work.BoseB7.excited Mode = (Finset.univ : Finset Mode).erase 0 from rfl,
    Finset.filter_erase, Finset.erase_eq_self.mpr (by simp [h0])]

theorem not_RHi_zero (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (hκ : 0 < E.KL * Real.sqrt (E.mu * E.aScat)) : ¬ RHi F E 0 := by
  intro h
  have h0 : F.kmom 0 = 0 := kmom_zero F
  simp only [RHi, h0, norm_zero] at h
  linarith [hκ]

/-! ## 7. The reserve identity and the reserve row -/

/-- **The exact shift identity.**  On a `k ↦ −k`-symmetric index set, the shifted diagonal is
the unshifted one plus the `𝒞`-form plus a scalar. -/
theorem qw_shifted_eq_dNumOpR_add (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (s : Finset Mode) (hs : ∀ k : Mode, k ∈ s ↔ -k ∈ s) (f : F.H)
    (hnum : BogNumeric F E ρ) :
    F.qw f (∑ k ∈ s, (bogD E ρ k) •
        ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)))
      = F.qw f (∑ k ∈ s, (bogD E ρ k) •
          ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)))
        + F.qw f (bogCform F E ρ s)
        + (∑ k ∈ s, (bogD E ρ k) * (bogGamma E ρ k) ^ 2) * F.normSq f := by
  have hsumAB : (∑ k ∈ s, (bogD E ρ k) •
        ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)))
      = ∑ k ∈ s, (bogD E ρ k) •
          ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)
            + (bogGamma E ρ k) • bogLin F E ρ k
            + ((bogGamma E ρ k) ^ 2) • (1 : F.H →ₗ[ℝ] F.H)) :=
    Finset.sum_congr rfl (fun k _ => by rw [bogBShift_mul F E ρ k])
  rw [hsumAB, qw_sum_finset]
  have hterm : ∀ k : Mode, (bogD E ρ k) * F.qw f
        ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)
          + (bogGamma E ρ k) • bogLin F E ρ k
          + ((bogGamma E ρ k) ^ 2) • (1 : F.H →ₗ[ℝ] F.H))
      = (bogD E ρ k) * F.qw f ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k))
        + (bogD E ρ k * bogGamma E ρ k) * F.qw f (bogLin F E ρ k)
        + (bogD E ρ k * (bogGamma E ρ k) ^ 2) * F.normSq f := by
    intro k
    rw [qw_add_of, qw_add_of, qw_smul_of, qw_smul_of, qw_one_of]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← qw_sum_finset]
  rw [sum_gamma_lin_eq_qw_cform F E ρ s hs f hnum]
  rw [← Finset.sum_mul]

/-- **The reserve row, rewired around the `𝒞`-form.**  If the `𝒞`-form of the state is
bounded by `Res·‖f‖²`, then the unshifted diagonal on `RHi` is dominated by `𝒦^Bog` plus
`(Σ_k ½(𝒵_k+κ_k) + Res)·‖f‖²` — no `winKbar`, no Cauchy–Schwarz parameter. -/
theorem qw_dNumOpR_le_lin (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ Res : ℝ) (hnum : BogNumeric F E ρ)
    (hlin : ∀ f : F.H, T.NWindow E.bigM f →
      |F.qw f (bogCform F E ρ ((Work.BoseB7.excited Mode).filter
          (RHi F (Work.BoseFixR.KzEnvAt E ρ))))| ≤ Res * F.normSq f) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (F.dNumOpR (Work.BoseFixR.KzEnvAt E ρ) (RHi F (Work.BoseFixR.KzEnvAt E ρ)))
        ≤ F.qw f (KzBogFS F E ρ)
          + ((∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
                + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))) + Res)
              * F.normSq f := by
  intro f hf
  set s : Finset Mode := (Work.BoseB7.excited Mode).filter (RHi F (Work.BoseFixR.KzEnvAt E ρ))
    with hsdef
  have hsymm : ∀ k : Mode, k ∈ s ↔ -k ∈ s := by
    intro k
    rw [hsdef]
    exact symm_excited_filter_RHi F (Work.BoseFixR.KzEnvAt E ρ) k
  have hDl : (Work.BoseFixR.KzEnvAt E ρ).D = bogD E ρ := funext fun k => rfl
  have hAl : (Work.BoseFixR.KzEnvAt E ρ).alpha = bogAlpha E ρ := funext fun k => rfl
  have hdnr : F.qw f (∑ k ∈ s, (bogD E ρ k) •
        ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)))
      = F.qw f (F.dNumOpR (Work.BoseFixR.KzEnvAt E ρ)
          (RHi F (Work.BoseFixR.KzEnvAt E ρ))) := by
    simp only [FockData.dNumOpR, FockData.regionSum, FockData.bNumOp, hsdef, s]
    rw [hDl, hAl]
  have hdns : F.qw f (∑ k ∈ s, (bogD E ρ k) •
        ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)))
      = F.qw f (dNumOpShifted F E ρ (RHi F (Work.BoseFixR.KzEnvAt E ρ))) := by
    simp only [dNumOpShifted, FockData.regionSum, hsdef, s]
  have hid := qw_shifted_eq_dNumOpR_add F E ρ s hsymm f hnum
  have hle := qw_dNumOpShifted_le F E ρ f hnum.hA hnum.hB hnum.hAB hnum.hAe hnum.hBe hnum.hCe
    hnum.hccr
  rw [← hdns] at hle
  have hlinf := hlin f hf
  have hnn : 0 ≤ F.normSq f := F.bp_nonneg f
  have hsq : 0 ≤ (∑ k ∈ s, (bogD E ρ k) * (bogGamma E ρ k) ^ 2) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (Submission.BoseGases.bogD_pos
      (hnum.hA k) (hnum.hB k))) (sq_nonneg _))
  have hnegc : -F.qw f (bogCform F E ρ s) ≤ Res * F.normSq f :=
    le_trans (neg_le_abs _) hlinf
  rw [← hdnr]
  have hkey : F.qw f (∑ k ∈ s, (bogD E ρ k) •
        ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)))
      = F.qw f (∑ k ∈ s, (bogD E ρ k) •
          ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)))
        - F.qw f (bogCform F E ρ s)
        - (∑ k ∈ s, (bogD E ρ k) * (bogGamma E ρ k) ^ 2) * F.normSq f := by
    linarith [hid]
  rw [hkey]
  nlinarith [hle, hnegc, hnn, hsq]

end Work.BoseBogFSAllPort
