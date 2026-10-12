import ChallengeDeps
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Normalisation` — the scaling analysis of the delivered inputs

The corpus trial space `CSBox N L` is *unnormalised*, while

* `WordDens`, `EnergyWord` are homogeneous of degree `0`
  (`Submission.Work.SboxHomogeneity.sboxE_smul` divided by the `L²`-norm), and
* `cnPlus` is homogeneous of degree `2`
  (`Submission.Work.SboxHomogeneity.cnPlus_smul`).

Hence a statement of the shape

    ∀ Φ, WordDens Φ ≤ Θ → cnPlus Φ ≤ W          (†)

has a *scale-invariant hypothesis* and a *quadratic conclusion*: it is not a
statement about normalised states.  This module machine-checks the consequences:

* `aprioriNPlus_forces_cnPlus_zero` — **(†) forces `cnPlus = 0` on every low
  state.**  Applied to the scaled state `c•Φ` (`c → ∞`, `WordDens (c•Φ) =
  WordDens Φ`) it gives `c²·cnPlus Φ ≤ W N L` for every `c > 0`, hence
  `cnPlus Φ = 0`.  So the delivered `Work.UBB.AprioriNPlus` is **not** FS
  `eq:apriorinn+`; it is a much stronger (and, as soon as one low state has
  `cnPlus ≠ 0`, false) statement.
* `dlSlide_forces_cnPlus_zero` — the same for the delivered
  `Work.DLWire.DLSlide` (whose conclusion `R' + (b/2L²)·cnPlus − K` is
  quadratic while `EnergyWord` is invariant).
* `dlSlideNorm_iff_dlSlideCov` — the *correct* form is the delivered statement
  restricted to states of `abox`-norm one (`DLSlideNorm`), equivalently its
  scale-covariant closure `DLSlideCov`.  `dlSlide_imp_dlSlideNorm` records that
  the delivered `DLSlide` implies its own restriction (it is strictly stronger
  — that is exactly the defect).
* `spectralInput_iff_bogoliubovLow` — the delivered `Work.UBB.BogoliubovLow`
  (hypothesis `cnPlus ≤ W N L`) is **equivalent** to `Work.UBB.SpectralInput`
  once `W > 0`: scaling a low state *down* makes the window hypothesis hold, so
  the window is vacuous in the delivered normalisation.  The covariant repair
  `BogoliubovLowCov` is what makes the window a genuine hypothesis.

Nothing here edits the UBB/DLWire chapters (they are other areas' files): the
repairs are *new* definitions in `Work.UBBInputs.Defs`, and `Chain.lean` runs
`hpres` from the repaired inputs through the delivered assembly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Scaling of the corpus words -/

/-- `sqNormN` is homogeneous of degree `2`. -/
lemma smul_sqNormN {N : ℕ} (L : ℝ) (Φ : X N → ℝ) (c : ℝ) :
    sqNormN N L (c • Φ) = c ^ 2 * sqNormN N L Φ := by
  simp only [sqNormN]
  exact abox_integral_sq_smul L Φ c

/-- The scaled state `c • Φ` of a `CSBox` state, for `c ≠ 0`. -/
noncomputable def scaledBox {N : ℕ} {L : ℝ} (Φ : CSBox N L) {c : ℝ} (hc : c ≠ 0) :
    CSBox N L :=
  let Ph : X N → ℝ := Φ
  have hPhc : ContDiff ℝ ∞ (c • Ph) := Φ.contDiff.const_smul c
  have hne : c • Ph ≠ 0 := smul_ne_zero hc Φ.nezero
  have hpos : 0 < ∫ x in abox N L, ((c • Ph) x) ^ 2 := by
    rw [abox_integral_sq_smul]
    exact mul_pos (sq_pos_of_ne_zero hc) (by simpa [Ph] using Φ.sq_pos)
  CSBox.ofFun hPhc hne hpos

@[simp] lemma scaledBox_coe {N : ℕ} {L : ℝ} (Φ : CSBox N L) {c : ℝ} (hc : c ≠ 0) :
    ((scaledBox Φ hc : CSBox N L) : X N → ℝ) = c • (Φ : X N → ℝ) := rfl

/-- Unfolding of `WordDens` in the corpus words. -/
lemma wordDens_eq {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v} (Φ : X N → ℝ) :
    WordDens N L μ v h Φ
      = sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) Φ / (L ^ 3 * sqNormN N L Φ) := rfl

/-- Unfolding of `EnergyWord` in the corpus words. -/
lemma energyWord_eq {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v} (Φ : CSBox N L) :
    EnergyWord N L μ v h Φ
      = (kinWord N L (Φ : X N → ℝ)
          + qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ))
        / sqNormN N L (Φ : X N → ℝ) := rfl

/-- Cancellation of a common nonzero factor in a quotient. -/
lemma div_scale_cancel (a b c : ℝ) (hc : c ≠ 0) : c * a / (c * b) = a / b := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  · have hcb : c * b ≠ 0 := mul_ne_zero hc hb
    rw [div_eq_div_iff hcb hb]
    ring

/-- **`WordDens` is scale-invariant** — the squared norms cancel. -/
lemma wordDens_smul {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v}
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {c : ℝ} (hc : c ≠ 0) :
    WordDens N L μ v h (c • Φ) = WordDens N L μ v h Φ := by
  have hq : ∀ Ψ : X N → ℝ, WordDens N L μ v h Ψ
      = sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) Ψ / (L ^ 3 * sqNormN N L Ψ) := by
    intro Ψ
    simp only [WordDens, sboxE, sqNormN]
  rw [hq, hq, sboxE_smul (wPairC L v) (wPairC L (g0 v h)) hΦ c, smul_sqNormN,
    show L ^ 3 * (c ^ 2 * sqNormN N L Φ) = c ^ 2 * (L ^ 3 * sqNormN N L Φ) by ring]
  exact div_scale_cancel _ _ _ (pow_ne_zero 2 hc)

/-- **`EnergyWord` is scale-invariant.** -/
lemma energyWord_smul {N : ℕ} {L μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v}
    (Φ : CSBox N L) {c : ℝ} (hc : c ≠ 0) :
    EnergyWord N L μ v h (scaledBox Φ hc) = EnergyWord N L μ v h Φ := by
  have hq : ∀ Ψ : CSBox N L, EnergyWord N L μ v h Ψ
      = sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) (Ψ : X N → ℝ)
          / sqNormN N L (Ψ : X N → ℝ) := by
    intro Ψ
    simp only [EnergyWord, sboxE, sqNormN]
  rw [hq, hq, scaledBox_coe, sboxE_smul (wPairC L v) (wPairC L (g0 v h)) Φ.contDiff c,
    smul_sqNormN]
  exact div_scale_cancel _ _ _ (pow_ne_zero 2 hc)

/-! ## 2. The normalisation defect of the delivered inputs -/

/-- **`AprioriNPlus` forces `cnPlus = 0` on every low state.**  A machine-checked
consequence of the delivered statement's shape (`WordDens` scale-invariant,
`cnPlus` quadratic): applying it to `c • Φ` for every `c > 0` gives
`c²·cnPlus Φ ≤ W N L`, hence `cnPlus Φ = 0`. -/
theorem aprioriNPlus_forces_cnPlus_zero {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    {W : ℕ → ℝ → ℝ} {ε₀ : ℝ} (hA : AprioriNPlus v h J W ε₀)
    {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : dens N L * (a v) ^ 3 ≤ ε₀)
    {Φ : CSBox N L}
    (hlow : WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L)) :
    cnPlus L (Φ : X N → ℝ) = 0 := by
  have hcn0 : 0 ≤ cnPlus L (Φ : X N → ℝ) := Work.SmallBoxSliding.cnPlus_nonneg L
  have key : ∀ c : ℝ, 0 < c → c ^ 2 * cnPlus L (Φ : X N → ℝ) ≤ W N L := by
    intro c hc
    have hlow' : WordDens N L (dens N L) v h ((scaledBox Φ hc.ne') : X N → ℝ)
        ≤ Theta (a v) J (dens N L) := by
      rw [scaledBox_coe, wordDens_smul Φ.contDiff hc.ne']
      exact hlow
    have hres := hA L hL N hN (scaledBox Φ hc.ne') hlow'
    rw [scaledBox_coe, cnPlus_smul] at hres
    exact hres
  by_contra hne
  have hnpos : 0 < cnPlus L (Φ : X N → ℝ) := lt_of_le_of_ne hcn0 (Ne.symm hne)
  have hbig : W N L < ((|W N L| / cnPlus L (Φ : X N → ℝ) + 1) : ℝ) ^ 2
      * cnPlus L (Φ : X N → ℝ) := by
    set c : ℝ := |W N L| / cnPlus L (Φ : X N → ℝ) + 1 with hcdef
    have hge1 : (1 : ℝ) ≤ c := by
      rw [hcdef]
      have hnn : 0 ≤ |W N L| / cnPlus L (Φ : X N → ℝ) :=
        div_nonneg (abs_nonneg _) hcn0
      linarith
    have hcn : c * cnPlus L (Φ : X N → ℝ) = |W N L| + cnPlus L (Φ : X N → ℝ) := by
      rw [hcdef]
      field_simp
    have hstep1 : cnPlus L (Φ : X N → ℝ) ≤ c * cnPlus L (Φ : X N → ℝ) := by
      have h := mul_le_mul_of_nonneg_right hge1 hcn0
      simpa using h
    have hstep2 : c * cnPlus L (Φ : X N → ℝ) ≤ c * (c * cnPlus L (Φ : X N → ℝ)) :=
      mul_le_mul_of_nonneg_left hstep1 (by rw [hcdef]; positivity)
    have hsq : c ^ 2 * cnPlus L (Φ : X N → ℝ) = c * (c * cnPlus L (Φ : X N → ℝ)) := by ring
    rw [hsq]
    linarith [hstep2, hcn, le_abs_self (W N L), hnpos]
  have hkey := key (|W N L| / cnPlus L (Φ : X N → ℝ) + 1) (by positivity)
  linarith [hkey, hbig]

/-- The `DLSlide` conclusion is quadratic in the state while `EnergyWord` is
scale-invariant; hence the same argument: **`DLSlide` forces `cnPlus = 0` on
every low state.** -/
theorem dlSlide_forces_cnPlus_zero {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    (hb : 0 < b) (hd : Work.DLWire.DLSlide v h b K_B R' J ε₀)
    {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : dens N L * (a v) ^ 3 ≤ ε₀)
    {Φ : CSBox N L}
    (hlow : WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L)) :
    cnPlus L (Φ : X N → ℝ) = 0 := by
  have hcn0 : 0 ≤ cnPlus L (Φ : X N → ℝ) := Work.SmallBoxSliding.cnPlus_nonneg L
  let A : ℝ := b / (2 * L ^ 2)
  have hApos : 0 < A := by rw [show A = b / (2 * L ^ 2) from rfl]; positivity
  let D : ℝ := EnergyWord N L (dens N L) v h Φ - R'
    + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
        * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
  have key : ∀ c : ℝ, 0 < c → A * (c ^ 2 * cnPlus L (Φ : X N → ℝ)) ≤ D := by
    intro c hc
    have hlow' : WordDens N L (dens N L) v h ((scaledBox Φ hc.ne') : X N → ℝ)
        ≤ Theta (a v) J (dens N L) := by
      rw [scaledBox_coe, wordDens_smul Φ.contDiff hc.ne']
      exact hlow
    have hres := hd L hL N hN (scaledBox Φ hc.ne') hlow'
    rw [scaledBox_coe, cnPlus_smul, energyWord_smul Φ hc.ne'] at hres
    show A * (c ^ 2 * cnPlus L (Φ : X N → ℝ)) ≤ D
    rw [show A = b / (2 * L ^ 2) from rfl,
      show D = EnergyWord N L (dens N L) v h Φ - R'
        + 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
            * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) from rfl]
    linarith [hres]
  by_contra hne
  have hnpos : 0 < cnPlus L (Φ : X N → ℝ) := lt_of_le_of_ne hcn0 (Ne.symm hne)
  have hAn : 0 < A * cnPlus L (Φ : X N → ℝ) := mul_pos hApos hnpos
  set c : ℝ := Real.sqrt ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ))) + 1 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hbig : D < A * (c ^ 2 * cnPlus L (Φ : X N → ℝ)) := by
    have hs : (Real.sqrt ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)))) ^ 2
        = (|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)) := Real.sq_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ))) + 1 := by
      have := Real.sqrt_nonneg ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)))
      linarith
    have hsq : (|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)) ≤ c ^ 2 := by
      rw [hcdef]
      nlinarith [hs, hs1,
        Real.sqrt_nonneg ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)))]
    have hmul : A * cnPlus L (Φ : X N → ℝ) * ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)))
        = |D| + 1 := by
      field_simp
    have hstep : A * cnPlus L (Φ : X N → ℝ) * ((|D| + 1) / (A * cnPlus L (Φ : X N → ℝ)))
        ≤ A * cnPlus L (Φ : X N → ℝ) * c ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hAn)
    rw [hmul] at hstep
    nlinarith [hstep, le_abs_self D]
  have hkey := key c hcpos
  linarith [hkey, hbig]

/-! ## 3. The repaired statements and the delivered ones -/

/-- The delivered `DLSlide` is *stronger* than its restriction to states of
`abox`-norm one — which is exactly the defect (`dlSlide_forces_cnPlus_zero`). -/
theorem dlSlide_imp_dlSlideNorm {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    (hd : Work.DLWire.DLSlide v h b K_B R' J ε₀) : DLSlideNorm v h b K_B R' J ε₀ := by
  intro L hL N hN Φ _ hlow
  exact hd L hL N hN Φ hlow

/-- `DLSlideNorm` restricts `DLSlideCov` (set the normalisation to `1`). -/
theorem dlSlideNorm_of_dlSlideCov {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    (hd : DLSlideCov v h b K_B R' J ε₀) : DLSlideNorm v h b K_B R' J ε₀ := by
  intro L hL N hN Φ hnorm hlow
  have hres := hd L hL N hN Φ hlow
  rwa [hnorm, div_one] at hres

/-- **`DLSlideCov` from `DLSlideNorm`**: rescale the state to `abox`-norm one
(`scaledBox` with `c = (√∫Φ²)⁻¹`) and use the homogeneity
`cnPlus(c•Φ) = c²·cnPlus Φ` and the invariance `EnergyWord(c•Φ) = EnergyWord Φ`.
Hence `DLSlideNorm ↔ DLSlideCov`: the covariant form is the honest closure of
FS's normalised statement. -/
theorem dlSlideCov_of_dlSlideNorm {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ}
    (hd : DLSlideNorm v h b K_B R' J ε₀) : DLSlideCov v h b K_B R' J ε₀ := by
  intro L hL N hN Φ hlow
  have hIpos : 0 < sqNormN N L (Φ : X N → ℝ) := Φ.sq_pos
  set c : ℝ := (Real.sqrt (sqNormN N L (Φ : X N → ℝ)))⁻¹ with hcdef
  have hcne : c ≠ 0 := by
    rw [hcdef]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hIpos))
  have hc2 : c ^ 2 = (sqNormN N L (Φ : X N → ℝ))⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (le_of_lt hIpos)]
  have hnorm : sqNormN N L ((scaledBox Φ hcne : CSBox N L) : X N → ℝ) = 1 := by
    rw [scaledBox_coe, smul_sqNormN, hc2]
    field_simp
  have hlow' : WordDens N L (dens N L) v h ((scaledBox Φ hcne : CSBox N L) : X N → ℝ)
      ≤ Theta (a v) J (dens N L) := by
    rw [scaledBox_coe, wordDens_smul Φ.contDiff hcne]
    exact hlow
  have hres := hd L hL N hN (scaledBox Φ hcne) hnorm hlow'
  rw [scaledBox_coe, cnPlus_smul, energyWord_smul Φ hcne] at hres
  have hdiv : c ^ 2 * cnPlus L (Φ : X N → ℝ)
      = cnPlus L (Φ : X N → ℝ) / sqNormN N L (Φ : X N → ℝ) := by
    rw [hc2, div_eq_mul_inv, mul_comm]
  rw [hdiv] at hres
  exact hres

theorem dlSlideNorm_iff_dlSlideCov {v : ℝ³ → ℝ} {h : ScatSol v} {b K_B R' J ε₀ : ℝ} :
    DLSlideNorm v h b K_B R' J ε₀ ↔ DLSlideCov v h b K_B R' J ε₀ :=
  ⟨dlSlideCov_of_dlSlideNorm, dlSlideNorm_of_dlSlideCov⟩

/-! ## 4. The Bogoliubov window of the delivered `BogoliubovLow` is vacuous -/

/-- **`SpectralInput` from the delivered `BogoliubovLow`**: for a low state,
scale it *down* (`c → 0`) so that the window hypothesis
`cnPlus(c•Φ) = c²·cnPlus Φ ≤ W N L` holds; the conclusion `Λ ≤ WordDens Φ` is
scale-invariant.  Hence the delivered window is vacuous. -/
theorem spectralInput_of_bogoliubovLow {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hW : ∀ N L, 0 < W N L)
    (hB : BogoliubovLow v h J W ε₀ η₀) : SpectralInput v h J ε₀ η₀ := by
  rcases hB with ⟨C, hC, hlow⟩
  refine ⟨C, hC, ?_⟩
  intro L hL N hN Φ hΦ
  have hcn0 : 0 ≤ cnPlus L (Φ : X N → ℝ) := Work.SmallBoxSliding.cnPlus_nonneg L
  have hdenpos : 0 < cnPlus L (Φ : X N → ℝ) + 1 := by linarith
  let c : ℝ := Real.sqrt (W N L / (4 * (cnPlus L (Φ : X N → ℝ) + 1)))
  have hcpos : 0 < c := by
    refine Real.sqrt_pos.mpr ?_
    exact div_pos (hW N L) (by linarith)
  have hcle : c ^ 2 * cnPlus L (Φ : X N → ℝ) ≤ W N L := by
    have hcsq : c ^ 2 = W N L / (4 * (cnPlus L (Φ : X N → ℝ) + 1)) := by
      simp only [c]
      exact Real.sq_sqrt (le_of_lt (div_pos (hW N L) (by linarith)))
    rw [hcsq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [hcn0, hW N L]
  have hwin : cnPlus L ((scaledBox Φ hcpos.ne') : X N → ℝ) ≤ W N L := by
    rw [scaledBox_coe, cnPlus_smul]
    exact hcle
  have hlow' : WordDens N L (dens N L) v h ((scaledBox Φ hcpos.ne') : X N → ℝ)
      ≤ Theta (a v) J (dens N L) := by
    rw [scaledBox_coe, wordDens_smul Φ.contDiff hcpos.ne']
    exact hΦ
  have hres := hlow L hL N hN (scaledBox Φ hcpos.ne') hwin hlow'
  rw [scaledBox_coe, wordDens_smul Φ.contDiff hcpos.ne'] at hres
  exact hres

/-- The converse: `SpectralInput` drops the window. -/
theorem bogoliubovLow_of_spectralInput {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hS : SpectralInput v h J ε₀ η₀) :
    BogoliubovLow v h J W ε₀ η₀ := by
  rcases hS with ⟨C, hC, hlow⟩
  exact ⟨C, hC, fun L hL N hN Φ _ hΦ => hlow L hL N hN Φ hΦ⟩

/-- **The delivered `BogoliubovLow` is `SpectralInput`**: its window
`cnPlus ≤ W N L` is vacuous in the delivered (unnormalised) setting. -/
theorem spectralInput_iff_bogoliubovLow {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hW : ∀ N L, 0 < W N L) :
    SpectralInput v h J ε₀ η₀ ↔ BogoliubovLow v h J W ε₀ η₀ :=
  ⟨bogoliubovLow_of_spectralInput, spectralInput_of_bogoliubovLow hW⟩

end Work.UBBInputs
