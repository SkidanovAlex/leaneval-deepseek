import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.Defs
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Work.KMTAreas.A7.cw_varphiNt_summable
import Submission.Work.KMTAreas.A7.SmallExcBound
import Submission.Work.KMTPlan.A6.kmtProj_l2_bound_finset
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.LowModApproxBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-!
# The `f`-side bounded-height packet estimate

This file proves `Work.KMTPlan.A6.PieceBoundedH.SliceFBound r C₀ ρ B` for *arbitrary* `ρ > 0`
(the statement is the `(2,2,1)`-instance of the paper's linear lacunary variational estimate
`(lin-1)` at bounded arithmetic height, with the loss absorbed into a constant depending on
`ρ, B`).  The file is self-contained: the lift/reduction lemmas of
`LowModApproxBoundedH/mdlPartVar.lean` are reproduced here (with `_aux` names) so that the module
does not depend on the build state of `mdlPartVar`.

The route:

* the multiplicative lift `Tle_eq_sum_modulation_aux` writes the height-`≤ l₁` IW multiplier as a
  finite sum over `α ∈ (ℚ/ℤ)_{≤l₁}` of *height-`0`* multipliers applied to the modulated inputs
  `y ↦ e(yα) F y`; `variationalNorm_Tle_le_sum_aux` turns this into the pointwise bound of the
  variational norms;
* the height-`0` operators are `ρ`-free (`Tle ρ 0 φ = Tle 1 0 φ`, since `iwArithFreqs ρ 0 = {0}`),
  so the level-`0` input `lev0CoreClip` (proved by a colleague, from `A7.LoLinVar` by the
  tail-clipping of `core`) applies for arbitrary `ρ`;
* the modulated input has the same `ℓ²`-norm as `F` (unit modulus), and
  `‖F‖₂ ≤ C(ρ,B)‖f‖₂` by `kmtProj_l2_bound_finset` on the finite set of heights `l ≤ B`;
* the case `eLpNorm f 2 = ⊤` is trivial because the constant is `≥ 1`, and in the remaining case
  `F` is pointwise bounded (`bounded_of_eLpNorm_count_lt_top`), which is exactly what the lift
  needs.
-/

/-! ## 1. The lift: `Tle` at height `l` as a finite sum of modulated height-`0` operators

(Copied from `Submission/Work/KMTPlan/A6/LowModApproxBoundedH/mdlPartVar.lean`.) -/

/-- The character identity behind the lift:
`conj (fourier x α) * fourier (x - j) α = conj (fourier j α)`. -/
theorem fourier_conj_mul_sub_aux (α : Circ) (x j : ℤ) :
    (starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α
      = (starRingEnd ℂ) (fourier (T := 1) j α) := by
  rw [← fourier_neg (T := 1) (n := x) (x := α), ← fourier_neg (T := 1) (n := j) (x := α)]
  rw [← fourier_add (T := 1) (m := -x) (n := x - j) (x := α)]
  ring_nf

/-- The height-`0` kernel is `cw φ`. -/
theorem TleKer_zero_eq_cw_aux (ρ : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ 0 hφ j]
  have h1 : Work.KMTPlan.A6.TleArChar ρ 0 j = 1 := by
    rw [Work.KMTPlan.A6.TleArChar]
    have h0 : Work.Analysis.IonescuWainger.iwArithFreqs ρ 0
        = ({(0 : Circ)} : Finset Circ) := Work.KMTAreas.A7.iwArithFreqs_zero ρ
    rw [h0, Finset.sum_singleton]
    simp
  rw [h1, one_mul]

/-- The height-`l` kernel is the character-weighted height-`0` kernel. -/
theorem TleKer_eq_char_mul_cw_aux (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
            (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ l hφ j, Work.KMTPlan.A6.TleArChar]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  exact fourier_neg (n := j) (x := α)

/-- **The lift.**  For an integrable symbol `φ`, the cumulative Ionescu–Wainger multiplier at
arithmetic height `≤ l` is the finite sum over the arithmetic frequencies
`α ∈ (ℚ/ℤ)_{≤ l}` of the modulation `M_{-α}` of the *height-`0`* operator applied to `M_α f`. -/
theorem Tle_eq_sum_modulation_aux (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (f : ℤ → ℂ)
    (Cf : ℝ) (hbdd : ∀ y : ℤ, ‖f y‖ ≤ Cf)
    (hcw : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖) (x : ℤ) :
    Work.KMTAreas.A7.Tle ρ l φ f x
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          (starRingEnd ℂ) (fourier (T := 1) x α)
            * Work.KMTAreas.A7.Tle ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y) x := by
  classical
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  have hK0 : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_zero_eq_cw_aux ρ hφ j
  have hKl : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_eq_char_mul_cw_aux ρ l hφ j
  -- the individual summands are summable
  have hsumm : ∀ α : Circ,
      Summable fun j : ℤ => (starRingEnd ℂ) (fourier (T := 1) j α)
        * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    intro α
    refine Summable.of_norm_bounded (hcw.mul_right Cf) fun j => ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖(starRingEnd ℂ) (fourier (T := 1) j α)‖ = 1 := by
      rw [RCLike.norm_conj, fourier_apply]
      exact Circle.norm_coe _
    rw [h1, one_mul]
    exact mul_le_mul_of_nonneg_left (hbdd (x - j)) (norm_nonneg _)
  -- left-hand side as a sum over the arithmetic frequencies
  have hL : Work.KMTAreas.A7.Tle ρ l φ f x
      = ∑ α ∈ A, ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    rw [Work.KMTPlan.A6.Tle_eq_convOp_TleKer ρ l φ f]
    show (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j * f (x - j)) = _
    have hstep : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j * f (x - j)
        = ∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)
            * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
      intro j
      rw [hKl j, mul_assoc, Finset.sum_mul]
    rw [tsum_congr hstep]
    exact Summable.tsum_finsetSum (s := A) fun α _ => hsumm α
  -- each arithmetic frequency gives the modulated height-`0` operator
  have hR : ∀ α : Circ, (starRingEnd ℂ) (fourier (T := 1) x α)
        * Work.KMTAreas.A7.Tle ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y) x
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    intro α
    rw [Work.KMTPlan.A6.Tle_eq_convOp_TleKer ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y)]
    show (starRingEnd ℂ) (fourier (T := 1) x α)
        * (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j
            * (fourier (T := 1) (x - j) α * f (x - j)))
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j))
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j
              * (fourier (T := 1) (x - j) α * f (x - j)))
        = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) x α)
              * (Work.KMTPlan.A6.TleKer ρ 0 φ j
                  * (fourier (T := 1) (x - j) α * f (x - j))) from
        (tsum_mul_left).symm]
    refine tsum_congr fun j => ?_
    rw [hK0 j]
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (Work.KMTAreas.A7.cw φ j * (fourier (T := 1) (x - j) α * f (x - j)))
        = ((starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α)
            * (Work.KMTAreas.A7.cw φ j * f (x - j)) from by ring]
    rw [fourier_conj_mul_sub_aux α x j]
  rw [hL]
  exact Finset.sum_congr rfl fun α _ => (hR α).symm

/-- Scaling a sequence family by a *unit modulus* scalar does not increase its variational norm. -/
theorem variationalNorm_unit_mul_le_aux (r : NNReal) (hr : 1 ≤ r) (c : ℂ) (hc : ‖c‖ = 1)
    (w : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => c * w n)
      ≤ PointwiseErgodicTheorems.variationalNorm r w := by
  have hfam : (fun n : ℕ => c * w n) = c • w := rfl
  rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr c w]
  have h1 : ‖c‖ₑ = 1 := by rw [← ofReal_norm, hc, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- **The level-`l` variational bound from the level-`0` one.**  For a family of integrable symbols
`ψ` with summable `cw`-coefficients and a bounded input `F`, the `r`-variation of the clipped
level-`l` family is dominated by the sum, over the arithmetic frequencies `α` of height `≤ l`, of
the `r`-variations of the (clipped) *level-`0`* families applied to the modulated inputs
`y ↦ fourier y α · F y`. -/
theorem variationalNorm_Tle_le_sum_aux (ρ : ℝ) (l : ℕ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ n, Integrable (ψ n))
    (hcw : ∀ n, Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (ψ n) j‖)
    (F : ℤ → ℂ) (Cf : ℝ) (hbdd : ∀ y : ℤ, ‖F y‖ ≤ Cf)
    (c : ℕ → Prop) [DecidablePred c] (r : NNReal) (hr : 1 ≤ r) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if c n then
              Work.KMTAreas.A7.Tle ρ 0 (ψ n) (fun y : ℤ => fourier (T := 1) y α * F y) x
              else 0) := by
  classical
  set A := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  have hfun : (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0)
      = fun n : ℕ => ∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) x α)
          * (if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
              (fun y : ℤ => fourier (T := 1) y α * F y) x else 0) := by
    funext n
    by_cases h : c n
    · rw [if_pos h, Tle_eq_sum_modulation_aux ρ l (hψ n) F Cf hbdd (hcw n) x]
      exact Finset.sum_congr rfl fun α _ => by rw [if_pos h]
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun α _ => by rw [if_neg h, mul_zero]).symm
  rw [hfun]
  refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr A (fun α n =>
    (starRingEnd ℂ) (fourier (T := 1) x α)
      * (if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
          (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  refine variationalNorm_unit_mul_le_aux r hr _ ?_ _
  rw [RCLike.norm_conj, fourier_apply]
  exact Circle.norm_coe _

/-! ## 2. Elementary eLpNorm lemmas -/

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
theorem enorm_eq_ofReal_norm_aux (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- The characters have unit modulus. -/
theorem norm_fourier_one_aux (y : ℤ) (α : Circ) : ‖fourier (T := 1) y α‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- Modulating by a character does not change the `ℓᵖ`-norm. -/
theorem eLpNorm_fourier_mul_aux (α : Circ) (F : ℤ → ℂ) (p : ENNReal) :
    MeasureTheory.eLpNorm (fun y : ℤ => fourier (T := 1) y α * F y) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
  have h1 : ∀ y : ℤ, ‖fourier (T := 1) y α‖ₑ = 1 := fun y => by
    rw [enorm_eq_ofReal_norm_aux, norm_fourier_one_aux, ENNReal.ofReal_one]
  refine le_antisymm ?_ ?_
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]

/-- `eLpNorm` of a finite sum of `ℝ≥0∞`-valued functions. -/
theorem eLpNorm_finset_sum_le_aux {ι : Type*} (s : Finset ι) (G : ι → ℤ → ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ s, G i x) 2 MeasureTheory.Measure.count
      ≤ ∑ i ∈ s, MeasureTheory.eLpNorm (G i) 2 MeasureTheory.Measure.count := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : (fun x : ℤ => ∑ i ∈ insert a s, G i x)
        = (G a) + (fun x : ℤ => ∑ i ∈ s, G i x) := by
      funext x
      rw [Finset.sum_insert ha]
      rfl
    rw [h1]
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal (by norm_num) (by norm_num)).trans ?_
    rw [Finset.sum_insert ha]
    exact add_le_add le_rfl ih

/-! ## 3. The `ℓ²`-bound on the fixed input `F = mdlF ρ u l₁ f` -/

/-- **A finite rectangle of IW projections at bounded arithmetic height is uniformly bounded on
`ℓ²`.**  This unwraps the definition of `piExact` (a difference of two `kmtProj` at heights `l` and
`l - 1`) and applies the proved finset bound `Work.KMTPlan.A6.kmtProj_l2_bound_finset`. -/
theorem piExact_l2_bound_range_aux (ρ : ℝ) (B : ℕ) (Kl : ℤ) :
    ∃ C : NNReal, 0 < C ∧ ∀ (l : ℕ) (k : ℤ), l ≤ B → Kl ≤ k → k ≤ 0 → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f)
          2 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.KMTPlan.A6.kmtProj_l2_bound_finset ρ
    ((Finset.range (B + 1)).product (Finset.Icc Kl 0))
  refine ⟨2 * C₀ + 1, by positivity, ?_⟩
  intro l k hl hk1 hk2 f
  have hkI : k ∈ Finset.Icc Kl 0 := Finset.mem_Icc.mpr ⟨hk1, hk2⟩
  have hlI : l ∈ Finset.range (B + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hl'I : l - 1 ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  have hmem1 : (l, k) ∈ (Finset.range (B + 1)).product (Finset.Icc Kl 0) :=
    Finset.mem_product.mpr ⟨hlI, hkI⟩
  have hmem2 : (l - 1, k) ∈ (Finset.range (B + 1)).product (Finset.Icc Kl 0) :=
    Finset.mem_product.mpr ⟨hl'I, hkI⟩
  have hb1 := hC₀ (l, k) hmem1 f
  have hb2 := hC₀ (l - 1, k) hmem2 f
  have hAEm : MeasureTheory.AEStronglyMeasurable (Work.KMTContract.kmtProj ρ l k f)
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hAEm' : MeasureTheory.AEStronglyMeasurable (Work.KMTContract.kmtProj ρ (l - 1) k f)
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hsub : MeasureTheory.eLpNorm
        (Work.KMTContract.kmtProj ρ l k f - Work.KMTContract.kmtProj ρ (l - 1) k f)
        2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) 2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ (l - 1) k f) 2
            MeasureTheory.Measure.count := by
    have h := MeasureTheory.eLpNorm_add_le (p := (2 : ENNReal)) (μ := MeasureTheory.Measure.count)
      (f := Work.KMTContract.kmtProj ρ l k f)
      (g := -Work.KMTContract.kmtProj ρ (l - 1) k f) (by norm_num)
    rw [MeasureTheory.eLpNorm_neg] at h
    exact h
  have hstep : MeasureTheory.eLpNorm
        (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f)
        2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) 2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ (l - 1) k f) 2
            MeasureTheory.Measure.count := by
    rw [Work.Analysis.EndVar.piExact]
    by_cases hl0 : l = 0
    · rw [hl0, if_pos rfl, Work.KMTContract.kmtPj_proj]
      exact le_add_of_nonneg_right (by positivity : (0 : ENNReal) ≤ _)
    · rw [if_neg hl0, Work.KMTContract.kmtPj_proj, Work.KMTContract.kmtPj_proj]
      exact hsub
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) 2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ (l - 1) k f) 2
            MeasureTheory.Measure.count
      ≤ (C₀ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
        + (C₀ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        add_le_add hb1 hb2
    _ = ((C₀ + C₀ : NNReal) : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.coe_add]
    _ ≤ ((2 * C₀ + 1 : NNReal) : ENNReal) * MeasureTheory.eLpNorm f 2
          MeasureTheory.Measure.count := by
        refine mul_le_mul_left (ENNReal.coe_le_coe.mpr ?_) _
        rw [two_mul]
        exact le_add_right le_rfl

/-! ## 3b. The level-`0` clipped estimate (at the clip `core ρ C₀ l₁ l₂ k₁ k₂`) -/

/-- A `Λ`-lacunary sequence with all terms `≥ 1` is monotone. -/
theorem monotone_of_lacunary_aux {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- At arithmetic height `0` the Ionescu--Wainger operator `Tle ρ 0` does not depend on `ρ`. -/
theorem Tle_zero_rho_indep_aux (ρ ρ' : ℝ) {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Work.KMTAreas.A7.Tle ρ 0 φ f = Work.KMTAreas.A7.Tle ρ' 0 φ f := by
  unfold Work.KMTAreas.A7.Tle
  rw [Work.KMTAreas.A7.iwArithFreqs_zero, Work.KMTAreas.A7.iwArithFreqs_zero]

/-- The level-`0` clipped lacunary variational estimate at `p = 2` for a fixed lacunarity
constant `Λ > 1`, with the clip `core ρ C₀ l₁ l₂ k₁ k₂`.  The proof applies `LoLinVar` at
`ρ = 1` (transported to the given `ρ` along `Tle ρ 0 = Tle 1 0`) to the lacunary tail
`n ↦ a (n + m)` of the scale family, where `m` is the first index of the `core` set: the `core`
set is a tail, and the main-regime condition guarantees the guard `2^{k₁} ≤ ⌊a n⌋` on it, so the
clipping costs only the factor `2` of `variationalNorm_clip_le`.  The clip's parameters `l₁, l₂`
enter only through the tail start, so the constant is uniform in them. -/
theorem lev0CoreClipAuxFixed (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        k₁ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (C : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
  obtain ⟨Cl, hCl⟩ := Work.KMTAreas.A7.LoLinVar 1 one_pos le_rfl (2 : ENNReal)
    ENNReal.one_lt_two (ENNReal.ofNat_lt_top (n := 2)) r hr Λ hΛ
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2, ?_⟩
  intro a l₁ l₂ k₁ k₂ t F ha ha1 hk ht
  have hamono : Monotone a := monotone_of_lacunary_aux hΛ ha ha1
  by_cases hex : ∃ n, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ↔ m ≤ n := by
      refine ⟨Nat.find hex, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hex hcon h
      · exact Work.KMTAreas.A7.core_mono hamono h (Nat.find_spec hex)
    have hclipx : ∀ x : ℤ,
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x) := by
      intro x
      have hfun : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)
          = (fun n : ℕ => if m ≤ n then Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x else 0) := by
        funext n
        by_cases h : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
        · rw [if_pos h, if_pos ((hm n).mp h)]
        · rw [if_neg h, if_neg (fun hc => h ((hm n).mpr hc))]
      rw [hfun]
      refine (Work.KMTAreas.A7.variationalNorm_clip_le r hr1
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x) m).trans (le_of_eq ?_)
      exact (two_mul _).symm
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)) 2 MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]
          exact hclipx x)) 2
    have hshift : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count
        ≤ (Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
      have hfun2 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle 1 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x)) := by
        funext x
        have hfam : (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x)
            = (fun j : ℕ => Work.KMTAreas.A7.Tle 1 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x) := by
          funext j
          rw [Tle_zero_rho_indep_aux ρ 1]
        rw [hfam]
      rw [hfun2]
      refine hCl (fun j : ℕ => a (j + m)) ?_ (fun j => ha1 (j + m)) k₁ ?_ t ht F
      · intro j
        have h := ha (j + m)
        have hidx : j + 1 + m = (j + m) + 1 := by omega
        show Λ < a (j + 1 + m) / a (j + m)
        rw [hidx]; exact h
      · intro j
        exact Work.KMTAreas.A7.two_pow_le_floor_of_core
          ((hm (j + m)).mpr (Nat.le_add_left m j))
    have h2coe : ((2 : NNReal) : ENNReal) = (2 : ENNReal) := rfl
    have hcoef : (2 : ENNReal) * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))
        ≤ (((2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2 : NNReal)) : ENNReal) := by
      have hcast : (1 + (k₁ : ℝ)) = ((1 + k₁ : ℕ) : ℝ) := by push_cast; ring
      have hof : ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) = ↑(((1 + k₁ : ℕ) : NNReal) ^ 2) := by
        rw [hcast, ENNReal.ofReal_pow (Nat.cast_nonneg (1 + k₁)), ENNReal.ofReal_natCast]
        rfl
      have hm2 : (((1 + k₁ : ℕ) : NNReal) ^ 2) ≤ (((1 + B : ℕ) : NNReal) ^ 2) := by
        have hle : ((1 + k₁ : ℕ) : NNReal) ≤ ((1 + B : ℕ) : NNReal) :=
          by exact_mod_cast Nat.add_le_add_left hk 1
        rw [sq, sq]; exact mul_le_mul' hle hle
      have hmid : (Cl : ENNReal) * ↑(((1 + k₁ : ℕ) : NNReal) ^ 2)
          ≤ (Cl : ENNReal) * ↑(((1 + B : ℕ) : NNReal) ^ 2) :=
        mul_le_mul' le_rfl (ENNReal.coe_le_coe.mpr hm2)
      have hmain : (2 : ENNReal) * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))
          ≤ (2 : ENNReal) * ((Cl : ENNReal) * ↑(((1 + B : ℕ) : NNReal) ^ 2)) := by
        rw [hof]
        exact mul_le_mul' le_rfl hmid
      refine hmain.trans (le_of_eq ?_)
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow, h2coe]
      ring
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0)) 2 MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count := hstep
      _ ≤ 2 * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count) :=
            mul_le_mul' le_rfl hshift
      _ ≤ (((2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2 : NNReal)) : ENNReal) *
              MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
            rw [← mul_assoc]
            exact mul_le_mul' hcoef le_rfl
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
      funext x
      have hfam : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0) = (fun _ : ℕ => (0 : ℂ)) := by
        funext n
        rw [if_neg (fun hc => hex ⟨n, hc⟩)]
      rw [hfam]
    rw [hzero, Work.KMTAreas.A7.eLpNorm_variationalNorm_zero hr1 2]
    exact zero_le

/-- **The level-`0` clipped estimate with the clip `core ρ C₀ l₁ l₂ k₁ k₂`, uniformly in `Λ`.** -/
theorem lev0CoreClip_aux (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ)
    (hρ : 0 < ρ) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨fun Λ => if h : 1 < Λ then
    Classical.choose (lev0CoreClipAuxFixed r hr C₀ hC₀ ρ hρ B Λ h) else 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t F hΛ ha ha1 hL ht
  dsimp only
  rw [dif_pos hΛ]
  have hk₁ : k₁ ≤ B := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hL
  exact Classical.choose_spec (lev0CoreClipAuxFixed r hr C₀ hC₀ ρ hρ B Λ hΛ)
    a l₁ l₂ k₁ k₂ t F ha ha1 hk₁ ht

/-! ## 4. The assembly -/

/-- **The bounded-height packet estimate from the level-`0` clipped estimate.** -/
theorem sliceFBound_of_lev0 (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ)
    (hρ : 0 < ρ) (B : ℕ)
    (hlev : ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0))
          2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count) :
    Work.KMTPlan.A6.PieceBoundedH.SliceFBound r C₀ ρ B := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨Cp, hCppos, hCp⟩ :=
    piExact_l2_bound_range_aux ρ B (-((Work.KMTAreas.A7.uScale ρ B : ℕ) : ℤ))
  obtain ⟨Klev, hKlev⟩ := hlev
  set A0 : ℕ := (Finset.range (B + 1)).sup
    (fun l => (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card) with hA0
  refine ⟨fun Λ => max 1 (A0 * Klev Λ * Cp), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hB
  have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hB
  have hKpos : (max 1 (A0 * Klev Λ * Cp) : NNReal) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  by_cases htop : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.mpr hKpos)]
    exact le_top
  · have hflt : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    -- the fixed input `F` and its `ℓ²` bound
    set u : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hu
    set F : ℤ → ℂ := Work.KMTPlan.A6.mdlF ρ u l₁ f with hF
    have hFle : MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count
        ≤ (Cp : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
      have hmono : Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
          ≤ Work.KMTAreas.A7.uScale ρ B := Work.KMTAreas.A7.uScale_mono hρ.le hB
      have hk1 : (-((Work.KMTAreas.A7.uScale ρ B : ℕ) : ℤ))
          ≤ (-((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ)) := by
        exact neg_le_neg (by exact_mod_cast hmono)
      have hk2 : (-((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ))
          ≤ 0 := by simp
      have h := hCp l₁
        (-((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ))
        hl₁B hk1 hk2 f
      simpa [hF, hu, Work.KMTPlan.A6.mdlF] using h
    have hFlt : MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count < ⊤ := by
      refine lt_of_le_of_lt hFle ?_
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top hflt
    obtain ⟨Cf, hCf⟩ :=
      Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := (2 : ENNReal))
        (by norm_num) hFlt
    -- the clips agree
    have hclipeq : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂
        = Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a := by
      funext n
      exact propext (Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n)
    -- the level-`l₁` walk, lifted to level `0`
    have hlift : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTPlan.A6.PieceBoundedH.sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
        ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
                  (fun y : ℤ => fourier (T := 1) y α * F y) x else 0) := by
      intro x
      have hkey := variationalNorm_Tle_le_sum_aux ρ l₁
        (ψ := fun n => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
        (fun n => Work.KMTAreas.A7.integrable_varphiNt _ _ _)
        (fun n => Work.KMTAreas.A7.cw_varphiNt_summable _ _ _)
        F Cf hCf (fun n => Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) r hr1 x
      have hfun : (fun n : ℕ => Work.KMTPlan.A6.PieceBoundedH.sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
          = (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ l₁
                (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x else 0) := by
        funext n
        show (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
                (Work.KMTPlan.A6.mdlF ρ
                  (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ f)
            else 0) x
          = (if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)
        by_cases h : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n
        · rw [if_pos ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mpr h),
            if_pos h, hF, hu]
        · rw [if_neg (fun hh => h ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hh)),
            if_neg h]
          simp
      rw [hfun]
      exact hkey
    -- the `eLpNorm` bound of the sum
    have hsumbound : MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
                  (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))
        2 MeasureTheory.Measure.count
        ≤ ((A0 * Klev Λ * Cp : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
      refine (eLpNorm_finset_sum_le_aux (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
        (fun α x => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
              (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))).trans ?_
      have hterm : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
                (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))
            2 MeasureTheory.Measure.count
          ≤ ((Klev Λ * Cp : NNReal) : ENNReal)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        intro α _
        have h1 := hKlev a Λ l₁ l₂ k₁ k₂ t
          (fun y : ℤ => fourier (T := 1) y α * F y) hΛ ha ha1 hB ht
        have h2 := eLpNorm_fourier_mul_aux α F 2
        calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
                  (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))
              2 MeasureTheory.Measure.count
            ≤ (Klev Λ : ENNReal) * MeasureTheory.eLpNorm
                (fun y : ℤ => fourier (T := 1) y α * F y) 2 MeasureTheory.Measure.count := h1
          _ = (Klev Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
              rw [h2]
          _ ≤ (Klev Λ : ENNReal)
                * ((Cp : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :=
              mul_le_mul_right hFle _
          _ = ((Klev Λ * Cp : NNReal) : ENNReal)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              rw [ENNReal.coe_mul, mul_assoc]
      refine (Finset.sum_le_sum hterm).trans ?_
      have hcard' : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ENNReal)
          ≤ (A0 : ENNReal) := by
        have hmem : l₁ ∈ Finset.range (B + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le
            (le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hB))
        have := Finset.le_sup (s := Finset.range (B + 1))
          (f := fun l => (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card) hmem
        rw [← hA0] at this
        exact_mod_cast this
      rw [Finset.sum_const, nsmul_eq_mul]
      have hconst_eq : ((A0 : ENNReal) * ((Klev Λ * Cp : NNReal) : ENNReal))
          = ((A0 * Klev Λ * Cp : NNReal) : ENNReal) := by
        rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul]
        congr 1
        ring
      calc ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ENNReal)
            * (((Klev Λ * Cp : NNReal) : ENNReal)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
          = (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ENNReal)
              * ((Klev Λ * Cp : NNReal) : ENNReal))
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := (mul_assoc _ _ _).symm
        _ ≤ ((A0 : ENNReal) * ((Klev Λ * Cp : NNReal) : ENNReal))
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
            mul_le_mul_left (mul_le_mul_left hcard' _) _
        _ = ((A0 * Klev Λ * Cp : NNReal) : ENNReal)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
            rw [hconst_eq]
    -- the triangle inequality for the pointwise lift, then the constant absorption
    have hmain : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTPlan.A6.PieceBoundedH.sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x))
          2 MeasureTheory.Measure.count
        ≤ ((A0 * Klev Λ * Cp : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
      (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by rw [enorm_eq_self]; exact hlift x)).trans
        hsumbound
    exact hmain.trans
      (mul_le_mul_left (ENNReal.coe_le_coe.mpr (le_max_right _ _)) _)

/-- The `f`-side bounded-height packet estimate (the Prop `SliceFBound r C₀ ρ B` of
`Submission/Work/KMTPlan/A6/PieceBoundedH/Defs.lean`), for arbitrary `ρ > 0`.

Route (see also `Submission/Work/KMTPlan/A6/LowModApproxBoundedH/mdlPartVar.lean`): the packet is
`1_{mdlCore} · Tle ρ l₁ (varphiNt ⌊a n⌋ k₁ t) F` with `F = mdlF ρ (uScale ρ (lcL l₁ l₂ k₁ k₂)) l₁ f`;
use the lift `Tle_eq_sum_modulation`, `variationalNorm_Tle_le_sum` and
`variationalNorm_unit_mul_le` of that file to reduce it to the finite sum over
`α ∈ iwArithFreqs ρ l₁` of height-`0` clipped families applied to the modulated inputs
`y ↦ fourier y α · F y`; bound those by the level-`0` estimate `plainVarF_lev0` of the same
directory (or reproduce it from the proved `A7.LoFLinVarClipped` by the ρ-transfer along
`Tle ρ 0 = Tle 1 0` and the tail-clipping of `core`); bound `‖F‖₂ ≤ C(ρ,B)‖f‖₂` with the proved
`Work.KMTPlan.A6.kmtProj_l2_bound_finset` on the finite set of heights `l ≤ B`, and split off
`eLpNorm f 2 = 0` and `= ⊤`. -/
theorem sliceFBound (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (B : ℕ) : Work.KMTPlan.A6.PieceBoundedH.SliceFBound r C₀ ρ B :=
  sliceFBound_of_lev0 r hr C₀ hC₀ ρ hρ B (lev0CoreClip_aux r hr C₀ hC₀ ρ hρ B)

end

end Work.KMTPlan.A6.LowModApproxBoundedH
