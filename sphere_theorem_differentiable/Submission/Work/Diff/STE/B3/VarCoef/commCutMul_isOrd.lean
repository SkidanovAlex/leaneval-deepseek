import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The commutator `[S_ε, M_m]` of the Friedrichs cutoff with a multiplication is of order `-1`

This file proves `Work.Diff.STE.B3.VarCoef.commCutMul_isOrd`: for a smooth `1`-periodic `m` and a
profile `ρ` with `‖ρ‖ ≤ 1`, `ρ = 0` off the ball `∑ yᵢ² ≤ 2` and Lipschitz constant `L`, the
commutator `[S_ε, M_m] = [cutOp ρ ε, mulOp m]` **gains** one derivative,

`CSqZ (t + 1) (fourierCoeff ([S_ε, M_m] f)) ≤ C t · CSqZ t (fourierCoeff f)`,

with a constant `C` independent of the cutoff parameter `ε ∈ (0,1]`.

The mathematics is entirely contained in
`Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_CSqZ`, which states exactly this estimate for
the function `β · S_ε h - S_ε (β · h)` with `β` smooth `1`-periodic.  The commutator here is the
*negative* of that expression, with `β = m` (viewed as a complex-valued function) and `h = f`; the
negative sign is absorbed with `CSqZ_neg`.  What is added in this file is (a) the two structural
facts needed by the `IsOrd` certificate — preservation of smooth `1`-periodic functions and
`ℂ`-linearity — for `mulOp m`, `cutOp ρ ε` and hence for their commutator, and (b) the translation
of the estimate through the definitions (`cutOp`, `mulOp`, `commOp`).

The elementary `L¹`/`ℓ²` bookkeeping for `flatCut` (additivity and `ℂ`-homogeneity) is proved from
the definition `flatCut ρ ε g = seriesFun (trunc ρ ε (fourierCoeff g))`, using the additivity of
`fourierCoeff` on continuous functions and the definition of `seriesFun` as a `tsum` of absolutely
summable terms.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary summability for `seriesFun` -/

/-- The terms `a k · exp (2πi k·x)` of `seriesFun a` are summable as soon as `a ∈ ℓ¹`. -/
private lemma commCutMul_summable_mul_fourierExp {a : (ι → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (x : ι → ℝ) : Summable fun k : ι → ℤ => a k * Work.Diff.STE.fourierExp k x :=
  Summable.of_norm_bounded ha (fun k => by rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])

/-- `seriesFun` is additive on `ℓ¹` coefficient families. -/
private lemma commCutMul_seriesFun_add {a b : (ι → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Work.Diff.STE.seriesFun (fun k => a k + b k)
      = Work.Diff.STE.seriesFun a + Work.Diff.STE.seriesFun b := by
  funext x
  show ∑' k : ι → ℤ, (a k + b k) * Work.Diff.STE.fourierExp k x
      = ∑' k : ι → ℤ, a k * Work.Diff.STE.fourierExp k x
        + ∑' k : ι → ℤ, b k * Work.Diff.STE.fourierExp k x
  rw [← Summable.tsum_add (commCutMul_summable_mul_fourierExp ha x)
    (commCutMul_summable_mul_fourierExp hb x)]
  exact tsum_congr fun k => add_mul _ _ _

/-- `seriesFun` is `ℂ`-homogeneous on `ℓ¹` coefficient families. -/
private lemma commCutMul_seriesFun_smul {a : (ι → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (c : ℂ) : Work.Diff.STE.seriesFun (fun k => c * a k) = c • Work.Diff.STE.seriesFun a := by
  funext x
  show ∑' k : ι → ℤ, (c * a k) * Work.Diff.STE.fourierExp k x
      = c * ∑' k : ι → ℤ, a k * Work.Diff.STE.fourierExp k x
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-! ## `S_ε = flatCut ρ ε` is additive and `ℂ`-homogeneous -/

/-- The truncated Fourier family of a smooth `1`-periodic function is `ℓ¹`. -/
private lemma commCutMul_summable_trunc (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    Summable fun k : ι → ℤ => ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f) k‖ :=
  Work.Diff.STE.B3.SymCalcStep1.summable_trunc_one ρ hρb ε
    (by simpa using Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff 0 f hf.1 hf.2)

/-- `S_ε` is additive on smooth `1`-periodic functions. -/
private lemma commCutMul_flatCut_add (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) {f g : (ι → ℝ) → ℂ} (hf : SmoothPer f) (hg : SmoothPer g) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (f + g)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε f + Work.Diff.STE.B3.SymCalc.flatCut ρ ε g := by
  have hf1 := commCutMul_summable_trunc ρ hρb ε hf
  have hg1 := commCutMul_summable_trunc ρ hρb ε hg
  have hcoeff : Work.Diff.STE.fourierCoeff (f + g)
      = fun k : ι → ℤ => Work.Diff.STE.fourierCoeff f k + Work.Diff.STE.fourierCoeff g k :=
    fourierCoeff_add_of_continuous hf.continuous hg.continuous
  have htr : Work.Diff.STE.trunc ρ ε
        (fun k : ι → ℤ => Work.Diff.STE.fourierCoeff f k + Work.Diff.STE.fourierCoeff g k)
      = fun k : ι → ℤ => Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f) k
          + Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff g) k := by
    funext k
    simp only [Work.Diff.STE.trunc]
    ring
  show Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (f + g)))
      = Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f))
        + Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff g))
  rw [hcoeff, htr]
  exact commCutMul_seriesFun_add hf1 hg1

/-- `S_ε` is `ℂ`-homogeneous on smooth `1`-periodic functions. -/
private lemma commCutMul_flatCut_smul (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (c : ℂ) {f : (ι → ℝ) → ℂ} (hf : SmoothPer f) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (c • f)
      = c • Work.Diff.STE.B3.SymCalc.flatCut ρ ε f := by
  have hf1 := commCutMul_summable_trunc ρ hρb ε hf
  have hcf : Work.Diff.STE.fourierCoeff (c • f)
      = fun k : ι → ℤ => c * Work.Diff.STE.fourierCoeff f k :=
    fourierCoeff_const_mul_of_continuous c hf.continuous
  have htr : Work.Diff.STE.trunc ρ ε (fun k : ι → ℤ => c * Work.Diff.STE.fourierCoeff f k)
      = fun k : ι → ℤ => c * Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f) k := by
    funext k
    simp only [Work.Diff.STE.trunc]
    ring
  show Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (c • f)))
      = c • Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff f))
  rw [hcf, htr]
  exact commCutMul_seriesFun_smul hf1 c

/-! ## Structure of `mulOp` and `cutOp` -/

/-- A multiplication operator preserves smooth `1`-periodic functions. -/
private lemma commCutMul_pres_mulOp (m : (ι → ℝ) → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) : Preserves (mulOp m) := fun f hf =>
  ⟨(Complex.ofRealCLM.contDiff.comp hm).mul hf.1, fun i x => by
    simp only [mulOp, hf.2 i x, hmp i x]⟩

/-- A multiplication operator is `ℂ`-linear on smooth `1`-periodic functions. -/
private lemma commCutMul_linSP_mulOp (m : (ι → ℝ) → ℝ) : LinSP (mulOp m) where
  add f g _ _ := by funext x; simp only [mulOp, Pi.add_apply, mul_add]
  smul c f _ := by funext x; simp only [mulOp, Pi.smul_apply, smul_eq_mul]; ring

/-- The Friedrichs cutoff preserves smooth `1`-periodic functions. -/
private lemma commCutMul_pres_cutOp (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) : Preserves (cutOp ρ ε) := fun f hf =>
  ⟨Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hf.1 hf.2,
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε f⟩

/-- The Friedrichs cutoff is `ℂ`-linear on smooth `1`-periodic functions. -/
private lemma commCutMul_linSP_cutOp (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) : LinSP (cutOp ρ ε) where
  add f g hf hg := commCutMul_flatCut_add ρ hρ ε hf hg
  smul c f hf := commCutMul_flatCut_smul ρ hρ ε c hf

theorem commCutMul_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ)
    (m : (ι → ℝ) → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hmp : Work.Diff.STE.Periodic1 m)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) (hρ1 : ρ 0 = 1) :
    ∃ C : ℤ → ℝ, (∀ t : ℤ, 0 ≤ C t) ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Work.Diff.STE.B3.VarCoef.IsOrd (-1) C
        (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
          (Work.Diff.STE.B3.VarCoef.mulOp m)) := by
  classical
  -- ## The one-derivative gain on the Fourier side
  have hgain : ∀ s : ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ h : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
        Work.Diff.STE.B3.SymCalcStep8.CSqZ s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
            ((m x : ℝ) : ℂ) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                  (fun y : ι → ℝ => ((m y : ℝ) : ℂ) * h y) x))
          ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (s - 1) (Work.Diff.STE.fourierCoeff h) :=
    fun s => Work.Diff.STE.B3.SymCalcStep8.flat_multiplier_gain_CSqZ ρ hρ hρ0 L hL hρlip
      (fun x : ι → ℝ => ((m x : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp hm)
      (fun i x => by simp only [hmp i x]) s
  choose C0 hC0 using hgain
  refine ⟨fun t => C0 (t + 1), fun t => (hC0 (t + 1)).1, ?_⟩
  intro ε hε hε1
  -- ## The structural fields of the certificate
  have hpres_m : Preserves (mulOp m) := commCutMul_pres_mulOp m hm hmp
  have hlin_m : LinSP (mulOp m) := commCutMul_linSP_mulOp m
  have hpres_c : Preserves (cutOp ρ ε) := commCutMul_pres_cutOp ρ hρ ε
  have hlin_c : LinSP (cutOp ρ ε) := commCutMul_linSP_cutOp ρ hρ ε
  have hpres : Preserves (commOp (cutOp ρ ε) (mulOp m)) := by
    intro f hf
    exact SmoothPer.sub (hpres_c (mulOp m f) (hpres_m f hf))
      (hpres_m (cutOp ρ ε f) (hpres_c f hf))
  have hlin : LinSP (commOp (cutOp ρ ε) (mulOp m)) :=
    linSP_sub (linSP_comp hlin_c hlin_m hpres_m) (linSP_comp hlin_m hlin_c hpres_c)
  refine ⟨hpres, hlin, fun t => (hC0 (t + 1)).1, ?_⟩
  -- ## The estimate
  intro t f hf
  have hSm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => ((m x : ℝ) : ℂ) * f x) :=
    (Complex.ofRealCLM.contDiff.comp hm).mul hf.1
  have hSp : Work.Diff.STE.Periodic1 (fun x : ι → ℝ => ((m x : ℝ) : ℂ) * f x) :=
    fun i x => by simp only [hmp i x, hf.2 i x]
  have hG_cont : Continuous (fun x : ι → ℝ =>
      ((m x : ℝ) : ℂ) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε f x
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => ((m y : ℝ) : ℂ) * f y) x) :=
    (((Complex.ofRealCLM.contDiff.comp hm).continuous).mul
        (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hf.1 hf.2).continuous).sub
      (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hSm hSp).continuous
  have hkey := (hC0 (t + 1)).2 ε hε hε1 f hf.1 hf.2
  have hmf : mulOp m f = fun y : ι → ℝ => ((m y : ℝ) : ℂ) * f y := rfl
  have hneg : commOp (cutOp ρ ε) (mulOp m) f
      = fun x : ι → ℝ => -(((m x : ℝ) : ℂ) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε f x
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y : ι → ℝ => ((m y : ℝ) : ℂ) * f y) x) := by
    funext x
    simp only [commOp_apply, cutOp, mulOp, Pi.sub_apply]
    rw [hmf]
    ring
  rw [hneg, fourierCoeff_neg_of_continuous hG_cont, CSqZ_neg]
  have h1 : t - (-1) = t + 1 := by ring
  have h2 : (t + 1) - 1 = t := by ring
  rw [h1]
  rw [h2] at hkey
  exact hkey

end Work.Diff.STE.B3.VarCoef
