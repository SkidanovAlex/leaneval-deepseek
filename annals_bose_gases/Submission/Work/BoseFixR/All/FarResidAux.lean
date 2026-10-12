import ChallengeDeps
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.All.FarBogPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarResidAux.lean` — the provable core of `FarResidAdm`

Design: `FINDING_FarResidAdm.md` §13.  The *route through `FarBogPair`* (the scalar
`zpSumOf` lower bound for `KzBogFS`) is a dead end: `zpSumOf (farEnv E v μ ρ) ρ` is an
`N`-free scalar whose `κ`-half alone exceeds `½ρ²ℓ³ω₀ + ErrRes/4` as soon as
`ρ/μ ≳ 10^{148}` (`FINDING_FarMassFix.md` §§2–4), and a window hypothesis cannot repair
a *scalar* statement.  What the window repairs is the **operator** estimate, and the
correct per-pair decomposition is

```
pairOpFar F E ρ k = pairQuad F E ρ k + (cCoefFar E ρ k) • pairLin F k
```

with the two pieces bounded *separately*:

* `pairQuad_ground` — the quadratic piece is `≥ −𝒵_k` per pair (Bogoliubov,
  `zpPairOp_ground` at the environment with `hatChi := 0`, where the `κ`-error vanishes);
* `abs_qw_pairLin_le` — the linear piece is Cauchy–Schwarz bounded by
  `2(√⟨n_k⟩ + √⟨n_{−k}⟩)√(‖f‖²)`;
* `linWord_le` — the summed linear piece is `≤ 8√(Σ_k𝒞_k²)√𝓜·‖f‖²` on the `𝓜`-window
  (`NWindow` + the view's Bessel conjunct `Σn_k ≤ Cn N`, `Cn ≤ 16`).

The two remaining inputs of `FarResidAdm` are then the **`𝒵`-half mass comparison**
(FS `eq:Rough2` + `eq:I2-integral`) and the **`Q₃` wedge** (FS `eq:Rough1`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The quadratic/linear split of the pair form -/

/-- The *quadratic* part of FS's pair form at the datum `(E, ρ)`: the diagonal
`𝒜_k = τ_k + ρŴ₁(k)` and the pairing `ℬ_k = ρŴ₁(k)` (no linear word). -/
noncomputable def pairQuad {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  ((KzEnvAt E ρ).A k) • (F.nOp k + F.nOp (-k))
    + ((KzEnvAt E ρ).B k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))

/-- The *linear* word `a_k + a_k† + a_{−k} + a_{−k}†` of the pair form. -/
noncomputable def pairLin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.a k + F.aDag k + F.a (-k) + F.aDag (-k)

/-- **Definitional split** of FS's pair form into its quadratic and linear halves. -/
lemma pairOpFar_eq_quad_add {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    pairOpFar F E ρ k = pairQuad F E ρ k + (cCoefFar E ρ k) • pairLin F k := rfl

/-- The environment with the linear coefficient killed (`χ̂ ≡ 0`).  At it, FS's pair form
is exactly the quadratic form `pairQuad F E ρ k`. -/
noncomputable def zeroChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) : Q3Env Mode :=
  { E with hatChi := fun _ => 0 }

@[simp] lemma zeroChi_A {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt (zeroChi E) ρ).A k = (KzEnvAt E ρ).A k := rfl

@[simp] lemma zeroChi_B {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    (KzEnvAt (zeroChi E) ρ).B k = (KzEnvAt E ρ).B k := rfl

lemma cCoefFar_zeroChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    cCoefFar (zeroChi E) ρ k = 0 := by
  simp only [cCoefFar, zeroChi]
  ring

lemma pairOpFar_zeroChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    pairOpFar F (zeroChi E) ρ k = pairQuad F E ρ k := by
  simp only [pairOpFar, pairQuad, zeroChi, KzEnvAt, mul_zero, zero_mul, zero_smul, add_zero]

/-! ## 2. The quadratic ground bound (Bogoliubov, per pair) -/

/-- **FS `eq:BogIneq` for the quadratic half alone**: the pairing form
`𝒜_k(n_k+n_{−k}) + ℬ_k(a_ka_{−k} + h.c.)` is bounded below by `−𝒵_k‖f‖²`, where
`𝒵_k = bogZeroPoint 𝒜_k ℬ_k = 𝒜_k − √(𝒜_k²−ℬ_k²)` is FS's zero point.
Proof: `pairOpFar` at `zeroChi E` is the quadratic form (`pairOpFar_zeroChi`) with vanishing
`κ`-error (`cCoefFar_zeroChi`), so `zpPairOp_ground` applies. -/
theorem pairQuad_ground {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < (KzEnvAt E ρ).A k) (hB : |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k)
    (hccr : F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) (f : F.H) :
    -(Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k)) * F.normSq f
      ≤ F.qw f (pairQuad F E ρ k) := by
  have hCe : zpC (zeroChi E) ρ (-k) = zpC (zeroChi E) ρ k := by
    simp only [zpC, cCoefFar_zeroChi]
  have h := zpPairOp_ground F (zeroChi E) ρ k hA hB hAB hAe hBe hCe hccr f
  rw [pairOpFar_zeroChi] at h
  have hk : Work.BoseB6.bogKappaErr (zpA (zeroChi E) ρ k) (zpB (zeroChi E) ρ k)
      (zpC (zeroChi E) ρ k) = 0 := by
    simp only [zpC, cCoefFar_zeroChi, Work.BoseB6.bogKappaErr]
    ring
  rw [hk, add_zero] at h
  simpa only [zpA, zpB, zeroChi_A, zeroChi_B] using h

/-! ## 3. The linear word and its Cauchy–Schwarz bound -/

/-- The quadratic form of the linear word, in terms of the `a`-operators. -/
lemma qw_pairLin_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (k : Mode) (f : F.H) :
    F.qw f (pairLin F k) = 2 * F.bp (F.a k f) f + 2 * F.bp (F.a (-k) f) f := by
  have h1 : F.bp (F.aDag k f) f = F.bp (F.a k f) f :=
    (F.aDag_adjoint k f f).trans (F.bp_symm (F.a k f) f).symm
  have h2 : F.bp (F.aDag (-k) f) f = F.bp (F.a (-k) f) f :=
    (F.aDag_adjoint (-k) f f).trans (F.bp_symm (F.a (-k) f) f).symm
  simp only [FockData.qw, pairLin, LinearMap.add_apply, map_add, LinearMap.add_apply, h1, h2]
  ring

/-- `‖a_k f‖² = ⟨f, n_k f⟩`. -/
lemma normSq_a_eq_qw_nOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (k : Mode) (f : F.H) :
    F.normSq (F.a k f) = F.qw f (F.nOp k) := by
  simp only [FockData.normSq, FockData.qw, FockData.nOp, LinearMap.comp_apply]
  exact (F.aDag_adjoint k (F.a k f) f).symm

/-- **Cauchy–Schwarz for the linear word**: `|⟨f,(a_k+a_k†+a_{−k}+a_{−k}†)f⟩|` is at most
`2(√⟨n_k⟩ + √⟨n_{−k}⟩)√(‖f‖²)`. -/
lemma abs_qw_pairLin_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (k : Mode) (f : F.H) :
    |F.qw f (pairLin F k)|
      ≤ 2 * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
          * Real.sqrt (F.normSq f) := by
  have h1 : |F.bp (F.a k f) f| ≤ Real.sqrt (F.qw f (F.nOp k)) * Real.sqrt (F.normSq f) := by
    have h := Work.BoseB7.bp_cauchy_abs F (F.a k f) f
    have hq : F.bp (F.a k f) (F.a k f) = F.qw f (F.nOp k) := normSq_a_eq_qw_nOp F k f
    have hnf : F.bp f f = F.normSq f := rfl
    rw [hq, hnf] at h
    exact h
  have h2 : |F.bp (F.a (-k) f) f| ≤ Real.sqrt (F.qw f (F.nOp (-k))) * Real.sqrt (F.normSq f) := by
    have h := Work.BoseB7.bp_cauchy_abs F (F.a (-k) f) f
    have hq : F.bp (F.a (-k) f) (F.a (-k) f) = F.qw f (F.nOp (-k)) :=
      normSq_a_eq_qw_nOp F (-k) f
    have hnf : F.bp f f = F.normSq f := rfl
    rw [hq, hnf] at h
    exact h
  rw [qw_pairLin_eq]
  have ha := abs_add_le (2 * F.bp (F.a k f) f) (2 * F.bp (F.a (-k) f) f)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at ha
  have h4 : |F.bp (F.a k f) f| * 2 + |F.bp (F.a (-k) f) f| * 2
      ≤ (Real.sqrt (F.qw f (F.nOp k)) * Real.sqrt (F.normSq f)) * 2
        + (Real.sqrt (F.qw f (F.nOp (-k))) * Real.sqrt (F.normSq f)) * 2 := by
    have h1' : |F.bp (F.a k f) f| * 2
        ≤ (Real.sqrt (F.qw f (F.nOp k)) * Real.sqrt (F.normSq f)) * 2 := by
      linarith [h1]
    have h2' : |F.bp (F.a (-k) f) f| * 2
        ≤ (Real.sqrt (F.qw f (F.nOp (-k))) * Real.sqrt (F.normSq f)) * 2 := by
      linarith [h2]
    linarith
  have hgoal : (Real.sqrt (F.qw f (F.nOp k)) * Real.sqrt (F.normSq f)) * 2
        + (Real.sqrt (F.qw f (F.nOp (-k))) * Real.sqrt (F.normSq f)) * 2
      = 2 * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
          * Real.sqrt (F.normSq f) := by ring
  linarith [ha, h4, hgoal]

/-! ## 4. The summed linear word on the window -/

/-- **The linear-word cost on the `𝓜`-window.**  With the view's Bessel bound
`Σ_k n_k ≤ Cn·N` (`Cn ≤ 16`) and the window `NWindow M f`, the linear part of `KzBogFS`,
`Σ_k ½𝒞_k⟨f,(a_k+a_k†+a_{−k}+a_{−k}†)f⟩`, is bounded above by
`8√(Σ_k𝒞_k²)√M·‖f‖²`. -/
theorem linWord_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (ρ Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hCn16 : Cn ≤ 16)
    (hCn : ∀ g : F.H, F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g)
    (hM : 0 ≤ M) (f : F.H) (hf : T.NWindow M f) :
    (∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k))
      ≤ 8 * Real.sqrt (∑ k : Mode, (cCoefFar E ρ k) ^ 2) * Real.sqrt M * F.normSq f := by
  have hnsq : 0 ≤ F.normSq f := F.normSq_nonneg f
  have hsqn : 0 ≤ Real.sqrt (F.normSq f) := Real.sqrt_nonneg _
  set S : ℝ := ∑ k : Mode, (cCoefFar E ρ k) ^ 2 with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsS : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  -- the window bound on `∑_k ⟨f, n_k f⟩`
  have hQnn : ∀ k : Mode, 0 ≤ F.qw f (F.nOp k) := by
    intro k
    rw [← normSq_a_eq_qw_nOp F k f]
    exact F.bp_nonneg _
  have hsumN : (∑ k : Mode, F.qw f (F.nOp k)) ≤ Cn * M * F.normSq f := by
    have hTN : F.bp (T.N f) f ≤ M * F.normSq f := NWindow_bp_N_le F T hM hf
    have h1 : F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := hCn f
    have h2 : Cn * F.bp (T.N f) f ≤ Cn * (M * F.normSq f) :=
      mul_le_mul_of_nonneg_left hTN hCn0
    have h3 : (∑ k : Mode, F.qw f (F.nOp k)) = F.bp ((∑ k : Mode, F.nOp k) f) f := by
      simp only [FockData.qw, LinearMap.sum_apply, map_sum]
    rw [h3]
    linarith [h1, h2]
  have hsumN0 : 0 ≤ ∑ k : Mode, F.qw f (F.nOp k) := Finset.sum_nonneg fun k _ => hQnn k
  -- Cauchy–Schwarz in the mode sum
  have hCS : (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
      ≤ Real.sqrt S * Real.sqrt (∑ k : Mode, F.qw f (F.nOp k)) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Mode)
      (fun k => |cCoefFar E ρ k|) (fun k => Real.sqrt (F.qw f (F.nOp k)))
    have h2 : (∑ k : Mode, |cCoefFar E ρ k| ^ 2) = S := by
      rw [hS]
      exact Finset.sum_congr rfl fun k _ => by rw [sq_abs]
    have h3 : (∑ k : Mode, (Real.sqrt (F.qw f (F.nOp k))) ^ 2)
        = ∑ k : Mode, F.qw f (F.nOp k) :=
      Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hQnn k)
    rwa [h2, h3] at h
  have hCS' : (∑ k : Mode, |cCoefFar E ρ (-k)| * Real.sqrt (F.qw f (F.nOp k)))
      ≤ Real.sqrt S * Real.sqrt (∑ k : Mode, F.qw f (F.nOp k)) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Mode)
      (fun k => |cCoefFar E ρ (-k)|) (fun k => Real.sqrt (F.qw f (F.nOp k)))
    have h2 : (∑ k : Mode, |cCoefFar E ρ (-k)| ^ 2) = S := by
      rw [hS]
      have hre : (∑ k : Mode, |cCoefFar E ρ (-k)| ^ 2)
          = ∑ k : Mode, (cCoefFar E ρ (-k)) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [sq_abs]
      rw [hre]
      exact Equiv.sum_comp (Equiv.neg Mode) (fun k => (cCoefFar E ρ k) ^ 2)
    have h3 : (∑ k : Mode, (Real.sqrt (F.qw f (F.nOp k))) ^ 2)
        = ∑ k : Mode, F.qw f (F.nOp k) :=
      Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hQnn k)
    rwa [h2, h3] at h
  -- the final chain
  have hstep1 : (∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * |cCoefFar E ρ k| * |F.qw f (pairLin F k)| := by
    refine Finset.sum_le_sum fun k _ => ?_
    have h : cCoefFar E ρ k * F.qw f (pairLin F k)
        ≤ |cCoefFar E ρ k| * |F.qw f (pairLin F k)| := by
      rw [← abs_mul]; exact le_abs_self _
    linarith
  have hstep2 : (∑ k : Mode, (1 / 2 : ℝ) * |cCoefFar E ρ k| * |F.qw f (pairLin F k)|)
      ≤ ∑ k : Mode, |cCoefFar E ρ k|
          * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
          * Real.sqrt (F.normSq f) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hk := abs_qw_pairLin_le F k f
    have hC : 0 ≤ |cCoefFar E ρ k| := abs_nonneg _
    nlinarith [hk, hC]
  have hstep3 : (∑ k : Mode, |cCoefFar E ρ k|
        * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
        * Real.sqrt (F.normSq f))
      = Real.sqrt (F.normSq f)
        * ((∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
          + (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))) := by
    calc (∑ k : Mode, |cCoefFar E ρ k|
          * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
          * Real.sqrt (F.normSq f))
        = ∑ k : Mode, (Real.sqrt (F.normSq f) * (|cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
            + Real.sqrt (F.normSq f) * (|cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = (∑ k : Mode, Real.sqrt (F.normSq f) * (|cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k))))
            + (∑ k : Mode, Real.sqrt (F.normSq f)
                * (|cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))) :=
          Finset.sum_add_distrib
      _ = Real.sqrt (F.normSq f) * (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
            + Real.sqrt (F.normSq f)
              * (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k)))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = Real.sqrt (F.normSq f)
        * ((∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
          + (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))) := by
          ring
  have hstep4 : (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))
      ≤ Real.sqrt S * Real.sqrt (∑ k : Mode, F.qw f (F.nOp k)) := by
    have hre : (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))
        = ∑ k : Mode, |cCoefFar E ρ (-k)| * Real.sqrt (F.qw f (F.nOp k)) := by
      rw [← Equiv.sum_comp (Equiv.neg Mode)
        (fun k => |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))]
      exact Finset.sum_congr rfl fun k _ => by simp
    rw [hre]; exact hCS'
  have hsq : Real.sqrt (Cn * M * F.normSq f) ≤ Real.sqrt 16 * Real.sqrt M * Real.sqrt (F.normSq f) := by
    have hCM : 0 ≤ Cn * M := mul_nonneg hCn0 hM
    rw [Real.sqrt_mul hCM, Real.sqrt_mul hCn0]
    have h1 : Real.sqrt Cn ≤ Real.sqrt 16 := Real.sqrt_le_sqrt hCn16
    have hM' : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have hf' : 0 ≤ Real.sqrt (F.normSq f) := Real.sqrt_nonneg _
    calc Real.sqrt Cn * Real.sqrt M * Real.sqrt (F.normSq f)
        = Real.sqrt Cn * (Real.sqrt M * Real.sqrt (F.normSq f)) := by ring
      _ ≤ Real.sqrt 16 * (Real.sqrt M * Real.sqrt (F.normSq f)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hM' hf')
      _ = Real.sqrt 16 * Real.sqrt M * Real.sqrt (F.normSq f) := by ring
  have hbound : Real.sqrt (Cn * M * F.normSq f) ≤ 4 * Real.sqrt M * Real.sqrt (F.normSq f) := by
    refine hsq.trans (le_of_eq ?_)
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h16]
  have hfin : Real.sqrt S * Real.sqrt (Cn * M * F.normSq f) ≤ Real.sqrt S * (4 * Real.sqrt M * Real.sqrt (F.normSq f)) :=
    mul_le_mul_of_nonneg_left hbound hsS
  have hsqrt16 : Real.sqrt S * Real.sqrt (∑ k : Mode, F.qw f (F.nOp k))
      ≤ Real.sqrt S * Real.sqrt (Cn * M * F.normSq f) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumN) hsS
  have hkey : (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
      + (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))
      ≤ 2 * (Real.sqrt S * Real.sqrt (Cn * M * F.normSq f)) := by
    linarith [hCS, hstep4, hsqrt16]
  have hexp : Real.sqrt (F.normSq f) * (2 * (Real.sqrt S * Real.sqrt (Cn * M * F.normSq f)))
      = 2 * Real.sqrt S * Real.sqrt (Cn * M * F.normSq f) * Real.sqrt (F.normSq f) := by ring
  have hcomb : Real.sqrt (F.normSq f) * (2 * (Real.sqrt S * Real.sqrt (Cn * M * F.normSq f)))
      ≤ 8 * Real.sqrt S * Real.sqrt M * F.normSq f := by
    rw [hexp]
    have h1 : Real.sqrt (Cn * M * F.normSq f) * Real.sqrt (F.normSq f) ≤ 4 * Real.sqrt M * F.normSq f := by
      have h := hbound
      have hsqf : Real.sqrt (F.normSq f) * Real.sqrt (F.normSq f) = F.normSq f := by
        rw [← sq, Real.sq_sqrt hnsq]
      nlinarith [h, hsqn, Real.sqrt_nonneg M, hnsq, hsqf]
    nlinarith [h1, hsS, hnsq]
  calc (∑ k : Mode, (1 / 2 : ℝ) * cCoefFar E ρ k * F.qw f (pairLin F k))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * |cCoefFar E ρ k| * |F.qw f (pairLin F k)| := hstep1
    _ ≤ ∑ k : Mode, |cCoefFar E ρ k|
          * (Real.sqrt (F.qw f (F.nOp k)) + Real.sqrt (F.qw f (F.nOp (-k))))
          * Real.sqrt (F.normSq f) := hstep2
    _ = Real.sqrt (F.normSq f)
        * ((∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp k)))
          + (∑ k : Mode, |cCoefFar E ρ k| * Real.sqrt (F.qw f (F.nOp (-k))))) := hstep3
    _ ≤ Real.sqrt (F.normSq f) * (2 * (Real.sqrt S * Real.sqrt (Cn * M * F.normSq f))) :=
        mul_le_mul_of_nonneg_left hkey hsqn
    _ ≤ 8 * Real.sqrt S * Real.sqrt M * F.normSq f := hcomb

/-! ## 5. The window bound on the `n₊`-content -/

/-- **The window bound on `Σ_k ½⟨(n_k+n_{−k})f,f⟩`.**  The view's Bessel conjunct (`Cn ≤ 16`)
composed with the window `NWindow 𝓜 f` gives `Σ_k ⟨f,n_kf⟩ ≤ 16𝓜‖f‖²`; the pairing kernel
`(n_k+n_{−k})` doubles nothing after the `k ↦ −k` reindexing. -/
theorem window_nplus_le {v : E3 → ℝ} {h : ScatSol v} {μ : ℝ}
    (D : KzDatum) (hview : D.viewFSAll v h μ) (f : D.F.H)
    (hf : D.T.NWindow D.E.bigM f) :
    (∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k)))
      ≤ 16 * D.E.bigM * D.F.normSq f := by
  unfold KzDatum.viewFSAll RViewFSAll at hview
  obtain ⟨hFSP, -, haSc, -, hbigM, -, hd, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hBessel, -⟩ := hview
  obtain ⟨Cn, hCn0, hCn16, hCn⟩ := hBessel
  have hFSPv : FSParamsView D.E := Classical.choice hFSP
  have hM : 0 ≤ D.E.bigM := le_trans zero_le_one hFSPv.one_le_bigM
  have hnsq : 0 ≤ D.F.normSq f := D.F.normSq_nonneg f
  have hTN : D.F.bp (D.T.N f) f ≤ D.E.bigM * D.F.normSq f :=
    NWindow_bp_N_le D.F D.T hM hf
  have hB : D.F.qw f (∑ k : D.Mode, D.F.nOp k) ≤ Cn * D.E.bigM * D.F.normSq f := by
    have h2 : Cn * D.F.bp (D.T.N f) f ≤ Cn * (D.E.bigM * D.F.normSq f) :=
      mul_le_mul_of_nonneg_left hTN hCn0
    calc D.F.qw f (∑ k : D.Mode, D.F.nOp k)
        = D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f := rfl
      _ ≤ Cn * D.F.bp (D.T.N f) f := hCn f
      _ ≤ Cn * (D.E.bigM * D.F.normSq f) := h2
      _ = Cn * D.E.bigM * D.F.normSq f := by ring
  -- `Σ_k ½(qw(n_k) + qw(n_{−k})) = Σ_k qw(n_k)`
  have hsplit : (∑ k : D.Mode, (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k)))
      = ∑ k : D.Mode, D.F.qw f (D.F.nOp k) := by
    have h1 : ∀ k : D.Mode,
        (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k + D.F.nOp (-k))
          = (1 / 2 : ℝ) * D.F.qw f (D.F.nOp k) + (1 / 2 : ℝ) * D.F.qw f (D.F.nOp (-k)) := by
      intro k
      rw [FockData.qw_add]
      ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have h2 : (∑ k : D.Mode, D.F.qw f (D.F.nOp (-k)))
        = ∑ k : D.Mode, D.F.qw f (D.F.nOp k) :=
      Equiv.sum_comp (Equiv.neg D.Mode) (fun k => D.F.qw f (D.F.nOp k))
    rw [h2]
    ring
  have hq : (∑ k : D.Mode, D.F.qw f (D.F.nOp k)) = D.F.qw f (∑ k : D.Mode, D.F.nOp k) := by
    simp only [FockData.qw, map_sum, LinearMap.sum_apply]
  rw [hsplit, hq]
  calc D.F.qw f (∑ k : D.Mode, D.F.nOp k)
      ≤ Cn * D.E.bigM * D.F.normSq f := hB
    _ ≤ 16 * D.E.bigM * D.F.normSq f := by
        have h1 : Cn * D.E.bigM ≤ 16 * D.E.bigM := mul_le_mul_of_nonneg_right hCn16 hM
        have := mul_le_mul_of_nonneg_right h1 hnsq
        linarith [this]

end Work.BoseFixR.All
