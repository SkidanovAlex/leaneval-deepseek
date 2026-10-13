/-
# `Submission/Work/FTS_MuLipC/RowN/diffRow1.lean` — the difference row of `N`

The target is `Work.FTS_MuLipC.DiffRow1 α C₀ Φs E`: for `ClassC α` profiles `f`, `f'` of
`ℋ⁴`-size `≤ C₀α²` (and `C₀α² ≤ 1`) the `L₁₂`-zero mode of the bilinear field
`Sn α Φs E g = N α (F_*+g) (Φ_s+E g)` is Lipschitz in the profile, with a constant depending on
`α, C₀, Ce, Cs` only.

## Route

1. `SnPol` (`RowN/SnPol.lean`) is the *field* polarization identity
   `Sn f - Sn f' = (1/(4t)) • (Sn(u+td) - Sn(u-td) + Sn(td) - Sn(-td))`, `u = f+f'`, `d = f-f'`,
   for `ClassC` profiles and `t ≠ 0`, pointwise on the open quadrant.
2. `NHonest` (`RowN/NHonest.lean`) supplies the honesty of the field `Sn α Φs E g` (finiteness of
   `Fa`, joint a.e. strong measurability, a.e. `θ`-slice integrability of the density integrand,
   integrability of the `L₁₂`-density), which is exactly what `L12Ae.lean` needs in order to turn
   the field identity into the identity of `L₁₂`-zero modes at the four scaled profiles `xᵢ`.
3. The proved single-profile row `Work.FTS_MuLamOK.KMu1_row` bounds the four terms by
   `K₁·Env α |xᵢ|_{ℋ⁴}`, and the sizes are `|u ± t·d|_{ℋ⁴} ≤ √2(2√2 C₀α² + t|d|)`, `|t·d| = t|d|`.
4. Taking `t := α²/|d|_{ℋ⁴}` gives the Lipschitz bound; for `|d|_{ℋ⁴} = 0` the estimate holds for
   every `t`, and `t → ∞` gives the value `0`.

Since there is no `classC_sub`, the difference is spelled `d' = f + (-1)•f'` and the four scaled
profiles are `(f+f') + t•d'`, `(f+f') + (-t)•d'`, `t•d'`, `(-t)•d'`; the translation from the
spelling used by `SnPol` is the pointwise-congruence lemma `Sn_congr`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS_MuLipC.RowN.Defs
import Submission.Work.FTS_MuLipC.RowN.L12Ae
import Submission.Work.FTS_MuLipC.RowN.NHonest
import Submission.Work.FTS_MuLipC.RowN.SnPol
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS_MuLamOK.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary auxiliary lemmas -/

/-- `HkNorm` only sees the values on the open quadrant. -/
theorem HkNorm_congr_Qd (α : ℝ) (k : ℕ) {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g :=
  congrArg Real.sqrt (Work.FTS.EllipticEst.HkSq_congr_open α k h)

/-- Congruence of `|·|_{ℋ⁴}` on the open quadrant. -/
theorem Xn_congr_Qd {α : ℝ} {f g : Fn}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g :=
  HkNorm_congr_Qd α 4 h

/-- The field `Sn` only sees the profile through its pointwise values. -/
theorem Sn_congr {α : ℝ} {Φs : Fn} {E : Fn → Fn} {X Y : Fn}
    (h : ∀ z θ : ℝ, X z θ = Y z θ) : Sn α Φs E X = Sn α Φs E Y := by
  have hXY : X = Y := funext (fun z => funext (h z))
  rw [hXY]

/-- Monotonicity of the envelope in its second argument on the nonnegative half-line. -/
theorem Env_mono {α X Y : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    Work.FTS_MuLipC.Env α X ≤ Work.FTS_MuLipC.Env α Y := by
  have h1 : Real.sqrt α * X ≤ Real.sqrt α * Y :=
    mul_le_mul_of_nonneg_left hXY (Real.sqrt_nonneg α)
  have h2 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * Y ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Real.rpow_nonneg hα _)
  rw [Work.FTS_MuLipC.Env, Work.FTS_MuLipC.Env]
  linarith

/-- `√α·α^{5/2} = α³`, hence `√α·α² ≤ α²` for `α ≤ 1`: the two elementary facts behind
`Env_scaled`. -/
theorem sqrt_alpha_mul_sq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt α * α ^ 2 ≤ α ^ 2 := by
  have hs : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  calc Real.sqrt α * α ^ 2 ≤ 1 * α ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg α)
    _ = α ^ 2 := one_mul _

/-- `α^{-3/2}·(α²)² ≤ α²` for `0 < α ≤ 1`. -/
theorem rpow_neg_mul_four {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(3 / 2 : ℝ)) * (α ^ 2) ^ 2 ≤ α ^ 2 := by
  have hsq : α ^ 2 = α ^ (2 : ℝ) := by rw [Real.rpow_two, pow_two]
  have h : α ^ (-(3 / 2 : ℝ)) * α ^ (2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα]
    have h2 : -(3 / 2 : ℝ) + 2 = 1 / 2 := by norm_num
    rw [h2]
    exact Real.rpow_le_one hα.le hα1 (by norm_num)
  rw [hsq]
  calc α ^ (-(3 / 2 : ℝ)) * (α ^ (2 : ℝ)) ^ 2
      = (α ^ (-(3 / 2 : ℝ)) * α ^ (2 : ℝ)) * α ^ (2 : ℝ) := by
        rw [pow_two]
        ring
    _ ≤ 1 * α ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hα.le _)
    _ = α ^ (2 : ℝ) := one_mul _

/-- The scaled envelope: `Env α (B·α²) ≤ (1+B+B²)·α²` for `0 < α ≤ 1` and `B ≥ 0`. -/
theorem Env_scaled {α B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B) :
    Work.FTS_MuLipC.Env α (B * α ^ 2) ≤ (1 + B + B ^ 2) * α ^ 2 := by
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  have h1 : Real.sqrt α * (B * α ^ 2) ≤ B * α ^ 2 := by
    calc Real.sqrt α * (B * α ^ 2) = B * (Real.sqrt α * α ^ 2) := by ring
      _ ≤ B * α ^ 2 := mul_le_mul_of_nonneg_left (sqrt_alpha_mul_sq hα hα1) hB
  have h2 : α ^ (-(3 / 2 : ℝ)) * (B * α ^ 2) ^ 2 ≤ B ^ 2 * α ^ 2 := by
    have hmain := rpow_neg_mul_four hα hα1
    have hfac : α ^ (-(3 / 2 : ℝ)) * (B * α ^ 2) ^ 2
        = B ^ 2 * (α ^ (-(3 / 2 : ℝ)) * (α ^ 2) ^ 2) := by
      rw [mul_pow]
      ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hmain (sq_nonneg B)
  rw [Work.FTS_MuLipC.Env]
  linarith

/-! ## The analytic core -/

/-- **The core estimate.**  For `ClassC` profiles `f`, `f'` with `|f|_{ℋ⁴}, |f'|_{ℋ⁴} ≤ C·α²`
(`C ≥ 0`) and every `t > 0`,

`|L₁₂(Sn f)(0) - L₁₂(Sn f')(0)| ≤ (K₁/t)·Env α (√2·(2√2·C·α² + t·|f - f'|_{ℋ⁴}))`. -/
theorem l12_diff_le {α C Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {f f' : Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f')
    (hXf : Work.FTS.Nonlin.Xn α f ≤ C * α ^ 2)
    (hXf' : Work.FTS.Nonlin.Xn α f' ≤ C * α ^ 2)
    {t : ℝ} (ht : 0 < t) :
    |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      ≤ (Work.FTS_MuLamOK.KMu1 Ce Cs / t) * Work.FTS_MuLipC.Env α
          (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
            + t * Work.FTS.Nonlin.Xn α (f - f'))) := by
  classical
  have hCα : 0 ≤ C * α ^ 2 := mul_nonneg hC (sq_nonneg α)
  have hK1pos : 0 < Work.FTS_MuLamOK.KMu1 Ce Cs := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  -- ### the class-friendly difference and the four scaled profiles
  have hd' : Work.FTS.ClassC.ClassC α (f + (-1 : ℝ) • f') :=
    Work.FTS.ClassC.classC_add hf (Work.FTS.ClassC.classC_smul (-1) hf')
  have hu : Work.FTS.ClassC.ClassC α (f + f') := Work.FTS.ClassC.classC_add hf hf'
  have hP1 : Work.FTS.ClassC.ClassC α ((f + f') + t • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul t hd')
  have hP2 : Work.FTS.ClassC.ClassC α ((f + f') + (-t) • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul (-t) hd')
  have hP3 : Work.FTS.ClassC.ClassC α (t • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_smul t hd'
  have hP4 : Work.FTS.ClassC.ClassC α ((-t) • (f + (-1 : ℝ) • f')) :=
    Work.FTS.ClassC.classC_smul (-t) hd'
  -- ### the honesty of the six fields, in the field's own spelling
  have sl : ∀ {g : Fn} (hg : Work.FTS.ClassC.ClassC α g),
      ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Sn α Φs E g r θ / r) Work.Spaces.Iθ :=
    fun {g} hg => (NHonest hα hα1 hg.reg (Work.FTS.ClassC.classC_hkMem_four hg)
      hstar.toStarPkgo (hell g hg)).2.2.1
  have dn : ∀ {g : Fn} (hg : Work.FTS.ClassC.ClassC α g),
      MeasureTheory.IntegrableOn (fun r => Work.Construction.L12dens (Sn α Φs E g) r)
        (Set.Ioi (0 : ℝ)) :=
    fun {g} hg => (NHonest hα hα1 hg.reg (Work.FTS.ClassC.classC_hkMem_four hg)
      hstar.toStarPkgo (hell g hg)).2.2.2
  -- ### the field polarization identity in the class-friendly spelling
  have hpol := SnPol hα hα1 hEadd hEsmul hstar hell hf hf' (ne_of_gt ht)
  have hbrid : ∀ {X Y : Fn}, (∀ z θ : ℝ, X z θ = Y z θ) → Sn α Φs E X = Sn α Φs E Y :=
    fun h => Sn_congr h
  have hp1 : Sn α Φs E (f + f' + t • (f - f'))
      = Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp2 : Sn α Φs E (f + f' - t • (f - f'))
      = Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp3 : Sn α Φs E (t • (f - f')) = Sn α Φs E (t • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring)
  have hp4 : Sn α Φs E (-(t • (f - f'))) = Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) :=
    hbrid (fun z θ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring)
  have hpol' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Sn α Φs E f z θ - Sn α Φs E f' z θ
        = (1 / (4 * t)) * (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) z θ
            + Sn α Φs E (t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) z θ) := by
    intro z θ hz hθ0 hθ1
    rw [hpol z θ hz hθ0 hθ1, hp1, hp2, hp3, hp4]
  -- ### the `L₁₂`-identity
  have hsub := L12_sub_eq (a := Sn α Φs E f) (b := Sn α Φs E f') (z := 0)
    (sl hf) (sl hf') (dn hf) (dn hf')
  have hcongr : Work.Construction.L12
        (fun z θ => Sn α Φs E f z θ - Sn α Φs E f' z θ) 0
      = Work.Construction.L12 (fun z θ => (1 / (4 * t))
          * (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f')) z θ
            + Sn α Φs E (t • (f + (-1 : ℝ) • f')) z θ
            - Sn α Φs E ((-t) • (f + (-1 : ℝ) • f')) z θ)) 0 :=
    L12_congrQd (le_refl 0) (fun z θ hz hθ0 hθ1 => hpol' z θ hz hθ0 hθ1)
  have halt4 := L12_alt4 (z := 0) (le_refl 0)
    (sl hP1) (sl hP2) (sl hP3) (sl hP4) (dn hP1) (dn hP2) (dn hP3) (dn hP4)
  have hkey : Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0
      = (1 / (4 * t)) * (Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0) := by
    rw [hsub, hcongr, L12_const_mul, halt4]
  -- ### the single-profile row at the four scaled profiles
  have hrow : ∀ {g : Fn}, Work.FTS.ClassC.ClassC α g →
      |Work.Construction.L12 (Sn α Φs E g) 0| ≤ Work.FTS_MuLamOK.KMu1 Ce Cs
        * Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α g) :=
    fun hg => Work.FTS_MuLamOK.KMu1_row Ce Cs hα hα1 hg.reg
      (Work.FTS.ClassC.classC_hkMem_four hg) hstar.toStarPkgo (hell _ hg)
  -- ### the sizes of the four profiles
  have hdiff : ∀ z θ : ℝ, (f - f') z θ = (f + (-1 : ℝ) • f') z θ := by
    intro z θ
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hXd : Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f')
      = Work.FTS.Nonlin.Xn α (f - f') :=
    (Xn_congr_Qd (fun z θ _ _ _ => hdiff z θ)).symm
  have hXu : Work.FTS.Nonlin.Xn α (f + f') ≤ 2 * Real.sqrt 2 * C * α ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α (f + f')
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α f') :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hf.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hf'.reg)
        (Work.FTS.ClassC.classC_hkMem_four hf) (Work.FTS.ClassC.classC_hkMem_four hf')
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α f')
        ≤ Real.sqrt 2 * (C * α ^ 2 + C * α ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hXf hXf') (Real.sqrt_nonneg 2)
    have h3 : Real.sqrt 2 * (C * α ^ 2 + C * α ^ 2) = 2 * Real.sqrt 2 * C * α ^ 2 := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hX3 : Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f'))
      = t * Work.FTS.Nonlin.Xn α (f - f') := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => t * (f + (-1 : ℝ) • f') z θ)
        = |t| * Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f') :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 t
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hd'.reg)
    rw [show (t • (f + (-1 : ℝ) • f'))
        = fun z θ => t * (f + (-1 : ℝ) • f') z θ from rfl, h1, abs_of_pos ht, hXd]
  have hX4 : Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f'))
      = t * Work.FTS.Nonlin.Xn α (f - f') := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => (-t) * (f + (-1 : ℝ) • f') z θ)
        = |-t| * Work.FTS.Nonlin.Xn α (f + (-1 : ℝ) • f') :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (-t)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hd'.reg)
    rw [show ((-t) • (f + (-1 : ℝ) • f'))
        = fun z θ => (-t) * (f + (-1 : ℝ) • f') z θ from rfl, h1, abs_neg, abs_of_pos ht, hXd]
  have hXadd1 : Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f'))
      ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    have h1 : Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f'))
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f'))) :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hu.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hP3.reg)
        (Work.FTS.ClassC.classC_hkMem_four hu) (Work.FTS.ClassC.classC_hkMem_four hP3)
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f')))
        ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f')) :=
      mul_le_mul_of_nonneg_left (add_le_add hXu (le_of_eq hX3)) (Real.sqrt_nonneg 2)
    linarith
  have hXadd2 : Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f'))
      ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    have h1 : Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f'))
        ≤ Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f'))) :=
      Work.FTS.EllipticEst.HkNorm_add_le α 4
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hu.reg)
        (Work.FTS_EllLimOK.contDiffOn_of_smoothOpen hP4.reg)
        (Work.FTS.ClassC.classC_hkMem_four hu) (Work.FTS.ClassC.classC_hkMem_four hP4)
    have h2 : Real.sqrt 2 * (Work.FTS.Nonlin.Xn α (f + f')
          + Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f')))
        ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f')) :=
      mul_le_mul_of_nonneg_left (add_le_add hXu (le_of_eq hX4)) (Real.sqrt_nonneg 2)
    linarith
  -- ### assembly
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α (f - f') := Work.Spaces.HkNorm_nonneg α 4 _
  have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
      + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
  have hb1 := hrow hP1
  have hb2 := hrow hP2
  have hb3 := hrow hP3
  have hb4 := hrow hP4
  have e1 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((f + f') + t • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) hXadd1
  have e2 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((f + f') + (-t) • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) hXadd2
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have harg : ∀ {Y : ℝ}, Y = t * Work.FTS.Nonlin.Xn α (f - f') →
      Y ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')) := by
    intro Y hY
    rw [hY]
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 * C * α ^ 2 := by positivity
    have h3 : 0 ≤ t * Work.FTS.Nonlin.Xn α (f - f') := mul_nonneg ht.le hXn0
    calc t * Work.FTS.Nonlin.Xn α (f - f')
        ≤ Real.sqrt 2 * (t * Work.FTS.Nonlin.Xn α (f - f')) := by
          simpa using mul_le_mul_of_nonneg_right hsqrt2 h3
      _ ≤ Real.sqrt 2 * (t * Work.FTS.Nonlin.Xn α (f - f')
            + 2 * Real.sqrt 2 * C * α ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
            + t * Work.FTS.Nonlin.Xn α (f - f')) := by ring
  have e3 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α (t • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) (harg hX3)
  have e4 : Work.FTS_MuLipC.Env α (Work.FTS.Nonlin.Xn α ((-t) • (f + (-1 : ℝ) • f')))
      ≤ Work.FTS_MuLipC.Env α (Real.sqrt 2 * (2 * Real.sqrt 2 * C * α ^ 2
          + t * Work.FTS.Nonlin.Xn α (f - f'))) :=
    Env_mono hα.le (Work.Spaces.HkNorm_nonneg α 4 _) (harg hX4)
  have hB0 : 0 ≤ 1 / (4 * t) := by positivity
  calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      = |(1 / (4 * t)) * (Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0)| := by
        rw [hkey]
    _ = (1 / (4 * t)) * |(Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
          + Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
          - Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0)| := by
        rw [abs_mul, abs_of_nonneg hB0]
    _ ≤ (1 / (4 * t)) * (|Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0|
          + |Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0|) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        set A := Work.Construction.L12 (Sn α Φs E ((f + f') + t • (f + (-1 : ℝ) • f'))) 0
        set B := Work.Construction.L12 (Sn α Φs E ((f + f') + (-t) • (f + (-1 : ℝ) • f'))) 0
        set Cc := Work.Construction.L12 (Sn α Φs E (t • (f + (-1 : ℝ) • f'))) 0
        set D := Work.Construction.L12 (Sn α Φs E ((-t) • (f + (-1 : ℝ) • f'))) 0
        have h1 : |(A - B + Cc) - D| ≤ |A - B + Cc| + |D| := by
          rw [sub_eq_add_neg]
          simpa using abs_add_le (A - B + Cc) (-D)
        have h2 : |A - B + Cc| ≤ |A - B| + |Cc| := abs_add_le (A - B) Cc
        have h3 : |A - B| ≤ |A| + |B| := by
          rw [sub_eq_add_neg]
          simpa using abs_add_le A (-B)
        linarith
    _ ≤ (1 / (4 * t)) * (Work.FTS_MuLamOK.KMu1 Ce Cs * (Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f')))
          + Work.FTS_MuLipC.Env α (Real.sqrt 2
            * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f'))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        have hK0 : 0 ≤ Work.FTS_MuLamOK.KMu1 Ce Cs := hK1pos.le
        nlinarith [hb1, hb2, hb3, hb4, e1, e2, e3, e4, hEnv0, hK0]
    _ = (Work.FTS_MuLamOK.KMu1 Ce Cs / t) * Work.FTS_MuLipC.Env α (Real.sqrt 2
          * (2 * Real.sqrt 2 * C * α ^ 2 + t * Work.FTS.Nonlin.Xn α (f - f'))) := by
        field_simp
        ring

/-! ## The target -/

/-- **The difference row of `N`** (`DiffRow1 α C₀ Φs E`, `Submission/Work/FTS_MuLipC/Defs.lean`):
for `ClassC α` profiles `f`, `f'` of `ℋ⁴`-size `≤ C₀α²` (with `C₀α² ≤ 1`), the `L₁₂`-zero-mode of
the bilinear field `Sn α Φs E g = N α (F_*+g) (Φ_s + E g)` is Lipschitz in the profile, with a
constant depending on `α, C₀, Ce, Cs` only.  The map `E` is additive and `ℝ`-homogeneous (it is a
linear map in the application — the additivity and homogeneity are exactly what the polarization
at the scaled profiles `±t·d`, `u ± t·d` needs), `Φ_s` satisfies the star package, and `E g`
satisfies the elliptic package at every `ClassC` profile `g`.  Read
`Submission/Work/FTS_MuLipC/NOTES.md` for the route. -/
theorem diffRow1 {α C₀ Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hsmall : C₀ * α ^ 2 ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    Work.FTS_MuLipC.DiffRow1 α C₀ Φs E := by
  classical
  -- ### the constants
  set K₁ : ℝ := Work.FTS_MuLamOK.KMu1 Ce Cs with hK₁
  have hK₁pos : 0 < K₁ := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  have hK₁0 : 0 ≤ K₁ := hK₁pos.le
  set c : ℝ := max C₀ 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hcC : C₀ ≤ c := le_max_left _ _
  set B₁ : ℝ := Real.sqrt 2 * (2 * Real.sqrt 2 * c + 1) with hB₁
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  set B₂ : ℝ := 1 + B₁ + B₁ ^ 2 with hB₂
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  refine ⟨K₁ * B₂ + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hXc : Work.FTS.Nonlin.Xn α f ≤ c * α ^ 2 :=
    le_trans hXf (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  have hXc' : Work.FTS.Nonlin.Xn α f' ≤ c * α ^ 2 :=
    le_trans hXf' (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  rcases lt_or_eq_of_le hX0 with hXpos | hXzero
  · -- ### the main case `|f - f'|_{ℋ⁴} > 0`
    set t : ℝ := α ^ 2 / X with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htX : t * X = α ^ 2 := by
      rw [ht]
      field_simp
    have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
    rw [← hX, htX] at hle
    have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + α ^ 2) = B₁ * α ^ 2 := by
      rw [hB₁]
      ring
    rw [hV] at hle
    have hEnv : Work.FTS_MuLipC.Env α (B₁ * α ^ 2) ≤ B₂ * α ^ 2 := by
      rw [hB₂]
      exact Env_scaled hα hα1 hB₁0
    have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (B₁ * α ^ 2) :=
      Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
    have htinv : K₁ / t = K₁ * X / α ^ 2 := by
      rw [ht]
      field_simp
    calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
        ≤ (K₁ / t) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := hle
      _ = (K₁ * X / α ^ 2) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := by rw [htinv]
      _ ≤ (K₁ * X / α ^ 2) * (B₂ * α ^ 2) := by
          refine mul_le_mul_of_nonneg_left hEnv ?_
          positivity
      _ = K₁ * B₂ * X := by
          field_simp
      _ ≤ (K₁ * B₂ + 1) * X := by nlinarith [hX0, hB₂0, hK₁0]
  · -- ### the degenerate case `|f - f'|_{ℋ⁴} = 0`
    have hzero : |Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0| = 0 := by
      refine le_antisymm ?_ (abs_nonneg _)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      set t : ℝ := K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1 with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
      rw [← hX, hXzero.symm] at hle
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two]
        exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + t * 0) = (4 * c) * α ^ 2 := by
        have hmid : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2) = (4 * c) * α ^ 2 := by
          calc Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2)
              = (Real.sqrt 2 * Real.sqrt 2) * (2 * c * α ^ 2) := by ring
            _ = 2 * (2 * c * α ^ 2) := by rw [hsq2]
            _ = (4 * c) * α ^ 2 := by ring
        rw [mul_zero, add_zero, hmid]
      rw [hV] at hle
      have hEnv : Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 :=
        Env_scaled hα hα1 (by positivity)
      have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) :=
        Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
      have hnum0 : 0 ≤ K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 := by positivity
      have hfin : (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ ε := by
        calc (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2)
            ≤ (K₁ / t) * ((1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) := by
              refine mul_le_mul_of_nonneg_left hEnv ?_
              positivity
          _ = (K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) / t := by
              field_simp
          _ ≤ ε := by
              rw [ht]
              rw [div_le_iff₀ (by positivity : 0 < K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1)]
              field_simp
              nlinarith [hε.le, hnum0]
      linarith [hle, hfin]
    rw [hzero]
    exact mul_nonneg (by positivity) hX0

end Work.FTS_MuLipC.RowN
