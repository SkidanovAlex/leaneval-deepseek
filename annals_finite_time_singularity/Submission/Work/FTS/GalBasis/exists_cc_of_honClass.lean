import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts: extensionality of the `ℋ⁴`-objects and of `L₁₂` -/

/-- Pointwise-equal functions have the same `D_z`-iterates. -/
theorem DzIter_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (n : ℕ) :
    ∀ z θ, Work.Spaces.DzIter n a z θ = Work.Spaces.DzIter n b z θ := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.Dz,
        Work.Spaces.pz, Work.Spaces.pz]
      have heq : (fun z' => Work.Spaces.DzIter n a z' θ)
          = (fun z' => Work.Spaces.DzIter n b z' θ) := funext fun z' => ih z' θ
      rw [heq]

/-- Pointwise-equal functions have the same `D_θ`-iterates. -/
theorem DthIter_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (n : ℕ) :
    ∀ z θ, Work.Spaces.DthIter n a z θ = Work.Spaces.DthIter n b z θ := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Spaces.pth]
      have heq : (fun θ' => Work.Spaces.DthIter n a z θ')
          = (fun θ' => Work.Spaces.DthIter n b z θ') := funext fun θ' => ih z θ'
      rw [heq]

/-- Pointwise-equal functions have the same mixed iterates. -/
theorem mixed_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (j i : ℕ) :
    ∀ z θ, Work.Spaces.mixed j i a z θ = Work.Spaces.mixed j i b z θ := by
  intro z θ
  exact DzIter_congr_all (DthIter_congr_all h i) j z θ

/-- Pointwise-equal functions have the same `ℋ^k`-integrand. -/
theorem HkIntegrand_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k a z θ = Work.Spaces.HkIntegrand α k b z θ := by
  have hz : ∀ i : ℕ, Work.Spaces.DzIter i a z θ = Work.Spaces.DzIter i b z θ :=
    fun i => DzIter_congr_all h i z θ
  have hm : ∀ j i : ℕ, Work.Spaces.mixed j i a z θ = Work.Spaces.mixed j i b z θ :=
    fun j i => mixed_congr_all h j i z θ
  simp only [Work.Spaces.HkIntegrand, hz, hm]

/-- Pointwise-equal functions have the same `ℋ^k`-square. -/
theorem HkSq_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkSq α k a = Work.Spaces.HkSq α k b := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => HkIntegrand_congr_all h α k z θ)

/-- Pointwise-equal functions have the same `ℋ^k`-norm. -/
theorem HkNorm_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k a = Work.Spaces.HkNorm α k b := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_congr_all h α k]

/-- Pointwise-equal functions have the same `ℋ^k`-membership. -/
theorem HkMem_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) (α : ℝ) (k : ℕ)
    (hm : Work.Spaces.HkMem α k a) : Work.Spaces.HkMem α k b := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k a z θ = Work.Spaces.HkIntegrand α k b z θ :=
    fun z θ => HkIntegrand_congr_all h α k z θ
  constructor
  · intro z hz
    exact (hm.1 z hz).congr_fun (fun θ _ => hpt z θ) measurableSet_Icc
  · have h2 : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k a z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k b z θ) := by
      funext z
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt z θ)
    rw [← h2]
    exact hm.2

/-- `L₁₂` only depends on the pointwise values. -/
theorem L12_congr_all {a b : Fn} (h : ∀ z θ, a z θ = b z θ) :
    ∀ z, Work.Construction.L12 a z = Work.Construction.L12 b z := by
  intro z
  simp only [Work.Construction.L12, Work.FM.L12]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  simp only [Work.FM.L12dens]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [h s θ])

/-- `L₁₂` is homogeneous. -/
theorem L12_const_mul (c : ℝ) (a : Fn) :
    ∀ z, Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  intro z
  simp only [Work.Construction.L12, Work.FM.L12]
  have hpt : (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => c * a z θ) s)
      = fun s => c * Work.FM.L12dens Work.Spaces.K a s :=
    funext fun s => Work.FTS.LocData.L12dens_const_mul Work.Spaces.K c a s
  rw [hpt, MeasureTheory.integral_const_mul]



/-- `HkMem` is closed under multiplication by a constant. -/
theorem HkMem_const_mul_all {α : ℝ} {k : ℕ} (c : ℝ) {g : Fn}
    (hm : Work.Spaces.HkMem α k g) : Work.Spaces.HkMem α k (fun z θ => c * g z θ) := by
  constructor
  · intro z hz
    rw [funext fun θ => Work.FTS.LocData.HkIntegrand_const_mul α k c g z θ]
    exact (hm.1 z hz).const_mul (c ^ 2)
  · have h2 : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => c * g z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
      funext z
      rw [funext fun θ => Work.FTS.LocData.HkIntegrand_const_mul α k c g z θ,
        MeasureTheory.integral_const_mul]
    rw [h2]
    exact hm.2.const_mul (c ^ 2)






end Work.FTS.GalBasis
