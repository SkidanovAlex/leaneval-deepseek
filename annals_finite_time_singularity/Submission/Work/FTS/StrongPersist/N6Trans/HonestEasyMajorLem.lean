import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.HonestSupMixed
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
import Submission.Work.FTS.H2.T1EasyBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The honest-class bound for the pointwise majorant `EasyMajor` of the flat `ℋ⁴` pairing.**

For the honest data class — `f`, `g` of class `C^∞` on the *open* quadrant (`SmoothOpen`),
honestly in `ℋ⁴` (`HkMem α 4`), and `g` with `DecayAll 4 g` (no decay of `f`, no smoothness at
`z = 0` or at the angular boundary) — the majorant `EasyMajor α f g` is integrable for the
product measure `pm` and

  `∫ EasyMajor α f g ≤ C/√(γ-1) · |f|_{ℋ⁴} · |g|²_{ℋ⁴}`.

Route: the two pointwise `L^∞`-bounds `Kf`, `Kg` of order `≤ 2` come from `HonestSupMixed`
(`C1/√(γ-1)·|f|_{ℋ⁴}` resp. `C1/√(γ-1)·|g|_{ℋ⁴}`), the angular-supremum device `K3` from the
open-class `Work.FTS.TransportS.SlotT2.supThetaIntOpen` (`K3 = CK/√(γ-1)²·|f|²_{ℋ⁴}`), and the
`2`-dimensional assembly is the open-class (no-decay) port `AssemblyQ_o` of
`Work.H2.T1Q.AssemblyQ` (see `HonestEasyMajorAux`), whose exceptional summand is
`OpenTwins.ExcBoundOpen`.  The three terms of `TTot α f g Kf Kg K3` are all
`(const/√(γ-1))·|f|_{ℋ⁴}·HkSq α 4 g`, with constants `C1`, `C1` and `√CK`. -/
theorem HonestEasyMajorLem : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.EasyMajor α f g p.1 p.2)
        Work.FTS.H2.pm ∧
    ∫ p, Work.FTS.H2.EasyMajor α f g p.1 p.2 ∂Work.FTS.H2.pm
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C1, hC1pos, hC1⟩ := HonestSupMixed
  obtain ⟨CK, hCKpos, hCK⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  refine ⟨5000000 * (2 * C1 + Real.sqrt CK), by positivity, ?_⟩
  intro α f g hα hα1 hf hmf hg hmg hdecg
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hs0 : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
  have hF0 : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hG0 : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ### the two pointwise `L^∞`-bounds of order `≤ 2`
  have hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
    fun b a hab z θ hz hθ hθ2 => hC1 α f hα hα1 hf hmf b a hab z θ hz hθ hθ2
  have hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ|
        ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
    fun b a hab z θ hz hθ hθ2 => hC1 α g hα hα1 hg hmg b a hab z θ hz hθ hθ2
  -- ### the angular-supremum device `K3`
  obtain ⟨hGint0, hGle0⟩ := hCK α f 3 hα hα1 (by norm_num) hf hmf
  have hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    simpa only [Work.FTS.H2.supAbsThO, mul_pow] using hGint0
  have hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      ≤ CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    simpa only [Work.FTS.H2.supAbsThO, mul_pow] using hGle0
  have hK30 : (0 : ℝ) ≤ CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f :=
    mul_nonneg (div_nonneg hCKpos.le hγ.le) (Work.Spaces.HkSq_nonneg α 4 f)
  have hK3sqrt : Real.sqrt (CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      = Real.sqrt CK / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [show Work.Spaces.HkNorm α 4 f = Real.sqrt (Work.Spaces.HkSq α 4 f) from rfl]
    rw [← Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [Real.sqrt_mul (div_nonneg hCKpos.le hγ.le), Real.sqrt_mul_self (Real.sqrt_nonneg _),
      Real.sqrt_div hCKpos.le]
  -- ### nonnegativity of `Kf` and `Kg`
  have hKf0 : (0 : ℝ) ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg (div_nonneg hC1pos.le hs0.le) hF0
  have hKg0 : (0 : ℝ) ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g :=
    mul_nonneg (div_nonneg hC1pos.le hs0.le) hG0
  -- ### the open-class assembly
  obtain ⟨hEM_int, hEM_le⟩ :=
    HonestEasyMajorAux.AssemblyQ_o α f g
      (C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f)
      (C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g)
      (CK / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      hα hα1 hf hg hdecg hmf hmg hKf hKg hGint hGle hKf0 hKg0 hK30
  refine ⟨hEM_int, hEM_le.trans (le_of_eq ?_)⟩
  rw [Work.FTS.H2.TTot, hK3sqrt, ← Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g),
    show Work.Spaces.HkNorm α 4 g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl]
  ring

end Work.FTS.StrongPersist.N6Trans
