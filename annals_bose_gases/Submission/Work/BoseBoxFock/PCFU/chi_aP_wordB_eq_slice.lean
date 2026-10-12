import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.wordB_integrable_family
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chi_aP_wordB_eq_slice`

The `d = 0` **slice identity** of the word split.  Plugging the `j`-th coordinate `y` of the state
into `wordB` factors the word into the windowed pair kernel and `wordF`
(`wordB_update_eq` below), so the `j`-slot mean `aP ℓ j (wordB)` reproduces — after the
`χ_ℓ(xᵢ)·ℓ³` versus `ℓ⁶·(1/ℓ³)` bookkeeping — exactly the `χ_ℓ`-slice integral

  `χ_ℓ(xᵢ)·ℓ³·∫_z χ_ℓ(z)·W₁(xᵢ − z)·wordF x z = ℓ⁶·aP ℓ j (wordB) x`.

Both directions are *unconditional*: no measurability or boundedness of `Θ` is needed, because the
only transformations used are

* `∫` over the centred cube `acube ℓ` equals `∫` over `ℝ³` — the factor `χ_ℓ(z) = chiScale ℓ z`
  vanishes off `acube ℓ` (`chiScale_support_le`, `mem_acube_of_norm_le`);
* pulling out the constant `χ_ℓ(xᵢ)` from the integral (`integral_const_mul`).

The complex-valued statement is the image of the real identity under `Complex.ofReal`
(`integral_ofReal` moves the Bochner integral of the cast across the cast).
-/

noncomputable section

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Pointwise factorisation of the word.**  For `i ≠ j`, inserting `y` into the `j`-th coordinate
of the state `x` splits `wordB` into the windowed pair kernel `χ_ℓ(xᵢ)·W₁(xᵢ − y)·χ_ℓ(y)` (i.e. the
`u = 0` localised kernel `wLoc ℓ (g₀ v h) 0` evaluated at `(xᵢ, y)`) times the low-slot factor
`wordF x y`. -/
theorem wordB_update_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut} {ℓ κ : ℝ}
    {Θ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n) (y : E3) :
    wordB v h fc κ ℓ i j Θ (Function.update x j y)
      = Submission.BoseGases.chiScale ℓ (x i) *
        (Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (x i - y)
          * wordF fc κ ℓ i j Θ x y) := by
  have h1 : (Function.update x j y) i = x i := Function.update_of_ne hij y x
  have h2 : (Function.update x j y) j = y := Function.update_self j y x
  simp only [wordB, wordF, h1, h2, Submission.BoseGases.wLoc, Submission.BoseGases.chiU,
    Submission.BoseGases.chiScale, Work.BoseFixR.W1fun, sub_zero]
  ring

theorem chi_aP_wordB_eq_slice {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {fc : Work.BoseBoxFix.LowCut} {ℓ κ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n) :
    ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) *
        (∫ z : EuclideanSpace ℝ (Fin 3),
          ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
            * ((Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ)
            * ((Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z : ℝ) : ℂ))
      = ((ℓ ^ 6 : ℝ) : ℂ) * ((Submission.BoseGases.aP ℓ j
          (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ) x : ℝ) : ℂ) := by
  classical
  -- `χ_ℓ` is supported in the centred cube `acube ℓ`.
  have hmem : ∀ z : E3, Submission.BoseGases.chiScale ℓ z ≠ 0 →
      z ∈ Submission.BoseGases.acube ℓ :=
    fun z hz => Submission.BoseGases.mem_acube_of_norm_le hℓ.le
      (Submission.BoseGases.chiScale_support_le hℓ hz)
  -- the word vanishes off the cube
  have hzero : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
      wordB v h fc κ ℓ i j Θ (Function.update x j z) = 0 := by
    intro z hz
    rw [wordB_update_eq hij h x z]
    have hχ : Submission.BoseGases.chiScale ℓ z = 0 := by
      by_contra hne
      exact hz (hmem z hne)
    rw [hχ]
    ring
  -- ### Step 1: the `j`-slot mean over the cube is the full `χ_ℓ`-slice integral
  have hset : (∫ z in Submission.BoseGases.acube ℓ,
        wordB v h fc κ ℓ i j Θ (Function.update x j z))
      = Submission.BoseGases.chiScale ℓ (x i) * ∫ z : E3,
          Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (x i - z)
            * wordF fc κ ℓ i j Θ x z := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    rw [show (∫ z : E3, wordB v h fc κ ℓ i j Θ (Function.update x j z))
        = ∫ z : E3, Submission.BoseGases.chiScale ℓ (x i) *
            (Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (x i - z)
              * wordF fc κ ℓ i j Θ x z)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
              (fun z => wordB_update_eq hij h x z))]
    rw [MeasureTheory.integral_const_mul]
  -- ### Step 2: the real identity
  have hreal : Submission.BoseGases.chiScale ℓ (x i) * ℓ ^ 3 *
      (∫ z : E3, Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (x i - z)
        * wordF fc κ ℓ i j Θ x z)
      = ℓ ^ 6 * Submission.BoseGases.aP ℓ j (wordB v h fc κ ℓ i j Θ) x := by
    have haP : Submission.BoseGases.aP ℓ j (wordB v h fc κ ℓ i j Θ) x
        = (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ,
            wordB v h fc κ ℓ i j Θ (Function.update x j z) := rfl
    rw [haP, hset]
    have h3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    field_simp
  -- ### Step 3: the complex integral is the cast of the real one
  have hIntC : (∫ z : E3, ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) *
        ((Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ) *
        ((wordF fc κ ℓ i j Θ x z : ℝ) : ℂ))
      = ((∫ z : E3, Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (x i - z)
          * wordF fc κ ℓ i j Θ x z : ℝ) : ℂ) := by
    rw [show (∫ z : E3, ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) *
          ((Work.BoseFixR.W1fun v h ℓ (x i - z) : ℝ) : ℂ) *
          ((wordF fc κ ℓ i j Θ x z : ℝ) : ℂ))
        = ∫ z : E3, ((Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (x i - z)
            * wordF fc κ ℓ i j Θ x z : ℝ) : ℂ)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          push_cast
          ring))]
    exact integral_ofReal
  -- ### Step 4: assemble
  rw [hIntC, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal hreal

end Work.BoseBoxFock.PCFU
