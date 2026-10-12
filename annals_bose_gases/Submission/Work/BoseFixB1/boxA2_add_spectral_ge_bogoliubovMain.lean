import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1.perBoxF_pieces
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxA2_add_spectral_ge_bogoliubovMain`

**VERDICT (this session): the frozen target is FALSE as written** — see
`FINDING_boxA2_add_spectral_Verdict.md`.  The file keeps the frozen statement (with its `sorry`) and
proves, axiom-clean, the surrounding bookkeeping and *both* directions of the reduction:

* the homogeneity of the five box words (`bFlat_mul` … `bA2_mul`) and the sign facts
  (`bFlat_nonneg`, `bQ_nonneg`, `bI_nonneg`, `bV_nonneg`, `core_signs`);
* `boxA2_eq_twoMean`, `def BoxA2Core`, `def boxStateScale`;
* `boxA2_add_spectral_ge_bogoliubovMain_of_core : BoxA2Core v h → (target)`;
* `BoxA2Core_of_main : (target) → BoxA2Core v h`,

so **target ⟺ `BoxA2Core`** is machine-checked.

Every box word occurring in the target (`bFlat`, `bQ`, `bI`, `bSpectral`, `bA2`) is a **quadratic
form** in the state, and the target's two sides differ by

    α + β,  α = (1/2)(1+η)·g0w0Mass·S²·chiMass/V² + C·a·(S/V)·Q   (≥ 0 automatically),
            β = (1/2)(1+η)·g0w0Mass·S·chiMass/V² + bSpectral + bA2 + C·a·μ·(Q + I),

so the target is equivalent to `β ≥ 0` for all admissible states — the core.  Because `α ≥ 0` is
*annihilated* by rescaling the state (`Φ ↦ t·Φ`), the statement's content is only the *linear-in-`S`*
half of the payer, and that half is missing the **particle-number** factor of FS's sharp
`lm:appbogolubov` (`(n+1)n/|B|²`); the product states `Φ = ∏(ū+ψ)` with `θ = ⟨ψ,w₁ψ⟩ < 0` therefore
refute the target for large `n` (see the FINDING, §2–§3).
-/

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma boxPInd_mul (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (i : Fin N) (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    UBBInputs8.boxPInd volA A i (fun x => t * Φ x)
      = fun x => t * UBBInputs8.boxPInd volA A i Φ x := by
  funext x
  unfold UBBInputs8.boxPInd
  have h : (∫ z in A, t * Φ (Function.update x i z))
      = t * ∫ z in A, Φ (Function.update x i z) :=
    MeasureTheory.integral_const_mul t (fun z => Φ (Function.update x i z))
  rw [h]
  ring

lemma boxQInd_mul (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (i : Fin N) (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    UBBInputs8.boxQInd volA A i (fun x => t * Φ x)
      = fun x => t * UBBInputs8.boxQInd volA A i Φ x := by
  funext x
  unfold UBBInputs8.boxQInd
  rw [congrFun (boxPInd_mul volA i t Φ) x]
  ring

lemma boxFlatCount_mul (volA ℓ : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
  unfold Work.BoseFixB1S.boxFlatCount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpt : (fun x => (UBBInputs8.boxPInd volA A i (fun x => t * Φ x) x) ^ 2)
      = fun x => t ^ 2 * (UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
    funext x
    rw [congrFun (boxPInd_mul volA i t Φ) x]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]

lemma boxQCount_mul (volA ℓ : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1S.boxQCount volA ℓ A (fun x => t * Φ x)
      = t ^ 2 * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  unfold Work.BoseFixB1S.boxQCount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpt : (fun x => (UBBInputs8.boxQInd volA A i (fun x => t * Φ x) x) ^ 2)
      = fun x => t ^ 2 * (UBBInputs8.boxQInd volA A i Φ x) ^ 2 := by
    funext x
    rw [congrFun (boxQInd_mul volA i t Φ) x]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]

lemma boxA2_mul (ℓ volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ} (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    boxA2 ℓ volA A w1 (fun x => t * Φ x) = t ^ 2 * boxA2 ℓ volA A w1 Φ := by
  unfold boxA2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : UBBInputs8.boxPInd volA A p.1
        (UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x))
      = fun x => t * UBBInputs8.boxPInd volA A p.1
          (UBBInputs8.boxPInd volA A p.2 Φ) x := by
    rw [boxPInd_mul volA p.2 t Φ]
    exact boxPInd_mul volA p.1 t (UBBInputs8.boxPInd volA A p.2 Φ)
  have h2 : UBBInputs8.boxQInd volA A p.2
        (UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x))
      = fun x => t * UBBInputs8.boxQInd volA A p.2
          (UBBInputs8.boxQInd volA A p.1 Φ) x := by
    rw [boxQInd_mul volA p.1 t Φ]
    exact boxQInd_mul volA p.2 t (UBBInputs8.boxQInd volA A p.1 Φ)
  have hpt : (fun x => (UBBInputs8.boxPInd volA A p.1
          (UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x)) x
        * UBBInputs8.boxQInd volA A p.2
            (UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x)) x)
          * w1 (x p.1) (x p.2))
      = fun x => t ^ 2 * ((UBBInputs8.boxPInd volA A p.1
            (UBBInputs8.boxPInd volA A p.2 Φ) x
          * UBBInputs8.boxQInd volA A p.2
              (UBBInputs8.boxQInd volA A p.1 Φ) x) * w1 (x p.1) (x p.2)) := by
    funext x
    rw [congrFun h1 x, congrFun h2 x]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]

lemma tBamp_mul (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) {N : ℕ} (i : Fin N) (t : ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.SmallBoxTBWord.tBamp χ p (fun y => t * Ψ y) i x
      = (t : ℂ) * Work.SmallBoxTBWord.tBamp χ p Ψ i x := by
  unfold Work.SmallBoxTBWord.tBamp
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  push_cast
  ring

lemma sqIntegral_mul (ℓ : ℝ) {N : ℕ} (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (t * Φ x) ^ 2)
      = t ^ 2 * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  have hpt : (fun x => (t * Φ x) ^ 2) = fun x => t ^ 2 * (Φ x) ^ 2 := by
    funext x; ring
  rw [hpt, MeasureTheory.integral_const_mul]

lemma tBamp_normSq_mul (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3))
    {N : ℕ} (i : Fin N) (t : ℝ) (Ψ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    ‖Work.SmallBoxTBWord.tBamp χ p (fun y => t * Ψ y) i x‖ ^ 2
      = t ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ^ 2 := by
  rw [tBamp_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma tBwordKinInd_mul (ℓ : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} (volA : ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (c : ℝ) {N : ℕ} (t : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    UBBInputs8.tBwordKinInd ℓ A volA χ c (fun x => t * Φ x)
      = t ^ 2 * UBBInputs8.tBwordKinInd ℓ A volA χ c Φ := by
  unfold UBBInputs8.tBwordKinInd UBBInputs8.tBdiagFormInd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstep : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (UBBInputs8.boxQInd volA A i (fun x => t * Φ x)) i x‖ ^ 2))
        = t ^ 2 * (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
              ‖Work.SmallBoxTBWord.tBamp χ p (UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2))) := by
    intro p
    have hpt : (fun x => ‖Work.SmallBoxTBWord.tBamp χ p
          (UBBInputs8.boxQInd volA A i (fun x => t * Φ x)) i x‖ ^ 2)
        = fun x => t ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p
            (UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2 := by
      funext x
      rw [boxQInd_mul volA i t Φ,
        tBamp_mul χ p i t (UBBInputs8.boxQInd volA A i Φ) x,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hpt, MeasureTheory.integral_const_mul]
    ring
  rw [show (∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (UBBInputs8.boxQInd volA A i (fun x => t * Φ x)) i x‖ ^ 2)))
      = ∫ p : EuclideanSpace ℝ (Fin 3), t ^ 2 *
          (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
              ‖Work.SmallBoxTBWord.tBamp χ p (UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2)))
      from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep)]
  rw [MeasureTheory.integral_const_mul]
  ring


/-! ## 2. The homogeneity of the *named* per-box words of the target -/

lemma bFlat_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ t : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    bFlat v μ (fun x => t * Φ x) u = t ^ 2 * bFlat v μ Φ u :=
  boxFlatCount_mul (bV v μ u) (bSide v μ) (A := bA v μ u) t Φ

lemma bQ_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ t : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    bQ v μ (fun x => t * Φ x) u = t ^ 2 * bQ v μ Φ u :=
  boxQCount_mul (bV v μ u) (bSide v μ) (A := bA v μ u) t Φ

lemma bI_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ t : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    bI v μ (fun x => t * Φ x) = t ^ 2 * bI v μ Φ :=
  sqIntegral_mul (bSide v μ) t Φ

lemma bSpectral_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ t : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    bSpectral v μ (fun x => t * Φ x) u = t ^ 2 * bSpectral v μ Φ u :=
  tBwordKinInd_mul (bSide v μ) (A := bA v μ u) (bV v μ u)
    (Submission.BoseGases.chiB (bSide v μ) (bD v μ) u) (sbCut μ (_root_.BoseGases.a v)) t Φ

lemma bA2_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ t : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    bA2 v h μ (fun x => t * Φ x) u = t ^ 2 * bA2 v h μ Φ u :=
  boxA2_mul (bSide v μ) (bV v μ u) (A := bA v μ u)
    (Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u) t Φ

/-! ## 2b. The pairing's exact form at the box projections -/

/-- **The box pairing word in mean form.**  For `p = (i,j) ∈ pairSet n` the `P`-factor of
`boxA2` is the indicator-carried two-slot mean `Aind A (x i)·Aind A (x j)·twoMean volA A i j Φ`
(the corpus's `Work.BoseFixB1S.boxPInd_twoMean`), so `boxA2` is the sum of the two-fold
fluctuation against that mean. -/
theorem boxA2_eq_twoMean {n : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X n → ℝ} :
    boxA2 ℓ volA A w1 Φ
      = ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1S.Aind A (x p.1) * Work.BoseFixB1S.Aind A (x p.2)
              * Work.BoseFixB1S.twoMean volA A p.1 p.2 Φ x)
            * (UBBInputs8.boxQInd volA A p.2 (UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w1 (x p.1) (x p.2) := by
  unfold boxA2
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [Work.BoseFixB1S.boxPInd_twoMean volA A hpne Φ x]

/-! ## 3. Sign facts -/

lemma bFlat_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ bFlat v μ Φ u := by
  unfold bFlat Work.BoseFixB1S.boxFlatCount
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

lemma bQ_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ bQ v μ Φ u := by
  unfold bQ Work.BoseFixB1S.boxQCount
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

lemma bI_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ bI v μ Φ := by
  unfold bI
  exact integral_nonneg fun x => sq_nonneg _

/-! ## 4. The quadratic core and the reduction -/

/-- **The quadratic core of the target.**  The two sides of the target differ by `α + β`, where
`α ≥ 0` holds automatically (a square times the `χ`-mass, plus `C·a·(S/V)·Q`), so by the
*quadratic homogeneity* of all five box words the target is equivalent to `β ≥ 0` on all
states — this is `BoxA2Core`. -/
def BoxA2Core (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (bSide v μ) (bD v μ) μ →
        0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
                  / (bV v μ u) ^ 2)
            + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    + μ * bI v μ (Φ : Submission.BoseGases.X n → ℝ))

/-- Scaling a box state by a nonzero scalar (smoothness, symmetry and nonvanishing are all
scale-invariant). -/
def boxStateScale {n : ℕ} {ℓ : ℝ} (t : ℝ) (ht : t ≠ 0)
    (Φ : Work.BoseKinLoc.BoxState n ℓ) : Work.BoseKinLoc.BoxState n ℓ where
  toFun := fun x => t * Φ x
  contDiff := Φ.contDiff.const_smul t
  symm := by
    intro σ x
    show t * (Φ : Submission.BoseGases.X n → ℝ) (Submission.BoseGases.actPerm n σ x)
      = t * (Φ : Submission.BoseGases.X n → ℝ) x
    rw [Φ.symm σ x]
  nezero := by
    intro hzero
    obtain ⟨x, hx⟩ := Function.ne_iff.mp Φ.nezero
    have h0 := congrFun hzero x
    simp only [Pi.zero_apply, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact ht h0
    · exact hx h0

/-- The box volume is nonnegative. -/
lemma bV_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : 0 ≤ bV v μ u := by
  classical
  unfold bV Work.SmallBoxSliding.boxMass Work.SmallBoxSliding.boxInd
  exact integral_nonneg fun x => by
    rw [Set.indicator_apply]
    split <;> norm_num

/-- The pairing's quadratic core and the sign facts it consumes. -/
lemma core_signs (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ bV v μ u ∧ 0 ≤ bFlat v μ Φ u ∧ 0 ≤ bQ v μ Φ u ∧ 0 ≤ bI v μ Φ
      ∧ 0 ≤ Submission.BoseGases.g0w0Mass h
      ∧ 0 ≤ Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
      ∧ 0 ≤ _root_.BoseGases.a v :=
  ⟨bV_nonneg v μ u, bFlat_nonneg v μ Φ u, bQ_nonneg v μ Φ u, bI_nonneg v μ Φ,
    Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h,
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _, le_of_lt hav⟩

/-- **The quadratic core implies the target**: the target's two sides differ by `α + β` with
`α ≥ 0` automatic (sign facts) and `β ≥ 0` the core's content. -/
theorem boxA2_add_spectral_ge_bogoliubovMain_of_core {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    BoxA2Core v h →
      ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
            (u : EuclideanSpace ℝ (Fin 3)),
            u ∈ Work.SmallBoxSliding.goodSet (bSide v μ) (bD v μ) μ →
            - (C * (_root_.BoseGases.a v)
                  * (μ + bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
                  * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              - C * (_root_.BoseGases.a v) * μ
                  * bI v μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
                * (((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
                      * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                    / (bV v μ u) ^ 2)
                * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
              + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
              + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u := by
  rintro ⟨ε₀, η, C, hε, hη, hC, Hcore⟩
  refine ⟨ε₀, η, C, hε, hη, hC, fun μ hAdm n Φ u hgood => ?_⟩
  have hVnn : 0 ≤ bV v μ u := bV_nonneg v μ u
  have hSnn : 0 ≤ bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u :=
    bFlat_nonneg v μ _ u
  have hQnn : 0 ≤ bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := bQ_nonneg v μ _ u
  have hDnn : 0 ≤ Submission.BoseGases.g0w0Mass h :=
    Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h
  have hXnn : 0 ≤ Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hann : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hcore := Hcore μ hAdm n Φ u hgood
  have hαnn : 0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
        * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
              * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            / (bV v μ u) ^ 2)
      * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
      + C * (_root_.BoseGases.a v)
          * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
              * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u) := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        hDnn) (div_nonneg (mul_nonneg hSnn hSnn) (sq_nonneg _))) hXnn
    · exact mul_nonneg (mul_nonneg hC hann) (mul_nonneg (div_nonneg hSnn hVnn) hQnn)
  have hsplit : (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
        * (((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
              * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            / (bV v μ u) ^ 2)
        * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
      + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
      + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
      - (- (C * (_root_.BoseGases.a v)
            * (μ + bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
            * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
          - C * (_root_.BoseGases.a v) * μ
              * bI v μ (Φ : Submission.BoseGases.X n → ℝ))
      = ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
            * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                  * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                / (bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
        + C * (_root_.BoseGases.a v)
            * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
                * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u))
      + ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
            * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                  * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
                / (bV v μ u) ^ 2)
          + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
          + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
          + C * (_root_.BoseGases.a v)
              * (μ * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
                  + μ * bI v μ (Φ : Submission.BoseGases.X n → ℝ))) := by
    ring
  linarith [hcore, hαnn, hsplit]

/-- **The target implies the core** (the scaling direction of the reduction): by the quadratic
homogeneity of the five box words, the target's difference at the scaled state `t·Φ` is
`t⁴·A(Φ) + t²·B(Φ)`, with `A ≥ 0` automatic; so if `B(Φ) < 0` the target's inequality fails at
`t·Φ` for small `t ∈ (0,1]`.  Hence the target and the core are *equivalent*. -/
theorem BoxA2Core_of_main {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    (∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (bSide v μ) (bD v μ) μ →
          - (C * (_root_.BoseGases.a v)
                * (μ + bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
                * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              - C * (_root_.BoseGases.a v) * μ
                  * bI v μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
                * (((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
                      * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                    / (bV v μ u) ^ 2)
                * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
              + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
              + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u) → BoxA2Core v h := by
  -- The target's difference at the scaled state `t·Φ` is `t^4·A(Φ) + t^2·B(Φ)` with
  -- `A ≥ 0` (all its factors are nonnegative) and `B` the core's expression; since the target
  -- holds at `t·Φ` for every `t ∈ (0,1]`, the `t ↓ 0` limit gives `B(Φ) ≥ 0`.
  rintro ⟨ε₀, η, C, hε, hη, hC, Hmain⟩
  have key : ∀ A B : ℝ, 0 ≤ A →
      (∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t ^ 4 * A + t ^ 2 * B) → 0 ≤ B := by
    intro A B hA h
    by_contra hB
    rw [not_le] at hB
    have hu : 0 < -B / (2 * (A + 1)) := div_pos (by linarith) (by linarith)
    have hb2 : 0 < -B / 2 := by linarith
    have ht : 0 < min 1 (-B / (2 * (A + 1))) := lt_min one_pos hu
    have ht1 : min 1 (-B / (2 * (A + 1))) ≤ 1 := min_le_left _ _
    have hkey := h _ ht ht1
    have hstep : (min 1 (-B / (2 * (A + 1)))) ^ 2 * (A + 1) ≤ -B / 2 := by
      rcases lt_or_ge (-B / (2 * (A + 1))) 1 with h1 | h1
      · rw [min_eq_right (le_of_lt h1)]
        have h3 : (-B / (2 * (A + 1))) * (A + 1) = -B / 2 := by field_simp
        have h4 : (-B / (2 * (A + 1))) * ((-B / (2 * (A + 1))) * (A + 1)) ≤ 1 * (-B / 2) := by
          rw [h3]
          exact mul_le_mul_of_nonneg_right (le_of_lt h1) (le_of_lt hb2)
        nlinarith [h4]
      · rw [min_eq_left h1]
        have h3 : (-B / (2 * (A + 1))) * (2 * (A + 1)) = -B := by field_simp
        have h4 : 2 * (A + 1) ≤ (-B / (2 * (A + 1))) * (2 * (A + 1)) := by
          have h5 : 1 * (2 * (A + 1)) ≤ (-B / (2 * (A + 1))) * (2 * (A + 1)) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
          simpa using h5
        rw [h3] at h4
        nlinarith
    have hA2 : (min 1 (-B / (2 * (A + 1)))) ^ 2 * A ≤ -B / 2 := by nlinarith [hstep]
    have hneg : (min 1 (-B / (2 * (A + 1)))) ^ 2
        * ((min 1 (-B / (2 * (A + 1)))) ^ 2 * A + B) < 0 :=
      mul_neg_of_pos_of_neg (pow_pos ht 2) (by linarith)
    nlinarith [hkey]
  refine ⟨ε₀, η, C, hε, hη, hC, fun μ hAdm n Φ u hgood => ?_⟩
  have hVnn : 0 ≤ bV v μ u := bV_nonneg v μ u
  have hSnn : 0 ≤ bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u := bFlat_nonneg v μ _ u
  have hQnn : 0 ≤ bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := bQ_nonneg v μ _ u
  have hDnn : 0 ≤ Submission.BoseGases.g0w0Mass h :=
    Work.SmallBoxA0.g0w0Mass_nonneg_general hR hv_supp h
  have hXnn : 0 ≤ Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hann : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  refine key
    ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
        * (((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
              * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
          / (bV v μ u) ^ 2)
      + C * (_root_.BoseGases.a v)
          * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
              * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u))
    ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
          * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
              / (bV v μ u) ^ 2)
        + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
        + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
        + C * (_root_.BoseGases.a v)
            * (μ * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
                + μ * bI v μ (Φ : Submission.BoseGases.X n → ℝ)))
    ?_ ?_
  · refine add_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hDnn)
        (div_nonneg (mul_nonneg (mul_nonneg hSnn hSnn) hXnn) (sq_nonneg (bV v μ u)))
    · exact mul_nonneg (mul_nonneg hC hann) (mul_nonneg (div_nonneg hSnn hVnn) hQnn)
  · intro t ht0 ht1
    have ht : t ≠ 0 := ne_of_gt ht0
    have hSsc : bFlat v μ (((boxStateScale t ht Φ :
        Work.BoseKinLoc.BoxState n (bSide v μ)) : Submission.BoseGases.X n → ℝ)) u
        = t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      show bFlat v μ (fun x => t * (Φ : Submission.BoseGases.X n → ℝ) x) u = _
      exact bFlat_mul v μ t (Φ : Submission.BoseGases.X n → ℝ) u
    have hQsc : bQ v μ (((boxStateScale t ht Φ :
        Work.BoseKinLoc.BoxState n (bSide v μ)) : Submission.BoseGases.X n → ℝ)) u
        = t ^ 2 * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      show bQ v μ (fun x => t * (Φ : Submission.BoseGases.X n → ℝ) x) u = _
      exact bQ_mul v μ t (Φ : Submission.BoseGases.X n → ℝ) u
    have hIsc : bI v μ (((boxStateScale t ht Φ :
        Work.BoseKinLoc.BoxState n (bSide v μ)) : Submission.BoseGases.X n → ℝ))
        = t ^ 2 * bI v μ (Φ : Submission.BoseGases.X n → ℝ) := by
      show bI v μ (fun x => t * (Φ : Submission.BoseGases.X n → ℝ) x) = _
      exact bI_mul v μ t (Φ : Submission.BoseGases.X n → ℝ)
    have hKsc : bSpectral v μ (((boxStateScale t ht Φ :
        Work.BoseKinLoc.BoxState n (bSide v μ)) : Submission.BoseGases.X n → ℝ)) u
        = t ^ 2 * bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      show bSpectral v μ (fun x => t * (Φ : Submission.BoseGases.X n → ℝ) x) u = _
      exact bSpectral_mul v μ t (Φ : Submission.BoseGases.X n → ℝ) u
    have hAsc : bA2 v h μ (((boxStateScale t ht Φ :
        Work.BoseKinLoc.BoxState n (bSide v μ)) : Submission.BoseGases.X n → ℝ)) u
        = t ^ 2 * bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      show bA2 v h μ (fun x => t * (Φ : Submission.BoseGases.X n → ℝ) x) u = _
      exact bA2_mul v h μ t (Φ : Submission.BoseGases.X n → ℝ) u
    have hmain := Hmain μ hAdm n (boxStateScale t ht Φ) u hgood
    rw [hSsc, hQsc, hIsc, hKsc, hAsc] at hmain
    have hba : 0 ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
          * (((t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
                * (t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u))
              / (bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
        + t ^ 2 * bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
        + t ^ 2 * bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
        + C * (_root_.BoseGases.a v)
            * (μ + (t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u) / bV v μ u)
            * (t ^ 2 * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
        + C * (_root_.BoseGases.a v) * μ
            * (t ^ 2 * bI v μ (Φ : Submission.BoseGases.X n → ℝ)) := by
      linarith [hmain]
    rw [show (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
          * (((t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
                * (t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u))
              / (bV v μ u) ^ 2)
          * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
        + t ^ 2 * bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
        + t ^ 2 * bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
        + C * (_root_.BoseGases.a v)
            * (μ + (t ^ 2 * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u) / bV v μ u)
            * (t ^ 2 * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
        + C * (_root_.BoseGases.a v) * μ
            * (t ^ 2 * bI v μ (Φ : Submission.BoseGases.X n → ℝ))
        = t ^ 4 * ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * (((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    * bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                  * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
                / (bV v μ u) ^ 2)
            + C * (_root_.BoseGases.a v)
                * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u / bV v μ u)
                    * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u))
          + t ^ 2 * ((1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * ((bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u)
                  / (bV v μ u) ^ 2)
            + bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            + C * (_root_.BoseGases.a v)
                * (μ * bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    + μ * bI v μ (Φ : Submission.BoseGases.X n → ℝ))) from by ring] at hba
    exact hba

/-- **The main target** (statement frozen by the requester): the pairing `boxA2` together with
the spectral half dominates the negative of the error bracket, at the cost of the Bogoliubov main
term `(1/2)(1+η)·g0w0Mass·((S+1)S/V²)·chiMass`.

**THIS STATEMENT IS FALSE AS WRITTEN** — see `FINDING_boxA2_add_spectral_Verdict.md`.  Its content is
equivalent (machine-checked: `BoxA2Core_of_main` + `_of_core`) to the *linear*-in-`S` bound
`bSpectral + bA2 ≥ −(1/2)(1+η)·g0w0Mass·S·chiMass/V² − C·a·μ·(Q+I)`, whose payer is missing the
**particle-number** factor that FS's sharp `lm:appbogolubov` carries (`(n+1)n/|B|²`; the corpus's
proved D1 renderings carry `d4MassCoeff (N+1) s`).  The product states `Φ = ∏(ū+ψ)` with
`θ = ⟨ψ,w₁ψ⟩ < 0` (available: the flat-bump `g₀` model has `ĝ₀(p) < 0` on `pR ∈ (4.49,7.72)`) refute
it for large `n`, since `bA2` grows like `n²` while every payer is at most `n`-linear.  Faithful
repairs: restore the particle-number factor in the payer (`(n+1)·bFlat` in place of `(S+1)·bFlat`),
or window `n`. -/
theorem boxA2_add_spectral_ge_bogoliubovMain {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ η C : ℝ, 0 < ε₀ ∧ 0 ≤ η ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          - (C * (_root_.BoseGases.a v)
                * (μ + Work.BoseFixB1.bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            - C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 2) * (1 + η) * Submission.BoseGases.g0w0Mass h
              * (((Work.BoseFixB1.bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u + 1)
                    * Work.BoseFixB1.bFlat v μ (Φ : Submission.BoseGases.X n → ℝ) u)
                  / (Work.BoseFixB1.bV v μ u) ^ 2)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            + Work.BoseFixB1.bSpectral v μ (Φ : Submission.BoseGases.X n → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u := by
  sorry

end Work.BoseFixB1
