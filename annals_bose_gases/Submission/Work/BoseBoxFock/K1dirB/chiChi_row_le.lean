import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1dirB.chiChi_eq_split
import Submission.Work.BoseBoxFock.K1dirB.cubeRow_tail_le
import Submission.Work.BoseBoxFock.K1dirB.finiteRow_pairing_eq
import Submission.Work.BoseBoxFock.err_aesm_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.chiChi_row_le` — the `χχ` row of the `K1exp − K1lim` pairing bound

The target bounds the box-squared pairing of the `χχ` row error `k1ErrA` against the weighted
test kernel `k1H ℓ G = ℓ⁻³ χ(w)χ(y)G(w,y)` by the Coulomb tail data `τa`, `τb` and the Dirichlet
energy `D` of the test kernel.

## Route

`k1ErrA = pinQA(k1cfun) − latPer3 ℓ (Wa + Wb)` is the difference of a *finite* lattice row and a
*periodisation*, and each of the two pieces is evaluated by one of the two proved engines:

* the periodisation piece is the target of `L1Tails.kernelTail` (the `L¹`-tail engine, which gives
  the sharp `2√(τ ℓ⁹ D)` bound against the Coulomb tail of a *single* weight, here `Wa + Wb`);
* the finite row is reduced to the lattice sample sum `Σ_n F n · hPair ℓ H n` by
  `K1dirB.finiteRow_pairing_eq` (the finite Fubini/support swap), and the remaining annulus sum is
  bounded by the Cauchy–Schwarz engine `L1Tails.tail_cs` with the Coulomb tail of `Wb`
  (`K1dirB.cubeRow_tail_le`).

The only bookkeeping left in this file is the split of the pairing (`K1dirB.chiChi_eq_split`), the
identification of the `pinQA` row with the cube-`N` coefficient row (`pinQA_eq_cubeRow`), and the
coefficient algebra `χ̂ = k̂` of the two even weights plus the linearity of the Fourier transform.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. Elementary helpers -/

/-- The real coefficient of the row `pinQA v μ N (k1cfun fu Wa Wb ℓ N)`, indexed by the lattice
labels `n : Fin 3 → ℤ` (its `Lab N`-restriction is `k1cfun`). -/
noncomputable def chiRowCoeff (fu : Work.BoseBoxFix.LowCut) (Wa Wb : E3 → ℝ) (ℓ : ℝ) (N : ℕ)
    (n : Fin 3 → ℤ) : ℝ :=
  uvCut fu (uvRad ℓ N) (kmomInt ℓ n) * Work.BoseFixR.chat Wa (kmomInt ℓ n)
    + Work.BoseFixR.chat Wb (kmomInt ℓ n)

/-- The sum over the cube `cube N` of lattice labels is the sum over the labels `Lab N`. -/
lemma sum_cube_eq_sum_lab (N : ℕ) (g : (Fin 3 → ℤ) → ℂ) :
    (∑ n ∈ Work.BoseRowQ2.cube N, g n) = ∑ k : Lab N, g (labVec N k) := by
  rw [← Work.BoseRowQ2.image_labVec_eq_cube, Finset.sum_image]
  intro a _ b _ h
  exact Work.BoseRowQ2.labVec_inj' N h

/-- `pinQA` at `k1cfun` is the cube-`N` row of the coefficients `chiRowCoeff`. -/
lemma pinQA_eq_cubeRow {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (N : ℕ) (z : E3) :
    pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z
      = ∑ n ∈ Work.BoseRowQ2.cube N,
          ((chiRowCoeff fu Wa Wb (ellH v μ) N n : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt (ellH v μ) n) z : ℝ) : ℂ)) := by
  rw [Work.BoseBoxFock.pinQA]
  rw [sum_cube_eq_sum_lab]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1

/-- A double integral over the box of a kernel vanishing off the box is the full-space integral. -/
lemma boxDouble_eq_full {ℓ : ℝ} {f : E3 → E3 → ℂ}
    (hf1 : ∀ w y, w ∉ Work.BoseK15.corpusBox.boxL ℓ → f w y = 0)
    (hf2 : ∀ w y, y ∉ Work.BoseK15.corpusBox.boxL ℓ → f w y = 0) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y)
      = ∫ w, ∫ y, f w y := by
  have hs : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hinner : ∀ w, (∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y) = ∫ y, f w y := by
    intro w
    rw [← MeasureTheory.integral_indicator hs (f := fun y => f w y)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hf2 w y hy])
  calc (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y, f w y :=
        MeasureTheory.setIntegral_congr_fun hs fun w _ => hinner w
    _ = ∫ w, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun w => ∫ y, f w y) w := by
        rw [MeasureTheory.integral_indicator hs]
    _ = ∫ w, ∫ y, f w y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ
        · rw [Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem hw]
          simp only [hf1 w _ hw, integral_zero]

/-- Multiplication of an integrable function by the unit-modulus phase `e^{−i⟪p,y⟫}` is again
integrable. -/
lemma integrable_kinFT_phase_mul {u : E3 → ℂ} (hu : MeasureTheory.Integrable u) (p : E3) :
    MeasureTheory.Integrable
      (fun y : E3 => Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * u y) := by
  refine hu.bdd_mul (c := 1) (Continuous.aestronglyMeasurable ?_) (Filter.Eventually.of_forall (fun y => ?_))
  · fun_prop
  · rw [Complex.norm_exp]
    simp [Complex.neg_re, Complex.mul_re]

/-- The complexification of an integrable real function is integrable. -/
lemma integrable_ofReal {W : E3 → ℝ} (hW : MeasureTheory.Integrable W) :
    MeasureTheory.Integrable (fun y : E3 => ((W y : ℝ) : ℂ)) := by
  refine hW.norm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hW.aestronglyMeasurable
  · simp

/-- `kinFT` is additive on coercions of real functions. -/
lemma kinFT_add_coe {Wa Wb : E3 → ℝ} (hWai : MeasureTheory.Integrable Wa)
    (hWbi : MeasureTheory.Integrable Wb) (p : E3) :
    Submission.BoseGases.kinFT (fun y => (((Wa y + Wb y : ℝ)) : ℂ)) p
      = Submission.BoseGases.kinFT (fun y => ((Wa y : ℝ) : ℂ)) p
        + Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ)) p := by
  have h1 : MeasureTheory.Integrable (fun y : E3 => ((Wa y : ℝ) : ℂ)) volume :=
    integrable_ofReal hWai
  have h2 : MeasureTheory.Integrable (fun y : E3 => ((Wb y : ℝ) : ℂ)) volume :=
    integrable_ofReal hWbi
  simp only [Submission.BoseGases.kinFT]
  rw [← MeasureTheory.integral_add (integrable_kinFT_phase_mul h1 p)
    (integrable_kinFT_phase_mul h2 p)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

/-- The `pinQA` row is uniformly bounded. -/
lemma pinQA_row_bdd {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (N : ℕ) :
    ∃ B : ℝ, ∀ z : E3, ‖pinQA v μ N (k1cfun fu Wa Wb (ellH v μ) N) z‖ ≤ B := by
  refine ⟨∑ k : Lab N, |k1cfun fu Wa Wb (ellH v μ) N k|, fun z => ?_⟩
  rw [Work.BoseBoxFock.pinQA]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul]
  have he : ‖Complex.exp (Complex.I *
      ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [he, mul_one]
  simp

/-- The `uvCut` of the ultraviolet radius equals one below the radius. -/
lemma uvCut_uvRad_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) {N : ℕ}
    (hN : 1 ≤ N) {k : E3} (hk : ‖k‖ < uvRad ℓ N) :
    uvCut fu (uvRad ℓ N) k = 1 := by
  have hv : 0 < uvRad ℓ N := by rw [uvRad]; positivity
  rw [uvCut]
  exact fu.one _ ((div_le_one hv).mpr hk.le)

/-- `uvCut` lies in `[0,1]`. -/
lemma uvCut_mem (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (k : E3) :
    0 ≤ uvCut fu (uvRad ℓ N) k ∧ uvCut fu (uvRad ℓ N) k ≤ 1 :=
  ⟨by rw [uvCut]; exact fu.nonneg _, by rw [uvCut]; exact fu.le_one _⟩

/-! ## 2. The target -/

theorem chiChi_row_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ R : ℝ}
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWai : MeasureTheory.Integrable Wa) (hWbi : MeasureTheory.Integrable Wb)
    (hWae : ∀ z, Wa (-z) = Wa z) (hWbe : ∀ z, Wb (-z) = Wb z)
    (hWas : ∀ x, R ≤ ‖x‖ → Wa x = 0) (hWbs : ∀ x, R ≤ ‖x‖ → Wb x = 0)
    (fu : Work.BoseBoxFix.LowCut) {N : ℕ} (hN : 1 ≤ N)
    {Λ τa τb : ℝ} (hΛ : Λ ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
    (hτa : ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖) →
      ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ * ∑ n ∈ S,
        ‖Submission.BoseGases.kinFT (fun y => (((Wa y + Wb y : ℝ)) : ℂ))
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)‖ ^ 2
          / ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖ ^ 2 ≤ τa)
    (hτb : ∀ S : Finset (Fin 3 → ℤ),
      (∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖) →
      ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ * ∑ n ∈ S,
        ‖Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)‖ ^ 2
          / ‖Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n‖ ^ 2 ≤ τb)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    let D : ℝ := ∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.k1H (Work.BoseBoxFock.ellH v μ) G w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
    ‖∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
        ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          Work.BoseBoxFock.k1ErrA v μ fu N Wa Wb (w - y)
            * Work.BoseBoxFock.K1dirB.k1H (Work.BoseBoxFock.ellH v μ) G w y‖
      ≤ 2 * Real.sqrt (τa * (Work.BoseBoxFock.ellH v μ) ^ 9 * D)
        + Real.sqrt (τb * (Work.BoseBoxFock.ellH v μ) ^ 3)
            * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 6 * D) := by
  -- ## 0. notation and elementary facts about the box and the kernel
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hℓne : Work.BoseBoxFock.ellH v μ ≠ 0 := ne_of_gt hℓ
  have hNn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have huvRad : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by
    rw [Work.BoseBoxFock.uvRad]; positivity
  set H : E3 → E3 → ℂ := Work.BoseBoxFock.K1dirB.k1H (Work.BoseBoxFock.ellH v μ) G with hHdef
  have hHcd : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H) :=
    Work.BoseBoxFock.K1dirB.k1H_contDiff hℓne hG
  have hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
        ∧ y ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) :=
    fun w y h => Work.BoseBoxFock.K1dirB.k1H_support hℓ h
  have hHw : ∀ w y, w ∉ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) → H w y = 0 :=
    fun w y hw => by by_contra h; exact hw (hHs w y h).1
  have hHy : ∀ w y, y ∉ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) → H w y = 0 :=
    fun w y hy => by by_contra h; exact hy (hHs w y h).2
  -- zeta-reduce the `let D` and name it
  dsimp only
  set D : ℝ := ∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 with hDdef
  -- shorthand for the two lattice sums
  set SU : ℂ := ∑ n ∈ Work.BoseRowQ2.cube N,
      ((uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT (fun y => (((Wa y + Wb y : ℝ)) : ℂ))
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
        * Work.BoseBoxFock.L1Tails.hPair (Work.BoseBoxFock.ellH v μ) H n with hSU
  set SE : ℂ := ∑ n ∈ Work.BoseRowQ2.cube N,
      ((1 - uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
        * Work.BoseBoxFock.L1Tails.hPair (Work.BoseBoxFock.ellH v μ) H n with hSE
  set SR : ℂ := ∑ n ∈ Work.BoseRowQ2.cube N,
      ((chiRowCoeff fu Wa Wb (Work.BoseBoxFock.ellH v μ) N n : ℝ) : ℂ)
        * Work.BoseBoxFock.L1Tails.hPair (Work.BoseBoxFock.ellH v μ) H n with hSR
  -- ## 1. the split of the pairing
  have hsplit :
      (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
            Work.BoseBoxFock.k1ErrA v μ fu N Wa Wb (w - y) * H w y)
        = (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
              ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
                pinQA v μ N (k1cfun fu Wa Wb (Work.BoseBoxFock.ellH v μ) N) (w - y) * H w y)
          - (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
              ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
                Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) (w - y) * H w y) := by
    refine chiChi_eq_split (Wa := Wa) (Wb := Wb) (R := R) hℓ hWai hWbi hWas hWbs hHcd hHs
      (pinQA v μ N (k1cfun fu Wa Wb (Work.BoseBoxFock.ellH v μ) N))
      (Work.BoseBoxFock.errBdd_pinQA_cont _) ?_ 
    exact pinQA_row_bdd fu N
  -- ## 2. the `pinQA` row is the cube-`N` sample sum
  have hDA :
      (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
            pinQA v μ N (k1cfun fu Wa Wb (Work.BoseBoxFock.ellH v μ) N) (w - y) * H w y)
        = SR := by
    have hcongr :
        (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
            ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
              pinQA v μ N (k1cfun fu Wa Wb (Work.BoseBoxFock.ellH v μ) N) (w - y) * H w y)
          = ∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
              ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
                (∑ n ∈ Work.BoseRowQ2.cube N,
                    ((chiRowCoeff fu Wa Wb (Work.BoseBoxFock.ellH v μ) N n : ℝ) : ℂ)
                      * Complex.exp (Complex.I *
                          ((inner ℝ (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
                            (w - y) : ℝ) : ℂ))) * H w y := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseK15.corpusBox.boxL_measurableSet _) fun w _ => ?_
      refine MeasureTheory.setIntegral_congr_fun
        (Work.BoseK15.corpusBox.boxL_measurableSet _) fun y _ => ?_
      rw [pinQA_eq_cubeRow]
    rw [hcongr, hSR]
    exact finiteRow_pairing_eq hℓ hHcd hHs (Work.BoseRowQ2.cube N) _
  -- ## 3. the periodisation pairing is the full-space one
  have hDB :
      (∫ w in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ∫ y in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
            Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) (w - y) * H w y)
        = ∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) (w - y)
            * H w y :=
    boxDouble_eq_full (fun w y hw => by rw [hHw w y hw, mul_zero])
      (fun w y hy => by rw [hHy w y hy, mul_zero])
  -- ## 4. the `kernelTail` bound for the periodisation pairing
  have hK :
      ‖(∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) (w - y)
            * H w y) - SU‖ ≤ 2 * Real.sqrt (τa * (Work.BoseBoxFock.ellH v μ) ^ 9 * D) := by
    have h := Work.BoseBoxFock.L1Tails.kernelTail (ℓ := Work.BoseBoxFock.ellH v μ)
      (Λ := Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) (τ := τa) (R := R)
      hℓ huvRad (hWai.add hWbi)
      (fun x hx => by simp only [Pi.add_apply, hWas x hx, hWbs x hx, add_zero])
      (fun S hS => hτa S fun n hn => le_trans hΛ (hS n hn))
      hHcd hHs
      (fun n => ((uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ))
      (fun n => by
        have h1 : uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) ≤ 1 :=
          (uvCut_mem (Work.BoseBoxFock.ellH v μ) fu N
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)).2
        have h0 : (0 : ℝ) ≤ uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) :=
          (uvCut_mem (Work.BoseBoxFock.ellH v μ) fu N
            (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)).1
        rw [show ‖(((uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) : ℝ)) : ℂ)‖
            = |uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)| from by simp,
          abs_of_nonneg h0]
        exact h1)
      (fun n hn => by
        rw [uvCut_uvRad_eq_one hℓ fu hN hn]
        norm_num)
      (Work.BoseRowQ2.cube N)
      (fun n hn => Work.BoseBoxFock.K1dirB.mem_cube_of_lt_uvRad hℓ hn)
    rw [hSU]
    simpa only [hDdef, Work.BoseBoxFock.L1Tails.hPair, Pi.add_apply] using h
  -- ## 5. the coefficient algebra
  have halg : SR - SU = SE := by
    rw [hSR, hSU, hSE, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : ((chiRowCoeff fu Wa Wb (Work.BoseBoxFock.ellH v μ) N n : ℝ) : ℂ)
        = ((uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT (fun y => ((Wa y : ℝ) : ℂ))
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
          + Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
                (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) := by
      rw [chiRowCoeff]
      push_cast
      rw [chat_eq_kinFT_of_even hWae, chat_eq_kinFT_of_even hWbe]
    have h2 : Submission.BoseGases.kinFT (fun y => (((Wa y + Wb y : ℝ)) : ℂ))
          (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
        = Submission.BoseGases.kinFT (fun y => ((Wa y : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n)
          + Submission.BoseGases.kinFT (fun y => ((Wb y : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) n) :=
      kinFT_add_coe hWai hWbi _
    rw [h1, h2]
    push_cast
    ring
  -- ## 6. the annulus (Coulomb-tail of `Wb`) bound for the remainder
  have hE2 : ‖SE‖ ≤ Real.sqrt (τb * (Work.BoseBoxFock.ellH v μ) ^ 3)
      * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 6 * D) := by
    rw [hSE]
    refine cubeRow_tail_le hℓ fu hN hΛ (fun S hS => hτb S hS) ?_
    intro T
    rw [hDdef]
    exact Work.BoseBoxFock.L1Tails.hPair_tail_sum_le hℓ hHcd hHs T
  -- ## 7. assembly
  rw [hsplit, hDA, hDB]
  calc ‖SR - (∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ) (Wa + Wb) (w - y)
        * H w y)‖
      = ‖(SR - SU) - ((∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Wa + Wb) (w - y) * H w y) - SU)‖ := by
        congr 1
        ring
    _ = ‖SE - ((∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Wa + Wb) (w - y) * H w y) - SU)‖ := by rw [halg]
    _ ≤ ‖SE‖ + ‖(∫ w, ∫ y, Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Wa + Wb) (w - y) * H w y) - SU‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (τb * (Work.BoseBoxFock.ellH v μ) ^ 3)
          * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 6 * D)
        + 2 * Real.sqrt (τa * (Work.BoseBoxFock.ellH v μ) ^ 9 * D) := add_le_add hE2 hK
    _ = 2 * Real.sqrt (τa * (Work.BoseBoxFock.ellH v μ) ^ 9 * D)
        + Real.sqrt (τb * (Work.BoseBoxFock.ellH v μ) ^ 3)
            * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 6 * D) := by ring

end Work.BoseBoxFock.K1dirB
