import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiHat_abs_cubeCompl_tail
import Submission.Work.BoseBoxFock.chiHat_sq_cubeCompl_tail
import Submission.Work.BoseBoxFock.chiTailDefs
import Submission.Work.BoseBoxFock.chi_lat1_periodization_mul
import Submission.Work.BoseBoxFock.latticePoisson_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiTail_bound` — the `N^{-K}` decay of the lattice-truncation tails

The truncation tail `chiTail ℓ N x` of `Submission/Work/BoseBoxFock/chiTailDefs.lean` is the
difference between the *ideal* position-space mode `χ_Λ² − θ` of the FS `Q₁` χ-row and the
*truncated* lattice sum `∑_{k : Lab N} χ̂(ℓ k) • Q(e^{ikx}χ_Λ)`.  This file proves the uniform
sup-norm bound

  `‖chiTail ℓ N x‖ ≤ C / (N+1)^K`     for every `K`, uniformly in `ℓ > 0` and `x`,

i.e. FS's "the Fourier coefficients of χ decay faster than any polynomial".

## The structure of the proof

The whole `ℓ`-dependence of `chiTail` is the *scaling* `y = ℓ⁻¹ • x`: with `k_n = kmomLab ℓ N n`
one has `ℓ • k_n = vec (labVec N n)` (independent of `ℓ`), `⟪k_n, x⟫ = ⟪vec (labVec N n), y⟫`,
`chiLam ℓ x = χ y` and `thetaFun ℓ x = thetaFun 1 y`.  Substituting into the definition and
expanding the mode sum gives the **reduced form**

  `chiTail ℓ N x = χ(y)² − θ(y) − χ(y)·P_N(y) + θ(y)·Q_N`,

where `P_N(y) = ∑_{d ∈ cube N} χ̂(vec d) e^{i⟪vec d,y⟫}` (`cubeSum`) and
`Q_N = ∑_{d ∈ cube N} χ̂(vec d)²` (`cubeSq`) are the truncations of the two *continuum* lattice
sums.  Those are evaluated by the classical Poisson/Parseval identities for the corpus bump:

* `perSeries y = ∑_d χ(y + lat1 d) = ∑_n χ̂(vec n) e^{i⟪vec n,y⟫}` (Poisson summation,
  `chi_poisson_lattice`, a corollary of `Work.BoseFixR.poisson_scaled` at `ℓ = 1`);
* `∑_n χ̂(vec n)² = 1` (Parseval, `chiHat_sq_tsum_one`);
* because `χ` is supported in the ball of radius `1/2`, the translates `χ(· + d)` do not overlap
  and `χ(y)·perSeries y = χ(y)²` (`chi_lat1_periodization_mul`).

So the two truncation errors are the *tails* of those rapidly decaying series:
`perSeries y − P_N(y) = ∑_{d ∉ cube N} χ̂(vec d) e^{i⟪vec d,y⟫}` and
`1 − Q_N = ∑_{d ∉ cube N} χ̂(vec d)²`, and both are bounded by `C/(N+1)^K` by the Schwartz
decay of `χ̂` (`chiHat_abs_cubeCompl_tail`, `chiHat_sq_cubeCompl_tail`).
-/

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus bump `χ` (`Submission.BoseGases.chi`), as a real function. -/
def chiR : E3 → ℝ := Submission.BoseGases.chi

/-- The corpus `χ̂` (`= ∫ χ(x)cos⟪p,x⟫ dx`, `corpusBox.hatChi`) as a complex scalar. -/
def chatC (p : E3) : ℂ := ((Work.BoseK15.corpusBox.hatChi p : ℝ) : ℂ)

/-- The box indicator `θ = 1_Λ` at `ℓ = 1`. -/
def thetaB (y : E3) : ℂ := Work.BoseK15.corpusBox.thetaFun 1 y

/-- **The truncated χ-row sum** `P_N(y) = ∑_{d ∈ [-N,N]³} χ̂(vec d) e^{i⟪vec d,y⟫}`. -/
def cubeSum (N : ℕ) (y : E3) : ℂ :=
  ∑ d ∈ Work.BoseRowQ2.cube N, chatC (Work.BoseB4.vec d) *
    Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d) y : ℝ) : ℂ))

/-- **The truncated χ²-row sum** `Q_N = ∑_{d ∈ [-N,N]³} χ̂(vec d)²`. -/
def cubeSq (N : ℕ) : ℝ :=
  ∑ d ∈ Work.BoseRowQ2.cube N, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec d)) ^ 2

/-- The **periodization** of the corpus bump, `∑_d χ(y + d)`. -/
def perSeries (y : E3) : ℂ := ∑' d : Fin 3 → ℤ, ((chiR (y + Work.BoseFixR.lat1 d) : ℝ) : ℂ)

/-- The **continuum** χ-row sum `∑_n χ̂(vec n) e^{i⟪vec n,y⟫}` (the Poisson series). -/
def poisSeries (y : E3) : ℂ :=
  ∑' n : Fin 3 → ℤ, chatC (Work.BoseB4.vec n) *
    Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec n) y : ℝ) : ℂ))

/-- The **tail** of the Poisson series outside the cube `[-N,N]³`. -/
def poisTail (N : ℕ) (y : E3) : ℂ :=
  ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N},
    chatC (Work.BoseB4.vec d.val) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d.val) y : ℝ) : ℂ))

/-! ## 1. The scaling reduction: everything depends on `x` only through `y = ℓ⁻¹ • x` -/

/-- The real inner product with a scaled label is `ℓ`-independent after `x ↦ ℓ⁻¹ • x`. -/
lemma inner_kmomLab_vec {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k : Lab N) (x : E3) :
    (inner ℝ (kmomLab ℓ N k) x : ℝ)
      = (inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) := by
  rw [kmomLab, real_inner_smul_left, real_inner_smul_right, mul_comm]

/-- The box indicator is `ℓ`-independent after `x ↦ ℓ⁻¹ • x`. -/
lemma thetaFun_smul {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) :
    Work.BoseK15.corpusBox.thetaFun ℓ x = thetaB (ℓ⁻¹ • x) := by
  have hmem : (x ∈ Work.BoseK15.corpusBox.boxL ℓ) ↔
      (ℓ⁻¹ • x ∈ Work.BoseK15.corpusBox.boxL 1) := by
    rw [Work.BoseB4.BoxData.boxL, Work.BoseB4.BoxData.boxL, one_smul]
    exact Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ) _ x
  rw [thetaB, Work.BoseB4.BoxData.thetaFun_apply, Work.BoseB4.BoxData.thetaFun_apply]
  exact if_congr hmem rfl rfl

/-- `chiLam ℓ x = χ (ℓ⁻¹ • x)`. -/
lemma chiLam_eq_chiR (ℓ : ℝ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x = chiR (ℓ⁻¹ • x) := rfl

/-! ## 2. The `Lab N` ↔ `cube N` bookkeeping -/

/-- The `Lab N`-indexed sum over `labVec N` is the `cube N`-indexed sum. -/
lemma sum_labVec_eq_cube {M : Type*} [AddCommMonoid M] (N : ℕ) (F : (Fin 3 → ℤ) → M) :
    (∑ k : Lab N, F (labVec N k)) = ∑ d ∈ Work.BoseRowQ2.cube N, F d := by
  rw [← Finset.sum_image (f := F) (Work.BoseRowQ2.labVec_inj' N).injOn,
    Work.BoseRowQ2.image_labVec_eq_cube]

/-! ## 3. The reduced form of `chiTail` -/

/-- **The reduced form of `chiTail`.**  For `ℓ > 0`, with `y = ℓ⁻¹ • x`,

  `chiTail ℓ N x = χ(y)² − θ(y) − χ(y)·P_N(y) + θ(y)·Q_N`. -/
theorem chiTail_eq_cubeSum {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (x : E3) :
    chiTail ℓ N x = (((chiR (ℓ⁻¹ • x)) ^ 2 : ℝ) : ℂ) - thetaB (ℓ⁻¹ • x)
      - ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ) * cubeSum N (ℓ⁻¹ • x)
      + thetaB (ℓ⁻¹ • x) * ((cubeSq N : ℝ) : ℂ) := by
  have hterm : ∀ k : Lab N,
      ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N k) : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x
      = chatC (Work.BoseB4.vec (labVec N k)) *
          (Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))
            * ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ)
            - chatC (Work.BoseB4.vec (labVec N k)) * thetaB (ℓ⁻¹ • x)) := by
    intro k
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply,
      smul_kmomLab (ne_of_gt hℓ), inner_kmomLab_vec hℓ, chiLam_eq_chiR,
      thetaFun_smul hℓ]
    simp only [chatC]
  have hP : (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
        Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ)))
      = cubeSum N (ℓ⁻¹ • x) :=
    (sum_labVec_eq_cube N (fun d => chatC (Work.BoseB4.vec d) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d) (ℓ⁻¹ • x) : ℝ) : ℂ)))).trans rfl
  have hQ : (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
        chatC (Work.BoseB4.vec (labVec N k))) = ((cubeSq N : ℝ) : ℂ) := by
    have h1 : ∀ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
        chatC (Work.BoseB4.vec (labVec N k))
        = ((Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N k)) ^ 2 : ℝ) : ℂ) := by
      intro k
      simp only [chatC, ← Complex.ofReal_mul, sq]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Complex.ofReal_sum]
    congr 1
    exact sum_labVec_eq_cube N (fun d => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec d)) ^ 2)
  have hcontract : (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
        (Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))
          * ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ)
          - chatC (Work.BoseB4.vec (labVec N k)) * thetaB (ℓ⁻¹ • x)))
      = ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ) * cubeSum N (ℓ⁻¹ • x)
        - thetaB (ℓ⁻¹ • x) * ((cubeSq N : ℝ) : ℂ) := by
    rw [show (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
          (Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))
            * ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ)
            - chatC (Work.BoseB4.vec (labVec N k)) * thetaB (ℓ⁻¹ • x)))
        = ∑ k : Lab N, (chatC (Work.BoseB4.vec (labVec N k)) *
            (Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))
              * ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ))
            - chatC (Work.BoseB4.vec (labVec N k))
              * (chatC (Work.BoseB4.vec (labVec N k)) * thetaB (ℓ⁻¹ • x))) from
          Finset.sum_congr rfl (fun k _ => by ring)]
    rw [Finset.sum_sub_distrib]
    rw [show (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
            (Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))
              * ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ)))
          = ((chiR (ℓ⁻¹ • x) : ℝ) : ℂ) *
            (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
              Complex.exp (Complex.I *
                ((inner ℝ (Work.BoseB4.vec (labVec N k)) (ℓ⁻¹ • x) : ℝ) : ℂ))) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)]
    rw [show (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
            (chatC (Work.BoseB4.vec (labVec N k)) * thetaB (ℓ⁻¹ • x)))
          = (∑ k : Lab N, chatC (Work.BoseB4.vec (labVec N k)) *
            chatC (Work.BoseB4.vec (labVec N k))) * thetaB (ℓ⁻¹ • x) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)]
    rw [hP, hQ]
    ring
  unfold chiTail
  rw [chiLam_eq_chiR, thetaFun_smul hℓ, Finset.sum_congr rfl (fun k _ => hterm k), hcontract]
  push_cast
  ring

/-! ## 4. The two continuum lattice identities -/

/-- **Parseval for the corpus bump**: `∑_n χ̂(vec n)² = 1`
(the `n = 0` case of the lattice Parseval identity `chiLatticeParseval`). -/
theorem chiHat_sq_tsum_one :
    (∑' n : Fin 3 → ℤ, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2) = 1 := by
  have hv : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i; simp [Work.BoseB4.vec]
  have h := Work.BoseRowQ2.chiLatticeParseval (0 : Fin 3 → ℤ)
  rw [hv, Work.BoseB4.BoxData.hatChiSq_zero] at h
  rw [show (∑' n : Fin 3 → ℤ, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2)
      = ∑' n : Fin 3 → ℤ, Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)
          * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (n + 0)) from by
        refine tsum_congr (fun n => ?_)
        simp [sq]]
  exact h

/-- Summability of the χ̂² series (immediate from `chiHat_sq_tsum_one`, whose value is `1`). -/
lemma summable_chiHat_sq :
    Summable (fun n : (Fin 3 → ℤ) => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2) := by
  have hfull := chiHat_sq_tsum_one
  by_contra hns
  rw [tsum_eq_zero_of_not_summable hns] at hfull
  norm_num at hfull

/-! ## 5. The complement subtype of the cube -/

/-- The subtype of lattice points outside `cube N`, in the form produced by
`Summable.sum_add_tsum_compl`, agrees with the explicit subtype `{d // d ∉ cube N}`. -/
lemma tsum_cubeCompl_eq (N : ℕ) {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (F : (Fin 3 → ℤ) → M) :
    (∑' x : ↥((↑(Work.BoseRowQ2.cube N) : Set (Fin 3 → ℤ))ᶜ), F x)
      = ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N}, F d := by
  calc (∑' x : ↥((↑(Work.BoseRowQ2.cube N) : Set (Fin 3 → ℤ))ᶜ), F x)
      = ∑' x : Fin 3 → ℤ, ((↑(Work.BoseRowQ2.cube N) : Set (Fin 3 → ℤ))ᶜ).indicator F x :=
        tsum_subtype _ _
    _ = ∑' x : Fin 3 → ℤ, ({d : Fin 3 → ℤ | d ∉ Work.BoseRowQ2.cube N}).indicator F x := by
        refine tsum_congr fun x => ?_
        by_cases h : x ∈ Work.BoseRowQ2.cube N
        · rw [Set.indicator_apply, Set.indicator_apply]
          exact if_congr (by simp [Set.mem_compl_iff, Finset.mem_coe, h]) rfl rfl
        · rw [Set.indicator_apply, Set.indicator_apply]
          exact if_congr (by simp [Set.mem_compl_iff, Finset.mem_coe, h]) rfl rfl
    _ = ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N}, F d :=
        (tsum_subtype ({d : Fin 3 → ℤ | d ∉ Work.BoseRowQ2.cube N}) F).symm

/-- `1 − cubeSq N` is the tail of the χ̂² Parseval series outside the cube. -/
theorem one_sub_cubeSq (N : ℕ) :
    1 - cubeSq N
      = ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N},
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec d.val)) ^ 2 := by
  have hfull := chiHat_sq_tsum_one
  have h := Summable.sum_add_tsum_compl summable_chiHat_sq (s := Work.BoseRowQ2.cube N)
  rw [hfull] at h
  rw [tsum_cubeCompl_eq N
    (fun d => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec d)) ^ 2)] at h
  rw [cubeSq]
  linarith

/-! ## 6. Summability of the Poisson series -/

/-- `kinFT` of the (complexified) corpus bump is its cosine transform `χ̂`. -/
lemma kinFT_chiR_eq_chatC (p : E3) :
    Submission.BoseGases.kinFT (fun x : E3 => ((chiR x : ℝ) : ℂ)) p = chatC p := by
  have h := Work.BoseRowQ2.integral_exp_inner_of_even (F := chiR)
    Submission.BoseGases.chi_continuous Submission.BoseGases.chi_hasCompactSupport
    Submission.BoseGases.chi_even p
  rw [show Submission.BoseGases.kinFT (fun x : E3 => ((chiR x : ℝ) : ℂ)) p
      = ∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
          ((chiR y : ℝ) : ℂ) from rfl, h, chatC]
  rw [show Work.BoseK15.corpusBox.hatChi p = ∫ y : E3, chiR y * Real.cos (inner ℝ p y) from rfl]

/-- Summability of the Poisson series (any phase).  This is the summability input of
`Work.BoseFixR.poisson_scaled` transported through the Fourier identification of `χ̂`. -/
lemma summable_poisSeries (y : E3) :
    Summable (fun d : Fin 3 → ℤ => chatC (Work.BoseB4.vec d) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d) y : ℝ) : ℂ))) := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun x : E3 => ((chiR x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Submission.BoseGases.chi_contDiff
  have hWs : HasCompactSupport (fun x : E3 => ((chiR x : ℝ) : ℂ)) :=
    Submission.BoseGases.chi_hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have h := summable_kinFT_lattice_phase (ℓ := 1) one_pos hW hWs y
  refine h.congr (fun n => ?_)
  have hkm : Work.BoseBoxFock.kmomInt 1 n = Work.BoseB4.vec n := by
    rw [Work.BoseBoxFock.kmomInt, inv_one, one_smul]
  rw [hkm, kinFT_chiR_eq_chatC]

/-! ## 7. Poisson summation for the corpus bump, and the two truncation tails -/

/-- `kmomInt 1 n = vec n`. -/
lemma kmomInt_one_vec (n : Fin 3 → ℤ) : Work.BoseBoxFock.kmomInt 1 n = Work.BoseB4.vec n := by
  rw [Work.BoseBoxFock.kmomInt, inv_one, one_smul]

/-- **Poisson summation for the corpus bump**: the continuum χ-row sum
`∑_n χ̂(vec n) e^{i⟪vec n,y⟫}` is the periodization `∑_d χ(y + d)`.

This is `Work.BoseBoxFock.latticePoisson_kernel` at `ℓ = 1` (`kmomInt 1 n = vec n`) together
with the identification `kinFT χ = χ̂` of an even real function (`kinFT_chiR_eq_chatC`). -/
theorem poisSeries_eq_perSeries (y : E3) : poisSeries y = perSeries y := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun x : E3 => ((chiR x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Submission.BoseGases.chi_contDiff
  have hWs : HasCompactSupport (fun x : E3 => ((chiR x : ℝ) : ℂ)) :=
    Submission.BoseGases.chi_hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have h := Work.BoseBoxFock.latticePoisson_kernel 1 one_pos
    (fun x : E3 => ((chiR x : ℝ) : ℂ)) hW hWs y
  have h1 : ((1 : ℝ) : ℂ) ^ 3 = 1 := by norm_num
  rw [h1, one_mul] at h
  calc poisSeries y
      = ∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT (fun x : E3 => ((chiR x : ℝ) : ℂ))
          (Work.BoseBoxFock.kmomInt 1 n) *
            Complex.exp (Complex.I *
              ((inner ℝ (Work.BoseBoxFock.kmomInt 1 n) y : ℝ) : ℂ)) := by
        rw [poisSeries]
        refine tsum_congr (fun n => ?_)
        rw [kmomInt_one_vec, kinFT_chiR_eq_chatC]
    _ = ∑' m : Fin 3 → ℤ, ((chiR (y + Work.BoseFixR.lat1 m) : ℝ) : ℂ) :=
        h.trans (tsum_congr (fun m => by congr 2; rw [one_smul]; rfl))
    _ = perSeries y := rfl

/-- `perSeries y − cubeSum N y` is the tail of the Poisson series outside the cube. -/
theorem perSeries_sub_cubeSum (N : ℕ) (y : E3) :
    perSeries y - cubeSum N y = poisTail N y := by
  have h := Summable.sum_add_tsum_compl (summable_poisSeries y) (s := Work.BoseRowQ2.cube N)
  rw [tsum_cubeCompl_eq N
    (fun d => chatC (Work.BoseB4.vec d) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d) y : ℝ) : ℂ)))] at h
  have hP : (∑' x : Fin 3 → ℤ, chatC (Work.BoseB4.vec x) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec x) y : ℝ) : ℂ))) = perSeries y := by
    rw [← poisSeries_eq_perSeries y]
    rfl
  have hC : (∑ d ∈ Work.BoseRowQ2.cube N, chatC (Work.BoseB4.vec d) *
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d) y : ℝ) : ℂ))) = cubeSum N y := rfl
  rw [hC, hP] at h
  rw [poisTail, sub_eq_iff_eq_add]
  exact h.symm.trans (add_comm _ _)

/-! ## 8. The bound -/

/-- `‖e^{i x}‖ = 1` for real `x`. -/
lemma norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- The box indicator has modulus at most `1`. -/
lemma norm_thetaB_le_one (y : E3) : ‖thetaB y‖ ≤ 1 := by
  rw [thetaB, Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- The corpus bump is bounded by `√(48/π)`. -/
lemma abs_chiR_le (y : E3) : |chiR y| ≤ Real.sqrt (48 / Real.pi) := by
  have h : (chiR y) ^ 2 ≤ 48 / Real.pi := Work.BoseRowQ2.chi_sq_le_48_div_pi' y
  have h1 : |chiR y| = Real.sqrt ((chiR y) ^ 2) := (Real.sqrt_sq_eq_abs (chiR y)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

theorem chiTail_bound (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)),
      ‖chiTail ℓ N x‖ ≤ C / ((N : ℝ) + 1) ^ K := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := chiHat_abs_cubeCompl_tail K
  obtain ⟨C₂, hC₂0, hC₂⟩ := chiHat_sq_cubeCompl_tail K
  refine ⟨Real.sqrt (48 / Real.pi) * C₁ + C₂, by positivity, ?_⟩
  intro ℓ hℓ N x
  set y : E3 := ℓ⁻¹ • x with hy
  -- the reduced form, with `ℓ⁻¹ • x` renamed to `y`
  have hred := chiTail_eq_cubeSum hℓ N x
  rw [← hy] at hred
  -- the two tail bounds
  have htail : ‖perSeries y - cubeSum N y‖ ≤ C₁ / ((N : ℝ) + 1) ^ K := by
    rw [perSeries_sub_cubeSum N y]
    have hsub : Summable (fun d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N} =>
        chatC (Work.BoseB4.vec d.val) *
          Complex.exp (Complex.I * ((inner ℝ (Work.BoseB4.vec d.val) y : ℝ) : ℂ))) :=
      (summable_poisSeries y).subtype _
    calc ‖poisTail N y‖
        ≤ ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N},
            ‖chatC (Work.BoseB4.vec d.val) *
              Complex.exp (Complex.I *
                ((inner ℝ (Work.BoseB4.vec d.val) y : ℝ) : ℂ))‖ :=
          norm_tsum_le_tsum_norm (f := fun d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N} =>
            chatC (Work.BoseB4.vec d.val) *
              Complex.exp (Complex.I *
                ((inner ℝ (Work.BoseB4.vec d.val) y : ℝ) : ℂ))) hsub.norm
      _ = ∑' d : {d : Fin 3 → ℤ // d ∉ Work.BoseRowQ2.cube N},
            |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec d.val)| := by
          refine tsum_congr (fun d => ?_)
          rw [norm_mul, norm_exp_I_mul, mul_one]
          simp [chatC]
      _ ≤ C₁ / ((N : ℝ) + 1) ^ K := hC₁ N
  have hsq : |1 - cubeSq N| ≤ C₂ / ((N : ℝ) + 1) ^ K := by
    have h0 : 0 ≤ 1 - cubeSq N := by
      rw [one_sub_cubeSq N]
      exact tsum_nonneg (fun d => sq_nonneg _)
    rw [abs_of_nonneg h0, one_sub_cubeSq N]
    exact hC₂ N
  -- the algebra: `chiTail = χ(y)·(perSeries − cubeSum) − θ(y)·(1 − cubeSq)`
  have halg : chiTail ℓ N x = ((chiR y : ℝ) : ℂ) * (perSeries y - cubeSum N y)
      - thetaB y * (1 - ((cubeSq N : ℝ) : ℂ)) := by
    simp only [chiR] at hred ⊢
    rw [hred, Complex.ofReal_pow, ← chi_lat1_periodization_mul y, perSeries]
    simp only [chiR]
    ring
  rw [halg]
  have hDpos : (0 : ℝ) < ((N : ℝ) + 1) ^ K := by positivity
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (48 / Real.pi) := Real.sqrt_nonneg _
  have h1 : ‖((chiR y : ℝ) : ℂ)‖ = |chiR y| := by simp
  have h2 : ‖(1 : ℂ) - ((cubeSq N : ℝ) : ℂ)‖ = |1 - cubeSq N| := by
    have hc : (1 : ℂ) - ((cubeSq N : ℝ) : ℂ) = ((1 - cubeSq N : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_def, Complex.normSq_ofReal,
      show (1 - cubeSq N) * (1 - cubeSq N) = (1 - cubeSq N) ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
  calc ‖((chiR y : ℝ) : ℂ) * (perSeries y - cubeSum N y)
        - thetaB y * (1 - ((cubeSq N : ℝ) : ℂ))‖
      ≤ ‖((chiR y : ℝ) : ℂ) * (perSeries y - cubeSum N y)‖
        + ‖thetaB y * (1 - ((cubeSq N : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ = |chiR y| * ‖perSeries y - cubeSum N y‖ + ‖thetaB y‖ * |1 - cubeSq N| := by
        rw [norm_mul, norm_mul, h1, h2]
    _ ≤ Real.sqrt (48 / Real.pi) * (C₁ / ((N : ℝ) + 1) ^ K)
        + 1 * (C₂ / ((N : ℝ) + 1) ^ K) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul (abs_chiR_le y) htail (norm_nonneg _) hsqrt
        · exact mul_le_mul (norm_thetaB_le_one y) hsq (abs_nonneg _) (by norm_num)
    _ = (Real.sqrt (48 / Real.pi) * C₁ + C₂) / ((N : ℝ) + 1) ^ K := by
        rw [one_mul, ← mul_div_assoc, add_div]

end Work.BoseBoxFock
