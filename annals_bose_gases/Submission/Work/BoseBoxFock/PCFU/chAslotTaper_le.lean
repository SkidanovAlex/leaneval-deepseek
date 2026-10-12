import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.PCFU.admDiluLeOne
import Submission.Work.BoseBoxFock.PCFU.dirichletSliceBound
import Submission.Work.BoseBoxFock.PCFU.taperArith
import Submission.Work.BoseBoxFock.PCFU.taperIntegrand_box_eq
import Submission.Work.BoseBoxFock.PCFU.taperSlotCore
import Submission.Work.BoseBoxFock.PCFU.taperSlotOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAslotTaper_le`

The taper estimate for the `(A)`-channel alias slot, with the kernel
`T = KfrU v h μ fu N − latPer3 ℓ (W₁fun v h ℓ)`.

The proof assembles three inputs, none of which involves the box state `Φ` or the pair `(i,j)`:

* `Work.BoseBoxFock.PCFU.taperSlotOne` (`TaperSlotOneBound`) — the single-slice bound `(★)`
  (the Fourier analysis of the taper: `ĉ(k) = (uvCut(κ_k) − 1)·chat W₁(κ_k)`, `ĉ(0) = 0`,
  Cauchy–Schwarz against `‖κ_k‖`, the sampling identity and the Coulomb-tail bound);
* `Work.BoseBoxFock.PCFU.taperArith` — the arithmetic
  `√(ℓ³/uvRad ℓ N) ≤ √(2/π)·((a v)^{−3/2}+1)·ℓ³√ℓ/√N` for `a v ≤ ℓ`;
* `Work.BoseBoxFock.PCFU.taperIntegrand_box_eq` — the reduction of the whole-space integral
  (carrying the box restriction `boxRestrictR`) to the box integral of the unrestricted state.

The state-dependent part is `Work.BoseBoxFock.PCFU.taperSlot_core`
(`PCFU/taperSlotCore.lean`): peel the slot `i` out of `abox (n+1) ℓ`, apply `(★)` slicewise,
Cauchy–Schwarz in the peeled configuration, and the `L²`-contraction `∫ Γ² ≤ ℓ^{−3}∫ Φ²`.

The only arithmetic input from the regime is `Adm v ε₀ μ` through
`Work.BoseBoxFock.PCFU.admDiluLeOne` (`μ(a v)³ ≤ 1`), which gives `a v ≤ ℓ = sideAt μ (a v)`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The single-slice bound `(★)`, in the exact shape of `Work.BoseBoxFock.PCFU.taperSlotOne`. -/
def TaperSlotOneBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
      {R μ : ℝ} {fu : Work.BoseBoxFix.LowCut} {N : ℕ},
      0 < R → 0 < Work.BoseBox.sideAt μ (BoseGases.a v) →
      (∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x) → MeasureTheory.MemLp v 1 →
      _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      1 ≤ N →
      ∀ (y : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) g →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w)
              - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))‖
          ≤ C * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3
              * Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹
                  * ∫ x : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
                      ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)

/-- The integrand reduction, in the exact shape of
`Work.BoseBoxFock.PCFU.taperIntegrand_box_eq`. -/
def TaperIntegrandBound : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ}
    {Φ : Submission.BoseGases.X n → ℝ} (T : EuclideanSpace ℝ (Fin 3) → ℂ),
    (∫ x : Submission.BoseGases.X n,
        ((Work.BoseBoxFock.boxRestrictR ℓ Φ x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
          * T (x j - x i)
          * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
                (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
            * T (x j - x i)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x : ℝ) : ℂ)

/-- The arithmetic input, in the exact shape of `Work.BoseBoxFock.PCFU.taperArith`. -/
def TaperArithBound : Prop :=
  ∀ {ℓ a : ℝ} {N : ℕ}, 0 < ℓ → 0 < a → a ≤ ℓ → 1 ≤ N →
    Real.sqrt (ℓ ^ 3 / Work.BoseBoxFock.uvRad ℓ N)
      ≤ Real.sqrt (2 / Real.pi) * (a ^ (-(3 / 2 : ℝ)) + 1) * ℓ ^ 3 * Real.sqrt ℓ
          / Real.sqrt (N : ℝ)

theorem chAslotTaper_of_bound (hTSO : TaperSlotOneBound)
    (hARITH : TaperArithBound) (hCONV : TaperIntegrandBound)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) {J ε₀ : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 ∧
        2 * R ≤ Work.BoseBoxFock.ellH v μ) →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (N : ℕ) (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ ≤ N →
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ (i j : Fin n), i ≠ j → ∀ D : ℝ,
          (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) z *
                  (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ D) →
          ‖∫ x : Submission.BoseGases.X n,
              ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                    - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i))
                * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                            (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
            ≤ C * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3
                * (Work.BoseBoxFock.ellH v μ) ^ 3 * Real.sqrt (Work.BoseBoxFock.ellH v μ)
                * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
                / Real.sqrt ((N : ℝ)) := by
  obtain ⟨CA, hCA0, hCA⟩ := hTSO
  refine ⟨CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
    * Real.sqrt Submission.BoseGases.chiSup, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg hCA0 (Real.sqrt_nonneg _)) ?_)
      (Real.sqrt_nonneg _)
    have h1 : 0 < (BoseGases.a v) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hav _
    linarith
  intro μ hAdm hRm hJ N n Φ hN hn hnorm hlow i j hij D hD
  have hμ : 0 < μ := hAdm.1
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    unfold Work.BoseBoxFock.ellH
    rw [if_pos hside]
  -- the diluteness bound and the threshold arithmetic
  have hdil : μ * (BoseGases.a v) ^ 3 ≤ 1 := admDiluLeOne hav hAdm
  have hdpos : (0 : ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    show 0 < Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) 6
    exact Work.BoseBox.fsXp_pos (by positivity)
  have hN1 : 1 ≤ N := by
    have h2 : (2 : ℕ) ≤ ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ := by
      have h2' : (2 : ℝ) ≤ Work.BoseBoxFock.chNThresh v μ := by
        rw [Work.BoseBoxFock.chNThresh]
        have hd2 : (0 : ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBoxFock.ellH v μ :=
          mul_pos (pow_pos hdpos 2) (Work.BoseBoxFock.ellH_pos v μ)
        have h1 : 0 ≤ 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
            * Work.BoseBoxFock.ellH v μ)⁻¹ * Work.BoseBoxFock.ellH v μ / (2 * Real.pi) := by
          refine div_nonneg ?_ (by positivity)
          exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hd2.le))
            (Work.BoseBoxFock.ellH_pos v μ).le
        linarith
      calc (2 : ℕ) = ⌈(2 : ℝ)⌉₊ := (Nat.ceil_natCast 2).symm
        _ ≤ ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ := Nat.ceil_mono h2'
    omega
  -- the diluteness bound `a v ≤ ℓ`
  have hℓa : BoseGases.a v ≤ Work.BoseBox.sideAt μ (BoseGases.a v) := by
    have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    rw [Work.BoseBox.sideAt_eq_rpow hav hμ]
    calc BoseGases.a v = BoseGases.a v * 1 := (mul_one _).symm
      _ ≤ BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hav.le
          have h := Real.rpow_le_rpow_of_nonpos ht hdil (by norm_num : (-(163 / 323 : ℝ)) ≤ 0)
          simpa using h
  -- the vacuum case: two distinct slots need `n ≥ 2`
  by_cases hn2 : n < 2
  · exact absurd (Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega)) hij
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hellH] at hD
    rw [hellH]
    -- * the single-slice bound in the spelling `ℓ = sideAt μ (a v)`
    have hTb' : ∀ (y : E3) (g : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v)) →
        ‖∫ w : E3, ((g w : ℝ) : ℂ) *
            (KfrU v h μ fu N (y - w) - latPer3
              (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) (y - w))‖
          ≤ CA * (1 + R) ^ 3 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
              * Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)⁻¹
                  * ∫ x : E3, ∑ k : Fin 3,
                      ‖fderiv ℝ g x (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) := by
      intro y g hg hgs
      have hRχ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := hRm.1
      have hgs' : tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) := by
        rwa [hellH]
      have h1 := hCA (v := v) (h := h) (R := R) (μ := μ) (fu := fu) (N := N)
        hR hside hv hv1 hvrad hv_supp hRχ hN1 y g hg hgs'
      rw [hellH] at h1
      exact h1
    -- * the state-dependent core estimate
    have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X (n' + 1) → ℝ) := Φ.contDiff
    have hκ : 0 < chKappa v μ := by
      unfold chKappa
      exact inv_pos.mpr (mul_pos (pow_pos hdpos 2) hside)
    have hΛ0 : 0 < Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N := by
      unfold Work.BoseBoxFock.uvRad
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      positivity
    obtain ⟨hΘm, Cθ, hCθ0, hΘb⟩ :=
      Work.BoseBoxFock.boxRestrictR_measurable_bounded (n := n' + 1) hside hΦc.continuous
    obtain ⟨hΓm, DΓ, hDΓ0, hΓb⟩ :=
      lowSlot_aQ_aP_measurable_bounded (n := n' + 1) (fc := fc) (μ := μ) hside hκ hCθ0 hΘm hΘb
    have hΓeq : ∀ x ∈ Submission.BoseGases.abox (n' + 1) (Work.BoseBox.sideAt μ (BoseGases.a v)),
        Work.BoseBoxFix.lowSlot fc (chKappa v μ) (Work.BoseBox.sideAt μ (BoseGases.a v)) j
          (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
            (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
              (Work.BoseBoxFock.boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X (n' + 1) → ℝ)))) x
        = Work.BoseBoxFix.lowSlot fc (chKappa v μ) (Work.BoseBox.sideAt μ (BoseGases.a v)) j
          (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
            (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
              (Φ : Submission.BoseGases.X (n' + 1) → ℝ))) x :=
      fun x hx => lowSlot_boxRestrictR_agree fc (chKappa v μ)
        (Work.BoseBox.sideAt μ (BoseGases.a v)) i j
        (Φ : Submission.BoseGases.X (n' + 1) → ℝ) hx
    obtain ⟨E, hE0, hDirb, hDirm⟩ := dirichletSliceBound (n := n') i hside hΦc
    have hDirInt : (∫ r in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (BoseGases.a v)),
        (∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
          Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) z *
            (Φ : Submission.BoseGases.X (n' + 1) → ℝ)
              (Submission.BoseGases.kcInsN n' i (z, r))) y
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)) ≤ D := by
      rw [← dirichletPeel (n := n') i hside hΦc]
      exact hD
    have hcore := taperSlot_core (n := n') i j hij hside hκ fc
      (Φ := (Φ : Submission.BoseGases.X (n' + 1) → ℝ)) hΦc
      (T := fun z : E3 => KfrU v h μ fu N z - latPer3
        (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) z)
      (Λ := Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
      (CA := CA) (R := R) (D := D) (DΓ := DΓ) (E := E)
      hCA0 hΛ0 hR.le hDΓ0 hE0 hTb' hΓm hΓb hΓeq hDirm hDirb hDirInt
    -- * the reduction of the whole-space integral to the box integral
    have hInt_eq : (∫ x : Submission.BoseGases.X (n' + 1),
        ((Work.BoseBoxFock.boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X (n' + 1) → ℝ) x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x i) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x j) : ℝ) : ℂ)
          * (KfrU v h μ fu N (x j - x i) - latPer3
              (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) (x j - x i))
          * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ)
                (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                  (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
                    (Work.BoseBoxFock.boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (n' + 1) → ℝ)))) x : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox (n' + 1) (Work.BoseBox.sideAt μ (BoseGases.a v)),
          ((Φ x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x j) : ℝ) : ℂ)
            * (KfrU v h μ fu N (x j - x i) - latPer3
                (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) (x j - x i))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ)
                  (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                  (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                    (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
                      (Φ : Submission.BoseGases.X (n' + 1) → ℝ))) x : ℝ) : ℂ) :=
      hCONV i j hij fc (fun z : E3 => KfrU v h μ fu N z - latPer3
        (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) z)
    -- * the arithmetic
    have hχ0 : 0 ≤ Submission.BoseGases.chiSup := le_of_lt Submission.BoseGases.chiSup_pos
    have hCeq : (CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
          * Real.sqrt Submission.BoseGases.chiSup) * Real.sqrt Submission.BoseGases.chiSup
        = CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
          * Submission.BoseGases.chiSup := by
      rw [mul_assoc, Real.mul_self_sqrt hχ0]
    have h1R : 0 ≤ (1 + R) ^ 3 := pow_nonneg (by linarith) 3
    have hnormB : Work.BoseBoxFix.normB v μ (n' + 1) Φ
        = ∫ x in Submission.BoseGases.abox (n' + 1) (Work.BoseBox.sideAt μ (BoseGases.a v)),
            (Φ x) ^ 2 := rfl
    have hM : Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
        ≤ Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
            * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v)) / Real.sqrt ((N : ℝ)) :=
      hARITH hside hav hℓa hN1
    have hstep3 : CA * Submission.BoseGases.chiSup * (1 + R) ^ 3
          * Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
              / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
          * Real.sqrt D
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
              (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2)
        ≤ (CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1))
            * Submission.BoseGases.chiSup * (1 + R) ^ 3
            * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v))
            * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ (n' + 1) Φ)
            / Real.sqrt ((N : ℝ)) := by
      have hX0 : 0 ≤ Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
          (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2) := Real.sqrt_nonneg _
      have hK0 : 0 ≤ CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt D
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
              (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCA0 hχ0) h1R)
          (Real.sqrt_nonneg D)) hX0
      calc
        CA * Submission.BoseGases.chiSup * (1 + R) ^ 3
            * Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
                / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
            * Real.sqrt D
            * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
                (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2)
          = (CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt D
              * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
                  (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2))
            * Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
                / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N) := by ring
        _ ≤ (CA * Submission.BoseGases.chiSup * (1 + R) ^ 3 * Real.sqrt D
              * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
                  (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2))
            * (Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
              * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
              * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v)) / Real.sqrt ((N : ℝ))) :=
            mul_le_mul_of_nonneg_left hM hK0
        _ = (CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1))
              * Submission.BoseGases.chiSup * (1 + R) ^ 3
              * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
              * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v))
              * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ (n' + 1) Φ)
              / Real.sqrt ((N : ℝ)) := by
            rw [hnormB]
            ring_nf
    calc
      ‖∫ x : Submission.BoseGases.X (n' + 1),
        ((Work.BoseBoxFock.boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X (n' + 1) → ℝ) x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x i) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x j) : ℝ) : ℂ)
          * (KfrU v h μ fu N (x j - x i) - latPer3
              (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) (x j - x i))
          * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ)
                (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                  (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
                    (Work.BoseBoxFock.boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (n' + 1) → ℝ)))) x : ℝ) : ℂ)‖
        = ‖∫ x in Submission.BoseGases.abox (n' + 1) (Work.BoseBox.sideAt μ (BoseGases.a v)),
          ((Φ x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) (x j) : ℝ) : ℂ)
            * (KfrU v h μ fu N (x j - x i) - latPer3
                (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) (x j - x i))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ)
                  (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                  (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) j
                    (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
                      (Φ : Submission.BoseGases.X (n' + 1) → ℝ))) x : ℝ) : ℂ)‖ := by
        rw [hInt_eq]
      _ ≤ CA * Submission.BoseGases.chiSup * (1 + R) ^ 3
            * Real.sqrt ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
                / Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (BoseGases.a v)) N)
            * Real.sqrt D
            * Real.sqrt (∫ x in Submission.BoseGases.abox (n' + 1)
                (Work.BoseBox.sideAt μ (BoseGases.a v)), (Φ x) ^ 2) := hcore
      _ ≤ CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
            * Submission.BoseGases.chiSup * (1 + R) ^ 3
            * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v))
            * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ (n' + 1) Φ)
            / Real.sqrt ((N : ℝ)) := hstep3
      _ ≤ ((CA * Real.sqrt (2 / Real.pi) * ((BoseGases.a v) ^ (-(3 / 2 : ℝ)) + 1)
              * Real.sqrt Submission.BoseGases.chiSup) * Real.sqrt Submission.BoseGases.chiSup)
            * (1 + R) ^ 3
            * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            * Real.sqrt (Work.BoseBox.sideAt μ (BoseGases.a v))
            * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ (n' + 1) Φ)
            / Real.sqrt ((N : ℝ)) := by
          exact le_of_eq (by rw [hCeq])

theorem chAslotTaper_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) {J ε₀ : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 ∧
        2 * R ≤ Work.BoseBoxFock.ellH v μ) →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (N : ℕ) (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ ≤ N →
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ (i j : Fin n), i ≠ j → ∀ D : ℝ,
          (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) z *
                  (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ D) →
          ‖∫ x : Submission.BoseGases.X n,
              ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                    - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i))
                * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                            (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
            ≤ C * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3
                * (Work.BoseBoxFock.ellH v μ) ^ 3 * Real.sqrt (Work.BoseBoxFock.ellH v μ)
                * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
                / Real.sqrt ((N : ℝ)) :=
  chAslotTaper_of_bound taperSlotOne taperArith taperIntegrand_box_eq
    v h hv hv1 hvrad hR hv_supp hav fc fu

end Work.BoseBoxFock.PCFU
