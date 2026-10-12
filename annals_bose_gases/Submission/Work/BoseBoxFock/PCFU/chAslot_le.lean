import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU._asmArith
import Submission.Work.BoseBoxFock.PCFU._asmSplit
import Submission.Work.BoseBoxFock.PCFU.chAslotImages_le
import Submission.Work.BoseBoxFock.PCFU.chAslotTaper_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-- **`Work.BoseBoxFock.PCFU.chAslot_le`** — the per-slot bound for the `(A)`-channel alias slot of
the cubic dictionary.  The proof is the assembly of

* `PCFU.chAslotTaper_le` (the `KfrU − latPer3 ℓ W₁` half),
* `PCFU.chAslotImages_le` (the `latPer3 ℓ W₁ − ℓ³W₁` half),
* `PCFU.windowedDirichlet_bound` (the `D`-budget),
* `PCFU.chAslotSplitMine` (the pointwise split of the two halves),
* `PCFU.chAslot_sqrtD`, `PCFU.chAslot_taper_arith`, `PCFU.chAslot_images_arith` (the arithmetic).

See `PCFU/FINDING_chAslot_le_SESSION2.md` for the details and for the status of the last input. -/
theorem chAslot_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chAslot v h fc fu μ N i j Θ) := by
  classical
  -- ⚑ the taper constant (child `chAslotTaper_le`)
  obtain ⟨Ct, hCt0, hCt⟩ := chAslotTaper_le v h hv hv1 hvrad hR hv_supp hav fc fu (J := J) (ε₀ := ε₀)
  -- ⚑ the Dirichlet constant (child `windowedDirichlet_bound`)
  obtain ⟨Cd, hCd0, hCd⟩ := windowedDirichlet_bound v h hv hv1 hvrad hR hv_supp hav (J := J) (ε₀ := ε₀)
  -- ⚑ the images constant (child `chAslotImages_le`)
  obtain ⟨Ci, hCi0, hCi⟩ :=
    chAslotImages_le v h hv hv1 hvrad hR hv_supp hav fc fu (J := J) (ε₀ := ε₀) 4
  have hchiSup0 : 0 ≤ Submission.BoseGases.chiSup := le_of_lt Submission.BoseGases.chiSup_pos
  have hassqnn : (0 : ℝ) ≤ (ε₀ / (BoseGases.a v) ^ 3) ^ 2 := sq_nonneg _
  have hinvnn : (0 : ℝ) ≤ ((2 * R) ^ 3)⁻¹ := by apply inv_nonneg.mpr; positivity
  -- ⚑ the constant `K0`
  set K0 : ℝ := 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
      * R ^ 8 * (ε₀ / (BoseGases.a v) ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹) + 1 with hK0def
  have hK0big : 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup * R ^ 8
      * (ε₀ / (BoseGases.a v) ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹) ≤ K0 := by
    rw [hK0def]; exact le_add_of_nonneg_right zero_le_one
  have hK0pos : 0 < K0 := by
    rw [hK0def]
    have p1 : (0 : ℝ) ≤ 16 * Ci := mul_nonneg (by norm_num) hCi0
    have p2 : (0 : ℝ) ≤ 16 * Ci * Real.sqrt Cd := mul_nonneg p1 (Real.sqrt_nonneg _)
    have p3 : (0 : ℝ) ≤ 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup :=
      mul_nonneg p2 (Real.sqrt_nonneg _)
    have p4 : (0 : ℝ) ≤ 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
        * R ^ 8 := mul_nonneg p3 (pow_nonneg hR.le 8)
    have p5 : (0 : ℝ) ≤ 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
        * R ^ 8 * (ε₀ / (BoseGases.a v) ^ 3) ^ 2 := mul_nonneg p4 hassqnn
    have p6 : (0 : ℝ) ≤ 1 + ((2 * R) ^ 3)⁻¹ := by linarith
    have p7 : (0 : ℝ) ≤ 16 * Ci * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
        * R ^ 8 * (ε₀ / (BoseGases.a v) ^ 3) ^ 2 * (1 + ((2 * R) ^ 3)⁻¹) :=
      mul_nonneg p5 p6
    linarith
  refine ⟨K0, hK0pos, ?_⟩
  -- ⚑ the bound constant `A μ`
  set Af : ℝ → ℝ := fun μ =>
    if 0 < μ then K0 * BoseGases.a v / (8 * μ * ((ellH v μ) ^ 3 + 1)) else 0 with hAdef
  -- ⚑ the `N`-threshold: `Y μ ^ 2` together with `⌈chNThresh⌉₊`
  set Y : ℝ → ℝ := fun μ => 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
      * (1 + R) ^ 3 * μ ^ 2 * Real.sqrt (BoseGases.a v) * (ellH v μ) ^ 5
      * ((ellH v μ) ^ 3 + 1) / (K0 * BoseGases.a v) with hYdef
  set Tf : ℝ → ℕ := fun μ =>
    Nat.ceil ((Y μ) ^ 2) + Nat.ceil (chNThresh v μ) + 2 with hTdef
  refine ⟨Af, Tf, ?_, ?_, ?_⟩
  · -- `0 ≤ A μ`
    intro μ
    rw [hAdef]
    by_cases hμ : 0 < μ
    · simp only [hμ, if_true]
      have hℓ0 : (0 : ℝ) ≤ ellH v μ := (ellH_pos v μ).le
      exact div_nonneg (mul_nonneg hK0pos.le hav.le) (by positivity)
    · simp only [hμ, if_false]; exact le_refl 0
  · -- the budget clause, saturated
    intro μ hμ
    rw [hAdef]
    simp only [hμ, if_true]
    exact le_of_eq (budget_saturates (v := v) (μ := μ) (ne_of_gt hμ) K0)
  · -- the per-slot bound
    intro Nmin hNmin hT hreg HM hHM μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have hμ : 0 < μ := hAdm.1
    have hℓ : 0 < ellH v μ := ellH_pos v μ
    have hRchi : R ≤ ellH v μ * Submission.BoseGases.chiR0 := (hreg μ hAdm).1
    have h2R : 2 * R ≤ ellH v μ := by linarith [(hreg μ hAdm).2]
    have hnb : 0 < Work.BoseBoxFix.normB v μ n Φ := hnorm
    -- ⚑ the threshold facts
    have hNT : Tf μ ≤ (HM μ).N := le_trans (hT μ) (hHM μ)
    simp only [hTdef] at hNT
    have hNcel : Nat.ceil ((Y μ) ^ 2) ≤ (HM μ).N := by omega
    have hNthr : ⌈chNThresh v μ⌉₊ ≤ (HM μ).N := by omega
    have hN2 : 2 ≤ (HM μ).N := by omega
    have hNpos : (0 : ℝ) < ((HM μ).N : ℝ) := by exact_mod_cast (by omega : 0 < (HM μ).N)
    have hYnn : 0 ≤ Y μ := by
      rw [hYdef]
      have q1 : (0 : ℝ) ≤ 16 * Ct := mul_nonneg (by norm_num) hCt0
      have q2 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd := mul_nonneg q1 (Real.sqrt_nonneg _)
      have q3 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup :=
        mul_nonneg q2 (Real.sqrt_nonneg _)
      have q4 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
          * (1 + R) ^ 3 := mul_nonneg q3 (by positivity)
      have q5 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
          * (1 + R) ^ 3 * μ ^ 2 := mul_nonneg q4 (sq_nonneg μ)
      have q6 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
          * (1 + R) ^ 3 * μ ^ 2 * Real.sqrt (BoseGases.a v) :=
        mul_nonneg q5 (Real.sqrt_nonneg _)
      have q7 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
          * (1 + R) ^ 3 * μ ^ 2 * Real.sqrt (BoseGases.a v) * (ellH v μ) ^ 5 :=
        mul_nonneg q6 (by positivity)
      have q8 : (0 : ℝ) ≤ 16 * Ct * Real.sqrt Cd * Real.sqrt Submission.BoseGases.chiSup
          * (1 + R) ^ 3 * μ ^ 2 * Real.sqrt (BoseGases.a v) * (ellH v μ) ^ 5
          * ((ellH v μ) ^ 3 + 1) := mul_nonneg q7 (by positivity)
      exact div_nonneg q8 (mul_pos hK0pos hav).le
    have hYsq : (Y μ) ^ 2 ≤ ((HM μ).N : ℝ) :=
      le_trans (Nat.le_ceil ((Y μ) ^ 2)) (by exact_mod_cast hNcel)
    have hYle : Y μ ≤ Real.sqrt ((HM μ).N : ℝ) := by
      have h := Real.sqrt_le_sqrt hYsq
      rwa [Real.sqrt_sq hYnn] at h
    -- ⚑ the `D`-bound from `windowedDirichlet_bound`
    set D : ℝ := Cd * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3
      * Work.BoseBoxFix.normB v μ n Φ with hDdef
    have hD : (∫ x in Submission.BoseGases.abox n (ellH v μ),
          (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
            Submission.BoseGases.chiScale (ellH v μ) z *
              (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)) ≤ D := by
      rw [hDdef]
      exact hCd μ hAdm ⟨hRchi, h2R⟩ hJ n Φ hn hnorm hlowB i
    -- ⚑ the taper bound (child `chAslotTaper_le`)
    have htaper : ‖∫ x : Submission.BoseGases.X n,
          ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
            * (KfrU v h μ fu ((HM μ).N) (x j - x i)
                - latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i
                      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
        ≤ Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3 * (ellH v μ) ^ 3
            * Real.sqrt (ellH v μ) * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
            / Real.sqrt (((HM μ).N : ℕ) : ℝ) := by
      exact hCt μ hAdm ⟨hRchi, h2R⟩ hJ ((HM μ).N) n Φ hNthr hn hnorm hlowB i j hij D hD
    have himages : ‖∫ x : Submission.BoseGases.X n,
          ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
            * (latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i)
                - ((ellH v μ) ^ 3 : ℂ)
                  * ((Work.BoseFixR.W1fun v h (ellH v μ) (x j - x i) : ℝ) : ℂ))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i
                      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
        ≤ Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
            * Real.sqrt (BoseGases.a v) * (ellH v μ) ^ 3 * Real.sqrt (ellH v μ)
            * Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) := by
      exact hCi μ hAdm ⟨hRchi, h2R⟩ hJ n Φ hn hnorm hlowB i j hij D hD
    -- ⚑ the split (child `chAslotSplit`)
    have hΘm : Measurable (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) := by
      unfold boxRestrictR
      exact (Φ.contDiff.continuous.measurable).mul
        (measurable_const.indicator (Submission.BoseGases.abox_measurable n (ellH v μ)))
    have hΘb : ∃ C : ℝ, ∀ x,
        |boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x| ≤ C := by
      obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
        Φ.contDiff.continuous.continuousOn
      exact ⟨max C 0, fun x => boxRestrictR_abs_le (ellH v μ) C
        (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx) x⟩
    have hΘs : Function.support (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
        ⊆ Submission.BoseGases.abox n (ellH v μ) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      exact hx (by rw [boxRestrictR, Set.indicator_of_notMem hcon, mul_zero])
    have hsplit : chAslot v h fc fu μ ((HM μ).N) i j
        (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
        = (∫ x : Submission.BoseGases.X n,
            ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
              * (KfrU v h μ fu ((HM μ).N) (x j - x i)
                  - latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i))
              * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j
                      (Submission.BoseGases.aP (ellH v μ) i
                        (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ))
          + (∫ x : Submission.BoseGases.X n,
            ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
              * (latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i)
                  - ((ellH v μ) ^ 3 : ℂ)
                    * ((Work.BoseFixR.W1fun v h (ellH v μ) (x j - x i) : ℝ) : ℂ))
              * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j
                      (Submission.BoseGases.aP (ellH v μ) i
                        (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)) := by
      exact chAslotSplitMine v h fc fu hR hμ hav hv_supp hRchi ((HM μ).N) hij hΘm hΘb hΘs
    -- ⚑ the arithmetic
    have hAeq : Af μ = K0 * BoseGases.a v / (8 * μ * ((ellH v μ) ^ 3 + 1)) := by
      rw [hAdef]; simp only [hμ, if_true]
    have hprod : (ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
        * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
        = (ellH v μ) ^ 5 * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v)
          * Work.BoseBoxFix.normB v μ n Φ := by
      rw [show (ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
            * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
          = (ellH v μ) ^ 3 * Real.sqrt (ellH v μ)
            * (Real.sqrt D * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)) by ring,
        hDdef, chAslot_sqrtD hCd0 hμ.le hav.le hℓ.le hnb.le]
      rw [show (ellH v μ) ^ 3 * Real.sqrt (ellH v μ)
            * (Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v) * (ellH v μ)
              * Real.sqrt (ellH v μ) * Work.BoseBoxFix.normB v μ n Φ)
          = (ellH v μ) ^ 3 * (Real.sqrt (ellH v μ) * Real.sqrt (ellH v μ))
            * (ellH v μ) * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v)
            * Work.BoseBoxFix.normB v μ n Φ by ring,
        Real.mul_self_sqrt hℓ.le]
      ring
    have hnumT : Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3
        * ((ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
          * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ))
        = Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3 * (ellH v μ) ^ 5
          * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v) * Work.BoseBoxFix.normB v μ n Φ := by
      rw [hprod]; ring
    have hT1 : ‖∫ x : Submission.BoseGases.X n,
          ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
            * (KfrU v h μ fu ((HM μ).N) (x j - x i)
                - latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i
                      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
        ≤ Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3 * (ellH v μ) ^ 5
          * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v)
          * Work.BoseBoxFix.normB v μ n Φ / Real.sqrt (((HM μ).N : ℕ) : ℝ) := by
      refine le_trans htaper ?_
      rw [show Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3 * (ellH v μ) ^ 3
            * Real.sqrt (ellH v μ) * Real.sqrt D
            * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
            / Real.sqrt (((HM μ).N : ℕ) : ℝ)
          = Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3
            * ((ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
              * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ))
            / Real.sqrt (((HM μ).N : ℕ) : ℝ) by ring,
        hnumT]
    have hTfinal : Ct * Real.sqrt Submission.BoseGases.chiSup * (1 + R) ^ 3
        * (ellH v μ) ^ 5 * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v)
        * Work.BoseBoxFix.normB v μ n Φ / Real.sqrt (((HM μ).N : ℕ) : ℝ)
        ≤ (1 / 2) * (Af μ * Work.BoseBoxFix.normB v μ n Φ) := by
      have h := chAslot_taper_arith (Ct := Ct) (chiSup := Submission.BoseGases.chiSup) (R := R)
        (ℓ := ellH v μ) (Cd := Cd) (μ := μ) (A := BoseGases.a v)
        (nb := Work.BoseBoxFix.normB v μ n Φ) (Y := Y μ) (K0 := K0) (a := BoseGases.a v)
        (N := ((HM μ).N : ℝ)) hCt0 hchiSup0 hR hμ hav hℓ hnb.le hK0pos hav hNpos
        (by rw [hYdef]) hYnn hYle
      rw [hAeq]
      exact h
    have hnumI : Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
        * Real.sqrt (BoseGases.a v)
        * ((ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
          * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ))
        = Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup * Real.sqrt Cd * μ
          * (BoseGases.a v) * (ellH v μ) ^ 5 * Work.BoseBoxFix.normB v μ n Φ := by
      rw [hprod]
      rw [show Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
            * Real.sqrt (BoseGases.a v)
            * ((ellH v μ) ^ 5 * Real.sqrt Cd * μ * Real.sqrt (BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n Φ)
          = Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
            * (Real.sqrt (BoseGases.a v) * Real.sqrt (BoseGases.a v))
            * (ellH v μ) ^ 5 * Real.sqrt Cd * μ * Work.BoseBoxFix.normB v μ n Φ by ring,
        Real.mul_self_sqrt hav.le]
      ring
    have hI1 : ‖∫ x : Submission.BoseGases.X n,
          ((boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (ellH v μ) (x j) : ℝ) : ℂ)
            * (latPer3 (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) (x j - x i)
                - ((ellH v μ) ^ 3 : ℂ)
                  * ((Work.BoseFixR.W1fun v h (ellH v μ) (x j - x i) : ℝ) : ℂ))
            * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i
                      (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
        ≤ Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup * Real.sqrt Cd * μ
          * (BoseGases.a v) * (ellH v μ) ^ 5 * Work.BoseBoxFix.normB v μ n Φ := by
      refine le_trans himages ?_
      rw [show Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
            * Real.sqrt (BoseGases.a v) * (ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
            * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
          = Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
            * Real.sqrt (BoseGases.a v)
            * ((ellH v μ) ^ 3 * Real.sqrt (ellH v μ) * Real.sqrt D
              * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)) by ring,
        hnumI]
    have hIarith := chAslot_images_arith (Ci := Ci) (Cd := Cd)
      (chiSup := Submission.BoseGases.chiSup) (R := R) (ℓ := ellH v μ) (μ := μ)
      (A := BoseGases.a v) (ε₀ := ε₀) (K0 := K0) hCi0 hCd0 hchiSup0 hR hμ hav hℓ h2R
      (hAdm.2.1) hK0big
    have hIfinal : Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup * Real.sqrt Cd
        * μ * (BoseGases.a v) * (ellH v μ) ^ 5 * Work.BoseBoxFix.normB v μ n Φ
        ≤ (1 / 2) * (Af μ * Work.BoseBoxFix.normB v μ n Φ) := by
      have hkey : 16 * Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
          * Real.sqrt Cd * μ ^ 2 * (ellH v μ) ^ 5 * ((ellH v μ) ^ 3 + 1) ≤ K0 := by
        have h := hIarith
        linarith
      rw [hAeq]
      have hc : (0 : ℝ) ≤ BoseGases.a v * Work.BoseBoxFix.normB v μ n Φ
          / (16 * μ * ((ellH v μ) ^ 3 + 1)) := by positivity
      have h1 : Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup * Real.sqrt Cd
          * μ * (BoseGases.a v) * (ellH v μ) ^ 5 * Work.BoseBoxFix.normB v μ n Φ
          = (16 * Ci * (R / ellH v μ) ^ 8 * Real.sqrt Submission.BoseGases.chiSup
              * Real.sqrt Cd * μ ^ 2 * (ellH v μ) ^ 5 * ((ellH v μ) ^ 3 + 1))
            * (BoseGases.a v * Work.BoseBoxFix.normB v μ n Φ
              / (16 * μ * ((ellH v μ) ^ 3 + 1))) := by
        field_simp
      have h2 : (1 / 2) * (K0 * BoseGases.a v / (8 * μ * ((ellH v μ) ^ 3 + 1))
            * Work.BoseBoxFix.normB v μ n Φ)
          = K0 * (BoseGases.a v * Work.BoseBoxFix.normB v μ n Φ
              / (16 * μ * ((ellH v μ) ^ 3 + 1))) := by
        field_simp
        ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hkey hc
    -- ⚑ assembly
    show ‖chAslot v h fc fu μ ((HM μ).N) i j
        (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
      ≤ Af μ * Work.BoseBoxFix.normB v μ n Φ
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hb := add_le_add (le_trans hT1 hTfinal) (le_trans hI1 hIfinal)
    linarith

end Work.BoseBoxFock.PCFU
