import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.W1omega0_le_g0w0
import Submission.Work.BoseBoxFock.boxFormContactChem
import Submission.Work.BoseBoxFock.q0word_wLoc_eq
import Submission.Work.BoseFixB1S.conv3chi_dev_quadratic
import Submission.Work.BoseFixB1S.noDLBoxDataAtWholeBox
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- The one-body rank-one operator `|evec0⟩⟨evec0|` of the condensate direction is idempotent. -/
theorem rankOne_evec0_comp_self {m : ℕ} [NeZero m] :
    (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m)).comp
        (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
      = Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m) := by
  -- `proj0 m v = (v 0) • evec m 0` with `(evec m 0) 0 = 1` (both definitional).
  rw [← Work.BoseBoxFock.proj0_eq_rankOne]
  refine LinearMap.ext (fun w => ?_)
  show Work.BoseBoxFock.proj0 m (Work.BoseBoxFock.proj0 m w) = Work.BoseBoxFock.proj0 m w
  rw [show Work.BoseBoxFock.proj0 m w = w 0 • Work.BoseBoxFock.evec0 m from rfl,
    show Work.BoseBoxFock.proj0 m (w 0 • Work.BoseBoxFock.evec0 m)
      = ((w 0 • Work.BoseBoxFock.evec0 m) 0) • Work.BoseBoxFock.evec0 m from rfl]
  rw [Pi.smul_apply, Work.BoseBoxFock.evec0_apply_zero, smul_eq_mul, mul_one]

/-- **The scalar arithmetic of the contact/chemical row.**  In the dilute regime the error
allowance `(64πC₁+1)μ²aℓ³√t·((R/a)²√t)` supplied by `errKafz` dominates `64πC₁R²aμ²ℓ`; the only
diluteness input is `1 ≤ μaℓ²` (the `t^{−3/323}` fact), which `one_le_mu_a_sideAt_sq` provides. -/
private lemma errKafz_arith_local {a t R L μ C₁ K : ℝ} (ha : 0 < a) (hR : 0 < R) (hL : 0 < L)
    (hμ : 0 < μ) (ht : t = μ * a ^ 3) (hC₁ : 0 ≤ C₁) (hY : 1 ≤ μ * a * L ^ 2)
    (hK : K ≥ (64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * Real.sqrt t
        * ((R / a) ^ 2 * Real.sqrt t)) :
    64 * Real.pi * C₁ * R ^ 2 * a * μ ^ 2 * L ≤ K := by
  have ht0 : 0 < t := by rw [ht]; positivity
  have hsq : Real.sqrt t * Real.sqrt t = t := by
    rw [← sq, Real.sq_sqrt ht0.le]
  have ha2 : 0 < a ^ 2 := by positivity
  -- `a ^ 2 ≤ L ^ 2 * t`
  have hLa2 : a ^ 2 ≤ L ^ 2 * t := by
    have h1 : a ^ 2 ≤ a ^ 2 * (μ * a * L ^ 2) := by
      simpa using mul_le_mul_of_nonneg_left hY (sq_nonneg a)
    have h2 : a ^ 2 * (μ * a * L ^ 2) = L ^ 2 * t := by rw [ht]; ring
    linarith
  -- `64πC₁ a² ≤ (64πC₁+1) L² t`
  have hstep : 64 * Real.pi * C₁ * a ^ 2 ≤ (64 * Real.pi * C₁ + 1) * (L ^ 2 * t) := by
    have h1 : 64 * Real.pi * C₁ * a ^ 2 ≤ 64 * Real.pi * C₁ * (L ^ 2 * t) :=
      mul_le_mul_of_nonneg_left hLa2 (by positivity)
    have h2 : 64 * Real.pi * C₁ * (L ^ 2 * t)
        ≤ (64 * Real.pi * C₁ + 1) * (L ^ 2 * t) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  -- the `√t` collapse, after multiplying by `a ^ 2`
  have hB2 : ((64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * Real.sqrt t
        * ((R / a) ^ 2 * Real.sqrt t)) * a ^ 2
      = (64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * R ^ 2 * t := by
    rw [show (64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * Real.sqrt t
          * ((R / a) ^ 2 * Real.sqrt t)
        = ((64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3)
            * ((R / a) ^ 2 * (Real.sqrt t * Real.sqrt t)) by ring,
      hsq, div_pow]
    field_simp
  -- the comparison
  have hT : 64 * Real.pi * C₁ * R ^ 2 * a * μ ^ 2 * L
      ≤ (64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * Real.sqrt t
        * ((R / a) ^ 2 * Real.sqrt t) := by
    have hmain : (64 * Real.pi * C₁ * R ^ 2 * a * μ ^ 2 * L) * a ^ 2
        ≤ ((64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * Real.sqrt t
            * ((R / a) ^ 2 * Real.sqrt t)) * a ^ 2 := by
      rw [hB2]
      calc (64 * Real.pi * C₁ * R ^ 2 * a * μ ^ 2 * L) * a ^ 2
          = (μ ^ 2 * a * L * R ^ 2) * (64 * Real.pi * C₁ * a ^ 2) := by ring
        _ ≤ (μ ^ 2 * a * L * R ^ 2) * ((64 * Real.pi * C₁ + 1) * (L ^ 2 * t)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (64 * Real.pi * C₁ + 1) * μ ^ 2 * a * L ^ 3 * R ^ 2 * t := by ring
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_right hcon ha2
    linarith [hmain, this]
  linarith [hK, hT]

theorem PotContactChem_holds (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ Work.BoseBoxFock.PotContactChem v h fc fu R J Nmin ε₀ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.BoseFixB1S.conv3chi_dev_quadratic
  obtain ⟨ε₀₀, hε₀₀pos, hε₀₀⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  refine ⟨min ε₀₀ 1, 64 * Real.pi * C₁ + 1, lt_min hε₀₀pos one_pos, by positivity, ?_⟩
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlow hspec e hemeas hebdd hesupp heorth heint hemem hpin
    hKp hLp hθp T_NH hTNH
  have hμpos : 0 < μ := hAdm.1
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀₀ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 :=
    hε₀₀ μ hAdm₀
  have hSp : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμpos hav
  -- #### the chamber data
  set E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E with hE
  have hEmu : E.mu = μ := rfl
  have hEell : E.ell = Work.BoseBox.sideAt μ (BoseGases.a v) := rfl
  have hEW : E.W1omega0 = Work.BoseFixR.chat
      (Work.BoseFixR.W1omegaFun v h (Work.BoseBox.sideAt μ (BoseGases.a v))) 0 := rfl
  have hnormBnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  -- #### the state
  set Θ : Submission.BoseGases.X n → ℂ :=
    Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ with hΘdef
  obtain ⟨hΘmeas, hΘbdd, hΘsupp0, hΘperm, hΘmass⟩ :=
    Work.BoseBoxFock.boxRestrictState hSp Φ
  have hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (BoseGases.a v)) := by
    intro x hx
    have h1 := hΘsupp0 hx
    simp only [Work.MB.boxPow, Set.mem_pi, Set.mem_univ, forall_true_left] at h1
    simp only [Submission.BoseGases.abox, Set.mem_setOf_eq]
    intro i
    rw [← Work.BoseBoxFock.corpusBox_boxL_eq_acube hSp]
    exact h1 i
  have hΘaesm : MeasureTheory.AEStronglyMeasurable Θ MeasureTheory.volume :=
    hΘmeas.aestronglyMeasurable
  obtain ⟨CΘ, hCΘ⟩ := hΘbdd
  have hCΘnn : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ 0)
  have hΘb : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)),
      ‖Θ x‖ ≤ CΘ := Filter.Eventually.of_forall hCΘ
  -- #### hypotheses in the shapes the evaluation lemmas want
  obtain ⟨c, hcc, hun⟩ := hpin
  have he0 : e 0 =ᵐ[MeasureTheory.volume] fun z => c * Work.BoseK15.corpusBox.thetaFun
      (Work.BoseBox.sideAt μ (BoseGases.a v)) z := hun
  -- #### the LHS evaluation
  have hLHS : (∫ x : Submission.BoseGases.X n, star (Θ x)
        * Work.BoseBoxFock.potContactChem (fun T => Work.BoseDict.boxSlotSum e T) E
            (8 * Real.pi * BoseGases.a v) Θ x).re
      = (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (8 * Real.pi * BoseGases.a v + E.W1omega0)
            * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ)
        - (8 * Real.pi * BoseGases.a v) * μ
            * Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) := by
    have heval := Work.BoseBoxFock.boxFormContactChem_re (m := (HM μ).m) (d := n)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) hSp heorth hemem hesupp hcc he0 hCΘnn
      hΘsupp hΘaesm hΘb
      ((1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
        * (8 * Real.pi * BoseGases.a v + E.W1omega0))
      (E.mu * (8 * Real.pi * BoseGases.a v))
    -- the word of `potContactChem` is the word of the evaluation lemma
    have hword : Work.BoseBoxFock.potContactChem (fun T => Work.BoseDict.boxSlotSum e T) E
          (8 * Real.pi * BoseGases.a v) Θ
        = ((1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
              * (8 * Real.pi * BoseGases.a v + E.W1omega0))
            • (Work.BoseDict.boxSlotSum e (rankOne (evec0 (HM μ).m))
                  (Work.BoseDict.boxSlotSum e (rankOne (evec0 (HM μ).m)) Θ)
                - Work.BoseDict.boxSlotSum e (rankOne (evec0 (HM μ).m)) Θ)
          - (E.mu * (8 * Real.pi * BoseGases.a v))
            • (Work.BoseDict.boxSlotSum e (rankOne (evec0 (HM μ).m)) Θ) := by
      simp only [Work.BoseBoxFock.potContactChem, Function.comp_apply, Pi.sub_apply,
        Pi.smul_apply, Work.BoseBoxFock.rankOne_evec0_comp_self, hEell]
    show (Work.BoseDict.cIPn n Θ (Work.BoseBoxFock.potContactChem
        (fun T => Work.BoseDict.boxSlotSum e T) E (8 * Real.pi * BoseGases.a v) Θ)).re = _
    rw [hword, heval]
    have h2 : Work.BoseBoxFock.cS2C (Work.BoseBox.sideAt μ (BoseGases.a v)) Θ
        = Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ) := by
      rw [hΘdef]
      exact Work.BoseBoxFock.cS2C_boxRestrictC (Φ : Submission.BoseGases.X n → ℝ)
    have h1 : Work.BoseBoxFock.cS1C (Work.BoseBox.sideAt μ (BoseGases.a v)) Θ
        = Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ) := by
      rw [hΘdef]
      exact Work.BoseBoxFock.cS1C_boxRestrictC (Φ : Submission.BoseGases.X n → ℝ)
    rw [h2, h1, hEmu]
    ring
  -- #### the RHS evaluation
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hQ0 := Work.BoseBoxFock.q0word_wLoc_eq (N := n) (v := v) (R := R)
    (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) hR hv hvrad hv_supp h hSp hRℓ μ hΦc
  -- #### the mass identity and the comparison
  have hg0i : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0w0i : MeasureTheory.Integrable
      (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) :=
    Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h
  have hg2 : (∫ z, Submission.BoseGases.g2 v h z)
      = 8 * Real.pi * BoseGases.a v
        + ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z := by
    have hfun : Submission.BoseGases.g2 v h = Submission.BoseGases.g0 v h
        + fun z => Submission.BoseGases.g0 v h z * Classical.choose h z := by
      funext z
      simp only [Submission.BoseGases.g2, Submission.BoseGases.g0, Pi.add_apply]
      ring
    rw [hfun]
    simp only [Pi.add_apply]
    rw [MeasureTheory.integral_add hg0i hg0w0i,
      Submission.BoseGases.g0_integral hR hv_supp h]
  have hgom : ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z ≤ 8 * Real.pi * BoseGases.a v := by
    simpa only [Submission.BoseGases.g0] using
      (Submission.BoseGases.chosen_gomega_integral_bounds hR hv hvrad hv_supp h).2
  have hgomnn : 0 ≤ ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z := by
    simpa only [Submission.BoseGases.g0] using
      (Submission.BoseGases.chosen_gomega_integral_bounds hR hv hvrad hv_supp h).1
  have hW1 := Work.BoseBoxFock.W1omega0_le_g0w0 (v := v) (h := h) (R := R)
    (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (C₁ := C₁)
    hR hSp hC₁0 hC₁ hv hvrad hv_supp hRℓ
  rw [← hEW] at hW1
  -- #### the two bounds on the condensate counts
  have hcS1le : Submission.BoseGases.cS1 (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Submission.BoseGases.aP_sq_le hSp i hΦc)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    simpa only [Submission.BoseGases.cS1, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      using h
  have hcS2le : Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (n : ℝ) * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) := by
    have h1 := Submission.BoseGases.cS2_le_n_mul_cS1 hSp hΦc
    exact le_trans h1 (mul_le_mul_of_nonneg_left hcS1le (Nat.cast_nonneg n))
  have hnn : (n : ℝ) ≤ 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := hn
  have hcS2nn : 0 ≤ Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Submission.BoseGases.cS2]
    refine Finset.sum_nonneg (fun p _ => ?_)
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  -- #### the final arithmetic
  have herr : Work.BoseFixR.errKafz v R μ (64 * Real.pi * C₁ + 1)
      ≥ (64 * Real.pi * C₁ + 1) * μ ^ 2 * BoseGases.a v
          * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Real.sqrt (μ * (BoseGases.a v) ^ 3)
          * ((R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3)) := by
    rw [Work.BoseFixR.errKafz]
    have hdil : Work.BoseFixR.dil v μ = μ * (BoseGases.a v) ^ 3 := rfl
    have hell3 : Work.BoseFixR.ell3 v μ = (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := rfl
    rw [hdil, hell3]
    have hKlpos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl :=
      Work.BoseBox.fsXp_pos (mul_pos hμpos (pow_pos hav 3))
    have h1 : (0 : ℝ) ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) :=
      Real.rpow_nonneg hKlpos.le _
    have h2 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : (0 : ℝ) ≤ Work.BoseFixR.errExp v μ :=
      Real.rpow_nonneg (le_of_lt (mul_pos hμpos (pow_pos hav 3))) _
    have h5 : (0 : ℝ) ≤ 64 * Real.pi * C₁ + 1 := by positivity
    have h6 : (0 : ℝ) ≤ μ ^ 2 * BoseGases.a v
        * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
        * Real.sqrt (μ * (BoseGases.a v) ^ 3) := by positivity
    have hge : (R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3)
        ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
          + Work.BoseFixR.fsX v μ ^ 2
          + (R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3)
          + Work.BoseFixR.errExp v μ := by linarith
    have h7 : (0 : ℝ) ≤ (64 * Real.pi * C₁ + 1) * μ ^ 2 * BoseGases.a v
        * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
        * Real.sqrt (μ * (BoseGases.a v) ^ 3) := by positivity
    calc (64 * Real.pi * C₁ + 1) * μ ^ 2 * BoseGases.a v
          * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Real.sqrt (μ * (BoseGases.a v) ^ 3)
          * ((R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3))
        = (64 * Real.pi * C₁ + 1) * μ ^ 2 * BoseGases.a v
          * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Real.sqrt (μ * (BoseGases.a v) ^ 3)
          * ((R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3)) := rfl
      _ ≤ (64 * Real.pi * C₁ + 1) * μ ^ 2 * BoseGases.a v
          * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Real.sqrt (μ * (BoseGases.a v) ^ 3)
          * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
            + Work.BoseFixR.fsX v μ ^ 2
            + (R / BoseGases.a v) ^ 2 * Real.sqrt (μ * (BoseGases.a v) ^ 3)
            + Work.BoseFixR.errExp v μ) := by
          exact mul_le_mul_of_nonneg_left hge h7
  -- #### the final comparison
  have hY : 1 ≤ μ * BoseGases.a v * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2 :=
    Work.BoseFixB1S.one_le_mu_a_sideAt_sq hav hμpos ht1
  have hLm3 : (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
      = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ := by
    rw [show (-(3 : ℝ)) = -(((3 : ℕ)) : ℝ) from by norm_num,
      Real.rpow_neg hSp.le, Real.rpow_natCast]
  have hgoal : (∫ x : Submission.BoseGases.X n, star (Θ x)
        * Work.BoseBoxFock.potContactChem (fun T => Work.BoseDict.boxSlotSum e T) E
            (8 * Real.pi * BoseGases.a v) Θ x).re
      ≤ Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
          (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0)
          (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h) 0)
          (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * Work.BoseFixR.errKafz v R μ (64 * Real.pi * C₁ + 1)
            * Work.BoseBoxFix.normB v μ n Φ := by
    -- the exact value of `LHS - q0word`
    have hdiff : (∫ x : Submission.BoseGases.X n, star (Θ x)
          * Work.BoseBoxFock.potContactChem (fun T => Work.BoseDict.boxSlotSum e T) E
              (8 * Real.pi * BoseGases.a v) Θ x).re
        = Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) 0)
            (Submission.BoseGases.wLoc (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
              * (E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z)
              * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ) := by
      rw [hLHS, hQ0, hg2, hLm3]
      ring
    rw [hdiff]
    -- the increment is paid by the allowance
    have hW1'' : E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z
        ≤ 2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
          * (∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z) := by
      nlinarith [hW1]
    have hW1''' : E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z
        ≤ 2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
          * (8 * Real.pi * BoseGases.a v) := by
      calc E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z
          ≤ 2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z) := hW1''
        _ ≤ 2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (8 * Real.pi * BoseGases.a v) :=
            mul_le_mul_of_nonneg_left hgom (by positivity)
    have hkey : (E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z)
          * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (8 * Real.pi * BoseGases.a v))
          * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_le_mul_of_nonneg_right hW1''' hcS2nn
    have hcS2bound : Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ 4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
            * Work.BoseBoxFix.normB v μ n Φ := by
      have hA0 : (0 : ℝ) ≤ 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := by positivity
      calc Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (n : ℝ) * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) := hcS2le
        _ ≤ (2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
              * ((2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
                * Work.BoseBoxFix.normB v μ n Φ) := by
            refine mul_le_mul hnn ?_ (mul_nonneg (Nat.cast_nonneg n) hnormBnn) hA0
            exact mul_le_mul hnn le_rfl hnormBnn hA0
        _ = 4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
              * Work.BoseBoxFix.normB v μ n Φ := by ring
    have hfinal : (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
          * (E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z)
          * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ (64 * Real.pi * C₁ + 1)
            * Work.BoseBoxFix.normB v μ n Φ := by
      have hposL : (0 : ℝ) ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ)) := by
        have hlt : (0 : ℝ) < (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ)) :=
          Real.rpow_pos_of_pos hSp _
        linarith
      have hB2 : (0 : ℝ) ≤ 2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
          * (8 * Real.pi * BoseGases.a v) := by positivity
      have hposB : (0 : ℝ) ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
          * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (8 * Real.pi * BoseGases.a v)) := mul_nonneg hposL hB2
      have hstep1 : (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z)
          ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v)) :=
        mul_le_mul_of_nonneg_left hW1''' hposL
      have hstep2 : (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v))
            * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v))
            * (4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
              * Work.BoseBoxFix.normB v μ n Φ) :=
        mul_le_mul_of_nonneg_left hcS2bound hposB
      have hL6 : ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹
            * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
          = R ^ 2 * Work.BoseBox.sideAt μ (BoseGases.a v) := by
        field_simp
      have hcollapse : (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v))
            * (4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
              * Work.BoseBoxFix.normB v μ n Φ)
          = 32 * Real.pi * C₁ * R ^ 2 * BoseGases.a v * μ ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n Φ := by
        rw [hLm3]
        rw [show (1 / 2) * ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹
              * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
                * (8 * Real.pi * BoseGases.a v))
              * (4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
                * Work.BoseBoxFix.normB v μ n Φ)
            = (32 * Real.pi * C₁ * BoseGases.a v * μ ^ 2 * Work.BoseBoxFix.normB v μ n Φ)
              * (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹
                * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
                * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6) by ring]
        rw [hL6]
        ring
      calc (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (E.W1omega0 - ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z)
            * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v))
            * Submission.BoseGases.cS2 (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ) :=
            mul_le_mul hstep1 le_rfl hcS2nn hposB
        _ ≤ (1 / 2) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-(3 : ℝ))
            * (2 * C₁ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
              * (8 * Real.pi * BoseGases.a v))
            * (4 * μ ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 6
              * Work.BoseBoxFix.normB v μ n Φ) := hstep2
        _ = 32 * Real.pi * C₁ * R ^ 2 * BoseGases.a v * μ ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v)
              * Work.BoseBoxFix.normB v μ n Φ := hcollapse
        _ ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ (64 * Real.pi * C₁ + 1)
              * Work.BoseBoxFix.normB v μ n Φ := by
            refine mul_le_mul_of_nonneg_right ?_ hnormBnn
            have hK := errKafz_arith_local (a := BoseGases.a v) (t := μ * (BoseGases.a v) ^ 3)
              (R := R) (L := Work.BoseBox.sideAt μ (BoseGases.a v)) (μ := μ) (C₁ := C₁)
              (K := Work.BoseFixR.errKafz v R μ (64 * Real.pi * C₁ + 1))
              hav hR hSp hμpos rfl hC₁0 hY herr
            linarith
    linarith [hfinal]
  exact hgoal
end Work.BoseBoxFock
