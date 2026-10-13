import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.SlotStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The induction step -/

/-- **The induction step.**  From the bundled level-`(i-1)` bound we obtain the level-`i` bound by
the exact recursion `dthRecOpen`: the coefficient of the level-zero quotient term is
`D_θ^{i-1}(2 cos 2θ) = O(sin(2θ)²)`, so that term is controlled by the sharp weighted Hardy
inequality `sliceBoundEta`, while all other terms come from the induction hypothesis. -/
theorem levelBnd_step (i : ℕ) (hi2 : 2 ≤ i) (hC : LevelBnd (i - 1)) : LevelBnd i := by
  obtain ⟨C, hCpos, hCb⟩ := hC
  -- ### the bounded coefficients of the recursion
  have hexKl : ∀ l : ℕ, 1 ≤ l → l ≤ i - 1 → ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ) ^ 2 ≤ K := by
    intro l hl1 hli
    exact bdd_coeff (i - 1) l hl1
  let Kl : ℕ → ℝ := fun l => if h : 1 ≤ l ∧ l ≤ i - 1 then (hexKl l h.1 h.2).choose else 1
  have hKl0 : ∀ l : ℕ, 0 ≤ Kl l := by
    intro l
    dsimp only [Kl]
    split_ifs with h
    · exact (hexKl l h.1 h.2).choose_spec.1
    · norm_num
  have hKlb : ∀ l : ℕ, 1 ≤ l → l ≤ i - 1 → ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ) ^ 2 ≤ Kl l := by
    intro l hl1 hli θ
    dsimp only [Kl]
    rw [dif_pos ⟨hl1, hli⟩]
    exact (hexKl l hl1 hli).choose_spec.2 θ
  -- ### the sharpened level-zero coefficient
  obtain ⟨M0', hM0'pos, hM0'b⟩ :=
    Work.FTS.EllipticEst.Dth1IterTwoCosBoundN (i - 1) (by omega)
  set M0 : ℝ := M0' ^ 2 with hM0def
  have hM0pos : 0 < M0 := by rw [hM0def]; positivity
  have hM0bd : ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - 1) cfun θ) ^ 2 ≤ M0 * (Real.sin (2 * θ)) ^ 4 := by
    intro θ
    have h := abs_le.mp (hM0'b θ)
    rw [hM0def]
    nlinarith [h.1, h.2, sq_nonneg (Real.sin (2 * θ)), le_of_lt hM0'pos]
  -- ### the weighted sum of the lower coefficients
  set Dsum : ℝ := ∑ l ∈ Finset.range (i - 1),
    ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1) with hDsumdef
  have hDsum0 : 0 ≤ Dsum := by
    rw [hDsumdef]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (sq_nonneg _) (hKl0 (l + 1)))
  have hCeta_pos : 0 < Ceta := Ceta_pos
  have hXnnc : (0 : ℝ) ≤ M0 * Ceta + Dsum * C :=
    add_nonneg (mul_nonneg hM0pos.le hCeta_pos.le) (mul_nonneg hDsum0 hCpos.le)
  have hYnnc : (0 : ℝ) ≤ 2 * (i : ℝ) * (M0 * Ceta + Dsum * C) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg i)) hXnnc
  have hKle : C ≤ C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1 := by linarith
  have hKpos : 0 < C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1 := by linarith
  refine ⟨C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1, hKpos, ?_⟩
  intro α h hα hα1 hsm h0 hπ hD hG j hj1 hji
  rcases lt_or_eq_of_le hji with hlt | heq
  · -- ### the levels `j ≤ i - 1`
    have hji' : j ≤ i - 1 := by omega
    obtain ⟨hint, hbd⟩ := hCb α h hα hα1 hsm h0 hπ hD
      (fun m hm1 hmi => hG m hm1 (by omega)) j hj1 hji'
    refine ⟨hint, ?_⟩
    have hmono : (∑ m ∈ Finset.Icc 1 (i - 1), pGam α m h)
        ≤ ∑ m ∈ Finset.Icc 1 i, pGam α m h := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => pGam_nonneg α m h)
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨hm1, by omega⟩
    have hXnn : 0 ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h :=
      add_nonneg (pEta_nonneg h) (Finset.sum_nonneg (fun m _ => pGam_nonneg α m h))
    calc pLhs α j h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 (i - 1), pGam α m h) := hbd
      _ ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
          refine mul_le_mul_of_nonneg_left ?_ hCpos.le
          linarith
      _ ≤ (C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1)
            * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) :=
          mul_le_mul_of_nonneg_right hKle hXnn
  · -- ### the top level `j = i`
    rw [heq]
    -- the pointwise bound
    have hae := step_pointwise (i := i) hi2 hsm (Kl := Kl) (M0 := M0) (α := α) hKlb hM0bd hKl0
    have hznn : 0 ≤ M0 := hM0pos.le
    have hZle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        zTerm α M0 h θ ≤ M0 * ((Work.Elliptic.SinQ h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
      have h4 := sin_four_mul_le (α := α) hα1 (h := h) hθ
      simp only [zTerm]
      nlinarith [h4, hznn]
    have hQle : ∀ l : ℕ, ∀ θ : ℝ, qTerm α i l Kl h θ
        = ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
            * lhsInt α (l + 1) h θ := by
      intro l θ
      simp only [qTerm, lhsInt]
      ring
    set Maj : ℝ → ℝ := fun θ => 2 * gamInt α (i - 1) h θ
        + ((2 * (i : ℝ)) * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
            (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
              * lhsInt α (l + 1) h θ) with hMajdef
    have haeMaj : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        lhsInt α i h θ ≤ Maj θ := by
      filter_upwards [hae, hZle] with θ h1 h2
      have h3 : (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ
          = (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * lhsInt α (l + 1) h θ := by
        congr 1
        exact Finset.sum_congr rfl (fun l hl => hQle l θ)
      have h4 : (2 * (i : ℝ)) * zTerm α M0 h θ
          ≤ (2 * (i : ℝ)) * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      rw [hMajdef]
      linarith
    -- the integrability of the majorant
    have hint_gam : MeasureTheory.IntegrableOn (fun θ => 2 * gamInt α (i - 1) h θ)
        Work.Spaces.Iθ := (hG (i - 1) (by omega) (by omega)).const_mul 2
    have hint_Z : MeasureTheory.IntegrableOn (fun θ => (Work.Elliptic.SinQ h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
      (levelZeroData hsm h0 hπ hD).1
    have hint_Z2 : MeasureTheory.IntegrableOn (fun θ => (2 * (i : ℝ))
        * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) Work.Spaces.Iθ :=
      (hint_Z.const_mul M0).const_mul (2 * (i : ℝ))
    have hint_Q : ∀ l ∈ Finset.range (i - 1), MeasureTheory.IntegrableOn
        (fun θ => ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
          * lhsInt α (l + 1) h θ) Work.Spaces.Iθ := by
      intro l hl
      have hli : l + 1 ≤ i - 1 := by have := Finset.mem_range.mp hl; omega
      exact ((hCb α h hα hα1 hsm h0 hπ hD (fun m hm1 hmi => hG m hm1 (by omega))
        (l + 1) (by omega) hli).1).const_mul (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
    have hint_Q2 : MeasureTheory.IntegrableOn (fun θ => (2 * (i : ℝ))
        * ∑ l ∈ Finset.range (i - 1), (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
            * lhsInt α (l + 1) h θ) Work.Spaces.Iθ :=
      (MeasureTheory.integrable_finsetSum (Finset.range (i - 1)) hint_Q).const_mul (2 * (i : ℝ))
    have hZQ : MeasureTheory.IntegrableOn (fun θ => (2 * (i : ℝ))
        * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * lhsInt α (l + 1) h θ) Work.Spaces.Iθ :=
      hint_Z2.add hint_Q2
    have hMajint : MeasureTheory.IntegrableOn Maj Work.Spaces.Iθ := by
      have h5 : MeasureTheory.IntegrableOn (fun θ => 2 * gamInt α (i - 1) h θ
          + ((2 * (i : ℝ)) * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
            + (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
                (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                  * lhsInt α (l + 1) h θ)) Work.Spaces.Iθ :=
        hint_gam.add hZQ
      rw [hMajdef]
      exact h5
    have hint : MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' hMajint (aesm_lhsInt (i := i) hsm) ?_
      filter_upwards [haeMaj, ae_Iθ_of_forall_Ioo
        (fun θ hθ => lhsInt_nonneg_of_Ioo (α := α) (i := i) (h := h) hθ)] with θ hθ hnn
      rw [Real.norm_of_nonneg hnn]
      exact hθ
    refine ⟨hint, ?_⟩
    -- the value bound
    have hmono : pLhs α i h ≤ ∫ θ in Work.Spaces.Iθ, Maj θ := by
      rw [pLhs]
      exact MeasureTheory.integral_mono_ae hint hMajint haeMaj
    -- the integral of the majorant
    have hval : (∫ θ in Work.Spaces.Iθ, Maj θ)
        = 2 * pGam α (i - 1) h
          + (2 * (i : ℝ)) * (M0 * (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.SinQ h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * pLhs α (l + 1) h := by
      rw [hMajdef]
      dsimp only
      rw [MeasureTheory.integral_add (f := fun θ => 2 * gamInt α (i - 1) h θ)
        (g := fun θ => (2 * (i : ℝ)) * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * lhsInt α (l + 1) h θ) hint_gam hZQ]
      rw [MeasureTheory.integral_add (f := fun θ => (2 * (i : ℝ))
            * (M0 * ((Work.Elliptic.SinQ h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
        (g := fun θ => (2 * (i : ℝ)) * ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * lhsInt α (l + 1) h θ) hint_Z2 hint_Q2]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hgam_eq : (∫ θ in Work.Spaces.Iθ, gamInt α (i - 1) h θ) = pGam α (i - 1) h := rfl
      have hsum : (∫ θ in Work.Spaces.Iθ, ∑ l ∈ Finset.range (i - 1),
            (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
              * lhsInt α (l + 1) h θ)
          = ∑ l ∈ Finset.range (i - 1),
              (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1))
                * pLhs α (l + 1) h := by
        rw [MeasureTheory.integral_finsetSum]
        · refine Finset.sum_congr rfl (fun l hl => ?_)
          rw [MeasureTheory.integral_const_mul]
          rfl
        · intro l hl
          exact hint_Q l hl
      rw [hgam_eq, hsum]
      ring
    -- the bounds on the three pieces
    have hLIcc : (∑ m ∈ Finset.Icc 1 (i - 1), pGam α m h)
        ≤ ∑ m ∈ Finset.Icc 1 i, pGam α m h := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => pGam_nonneg α m h)
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨hm1, by omega⟩
    have hP1 : pGam α (i - 1) h ≤ ∑ m ∈ Finset.Icc 1 i, pGam α m h := by
      have hmem : i - 1 ∈ Finset.Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact Finset.single_le_sum (f := fun m => pGam α m h)
        (fun m _ => pGam_nonneg α m h) hmem
    have hXnn : 0 ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h :=
      add_nonneg (pEta_nonneg h) (Finset.sum_nonneg (fun m _ => pGam_nonneg α m h))
    have hP2 : (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.SinQ h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ Ceta * pEta h :=
      (levelZeroData hsm h0 hπ hD).2
    have hP3 : ∀ l ∈ Finset.range (i - 1),
        pLhs α (l + 1) h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
      intro l hl
      have hli : l + 1 ≤ i - 1 := by have := Finset.mem_range.mp hl; omega
      have hb := (hCb α h hα hα1 hsm h0 hπ hD (fun m hm1 hmi => hG m hm1 (by omega))
        (l + 1) (by omega) hli).2
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCpos.le
      have := Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc 1 (i - 1))
        (t := Finset.Icc 1 i) ?_ (fun m _ _ => pGam_nonneg α m h)
      · linarith [this]
      · intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        exact Finset.mem_Icc.mpr ⟨hm1, by omega⟩
    have hP3sum : (∑ l ∈ Finset.range (i - 1),
          (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)) * pLhs α (l + 1) h)
        ≤ Dsum * (C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)) := by
      rw [hDsumdef]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      exact mul_le_mul_of_nonneg_left (hP3 l hl)
        (mul_nonneg (sq_nonneg _) (hKl0 (l + 1)))
    -- the final arithmetic
    have hfinal : pLhs α i h ≤ (C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1)
        * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have h2i : (0 : ℝ) ≤ 2 * (i : ℝ) := by linarith
      have hZb : (2 * (i : ℝ)) * (M0 * (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.SinQ h θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          ≤ (2 * (i : ℝ)) * (M0 * (Ceta * pEta h)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP2 hM0pos.le) h2i
      have hQb : (2 * (i : ℝ)) * (∑ l ∈ Finset.range (i - 1),
            (((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)) * pLhs α (l + 1) h)
          ≤ (2 * (i : ℝ)) * (Dsum * (C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h))) :=
        mul_le_mul_of_nonneg_left hP3sum h2i
      have hgam : 2 * pGam α (i - 1) h ≤ 2 * (∑ m ∈ Finset.Icc 1 i, pGam α m h) := by linarith
      have hPE : 0 ≤ pEta h := pEta_nonneg h
      have hSG : 0 ≤ ∑ m ∈ Finset.Icc 1 i, pGam α m h :=
        Finset.sum_nonneg (fun m _ => pGam_nonneg α m h)
      -- step 1: reduce to the three-term bound
      have hstep : pLhs α i h ≤ 2 * (∑ m ∈ Finset.Icc 1 i, pGam α m h)
          + (2 * (i : ℝ)) * (M0 * (Ceta * pEta h))
          + (2 * (i : ℝ)) * (Dsum * (C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h))) := by
        have hmono' := hmono
        rw [hval] at hmono'
        linarith [hmono', hgam, hZb, hQb]
      -- step 2: rescale to the common factor `pEta h + Σ`
      have hX : (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) ≥ 0 := by linarith
      have h1 : (∑ m ∈ Finset.Icc 1 i, pGam α m h) ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h := by
        linarith
      have h2 : 2 * (∑ m ∈ Finset.Icc 1 i, pGam α m h)
          ≤ (2 : ℝ) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by linarith
      have h3 : (2 * (i : ℝ)) * (M0 * (Ceta * pEta h))
          ≤ (2 * (i : ℝ) * (M0 * Ceta)) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
        have hpe : pEta h ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h := by linarith
        have h1' : Ceta * pEta h ≤ Ceta * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) :=
          mul_le_mul_of_nonneg_left hpe hCeta_pos.le
        have h2' : M0 * (Ceta * pEta h)
            ≤ M0 * (Ceta * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)) :=
          mul_le_mul_of_nonneg_left h1' hM0pos.le
        calc (2 * (i : ℝ)) * (M0 * (Ceta * pEta h))
            ≤ (2 * (i : ℝ)) * (M0 * (Ceta * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h))) :=
              mul_le_mul_of_nonneg_left h2' h2i
          _ = (2 * (i : ℝ) * (M0 * Ceta)) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
              ring
      have hbound : pLhs α i h ≤ (2 + (2 * (i : ℝ) * (M0 * Ceta))
            + (2 * (i : ℝ)) * (Dsum * C)) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
        calc pLhs α i h
            ≤ 2 * (∑ m ∈ Finset.Icc 1 i, pGam α m h)
              + (2 * (i : ℝ)) * (M0 * (Ceta * pEta h))
              + (2 * (i : ℝ)) * (Dsum * (C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h))) :=
              hstep
          _ ≤ (2 : ℝ) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)
              + (2 * (i : ℝ) * (M0 * Ceta)) * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)
              + (2 * (i : ℝ)) * (Dsum * (C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h))) := by
              linarith [h2, h3]
          _ = (2 + (2 * (i : ℝ) * (M0 * Ceta)) + (2 * (i : ℝ)) * (Dsum * C))
                * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by ring
      have hcoef : (2 + (2 * (i : ℝ) * (M0 * Ceta)) + (2 * (i : ℝ)) * (Dsum * C))
          ≤ C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1 := by
        have hC1 : (0 : ℝ) ≤ C + 1 := by linarith
        have : 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)
            = 2 * (i : ℝ) * (M0 * Ceta) + 2 * (i : ℝ) * (Dsum * C) := by ring
        linarith [this]
      calc pLhs α i h
          ≤ (2 + (2 * (i : ℝ) * (M0 * Ceta)) + (2 * (i : ℝ)) * (Dsum * C))
              * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := hbound
        _ ≤ (C + (2 + 2 * (i : ℝ) * (M0 * Ceta + Dsum * C)) + 1)
              * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) :=
            mul_le_mul_of_nonneg_right hcoef hX
    exact hfinal

end Work.FTS.EllSol.PkgK5
