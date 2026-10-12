import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBogFS.ZPKernel.Bound
import Submission.Work.BoseBogFS.ZPKernel.Scale
import Submission.Work.BoseBogFS.ZPW1Facts
import Submission.Work.BoseBogFS.zBall_finite
import Submission.Work.BoseRowsL.Tails.integrable_chat_g0_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPKernel.Row`

The honest sharp lattice–Coulomb row at `W₁ = W1At v h μ`: the mass row of the
zero-point chapter.  Given the two telescoping inputs of `ZPKernel.Bound`, the row is the
composition

* the kernel bound (`kernelBound_of`) at the rescaled ball `‖nvec n‖ ≤ Kℓ/(2π)`;
* the `ℓ`-scaling of `kcal` (`kcalScale`);
* `reduction_core` (the Fourier pairing against `W₁ ⊗ W₁`);
* the untruncation `∫_{‖p‖≤K} ≤ ∫` (`setIntegral_le_integral`, from the finiteness of the
  position-space Coulomb energy).
-/

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseBogFS

set_option autoImplicit false

open Work.BoseRowsL.LatticeCoulomb

/-- A nonzero lattice vector has norm at least `1`. -/
lemma one_le_norm_nvec {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖nvec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : ((n i : ℤ) : ℝ) ^ 2 ≤ ‖nvec n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h3 := Finset.single_le_sum (f := fun j : Fin 3 => ‖(nvec n).ofLp j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    rw [nvec_apply, Real.norm_eq_abs, sq_abs] at h3
    exact h3
  nlinarith [norm_nonneg (nvec n), abs_nonneg ((n i : ℤ) : ℝ), sq_abs ((n i : ℤ) : ℝ)]

/-- The pointwise halving of the mass summand. -/
lemma mass_half (x y : ℝ) : x ^ 2 / (4 * y) = (1 / 2) * (x * x / (2 * y)) := by
  rw [sq, div_eq_mul_inv, div_eq_mul_inv]
  rw [show (4 : ℝ) * y = 2 * (2 * y) by ring, mul_inv]
  ring

/-- The mass row, from the two telescoping inputs. -/
theorem ZPMassLatticeRowHonest_of (hcos : CosBound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : ℝ³) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, n ≠ 0) →
          ∑ n ∈ S, (Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ)
              (Work.BoseBogFS.kAt v μ n)) ^ 2 / (4 * ‖Work.BoseBogFS.kAt v μ n‖ ^ 2)
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
                * (∫ p : ℝ³, (Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ) p) ^ 2
                    / (4 * ‖p‖ ^ 2))
              + C * (Work.BoseFixR.ell v μ) ^ 2
                  * (∫ x : ℝ³, Work.BoseBogFS.W1At v h μ x) ^ 2 := by
  obtain ⟨Ck, hCk0, hkernel⟩ := kernelBound_of hcos
  refine ⟨Ck / (16 * Real.pi ^ 2) + 1, by positivity, ?_⟩
  intro v h R hR hv hvrad hv_supp hav
  obtain ⟨ε₁, hε₁, hW1⟩ := ZPW1Facts (v := v) (h := h) (R := R) hR hv hvrad hv_supp hav
  obtain ⟨Cchi, hCchi0, r₁, hr₁, hT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  obtain ⟨ε₂, hε₂, hreg⟩ :=
    existsAdmRegime (v := v) (R := R) (C := Cchi) (r₁ := 1 / 4) hR hav hCchi0 (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hμ ρ hclose S hS
  have hμ1 : Work.BoseBoxFix.Adm v ε₁ μ := ⟨hμ.1, le_trans hμ.2.1 (min_le_left _ _), hμ.2.2⟩
  have hμ2 : Work.BoseBoxFix.Adm v ε₂ μ := ⟨hμ.1, le_trans hμ.2.1 (min_le_right _ _), hμ.2.2⟩
  obtain ⟨hWev, hWsupp, hWint, hWnn, hWpair, h4R, hMlo, hMhi⟩ := hW1 μ hμ1
  obtain ⟨hRchi, hRr, hCq⟩ := hreg μ hμ2
  have hℓ : 0 < Work.BoseFixR.ell v μ := by linarith
  set W : ℝ³ → ℝ := Work.BoseBogFS.W1At v h μ with hWdef
  have hsupp : Function.support W ⊆ Metric.closedBall 0 R := fun x hx =>
    Metric.ball_subset_closedBall (hWsupp (subset_tsupport _ hx))
  have hMass0 : 0 ≤ ∫ x, W x := integral_nonneg_of_ae hWnn
  -- integrability of the momentum density
  have hWfin := (Work.BoseRowsFS.W1_g0_finite (v := v) (R := R)
      (ℓ := Work.BoseFixR.ell v μ) hR hℓ hv hvrad hv_supp h hRchi).1
  have hInt2 : MeasureTheory.Integrable
      (fun q : ℝ³ => (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
    Work.BoseRowsL.Tails.chat_sq_div_integrable_of_coulomb_finite hWint hWnn hWfin
  have hInt4 : MeasureTheory.Integrable
      (fun q : ℝ³ => (Work.BoseFixR.chat W q) ^ 2 / (4 * ‖q‖ ^ 2)) := by
    have h := hInt2.const_mul (1 / 2 : ℝ)
    refine h.congr (Filter.Eventually.of_forall (fun q => ?_))
    simp only [div_eq_mul_inv]
    rw [show (4 : ℝ) * ‖q‖ ^ 2 = 2 * (2 * ‖q‖ ^ 2) by ring, mul_inv]
    ring
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.sum_empty]
    have h0 : 0 ≤ ∫ p : ℝ³, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2) :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall
        (fun p => div_nonneg (sq_nonneg _) (by positivity)))
    have hC0 : 0 ≤ Ck / (16 * Real.pi ^ 2) + 1 := by positivity
    have hℓ3 : 0 ≤ (Work.BoseFixR.ell v μ) ^ 3 := by positivity
    have hc0 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have h1 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
        * (∫ p : ℝ³, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2)) :=
      mul_nonneg (mul_nonneg hc0 hℓ3) h0
    have h2 : 0 ≤ (Ck / (16 * Real.pi ^ 2) + 1) * (Work.BoseFixR.ell v μ) ^ 2
        * (∫ x, W x) ^ 2 := mul_nonneg (mul_nonneg hC0 (sq_nonneg _)) (sq_nonneg _)
    linarith
  · simp only [Work.BoseBogFS.kAt]
    have hSne' : S.Nonempty := hSne
    obtain ⟨n0, hn0⟩ := hSne
    set K : ℝ := S.sup' hSne' (fun n => ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖) with hKdef
    have hKle : ∀ n ∈ S, ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ≤ K := fun n hn => by
      rw [hKdef]
      exact Finset.le_sup' (fun n => ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖) hn
    have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (hKle n0 hn0)
    have hKpos : 0 < K := by
      have h1n : (1 : ℝ) ≤ ‖nvec n0‖ := one_le_norm_nvec (hS n0 hn0)
      have hnorm : ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n0‖
          = (Work.BoseFixR.ell v μ)⁻¹ * (2 * Real.pi) * ‖nvec n0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ),
          Work.BoseRowsL.LatticeCoulomb.norm_vec_eq]
        ring
      have hL : (2 * Real.pi) / (Work.BoseFixR.ell v μ)
          = (Work.BoseFixR.ell v μ)⁻¹ * (2 * Real.pi) * 1 := by
        rw [div_eq_mul_inv]; ring
      have hkn : (2 * Real.pi) / (Work.BoseFixR.ell v μ)
          ≤ ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n0‖ := by
        rw [hnorm, hL]
        exact mul_le_mul_of_nonneg_left h1n (by positivity)
      have hpos : 0 < (2 * Real.pi) / Work.BoseFixR.ell v μ := by positivity
      linarith [hKle n0 hn0, hkn, hpos]
    have hTfin : (Work.BoseBogFS.zBall v μ K).Finite := Work.BoseBogFS.zBall_finite v μ K hℓ
    set T : Finset (Fin 3 → ℤ) := hTfin.toFinset with hTdef
    have hmemT : ∀ n, n ∈ T ↔ n ≠ 0 ∧
        ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ≤ K := by
      intro n
      rw [hTdef, Set.Finite.mem_toFinset]
      exact Work.BoseBogFS.mem_zBall
    have hST : S ⊆ T := fun n hn => (hmemT n).mpr ⟨hS n hn, hKle n hn⟩
    have h1' : ∀ n ∈ T, n ≠ 0 := fun n hn => ((hmemT n).mp hn).1
    have h2' : ∀ n ∈ T, ‖nvec n‖ ≤ K * Work.BoseFixR.ell v μ / (2 * Real.pi) :=
      fun n hn => (norm_inv_smul_vec_le_iff hℓ hKpos n).mp ((hmemT n).mp hn).2
    have h4' : ∀ n : Fin 3 → ℤ, n ≠ 0 →
        ‖nvec n‖ ≤ K * Work.BoseFixR.ell v μ / (2 * Real.pi) → n ∈ T :=
      fun n hn0 hnR => (hmemT n).mpr ⟨hn0, (norm_inv_smul_vec_le_iff hℓ hKpos n).mpr hnR⟩
    have hRk : 1 ≤ K * Work.BoseFixR.ell v μ / (2 * Real.pi) := by
      have h1n : (1 : ℝ) ≤ ‖nvec n0‖ := one_le_norm_nvec (hS n0 hn0)
      have hnorm : ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n0‖
          = (Work.BoseFixR.ell v μ)⁻¹ * (2 * Real.pi) * ‖nvec n0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ),
          Work.BoseRowsL.LatticeCoulomb.norm_vec_eq]
        ring
      have hL : (2 * Real.pi) / (Work.BoseFixR.ell v μ)
          = (Work.BoseFixR.ell v μ)⁻¹ * (2 * Real.pi) * 1 := by
        rw [div_eq_mul_inv]; ring
      have hkn : (2 * Real.pi) / (Work.BoseFixR.ell v μ) ≤ K := by
        rw [hL]
        exact le_trans (mul_le_mul_of_nonneg_left h1n (by positivity)) (by rw [← hnorm]; exact hKle n0 hn0)
      calc (1 : ℝ) = (2 * Real.pi) / Work.BoseFixR.ell v μ
              * (Work.BoseFixR.ell v μ / (2 * Real.pi)) := by
            field_simp
        _ ≤ K * (Work.BoseFixR.ell v μ / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_right hkn (by positivity)
        _ = K * Work.BoseFixR.ell v μ / (2 * Real.pi) := by ring
    -- the kernel bound at the rescaled ball
    set M : ℝ := (Work.BoseFixR.ell v μ) ^ 2 * Ck / (8 * Real.pi ^ 2) with hMdef
    have hMnn : 0 ≤ M := by rw [hMdef]; positivity
    have hker : ∀ w : ℝ³, ‖w‖ ≤ 2 * R →
        |Work.BoseRowsL.LatticeCoulomb.kcal T (Work.BoseFixR.ell v μ) K w| ≤ M := by
      intro w hw
      have hz : ‖(Work.BoseFixR.ell v μ)⁻¹ • w‖ ≤ 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
        rw [inv_mul_le_iff₀ hℓ]
        linarith
      have hb := hkernel (K * Work.BoseFixR.ell v μ / (2 * Real.pi)) T
        ((Work.BoseFixR.ell v μ)⁻¹ • w) hRk h1' h2' h4' hz
      rw [kcalScale T hℓ hKnn w]
      have hfac : (0 : ℝ) ≤ (Work.BoseFixR.ell v μ) ^ 2 / (8 * Real.pi ^ 2) := by positivity
      calc |(Work.BoseFixR.ell v μ) ^ 2 / (8 * Real.pi ^ 2) *
              ((∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n)
                    ((Work.BoseFixR.ell v μ)⁻¹ • w)) / ‖nvec n‖ ^ 2)
                - ∫ q in Metric.closedBall 0 (K * Work.BoseFixR.ell v μ / (2 * Real.pi)),
                    Real.cos (2 * Real.pi * inner ℝ q ((Work.BoseFixR.ell v μ)⁻¹ • w))
                      / ‖q‖ ^ 2)|
          = (Work.BoseFixR.ell v μ) ^ 2 / (8 * Real.pi ^ 2) *
              |((∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n)
                    ((Work.BoseFixR.ell v μ)⁻¹ • w)) / ‖nvec n‖ ^ 2)
                - ∫ q in Metric.closedBall 0 (K * Work.BoseFixR.ell v μ / (2 * Real.pi)),
                    Real.cos (2 * Real.pi * inner ℝ q ((Work.BoseFixR.ell v μ)⁻¹ • w))
                      / ‖q‖ ^ 2)| := by
            rw [abs_mul, abs_of_nonneg hfac]
        _ ≤ (Work.BoseFixR.ell v μ) ^ 2 / (8 * Real.pi ^ 2) * Ck :=
            mul_le_mul_of_nonneg_left hb hfac
        _ = M := by rw [hMdef]; ring
    have hred := Work.BoseRowsL.LatticeCoulomb.reduction_core T (Work.BoseFixR.ell v μ) K R M
      W W hMnn hker hWint hWint hsupp hsupp
    have hWabs : (∫ x, |W x|) = ∫ x, W x :=
      integral_congr_ae (hWnn.mono (fun x hx => abs_of_nonneg hx))
    -- the sum comparison
    have hsum1 : (∑ n ∈ S, (Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)) ^ 2
          / (4 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2))
        ≤ ∑ n ∈ T, (Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)) ^ 2
          / (4 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2) :=
      finset_sum_le_of_subset_of_nonneg hST (fun n _ => by positivity)
    have hsum2 : (∑ n ∈ T, (Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)) ^ 2
          / (4 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2))
        = (1 / 2) * ∑ n ∈ T, Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            / (2 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => mass_half _ _)
    -- the integral comparison
    have hint1 : (∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p) ^ 2
          / (4 * ‖p‖ ^ 2))
        ≤ ∫ p : ℝ³, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2) :=
      setIntegral_le_integral hInt4
        (Filter.Eventually.of_forall (fun p => div_nonneg (sq_nonneg _) (by positivity)))
    have hint2 : ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
          * (∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2))
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
          * (∫ p : ℝ³, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left hint1 (by positivity)
    have hint3 : (1 / 2) * ((Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
          * ∫ p in Metric.closedBall 0 K,
              Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2))
        = ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
          * (∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2)) := by
      have hpt : ∀ p : ℝ³, (1 / 2) * (Work.BoseFixR.chat W p * Work.BoseFixR.chat W p
            / (2 * ‖p‖ ^ 2)) = (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2) :=
        fun p => (mass_half (Work.BoseFixR.chat W p) (‖p‖ ^ 2)).symm
      have h1 : (∫ p in Metric.closedBall 0 K, (1 / 2) * (Work.BoseFixR.chat W p
            * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2)))
          = (1 / 2) * ∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p
            * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2)) := by
        rw [integral_const_mul]
      have h2 : (∫ p in Metric.closedBall 0 K, (1 / 2) * (Work.BoseFixR.chat W p
            * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2)))
          = ∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2) :=
        setIntegral_congr_fun measurableSet_closedBall (fun p _ => hpt p)
      rw [show (1 / 2) * (Work.BoseFixR.ell v μ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
            * ∫ p in Metric.closedBall 0 K,
                Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2))
          = Work.BoseFixR.ell v μ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
            * ((1 / 2) * ∫ p in Metric.closedBall 0 K,
                Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2)) by ring]
      rw [← h1, h2]
      ring
    have hred' : (∑ n ∈ T, Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
          * Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
          / (2 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2))
        ≤ (Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
            * (∫ p in Metric.closedBall 0 K,
                Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2))
          + M * (∫ x, W x) * (∫ x, W x) := by
      have habs : (∑ n ∈ T, Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            / (2 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2))
          - (Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
            * (∫ p in Metric.closedBall 0 K,
                Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2))
          ≤ M * (∫ x, W x) * (∫ x, W x) := by
        have h := (abs_le.mp hred).2
        rw [hWabs] at h
        exact h
      linarith only [habs]
    have hmass : (1 / 2) * (M * (∫ x, W x) * (∫ x, W x))
        ≤ (Ck / (16 * Real.pi ^ 2) + 1) * (Work.BoseFixR.ell v μ) ^ 2
            * (∫ x, W x) ^ 2 := by
      have h1 : (1 / 2) * (M * (∫ x, W x) * (∫ x, W x))
          = (Ck / (16 * Real.pi ^ 2)) * (Work.BoseFixR.ell v μ) ^ 2
            * (∫ x, W x) ^ 2 := by
        rw [hMdef]
        ring_nf
      rw [h1]
      have h2 : 0 ≤ (Work.BoseFixR.ell v μ) ^ 2 * (∫ x, W x) ^ 2 := by positivity
      have h3 : 1 * (Work.BoseFixR.ell v μ) ^ 2 * (∫ x, W x) ^ 2 = (Work.BoseFixR.ell v μ) ^ 2
          * (∫ x, W x) ^ 2 := by ring
      nlinarith [h2, h3, Real.pi_pos]
    calc (∑ n ∈ S, (Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)) ^ 2
          / (4 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2))
        ≤ (1 / 2) * ∑ n ∈ T, Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            * Work.BoseFixR.chat W ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n)
            / (2 * ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2) := by
          rw [hsum2] at hsum1
          exact hsum1
      _ ≤ (1 / 2) * ((Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹
            * (∫ p in Metric.closedBall 0 K,
                Work.BoseFixR.chat W p * Work.BoseFixR.chat W p / (2 * ‖p‖ ^ 2))
            + M * (∫ x, W x) * (∫ x, W x)) :=
          mul_le_mul_of_nonneg_left hred' (by norm_num)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * (∫ p in Metric.closedBall 0 K, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2))
          + (1 / 2) * (M * (∫ x, W x) * (∫ x, W x)) := by
          rw [mul_add, hint3]
      _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
            * (∫ p : ℝ³, (Work.BoseFixR.chat W p) ^ 2 / (4 * ‖p‖ ^ 2))
          + (Ck / (16 * Real.pi ^ 2) + 1) * (Work.BoseFixR.ell v μ) ^ 2
            * (∫ x, W x) ^ 2 := by
          linarith [hint2, hmass]

end Work.BoseBogFS
