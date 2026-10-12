import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Fourier.box3_neumann_heat_factor
import Submission.Commons.Analysis.Integral.integral_Ioi_exp_neg_mul
import Submission.Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
import Submission.Work.SmallBoxEwald
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-271 — the spectral chapter of the box-Neumann Laplacian
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 Definitions -/

/-- The mode eigenvalue `λ_k = Σ_j (π k_j / s)²`. -/
noncomputable def modeEig (s : ℝ) (k : Fin 3 → ℕ) : ℝ :=
  ∑ j : Fin 3, (Real.pi * (k j) / s) ^ 2

/-- The mode weight `(∏_j coordSqNorm s (k j))⁻¹`. -/
noncomputable def modeW (s : ℝ) (k : Fin 3 → ℕ) : ℝ :=
  (∏ j : Fin 3, coordSqNorm s (k j))⁻¹

/-- The spectral kernel term. -/
noncomputable def modeTerm (s t : ℝ) (k : Fin 3 → ℕ) (x y : ℝ³) : ℝ :=
  modeW s k * boxNeumann3 s k x * boxNeumann3 s k y * Real.exp (-(t * modeEig s k))

/-- The mode Fourier coefficient `∫ x, boxNeumann3 s k x · W x`. -/
noncomputable def modeFourier (s : ℝ) (k : Fin 3 → ℕ) (W : ℝ³ → ℝ) : ℝ :=
  ∫ x : ℝ³, boxNeumann3 s k x * W x

/-! ## 2 Basic facts -/

lemma modeEig_zero (s : ℝ) : modeEig s 0 = 0 := by
  simp [modeEig]

lemma modeW_zero (s : ℝ) : modeW s 0 = (s ^ 3)⁻¹ := by
  rw [modeW]
  norm_num [coordSqNorm, Fin.prod_univ_three]

lemma modeW_nonneg {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) : 0 ≤ modeW s k := by
  rw [modeW, inv_nonneg]
  exact Finset.prod_nonneg fun j _ => (coordSqNorm_pos hs (k j)).le

lemma modeW_pos {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) : 0 < modeW s k := by
  rw [modeW, inv_pos]
  exact Finset.prod_pos fun j _ => coordSqNorm_pos hs (k j)

/-- the mode weight is bounded by `8/s³`. -/
lemma modeW_le {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) : modeW s k ≤ 8 / s ^ 3 := by
  have h1 : (s / 2) ^ 3 ≤ ∏ j : Fin 3, coordSqNorm s (k j) := by
    calc (s / 2) ^ 3 = ∏ _j : Fin 3, (s / 2) := by
          rw [Fin.prod_univ_three]; ring
      _ ≤ ∏ j : Fin 3, coordSqNorm s (k j) := by
          apply Finset.prod_le_prod₀
          · intro j _; positivity
          · intro j _
            rw [coordSqNorm]
            split
            · linarith
            · linarith
  have h2 : ((s / 2) ^ 3)⁻¹ = 8 / s ^ 3 := by field_simp; ring
  rw [modeW, ← h2]
  exact inv_anti₀ (by positivity) h1

lemma modeEig_nonneg (s : ℝ) (k : Fin 3 → ℕ) : 0 ≤ modeEig s k :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma modeEig_pos {s : ℝ} (hs : 0 < s) {k : Fin 3 → ℕ} (hk : k ≠ 0) :
    0 < modeEig s k := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, k j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  rw [modeEig]
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
  have hj' : (0 : ℝ) < (k j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
  have h1 : 0 < Real.pi * (k j) / s := div_pos (mul_pos Real.pi_pos hj') hs
  exact pow_pos h1 2

/-! ## 3 The spectral expansion of the heat kernel (S1) -/

/-- `∏ j, A j * B j * C j * D j = (∏A)(∏B)(∏C)(∏D)`. -/
private lemma prod_four (A B C D : Fin 3 → ℝ) :
    (∏ j : Fin 3, (A j * (B j * C j) * D j))
      = (∏ j : Fin 3, A j) * (∏ j : Fin 3, B j) * (∏ j : Fin 3, C j) * (∏ j : Fin 3, D j) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- **S1: the spectral expansion of the box Neumann heat kernel.** -/
theorem boxHeat3_eq_modeSum (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : ℝ³) :
    boxHeat3 s t x y = ∑' k : Fin 3 → ℕ, modeTerm s t k x y := by
  set F : Fin 3 → ℕ → ℝ := fun j m =>
    (coordSqNorm s m)⁻¹ * (boxNeumann s m (x j) * boxNeumann s m (y j))
      * Real.exp (-(t * (Real.pi * m / s) ^ 2)) with hFdef
  have hone : ∀ j : Fin 3, neuHeat1 s t (x j) (y j) = ∑' m : ℕ, F j m := by
    intro j
    rw [neuHeat1]
    apply tsum_congr
    intro m
    simp only [hFdef, coordSqNorm, boxNeumann]
    rw [show Real.pi * ↑m * (x j + s / 2) / s = (↑m * Real.pi / s) * (x j + s / 2) by ring,
        show Real.pi * ↑m * (y j + s / 2) / s = (↑m * Real.pi / s) * (y j + s / 2) by ring]
    ring
  have hsumm : ∀ j : Fin 3, Summable fun m => ‖F j m‖ := by
    intro j
    have hbase : Summable fun m : ℕ => Real.exp (-(t * (Real.pi / s) ^ 2) * (m : ℝ) ^ 2) := by
      refine Real.summable_exp_nat_mul_of_ge ?_ (fun i => ?_)
      · have h : 0 < t * (Real.pi / s) ^ 2 := by positivity
        linarith
      · rcases i with _ | i
        · simp
        · push_cast
          have h : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          nlinarith
    set M : ℝ := max s⁻¹ (s / 2)⁻¹ with hM
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hbase.mul_left M)
    set w : ℝ := (coordSqNorm s m)⁻¹ with hwdef
    set E : ℝ := Real.exp (-(t * (Real.pi * (m : ℝ) / s) ^ 2)) with hEdef
    have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
    have hwnn : 0 ≤ w := by
      rw [hwdef, coordSqNorm]; split <;> positivity
    have hwb : w ≤ M := by
      rw [hwdef, hM, coordSqNorm]; split
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hb1 : |boxNeumann s m (x j)| ≤ 1 := by
      rw [boxNeumann]; exact Real.abs_cos_le_one _
    have hb2 : |boxNeumann s m (y j)| ≤ 1 := by
      rw [boxNeumann]; exact Real.abs_cos_le_one _
    have hprod2 : |boxNeumann s m (x j)| * |boxNeumann s m (y j)| ≤ 1 := by
      nlinarith [hb1, hb2, abs_nonneg (boxNeumann s m (x j)), abs_nonneg (boxNeumann s m (y j))]
    have hwnn' : 0 ≤ (coordSqNorm s m)⁻¹ := by rw [← hwdef]; exact hwnn
    have hnorm : ‖F j m‖ = w * (|boxNeumann s m (x j)| * |boxNeumann s m (y j)|) * E := by
      rw [Real.norm_eq_abs, hFdef]
      dsimp only
      rw [abs_mul, abs_mul, abs_mul, hwdef, hEdef, abs_of_pos hEpos, abs_of_nonneg hwnn']
    calc ‖F j m‖
        = w * (|boxNeumann s m (x j)| * |boxNeumann s m (y j)|) * E := hnorm
      _ ≤ w * 1 * E := by
          refine mul_le_mul_of_nonneg_right ?_ hEpos.le
          exact mul_le_mul_of_nonneg_left hprod2 hwnn
      _ ≤ M * 1 * E := by
          refine mul_le_mul_of_nonneg_right ?_ hEpos.le
          exact mul_le_mul_of_nonneg_right hwb (by norm_num)
      _ = M * Real.exp (-(t * (Real.pi / s) ^ 2) * (m : ℝ) ^ 2) := by
          rw [hEdef]; ring
  have hprod : boxHeat3 s t x y = ∏ j : Fin 3, ∑' m : ℕ, F j m := by
    rw [boxHeat3]
    exact Finset.prod_congr rfl fun j _ => (hone j)
  rw [hprod, ← Commons.Analysis.Fourier.tsum_fin3_prod F hsumm]
  apply tsum_congr
  intro k
  simp only [modeTerm, modeW, modeEig, boxNeumann3]
  rw [show Real.exp (-(t * ∑ j : Fin 3, (Real.pi * (k j) / s) ^ 2))
        = ∏ j : Fin 3, Real.exp (-(t * (Real.pi * (k j) / s) ^ 2)) from by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.sum_neg_distrib, Finset.mul_sum],
      ← Finset.prod_inv_distrib]
  have key : (∏ j : Fin 3, F j (k j))
      = (∏ j : Fin 3, (coordSqNorm s (k j))⁻¹) * (∏ j : Fin 3, boxNeumann s (k j) (x j))
        * (∏ j : Fin 3, boxNeumann s (k j) (y j))
        * (∏ j : Fin 3, Real.exp (-(t * (Real.pi * (k j) / s) ^ 2))) := by
    rw [hFdef]
    exact prod_four (fun j => (coordSqNorm s (k j))⁻¹)
      (fun j => boxNeumann s (k j) (x j)) (fun j => boxNeumann s (k j) (y j))
      (fun j => Real.exp (-(t * (Real.pi * (k j) / s) ^ 2)))
  rw [key]

/-! ## 4 Summability of the spectral series and removal of the `k = 0` term -/

private lemma summable_exp_gauss_nat {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 2) := by
  refine Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
    (f := fun i : ℕ => (i : ℝ) ^ 2) (fun i => ?_)
  rcases i with _ | i
  · simp
  · push_cast
    have h : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith

/-- The pi-product of one-dimensional Gaussian series is summable: the
`tsum`-junk-value trick (a `tsum` is `0` for a non-summable series, so a
nonzero value forces summability) turns `tsum_fin3_prod` into summability. -/
theorem summable_pi_gauss_fin3 {c : ℝ} (hc : 0 < c) :
    Summable fun k : Fin 3 → ℕ => ∏ j : Fin 3, Real.exp (-c * ((k j : ℝ)) ^ 2) := by
  have hF : ∀ j : Fin 3, Summable fun m : ℕ => ‖Real.exp (-c * (m : ℝ) ^ 2)‖ := by
    intro j
    refine (summable_exp_gauss_nat hc).congr (fun m => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_contra hcon
  have h := Commons.Analysis.Fourier.tsum_fin3_prod
    (fun (_ : Fin 3) (m : ℕ) => Real.exp (-c * (m : ℝ) ^ 2)) hF
  rw [tsum_eq_zero_of_not_summable hcon] at h
  have hpos : 0 < ∏ j : Fin 3, ∑' m : ℕ, Real.exp (-c * (m : ℝ) ^ 2) :=
    Finset.prod_pos fun j _ =>
      (summable_exp_gauss_nat hc).tsum_pos (fun m => (Real.exp_pos _).le) 0 (by simp)
  exact hpos.ne' h.symm

lemma modeEig_eq (s : ℝ) (k : Fin 3 → ℕ) :
    modeEig s k = (Real.pi / s) ^ 2 * ∑ j : Fin 3, ((k j : ℝ)) ^ 2 := by
  rw [modeEig, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma sum_neg_lin (t a : ℝ) (k : Fin 3 → ℕ) :
    (∑ j : Fin 3, -(t * a) * ((k j : ℝ)) ^ 2) = -(t * (a * ∑ j : Fin 3, ((k j : ℝ)) ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- the exponential factor of `modeTerm` in product form. -/
lemma exp_neg_modeEig_eq_prod (s t : ℝ) (k : Fin 3 → ℕ) :
    Real.exp (-(t * modeEig s k))
      = ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
  rw [modeEig_eq, ← Real.exp_sum]
  congr 1
  exact (sum_neg_lin t ((Real.pi / s) ^ 2) k).symm

/-- the norm bound of the spectral term. -/
lemma modeTerm_norm_le {s t : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) (x y : ℝ³) :
    ‖modeTerm s t k x y‖
      ≤ (8 / s ^ 3) * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
  set E : ℝ := ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) with hE
  have hEpos : 0 < E := by
    rw [hE]; exact Finset.prod_pos fun j _ => Real.exp_pos _
  have hw : |modeW s k| ≤ 8 / s ^ 3 := by
    rw [abs_of_nonneg (modeW_nonneg hs k)]; exact modeW_le hs k
  have hb1 : |boxNeumann3 s k x| ≤ 1 := boxNeumann3_abs_le_one k x
  have hb2 : |boxNeumann3 s k y| ≤ 1 := boxNeumann3_abs_le_one k y
  have h8 : 0 ≤ 8 / s ^ 3 := by positivity
  have h1 : |boxNeumann3 s k x| * |boxNeumann3 s k y| ≤ 1 := by
    nlinarith [hb1, hb2, abs_nonneg (boxNeumann3 s k x), abs_nonneg (boxNeumann3 s k y)]
  rw [Real.norm_eq_abs, modeTerm, exp_neg_modeEig_eq_prod]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos hEpos]
  calc |modeW s k| * |boxNeumann3 s k x| * |boxNeumann3 s k y| * E
      = |modeW s k| * (|boxNeumann3 s k x| * |boxNeumann3 s k y|) * E := by ring
    _ ≤ (8 / s ^ 3) * 1 * E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hw h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) h8) hEpos.le
    _ = (8 / s ^ 3) * E := by ring

lemma summable_modeTerm {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : ℝ³) :
    Summable fun k : Fin 3 → ℕ => modeTerm s t k x y := by
  have hc : 0 < t * (Real.pi / s) ^ 2 := by positivity
  refine Summable.of_norm_bounded ((summable_pi_gauss_fin3 hc).mul_left (8 / s ^ 3))
    (fun k => modeTerm_norm_le hs k x y)

lemma modeTerm_zero (s t : ℝ) (x y : ℝ³) : modeTerm s t 0 x y = (s ^ 3)⁻¹ := by
  have hx : boxNeumann3 s 0 x = 1 := by
    rw [boxNeumann3, Fin.prod_univ_three]
    simp [boxNeumann_zero]
  have hy : boxNeumann3 s 0 y = 1 := by
    rw [boxNeumann3, Fin.prod_univ_three]
    simp [boxNeumann_zero]
  rw [modeTerm, modeW_zero, modeEig_zero, mul_zero, neg_zero, Real.exp_zero, hx, hy]
  ring

/-- **S1', the spectral expansion with the `k = 0` term removed.** -/
theorem boxHeat3_sub_eq_modeSum (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : ℝ³) :
    boxHeat3 s t x y - (s ^ 3)⁻¹
      = ∑' k : Fin 3 → ℕ, (if k = 0 then 0 else modeTerm s t k x y) := by
  have hsum := summable_modeTerm (s := s) (t := t) hs ht x y
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : Fin 3 → ℕ)
  rw [boxHeat3_eq_modeSum s t hs ht x y, hsplit, modeTerm_zero]
  ring

/-! ## 5 The per-`t` Fubini identity -/

/-- the spectral sharp-mass term. -/
noncomputable def modeSharpTerm (s t : ℝ) (k : Fin 3 → ℕ) (W : ℝ³ → ℝ) : ℝ :=
  modeW s k * (modeFourier s k W) ^ 2 * Real.exp (-(t * modeEig s k))

/-- the spectral kernel with the `k = 0` mode removed. -/
noncomputable def modeSharpKernel (s t : ℝ) (k : Fin 3 → ℕ) (p : ℝ³ × ℝ³) : ℝ :=
  if k = 0 then 0 else modeTerm s t k p.1 p.2

/-- the box-mode spectral sharp mass `Σ_{k ≠ 0} λ_k⁻¹ ⟨W, ê_k⟩²`. -/
noncomputable def modeSharpMass (s : ℝ) (W : ℝ³ → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℕ, if k = 0 then 0 else modeW s k * (modeFourier s k W) ^ 2 / modeEig s k

lemma modeSharpKernel_eq_zero {s t : ℝ} {k : Fin 3 → ℕ} (hk : k = 0) (p : ℝ³ × ℝ³) :
    modeSharpKernel s t k p = 0 := by
  unfold modeSharpKernel; rw [if_pos hk]

lemma modeSharpKernel_eq_modeTerm {s t : ℝ} {k : Fin 3 → ℕ} (hk : k ≠ 0) (p : ℝ³ × ℝ³) :
    modeSharpKernel s t k p = modeTerm s t k p.1 p.2 := by
  unfold modeSharpKernel; rw [if_neg hk]

lemma modeSharpKernel_norm_le {s t : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) (p : ℝ³ × ℝ³) :
    ‖modeSharpKernel s t k p‖
      ≤ (8 / s ^ 3) * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
  by_cases hk : k = 0
  · rw [modeSharpKernel_eq_zero hk, norm_zero]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
  · rw [modeSharpKernel_eq_modeTerm hk]
    exact modeTerm_norm_le hs k p.1 p.2

lemma continuous_modeSharpKernel (s t : ℝ) (k : Fin 3 → ℕ) :
    Continuous fun p : ℝ³ × ℝ³ => modeSharpKernel s t k p := by
  by_cases hk : k = 0
  · have : (fun p : ℝ³ × ℝ³ => modeSharpKernel s t k p) = fun _ => (0 : ℝ) := by
      funext p; rw [modeSharpKernel_eq_zero hk]
    rw [this]; exact continuous_const
  · have : (fun p : ℝ³ × ℝ³ => modeSharpKernel s t k p)
        = fun p => modeTerm s t k p.1 p.2 := by
      funext p; rw [modeSharpKernel_eq_modeTerm hk]
    rw [this]
    unfold modeTerm modeW boxNeumann3 boxNeumann
    fun_prop

lemma modeEig_ne_zero {s : ℝ} (hs : 0 < s) {k : Fin 3 → ℕ} (hk : k ≠ 0) :
    modeEig s k ≠ 0 := ne_of_gt (modeEig_pos hs hk)

/-- the per-mode double-integral identity. -/
lemma integral_modeSharpKernel {W : ℝ³ → ℝ} (hWint : Integrable W) (s t : ℝ) (k : Fin 3 → ℕ) :
    (∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * modeSharpKernel s t k p)
      = (if k = 0 then 0 else modeSharpTerm s t k W) := by
  have hv : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
  by_cases hk : k = 0
  · rw [if_pos hk]
    have : (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * modeSharpKernel s t k p)
        = fun _ : ℝ³ × ℝ³ => (0 : ℝ) := by
      funext p; rw [modeSharpKernel_eq_zero hk, mul_zero]
    rw [this, hv]
    simp
  · rw [if_neg hk]
    rw [hv]
    set F : ℝ³ → ℝ := fun x => W x * boxNeumann3 s k x with hFdef
    set C : ℝ := modeW s k * Real.exp (-(t * modeEig s k)) with hCdef
    have hpt : (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * modeSharpKernel s t k p)
        = fun p : ℝ³ × ℝ³ => F p.1 * F p.2 * C := by
      funext p
      rw [modeSharpKernel_eq_modeTerm hk, hFdef, hCdef, modeTerm]
      ring
    rw [hpt, MeasureTheory.integral_mul_const, MeasureTheory.integral_prod_mul]
    rw [show (∫ x, F x) = modeFourier s k W from by
      rw [hFdef, modeFourier]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
    rw [hCdef, modeSharpTerm]
    ring

lemma integrable_modeSharpKernel_mul {W : ℝ³ → ℝ} (hWint : Integrable W) {s t : ℝ}
    (hs : 0 < s) (k : Fin 3 → ℕ) :
    Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * modeSharpKernel s t k p) volume := by
  have hv : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
  rw [hv]
  have hH : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2) ((volume : Measure ℝ³).prod volume) :=
    hWint.mul_prod hWint
  refine hH.mul_bdd (c := (8 / s ^ 3) * ∏ j : Fin 3,
      Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2))
    (continuous_modeSharpKernel s t k).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => modeSharpKernel_norm_le hs k p

/-- **the per-`t` Fubini identity.** -/
theorem tsum_modeSharpTerm_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {W : ℝ³ → ℝ}
    (hWint : Integrable W) :
    (∑' k : Fin 3 → ℕ, if k = 0 then 0 else modeSharpTerm s t k W)
      = ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹) := by
  have hc : 0 < t * (Real.pi / s) ^ 2 := by positivity
  have hsumm : Summable fun k : Fin 3 → ℕ =>
      ∫ p : ℝ³ × ℝ³, ‖W p.1 * W p.2 * modeSharpKernel s t k p‖ := by
    have hb : ∀ k : Fin 3 → ℕ, (∫ p : ℝ³ × ℝ³, ‖W p.1 * W p.2 * modeSharpKernel s t k p‖)
        ≤ (8 / s ^ 3 * (∫ x, ‖W x‖) ^ 2)
          * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
      intro k
      have hv : (volume : Measure (ℝ³ × ℝ³)) = (volume : Measure ℝ³).prod volume := rfl
      set G : ℝ³ → ℝ := fun x => ‖W x‖ with hGdef
      set H : ℝ³ → ℝ := fun x => ‖W x‖
        * ((8 / s ^ 3) * ∏ j : Fin 3,
            Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2)) with hHdef
      calc (∫ p : ℝ³ × ℝ³, ‖W p.1 * W p.2 * modeSharpKernel s t k p‖
              ∂((volume : Measure ℝ³).prod volume))
          ≤ ∫ p : ℝ³ × ℝ³, G p.1 * H p.2 ∂((volume : Measure ℝ³).prod volume) := by
            refine integral_mono_of_nonneg ?_ ?_ ?_
            · exact Filter.Eventually.of_forall fun p => norm_nonneg _
            · rw [hGdef, hHdef]
              exact hWint.norm.mul_prod (hWint.norm.mul_const _)
            · filter_upwards with p
              have hp := modeSharpKernel_norm_le (t := t) hs k p
              rw [hGdef, hHdef, norm_mul, norm_mul, mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (norm_nonneg _)
        _ = (8 / s ^ 3 * (∫ x, ‖W x‖) ^ 2)
              * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
            rw [MeasureTheory.integral_prod_mul]
            simp only [hGdef, hHdef]
            rw [MeasureTheory.integral_mul_const]
            ring
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun p => norm_nonneg _) hb ?_
    have h := (summable_pi_gauss_fin3 hc).mul_left (8 / s ^ 3 * (∫ x, ‖W x‖) ^ 2)
    simpa only [mul_assoc] using h
  have hint : ∀ k : Fin 3 → ℕ,
      Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * modeSharpKernel s t k p) volume :=
    fun k => integrable_modeSharpKernel_mul hWint hs k
  have hhas := hasSum_integral_of_summable_integral_norm
    (F := fun (k : Fin 3 → ℕ) (p : ℝ³ × ℝ³) => W p.1 * W p.2 * modeSharpKernel s t k p)
    hint hsumm
  have htsum := hhas.tsum_eq
  have hL : (∑' k : Fin 3 → ℕ, if k = 0 then 0 else modeSharpTerm s t k W)
      = ∑' k : Fin 3 → ℕ,
          ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * modeSharpKernel s t k p := by
    apply tsum_congr
    intro k
    exact (integral_modeSharpKernel hWint s t k).symm
  rw [hL, htsum]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  rw [show (∑' k : Fin 3 → ℕ, W p.1 * W p.2 * modeSharpKernel s t k p)
      = W p.1 * W p.2 * ∑' k : Fin 3 → ℕ, modeSharpKernel s t k p from by
        rw [tsum_mul_left]]
  rw [show (∑' k : Fin 3 → ℕ, modeSharpKernel s t k p)
      = boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹ from by
        rw [boxHeat3_sub_eq_modeSum s t hs ht p.1 p.2]
        exact tsum_congr fun k => by
          by_cases hk : k = 0
          · rw [modeSharpKernel_eq_zero hk]; simp [hk]
          · rw [modeSharpKernel_eq_modeTerm hk]; simp [hk]]

/-! ## 6 The `t`-side: integrability of the heat-kernel difference -/

private lemma integrableOn_heat_exp_form {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t)))
      (Set.Ioi 0) := by
  have hval := Commons.Analysis.Integral.integral_heat_exp_neg hc
  by_contra h
  rw [integral_undef h] at hval
  have hpos : 0 < 1 / (8 * Real.pi * Real.sqrt c) := by positivity
  linarith

private lemma inv_s_le' {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s) :
    s⁻¹ ≤ 2 / δ := by
  have h2d : (0 : ℝ) < 2 * δ := by linarith
  have h5 : s⁻¹ ≤ (2 * δ)⁻¹ := (inv_le_inv₀ hs h2d).mpr hδs
  have h6 : (2 * δ)⁻¹ ≤ 2 / δ := by
    rw [mul_inv, div_eq_mul_inv]
    nlinarith [inv_pos.mpr hδ]
  linarith

/-- the `t`-lintegral of `|boxHeat3 s t x y − s^{-3}|` is bounded by
`C/δ + (4π‖x−y‖)^{-1}` on the `δ`-inner region. -/
theorem lintegral_boxHeat3_sub_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    {x y : ℝ³} (hxy : x ≠ y) (hx : ∀ j, |x j| ≤ s / 2 - δ)
    (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
      ≤ ENNReal.ofReal (400 / δ + (4 * Real.pi * ‖x - y‖)⁻¹) := by
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hb : 0 < (Real.pi / s) ^ 2 := by positivity
  have hδne : δ ≠ 0 := ne_of_gt hδ
  set A : ℝ → ℝ := fun t => 7000 * ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)))
    with hAdef
  set B : ℝ → ℝ := fun t => freeHeat3 t x y with hBdef
  set Cc : ℝ := (s ^ 3)⁻¹ with hCdef
  set W : ℝ → ℝ := fun t => A t + B t + Cc with hWdef
  have hA : IntegrableOn A (Set.Ioc 0 (s ^ 2)) := by
    simp only [hAdef]
    exact ((integrableOn_heat_exp_form hδ2).mono_set Set.Ioc_subset_Ioi_self).const_mul 7000
  have hB : IntegrableOn B (Set.Ioc 0 (s ^ 2)) := by
    simp only [hBdef]
    exact (integrableOn_freeHeat3 hxy).mono_set Set.Ioc_subset_Ioi_self
  have hC : IntegrableOn (fun _ : ℝ => Cc) (Set.Ioc 0 (s ^ 2)) := by
    simp only [hCdef]
    exact integrableOn_const (C := (s ^ 3)⁻¹)
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hW : IntegrableOn W (Set.Ioc 0 (s ^ 2)) := by
    simp only [hWdef]
    exact (hA.add hB).add hC
  -- the small-`t` half
  have hsmall : (∫⁻ t in Set.Ioc (0 : ℝ) (s ^ 2),
        ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
      ≤ ENNReal.ofReal (300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ) := by
    have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) (s ^ 2))),
        ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹| ≤ ENNReal.ofReal (W t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have h1 : |boxHeat3 s t x y - freeHeat3 t x y| ≤ A t := by
        simp only [hAdef]
        simpa only [mul_assoc] using boxHeat3_sub_freeHeat3_le hs ht0 hδ hδs ht.2 x y hx hy
      have h2 : 0 ≤ B t := by simp only [hBdef]; exact freeHeat3_nonneg t ht0 x y
      have h3 : 0 ≤ Cc := by simp only [hCdef]; positivity
      have h5 : |freeHeat3 t x y - (s ^ 3)⁻¹| ≤ B t + Cc := by
        have hB' : B t = freeHeat3 t x y := by simp only [hBdef]
        rw [abs_le]
        constructor
        · rw [hB']; linarith
        · rw [hB']; linarith
      have h6 : boxHeat3 s t x y - (s ^ 3)⁻¹
          = (boxHeat3 s t x y - freeHeat3 t x y) + (freeHeat3 t x y - (s ^ 3)⁻¹) := by ring
      have h7 : W t = A t + (B t + Cc) := by simp only [hWdef]; ring
      rw [h7, h6, ENNReal.ofReal_le_ofReal_iff
        (by linarith [h1, h2, h3, abs_nonneg (boxHeat3 s t x y - freeHeat3 t x y)])]
      exact le_trans (abs_add_le _ _) (by linarith [h1, h5])
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (s ^ 2))] W := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have h1 : 0 ≤ A t := by
        simp only [hAdef]
        exact mul_nonneg (by norm_num) (mul_nonneg
          (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi * t) _) (Real.exp_pos _).le)
      have h2 : 0 ≤ B t := by simp only [hBdef]; exact freeHeat3_nonneg t ht0 x y
      have h3 : 0 ≤ Cc := by simp only [hCdef]; positivity
      simp only [hWdef]
      exact add_nonneg (add_nonneg h1 h2) h3
    have h1 := lintegral_mono_ae hpt
    rw [← ofReal_integral_eq_lintegral_ofReal hW hnn] at h1
    refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
    have hAB : Integrable (fun t : ℝ => A t + B t) (volume.restrict (Set.Ioc 0 (s ^ 2))) :=
      hA.add hB
    have hCc : Integrable (fun _ : ℝ => Cc) (volume.restrict (Set.Ioc 0 (s ^ 2))) := hC
    have hW2 : (fun t : ℝ => A t + B t + Cc) = W := by simp only [hWdef]
    rw [← hW2, MeasureTheory.integral_add hAB hCc, MeasureTheory.integral_add hA hB]
    have hb1 : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), A t) ≤ 7000 / (8 * Real.pi * δ) := by
      have hmono : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2),
            (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)))
          ≤ ∫ t in Set.Ioi (0 : ℝ),
            (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)) :=
        setIntegral_mono_set (s := Set.Ioc 0 (s ^ 2)) (t := Set.Ioi 0) (μ := volume)
          (integrableOn_heat_exp_form hδ2)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : 0 < t := ht
            exact mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi * t) _)
              (Real.exp_pos _).le)
          Set.Ioc_subset_Ioi_self.eventuallyLE
      have hval : (∫ t in Set.Ioi (0 : ℝ),
            (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)))
          = 1 / (8 * Real.pi * δ) := by
        rw [Commons.Analysis.Integral.integral_heat_exp_neg hδ2, Real.sqrt_sq hδ.le]
      calc (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), A t)
          = 7000 * (∫ t in Set.Ioc (0 : ℝ) (s ^ 2),
              (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t))) := by
            simp only [hAdef]; rw [MeasureTheory.integral_const_mul]
        _ ≤ 7000 * (∫ t in Set.Ioi (0 : ℝ),
              (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t))) :=
            mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ = 7000 / (8 * Real.pi * δ) := by rw [hval]; ring
    have hb2 : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), B t) ≤ (4 * Real.pi * ‖x - y‖)⁻¹ := by
      have hmono : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), freeHeat3 t x y)
          ≤ ∫ t in Set.Ioi (0 : ℝ), freeHeat3 t x y :=
        setIntegral_mono_set (s := Set.Ioc 0 (s ^ 2)) (t := Set.Ioi 0) (μ := volume)
          (integrableOn_freeHeat3 hxy)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact freeHeat3_nonneg t ht x y)
          Set.Ioc_subset_Ioi_self.eventuallyLE
      rw [integral_freeHeat3 hxy] at hmono
      simpa only [hBdef] using hmono
    have hb3 : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), Cc) = Cc * s ^ 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ s ^ 2)]
      ring
    rw [hb3]
    have harith : 7000 / (8 * Real.pi * δ) + (4 * Real.pi * ‖x - y‖)⁻¹ + Cc * s ^ 2
        ≤ 300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ := by
      have h1 : 7000 / (8 * Real.pi * δ) ≤ 300 / δ := by
        rw [div_le_div_iff₀ (by positivity) hδ]
        nlinarith [Real.pi_gt_three]
      have h2 : Cc * s ^ 2 ≤ 2 / δ := by
        have hCc : Cc = (s ^ 3)⁻¹ := hCdef
        rw [hCc, inv_mul_eq_div]
        have heq : s ^ 2 / s ^ 3 = s⁻¹ := by
          rw [div_eq_iff (by positivity : s ^ 3 ≠ 0)]
          field_simp
        rw [heq]
        exact inv_s_le' hs hδ hδs
      linarith [h1, h2]
    linarith [hb1, hb2, harith]
  -- the large-`t` half
  have htail : (∫⁻ t in Set.Ioi (s ^ 2), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
      ≤ ENNReal.ofReal (4 / δ) := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(t * (Real.pi / s) ^ 2)))
        (Set.Ioi (s ^ 2)) := by
      have h := exp_neg_integrableOn_Ioi (s ^ 2) hb
      simpa [mul_comm, neg_mul] using h
    set D : ℝ → ℝ := fun t => 48 * (s ^ 3)⁻¹ * Real.exp (-(t * (Real.pi / s) ^ 2)) with hDdef
    have hD : IntegrableOn D (Set.Ioi (s ^ 2)) := by
      simp only [hDdef]; exact hexp.const_mul _
    have hnnD : 0 ≤ᵐ[volume.restrict (Set.Ioi (s ^ 2))] D := by
      filter_upwards with t
      simp only [hDdef]
      exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (Real.exp_pos _).le
    have hptD : ∀ᵐ t ∂(volume.restrict (Set.Ioi (s ^ 2))),
        ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹| ≤ ENNReal.ofReal (D t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [hDdef]
      exact ENNReal.ofReal_le_ofReal (boxHeat3_sub_le hs ht.le x y)
    have hvalD : (∫ t in Set.Ioi (s ^ 2), D t)
        = 48 * s⁻¹ * Real.exp (-(Real.pi ^ 2)) / Real.pi ^ 2 := by
      simp only [hDdef]
      rw [MeasureTheory.integral_const_mul]
      have h1 : (fun t : ℝ => Real.exp (-(t * (Real.pi / s) ^ 2)))
          = fun t : ℝ => Real.exp ((-((Real.pi / s) ^ 2)) * t) := by funext t; ring_nf
      rw [h1, integral_exp_mul_Ioi (a := -((Real.pi / s) ^ 2)) (by
        have hp : 0 < (Real.pi / s) ^ 2 := by positivity
        linarith) (s ^ 2)]
      have h2 : -((Real.pi / s) ^ 2) * s ^ 2 = -(Real.pi ^ 2) := by
        rw [div_pow]; field_simp
      rw [h2, show -((Real.pi / s) ^ 2) = -(Real.pi ^ 2 / s ^ 2) by rw [div_pow]]
      field_simp
    have h1 := lintegral_mono_ae hptD
    rw [← ofReal_integral_eq_lintegral_ofReal hD hnnD, hvalD] at h1
    refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
    have hexp8 : Real.exp (-(Real.pi ^ 2)) ≤ 1 / 8 := exp_neg_pi_sq_le_eighth
    have hstep1 : 48 * s⁻¹ * Real.exp (-(Real.pi ^ 2)) / Real.pi ^ 2 ≤ 6 * s⁻¹ / Real.pi ^ 2 := by
      have hnum : 48 * s⁻¹ * Real.exp (-(Real.pi ^ 2)) ≤ 48 * s⁻¹ * (1 / 8) :=
        mul_le_mul_of_nonneg_left hexp8 (by positivity)
      have := div_le_div_of_nonneg_right hnum (le_of_lt (by positivity : (0:ℝ) < Real.pi ^ 2))
      calc 48 * s⁻¹ * Real.exp (-(Real.pi ^ 2)) / Real.pi ^ 2
          ≤ 48 * s⁻¹ * (1 / 8) / Real.pi ^ 2 := this
        _ = 6 * s⁻¹ / Real.pi ^ 2 := by ring
    have hstep2 : 6 * s⁻¹ / Real.pi ^ 2 ≤ (2 / 3 : ℝ) * s⁻¹ := by
      have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2)]
      nlinarith [hpi2, inv_pos.mpr hs, Real.pi_pos]
    have hstep3 : (2 / 3 : ℝ) * s⁻¹ ≤ 4 / δ := by
      have h := inv_s_le' hs hδ hδs
      have h1 : (2 / 3 : ℝ) * s⁻¹ ≤ (2 / 3) * (2 / δ) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      have h2 : (2 / 3 : ℝ) * (2 / δ) ≤ 4 / δ := by
        have heq : (2 / 3 : ℝ) * (2 / δ) = 4 / (3 * δ) := by field_simp; ring
        rw [heq, div_le_div_iff₀ (by positivity) hδ]
        nlinarith [hδ]
      linarith [h1, h2]
    linarith [hstep1, hstep2, hstep3]
  -- assembly
  have hsplit : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
      = (∫⁻ t in Set.Ioc (0 : ℝ) (s ^ 2), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
        + (∫⁻ t in Set.Ioi (s ^ 2), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hs2.le]
    exact lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same
  rw [hsplit]
  have ha1 : 0 ≤ 300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ := by positivity
  have ha2 : 0 ≤ (4 : ℝ) / δ := by positivity
  have hfin : 300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ + 4 / δ
      = 306 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ := by
    field_simp
    ring
  calc (∫⁻ t in Set.Ioc (0 : ℝ) (s ^ 2), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
        + (∫⁻ t in Set.Ioi (s ^ 2), ENNReal.ofReal |boxHeat3 s t x y - (s ^ 3)⁻¹|)
      ≤ ENNReal.ofReal (300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ) + ENNReal.ofReal (4 / δ) :=
        add_le_add hsmall htail
    _ = ENNReal.ofReal (300 / δ + (4 * Real.pi * ‖x - y‖)⁻¹ + 2 / δ + 4 / δ) := by
        rw [ENNReal.ofReal_add ha1 ha2]
    _ = ENNReal.ofReal (306 / δ + (4 * Real.pi * ‖x - y‖)⁻¹) := by rw [hfin]
    _ ≤ ENNReal.ofReal (400 / δ + (4 * Real.pi * ‖x - y‖)⁻¹) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (306:ℝ) / δ ≤ 400 / δ := by
          rw [div_le_div_iff₀ hδ hδ]; linarith
        linarith

/-! ## 7 The `t`-Fubini and the spectral sharp-mass identity -/

private abbrev muT : Measure ℝ := volume.restrict (Set.Ioi 0)

private abbrev nuP : Measure (ℝ³ × ℝ³) := (volume : Measure ℝ³).prod volume

private lemma volume_prod_eq : (volume : Measure (ℝ³ × ℝ³)) = nuP := rfl

/-- a.e. strong measurability of `W ∘ fst` for the restricted-product measure. -/
private lemma aestronglyMeasurable_comp_fst {W : ℝ³ → ℝ} (hW : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (fun q : ℝ × (ℝ³ × ℝ³) => W q.2.1) (muT.prod nuP) := by
  let g : ℝ³ → ℝ := hW.mk
  refine ⟨fun q => g q.2.1,
    (hW.stronglyMeasurable_mk.measurable.comp (measurable_fst.comp measurable_snd)).stronglyMeasurable, ?_⟩
  change ∀ᵐ q ∂(muT.prod nuP), W q.2.1 = g q.2.1
  rw [MeasureTheory.ae_iff]
  have hS : (volume : Measure ℝ³) {y : ℝ³ | W y ≠ g y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact hW.ae_eq_mk
  have hset : {q : ℝ × (ℝ³ × ℝ³) | ¬ (W q.2.1 = g q.2.1)}
      = Set.univ ×ˢ ({y : ℝ³ | W y ≠ g y} ×ˢ Set.univ) := by
    ext q; simp
  rw [hset, muT, nuP, Measure.prod_prod, Measure.prod_prod, hS]
  ring

/-- a.e. strong measurability of `W ∘ snd ∘ fst`. -/
private lemma aestronglyMeasurable_comp_snd {W : ℝ³ → ℝ} (hW : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (fun q : ℝ × (ℝ³ × ℝ³) => W q.2.2) (muT.prod nuP) := by
  let g : ℝ³ → ℝ := hW.mk
  refine ⟨fun q => g q.2.2,
    (hW.stronglyMeasurable_mk.measurable.comp (measurable_snd.comp measurable_snd)).stronglyMeasurable, ?_⟩
  change ∀ᵐ q ∂(muT.prod nuP), W q.2.2 = g q.2.2
  rw [MeasureTheory.ae_iff]
  have hS : (volume : Measure ℝ³) {y : ℝ³ | W y ≠ g y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact hW.ae_eq_mk
  have hset : {q : ℝ × (ℝ³ × ℝ³) | ¬ (W q.2.2 = g q.2.2)}
      = Set.univ ×ˢ (Set.univ ×ˢ {y : ℝ³ | W y ≠ g y}) := by
    ext q; simp
  rw [hset, muT, nuP, Measure.prod_prod, Measure.prod_prod, hS]
  ring

private lemma aestronglyMeasurable_boxHeat3_joint (s : ℝ) :
    AEStronglyMeasurable (fun q : ℝ × (ℝ³ × ℝ³) => boxHeat3 s q.1 q.2.1 q.2.2)
      (muT.prod nuP) := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  have h : (fun q : ℝ × (ℝ³ × ℝ³) => boxHeat3 s q.1 q.2.1 q.2.2)
      = fun q => ∏ j : Fin 3, neuHeat1 s q.1 (q.2.1 j) (q.2.2 j) := rfl
  rw [h]
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      AEMeasurable (fun q : ℝ × (ℝ³ × ℝ³) => neuHeat1 s q.1 (q.2.1 j) (q.2.2 j))
        (muT.prod nuP) := by
    intro j _
    apply AEMeasurable.tsum
    intro k
    refine (by fun_prop : Measurable (fun q : ℝ × (ℝ³ × ℝ³) =>
      Real.cos (Real.pi * (k:ℝ) * ((q.2.1 j) + s / 2) / s)
        * Real.cos (Real.pi * (k:ℝ) * ((q.2.2 j) + s / 2) / s)
        * Real.exp (-(q.1 * (Real.pi * (k:ℝ) / s) ^ 2))
        * (if k = 0 then s else s / 2)⁻¹)).aemeasurable
  have hfun : (fun q : ℝ × (ℝ³ × ℝ³) => ∏ j : Fin 3, neuHeat1 s q.1 (q.2.1 j) (q.2.2 j))
      = ∏ j : Fin 3, fun q : ℝ × (ℝ³ × ℝ³) => neuHeat1 s q.1 (q.2.1 j) (q.2.2 j) := by
    funext q; simp [Finset.prod_apply]
  rw [hfun]
  exact Finset.aemeasurable_prod (μ := muT.prod nuP) Finset.univ hf

private lemma aestronglyMeasurable_sharpKernel {s : ℝ} {W : ℝ³ → ℝ}
    (hW : AEStronglyMeasurable W volume) :
    AEStronglyMeasurable (fun q : ℝ × (ℝ³ × ℝ³) =>
      W q.2.1 * W q.2.2 * (boxHeat3 s q.1 q.2.1 q.2.2 - (s ^ 3)⁻¹)) (muT.prod nuP) :=
  ((aestronglyMeasurable_comp_fst hW).mul (aestronglyMeasurable_comp_snd hW)).mul
    ((aestronglyMeasurable_boxHeat3_joint s).sub aestronglyMeasurable_const)

/-- the sharp-mass kernel `(t,p) ↦ W p.1 W p.2 (p_N(t,p.1,p.2) − s^{-3})`. -/
private noncomputable def sharpKernel (s : ℝ) (W : ℝ³ → ℝ) (t : ℝ) (p : ℝ³ × ℝ³) : ℝ :=
  W p.1 * W p.2 * (boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹)

/-- integrability of the sharp-mass kernel for the restricted product measure. -/
private lemma integrable_uncurry_sharpKernel {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) {W : ℝ³ → ℝ} (hWnn : 0 ≤ W) (hWint : Integrable W)
    (hinner : ∀ x ∈ tsupport W, ∀ j : Fin 3, |x j| ≤ s / 2 - δ)
    (hintC : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :
    Integrable (Function.uncurry (sharpKernel s W)) (muT.prod nuP) := by
  have hWm : AEStronglyMeasurable W volume := hWint.aestronglyMeasurable
  refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
    (g := fun p : ℝ³ × ℝ³ => ENNReal.ofReal
      (W p.1 * W p.2 * (400 / δ + (4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹))) ?_ ?_ ?_
  · exact aestronglyMeasurable_sharpKernel (s := s) hWm
  · -- the `p`-integral of the majorant is finite
    have hbase : Integrable (fun p : ℝ³ × ℝ³ => (400 / δ) * (W p.1 * W p.2)) nuP :=
      (hWint.mul_prod hWint).const_mul _
    have hdev : Integrable (fun p : ℝ³ × ℝ³ =>
        (4 * Real.pi)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) nuP :=
      hintC.const_mul _
    have hsum : Integrable (fun p : ℝ³ × ℝ³ =>
        (400 / δ) * (W p.1 * W p.2)
          + (4 * Real.pi)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) nuP :=
      hbase.add hdev
    have hnn : 0 ≤ᵐ[nuP] (fun p : ℝ³ × ℝ³ =>
        (400 / δ) * (W p.1 * W p.2)
          + (4 * Real.pi)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) :=
      Filter.Eventually.of_forall fun p => by
        have h2 : 0 ≤ W p.1 * W p.2 := mul_nonneg (hWnn _) (hWnn _)
        have h3 : 0 ≤ W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹ := mul_nonneg h2 (by positivity)
        have h1 : 0 ≤ (400 : ℝ) / δ := by positivity
        have h4 : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
        exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h4 h3)
    have hfun : (fun p : ℝ³ × ℝ³ => ENNReal.ofReal
        (W p.1 * W p.2 * (400 / δ + (4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹)))
        = fun p : ℝ³ × ℝ³ => ENNReal.ofReal
            ((400 / δ) * (W p.1 * W p.2)
              + (4 * Real.pi)⁻¹ * (W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹)) := by
      funext p
      congr 1
      have h4 : (4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹ = (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ : ℝ)⁻¹ := by
        rw [mul_inv]
      rw [h4]; ring
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hsum hnn]
    exact ENNReal.ofReal_ne_top
  · -- the a.e. pointwise `t`-bound
    filter_upwards [ae_fst_ne_snd] with p hp
    by_cases hzero : W p.1 * W p.2 = 0
    · have hz : (fun t : ℝ => ENNReal.ofReal ‖sharpKernel s W t p‖) = fun _ => (0 : ENNReal) := by
        funext t
        simp only [sharpKernel, hzero, zero_mul, norm_zero, ENNReal.ofReal_zero]
      rw [hz, lintegral_zero, hzero, zero_mul, ENNReal.ofReal_zero]
    · have hx : p.1 ∈ tsupport W := by
        by_contra hcon
        exact hzero (by rw [image_eq_zero_of_notMem_tsupport hcon]; ring)
      have hy : p.2 ∈ tsupport W := by
        by_contra hcon
        exact hzero (by rw [image_eq_zero_of_notMem_tsupport hcon]; ring)
      have hxnn : 0 ≤ W p.1 := hWnn p.1
      have hynn : 0 ≤ W p.2 := hWnn p.2
      have hcinv : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal ‖sharpKernel s W t p‖)
          = ENNReal.ofReal (W p.1 * W p.2)
            * (∫⁻ t in Set.Ioi (0:ℝ),
                ENNReal.ofReal |boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹|) := by
        have hpt : ∀ t : ℝ, ENNReal.ofReal ‖sharpKernel s W t p‖
            = ENNReal.ofReal (W p.1 * W p.2)
              * ENNReal.ofReal |boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹| := by
          intro t
          simp only [sharpKernel]
          rw [Real.norm_eq_abs, abs_mul]
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          congr 1
          rw [abs_of_nonneg (mul_nonneg hxnn hynn)]
        rw [show (fun t : ℝ => ENNReal.ofReal ‖sharpKernel s W t p‖)
            = fun t => ENNReal.ofReal (W p.1 * W p.2)
              * ENNReal.ofReal |boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹| from funext hpt,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [hcinv]
      refine le_trans (mul_le_mul_of_nonneg_left
        (lintegral_boxHeat3_sub_le hs hδ hδs hp (hinner p.1 hx) (hinner p.2 hy))
        (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal (W p.1 * W p.2))) ?_
      rw [← ENNReal.ofReal_mul (mul_nonneg hxnn hynn)]

lemma modeSharpTerm_nonneg (s t : ℝ) (hs : 0 < s) (k : Fin 3 → ℕ) (W : ℝ³ → ℝ) :
    0 ≤ modeSharpTerm s t k W :=
  mul_nonneg (mul_nonneg (modeW_nonneg hs k) (sq_nonneg _)) (Real.exp_pos _).le

lemma modeSharpTerm_le {s t : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) {W : ℝ³ → ℝ}
    (hWint : Integrable W) :
    modeSharpTerm s t k W
      ≤ (8 / s ^ 3) * (∫ x, ‖W x‖) ^ 2
        * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
  have hw : modeW s k ≤ 8 / s ^ 3 := modeW_le hs k
  have hwnn : 0 ≤ modeW s k := modeW_nonneg hs k
  have hc : |modeFourier s k W| ≤ ∫ x, ‖W x‖ := by
    rw [modeFourier, ← Real.norm_eq_abs]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · exact hWint.norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg (W x)) (boxNeumann3_abs_le_one k x)
  have hI : 0 ≤ ∫ x, ‖W x‖ := integral_nonneg fun x => norm_nonneg _
  have hprod : Real.exp (-(t * modeEig s k))
      = ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) :=
    exp_neg_modeEig_eq_prod s t k
  have hprodnn : 0 ≤ ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) :=
    Finset.prod_nonneg fun j _ => (Real.exp_pos _).le
  rw [modeSharpTerm, hprod]
  have hsq : (modeFourier s k W) ^ 2 ≤ (∫ x, ‖W x‖) ^ 2 := by
    rw [← sq_abs (modeFourier s k W)]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  calc modeW s k * (modeFourier s k W) ^ 2
        * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2)
      ≤ (8 / s ^ 3) * (∫ x, ‖W x‖) ^ 2
        * ∏ j : Fin 3, Real.exp (-(t * (Real.pi / s) ^ 2) * ((k j : ℝ)) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hprodnn
        exact mul_le_mul hw hsq (sq_nonneg _) (by positivity)

lemma summable_modeSharpTerm {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {W : ℝ³ → ℝ}
    (hWint : Integrable W) :
    Summable fun k : Fin 3 → ℕ => (if k = 0 then 0 else modeSharpTerm s t k W) := by
  have hc : 0 < t * (Real.pi / s) ^ 2 := by positivity
  have hI : 0 ≤ (∫ x, ‖W x‖) ^ 2 := sq_nonneg _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_pi_gauss_fin3 hc).mul_left (8 / s ^ 3 * (∫ x, ‖W x‖) ^ 2))
  · by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]; exact modeSharpTerm_nonneg s t hs k W
  · by_cases hk : k = 0
    · rw [if_pos hk]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
    · rw [if_neg hk]
      exact modeSharpTerm_le (s := s) hs k hWint

/-- the per-mode `t`-integral of the spectral sharp-mass summand. -/
lemma integral_modeSharpTerm {s : ℝ} (hs : 0 < s) {k : Fin 3 → ℕ} {W : ℝ³ → ℝ} :
    (∫ t in Set.Ioi (0 : ℝ), (if k = 0 then 0 else modeSharpTerm s t k W))
      = (if k = 0 then 0 else modeW s k * (modeFourier s k W) ^ 2 / modeEig s k) := by
  by_cases hk : k = 0
  · simp [hk]
  · have hlam : 0 < modeEig s k := modeEig_pos hs hk
    have hintegrable : IntegrableOn (fun t : ℝ => Real.exp (-(modeEig s k * t))) (Set.Ioi 0) := by
      have h := exp_neg_integrableOn_Ioi (0 : ℝ) hlam
      simpa [neg_mul] using h
    have hval : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * modeEig s k)))
        = (modeEig s k)⁻¹ := by
      rw [show (fun t : ℝ => Real.exp (-(t * modeEig s k)))
          = fun t => Real.exp (-(modeEig s k * t)) from by funext t; ring_nf]
      exact Commons.Analysis.Integral.integral_Ioi_exp_neg_mul hlam
    have hmain : (∫ t in Set.Ioi (0 : ℝ), modeW s k * (modeFourier s k W) ^ 2
        * Real.exp (-(t * modeEig s k)))
        = modeW s k * (modeFourier s k W) ^ 2 / modeEig s k := by
      rw [MeasureTheory.integral_const_mul, hval, div_eq_mul_inv]
    have hcongr : (fun t : ℝ => (if k = 0 then 0 else modeSharpTerm s t k W))
        = fun t : ℝ => modeW s k * (modeFourier s k W) ^ 2 * Real.exp (-(t * modeEig s k)) := by
      funext t; rw [if_neg hk, modeSharpTerm]
    rw [hcongr, if_neg hk]
    exact hmain

/-- **the spectral sharp-mass identity**: the box-mode sharp mass equals the
box Neumann Green double energy. -/
theorem modeSharpMass_eq_green {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    {W : ℝ³ → ℝ} (hWnn : 0 ≤ W) (hWint : Integrable W)
    (hinner : ∀ x ∈ tsupport W, ∀ j : Fin 3, |x j| ≤ s / 2 - δ)
    (hintC : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹))
    (hintD : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * boxGreenDev s p.1 p.2)) :
    modeSharpMass s W = ∫ p : ℝ³ × ℝ³,
      W p.1 * W p.2 * ((4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹ + boxGreenDev s p.1 p.2) := by
  have hInt := integrable_uncurry_sharpKernel (s := s) (δ := δ) hs hδ hδs hWnn hWint hinner hintC
  have hL : Integrable (fun t : ℝ => ∫ p, sharpKernel s W t p ∂nuP) muT := hInt.integral_prod_left
  have hswap := integral_integral_swap hInt
  -- (A) the value of the inner `t`-integral
  have hA : ∀ᵐ p ∂nuP, (∫ t, sharpKernel s W t p ∂muT)
      = W p.1 * W p.2 * ((4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹ + boxGreenDev s p.1 p.2) := by
    filter_upwards [ae_fst_ne_snd] with p hp
    by_cases hzero : W p.1 * W p.2 = 0
    · have hz : (fun t : ℝ => sharpKernel s W t p) = fun _ => (0 : ℝ) := by
        funext t; simp only [sharpKernel, hzero, zero_mul]
      rw [hz, MeasureTheory.integral_zero, hzero, zero_mul]
    · have hx : p.1 ∈ tsupport W := by
        by_contra hcon
        exact hzero (by rw [image_eq_zero_of_notMem_tsupport hcon]; ring)
      have hy : p.2 ∈ tsupport W := by
        by_contra hcon
        exact hzero (by rw [image_eq_zero_of_notMem_tsupport hcon]; ring)
      have h1 : (∫ t, sharpKernel s W t p ∂muT)
          = W p.1 * W p.2 * (∫ t in Set.Ioi (0 : ℝ), (boxHeat3 s t p.1 p.2 - (s ^ 3)⁻¹)) := by
        simp only [sharpKernel]
        rw [MeasureTheory.integral_const_mul]
      rw [h1, integral_boxHeat3_eq hs hδ hδs hp (hinner p.1 hx) (hinner p.2 hy)]
  -- (B) the pointwise spectral identity
  have hB : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∑' k : Fin 3 → ℕ, if k = 0 then 0 else modeSharpTerm s t k W)
        = ∫ p, sharpKernel s W t p ∂nuP := by
    intro t ht
    exact tsum_modeSharpTerm_eq hs ht hWint
  have hΨint : Integrable (fun t : ℝ => ∑' k : Fin 3 → ℕ,
      if k = 0 then 0 else modeSharpTerm s t k W) muT :=
    hL.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hB t ht).symm)
  -- (C) the extended-integral (Tonelli) bookkeeping
  set hfun : (Fin 3 → ℕ) → ℝ → ℝ := fun k t => if k = 0 then 0 else modeSharpTerm s t k W
    with hhfdef
  set ak : (Fin 3 → ℕ) → ℝ := fun k =>
    if k = 0 then 0 else modeW s k * (modeFourier s k W) ^ 2 / modeEig s k with hakdef
  have hhf : ∀ k t, hfun k t = if k = 0 then 0 else modeSharpTerm s t k W := fun k t => rfl
  have hmass : modeSharpMass s W = ∑' k, ak k := by
    simp only [modeSharpMass, hakdef]
  have hnnak : ∀ k, 0 ≤ ak k := by
    intro k
    simp only [hakdef]
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      refine div_nonneg (mul_nonneg (modeW_nonneg hs k) (sq_nonneg _)) (modeEig_nonneg s k)
  have hmeash : ∀ k, AEMeasurable (fun t : ℝ => ENNReal.ofReal (hfun k t)) muT := by
    intro k
    by_cases hk : k = 0
    · have h1 : (fun t : ℝ => ENNReal.ofReal (hfun k t)) = fun _ => (0 : ENNReal) := by
        funext t; simp only [hhfdef]; rw [if_pos hk]; simp
      rw [h1]; exact aemeasurable_const
    · have h1 : (fun t : ℝ => ENNReal.ofReal (hfun k t))
          = fun t => ENNReal.ofReal (modeW s k * (modeFourier s k W) ^ 2
              * Real.exp (-(t * modeEig s k))) := by
        funext t; rw [hhf, if_neg hk]; rfl
      rw [h1]
      exact ENNReal.measurable_ofReal.comp_aemeasurable (Measurable.aemeasurable
        (by fun_prop : Measurable (fun t : ℝ =>
          modeW s k * (modeFourier s k W) ^ 2 * Real.exp (-(t * modeEig s k)))))
  have hintfun : ∀ k, Integrable (fun t : ℝ => hfun k t) muT := by
    intro k
    by_cases hk : k = 0
    · have h1 : (fun t : ℝ => hfun k t) = fun _ => (0 : ℝ) := by
        funext t; rw [hhf, if_pos hk]
      rw [h1]; exact integrable_zero _ _ _
    · have h1 : (fun t : ℝ => hfun k t) = fun t => modeW s k * (modeFourier s k W) ^ 2
            * Real.exp (-(t * modeEig s k)) := by
        funext t; rw [hhf, if_neg hk]; rfl
      rw [h1]
      have h2 : Integrable (fun x : ℝ => Real.exp (-(modeEig s k) * x)) muT :=
        exp_neg_integrableOn_Ioi (0 : ℝ) (modeEig_pos hs hk)
      have h3 : (fun t : ℝ => modeW s k * (modeFourier s k W) ^ 2
            * Real.exp (-(t * modeEig s k)))
          = fun x : ℝ => modeW s k * (modeFourier s k W) ^ 2
            * Real.exp (-(modeEig s k) * x) := by
        funext t; rw [mul_comm t (modeEig s k), ← neg_mul]
      rw [h3]
      exact h2.const_mul _
  have hnnfun : ∀ k, 0 ≤ᵐ[muT] (fun t : ℝ => hfun k t) := by
    intro k
    refine Filter.Eventually.of_forall fun t => ?_
    show 0 ≤ hfun k t
    rw [hhf]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; exact modeSharpTerm_nonneg s t hs k W
  have hterm : ∀ k, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (hfun k t))
      = ENNReal.ofReal (ak k) := by
    intro k
    have h2 : (∫ t in Set.Ioi (0 : ℝ), hfun k t) = ak k := by
      simp only [hakdef]
      exact integral_modeSharpTerm (s := s) hs
    rw [← h2]
    exact (ofReal_integral_eq_lintegral_ofReal (hintfun k) (hnnfun k)).symm
  have hpoint : ∀ᵐ t ∂muT,
      ENNReal.ofReal (∑' k, hfun k t) = ∑' k, ENNReal.ofReal (hfun k t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    refine ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) (summable_modeSharpTerm hs ht hWint)
    rw [hhf]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; exact modeSharpTerm_nonneg s t hs k W
  have hLint : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (∑' k, hfun k t))
      = ∑' k, ENNReal.ofReal (ak k) := by
    calc (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (∑' k, hfun k t))
        = ∫⁻ t in Set.Ioi (0 : ℝ), ∑' k, ENNReal.ofReal (hfun k t) :=
          lintegral_congr_ae hpoint
      _ = ∑' k, ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (hfun k t) := lintegral_tsum hmeash
      _ = ∑' k, ENNReal.ofReal (ak k) := tsum_congr hterm
  have hnnΨ : 0 ≤ᵐ[muT] (fun t : ℝ => ∑' k, hfun k t) :=
    Filter.Eventually.of_forall fun t => tsum_nonneg fun k => by
      simp only [hhf]
      by_cases hk : k = 0
      · rw [if_pos hk]
      · rw [if_neg hk]; exact modeSharpTerm_nonneg s t hs k W
  have hleft : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (∑' k, hfun k t))
      = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), ∑' k, hfun k t) := by
    have h1 := (ofReal_integral_eq_lintegral_ofReal hΨint hnnΨ).symm
    have h2 : (fun t : ℝ => ∑' k, hfun k t)
        = fun t => ∑' k, (if k = 0 then 0 else modeSharpTerm s t k W) := by
      funext t; exact tsum_congr fun k => hhf k t
    rw [h2]; exact h1
  have hsumm_ak : Summable ak := by
    have h1 : ∑' k, ENNReal.ofReal (ak k) < ⊤ := by
      rw [← hLint, hleft]; exact ENNReal.ofReal_lt_top
    set b : (Fin 3 → ℕ) → NNReal := fun k => ⟨ak k, hnnak k⟩ with hbdef
    have h2 : (∑' k, (b k : ENNReal)) = ∑' k, ENNReal.ofReal (ak k) := by
      apply tsum_congr; intro k
      simp only [hbdef]
      exact (ENNReal.ofReal_eq_coe_nnreal (hnnak k)).symm
    have h3 : Summable b :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp (by rw [h2]; exact h1.ne)
    have h4 : Summable (fun k => ((b k : NNReal) : ℝ)) := NNReal.summable_coe.mpr h3
    refine h4.congr fun k => ?_
    simp only [hbdef]; rfl
  have hkey : (∑' k, ak k) = ∫ t in Set.Ioi (0 : ℝ), ∑' k, hfun k t := by
    have h1 : ENNReal.ofReal (∑' k, ak k) = ∑' k, ENNReal.ofReal (ak k) :=
      ENNReal.ofReal_tsum_of_nonneg hnnak hsumm_ak
    have h2 : ENNReal.ofReal (∑' k, ak k)
        = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), ∑' k, hfun k t) := by
      rw [h1, ← hleft, hLint]
    have h3 := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_ofReal (tsum_nonneg hnnak),
      ENNReal.toReal_ofReal (integral_nonneg fun t => tsum_nonneg fun k => by
        simp only [hhf]
        by_cases hk : k = 0
        · rw [if_pos hk]
        · rw [if_neg hk]; exact modeSharpTerm_nonneg s t hs k W)] at h3
    exact h3
  -- (D) assembly
  have hBae : (fun t : ℝ => ∑' k, hfun k t)
      =ᵐ[muT] fun t => ∫ p, sharpKernel s W t p ∂nuP := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hB t ht
  rw [hmass, hkey, MeasureTheory.integral_congr_ae hBae, hswap]
  exact MeasureTheory.integral_congr_ae hA

/-- **the packaged D1 sharp-mass comparison**: the box-mode sharp mass is at most
`(1 + 8π·400·R/δ)` times the continuum Newtonian double energy. -/
theorem modeSharpMass_le {s δ R : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    (hR : 0 < R) {W : ℝ³ → ℝ} (hWnn : 0 ≤ W) (hWint : Integrable W)
    (hWsupp : tsupport W ⊆ ball (0 : ℝ³) R)
    (hinner : ∀ x ∈ tsupport W, ∀ j : Fin 3, |x j| ≤ s / 2 - δ)
    (hintC : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹))
    (hintD : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * boxGreenDev s p.1 p.2)) :
    modeSharpMass s W ≤ (1 + 8 * Real.pi * 400 * R / δ)
      * ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (4 * Real.pi * ‖p.1 - p.2‖ : ℝ)⁻¹ := by
  rw [modeSharpMass_eq_green hs hδ hδs hWnn hWint hinner hintC hintD]
  exact boxSharpMass_continuum_le hs hδ hδs hR hWnn hWint hWsupp hinner hintC hintD

/-! ## 8 The `L²`-bridge: the spectral sharp mass in the corpus's inner-product form -/

/-- the `L²` inner product of a box mode with an arbitrary `L²`-function. -/
lemma boxInner_toLp_eq {s : ℝ} (k : Fin 3 → ℕ) {W : ℝ³ → ℝ} (hW : MemLp W 2 (boxVol s)) :
    inner ℝ (boxModeLp s k) (MemLp.toLp W hW)
      = ∫ x : ℝ³, boxNeumann3 s k x * W x ∂(boxVol s) := by
  rw [L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  have hk : ((boxModeLp s k : ℝ³ → ℝ)) =ᵐ[boxVol s] (fun z : ℝ³ => boxNeumann3 s k z) := by
    dsimp [boxModeLp]
    simpa using (MemLp.coeFn_toLp (boxMode_memLp s k))
  filter_upwards [hk, MemLp.coeFn_toLp hW] with x hx hw
  rw [hx, hw, Real.inner_apply]

/-- **the normalised box mode against an `L²`-function**: the inner product with the
unit mode `ê_k` is `√(modeW s k)` times the unnormalised Fourier coefficient.  This is the
bridge between the corpus's `Lp`-level mode sums (`tBmode`, `kMode`) and the spectral
sharp mass of `modeSharpMass`. -/
theorem boxModeOrtho_inner_eq {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) {W : ℝ³ → ℝ}
    (hW : MemLp W 2 (boxVol s)) :
    inner ℝ (boxModeOrtho s hs k) (MemLp.toLp W hW)
      = Real.sqrt (modeW s k) * ∫ x : ℝ³, boxNeumann3 s k x * W x ∂(boxVol s) := by
  rw [boxModeOrtho, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [boxInner_toLp_eq k hW]
  congr 1
  rw [modeW, ← Real.sqrt_inv]

end BoseGases
end Submission
