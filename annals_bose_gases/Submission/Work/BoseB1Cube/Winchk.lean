import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.cubeWindowPort
import Submission.Work.BoseFixB1B.B1Bfix2.CutFibreBase
import Submission.Work.BoseFixB1S.win.chiSmallB_windowIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Winchk` — the `chiSmallB` window layer

The **cube** cutoff `χ^{S}_{B(u)} = chiSmallB M ℓ d u` (the corpus bump `chiScale ℓ` times the
cosine-`M`-th-power bump `chiSmall M ((ℓ d)⁻¹ • x - u)`) is the window of the *matched*
(cube-cutoff) sliding word `Work.BoseFixB1B.sbWordCube`.  Every `χ`-generic estimate of the
sharp-fibre convergence chain (`B1Bfix2/CutFibreBase`, `B1Bfix2/diffFibre_factsB`,
`B1Bfix2/fibreDirI_diff_tendstoB`, `cutFibreMass_facts`, `cutPlancherel_le`,
`cutAmplitude_integrable`, `tendsto_tBdiagFormInd_cutB`, …) is stated at the **ball** window
`chiB ℓ d u`; this module is the *window layer* those files consume, at the cube cutoff.

What is proved here (all `sorry`-free):

* `kappaS` — the sup constant of the cube window (`chiSupAbs * chiSmallNormFactor M`), with
  `kappaS_nonneg`, `abs_chiSmallB_le_kappaS`, `chiSmallB_sq_le_kappaS`;
* `abs_zeta1d_le` — the 1D bump `ζ(y) = 1_{|y| ≤ 1/2} cos (π y)` vanishes *at least linearly* at
  the boundary of its support: `|ζ y| ≤ π · max 0 (1/2 - |y|)`;
* `cubeMargin`, `chiSmall_le_linMarg` — the `M`-th-power bump vanishes at least linearly in the
  **cube** margin `⨅_j max 0 (1/2 - |z_j|)` (the `M`-th power of a linear function `[0,1] → [0,1]`
  is bounded by the linear function itself, `M ≥ 1`);
* **`chiSmallB_abs_le_boxMargin`** — the cube window vanishes at least linearly in
  `boxMargin ℓ d u`: `∃ C ≥ 0, ∀ x ∈ dlBox ℓ d u, |chiSmallB M ℓ d u x| ≤ C · boxMargin ℓ d u x`
  (the cube twin of the PROVED `Work.BoseFixB1B.chiB_abs_le_boxMargin`; this is the *only*
  genuinely new analytic input of the port);
* `exists_bound_fderiv_chiSmallB` — the Fréchet derivative of the cube window is globally bounded
  (twin of the private `exists_bound_fderiv_chiB` of `B1Bfix2/fibreDirI_diff_tendstoB.lean`);
* `chiSmallB_sup_bounds` — the sup bounds of the window and of the square of its gradient (twin of
  `Work.BoseFixB1B.chiB_sup_bounds`);
* `integral_chiSmallB_sq_collarInd_le` — the window-weighted collar integral is linear in `δ`
  (twin of `Work.BoseFixB1B.integral_chiB_sq_collarInd_le`);
* `chiSmallB_eq_zero_of_notMem_dlBox`, `chiSmallB_mul_boxInd` — the support facts.

The regularity hypothesis is `4 ≤ M` where `C³` is needed: `chiSmallB M` is `C^{M-1}`
(`Submission.Work.ChiSmall`) and `Work.BoseFixB1S.win.contDiff_chiSmallB` needs `N + 1 ≤ M` for
`C^N`.
-/

noncomputable section

open scoped Topology ContDiff
open MeasureTheory Metric

namespace Work.BoseB1Cube.Winchk

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 0. The sup constant of the cube window -/

/-- The sup constant of the cube window: `chiSupAbs * chiSmallNormFactor M`. -/
noncomputable def kappaS (M : ℕ) : ℝ :=
  Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M

theorem kappaS_nonneg (M : ℕ) : 0 ≤ kappaS M :=
  mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
    (Submission.BoseGases.chiSmallNormFactor_nonneg M)

/-- The cube window is dominated by `kappaS M`. -/
theorem abs_chiSmallB_le_kappaS {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : E3) :
    |Submission.BoseGases.chiSmallB M ℓ d u x| ≤ kappaS M := by
  have h1 : |Submission.BoseGases.chiScale ℓ x| ≤ Submission.BoseGases.chiSupAbs :=
    Submission.BoseGases.chiScale_abs_le_sup ℓ x
  have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) ≤
      Submission.BoseGases.chiSmallNormFactor M := by
    rw [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor, div_eq_mul_inv]
    exact mul_le_of_le_one_left (Submission.BoseGases.chiSmallNormFactor_nonneg M)
      (Submission.BoseGases.chiSmallBase_le_one M _)
  rw [Submission.BoseGases.chiSmallB, abs_mul,
    abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _), kappaS]
  exact mul_le_mul h1 h2 (Submission.BoseGases.chiSmall_nonneg M _)
    Submission.BoseGases.chiSupAbs_nonneg

/-- The square of the cube window is dominated by `kappaS M ^ 2`. -/
theorem chiSmallB_sq_le_kappaS {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : E3) :
    (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2 ≤ (kappaS M) ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_chiSmallB_le_kappaS hM u x) 2

/-! ## 1. The linear vanishing of the 1D bump `ζ` -/

/-- The 1D bump `ζ y = 1_{|y| ≤ 1/2} cos (π y)` vanishes at least linearly at the boundary of
its support: `|ζ y| ≤ π · max 0 (1/2 - |y|)`. -/
theorem abs_zeta1d_le (y : ℝ) :
    |Submission.BoseGases.zeta1d y| ≤ Real.pi * max 0 (1 / 2 - |y|) := by
  by_cases hy : |y| ≤ 1 / 2
  · rw [Submission.BoseGases.zeta1d, if_pos hy]
    have hy1 : y ≤ 1 / 2 := le_trans (le_abs_self y) hy
    have hy2 : -(1 / 2 : ℝ) ≤ y := by
      have h := neg_abs_le y
      linarith
    have key : |Real.cos (Real.pi * y)| ≤ Real.pi * max 0 (1 / 2 - |y|) := by
      rcases le_total 0 y with hy0 | hy0
      · have h := Real.lipschitzWith_cos.dist_le_mul (Real.pi * y) (Real.pi / 2)
        rw [Real.dist_eq, Real.dist_eq] at h
        norm_num at h
        have h2 : |Real.pi * y - Real.pi / 2| = Real.pi * (1 / 2 - y) := by
          rw [abs_of_nonpos (by nlinarith [Real.pi_pos, hy1])]
          ring
        rw [h2] at h
        rw [abs_of_nonneg hy0, max_eq_right (by linarith)]
        exact h
      · have hyneg : |y| = -y := abs_of_nonpos hy0
        have h := Real.lipschitzWith_cos.dist_le_mul (Real.pi * y) (-(Real.pi / 2))
        rw [Real.dist_eq, Real.dist_eq] at h
        norm_num at h
        have h2 : |Real.pi * y + Real.pi / 2| = Real.pi * (1 / 2 + y) := by
          rw [abs_of_nonneg (by nlinarith [Real.pi_pos, hy2])]
          ring
        rw [h2] at h
        rw [hyneg, max_eq_right (by linarith)]
        linarith
    exact key
  · rw [Submission.BoseGases.zeta1d, if_neg hy, abs_zero]
    exact mul_nonneg Real.pi_pos.le (le_max_left _ _)

/-! ## 2. The cube margin -/

/-- The cube margin of a point of `ℝ³`: `⨅_j max 0 (1/2 - |z_j|)`. -/
noncomputable def cubeMargin (z : E3) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 3 => max 0 (1 / 2 - |z.ofLp j|))

theorem cubeMargin_nonneg (z : E3) : 0 ≤ cubeMargin z :=
  Finset.le_inf' Finset.univ_nonempty _ (fun j _ => le_max_left _ _)

theorem le_cubeMargin {z : E3} (j : Fin 3) :
    cubeMargin z ≤ max 0 (1 / 2 - |z.ofLp j|) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem cubeMargin_le_half (z : E3) : cubeMargin z ≤ 1 / 2 := by
  refine le_trans (le_cubeMargin (0 : Fin 3)) ?_
  exact max_le (by norm_num) (by linarith [abs_nonneg (z.ofLp 0)])

theorem cubeMargin_le_one (z : E3) : cubeMargin z ≤ 1 :=
  le_trans (cubeMargin_le_half z) (by norm_num)

theorem exists_cubeMargin_eq (z : E3) :
    ∃ j : Fin 3, cubeMargin z = max 0 (1 / 2 - |z.ofLp j|) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin 3 => max 0 (1 / 2 - |z.ofLp j|))
  exact ⟨j, hj⟩

/-- Scaling the index set: `inf'_j (c * f j) = c * inf'_j f j` for `c ≥ 0`. -/
theorem inf'_univ_mul_const {f : Fin 3 → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => c * f j)
      = c * Finset.univ.inf' Finset.univ_nonempty f := by
  rcases eq_or_lt_of_le hc with h0 | h0
  · rw [← h0]; simp
  · refine le_antisymm ?_ ?_
    · have h3 : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
          c⁻¹ * (Finset.univ.inf' Finset.univ_nonempty (fun j => c * f j)) ≤ f j := by
        intro j _
        have h := Finset.inf'_le (fun j => c * f j) (Finset.mem_univ j)
        have h4 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc)
        rwa [inv_mul_cancel_left₀ (ne_of_gt h0) (f j)] at h4
      have h4 : c⁻¹ * (Finset.univ.inf' Finset.univ_nonempty (fun j => c * f j))
          ≤ Finset.univ.inf' Finset.univ_nonempty f :=
        Finset.le_inf' Finset.univ_nonempty f h3
      have h5 := mul_le_mul_of_nonneg_left h4 hc
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h0), one_mul] at h5
    · refine Finset.le_inf' Finset.univ_nonempty (fun j => c * f j) (fun j _ => ?_)
      exact mul_le_mul_of_nonneg_left (Finset.inf'_le f (Finset.mem_univ j)) hc

/-- Scaling the index set: `inf'_j (f j / c) = (inf'_j f j) / c` for `c > 0`. -/
theorem inf'_univ_div_const {f : Fin 3 → ℝ} {c : ℝ} (hc : 0 < c) :
    Finset.univ.inf' Finset.univ_nonempty (fun j => f j / c)
      = (Finset.univ.inf' Finset.univ_nonempty f) / c := by
  rw [show (fun j => f j / c) = (fun j => c⁻¹ * f j) by
        funext j; rw [div_eq_inv_mul],
    inf'_univ_mul_const (inv_nonneg.mpr hc.le), inv_mul_eq_div]

/-! ## 3. The linear vanishing of the M-th power bump -/

/-- The `M`-th power bump vanishes at least linearly in the cube margin. -/
theorem chiSmall_le_linMarg (M : ℕ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3,
      |Submission.BoseGases.chiSmall M z| ≤ C * cubeMargin z := by
  refine ⟨Submission.BoseGases.chiSmallNormFactor M * (Real.pi ^ 3) ^ M / 4, ?_, ?_⟩
  · have h1 : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
      Submission.BoseGases.chiSmallNormFactor_nonneg M
    have h2 : (0 : ℝ) ≤ (Real.pi ^ 3) ^ M := by positivity
    exact div_nonneg (mul_nonneg h1 h2) (by norm_num)
  · intro z
    set m : Fin 3 → ℝ := fun j => max 0 (1 / 2 - |z.ofLp j|) with hm
    have hm0 : ∀ j : Fin 3, 0 ≤ m j := fun j => le_max_left _ _
    have hmle : ∀ j : Fin 3, m j ≤ 1 / 2 := fun j =>
      max_le (by norm_num) (by linarith [abs_nonneg (z.ofLp j)])
    have hfac : |Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
        * Submission.BoseGases.zeta1d (z.ofLp 2)| ≤ Real.pi ^ 3 * (m 0 * m 1 * m 2) := by
      rw [abs_mul, abs_mul]
      have h0 := abs_zeta1d_le (z.ofLp 0)
      have h1 := abs_zeta1d_le (z.ofLp 1)
      have h2 := abs_zeta1d_le (z.ofLp 2)
      simp only [hm] at h0 h1 h2 ⊢
      have h01 : |Submission.BoseGases.zeta1d (z.ofLp 0)|
            * |Submission.BoseGases.zeta1d (z.ofLp 1)|
          ≤ (Real.pi * max 0 (1 / 2 - |z.ofLp 0|))
            * (Real.pi * max 0 (1 / 2 - |z.ofLp 1|)) :=
        mul_le_mul h0 h1 (abs_nonneg _) (mul_nonneg Real.pi_pos.le (le_max_left _ _))
      have htot : (Real.pi * max 0 (1 / 2 - |z.ofLp 0|))
            * (Real.pi * max 0 (1 / 2 - |z.ofLp 1|))
            * (Real.pi * max 0 (1 / 2 - |z.ofLp 2|))
          ≤ Real.pi ^ 3 * (max 0 (1 / 2 - |z.ofLp 0|) * max 0 (1 / 2 - |z.ofLp 1|)
            * max 0 (1 / 2 - |z.ofLp 2|)) := by
        ring_nf
        exact le_rfl
      exact le_trans (mul_le_mul h01 h2 (abs_nonneg _) (mul_nonneg
        (mul_nonneg Real.pi_pos.le (le_max_left _ _)) (mul_nonneg Real.pi_pos.le
          (le_max_left _ _)))) htot
    have hprod : m 0 * m 1 * m 2 ≤ (1 / 4 : ℝ) * cubeMargin z := by
      obtain ⟨j, hj⟩ := exists_cubeMargin_eq z
      have hb : m 0 * m 1 * m 2 ≤ (1 / 2 : ℝ) * (1 / 2) * m j := by
        fin_cases j
        · have h12 : m 1 * m 2 ≤ (1 / 2 : ℝ) * (1 / 2) :=
            mul_le_mul (hmle 1) (hmle 2) (hm0 2) (by norm_num)
          calc m 0 * m 1 * m 2 = m 0 * (m 1 * m 2) := by ring
            _ ≤ m 0 * ((1 / 2 : ℝ) * (1 / 2)) := mul_le_mul_of_nonneg_left h12 (hm0 0)
            _ = (1 / 2 : ℝ) * (1 / 2) * m 0 := by ring
        · have h02 : m 0 * m 2 ≤ (1 / 2 : ℝ) * (1 / 2) :=
            mul_le_mul (hmle 0) (hmle 2) (hm0 2) (by norm_num)
          calc m 0 * m 1 * m 2 = m 1 * (m 0 * m 2) := by ring
            _ ≤ m 1 * ((1 / 2 : ℝ) * (1 / 2)) := mul_le_mul_of_nonneg_left h02 (hm0 1)
            _ = (1 / 2 : ℝ) * (1 / 2) * m 1 := by ring
        · have h01 : m 0 * m 1 ≤ (1 / 2 : ℝ) * (1 / 2) :=
            mul_le_mul (hmle 0) (hmle 1) (hm0 1) (by norm_num)
          calc m 0 * m 1 * m 2 = m 2 * (m 0 * m 1) := by ring
            _ ≤ m 2 * ((1 / 2 : ℝ) * (1 / 2)) := mul_le_mul_of_nonneg_left h01 (hm0 2)
            _ = (1 / 2 : ℝ) * (1 / 2) * m 2 := by ring
      rw [hj]
      linarith
    have hbase : |Submission.BoseGases.chiSmallBase M z|
        ≤ (Real.pi ^ 3) ^ M * ((1 / 4 : ℝ) * cubeMargin z) := by
      rw [Submission.BoseGases.chiSmallBase, abs_pow]
      have hp : (m 0 * m 1 * m 2) ^ M ≤ (1 / 4 : ℝ) * cubeMargin z := by
        have hc0 : (0 : ℝ) ≤ (1 / 4 : ℝ) * cubeMargin z := by
          have := cubeMargin_nonneg z; linarith
        have h1 : (m 0 * m 1 * m 2) ^ M ≤ ((1 / 4 : ℝ) * cubeMargin z) ^ M :=
          pow_le_pow_left₀ (by positivity) hprod M
        refine le_trans h1 ?_
        calc ((1 / 4 : ℝ) * cubeMargin z) ^ M ≤ ((1 / 4 : ℝ) * cubeMargin z) ^ 1 :=
              pow_le_pow_of_le_one hc0 (by linarith [cubeMargin_le_one z]) hM
          _ = (1 / 4 : ℝ) * cubeMargin z := pow_one _
      calc |Submission.BoseGases.zeta1d (z.ofLp 0) * Submission.BoseGases.zeta1d (z.ofLp 1)
              * Submission.BoseGases.zeta1d (z.ofLp 2)| ^ M
          ≤ (Real.pi ^ 3 * (m 0 * m 1 * m 2)) ^ M :=
            pow_le_pow_left₀ (abs_nonneg _) hfac M
        _ = (Real.pi ^ 3) ^ M * (m 0 * m 1 * m 2) ^ M := by rw [mul_pow]
        _ ≤ (Real.pi ^ 3) ^ M * ((1 / 4 : ℝ) * cubeMargin z) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
    rw [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor, div_eq_mul_inv,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    calc |Submission.BoseGases.chiSmallBase M z|
            * (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))⁻¹
        ≤ ((Real.pi ^ 3) ^ M * ((1 / 4 : ℝ) * cubeMargin z))
            * (Real.sqrt (Submission.BoseGases.chiSmallNormSq M))⁻¹ :=
          mul_le_mul_of_nonneg_right hbase (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = (Submission.BoseGases.chiSmallNormFactor M * (Real.pi ^ 3) ^ M / 4) * cubeMargin z := by
          rw [Submission.BoseGases.chiSmallNormFactor]; ring

/-! ## 4. The linear margin bound for the cube window -/

/-- **The linear margin bound for the cube window**: `chiSmallB M ℓ d u` vanishes at least
linearly in `boxMargin ℓ d u` on the sliding box. -/
theorem chiSmallB_abs_le_boxMargin (M : ℕ) (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, x ∈ Submission.BoseGases.dlBox ℓ d u →
      |Submission.BoseGases.chiSmallB M ℓ d u x| ≤ C * Work.BoseFixB1B.boxMargin ℓ d u x := by
  obtain ⟨K, hK0, hK⟩ := Work.BoseFixB1B.abs_chi_le_lin_margin
  obtain ⟨CM, hCM0, hCM⟩ := chiSmall_le_linMarg M hM
  have hld : (0 : ℝ) < ℓ * d := mul_pos hℓ hd
  refine ⟨max Submission.BoseGases.chiSupAbs (CM * (1 / 2)) * (K / ℓ + CM / (ℓ * d)), ?_, ?_⟩
  · refine mul_nonneg ?_ (add_nonneg (div_nonneg hK0 hℓ.le) (div_nonneg hCM0 hld.le))
    exact le_trans Submission.BoseGases.chiSupAbs_nonneg (le_max_left _ _)
  · intro x hx
    have hbm : Work.BoseFixB1B.boxMargin ℓ d u x
        = min (Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|))
            (Finset.univ.inf' Finset.univ_nonempty
              (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|)) := rfl
    set A : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|)
    set B : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun i : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) i|)
    have h0 : 0 ≤ min A B := by rw [← hbm]; exact Work.BoseFixB1B.boxMargin_nonneg_iff.mpr hx
    have hA0 : 0 ≤ A := le_trans h0 (min_le_left A B)
    have hB0 : 0 ≤ B := le_trans h0 (min_le_right A B)
    have hA : ℓ / 2 - ‖x‖ ≤ A := by
      refine Finset.le_inf' Finset.univ_nonempty (fun i : Fin 3 => ℓ / 2 - |x i|) (fun i _ => ?_)
      have hi : |x i| ≤ ‖x‖ := by
        have h := PiLp.norm_apply_le x i
        simpa [Real.norm_eq_abs] using h
      linarith
    have hmulA : max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ ≤ A := by
      have hsplit : max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ = max 0 (ℓ / 2 - ‖x‖) := by
        rw [max_mul_of_nonneg _ _ hℓ.le, zero_mul]
        congr 1
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hℓ)]
        ring
      rw [hsplit]
      exact Work.BoseFixB1B.max_zero_le_of_le hA0 hA
    have hF1 : |Submission.BoseGases.chiScale ℓ x| ≤ (K / ℓ) * A := by
      have h1 : |Submission.BoseGases.chiScale ℓ x| ≤ K * max 0 (1 / 2 - ‖x‖ / ℓ) :=
        Work.BoseFixB1B.abs_chiScale_le_lin_margin hK hℓ x
      calc |Submission.BoseGases.chiScale ℓ x| ≤ K * max 0 (1 / 2 - ‖x‖ / ℓ) := h1
        _ ≤ K * A / ℓ := by
            rw [le_div_iff₀ hℓ]
            calc K * max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ = K * (max 0 (1 / 2 - ‖x‖ / ℓ) * ℓ) := by
                  ring
              _ ≤ K * A := mul_le_mul_of_nonneg_left hmulA hK0
        _ = (K / ℓ) * A := by ring
    have hcm : cubeMargin ((ℓ * d)⁻¹ • x - u) = B / (ℓ * d) := by
      rw [cubeMargin]
      have hcoord : ∀ j : Fin 3,
          max 0 (1 / 2 - |((ℓ * d)⁻¹ • x - u).ofLp j|)
            = (max 0 (ℓ * d / 2 - |(x - (ℓ * d) • u) j|)) / (ℓ * d) := by
        intro j
        set w : ℝ := |((ℓ * d)⁻¹ • x - u).ofLp j| with hw
        have hlin : |(x - (ℓ * d) • u) j| = (ℓ * d) * w := by
          have h : (x - (ℓ * d) • u) j = (ℓ * d) * (((ℓ * d)⁻¹ • x - u).ofLp j) := by
            rw [show (x - (ℓ * d) • u) j = x j - (ℓ * d) * u j by simp,
              show ((ℓ * d)⁻¹ • x - u).ofLp j = (ℓ * d)⁻¹ * x j - u j by simp]
            field_simp
          rw [h, abs_mul, abs_of_pos hld, hw]
        rw [hlin]
        have h2 : ℓ * d / 2 - (ℓ * d) * w = (ℓ * d) * (1 / 2 - w) := by ring
        rw [h2]
        have h3 : max 0 ((ℓ * d) * (1 / 2 - w)) = (ℓ * d) * max 0 (1 / 2 - w) := by
          rw [mul_max_of_nonneg _ _ hld.le, mul_zero]
        rw [h3, mul_comm (ℓ * d) (max 0 (1 / 2 - w))]
        exact (mul_div_cancel_right₀ _ (ne_of_gt hld)).symm
      have hmax : Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 3 =>
          max 0 (ℓ * d / 2 - |(x - (ℓ * d) • u) j|)) = B := by
        have hfun : (fun j : Fin 3 => max 0 (ℓ * d / 2 - |(x - (ℓ * d) • u) j|))
            = (fun j : Fin 3 => ℓ * d / 2 - |(x - (ℓ * d) • u) j|) := by
          funext j
          exact max_eq_right (le_trans hB0 (Finset.inf'_le _ (Finset.mem_univ j)))
        rw [hfun]
      simp only [hcoord]
      rw [inf'_univ_div_const hld, hmax]
    have hF2 : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤ (CM / (ℓ * d)) * B := by
      refine le_trans (hCM _) ?_
      rw [hcm, show (CM / (ℓ * d)) * B = CM * (B / (ℓ * d)) by ring]
    have hS0 : 0 ≤ max Submission.BoseGases.chiSupAbs (CM * (1 / 2)) :=
      le_trans Submission.BoseGases.chiSupAbs_nonneg (le_max_left _ _)
    have hF1sup : |Submission.BoseGases.chiScale ℓ x|
        ≤ max Submission.BoseGases.chiSupAbs (CM * (1 / 2)) :=
      le_trans (Submission.BoseGases.chiScale_abs_le_sup ℓ x) (le_max_left _ _)
    have hF2sup : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)|
        ≤ max Submission.BoseGases.chiSupAbs (CM * (1 / 2)) := by
      refine le_trans (hCM _) ?_
      calc CM * cubeMargin ((ℓ * d)⁻¹ • x - u) ≤ CM * (1 / 2) :=
            mul_le_mul_of_nonneg_left (cubeMargin_le_half _) hCM0
        _ ≤ max Submission.BoseGases.chiSupAbs (CM * (1 / 2)) := le_max_right _ _
    have hfin := Work.BoseFixB1B.abs_mul_le_of_margin_bounds
      (f := Submission.BoseGases.chiScale ℓ x)
      (g := Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
      (A := A) (B := B) (c₁ := K / ℓ) (c₂ := CM / (ℓ * d))
      (S := max Submission.BoseGases.chiSupAbs (CM * (1 / 2)))
      hA0 hB0 (div_nonneg hK0 hℓ.le) (div_nonneg hCM0 hld.le) hS0 hF1 hF2sup hF1sup hF2
    rw [hbm, Submission.BoseGases.chiSmallB, abs_mul]
    exact hfin

/-! ## 5. A global derivative bound -/

/-- The cube window is `C³` and compactly supported, so its Fréchet derivative is globally
bounded. -/
theorem exists_bound_fderiv_chiSmallB {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y‖ ≤ C := by
  have hcont : Continuous (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u)) :=
    (Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u).continuous_fderiv (by simp)
  have hcpt : HasCompactSupport (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u)) :=
    (Submission.BoseGases.chiSmallB_hasCompactSupport (by omega) hℓ u).fderiv ℝ
  obtain ⟨C, hCpos, hCle⟩ := (hcpt.isCompact_range hcont).isBounded.subset_closedBall_lt 0 0
  exact ⟨C, le_of_lt hCpos, fun y => by
    have hy := hCle ⟨y, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact hy⟩

/-! ## 6. Sup bounds for the window and its gradient -/

/-- Sup bounds for the cube window and for the square of its gradient. -/
theorem chiSmallB_sup_bounds {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y : E3, |Submission.BoseGases.chiSmallB M ℓ d u y| ≤ C)
      ∧ (∀ y : E3, (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y
          (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) := by
  have hcd : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
    Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u
  have hcs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport (by omega) hℓ u
  have hcontG : Continuous (fun y : E3 => ∑ k : Fin 3,
      (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    have h1 : Continuous (fun y : E3 =>
        fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y) :=
      hcd.continuous_fderiv (by simp)
    exact continuous_finsetSum _ (fun k _ => ((h1.clm_apply continuous_const).pow 2))
  obtain ⟨S, hS⟩ := hcs.exists_bound_of_continuousOn hcd.continuous.continuousOn
  obtain ⟨S', hS'⟩ := hcs.exists_bound_of_continuousOn hcontG.continuousOn
  have hvan : ∀ y ∉ tsupport (Submission.BoseGases.chiSmallB M ℓ d u),
      Submission.BoseGases.chiSmallB M ℓ d u y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_tsupport _ (Function.mem_support.mpr hne))
  have hvanG : ∀ y ∉ tsupport (Submission.BoseGases.chiSmallB M ℓ d u),
      (∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y
        (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 := by
    intro y hy
    have hzero : fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) y = 0 := by
      obtain ⟨ε, hεpos, hεsub⟩ :=
        (Metric.isOpen_iff.mp isClosed_closure.isOpen_compl) y hy
      have hev : (Submission.BoseGases.chiSmallB M ℓ d u) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds y hεpos] with z hz
        exact hvan z (hεsub (Metric.mem_ball.mpr hz))
      rw [Work.BoseFixB1B.fderiv_eq_zero_of_eventuallyEq_const hev]
    simp [hzero]
  refine ⟨max (max S 0) (max S' 0), le_max_of_le_left (le_max_right _ _), ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ tsupport (Submission.BoseGases.chiSmallB M ℓ d u)
    · have h := hS y hy
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [hvan y hy, abs_zero]
      exact le_max_of_le_left (le_max_right _ _)
  · intro y
    by_cases hy : y ∈ tsupport (Submission.BoseGases.chiSmallB M ℓ d u)
    · have h := hS' y hy
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at h
      exact le_trans h (le_max_of_le_right (le_max_left _ _))
    · rw [hvanG y hy]
      exact le_max_of_le_right (le_max_right _ _)

/-! ## 7. Support facts -/

theorem chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u x : E3} (hx : x ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
  by_contra hne
  exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)

theorem chiSmallB_mul_boxInd {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u x : E3) :
    Submission.BoseGases.chiSmallB M ℓ d u x
        * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x
      = Submission.BoseGases.chiSmallB M ℓ d u x := by
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hx, mul_one]
  · rw [Set.indicator_of_notMem hx, mul_zero, chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd hx]

/-! ## 8. The collar-weighted mass of the cube window -/

/-- The window-weighted collar integral is linear in `δ`. -/
theorem integral_chiSmallB_sq_collarInd_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
      (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
          * Work.BoseFixB1B.collarInd ℓ d u δ y) ≤ C * δ := by
  obtain ⟨Cc, hCc0, hCc⟩ := Work.BoseFixB1B.collarBox_le (L := ℓ) (d := d) hℓ hd u
  refine ⟨(kappaS M) ^ 2 * Cc * 2, ?_, ?_⟩
  · have h1 : 0 ≤ (kappaS M) ^ 2 := sq_nonneg _
    positivity
  · intro δ hδ
    have h2δ : (0 : ℝ) < 2 * δ := by linarith
    set T : Set E3 := Work.BoseFixB1B.collarBoxSet ℓ d (2 * δ) u with hTdef
    have hTmeas : MeasurableSet T := by
      rw [hTdef]; exact Work.BoseFixB1B.measurableSet_collarBoxSet ℓ d (2 * δ) u
    have hTfin : (volume : Measure E3) T ≠ ⊤ := by
      intro htop
      have hle := hCc (2 * δ) h2δ
      rw [htop] at hle
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)
    have hsupp : ∀ y : E3, Work.BoseFixB1B.collarInd ℓ d u δ y ≠ 0 → y ∈ T := by
      intro y hy
      have hmem : y ∈ Submission.BoseGases.dlBox ℓ d u ∩
          {z : E3 | Work.BoseFixB1B.boxMargin ℓ d u z ≤ δ} := by
        by_contra h
        exact hy (Set.indicator_of_notMem h (fun _ : E3 => (1 : ℝ)))
      rw [hTdef, Work.BoseFixB1B.collarBoxSet]
      exact ⟨hmem.1, lt_of_le_of_lt hmem.2 (by linarith : δ < 2 * δ)⟩
    have hM0 : 0 ≤ (kappaS M) ^ 2 := sq_nonneg _
    have hbd : ∀ y : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
            * Work.BoseFixB1B.collarInd ℓ d u δ z) y
        ≤ (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y := by
      intro y
      by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hy]
        rcases Work.BoseFixB1B.collarInd_eq_one_or_zero ℓ d u δ y with h1 | h0
        · have hyT : y ∈ T := hsupp y (by rw [h1]; norm_num)
          rw [h1, mul_one, Set.indicator_of_mem hyT]
          simpa using chiSmallB_sq_le_kappaS hM (ℓ := ℓ) (d := d) u y
        · rw [h0, mul_zero]
          have hpos : (0 : ℝ) ≤ (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y :=
            mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
          simpa using hpos
      · rw [Set.indicator_of_notMem hy]
        have hpos : (0 : ℝ) ≤ (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y :=
          mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
        simpa using hpos
    have hgi : Integrable (fun y : E3 => (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y)
        (volume : Measure E3) := by
      have hind : Integrable (T.indicator (1 : E3 → ℝ)) (volume : Measure E3) :=
        (integrable_indicator_iff hTmeas).mpr (integrableOn_const (C := (1 : ℝ)) hTfin (by simp))
      exact hind.const_mul _
    have hmono : (∫ y : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
            * Work.BoseFixB1B.collarInd ℓ d u δ z) y)
        ≤ ∫ y : E3, (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => by
        by_cases hy : y ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem hy]
          exact mul_nonneg (sq_nonneg _) (Work.BoseFixB1B.collarInd_nonneg ℓ d u δ y)
        · simp [Set.indicator_of_notMem hy])) hgi
        (Filter.Eventually.of_forall hbd)
    have hright : (∫ y : E3, (kappaS M) ^ 2 * T.indicator (1 : E3 → ℝ) y)
        = (kappaS M) ^ 2 * ((volume : Measure E3) T).toReal := by
      rw [integral_const_mul, integral_indicator_one hTmeas, Measure.real_def]
    have hleft : (∫ y : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
            * Work.BoseFixB1B.collarInd ℓ d u δ z) y)
        = ∫ y in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
              * Work.BoseFixB1B.collarInd ℓ d u δ y :=
      integral_indicator (Submission.BoseGases.acube_measurable ℓ)
    have hvol : ((volume : Measure E3) T).toReal ≤ Cc * (2 * δ) := by
      rw [hTdef]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hCc (2 * δ) h2δ)
    rw [← hleft]
    refine le_trans hmono ?_
    rw [hright]
    calc (kappaS M) ^ 2 * ((volume : Measure E3) T).toReal
        ≤ (kappaS M) ^ 2 * (Cc * (2 * δ)) :=
          mul_le_mul_of_nonneg_left hvol (sq_nonneg _)
      _ = ((kappaS M) ^ 2 * Cc * 2) * δ := by ring

end Work.BoseB1Cube.Winchk
