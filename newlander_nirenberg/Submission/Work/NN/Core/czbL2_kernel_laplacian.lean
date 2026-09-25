import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.flatLap_bmKerEps
import Submission.Work.CR.Flat.Cauchy.bmKerEpsAux
import Submission.Work.CR.Flat.Cauchy.bmRhs_tendsto_eps
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.NN.Core.czbL2_integral_radial_dCoord
import Submission.Work.NN.Core.czbL2_integral_mul_flatLap_eq
import Submission.Work.NN.Core.czbL2_tendsto_integral_bmKerEps_mul

namespace Work.NN.Core

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

open Work.CR.Flat.Cauchy

/-! ## Auxiliary facts about supports and about `flatLap`

These are the bookkeeping lemmas needed to feed the regularised kernel `bmKerEps`
(`Work.CR.Flat.Cauchy.bmKerEps`) and its limits to the dominated-convergence statements of
the workspace.  A compactly supported function vanishes off a ball of some radius `R`
(`exists_norm_radius_of_hasCompactSupport`), its Wirtinger derivatives vanish off the ball of
radius `R + 1` and `flatLap` off the ball of radius `R + 2`; `flatLap` of a `C²` function is
continuous and compactly supported. -/

/-- A compactly supported function vanishes off some ball. -/
lemma exists_norm_radius_of_hasCompactSupport {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : HasCompactSupport f) : ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0 := by
  obtain ⟨R₀, hR₀⟩ := (hf.isCompact.isBounded).subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max R₀ 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hne
  have hmem : x ∈ Metric.closedBall (0 : Fin n → ℂ) R₀ :=
    hR₀ (subset_tsupport f (Function.mem_support.mpr hne))
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hle : ‖x‖ ≤ max R₀ 0 := le_trans hmem (le_max_left R₀ 0)
  linarith

/-- The `(1,0)`-Wirtinger derivative of a `C²` function is `C¹`. -/
lemma contDiff_dCoord_of_contDiff_two {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (j : Fin n) : ContDiff ℝ 1 (fun z => Work.CR.Flat.dCoord j ψ z) := by
  have hm : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((2 : ℕ) : WithTop ℕ∞) := by norm_num
  have h1 : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ ψ) := hψ.fderiv_right hm
  have h3 : (fun z => Work.CR.Flat.dCoord j ψ z)
      = ⇑(Work.CR.Flat.Cauchy.dCoordPhi j) ∘ (fderiv ℝ ψ) := by
    funext z
    exact congrFun (Work.CR.Flat.Cauchy.dCoord_eq_comp j ψ) z
  rw [h3]
  exact (Work.CR.Flat.Cauchy.dCoordPhi j).contDiff.comp h1

/-- The `(0,1)`-Wirtinger derivative of a `C²` function is `C¹`. -/
lemma contDiff_dbarCoord_of_contDiff_two {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (j : Fin n) : ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarCoord j ψ z) := by
  have hm : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((2 : ℕ) : WithTop ℕ∞) := by norm_num
  have h1 : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ ψ) := hψ.fderiv_right hm
  have h3 : (fun z => Work.CR.Flat.dbarCoord j ψ z)
      = ⇑(Work.CR.Flat.Polydisc.dbarCoordPhi j) ∘ (fderiv ℝ ψ) := by
    funext z
    exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp j ψ) z
  rw [h3]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp h1

/-- A function vanishing off the ball of radius `R` has `(1,0)`-derivative vanishing off the
ball of radius `R + 1`. -/
lemma dCoord_eq_zero_of_supp {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → ψ x = 0) (j : Fin n) :
    ∀ x : Fin n → ℂ, R + 1 ≤ ‖x‖ → Work.CR.Flat.dCoord j ψ x = 0 :=
  fun x hx => Work.CR.Flat.Cauchy.bmCz.dCoord_eq_zero_of_lt_norm hsupp j (by linarith)

/-- A function vanishing off the ball of radius `R` has `(0,1)`-derivative vanishing off the
ball of radius `R + 1`. -/
lemma dbarCoord_eq_zero_of_supp {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → ψ x = 0) (j : Fin n) :
    ∀ x : Fin n → ℂ, R + 1 ≤ ‖x‖ → Work.CR.Flat.dbarCoord j ψ x = 0 :=
  fun x hx => Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp j (by linarith)

/-- The flat Laplacian of a `C²` function is continuous. -/
lemma continuous_flatLap {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (flatLap ψ) := by
  have hfun : flatLap ψ
      = fun z => 4 * ∑ k : Fin n,
          Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k ψ w) z := by
    funext z
    exact flatLap_apply ψ z
  rw [hfun]
  refine Continuous.mul continuous_const (continuous_finsetSum _ fun k _ => ?_)
  exact Work.CR.Flat.Cauchy.bmCz.continuous_dCoord (contDiff_dbarCoord_of_contDiff_two hψ k) k

/-- A function vanishing off the ball of radius `R` has `flatLap` vanishing off the ball
of radius `R + 2`. -/
lemma flatLap_eq_zero_of_supp {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → ψ x = 0) {x : Fin n → ℂ} (hx : R + 2 ≤ ‖x‖) :
    flatLap ψ x = 0 := by
  rw [flatLap_apply]
  have h : ∀ k : Fin n, Work.CR.Flat.dCoord k (fun w => Work.CR.Flat.dbarCoord k ψ w) x = 0 := by
    intro k
    exact Work.CR.Flat.Cauchy.bmCz.dCoord_eq_zero_of_lt_norm
      (dbarCoord_eq_zero_of_supp hsupp k) k (by linarith)
  rw [Finset.sum_eq_zero fun k _ => h k, mul_zero]

/-- The flat Laplacian of a compactly supported `C²` function is compactly supported. -/
lemma hasCompactSupport_flatLap {n : ℕ} {ψ : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → ψ x = 0) : HasCompactSupport (flatLap ψ) :=
  Work.CR.Flat.Cauchy.bmCz.hasCompactSupport_of_norm_le (R := R + 2)
    (fun x hx => @flatLap_eq_zero_of_supp n ψ R hsupp x hx)

/-! ## Smoothness of the regularised kernel -/

/-- For `ε > 0` the regularised Bochner–Martinelli kernel `bmKerEps k ε` is `C²`. -/
lemma contDiff_two_bmKerEps {n : ℕ} (k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (bmKerEps k ε) := by
  have hnrm : ContDiff ℝ ⊤ (fun x : Fin n → ℂ => nrmSq x) := by
    have h : (fun x : Fin n → ℂ => nrmSq x) = fun x => ∑ j : Fin n, ‖x j‖ ^ 2 := rfl
    rw [h]
    exact ContDiff.sum (s := Finset.univ) fun j _ =>
      (contDiff_norm_sq ℝ (E := ℂ) (n := ⊤)).comp
        (((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
          (𝕜 := ℝ))
  have hnum : ContDiff ℝ ⊤ (fun x : Fin n → ℂ => starRingEnd ℂ (x k)) := by
    have h : (fun x : Fin n → ℂ => starRingEnd ℂ (x k))
        = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘
            ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := by
      funext x; simp
    rw [h]
    exact Complex.conjCLE.contDiff.comp
      (((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))
  have hden : ContDiff ℝ ⊤ (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n) :=
    (Complex.ofRealCLM.contDiff.comp (hnrm.add contDiff_const)).pow n
  have hne : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n ≠ 0 := by
    intro x
    apply pow_ne_zero
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg x; positivity)
  have hfun : bmKerEps k ε
      = fun x : Fin n → ℂ => starRingEnd ℂ (x k) * ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)⁻¹ := by
    funext x
    rw [bmKerEps_apply, div_eq_mul_inv]
  rw [hfun]
  exact (hnum.mul (hden.inv hne)).of_le le_top

/-! ## The regularised identity -/

/-- **The regularised Bochner–Martinelli Laplacian identity.**  For `ε > 0` and `ψ ∈ C²_c`,
`∫ x, bmKerEps j ε x · flatLap ψ x = -4 n ε² ∫ x, (nrmSq x + ε²)^{-(n+1)} · ∂_j ψ x`.
This is Green's identity applied to the smooth kernel `bmKerEps j ε`
(`czbL2_integral_mul_flatLap_eq`), whose Laplacian is computed pointwise
(`flatLap_bmKerEps`), followed by one integration by parts in the `∂_j`-direction
(`czbL2_integral_radial_dCoord`). -/
lemma integral_bmKerEps_mul_flatLap {n : ℕ} {ψ : (Fin n → ℂ) → ℂ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) (j : Fin n) :
    ∫ x, bmKerEps j ε x * flatLap ψ x
      = -4 * ∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
          * Work.CR.Flat.dCoord j ψ x := by
  have hG := czbL2_integral_mul_flatLap_eq (u := fun y => bmKerEps j ε y) (v := ψ)
    (contDiff_two_bmKerEps j hε) hψ hψc
  rw [hG]
  have hpt : ∀ x : Fin n → ℂ, flatLap (fun y => bmKerEps j ε y) x * ψ x
      = ((-4 * (n : ℂ) * ((n : ℂ) + 1) * (ε : ℂ) ^ 2)
          * ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ)) * star (x j) * ψ x := by
    intro x
    rw [flatLap_bmKerEps j hε x]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hK := czbL2_integral_radial_dCoord (n := n) hε j (hψ.of_le (by norm_num)) hψc
  calc ∫ x, ((-4 * (n : ℂ) * ((n : ℂ) + 1) * (ε : ℂ) ^ 2)
          * ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ)) * star (x j) * ψ x
      = (-4 * (n : ℂ) * ((n : ℂ) + 1) * (ε : ℂ) ^ 2)
          * ∫ x, ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ) * star (x j) * ψ x := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = -4 * (n : ℂ) * (ε : ℂ) ^ 2
          * (((n : ℂ) + 1)
              * ∫ x, ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 2) : ℝ)) : ℂ) * star (x j) * ψ x) := by
        ring
    _ = -4 * (n : ℂ) * (ε : ℂ) ^ 2
          * ∫ x, ((((nrmSq x + ε ^ 2) ^ (-(n : ℤ) - 1) : ℝ)) : ℂ)
              * Work.CR.Flat.dCoord j ψ x := by
        rw [hK]
    _ = -4 * ∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
          * Work.CR.Flat.dCoord j ψ x := by
        rw [show -4 * (n : ℂ) * (ε : ℂ) ^ 2 = -4 * ((n : ℂ) * (ε : ℂ) ^ 2) by ring, mul_assoc,
          ← MeasureTheory.integral_const_mul]
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [Complex.ofReal_zpow]
        rw [show (-(n : ℤ) - 1) = -(((n + 1 : ℕ)) : ℤ) by push_cast; ring]
        rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
        ring

/-! ## The Laplacian kernel identity -/

/-- **The Laplacian kernel identity for the Bochner–Martinelli kernel.**  For `ψ ∈ C²_c` and every
`j`, `∫ x, bmKernel j x * flatLap ψ x = 4 * bmGamma n * ∂_j ψ 0`, where
`bmKernel j x = \bar x_j / ‖x‖^{2n}` and `flatLap f = 4 Σ_k ∂_k ∂̄_k f`.

Route (everything needed is already proved in the workspace).  Write `K_j = bmKernel j` and
`K_j^ε = bmKerEps j ε`.  By dominated convergence
(`czbL2_tendsto_integral_bmKerEps_mul`) `∫ K_j^ε · flatLap ψ → ∫ K_j · flatLap ψ`, while for
`ε > 0` the regularised identity (`integral_bmKerEps_mul_flatLap`) turns the left-hand side
into `-4 n ε² ∫ (nrmSq x + ε²)^{-(n+1)} ∂_j ψ x`
`= -4 ∫ (n ε²/(nrmSq x + ε²)^{n+1}) ∂_j ψ x`.  The latter converges to
`-4 (∫ y, n/(nrmSq y+1)^{n+1}) ∂_j ψ 0` by `bmRhs_tendsto_eps`, i.e. to
`4 bmGamma n ∂_j ψ 0` because `bmGamma n = -∫ y, n/(nrmSq y+1)^{n+1}`.  Conclude with
`tendsto_nhds_unique`. -/
theorem czbL2_kernel_laplacian {n : ℕ} (hn : 0 < n) :
    ∀ (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ 2 ψ → HasCompactSupport ψ → ∀ j : Fin n,
      ∫ x : Fin n → ℂ, bmKernel j x * flatLap ψ x
        = 4 * bmGamma n * Work.CR.Flat.dCoord j ψ 0 := by
  intro ψ hψ hψc j
  obtain ⟨R, hR0, hsupp⟩ := exists_norm_radius_of_hasCompactSupport hψc
  have hsupp1 := dCoord_eq_zero_of_supp hsupp j
  have hg : ContDiff ℝ 1 (fun x : Fin n → ℂ => Work.CR.Flat.dCoord j ψ x) :=
    contDiff_dCoord_of_contDiff_two hψ j
  have hJ : Integrable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) volume :=
    (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
  have hL := czbL2_tendsto_integral_bmKerEps_mul hn (continuous_flatLap hψ)
    (hasCompactSupport_flatLap hsupp) j
  have hlim := Work.CR.Flat.Cauchy.bmRhs_tendsto_eps hn (R := R + 1) (by linarith) hg hsupp1 hJ
  have hRlim : Filter.Tendsto (fun ε : ℝ => -4 * ∫ x,
      ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
        * Work.CR.Flat.dCoord j ψ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (4 * bmGamma n * Work.CR.Flat.dCoord j ψ 0)) := by
    have h := hlim.const_mul (-4 : ℂ)
    rw [show (-4 : ℂ) * ((((∫ y : Fin n → ℂ, (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) : ℝ) : ℂ)
          * Work.CR.Flat.dCoord j ψ 0) = 4 * bmGamma n * Work.CR.Flat.dCoord j ψ 0 by
      rw [bmGamma]
      ring] at h
    exact h
  have hId : (fun ε : ℝ => ∫ x, bmKerEps j ε x * flatLap ψ x)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun ε : ℝ => -4 * ∫ x,
        ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
          * Work.CR.Flat.dCoord j ψ x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_bmKerEps_mul_flatLap hψ hψc hε j
  exact tendsto_nhds_unique hL (hRlim.congr' hId.symm)

end

end Work.NN.Core
