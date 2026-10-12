import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds
import Submission.Work.BoseFixB1S.CubeWindow.marginalCube
import Submission.Work.BoseFixB1S.CubeWindowKinetic
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chiSmallB_bounds3` — the `C³` window certificate for the cube cutoff

The **window certificate** for the (cube-supported) cutoff

    `chiSmallB M ℓ d u x = χ(x/ℓ) · χ_M((ℓd)⁻¹ • x − u)`

at the `C³` level, i.e. exactly what the sliding-box hand-offs consume:

* the complexified window `z ↦ (chiSmallB M ℓ d u z : ℂ)` is `C³` in `z` **for every** sliding
  parameter `u` (this is `3 + 1 ≤ M`, the point where the cosine-`M`-th-power bump `χ_M` is `C³`);
* the window is supported in the **fixed** ball of radius `ℓ/2`, uniformly in `u` (only the
  `ℓ`-scale factor `χ(·/ℓ)` can vanish the product); and
* the iterated derivatives of order `k ≤ 3` are bounded by a constant `G k` **independent of `u`**.

The uniformity in `u` is the point of the last item: `u` enters only through the *translation*
`z ↦ (ℓd)⁻¹ • z − u` of the small-box factor, and translation invariance of the iterated
derivative (`iteratedFDeriv_comp_sub`) makes the bound uniform.  The explicit constants are the
product-rule constants of the two factors separately, `win.chiBumpCBound 3` for the corpus bump
`χ` and `win.chiSmallCBound 3 M` for `χ_M`, with the dilations
`‖ℓ⁻¹ • 1‖` and `‖(ℓd)⁻¹ • 1‖` supplying the powers.

The `C^∞` ball-window bounds of the frozen chapter do **not** apply here (`chiSmallB` is only
`C^{M−1}`), which is why the derivative bookkeeping is redone from scratch in this file.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The uniform support radius -/

/-- **Uniform support radius of the cube cutoff.**  If `chiSmallB M ℓ d u z ≠ 0` then
`‖z‖ ≤ ℓ/2`: the product can only be nonzero when its `ℓ`-scale factor `χ(ℓ⁻¹ • z)` is nonzero,
and the corpus bump `χ` vanishes for `‖·‖ ≥ 1/2`. -/
lemma chiSmallB3_support_radius {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {z : E3} (hz : Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0) : ‖z‖ ≤ ℓ / 2 := by
  have h1 : Submission.BoseGases.chiScale ℓ z ≠ 0 :=
    fun h => hz (by dsimp [Submission.BoseGases.chiSmallB]; rw [h, zero_mul])
  have h2 : Submission.BoseGases.chi (ℓ⁻¹ • z) ≠ 0 := h1
  have hlt : ‖ℓ⁻¹ • z‖ < 1 / 2 := by
    by_contra hcon
    exact h2 (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have hnorm : ‖ℓ⁻¹ • z‖ = ‖z‖ / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, div_eq_inv_mul, mul_comm]
  rw [hnorm] at hlt
  have hlt' : ‖z‖ < 1 / 2 * ℓ := (div_lt_iff₀ hℓ).mp hlt
  linarith

/-! ## 2. Complexified `C³`-smoothness in the space variable -/

/-- **The complexified cube cutoff is `C³` in the space variable** for every `M ≥ 4` (i.e.
`3 + 1 ≤ M`), uniformly in the sliding parameter `u`. -/
lemma chiSmallB3_contDiff {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    ContDiff ℝ 3 (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ)) := by
  have hreal : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
    Work.BoseFixB1S.win.contDiff_chiSmallB 3 M (by omega) (ne_of_gt hℓ) (ne_of_gt hd) u
  have hclm := Complex.ofRealCLM.contDiff.comp hreal
  simpa [Function.comp_def] using hclm

/-! ## 3. Uniform bounds on the iterated derivatives of order `≤ 3`

The two factors are bounded separately: the `ℓ`-scale corpus bump is handled through its
complexification `chiBumpC`, the `(ℓd)`-scale cosine bump through `chiSmallC M`, and the two
bounds are combined by the product rule.  Every constant below is `u`-independent, which is the
whole content: `u` is a translation of the argument of the *second* factor only. -/

/-- **Derivative bound for the big-box factor.**  The `j`-th iterated derivative (`j ≤ 3`) of the
complexified `ℓ`-scale corpus window `χ(·/ℓ)` at any point is at most
`chiBumpCBound 3 · ‖ℓ⁻¹ • 1‖ ^ j`. -/
lemma chiSmallB3_scaleC_iteratedFDeriv_le (ℓ : ℝ) (j : ℕ) (hj : j ≤ 3) (z : E3) :
    ‖iteratedFDeriv ℝ j (fun x : E3 => (Submission.BoseGases.chiScale ℓ x : ℂ)) z‖
      ≤ Work.BoseFixB1S.win.chiBumpCBound 3 * ‖((ℓ⁻¹ : ℝ) • (1 : E3 →L[ℝ] E3))‖ ^ j := by
  set L : E3 →L[ℝ] E3 := (ℓ⁻¹) • (1 : E3 →L[ℝ] E3) with hL
  have hLx : ∀ x : E3, L x = (ℓ⁻¹) • x := by
    intro x
    rw [hL]
    simp
  have hfun : (fun x : E3 => (Submission.BoseGases.chiScale ℓ x : ℂ))
      = fun x : E3 => Work.BoseFixB1S.win.chiBumpC (L x) := by
    funext x
    rw [hLx x]
    rfl
  rw [hfun]
  have hstep : iteratedFDeriv ℝ j (fun x : E3 => Work.BoseFixB1S.win.chiBumpC (L x)) z
      = (iteratedFDeriv ℝ j Work.BoseFixB1S.win.chiBumpC (L z)).compContinuousLinearMap
          (fun _ : Fin j => L) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L
      Work.BoseFixB1S.win.chiBumpC_contDiff z (i := j) (hi := by exact_mod_cast le_top)
  rw [hstep]
  have hprod : ∏ _ : Fin j, ‖L‖ = ‖L‖ ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    ‖(iteratedFDeriv ℝ j Work.BoseFixB1S.win.chiBumpC (L z)).compContinuousLinearMap
        (fun _ : Fin j => L)‖
        ≤ ‖iteratedFDeriv ℝ j Work.BoseFixB1S.win.chiBumpC (L z)‖ * ∏ _ : Fin j, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j Work.BoseFixB1S.win.chiBumpC (L z)‖ * ‖L‖ ^ j := by
          rw [hprod]
    _ ≤ Work.BoseFixB1S.win.chiBumpCBound 3 * ‖L‖ ^ j :=
          mul_le_mul_of_nonneg_right
            (Work.BoseFixB1S.win.norm_iteratedFDeriv_chiBumpC_le 3 j hj (L z)) (by positivity)

/-- **Derivative bound for the small-box factor.**  The `j`-th iterated derivative (`j ≤ 3`) of
`chiSmallC M ((c • ·) − u)` at any point is at most `chiSmallCBound 3 M · ‖c • 1‖ ^ j`,
**uniformly in the shift `u`** (the translation is invisible for the iterated derivative, by
`iteratedFDeriv_comp_sub`). -/
lemma chiSmallB3_smallC_sub_iteratedFDeriv_le {M : ℕ} (hM : 4 ≤ M) (j : ℕ) (hj : j ≤ 3)
    (c : ℝ) (u z : E3) :
    ‖iteratedFDeriv ℝ j (fun x : E3 => Work.BoseFixB1S.win.chiSmallC M (c • x - u)) z‖
      ≤ Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) * ‖(c • (1 : E3 →L[ℝ] E3))‖ ^ j := by
  set L : E3 →L[ℝ] E3 := c • (1 : E3 →L[ℝ] E3) with hL
  have hLx : ∀ x : E3, L x = c • x := by
    intro x
    rw [hL]
    simp
  have htrans : ContDiff ℝ 3 (fun y : E3 => y - u) := by fun_prop
  have hg : ContDiff ℝ 3 (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u)) :=
    (Work.BoseFixB1S.win.contDiff_chiSmallC 3 M (by omega)).comp htrans
  have hfun : (fun x : E3 => Work.BoseFixB1S.win.chiSmallC M (c • x - u))
      = fun x : E3 => Work.BoseFixB1S.win.chiSmallC M (L x - u) := by
    funext x
    rw [hLx x]
  rw [hfun]
  have hstep : iteratedFDeriv ℝ j
        (fun x : E3 => Work.BoseFixB1S.win.chiSmallC M (L x - u)) z
      = (iteratedFDeriv ℝ j
          (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)).compContinuousLinearMap
          (fun _ : Fin j => L) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hg z (i := j)
      (hi := by exact_mod_cast hj)
  rw [hstep]
  have hprod : ∏ _ : Fin j, ‖L‖ = ‖L‖ ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : iteratedFDeriv ℝ j
        (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)
      = iteratedFDeriv ℝ j (Work.BoseFixB1S.win.chiSmallC M) (L z - u) :=
    iteratedFDeriv_comp_sub (f := Work.BoseFixB1S.win.chiSmallC M) j u (L z)
  calc
    ‖(iteratedFDeriv ℝ j (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u))
        (L z)).compContinuousLinearMap (fun _ : Fin j => L)‖
        ≤ ‖iteratedFDeriv ℝ j (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)‖
            * ∏ _ : Fin j, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j (fun y : E3 => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)‖
            * ‖L‖ ^ j := by
          rw [hprod]
    _ ≤ Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) * ‖L‖ ^ j := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hsub]
          exact Work.BoseFixB1S.win.norm_iteratedFDeriv_chiSmallC_le 3 M (by omega) j hj (L z - u)

/-- The explicit uniform bound on the iterated derivatives of the complexified cube cutoff: the
product rule applied to the two factors, with the constants frozen at order `3` and the dilations
`ℓ⁻¹` and `(ℓd)⁻¹` supplying the powers.  Only the values at `k ≤ 3` are meaningful; for `k > 3`
the function is set to `0` (where no bound is claimed). -/
noncomputable def chiSmallB3WinG (M : ℕ) (hM : 4 ≤ M) (ℓ d : ℝ) (k : ℕ) : ℝ :=
  if k ≤ 3 then
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        (Work.BoseFixB1S.win.chiBumpCBound 3 * ‖((ℓ⁻¹ : ℝ) • (1 : E3 →L[ℝ] E3))‖ ^ i) *
        (Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) *
          ‖(((ℓ * d)⁻¹ : ℝ) • (1 : E3 →L[ℝ] E3))‖ ^ (k - i))
  else 0

lemma chiSmallB3WinG_nonneg (M : ℕ) (hM : 4 ≤ M) (ℓ d : ℝ) (k : ℕ) :
    0 ≤ chiSmallB3WinG M hM ℓ d k := by
  rw [chiSmallB3WinG]
  by_cases hk : k ≤ 3
  · rw [if_pos hk]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : (0 : ℝ) ≤ Work.BoseFixB1S.win.chiBumpCBound 3 :=
      Work.BoseFixB1S.win.chiBumpCBound_nonneg 3
    have h2 : (0 : ℝ) ≤ Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) :=
      Work.BoseFixB1S.win.chiSmallCBound_nonneg 3 M (by omega)
    exact mul_nonneg
      (mul_nonneg (by positivity) (mul_nonneg h1 (by positivity)))
      (mul_nonneg h2 (by positivity))
  · rw [if_neg hk]

/-- **The quantitative uniform derivative bound.**  For every `k ≤ 3`, every sliding parameter `u`
and every point `z`, the `k`-th iterated derivative of the complexified cube cutoff is bounded by
the `u`-independent constant `chiSmallB3WinG M hM ℓ d k`. -/
lemma chiSmallB3_complex_iteratedFDeriv_le {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : E3) (k : ℕ) (hk : k ≤ 3) (z : E3) :
    ‖iteratedFDeriv ℝ k (fun x : E3 => (Submission.BoseGases.chiSmallB M ℓ d u x : ℂ)) z‖
      ≤ chiSmallB3WinG M hM ℓ d k := by
  have hprod : (fun x : E3 => (Submission.BoseGases.chiSmallB M ℓ d u x : ℂ))
      = fun x : E3 =>
          (Submission.BoseGases.chiScale ℓ x : ℂ) *
            (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) : ℂ) := by
    funext x
    simp only [Submission.BoseGases.chiSmallB, Complex.ofReal_mul]
  rw [hprod]
  have hA0 : ContDiff ℝ 3 (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hA : ContDiff ℝ 3 (fun x : E3 => (Submission.BoseGases.chiScale ℓ x : ℂ)) := by
    have hclm := hA0.continuousLinearMap_comp Complex.ofRealCLM
    simpa [Function.comp_def] using hclm
  have hB : ContDiff ℝ 3
      (fun x : E3 => (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) : ℂ)) :=
    (Work.BoseFixB1S.win.contDiff_chiSmallC 3 M (by omega)).comp (by fun_prop)
  rw [chiSmallB3WinG, if_pos hk]
  refine (norm_iteratedFDeriv_mul_le hA hB z (n := k) (hn := by exact_mod_cast hk)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi3 : i ≤ 3 := by omega
  have hki3 : k - i ≤ 3 := by omega
  have h1 := chiSmallB3_scaleC_iteratedFDeriv_le ℓ i hi3 z
  have h2 := chiSmallB3_smallC_sub_iteratedFDeriv_le (M := M) hM (k - i) hki3 ((ℓ * d)⁻¹) u z
  have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
  have hL1 : (0 : ℝ) ≤ ‖((ℓ⁻¹ : ℝ) • (1 : E3 →L[ℝ] E3))‖ ^ i := by positivity
  have hb1 : (0 : ℝ) ≤ Work.BoseFixB1S.win.chiBumpCBound 3 :=
    Work.BoseFixB1S.win.chiBumpCBound_nonneg 3
  refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _) ?_
  exact mul_nonneg hc (mul_nonneg hb1 hL1)

/-! ## 4. The window certificate -/

theorem chiSmallB_bounds3 {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∀ u : EuclideanSpace ℝ (Fin 3),
        ContDiff ℝ 3 (fun z : EuclideanSpace ℝ (Fin 3) =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ))) ∧
    ∃ (R : ℝ) (G : ℕ → ℝ), 0 < R ∧ (∀ k : ℕ, 0 ≤ G k) ∧
      (∀ (u z : EuclideanSpace ℝ (Fin 3)),
        Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0 → ‖z‖ ≤ R) ∧
      (∀ (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ), k ≤ 3 → ∀ z : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin 3) =>
          (Submission.BoseGases.chiSmallB M ℓ d u z : ℂ)) z‖ ≤ G k) := by
  refine ⟨fun u => chiSmallB3_contDiff hM hℓ hd u, ℓ / 2, chiSmallB3WinG M hM ℓ d,
    by positivity, ?_, ?_, ?_⟩
  · intro k
    exact chiSmallB3WinG_nonneg M hM ℓ d k
  · intro u z hz
    exact chiSmallB3_support_radius (M := M) (by omega) hℓ hd u hz
  · intro u k hk z
    exact chiSmallB3_complex_iteratedFDeriv_le (M := M) hM hℓ u k hk z

end Work.BoseFixB1S
