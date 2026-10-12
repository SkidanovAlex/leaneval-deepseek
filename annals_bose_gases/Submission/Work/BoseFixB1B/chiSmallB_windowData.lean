import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Window data for the sliding small-box cutoff `chiSmallB`

The cutoff

    `chiSmallB M ℓ d u x = χ(x/ℓ) · χ_M((ℓd)⁻¹ • x − u)`

(`Submission.BoseGases.chiSmallB`) is, for `M ≥ 4`,

* `C³` in the space variable (the `M`-th power of the cosine profile kills the derivative jumps
  of `ζ` at the cube faces to order `M − 1 ≥ 3`); and
* compactly supported **uniformly in the shift `u`** — the ball factor `χ(·/ℓ)` already forces
  `‖x‖ < ℓ/2`, so the `u`-dependent small-box factor is irrelevant for the support; and
* has **iterated derivatives of every order `k ≤ 3` bounded uniformly in `u`** — translations do
  not change the norm of an iterated derivative (`iteratedFDeriv_comp_sub`), so the only losses
  are the dilations `ℓ⁻¹` and `(ℓd)⁻¹`.

The quantitative bound is the product rule applied to the two factors, with the fixed constants
`chiBumpCBound 3` (the corpus bump) and `chiSmallCBound 3 M` (the cosine-`M` bump) and no
dependence on the shift `u`.

This is the "window data" certificate consumed by the port hand-offs (`tBwordKinInd`, the pairing
kernels `wSmall1Pair` and the cubic error `boxQ3`), which need the window of the first conjunct to
be `C³` and the derivative bounds to be **independent of `u`**.
-/

namespace Work.BoseFixB1B

open scoped ContDiff Topology

open Submission.BoseGases (chi chiSmall chiScale chiSmallB chi_eq_zero_of_half_le_norm
  chi_contDiff)

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Smoothness of `chiSmallB` in the space variable -/

/-- **The corpus small-box cutoff is `C³` in the space variable** (`M ≥ 4`): the `ℓ`-scale factor
`χ(·/ℓ)` is smooth, and the `(ℓd)`-scale factor `χ_M((ℓd)⁻¹ • · − u)` is `C³` because
`chiSmall M` is `C³` for `M ≥ 4` (`Work.BoseFixB1S.win.contDiff_chiSmall`), composed with the
smooth affine map `x ↦ (ℓd)⁻¹ • x − u`. -/
theorem chiSmallB_contDiff_three {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    ContDiff ℝ 3 (chiSmallB M ℓ d u) := by
  have hchi : ContDiff ℝ 3 (chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have haff : ContDiff ℝ 3 (fun x : ℝ³ => (ℓ * d)⁻¹ • x - u) := by fun_prop
  have hsmall : ContDiff ℝ 3 (fun x : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    (Work.BoseFixB1S.win.contDiff_chiSmall 3 M (by omega)).comp haff
  have hprod : ContDiff ℝ 3 (fun x : ℝ³ =>
      chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u)) := hchi.mul hsmall
  have hfun : chiSmallB M ℓ d u
      = fun x : ℝ³ => chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl
  rw [hfun]
  exact hprod

/-! ## The uniform derivative bound -/

/-- **Derivative bound for the first factor.**  The `j`-th iterated derivative of the complexified
`ℓ`-scale corpus window `χ(·/ℓ)` is at most `chiBumpCBound 3 · ‖ℓ⁻¹ • 1‖^j`. -/
lemma norm_iteratedFDeriv_chiScaleC_le (ℓ : ℝ) (j : ℕ) (hj : j ≤ 3) (z : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun x : ℝ³ => (chiScale ℓ x : ℂ)) z‖
      ≤ Work.BoseFixB1S.win.chiBumpCBound 3 * ‖((ℓ⁻¹ : ℝ) • (1 : ℝ³ →L[ℝ] ℝ³))‖ ^ j := by
  set L : ℝ³ →L[ℝ] ℝ³ := (ℓ⁻¹) • (1 : ℝ³ →L[ℝ] ℝ³) with hL
  have hLx : ∀ x : ℝ³, L x = (ℓ⁻¹) • x := by
    intro x
    rw [hL]
    simp
  have hfun : (fun x : ℝ³ => (chiScale ℓ x : ℂ))
      = fun x : ℝ³ => Work.BoseFixB1S.win.chiBumpC (L x) := by
    funext x
    rw [hLx x]
    rfl
  rw [hfun]
  have hstep : iteratedFDeriv ℝ j (fun x : ℝ³ => Work.BoseFixB1S.win.chiBumpC (L x)) z
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

/-- **Derivative bound for the second factor.**  The `j`-th iterated derivative of
`χ_M((c • ·) − u)` (complexified) is at most `chiSmallCBound 3 M · ‖c • 1‖^j`, uniformly in the
shift `u`: the translation `− u` is invisible for the iterated derivative
(`iteratedFDeriv_comp_sub`). -/
lemma norm_iteratedFDeriv_chiSmallC_sub_le {M : ℕ} (hM : 4 ≤ M) (j : ℕ) (hj : j ≤ 3)
    (c : ℝ) (u z : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun x : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (c • x - u)) z‖
      ≤ Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega)
          * ‖(c • (1 : ℝ³ →L[ℝ] ℝ³))‖ ^ j := by
  set L : ℝ³ →L[ℝ] ℝ³ := c • (1 : ℝ³ →L[ℝ] ℝ³) with hL
  have hLx : ∀ x : ℝ³, L x = c • x := by
    intro x
    rw [hL]
    simp
  have htrans : ContDiff ℝ 3 (fun y : ℝ³ => y - u) := by fun_prop
  have hg : ContDiff ℝ 3 (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u)) :=
    (Work.BoseFixB1S.win.contDiff_chiSmallC 3 M (by omega)).comp htrans
  have hfun : (fun x : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (c • x - u))
      = fun x : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (L x - u) := by
    funext x
    rw [hLx x]
  rw [hfun]
  have hstep : iteratedFDeriv ℝ j
        (fun x : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (L x - u)) z
      = (iteratedFDeriv ℝ j
          (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)).compContinuousLinearMap
          (fun _ : Fin j => L) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hg z (i := j)
      (hi := by exact_mod_cast hj)
  rw [hstep]
  have hprod : ∏ _ : Fin j, ‖L‖ = ‖L‖ ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : iteratedFDeriv ℝ j
        (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)
      = iteratedFDeriv ℝ j (Work.BoseFixB1S.win.chiSmallC M) (L z - u) :=
    iteratedFDeriv_comp_sub (f := Work.BoseFixB1S.win.chiSmallC M) j u (L z)
  calc
    ‖(iteratedFDeriv ℝ j (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u))
        (L z)).compContinuousLinearMap (fun _ : Fin j => L)‖
        ≤ ‖iteratedFDeriv ℝ j (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)‖
            * ∏ _ : Fin j, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j (fun y : ℝ³ => Work.BoseFixB1S.win.chiSmallC M (y - u)) (L z)‖
            * ‖L‖ ^ j := by
          rw [hprod]
    _ ≤ Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) * ‖L‖ ^ j := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hsub]
          exact Work.BoseFixB1S.win.norm_iteratedFDeriv_chiSmallC_le 3 M (by omega) j hj (L z - u)

/-- The explicit uniform bound on the iterated derivatives of the complexified cutoff: the product
rule applied to the two factors, with the constants frozen at order `3`.  Only the values at
`k ≤ 3` are meaningful; for `k > 3` the function is set to `0`. -/
noncomputable def chiSmallBWinG (M : ℕ) (hM : 4 ≤ M) (ℓ d : ℝ) (k : ℕ) : ℝ :=
  if k ≤ 3 then
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) *
        (Work.BoseFixB1S.win.chiBumpCBound 3 * ‖((ℓ⁻¹ : ℝ) • (1 : ℝ³ →L[ℝ] ℝ³))‖ ^ i) *
        (Work.BoseFixB1S.win.chiSmallCBound 3 M (by omega) *
          ‖(((ℓ * d)⁻¹ : ℝ) • (1 : ℝ³ →L[ℝ] ℝ³))‖ ^ (k - i))
  else 0

lemma chiSmallBWinG_nonneg (M : ℕ) (hM : 4 ≤ M) (ℓ d : ℝ) (k : ℕ) :
    0 ≤ chiSmallBWinG M hM ℓ d k := by
  rw [chiSmallBWinG]
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

/-- **The quantitative derivative bound** for the complexified cutoff, uniform in the shift `u`:
for every `k ≤ 3` the `k`-th iterated derivative is bounded by `chiSmallBWinG`. -/
lemma chiSmallB_complex_iteratedFDeriv_le {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ³) (k : ℕ) (hk : k ≤ 3) (z : ℝ³) :
    ‖iteratedFDeriv ℝ k (fun x : ℝ³ => (chiSmallB M ℓ d u x : ℂ)) z‖
      ≤ chiSmallBWinG M hM ℓ d k := by
  have hprod : (fun x : ℝ³ => (chiSmallB M ℓ d u x : ℂ))
      = fun x : ℝ³ =>
          (chiScale ℓ x : ℂ) * (chiSmall M ((ℓ * d)⁻¹ • x - u) : ℂ) := by
    funext x
    simp only [chiSmallB, Complex.ofReal_mul]
  rw [hprod]
  have hA0 : ContDiff ℝ 3 (chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hA : ContDiff ℝ 3 (fun x : ℝ³ => (chiScale ℓ x : ℂ)) := by
    have hclm := hA0.continuousLinearMap_comp Complex.ofRealCLM
    simpa [Function.comp_def] using hclm
  have hB : ContDiff ℝ 3
      (fun x : ℝ³ => (chiSmall M ((ℓ * d)⁻¹ • x - u) : ℂ)) :=
    (Work.BoseFixB1S.win.contDiff_chiSmallC 3 M (by omega)).comp (by fun_prop)
  rw [chiSmallBWinG, if_pos hk]
  refine (norm_iteratedFDeriv_mul_le hA hB z (n := k) (hn := by exact_mod_cast hk)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi3 : i ≤ 3 := by omega
  have hki3 : k - i ≤ 3 := by omega
  have h1 := norm_iteratedFDeriv_chiScaleC_le ℓ i hi3 z
  have h2 := norm_iteratedFDeriv_chiSmallC_sub_le hM (k - i) hki3 ((ℓ * d)⁻¹) u z
  have hc : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
  have hL1 : (0 : ℝ) ≤ ‖((ℓ⁻¹ : ℝ) • (1 : ℝ³ →L[ℝ] ℝ³))‖ ^ i := by positivity
  have hb1 : (0 : ℝ) ≤ Work.BoseFixB1S.win.chiBumpCBound 3 :=
    Work.BoseFixB1S.win.chiBumpCBound_nonneg 3
  refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _) ?_
  exact mul_nonneg hc (mul_nonneg hb1 hL1)

theorem chiSmallB_windowData {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∀ u : EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ 3 (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u x)) ∧
    ∃ (R : ℝ) (G : ℕ → ℝ), 0 < R ∧ (∀ k : ℕ, 0 ≤ G k) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3),
        tsupport (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u x)
          ⊆ Metric.closedBall 0 R) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3), ∀ k : ℕ, k ≤ 3 →
        ∀ z : EuclideanSpace ℝ (Fin 3),
          ‖iteratedFDeriv ℝ k
            (fun x : EuclideanSpace ℝ (Fin 3) =>
              (Submission.BoseGases.chiSmallB M ℓ d u x : ℂ)) z‖ ≤ G k) := by
  refine ⟨fun u => chiSmallB_contDiff_three hM hℓ u, ℓ / 2, chiSmallBWinG M hM ℓ d,
    by positivity, ?_, ?_, ?_⟩
  · exact chiSmallBWinG_nonneg M hM ℓ d
  · -- support containment, uniformly in `u`: only the ball factor `χ(·/ℓ)` matters
    intro u
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    rw [Function.mem_support] at hx
    have h1 : chiScale ℓ x ≠ 0 := by
      intro h
      exact hx (by simp [chiSmallB, h])
    have h2 : chi ((ℓ⁻¹) • x) ≠ 0 := by simpa [chiScale] using h1
    have h3 : ‖(ℓ⁻¹) • x‖ < 1 / 2 := by
      by_contra hcon
      exact h2 (chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hnorm : ‖(ℓ⁻¹) • x‖ = ℓ⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    rw [hnorm] at h3
    have h4 : ‖x‖ < ℓ * (1 / 2) := (inv_mul_lt_iff₀ hℓ).mp h3
    linarith
  · intro u k hk z
    exact chiSmallB_complex_iteratedFDeriv_le hM hℓ u k hk z

end Work.BoseFixB1B
