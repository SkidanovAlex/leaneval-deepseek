import Mathlib
import Submission.Work.LandLeaves.gronwallDefs
import Submission.Work.LandLeaves.koebeDerivAux.psiDefs
import Submission.Work.LandLeaves.gronwallSummable
import Submission.Work.LandLeaves.gronwallSummableBco

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Weighted Laurent-coefficient summability under a localized exterior bound

The hypothesis of the exterior area theorem is normally that `ψ` is holomorphic on the exterior
`1 < ‖w‖` of the unit disc and satisfies a *global* bound `‖ψ w - w‖ ≤ C` there.  The statements in
this directory (`psiLevelW`, `psiAnnulusAreaW`, `psiCoeffSummableW`) only assume the bound on the
outer region `‖w‖ ≥ W` for some `W > 1`.

The point of the present file is that this weaker hypothesis is still enough to make the whole
coefficient series converge.  The reason is that `ζ ↦ ψ ζ⁻¹ - ζ⁻¹` is holomorphic on
`0 < ‖ζ‖ < 1` and bounded by `C` on `0 < ‖ζ‖ ≤ 1/W`, so `0` is a removable singularity: the
function `Fext ψ` is holomorphic on the *whole* unit disc, not only on `ball 0 (1/W)`.  Cauchy's
estimate applied on a circle of radius `ρ` with `1/R < ρ < 1` then gives the geometric decay of the
coefficients needed for summability.

* `differentiableOn_Fext_of_weakBound` is the localized removable-singularity step;
* `bco_summable_of_differentiableOn` carries out the Cauchy-estimate/comparison argument for any
  `ψ` whose extension `Fext ψ` is holomorphic on the unit disc;
* `psiCoeffSummableW` is the requested statement.
-/

open Complex Metric Set Filter
open scoped Topology

namespace Work.LandLeaves.koebeDerivAux

/-- **Localized removable singularity.**  If the exterior bound `‖ψ w - w‖ ≤ C` holds only for
`‖w‖ ≥ W` (with `1 < W`), the function `Fext ψ = ψ ζ⁻¹ - ζ⁻¹` (extended to `0`) is nevertheless
holomorphic on the whole unit disc.

Indeed, `regPart ψ` is differentiable on `{ζ | 0 < ‖ζ‖ < 1}` (where `‖ζ⁻¹‖ > 1`, so `hd` applies)
and bounded by `C` on `{ζ | 0 < ‖ζ‖ ≤ W⁻¹}` (where `‖ζ⁻¹‖ ≥ W`); Riemann's removable singularity
theorem therefore makes it differentiable on `ball 0 W⁻¹`, and on the remaining part
`{ζ | 0 < ‖ζ‖ < 1}` it agrees with `ψ ζ⁻¹ - ζ⁻¹`. -/
lemma differentiableOn_Fext_of_weakBound (ψ : ℂ → ℂ) (W C : ℝ) (hW : 1 < W)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, W ≤ ‖w‖ → ‖ψ w - w‖ ≤ C) :
    DifferentiableOn ℂ (Fext ψ) (ball 0 1) := by
  have hW0 : (0 : ℝ) < W := lt_trans zero_lt_one hW
  have hWinv0 : (0 : ℝ) < W⁻¹ := inv_pos.mpr hW0
  have hWinv1 : W⁻¹ < 1 := inv_lt_one_of_one_lt₀ hW
  -- identify the punctured small ball with a set where `‖ζ‖` is directly controlled
  have hsetW : ball (0 : ℂ) W⁻¹ \ {0} = {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < W⁻¹} := by
    ext ζ
    simp only [Set.mem_sdiff, mem_ball, dist_zero_right, Set.mem_singleton_iff, Set.mem_setOf_eq,
      norm_pos_iff]
    tauto
  -- differentiability of `regPart ψ` on the punctured small ball
  have hdiff1 : DifferentiableOn ℂ (regPart ψ) (ball 0 W⁻¹ \ {0}) := by
    rw [hsetW]
    refine DifferentiableOn.congr ?_ (fun ζ hζ => by rw [regPart, if_neg (norm_pos_iff.mp hζ.1)])
    intro ζ hζ
    obtain ⟨hζ0, hζ1⟩ := hζ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hinv : 1 < ‖ζ⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hζne)]
      exact lt_trans hζ1 hWinv1
    have h1 : DifferentiableAt ℂ ψ ζ⁻¹ := hd.differentiableAt ((isOpen_lt_norm 1).mem_nhds hinv)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => ζ⁻¹) ζ := differentiableAt_inv hζne
    exact ((h1.comp ζ h2).sub h2).differentiableWithinAt
  -- boundedness of `regPart ψ` on the punctured small ball
  have hbdd1 : BddAbove (norm ∘ regPart ψ '' (ball 0 W⁻¹ \ {0})) := by
    rw [hsetW, bddAbove_def]
    refine ⟨C, ?_⟩
    rintro y ⟨ζ, hζ, rfl⟩
    simp only [Function.comp_apply]
    obtain ⟨hζ0, hζ1⟩ := hζ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    rw [regPart, if_neg hζne]
    refine hb ζ⁻¹ ?_
    rw [norm_inv, le_inv_comm₀ hW0 hζ0]
    exact hζ1.le
  have hFext_small : DifferentiableOn ℂ (Fext ψ) (ball 0 W⁻¹) := by
    rw [Fext]
    exact differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hWinv0) hdiff1 hbdd1
  -- differentiability at the non-zero points of the unit disc
  have hset1 : ball (0 : ℂ) 1 \ {0} = {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < 1} := by
    ext ζ
    simp only [Set.mem_sdiff, mem_ball, dist_zero_right, Set.mem_singleton_iff, Set.mem_setOf_eq,
      norm_pos_iff]
    tauto
  have hFext_big : DifferentiableOn ℂ (Fext ψ) (ball 0 1 \ {0}) := by
    rw [hset1]
    refine DifferentiableOn.congr ?_ (fun ζ hζ => by rw [Fext_eq ψ (norm_pos_iff.mp hζ.1)])
    intro ζ hζ
    obtain ⟨hζ0, hζ1⟩ := hζ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hinv : 1 < ‖ζ⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hζne)]
      exact hζ1
    have h1 : DifferentiableAt ℂ ψ ζ⁻¹ := hd.differentiableAt ((isOpen_lt_norm 1).mem_nhds hinv)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => ζ⁻¹) ζ := differentiableAt_inv hζne
    exact ((h1.comp ζ h2).sub h2).differentiableWithinAt
  -- glue the two pieces
  have hunion : ball (0 : ℂ) 1
      = ball 0 W⁻¹ ∪ {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < 1} := by
    ext ζ
    simp only [mem_ball, dist_zero_right, Set.mem_union, Set.mem_setOf_eq, norm_pos_iff]
    constructor
    · intro h
      by_cases h' : ‖ζ‖ < W⁻¹
      · exact Or.inl h'
      · exact Or.inr ⟨norm_pos_iff.mp (lt_of_lt_of_le hWinv0 (le_of_not_gt h')), h⟩
    · rintro (h | ⟨-, h1⟩)
      · exact lt_trans h hWinv1
      · exact h1
  rw [hunion, ← hset1]
  exact hFext_small.union_of_isOpen hFext_big Metric.isOpen_ball
    (Metric.isOpen_ball.sdiff isClosed_singleton)

/-- **Summability from holomorphy of `Fext`.**  If the extension `Fext ψ` of `ζ ↦ ψ ζ⁻¹ - ζ⁻¹` is
holomorphic on the unit disc, then the weighted coefficient series converges at every radius
`r > 1`.  Cauchy's estimate on a circle of radius `ρ` with `r⁻¹ < ρ < 1` gives
`‖bco ψ n‖ ≤ M ρ⁻ⁿ`, hence `n ‖bco ψ n‖² r^{-2n} ≤ M² n (ρ⁻² r⁻²)ⁿ` with `ρ⁻² r⁻² < 1`. -/
theorem bco_summable_of_differentiableOn (ψ : ℂ → ℂ)
    (hFd : DifferentiableOn ℂ (Fext ψ) (Metric.ball 0 1)) (r : ℝ) (hr : 1 < r) :
    Summable (fun n : ℕ => (n : ℝ) * ‖bco ψ n‖ ^ 2 * (r ^ (2 * n))⁻¹) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrinv0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hrinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  -- choose `ρ` with `r⁻¹ < ρ < 1`
  set ρ : ℝ := (r⁻¹ + 1) / 2 with hρdef
  have hρgt : r⁻¹ < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hrinv0 hρgt
  -- a bound for `Fext ψ` on the circle of radius `ρ`, by compactness
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖Fext ψ z‖ ≤ M := by
    refine (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn ?_
    refine hFd.continuousOn.mono ?_
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right, hz]
    exact hρlt
  -- Cauchy's estimate
  have hbco : ∀ n : ℕ, ‖bco ψ n‖ ≤ M * (ρ⁻¹) ^ n := by
    intro n
    have h := norm_gco_le (Fext ψ) hFd hρ0 hρlt hM n
    rw [div_eq_mul_inv, ← inv_pow] at h
    rwa [bco_eq_gco ψ n]
  have hsq : ∀ n : ℕ, ‖bco ψ n‖ ^ 2 ≤ M ^ 2 * (ρ⁻¹ ^ 2) ^ n := by
    intro n
    calc ‖bco ψ n‖ ^ 2 ≤ (M * (ρ⁻¹) ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbco n) 2
      _ = M ^ 2 * (ρ⁻¹ ^ 2) ^ n := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  -- the geometric ratio `t = ρ⁻² r⁻² < 1`
  set t : ℝ := ρ⁻¹ ^ 2 * (r⁻¹) ^ 2 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hρr : 1 < ρ * r := by
    have h := mul_lt_mul_of_pos_right hρgt hr0
    rwa [inv_mul_cancel₀ (ne_of_gt hr0)] at h
  have ht1 : t < 1 := by
    have he : t = ((ρ * r)⁻¹) ^ 2 := by rw [htdef, mul_inv, mul_pow]
    rw [he]
    exact pow_lt_one₀ (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hρr)))
      (inv_lt_one_of_one_lt₀ hρr) (by norm_num)
  -- summability of `n ↦ (n : ℝ) * t^n`
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * t ^ n) := by
    have hbase := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := t)
      (by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1)
    refine hbase.congr (fun n => ?_)
    rw [pow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ht0 n))]
  -- the termwise comparison
  have hterm : ∀ n : ℕ,
      (n : ℝ) * ‖bco ψ n‖ ^ 2 * (r ^ (2 * n))⁻¹ ≤ M ^ 2 * ((n : ℝ) * t ^ n) := by
    intro n
    have hv : (r ^ (2 * n))⁻¹ = ((r⁻¹) ^ 2) ^ n := by rw [← inv_pow, ← pow_mul]
    have hX0 : 0 ≤ ((r⁻¹) ^ 2) ^ n := pow_nonneg (pow_nonneg hrinv0 2) n
    rw [hv, htdef]
    calc (n : ℝ) * ‖bco ψ n‖ ^ 2 * ((r⁻¹) ^ 2) ^ n
        ≤ (n : ℝ) * (M ^ 2 * (ρ⁻¹ ^ 2) ^ n) * ((r⁻¹) ^ 2) ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsq n) (Nat.cast_nonneg n)) hX0
      _ = M ^ 2 * ((n : ℝ) * (ρ⁻¹ ^ 2 * (r⁻¹) ^ 2) ^ n) := by rw [mul_pow]; ring
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => M ^ 2 * ((n : ℝ) * t ^ n)) ?_ hterm ?_
  · intro n
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
      (inv_nonneg.mpr (pow_pos hr0 _).le)
  · exact hgeo.mul_left (M ^ 2)

/-- The weighted coefficient series converges at every radius `R > 1`, under the weaker hypothesis that the exterior bound holds only for `‖w‖ ≥ W`.

Reason: `regPart ψ ζ = ψ ζ⁻¹ - ζ⁻¹` is holomorphic on `0 < ‖ζ‖ < 1` and bounded by `C` on `0 < ‖ζ‖ ≤ 1/W`, so `0` is a removable singularity and `Fext ψ` is holomorphic on the whole unit disc with Taylor coefficients `bco ψ n`; hence `limsup ‖bco ψ n‖^{1/n} ≤ 1`, and for every `ε > 0` there is `K` with `‖bco ψ n‖ ≤ K (1+ε)^n`, so `n‖bco ψ n‖² R^{-2n}` decays geometrically once `(1+ε)² < R²`. (The workspace's `gronwallSummableBco` proves the corresponding statement under the global bound; the removable-singularity step has to be localized to `ball 0 (1/W)`.) -/
lemma psiCoeffSummableW (ψ : ℂ → ℂ) (W C : ℝ) (hW : 1 < W)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, W ≤ ‖w‖ → ‖ψ w - w‖ ≤ C) :
    ∀ R : ℝ, 1 < R → Summable (fun n : ℕ => psiCoeff ψ n * ((R ^ 2)⁻¹) ^ n) := by
  intro R hR
  have hFd := differentiableOn_Fext_of_weakBound ψ W C hW hd hb
  refine (bco_summable_of_differentiableOn ψ hFd R hR).congr (fun n => ?_)
  simp only [psiCoeff]
  rw [pow_mul, inv_pow]

end Work.LandLeaves.koebeDerivAux
