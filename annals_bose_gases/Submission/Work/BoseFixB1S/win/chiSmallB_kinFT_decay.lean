import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1S.oneBodyB1.fourierDecayHigh
import Submission.Work.OneBodyKin.fourier_convScale_scaling
import Submission.Work.OneBodyKin.kinFT_comp_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.win.chiSmallB_kinFT_decay`

**Scale-sharp Fourier decay of the sliding small-box cosine cutoff `chiSmallB`.**

The cutoff is

    `chiSmallB M ℓ d u x = χ(x/ℓ) · χ_M((ℓd)⁻¹ • x − u)`

(`Submission.BoseGases.chiSmallB`): the `ℓ`-scale factor is the smooth corpus bump `χ(·/ℓ)` and
the `(ℓd)`-scale factor is the cosine-`M`-th-power bump `chiSmall M`, whose support is the unit
cube and which is `C^{M−1}` (`ζ^M` kills the derivative jumps of the cosine profile `ζ` at the box
faces to order `M−1`).

**Target** (the statement of this file): for all `N, M` with `N + 1 ≤ M` there is a constant `C`
with

    `‖kinFT (χ_{B(u)}) p‖ ≤ C (ℓd)³ (1 + (ℓd)‖p‖)^{-N}`

uniformly in `0 < ℓ`, `0 < d ≤ 1`, `u` and `p`.

## The route

1. **`C^{M−1}` of `ζ^M`** (`contDiff_zeta1d_pow`): induction on the order, using
   `contDiff_succ_iff_deriv` and the *global* derivative formula
   `deriv (ζ^M) = −Mπ·sin(π·)·ζ^{M−1}` (`zeta1d_pow_deriv_eq`) — the key point being that the
   smooth factor `sin(π·)` costs no order, so `ζ^{M−1}` only has to be `C^{N}` when `ζ^M` is
   `C^{N+1}`.  This is exactly the hypothesis `N + 1 ≤ M`.
2. **`C^N` of `chiSmall M`** on `ℝ³`: `(ζ₀ζ₁ζ₂)^M = ζ₀^M ζ₁^M ζ₂^M` (`mul_pow`), products and
   compositions of `C^N` maps, then divide by the fixed constant `√chiSmallNormSq M`.
3. **Uniform derivative bounds** `‖D^j (chiSmall M)‖ ≤ B (j ≤ N)` from compactness of the support.
4. **The rescaled profile** `P(w) = χ(d•(w+u))·χ_M(w)`: since `chiSmallB M ℓ d u z = P((ℓd)⁻¹z−u)`,
   the dilation/rescaling identity for `kinFT` (the general lemma
   `kinFT_inv_smul_sub`) turns the estimate into `(ℓd)³ ‖kinFT P ((ℓd)•p)‖`.
5. **Fourier decay of `P`**: `P` is `C^N` with compact support and its support lies in the *fixed*
   ball of radius `1`; the product rule (`norm_iteratedFDeriv_mul_le`) with the dilation-contraction
   bound for the `ℓ`-scale factor gives `L¹` bounds for `D^j P` uniform in `d ∈ (0,1]` and `u`, and
   `norm_fourier_le_of_integral_iteratedFDeriv` converts them into
   `‖kinFT P q‖ ≤ C (1+‖q‖)^{-N}`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff BigOperators

namespace Work.BoseFixB1S.win

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. The one-dimensional regularity of the cosine-`M` bump -/

/-- **The global derivative formula for `ζ^M`** (`M ≥ 2`): the corpus's piecewise formula
`zeta1d_pow_deriv` can be written without the case distinction, because `ζ` itself vanishes
(and `ζ^{M−1} = 0` with it) outside the unit interval. -/
lemma zeta1d_pow_deriv_eq {M : ℕ} (hM : 2 ≤ M) :
    deriv (fun y : ℝ => zeta1d y ^ M)
      = fun y : ℝ => -((M : ℝ) * Real.pi) * Real.sin (Real.pi * y) * zeta1d y ^ (M - 1) := by
  funext y
  rw [zeta1d_pow_deriv hM y]
  by_cases hy : |y| < 1 / 2
  · rw [if_pos hy, zeta1d_of_abs_le hy.le]
    ring
  · rw [if_neg hy]
    have hζ : zeta1d y = 0 := by
      rcases lt_or_eq_of_le (le_of_not_gt hy) with h | h
      · exact zeta1d_of_one_half_lt h
      · have hy' : y = 1 / 2 ∨ y = -(1 / 2) := by
          by_cases hy0 : 0 ≤ y
          · left
            have h1 : |y| = y := abs_of_nonneg hy0
            linarith
          · right
            have h1 : |y| = -y := abs_of_neg (lt_of_not_ge hy0)
            linarith
        rcases hy' with h' | h'
        · rw [h', zeta1d_of_abs_le (by norm_num),
            show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]
        · rw [h', zeta1d_of_abs_le (by norm_num),
            show Real.pi * (-(1 / 2) : ℝ) = -(Real.pi / 2) by ring, Real.cos_neg,
            Real.cos_pi_div_two]
    have hM1 : M - 1 ≠ 0 := by omega
    rw [hζ, zero_pow hM1, mul_zero]

/-- **`ζ^M` is `C^{M−1}` on `ℝ`.**  Induction on the order `N`: with the global derivative formula
`deriv (ζ^M) = −Mπ·sin(π·)·ζ^{M−1}`, one step of `contDiff_succ_iff_deriv` costs exactly one power
of `M` (the smooth factor `sin(π·)` is free). -/
lemma contDiff_zeta1d_pow : ∀ (N M : ℕ), N + 1 ≤ M →
    ContDiff ℝ (N : WithTop ℕ∞) (fun y : ℝ => zeta1d y ^ M) := by
  intro N
  induction N with
  | zero =>
      intro M _
      exact (contDiff_zero (𝕜 := ℝ) (f := fun y : ℝ => zeta1d y ^ M)).mpr
        (zeta1d_continuous.pow M)
  | succ N ih =>
      intro M hM
      have hcast : (((N + 1 : ℕ)) : WithTop ℕ∞) = ((N : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast
        ring
      rw [hcast, contDiff_succ_iff_deriv]
      have h2M : 2 ≤ M := by omega
      refine ⟨zeta1d_pow_differentiable h2M, ?_, ?_⟩
      · intro h
        exact absurd h (WithTop.coe_lt_top ((N : ℕ) : ℕ∞)).ne
      · rw [zeta1d_pow_deriv_eq h2M]
        have hsin : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) (fun y : ℝ => Real.sin (Real.pi * y)) :=
          Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
        have hM1 : N + 1 ≤ M - 1 := by omega
        have hc := ih (M - 1) hM1
        have hconst : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞)
            (fun _ : ℝ => -((M : ℝ) * Real.pi)) := contDiff_const
        exact (hconst.mul hsin).mul hc

/-! ## 2. `chiSmall M` is `C^N` on `ℝ³` for `N + 1 ≤ M` -/

/-- The `j`-th coordinate of `ℝ³` as a continuous linear functional. -/
noncomputable def coordCLM (j : Fin 3) : ℝ³ →L[ℝ] ℝ :=
  { toFun := fun z => z.ofLp j
    map_add' := by intro a b; rfl
    map_smul' := by intro c a; rfl
    cont := by fun_prop }

lemma contDiff_coord_zeta1d_pow (N M : ℕ) (hNM : N + 1 ≤ M) (j : Fin 3) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun z : ℝ³ => zeta1d (z.ofLp j) ^ M) := by
  have h1 := contDiff_zeta1d_pow N M hNM
  have h2 : ContDiff ℝ (N : WithTop ℕ∞) (fun z : ℝ³ => z.ofLp j) :=
    (ContinuousLinearMap.contDiff (coordCLM j) : ContDiff ℝ (N : WithTop ℕ∞) ⇑(coordCLM j))
  simpa [coordCLM, Function.comp_def] using h1.comp h2

/-- **`chiSmallBase M` is `C^N`** (`N + 1 ≤ M`), via `(ζ₀ζ₁ζ₂)^M = ζ₀^M ζ₁^M ζ₂^M`. -/
lemma contDiff_chiSmallBase (N M : ℕ) (hNM : N + 1 ≤ M) :
    ContDiff ℝ (N : WithTop ℕ∞) (chiSmallBase M) := by
  have hfac : ∀ j : Fin 3, ContDiff ℝ (N : WithTop ℕ∞)
      (fun z : ℝ³ => zeta1d (z.ofLp j) ^ M) := fun j => contDiff_coord_zeta1d_pow N M hNM j
  have hprod : ContDiff ℝ (N : WithTop ℕ∞) (fun z : ℝ³ =>
      zeta1d (z.ofLp 0) ^ M * zeta1d (z.ofLp 1) ^ M * zeta1d (z.ofLp 2) ^ M) :=
    ((hfac 0).mul (hfac 1)).mul (hfac 2)
  have heq : chiSmallBase M = fun z : ℝ³ =>
      zeta1d (z.ofLp 0) ^ M * zeta1d (z.ofLp 1) ^ M * zeta1d (z.ofLp 2) ^ M := by
    funext z
    dsimp [chiSmallBase]
    rw [mul_pow, mul_pow]
  rwa [heq]

/-- **`chiSmall M` is `C^N`** (`N + 1 ≤ M`). -/
lemma contDiff_chiSmall (N M : ℕ) (hNM : N + 1 ≤ M) :
    ContDiff ℝ (N : WithTop ℕ∞) (chiSmall M) := by
  have hbase := contDiff_chiSmallBase N M hNM
  have hconst : ContDiff ℝ (N : WithTop ℕ∞)
      (fun _ : ℝ³ => (Real.sqrt (chiSmallNormSq M))⁻¹) := contDiff_const
  have heq : chiSmall M = fun z : ℝ³ => chiSmallBase M z * (Real.sqrt (chiSmallNormSq M))⁻¹ := by
    funext z
    dsimp [chiSmall]
    rw [div_eq_mul_inv]
  rw [heq]
  exact hbase.mul hconst

/-- The complexified bump `χ_M`. -/
noncomputable def chiSmallC (M : ℕ) : ℝ³ → ℂ := fun z => (chiSmall M z : ℂ)

lemma contDiff_chiSmallC (N M : ℕ) (hNM : N + 1 ≤ M) :
    ContDiff ℝ (N : WithTop ℕ∞) (chiSmallC M) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_chiSmall N M hNM)

/-- The corpus bump `χ` as a `ℂ`-valued function. -/
noncomputable def chiBumpC : ℝ³ → ℂ := fun z => (chi z : ℂ)

lemma chiBumpC_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chiBumpC :=
  Complex.ofRealCLM.contDiff.comp chi_contDiff

lemma chiBumpC_hasCompactSupport : HasCompactSupport chiBumpC :=
  chi_hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

/-! ## 3. Uniform derivative bounds (from compactness of the support) -/

/-- **A `C^N` function with compact support has uniformly bounded iterated derivatives up to
order `N`** (each derivative is continuous and compactly supported, hence bounded; the finite sum
over `j ≤ N` makes a single constant). -/
lemma exists_bound_iteratedFDeriv (N : ℕ) {f : ℝ³ → ℂ}
    (hf : ContDiff ℝ (N : WithTop ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, j ≤ N → ∀ x : ℝ³, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hsingle : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (j ≤ N → ∀ x : ℝ³, ‖iteratedFDeriv ℝ j f x‖ ≤ B) := by
    intro j
    by_cases hj : j ≤ N
    · have hcont : Continuous (fun x : ℝ³ => iteratedFDeriv ℝ j f x) :=
        hf.continuous_iteratedFDeriv (by exact_mod_cast hj)
      obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuousOn hcont.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun _ x => ?_⟩
      by_cases hx : x ∈ tsupport f
      · exact le_trans (hC x hx) (le_max_left _ _)
      · have h0 : iteratedFDeriv ℝ j f x = 0 := by
          by_contra h
          exact hx (support_iteratedFDeriv_subset (𝕜 := ℝ) j (Function.mem_support.mpr h))
        rw [h0, norm_zero]
        exact le_max_right _ _
    · exact ⟨0, le_refl 0, fun h => absurd h hj⟩
  choose b hb0 hb using hsingle
  refine ⟨∑ j ∈ Finset.range (N + 1), max 0 (b j), ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => le_max_left 0 (b j)
  · intro j hj x
    have hmem : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have h1 : max 0 (b j) ≤ ∑ i ∈ Finset.range (N + 1), max 0 (b i) :=
      Finset.single_le_sum (fun i _ => le_max_left 0 (b i)) hmem
    exact le_trans (le_trans (hb j hj x) (le_max_right 0 (b j))) h1

lemma exists_bound_iteratedFDeriv_chiBumpC (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, j ≤ N → ∀ x : ℝ³, ‖iteratedFDeriv ℝ j chiBumpC x‖ ≤ B :=
  exists_bound_iteratedFDeriv N (chiBumpC_contDiff.of_le (by exact_mod_cast le_top : _))
    chiBumpC_hasCompactSupport

/-- A bound for `‖D^j χ‖` for all `j ≤ N`. -/
noncomputable def chiBumpCBound (N : ℕ) : ℝ :=
  Classical.choose (exists_bound_iteratedFDeriv_chiBumpC N)

lemma chiBumpCBound_nonneg (N : ℕ) : 0 ≤ chiBumpCBound N :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_chiBumpC N)).1

lemma norm_iteratedFDeriv_chiBumpC_le (N j : ℕ) (hj : j ≤ N) (x : ℝ³) :
    ‖iteratedFDeriv ℝ j chiBumpC x‖ ≤ chiBumpCBound N :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_chiBumpC N)).2 j hj x

/-- The complexified bump `χ_M` is compactly supported (`M ≥ 1`). -/
lemma chiSmallC_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) : HasCompactSupport (chiSmallC M) :=
  (chiSmall_hasCompactSupport hM).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

lemma exists_bound_iteratedFDeriv_chiSmallC (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, j ≤ N → ∀ x : ℝ³, ‖iteratedFDeriv ℝ j (chiSmallC M) x‖ ≤ B :=
  exists_bound_iteratedFDeriv N (contDiff_chiSmallC N M hNM)
    (chiSmallC_hasCompactSupport (by omega))

/-- A bound for `‖D^j χ_M‖` for all `j ≤ N` (`N + 1 ≤ M`). -/
noncomputable def chiSmallCBound (N M : ℕ) (hNM : N + 1 ≤ M) : ℝ :=
  Classical.choose (exists_bound_iteratedFDeriv_chiSmallC N M hNM)

lemma chiSmallCBound_nonneg (N M : ℕ) (hNM : N + 1 ≤ M) : 0 ≤ chiSmallCBound N M hNM :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_chiSmallC N M hNM)).1

lemma norm_iteratedFDeriv_chiSmallC_le (N M : ℕ) (hNM : N + 1 ≤ M) (j : ℕ) (hj : j ≤ N)
    (x : ℝ³) :
    ‖iteratedFDeriv ℝ j (chiSmallC M) x‖ ≤ chiSmallCBound N M hNM :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_chiSmallC N M hNM)).2 j hj x

/-- The dilation `d • ·` of `ℝ³` has operator norm `≤ 1` for `|d| ≤ 1`. -/
lemma norm_smul_id_le (d : ℝ) (hd : |d| ≤ 1) :
    ‖(d • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³)‖ ≤ 1 := by
  have hcalc : ∀ x : ℝ³,
      ‖(d • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³) x‖ ≤ 1 * ‖x‖ := by
    intro x
    have h1 : ‖(d • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³) x‖ = |d| * ‖x‖ := by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Real.norm_eq_abs]
    rw [h1, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg x) hd
  exact ContinuousLinearMap.opNorm_le_bound (d • ContinuousLinearMap.id ℝ ℝ³) (by norm_num) hcalc

/-- **Dilation contraction for the corpus bump**: for `|d| ≤ 1`, the `j`-th derivative of the
dilated and shifted bump `w ↦ χ(d•(w+u))` is bounded by the fixed constant `chiBumpCBound N`,
uniformly in the shift `u`. -/
lemma norm_iteratedFDeriv_chiBumpC_dilated_le (N j : ℕ) (hj : j ≤ N) (d : ℝ) (hd : |d| ≤ 1)
    (u x : ℝ³) :
    ‖iteratedFDeriv ℝ j (fun w : ℝ³ => chiBumpC (d • (w + u))) x‖ ≤ chiBumpCBound N := by
  have hstep : iteratedFDeriv ℝ j (fun w : ℝ³ => chiBumpC (d • (w + u))) x
      = iteratedFDeriv ℝ j (fun w : ℝ³ => chiBumpC (d • w)) (x + u) :=
    iteratedFDeriv_comp_add_right (f := fun w : ℝ³ => chiBumpC (d • w)) j u x
  rw [hstep]
  have hstep2 : iteratedFDeriv ℝ j (fun w : ℝ³ => chiBumpC (d • w)) (x + u)
      = (iteratedFDeriv ℝ j chiBumpC
          ((d • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³) (x + u))).compContinuousLinearMap
          (fun _ : Fin j => (d • ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →L[ℝ] ℝ³)) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ)
      (d • ContinuousLinearMap.id ℝ ℝ³) chiBumpC_contDiff (x + u) (i := j)
      (hi := by exact_mod_cast le_top)
  rw [hstep2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine (mul_le_mul (norm_iteratedFDeriv_chiBumpC_le N j hj _)
    (pow_le_one₀ (norm_nonneg _) (norm_smul_id_le d hd)) (by positivity)
    (chiBumpCBound_nonneg N)).trans ?_
  rw [mul_one]

/-! ## 4. The rescaled profile `P(w) = χ(d•(w+u))·χ_M(w)` -/

/-- The rescaled profile of `chiSmallB M ℓ d u`: with `c = ℓd`,
`chiSmallB M ℓ d u z = profileC M d u (c⁻¹ • z − u)`. -/
noncomputable def profileC (M : ℕ) (d : ℝ) (u : ℝ³) : ℝ³ → ℂ :=
  fun w => chiBumpC (d • (w + u)) * chiSmallC M w

lemma hasCompactSupport_profileC {M : ℕ} (hM : 1 ≤ M) (d : ℝ) (u : ℝ³) :
    HasCompactSupport (profileC M d u) := by
  refine (chiSmallC_hasCompactSupport hM).mono ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro h
  exact hw (by simp [profileC, h])

/-- the support of `χ_M` (and hence of the profile) is contained in the unit ball. -/
lemma chiSmall_support_norm_le {M : ℕ} (hM : 1 ≤ M) {z : ℝ³} (hz : chiSmall M z ≠ 0) :
    ‖z‖ ≤ 1 := by
  have hcoord : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j => chiSmall_support_mem_abs_le hM hz j
  have hsq : ‖z‖ ^ 2 = ∑ j : Fin 3, |z.ofLp j| ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) z)
  have hsum : (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ 3 * (1 / 2) ^ 2 := by
    calc (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, (1 / 2) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
      _ = 3 * (1 / 2) ^ 2 := by simp
  have hsq1 : ‖z‖ ^ 2 ≤ 1 := by
    rw [hsq]
    have hc : 3 * (1 / 2) ^ 2 ≤ 1 := by norm_num
    linarith
  have hx0 : 0 ≤ ‖z‖ := norm_nonneg z
  have habs : |‖z‖| ≤ |(1 : ℝ)| := sq_le_sq.mp (by simpa using hsq1)
  simpa [abs_of_nonneg hx0] using habs

lemma profileC_support_le_one {M : ℕ} (hM : 1 ≤ M) (d : ℝ) (u w : ℝ³)
    (hw : profileC M d u w ≠ 0) : ‖w‖ ≤ 1 := by
  have h2 : chiSmallC M w ≠ 0 := by
    intro h
    exact hw (by simp [profileC, h])
  have h3 : chiSmall M w ≠ 0 := by
    intro h
    exact h2 (by simp [chiSmallC, h])
  exact chiSmall_support_norm_le hM h3

lemma contDiff_profileC (N M : ℕ) (hNM : N + 1 ≤ M) (d : ℝ) (u : ℝ³) :
    ContDiff ℝ (N : WithTop ℕ∞) (profileC M d u) := by
  have hclm : ContDiff ℝ (N : WithTop ℕ∞) (fun w : ℝ³ => d • w) :=
    ContinuousLinearMap.contDiff (d • ContinuousLinearMap.id ℝ ℝ³)
  have haff : ContDiff ℝ (N : WithTop ℕ∞) (fun w : ℝ³ => d • (w + u)) := by
    have h := hclm.add (contDiff_const (c := d • u) : ContDiff ℝ (N : WithTop ℕ∞)
      (fun _ : ℝ³ => d • u))
    simpa [smul_add] using h
  have h1 : ContDiff ℝ (N : WithTop ℕ∞) (fun w : ℝ³ => chiBumpC (d • (w + u))) :=
    (chiBumpC_contDiff.of_le (by exact_mod_cast le_top : _)).comp haff
  have h2 : ContDiff ℝ (N : WithTop ℕ∞) (chiSmallC M) := contDiff_chiSmallC N M hNM
  exact h1.mul h2

/-- the derivative bound of the profile, as a constant (`N`-th order, uniform in `d ∈ (0,1]` and
in the shift `u`). -/
noncomputable def profileBound (N M : ℕ) (hNM : N + 1 ≤ M) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * chiBumpCBound N * chiSmallCBound N M hNM

lemma profileBound_nonneg (N M : ℕ) (hNM : N + 1 ≤ M) (j : ℕ) :
    0 ≤ profileBound N M hNM j := by
  unfold profileBound
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (mul_nonneg (by positivity) (chiBumpCBound_nonneg N))
    (chiSmallCBound_nonneg N M hNM)

/-- **The `j`-th derivative of the profile is bounded by `profileBound N M hNM j`**, uniformly in
`d ∈ (0,1]` and `u`. -/
lemma norm_iteratedFDeriv_profileC_le (N M : ℕ) (hNM : N + 1 ≤ M) (d : ℝ) (hd : |d| ≤ 1)
    (u : ℝ³) (j : ℕ) (hj : j ≤ N) (x : ℝ³) :
    ‖iteratedFDeriv ℝ j (profileC M d u) x‖ ≤ profileBound N M hNM j := by
  have hclm : ContDiff ℝ (j : WithTop ℕ∞) (fun w : ℝ³ => d • w) :=
    ContinuousLinearMap.contDiff (d • ContinuousLinearMap.id ℝ ℝ³)
  have haff : ContDiff ℝ (j : WithTop ℕ∞) (fun w : ℝ³ => d • (w + u)) := by
    have h := hclm.add (contDiff_const (c := d • u) : ContDiff ℝ (j : WithTop ℕ∞)
      (fun _ : ℝ³ => d • u))
    simpa [smul_add] using h
  have h1 : ContDiff ℝ (j : WithTop ℕ∞) (fun w : ℝ³ => chiBumpC (d • (w + u))) :=
    (chiBumpC_contDiff.of_le (by exact_mod_cast le_top : _)).comp haff
  have h2 : ContDiff ℝ (j : WithTop ℕ∞) (chiSmallC M) :=
    (contDiff_chiSmallC N M hNM).of_le (by exact_mod_cast hj)
  unfold profileBound
  refine (norm_iteratedFDeriv_mul_le h1 h2 x (hn := le_rfl)).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hiN : i ≤ N := by
    have := Finset.mem_range.mp hi
    omega
  have hjN : j - i ≤ N := by omega
  have hbc := norm_iteratedFDeriv_chiBumpC_dilated_le N i hiN d hd u x
  have hbs := norm_iteratedFDeriv_chiSmallC_le N M hNM (j - i) hjN x
  have hc0 : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left hbc hc0) hbs (norm_nonneg _)
    (mul_nonneg hc0 (chiBumpCBound_nonneg N))

/-! ## 5. `L¹` bounds for the profile and its `N`-th derivative -/

/-- **Support-volume bound.**  If `f` is supported in the closed ball of radius `R` and is
bounded by `B` there, then `∫ ‖f‖ ≤ B · vol(closedBall 0 R)`. -/
private lemma integral_norm_le_of_support_closedBall {F : Type*} [NormedAddCommGroup F]
    (f : ℝ³ → F) (R B : ℝ)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) (hb : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∫ z, ‖f z‖ ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := by
  have hzero : ∀ z ∉ Metric.closedBall (0 : ℝ³) R, ‖f z‖ = 0 := by
    intro z hz
    have hz' : ¬ ‖z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    have hfz : f z = 0 := by
      by_contra h
      exact hz' (hsupp z h)
    rw [hfz, norm_zero]
  have hfin : volume (Metric.closedBall (0 : ℝ³) R) < ⊤ :=
    (isCompact_closedBall (0 : ℝ³) R).measure_lt_top
  have h1 : ‖∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖‖
      ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := by
    refine norm_setIntegral_le_of_norm_le_const hfin (fun z hz => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hb z (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz)
  have hnn : 0 ≤ ∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  calc ∫ z, ‖f z‖ = ∫ z in Metric.closedBall (0 : ℝ³) R, ‖f z‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ B * volume.real (Metric.closedBall (0 : ℝ³) R) := h1

/-- the two `L¹` bounds of the profile, as one constant. -/
noncomputable def profileA (N M : ℕ) (hNM : N + 1 ≤ M) : ℝ :=
  (profileBound N M hNM 0 + profileBound N M hNM N) *
    volume.real (Metric.closedBall (0 : ℝ³) 1)

lemma profileA_nonneg (N M : ℕ) (hNM : N + 1 ≤ M) : 0 ≤ profileA N M hNM :=
  mul_nonneg (add_nonneg (profileBound_nonneg N M hNM 0) (profileBound_nonneg N M hNM N))
    measureReal_nonneg

/-- `∫ ‖P‖ ≤ profileA` for every profile. -/
lemma integral_norm_profileC_le (N M : ℕ) (hNM : N + 1 ≤ M) (d : ℝ) (hd : |d| ≤ 1) (u : ℝ³) :
    ∫ x : ℝ³, ‖profileC M d u x‖ ≤ profileA N M hNM := by
  have hM1 : 1 ≤ M := by omega
  have hb : ∀ x : ℝ³, ‖profileC M d u x‖ ≤ profileBound N M hNM 0 := by
    intro x
    have h := norm_iteratedFDeriv_profileC_le N M hNM d hd u 0 (by omega) x
    rwa [norm_iteratedFDeriv_zero] at h
  refine (integral_norm_le_of_support_closedBall (profileC M d u) 1 (profileBound N M hNM 0)
    (fun z hz => profileC_support_le_one hM1 d u z hz) (fun z _ => hb z)).trans ?_
  unfold profileA
  rw [add_mul]
  exact le_add_of_nonneg_right (mul_nonneg (profileBound_nonneg N M hNM N) measureReal_nonneg)

/-- `∫ ‖D^N P‖ ≤ profileA` for every profile. -/
lemma integral_norm_iteratedFDeriv_profileC_le (N M : ℕ) (hNM : N + 1 ≤ M) (d : ℝ)
    (hd : |d| ≤ 1) (u : ℝ³) :
    ∫ x : ℝ³, ‖iteratedFDeriv ℝ N (profileC M d u) x‖ ≤ profileA N M hNM := by
  have hM1 : 1 ≤ M := by omega
  have hb : ∀ x : ℝ³, ‖iteratedFDeriv ℝ N (profileC M d u) x‖ ≤ profileBound N M hNM N :=
    fun x => norm_iteratedFDeriv_profileC_le N M hNM d hd u N le_rfl x
  have hsub : Function.support (profileC M d u) ⊆ Metric.closedBall (0 : ℝ³) 1 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact profileC_support_le_one hM1 d u y (Function.mem_support.mp hy)
  have hcl : tsupport (profileC M d u) ⊆ Metric.closedBall (0 : ℝ³) 1 :=
    closure_minimal hsub (isClosed_closedBall : IsClosed (Metric.closedBall (0 : ℝ³) 1))
  have hsup : ∀ z : ℝ³, iteratedFDeriv ℝ N (profileC M d u) z ≠ 0 → ‖z‖ ≤ 1 := by
    intro z hz
    have hmem : z ∈ tsupport (profileC M d u) :=
      support_iteratedFDeriv_subset (𝕜 := ℝ) N (Function.mem_support.mpr hz)
    have hz1 := hcl hmem
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz1
  refine (integral_norm_le_of_support_closedBall (iteratedFDeriv ℝ N (profileC M d u)) 1
    (profileBound N M hNM N) hsup (fun z _ => hb z)).trans ?_
  unfold profileA
  rw [add_mul]
  exact le_add_of_nonneg_left (mul_nonneg (profileBound_nonneg N M hNM 0) measureReal_nonneg)

/-! ## 6. Fourier decay of the profile -/

/-- `(1 + ‖q‖)^k ≤ (2π)^k (1 + ‖(2π)⁻¹ • q‖)^k` (the `2π`-rescaling of the frequency). -/
lemma one_add_le_two_pi_mul_inv_smul (k : ℕ) (q : ℝ³) :
    (1 + ‖q‖) ^ k ≤ (2 * Real.pi) ^ k * (1 + ‖((2 * Real.pi)⁻¹ : ℝ) • q‖) ^ k := by
  have hnorm : ‖((2 * Real.pi)⁻¹ : ℝ) • q‖ = (2 * Real.pi)⁻¹ * ‖q‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [hnorm]
  have h3 : (2 * Real.pi) * (1 + (2 * Real.pi)⁻¹ * ‖q‖) = 2 * Real.pi + ‖q‖ := by
    field_simp
  rw [h3]
  linarith

/-- **Fourier decay of the profile**: for every `N ≥ 1` the profile's `kinFT` is bounded by
`2^N · A · (2π)^N / (1 + ‖q‖)^N`, uniformly in `0 < d ≤ 1` and `u`. -/
lemma profileC_kinFT_decay_pos (N M : ℕ) (hN : 1 ≤ N) (hNM : N + 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (u q : ℝ³), 0 < d → d ≤ 1 →
      ‖kinFT (profileC M d u) q‖ ≤ C / (1 + ‖q‖) ^ N := by
  refine ⟨2 ^ N * profileA N M hNM * (2 * Real.pi) ^ N, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N)
      (profileA_nonneg N M hNM)) (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) N)
  · intro d u q hd hd1
    have hdle : |d| ≤ 1 := by rw [abs_of_pos hd]; exact hd1
    have hdec := Work.BoseFixB1S.oneBodyB1.norm_fourier_le_of_integral_iteratedFDeriv N hN
      (profileC M d u) (profileA N M hNM) (profileA_nonneg N M hNM)
      (contDiff_profileC N M hNM d u) (hasCompactSupport_profileC (by omega) d u)
      (integral_norm_profileC_le N M hNM d hdle u)
      (integral_norm_iteratedFDeriv_profileC_le N M hNM d hdle u)
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    refine (hdec ((2 * Real.pi)⁻¹ • q)).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 ^ N * profileA N M hNM * (1 + ‖q‖) ^ N
        ≤ 2 ^ N * profileA N M hNM *
            ((2 * Real.pi) ^ N * (1 + ‖((2 * Real.pi)⁻¹ : ℝ) • q‖) ^ N) :=
          mul_le_mul_of_nonneg_left (one_add_le_two_pi_mul_inv_smul N q)
            (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N) (profileA_nonneg N M hNM))
      _ = (2 ^ N * profileA N M hNM * (2 * Real.pi) ^ N) *
            (1 + ‖((2 * Real.pi)⁻¹ : ℝ) • q‖) ^ N := by ring

/-- The `N = 0` case of the profile decay (the bare `L¹` bound). -/
lemma profileC_kinFT_decay_zero (M : ℕ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (u q : ℝ³), 0 < d → d ≤ 1 →
      ‖kinFT (profileC M d u) q‖ ≤ C / (1 + ‖q‖) ^ 0 := by
  have hNM : 0 + 1 ≤ M := by omega
  refine ⟨profileA 0 M hNM, profileA_nonneg 0 M hNM, ?_⟩
  intro d u q hd hd1
  have hdle : |d| ≤ 1 := by rw [abs_of_pos hd]; exact hd1
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, pow_zero, div_one]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm (𝕜 := ℝ) Real.fourierChar volume
    (innerₗ ℝ³) (profileC M d u) ((2 * Real.pi)⁻¹ • q)).trans
    (integral_norm_profileC_le 0 M hNM d hdle u)

lemma profileC_kinFT_decay : ∀ (N M : ℕ), N + 1 ≤ M →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (u q : ℝ³), 0 < d → d ≤ 1 →
      ‖kinFT (profileC M d u) q‖ ≤ C / (1 + ‖q‖) ^ N := by
  intro N M hNM
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact profileC_kinFT_decay_zero M (by omega)
  · exact profileC_kinFT_decay_pos N M hNpos hNM

/-! ## 7. Rescaling: `chiSmallB` as a dilated profile -/

/-- `chiSmallB M ℓ d u z = profileC M d u ((ℓd)⁻¹ • z − u)`. -/
lemma chiSmallB_eq_profileC (M : ℕ) (ℓ d : ℝ) (u z : ℝ³) (hℓ : ℓ ≠ 0) (hd : d ≠ 0) :
    ((chiSmallB M ℓ d u z : ℝ) : ℂ) = profileC M d u ((ℓ * d)⁻¹ • z - u) := by
  have h1 : d • (((ℓ * d)⁻¹ • z - u) + u) = ℓ⁻¹ • z := by
    rw [sub_add_cancel, smul_smul]
    congr 1
    field_simp
  simp only [chiSmallB, chiScale, profileC, chiSmallC, chiBumpC, h1, Complex.ofReal_mul]

/-- **The dilation/rescaling identity for `kinFT`**: for `c > 0`,
`kinFT (fun z ↦ g (c⁻¹ • z − u)) p = c³ e^{−i⟪c•p,u⟫} kinFT g (c • p)`. -/
lemma kinFT_inv_smul_sub (g : ℝ³ → ℂ) {c : ℝ} (hc : 0 < c) (u p : ℝ³) :
    kinFT (fun z : ℝ³ => g (c⁻¹ • z - u)) p
      = ((c ^ 3 : ℝ) : ℂ) * (Complex.exp (-(Complex.I * ((inner ℝ (c • p) u : ℝ) : ℂ))) *
          kinFT g (c • p)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [show kinFT (fun z : ℝ³ => g (c⁻¹ • z - u)) p
      = ∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * g (c⁻¹ • z - u) from rfl]
  rw [Work.OneBodyKin.integral_eq_smul_integral_comp_smul
    (g := fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * g (c⁻¹ • z - u)) hc,
    Complex.real_smul]
  congr 1
  rw [show (∫ s : ℝ³, (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        g (c⁻¹ • z - u)) (c • s))
      = ∫ s : ℝ³, Complex.exp (-(Complex.I * (inner ℝ (c • p) s : ℂ))) * g (s - u) from by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    have h1 : c⁻¹ • (c • s) = s := by rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
    have h2 : inner ℝ p (c • s) = inner ℝ (c • p) s := by
      rw [real_inner_smul_right, real_inner_smul_left]
    rw [h1, h2]]
  rw [show (∫ s : ℝ³, Complex.exp (-(Complex.I * (inner ℝ (c • p) s : ℂ))) * g (s - u))
      = kinFT (fun s : ℝ³ => g (s - u)) (c • p) from rfl]
  rw [Work.OneBodyKin.kinFT_comp_sub g u (c • p)]

/-- **Norm form of the rescaling identity.** -/
lemma kinFT_inv_smul_sub_norm_le (g : ℝ³ → ℂ) {c : ℝ} (hc : 0 < c) (u p : ℝ³) :
    ‖kinFT (fun z : ℝ³ => g (c⁻¹ • z - u)) p‖ ≤ c ^ 3 * ‖kinFT g (c • p)‖ := by
  rw [kinFT_inv_smul_sub g hc u p, norm_mul, norm_mul]
  have hpow : ‖(((c ^ 3 : ℝ)) : ℂ)‖ = c ^ 3 := by
    rw [Complex.norm_def, Complex.normSq_ofReal]
    exact Real.sqrt_mul_self (by positivity)
  have hphase : ‖Complex.exp (-(Complex.I * ((inner ℝ (c • p) u : ℝ) : ℂ)))‖ = 1 := by
    have hrew : -(Complex.I * ((inner ℝ (c • p) u : ℝ) : ℂ))
        = ((-(inner ℝ (c • p) u) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrew, Complex.norm_exp_ofReal_mul_I]
  rw [hpow, hphase, one_mul]

/-! ## 8. The target -/

theorem chiSmallB_kinFT_decay (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → d ≤ 1 →
      ∀ (u p : EuclideanSpace ℝ (Fin 3)),
        ‖Submission.BoseGases.kinFT
            (fun z : EuclideanSpace ℝ (Fin 3) =>
              ((Submission.BoseGases.chiSmallB M ℓ d u z : ℝ) : ℂ)) p‖
          ≤ C * (ℓ * d) ^ 3 / (1 + (ℓ * d) * ‖p‖) ^ N := by
  obtain ⟨C, hC0, hC⟩ := profileC_kinFT_decay N M hNM
  refine ⟨C, hC0, ?_⟩
  intro ℓ d hℓ hd hd1 u p
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hfun : (fun z : ℝ³ => ((chiSmallB M ℓ d u z : ℝ) : ℂ))
      = fun z : ℝ³ => profileC M d u ((ℓ * d)⁻¹ • z - u) := by
    funext z
    exact chiSmallB_eq_profileC M ℓ d u z (ne_of_gt hℓ) (ne_of_gt hd)
  rw [hfun]
  have hbound := hC d u ((ℓ * d) • p) hd hd1
  calc ‖kinFT (fun z : ℝ³ => profileC M d u ((ℓ * d)⁻¹ • z - u)) p‖
      ≤ (ℓ * d) ^ 3 * ‖kinFT (profileC M d u) ((ℓ * d) • p)‖ :=
        kinFT_inv_smul_sub_norm_le (profileC M d u) hld u p
    _ ≤ (ℓ * d) ^ 3 * (C / (1 + ‖(ℓ * d) • p‖) ^ N) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C * (ℓ * d) ^ 3 / (1 + (ℓ * d) * ‖p‖) ^ N := by
        have hnorm : ‖(ℓ * d) • p‖ = (ℓ * d) * ‖p‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hld)]
        rw [hnorm]
        ring

end Work.BoseFixB1S.win
