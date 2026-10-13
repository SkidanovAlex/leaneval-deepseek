/-
# `Work.FTS.PhiStar.Honesty.CptApp.approxSmoothCptQ`

`SmoothCptQ (approx n F)` for `F` merely `C^∞` on the *open* quadrant and `2 ≤ n`.

The two halves:

* **compact support** — `approx n F = chiR n · (zetaR n · F - lam n F · rho)`: away from
  `(1/n, 2n)` the radial cutoff `chiR n` vanishes, and away from
  `(1/n, π/2 - 1/n) ∪ (1, 3/2)` both `zetaR n` and `rho` vanish, so the support lies in
  `[1/n, 2n] × [1/n, max (3/2) (π/2 - 1/n)]`, a rectangle strictly inside the open quadrant.
* **smoothness** — `chiR n`, `zetaR n`, `rho` are globally `C^∞`; the product
  `chiR n z · zetaR n θ · F z θ` is globally `C^∞` because the multiplier
  `(z,θ) ↦ chiR n z · zetaR n θ` has its topological support inside the open quadrant, where `F`
  is `C^∞` (`contDiff_mul_of_tsupport_subset`, a locality lemma); and `z ↦ lam n F z` is `C^∞`
  on a neighbourhood of `supp (chiR n)` (a truncated angular integral of a smooth integrand over
  a compact interval strictly inside `(0,π/2)`), whence `fun z => chiR n z * lam n F z` is
  globally `C^∞`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## A locality lemma

A `C^m` multiplier whose topological support lies in an open set `U` may be multiplied by a
function that is only `C^m` on `U`. -/

theorem contDiff_mul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : WithTop ℕ∞} {c u : E → ℝ} {U : Set E} (hc : ContDiff ℝ m c)
    (hu : ContDiffOn ℝ m u U) (hU : IsOpen U) (hsub : tsupport c ⊆ U) :
    ContDiff ℝ m (fun p => c p * u p) := by
  rw [← contDiffOn_univ]
  refine contDiffOn_of_locally_contDiffOn (fun z _ => ?_)
  by_cases hzU : z ∈ U
  · exact ⟨U, hU, hzU, (hc.contDiffOn.mul hu).mono Set.inter_subset_right⟩
  · refine ⟨(tsupport c)ᶜ, (isClosed_tsupport c).isOpen_compl, fun h => hzU (hsub h), ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr (fun x hx => ?_)
    have hx0 : c x = 0 := by
      by_contra hxc
      exact hx.2 (subset_tsupport c (Function.mem_support.mpr hxc))
    rw [hx0, zero_mul]

/-! ## The cutoffs are globally smooth -/

theorem contDiff_chiR (n : ℕ) (m : ℕ) : ContDiff ℝ m (chiR n) := by
  unfold chiR cut01
  fun_prop

theorem contDiff_zetaR (n : ℕ) (m : ℕ) : ContDiff ℝ m (zetaR n) := by
  unfold zetaR cut01
  fun_prop

theorem contDiff_rho (m : ℕ) : ContDiff ℝ m (rho) := by
  unfold rho rhoAux cut01
  fun_prop

/-! ## Support facts -/

/-- `cut01 t ≠ 0` forces `t > 0`. -/
theorem pos_of_cut01_ne_zero {t : ℝ} (h : cut01 t ≠ 0) : 0 < t := by
  by_contra hle
  exact h (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hle))

theorem chiR_ne_zero_bounds {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (h : chiR n z ≠ 0) :
    1 / (n : ℝ) < z ∧ z < 2 * (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h1 : cut01 ((n : ℝ) * z - 1) ≠ 0 := fun hh => h (by rw [chiR, hh, zero_mul])
  have h2 : cut01 (2 - z / (n : ℝ)) ≠ 0 := fun hh => h (by rw [chiR, hh, mul_zero])
  have h1' := pos_of_cut01_ne_zero h1
  have h2' := pos_of_cut01_ne_zero h2
  constructor
  · rw [div_lt_iff₀ hnpos]
    nlinarith
  · have h2'' : z / (n : ℝ) < 2 := by linarith
    rw [div_lt_iff₀ hnpos] at h2''
    linarith

theorem zetaR_ne_zero_bounds {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (h : zetaR n θ ≠ 0) :
    1 / (n : ℝ) < θ ∧ θ < Real.pi / 2 - 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h1 : cut01 ((n : ℝ) * θ - 1) ≠ 0 := fun hh => h (by rw [zetaR, hh, zero_mul])
  have h2 : cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1) ≠ 0 :=
    fun hh => h (by rw [zetaR, hh, mul_zero])
  have h1' := pos_of_cut01_ne_zero h1
  have h2' := pos_of_cut01_ne_zero h2
  constructor
  · rw [div_lt_iff₀ hnpos]
    nlinarith
  · have h2'' : 1 / (n : ℝ) < Real.pi / 2 - θ := by
      rw [div_lt_iff₀ hnpos]
      nlinarith
    linarith

theorem rhoAux_ne_zero_bounds {θ : ℝ} (h : rhoAux θ ≠ 0) : 1 < θ ∧ θ < 3 / 2 := by
  have h1 : cut01 (2 * θ - 2) ≠ 0 := fun hh => h (by rw [rhoAux, hh, zero_mul])
  have h2 : cut01 (3 - 2 * θ) ≠ 0 := fun hh => h (by rw [rhoAux, hh, mul_zero])
  have h1' := pos_of_cut01_ne_zero h1
  have h2' := pos_of_cut01_ne_zero h2
  constructor <;> linarith

theorem rho_ne_zero_bounds {θ : ℝ} (h : rho θ ≠ 0) : 1 < θ ∧ θ < 3 / 2 := by
  refine rhoAux_ne_zero_bounds (fun hh => h ?_)
  rw [rho, hh, mul_zero]

/-- The topological support of `chiR n` lies in `(1/(2n), 4n)` (for `n ≥ 1`). -/
theorem chiR_tsupport_subset {n : ℕ} (hn : 1 ≤ n) :
    tsupport (chiR n) ⊆ Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hle : tsupport (chiR n) ⊆ Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)) :=
    closure_minimal (fun z hz => by
      obtain ⟨h1, h2⟩ := chiR_ne_zero_bounds hn (Function.mem_support.mp hz)
      exact ⟨le_of_lt h1, le_of_lt h2⟩) isClosed_Icc
  refine subset_trans hle fun z hz => ⟨?_, ?_⟩
  · have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have : 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) :=
      one_div_lt_one_div_of_lt hnpos (by linarith)
    linarith [hz.1]
  · have : 2 * (n : ℝ) < 4 * (n : ℝ) := by linarith
    linarith [hz.2]

/-- The topological support of `(z,θ) ↦ chiR n z · zetaR n θ` lies in the open quadrant. -/
theorem chiR_zetaR_tsupport_subset {n : ℕ} (hn : 1 ≤ n) :
    tsupport (fun p : ℝ × ℝ => chiR n p.1 * zetaR n p.2) ⊆
      Work.FTS.EllipticEst.Q0 := by
  have hle : tsupport (fun p : ℝ × ℝ => chiR n p.1 * zetaR n p.2) ⊆
      Set.Icc (1 / (n : ℝ)) (2 * (n : ℝ)) ×ˢ
        Set.Icc (1 / (n : ℝ)) (Real.pi / 2 - 1 / (n : ℝ)) :=
    closure_minimal (fun p hp => by
      have hp' : chiR n p.1 * zetaR n p.2 ≠ 0 := Function.mem_support.mp hp
      have h1 : chiR n p.1 ≠ 0 := fun hh => hp' (by rw [hh, zero_mul])
      have h2 : zetaR n p.2 ≠ 0 := fun hh => hp' (by rw [hh, mul_zero])
      obtain ⟨ha1, ha2⟩ := chiR_ne_zero_bounds hn h1
      obtain ⟨hb1, hb2⟩ := zetaR_ne_zero_bounds hn h2
      exact ⟨⟨le_of_lt ha1, le_of_lt ha2⟩, ⟨le_of_lt hb1, le_of_lt hb2⟩⟩)
      (isClosed_Icc.prod isClosed_Icc)
  refine subset_trans hle fun p hp => ?_
  rw [Work.FTS.EllipticEst.mem_Q0]
  have h1n : (0 : ℝ) < 1 / (n : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    positivity
  exact ⟨lt_of_lt_of_le (by positivity) hp.1.1,
    lt_of_lt_of_le (by positivity) hp.2.1,
    lt_of_le_of_lt hp.2.2 (by linarith)⟩

/-! ## Compact support of the approximation -/

/-- `approx n F` is compactly supported in the open quadrant (no smoothness of `F` needed). -/
theorem approxCptQ_local (F : ℝ → ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    Work.FTS.PhiStar.Honesty.CptQ (approx n F) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h1n : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnpos]
    exact hn1R
  refine ⟨1 / (n : ℝ), 2 * (n : ℝ), 1 / (n : ℝ), max (3 / 2) (Real.pi / 2 - 1 / (n : ℝ)),
    by positivity, ?_, by positivity, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hnpos]
    nlinarith [hn1R]
  · have h32 : (1 : ℝ) < 3 / 2 := by norm_num
    linarith [le_max_left (3 / 2) (Real.pi / 2 - 1 / (n : ℝ))]
  · refine max_lt (by linarith [Real.pi_gt_three]) ?_
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  · intro z θ h
    have hchi : chiR n z ≠ 0 := fun hh => h (by rw [approx, hh, zero_mul])
    have hinner : zetaR n θ * F z θ - lam n F z * rho θ ≠ 0 :=
      fun hh => h (by rw [approx, hh, mul_zero])
    obtain ⟨hz1, hz2⟩ := chiR_ne_zero_bounds hn1 hchi
    refine ⟨⟨le_of_lt hz1, le_of_lt hz2⟩, ?_⟩
    by_cases hz : zetaR n θ = 0
    · have hrho : rho θ ≠ 0 := by
        intro hr
        exact hinner (by rw [hz, hr, mul_zero, zero_mul, sub_zero])
      obtain ⟨hr1, hr2⟩ := rho_ne_zero_bounds hrho
      exact ⟨le_trans h1n (le_of_lt hr1),
        le_of_lt (lt_of_lt_of_le hr2 (le_max_left _ _))⟩
    · obtain ⟨ht1, ht2⟩ := zetaR_ne_zero_bounds hn1 hz
      exact ⟨le_of_lt ht1, le_of_lt (lt_of_lt_of_le ht2 (le_max_right _ _))⟩

/-! ## The approximation is smooth

The remaining input is the smoothness of the truncated angular moment `lam n F` on a
neighbourhood of the support of `chiR n`; everything else is localised multiplication. -/

/-- **Smoothness of `approx n F`** from the smoothness of the truncated moment at scale `n`. -/
theorem contDiff_uncurry_approx_of_lam {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 2 ≤ n)
    (hlam : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => lam n F z)
      (Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ)))) :
    ∀ m : ℕ, ContDiff ℝ m (Function.uncurry (approx n F)) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  intro m
  have hF_on : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsm m
  -- (1) the `zetaR · F` term
  have hc1 : ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => chiR n p.1 * zetaR n p.2) :=
    ((contDiff_chiR n m).comp contDiff_fst).mul
      ((contDiff_zetaR n m).comp contDiff_snd)
  have h1 : ContDiff ℝ (m : WithTop ℕ∞)
      (fun p : ℝ × ℝ => chiR n p.1 * zetaR n p.2 * F p.1 p.2) :=
    contDiff_mul_of_tsupport_subset hc1 hF_on Work.FTS.EllipticEst.isOpen_Q0
      (chiR_zetaR_tsupport_subset hn1)
  -- (2) the `lam · rho` term
  have hchiLam : ContDiff ℝ (m : WithTop ℕ∞) (fun z : ℝ => chiR n z * lam n F z) :=
    contDiff_mul_of_tsupport_subset (contDiff_chiR n m) (hlam m) isOpen_Ioo
      (chiR_tsupport_subset hn1)
  have hc2 : ContDiff ℝ (m : WithTop ℕ∞) (fun p : ℝ × ℝ => chiR n p.1 * lam n F p.1) :=
    hchiLam.comp contDiff_fst
  have h2 : ContDiff ℝ (m : WithTop ℕ∞)
      (fun p : ℝ × ℝ => chiR n p.1 * lam n F p.1 * rho p.2) :=
    hc2.mul ((contDiff_rho m).comp contDiff_snd)
  -- (3) the difference is the uncurried approximation
  rw [show Function.uncurry (approx n F) =
      (fun p : ℝ × ℝ => chiR n p.1 * zetaR n p.2 * F p.1 p.2
        - chiR n p.1 * lam n F p.1 * rho p.2) from by
    funext p
    simp only [Function.uncurry, approx]
    ring]
  exact h1.sub h2

/-! ## The truncated moment is smooth

`lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ`; the integrand vanishes outside the closed
interval `[1/n, π/2 - 1/n] ⊂ (0,π/2)`, on which `F` and all its `z`-derivatives are continuous
(they live in the open quadrant).  Hence the parametric integral may be differentiated under the
integral sign, and an induction on the order gives `C^∞` on a neighbourhood of `supp (chiR n)`. -/

/-- The truncated angular integral `lam n F z` is the interval integral of the same integrand
over `(1/n, π/2 - 1/n)`. -/
theorem lam_eq_interval (F : ℝ → ℝ → ℝ) {n : ℕ} (hn : 2 ≤ n) (z : ℝ) :
    lam n F z = ∫ θ in (1 / (n : ℝ))..(Real.pi / 2 - 1 / (n : ℝ)),
      zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ := by
  set a := 1 / (n : ℝ) with ha
  set b := Real.pi / 2 - 1 / (n : ℝ) with hb
  have hab : a ≤ b := by
    rw [ha, hb]
    have h2 : 2 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < (n:ℝ))]
      exact_mod_cast hn
    have h3 : (1:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    have h4 : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
    linarith
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    refine fun θ hθ => ⟨?_, ?_⟩
    · have : (0 : ℝ) < a := by rw [ha]; positivity
      linarith [hθ.1]
    · have hb' : b < Real.pi / 2 := by
        rw [hb]
        have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
        linarith
      linarith [hθ.2]
  have hzero : ∀ θ ∈ Work.Spaces.Iθ \ Set.Icc a b,
      zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ = 0 := by
    intro θ hθ
    rcases lt_or_ge θ a with hlt | hge
    · have h0 : cut01 ((n : ℝ) * θ - 1) = 0 := by
        refine Real.smoothTransition.zero_of_nonpos ?_
        rw [ha] at hlt
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ))] at hlt
        nlinarith
      rw [zetaR, h0]
      simp
    · have hgt : b < θ := by
        by_contra hle
        exact hθ.2 ⟨hge, le_of_not_gt hle⟩
      have h0 : cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1) = 0 := by
        refine Real.smoothTransition.zero_of_nonpos ?_
        rw [hb] at hgt
        have hkey : Real.pi / 2 - θ < 1 / (n : ℝ) := by linarith
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ))] at hkey
        nlinarith
      rw [zetaR, h0]
      simp
  calc lam n F z
      = ∫ θ in Work.Spaces.Iθ, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ := rfl
    _ = ∫ θ in Set.Icc a b, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) hsub hzero
    _ = ∫ θ in Set.Ioc a b, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ θ in a..b, zetaR n θ * F z θ * Work.Elliptic.sinCos2 θ :=
        (intervalIntegral.integral_of_le hab).symm

/-- **One parametric differentiation step**: for `z` in the support window of `chiR n`, the
`k`-th truncated integral is differentiable with derivative the `(k+1)`-st. -/
theorem lam_hasDerivAt {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ}
    (hn : 2 ≤ n) (k : ℕ) {z : ℝ}
    (hz : z ∈ Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ))) :
    HasDerivAt (fun z' => ∫ θ in (1 / (n : ℝ))..(Real.pi / 2 - 1 / (n : ℝ)),
        zetaR n θ * Work.Spaces.pzIter k F z' θ * Work.Elliptic.sinCos2 θ)
      (∫ θ in (1 / (n : ℝ))..(Real.pi / 2 - 1 / (n : ℝ)),
        zetaR n θ * Work.Spaces.pzIter (k + 1) F z θ * Work.Elliptic.sinCos2 θ) z := by
  set a := 1 / (n : ℝ) with ha
  set b := Real.pi / 2 - 1 / (n : ℝ) with hb
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hb_lt : b < Real.pi / 2 := by
    rw [hb]
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  have hab : a < b := by
    rw [ha, hb]
    have h2 : 2 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn
    have h3 : (1:ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have h4 : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
    linarith
  -- the comparison window `(x₁, x₂)` around `z`
  set x₁ := (z + 1 / (2 * (n : ℝ))) / 2 with hx₁
  set x₂ := (z + 4 * (n : ℝ)) / 2 with hx₂
  have hx₁_lt : x₁ < z := by rw [hx₁]; linarith [hz.1]
  have hx₂_gt : z < x₂ := by rw [hx₂]; linarith [hz.2]
  have hx₁_gt : 1 / (2 * (n : ℝ)) < x₁ := by rw [hx₁]; linarith [hz.1]
  have hx₂_lt : x₂ < 4 * (n : ℝ) := by rw [hx₂]; linarith [hz.2]
  have hx₁_pos : (0 : ℝ) < x₁ := by
    have : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hbox : ∀ x ∈ Set.Icc x₁ x₂, ∀ θ ∈ Set.Icc a b, (x, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    intro x hx θ hθ
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le hx₁_pos hx.1, lt_of_lt_of_le ha_pos hθ.1,
      lt_of_le_of_lt hθ.2 hb_lt⟩
  -- joint continuity of the `k`-th integrand on the compact window
  have hcontG : ∀ j : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      zetaR n p.2 * Work.Spaces.pzIter j F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Icc x₁ x₂ ×ˢ Set.Icc a b) := by
    intro j
    have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter j F p.1 p.2)
        (Set.Icc x₁ x₂ ×ˢ Set.Icc a b) :=
      ((hsm.pzIter j).continuousOn).mono (fun p hp => hbox p.1 hp.1 p.2 hp.2)
    have hz : Continuous (fun p : ℝ × ℝ => zetaR n p.2) :=
      (contDiff_zetaR n 0).continuous.comp continuous_snd
    have hs : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) :=
      (by unfold Work.Elliptic.sinCos2; fun_prop :
        Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ)).comp continuous_snd
    exact ((hz.continuousOn.mul hpz).mul hs.continuousOn).congr (fun p _ => rfl)
  -- a uniform bound for the `(k+1)`-st integrand on the window
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hcontG (k + 1))
  refine Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
    (x₀ := z) (x₁ := x₁) (x₂ := x₂)
    (G := fun t x => zetaR n t * Work.Spaces.pzIter k F x t * Work.Elliptic.sinCos2 t)
    (G' := fun t x => zetaR n t * Work.Spaces.pzIter (k + 1) F x t * Work.Elliptic.sinCos2 t)
    (bound := fun _ => C) hx₁_lt hx₂_gt ?_ ?_ ?_ ?_ ?_ ?_
  · -- measurability of `G · x`
    intro x hx
    have hxIcc : x ∈ Set.Icc x₁ x₂ := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hslice : ContinuousOn (fun θ : ℝ =>
        zetaR n θ * Work.Spaces.pzIter k F x θ * Work.Elliptic.sinCos2 θ) (Set.Icc a b) :=
      (hcontG k).comp (continuousOn_const.prodMk continuousOn_id)
        (fun θ hθ => ⟨hxIcc, hθ⟩)
    refine (hslice.mono ?_).aestronglyMeasurable measurableSet_uIoc
    rw [Set.uIoc_of_le (le_of_lt hab)]
    exact Set.Ioc_subset_Icc_self
  · -- integrability of `G · z`
    have hslice : ContinuousOn (fun θ : ℝ =>
        zetaR n θ * Work.Spaces.pzIter k F z θ * Work.Elliptic.sinCos2 θ) (Set.Icc a b) :=
      (hcontG k).comp (continuousOn_const.prodMk continuousOn_id)
        (fun θ hθ => ⟨⟨le_of_lt hx₁_lt, le_of_lt hx₂_gt⟩, hθ⟩)
    exact hslice.intervalIntegrable_of_Icc (le_of_lt hab)
  · -- measurability of `G' · z`
    have hslice : ContinuousOn (fun θ : ℝ =>
        zetaR n θ * Work.Spaces.pzIter (k + 1) F z θ * Work.Elliptic.sinCos2 θ) (Set.Icc a b) :=
      (hcontG (k + 1)).comp (continuousOn_const.prodMk continuousOn_id)
        (fun θ hθ => ⟨⟨le_of_lt hx₁_lt, le_of_lt hx₂_gt⟩, hθ⟩)
    refine (hslice.mono ?_).aestronglyMeasurable measurableSet_uIoc
    rw [Set.uIoc_of_le (le_of_lt hab)]
    exact Set.Ioc_subset_Icc_self
  · -- the domination bound
    intro t ht x hx
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have htIcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
    have h := hC (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, htIcc⟩
    simpa only [Real.norm_eq_abs] using h
  · exact intervalIntegrable_const
  · -- the pointwise `z`-derivative of the integrand
    intro t ht x hx
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have htIcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
    have htIoo : t ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ha_pos htIcc.1, lt_of_le_of_lt htIcc.2 hb_lt⟩
    have hxpos : 0 < x := lt_of_lt_of_le hx₁_pos (le_of_lt hx.1)
    have hd := hsm.hasDerivAt_slice_pzIter k htIoo hxpos
    simpa only [Function.uncurry] using
      (hd.const_mul (zetaR n t)).mul_const (Work.Elliptic.sinCos2 t)

/-- **Smoothness of the truncated integral on the support window**, by induction on the order;
the `k`-th integral has derivative the `(k+1)`-st, and continuity comes from those
derivatives. -/
theorem contDiffOn_Ilam {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ}
    (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ k : ℕ, ContDiffOn ℝ m
      (fun z => ∫ θ in (1 / (n : ℝ))..(Real.pi / 2 - 1 / (n : ℝ)),
        zetaR n θ * Work.Spaces.pzIter k F z θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ))) := by
  intro m
  induction m with
  | zero =>
    intro k
    exact (contDiffOn_zero (𝕜 := ℝ)).mpr
      (fun z hz => (lam_hasDerivAt hsm hn k hz).continuousAt.continuousWithinAt)
  | succ m ih =>
    intro k
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := fun z => ∫ θ in (1 / (n : ℝ))..(Real.pi / 2 - 1 / (n : ℝ)),
        zetaR n θ * Work.Spaces.pzIter k F z θ * Work.Elliptic.sinCos2 θ)
      (n := ((m : ℕ) : WithTop ℕ∞))
      (s := Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ))) isOpen_Ioo).2
      ⟨fun z hz => (lam_hasDerivAt hsm hn k hz).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp),
        (ih (k + 1)).congr (fun z hz => (lam_hasDerivAt hsm hn k hz).deriv)⟩

/-- The smoothness input consumed by `contDiff_uncurry_approx_of_lam`: `lam n F` is `C^∞` on a
neighbourhood of the support of `chiR n`. -/
theorem lam_contDiffOn_local {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => lam n F z)
      (Set.Ioo (1 / (2 * (n : ℝ))) (4 * (n : ℝ))) :=
  (contDiffOn_Ilam hsm hn m 0).congr (fun z _ => lam_eq_interval F hn z)

theorem approxSmoothCptQ {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (n : ℕ) (hn : 2 ≤ n) :
    Work.FTS.PhiStar.Honesty.SmoothCptQ (Work.FTS.PhiStar.Honesty.CptApp.approx n F) :=
  ⟨contDiff_uncurry_approx_of_lam hsm hn (lam_contDiffOn_local hsm hn),
    approxCptQ_local F n hn⟩

end Work.FTS.PhiStar.Honesty.CptApp
