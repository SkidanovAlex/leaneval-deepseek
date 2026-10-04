import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.GrowthDefs
import Submission.Work.Diff.L.riccati_le
import Submission.Work.Diff.L.scal_Q_ge
import Submission.Work.Diff.L.track_closed
import Submission.Work.Diff.Alg.Pinch.scalAlg_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar-curvature growth barrier is an invariant family

For an invariant set `F` of algebraic curvature arrays and `φ₀ > 0`, the time-dependent family

`t ↦ {R ∈ F | φ(t) ≤ scalAlg R}`,   `φ(t) = φ₀ / (1 - (2/n) φ₀ t)` for `t < n/(2φ₀)`, else `0`,

satisfies Hamilton's hypotheses `IsInvariantFamily`: its space-time track is closed, its fibres are
convex, consist of algebraic curvature tensors and are `O(n)`-invariant, and it is invariant under
the ODE `R' = Q(R)`.

The proof of the ODE invariance is the classical scalar maximum principle: if `x t = scalAlg (R t)`
along a solution, then `x' = scalAlg (Q (R t)) ≥ (2/n) x²` (the algebraic input
`Work.Diff.L.scal_Q_ge`, from `scalAlg (Q R) = 2 |Ric|² ≥ (2/n) (scalAlg R)²`), and a one-sided
Gronwall/Riccati comparison (`Work.Diff.L.riccati_le`) against the explicit solution
`y' = (2/n) y²` of the barrier gives `φ(t) ≤ x t`; past the pole of `φ` the barrier vanishes and
`x ≥ x t₀ ≥ φ(t₀) ≥ 0` (monotonicity of `x`) finishes the job.

The helper lemmas below are prefixed `sgf_` (scalar growth family) to keep the shared namespace
`Work.Diff.L` free of collisions.
-/

namespace Work.Diff.L

open Set
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary facts about `scalAlg` -/

theorem sgf_scalAlg_add (R S : Curv4 n) : scalAlg (R + S) = scalAlg R + scalAlg S := by
  simp only [scalAlg, Pi.add_apply, Finset.sum_add_distrib]

theorem sgf_scalAlg_smul (c : ℝ) (R : Curv4 n) : scalAlg (c • R) = c * scalAlg R := by
  simp only [scalAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The superlevel sets of the scalar curvature are convex. -/
theorem sgf_convex_scalAlg_ge (c : ℝ) : Convex ℝ {R : Curv4 n | c ≤ scalAlg R} := by
  intro R hR S hS a b ha hb hab
  simp only [Set.mem_setOf_eq] at hR hS ⊢
  rw [sgf_scalAlg_add, sgf_scalAlg_smul, sgf_scalAlg_smul]
  have h1 : a * c ≤ a * scalAlg R := mul_le_mul_of_nonneg_left hR ha
  have h2 : b * c ≤ b * scalAlg S := mul_le_mul_of_nonneg_left hS hb
  have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  linarith

/-! ## Calculus helpers -/

/-- `scalAlg` is linear, so it commutes with taking derivatives of a curve of curvature arrays. -/
theorem sgf_hasDerivWithinAt_scalAlg_comp (R : ℝ → Curv4 n) (R' : Curv4 n) (t₀ T u : ℝ)
    (h : HasDerivWithinAt R R' (Ico t₀ T) u) :
    HasDerivWithinAt (fun s => scalAlg (R s)) (scalAlg R') (Ico t₀ T) u := by
  have hcoord : ∀ (i j k l : Fin n),
      HasDerivWithinAt (fun s => R s i j k l) (R' i j k l) (Ico t₀ T) u := by
    intro i j k l
    have h1 := hasDerivWithinAt_pi.mp h
    have h2 := hasDerivWithinAt_pi.mp (h1 i)
    have h3 := hasDerivWithinAt_pi.mp (h2 j)
    exact hasDerivWithinAt_pi.mp (h3 k) l
  have hsum : HasDerivWithinAt (fun s => ∑ i, ∑ j, R s i j i j)
      (∑ i, ∑ j, R' i j i j) (Ico t₀ T) u := by
    refine HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ => ?_
    refine HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ => ?_
    exact hcoord i j i j
  simpa only [scalAlg] using hsum

/-- Time shift of a solution of the ODE `R' = Q(R)`. -/
theorem sgf_ode_shift (t₀ T : ℝ) (R : ℝ → Curv4 n)
    (hode : ∀ t ∈ Ico t₀ T, HasDerivWithinAt R (Q (R t)) (Ico t₀ T) t) :
    ∀ s ∈ Ico 0 (T - t₀),
      HasDerivWithinAt (fun s : ℝ => R (s + t₀)) (Q (R (s + t₀))) (Ico 0 (T - t₀)) s := by
  intro s hs
  have hmap : MapsTo (fun s : ℝ => s + t₀) (Ico 0 (T - t₀)) (Ico t₀ T) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have htrans : HasDerivWithinAt (fun s : ℝ => s + t₀) 1 (Ico 0 (T - t₀)) s :=
    (hasDerivWithinAt_id s (Ico 0 (T - t₀))).add_const t₀
  have h := (hode (s + t₀) (hmap hs)).scomp s htrans hmap
  simpa only [one_smul, Function.comp_def] using h

/-- Derivative of the closed form of the barrier: `(φ₀/(1 - (2/n)φ₀ t))' = (2/n) (φ₀/(1 - (2/n)φ₀ t))²`. -/
theorem sgf_hasDerivAt_φbarForm {φ₀ s : ℝ}
    (hden : (1 : ℝ) - (2 / (n : ℝ)) * φ₀ * s ≠ 0) :
    HasDerivAt (fun u : ℝ => φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u))
      ((2 / (n : ℝ)) * (φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * s)) ^ 2) s := by
  have hD : HasDerivAt (fun u : ℝ => 1 - (2 / (n : ℝ)) * φ₀ * u)
      (-((2 / (n : ℝ)) * φ₀)) s :=
    (hasDerivAt_const_mul ((2 / (n : ℝ)) * φ₀) (x := s)).const_sub 1
  have h1 := (hD.inv hden).const_mul φ₀
  have h2 : HasDerivAt (fun y : ℝ => φ₀ * (1 - (2 / (n : ℝ)) * φ₀ * y)⁻¹)
      (φ₀ * (-(-((2 / (n : ℝ)) * φ₀)) / (1 - (2 / (n : ℝ)) * φ₀ * s) ^ 2)) s := h1
  refine h2.congr_deriv ?_
  rw [div_pow]
  ring

/-! ## The main family -/

/-- **The scalar-growth family is invariant**, stated with the explicit barrier `φbar`. -/
theorem sgf_main {F : Set (Curv4 n)} (hF : IsInvariantSet F) {φ₀ : ℝ} (hφ₀ : 0 < φ₀) :
    IsInvariantFamily (fun t : ℝ => {R : Curv4 n | R ∈ F ∧ φbar n φ₀ t ≤ scalAlg R}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact track_closed hF.1 hφ₀
  · intro t
    exact hF.2.1.inter (sgf_convex_scalAlg_ge (φbar n φ₀ t))
  · intro t R hR
    exact hF.2.2.1 R hR.1
  · intro t A hA R hR
    exact ⟨hF.2.2.2.1 A hA R hR.1,
      by rw [Work.Diff.Alg.Pinch.scalAlg_rot n A hA R]; exact hR.2⟩
  · intro t₀ T R hR0 hode t ht
    -- the solution stays in `F`
    have hmemF : ∀ s ∈ Ico t₀ T, R s ∈ F := by
      intro s hs
      have h0 : (fun u : ℝ => R (u + t₀)) 0 ∈ F := by simpa using hR0.1
      have hode' := sgf_ode_shift t₀ T R hode
      have hres := hF.2.2.2.2 (T - t₀) (fun u : ℝ => R (u + t₀)) h0 hode' (s - t₀)
        ⟨sub_nonneg.mpr hs.1, sub_lt_sub_right hs.2 t₀⟩
      simpa only [sub_add_cancel] using hres
    refine ⟨hmemF t ht, ?_⟩
    -- the scalar curvature along the solution
    have hxderiv : ∀ s ∈ Ico t₀ T,
        HasDerivWithinAt (fun u => scalAlg (R u)) (scalAlg (Q (R s))) (Ico t₀ T) s :=
      fun s hs => sgf_hasDerivWithinAt_scalAlg_comp R (Q (R s)) t₀ T s (hode s hs)
    have hxcont : ContinuousOn (fun u => scalAlg (R u)) (Ico t₀ T) :=
      HasDerivWithinAt.continuousOn hxderiv
    have hineq : ∀ s ∈ Ico t₀ T, (2 / (n : ℝ)) * (scalAlg (R s)) ^ 2 ≤ scalAlg (Q (R s)) :=
      fun s hs => scal_Q_ge (hF.2.2.1 (R s) (hmemF s hs))
    -- `x` is nondecreasing, since `x' = scalAlg (Q R) ≥ (2/n) x² ≥ 0`
    have hmono : ∀ s ∈ Ico t₀ T, scalAlg (R t₀) ≤ scalAlg (R s) := by
      intro s hs
      have hsub : Set.Icc t₀ s ⊆ Set.Ico t₀ T := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hs.2⟩
      have hmono' : MonotoneOn (fun u => scalAlg (R u)) (Set.Icc t₀ s) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ s) (hxcont.mono hsub)
          (fun u hu => by
            rw [interior_Icc] at hu ⊢
            exact (hxderiv u ⟨le_of_lt hu.1, lt_trans hu.2 hs.2⟩).mono
              (fun v hv => ⟨le_of_lt hv.1, lt_trans hv.2 hs.2⟩))
          (fun u hu => by
            rw [interior_Icc] at hu
            exact le_trans
              (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) (sq_nonneg _))
              (hineq u ⟨le_of_lt hu.1, lt_trans hu.2 hs.2⟩))
      exact hmono' (Set.left_mem_Icc.mpr hs.1) (Set.right_mem_Icc.mpr hs.1) hs.1
    have hx0nn : 0 ≤ scalAlg (R t₀) := le_trans (φbar_nonneg hφ₀ t₀) hR0.2
    by_cases hcase : t₀ < pole n φ₀
    · by_cases htp : t < pole n φ₀
      · -- below the pole: Riccati comparison against the explicit solution
        have hsub : Ico t₀ (min T (pole n φ₀)) ⊆ Ico t₀ T :=
          fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
        have hle : ∀ u ∈ Ico t₀ (min T (pole n φ₀)),
            0 < (1 : ℝ) - (2 / (n : ℝ)) * φ₀ * u := by
          intro u hu
          exact one_sub_mul_pos_of_lt_pole hφ₀ (lt_of_lt_of_le hu.2 (min_le_right _ _))
        have hcontD : ContinuousOn (fun u : ℝ => 1 - (2 / (n : ℝ)) * φ₀ * u)
            (Ico t₀ (min T (pole n φ₀))) :=
          (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
        have hycont : ContinuousOn (fun u : ℝ => φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u))
            (Ico t₀ (min T (pole n φ₀))) :=
          ContinuousOn.div continuousOn_const hcontD (fun u hu => ne_of_gt (hle u hu))
        have hx' : ∀ u ∈ Ico t₀ (min T (pole n φ₀)),
            HasDerivWithinAt (fun u => scalAlg (R u)) (scalAlg (Q (R u)))
              (Ico t₀ (min T (pole n φ₀))) u :=
          fun u hu => (hxderiv u (hsub hu)).mono hsub
        have hxineq' : ∀ u ∈ Ico t₀ (min T (pole n φ₀)),
            (2 / (n : ℝ)) * (scalAlg (R u)) ^ 2 ≤ scalAlg (Q (R u)) :=
          fun u hu => hineq u (hsub hu)
        have hy' : ∀ u ∈ Ico t₀ (min T (pole n φ₀)),
            HasDerivWithinAt (fun u : ℝ => φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u))
              ((2 / (n : ℝ)) * (φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u)) ^ 2)
              (Ico t₀ (min T (pole n φ₀))) u :=
          fun u hu =>
            (sgf_hasDerivAt_φbarForm (φ₀ := φ₀) (s := u) (ne_of_gt (hle u hu))).hasDerivWithinAt
        have hyp' : ∀ u ∈ Ico t₀ (min T (pole n φ₀)),
            0 < φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u) :=
          fun u hu => div_pos hφ₀ (hle u hu)
        have h0' : (fun u : ℝ => φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u)) t₀
            ≤ (fun u => scalAlg (R u)) t₀ := by
          show φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t₀) ≤ scalAlg (R t₀)
          rw [← φbar_of_lt (n := n) (t := t₀) hcase]
          exact hR0.2
        have hcmp := riccati_le (c := 2 / (n : ℝ)) (t₀ := t₀) (T := min T (pole n φ₀))
          (x := fun u => scalAlg (R u)) (x' := fun u => scalAlg (Q (R u)))
          (y := fun u : ℝ => φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * u))
          (div_nonneg (by norm_num) (Nat.cast_nonneg n)) (hxcont.mono hsub) hycont hx' hxineq'
          hy' hyp' h0'
        have := hcmp t ⟨ht.1, lt_min ht.2 htp⟩
        rwa [φbar_of_lt htp]
      · -- the barrier has vanished below `T`
        rw [φbar_of_pole_le (n := n) (t := t) (le_of_not_gt htp)]
        exact le_trans hx0nn (hmono t ht)
    · -- `t₀` is already past the pole, so the barrier is `0` throughout
      rw [φbar_of_pole_le (n := n) (t := t) (le_trans (le_of_not_gt hcase) ht.1)]
      exact le_trans hx0nn (hmono t ht)

/-- **The scalar-curvature growth family is invariant.**  For an invariant set `F` of curvature
arrays and `φ₀ > 0`, the family `t ↦ {R ∈ F | φ(t) ≤ scalAlg R}` with `φ' = (2/n) φ²` (i.e.
`φ(t) = φ₀/(1 - (2/n)φ₀ t)`, continued by `0` past its pole `n/(2φ₀)`) is invariant under
Hamilton's ODE. -/
theorem scalar_growth_family_v3 {n : ℕ} {F : Set (Submission.Diff.Alg.Curv4 n)}
    (hF : Submission.Diff.Alg.IsInvariantSet F) {φ₀ : ℝ} (hφ₀ : 0 < φ₀) :
    Submission.Diff.Alg.IsInvariantFamily (fun t : ℝ => {R : Submission.Diff.Alg.Curv4 n |
      R ∈ F ∧ (if t < (n : ℝ) / (2 * φ₀) then φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) else 0)
        ≤ Submission.Diff.Alg.scalAlg R}) := by
  exact sgf_main hF hφ₀

end Work.Diff.L
