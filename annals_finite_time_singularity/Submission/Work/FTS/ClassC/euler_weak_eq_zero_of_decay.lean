/-
Copyright: work module for the Elgindi finite-time singularity project.

# Rigidity of the weak (integrated) Euler-type ODE with decay

Let `u, v : ℝ → ℝ` satisfy the two *integrated* (weak) chains of the Euler-type ODE
`α² z² u'' + α (5 + α) z u' = 0` on `(0, ∞)`:

* `u z - u s = ∫_s^z v`,  and
* `v z - v s = ∫_s^z (-(5+α)/(α r)) * v r dr`  for all `0 < s ≤ z`,

together with the decay `u → 0` at `+∞` and the paper's condition `z² u → 0` at `0⁺`.  Then
`u ≡ 0` on `(0, ∞)` (for `0 < α < 5/2`).

The mathematical content is:

1. **Regularity from the weak chains.**  The integrated ODE forces `v` to be locally bounded
   (`Work.FTS.ClassC.euler_weak_gronwall`, a Gronwall estimate for the weak chain), hence
   continuous, hence `C¹`; and `u` is `C¹` with `u' = v`.  The key point is that the dichotomy
   "`∫_s^z g = 0`" / "`g` is interval integrable" makes the primitive well behaved and yields a
   Lipschitz bound on every compact subinterval of `(0, ∞)`.
2. **The classical solution form.**  `u` then solves the ODE in the strong (classical) sense
   and `u` is `C²` on `(0, ∞)`, so `Work.FTS.ClassC.euler_ode_eq_zero_of_decay_of_zsq`
   applies: `u = B₁ + B₂ z^{-5/α}`, `u → 0` at `+∞` kills `B₁` and `z²u → 0` at `0` kills `B₂`
   because `α < 5/2`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.euler_ode_unique
import Submission.Work.FTS.ClassC.euler_weak_gronwall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The norm of the second chain's coefficient times an arbitrary factor. -/
private lemma norm_coeff_mul {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) (w : ℝ) :
    ‖(-(5 + α) / (α * r)) * w‖ = ((5 + α) / (α * r)) * |w| := by
  have heq : (-(5 + α) / (α * r)) * w = -(((5 + α) / (α * r)) * w) := by ring
  rw [heq, norm_neg, norm_mul]
  have hpos : (0 : ℝ) ≤ (5 + α) / (α * r) := by positivity
  rw [Real.norm_of_nonneg hpos, Real.norm_eq_abs]

theorem euler_weak_eq_zero_of_decay {α : ℝ} {u v : ℝ → ℝ} (hα : 0 < α) (hα2 : α < 5 / 2)
    (hchain0 : ∀ s z : ℝ, 0 < s → s ≤ z → u z - u s = ∫ r in s..z, v r)
    (hchain1 : ∀ s z : ℝ, 0 < s → s ≤ z →
      v z - v s = ∫ r in s..z, (-(5 + α) / (α * r)) * v r)
    (hdec : Filter.Tendsto u Filter.atTop (nhds 0))
    (hzsq : Filter.Tendsto (fun z : ℝ => z ^ 2 * u z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z : ℝ, 0 < z → u z = 0 := by
  set K : ℝ := (5 + α) / α with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  -- ## (A) the Gronwall bound for the weak second chain
  have hgron : ∀ a b : ℝ, 0 < a → a ≤ b → |v b| ≤ |v a| * (b / a) ^ K := by
    intro a b ha hab
    rw [hKdef]
    exact euler_weak_gronwall hα hchain1 a b ha hab
  -- ## (B) the bound on `[a,x]`, with the weight frozen at the right endpoint
  have hbdd : ∀ a x : ℝ, 0 < a → a ≤ x → ∀ r ∈ Set.Icc a x,
      |v r| ≤ |v a| * (x / a) ^ K := by
    intro a x ha hax r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    refine le_trans (hgron a r ha hr.1) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    exact Real.rpow_le_rpow (div_nonneg hr0.le ha.le)
      (div_le_div_of_nonneg_right hr.2 ha.le) hKpos.le
  -- ## (C) a Lipschitz bound on `[a,x]`
  have hlip : ∀ a x : ℝ, 0 < a → a ≤ x → ∃ C : ℝ, 0 ≤ C ∧ ∀ s z : ℝ,
      a ≤ s → s ≤ z → z ≤ x → |v z - v s| ≤ C * (z - s) := by
    intro a x ha hax
    have hM : ∀ r ∈ Set.Icc a x, |v r| ≤ |v a| * (x / a) ^ K := hbdd a x ha hax
    have hxa : 0 ≤ x / a := div_nonneg (le_trans ha.le hax) ha.le
    have hCcoef : 0 ≤ (5 + α) / (α * a) := by positivity
    have hCnn : 0 ≤ ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K) :=
      mul_nonneg hCcoef (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hxa _))
    refine ⟨((5 + α) / (α * a)) * (|v a| * (x / a) ^ K), hCnn, ?_⟩
    intro s z has hsz hzx
    have hs0 : 0 < s := lt_of_lt_of_le ha has
    have hpt : ∀ r ∈ Set.Icc s z,
        ‖(-(5 + α) / (α * r)) * v r‖ ≤ ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hs0 hr.1
      rw [norm_coeff_mul hα hr0]
      have h1 : (5 + α) / (α * r) ≤ (5 + α) / (α * a) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (le_trans has hr.1) hα.le)
      have h2 : |v r| ≤ |v a| * (x / a) ^ K := hM r ⟨le_trans has hr.1, le_trans hr.2 hzx⟩
      exact mul_le_mul h1 h2 (abs_nonneg _) hCcoef
    have key : |∫ r in s..z, (-(5 + α) / (α * r)) * v r|
        ≤ ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K) * (z - s) := by
      have h1 : ‖∫ r in s..z, (-(5 + α) / (α * r)) * v r‖ ≤
          ∫ r in s..z, ‖(-(5 + α) / (α * r)) * v r‖ :=
        intervalIntegral.norm_integral_le_integral_norm hsz
      have h2 : (∫ r in s..z, ‖(-(5 + α) / (α * r)) * v r‖)
          ≤ ∫ r in s..z, ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K) := by
        by_cases hint : IntervalIntegrable (fun r => ‖(-(5 + α) / (α * r)) * v r‖) volume s z
        · exact intervalIntegral.integral_mono_on hsz hint
            continuousOn_const.intervalIntegrable hpt
        · rw [intervalIntegral.integral_undef hint, intervalIntegral.integral_const,
            smul_eq_mul]
          exact mul_nonneg (sub_nonneg.mpr hsz) hCnn
      have h3 : (∫ r in s..z, ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K))
          = ((5 + α) / (α * a)) * (|v a| * (x / a) ^ K) * (z - s) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [Real.norm_eq_abs] at h1
      linarith [h1, h2, h3]
    rw [hchain1 s z hs0 hsz]
    exact key
  -- ## (D) `v` is continuous on `(0,∞)`
  have hvcont : ContinuousOn v (Set.Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    obtain ⟨C, hCnn, hC⟩ := hlip (x / 2) (2 * x) (by linarith) (by linarith)
    have hLip : LipschitzOnWith ⟨C, hCnn⟩ v (Set.Icc (x / 2) (2 * x)) :=
      LipschitzOnWith.of_dist_le_mul (fun s hs z hz => by
        rw [Real.dist_eq, Real.dist_eq]
        rcases le_total s z with hsz | hzs
        · have h := hC s z hs.1 hsz hz.2
          rw [abs_of_nonpos (sub_nonpos.mpr hsz), neg_sub, abs_sub_comm (v s) (v z)]
          exact h
        · have h := hC z s hz.1 hzs hs.2
          rw [abs_of_nonneg (sub_nonneg.mpr hzs)]
          exact h)
    have hxmem : Set.Icc (x / 2) (2 * x) ∈ 𝓝 x :=
      Icc_mem_nhds (by linarith) (by linarith)
    exact (hLip.continuousOn.continuousAt hxmem).continuousWithinAt
  -- ## (E) the coefficient block is continuous
  have hgcoefcont : ContinuousOn (fun r : ℝ => (-(5 + α) / (α * r))) (Set.Ioi 0) :=
    ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
      (fun r hr => mul_ne_zero (ne_of_gt hα) (ne_of_gt hr))
  have hgcont : ContinuousOn (fun r : ℝ => (-(5 + α) / (α * r)) * v r) (Set.Ioi 0) :=
    hgcoefcont.mul hvcont
  -- ## (F) the pointwise derivatives `u' = v` and `v' = gcoef`
  have hu_deriv : ∀ x : ℝ, 0 < x → HasDerivAt u (v x) x := by
    intro x hx
    have ha : 0 < x / 2 := by linarith
    have hax : x / 2 < x := by linarith
    have hle : x / 2 ≤ x := le_of_lt hax
    have hueq : Set.EqOn u (fun z => u (x / 2) + ∫ r in (x / 2)..z, v r)
        (Set.Icc (x / 2) (2 * x)) := by
      intro z hz
      have h := hchain0 (x / 2) z ha hz.1
      show u z = u (x / 2) + ∫ r in (x / 2)..z, v r
      linarith
    have hvcontOn : ContinuousOn v (Set.uIcc (x / 2) x) := by
      rw [Set.uIcc_of_le hle]
      exact hvcont.mono (fun y hy => lt_of_lt_of_le ha hy.1)
    have hvint : IntervalIntegrable v volume (x / 2) x := hvcontOn.intervalIntegrable
    have hvA : ContinuousAt v x := hvcont.continuousAt (Ioi_mem_nhds hx)
    have hsm : StronglyMeasurableAtFilter v (𝓝 x) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun y hy => hvcont.continuousAt (Ioi_mem_nhds hy)) x hx
    have hFTC := intervalIntegral.integral_hasDerivAt_right hvint hsm hvA
    have hmain : HasDerivAt (fun z => u (x / 2) + ∫ r in (x / 2)..z, v r) (v x) x :=
      hFTC.const_add (u (x / 2))
    exact hmain.congr_of_eventuallyEq
      (eventually_of_mem (Icc_mem_nhds hax (by linarith)) hueq)
  have hv_deriv : ∀ x : ℝ, 0 < x →
      HasDerivAt v ((-(5 + α) / (α * x)) * v x) x := by
    intro x hx
    have ha : 0 < x / 2 := by linarith
    have hax : x / 2 < x := by linarith
    have hle : x / 2 ≤ x := le_of_lt hax
    have hveq : Set.EqOn v
        (fun z => v (x / 2) + ∫ r in (x / 2)..z, (-(5 + α) / (α * r)) * v r)
        (Set.Icc (x / 2) (2 * x)) := by
      intro z hz
      have h := hchain1 (x / 2) z ha hz.1
      show v z = v (x / 2) + ∫ r in (x / 2)..z, (-(5 + α) / (α * r)) * v r
      linarith
    have hgcontOn : ContinuousOn (fun r : ℝ => (-(5 + α) / (α * r)) * v r)
        (Set.uIcc (x / 2) x) := by
      rw [Set.uIcc_of_le hle]
      exact hgcont.mono (fun y hy => lt_of_lt_of_le ha hy.1)
    have hgint : IntervalIntegrable (fun r : ℝ => (-(5 + α) / (α * r)) * v r)
        volume (x / 2) x := hgcontOn.intervalIntegrable
    have hgA : ContinuousAt (fun r : ℝ => (-(5 + α) / (α * r)) * v r) x :=
      hgcont.continuousAt (Ioi_mem_nhds hx)
    have hsm : StronglyMeasurableAtFilter (fun r : ℝ => (-(5 + α) / (α * r)) * v r)
        (𝓝 x) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun y hy => hgcont.continuousAt (Ioi_mem_nhds hy)) x hx
    have hFTC := intervalIntegral.integral_hasDerivAt_right hgint hsm hgA
    have hmain : HasDerivAt
        (fun z => v (x / 2) + ∫ r in (x / 2)..z, (-(5 + α) / (α * r)) * v r)
        ((-(5 + α) / (α * x)) * v x) x := hFTC.const_add (v (x / 2))
    exact hmain.congr_of_eventuallyEq
      (eventually_of_mem (Icc_mem_nhds hax (by linarith)) hveq)
  -- ## (G) `u` is `C²` on `(0,∞)` and solves the strong ODE
  have hderivu : Set.EqOn (deriv u) v (Set.Ioi 0) := fun x hx => (hu_deriv x hx).deriv
  have hderivv : Set.EqOn (deriv v) (fun r : ℝ => (-(5 + α) / (α * r)) * v r)
      (Set.Ioi 0) := fun x hx => (hv_deriv x hx).deriv
  have hu_diffOn : DifferentiableOn ℝ u (Set.Ioi 0) :=
    fun x hx => (hu_deriv x hx).differentiableAt.differentiableWithinAt
  have hv_diffOn : DifferentiableOn ℝ v (Set.Ioi 0) :=
    fun x hx => (hv_deriv x hx).differentiableAt.differentiableWithinAt
  have hvC1 : ContDiffOn ℝ 1 v (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (0 : WithTop ℕ∞))
      (f := v) (s := Set.Ioi 0) isOpen_Ioi).mpr
      ⟨hv_diffOn, fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_zero]
    exact hgcont.congr hderivv
  have huC2 : ContDiffOn ℝ 2 u (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (1 : WithTop ℕ∞))
      (f := u) (s := Set.Ioi 0) isOpen_Ioi).mpr
      ⟨hu_diffOn, fun h => absurd h (by simp), ?_⟩
    exact hvC1.congr hderivu
  have hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv u z') z + α * (5 + α) * z * deriv u z = 0 := by
    intro z hz
    have h1 : deriv u z = v z := (hu_deriv z hz).deriv
    have h2 : deriv (fun z' => deriv u z') z = (-(5 + α) / (α * z)) * v z := by
      have hev : (fun z' => deriv u z') =ᶠ[𝓝 z] v :=
        eventually_of_mem (Ioi_mem_nhds hz) hderivu
      rw [Filter.EventuallyEq.deriv_eq hev, (hv_deriv z hz).deriv]
    rw [h1, h2]
    have hαz : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
    have harith : α ^ 2 * z ^ 2 * ((-(5 + α) / (α * z)) * v z)
        = -(α * (5 + α) * z * v z) := by
      field_simp
    rw [harith]
    ring
  exact euler_ode_eq_zero_of_decay_of_zsq hα hα2 huC2 hode hdec hzsq

end Work.FTS.ClassC
