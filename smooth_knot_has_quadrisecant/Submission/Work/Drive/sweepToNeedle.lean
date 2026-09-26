import Mathlib
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.reparam_slice_knot
import Submission.Work.Drive.gluePsi_facts

/-!
# The reparametrisation helpers of the top end of the chord sweep (minimal restoration)

The module `Submission.Work.Drive.sweepToNeedle` was deleted from the tree by the pruning of
2026-09-25.  It contained a proof of the top-end statement `Work.Drive.sweepToNeedle` (and of its two
"pieces" reductions) together with the elementary helpers used by
`Submission/Work/Drive/sweepToNeedleStrict.lean` — the module that is *actually* used by the top end
of the chord sweep.  The helpers are re-established here; the big top-end statements, which are not
needed by `sweepToNeedleStrict` (nor by anything else in the tree), are not restated.

What is provided (all with their original names, statements and arguments, so that
`sweepToNeedleStrict` compiles again):

* `Work.Drive.deriv_shift` — `deriv (r (· + c)) t = deriv r (t + c)`;
* `Work.Drive.eq_of_eq_add_int_mul` — period reduction for a knot injective on one fundamental
  domain: `f x = f y → ∃ k : ℤ, y = x + k * period`;
* `Work.Drive.isCInfKnot_shift` — `C^∞` knots are closed under time shifts;
* `Work.Drive.isCInfKnot_comp_reparam` — `C^∞` knots are closed under period-shifting
  reparametrisation with positive derivative;
* `Work.Drive.shift_eq_mod` — a `period`-periodic map depends on `c` only through
  `sweepParam c * period`;
* `Work.Drive.interpTheta_smooth`, `Work.Drive.interpTheta_facts` — the joint smoothness and the
  three facts about the interpolation `(p, t) ↦ (1 - p) * Θ t + p * t` of a strictly increasing
  period-shifting `Θ` and the identity, used to interpolate the reparametrisation of the last phase
  of `sweepToNeedleStrict`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The derivative of a shifted function: `deriv (r (· + c)) t = deriv r (t + c)`. -/
theorem deriv_shift (r : ℝ → Space) {c t : ℝ} (hr : DifferentiableAt ℝ r (t + c)) :
    deriv (fun u : ℝ => r (u + c)) t = deriv r (t + c) := by
  have h1 : HasDerivAt (fun y : ℝ => y + c) 1 t := (hasDerivAt_id t).add_const c
  have h2 : HasDerivAt r (deriv r (t + c)) (t + c) := hr.hasDerivAt
  have h3 := h2.scomp t h1
  have h4 := h3.deriv
  rw [show (r ∘ fun y : ℝ => y + c) = (fun y : ℝ => r (y + c)) from funext fun y => rfl] at h4
  simpa only [one_smul] using h4

/-- Reducing a real number into the fundamental domain `[0, period)` by subtracting an integer
multiple of `period`. -/
private lemma sub_floor_mul_mem (hP : 0 < period) (z : ℝ) :
    z - (((⌊z / period⌋ : ℤ)) : ℝ) * period ∈ Set.Ico (0 : ℝ) period := by
  rw [Set.mem_Ico]
  constructor
  · have h1 : (((⌊z / period⌋ : ℤ)) : ℝ) * period ≤ z := by
      have h := mul_le_mul_of_nonneg_right (Int.floor_le (z / period)) hP.le
      rwa [div_mul_cancel₀ z (ne_of_gt hP)] at h
    linarith
  · have h2 : z < ((((⌊z / period⌋ : ℤ)) : ℝ) + 1) * period := by
      have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (z / period)) hP
      rwa [div_mul_cancel₀ z (ne_of_gt hP)] at h
    linarith

/-- Two points with the same image under a map that is `period`-periodic and injective on one
fundamental domain differ by an integer multiple of the period. -/
theorem eq_of_eq_add_int_mul {f : ℝ → Space} (hper : Function.Periodic f period)
    (hinj : Set.InjOn f (Set.Ico (0 : ℝ) period)) {x y : ℝ} (h : f x = f y) :
    ∃ k : ℤ, y = x + (k : ℝ) * period := by
  have hP : 0 < period := period_pos
  have hfx : f (x - (((⌊x / period⌋ : ℤ)) : ℝ) * period) = f x := hper.sub_int_mul_eq ⌊x / period⌋
  have hfy : f (y - (((⌊y / period⌋ : ℤ)) : ℝ) * period) = f y := hper.sub_int_mul_eq ⌊y / period⌋
  have hmx := sub_floor_mul_mem hP x
  have hmy := sub_floor_mul_mem hP y
  have heq : x - (((⌊x / period⌋ : ℤ)) : ℝ) * period
      = y - (((⌊y / period⌋ : ℤ)) : ℝ) * period :=
    hinj hmx hmy (by rw [hfx, hfy, h])
  refine ⟨⌊y / period⌋ - ⌊x / period⌋, ?_⟩
  push_cast
  linarith

/-- A time shift of a `C^∞` knot is again a `C^∞` knot. -/
theorem isCInfKnot_shift {r : ℝ → Space} (h : IsCInfKnot r) (c : ℝ) :
    IsCInfKnot (fun t : ℝ => r (t + c)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.1.comp (by fun_prop)
  · intro t
    show r (t + period + c) = r (t + c)
    rw [show t + period + c = (t + c) + period from by ring, h.2.1]
  · intro a ha b hb hab
    have hmem : ∀ u ∈ Set.Ico (0 : ℝ) period, u + c ∈ Set.Ico c (c + period) := by
      intro u hu
      rw [Set.mem_Ico] at hu ⊢
      constructor <;> linarith [hu.1, hu.2]
    have h' := injOn_Ico_add_period (a := c) period_pos h.2.1 h.2.2.1
      (hmem a ha) (hmem b hb) hab
    linarith
  · intro t
    have hd : HasDerivAt (fun u : ℝ => r (u + c)) (deriv r (t + c)) t := by
      have h1 : HasDerivAt (fun y : ℝ => y + c) 1 t := (hasDerivAt_id t).add_const c
      have h2 : HasDerivAt r (deriv r (t + c)) (t + c) :=
        (h.1.differentiable (by simp) (t + c)).hasDerivAt
      have h3 := h2.scomp t h1
      rw [show (r ∘ fun y : ℝ => y + c) = (fun y : ℝ => r (y + c)) from
        funext fun y => rfl] at h3
      simpa only [one_smul] using h3
    rw [velocity, hd.deriv]
    exact h.2.2.2 (t + c)

/-- Precomposing a `C^∞` knot with a `C^∞` map `g` with `g (t + period) = g t + period` and
everywhere positive derivative again gives a `C^∞` knot. -/
theorem isCInfKnot_comp_reparam {r : ℝ → Space} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgshift : ∀ t : ℝ, g (t + period) = g t + period)
    (hgderiv : ∀ t : ℝ, 0 < deriv g t)
    (h : IsCInfKnot r) : IsCInfKnot (fun t : ℝ => r (g t)) := by
  refine ⟨h.1.comp hg, ?_, ?_, ?_⟩
  · intro t
    show r (g (t + period)) = r (g t)
    rw [hgshift t]
    exact h.2.1 (g t)
  · intro a ha b hb hab
    have hP : 0 < period := period_pos
    have hmono : StrictMono g := strictMono_of_deriv_pos hgderiv
    have hgP : g period = g 0 + period := by simpa using hgshift 0
    have hmem : ∀ t ∈ Set.Ico (0 : ℝ) period, g t ∈ Set.Ico (g 0) (g 0 + period) := by
      intro t ht
      rw [Set.mem_Ico] at ht ⊢
      constructor
      · exact hmono.monotone ht.1
      · have h' : g t < g period := hmono ht.2
        rwa [hgP] at h'
    have hgab : g a = g b :=
      injOn_Ico_add_period hP h.2.1 h.2.2.1 (hmem a ha) (hmem b hb) hab
    exact hmono.injective hgab
  · intro t
    have hdiffg : DifferentiableAt ℝ g t := hg.differentiable (by simp) t
    have hdiffr : DifferentiableAt ℝ r (g t) := h.1.differentiable (by simp) (g t)
    have hchain : deriv (fun u : ℝ => r (g u)) t = deriv g t • deriv r (g t) :=
      deriv.scomp t hdiffr hdiffg
    rw [velocity, hchain]
    exact smul_ne_zero (ne_of_gt (hgderiv t)) (h.2.2.2 (g t))

/-- A `period`-periodic map depends on the translation parameter only through
`sweepParam c * period`, i.e. only through `c` modulo `period`. -/
theorem shift_eq_mod {r : ℝ → Space} (hper : Function.Periodic r period) (c t : ℝ) :
    r (t + c) = r (t + sweepParam c * period) := by
  have hsw : sweepParam c * period = c - (((⌊c / period⌋ : ℤ)) : ℝ) * period := by
    rw [sweepParam, sub_mul, div_mul_cancel₀ c (ne_of_gt period_pos)]
  rw [hsw]
  have hg : Function.Periodic
      (fun z : ℝ => r (z + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period)))) period := by
    intro z
    show r (z + period + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period)))
      = r (z + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period)))
    rw [show z + period + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period))
        = (z + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period))) + period from by ring]
    exact hper _
  have hkey := hg.int_mul_eq ⌊c / period⌋
  rw [show t + c = (((⌊c / period⌋ : ℤ)) : ℝ) * period
      + (t + (c - (((⌊c / period⌋ : ℤ)) : ℝ) * period)) from by ring]
  simpa using hkey

/-- Joint smoothness of the interpolation `(p, t) ↦ (1 - p) * Θ t + p * t`. -/
theorem interpTheta_smooth {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.2) * Θ p.1 + p.2 * p.1) := by
  fun_prop

/-- The three facts about the interpolation `(p, t) ↦ (1 - p) * Θ t + p * t` of a strictly
increasing period-shifting `Θ` with the identity: it is jointly `C¹`, its `t`-derivative is
everywhere positive, and it shifts periods. -/
theorem interpTheta_facts {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ 1 Θ)
    (hΘshift : ∀ t : ℝ, Θ (t + period) = Θ t + period)
    (hΘderiv : ∀ t : ℝ, 0 < deriv Θ t) :
    (ContDiff ℝ 1 (fun p : ℝ × ℝ => (1 - p.2) * Θ p.1 + p.2 * p.1)) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, 0 < deriv (fun u : ℝ => (1 - p) * Θ u + p * u) t) ∧
    (∀ p t : ℝ, (1 - p) * Θ (t + period) + p * (t + period)
      = (1 - p) * Θ t + p * t + period) := by
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · intro p hp t
    have hd : deriv (fun u : ℝ => (1 - p) * Θ u + p * u) t = (1 - p) * deriv Θ t + p := by
      have h1 : HasDerivAt (fun u : ℝ => Θ u) (deriv Θ t) t :=
        ((hΘ.differentiable_one) t).hasDerivAt
      have h2 : HasDerivAt (fun u : ℝ => (1 - p) * Θ u) ((1 - p) * deriv Θ t) t :=
        h1.const_mul (1 - p)
      have h3 : HasDerivAt (fun u : ℝ => p * u) p t := by
        have := (hasDerivAt_id t).const_mul p
        simpa using this
      exact (h2.add h3).deriv
    rw [hd]
    have h1 : 0 ≤ 1 - p := by linarith [hp.2]
    have h2 : 0 ≤ p := hp.1
    rcases lt_or_eq_of_le h1 with hlt | heq
    · have hpos : 0 < (1 - p) * deriv Θ t := mul_pos hlt (hΘderiv t)
      linarith [hpos, h2]
    · have hp1 : p = 1 := by linarith
      rw [hp1]; norm_num
  · intro p t; rw [hΘshift t]; ring

end Work.Drive
