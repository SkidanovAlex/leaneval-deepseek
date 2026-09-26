import Mathlib
import Submission.Work.Drive.KnotDefs

/-!
# Reparametrising a knot slice by a strictly increasing period-shifting `H`

`IsSmoothKnot` is preserved by precomposition with a `C^∞` (here: analytic) map `g` with
`g (t + period) = g t + period` and everywhere positive derivative.  Consequently, for a
two-parameter family `R` of knots whose parameter is shifted by such an `H`, every slice
`t ↦ R (H t s) s` is again a knot.

The mathematical content is:
* `smooth`/`periodic`/`regular` are immediate from the chain rule and periodicity;
* `injective_on_period` uses that a `period`-periodic map which is injective on `Ico 0 period`
  is injective on *any* half-open interval of length `period` (reduce modulo `period` with
  `⌊·/period⌋`), while a strictly increasing `g` maps `[0, period)` into the interval
  `[g 0, g 0 + period)` of length `period`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- A `period`-periodic map that is injective on `[0, period)` is injective on every
half-open interval `[a, a + period)` of length `period`.

This is the standard "reduce the argument modulo the period" argument: writing
`z = ⌊z/P⌋·P + (z - ⌊z/P⌋·P)` with the second summand in `[0, P)`, an equality `r x = r y`
forces `x - y ∈ Pℤ`; on an interval of length `P` this forces `x = y`. -/
lemma injOn_Ico_add_period {E : Type*} {r : ℝ → E} {P a : ℝ} (hP : 0 < P)
    (hper : Function.Periodic r P) (hinj : Set.InjOn r (Set.Ico (0:ℝ) P)) :
    Set.InjOn r (Set.Ico a (a + P)) := by
  intro x hx y hy hxy
  rw [Set.mem_Ico] at hx hy
  -- reduce `z` into the fundamental domain `[0, P)`
  have hfloor : ∀ z : ℝ, z - ((⌊z / P⌋ : ℤ) : ℝ) * P ∈ Set.Ico (0 : ℝ) P := by
    intro z
    rw [Set.mem_Ico]
    constructor
    · have h1 : (⌊z / P⌋ : ℝ) ≤ z / P := Int.floor_le _
      have h1' : (⌊z / P⌋ : ℝ) * P ≤ z := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hP)
        rwa [div_mul_cancel₀ z (ne_of_gt hP)] at this
      linarith
    · have h2 : z / P < (⌊z / P⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2' : z < ((⌊z / P⌋ : ℝ) + 1) * P := by
        have := mul_lt_mul_of_pos_right h2 hP
        rwa [div_mul_cancel₀ z (ne_of_gt hP)] at this
      nlinarith [h2']
  have hxn : r (x - ((⌊x / P⌋ : ℤ) : ℝ) * P) = r x := hper.sub_int_mul_eq ⌊x / P⌋
  have hym : r (y - ((⌊y / P⌋ : ℤ) : ℝ) * P) = r y := hper.sub_int_mul_eq ⌊y / P⌋
  have heq : x - ((⌊x / P⌋ : ℤ) : ℝ) * P = y - ((⌊y / P⌋ : ℤ) : ℝ) * P :=
    hinj (hfloor x) (hfloor y) (by rw [hxn, hym, hxy])
  -- hence `x - y` is an integer multiple of `P`
  have hdiff : x - y = (((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ)) * P := by
    have : x - y = ((⌊x / P⌋ : ℝ) - (⌊y / P⌋ : ℝ)) * P := by linarith [heq]
    rw [this]; push_cast; ring
  -- but `|x - y| < P` since `x, y` lie in an interval of length `P`
  have habs : |x - y| < P := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hkprod : |(((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ))| * P < P := by
    have h : |x - y| = |(((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ))| * P := by
      rw [hdiff, abs_mul, abs_of_pos hP]
    linarith [h, habs]
  have hk1 : |(((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ))| < 1 :=
    (mul_lt_mul_iff_left₀ hP).mp (by linarith [hkprod])
  have hk0 : ⌊x / P⌋ - ⌊y / P⌋ = 0 := by
    have hlt := (abs_lt.mp hk1)
    have h1 : (-1 : ℤ) < ⌊x / P⌋ - ⌊y / P⌋ := by
      have : ((-1 : ℤ) : ℝ) < (((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ)) := by simpa using hlt.1
      exact_mod_cast this
    have h2 : ⌊x / P⌋ - ⌊y / P⌋ < 1 := by
      have : (((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ)) < ((1 : ℤ) : ℝ) := by simpa using hlt.2
      exact_mod_cast this
    omega
  have hzero : (((⌊x / P⌋ - ⌊y / P⌋ : ℤ) : ℝ)) = 0 := by simp [hk0]
  have : x - y = 0 := by rw [hdiff, hzero, zero_mul]
  exact sub_eq_zero.mp this

/-- Precomposing a knot with a `C^∞` map `g` having `g (t + period) = g t + period` and
everywhere positive derivative again yields a knot. -/
theorem isSmoothKnot_comp_reparam {r : ℝ → Space} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ⊤ g)
    (hgshift : ∀ t : ℝ, g (t + period) = g t + period)
    (hgderiv : ∀ t : ℝ, 0 < deriv g t)
    (h : IsSmoothKnot r) : IsSmoothKnot (fun t : ℝ => r (g t)) where
  smooth := h.smooth.comp hg
  periodic := by
    intro t
    show r (g (t + period)) = r (g t)
    rw [hgshift t]
    exact h.periodic (g t)
  injective_on_period := by
    intro a ha b hb hab
    have hP : 0 < period := by rw [period]; positivity
    have hmono : StrictMono g := strictMono_of_deriv_pos hgderiv
    have hgP : g period = g 0 + period := by simpa using hgshift 0
    -- `g` maps `[0, period)` into an interval of length `period`
    have hmem : ∀ t ∈ Set.Ico (0:ℝ) period, g t ∈ Set.Ico (g 0) (g 0 + period) := by
      intro t ht
      rw [Set.mem_Ico] at ht ⊢
      constructor
      · exact hmono.monotone ht.1
      · have h' : g t < g period := hmono ht.2
        rwa [hgP] at h'
    have hgab : g a = g b :=
      injOn_Ico_add_period hP h.periodic h.injective_on_period (hmem a ha) (hmem b hb) hab
    exact hmono.injective hgab
  regular := by
    intro t
    have hdiffg : DifferentiableAt ℝ g t := hg.differentiable (by simp) t
    have hdiffr : DifferentiableAt ℝ r (g t) := h.smooth.differentiable (by simp) (g t)
    have hchain : deriv (fun u : ℝ => r (g u)) t = deriv g t • deriv r (g t) :=
      deriv.scomp t hdiffr hdiffg
    rw [velocity, hchain]
    exact smul_ne_zero (ne_of_gt (hgderiv t)) (h.regular (g t))

theorem reparam_slice_knot {R : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space} {H : ℝ → ℝ → ℝ}
    (hR : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2))
    (hk : ∀ s ∈ Set.Icc (0 : ℝ) 1, LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R t s))
    (hHcont : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => H p.1 p.2))
    (hHper : ∀ s t : ℝ, H (t + LeanEval.KnotTheory.Quadrisecant.period) s
      = H t s + LeanEval.KnotTheory.Quadrisecant.period)
    (hHderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, 0 < deriv (fun u : ℝ => H u s) t)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R (H t s) s) := by
  have hHs : ContDiff ℝ ⊤ (fun t : ℝ => H t s) :=
    hHcont.comp ((contDiff_id : ContDiff ℝ ⊤ (id : ℝ → ℝ)).prodMk contDiff_const)
  exact isSmoothKnot_comp_reparam (r := fun t : ℝ => R t s) (g := fun t : ℝ => H t s)
    hHs (fun t => hHper s t) (fun t => hHderiv s hs t) (hk s hs)

end Work.Drive
