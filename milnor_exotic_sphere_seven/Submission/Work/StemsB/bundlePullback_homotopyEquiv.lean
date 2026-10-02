import Mathlib
import Submission.Work.StemsB.BundlePullback
import Submission.Work.StemsB.isSerreFibration_evalOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The path–loop fibration is trivial over a based-contractible parameter space (explicitly)

For `X` a topological space, `x₀ : X`, `D` a topological space with a *based* contraction
`c : C(D × I, D)` to `d₀` (`hc0 : c (u,0) = u`, `hc1 : c (u,1) = d₀`, `hcb : c (d₀,t) = d₀`), the
pullback `Work.StemsB.bundlePullback X x₀ D s` of the path–loop fibration `evalOne X x₀` over
`s : C(D, X)` has the fibre over `d₀` — the space `Path x₀ (s d₀)` of paths from `x₀` to `s d₀` — as
a homotopy retract, via the explicit maps

* `Φ (u,γ) = γ * (t ↦ s (c (u,t)))` (`bundleTransportMap`),
* `Ψ δ = (d₀, δ)` (`bundleSectionMap`),

both homotopies being written out on the nose.  This is the transcription of
`Work.StemsB.cubePullback_homotopyEquiv` to an arbitrary parameter space `D` (the cube `I^n` of that
statement being replaced by `D`); no structure of `D` beyond its topology is used.

## Main declarations

* `Work.StemsB.bundleTransportFun`, `Work.StemsB.bundleTransportMap` — `Φ`.
* `Work.StemsB.bundleSectionMap` — `Ψ`.
* `Work.StemsB.bundleHomotopyRight` — the homotopy `Ψ ∘ Φ ≃ id`.
* `Work.StemsB.bundleHomotopyLeft` — the homotopy `Φ ∘ Ψ ≃ id`.
* `Work.StemsB.bundlePullback_homotopyEquiv` — `bundlePullback X x₀ D s ≃ₕ Path x₀ (s d₀)`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {D : Type} [TopologicalSpace D]
variable {s : C(D, X)} {d₀ : D} {c : C(D × I, D)} {hc0 : ∀ u, c (u, 0) = u}

/-! ## Continuity of the data of the pullback -/

theorem continuous_bundlePullback_fst :
    Continuous fun p : bundlePullback X x₀ D s => p.1.1 := by
  fun_prop

theorem continuous_bundlePullback_snd :
    Continuous fun p : bundlePullback X x₀ D s => p.1.2.1 := by
  fun_prop

/-! ## The trivialisation `Φ` -/

/-- The underlying function of the trivialisation `Φ`: the concatenation of `p` (on the first half of
the interval) with the track `t ↦ s (c (p.1, t))` of the contraction. -/
def bundleTransportFun (c : C((D) × I, D)) (p : bundlePullback X x₀ D s) (t : I) : X :=
  if ((2 : ℝ) * (t : ℝ) ≤ 1) then p.1.2.1 (clampI ((2 : ℝ) * (t : ℝ)))
  else s (c (p.1.1, clampI ((2 : ℝ) * (t : ℝ) - 1)))

theorem bundleTransportFun_zero (p : bundlePullback X x₀ D s) : bundleTransportFun c p 0 = x₀ := by
  rw [bundleTransportFun, if_pos (by norm_num : (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1)]
  show p.1.2.1 (clampI ((2 : ℝ) * (((0 : I)) : ℝ))) = x₀
  rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero, clampI_zero]
  exact p.1.2.2

theorem bundleTransportFun_one (hc1 : ∀ u, c (u, 1) = d₀) (p : bundlePullback X x₀ D s) :
    bundleTransportFun c p 1 = s d₀ := by
  rw [bundleTransportFun, if_neg (by norm_num : ¬ ((2 : ℝ) * (((1 : I)) : ℝ) ≤ 1))]
  show s (c (p.1.1, clampI ((2 : ℝ) * (((1 : I)) : ℝ) - 1))) = s d₀
  have h : (2 : ℝ) * (((1 : I)) : ℝ) - 1 = 1 := by
    rw [show (((1 : I)) : ℝ) = 1 from rfl]; norm_num
  rw [h, clampI_one, hc1 p.1.1]

theorem continuous_bundleTransportFun (hc0 : ∀ u, c (u, 0) = u) :
    Continuous fun q : bundlePullback X x₀ D s × I => bundleTransportFun c q.1 q.2 := by
  unfold bundleTransportFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have h : Continuous fun q : bundlePullback X x₀ D s × I =>
        (q.1.1.2.1, clampI ((2 : ℝ) * (q.2 : ℝ))) :=
      (continuous_bundlePullback_snd.comp continuous_fst).prodMk
        (continuous_clampI.comp (by fun_prop))
    exact continuous_eval.comp h
  · have h : Continuous fun q : bundlePullback X x₀ D s × I =>
        (q.1.1.1, clampI ((2 : ℝ) * (q.2 : ℝ) - 1)) :=
      (continuous_bundlePullback_fst.comp continuous_fst).prodMk
        (continuous_clampI.comp (by fun_prop))
    exact (s.continuous.comp c.continuous).comp h
  · fun_prop
  · fun_prop
  · intro q hq
    have hmul : (2 : ℝ) * (q.2 : ℝ) = 1 := by linarith [hq]
    show q.1.1.2.1 (clampI ((2 : ℝ) * (q.2 : ℝ))) = s (c (q.1.1.1, clampI ((2 : ℝ) * (q.2 : ℝ) - 1)))
    rw [hmul, clampI_one, sub_self, clampI_zero]
    show q.1.1.2.1 1 = s (c (q.1.1.1, 0))
    have h1 : q.1.1.2.1 1 = s q.1.1.1 := mem_bundlePullback q.1
    rw [h1, hc0 q.1.1.1]

/-! ## The two maps -/

/-- The trivialisation `Φ : bundlePullback X x₀ D s → Path x₀ (s d₀)`. -/
def bundleTransportMap (c : C((D) × I, D)) (hc0 : ∀ u, c (u, 0) = u)
    (hc1 : ∀ u, c (u, 1) = d₀) : C(bundlePullback X x₀ D s, Path x₀ (s d₀)) where
  toFun p :=
    { toContinuousMap :=
        ⟨fun t => bundleTransportFun c p t,
          (continuous_bundleTransportFun hc0).comp (continuous_const.prodMk continuous_id)⟩
      source' := bundleTransportFun_zero p
      target' := bundleTransportFun_one hc1 p }
  continuous_toFun := Path.continuous_uncurry_iff.mp (continuous_bundleTransportFun hc0)

/-- The section `Ψ : Path x₀ (s d₀) → bundlePullback X x₀ D s`, `δ ↦ (d₀, δ)`. -/
def bundleSectionMap : C(Path x₀ (s d₀), bundlePullback X x₀ D s) where
  toFun δ := ⟨(d₀, ⟨δ.toContinuousMap, δ.source'⟩), δ.target'⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_const.prodMk ?_
    exact Continuous.subtype_mk continuous_induced_dom _

@[simp]
theorem bundleSectionMap_apply (δ : Path x₀ (s d₀)) :
    bundleSectionMap (s := s) (d₀ := d₀) δ = ⟨(d₀, ⟨δ.toContinuousMap, δ.source'⟩), δ.target'⟩ := rfl

/-! ## The homotopy `Ψ ∘ Φ ≃ id` -/

/-- The underlying function of the homotopy from `Ψ (Φ p)` to `p` in the pullback. -/
def bundleHomotopyRightFun (c : C((D) × I, D))
    (r : I) (p : bundlePullback X x₀ D s) (t : I) : X :=
  if ((2 : ℝ) * (t : ℝ) ≤ 1 + (r : ℝ)) then
    p.1.2.1 (clampI ((2 : ℝ) * (t : ℝ) / (1 + (r : ℝ))))
  else s (c (p.1.1, clampI ((2 : ℝ) * (t : ℝ) - 1 - (r : ℝ))))

theorem bundleHomotopyRightFun_zero (r : I) (p : bundlePullback X x₀ D s) :
    bundleHomotopyRightFun c r p 0 = x₀ := by
  rw [bundleHomotopyRightFun,
    if_pos (by rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero]; linarith [r.2.1])]
  show p.1.2.1 (clampI ((2 : ℝ) * (((0 : I)) : ℝ) / (1 + (r : ℝ)))) = x₀
  rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero, zero_div, clampI_zero]
  exact p.1.2.2

theorem bundleHomotopyRightFun_one (hc0 : ∀ u, c (u, 0) = u) (r : I) (p : bundlePullback X x₀ D s) :
    bundleHomotopyRightFun c r p 1 = s (c (p.1.1, clampI (1 - (r : ℝ)))) := by
  rw [bundleHomotopyRightFun]
  by_cases hr : ((1 : I) : ℝ) ≤ r
  · -- then `r = 1` and both sides are `s p.1`
    rw [if_pos (by rw [show (((1 : I)) : ℝ) = 1 from rfl] at *; norm_num; linarith)]
    have hr1 : (r : ℝ) = 1 := le_antisymm r.2.2 hr
    have hdiv : (2 : ℝ) * (((1 : I)) : ℝ) / (1 + (r : ℝ)) = 1 := by
      rw [show (((1 : I)) : ℝ) = 1 from rfl, hr1]; norm_num
    rw [hdiv, clampI_one]
    have hpt : p.1.2.1 (1 : I) = s p.1.1 := mem_bundlePullback p
    rw [hpt]
    congr 1
    rw [show (1 : ℝ) - (r : ℝ) = 0 by rw [hr1]; norm_num, clampI_zero]
    exact (hc0 p.1.1).symm
  · -- then `2 < 1 + r` fails, so we are in the second branch
    rw [if_neg (by
      rw [show (((1 : I)) : ℝ) = 1 from rfl] at hr ⊢
      push Not at hr
      intro h
      linarith)]
    congr 1
    congr 1
    rw [show (((1 : I)) : ℝ) = 1 from rfl]
    ring_nf

theorem continuous_bundleHomotopyRightFun (hc0 : ∀ u, c (u, 0) = u) :
    Continuous fun w : (I × bundlePullback X x₀ D s) × I => bundleHomotopyRightFun c w.1.1 w.1.2 w.2 := by
  unfold bundleHomotopyRightFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have h : Continuous fun w : (I × bundlePullback X x₀ D s) × I =>
        (w.1.2.1.2.1, clampI ((2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ)))) :=
      (continuous_bundlePullback_snd.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_clampI.comp
          (Continuous.div (by fun_prop) (by fun_prop) (fun w => by
            have := w.1.1.2.1; linarith)))
    exact continuous_eval.comp h
  · have h : Continuous fun w : (I × bundlePullback X x₀ D s) × I =>
        (w.1.2.1.1, clampI ((2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ))) :=
      (continuous_bundlePullback_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_clampI.comp (by fun_prop))
    exact (s.continuous.comp c.continuous).comp h
  · fun_prop
  · fun_prop
  · intro w hw
    have hpos : (0 : ℝ) < 1 + (w.1.1 : ℝ) := by have := w.1.1.2.1; linarith
    have h1 : (2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ)) = 1 := by
      rw [hw]; exact div_self (ne_of_gt hpos)
    have h2 : (2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ) = 0 := by linarith
    show w.1.2.1.2.1 (clampI ((2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ))))
      = s (c (w.1.2.1.1, clampI ((2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ))))
    rw [h1, clampI_one, h2, clampI_zero]
    have hpt : w.1.2.1.2.1 (1 : I) = s w.1.2.1.1 := mem_bundlePullback w.1.2
    rw [hpt, hc0 w.1.2.1.1]

/-- The joint continuous map underlying the homotopy from `Ψ (Φ p)` to `p`. -/
def bundleHomotopyRightJoint (hc0 : ∀ u, c (u, 0) = u) :
    C((I × bundlePullback X x₀ D s) × I, X) where
  toFun w := bundleHomotopyRightFun c w.1.1 w.1.2 w.2
  continuous_toFun := continuous_bundleHomotopyRightFun hc0

@[simp]
theorem bundleHomotopyRightJoint_apply (hc0 : ∀ u, c (u, 0) = u)
    (w : (I × bundlePullback X x₀ D s) × I) :
    bundleHomotopyRightJoint (c := c) hc0 w = bundleHomotopyRightFun c w.1.1 w.1.2 w.2 := rfl

/-- The `PathSpace`-valued family underlying the homotopy from `Ψ (Φ p)` to `p`. -/
def bundleHomotopyRightPath (hc0 : ∀ u, c (u, 0) = u) :
    C(I × bundlePullback X x₀ D s, PathSpace X x₀) where
  toFun w := ⟨(bundleHomotopyRightJoint (c := c) hc0).curry w, bundleHomotopyRightFun_zero w.1 w.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (bundleHomotopyRightJoint (c := c) hc0).curry.continuous _

@[simp]
theorem bundleHomotopyRightPath_apply_apply (hc0 : ∀ u, c (u, 0) = u)
    (w : I × bundlePullback X x₀ D s) (t : I) :
    (bundleHomotopyRightPath (c := c) hc0 w).1 t = bundleHomotopyRightFun c w.1 w.2 t := rfl

/-- The homotopy from `Ψ (Φ p)` to `p` in the pullback, exhibiting `Ψ` as a retraction of `Φ`. -/
def bundleHomotopyRight (hc0 : ∀ u, c (u, 0) = u) (hc1 : ∀ u, c (u, 1) = d₀) :
    ContinuousMap.Homotopy (bundleSectionMap.comp (bundleTransportMap c hc0 hc1))
      (ContinuousMap.id (bundlePullback X x₀ D s)) where
  toFun w := ⟨(c (w.2.1.1, clampI (1 - (w.1 : ℝ))), bundleHomotopyRightPath (c := c) hc0 w),
    bundleHomotopyRightFun_one hc0 w.1 w.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (c.continuous.comp ((continuous_bundlePullback_fst.comp continuous_snd).prodMk
      (continuous_clampI.comp (by fun_prop)))).prodMk
      (bundleHomotopyRightPath (c := c) hc0).continuous
  map_zero_left := by
    intro p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show c (p.1.1, clampI (1 - (((0 : I)) : ℝ))) = d₀
      rw [show (((0 : I)) : ℝ) = 0 from rfl, sub_zero, clampI_one]
      exact hc1 p.1.1
    · refine Subtype.ext (ContinuousMap.ext fun t => ?_)
      show bundleHomotopyRightFun c 0 p t = bundleTransportFun c p t
      simp only [bundleHomotopyRightFun, bundleTransportFun]
      norm_num
  map_one_left := by
    intro p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show c (p.1.1, clampI (1 - (((1 : I)) : ℝ))) = p.1.1
      rw [show (((1 : I)) : ℝ) = 1 from rfl, sub_self, clampI_zero]
      exact hc0 p.1.1
    · refine Subtype.ext (ContinuousMap.ext fun t => ?_)
      show bundleHomotopyRightFun c 1 p t = p.1.2.1 t
      rw [bundleHomotopyRightFun, if_pos (by
        rw [show (((1 : I)) : ℝ) = 1 from rfl]
        have := t.2.2; linarith)]
      have h : (2 : ℝ) * (t : ℝ) / (1 + (((1 : I)) : ℝ)) = (t : ℝ) := by
        rw [show (((1 : I)) : ℝ) = 1 from rfl]; norm_num
      rw [h, clampI_coe_I]

/-! ## The homotopy `Φ ∘ Ψ ≃ id` -/

/-- The underlying function of the homotopy from `Φ (Ψ δ)` to `δ`.  This is where the *basedness* of
the contraction at `d₀` (`hcb`) is used (together with `hc0`): at the endpoint `t = 1` both branches
give `s d₀`. -/
def bundleHomotopyLeftFun (c : C((D) × I, D))
    (r : I) (δ : Path x₀ (s d₀)) (t : I) : X :=
  if ((2 : ℝ) * (t : ℝ) ≤ 1 + (r : ℝ)) then
    δ (clampI ((2 : ℝ) * (t : ℝ) / (1 + (r : ℝ))))
  else s (c (d₀, clampI ((2 : ℝ) * (t : ℝ) - 1 - (r : ℝ))))

theorem bundleHomotopyLeftFun_zero (r : I) (δ : Path x₀ (s d₀)) :
    bundleHomotopyLeftFun c r δ 0 = x₀ := by
  have h : (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 + (r : ℝ) := by
    rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero]; linarith [r.2.1]
  rw [bundleHomotopyLeftFun, if_pos h]
  show δ (clampI ((2 : ℝ) * (((0 : I)) : ℝ) / (1 + (r : ℝ)))) = x₀
  rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero, zero_div, clampI_zero]
  exact δ.source'

theorem bundleHomotopyLeftFun_one (hcb : ∀ t, c (d₀, t) = d₀) (r : I) (δ : Path x₀ (s d₀)) :
    bundleHomotopyLeftFun c r δ 1 = s d₀ := by
  have h1I : (((1 : I)) : ℝ) = 1 := rfl
  rw [bundleHomotopyLeftFun]
  by_cases hr : (1 : ℝ) ≤ (r : ℝ)
  · rw [if_pos (by rw [h1I]; linarith)]
    have hr1 : (r : ℝ) = 1 := le_antisymm r.2.2 hr
    have hdiv : (2 : ℝ) * (((1 : I)) : ℝ) / (1 + (r : ℝ)) = 1 := by
      rw [h1I, hr1]; norm_num
    rw [hdiv, clampI_one]
    exact δ.target'
  · rw [if_neg (by rw [h1I]; intro h; linarith)]
    have harg : (2 : ℝ) * (((1 : I)) : ℝ) - 1 - (r : ℝ) = 1 - (r : ℝ) := by
      rw [h1I]; ring
    rw [harg]
    have hmem : (1 - (r : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by have := r.2.2; linarith, by have := r.2.1; linarith⟩
    rw [clampI_of_mem hmem]
    exact congrArg s (hcb ⟨1 - r, hmem⟩)

theorem continuous_bundleHomotopyLeftFun (hc0 : ∀ u, c (u, 0) = u) :
    Continuous fun w : (I × Path x₀ (s d₀)) × I => bundleHomotopyLeftFun c w.1.1 w.1.2 w.2 := by
  unfold bundleHomotopyLeftFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hcw : Continuous fun w : (I × Path x₀ (s d₀)) × I => (w.1.2 : C(I, X)) :=
      (show Continuous (fun y : Path x₀ (s d₀) => (y : C(I, X))) from
        continuous_induced_dom).comp (continuous_snd.comp continuous_fst)
    have hτ : Continuous fun w : (I × Path x₀ (s d₀)) × I =>
        clampI ((2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ))) :=
      continuous_clampI.comp
        (Continuous.div (by fun_prop) (by fun_prop) (fun w => by
          have := w.1.1.2.1; linarith))
    exact continuous_eval.comp (hcw.prodMk hτ)
  · have hc2 : Continuous fun w : (I × Path x₀ (s d₀)) × I =>
        (d₀, clampI ((2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ))) :=
      (continuous_const (y := d₀)).prodMk (continuous_clampI.comp (by fun_prop))
    exact (s.continuous.comp c.continuous).comp hc2
  · fun_prop
  · fun_prop
  · intro w hw
    have hpos : (0 : ℝ) < 1 + (w.1.1 : ℝ) := by have := w.1.1.2.1; linarith
    have h1 : (2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ)) = 1 := by
      rw [hw]; exact div_self (ne_of_gt hpos)
    have h2 : (2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ) = 0 := by linarith
    show w.1.2 (clampI ((2 : ℝ) * (w.2 : ℝ) / (1 + (w.1.1 : ℝ))))
      = s (c (d₀, clampI ((2 : ℝ) * (w.2 : ℝ) - 1 - (w.1.1 : ℝ))))
    rw [h1, clampI_one, h2, clampI_zero]
    show (w.1.2 : C(I, X)) 1 = s (c (d₀, 0))
    rw [show (w.1.2 : C(I, X)) 1 = s d₀ from w.1.2.target', hc0 d₀]

/-- The joint continuous map underlying the homotopy from `Φ (Ψ δ)` to `δ`. -/
def bundleHomotopyLeftJoint (hc0 : ∀ u, c (u, 0) = u) :
    C((I × Path x₀ (s d₀)) × I, X) where
  toFun w := bundleHomotopyLeftFun c w.1.1 w.1.2 w.2
  continuous_toFun := continuous_bundleHomotopyLeftFun hc0

/-- The homotopy `Φ ∘ Ψ ≃ id` on `Path x₀ (s d₀)`. -/
def bundleHomotopyLeft (hc0 : ∀ u, c (u, 0) = u) (hc1 : ∀ u, c (u, 1) = d₀)
    (hcb : ∀ t, c (d₀, t) = d₀) :
    ContinuousMap.Homotopy ((bundleTransportMap c hc0 hc1).comp bundleSectionMap)
      (ContinuousMap.id (Path x₀ (s d₀))) where
  toFun w :=
    { toContinuousMap := (bundleHomotopyLeftJoint (c := c) hc0).curry w
      source' := bundleHomotopyLeftFun_zero w.1 w.2
      target' := bundleHomotopyLeftFun_one hcb w.1 w.2 }
  continuous_toFun :=
    Path.continuous_uncurry_iff.mp (continuous_bundleHomotopyLeftFun (c := c) hc0)
  map_zero_left := by
    intro δ
    ext t
    show bundleHomotopyLeftFun c 0 δ t = bundleTransportFun c (bundleSectionMap δ) t
    simp only [bundleHomotopyLeftFun, bundleTransportFun, bundleSectionMap_apply]
    norm_num
  map_one_left := by
    intro δ
    ext t
    show bundleHomotopyLeftFun c 1 δ t = δ t
    rw [bundleHomotopyLeftFun, if_pos (by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]
      have := t.2.2; linarith)]
    have h : (2 : ℝ) * (t : ℝ) / (1 + (((1 : I)) : ℝ)) = (t : ℝ) := by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; norm_num
    rw [h, clampI_coe_I]

/-- **The path–loop fibration is trivial over a space with a based contraction, explicitly.**
The fibre over `d₀` of the pullback of `evalOne X x₀` over `s : D → X` is a homotopy retract of the
pullback, via the explicit maps `bundleTransportMap` and `bundleSectionMap`. -/
theorem bundlePullback_homotopyEquiv (X : Type) [TopologicalSpace X] (x₀ : X)
    (D : Type) [TopologicalSpace D] (s : ContinuousMap D X) (d₀ : D)
    (c : ContinuousMap (D × unitInterval) D)
    (hc0 : ∀ u, c (u, 0) = u) (hc1 : ∀ u, c (u, 1) = d₀) (hcb : ∀ t, c (d₀, t) = d₀) :
    Nonempty (ContinuousMap.HomotopyEquiv (Work.StemsB.bundlePullback X x₀ D s) (Path x₀ (s d₀))) :=
  ⟨{ toFun := bundleTransportMap c hc0 hc1
     invFun := bundleSectionMap
     left_inv := ⟨bundleHomotopyRight hc0 hc1⟩
     right_inv := ⟨bundleHomotopyLeft hc0 hc1 hcb⟩ }⟩



end

end Work.StemsB
