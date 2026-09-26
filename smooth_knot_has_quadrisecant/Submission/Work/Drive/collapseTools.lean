import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.collapseBase
import Submission.Work.Drive.knotSeparation
import Submission.Work.Drive.uniformCurveBounds
import Submission.Work.Drive.spatial_le_slope_mul_dist
import Submission.Work.Drive.knot_tangent_chord_bound

set_option maxHeartbeats 1000000

/-!
# Tools for the collapse-resistance proof (`Work.Drive.collapseResistance`)

This module collects the elementary ingredients of the proof that a short and narrow secant of a
knot close to `r` is topologically trivial:

* `addCircle_dist_eq_shift` — a real parameter can be shifted by a multiple of the period to
  realise the circular distance to another one;
* `noOvershoot_real` / `noOvershoot` — a continuous injective real function on an interval never
  leaves the interval spanned by its endpoint values;
* `image_Icc_subset_min_max` — the intermediate value theorem in interval form;
* `exists_continuous_lift` — a continuous injective map on an interval has a *continuous* inverse on
  its image, hence a continuous `t` with `sig ∘ t = xi`;
* `baseMap_continuousOn` — the base map `q ↦ x` of the window lemma is continuous (strict
  monotonicity plus the intermediate value theorem);
* `sectionLocal` — a curve `C¹`-close to `r` meets every normal fibre of `r` at most once in a
  short window;
* fibre algebra: convex combinations of two points of a normal fibre stay in the fibre.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

/-! ## The period shift -/

/-- **The period shift.**  For all reals `s, x` there is an integer `k` with `|s - k * period - x|`
equal to the circular distance of the classes of `s` and `x` on `AddCircle period`. -/
lemma addCircle_dist_eq_shift (s x : ℝ) :
    ∃ k : ℤ, |s - k * period - x| = dist (s : AddCircle period) (x : AddCircle period) := by
  refine ⟨round (period⁻¹ * (s - x)), ?_⟩
  have h1 : ‖((s - x : ℝ) : AddCircle period)‖
      = |s - x - ↑(round (period⁻¹ * (s - x))) * period| := by
    rw [AddCircle.norm_eq period]
  rw [dist_eq_norm, ← AddCircle.coe_sub period s x, h1]
  congr 1
  ring

/-! ## No overshoot for a continuous injective function on an interval -/

/-- **No overshoot.**  A continuous injective real function on `[a,b]` never leaves the interval
spanned by its values at the two endpoints: if `f` took a value above `max (f a) (f b)` at a point
`u`, the intermediate value theorem applied on `[a,u]` and on `[u,b]` would produce two distinct
preimages of the same value. -/
lemma noOvershoot_real {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b)) (hinj : Set.InjOn f (Set.Icc a b))
    {u : ℝ} (hu : u ∈ Set.Icc a b) :
    f u ∈ Set.Icc (min (f a) (f b)) (max (f a) (f b)) := by
  rw [Set.mem_Icc]
  by_contra h
  rw [not_and_or] at h
  rcases h with h | h
  · -- `¬ (min (f a) (f b) ≤ f u)`, i.e. `f u < min (f a) (f b)`
    have hmin : f u < min (f a) (f b) := not_le.mp h
    have hfa : f u < f a := lt_of_lt_of_le hmin (min_le_left _ _)
    have hfb : f u < f b := lt_of_lt_of_le hmin (min_le_right _ _)
    have hau : a < u := by
      rcases lt_or_eq_of_le hu.1 with h' | h'
      · exact h'
      · rw [← h'] at hfa; exact absurd hfa (lt_irrefl _)
    have hub : u < b := by
      rcases lt_or_eq_of_le hu.2 with h' | h'
      · exact h'
      · rw [h'] at hfb; exact absurd hfb (lt_irrefl _)
    set y : ℝ := (f u + min (f a) (f b)) / 2 with hy
    have hyu : f u < y := by rw [hy]; linarith [min_le_left (f a) (f b)]
    have hya : y < f a := by rw [hy]; linarith [min_le_left (f a) (f b)]
    have hyb : y < f b := by rw [hy]; linarith [min_le_right (f a) (f b)]
    obtain ⟨t₁, ht₁, ht₁y⟩ := (intermediate_value_Ioo' hau.le
      (hcont.mono (Set.Icc_subset_Icc le_rfl hu.2)))
      (show y ∈ Set.Ioo (f u) (f a) from ⟨hyu, hya⟩)
    obtain ⟨t₂, ht₂, ht₂y⟩ := (intermediate_value_Ioo hub.le
      (hcont.mono (Set.Icc_subset_Icc hu.1 le_rfl)))
      (show y ∈ Set.Ioo (f u) (f b) from ⟨hyu, hyb⟩)
    have ht₁mem : t₁ ∈ Set.Icc a b := ⟨ht₁.1.le, le_trans ht₁.2.le hu.2⟩
    have ht₂mem : t₂ ∈ Set.Icc a b := ⟨le_trans hu.1 ht₂.1.le, ht₂.2.le⟩
    exact (ne_of_lt (lt_trans ht₁.2 ht₂.1)) (hinj ht₁mem ht₂mem (by rw [ht₁y, ht₂y]))
  · -- `¬ (f u ≤ max (f a) (f b))`, i.e. `max (f a) (f b) < f u`
    have hmax : max (f a) (f b) < f u := not_le.mp h
    have hfa : f a < f u := lt_of_le_of_lt (le_max_left _ _) hmax
    have hfb : f b < f u := lt_of_le_of_lt (le_max_right _ _) hmax
    have hau : a < u := by
      rcases lt_or_eq_of_le hu.1 with h' | h'
      · exact h'
      · rw [← h'] at hfa; exact absurd hfa (lt_irrefl _)
    have hub : u < b := by
      rcases lt_or_eq_of_le hu.2 with h' | h'
      · exact h'
      · rw [h'] at hfb; exact absurd hfb (lt_irrefl _)
    set y : ℝ := (max (f a) (f b) + f u) / 2 with hy
    have hya : f a < y := by rw [hy]; linarith [le_max_left (f a) (f b)]
    have hyb : f b < y := by rw [hy]; linarith [le_max_right (f a) (f b)]
    have hyu : y < f u := by rw [hy]; linarith
    obtain ⟨t₁, ht₁, ht₁y⟩ := (intermediate_value_Ioo hau.le
      (hcont.mono (Set.Icc_subset_Icc le_rfl hu.2)))
      (show y ∈ Set.Ioo (f a) (f u) from ⟨hya, hyu⟩)
    obtain ⟨t₂, ht₂, ht₂y⟩ := (intermediate_value_Ioo' hub.le
      (hcont.mono (Set.Icc_subset_Icc hu.1 le_rfl)))
      (show y ∈ Set.Ioo (f b) (f u) from ⟨hyb, hyu⟩)
    have ht₁mem : t₁ ∈ Set.Icc a b := ⟨ht₁.1.le, le_trans ht₁.2.le hu.2⟩
    have ht₂mem : t₂ ∈ Set.Icc a b := ⟨le_trans hu.1 ht₂.1.le, ht₂.2.le⟩
    exact (ne_of_lt (lt_trans ht₁.2 ht₂.1)) (hinj ht₁mem ht₂mem (by rw [ht₁y, ht₂y]))

/-- **No overshoot, unit-interval form.**  A continuous injective `f : I → ℝ` never leaves the
interval spanned by `f 0` and `f 1`. -/
lemma noOvershoot {f : I → ℝ} (hcont : Continuous f) (hinj : Function.Injective f) (u : I) :
    f u ∈ Set.Icc (min (f 0) (f 1)) (max (f 0) (f 1)) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hgcont : Continuous (fun t : ℝ => f (Set.projIcc 0 1 h01 t)) :=
    hcont.comp continuous_projIcc
  have hginj : Set.InjOn (fun t : ℝ => f (Set.projIcc 0 1 h01 t)) (Set.Icc (0:ℝ) 1) := by
    intro t ht t' ht' h
    change f (Set.projIcc 0 1 h01 t) = f (Set.projIcc 0 1 h01 t') at h
    have h1 : Set.projIcc 0 1 h01 t = ⟨t, ht⟩ := Set.projIcc_of_mem h01 ht
    have h2 : Set.projIcc 0 1 h01 t' = ⟨t', ht'⟩ := Set.projIcc_of_mem h01 ht'
    rw [h1, h2] at h
    exact congrArg Subtype.val (hinj h)
  have key := noOvershoot_real h01 hgcont.continuousOn hginj u.2
  have eu : Set.projIcc 0 1 h01 (u : ℝ) = u := Set.projIcc_of_mem h01 u.2
  have e0 : Set.projIcc 0 1 h01 (0:ℝ) = (0 : I) := by
    rw [Set.projIcc_of_mem h01 (Set.mem_Icc.mpr ⟨le_rfl, h01⟩)]
    exact Subtype.ext rfl
  have e1 : Set.projIcc 0 1 h01 (1:ℝ) = (1 : I) := by
    rw [Set.projIcc_of_mem h01 (Set.mem_Icc.mpr ⟨h01, le_rfl⟩)]
    exact Subtype.ext rfl
  rw [eu, e0, e1] at key
  exact key

/-- **The intermediate value theorem in interval form.**  A continuous function on `[a,b]` attains
every value between `f a` and `f b`. -/
lemma image_Icc_subset_min_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b)) :
    Set.Icc (min (f a) (f b)) (max (f a) (f b)) ⊆ f '' Set.Icc a b := by
  rcases le_total (f a) (f b) with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact intermediate_value_Icc hab hcont
  · rw [min_eq_right h, max_eq_left h]
    exact intermediate_value_Icc' hab hcont

/-! ## The continuous lift along an injective continuous map -/

/-- **The continuous lift.**  If `sig : ℝ → ℝ` is continuous and injective on `[a,b]`, and
`xi : I → ℝ` is continuous and injective with values in `sig '' [a,b]` and `xi 0 = sig a`,
`xi 1 = sig b`, then there is a continuous injective `t : I → ℝ` with `t (I) ⊆ [a,b]`,
`sig (t u) = xi u`, `t 0 = a` and `t 1 = b`.  The map `t` is `sig⁻¹ ∘ xi`, and `sig⁻¹` is
continuous because `sig` is a continuous bijection from the compact interval `[a,b]` onto its
Hausdorff image. -/
lemma exists_continuous_lift {sig : ℝ → ℝ} {xi : I → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsig : ContinuousOn sig (Set.Icc a b)) (hinjsig : Set.InjOn sig (Set.Icc a b))
    (hxi : Continuous xi) (hinjxi : Function.Injective xi)
    (hmem : ∀ u : I, ∃ x : Set.Icc a b, sig (x : ℝ) = xi u)
    (h0 : xi 0 = sig a) (h1 : xi 1 = sig b) :
    ∃ t : I → ℝ, Continuous t ∧ (∀ u, t u ∈ Set.Icc a b) ∧ (∀ u, sig (t u) = xi u) ∧
      t 0 = a ∧ t 1 = b ∧ Function.Injective t := by
  have hinjS : Function.Injective (fun x : Set.Icc a b => sig (x : ℝ)) := by
    intro x y hxy
    exact Subtype.ext (hinjsig x.2 y.2 hxy)
  have hcontS : Continuous (fun x : Set.Icc a b => sig (x : ℝ)) := hsig.domRestrict
  let e : Set.Icc a b ≃ Set.range (fun x : Set.Icc a b => sig (x : ℝ)) :=
    Equiv.ofInjective _ hinjS
  have hcontE : Continuous ⇑e := by
    have he : ⇑e = fun x : Set.Icc a b =>
        (⟨sig (x : ℝ), x, rfl⟩ : Set.range (fun x : Set.Icc a b => sig (x : ℝ))) := by
      funext x
      exact Equiv.ofInjective_apply _ hinjS x
    rw [he]
    exact Continuous.subtype_mk hcontS (fun x => ⟨x, rfl⟩)
  let Φ : Set.Icc a b ≃ₜ Set.range (fun x : Set.Icc a b => sig (x : ℝ)) :=
    Continuous.homeoOfEquivCompactToT2 (f := e) hcontE
  have hΦval : ∀ x : Set.Icc a b,
      (Φ x : Set.range (fun x : Set.Icc a b => sig (x : ℝ))).1 = sig (x : ℝ) := by
    intro x
    have hx : (Φ x : Set.range (fun x : Set.Icc a b => sig (x : ℝ))) = e x := rfl
    rw [hx]
    exact congrArg Subtype.val (Equiv.ofInjective_apply _ hinjS x)
  let tfun : I → ℝ := fun u => (Φ.symm ⟨xi u, Set.mem_range.mpr (hmem u)⟩ : ℝ)
  have htcont : Continuous tfun :=
    continuous_subtype_val.comp
      (Φ.continuous_symm.comp (Continuous.subtype_mk hxi (fun u => hmem u)))
  have htm : ∀ u : I, tfun u ∈ Set.Icc a b := fun u =>
    (Φ.symm ⟨xi u, Set.mem_range.mpr (hmem u)⟩ : Set.Icc a b).2
  have htx : ∀ u : I, sig (tfun u) = xi u := by
    intro u
    have h := congrArg Subtype.val (Homeomorph.apply_symm_apply Φ ⟨xi u, Set.mem_range.mpr (hmem u)⟩)
    rw [hΦval] at h
    exact h
  have ht0 : tfun 0 = a :=
    hinjsig (htm 0) (Set.mem_Icc.mpr ⟨le_rfl, hab⟩) (by rw [htx 0, h0])
  have ht1 : tfun 1 = b :=
    hinjsig (htm 1) (Set.mem_Icc.mpr ⟨hab, le_rfl⟩) (by rw [htx 1, h1])
  refine ⟨tfun, htcont, htm, htx, ht0, ht1, ?_⟩
  intro u v huv
  apply hinjxi
  rw [← htx u, ← htx v, huv]

/-! ## Fibre algebra -/

/-- A convex combination of two points of the normal fibre
`F x = {z | ⟪z - r x, velocity r x⟫ = 0}` lies in the fibre. -/
lemma inner_fiber_smul_add {r : ℝ → Space} {x : ℝ} {p q : Space}
    (hp : inner ℝ (p - r x) (velocity r x) = 0)
    (hq : inner ℝ (q - r x) (velocity r x) = 0) (v : ℝ) :
    inner ℝ ((1 - v) • p + v • q - r x) (velocity r x) = 0 := by
  have h : (1 - v) • p + v • q - r x = (1 - v) • (p - r x) + v • (q - r x) := by module
  rw [h, inner_add_left, inner_smul_left, inner_smul_left, hp, hq, mul_zero, mul_zero, add_zero]

/-- The difference of two points of a normal fibre is orthogonal to the velocity at the base. -/
lemma inner_fiber_sub_eq_zero {r : ℝ → Space} {x : ℝ} {p q : Space}
    (hp : inner ℝ (p - r x) (velocity r x) = 0)
    (hq : inner ℝ (q - r x) (velocity r x) = 0) :
    inner ℝ (p - q) (velocity r x) = 0 := by
  have h : p - q = (p - r x) - (q - r x) := by abel
  rw [h, inner_sub_left, hp, hq, sub_zero]

/-! ## Continuity of the base map -/

/-- **The base map of the window lemma is continuous.**  On the ball of radius `Θ` around `r a`,
the base `base q` (the unique zero of `y ↦ ⟪q - r y, velocity r y⟫` in the window
`(a - T, a + T)`) is unique by hypothesis and strictly decreasing along the fibre direction; the
sandwich `Φ (x₁ - e) > 0 > Φ (x₁ + e)` together with the intermediate value theorem then gives the
continuity of `base`.

The hypotheses are precisely the conclusions of `Work.Drive.baseMapWindowStrict` (with
`c₀ = t₀ = a`), packaged for the two applications in the collapse-resistance proof (the arc `r'` and
the chord). -/
lemma baseMap_continuousOn {r : ℝ → Space} {T N κ ηb Θ a : ℝ}
    {base : Space → ℝ}
    (hbase : ∀ q : Space, ‖q - r a‖ ≤ Θ →
      base q ∈ Set.Ioo (a - T) (a + T) ∧
        inner ℝ (q - r (base q)) (velocity r (base q)) = 0 ∧
        |base q - a| ≤ N * Θ ∧ ‖q - r (base q)‖ ≤ κ * Θ)
    (huniq : ∀ q : Space, ‖q - r a‖ ≤ Θ → ∀ y : ℝ, y ∈ Set.Ioo (a - T) (a + T) →
      inner ℝ (q - r y) (velocity r y) = 0 → y = base q)
    (hstrict : ∀ q : Space, ‖q - r a‖ ≤ Θ → ∀ y : ℝ, y ∈ Set.Ioo (a - T) (a + T) →
      ∀ z : ℝ, z ∈ Set.Ioo (a - T) (a + T) → y < z →
        inner ℝ (q - r z) (velocity r z) < inner ℝ (q - r y) (velocity r y))
    {vhi : ℝ} (hvhi : 0 < vhi) (hspd : ∀ t : ℝ, ‖velocity r t‖ ≤ vhi)
    (hcontΦ : ∀ q : Space, Continuous fun t : ℝ => inner ℝ (q - r t) (velocity r t)) :
    ContinuousOn base {q : Space | ‖q - r a‖ ≤ Θ} := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hx₁mem : base p ∈ Set.Ioo (a - T) (a + T) := (hbase p hp).1
  have hx₁eq : inner ℝ (p - r (base p)) (velocity r (base p)) = 0 := (hbase p hp).2.1
  have hgap : 0 < T - |base p - a| := by
    have h := Set.mem_Ioo.mp hx₁mem
    have h2 : |base p - a| < T := abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    linarith
  set e : ℝ := min (ε / 2) ((T - |base p - a|) / 2) with he
  have hepos : 0 < e := lt_min (by linarith) (by linarith)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have heT : e + |base p - a| < T := by
    have h := min_le_right (ε / 2) ((T - |base p - a|) / 2)
    linarith
  have hmem_p : base p + e ∈ Set.Ioo (a - T) (a + T) := by
    rw [Set.mem_Ioo]
    have h1 : |base p + e - a| ≤ |base p - a| + |e| := by
      have h2 : base p + e - a = (base p - a) + e := by ring
      rw [h2]; exact abs_add_le _ _
    rw [abs_of_pos hepos] at h1
    have h3 : |base p + e - a| < T := by linarith [h1, heT]
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    constructor <;> linarith
  have hmem_m : base p - e ∈ Set.Ioo (a - T) (a + T) := by
    rw [Set.mem_Ioo]
    have h1 : |base p - e - a| ≤ |base p - a| + e := by
      have h2 : base p - e - a = (base p - a) - e := by ring
      rw [h2]
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_pos hepos]
    have h3 : |base p - e - a| < T := by linarith [h1, heT]
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    constructor <;> linarith
  have hneg : inner ℝ (p - r (base p + e)) (velocity r (base p + e)) < 0 := by
    have h := hstrict p hp (base p) hx₁mem (base p + e) hmem_p (by linarith)
    rw [hx₁eq] at h
    exact h
  have hpos : 0 < inner ℝ (p - r (base p - e)) (velocity r (base p - e)) := by
    have h := hstrict p hp (base p - e) hmem_m (base p) hx₁mem (by linarith)
    rw [hx₁eq] at h
    exact h
  set Δ : ℝ := min (-inner ℝ (p - r (base p + e)) (velocity r (base p + e)))
    (inner ℝ (p - r (base p - e)) (velocity r (base p - e))) with hΔ
  have hΔpos : 0 < Δ := lt_min (by linarith) hpos
  have hΔ1 : Δ ≤ -inner ℝ (p - r (base p + e)) (velocity r (base p + e)) := min_le_left _ _
  have hΔ2 : Δ ≤ inner ℝ (p - r (base p - e)) (velocity r (base p - e)) := min_le_right _ _
  refine ⟨Δ / vhi, by positivity, ?_⟩
  intro q hq hqd
  have hqnorm : ‖q - p‖ < Δ / vhi := by
    rw [dist_eq_norm] at hqd
    exact hqd
  have hbd : ∀ y : ℝ, |inner ℝ (q - r y) (velocity r y) - inner ℝ (p - r y) (velocity r y)|
      ≤ ‖q - p‖ * vhi := by
    intro y
    have hdiff : inner ℝ (q - r y) (velocity r y) - inner ℝ (p - r y) (velocity r y)
        = inner ℝ (q - p) (velocity r y) := by
      rw [← inner_sub_left]
      congr 1
      abel
    rw [hdiff]
    calc |inner ℝ (q - p) (velocity r y)| ≤ ‖q - p‖ * ‖velocity r y‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖q - p‖ * vhi := mul_le_mul_of_nonneg_left (hspd y) (norm_nonneg _)
  have hvhi' : ‖q - p‖ * vhi < Δ := by
    have h := lt_div_iff₀ hvhi |>.mp hqnorm
    linarith
  have hqneg : inner ℝ (q - r (base p + e)) (velocity r (base p + e)) < 0 := by
    have h := (abs_le.mp (hbd (base p + e))).2
    linarith [h, hvhi', hΔ1]
  have hqpos : 0 < inner ℝ (q - r (base p - e)) (velocity r (base p - e)) := by
    have h := (abs_le.mp (hbd (base p - e))).1
    linarith [h, hvhi', hΔ2]
  have hcontq : ContinuousOn (fun y : ℝ => inner ℝ (q - r y) (velocity r y))
      (Set.Icc (base p - e) (base p + e)) := (hcontΦ q).continuousOn
  have h0mem : (0:ℝ) ∈ Set.Icc (inner ℝ (q - r (base p + e)) (velocity r (base p + e)))
      (inner ℝ (q - r (base p - e)) (velocity r (base p - e))) :=
    ⟨hqneg.le, hqpos.le⟩
  obtain ⟨z, hz, hz0⟩ :=
    (intermediate_value_Icc' (by linarith : base p - e ≤ base p + e) hcontq) h0mem
  have hzcoord : |z - base p| ≤ e := by
    rw [Set.mem_Icc] at hz
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hzmem : z ∈ Set.Ioo (a - T) (a + T) := by
    rw [Set.mem_Ioo]
    have h1 : |z - a| ≤ |z - base p| + |base p - a| := by
      have h2 : z - a = (z - base p) + (base p - a) := by ring
      rw [h2]; exact abs_add_le _ _
    have h3 : |z - a| < T := by linarith [h1, hzcoord, heT]
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    constructor <;> linarith
  have hzbase : z = base q := huniq q hq z hzmem hz0
  rw [hzbase] at hzcoord
  rw [Real.dist_eq]
  linarith [hzcoord, heε]

/-! ## The local section property -/

/-- **The local section property.**  For a smooth knot `r` there are `η' > 0` and `ε₁ > 0` such
that every curve `r'` whose velocity is uniformly within `ε₁` of that of `r` meets every normal
fibre `F_x = {z | ⟪z - r x, velocity r x⟫ = 0}` of `r` at most once in the window
`(x - η', x + η')`.  The proof is strict monotonicity of `φ y = ⟪r' y - r x, velocity r x⟫` on the
window, whose derivative `⟪velocity r' y, velocity r x⟫` is bounded below by `c ^ 2 / 2 > 0`. -/
theorem sectionLocal {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ η' : ℝ, 0 < η' ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ r' : ℝ → Space, Differentiable ℝ r' →
        (∀ t : ℝ, ‖velocity r' t - velocity r t‖ < ε₁) →
        ∀ s t x : ℝ, |s - x| ≤ η' → |t - x| ≤ η' →
          inner ℝ (r' s - r x) (velocity r x) = 0 →
          inner ℝ (r' t - r x) (velocity r x) = 0 →
          s = t := by
  obtain ⟨c, hc, hcle⟩ := speedLowerBound hr
  obtain ⟨Lv, hLv, hLvle⟩ := exists_velocity_bound hr
  have hcontv : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  have huc : UniformContinuous (velocity r) :=
    uniformContinuous_velocity hcontv hr.velocity_periodic
  have hc2pos : 0 < c ^ 2 / (4 * Lv) := by positivity
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨ηc, hηcpos, hηc⟩ := huc (c ^ 2 / (4 * Lv)) hc2pos
  refine ⟨ηc / 2, by positivity, c ^ 2 / (4 * Lv), hc2pos, ?_⟩
  intro r' hdiff hclose s t x hs ht hs0 ht0
  set w : Space := velocity r x with hw
  set φ : ℝ → ℝ := fun y => inner ℝ (r' y - r x) w with hφ
  have hderiv : ∀ y : ℝ, HasDerivAt φ (inner ℝ (velocity r' y) w) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => r' y - r x) (velocity r' y) y := by
      simpa [velocity] using (hdiff y).hasDerivAt.sub_const (r x)
    have h2 : HasDerivAt (fun _ : ℝ => w) 0 y := hasDerivAt_const y w
    have h3 := h1.inner ℝ h2
    simpa [hφ, inner_zero_right, add_zero] using h3
  have hwge : c ≤ ‖w‖ := by rw [hw]; exact hcle x
  have hwle : ‖w‖ ≤ Lv := by rw [hw]; exact hLvle x
  have hpos : ∀ y : ℝ, |y - x| ≤ ηc / 2 → 0 < inner ℝ (velocity r' y) w := by
    intro y hy
    have hlt : dist y x < ηc := by
      rw [Real.dist_eq]
      linarith
    have hv : ‖velocity r y - w‖ < c ^ 2 / (4 * Lv) := by
      have h1 := hηc hlt
      rw [dist_eq_norm] at h1
      rwa [← hw] at h1
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hc hwge
    have hKpos : 0 < c ^ 2 / (4 * Lv) := by positivity
    have hKLe : c ^ 2 / (4 * Lv) * Lv = c ^ 2 / 4 := by field_simp
    have hb1 : ‖velocity r y - w‖ * ‖w‖ < c ^ 2 / 4 := by
      have h2 : ‖velocity r y - w‖ * ‖w‖ < (c ^ 2 / (4 * Lv)) * ‖w‖ :=
        mul_lt_mul_of_pos_right hv hwpos
      have h4 := mul_le_mul_of_nonneg_left hwle hKpos.le
      linarith [h2, h4, hKLe]
    have hb2 : ‖velocity r' y - velocity r y‖ * ‖w‖ < c ^ 2 / 4 := by
      have h2 : ‖velocity r' y - velocity r y‖ * ‖w‖ < (c ^ 2 / (4 * Lv)) * ‖w‖ :=
        mul_lt_mul_of_pos_right (hclose y) hwpos
      have h4 := mul_le_mul_of_nonneg_left hwle hKpos.le
      linarith [h2, h4, hKLe]
    have hin1 : -(‖velocity r y - w‖ * ‖w‖) ≤ inner ℝ (velocity r y - w) w := by
      have ha := neg_abs_le (inner ℝ (velocity r y - w) w)
      have hb := abs_real_inner_le_norm (velocity r y - w) w
      linarith [ha, hb]
    have hin2 : -(‖velocity r' y - velocity r y‖ * ‖w‖)
        ≤ inner ℝ (velocity r' y - velocity r y) w := by
      have ha := neg_abs_le (inner ℝ (velocity r' y - velocity r y) w)
      have hb := abs_real_inner_le_norm (velocity r' y - velocity r y) w
      linarith [ha, hb]
    have hw2 : c ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hwge, hc, norm_nonneg w]
    have hsplit : inner ℝ (velocity r' y) w
        = inner ℝ w w + inner ℝ (velocity r y - w) w
          + inner ℝ (velocity r' y - velocity r y) w := by
      have hv' : velocity r' y = w + (velocity r y - w) + (velocity r' y - velocity r y) := by abel
      conv_lhs => rw [hv']
      rw [inner_add_left, inner_add_left]
    rw [hsplit, real_inner_self_eq_norm_sq]
    nlinarith [hw2, hb1, hb2, hin1, hin2, hc]
  have hmono : ∀ s t : ℝ, s < t → |s - x| ≤ ηc / 2 → |t - x| ≤ ηc / 2 → φ s < φ t := by
    intro s t hst hs' ht'
    have hcontOn : ContinuousOn φ (Set.Icc s t) := fun y _ =>
      (hderiv y).continuousAt.continuousWithinAt
    have hmono' := strictMonoOn_of_deriv_pos (convex_Icc s t) hcontOn ?_
    · exact hmono' (Set.left_mem_Icc.mpr hst.le) (Set.right_mem_Icc.mpr hst.le) hst
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y).deriv]
      refine hpos y ?_
      have h1 := abs_le.mp hs'
      have h2 := abs_le.mp ht'
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2, h1.1, h1.2, h2.1, h2.2]
  have hsφ : φ s = 0 := by simpa [hφ, hw] using hs0
  have htφ : φ t = 0 := by simpa [hφ, hw] using ht0
  rcases lt_trichotomy s t with h | h | h
  · have hlt := hmono s t h hs ht
    rw [hsφ, htφ] at hlt
    exact absurd hlt (lt_irrefl 0)
  · exact h
  · have hlt := hmono t s h ht hs
    rw [hsφ, htφ] at hlt
    exact absurd hlt (lt_irrefl 0)

end

end Work.Drive
