import Mathlib
import Submission.Work.Stems.StepI.SqueezeDefs

/-!
# Joint continuity of the first squeeze homotopy

`Work.Stems.StepI.squeezeH` is the family of reparametrisations that squeezes the path
`(γ * rev sg_w) * sg_w` onto `γ`; it is the source of the homotopy `id ≃ sect ∘ triv` of the
fibrewise trivialisation of the path–loop fibration over a set with a path field.  This file proves
that it is **jointly continuous** in `(z, t, s)`, i.e. the statement needed to package the homotopy
as a `ContinuousMap`:

`Continuous (Work.Stems.StepI.squeezeHUnc (x₀ := x₀) sg)`.

The definition of `squeezeH` is a two-fold `if` whose branches use the rational expressions
`t * ((s - hA t) / (hB t - hA t))` and `t * (1 - (s - hB t) / (1 - hB t))`.  These are **not**
continuous at `t = 0` (the denominators `hB t - hA t = t/4` and `1 - hB t = t/2` vanish there), and
`Continuous.if_le` requires each branch to be a globally continuous function.  The two branches
concerned are, however, only ever *taken* in the region `hA t < s` (resp. `hB t < s`), which forces
`t > 0`; there the two expressions simplify to the polynomials `5 - 4s - 3t` and `2s - 1`
(`squeezeH_eq_squeezeHClean`).  Replacing the branch functions by these polynomials gives
`squeezeHClean`, a continuous function which agrees with `squeezeH` on `I × I`, and the piecewise
gluing lemma `Continuous.if_le` finishes.  The hypothesis `sg (w, 1) = w` is exactly what makes the
two branches agree at the junction `s = hA t`.

## Main declarations

* `Work.Stems.StepI.squeezeHClean` — the "polynomialised" version of `squeezeH`.
* `Work.Stems.StepI.squeezeH_eq_squeezeHClean` — the two agree on `I × I`.
* `Work.Stems.StepI.continuous_squeezeHClean_comp` — `squeezeHClean` is jointly continuous, in the
  form needed here (arbitrary parameter space).
* `Work.Stems.StepI.continuous_squeezeHUnc` — **the target**.
-/

open scoped Topology unitInterval

namespace Work.Stems.StepI

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X}

/-! ## The polynomialised branches -/

/-- `squeezeH` with its two non-continuous branch expressions replaced by the polynomials they agree
with on the region where those branches are taken (`squeezeH_eq_squeezeHClean`).  Unlike `squeezeH`
this is manifestly continuous as a function of `(z, t, s)`. -/
def squeezeHClean (sg : C(↥W × I, X)) (z : ↥((evalOne X x₀) ⁻¹' W)) (t s : ℝ) : X :=
  if s ≤ hA t then cmOf z (clampI (s / hA t))
  else if s ≤ hB t then sg (wOf z, clampI (5 - 4 * s - 3 * t))
  else sg (wOf z, clampI (2 * s - 1))

/-- On `I × I` the two objects `squeezeH` and `squeezeHClean` coincide.  The only content is the
algebra `1 - t * ((s - hA t)/(hB t - hA t)) = 5 - 4s - 3t` and
`1 - t * (1 - (s - hB t)/(1 - hB t)) = 2s - 1`, valid on the respective branch regions because there
`s > hA t` (resp. `s > hB t`) forces `t > 0`, so the denominators `t/4` and `t/2` do not vanish. -/
theorem squeezeH_eq_squeezeHClean (sg : C(↥W × I, X)) (z : ↥((evalOne X x₀) ⁻¹' W))
    {t s : ℝ} (ht : t ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) :
    squeezeH sg z t s = squeezeHClean sg z t s := by
  unfold squeezeH squeezeHClean
  by_cases h1 : s ≤ hA t
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    -- the second and third branches force `t > 0`
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · exfalso
        rw [← h, hA_zero] at h1
        linarith [not_le.mp h1, hs.2]
      · exact h
    by_cases h2 : s ≤ hB t
    · rw [if_pos h2, if_pos h2]
      have harg : 1 - t * ((s - hA t) / (hB t - hA t)) = 5 - 4 * s - 3 * t := by
        have hsub : hB t - hA t = t / 4 := hB_sub_hA t
        have htne : t ≠ 0 := ne_of_gt htpos
        rw [hsub]
        field_simp
        unfold hA
        ring
      rw [harg]
    · rw [if_neg h2, if_neg h2]
      have harg : 1 - t * (1 - ((s - hB t) / (1 - hB t))) = 2 * s - 1 := by
        have hsub : 1 - hB t = t / 2 := by unfold hB; ring
        have htne : t ≠ 0 := ne_of_gt htpos
        rw [hsub]
        field_simp
        unfold hB
        ring
      rw [harg]

/-! ## Continuity of the polynomialised branches -/

/-- `squeezeHClean`, as a function of a parameter `a` ranging over an arbitrary topological space
through continuous maps `Z`, `T`, `S`, is continuous.  This is the form in which the result is
applied to the projections of the product `(p⁻¹W × I) × I`. -/
theorem continuous_squeezeHClean_comp {α : Type} [TopologicalSpace α]
    (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    {Z : α → ↥((evalOne X x₀) ⁻¹' W)} {T S : α → I}
    (hZ : Continuous Z) (hT : Continuous T) (hS : Continuous S) :
    Continuous fun a => squeezeHClean sg (Z a) (T a : ℝ) (S a : ℝ) := by
  have hF : Continuous fun p : C(I, X) × I => p.1 p.2 := continuous_eval
  have ht : Continuous fun a : α => (T a : ℝ) := continuous_subtype_val.comp hT
  have hs : Continuous fun a : α => (S a : ℝ) := continuous_subtype_val.comp hS
  -- the first branch: `cmOf z` evaluated at `clampI (s / hA t)` (`hA t ≥ 1/4`, so division is safe)
  have hAc : Continuous fun a : α => cmOf (Z a) (clampI ((S a : ℝ) / hA (T a : ℝ))) := by
    refine hF.comp (Continuous.prodMk (continuous_cmOf.comp hZ) ?_)
    exact continuous_clampI.comp (Continuous.div hs (continuous_hA.comp ht)
      (fun a => ne_of_gt (hA_pos (T a).2.2)))
  -- the second branch
  have hBc : Continuous fun a : α =>
      sg (wOf (Z a), clampI (5 - 4 * (S a : ℝ) - 3 * (T a : ℝ))) := by
    refine sg.continuous.comp (Continuous.prodMk (continuous_wOf.comp hZ) ?_)
    exact continuous_clampI.comp (by fun_prop)
  -- the third branch
  have hCc : Continuous fun a : α => sg (wOf (Z a), clampI (2 * (S a : ℝ) - 1)) := by
    refine sg.continuous.comp (Continuous.prodMk (continuous_wOf.comp hZ) ?_)
    exact continuous_clampI.comp (by fun_prop)
  -- the inner piecewise definition; the junction is `s = hB t`, where both arguments are `1 - t`
  have hBC : Continuous fun a : α =>
      if (S a : ℝ) ≤ hB (T a : ℝ) then
        sg (wOf (Z a), clampI (5 - 4 * (S a : ℝ) - 3 * (T a : ℝ)))
      else sg (wOf (Z a), clampI (2 * (S a : ℝ) - 1)) := by
    refine Continuous.if_le hBc hCc hs (continuous_hB.comp ht) ?_
    intro a ha
    have harg : 5 - 4 * (S a : ℝ) - 3 * (T a : ℝ) = 2 * (S a : ℝ) - 1 := by
      rw [ha]; unfold hB; ring
    rw [harg]
  show Continuous fun a : α =>
      if (S a : ℝ) ≤ hA (T a : ℝ) then cmOf (Z a) (clampI ((S a : ℝ) / hA (T a : ℝ)))
      else if (S a : ℝ) ≤ hB (T a : ℝ) then
        sg (wOf (Z a), clampI (5 - 4 * (S a : ℝ) - 3 * (T a : ℝ)))
      else sg (wOf (Z a), clampI (2 * (S a : ℝ) - 1))
  -- the outer piecewise definition; at the junction `s = hA t` the first branch is `w` and the
  -- second is `sg (w, 1) = w`, which is where `hsg1` is used
  refine Continuous.if_le hAc hBC hs (continuous_hA.comp ht) ?_
  intro a ha
  have hle : (S a : ℝ) ≤ hB (T a : ℝ) := by
    rw [ha]; exact hA_le_hB (T a).2.1
  rw [if_pos hle]
  have hne : hA (T a : ℝ) ≠ 0 := ne_of_gt (hA_pos (T a).2.2)
  have h1 : (S a : ℝ) / hA (T a : ℝ) = 1 := by rw [ha, div_self hne]
  have h2 : 5 - 4 * (S a : ℝ) - 3 * (T a : ℝ) = 1 := by
    rw [ha]; unfold hA; ring
  rw [h1, h2, clampI_one, cmOf_one, hsg1]

/-! ## The target -/

theorem continuous_squeezeHUnc {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X}
    (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    Continuous (Work.Stems.StepI.squeezeHUnc (x₀ := x₀) sg) := by
  have hcomp := continuous_squeezeHClean_comp (x₀ := x₀) (W := W) sg hsg1
    (α := (↥((evalOne X x₀) ⁻¹' W) × I) × I)
    (Z := fun q => q.1.1) (T := fun q => q.1.2) (S := fun q => q.2)
    (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd
  have heq : (fun q : (↥((evalOne X x₀) ⁻¹' W) × I) × I => squeezeHUnc (x₀ := x₀) sg q) =
      fun q => squeezeHClean sg q.1.1 (q.1.2 : ℝ) (q.2 : ℝ) := by
    funext q
    exact squeezeH_eq_squeezeHClean sg q.1.1 q.1.2.2 q.2.2
  show Continuous fun q : (↥((evalOne X x₀) ⁻¹' W) × I) × I => squeezeHUnc (x₀ := x₀) sg q
  rw [heq]
  exact hcomp

end

end Work.Stems.StepI
