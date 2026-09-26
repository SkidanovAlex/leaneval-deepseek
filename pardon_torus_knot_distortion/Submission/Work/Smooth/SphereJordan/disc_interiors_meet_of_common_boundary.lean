import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.no_retraction_disc
import Submission.Work.Smooth.Jordan.All

/-!
# Two embedded discs of the plane with the same boundary have intersecting interiors

Let `f g : 𝔻 → ℂ` be continuous injections of the closed unit disc into the plane which agree on the
boundary circle, `f (e^{iθ}) = g (e^{iθ})`.  Then there are interior points `z`, `w` of `𝔻` with
`f z = g w` (`Work.Smooth.SphereJordan.disc_interiors_meet_of_common_boundary`).

Equivalently: the common boundary circle `C = f (S¹) = g (S¹)` cannot bound two disjoint embedded
discs in the plane — the two discs must share interior points (in fact, as the argument shows, the
open images of the two embeddings coincide).

## The argument (the parity of the "relative winding" of an antipodal loop)

Assume the contrary, so that no interior point of the first disc maps to an interior point of the
second.  Then the continuous function

`W ζ = f ζ - g (-ζ)`

on `𝔻` is **nowhere zero**: for `‖ζ‖ < 1` its two terms lie in the two disjoint open images, while
for `‖ζ‖ = 1` injectivity of `g` together with `ζ ≠ -ζ` gives `g ζ ≠ g (-ζ)` and hence
`f ζ ≠ g (-ζ)`.  Consequently the normalised boundary loop

`λ θ = W (e^{iθ}) / ‖W (e^{iθ})‖ ∈ S¹`

extends over the disc (by `ζ ↦ W ζ / ‖W ζ‖`), so by the monodromy statement
`Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle` — "a loop which extends over the
disc has all its lifts closed" — every continuous lift `Λ : ℝ → ℝ` of `λ` satisfies `Λ (2π) = Λ 0`.

On the other hand the loop `λ` is **antipodal**: `λ (θ + π) = - λ θ`, because
`W (e^{i(θ+π)}) = - W (e^{iθ})` (the boundary parametrisation of `-ζ` is `θ + π`, and the two
boundary parametrisations of `f` and `g` agree).  For an antipodal loop, `Λ (θ + π) - Λ θ - π` is a
continuous `ℝ`-valued function with values in `2πℤ`, hence constant, equal to `2πk` for some
`k : ℤ`.  Therefore

`Λ (2π) - Λ 0 = [Λ (2π) - Λ π] + [Λ π - Λ 0] = 2π (1 + 2k) ≠ 0`,

an **odd** multiple of `2π`, contradicting `Λ (2π) = Λ 0`.

This is the parity (Borsuk–Ulam) form of the Jordan curve theorem, and it uses only the covering
space `ℝ → S¹` — no Jordan–Schoenflies input.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The antipodal map of the disc -/

/-- The antipodal map `ζ ↦ -ζ` on the model disc. -/
def discNeg (z : Disc) : Disc :=
  ⟨-(z : ℂ), by
    have h := z.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg]
    exact h⟩

@[simp] theorem discNeg_coe (z : Disc) : ((discNeg z : Disc) : ℂ) = -(z : ℂ) := rfl

theorem norm_discNeg (z : Disc) : ‖((discNeg z : Disc) : ℂ)‖ = ‖((z : Disc) : ℂ)‖ := by
  rw [discNeg_coe, norm_neg]

theorem continuous_discNeg : Continuous discNeg :=
  Continuous.subtype_mk (f := fun z : Disc => -(z : ℂ)) (by fun_prop) (fun z => (discNeg z).2)

theorem discNeg_involutive (z : Disc) : discNeg (discNeg z) = z := by
  apply Subtype.ext; rw [discNeg_coe, discNeg_coe, neg_neg]

theorem continuous_circlePoint : Continuous (circlePoint : ℝ → Disc) :=
  Continuous.subtype_mk (f := fun θ : ℝ => Complex.exp (θ * Complex.I))
    (by fun_prop) (fun θ => (circlePoint θ).2)

/-! ## `e^{i(θ+π)} = - e^{iθ}` -/

theorem circlePoint_add_pi (θ : ℝ) : (circlePoint (θ + Real.pi) : ℂ) = -(circlePoint θ : ℂ) := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  have hc : ((θ + Real.pi : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [hc, Complex.exp_add, Complex.exp_pi_mul_I]; ring

theorem circlePoint_add_pi_eq_neg (θ : ℝ) : circlePoint (θ + Real.pi) = discNeg (circlePoint θ) :=
  Subtype.ext (circlePoint_add_pi θ)

theorem discNeg_circlePoint_add_pi (θ : ℝ) :
    discNeg (circlePoint (θ + Real.pi)) = circlePoint θ := by
  rw [circlePoint_add_pi_eq_neg, discNeg_involutive]

theorem circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  rw [Circle.coe_exp]
  simpa using Complex.exp_pi_mul_I

/-! ## The theorem -/

theorem disc_interiors_meet_of_common_boundary {f g : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hbd : ∀ θ : ℝ, f (Work.Smooth.SphereJordan.circlePoint θ) = g (Work.Smooth.SphereJordan.circlePoint θ)) :
    ∃ z w : Work.Smooth.SphereJordan.Disc,
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 ∧
      ‖((w : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 ∧ f z = g w := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ z w, ‖z‖ < 1 → ‖w‖ < 1 → f z ≠ g w`.
  -- The nowhere-zero function `W ζ = f ζ - g (-ζ)`.
  set W : Disc → ℂ := fun ζ => f ζ - g (discNeg ζ) with hWdef
  have hWcont : Continuous W := f.continuous.sub (g.continuous.comp continuous_discNeg)
  have hWne : ∀ ζ : Disc, W ζ ≠ 0 := by
    intro ζ
    rw [hWdef]
    simp only
    rw [sub_ne_zero]
    intro heq
    by_cases hζ : ‖((ζ : Disc) : ℂ)‖ < 1
    · -- both arguments are interior points, lying in the two disjoint open images
      exact hcon ζ (discNeg ζ) hζ (by rw [norm_discNeg]; exact hζ) heq
    · -- `ζ` is a boundary point: `ζ ≠ -ζ`, and `f` and `g` agree on the boundary
      have hle : ‖((ζ : Disc) : ℂ)‖ ≤ 1 := by
        have h := ζ.2
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h; exact h
      have hζ1 : ‖((ζ : Disc) : ℂ)‖ = 1 := le_antisymm hle (not_lt.mp hζ)
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq ζ hζ1
      have h1 : f ζ = g ζ := by rw [← hθ]; exact hbd θ
      have h2 : g ζ = g (discNeg ζ) := by rw [← h1]; exact heq
      have h3 : ζ = discNeg ζ := hg h2
      have h4 : ((ζ : Disc) : ℂ) = -((ζ : Disc) : ℂ) := by
        have := congrArg (fun w : Disc => ((w : Disc) : ℂ)) h3
        simpa using this
      have h5 : ((ζ : Disc) : ℂ) = 0 := by linear_combination h4 / 2
      rw [h5] at hζ1
      norm_num at hζ1
  -- the normalised boundary loop
  let lam : C(ℝ, Circle) :=
    ⟨fun θ => Work.CoreTopology.normCircle (W (circlePoint θ)) (hWne (circlePoint θ)),
      Work.CoreTopology.continuous_normCircle (fun θ => W (circlePoint θ))
        (hWcont.comp continuous_circlePoint) (fun θ => hWne _)⟩
  -- it extends over the disc, so all its lifts are closed
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (lam 0)
  obtain ⟨Λ, hΛspec, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (A := ℝ) lam 0 e₀ he₀
  have hΛlift : ∀ t : ℝ, Circle.exp (Λ t) = lam t := fun t => congr_fun hΛspec.2 t
  have hclosed : Λ (2 * Real.pi) = Λ 0 :=
    Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle W hWcont hWne Λ
      Λ.continuous (fun t => (hΛlift t).symm)
  -- the loop is antipodal, because `W` changes sign under `ζ ↦ -ζ`
  have hWneg : ∀ θ : ℝ, W (circlePoint (θ + Real.pi)) = - W (circlePoint θ) := by
    intro θ
    rw [hWdef]
    simp only
    rw [discNeg_circlePoint_add_pi θ, ← circlePoint_add_pi_eq_neg θ]
    rw [hbd (θ + Real.pi), hbd θ]
    ring
  have hodd : ∀ θ : ℝ, lam (θ + Real.pi) = - lam θ := by
    intro θ
    apply Subtype.ext
    change W (circlePoint (θ + Real.pi)) / (↑‖W (circlePoint (θ + Real.pi))‖ : ℂ) =
      -(W (circlePoint θ) / (↑‖W (circlePoint θ)‖ : ℂ))
    rw [hWneg θ, norm_neg, neg_div]
  -- `Λ (θ + π) - Λ θ - π` is continuous with values in `2πℤ`, hence constant
  have hφcont : Continuous (fun θ : ℝ => Λ (θ + Real.pi) - Λ θ - Real.pi) := by fun_prop
  have hφint : ∀ θ : ℝ, ∃ k : ℤ,
      (Λ (θ + Real.pi) - Λ θ - Real.pi) = (k : ℝ) * (2 * Real.pi) := by
    intro θ
    apply Circle.exp_eq_one.mp
    have h1 : Circle.exp (Λ (θ + Real.pi) - Λ θ) = -1 := by
      rw [show Λ (θ + Real.pi) - Λ θ = Λ (θ + Real.pi) + (-(Λ θ)) from by ring]
      rw [Circle.exp_add, Circle.exp_neg, hΛlift (θ + Real.pi), hΛlift θ, hodd θ]
      rw [neg_mul, mul_inv_cancel]
    rw [show Λ (θ + Real.pi) - Λ θ - Real.pi =
      (Λ (θ + Real.pi) - Λ θ) + (-Real.pi) from by ring]
    rw [Circle.exp_add, h1, Circle.exp_neg, circle_exp_pi]
    simp
  obtain ⟨k, hk⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
      (fun θ : ℝ => Λ (θ + Real.pi) - Λ θ - Real.pi) hφcont hφint
  -- the resulting jump is an odd multiple of `2π`, hence nonzero
  have hkπ : Λ (2 * Real.pi) - Λ Real.pi = Real.pi + (k : ℝ) * (2 * Real.pi) := by
    have h := hk Real.pi
    rw [show Real.pi + Real.pi = 2 * Real.pi from by ring] at h
    linarith
  have hk0 : Λ Real.pi - Λ 0 = Real.pi + (k : ℝ) * (2 * Real.pi) := by
    have h := hk 0
    simp only [zero_add] at h
    linarith
  have hkey : Λ (2 * Real.pi) - Λ 0 = 2 * Real.pi + 2 * (k : ℝ) * (2 * Real.pi) := by
    linarith [hkπ, hk0]
  have hne : Λ (2 * Real.pi) - Λ 0 ≠ 0 := by
    rw [hkey]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hk' : (1 + 2 * (k : ℝ)) ≠ 0 := by
      have h1 : ((1 + 2 * k : ℤ) : ℝ) ≠ 0 := by
        have : (1 + 2 * k : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      have hc : (1 + 2 * (k : ℝ)) = ((1 + 2 * k : ℤ) : ℝ) := by push_cast; ring
      rw [hc]; exact h1
    have hfac : (2 * Real.pi + 2 * (k : ℝ) * (2 * Real.pi) : ℝ) =
        (2 * Real.pi) * (1 + 2 * (k : ℝ)) := by ring
    rw [hfac]
    exact mul_ne_zero hπ hk'
  exact hne (sub_eq_zero.mpr hclosed)

end

end Work.Smooth.SphereJordan
