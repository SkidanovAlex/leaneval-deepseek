import Submission.Work.CoreTopology.Winding

/-!
# Compressing disks, Pardon's invariant `I(F, β)` and homotopies

*  `BoundsDiskInComplement P α` says that the closed curve `α` on `F = P.carrier`
   bounds an embedded disk in `ℝ³` whose interior is disjoint from `F`.  Concretely
   the disk is presented as an injective continuous map `e` on the closed unit disk
   `𝔻 ⊂ ℂ`, whose boundary circle maps to `α` and whose open part avoids `F`.
   Discs of this kind are exactly the "compressing discs" of Pardon's definition of
   the invariant `I(F, β)`.
*  `pardonsI P β` is Pardon's `I(F, β)`: the infimum of the intersection counts
   `|α ∩ β|` over closed curves `α` on `F` that are *essential* (nontrivial
   isotopy class, here: nonzero winding vector) and bound a disc disjoint from `F`.
   It is an `ℕ∞`-valued quantity, so that the infimum over a possibly empty family
   and over curves meeting `β` infinitely often are both meaningful.
*  `Homotopic P α β` is homotopy of closed curves inside `F`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

variable {P : ParamTorus}

/-- The point `exp (i θ)` of the unit circle, regarded as an element of the closed
unit disc of `ℂ` (which models the standard embedded 2-disc). -/
def circlePoint (θ : ℝ) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨Complex.exp (θ * Complex.I), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I]⟩

@[simp] theorem circlePoint_coe (θ : ℝ) :
    ((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ) = Complex.exp (θ * Complex.I) := rfl

/-- `e` presents the curve `α` as the boundary of an embedded disc whose interior
is disjoint from `F`: `e` is injective on the closed unit disc, the unit circle maps
to `α`, and points of the open unit disc are not on `F`. -/
def IsBoundingDisk (P : ParamTorus) (α : ClosedCurve P)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3)) : Prop :=
  Function.Injective e ∧
    (∀ θ : ℝ, e (circlePoint θ) = α.γ θ) ∧
    (∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → e z ∉ P.carrier)

/-- The curve `α` on `F` **bounds a disc in the complement of `F`**: there is an
embedded disc in `ℝ³` bounded by `α` whose interior is disjoint from `F`
(Pardon's set `U` of "compressing" loops). -/
def BoundsDiskInComplement (P : ParamTorus) (α : ClosedCurve P) : Prop :=
  ∃ e : C(Metric.closedBall (0 : ℂ) 1, R3), IsBoundingDisk P α e

/-- A closed curve on the torus is **simple** if it is injective on a fundamental period
`[0, 2π)`.  By `2π`-periodicity this is the usual notion of an embedded (simple) closed
curve.  Pardon's invariant `I(F, β)` is a minimum over *simple* loops. -/
def IsSimple (P : ParamTorus) (γ : ClosedCurve P) : Prop :=
  Set.InjOn γ.γ (Set.Ico 0 (2 * Real.pi))

theorem ClosedCurve.range_eq_image (P : ParamTorus) (γ : ClosedCurve P) :
    Set.range γ.γ = γ.γ '' Set.Ico (0 : ℝ) (2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
    refine ⟨t - (n : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      have := (le_div_iff₀ hpos).mp (Int.floor_le (t / (2 * Real.pi)))
      linarith
    · have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (t / (2 * Real.pi)))
      linarith
    · have hper : Function.Periodic γ.γ (2 * Real.pi) := γ.periodic
      have := hper.int_mul n (t - (n : ℝ) * (2 * Real.pi))
      rw [show t - (n : ℝ) * (2 * Real.pi) + (n : ℝ) * (2 * Real.pi) = t from by ring] at this
      exact this.symm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

/-- Homotopy of closed curves on the torus `F` (a continuous family of curves on
`F`, each `2π`-periodic, joining `α` to `β`). -/
def Homotopic (P : ParamTorus) (α β : ClosedCurve P) : Prop :=
  ∃ H : ℝ → ℝ → R3, Continuous (Function.uncurry H) ∧
    (∀ s t : ℝ, H s t ∈ P.carrier) ∧
    (∀ t : ℝ, H 0 t = α.γ t) ∧ (∀ t : ℝ, H 1 t = β.γ t) ∧
    (∀ s t : ℝ, H s (t + 2 * Real.pi) = H s t)

theorem Homotopic.refl (P : ParamTorus) (α : ClosedCurve P) : Homotopic P α α :=
  ⟨fun _ t => α.γ t, α.cont.comp continuous_snd, fun _ t => α.mem t,
    fun _ => rfl, fun _ => rfl, fun _ t => α.periodic t⟩

/-- **Pardon's invariant** `I(F, β)`: following Pardon we take the infimum of the number of
intersection points of `β` with a *simple* closed curve `α` on `F` which is essential
(nonzero winding vector, i.e. a non-trivial isotopy class) and bounds an embedded disc whose
interior is disjoint from `F`.

It is `ℕ∞`-valued; for the standard torus and the standard `(p,q)` curve it equals
`min p q` (see `pardonsI_standard`). -/
noncomputable def pardonsI (P : ParamTorus) (β : ClosedCurve P) : ℕ∞ :=
  ⨅ (α : {α : ClosedCurve P // IsSimple P α ∧ IsEssential P α ∧
      BoundsDiskInComplement P α}),
    Set.encard (Set.range α.1.γ ∩ Set.range β.γ)

/-- `I(F, β)` is a lower bound for the intersection count of every simple compressing
essential loop with `β` (this is the defining property of the infimum). -/
theorem pardonsI_le {β α : ClosedCurve P} (hsimple : IsSimple P α) (hess : IsEssential P α)
    (hb : BoundsDiskInComplement P α) :
    pardonsI P β ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ) := by
  unfold pardonsI
  exact iInf_le (fun α : {α : ClosedCurve P // IsSimple P α ∧ IsEssential P α ∧
      BoundsDiskInComplement P α} =>
      Set.encard (Set.range α.1.γ ∩ Set.range β.γ)) ⟨α, hsimple, hess, hb⟩

/-- Conversely, to show `I(F, β) ≤ n` it suffices to exhibit one simple compressing
essential loop meeting `β` in at most `n` points. -/
theorem pardonsI_le_of_le {β α : ClosedCurve P} (hsimple : IsSimple P α)
    (hess : IsEssential P α) (hb : BoundsDiskInComplement P α) {n : ℕ∞}
    (h : Set.encard (Set.range α.γ ∩ Set.range β.γ) ≤ n) : pardonsI P β ≤ n :=
  le_trans (pardonsI_le hsimple hess hb) h

/-- To show `n ≤ I(F, β)` it suffices to bound the intersection count of *every* simple
compressing essential loop below by `n`. -/
theorem le_pardonsI {β : ClosedCurve P} {n : ℕ∞}
    (h : ∀ α : ClosedCurve P, IsSimple P α → IsEssential P α → BoundsDiskInComplement P α →
      n ≤ Set.encard (Set.range α.γ ∩ Set.range β.γ)) : n ≤ pardonsI P β := by
  unfold pardonsI
  exact le_iInf fun α => h α.1 α.2.1 α.2.2.1 α.2.2.2

end

end Work.CoreTopology
