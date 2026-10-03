/-
# From finitely supported estimates to `ℓ^p` inputs, for `T` defined on bounded functions

Area `A5` produces the minor-arc estimate for *finitely supported* inputs, because that is the
form in which the interpolation machinery of `Work.Analysis.Interpolation` applies.  The
counterpart for `ℓ^p` inputs is `Work.KMTAreas.A5.extendToAll`; this file records the variant
needed when the pointwise convergence hypothesis on `T` is only available for **bounded**
inputs (which is the case for the truncation argument of area A5, where `T` is only defined via
an absolutely convergent convolution on bounded functions).

The proof is Fatou's lemma for the `ℒ^r` seminorm (`MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`)
applied to the truncations `truncZ K f`; the `MemLp` hypotheses are part of the interface and are
not used.
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

/-- Pointwise domination of a truncation: `‖truncZ K f x‖ ≤ ‖f x‖`. -/
private theorem truncZ_norm_le (K : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    ‖Work.KMTContract.truncZ K f x‖ ≤ ‖f x‖ := by
  rw [Work.KMTContract.truncZ_apply]; split <;> simp

/-- `truncZ K f` is finitely supported. -/
private theorem truncZ_support_finite (K : ℕ) (f : ℤ → ℂ) :
    (Function.support (Work.KMTContract.truncZ K f)).Finite := by
  obtain ⟨s, hs⟩ := Work.KMTContract.finsupp_truncZ K f
  exact s.finite_toSet.subset (fun x hx => by
    by_contra hxs
    exact hx (hs x hxs))

/-- A finitely supported function is bounded. -/
theorem boundedZ_of_support_finite {u : ℤ → ℂ} (h : (Function.support u).Finite) :
    BoundedZ u := by
  refine boundedZ_of_bound (C := ∑ x ∈ h.toFinset, ‖u x‖) ?_
  intro x
  by_cases hx : u x = 0
  · rw [hx, norm_zero]; positivity
  · have hmem : x ∈ h.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact hx
    exact Finset.single_le_sum (f := fun x => ‖u x‖) (fun i _ => norm_nonneg _) hmem

/-- **Extension of a two-variable `eLpNorm` estimate from finitely supported inputs to all of
`ℓ^p ⊗ ℓ^q`**, for operators whose pointwise convergence along truncations is only known on
bounded inputs.  The `MemLp` hypotheses are not needed (they are part of the interface the
caller uses). -/
theorem extendToAllBdd (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)) {p q r : ENNReal} {M : ENNReal}
    (htend : ∀ f g : ℤ → ℂ, Work.KMTAreas.A5.BoundedZ f → Work.KMTAreas.A5.BoundedZ g →
      ∀ x : ℤ, Filter.Tendsto (fun K : ℕ =>
          T (Work.KMTContract.truncZ K f) (Work.KMTContract.truncZ K g) x)
        Filter.atTop (nhds (T f g x)))
    (hsimple : ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      MeasureTheory.eLpNorm (T f g) r MeasureTheory.Measure.count
        ≤ M * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g q MeasureTheory.Measure.count) :
    ∀ f g : ℤ → ℂ, Work.KMTAreas.A5.BoundedZ f → Work.KMTAreas.A5.BoundedZ g →
      MeasureTheory.MemLp f p MeasureTheory.Measure.count →
      MeasureTheory.MemLp g q MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (T f g) r MeasureTheory.Measure.count
        ≤ M * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g q MeasureTheory.Measure.count := by
  intro f g hf hg _ _
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (hg := by pw_aesm) (u := Filter.atTop)
    (f := fun K : ℕ => fun x : ℤ =>
      T (Work.KMTContract.truncZ K f) (Work.KMTContract.truncZ K g) x)
    (g := fun x : ℤ => T f g x)
    (C := M * eLpNorm f p Measure.count * eLpNorm g q Measure.count) ?_ ?_ ?_
  · -- the finitely supported estimate, uniformly in `K`
    filter_upwards with K
    have h1 : eLpNorm (Work.KMTContract.truncZ K f) p Measure.count ≤ eLpNorm f p Measure.count :=
      eLpNorm_mono (hf := by pw_aesm) (fun x => truncZ_norm_le K f x)
    have h2 : eLpNorm (Work.KMTContract.truncZ K g) q Measure.count ≤ eLpNorm g q Measure.count :=
      eLpNorm_mono (hf := by pw_aesm) (fun x => truncZ_norm_le K g x)
    calc eLpNorm (T (Work.KMTContract.truncZ K f) (Work.KMTContract.truncZ K g)) r Measure.count
        ≤ M * eLpNorm (Work.KMTContract.truncZ K f) p Measure.count *
            eLpNorm (Work.KMTContract.truncZ K g) q Measure.count :=
          hsimple _ _ (truncZ_support_finite K f) (truncZ_support_finite K g)
      _ = M * (eLpNorm (Work.KMTContract.truncZ K f) p Measure.count *
            eLpNorm (Work.KMTContract.truncZ K g) q Measure.count) := mul_assoc _ _ _
      _ ≤ M * (eLpNorm f p Measure.count * eLpNorm g q Measure.count) :=
          mul_le_mul' le_rfl (mul_le_mul' h1 h2)
      _ = M * eLpNorm f p Measure.count * eLpNorm g q Measure.count := (mul_assoc _ _ _).symm
  · -- everything is measurable on the countable discrete space `ℤ`
    intro K
    exact (measurable_of_countable _).aestronglyMeasurable
  · -- the truncations converge pointwise
    exact Filter.Eventually.of_forall (fun x => htend f g hf hg x)

end

end Work.KMTAreas.A5
