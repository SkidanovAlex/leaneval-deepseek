import Mathlib
import Submission.Work.RadialSpace.EvenHalfDeriv
import Submission.Work.RadialSpace.evenHalfDeriv_eq

/-!
# Iterated derivatives of `s ↦ g (√s)` for even smooth `g`

For an even smooth function `g : ℝ → ℂ` the function `s ↦ g (√s)` (defined on
`s > 0`) has as its `m`-th derivative the `m`-fold half-derivative
`evenHalfDeriv^[m] g` evaluated at `√s`:

`iteratedDeriv m (fun s => g (√s)) s = (evenHalfDeriv^[m] g) (√s)`,  `s > 0`.

This is proved by induction on `m`, the induction step being the chain rule
applied to the identity `deriv (fun s => G (√s)) s = evenHalfDeriv G (√s)`
(`s > 0`) together with the fact that `evenHalfDeriv` preserves smoothness
(`contDiff_evenHalfDeriv`) and evenness (`even_evenHalfDeriv`).

## Main results

* `Work.RadialSpace.contDiff_iterate_evenHalfDeriv`
* `Work.RadialSpace.even_iterate_evenHalfDeriv`
* `Work.RadialSpace.deriv_comp_sqrt_eq`
* `Work.RadialSpace.iteratedDeriv_comp_sqrt`
-/

open Filter Topology
open scoped ContDiff

namespace Work.RadialSpace

/-- The `m`-fold half-derivative of a smooth function is smooth. -/
lemma contDiff_iterate_evenHalfDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ Smooth g) (m : ℕ) :
    ContDiff ℝ Smooth ((evenHalfDeriv^[m]) g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_evenHalfDeriv ih

/-- The `m`-fold half-derivative of an even function is even. -/
lemma even_iterate_evenHalfDeriv {g : ℝ → ℂ} (he : Function.Even g) (m : ℕ) :
    Function.Even ((evenHalfDeriv^[m]) g) := by
  induction m with
  | zero => simpa using he
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact even_evenHalfDeriv ih

/-- The chain rule for `s ↦ G (√s)`: at `s > 0` its derivative is the
half-derivative of `G` evaluated at `√s`. -/
lemma deriv_comp_sqrt_eq {G : ℝ → ℂ} (hG : ContDiff ℝ Smooth G) (hGe : Function.Even G)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun s => G (Real.sqrt s)) t = evenHalfDeriv G (Real.sqrt t) := by
  have ht0 : Real.sqrt t ≠ 0 := by positivity
  have h1 : DifferentiableAt ℝ G (Real.sqrt t) := hG.contDiffAt.differentiableAt (by decide)
  have h2 : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt x) t :=
    (Real.hasDerivAt_sqrt (ne_of_gt ht)).differentiableAt
  have hcomp : deriv (fun s : ℝ => G (Real.sqrt s)) t
      = deriv (fun x : ℝ => Real.sqrt x) t • deriv G (Real.sqrt t) :=
    deriv.scomp t h1 h2
  rw [hcomp, (Real.hasDerivAt_sqrt (ne_of_gt ht)).deriv,
    evenHalfDeriv_eq hG hGe ht0, Complex.real_smul]
  push_cast
  rw [div_eq_mul_inv]
  ring

theorem iteratedDeriv_comp_sqrt {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g)
    (he : Function.Even g) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    iteratedDeriv m (fun s => g (Real.sqrt s)) s =
      (Work.RadialSpace.evenHalfDeriv^[m]) g (Real.sqrt s) := by
  have hmain : ∀ m : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv m (fun s => g (Real.sqrt s)) t =
        (evenHalfDeriv^[m]) g (Real.sqrt t) := by
    intro m
    induction m with
    | zero => intro t _; simp
    | succ m ih =>
        intro t ht
        have heq : iteratedDeriv m (fun s => g (Real.sqrt s)) =ᶠ[𝓝 t]
            fun s => (evenHalfDeriv^[m]) g (Real.sqrt s) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
          exact ih u hu
        rw [iteratedDeriv_succ, heq.deriv_eq]
        rw [deriv_comp_sqrt_eq (contDiff_iterate_evenHalfDeriv hg m)
          (even_iterate_evenHalfDeriv he m) ht]
        rw [Function.iterate_succ_apply']
  exact hmain m s hs

end Work.RadialSpace
