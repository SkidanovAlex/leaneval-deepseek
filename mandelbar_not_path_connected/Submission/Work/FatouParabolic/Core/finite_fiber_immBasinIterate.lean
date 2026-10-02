import Mathlib
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Core.injOn_of_simplyConnected_of_noCriticalPoint
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable
import Submission.Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open Set Filter

/-!
# The fibres of an iterate of a polynomial map are finite

The general fact behind `finite_fiber_immBasinIterate` is purely algebraic: a polynomial map of
degree at least two is non-constant, hence has finite fibres, and a composition of maps with
finite fibres again has finite fibres.  Consequently `F^[n] : ℂ → ℂ` has finite fibres for every
iterate, and *a fortiori* so has its restriction `immBasinIterate Ω F hmap n` to any `F`-invariant
set `Ω ⊆ ℂ`, because the coercion `↥Ω → ℂ` is injective.

In particular no dynamical input (boundedness of `Ω`, absence of critical points, relative
closedness in the punctured basin, ...) is needed for the finiteness of the fibres: these
hypotheses are part of the caller's interface (they are what turn the iterate into a *covering*
map), but the finiteness of the fibres is elementary.
-/

/-- **A polynomial map of degree at least two has finite fibres.**

Writing `F = P.eval` with `2 ≤ P.natDegree` (so in particular `P ≠ 0` is non-constant),
Mathlib's `Polynomial.tendstoCofinite_of_natDegree_ne_zero` says that `P.eval` pulls the
cofinite filter back to the cofinite filter, which is exactly the statement that all its fibres
are finite. -/
theorem tendstoCofinite_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) :
    Filter.TendstoCofinite F := by
  obtain ⟨P, hPdeg, hPF⟩ := hF
  have hne : P.natDegree ≠ 0 := by omega
  have h1 : Filter.TendstoCofinite (fun z : ℂ => P.eval z) :=
    Polynomial.tendstoCofinite_of_natDegree_ne_zero P hne
  rw [show F = fun z : ℂ => P.eval z from funext hPF]
  exact h1

/-- **Every iterate of a polynomial map of degree at least two has finite fibres.**

`F^[0] = id` is injective, and `F^[n+1] = F ∘ F^[n]` is a composite of two maps with finite
fibres. -/
theorem tendstoCofinite_iterate_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (n : ℕ) :
    Filter.TendstoCofinite (F^[n]) := by
  have hFc : Filter.TendstoCofinite F :=
    tendstoCofinite_of_isPolynomialMapOfDegreeAtLeastTwo hF
  induction n with
  | zero => simpa using (Filter.TendstoCofinite.id (α := ℂ))
  | succ n ih =>
      have hcomp : F^[n.succ] = F ∘ F^[n] := by
        funext z; simp [Function.comp_apply, Function.iterate_succ_apply']
      rw [hcomp]
      exact Filter.TendstoCofinite.comp (F^[n]) F

/-- The fibre of the `n`-th iterate of a polynomial map of degree at least two over any point is
finite. -/
theorem finite_fiber_iterate_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (n : ℕ) (a : ℂ) :
    ((F^[n]) ⁻¹' {a}).Finite :=
  (Filter.tendstoCofinite_iff_finite_preimage_singleton (F^[n])).mp
    (tendstoCofinite_iterate_of_isPolynomialMapOfDegreeAtLeastTwo hF n) a

/-- **The fibres of `F^[n]` restricted to an invariant set are finite.**

`immBasinIterate Ω F hmap n` is the map `z ↦ F^[n] z` on the subtype `↥Ω`; its fibre over `y` is
contained in the fibre of `F^[n]` over the point `y`, and the coercion `↥Ω → ℂ` is injective. -/
theorem finite_fiber_immBasinIterate {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hcl : ∀ x ∈ Work.FatouParabolic.puncturedBasin F z₀,
      x ∈ closure (Work.FatouParabolic.Core.immBasin F z₀ p₀) →
      x ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀)
    (hbdd : Bornology.IsBounded (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hnocrit : ∀ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w ≠ 0) (n : ℕ) :
    ∀ y : ↥(Work.FatouParabolic.Core.immBasin F z₀ p₀),
      (Work.FatouParabolic.Core.immBasinIterate
        (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n ⁻¹' {y}).Finite := by
  have hfin : ∀ a : ℂ, ((F^[n]) ⁻¹' {a}).Finite :=
    finite_fiber_iterate_of_isPolynomialMapOfDegreeAtLeastTwo hF n
  intro y
  -- The fibre of the restriction is contained in the fibre of `F^[n]`, pulled back along the
  -- injective coercion `↥Ω → ℂ`.
  have hsub : (Work.FatouParabolic.Core.immBasinIterate
        (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n ⁻¹' {y}) ⊆
      Subtype.val ⁻¹' ((F^[n]) ⁻¹' {y.1}) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← hx, Work.FatouParabolic.Core.immBasinIterate_coe]
  exact (hfin y.1).preimage (Subtype.val_injective.injOn) |>.subset hsub

end Work.FatouParabolic.Core
