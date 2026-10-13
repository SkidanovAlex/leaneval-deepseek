import Mathlib
import Submission.Work.DSM1p.Family

/-!
# `A′` is `(p)`-adically complete

Here `A = A_∞ = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]` is the root closure and
`A′ = AdicCompletion (p) A` is its `p`-adic completion (`Work.DSM1p.FamCompletion`).

The ideal `(p) ⊆ A′` is the extension of the principal ideal `(p) ⊆ A` along the structure
map `A → A′`, and `IsAdicComplete.map_algebraMap_iff` transports completeness of the
`A`-module `A′` with respect to `(p) ⊆ A` to completeness of the `A′`-module `A′` with
respect to the extended ideal.  The former is Mathlib's `AdicCompletion.isAdicComplete`,
which applies because `(p)` is finitely generated.
-/

namespace Work.DSM1p.Family

open AdicCompletion

/-- The `p`-adic ideal of the completion is the extension of the `p`-adic ideal of the
root closure: `(p)_{A′} = (p)_A · A′`. -/
theorem span_p_FamCompletion_eq_map (R : Type*) [CommRing R] (p : ℕ) {d : ℕ}
    (x : Fin d → R) :
    Ideal.span {(p : Work.DSM1p.FamCompletion R p x)} =
      Ideal.map (algebraMap (Work.DSM1p.FamClosure R p x) (Work.DSM1p.FamCompletion R p x))
        (Ideal.span {(p : Work.DSM1p.FamClosure R p x)}) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

theorem isAdicComplete (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    IsAdicComplete (Ideal.span {(p : Work.DSM1p.FamCompletion R p x)})
      (Work.DSM1p.FamCompletion R p x) := by
  rw [span_p_FamCompletion_eq_map R p x]
  exact (IsAdicComplete.map_algebraMap_iff _ (Work.DSM1p.FamCompletion R p x)).mpr
    (AdicCompletion.isAdicComplete
      (Submodule.fg_span_singleton (p : Work.DSM1p.FamClosure R p x)))

end Work.DSM1p.Family
