import Mathlib
import Submission.Work.WilC5.SatSetup

namespace Work.WilC5

/-- Every subset of the index set `SatIdx κ` whose cardinality is less than the cardinal
`(κ + ℵ₀)⁺⁺` — the cardinality of `SatIdx κ` itself, i.e. the bound `(κ + ℵ₀)⁺⁺` of its
order type — is bounded above.

Indeed `SatIdx κ` is the type of ordinals below `((κ + ℵ₀)⁺⁺).ord`, and `(κ + ℵ₀)⁺⁺` is a successor
cardinal, hence regular, so a family of fewer than `(κ + ℵ₀)⁺⁺` many ordinals below
`((κ + ℵ₀)⁺⁺).ord` has supremum below that ordinal. -/
theorem satIdxBdd_of_mk_lt_succ (κ : Cardinal.{0}) (X : Set (Work.WilC5.SatIdx κ))
    (hX : Cardinal.mk X < Order.succ (Order.succ (κ + Cardinal.aleph0))) :
    ∃ z : Work.WilC5.SatIdx κ, ∀ x ∈ X, x ≤ z := by
  -- `μ = (κ + ℵ₀)⁺⁺` is a successor cardinal, therefore regular.
  have hreg : (Order.succ (Order.succ (κ + Cardinal.aleph0))).IsRegular :=
    Cardinal.isRegular_succ (c := Order.succ (κ + Cardinal.aleph0))
      (le_trans (self_le_add_left Cardinal.aleph0 κ) (Order.le_succ _))
  -- `#X < μ = μ.ord.cof`.
  have hlt : Cardinal.mk X < ((Order.succ (Order.succ (κ + Cardinal.aleph0))).ord).cof := by
    rw [hreg.cof_ord]
    exact hX
  -- The sup of the ordinals attached to the elements of `X` is `< μ.ord`.
  let f : X → Ordinal := fun x => (Ordinal.ToType.toOrd x.1 : Ordinal)
  have hf : ∀ x : X, f x < (Order.succ (Order.succ (κ + Cardinal.aleph0))).ord := fun x =>
    (Ordinal.ToType.toOrd x.1).2
  have hsup : (⨆ x : X, f x) < (Order.succ (Order.succ (κ + Cardinal.aleph0))).ord :=
    Ordinal.iSup_lt_of_lt_cof hlt hf
  -- Transport it back into `SatIdx κ` via the order isomorphism `Iio μ.ord ≃o SatIdx κ`.
  refine ⟨Ordinal.ToType.mk ⟨⨆ x : X, f x, hsup⟩, ?_⟩
  intro x hx
  rw [← OrderIso.apply_symm_apply Ordinal.ToType.mk x, OrderIso.le_iff_le Ordinal.ToType.mk]
  exact Ordinal.le_iSup f ⟨x, hx⟩

/-- Every finite set of indices together with every set of fewer than `κ` indices is bounded above
in `SatIdx κ`.

In both cases the set has fewer than `(κ + ℵ₀)⁺⁺` elements — a finite set has fewer than `ℵ₀ ≤ κ + ℵ₀`
elements, and a set of fewer than `κ` elements has fewer than `κ ≤ κ + ℵ₀` elements — so
`satIdxBdd_of_mk_lt_succ` applies. -/
theorem SatIdxBdd2 (κ : Cardinal.{0}) (X : Set (Work.WilC5.SatIdx κ))
    (hX : X.Finite ∨ Cardinal.mk X < κ) :
    ∃ z : Work.WilC5.SatIdx κ, ∀ x ∈ X, x ≤ z := by
  have hμ : κ + Cardinal.aleph0 ≤ Order.succ (Order.succ (κ + Cardinal.aleph0)) :=
    le_trans (Order.le_succ (κ + Cardinal.aleph0)) (Order.le_succ _)
  have hmk : Cardinal.mk X < Order.succ (Order.succ (κ + Cardinal.aleph0)) := by
    rcases hX with hfin | hlt
    · exact lt_of_lt_of_le (lt_of_lt_of_le hfin.lt_aleph0
        (self_le_add_left Cardinal.aleph0 κ)) hμ
    · exact lt_of_lt_of_le (lt_of_lt_of_le hlt (self_le_add_right κ Cardinal.aleph0)) hμ
  exact satIdxBdd_of_mk_lt_succ κ X hmk

end Work.WilC5
