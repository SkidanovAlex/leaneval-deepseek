import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.cuspShimizuPositive

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- `lev ξ · = exp (busemann ξ ·)`, upper bound form: a horoball level bound in the `lev` scale is
a Busemann level bound. -/
lemma lev_lt_exp_iff {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) (t : ℝ) :
    lev ξ u < Real.exp t ↔ busemann ξ u < t := by
  rw [lev_eq_exp hξ u, Real.exp_lt_exp]

/-- `lev ξ · = exp (busemann ξ ·)`, lower bound form. -/
lemma exp_le_lev_iff {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) (t : ℝ) :
    Real.exp t ≤ lev ξ u ↔ t ≤ busemann ξ u := by
  rw [lev_eq_exp hξ u, Real.exp_le_exp]

/-- **Shimizu's precise invariance of a deep horoball, in `lev` form.**  For a lattice
`Γ ≤ PO(n,1)`, `n ≥ 2`, a cusp `ξ ∈ parFixed Γ` whose stabiliser preserves the horospherical
levels at `ξ` (`hvan`), there is a level `s > 0` such that every `Γ`-image of a point `u` of
`lev ξ`-level `< s` by an element `μ ∈ Γ` not fixing `ξ` has `lev ξ`-level at least `s`:
the horoball `{u | lev ξ u < s}` is precisely invariant under `Γ`.

This is Shimizu's lemma, the cuspidal input of the Margulis theory, equivalently the positivity of
the Shimizu constant of the cusp at `ξ`.  The mathematics: by
`Work.Mostow.cuspParabolicFlatTrans` (which uses Bieberbach's theorem
`Work.Mostow.bieberbach` plus the class of cusps given by `hvan`) the cusp stabiliser contains a
parabolic element `δ` fixing `ξ` whose flat action on the horospheres at `ξ` is a translation by a
nonzero vector `v ⊥ ξ`; the Margulis argument then shows that a horoball at `ξ` of sufficiently
small level is disjoint from all its translates by elements of `Γ` not fixing `ξ`.  That Busemann
level statement is `Work.Mostow.cuspPreciseInvariantOfFlatTrans`; here we translate it into the
`lev = exp ∘ busemann` scale of the statement. -/
theorem cuspShimizuPreciseInvariant (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ s : ℝ, 0 < s ∧ ∀ (μ : Γ),
      Submission.Mostow.bd (μ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ ≠ ξ →
      ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u < s →
        s ≤ Work.Mostow.lev ξ ((μ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) := by
  -- the cusp stabiliser contains a parabolic flat translation of the horospheres at `ξ`, and the
  -- Margulis argument turns it into a precisely invariant Busemann horoball
  obtain ⟨t, ht⟩ := cuspPreciseInvariantOfFlatTrans n hn hA hI Γ hΓ ξ hξ
    (cuspParabolicFlatTrans n hn hA hI (fun m => bieberbach m) Γ hΓ hvan ξ hξ)
  refine ⟨Real.exp t, Real.exp_pos t, fun μ hμ u hu => ?_⟩
  have hξS : ξ ∈ Sph n := hξ.1
  have hbu : busemann ξ u < t := (lev_lt_exp_iff hξS u t).mp hu
  have hb2 : ¬ (busemann ξ ((μ : PO n 1) • u) < t) :=
    fun hcon => ht μ hμ ⟨u, hbu, hcon⟩
  exact (exp_le_lev_iff hξS ((μ : PO n 1) • u) t).mpr (not_lt.mp hb2)

end Work.Mostow
