import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hdistIsCompact
import Submission.Work.Mostow.properAction

/-!
# A closest point of an orbit of a discrete subgroup of `PO n 1`

For a discrete subgroup `Γ ≤ PO n 1`, any orbit `Γ • o` has a point closest to a given point `x`.

The two ingredients are:

* `finite_orbit_near` : properness of the action — for every radius `R` only finitely many
  `γ ∈ Γ` satisfy `hdist x (γ • o) ≤ R`.  This is `finite_nearStab` (the near-stabiliser of the
  origin is finite) applied after bounding `γ • o` in a hyperbolic ball by the elementary
  chart estimate `‖u‖ ≤ M ⟹ hdist 0 u ≤ arcosh √(1 + M²)`.
* the reformulation of "the minimising set is finite" as the minimum of a real-valued function
  on a nonempty finite set.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

/-- **Properness.**  For a discrete subgroup `Γ ≤ PO n 1`, a point `o`, a centre `x` and a
radius `R`, only finitely many `γ ∈ Γ` have `hdist x (γ • o) ≤ R`.

The set of such `γ` is contained in the near-stabiliser of the origin: if `hdist x (γ • o) ≤ R`
then `γ • o` lies in the compact ball of radius `R` around `x`, hence `‖γ • o‖ ≤ M` for some
`M`, hence `hdist 0 (γ • o) ≤ arcosh √(1 + M²)`; the triangle inequality applied to the
isometry `γ` then bounds `hdist 0 (γ • 0)` by `arcosh √(1 + M²) + hdist 0 o`. -/
theorem finite_orbit_near (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)))
    (o x : Submission.Mostow.E n) (R : ℝ) :
    {γ : Γ | Submission.Mostow.hdist x
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • o) ≤ R}.Finite := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w : E n, hdist x w ≤ R → ‖w‖ ≤ M :=
    exists_norm_le_of_isCompact (hdistIsCompact n x R)
  have hdl : ∀ u : E n, ‖u‖ ≤ M → hdist (0 : E n) u ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) := by
    intro u hu
    have h0 : hdist (0 : E n) u = Real.arcosh (tpart u) := by rw [hdist]; simp [tpart]
    rw [h0]
    rw [Real.arcosh_le_arcosh (tpart_pos u) (Real.sqrt_pos.2 (by nlinarith [sq_nonneg M]))]
    rw [tpart]
    apply Real.sqrt_le_sqrt
    nlinarith [hu, norm_nonneg u, sq_nonneg (M - ‖u‖)]
  refine (finite_nearStab hAb hI' hdisc
    (Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) o)).subset ?_
  intro γ hγ
  have h1 : hdist (0 : E n) ((γ : PO n 1) • o) ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) :=
    hdl _ (hM _ hγ)
  have h2 : hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) = hdist o (0 : E n) :=
    hI'.isom_smul _ _ _
  have h3 := hI'.triangle (0 : E n) ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n))
  have h4 : hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
      ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) o := by
    calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) ((γ : PO n 1) • o) +
            hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) := h3
      _ = hdist (0 : E n) ((γ : PO n 1) • o) + hdist o (0 : E n) := by rw [h2]
      _ ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) o := by
            rw [hI'.symm o (0 : E n)]
            linarith
  exact h4

theorem exists_closest_orbit (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)))
    (o x : Submission.Mostow.E n) :
    ∃ γ : Γ, ∀ γ' : Γ,
      Submission.Mostow.hdist x ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • o) ≤
        Submission.Mostow.hdist x ((γ' : LeanEval.Geometry.MostowRigidity.PO n 1) • o) := by
  have hAb : POBasic n := POBasic.ofProp hA
  set R₀ : ℝ := hdist x o with hR₀
  have hfin : {γ : Γ | hdist x ((γ : PO n 1) • o) ≤ R₀}.Finite :=
    finite_orbit_near n hA hI hdisc o x R₀
  have hne : {γ : Γ | hdist x ((γ : PO n 1) • o) ≤ R₀}.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [Set.mem_ofPred_eq]
    have hone : ((1 : Γ) : PO n 1) = 1 := Subgroup.coe_one Γ
    rw [hone, hAb.one_smul]
  obtain ⟨γ, hγmem, hmin⟩ := Finset.exists_min_image hfin.toFinset
    (fun γ : Γ => hdist x ((γ : PO n 1) • o)) (by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, hfin.mem_toFinset.mpr ha⟩)
  refine ⟨γ, fun γ' => ?_⟩
  by_cases hle : hdist x ((γ' : PO n 1) • o) ≤ R₀
  · exact hmin γ' (hfin.mem_toFinset.mpr hle)
  · have hgt : R₀ < hdist x ((γ' : PO n 1) • o) := not_le.mp hle
    have hγ : hdist x ((γ : PO n 1) • o) ≤ R₀ := hfin.mem_toFinset.mp hγmem
    linarith

end Work.Mostow
