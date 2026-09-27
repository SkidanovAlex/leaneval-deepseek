import Mathlib
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.haarBridge

/-!
# A fundamental domain of positive volume for a discrete subgroup of `PO 1 1`

For every discrete subgroup `D ≤ PO 1 1` there is a `volH 1`-fundamental domain `DY` of
*nonzero* (extended) volume.

The construction is the Dirichlet domain at a base point `o` with trivial `D`-stabiliser
(`Work.Mostow.exists_trivial_stabiliser`, available for every `n`):
`dirichletSet_isFundamentalDomain` turns it into a fundamental domain
(`Work.Mostow.exists_closest_orbit` supplies nearest orbit points).

For the non-vanishing of the volume we use that the Dirichlet domain contains a hyperbolic ball
around `o`: by properness (`Work.Mostow.finite_orbit_near`) only finitely many `γ ≠ 1` have
`hdist o (γ • o) ≤ 1`, and each of those has `hdist o (γ • o) > 0` because the `o`-stabiliser is
trivial; hence there is a uniform `δ > 0` with `hdist o (γ • o) ≥ δ` for all `γ ≠ 1`.  Any `x`
with `hdist x o < δ/2` then satisfies `hdist x o < hdist x (γ • o)` for every `γ ≠ 1`.
Since `volH` is strictly positive on nonempty open sets (`Work.Mostow.volHPosOpen`), the Dirichlet
domain has positive — in particular nonzero — volume.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
set_option linter.style.haveILetI false

open scoped Topology

theorem existsFDone (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (D : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1)) (hdisc : IsDiscrete (SetLike.coe D)) :
    ∃ DY : Set (Submission.Mostow.E 1),
      MeasureTheory.IsFundamentalDomain D DY (Submission.Mostow.volH 1) ∧
      Submission.Mostow.volH 1 DY ≠ 0 := by
  classical
  have hAc : Submission.Mostow.POActionProp 1 := hA
  have hIc : Submission.Mostow.HypIsometryProp 1 := hI
  obtain ⟨-, -, -, hone, -, -, -, -, -, -, -, -⟩ := hAc
  obtain ⟨hdnn, hdsym, hdeq0, hdtri, -, -, -, -, -, -, -, -, -⟩ := hIc
  haveI : Countable ↥D := countable_of_isDiscrete (PO 1 1) hdisc
  obtain ⟨o, ho⟩ := exists_trivial_stabiliser 1 hA hI D hdisc
  have hfun : MeasureTheory.IsFundamentalDomain D (dirichletSet D o) (volH 1) :=
    dirichletSet_isFundamentalDomain 1 hA hI D o ho
      (fun x => exists_closest_orbit 1 hA hI hdisc o x)
  refine ⟨dirichletSet D o, hfun, ?_⟩
  -- every `γ ≠ 1` moves `o` by a positive amount
  have hposval : ∀ γ : D, γ ≠ 1 → 0 < hdist o (γ • o) := by
    intro γ hγ
    have hne : hdist o (γ • o) ≠ 0 := by
      intro h0
      exact hγ (ho γ ((hdeq0 o (γ • o)).mp h0).symm)
    exact lt_of_le_of_ne (hdnn o (γ • o)) (Ne.symm hne)
  -- only finitely many `γ ≠ 1` have `hdist o (γ • o) ≤ 1`, so the moving distance is bounded below
  have hfin : {γ : D | hdist o (γ • o) ≤ 1}.Finite :=
    finite_orbit_near 1 hA hI hdisc o o 1
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ γ : D, γ ≠ 1 → δ ≤ hdist o (γ • o) := by
    set S : Set D := {γ : D | hdist o (γ • o) ≤ 1} \ {1} with hS
    have hSfin : S.Finite := by
      rw [hS]
      exact hfin.subset Set.sdiff_subset
    rcases Set.eq_empty_or_nonempty S with hempty | hne
    · refine ⟨1, one_pos, fun γ hγ => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have hmem : γ ∈ S := by
        rw [hS]
        exact ⟨le_of_lt hlt, by simpa using hγ⟩
      rw [hempty] at hmem
      exact hmem
    · obtain ⟨γ₀, hγ₀S, hmin'⟩ := Set.exists_min_image S (fun γ : D => hdist o (γ • o)) hSfin hne
      have hγ₀ne : γ₀ ≠ 1 := by
        intro h1
        rw [hS] at hγ₀S
        exact hγ₀S.2 (by simpa using h1)
      have hγ₀le : hdist o (γ₀ • o) ≤ 1 := by
        rw [hS] at hγ₀S
        exact hγ₀S.1
      refine ⟨hdist o (γ₀ • o), hposval γ₀ hγ₀ne, fun γ hγ => ?_⟩
      by_cases hle : hdist o (γ • o) ≤ 1
      · exact hmin' γ (by rw [hS]; exact ⟨hle, by simpa using hγ⟩)
      · rw [not_le] at hle
        exact le_of_lt (lt_of_le_of_lt hγ₀le hle)
  -- the ball of radius `δ/2` about `o` is contained in the Dirichlet domain
  set U : Set (E 1) := {x : E 1 | hdist x o < δ / 2} with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_lt (dirichlet_hdist_continuous_right o) continuous_const
  have hoU : o ∈ U := by
    rw [hU]
    simp only [Set.mem_ofPred_eq]
    have h0 : hdist o o = 0 := (hdeq0 o o).mpr rfl
    rw [h0]
    linarith
  have hUsub : U ⊆ dirichletSet D o := by
    intro x hx
    rw [hU] at hx
    simp only [Set.mem_ofPred_eq] at hx
    intro γ
    by_cases hγ : γ = 1
    · subst hγ
      show hdist x o ≤ hdist x (((1 : ↥D) : PO 1 1) • o)
      rw [Subgroup.coe_one, hone]
    · have h2 := hdtri o x (γ • o)
      have h3 := hδ γ hγ
      have h4 := hdsym o x
      linarith
  intro hzero
  have hpos : 0 < volH 1 U := volHPosOpen 1 hUopen ⟨o, hoU⟩
  have hle : volH 1 U ≤ volH 1 (dirichletSet D o) := measure_mono hUsub
  rw [hzero] at hle
  exact absurd hpos (not_lt_of_ge hle)

end Work.Mostow
