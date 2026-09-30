import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `riemannZetaZeros` is countable: it is a discrete subset of the hereditarily Lindelöf
space `ℂ`. -/
lemma countable_riemannZetaZeros : riemannZetaZeros.Countable :=
  IsLindelof.countable_of_isDiscrete (HereditarilyLindelofSpace.isLindelof riemannZetaZeros)
    isDiscrete_riemannZetaZeros

/-- Circle avoidance for the zeros of `ζ`: given any non-degenerate real interval `[x,y]` with
`0 < x`, and any two centre points `a 0`, `a 1`, there is a radius `R ∈ [x,y]` such that the two
circles `‖u - a j‖ = R` (`j = 0,1`) carry no zero of `ζ`.

The zero set of `ζ` is countable (`Mathlib/NumberTheory/LSeries/ZetaZeros.lean` provides
`riemannZetaZeros`, `isDiscrete_riemannZetaZeros` and `IsCompact.inter_riemannZetaZeros_finite`;
an uncountable discrete subset of `ℂ` is impossible, or derive countability from
analyticity + discreteness directly).  Hence only countably many radii are realised as
`‖ρ - a j‖`, and a non-degenerate interval is not countable. -/
theorem zeta_sphere_avoid (a : Fin 2 → ℂ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ R : ℝ, x ≤ R ∧ R ≤ y ∧ ∀ j : Fin 2, ∀ u : ℂ, riemannZeta u = 0 → ‖u - a j‖ ≠ R := by
  -- The set of radii realised by a zero of `ζ` around one of the two centres.
  set S : Set ℝ := ⋃ j : Fin 2, (fun u : ℂ => ‖u - a j‖) '' riemannZetaZeros with hSdef
  have hSc : S.Countable := by
    rw [hSdef]
    exact Set.countable_iUnion fun j => countable_riemannZetaZeros.image _
  -- A non-degenerate real interval is uncountable.
  have hIcc : ¬ (Set.Icc x y).Countable := by
    rw [Cardinal.Real.Icc_countable_iff]
    exact not_le.mpr hxy
  -- So it is not contained in `S`.
  have hnotsub : ¬ (Set.Icc x y ⊆ S) := fun hsub => hIcc (hSc.mono hsub)
  obtain ⟨R, hRmem, hRnot⟩ := Set.not_subset.mp hnotsub
  refine ⟨R, hRmem.1, hRmem.2, ?_⟩
  intro j u hu hcontra
  apply hRnot
  rw [hSdef]
  exact Set.mem_iUnion.mpr
    ⟨j, (Set.mem_image (fun u : ℂ => ‖u - a j‖) riemannZetaZeros R).mpr
      ⟨u, mem_riemannZetaZeros.mpr hu, hcontra⟩⟩

end Work.BMF
