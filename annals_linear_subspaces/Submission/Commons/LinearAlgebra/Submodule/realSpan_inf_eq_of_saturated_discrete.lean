import Mathlib
import Submission.Commons.Lattice.Discrete.discreteTopology_quotLattice
import Submission.Commons.Lattice.Finrank.finrank_sup_add_finrank_inf_eq_of_discrete

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Submodule

/-- For a discrete `ℤ`-submodule `Λ` of `ℝ^d` and any two `ℤ`-submodules `V, W ≤ Λ`,
the real spans intersect as the real span of the intersection.

(The requested statement assumes the stronger saturation hypotheses
`V = Λ ∩ span ℝ V`, `W = Λ ∩ span ℝ W`; these are only used to conclude `V, W ≤ Λ`.
The argument is a dimension count: every submodule of the discrete lattice `Λ` is a
finitely generated free `ℤ`-module, its real span has `ℝ`-dimension equal to its `ℤ`-rank,
and the rank identity `rank(V⊔W) + rank(V⊓W) = rank V + rank W` mirrors the `ℝ`-dimension
identity `dim(span V ⊔ span W) + dim(span V ⊓ span W) = dim span V + dim span W`.) -/
theorem realSpan_inf_eq_of_saturated_discrete {d : ℕ} (Λ V W : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ]
    (hV : ∀ x, x ∈ V ↔ x ∈ Λ ∧ x ∈ Submodule.span ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hW : ∀ x, x ∈ W ↔ x ∈ Λ ∧ x ∈ Submodule.span ℝ (W : Set (EuclideanSpace ℝ (Fin d)))) :
    Submodule.span ℝ (V : Set (EuclideanSpace ℝ (Fin d))) ⊓
        Submodule.span ℝ (W : Set (EuclideanSpace ℝ (Fin d))) =
      Submodule.span ℝ ((V ⊓ W : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
        Set (EuclideanSpace ℝ (Fin d))) := by
  set SV : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℝ (V : Set (EuclideanSpace ℝ (Fin d))) with hSV
  set SW : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℝ (W : Set (EuclideanSpace ℝ (Fin d))) with hSW
  set SVW : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℝ ((V ⊓ W : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
      Set (EuclideanSpace ℝ (Fin d))) with hSVW
  have hVle : V ≤ Λ := fun x hx => ((hV x).mp hx).1
  have hWle : W ≤ Λ := fun x hx => ((hW x).mp hx).1
  haveI : DiscreteTopology V := Commons.Lattice.Discrete.discreteTopology_of_le hVle
  haveI : DiscreteTopology W := Commons.Lattice.Discrete.discreteTopology_of_le hWle
  haveI : DiscreteTopology ↥(V ⊓ W) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (le_trans inf_le_left hVle)
  haveI : DiscreteTopology ↥(V ⊔ W) :=
    Commons.Lattice.Discrete.discreteTopology_of_le (sup_le hVle hWle)
  -- the easy inclusion
  have hle : SVW ≤ SV ⊓ SW := by
    rw [hSVW, hSV, hSW]
    apply le_inf
    · apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ((Submodule.mem_inf.mp hx).1)
    · apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ((Submodule.mem_inf.mp hx).2)
  -- ranks of the real spans equal the corresponding ℤ-ranks
  have hSVrank : Module.finrank ℝ SV = Module.finrank ℤ V := by
    rw [hSV]; exact Commons.Lattice.Discrete.finrank_span_eq_finrank d V
  have hSWrank : Module.finrank ℝ SW = Module.finrank ℤ W := by
    rw [hSW]; exact Commons.Lattice.Discrete.finrank_span_eq_finrank d W
  have hSVWrank : Module.finrank ℝ SVW = Module.finrank ℤ ↥(V ⊓ W) := by
    rw [hSVW]; exact Commons.Lattice.Discrete.finrank_span_eq_finrank d (V ⊓ W)
  have hsuprank : Module.finrank ℝ ↥(SV ⊔ SW) = Module.finrank ℤ ↥(V ⊔ W) := by
    have hsup : SV ⊔ SW =
        Submodule.span ℝ ((V ⊔ W : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
          Set (EuclideanSpace ℝ (Fin d))) := by
      rw [hSV, hSW, ← Submodule.span_union]
      apply le_antisymm
      · apply Submodule.span_mono
        intro x hx
        rcases hx with hx | hx
        · exact Submodule.mem_sup_left hx
        · exact Submodule.mem_sup_right hx
      · apply Submodule.span_le.mpr
        intro x hx
        obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx
        rw [← hvw]
        exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hv))
          (Submodule.subset_span (Or.inr hw))
    rw [hsup]; exact Commons.Lattice.Discrete.finrank_span_eq_finrank d (V ⊔ W)
  -- the two dimension identities
  have hR := Submodule.finrank_sup_add_finrank_inf_eq SV SW
  have hZ := Commons.Lattice.Finrank.finrank_sup_add_finrank_inf_eq_of_discrete
    (L₀ := Λ) hVle hWle
  have hR' : Module.finrank ℤ ↥(V ⊔ W) + Module.finrank ℝ ↥(SV ⊓ SW) =
      Module.finrank ℤ V + Module.finrank ℤ W := by
    have h := hR
    rw [hsuprank, hSVrank, hSWrank] at h
    exact h
  have h2 : Module.finrank ℝ ↥(SV ⊓ SW) = Module.finrank ℤ ↥(V ⊓ W) := by
    have h := hR'
    rw [← hZ] at h
    exact Nat.add_left_cancel h
  have hfin : Module.finrank ℝ SVW = Module.finrank ℝ ↥(SV ⊓ SW) := by
    rw [hSVWrank, h2]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

end Commons.LinearAlgebra.Submodule
