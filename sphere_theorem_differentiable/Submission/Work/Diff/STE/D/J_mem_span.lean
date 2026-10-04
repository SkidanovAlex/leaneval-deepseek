import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.D.Rstar_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D, step 2 (continued): `J ρ ε h` lies in the Galerkin span for symmetric `h`

The Friedrichs mollifier `J ρ ε` (see `B3/Comp.lean`) has, for every section `h`, the finite
expansion

  `J ρ ε h = Σ_{i,a,b,q} scoeff (R i h a b) q • jVec i a b q`

(`B3/J_finite_rank.lean`, `J_eq_sum_index`).  Run over the number of Fourier modes, this exhibits
`J ρ ε h` as an element of the span of the *unsymmetrised* family `jVec`.

The Galerkin space of `D/Galerkin.lean`, however, is the range of the map
`genMap D ε c = Σ_z c z • jSym D ε z`, whose spanning families are the *symmetrised* combinations
`jSym z = jVec z + jVec (idxSwap z)` of the same vectors.  Since `jVec (idxSwap z)` is `jVec z` with
the two frame slots exchanged, the symmetrised span contains the unsymmetrised one *precisely on the
sections whose chart components are symmetric in the two slots* — which, for a symmetric section
`h`, they are: `D.mat i h a b = h (pt i z) (e i a) (e i b)` is symmetric in `a,b` by `hsym`, hence
so is `D.R i h a b` and hence so are its Fourier coefficients.

This file records that membership statement: for a symmetric `h` there is a coefficient family `c`
with `J ρ ε h = genMap D ε c` — i.e. `J ρ ε h` belongs to the span of the Galerkin family.  The
combinatorial content is isolated in `genMap_div_two_eq_sum`.
-/

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The symmetrisation of a swap-invariant coefficient family.**  If the coefficient family `C`
on the product index `JIdx` is invariant under the swap `idxSwap` of the two frame slots, then the
Galerkin combination of the *symmetrised* family with coefficients `C z / 2` is exactly the
combination of the *raw* family with coefficients `C`:

  `genMap D ε (C / 2) = Σ_z C z • jFamily D ε z`.

Indeed `jSym z = jFamily z + jFamily (idxSwap z)` and `jFamily (idxSwap z) = jVec i b a q` is the
same vector as `jFamily z = jVec i a b q` with the two slots exchanged; reindexing the sum by the
involution `idxSwap` and using `C ∘ idxSwap = C` turns the second half into a copy of the first,
and the two copies recombine with the factor `2`. -/
lemma genMap_div_two_eq_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (C : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hC : ∀ z, C (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z) = C z) :
    genMap (I := I) (M := M) D ε (fun z => C z / 2)
      = ∑ z, C z • Work.Diff.STE.B3.jFamily D ε z := by
  have hrw : genMap (I := I) (M := M) D ε (fun z => C z / 2)
      = ∑ z, (C z / 2) • (Work.Diff.STE.B3.jFamily D ε z
          + Work.Diff.STE.B3.jFamily D ε
              (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)) := rfl
  rw [hrw]
  calc (∑ z, (C z / 2) • (Work.Diff.STE.B3.jFamily D ε z
          + Work.Diff.STE.B3.jFamily D ε (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)))
      = ∑ z, ((C z / 2) • Work.Diff.STE.B3.jFamily D ε z
          + (C z / 2) • Work.Diff.STE.B3.jFamily D ε
              (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)) :=
        Finset.sum_congr rfl (fun z _ => smul_add (C z / 2)
          (Work.Diff.STE.B3.jFamily D ε z)
          (Work.Diff.STE.B3.jFamily D ε (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)))
    _ = (∑ z, (C z / 2) • Work.Diff.STE.B3.jFamily D ε z)
          + ∑ z, (C z / 2) • Work.Diff.STE.B3.jFamily D ε
              (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z) :=
        Finset.sum_add_distrib
    _ = (∑ z, (C z / 2) • Work.Diff.STE.B3.jFamily D ε z)
          + ∑ z, (C z / 2) • Work.Diff.STE.B3.jFamily D ε z := by
        refine congrArg (fun t => (∑ z, (C z / 2) • Work.Diff.STE.B3.jFamily D ε z) + t) ?_
        exact Fintype.sum_equiv (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε) _ _
          (fun z => by
            show (C z / 2) • Work.Diff.STE.B3.jFamily D ε
                (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)
              = (C (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z) / 2)
                • Work.Diff.STE.B3.jFamily D ε
                    (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)
            rw [hC z])
    _ = ∑ z, ((C z / 2) • Work.Diff.STE.B3.jFamily D ε z
          + (C z / 2) • Work.Diff.STE.B3.jFamily D ε z) :=
        (Finset.sum_add_distrib (s := Finset.univ)).symm
    _ = ∑ z, C z • Work.Diff.STE.B3.jFamily D ε z := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        exact calc (C z / 2) • Work.Diff.STE.B3.jFamily D ε z
              + (C z / 2) • Work.Diff.STE.B3.jFamily D ε z
            = (C z / 2 + C z / 2) • Work.Diff.STE.B3.jFamily D ε z :=
              (add_smul (C z / 2) (C z / 2) (Work.Diff.STE.B3.jFamily D ε z)).symm
          _ = C z • Work.Diff.STE.B3.jFamily D ε z := by
              rw [show C z / 2 + C z / 2 = C z by ring]

theorem J_mem_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : Work.Diff.STE.D.IsSymm (I := I) h) :
    ∃ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      D.J ρ ε h = Work.Diff.STE.D.genMap (I := I) (M := M) D ε c := by
  -- the chart components of a symmetric section are symmetric in the two frame slots
  have hR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.R i h a b = D.R i h b a := by
    intro i a b
    funext z
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
    rw [hsym (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))]
  -- hence the coefficients of the expansion of `J ρ ε h` are swap-invariant
  have hc : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.B3.jFamilyCoeff D ρ ε h (Work.Diff.STE.D.idxSwap (E := E) (ι₀ := ι₀) ε z)
        = Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z := by
    intro z
    simp only [Work.Diff.STE.B3.jFamilyCoeff, Work.Diff.STE.D.idxSwap_apply]
    rw [hR]
  -- and the symmetrised Galerkin combination with half these coefficients is `J ρ ε h`
  refine ⟨fun z => Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z / 2, ?_⟩
  rw [Work.Diff.STE.B3.J_eq_sum_index D ρ ε hε hρ0 h]
  exact (genMap_div_two_eq_sum D ε (Work.Diff.STE.B3.jFamilyCoeff D ρ ε h) hc).symm

end Work.Diff.STE.D
