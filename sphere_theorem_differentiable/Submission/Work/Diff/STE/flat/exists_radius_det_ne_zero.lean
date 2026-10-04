/-
# A ball of coefficient families on which the Galerkin jet stays non-degenerate

`Work.Diff.STE.flat.exists_radius_det_ne_zero`: if the explicit Galerkin value jet `valExp a₀` of a
coefficient family `a₀` has non-vanishing real-part determinant at *every* point of the closed unit
cube `[0,1]^n`, then the same holds for every coefficient family in an open ball around `a₀`.

This is the "positivity is open" step of the Galerkin scheme (DESIGN.md §5): the truncated Fourier
series `valExp (projBox N (fourierCoeffM u₀))` of a positive-definite datum `u₀` is again
non-degenerate on the cube for large `N`, which is precisely the hypothesis `hnd` of
`Work.Diff.STE.flat.galerkin_ode_existence`.

The proof is compactness.  The map
`(a, x) ↦ (reMat (valExp a x)).det` is continuous — at each `(i,j)` the entry is a finite sum of
products of a linear function of `a` with a smooth function of `x` — the closed cube `[0,1]^n` is
compact, and the preimage of `ℝ \ {0}` is an open neighbourhood of the compact set
`{a₀} × [0,1]^n`; a thickening of that compact set is contained in it, and a thickening of
`{a₀} × [0,1]^n` contains `ball a₀ (δ/2) × [0,1]^n`.
-/
import Mathlib
import Submission.Work.Diff.STE.flat.GalerkinDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat.Galerkin

/-- The characters of the torus are continuous functions of the point. -/
@[fun_prop]
lemma continuous_fourierExp_flat {n : ℕ} (k : Fin n → ℤ) :
    Continuous (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp k x) := by
  unfold Work.Diff.STE.fourierExp
  fun_prop

/-- The explicit value jet `valExp` is continuous in the coefficients and in the point. -/
lemma continuous_valExp_prod {n N : ℕ} :
    Continuous (fun p : Coeff n N × (Fin n → ℝ) => valExp p.1 p.2) := by
  unfold valExp
  fun_prop

/-- The closed unit cube `[0,1]^n` is compact. -/
lemma isCompact_closedCube (n : ℕ) : IsCompact (closedCube n) := by
  unfold closedCube
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem exists_radius_det_ne_zero {n N : ℕ} (a₀ : Work.Diff.STE.Flat.Galerkin.Coeff n N)
    (hnd : ∀ x ∈ Work.Diff.STE.Flat.Galerkin.closedCube n,
      (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.Galerkin.valExp a₀ x)).det ≠ 0) :
    ∃ r > 0, ∀ a : Work.Diff.STE.Flat.Galerkin.Coeff n N, dist a a₀ ≤ r →
      ∀ x ∈ Work.Diff.STE.Flat.Galerkin.closedCube n,
        (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.Galerkin.valExp a x)).det ≠ 0 := by
  -- Continuity of the determinant of the real part of the value jet, jointly in `(a, x)`.
  have hcont : Continuous fun p : Coeff n N × (Fin n → ℝ) =>
      (Work.Diff.STE.Flat.reMat (valExp p.1 p.2)).det :=
    (continuous_matrix fun i j => Complex.continuous_re.comp
      ((continuous_apply_apply i j).comp (continuous_valExp_prod (n := n) (N := N)))).matrix_det
  -- The non-degeneracy locus is open and contains the compact set `{a₀} × [0,1]^n`.
  have hK : IsCompact (({a₀} : Set (Coeff n N)) ×ˢ closedCube n) :=
    isCompact_singleton.prod (isCompact_closedCube n)
  have hsub : (({a₀} : Set (Coeff n N)) ×ˢ closedCube n) ⊆
      {p | (Work.Diff.STE.Flat.reMat (valExp p.1 p.2)).det ≠ 0} := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hnd x hx
  have hopen : IsOpen {p : Coeff n N × (Fin n → ℝ) |
      (Work.Diff.STE.Flat.reMat (valExp p.1 p.2)).det ≠ 0} :=
    isOpen_ne.preimage hcont
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_thickening_subset_open hopen hsub
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a ha x hx
  have hmem : (a, x) ∈ Metric.thickening δ (({a₀} : Set (Coeff n N)) ×ˢ closedCube n) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(a₀, x), ⟨rfl, hx⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    linarith
  exact hδsub hmem

end Work.Diff.STE.flat
