import Mathlib

/-!
# The base-cutoff shear: self-contained copy of the bricks needed by the fibre family

`CutPush/slice_flattening.lean` carries these bricks, but that file does **not compile** in the
current tree (its last theorem, `exists_smooth_partition_subordinate_of_compact`, uses the scoped
`𝓘` notation / a `SmoothPartitionOfUnity.exists_isSubordinate` signature that no longer elaborates).
The four lemmas below are the *analytic core* of the slice flattening and depend only on Mathlib, so
they are reproduced here (verbatim from that file) so that the fibre-family construction has a
compiling, axiom-clean source for them.

* `contDiff_comp_starProjection`, `starProjection_eq_zero_of_mem_orthogonal`: bookkeeping;
* `exists_global_diffeo_of_base_shear`: for any smooth `g` with values in `Pᗮ`, the *base-cutoff
  shear* `Φ y = y - g (pr_P y)` is a **global `C^∞` diffeomorphism** of the ambient Euclidean space,
  with the explicitly displayed inverse `y ↦ y + g (pr_P y)`.  No smallness, no support condition;
* `exists_global_diffeo_of_graph_slice`: if a set `D` lies in the graph of `g` over `P`, that same
  diffeomorphism carries `D` into `P`.
-/

namespace Work.Whitney.CutPush

open scoped ContDiff

set_option linter.unusedVariables false

/-- The correction `y ↦ g (pr_P y)` of the base-cutoff shear is smooth. -/
theorem contDiff_comp_starProjection {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => g (P.starProjection y)) :=
  hg.comp (P.starProjection : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).contDiff

/-- An element of `Pᗮ` is killed by the orthogonal projection onto `P`. -/
theorem starProjection_eq_zero_of_mem_orthogonal {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection] {v : EuclideanSpace ℝ (Fin N)} (hv : v ∈ Pᗮ) :
    P.starProjection v = 0 := by
  have h2 : P.orthogonalProjectionOnto v = 0 :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := P)).mpr hv
  have h3 : P.starProjection v =
      ((P.orthogonalProjectionOnto v : P) : EuclideanSpace ℝ (Fin N)) := rfl
  rw [h3, h2]
  rfl

/-- **The base-cutoff shear is a global diffeomorphism.**  For a smooth `g` with values in `Pᗮ`, the
map `Φ y = y - g (pr_P y)` is a global `C^∞` diffeomorphism with inverse `Φ⁻¹ y = y + g (pr_P y)`. -/
theorem exists_global_diffeo_of_base_shear {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hmem : ∀ y, g y ∈ Pᗮ) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y, Φ y = y - g (P.starProjection y)) ∧
      (∀ y, Φinv y = y + g (P.starProjection y)) := by
  classical
  have hcorr := contDiff_comp_starProjection P g hg
  have hfix : ∀ y : EuclideanSpace ℝ (Fin N), P.starProjection (g (P.starProjection y)) = 0 :=
    fun y => starProjection_eq_zero_of_mem_orthogonal P (hmem _)
  refine ⟨fun y => y - g (P.starProjection y), fun y => y + g (P.starProjection y),
    ?_, ?_, ?_, ?_, fun y => rfl, fun y => rfl⟩
  · exact contDiff_id.sub hcorr
  · exact contDiff_id.add hcorr
  · intro y
    have hbase : P.starProjection (y - g (P.starProjection y)) = P.starProjection y := by
      rw [map_sub, hfix, sub_zero]
    show (y - g (P.starProjection y)) + g (P.starProjection (y - g (P.starProjection y))) = y
    rw [hbase]
    abel
  · intro y
    have hbase : P.starProjection (y + g (P.starProjection y)) = P.starProjection y := by
      rw [map_add, hfix, add_zero]
    show (y + g (P.starProjection y)) - g (P.starProjection (y + g (P.starProjection y))) = y
    rw [hbase]
    abel

/-- **Graph slices are flattened into the base plane.**  If `D` is contained in the graph of `g`
over `P` (i.e. `y - g (pr_P y) ∈ P` for `y ∈ D`), then some global `C^∞` diffeomorphism of the
ambient space carries `D` into `P` (namely the base-cutoff shear of `g`). -/
theorem exists_global_diffeo_of_graph_slice {N : ℕ} (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [P.HasOrthogonalProjection]
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hmem : ∀ y, g y ∈ Pᗮ)
    (D : Set (EuclideanSpace ℝ (Fin N)))
    (hD : ∀ y ∈ D, y - g (P.starProjection y) ∈ P) :
    ∃ (Φ Φinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φinv ∧
      Function.LeftInverse Φinv Φ ∧ Function.RightInverse Φinv Φ ∧
      (∀ y ∈ D, Φ y ∈ P) := by
  obtain ⟨Φ, Φinv, h1, h2, h3, h4, h5, _⟩ := exists_global_diffeo_of_base_shear P g hg hmem
  exact ⟨Φ, Φinv, h1, h2, h3, h4, fun y hy => by rw [h5 y]; exact hD y hy⟩

end Work.Whitney.CutPush
