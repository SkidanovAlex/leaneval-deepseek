import Mathlib

/-!
# An isometry fixing a vector and matching two frames in its orthogonal complement

`CutPush/orthogonal_gauge_pointwise` (`CutPush/orthogonal_gauge_pointwise.lean`).  Two orthonormal
`k`-frames `B`, `C` in the orthogonal complement of a fixed nonzero vector `e` of `ℝ^m` are related
by a linear isometry fixing `e`:

  `∃ R : ℝ^m ≃ₗᵢ[ℝ] ℝ^m,  R e = e  ∧  ∀ i, R (B i) = C i`.

The proof is the classical one: the normalised vector `ê = ‖e‖⁻¹ • e` together with `B` (resp. `C`)
is an orthonormal family indexed by `Option (Fin k)`; both extend to orthonormal *bases* with the
*same* index type `Option (Fin k) ⊕ Fin (m - (k + 1))` (possible because `k + 1 ≤ m`, which follows
from `B` being orthonormal in `ℝ^m`), and the basis-matching isometry `b₁.equiv b₂` of the two
extensions has the required two properties.

This is the pointwise half of the "orthogonal gauge" input of the tube route
(`CutPush/orthogonal_gauge_family` is the smooth family version).
-/

open scoped BigOperators

namespace Work.Whitney.CutPush

/-- **Two frames in the orthogonal complement of a vector are matched by an isometry fixing it.** -/
theorem exists_linearIsometryEquiv_fixing_vector_matching_frames {m k : ℕ}
    (e : EuclideanSpace ℝ (Fin m)) (he : e ≠ 0)
    (B : Fin k → EuclideanSpace ℝ (Fin m)) (hB : Orthonormal ℝ B)
    (hBe : ∀ i, inner ℝ (B i) e = 0)
    (C : Fin k → EuclideanSpace ℝ (Fin m)) (hC : Orthonormal ℝ C)
    (hCe : ∀ i, inner ℝ (C i) e = 0) :
    ∃ R : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m),
      R e = e ∧ ∀ i, R (B i) = C i := by
  classical
  -- ## the normalised axis
  have hnorm_ne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  set ê : EuclideanSpace ℝ (Fin m) := ‖e‖⁻¹ • e with hêdef
  have hê_self : inner ℝ ê ê = 1 := by
    rw [hêdef, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hê_mul : ‖e‖ • ê = e := by
    rw [hêdef, smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
  have hBe' : ∀ i, inner ℝ e (B i) = 0 := fun i => by rw [real_inner_comm]; exact hBe i
  have hCe' : ∀ i, inner ℝ e (C i) = 0 := fun i => by rw [real_inner_comm]; exact hCe i
  -- ## the two extended families on `Option (Fin k)`
  let vB : Option (Fin k) → EuclideanSpace ℝ (Fin m) := fun a => Option.elim a ê B
  let vC : Option (Fin k) → EuclideanSpace ℝ (Fin m) := fun a => Option.elim a ê C
  have hvB : Orthonormal ℝ vB := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
        cases j with
        | none => simpa [vB] using hê_self
        | some j =>
            have h : inner ℝ ê (B j) = 0 := by
              rw [hêdef, real_inner_smul_left, hBe' j, mul_zero]
            simpa [vB] using h
    | some i =>
        cases j with
        | none =>
            have h : inner ℝ (B i) ê = 0 := by
              rw [hêdef, real_inner_smul_right, hBe i, mul_zero]
            simpa [vB] using h
        | some j => simpa [vB] using (orthonormal_iff_ite.mp hB i j)
  have hvC : Orthonormal ℝ vC := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
        cases j with
        | none => simpa [vC] using hê_self
        | some j =>
            have h : inner ℝ ê (C j) = 0 := by
              rw [hêdef, real_inner_smul_left, hCe' j, mul_zero]
            simpa [vC] using h
    | some i =>
        cases j with
        | none =>
            have h : inner ℝ (C i) ê = 0 := by
              rw [hêdef, real_inner_smul_right, hCe i, mul_zero]
            simpa [vC] using h
        | some j => simpa [vC] using (orthonormal_iff_ite.mp hC i j)
  -- ## the index type of the extensions
  have hcard_le : k + 1 ≤ m := by
    have h := hvB.linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) =
      Fintype.card (Option (Fin k) ⊕ Fin (m - (k + 1))) := by
    rw [finrank_euclideanSpace, Fintype.card_fin, Fintype.card_sum, Fintype.card_option,
      Fintype.card_fin, Fintype.card_fin]
    omega
  -- ## the families on the extended index type
  let wB : Option (Fin k) ⊕ Fin (m - (k + 1)) → EuclideanSpace ℝ (Fin m) :=
    fun i => vB (Sum.elim id (fun _ : Fin (m - (k + 1)) => none) i)
  let wC : Option (Fin k) ⊕ Fin (m - (k + 1)) → EuclideanSpace ℝ (Fin m) :=
    fun i => vC (Sum.elim id (fun _ : Fin (m - (k + 1)) => none) i)
  let s : Set (Option (Fin k) ⊕ Fin (m - (k + 1))) := Set.range (Sum.inl : Option (Fin k) → _)
  have hs_inj : Function.Injective
      (fun x : s => Sum.elim id (fun _ : Fin (m - (k + 1)) => none)
        (x : Option (Fin k) ⊕ Fin (m - (k + 1)))) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    simp only [Sum.elim_inl, id_eq] at hxy ⊢
    rw [hxy]
  have hsB : Orthonormal ℝ (s.domRestrict wB) := by
    have h := hvB.comp (fun x : s => Sum.elim id (fun _ : Fin (m - (k + 1)) => none)
      (x : Option (Fin k) ⊕ Fin (m - (k + 1)))) hs_inj
    exact h
  have hsC : Orthonormal ℝ (s.domRestrict wC) := by
    have h := hvC.comp (fun x : s => Sum.elim id (fun _ : Fin (m - (k + 1)) => none)
      (x : Option (Fin k) ⊕ Fin (m - (k + 1)))) hs_inj
    exact h
  -- ## the two orthonormal bases
  obtain ⟨b₁, hb₁⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (E := EuclideanSpace ℝ (Fin m))
      (ι := Option (Fin k) ⊕ Fin (m - (k + 1))) (v := wB) (s := s) hcard hsB
  obtain ⟨b₂, hb₂⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (E := EuclideanSpace ℝ (Fin m))
      (ι := Option (Fin k) ⊕ Fin (m - (k + 1))) (v := wC) (s := s) hcard hsC
  -- ## the matching isometry
  refine ⟨b₁.equiv b₂ (Equiv.refl (Option (Fin k) ⊕ Fin (m - (k + 1)))), ?_, ?_⟩
  · have h₁ : b₁ (Sum.inl (none : Option (Fin k))) = ê := by
      have := hb₁ (Sum.inl (none : Option (Fin k))) (Set.mem_range_self _)
      simpa [wB, vB] using this
    have h₂ : b₂ (Sum.inl (none : Option (Fin k))) = ê := by
      have := hb₂ (Sum.inl (none : Option (Fin k))) (Set.mem_range_self _)
      simpa [wC, vC] using this
    have hR' : (b₁.equiv b₂ (Equiv.refl (Option (Fin k) ⊕ Fin (m - (k + 1)))))
        (b₁ (Sum.inl (none : Option (Fin k)))) = b₂ (Sum.inl (none : Option (Fin k))) := by
      simp
    have hR : (b₁.equiv b₂ (Equiv.refl (Option (Fin k) ⊕ Fin (m - (k + 1))))) ê = ê := by
      rw [← h₁, hR', h₂]
      exact h₁.symm
    rw [← hê_mul, map_smul, hR]
  · intro i
    have h₁ : b₁ (Sum.inl (some i)) = B i := by
      have := hb₁ (Sum.inl (some i)) (Set.mem_range_self _)
      simpa [wB, vB] using this
    have h₂ : b₂ (Sum.inl (some i)) = C i := by
      have := hb₂ (Sum.inl (some i)) (Set.mem_range_self _)
      simpa [wC, vC] using this
    have hR' : (b₁.equiv b₂ (Equiv.refl (Option (Fin k) ⊕ Fin (m - (k + 1)))))
        (b₁ (Sum.inl (some i))) = b₂ (Sum.inl (some i)) := by
      simp
    rw [← h₁, ← h₂]
    exact hR'

end Work.Whitney.CutPush
