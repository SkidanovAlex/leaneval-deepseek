import Mathlib

/-!
# Linear-algebra: extend an independent family to a full basis using another basis

Used by `Submission.SecondSqueeze` (`lem:second_squeeze`, Smith GON.tex) to
complete the ℚ-linearly independent integer polynomials
`S_0..S_k` (degree ≤ m, one of degree exactly m) to a basis of the degree-≤-m
space using vectors from `{H_j : j < m}` (degree ≤ m−1, ℚ-independent).

## Claim (coordinate form)
Work in `V = Fin (m+1) → ℚ` (dimension m+1), whose element `e_m` is the vector
with `(Fin.last m)`-coordinate.  Given
  * `u : Fin (k+1) → V`, ℚ-independent, with some `u i₀` having nonzero
    coordinate at `Fin.last m` (the "degree-m" polynomial);
  * `v : Fin m → V`, ℚ-independent, all with zero coordinate at `Fin.last m`
    (the "degree ≤ m−1" polynomials; because `m` of them are independent they
    span the whole `Fin.last m`-zero subspace of dimension m);
there is a family `F : Fin (m+1) → V` that is ℚ-independent, has
`F ⟨i.val, _⟩ = u i` for all `i : Fin (k+1)`, and every other entry lies in
`range v`.

## Proof route (any correct route accepted)
1. Show `Submodule.span ℚ (Set.range v)` equals the "last-coordinate-zero"
   submodule `{x | x (Fin.last m) = 0}` (dimension m): use
   `finrank_span_eq_card` for the independent family `v` and compute the
   finrank of the zero-last subspace via a linear equivalence to `Fin m → ℚ`
   (`Module.finrank_pi`, `LinearEquiv.finrank_eq`), then
   `Submodule.eq_top_of_finrank_eq` / double-inclusion inside the subspace.
2. Conclude `span(range u) ⊔ span(range v) = ⊤` (a degree-m vector supplies the
   missing `Fin.last m` coordinate).
3. Greedily extend: with the independent family `u`, add `v j` for `j` in
   increasing order whenever it is not yet in the current span; the process
   ends with a basis of `V` (each remaining `v j` is in the span by
   maximality), so exactly `m − k` vectors are added (count via finrank or
   `finrank_span_eq_card` + `Submodule.eq_top_of_finrank_eq`).
4. Enumerate the chosen `m−k` indices (in increasing order, e.g. with
   `Finset.orderIsoOfFin` or `Finset.orderEmbOfFin`) and define `F` on
   `Fin (m+1)`: index `i` with `i.val ≤ k` ↦ `u ⟨i.val,_⟩`, index with value
   `k+1+t` ↦ `v (chosen t)`.  Check the two required properties and
   independence.

Mathlib tools: `LinearIndependent`, `Submodule.span`, `Module.finrank`,
`finrank_span_eq_card`, `Submodule.eq_top_of_finrank_eq`, `Module.finrank_pi`,
`LinearEquiv.finrank_eq`, `Finset.card`, `Finset.orderIsoOfFin`.
-/

noncomputable section
open scoped BigOperators
open Submodule Set

namespace Submission.ExtendFamily

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-- Evaluation at the `Fin.last m`-coordinate. -/
def lastCoordProj (m : ℕ) : (Fin (m + 1) → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj (R := ℚ) (i := Fin.last m)

/-- The kernel of the last-coordinate projection has dimension `m`. -/
lemma finrank_ker_lastCoordProj (m : ℕ) :
    Module.finrank ℚ
      ((lastCoordProj m).ker : Submodule ℚ (Fin (m + 1) → ℚ)) = m := by
  have hran : Module.finrank ℚ (lastCoordProj m).range = 1 := by
    have : (lastCoordProj m).range = (⊤ : Submodule ℚ ℚ) := by
      rw [LinearMap.range_eq_top]
      intro q
      refine ⟨fun _ => q, ?_⟩
      simp [lastCoordProj]
    rw [this]
    simp [finrank_top, Module.finrank_self]
  have htot : Module.finrank ℚ (Fin (m + 1) → ℚ) = m + 1 := by simp
  have hsplit := LinearMap.finrank_range_add_finrank_ker (K := ℚ) (lastCoordProj m)
  omega

/-- The independent family `v` (all vectors with zero last coordinate, `m` of
them) spans exactly the zero-last-coordinate subspace. -/
lemma span_range_v_eq_ker {m : ℕ} (v : Fin m → Fin (m + 1) → ℚ)
    (hv : LinearIndependent ℚ v)
    (hvlast : ∀ j : Fin m, v j (Fin.last m) = 0) :
    Submodule.span ℚ (Set.range v) = (lastCoordProj m).ker := by
  classical
  have hspan_le_ker : Submodule.span ℚ (Set.range v) ≤ (lastCoordProj m).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    apply LinearMap.mem_ker.mpr
    simp [lastCoordProj, hvlast j]
  have hd : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) =
      Module.finrank ℚ ((lastCoordProj m).ker : Submodule ℚ (Fin (m + 1) → ℚ)) := by
    rw [finrank_span_eq_card hv]
    rw [finrank_ker_lastCoordProj m]
    simp
  exact Submodule.eq_of_le_of_finrank_eq hspan_le_ker hd

/-- `range u ∪ range v` spans the whole space. -/
lemma span_u_union_v_eq_top {m k : ℕ} (_hkm : k ≤ m)
    (u : Fin (k + 1) → Fin (m + 1) → ℚ)
    (hlead : ∃ i₀ : Fin (k + 1), u i₀ (Fin.last m) ≠ 0)
    (v : Fin m → Fin (m + 1) → ℚ) (hv : LinearIndependent ℚ v)
    (hvlast : ∀ j : Fin m, v j (Fin.last m) = 0) :
    Submodule.span ℚ (Set.range u ∪ Set.range v) = ⊤ := by
  classical
  apply le_antisymm
  · exact le_top
  · intro x hx
    rw [Submodule.span_union]
    let i₀ : Fin (k + 1) := Classical.choose hlead
    have hc : u i₀ (Fin.last m) ≠ 0 := Classical.choose_spec hlead
    let α : ℚ := x (Fin.last m) / u i₀ (Fin.last m)
    let y : Fin (m + 1) → ℚ := x - α • u i₀
    have hzero : y (Fin.last m) = 0 := by
      simp [y, α, hc]
    have hyW : y ∈ (lastCoordProj m).ker := by
      apply LinearMap.mem_ker.mpr
      simpa [lastCoordProj] using hzero
    have hyV : y ∈ Submodule.span ℚ (Set.range v) := by
      rw [span_range_v_eq_ker v hv hvlast]
      exact hyW
    have hu0 : u i₀ ∈
        (Submodule.span ℚ (Set.range u) : Submodule ℚ (Fin (m + 1) → ℚ)) := by
      exact Submodule.subset_span ⟨i₀, rfl⟩
    have hαu : α • u i₀ ∈ Submodule.span ℚ (Set.range u) := Submodule.smul_mem _ α hu0
    apply Submodule.mem_sup.mpr
    refine ⟨α • u i₀, hαu, y, hyV, ?_⟩
    simp [y]

/-- Given an independent family `u` and a family `v` with
`range u ∪ range v` spanning the whole space, one can pick `m − k` vectors
from `range v` completing `u` to a linearly independent family. -/
lemma exists_ext_family {m k : ℕ} (hkm : k ≤ m)
    (u : Fin (k + 1) → Fin (m + 1) → ℚ) (hu : LinearIndependent ℚ u)
    (v : Fin m → Fin (m + 1) → ℚ)
    (hspan : Submodule.span ℚ (Set.range u ∪ Set.range v) = ⊤) :
    ∃ g : Fin (m - k) → Fin (m + 1) → ℚ,
      (∀ t : Fin (m - k), g t ∈ Set.range v) ∧
        LinearIndependent ℚ (Sum.elim u g) := by
  classical
  let hs : LinearIndepOn ℚ id (Set.range u) := hu.linearIndepOn_id
  have hst : Set.range u ⊆ Set.range u ∪ Set.range v := by
    intro x hx
    exact Or.inl hx
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range u ∪ Set.range v) := le_of_eq hspan.symm
  let B : Module.Basis (hs.extend hst) ℚ (Fin (m + 1) → ℚ) :=
    Module.Basis.extendLe hs hst htop
  let E : Set (Fin (m + 1) → ℚ) := hs.extend hst
  have hsubE : Set.range u ⊆ E := hs.subset_extend hst
  have hEsub : E ⊆ Set.range u ∪ Set.range v := hs.extend_subset hst
  -- Fintype and cardinality of `E` (the basis index set)
  haveI : Finite E := Module.Finite.finite_basis B
  haveI : Fintype E := Set.Finite.fintype (Set.toFinite E)
  have hBcard : Fintype.card E = m + 1 := by
    have hfinV : Module.finrank ℚ (Fin (m + 1) → ℚ) = m + 1 := by simp
    simpa [hfinV] using (Module.finrank_eq_card_basis B).symm
  -- Fintype and cardinality of `Set.range u`
  haveI : Fintype (Set.range u) := by
    exact Set.Finite.fintype ((Set.toFinite E).subset hsubE)
  have eU : Fin (k + 1) ≃ Set.range u := Equiv.ofInjective u hu.injective
  have hcardS : Fintype.card (Set.range u) = k + 1 := by
    exact (Fintype.card_congr eU).symm.trans (by simp)
  -- Fintype and cardinality of the complement `E \ range u`
  haveI : Fintype (E \ Set.range u : Set (Fin (m + 1) → ℚ)) := by
    exact Set.Finite.fintype ((Set.toFinite E).subset (Set.sdiff_subset (s := E) (t := Set.range u)))
  have hsumC :
      Fintype.card (Set.range u) +
          Fintype.card (E \ Set.range u : Set (Fin (m + 1) → ℚ)) =
        Fintype.card E := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumDiffSubset hsubE)
  have hcardC : Fintype.card (E \ Set.range u : Set (Fin (m + 1) → ℚ)) = m - k := by
    omega
  let ψ : Fin (m - k) ≃ (E \ Set.range u : Set (Fin (m + 1) → ℚ)) :=
    (Fintype.equivFinOfCardEq hcardC).symm
  -- injective family of basis indices: `u`-part plus chosen complement
  let σ : (Fin (k + 1) ⊕ Fin (m - k)) → E := fun z =>
    match z with
    | Sum.inl i => ⟨u i, hsubE ⟨i, rfl⟩⟩
    | Sum.inr t => ⟨(ψ t : Fin (m + 1) → ℚ), (ψ t).2.1⟩
  have hσinj : Function.Injective σ := by
    rintro (i | t) (j | s) hab
    · simp [σ] at hab ⊢
      exact hu.injective hab
    · simp [σ] at hab ⊢
      exact False.elim ((ψ s).2.2 ⟨i, hab⟩)
    · simp [σ] at hab ⊢
      exact False.elim ((ψ t).2.2 ⟨j, hab.symm⟩)
    · simp [σ] at hab ⊢
      exact ψ.injective (Subtype.ext hab)
  have hσu : ∀ i : Fin (k + 1), (B (σ (Sum.inl i))) = u i := by
    intro i
    simp [σ]
    rw [Module.Basis.coe_extendLe]
  have hσv : ∀ t : Fin (m - k), (B (σ (Sum.inr t))) = (ψ t : Fin (m + 1) → ℚ) := by
    intro t
    simp [σ]
    rw [Module.Basis.coe_extendLe]
  have hGLI : LinearIndependent ℚ (fun z => B (σ z)) := by
    change LinearIndependent ℚ (⇑B ∘ σ)
    exact B.linearIndependent.comp σ hσinj
  refine ⟨fun t => (ψ t : Fin (m + 1) → ℚ), ?_, ?_⟩
  · intro t
    have hxE : (ψ t : Fin (m + 1) → ℚ) ∈ E := (ψ t).2.1
    have hxU : (ψ t : Fin (m + 1) → ℚ) ∉ Set.range u := (ψ t).2.2
    have hxV : (ψ t : Fin (m + 1) → ℚ) ∈ Set.range u ∪ Set.range v := hEsub hxE
    rcases hxV with hxu | hxv
    · exact False.elim (hxU hxu)
    · exact hxv
  · have hG : (fun z => B (σ z)) =
        Sum.elim u (fun t : Fin (m - k) => (ψ t : Fin (m + 1) → ℚ)) := by
      funext z
      cases z with
      | inl i => exact hσu i
      | inr t => exact hσv t
    simpa [hG] using hGLI

/-- Split `Fin (m + 1)` into the first `k + 1` positions and the rest. -/
def splitIdx (k m : ℕ) (hkm : k ≤ m) : Fin (m + 1) → (Fin (k + 1) ⊕ Fin (m - k)) :=
  fun i => if h : (i : ℕ) < k + 1 then Sum.inl ⟨(i : ℕ), h⟩
           else Sum.inr ⟨(i : ℕ) - (k + 1), by
             have hk : k + 1 ≤ (i : ℕ) := by omega
             have hlt : (i : ℕ) < m + 1 := i.isLt
             omega⟩

lemma splitIdx_injective {k m : ℕ} (hkm : k ≤ m) : Function.Injective (splitIdx k m hkm) := by
  intro a b hab
  by_cases ha : (a : ℕ) < k + 1
  · by_cases hb : (b : ℕ) < k + 1
    · simp [splitIdx, ha, hb] at hab ⊢
      apply Fin.ext
      exact hab
    · simp [splitIdx, ha, hb] at hab
  · by_cases hb : (b : ℕ) < k + 1
    · simp [splitIdx, ha, hb] at hab
    · simp [splitIdx, ha, hb] at hab ⊢
      apply Fin.ext
      omega

lemma splitIdx_inl {k m : ℕ} (hkm : k ≤ m) (i : Fin (k + 1)) :
    splitIdx k m hkm ⟨(i : ℕ), by omega⟩ = Sum.inl i := by
  have hlt : ((⟨(i : ℕ), by omega⟩ : Fin (m + 1)) : ℕ) < k + 1 := by
    simpa using i.isLt
  simp [splitIdx, hlt]

lemma splitIdx_big {k m : ℕ} (hkm : k ≤ m) (i : Fin (m + 1)) (hi : k < (i : ℕ)) :
    ∃ t : Fin (m - k), splitIdx k m hkm i = Sum.inr t := by
  by_cases h : (i : ℕ) < k + 1
  · exfalso
    omega
  · refine ⟨⟨(i : ℕ) - (k + 1), by omega⟩, ?_⟩
    simp [splitIdx, h]

/-- Extend the independent family `u` (with a top-degree vector) by vectors
from the independent degree-≤(m−1) family `v` to a full ℚ-basis of
`Fin (m+1) → ℚ`, keeping the first `k+1` entries equal to `u`. -/
theorem exists_basis_extension {m k : ℕ} (hkm : k ≤ m)
    (u : Fin (k + 1) → Fin (m + 1) → ℚ)
    (hu : LinearIndependent ℚ u)
    (hlead : ∃ i₀ : Fin (k + 1), u i₀ (Fin.last m) ≠ 0)
    (v : Fin m → Fin (m + 1) → ℚ)
    (hv : LinearIndependent ℚ v)
    (hvlast : ∀ j : Fin m, v j (Fin.last m) = 0) :
    ∃ F : Fin (m + 1) → Fin (m + 1) → ℚ,
      (∀ i : Fin (k + 1), F ⟨(i : ℕ), by omega⟩ = u i) ∧
      (∀ i : Fin (m + 1), k < (i : ℕ) → ∃ j : Fin m, F i = v j) ∧
      LinearIndependent ℚ F := by
  classical
  have hspan : Submodule.span ℚ (Set.range u ∪ Set.range v) = ⊤ := by
    exact span_u_union_v_eq_top hkm u hlead v hv hvlast
  rcases exists_ext_family hkm u hu v hspan with ⟨g, hgrange, hgli⟩
  let F : Fin (m + 1) → Fin (m + 1) → ℚ := fun i => (Sum.elim u g) (splitIdx k m hkm i)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    change (Sum.elim u g) (splitIdx k m hkm ⟨(i : ℕ), by omega⟩) = u i
    rw [splitIdx_inl hkm i]
    rfl
  · intro i hi
    rcases splitIdx_big hkm i hi with ⟨t, ht⟩
    dsimp [F]
    rw [ht]
    rcases hgrange t with ⟨j, hj⟩
    exact ⟨j, by simp [hj]⟩
  · change LinearIndependent ℚ (fun i => (Sum.elim u g) (splitIdx k m hkm i))
    exact hgli.comp (splitIdx k m hkm) (splitIdx_injective hkm)

end Submission.ExtendFamily
