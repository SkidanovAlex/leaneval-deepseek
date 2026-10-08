import Submission.Work.Coherence.Isometry
import Submission.Work.Coherence.coherent_mono
import Submission.Work.Coherence.coherent_of_isometry_extension

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The basic API of coherent sets

Feit–Thompson Definition 10.1 / Peterfalvi: `Coherent S τ` means that `τ : ℤ[H → ℂ] → ℤ[G → ℂ]`
can be extended from the degree-zero lattice `ℤ[S]^0` to an isometry of the whole lattice `ℤ[S]`
whose values on `S` are virtual characters of `G`.  Here we record the elementary consequences:
the empty set is coherent, coherence is hereditary under subsets, and a coherent extension sends
*all* of `ℤ[S]` to virtual characters of `G`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

variable {H G : Type*}

section CoherentAPI

variable [Group H] [Fintype H] [Group G] [Fintype G]

/-- The empty set is coherent: take the zero extension. -/
theorem coherent_empty {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)} :
    Coherent (∅ : Finset (H → ℂ)) τ := by
  refine ⟨0, ?_, ?_, ?_⟩
  · intro α hα
    have hz : α ∈ ZSpan (∅ : Finset (H → ℂ)) := zSpan0_le_zSpan (∅ : Finset (H → ℂ)) hα
    obtain ⟨c, hc⟩ := mem_zSpan.mp hz
    rw [hc]
    simp
  · refine ⟨fun α hα β hβ => ?_⟩
    obtain ⟨c, hc⟩ := mem_zSpan.mp hα
    obtain ⟨d, hd⟩ := mem_zSpan.mp hβ
    rw [hc, hd]
    simp
  · intro χ hχ
    exact absurd hχ (Finset.notMem_empty χ)

/-- **A coherent extension is a virtual character on all of the lattice.**  If `S` is `τ`-coherent
then `τ` extends to an isometry `τ'` of `ℤ[S]` such that `τ' α` is a virtual character of `G` for
every `α ∈ ℤ[S]` (not merely for `α ∈ S`). -/
theorem coherent_isVChar_of_mem_zSpan {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : Coherent S τ) :
    ∃ τ' : (H → ℂ) →ₗ[ℤ] (G → ℂ),
      (∀ α ∈ ZSpan0 S, τ' α = τ α) ∧ IsometryOnAll S τ' ∧
        (∀ α ∈ ZSpan S, IsVChar (τ' α)) := by
  obtain ⟨τ', hagree, hiso, hvchar⟩ := h
  refine ⟨τ', hagree, hiso, fun α hα => ?_⟩
  obtain ⟨c, hc⟩ := mem_zSpan.mp hα
  rw [hc, map_sum]
  refine IsVChar.sum Finset.univ (fun x : S => τ' ((c x : ℂ) • (x : H → ℂ))) fun x _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul]
  exact (hvchar (x : H → ℂ) x.2).zsmul (c x)

/-- A `τ` which is already an isometry of `ℤ[S]` and sends `S` to virtual characters of `G` is
coherent (with itself as the required extension). -/
theorem coherent_of_isometryOnAll {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hτ : IsometryOnAll S τ) (hchar : ∀ χ ∈ S, IsVChar (τ χ)) : Coherent S τ :=
  ⟨τ, fun _ _ => rfl, hτ, hchar⟩

/-- Coherence implies that `τ` itself is an isometry on `ℤ[S]^0`. -/
theorem coherent_isometryOn {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : Coherent S τ) : IsometryOn S τ := by
  obtain ⟨τ', hagree, hiso, -⟩ := h
  refine ⟨fun α hα β hβ => ?_⟩
  rw [← hagree α hα, ← hagree β hβ]
  exact hiso.inner_eq α (zSpan0_le_zSpan S hα) β (zSpan0_le_zSpan S hβ)

/-- Coherence depends on `τ` only through its restriction to `ℤ[S]^0`. -/
theorem coherent_congr {S : Finset (H → ℂ)} {τ σ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : ∀ α ∈ ZSpan0 S, τ α = σ α) : Coherent S τ ↔ Coherent S σ := by
  constructor
  · rintro ⟨τ', hagree, hiso, hchar⟩
    exact ⟨τ', fun α hα => by rw [← h α hα]; exact hagree α hα, hiso, hchar⟩
  · rintro ⟨τ', hagree, hiso, hchar⟩
    exact ⟨τ', fun α hα => by rw [h α hα]; exact hagree α hα, hiso, hchar⟩

/-- **Coherence as the existence of a norm-preserving lift of `S`.**

For `S` orthonormal with all elements of the same non-zero degree, and `τ` an isometry on
`ℤ[S]^0`, the set `S` is `τ`-coherent if and only if there is a *single* family
`φ : (H → ℂ) → (G → ℂ)` of virtual characters of `G` which reproduces the `x₀`-row of the Gram
matrix of `S` and differs from `τ` by a constant on `S`.

This is the sharp form of Feit–Thompson Definition 10.1: the (hard) direction `⟸` is
`coherent_of_isometry_extension`, the (easy) direction `⟹` restricts the coherent extension `τ'`
to `S`. -/
theorem coherent_iff_exists_lift {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Orthonormal S) {x₀ : H → ℂ} (hx₀ : x₀ ∈ S) (hdeg : ∀ x ∈ S, x 1 = x₀ 1)
    (hd : x₀ 1 ≠ 0) (hτ : IsometryOn S τ) :
    Coherent S τ ↔ ∃ φ : (H → ℂ) → (G → ℂ),
      (∀ x ∈ S, cfInner (φ x₀) (φ x) = cfInner x₀ x) ∧
      (∀ x ∈ S, φ x - τ x = φ x₀ - τ x₀) ∧
      (∀ x ∈ S, IsVChar (φ x)) := by
  constructor
  · intro h
    obtain ⟨τ', hagree, hiso, hchar⟩ := h
    refine ⟨τ', fun x hx => ?_, fun x hx => ?_, fun x hx => hchar x hx⟩
    · exact hiso.inner_eq x₀ (self_mem_zSpan hx₀) x (self_mem_zSpan hx)
    · have hmem : x - x₀ ∈ ZSpan0 S := by
        refine mem_zSpan0.mpr ⟨AddSubgroup.sub_mem _ (self_mem_zSpan hx) (self_mem_zSpan hx₀), ?_⟩
        simp [Pi.sub_apply, hdeg x hx]
      have hxx : τ' x - τ' x₀ = τ x - τ x₀ := by
        have := hagree (x - x₀) hmem
        rwa [map_sub, map_sub] at this
      have hzero : τ' x - τ x - (τ' x₀ - τ x₀) = 0 := by
        rw [sub_eq_zero]
        calc τ' x - τ x = (τ' x - τ' x₀) + (τ' x₀ - τ x) := by abel
          _ = (τ x - τ x₀) + (τ' x₀ - τ x) := by rw [hxx]
          _ = τ' x₀ - τ x₀ := by abel
      exact sub_eq_zero.mp hzero
  · rintro ⟨φ, horth, hshift, hchar⟩
    exact coherent_of_isometry_extension hS hx₀ hdeg hd hτ horth hshift hchar

end CoherentAPI

end Work.Coherence
