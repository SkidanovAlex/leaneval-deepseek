import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.coherent_of_isometry_extension
import Submission.Work.Coherence.NormIrr
import Submission.Work.Coherence.exists_common_of_pairwise_inner_one_nonempty

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The norm-two lift: `Coherence.coherent_of_norm_two_lift`

Feit–Thompson's Lemma 10.1 (Peterfalvi's "coherence of `S` from the norm-two lifts"): if `S` is an
orthonormal set of functions on a finite group `H`, all of the same non-zero degree `d = x₀ 1`
(`x₀ ∈ S`), and `τ : ℤ[H → ℂ] → ℤ[G → ℂ]` is an isometry on `ℤ[S]^0` whose values
`τ (x - x₀)` (`x ∈ S`) are virtual characters of `G` of degree zero, then `S` is `τ`-coherent.

Since `S` is orthonormal and `x - x₀ ∈ ℤ[S]^0`, the isometry property gives
`⟨τ (x - x₀), τ (x - x₀)⟩ = ⟨x - x₀, x - x₀⟩ = 2` for `x ≠ x₀`, so each `τ (x - x₀)` is a
*difference* `χ x - ψ x` of two distinct irreducible characters of `G`
(`Coherence.vchar_norm_two_deg_zero_ordered`).  For `x ≠ y` the isometry property gives
`⟨τ (x - x₀), τ (y - x₀)⟩ = ⟨x - x₀, y - x₀⟩ = 1`, i.e.
`⟨χ x - ψ x, χ y - ψ y⟩ = 1`; Feit–Thompson's combinatorial lemma
(`Coherence.exists_common_of_pairwise_inner_one_nonempty`) then produces a single irreducible
character `Ψ` which is one member of every pair:

* `∀ x ∈ S \ {x₀}, χ x = Ψ`, in which case `τ (x - x₀) = Ψ - ψ x`, or
* `∀ x ∈ S \ {x₀}, ψ x = Ψ`, in which case `τ (x - x₀) = χ x - Ψ`.

Set `c := -Ψ` in the first case and `c := Ψ` in the second.  Then `c` is a virtual character with
`⟨c, c⟩ = 1` and `⟨c, τ (x - x₀)⟩ = -1` for every `x ∈ S`; consequently the lift

`φ x := τ (x - x₀) + c`

is a virtual character of `G` with `φ x₀ = c`, it satisfies the shift condition
`φ x - τ x = φ x₀ - τ x₀` (both sides equal `c - τ x₀`) and the orthogonality condition
`⟨φ x₀, φ x⟩ = ⟨x₀, x⟩` (`= 0` for `x ≠ x₀`, `= 1` for `x = x₀`).  The extension lemma
`Coherence.coherent_of_isometry_extension` then yields `Coherent S τ`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

variable {G : Type*}

/-- **Ordered form** of `Coherence.vchar_norm_two_deg_zero`: a virtual character of `G` of norm
two and degree zero is the difference `χ - ψ` of two *distinct* irreducible characters, in that
order. -/
theorem vchar_norm_two_deg_zero_ordered {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : IsVChar f) (h1 : f 1 = 0) (h : cfInner f f = 2) :
    ∃ χ ∈ Irr G, ∃ ψ ∈ Irr G, χ ≠ ψ ∧ f = χ - ψ := by
  obtain ⟨χ, hχ, ψ, hψ, hne, hcase⟩ := vchar_norm_two_deg_zero hf h1 h
  rcases hcase with h' | h'
  · exact ⟨χ, hχ, ψ, hψ, hne, h'⟩
  · exact ⟨ψ, hψ, χ, hχ, hne.symm, h'⟩

theorem coherent_of_norm_two_lift {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Orthonormal S) {x₀ : H → ℂ} (hx₀ : x₀ ∈ S) (hdeg : ∀ x ∈ S, x 1 = x₀ 1)
    (hd : x₀ 1 ≠ 0) (hτ : IsometryOn S τ)
    (hvchar : ∀ x ∈ S, IsVChar (τ (x - x₀)))
    (hdeg0 : ∀ x ∈ S, (τ (x - x₀)) 1 = 0)
    (hcard : 2 ≤ S.card) : Coherent S τ := by
  classical
  -- `x - x₀` lies in the degree-zero lattice `ℤ[S]^0`, for `x ∈ S`.
  have hsub_mem : ∀ x ∈ S, x - x₀ ∈ ZSpan0 S := fun x hx => by
    rw [mem_zSpan0]
    exact ⟨AddSubgroup.sub_mem _ (self_mem_zSpan hx) (self_mem_zSpan hx₀),
      by rw [Pi.sub_apply, hdeg x hx, sub_self]⟩
  -- The isometry property gives `⟨τ (x - x₀), τ (x - x₀)⟩ = ⟨x - x₀, x - x₀⟩ = 2` for `x ≠ x₀`.
  have hnorm : ∀ x ∈ S, x ≠ x₀ → cfInner (τ (x - x₀)) (τ (x - x₀)) = 2 := by
    intro x hx hxne
    rw [hτ.inner_eq (x - x₀) (hsub_mem x hx) (x - x₀) (hsub_mem x hx)]
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hS x hx x hx,
        hS x hx x₀ hx₀, hS x₀ hx₀ x hx, hS x₀ hx₀ x₀ hx₀]
    rw [ite_eq_right hxne, ite_eq_right (Ne.symm hxne)]
    norm_num
  -- Each `τ (x - x₀)`, `x ≠ x₀`, is an ordered difference of two distinct irreducibles.
  have hex : ∀ i : ↥(S.erase x₀), ∃ p : (G → ℂ) × (G → ℂ),
      p.1 ∈ Irr G ∧ p.2 ∈ Irr G ∧ p.1 ≠ p.2 ∧ τ ((i : H → ℂ) - x₀) = p.1 - p.2 := by
    intro i
    obtain ⟨hine, hiS⟩ := Finset.mem_erase.mp i.2
    obtain ⟨χ, hχ, ψ, hψ, hne, hdiff⟩ :=
      vchar_norm_two_deg_zero_ordered (hvchar _ hiS) (hdeg0 _ hiS) (hnorm _ hiS hine)
    exact ⟨(χ, ψ), hχ, hψ, hne, hdiff⟩
  let p : ↥(S.erase x₀) → (G → ℂ) × (G → ℂ) := fun i => Classical.choose (hex i)
  let A : ↥(S.erase x₀) → (G → ℂ) := fun i => (p i).1
  let B : ↥(S.erase x₀) → (G → ℂ) := fun i => (p i).2
  have hp : ∀ i : ↥(S.erase x₀), A i ∈ Irr G ∧ B i ∈ Irr G ∧ A i ≠ B i ∧
      τ ((i : H → ℂ) - x₀) = A i - B i := fun i => Classical.choose_spec (hex i)
  -- `S \ {x₀}` is non-empty, by `2 ≤ S.card`.
  have hcardι : 0 < Fintype.card ↥(S.erase x₀) := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hx₀]
    omega
  -- The finite orthonormal set of irreducibles carrying the common element.
  let T : Finset (G → ℂ) := (Finset.univ.image A) ∪ (Finset.univ.image B)
  have hTsub : (↑T : Set (G → ℂ)) ⊆ Irr G := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact (hp i).1
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact (hp i).2.1
  have hT : Orthonormal T := irr_orthonormal_finset hTsub
  have hAmem : ∀ i, A i ∈ T := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem A (Finset.mem_univ i))
  have hBmem : ∀ i, B i ∈ T := fun i =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem B (Finset.mem_univ i))
  -- `⟨x - x₀, y - x₀⟩ = 1` for distinct `x, y ∈ S \ {x₀}`.
  have hinner : ∀ i j : ↥(S.erase x₀), i ≠ j →
      cfInner ((i : H → ℂ) - x₀) ((j : H → ℂ) - x₀) = 1 := by
    intro i j hij
    have hiS : (i : H → ℂ) ∈ S := (Finset.mem_erase.mp i.2).2
    have hjS : (j : H → ℂ) ∈ S := (Finset.mem_erase.mp j.2).2
    have hine : (i : H → ℂ) ≠ x₀ := (Finset.mem_erase.mp i.2).1
    have hjne : (j : H → ℂ) ≠ x₀ := (Finset.mem_erase.mp j.2).1
    have hij' : (i : H → ℂ) ≠ (j : H → ℂ) := fun h => hij (Subtype.ext h)
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
        hS (i : H → ℂ) hiS (j : H → ℂ) hjS, hS (i : H → ℂ) hiS x₀ hx₀,
        hS x₀ hx₀ (j : H → ℂ) hjS, hS x₀ hx₀ x₀ hx₀,
        ite_eq_right hij', ite_eq_right hine, ite_eq_right (Ne.symm hjne)]
    norm_num
  -- Hence `⟨A i - B i, A j - B j⟩ = 1` for `i ≠ j`.
  have horth : ∀ i j : ↥(S.erase x₀), i ≠ j → cfInner (A i - B i) (A j - B j) = 1 := by
    intro i j hij
    rw [← (hp i).2.2.2, ← (hp j).2.2.2]
    rw [hτ.inner_eq ((i : H → ℂ) - x₀) (hsub_mem _ (Finset.mem_erase.mp i.2).2)
          ((j : H → ℂ) - x₀) (hsub_mem _ (Finset.mem_erase.mp j.2).2)]
    exact hinner i j hij
  -- Feit–Thompson's combinatorial lemma: a common element for the family of pairs.
  obtain ⟨Ψ, hΨT, hcase⟩ :=
    exists_common_of_pairwise_inner_one_nonempty hT A B hAmem hBmem
      (fun i => (hp i).2.2.1) horth hcardι
  have hΨirr : Ψ ∈ Irr G := hTsub hΨT
  -- The constant correction `c`, with `⟨c, c⟩ = 1` and `⟨c, τ (x - x₀)⟩ = -1`.
  have hkey : ∃ c : G → ℂ, IsVChar c ∧ cfInner c c = 1 ∧
      ∀ i : ↥(S.erase x₀), cfInner c (τ ((i : H → ℂ) - x₀)) = -1 := by
    rcases hcase with hcase | hcase
    · -- every `χ` is `Ψ`, so `τ (x - x₀) = Ψ - ψ x` and `c = -Ψ`
      refine ⟨-Ψ, (isVChar_of_mem_Irr hΨirr).neg, ?_, ?_⟩
      · rw [cfInner_neg_left, cfInner_neg_right, irr_cfInner hΨirr hΨirr]
        norm_num
      · intro i
        have hΨBi : Ψ ≠ B i := fun h => (hp i).2.2.1 ((hcase i).trans h)
        have hti : τ ((i : H → ℂ) - x₀) = Ψ - B i := by rw [(hp i).2.2.2, hcase i]
        rw [cfInner_neg_left, hti, cfInner_sub_right, irr_cfInner hΨirr hΨirr,
            irr_cfInner hΨirr (hp i).2.1, ite_eq_left rfl, ite_eq_right hΨBi]
        norm_num
    · -- every `ψ` is `Ψ`, so `τ (x - x₀) = χ x - Ψ` and `c = Ψ`
      refine ⟨Ψ, isVChar_of_mem_Irr hΨirr, ?_, ?_⟩
      · rw [irr_cfInner hΨirr hΨirr]
        norm_num
      · intro i
        have hΨAi : Ψ ≠ A i := fun h => (hp i).2.2.1 (h.symm.trans (hcase i).symm)
        have hti : τ ((i : H → ℂ) - x₀) = A i - Ψ := by rw [(hp i).2.2.2, hcase i]
        rw [hti, cfInner_sub_right, irr_cfInner hΨirr (hp i).1, irr_cfInner hΨirr hΨirr,
            ite_eq_right hΨAi, ite_eq_left rfl]
        norm_num
  obtain ⟨c, hcV, hcc, hckey⟩ := hkey
  -- The lift `φ x = τ (x - x₀) + c` has all the properties required by the extension lemma.
  refine coherent_of_isometry_extension (φ := fun x => τ (x - x₀) + c)
    hS hx₀ hdeg hd hτ ?_ ?_ ?_
  · intro x hx
    show cfInner (τ (x₀ - x₀) + c) (τ (x - x₀) + c) = cfInner x₀ x
    rw [sub_self, map_zero, zero_add]
    by_cases hxx : x = x₀
    · rw [hxx, sub_self, map_zero, zero_add, hcc, hS x₀ hx₀ x₀ hx₀, ite_eq_left rfl]
    · have hk : cfInner c (τ (x - x₀)) = -1 := hckey ⟨x, Finset.mem_erase.mpr ⟨hxx, hx⟩⟩
      rw [cfInner_add_right, hk, hcc, hS x₀ hx₀ x hx, ite_eq_right (Ne.symm hxx)]
      norm_num
  · intro x hx
    show (τ (x - x₀) + c) - τ x = (τ (x₀ - x₀) + c) - τ x₀
    rw [map_sub, sub_self, map_zero, zero_add]
    abel
  · intro x hx
    exact (hvchar x hx).add hcV

end Work.Coherence
