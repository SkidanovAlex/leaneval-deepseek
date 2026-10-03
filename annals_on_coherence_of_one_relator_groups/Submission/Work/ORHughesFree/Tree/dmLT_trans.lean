import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs

/-!
# Transitivity of the Dershowitz–Manna ordering on families of trees

`dmLT lt` is the Dershowitz–Manna (multiset) ordering on families of trees: `M` is below `N` if
`M = X + Y` and `N = X + Z` for some multisets `X`, `Y`, `Z` with `Z ≠ 0` such that every element of
`Y` is below some element of `Z` (`order_defs.lean`).  The main result here is that this relation is
transitive, as soon as the underlying relation `lt` is transitive *on the elements involved*
(hypothesis `hr`).  This restricted form is what the applications need: the tree order is only
available as a well-founded relation defined by recursion, and the relevant transitivity instances
are those between elements of `M`, `N` and `P`.

The argument is the one of [Dershowitz–Manna, *Proving termination with multiset orderings*, CACM
22 (1979)], with the transitivity of `lt` invoked only once (in the case where the element `b ∈ Z₁`
replacing `a ∈ Y₁` is itself replaced in the second step, `b ∈ Y₂`).  It is also the proof of
`Multiset.IsDershowitzMannaLT.trans` in Mathlib, which is the same statement for the `<` of a
`Preorder`; we reproduce it here for an arbitrary relation because the order `lt` on trees is not
(yet) packaged as `<` of a `Preorder` instance, and because `hr` is weaker than transitivity of
`lt`.

Given `M = X₁ + Y₁`, `N = X₁ + Z₁` and `N = X₂ + Y₂`, `P = X₂ + Z₂`, the composite decomposition is
`M = (X₁ ∩ X₂) + (Y₁ + (Y₂ \ Z₁))` and `P = (X₁ ∩ X₂) + (Z₂ + (Z₁ \ Y₂))`, i.e. the elements of `M`
that are replaced in the first step are replaced by their replacements, if the latter survive the
second step, and by the replacements of those replacements otherwise.
-/

namespace Work.ORHughesFree.Tree

theorem dmLT_trans {M N P : Multiset Tree}
    (hr : ∀ a ∈ M, ∀ b ∈ N, ∀ c ∈ P, lt a b → lt b c → lt a c)
    (hMN : dmLT lt M N) (hNP : dmLT lt N P) : dmLT lt M P := by
  classical
  obtain ⟨X₁, Y₁, Z₁, hZ₁, hM, hN₁, hYZ₁⟩ := hMN
  obtain ⟨X₂, Y₂, Z₂, hZ₂, hN₂, hP, hYZ₂⟩ := hNP
  -- `N` is decomposed in the two ways `X₁ + Z₁ = X₂ + Y₂`; the multiset lemma
  -- `inter_add_sub_of_add_eq_add` then computes the common parts.
  have hXX : Z₁ + X₁ = Y₂ + X₂ := by rw [add_comm Z₁ X₁, add_comm Y₂ X₂, ← hN₁, hN₂]
  have hsub₁ : (X₁ ∩ X₂) + (Y₂ - Z₁) = X₁ := Multiset.inter_add_sub_of_add_eq_add hXX
  have hsub₂ : (X₁ ∩ X₂) + (Z₁ - Y₂) = X₂ := by
    have h := Multiset.inter_add_sub_of_add_eq_add hXX.symm
    rwa [Multiset.inter_comm] at h
  refine ⟨X₁ ∩ X₂, Y₁ + (Y₂ - Z₁), Z₂ + (Z₁ - Y₂), ?_, ?_, ?_, ?_⟩
  · -- `Z₂ + (Z₁ - Y₂) ≠ 0`, since `Z₂ ≤ Z₂ + (Z₁ - Y₂)` and `Z₂ ≠ 0`
    intro h0
    have hle : Z₂ ≤ 0 := h0 ▸ Multiset.le_add_right Z₂ (Z₁ - Y₂)
    apply hZ₂
    rw [Multiset.ext]
    intro a
    rw [Multiset.le_iff_count] at hle
    have h1 := hle a
    rw [Multiset.count_zero] at h1
    rw [Multiset.count_zero]
    omega
  · -- `M = X₁ + Y₁ = (X₁ ∩ X₂) + (Y₁ + (Y₂ - Z₁))`
    calc M = X₁ + Y₁ := hM
      _ = ((X₁ ∩ X₂) + (Y₂ - Z₁)) + Y₁ := by conv_lhs => rw [← hsub₁]
      _ = (X₁ ∩ X₂) + (Y₁ + (Y₂ - Z₁)) := by ac_rfl
  · -- `P = X₂ + Z₂ = (X₁ ∩ X₂) + (Z₂ + (Z₁ - Y₂))`
    calc P = X₂ + Z₂ := hP
      _ = ((X₁ ∩ X₂) + (Z₁ - Y₂)) + Z₂ := by conv_lhs => rw [← hsub₂]
      _ = (X₁ ∩ X₂) + (Z₂ + (Z₁ - Y₂)) := by ac_rfl
  · intro a ha
    rcases Multiset.mem_add.mp ha with ha₁ | ha₂
    · -- `a ∈ Y₁`: it is replaced either by its replacement in `Z₁ \ Y₂`, or, if that replacement
      -- is itself replaced in the second step, by the replacement of the replacement (here `hr`).
      obtain ⟨b, hbZ₁, hab⟩ := hYZ₁ a ha₁
      by_cases hbY₂ : b ∈ Y₂
      · obtain ⟨c, hcZ₂, hbc⟩ := hYZ₂ b hbY₂
        exact ⟨c, Multiset.mem_add.mpr (Or.inl hcZ₂),
          hr a (by rw [hM]; exact Multiset.mem_add.mpr (Or.inr ha₁))
             b (by rw [hN₂]; exact Multiset.mem_add.mpr (Or.inr hbY₂))
             c (by rw [hP]; exact Multiset.mem_add.mpr (Or.inr hcZ₂)) hab hbc⟩
      · refine ⟨b, Multiset.mem_add.mpr (Or.inr ?_), hab⟩
        rw [Multiset.mem_sub, Multiset.count_eq_zero_of_notMem hbY₂]
        exact Multiset.count_pos.mpr hbZ₁
    · -- `a ∈ Y₂ - Z₁`: it is untouched by the first step, and is replaced in the second one
      have haY₂ : a ∈ Y₂ := Multiset.mem_of_le (Multiset.sub_le_self Y₂ Z₁) ha₂
      obtain ⟨c, hcZ₂, hac⟩ := hYZ₂ a haY₂
      exact ⟨c, Multiset.mem_add.mpr (Or.inl hcZ₂), hac⟩

end Work.ORHughesFree.Tree
