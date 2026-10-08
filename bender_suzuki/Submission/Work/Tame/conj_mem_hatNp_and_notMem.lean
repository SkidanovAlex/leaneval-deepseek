import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.one_mem_hatN

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The T. I. structure of `Ñ^#` (Feit–Thompson, Definition 9.1(ii)(e))

Let `L̂` be tamely imbedded in the finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n`
(Definition 9.1), and suppose `𝔇 ≠ ∅` so that the system of supporting subgroups is present.

This file records the elementary normalizer/T. I. content of axiom (ii)(e), namely that for each
supporting subgroup `K = 𝔎_j` the set `Ñ_j^# = hatNp K` behaves as a normal subset of its
normalizer and as a T. I. set away from it:

* `y ∈ 𝔏_j = N(𝔎_j)` conjugates every element of `Ñ_j^#` into `Ñ_j^#`;
* any `x ∉ 𝔏_j` conjugates no element of `Ñ_j^#` into `Ñ_j^#`.

Both halves follow from `N(Ñ_j) = N(𝔎_j)` and the T. I. property of `Ñ_j^#`.  The second half is
the reason `Ñ_j^#` is a *T. I. set*: the alternative in the T. I. condition in which the
conjugate set coincides with `Ñ_j^#` would force `x` into the normalizer of `Ñ_j`, hence into
`𝔏_j`.

## Main result

* `Work.Tame.conj_mem_hatNp_and_notMem`
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

/-- For a non-trivial subgroup `𝔎`, `Ñ = Ñ^# ∪ {1}`: since `𝔎 ≠ ⊥`, the identity lies in `Ñ`
(`one_mem_hatN`), and every other element of `Ñ` is a non-identity element of `Ñ`. -/
theorem hatN_eq_hatNp_union_singleton {X : Type*} [Group X] {K : Subgroup X} (hK : K ≠ ⊥) :
    hatN K = hatNp K ∪ ({1} : Set X) := by
  ext b
  rw [Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro hb
    by_cases hb1 : b = 1
    · exact Or.inr hb1
    · exact Or.inl (mem_punct.mpr ⟨hb, hb1⟩)
  · rintro (hb | hb)
    · exact (mem_punct.mp hb).1
    · rw [hb]; exact one_mem_hatN hK

/-- **Feit–Thompson, Definition 9.1(ii)(e).**  Let `L̂` be tamely imbedded in a finite group `X`
with supporting subgroups `𝔎_1, …, 𝔎_n`, and suppose `𝔇 ≠ ∅`.  For a fixed supporting subgroup
`𝔎_j = K`:

* `𝔏_j = N(𝔎_j)` normalizes `Ñ_j^#`: every `y ∈ 𝔏_j` sends `a ∈ Ñ_j^#` to `y a y⁻¹ ∈ Ñ_j^#`;
* any `x ∉ 𝔏_j` conjugates no element of `Ñ_j^#` into `Ñ_j^#`: for `a ∈ Ñ_j^#`,
  `x⁻¹ a x ∉ Ñ_j^#`. -/
theorem conj_mem_hatNp_and_notMem {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) (j : Fin n) :
    (∀ y : X, y ∈ Lgrp (Hs j : Set X) → ∀ a : X, a ∈ hatNp (Hs j) → y * a * y⁻¹ ∈ hatNp (Hs j)) ∧
    (∀ x : X, x ∉ Lgrp (Hs j : Set X) → ∀ a : X, a ∈ hatNp (Hs j) → x⁻¹ * a * x ∉ hatNp (Hs j)) := by
  have hK : Hs j ≠ ⊥ := h.supp_ne_bot hne j
  -- `N(Ñ_j) = 𝔏_j`, axiom (ii)(e).
  have hnorm : Subgroup.normalizer (hatN (Hs j)) = Lgrp (Hs j : Set X) := h.supp_hatN_norm hne j
  constructor
  · -- `𝔏_j` lies in `N(Ñ_j)`, so conjugation preserves `Ñ_j`, hence `Ñ_j^#`.
    intro y hy a ha
    obtain ⟨haN, ha1⟩ := mem_punct.mp ha
    have hy' : y ∈ Subgroup.normalizer (hatN (Hs j)) := hnorm.symm ▸ hy
    have hmem : y * a * y⁻¹ ∈ hatN (Hs j) := (mem_Lgrp.mp hy' a).mp haN
    refine mem_punct.mpr ⟨hmem, ?_⟩
    intro h1
    apply ha1
    have := congrArg (fun t => y⁻¹ * t * y) h1
    simpa [mul_assoc] using this
  · -- The T. I. alternative: either the conjugate set meets `Ñ_j^#` trivially, or it *is* `Ñ_j^#`.
    intro x hx a ha hconj
    rcases h.supp_ti hne j x with hA | hB
    · -- `(Ñ_j^#)^x ∩ Ñ_j^# ⊆ {1}`: then `x⁻¹ a x = 1`, impossible.
      have hmem : x⁻¹ * a * x ∈ ({1} : Set X) := hA ⟨⟨a, ha, rfl⟩, hconj⟩
      rw [Set.mem_singleton_iff] at hmem
      exact (mem_punct.mp hconj).2 hmem
    · -- `(Ñ_j^#)^x = Ñ_j^#` would force `x ∈ N(Ñ_j) = 𝔏_j`, contra `hx`.
      exfalso
      have hsplit := hatN_eq_hatNp_union_singleton (K := Hs j) hK
      have hstab : ∀ b : X, b ∈ hatN (Hs j) ↔ x⁻¹ * b * x ∈ hatN (Hs j) := by
        intro b
        rw [hsplit, Set.mem_union, Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
        constructor
        · rintro (hb | hb)
          · left
            have : x⁻¹ * b * x ∈ (fun a => x⁻¹ * a * x) '' hatNp (Hs j) := ⟨b, hb, rfl⟩
            rwa [hB] at this
          · right
            rw [hb]; group
        · rintro (hb | hb)
          · left
            have : x⁻¹ * b * x ∈ (fun a => x⁻¹ * a * x) '' hatNp (Hs j) := by rw [hB]; exact hb
            obtain ⟨c, hc, hceq⟩ := this
            have hcb : c = b := by
              have h1 := mul_right_cancel hceq
              exact mul_left_cancel h1
            rwa [hcb] at hc
          · right
            have := congrArg (fun t => x * t * x⁻¹) hb
            simpa [mul_assoc] using this
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (hatN (Hs j)) := by
        intro b
        simpa using hstab b
      rw [hnorm] at hxinv
      exact hx (by simpa using (Lgrp (Hs j : Set X)).inv_mem hxinv)

end Work.Tame
