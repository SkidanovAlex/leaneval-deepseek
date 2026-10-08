import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.conj_mem_hatNp_and_notMem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- If `A` is a T. I. set of `X`, `m ∈ A` with `m ≠ 1`, and `x` centralizes `m`
(`x⁻¹ * m * x = m`), then `x` normalizes `A`: the first alternative of the T. I. condition is
refuted by the element `m ≠ 1` of `A ∩ x⁻¹ A x`. -/
theorem image_inv_conj_eq_of_mem_of_ti {X : Type*} [Group X] {A : Set X} (hTI : IsTISet A)
    {m x : X} (hm : m ∈ A) (hm1 : m ≠ 1) (hx : x⁻¹ * m * x = m) :
    (fun a => x⁻¹ * a * x) '' A = A := by
  rcases hTI x with h | h
  · exfalso
    have hmem : m ∈ ((fun a => x⁻¹ * a * x) '' A) ∩ A := ⟨⟨m, hm, hx⟩, hm⟩
    exact hm1 (by simpa using h hmem)
  · exact h

/-- **Feit–Thompson, Definition 9.1(ii)(e) (consequence).**  Let `K = 𝔎` be a non-trivial
subgroup of `X` such that `Ñ^# = hatNp K` is a T. I. set and `N(Ñ) = 𝔏 = N(𝔎)`.  Then for every
`m ∈ Ñ^#` the centralizer of `m` in `X` is contained in `𝔏`.

Indeed, `𝔎 ≠ ⊥` gives `Ñ = Ñ^# ∪ {1}`, and any `c` centralizing `m` fixes the non-identity element
`m` of `Ñ^#`; by the T. I. property it therefore conjugates `Ñ^#` onto itself, hence `Ñ` onto
itself, i.e. `c ∈ N(Ñ) = 𝔏`. -/
theorem centralizer_le_normalizer_of_mem_hatNp {X : Type*} [Group X] {K : Subgroup X}
    (hTI : Work.Tame.IsTISet (Work.Tame.hatNp K))
    (hN : Subgroup.normalizer (Work.Tame.hatN K) = Work.Tame.Lgrp K) {m : X}
    (hm : m ∈ Work.Tame.hatNp K) : Subgroup.centralizer ({m} : Set X) ≤ Work.Tame.Lgrp K := by
  obtain ⟨_hmLgrp, hmnotK, _hmcomm⟩ := mem_hatNp_iff.mp hm
  have hmne : m ≠ 1 := fun h1 => hmnotK (by rw [h1]; exact K.one_mem)
  have hK : K ≠ ⊥ := by
    intro hbot
    obtain ⟨H, hH, hH1, -⟩ := (mem_hatNp_iff.mp hm).2.2
    rw [hbot] at hH
    exact hH1 (Subgroup.mem_bot.mp hH)
  have hsplit : hatN K = hatNp K ∪ ({1} : Set X) := hatN_eq_hatNp_union_singleton hK
  intro c hc
  have hcm : c * m = m * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hx1 : c⁻¹ * m * c = m := by
    rw [mul_assoc, ← hcm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hx2 : c * m * c⁻¹ = m := by
    rw [hcm, mul_assoc, mul_inv_cancel, mul_one]
  have hA1 : (fun a => c⁻¹ * a * c) '' hatNp K = hatNp K :=
    image_inv_conj_eq_of_mem_of_ti hTI hm hmne (x := c) hx1
  have hA2 : (fun a => c * a * c⁻¹) '' hatNp K = hatNp K := by
    have h := image_inv_conj_eq_of_mem_of_ti hTI hm hmne (x := c⁻¹) (by simpa using hx2)
    simpa only [inv_inv] using h
  have hB1 : (fun a => c⁻¹ * a * c) '' hatN K = hatN K := by
    rw [hsplit, Set.image_union, Set.image_singleton, hA1]
    simp
  have hB2 : (fun a => c * a * c⁻¹) '' hatN K = hatN K := by
    rw [hsplit, Set.image_union, Set.image_singleton, hA2]
    simp
  have hcinv : c⁻¹ ∈ Subgroup.normalizer (hatN K) := by
    intro n
    constructor
    · intro hn
      have hmem : c⁻¹ * n * (c⁻¹)⁻¹ ∈ (fun a => c⁻¹ * a * c) '' hatN K :=
        ⟨n, hn, by simp only [inv_inv]⟩
      rwa [hB1] at hmem
    · intro hn
      have hn' : c⁻¹ * n * c ∈ hatN K := by simpa only [inv_inv] using hn
      have hmem : n ∈ (fun a => c * a * c⁻¹) '' hatN K := ⟨c⁻¹ * n * c, hn', by group⟩
      rwa [hB2] at hmem
  have hcN : c ∈ Subgroup.normalizer (hatN K) := by
    simpa using (Subgroup.normalizer (hatN K)).inv_mem hcinv
  rw [hN] at hcN
  exact hcN

end Work.Tame
