/-
Higman's auxiliary result 8, exponent data of `A`.

Setting: `P` is a Suzuki 2-group (with exposed automorphism `ξ`), and `A ≤ P` is a
`ξ`-invariant abelian normal subgroup with `A ≠ ⊥` and `A ^ (2) ≠ ⊥`, containing `Ω₁(P)`.

The conclusion is the *exponent data* of `A`: there is `e` with `2 ≤ e` such that `A` has exponent
`2 ^ e`, the `2 ^ (e-1)`-st power subgroup of `A` is exactly `Ω₁(P)` (so the power map
`a ↦ a ^ 2 ^ (e-1)` realizes `A / A² ≅ Ω₁(P)`), and `A²` is exactly the kernel of that power
map.

Everything is derived from Higman's Lemma 1 in its homocyclic form,
`Work.Higman.homogeneous_structure`: `A` has a uniform tower of power subgroups
`A > A² > A⁴ > ⋯ > Ω₁(P)` in which `|A ^ (2 ^ i)| = |A ⊓ Ω₁(P)| ^ (e - i)`.  The kernel
statement is then the counting argument comparing the kernel and the range of the
`2 ^ (e-1)`-st power map.

This module deliberately imports only `Work.Higman.homogeneous_structure` and
`Work.Higman.SuzukiMaximal`, so that it can be imported from `Work.Higman.clo_lemma8`
(the hypothesis `Ω₁(P) ≤ A` is available here directly, so no use of the step-1 lemma
`Work.Higman.omega1_le_of_isXiAbelNormal_ne_bot` is needed).
-/

import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.MSA

variable {P : Type} [Group P] [Finite P]

/-- **Kernel of the `2 ^ (e-1)`-st power map on `A`.**  Let `A` be an abelian subgroup of a finite
group `P` with exponent `2 ^ e` (`e ≥ 1`), whose power subgroups form the uniform tower
`|A ^ (2 ^ i)| = q ^ (e - i)` with `q = |A ⊓ Ω₁(P)|` (the cardinality conclusion of Higman's
Lemma 1).  Then `A²` is exactly the kernel of the `2 ^ (e-1)`-st power map on `A`. -/
theorem powSub_two_kernel_of_homogeneous {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ} (he : 1 ≤ e)
    (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hcard : ∀ i ≤ e, Nat.card ↥(powSub A (2 ^ i))
      = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - i)) :
    ∀ y ∈ A, y ∈ powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 := by
  intro y hy
  have he1 : 2 * 2 ^ (e - 1) = 2 ^ e := by rw [mul_comm, ← pow_succ]; congr 1; omega
  set q : ℕ := Nat.card ↥(A ⊓ omega1 P) with hq
  have hqpos : 0 < q := Nat.card_pos
  constructor
  · intro hy2
    obtain ⟨z, hz, hzy⟩ := (mem_powSub_iff hab).mp hy2
    rw [← hzy, ← pow_mul, he1]
    exact h1 z hz
  · intro hy1
    let f : ↥A →* ↥A :=
      { toFun := fun z => z ^ 2 ^ (e - 1)
        map_one' := by simp
        map_mul' := fun u v => by
          have hc : Commute u v := Subtype.ext (hab u u.2 v v.2)
          exact hc.mul_pow (2 ^ (e - 1)) }
    have hrange : Nat.card ↥f.range = q := by
      have hmap : Subgroup.map A.subtype f.range = powSub A (2 ^ (e - 1)) := by
        apply le_antisymm
        · rintro w ⟨z, hz, rfl⟩
          obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hz
          exact pow_mem_powSub u.2
        · intro w hw
          rw [mem_powSub_iff hab] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          exact ⟨⟨u, hu⟩ ^ 2 ^ (e - 1), ⟨⟨u, hu⟩, rfl⟩, rfl⟩
      have hcardmap := Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective
        (K := f.range)
      rw [hmap, hcard (e - 1) (by omega), Nat.sub_sub_self he, pow_one] at hcardmap
      exact hcardmap.symm
    have hcardA : Nat.card ↥A = q ^ e := by
      have h0 := hcard 0 (Nat.zero_le e)
      rw [pow_zero, powSub_one_eq, Nat.sub_zero] at h0
      exact h0
    have hcard1 : Nat.card ↥(powSub A 2) = q ^ (e - 1) := by
      have h1' := hcard 1 (by omega)
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at h1'
      exact h1'
    have hker : Nat.card ↥f.ker = q ^ (e - 1) := by
      have hcm := card_ker_mul_card_range f
      rw [hrange, hcardA, hq] at hcm
      have heq : q ^ e = q ^ (e - 1) * q := by
        rw [← pow_succ]
        congr 1
        omega
      rw [heq] at hcm
      exact Nat.eq_of_mul_eq_mul_right hqpos hcm
    have hle : powSub A 2 ≤ Subgroup.map A.subtype f.ker := by
      intro w hw
      obtain ⟨u, hu, huw⟩ := (mem_powSub_iff hab).mp hw
      refine Subgroup.mem_map.mpr ⟨⟨u * u, A.mul_mem hu hu⟩, ?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ((u * u) ^ 2 ^ (e - 1) : P) = (1 : P)
        rw [show u * u = u ^ 2 from (pow_two u).symm, ← pow_mul, he1]
        exact h1 u hu
      · simpa [pow_two] using huw
    have hcard2 : Nat.card ↥(Subgroup.map A.subtype f.ker) = q ^ (e - 1) := by
      rw [Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective (K := f.ker), hker]
    have heqker : powSub A 2 = Subgroup.map A.subtype f.ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
    have hyker : (⟨y, hy⟩ : ↥A) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change (⟨y, hy⟩ : ↥A) ^ 2 ^ (e - 1) = 1
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hy1
    have hy2 : y ∈ Subgroup.map A.subtype f.ker :=
      Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hyker, rfl⟩
    rwa [← heqker] at hy2

/-- **The exponent data of `A`** (Higman's Lemma 8, exponential parameters).

Let `A` be a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P`, with `A ≠ ⊥`,
`A ^ (2) ≠ ⊥` and `Ω₁(P) ≤ A`.  Then there is `e ≥ 2` such that

* `A` has exponent `2 ^ e` (so `2 ^ e` is the exponent parameter of the homocyclic group `A`);
* `A ^ (2 ^ (e-1)) = Ω₁(P)`, i.e. the `2 ^ (e-1)`-st power map realizes `A / A² ≅ Ω₁(P)`;
* `A²` is exactly the kernel of the `2 ^ (e-1)`-st power map on `A`.

The hypothesis `hOmega` (`Ω₁(P) ≤ A`) is exactly what is needed to replace `A ⊓ Ω₁(P)` by
`Ω₁(P)` in the structure theorem `Work.Higman.homogeneous_structure`. -/
theorem l8_setup {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hAne : A ≠ ⊥) (hA2ne : powSub A 2 ≠ ⊥)
    (hOmega : omega1 P ≤ A) :
    ∃ e : ℕ, 2 ≤ e ∧ (∀ a ∈ A, a ^ 2 ^ e = 1) ∧
      (powSub A (2 ^ (e - 1)) = omega1 P) ∧
      (∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) := by
  obtain ⟨e, he1, hcard, htop, -⟩ :=
    Work.Higman.homogeneous_structure h hA.abelian hA.map_eq
  -- `A` is non-trivial, so its exponent parameter `e` is at least `1`.
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · exfalso
      apply hAne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      simpa [he0] using he1 x hx
    · exact hpos
  -- `Ω₁(P) ≤ A` turns `A ⊓ Ω₁(P)` into `Ω₁(P)`.
  have htopA : powSub A (2 ^ (e - 1)) = omega1 P := by
    rw [htop]
    exact inf_eq_right.mpr hOmega
  -- the elementwise kernel statement
  have hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1 :=
    powSub_two_kernel_of_homogeneous hA.abelian he he1 hcard
  refine ⟨e, ?_, he1, htopA, hkey⟩
  -- `A ^ (2) ≠ ⊥` forces `e ≥ 2` (if `e ≤ 1` then `A² = ⊥`).
  rcases (show e = 1 ∨ 2 ≤ e by omega) with h1 | h2
  · exfalso
    apply hA2ne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hA.abelian).mp hy
    rw [h1] at he1
    simpa using he1 a ha
  · exact h2

end Work.Higman.MSA
