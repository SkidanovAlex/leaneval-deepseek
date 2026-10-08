import Mathlib
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.clo_lemma8

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA

variable {P : Type} [Group P] [Finite P]

/-- **Kernel of the `2 ^ (e-1)`-st power map on `A`.**  Local copy of
`Work.Higman.mem_powSub_two_iff_of_homogeneous` (that module is currently entangled with a broken
work-in-progress file, so the proof is repeated here).  With the exponent data `2 ^ e` of the
homocyclic group `A` (`|A ^ (2 ^ i)| = q ^ (e - i)`), the subgroup `A²` is exactly the kernel of
the `2 ^ (e - 1)`-st power map on `A`. -/
theorem mem_powSub_two_iff_of_homogeneous {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {e : ℕ} (he : 1 ≤ e)
    (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hcard : ∀ i ≤ e, Nat.card ↥(Work.Higman.powSub A (2 ^ i))
      = (Nat.card ↥(A ⊓ Work.Higman.omega1 P)) ^ (e - i)) :
    ∀ y ∈ A, y ∈ Work.Higman.powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 := by
  intro y hy
  have he1 : 2 * 2 ^ (e - 1) = 2 ^ e := by rw [mul_comm, ← pow_succ]; congr 1; omega
  set q : ℕ := Nat.card ↥(A ⊓ Work.Higman.omega1 P) with hq
  have hqpos : 0 < q := Nat.card_pos
  constructor
  · intro hy2
    obtain ⟨z, hz, hzy⟩ := (Work.Higman.mem_powSub_iff hab).mp hy2
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
      have hmap : Subgroup.map A.subtype f.range = Work.Higman.powSub A (2 ^ (e - 1)) := by
        apply le_antisymm
        · rintro w ⟨z, hz, rfl⟩
          obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hz
          exact Work.Higman.pow_mem_powSub u.2
        · intro w hw
          rw [Work.Higman.mem_powSub_iff hab] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          exact ⟨⟨u, hu⟩ ^ 2 ^ (e - 1), ⟨⟨u, hu⟩, rfl⟩, rfl⟩
      have hcardmap := Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective
        (K := f.range)
      rw [hmap, hcard (e - 1) (by omega), Nat.sub_sub_self he, pow_one] at hcardmap
      exact hcardmap.symm
    have hcardA : Nat.card ↥A = q ^ e := by
      have h0 := hcard 0 (Nat.zero_le e)
      rw [pow_zero, Work.Higman.powSub_one_eq, Nat.sub_zero] at h0
      exact h0
    have hcard1 : Nat.card ↥(Work.Higman.powSub A 2) = q ^ (e - 1) := by
      have h1' := hcard 1 (by omega)
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num] at h1'
      exact h1'
    have hker : Nat.card ↥f.ker = q ^ (e - 1) := by
      have hcm := Work.Higman.card_ker_mul_card_range f
      rw [hrange, hcardA, hq] at hcm
      have heq : q ^ e = q ^ (e - 1) * q := by
        rw [← pow_succ]
        congr 1
        omega
      rw [heq] at hcm
      exact Nat.eq_of_mul_eq_mul_right hqpos hcm
    have hle : Work.Higman.powSub A 2 ≤ Subgroup.map A.subtype f.ker := by
      intro w hw
      obtain ⟨u, hu, huw⟩ := (Work.Higman.mem_powSub_iff hab).mp hw
      refine Subgroup.mem_map.mpr ⟨⟨u * u, A.mul_mem hu hu⟩, ?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ((u * u) ^ 2 ^ (e - 1) : P) = (1 : P)
        rw [show u * u = u ^ 2 from (pow_two u).symm, ← pow_mul, he1]
        exact h1 u hu
      · simpa [pow_two] using huw
    have hcard2 : Nat.card ↥(Subgroup.map A.subtype f.ker) = q ^ (e - 1) := by
      rw [Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective (K := f.ker), hker]
    have heqker : Work.Higman.powSub A 2 = Subgroup.map A.subtype f.ker :=
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

/-- **The exponent data of `A`** (Higman's Lemma 8, exponential parameters).  Under the
hypotheses of Higman's Lemma 8 with `A ≠ ⊥` and `A ^ 2 ≠ ⊥`, the homocyclic subgroup `A` has
exponent `2 ^ e` with `2 ≤ e`, contains `Ω₁(P)`, and the `2 ^ (e-1)`-st power map realizes
`A / A² ≅ Ω₁(P)`. -/
theorem l8_exp_data (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hAne : A ≠ ⊥) (hA2ne : Work.Higman.powSub A 2 ≠ ⊥) :
    ∃ e : ℕ, 2 ≤ e ∧ Work.Higman.omega1 P ≤ A ∧ (∀ a ∈ A, a ^ 2 ^ e = 1) ∧
      (Work.Higman.powSub A (2 ^ (e - 1)) = Work.Higman.omega1 P) ∧
      (∀ x ∈ A, x ∈ Work.Higman.powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) := by
  obtain ⟨e, he1, hcard, htop, _hclass⟩ :=
    Work.Higman.homogeneous_structure h hA.abelian hA.map_eq
  have hOm : Work.Higman.omega1 P ≤ A :=
    Work.Higman.omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · exfalso
      have hbot : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hh := he1 x hx
        simpa [he0] using hh
      exact hAne hbot
    · exact hpos
  have htopA : Work.Higman.powSub A (2 ^ (e - 1)) = Work.Higman.omega1 P := by
    rw [htop]
    exact inf_eq_right.mpr hOm
  have hkey : ∀ x ∈ A, x ∈ Work.Higman.powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1 :=
    mem_powSub_two_iff_of_homogeneous hA.abelian he he1 hcard
  refine ⟨e, ?_, hOm, he1, htopA, hkey⟩
  rcases (show e = 1 ∨ 2 ≤ e by omega) with h1 | h2
  · exfalso
    apply hA2ne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (Work.Higman.mem_powSub_iff hA.abelian).mp hy
    rw [h1] at he1
    simpa using he1 a ha
  · exact h2

end Work.Higman.MSA
