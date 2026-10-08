import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.commutator_powSub_A_C

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Higman.H8.bracket_radical`

Higman's Lemma 8, in the `CloH8Data` setting: an element `d ∈ C` whose bracket with every
element of `A` lands in `A ^ (4)` already lies in `A`.

The proof does not need any of the fine structure of the two layers.  The set

`radSub A C = {x ∈ C | ∀ a ∈ A, ⁅x, a⁆ ∈ A ^ (4)}`

is a subgroup of `P` (closed under multiplication by the standard commutator identity,
closed under inversion), it is normal in `P` (conjugation moves the second argument), and it is
`ξ`-invariant.  It contains `A` and is contained in `C`, so the minimality hypothesis `hcover`
on the `ξ`-section `C/A` forces `radSub A C = A` or `radSub A C = C`.  The second case would give
`⁅C,A⁆ ⊆ A ^ (4)`; but `⁅A,C⁆ = A ^ (2)` (the base case of `commutator_powSub_A_C`), so
`A ^ (2) = A ^ (4)`, i.e. `B := A ^ (2)` equals its own square subgroup.  If `B` is abelian
(which it is, being inside `A`) the squaring map on the finite group `↥B` is then surjective,
hence injective, so the only element of `B` with square `1` is `1`.  But `Ω₁(P) = A ^ (2 ^ (e-1))`
is contained in `A ^ (2)` and contains a non-trivial involution — contradiction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace Work.Higman.H8

section Basic

variable {P : Type} [Group P]

/-- An automorphism carries commutators to commutators. -/
theorem map_commutatorElement (φ : MulAut P) (x y : P) : φ ⁅x, y⁆ = ⁅φ x, φ y⁆ := by
  simp only [commutatorElement_def, map_mul, map_inv]

end Basic

/-- **The radical of the bracket pairing `C × A → A/A⁴`**: the elements of `C` whose brackets
with every element of `A` land in `A ^ (4)`. -/
def radSub {P : Type} [Group P] (A C : Subgroup P) [A.Normal] : Subgroup P where
  carrier := {x : P | x ∈ C ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ Work.Higman.powSub A 4}
  mul_mem' := by
    intro x y hx hy
    refine ⟨C.mul_mem hx.1 hy.1, fun a ha => ?_⟩
    have hx4 := hx.2 a ha
    have hy4 := hy.2 a ha
    have hc : x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ ∈ Work.Higman.powSub A 4 :=
      Subgroup.Normal.conj_mem (Work.Higman.powSub_normal (inferInstance : A.Normal) 4) _ hy4 x
    have hsplit : (x * y) * a * (x * y)⁻¹ * a⁻¹
        = (x * (y * a * y⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ hc hx4
  one_mem' := by
    refine ⟨C.one_mem, fun a _ => ?_⟩
    have h : (1 : P) * a * (1 : P)⁻¹ * a⁻¹ = 1 := by group
    rw [h]
    exact (Work.Higman.powSub A 4).one_mem
  inv_mem' := by
    intro x hx
    refine ⟨C.inv_mem hx.1, fun a ha => ?_⟩
    have hx4 := hx.2 a ha
    have hc : x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x ∈ Work.Higman.powSub A 4 := by
      have := Subgroup.Normal.conj_mem (Work.Higman.powSub_normal (inferInstance : A.Normal) 4)
        _ (Subgroup.inv_mem _ hx4) x⁻¹
      simpa using this
    have hsplit : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x := by group
    rw [hsplit]
    exact hc

section Rad

variable {P : Type} [Group P] [Finite P] {A C : Subgroup P} [A.Normal]

/-- The radical is normal in `P` (when `C` is): conjugating the first argument replaces the
second argument by its conjugate, and `A ^ (4)` is normal. -/
theorem radSub_normal (hCn : C.Normal) : (radSub A C).Normal := by
  refine Subgroup.Normal.mk (fun x hx p => ⟨hCn.conj_mem x hx.1 p, fun a ha => ?_⟩)
  have hx4 := hx.2 (p⁻¹ * a * p) (by
    have := Subgroup.Normal.conj_mem (inferInstance : A.Normal) a ha p⁻¹
    simpa using this)
  have hconj := Subgroup.Normal.conj_mem
    (Work.Higman.powSub_normal (inferInstance : A.Normal) 4) _ hx4 p
  have hsplit : (p * x * p⁻¹) * a * (p * x * p⁻¹)⁻¹ * a⁻¹
      = p * (x * (p⁻¹ * a * p) * x⁻¹ * (p⁻¹ * a * p)⁻¹) * p⁻¹ := by group
  rw [hsplit]
  exact hconj

/-- The radical is invariant under an automorphism preserving `A` and `C`. -/
theorem radSub_map_xi (h : Work.Higman.IsSuzuki2Grp P)
    (hA : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hC : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (radSub A C).map (h.xi : MulAut P).toMonoidHom = radSub A C := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨?_, fun a ha => ?_⟩
    · have : h.xi x ∈ C.map (h.xi : MulAut P).toMonoidHom := Subgroup.mem_map_of_mem _ hx.1
      rwa [hC] at this
    · have hb : (h.xi : MulAut P).symm a ∈ A := Work.Higman.symm_mem_of_map_eq h.xi hA ha
      have hx4 := hx.2 _ hb
      have h4 : h.xi ⁅x, (h.xi : MulAut P).symm a⁆ ∈ Work.Higman.powSub A 4 := by
        have := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) hx4
        rwa [Work.Higman.map_powSub (h.xi : MulAut P) hA 4] at this
      rwa [map_commutatorElement, MulEquiv.apply_symm_apply] at h4
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
    refine ⟨Work.Higman.symm_mem_of_map_eq h.xi hC hx.1, fun a ha => ?_⟩
    have hb : h.xi a ∈ A := by
      have := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) ha
      rwa [hA] at this
    have hx4 := hx.2 _ hb
    have h4 : h.xi ⁅(h.xi : MulAut P).symm x, a⁆ ∈ Work.Higman.powSub A 4 := by
      rw [map_commutatorElement, MulEquiv.apply_symm_apply]
      exact hx4
    have h5 := Work.Higman.symm_mem_of_map_eq h.xi
      (Work.Higman.map_powSub (h.xi : MulAut P) hA 4) h4
    simpa only [MulEquiv.symm_apply_apply, commutatorElement_def] using h5

end Rad

section FiniteAbelian

variable {P : Type} [Group P] [Finite P]

/-- In a finite abelian group, no non-trivial element can have square `1` if the group equals
its own square subgroup: squaring is then a surjective, hence injective, self-map. -/
theorem eq_one_of_mem_of_sq_one {B : Subgroup P}
    (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBB : Work.Higman.powSub B 2 = B)
    {x : P} (hx : x ∈ B) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hsurj : Function.Surjective (fun z : ↥B => z ^ 2) := by
    intro y
    have hy : (y : P) ∈ Work.Higman.powSub B 2 := by rw [hBB]; exact y.2
    rw [Work.Higman.mem_powSub_iff hab] at hy
    obtain ⟨z, hz, hzeq⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzeq⟩
  have hinj : Function.Injective (fun z : ↥B => z ^ 2) :=
    Finite.injective_iff_surjective.mpr hsurj
  have hx2B : (⟨x, hx⟩ : ↥B) ^ 2 = (1 : ↥B) ^ 2 := by
    rw [pow_two, pow_two]
    apply Subtype.ext
    show x * x = (1 : P) * 1
    rw [← pow_two, hx2, one_mul]
  have := hinj hx2B
  exact congrArg Subtype.val this

end FiniteAbelian

section Main

variable {P : Type} [Group P] [Finite P]

theorem bracket_radical {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A C : Subgroup P} [A.Normal] (S : CloH8Data h A C) {d : P} (hd : d ∈ C)
    (hrad : ∀ a ∈ A, d * a * d⁻¹ * a⁻¹ ∈ powSub A 4) : d ∈ A := by
  classical
  have hdK : d ∈ radSub A C := ⟨hd, hrad⟩
  have hAK : A ≤ radSub A C := by
    intro x hx
    refine ⟨S.hAC hx, fun a ha => ?_⟩
    have h1 : x * a * x⁻¹ * a⁻¹ = 1 := by
      rw [S.hA.abelian x hx a ha]
      group
    rw [h1]
    exact (powSub A 4).one_mem
  have hKC : radSub A C ≤ C := fun x hx => hx.1
  rcases S.hcover (radSub A C) (radSub_normal S.hCn)
      (radSub_map_xi h S.hA.map_eq S.hCinv) hAK hKC with hKA | hKC'
  · exact hKA ▸ hdK
  · exfalso
    -- `radSub A C = C` forces `⁅C,A⁆ ≤ A ^ (4)`
    have hCA4 : ⁅C, A⁆ ≤ powSub A 4 := by
      rw [Subgroup.commutator_le]
      intro c hc a ha
      have hcK : c ∈ radSub A C := by rw [hKC']; exact hc
      rw [commutatorElement_def]
      exact hcK.2 a ha
    -- the base case of the lower central series of `C`
    have hcomm0 : ⁅A, C⁆ = powSub A 2 := by
      have hh := commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 0
      simpa [powSub_one_eq] using hh
    have hA2leA4 : powSub A 2 ≤ powSub A 4 := by
      rw [← hcomm0, Subgroup.commutator_comm]
      exact hCA4
    have hA4leA2 : powSub A 4 ≤ powSub A 2 :=
      powSub_le_of_dvd S.hA.abelian (by norm_num)
    have hA2eq : powSub A 2 = powSub A 4 := le_antisymm hA2leA4 hA4leA2
    have hBB : powSub (powSub A 2) 2 = powSub A 2 := by
      rw [powSub_powSub S.hA.abelian 2 2, show (2:ℕ) * 2 = 4 from rfl, ← hA2eq]
    -- an involution inside `A ^ (2)`
    obtain ⟨x, y, hx2, _hy2, _hxy⟩ := h.manyInvol
    have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    have hxOm : x ∈ omega1 P := h.mem_omega1.mpr hx2'
    have hle : omega1 P ≤ powSub A 2 := by
      rw [← S.htopA]
      have he2 := S.he2
      have h2 : (2:ℕ) ^ (S.e - 1) = 2 * 2 ^ (S.e - 2) := by
        rw [show S.e - 1 = S.e - 2 + 1 from by omega, pow_succ']
      rw [h2]
      rw [← powSub_powSub S.hA.abelian 2 (2 ^ (S.e - 2))]
      exact powSub_le (by positivity)
    have hxB : x ∈ powSub A 2 := hle hxOm
    have habB : ∀ u ∈ powSub A 2, ∀ v ∈ powSub A 2, u * v = v * u :=
      powSub_comm S.hA.abelian 2
    have hx1 : x = 1 := eq_one_of_mem_of_sq_one habB hBB hxB hx2'
    exact (by rw [hx1, orderOf_one] at hx2; exact absurd hx2 (by norm_num))

end Main

end Work.Higman.H8
