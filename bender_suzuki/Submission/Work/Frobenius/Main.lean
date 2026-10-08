import Mathlib
import Submission.Work.Frobenius.Kernel
import Submission.Work.Frobenius.Basic.isFrobeniusComplement_iff
import Submission.Work.Frobenius.Basic.coprime_card_of_isFrobeniusGroupWithKernel
import Submission.Work.Frobenius.Basic.normalizer_eq_of_isFrobeniusComplement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frobenius' theorem

If `H ≤ G` is a Frobenius complement (nontrivial, proper, meeting every conjugate trivially)
then the set `frobeniusKernel H` of fixed-point-free elements together with `1` is the carrier of
a normal subgroup `K` of `G` which is a complement to `H`:

* `frobenius_theorem`, and for any subgroup `K` with carrier `frobeniusKernel H` the consequences
  `frobenius_normal`, `frobenius_inf_eq_bot`, `frobenius_sup_eq_top`, `frobenius_isComplement'`,
  `frobenius_card_kernel_eq_index` (`|K| = [G : H]`) and `frobenius_coprime`;
* `frobenius_normalizer_eq`: a Frobenius complement is self-normalizing;
* `frobenius_fpf_iff`: the two descriptions of a Frobenius group agree.

The proof follows Isaacs, *Character Theory of Finite Groups*, Theorem 7.2: for `θ ∈ Irr H`,
`θ ≠ 1`, the class function `θ* = (θ - θ 1 · 1_H)^G + θ 1 · 1_G` has norm one, hence is (up to
sign, and the sign is excluded by positivity of the degree) an irreducible character of `G`, and
the intersection `K` of the kernels of these representations is the Frobenius kernel.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise

namespace Work.Frobenius

variable {G : Type*} [Group G] [Finite G]

/-- **Frobenius' theorem.**  The Frobenius kernel of a Frobenius complement is the carrier of a
normal complement. -/
theorem frobenius_theorem {H : Subgroup G} (hH : IsFrobeniusComplement H) :
    ∃ K : Subgroup G, (K : Set G) = frobeniusKernel H ∧ K.Normal ∧ IsComplement' K H := by
  letI : Fintype G := Fintype.ofFinite G
  exact ⟨kernelSubgroup hH, kernelSubgroup_eq_frobeniusKernel hH, kernelSubgroup_normal hH,
    isComplement'_kernelSubgroup hH⟩

/-- A subgroup with carrier the Frobenius kernel is nontrivial. -/
theorem kernel_ne_bot {K H : Subgroup G} (hH : IsFrobeniusComplement H)
    (hK : (K : Set G) = frobeniusKernel H) : K ≠ ⊥ := by
  letI : Fintype G := Fintype.ofFinite G
  intro hbot
  have hcard : Nat.card (K : Set G) = H.index := by
    rw [hK]
    exact Basic.card_frobeniusKernel hH
  rw [hbot] at hcard
  exact hH.ne_top (Subgroup.index_eq_one.mp (by simpa using hcard.symm))

section Consequences

variable {K H : Subgroup G} (hH : IsFrobeniusComplement H)
  (hK : (K : Set G) = frobeniusKernel H)

include hH hK

/-- A subgroup with carrier the Frobenius kernel is normal. -/
theorem frobenius_normal : K.Normal where
  conj_mem := fun n hn g => by
    have hn' : n ∈ frobeniusKernel H := by
      rw [← hK]
      exact hn
    have hg' : g * n * g⁻¹ ∈ frobeniusKernel H := conj_mem_frobeniusKernel hn'
    change g * n * g⁻¹ ∈ (K : Set G)
    rw [hK]
    exact hg'

/-- A subgroup with carrier the Frobenius kernel meets the complement trivially. -/
theorem frobenius_inf_eq_bot : K ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxH⟩ := Subgroup.mem_inf.mp hx
  have hxk : x ∈ frobeniusKernel H := hK ▸ hxK
  rw [mem_frobeniusKernel_of_mem_complement hxH] at hxk
  simpa [hxk]

/-- The order of a subgroup with carrier the Frobenius kernel is the index of the complement. -/
theorem frobenius_card_kernel_eq_index : Nat.card K = H.index := by
  letI : Fintype G := Fintype.ofFinite G
  have h : Nat.card (K : Set G) = H.index := by
    rw [hK]
    exact Basic.card_frobeniusKernel hH
  simpa using h

/-- A subgroup with carrier the Frobenius kernel is a complement of `H`. -/
theorem frobenius_isComplement' : IsComplement' K H := by
  letI : Fintype G := Fintype.ofFinite G
  rw [isComplement'_iff]
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [frobenius_card_kernel_eq_index hH hK, Subgroup.index_mul_card]
  · rw [disjoint_iff_inf_le]
    intro x hx
    rw [frobenius_inf_eq_bot hH hK] at hx
    exact hx

/-- A subgroup with carrier the Frobenius kernel and the complement generate `G`. -/
theorem frobenius_sup_eq_top : K ⊔ H = ⊤ := by
  letI : Fintype G := Fintype.ofFinite G
  have hc : Subgroup.IsComplement' K H := (isComplement'_iff K H).mp (frobenius_isComplement' hH hK)
  exact hc.sup_eq_top

/-- The orders of the Frobenius kernel and of the complement are coprime. -/
theorem frobenius_coprime : (Nat.card K).Coprime (Nat.card H) := by
  letI : Fintype G := Fintype.ofFinite G
  refine Basic.coprime_card_of_isFrobeniusGroupWithKernel
    ⟨frobenius_normal hH hK, frobenius_inf_eq_bot hH hK, frobenius_sup_eq_top hH hK, ?_⟩
  exact (Basic.isFrobeniusComplement_iff (frobenius_normal hH hK) (frobenius_inf_eq_bot hH hK)
    (frobenius_sup_eq_top hH hK) hH.ne_bot (kernel_ne_bot hH hK)).mp hH

end Consequences

/-- A Frobenius complement is self-normalizing. -/
theorem frobenius_normalizer_eq {H : Subgroup G} (hH : IsFrobeniusComplement H) :
    Subgroup.normalizer (H : Set G) = H :=
  Basic.normalizer_eq_of_isFrobeniusComplement hH

/-- A normal complement of a nontrivial complement is a Frobenius kernel exactly when the
complement acts fixed-point-freely. -/
theorem frobeniusGroupWithKernel_iff_fpf {K H : Subgroup G} (hK : K.Normal) (hinf : K ⊓ H = ⊥)
    (hsup : K ⊔ H = ⊤) (hHne : H ≠ ⊥) (hKne : K ≠ ⊥) :
    IsFrobeniusGroupWithKernel K H ↔ IsFrobeniusComplement H := by
  constructor
  · intro h
    exact (Basic.isFrobeniusComplement_iff hK hinf hsup hHne hKne).mpr h.fpf
  · intro h
    exact ⟨hK, hinf, hsup, (Basic.isFrobeniusComplement_iff hK hinf hsup hHne hKne).mp h⟩

/-- The two descriptions of a Frobenius group agree: if `K` is a normal complement of `H` with
`K ≠ ⊥`, then `H` is a Frobenius complement in `G` if and only if `H` acts fixed-point-freely
on `K`. -/
theorem frobenius_fpf_iff {K H : Subgroup G} (hK : K.Normal) (hinf : K ⊓ H = ⊥)
    (hsup : K ⊔ H = ⊤) (hHne : H ≠ ⊥) (hKne : K ≠ ⊥) :
    IsFrobeniusComplement H ↔ IsFixedPointFreeOn K H :=
  Basic.isFrobeniusComplement_iff hK hinf hsup hHne hKne

end Work.Frobenius
