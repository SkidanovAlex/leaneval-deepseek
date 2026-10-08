/-
`PSU(3, 2^n)` has a strongly embedded subgroup.

The Borel subgroup `B = U ⋊ T` of `SU(3, 2^n)` is strongly embedded
(`suB_stronglyEmbedded`).  The projection `SU(3, 2^n) → PSU(3, 2^n)` is surjective
with kernel the centre `Z = Z(SU(3,2^n))` of order `gcd(3, q+1)`, which is odd and
central; moreover `Z ≤ B` because the scalar matrices fix the line `[e_0]` and the
point stabiliser of `[e_0]` is exactly `B`.  A general transfer lemma for strong
embedding along a surjection with central odd kernel then yields that the image
`B/Z` is strongly embedded in `PSU(3,2^n)`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.StronglyEmbedded
import Submission.Work.Models.Port.PSU3.PSU3Order
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective
import Submission.Work.Models.Port.PSU3.Perfect

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open Matrix LeanEval.GroupTheory.Defs
open scoped MatrixGroups

namespace Submission.PSU3

/-! ## The transfer lemma -/

/-- Strong embedding is preserved by a surjective homomorphism with central kernel of odd
order contained in the strongly embedded subgroup (commons lemma
`Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective`). -/
theorem isStronglyEmbedded_map_of_surjective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (φ : G →* H) (hφ : Function.Surjective φ) (M : Subgroup G)
    (hM : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hker : φ.ker ≤ M) (hcent : φ.ker ≤ Subgroup.center G) (hkerodd : Odd (Nat.card φ.ker)) :
    (M.map φ ≠ ⊤) ∧ Even (Nat.card (M.map φ)) ∧
      ∀ h : H, h ∉ M.map φ →
        Odd (Nat.card ((M.map φ ⊓ (M.map φ).map (MulAut.conj h).toMonoidHom : Subgroup H))) :=
  Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective φ hφ M hM hEven
    hOdd hker hcent hkerodd

/-! ## Finiteness of the projective group -/

instance instFinitePGL (n : ℕ) : Finite (ProjGenLinGroup (Fin 3) (F n)) :=
  Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) (F n) →* _) ProjGenLinGroup.mk_surjective

instance instFinitePSU3Model (n : ℕ) : Finite ↥(PSU3Model n) := Subtype.finite

/-! ## The projection `SU(3,2^n) → PSU(3,2^n)` -/

/-- The canonical surjection `SU(3,2^n) → PSU(3,2^n)`. -/
noncomputable def psu3Hom (n : ℕ) : ↥(SU3 n) →* ↥(PSU3Model n) :=
  ((ProjGenLinGroup.mk : GL (Fin 3) (F n) →* ProjGenLinGroup (Fin 3) (F n)).comp
    (SU3 n).subtype).codRestrict (PSU3Model n) (by
      intro x
      show ProjGenLinGroup.mk (x : GL (Fin 3) (F n)) ∈ PSU3Model n
      rw [PSU3Model_eq_map_SU3]
      exact Subgroup.mem_map.mpr ⟨(x : GL (Fin 3) (F n)), x.2, rfl⟩)

@[simp] lemma psu3Hom_apply (n : ℕ) (x : ↥(SU3 n)) :
    (psu3Hom n x : ProjGenLinGroup (Fin 3) (F n))
      = ProjGenLinGroup.mk (x : GL (Fin 3) (F n)) := rfl

lemma psu3Hom_surjective (n : ℕ) : Function.Surjective (psu3Hom n) := by
  intro y
  have hy : (y : ProjGenLinGroup (Fin 3) (F n)) ∈ (SU3 n).map ProjGenLinGroup.mk := by
    rw [← PSU3Model_eq_map_SU3]; exact y.2
  obtain ⟨A, hA, hAy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨A, hA⟩, Subtype.ext hAy⟩

/-- The kernel of `SU(3,2^n) → PSU(3,2^n)`, viewed in `GL`, is the centre of `SU(3,2^n)`. -/
lemma psu3Hom_ker_eq (n : ℕ) :
    (psu3Hom n).ker
      = (SU3 n ⊓ Subgroup.center (GL (Fin 3) (F n))).subgroupOf (SU3 n) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    have h : (psu3Hom n x : ProjGenLinGroup (Fin 3) (F n)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [psu3Hom_apply] at h
    exact ⟨x.2, ProjGenLinGroup.mk_eq_one.mp h⟩
  · rintro ⟨-, h⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    rw [psu3Hom_apply]
    simpa using ProjGenLinGroup.mk_eq_one.mpr h

/-- The centre of `SU(3,2^n)` is contained in the centre of `SU(3,2^n)` as a group, i.e. the
kernel of the projection is central. -/
lemma psu3Hom_ker_le_center (n : ℕ) : (psu3Hom n).ker ≤ Subgroup.center ↥(SU3 n) := by
  intro x hx
  have hx1 : (x : GL (Fin 3) (F n)) ∈ Subgroup.center (GL (Fin 3) (F n)) := by
    have h := hx
    rw [psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
    exact h.2
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hx1 (y : GL (Fin 3) (F n))

/-- The kernel of `SU(3,2^n) → PSU(3,2^n)` has order `gcd(3, q+1)`. -/
lemma card_psu3Hom_ker (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (psu3Hom n).ker = Nat.gcd 3 (2 ^ n + 1) := by
  rw [psu3Hom_ker_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    card_su3_center n hn]

/-- The kernel of `SU(3,2^n) → PSU(3,2^n)` has odd order. -/
lemma odd_card_psu3Hom_ker (n : ℕ) (hn : 1 ≤ n) : Odd (Nat.card (psu3Hom n).ker) := by
  rw [card_psu3Hom_ker n hn]
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (2 ^ n + 1)) with h | h <;>
    rw [h] <;> norm_num

/-- Every scalar matrix lies in the Borel subgroup: it fixes the line `[e_0]`. -/
lemma scalar_mem_suB (n : ℕ) {u : (F n)ˣ} (hu : IsSU3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u)) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ suB n := by
  rw [mem_suB_iff_smul n _ hu]
  refine ⟨(u : F n), Units.ne_zero u, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i
  fin_cases i <;> simp [suE0, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply]

/-- The kernel of `SU(3,2^n) → PSU(3,2^n)` is contained in the Borel subgroup. -/
lemma psu3Hom_ker_le_borel (n : ℕ) : (psu3Hom n).ker ≤ (suB n).subgroupOf (SU3 n) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hx1 : (x : GL (Fin 3) (F n)) ∈ Subgroup.center (GL (Fin 3) (F n)) := by
    have h := hx
    rw [psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
    exact h.2
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx1
  rw [← hu]
  exact scalar_mem_suB n (by rw [hu]; exact x.2)

/-- **`PSU(3,2^n)` has a strongly embedded subgroup** (the image of the Borel). -/
theorem PSU3Model_exists_isStronglyEmbedded (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Subgroup (PSU3Model n), IsStronglyEmbedded M := by
  have hn1 : 1 ≤ n := by omega
  have hB := suB_stronglyEmbedded n hn1
  refine ⟨((suB n).subgroupOf (SU3 n)).map (psu3Hom n), ?_⟩
  have h := isStronglyEmbedded_map_of_surjective (psu3Hom n) (psu3Hom_surjective n)
    ((suB n).subgroupOf (SU3 n)) hB.1 hB.2.1 hB.2.2 (psu3Hom_ker_le_borel n)
    (psu3Hom_ker_le_center n) (odd_card_psu3Hom_ker n hn1)
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **`PSU(3,2^n)` is perfect.** -/
theorem isPerfect_PSU3Model (n : ℕ) (hn : 2 ≤ n) : Group.IsPerfect ↥(PSU3Model n) := by
  haveI : Group.IsPerfect ↥(SU3 n) := isPerfect_SU3 n hn
  exact Group.IsPerfect.ofSurjective (f := psu3Hom n) (psu3Hom_surjective n)

/-- `PSU(3,2^n)` is one of the three families of the Bender–Suzuki classification. -/
theorem PSU3Model_isSimpleBenderGroup (n : ℕ) (hn : 2 ≤ n) :
    IsSimpleBenderGroup (PSU3Model n) :=
  IsSimpleBenderGroup.isPSU3 n hn (MulEquiv.refl _)

end Submission.PSU3
