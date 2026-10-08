/-
**The rank-`1` BN-pair skeleton of `SU(3,2^n)`, re-derived from the abstract commons layer.**

The analogue for `PSU(3,2^n)` of `Submission.Sz.SuzukiCondition`: the Suzuki condition
`[SU(3,2^n) : B] = |U| + 1`, the trivial-intersection property `U ⊓ B^g = ⊥` for `g ∉ B` and the
fact that `U` is a Sylow `2`-subgroup are all obtained from the general rank-`1` BN-pair lemmas
in the shared commons rather than from model-specific cardinal arithmetic.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.StronglyEmbedded
import Submission.Work.Models.Port.PSU3.Sylow
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.subgroupOf_inf_map_conj_eq
import Submission.Work.Models.Port.Commons.GroupTheory.DoubleCoset.inf_map_conj_eq_bot_of_doubleCoset_cover
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover_of_notMem
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.PSU3

/-- The Weyl element `w` as an element of `SU(3,2^n)`. -/
noncomputable def suSgM (n : ℕ) : ↥(SU3 n) := ⟨suSg n, suSg_mem_SU3 n⟩

/-- The maximal torus `T` as a subgroup of `SU(3,2^n)`. -/
noncomputable abbrev suTS (n : ℕ) : Subgroup (↥(SU3 n)) := (suT n).subgroupOf (SU3 n)

lemma suUS_le_suBS (n : ℕ) : suUS n ≤ suBS n :=
  Subgroup.subgroupOf_mono (SU3 n) (by rw [suB]; exact le_sup_left)

lemma suSgM_notMem_suBS (n : ℕ) : suSgM n ∉ suBS n := fun h =>
  suSg_notMem_suB n (Subgroup.mem_subgroupOf.mp h)

/-- The Bruhat cover of `SU(3,2^n)` by `B` and the double coset `B w B`. -/
theorem suSg_cover (n : ℕ) (hn : 1 ≤ n) :
    ∀ g : ↥(SU3 n), g ∈ suBS n ∨ ∃ b₁ b₂ : ↥(suBS n),
      g = (b₁ : ↥(SU3 n)) * suSgM n * (b₂ : ↥(SU3 n)) := by
  intro g
  by_cases hg : g ∈ suBS n
  · exact Or.inl hg
  · right
    have hgB : (g : GL (Fin 3) (F n)) ∉ suB n := fun h => hg (Subgroup.mem_subgroupOf.mpr h)
    obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := (suSg_bruhat_cover n hn g.2).resolve_left hgB
    refine ⟨⟨⟨b₁, suB_le_SU3 n hb₁⟩, hb₁⟩, ⟨⟨b₂, suB_le_SU3 n hb₂⟩, hb₂⟩, ?_⟩
    apply Subtype.ext
    show (g : GL (Fin 3) (F n)) = b₁ * suSg n * b₂
    exact heq

/-- `B = U ⊔ T` inside `SU(3,2^n)`. -/
lemma suBS_eq_sup (n : ℕ) : suBS n = suUS n ⊔ suTS n := by
  rw [suBS, suUS, suTS, suB,
    Subgroup.subgroupOf_sup (suU_le_SU3 n) (suT_le_SU3 n)]

/-- `U ⊓ T = ⊥` inside `SU(3,2^n)`. -/
lemma suTS_inf_suUS (n : ℕ) : suUS n ⊓ suTS n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hxT⟩ := Subgroup.mem_inf.mp hx
  have hxU' : (x : GL (Fin 3) (F n)) ∈ suU n := Subgroup.mem_subgroupOf.mp hxU
  have hxT' : (x : GL (Fin 3) (F n)) ∈ suT n := Subgroup.mem_subgroupOf.mp hxT
  refine Subtype.ext ?_
  have h1 : (x : GL (Fin 3) (F n)) ∈ (⊥ : Subgroup (GL (Fin 3) (F n))) := by
    rw [← suU_inf_suT n]
    exact ⟨hxU', hxT'⟩
  simpa using h1

/-- The torus normalizes the unipotent radical inside `SU(3,2^n)`. -/
lemma suTS_le_normalizer_suUS (n : ℕ) :
    suTS n ≤ Subgroup.normalizer (suUS n : Set (↥(SU3 n))) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht y hy
  have ht' : (t : GL (Fin 3) (F n)) ∈ suT n := Subgroup.mem_subgroupOf.mp ht
  have hy' : (y : GL (Fin 3) (F n)) ∈ suU n := Subgroup.mem_subgroupOf.mp hy
  have hconj : (t : GL (Fin 3) (F n)) * (y : GL (Fin 3) (F n)) *
      (t : GL (Fin 3) (F n))⁻¹ ∈ suU n :=
    (Subgroup.le_normalizer_iff.mp (suT_le_normalizer_suU n)) t ht' y hy'
  change (((t * y * t⁻¹ : ↥(SU3 n))) : GL (Fin 3) (F n)) ∈ suU n
  have hcoe : (((t * y * t⁻¹ : ↥(SU3 n))) : GL (Fin 3) (F n)) =
      (t : GL (Fin 3) (F n)) * (y : GL (Fin 3) (F n)) *
        (t : GL (Fin 3) (F n))⁻¹ := by
    simp
  rw [hcoe]
  exact hconj

/-- The BN-pair intersection `B ⊓ B^w` inside `SU(3,2^n)` is the torus. -/
lemma suBS_inf_map_conj_eq (n : ℕ) :
    suBS n ⊓ (suBS n).map (MulAut.conj (suSgM n)).toMonoidHom = suTS n := by
  have hw : ((suSgM n : ↥(SU3 n)) : GL (Fin 3) (F n)) = suSg n := rfl
  rw [suBS, Commons.GroupTheory.Subgroup.subgroupOf_inf_map_conj_eq (suB n) (SU3 n)
    (suB_le_SU3 n) (suSgM n), suTS, hw]
  exact congrArg (fun H => H.subgroupOf (SU3 n)) (suB_inf_map_conj_suSg n)

/-- **The Suzuki condition** for `SU(3,2^n)`, from the abstract rank-`1` BN-pair theory. -/
theorem suBS_index_eq_one_add (n : ℕ) (hn : 1 ≤ n) :
    (suBS n).index = 1 + Nat.card ↥(suUS n) :=
  Commons.GroupTheory.Subgroup.index_eq_one_add_card_of_doubleCoset_cover_of_notMem
    (suUS n) (suTS n) (suBS n) (suSgM n)
    (suBS_eq_sup n) (suTS_inf_suUS n) (suTS_le_normalizer_suUS n)
    (suSg_cover n hn) (suSgM_notMem_suBS n) (by rw [suBS_inf_map_conj_eq n])

/-- `U ⊓ B^g = ⊥` for `g ∉ B`. -/
theorem suUS_inf_map_conj_eq_bot (n : ℕ) (hn : 1 ≤ n) {g : ↥(SU3 n)} (hg : g ∉ suBS n) :
    suUS n ⊓ (suBS n).map (MulAut.conj g).toMonoidHom = ⊥ :=
  Commons.GroupTheory.DoubleCoset.inf_map_conj_eq_bot_of_doubleCoset_cover
    (suTS n) (suBS n) (suSgM n) (suSg_cover n hn) (suBS_inf_map_conj_eq n)
    (suUS_le_suBS n) (suUS_isPGroup n hn)
    (by
      rw [suTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suT_le_SU3 n)).toEquiv,
        card_suT n hn]
      exact odd_two_pow_sub_one (2 * n) (by omega))
    hg

/-- `2 ^ (k+1) + 1` is odd. -/
lemma odd_two_pow_add_one_psu (k : ℕ) : Odd (2 ^ (k + 1) + 1) :=
  ⟨2 ^ k, by rw [pow_succ]; ring⟩

/-- `U` is a Sylow `2`-subgroup of `SU(3,2^n)`, via the abstract BN-pair lemma. -/
theorem not_dvd_index_suUS_commons (n : ℕ) (hn : 1 ≤ n) : ¬ 2 ∣ (suUS n).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard : Nat.card ↥(suUS n) = 2 ^ (3 * n) := by
    rw [suUS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)).toEquiv,
      card_suU n hn]
  have hT : ¬ 2 ∣ Nat.card ↥(suTS n) := by
    rw [suTS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suT_le_SU3 n)).toEquiv,
      card_suT n hn]
    intro h
    exact Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one (2 * n) (by omega))
      (even_iff_two_dvd.mpr h)
  have hB : ¬ 2 ∣ (suBS n).index := by
    rw [suBS_index_eq_one_add n hn, hUcard, Nat.add_comm]
    have hodd : Odd (2 ^ (3 * n) + 1) := by
      have h1 : (3 * n - 1) + 1 = 3 * n := Nat.sub_add_cancel (by omega)
      rw [← h1]
      exact odd_two_pow_add_one_psu (3 * n - 1)
    intro h
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h)
  exact Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup (p := 2) (suUS n) (suTS n)
    (suBS n) (suBS_eq_sup n) (suTS_inf_suUS n) (suTS_le_normalizer_suUS n)
    (suUS_isPGroup n hn) hT hB

end Submission.PSU3
