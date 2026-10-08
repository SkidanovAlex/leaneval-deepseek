import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.SpecificGroups.PSL2_card_involutions_of_char_two
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.normalizer_le
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.sylow2_le
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_stabilizer_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.card_projectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.GroupTheory.Cardinality.card_pow_two_eq_one_eq_involutions_add_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of Sylow `2`-subgroups of `PSL(2, K)`, `K` of characteristic two

For a finite field `K` of characteristic two the projective special linear group
`PSL(2, K)` acts on the projective line `ℙ¹(K)`, which has `|K| + 1` points.  The Sylow
`2`-subgroups of `PSL(2, K)` are exactly the stabilizers of the points of the projective
line *in the unipotent sense*; in particular

`Nat.card (Sylow 2 (PSL(2, K))) = |K| + 1`.

The proof is a `2`-local computation together with the strongly embedded point stabiliser.
-/

set_option linter.style.haveILetI false

open scoped LinearAlgebra.Projectivization

namespace Commons.GroupTheory.SL2

/-- A finite group `H` whose set `{x | x ^ 2 = 1}` has the same cardinality as a subgroup
`S` all of whose elements satisfy `x ^ 2 = 1` must contain every such element in `S`.

Indeed the inclusion `S ↪ {x : H // x ^ 2 = 1}` is injective between finite types of equal
cardinality, hence bijective. -/
private lemma mem_of_sq_eq_one_of_card {H : Type*} [Group H] [Finite H] (S : Subgroup H)
    (hS : ∀ x ∈ S, x ^ 2 = 1)
    (hcard : Nat.card {x : H // x ^ 2 = 1} = Nat.card S) :
    ∀ x : H, x ^ 2 = 1 → x ∈ S := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : S → {x : H // x ^ 2 = 1} := fun y => ⟨(y : H), hS (y : H) y.2⟩
  have hf : Function.Injective f := by
    intro a b h
    have h' : ((a : H)) = ((b : H)) := by
      have hh := congrArg (fun z : {x : H // x ^ 2 = 1} => (z : H)) h
      simpa [f] using hh
    exact Subtype.ext h'
  have hcard' : Fintype.card S = Fintype.card {x : H // x ^ 2 = 1} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  have hsurj : Function.Surjective f :=
    Function.Injective.surjective_of_finite (Fintype.equivOfCardEq hcard') hf
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hyx : (y : H) = x := by
    have h := congrArg Subtype.val hy
    simpa [f] using h
  rw [← hyx]
  exact y.2

/-- Every Sylow `2`-subgroup of `PSL(2, K)` (`K` a finite field of characteristic two) has
`|K|` elements, each an involution: it is conjugate to the image of the subgroup of unipotent
matrices. -/
private lemma sylow_two_card_and_sq_one {K : Type*} [Field K] [Fintype K] (hchar : CharP K 2)
    (S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    Nat.card (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = Nat.card K ∧
      ∀ x : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)), x ^ 2 = 1 := by
  classical
  obtain ⟨S₀, hcard, hsq⟩ :=
    exists_sylow_two_elementaryAbelian_projectiveSpecialLinearGroup (K := K) hchar
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) S₀ S
  have hcoe : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =
      (S₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]; rfl
  refine ⟨?_, ?_⟩
  · rw [hcoe, Subgroup.card_map_of_injective (MulEquiv.injective _)]; exact hcard
  · intro x
    have hxmem : (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ∈
        (S₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map
          (MulAut.conj g).toMonoidHom := by
      rw [← hcoe]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmem
    have hy2 : y ^ 2 = 1 := by
      have h := congrArg (fun z : (S₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =>
        (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) (hsq ⟨y, hy⟩)
      simpa using h
    refine Subtype.ext ?_
    show (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ^ 2 = 1
    rw [show (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = MulAut.conj g y from hyx.symm,
      ← map_pow, hy2, map_one]

theorem card_sylow_two_projectiveSpecialLinearGroup {K : Type*} [Field K] [Fintype K]
    (hchar : CharP K 2) :
    Nat.card (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = Nat.card K + 1 := by
  classical
  haveI : CharP K 2 := hchar
  have hq2 : 2 ≤ Nat.card K := by
    have h : 1 < Fintype.card K := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card] at h
    omega
  -- a point of the projective line and its stabiliser
  let a0 : Projectivization K (Fin 2 → K) :=
    Projectivization.mk K (Pi.single 0 (1 : K)) (Pi.single_ne_zero_iff.2 one_ne_zero)
  set M : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a0 with hMdef
  have hSE := stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup (K := K) hchar hq2 a0
  rw [← hMdef] at hSE
  obtain ⟨hMtop, hMeven, hModd⟩ := hSE
  -- cardinality and index of `M`
  have hcardM : Nat.card M = Nat.card K * (Nat.card K - 1) := by
    rw [hMdef]; exact card_stabilizer_projectiveSpecialLinearGroup hchar hq2 a0
  have hcardG : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := card_projectiveSpecialLinearGroup hchar
  have hsub : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    have h := Nat.sq_sub_sq (Nat.card K) 1
    simpa using h
  have hMind : M.index = Nat.card K + 1 := by
    have h := Subgroup.index_mul_card M
    rw [hcardM, hcardG] at h
    have hq1 : 0 < Nat.card K * (Nat.card K - 1) :=
      Nat.mul_pos (by omega) (by omega)
    have hkey : M.index * (Nat.card K * (Nat.card K - 1)) =
        (Nat.card K + 1) * (Nat.card K * (Nat.card K - 1)) := by
      rw [h, hsub]; ring
    exact Nat.mul_right_cancel hq1 hkey
  -- the number of involutions of `M`
  have hinvG : Nat.card {t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K // orderOf t = 2} =
      Nat.card K ^ 2 - 1 :=
    Commons.GroupTheory.SpecificGroups.PSL2_card_involutions_of_char_two (F := K)
  have hinvM : Nat.card {t : M // orderOf t = 2} = Nat.card K - 1 := by
    have h := Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul M hMtop hMeven hModd
    rw [hinvG, hMind, hsub] at h
    exact (Nat.mul_left_cancel (by omega : 0 < Nat.card K + 1) h).symm
  have hpow2M : Nat.card {x : M // x ^ 2 = 1} = Nat.card K := by
    rw [Commons.GroupTheory.Cardinality.card_pow_two_eq_one_eq_involutions_add_one (G := M), hinvM]
    omega
  -- a Sylow `2`-subgroup of `G` inside `M`
  obtain ⟨U, hUle⟩ := Commons.GroupTheory.StronglyEmbedded.sylow2_le M hMtop hMeven hModd
  have hUspec := sylow_two_card_and_sq_one hchar U
  set Usub : Subgroup M :=
    (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).subgroupOf M with hUsubdef
  have hUsubcard : Nat.card Usub = Nat.card K := by
    have hmap := Subgroup.card_map_of_injective (Subgroup.subtype_injective M)
      (K := (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).subgroupOf M)
    rw [Subgroup.map_subgroupOf_eq_of_le hUle] at hmap
    rw [hUsubdef]
    exact hmap.symm.trans hUspec.1
  have hUsub_sq : ∀ x ∈ Usub, x ^ 2 = 1 := by
    intro x hx
    have hxU : ((x : M) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ∈
        (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
      Subgroup.mem_subgroupOf.mp (hUsubdef ▸ hx)
    have h := hUspec.2 ⟨((x : M) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K), hxU⟩
    have h2 : ((x : M) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
      have := congrArg (fun z : (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =>
        (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) h
      simpa using this
    refine Subtype.ext ?_
    simpa using h2
  have hmem : ∀ x : M, x ^ 2 = 1 → x ∈ Usub :=
    mem_of_sq_eq_one_of_card Usub hUsub_sq (by rw [hpow2M, hUsubcard])
  -- `M` normalizes `U`
  have key : ∀ (m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K), m ∈ M →
      ∀ u ∈ (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)),
        MulAut.conj m u ∈ (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := by
    intro m hm u hu
    have hzmem : m * u * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (hUle hu)) (M.inv_mem hm)
    have hz : (⟨m * u * m⁻¹, hzmem⟩ : M) ∈ Usub := by
      apply hmem
      apply Subtype.ext
      show (m * u * m⁻¹) ^ 2 = (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      have hu2 : u ^ 2 = 1 := by
        have h := hUspec.2 ⟨u, hu⟩
        have := congrArg (fun z : (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =>
          (z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) h
        simpa using this
      calc (m * u * m⁻¹) ^ 2 = m * u ^ 2 * m⁻¹ := by rw [pow_two, pow_two]; group
        _ = m * 1 * m⁻¹ := by rw [hu2]
        _ = 1 := by group
    have : m * u * m⁻¹ ∈ (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
      Subgroup.mem_subgroupOf.mp (hUsubdef ▸ hz)
    simpa [MulAut.conj_apply] using this
  have hMnorm : M ≤ Subgroup.normalizer
      (((U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map
        (MulAut.conj m).toMonoidHom ≤
        (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [MulAut.conj_apply] using key m hm u hu
    have hcard : Nat.card (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ≤
        Nat.card ((U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map
          (MulAut.conj m).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  have hNnorm : Subgroup.normalizer
      (((U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) ≤ M :=
    Commons.GroupTheory.StronglyEmbedded.normalizer_le M hMeven hModd U hUle
  have hNeq : Subgroup.normalizer
      (((U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) = M := le_antisymm hNnorm hMnorm
  rw [Sylow.card_eq_index_normalizer U]
  change (Subgroup.normalizer
    (((U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) : Set
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))).index = Nat.card K + 1
  rw [hNeq]
  exact hMind

end Commons.GroupTheory.SL2
