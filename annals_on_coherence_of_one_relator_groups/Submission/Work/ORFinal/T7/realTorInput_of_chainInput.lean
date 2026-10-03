/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# T7: the JL §5 flatness input from the dimension-shifting chain

This file proves `Work.ORFinal.T7.realTorInput_of_chainInput`: the JL §5 flatness input
`Work.ORFinal.RealTorInput` (the hypothesis `hTor` of the ring half) from the dimension-shifting
chain `Work.ORFinal.ChainInput` (JL Lemma 5.2, node N1/T6).

The assembly is the one described in `Submission/Work/ORFinal/T7_ROUTE.md`: for a real coefficient
field `L`, an embedding `ψ : L →+* ℝ` and a Magnus configuration `(r, u, l, t, Y)`, form the M1
Linnell datum `Ld` of the canonical envelope `E` of `G = ⟨Fin n | r⟩`, the `TorsionData` `T` of the
bridge (`Work.ORFinal.T7.torsionDataOfRoot`), and feed

* `hA`     — JL Lemma 5.1′ (`Work.ORFinal.hA_of_torsion_pow` fed with
             `Work.ORBridgeTor.torsionFree_tensor_diagRight`, Claim 5.9
             `Work.ORLyndon.rootVec_support_injOn` and the non-vanishing of the Fox component
             `Work.ORLyndon.rootVec_ne_zero_of_mem_relatorLetters`),
* `hswap`  — JL Lemma 5.2(2) (`Work.ORBridgeTor.hswap_of_jl52` fed with the antipode
             `Work.ORFinal.Antiaut.antiAutOfStar_torsionData`),
* `hchain` — the dimension-shifting chain (the hypothesis of the statement),

into `Work.ORLyndon.magnus_torTwoVanishes`.

## Main declarations

* `Work.ORFinal.T7.torsionDataOfRoot` — the bridge `LinnellDatum → TorsionData`, with the root
  retained definitionally;
* `Work.ORFinal.T7.realTorInput_of_chainInput` — the target theorem.
-/
import Mathlib
import Submission.Work.ORFinal.ChainDefs
import Submission.Work.ORFinal.Final
import Submission.Work.ORFinal.TorsionData.torsionDataOf
import Submission.Work.ORFinal.TorsionPow
import Submission.Work.ORFinal.Antiaut.antiAutOfStar
import Submission.Work.ORFinal.Antiaut.StarTorsionData
import Submission.Work.ORLyndon.LyndonFlatness
import Submission.Work.ORBridgeTor.HA
import Submission.Work.ORBridgeTor.HSwap
import Submission.Work.ORBridgeTor.torsionFree_tensor_diagRight
import Submission.Work.ORLyndon.annAtOfTorsionDataRoot
import Submission.Work.ORLyndon.rootVec_ne_zero_of_mem_relatorLetters
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORLocInd.Main
import Submission.Work.ORFinal.T7.torsionDataAtDatum
import Submission.Work.ORFinal.T7.star_algebraMap_of_real
import Submission.Work.OROneRel.isCyclicallyReducedRelator_of_pow
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.ORLyndon.relatorLetters_pow_clean

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open Work
open scoped TensorProduct

namespace Work.ORFinal.T7

/-! ## The bridge `LinnellDatum → TorsionData`, with a transparent root

`Work.ORFinal.TorsionData.torsionDataOf` and `Work.ORFinal.T7.exists_torsionData_eq` return only a
`Nonempty`/`∃`, so their witnesses are opaque (`Classical.choice`): the fields `gen` and `D` of the
result cannot be unfolded.  The consumers of the datum in this file (`hA` at the datum via
`Work.ORBridgeTor.torsionFree_tensor_diagRight`, the antipode via
`Work.ORFinal.Antiaut.antiAutOfStar_torsionData`, and finally the comparison of
`MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop` with `Work.ORAssembly.LinData.toS`) need `T.D = Dsub L`
and `T.gen = L.gen` definitionally, so we spell out the same structure literal as a `def`. -/
noncomputable def torsionDataOfRoot (K : Type) [Field K] [CharZero K] (G : Type) [Group G]
    (U : Type) [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex] (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (u : G) (hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure {u})) :
    Work.ORTorsion.TorsionData K G U := by
  refine ⟨L.gen, Work.ORFinal.TorsionData.Dsub L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u, hq, ?_⟩
  · intro H h; exact L.gen_mem H h
  · intro H₁ H₂ h; exact Work.ORFinal.TorsionData.Dsub_mono L h
  · intro H; exact L.isDivisionClosed H
  · intro H A hA hclosed
    exact L.minimal H A.toSubring (fun h => hA h) (fun k => A.algebraMap_mem k) hclosed
  · intro H n g hg a ha hsum i; exact L.independence H n g hg a ha hsum i
  · intro g H x hx; exact L.conjugation g H x hx
  · intro H
    exact Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn K G U L G'
      (inferInstance : G'.Normal) (inferInstance : G'.FiniteIndex)
      (fun x hx => hdiv G' hG'tf x hx) H
  · intro H φ hφ; exact Work.ORFinal.TorsionData.laurentBaseOf L G' hG'tf hdiv H φ hφ

@[simp] theorem torsionDataOfRoot_u (K : Type) [Field K] [CharZero K] (G : Type) [Group G]
    (U : Type) [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex] (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (u : G) (hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure {u})) :
    (torsionDataOfRoot K G U L G' hG'tf hdiv u hq).u = u := rfl

@[simp] theorem torsionDataOfRoot_gen (K : Type) [Field K] [CharZero K] (G : Type) [Group G]
    (U : Type) [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex] (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (u : G) (hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure {u})) :
    (torsionDataOfRoot K G U L G' hG'tf hdiv u hq).gen = L.gen := rfl

/-- **A variant of `Work.ORFinal.hA_of_torsion_pow` adapted to the relation module.**

In the intended application the module `A` is `K[G] ⧸ K[G]·(ug - 1)`, and the product
`(ug - 1) * c` is *not* a left multiple of `ug - 1` for arbitrary `c`.  The element `c` built in the
proof below, however, lies in the commutative subring `K[ug]`, so the statement is given with the
product written the other way round: `(c * (ug - 1)) • ae = 0` is a *left* multiple and hence always
holds for the relation module.  The proof is that of `Work.ORFinal.hA_of_torsion_pow`, with the
telescope of the geometric sum exchanged. -/
theorem hA_of_torsion_pow_comm (K : Type) [Field K] [CharZero K] (G : Type) [Group G]
    (S : Type) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (ug : MonoidAlgebra K G) (l : ℕ) (hl : 0 < l)
    (ν β₀ : MonoidAlgebra K G) (hν : ν = ∑ i ∈ Finset.range l, ug ^ i)
    {A : Type} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    {B : Type} [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    (f : A →ₗ[MonoidAlgebra K G] B) (ae : A)
    (hgen : ∀ a : A, ∃ r : MonoidAlgebra K G, a = r • ae)
    (hae : ∀ c : MonoidAlgebra K G, (c * (ug - 1)) • ae = 0)
    (π : B →ₗ[MonoidAlgebra K G] (MonoidAlgebra K G))
    (hπf : π (f ae) = ν * β₀)
    (hβ₀ : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (fun x : S ⊗[K] M => (MulOpposite.op β₀) • x)) :
    ∀ (M : Type) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f) := by
  intro M _ _ _ _ _
  letI := Work.ORFlatness.diagRightModule K G S φ M
  set S' : MonoidAlgebra K G := ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, ug ^ j with hS'
  set c : MonoidAlgebra K G := -((l : K)⁻¹ • S') with hc
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  have hcast : (l : K)⁻¹ • (l : MonoidAlgebra K G) = 1 := by
    rw [Algebra.smul_def, ← map_natCast (algebraMap K (MonoidAlgebra K G)) l, ← map_mul,
      inv_mul_cancel₀ hl0, map_one]
  have htel : ∀ i : ℕ, (∑ j ∈ Finset.range i, ug ^ j) * (ug - 1) = ug ^ i - 1 := by
    intro i
    rw [Finset.sum_mul]
    have hterm : ∀ j : ℕ, ug ^ j * (ug - 1) = ug ^ (j + 1) - ug ^ j := by
      intro j
      rw [mul_sub, mul_one, pow_succ]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [Finset.sum_range_sub (fun j => ug ^ j), pow_zero]
  have hsub : S' * (ug - 1) = ν - (l : MonoidAlgebra K G) := by
    rw [hS', Finset.sum_mul, hν,
      Finset.sum_congr rfl (fun i _ => htel i), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hone : c * (ug - 1) = 1 - (l : K)⁻¹ • ν := by
    rw [hc, neg_mul, smul_mul_assoc, hsub, smul_sub, hcast, neg_sub]
  have key : ∀ z : Work.ORFlatness.BalTensor (MonoidAlgebra K G) (S ⊗[K] M) A,
      Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f z = 0 → z = 0 := by
    intro z hz
    have hmem : ∀ (x : S ⊗[K] M) (a : A),
        Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x a ∈
          (Work.ORFlatness.BalTensor.mkLeft (MonoidAlgebra K G) ae).range := by
      intro x a
      obtain ⟨r, rfl⟩ := hgen a
      refine ⟨MulOpposite.op r • x, ?_⟩
      show Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) (MulOpposite.op r • x) ae
        = Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (r • ae)
      rw [Work.ORFlatness.BalTensor.mk_smul_right]
    have hzrange : z ∈ (Work.ORFlatness.BalTensor.mkLeft (MonoidAlgebra K G) ae).range :=
      (AddSubgroup.closure_le _).mpr (by
        rintro y ⟨⟨x, a⟩, rfl⟩
        exact hmem x a)
        (Work.ORFlatness.BalTensor.mem_closure_mk (R := MonoidAlgebra K G) z)
    obtain ⟨x, hx⟩ := hzrange
    have hx' : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x ae = z := hx
    have h1 : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (f ae) = 0 := by
      rw [← hx'] at hz
      rw [Work.ORFlatness.BalTensor.map_mk] at hz
      simpa using hz
    have h2 : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (ν * β₀) = 0 := by
      have h3 : Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
          (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) π
          (Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (f ae)) = 0 := by
        rw [h1, map_zero]
      rw [Work.ORFlatness.BalTensor.map_mk, LinearMap.id_coe, id_eq, hπf] at h3
      exact h3
    have h4 : (MulOpposite.op (ν * β₀)) • x = 0 :=
      (Work.ORBridgeTor.balTensor_mk_eq_zero_iff (MonoidAlgebra K G) (S ⊗[K] M) x (ν * β₀)).mp h2
    have h5 : (MulOpposite.op ν) • x = 0 := by
      have h6 : (MulOpposite.op β₀) • ((MulOpposite.op ν) • x) = 0 := by
        rw [← mul_smul, ← MulOpposite.op_mul, h4]
      exact hβ₀ M (by
        show (MulOpposite.op β₀) • ((MulOpposite.op ν) • x) = (MulOpposite.op β₀) • (0 : S ⊗[K] M)
        rw [h6, smul_zero])
    have h7 : x = (MulOpposite.op (1 - (l : K)⁻¹ • ν)) • x := by
      have h9 : (1 : MonoidAlgebra K G) - (l : K)⁻¹ • ν
          = 1 - ν * ((l : K)⁻¹ • (1 : MonoidAlgebra K G)) := by
        rw [Algebra.smul_def (l : K)⁻¹ ν, Algebra.smul_def (l : K)⁻¹ (1 : MonoidAlgebra K G),
          mul_one, Algebra.commutes]
      rw [h9, MulOpposite.op_sub, MulOpposite.op_mul, sub_smul, mul_smul, h5, smul_zero,
        MulOpposite.op_one, one_smul, sub_zero]
    have h8 : x = (MulOpposite.op (c * (ug - 1))) • x := by
      rw [← hone] at h7
      exact h7
    rw [← hx', h8, Work.ORFlatness.BalTensor.mk_smul_right, hae c,
      Work.ORFlatness.BalTensor.mk_zero_right]
  intro z z' hzz
  have h2 : Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
      (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f (z - z') = 0 := by
    rw [map_sub, hzz, sub_self]
  exact sub_eq_zero.mp (key (z - z') h2)

theorem realTorInput_of_chainInput (hchain : Work.ORFinal.ChainInput) : Work.ORFinal.RealTorInput := by
  intro L instL instLC ψ n r u l t Y hr hl hpow hpp hcr htY hY hnotmem hdiv hin
  classical
  let ψc : L →+* ℂ := (algebraMap ℝ ℂ).comp ψ
  let G : Type := PresentedGroup ({r} : Set (FreeGroup (Fin n)))
  let E := Work.ORBridgeLinnell.countableEnvelope G
  letI : Algebra L E.U := Work.ORBridgeLinnell.kAlgebra E ψc
  let Ld : Work.ORLinnell.LinnellDatum L G E.U :=
    Work.ORBridgeLinnell.linnellDatumOfEnvelope E ψc hin
  -- `Y` is the complement of `{t}`
  have hYuniv : Y = Finset.univ.erase t := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hx hxt
      rw [hxt] at hx
      exact htY hx
    · intro hx
      by_contra hxY
      exact hx (hY x hxY)
  have hnotmem' : r ∉ Subgroup.closure (FreeGroup.of '' (Finset.univ.erase t : Set (Fin n))) := by
    rw [← hYuniv]; exact hnotmem
  -- `t` occurs in `r`, hence in the root `u`
  have ht_mem_r : t ∈ Work.OROneRel.relatorLetters r := by
    by_contra hcon
    apply hnotmem'
    rw [Work.OROneRel.letters_closure_iff]
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
    intro hxt
    rw [hxt] at hx
    exact hcon hx
  have ht_mem_u : t ∈ Work.OROneRel.relatorLetters u := by
    have h := Work.ORLyndon.relatorLetters_pow u hl
    rw [← h]
    exact hpow ▸ ht_mem_r
  have hcyc_u : Work.OROneRel.IsCyclicallyReducedRelator u :=
    Work.OROneRel.isCyclicallyReducedRelator_of_pow u hl (hpow ▸ hcr)
  -- the quotient `G ⧸ ⟨⟨u⟩⟩` is locally indicable (FKS/Brodskii)
  have hq : Work.ORLocInd.Group.LocallyIndicable
      (G ⧸ Subgroup.normalClosure ({Work.ORLyndon.presentRho r u} : Set G)) :=
    locallyIndicable_quotient_normalClosure_presentRho n r u l hl hpow hpp
  -- the division property at torsion-free subgroups, from `DivLoc` and node N4
  have hdiv' : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H →
      ∀ x : ↥(Ld.D H), x ≠ 0 → IsUnit x := by
    intro H htf x hx
    have hLI : Work.ORLocInd.Group.LocallyIndicable H :=
      Work.ORLocInd.torsionFree_subgroup_locallyIndicable
        (Work.OROneRel.group_oneRelator_presentedGroup r)
        Work.OROneRel.oneRelatorCombinatorics H htf
    exact hdiv H hLI x hx
  -- node N4: a normal, finite-index, torsion-free subgroup
  obtain ⟨G', hG'N, hG'fi, hG'tf, _⟩ :=
    Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable
      (Work.OROneRel.group_oneRelator_presentedGroup r) Work.OROneRel.oneRelatorCombinatorics
  haveI : G'.Normal := hG'N
  haveI : G'.FiniteIndex := hG'fi
  -- the `TorsionData` of the M1 datum, with root `presentRho r u`
  let T : Work.ORTorsion.TorsionData L G E.U :=
    torsionDataOfRoot L G E.U Ld G' hG'tf hdiv' (Work.ORLyndon.presentRho r u) hq
  have hTu : T.u = Work.ORLyndon.presentRho r u := rfl
  -- the antipode `star` of the envelope
  have hreal : ∀ k : L, star (algebraMap L E.U k) = algebraMap L E.U k :=
    fun k => star_algebraMap_of_real E ψ k
  have hstarD : ∀ (H : Subgroup G) (x : E.U),
      x ∈ (T.D H : Set E.U) → star x ∈ (T.D H : Set E.U) := by
    intro H x hx
    exact Work.ORFinal.Antiaut.star_mem_D E ψc hreal H hx
  have hstarGen : ∀ g : G, star ((T.gen g : E.Uˣ) : E.U) = ↑((T.gen g)⁻¹ : E.Uˣ) := by
    intro g
    exact Work.ORFinal.Antiaut.star_gen E g
  obtain ⟨ι, hι⟩ := Work.ORFinal.Antiaut.antiAutOfStar_torsionData L T hreal hstarD hstarGen
  -- Lyndon's identity theorem and the two-term Lyndon sequence
  have hLyn : Work.ORLyndon.LyndonIdentity L (Fin n) r u l :=
    Work.ORLyndon.lyndonIdentity_of_pow r u l hl hpow hpp hr
  have hM2 := Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn
  -- JL Claim 5.9 (Weinbaum) and the non-vanishing of the root Fox component
  have hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure
      ({T.u} : Set G)))
      (Work.ORLyndon.rootVec L r u t).coeff.support :=
    Work.ORLyndon.rootVec_support_injOn hpow hcyc_u hpp T hTu
  have hβ0 : Work.ORLyndon.rootVec L r u t ≠ 0 :=
    Work.ORLyndon.rootVec_ne_zero_of_mem_relatorLetters r u l hpow hcyc_u hpp ht_mem_u
  -- ## `hA`: JL Lemma 5.1′ at the datum, from `hA_of_torsion_pow`
  have hA : ∀ (M : Type) [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
      [IsScalarTower L (MonoidAlgebra L G) M] [SMulCommClass L (MonoidAlgebra L G) M],
      letI := Work.ORFlatness.diagRightModule L G ↥(T.D ⊤)
        (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra L G)
        (LinearMap.id : (↥(T.D ⊤) ⊗[L] M) →ₗ[(MonoidAlgebra L G)ᵐᵒᵖ] (↥(T.D ⊤) ⊗[L] M))
        (Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ) := by
    let ug : MonoidAlgebra L G := MonoidAlgebra.of L G (Work.ORLyndon.presentRho r u)
    let QQ : Ideal (MonoidAlgebra L G) := Ideal.span ({ug - 1} : Set (MonoidAlgebra L G))
    let ae : MonoidAlgebra L G ⧸ QQ := Submodule.Quotient.mk (p := QQ) (1 : MonoidAlgebra L G)
    refine hA_of_torsion_pow_comm L G ↥(T.D ⊤)
      (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) ug l (lt_of_lt_of_le Nat.zero_lt_one hl)
      (Work.ORLyndon.normElem L l (Work.ORLyndon.presentRho r u))
      (Work.ORLyndon.rootVec L r u t) rfl (Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ ae ?_ ?_ (LinearMap.snd _ _ _) ?_ ?_
    · -- every element of the relation module is a right multiple of `ae`
      intro a
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective (p := QQ) a
      refine ⟨c, ?_⟩
      rw [← hc]
      show Submodule.Quotient.mk (p := QQ) c = c • ae
      have h1 : c • (1 : MonoidAlgebra L G) = c := by rw [smul_eq_mul, mul_one]
      calc Submodule.Quotient.mk (p := QQ) c
          = Submodule.Quotient.mk (p := QQ) (c • (1 : MonoidAlgebra L G)) := by rw [h1]
        _ = c • Submodule.Quotient.mk (p := QQ) (1 : MonoidAlgebra L G) :=
            Submodule.Quotient.mk_smul QQ c 1
        _ = c • ae := rfl
    · -- the relation module is annihilated by the left ideal generated by `ug - 1`
      intro c
      have hmem : c * (ug - 1) ∈ QQ :=
        Ideal.mul_mem_left QQ c (Submodule.subset_span rfl)
      have h1 : (c * (ug - 1)) • ae
          = Submodule.Quotient.mk (p := QQ) (c * (ug - 1)) := by
        show (c * (ug - 1)) • Submodule.Quotient.mk (p := QQ) (1 : MonoidAlgebra L G) = _
        rw [← Submodule.Quotient.mk_smul QQ (c * (ug - 1)) (1 : MonoidAlgebra L G),
          smul_eq_mul, mul_one]
      rw [h1]
      exact (Submodule.Quotient.mk_eq_zero QQ).mpr hmem
    · -- the second component of `γ` on the generator is `ν * β₀`
      show ((Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ ae).2 = Work.ORLyndon.normElem L l (Work.ORLyndon.presentRho r u)
        * Work.ORLyndon.rootVec L r u t
      rw [show (Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ ae
          = (Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ (Submodule.Quotient.mk (p := QQ) (1 : MonoidAlgebra L G)) from rfl,
        (Work.ORLyndon.magnusTwoTerm_of_lyndon Y t htY hY hcr hnotmem hLyn).γ_snd 1, Work.ORLyndon.magnusSecond_apply, one_mul,
        Work.ORLyndon.rootVec_apply]
    · -- node N8: right multiplication by the root Fox component is injective
      intro M inst1 inst2 inst3 inst4 inst5
      exact Work.ORBridgeTor.torsionFree_tensor_diagRight L G E.U T ι hι M
        (Work.ORLyndon.rootVec L r u t) hβ hβ0
  -- ## `hswap`: JL Lemma 5.2(2) at the datum, from the antipode
  letI instSmod : Module (MonoidAlgebra L G) ↥(T.D ⊤) :=
    Module.compHom ↥(T.D ⊤) (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop).toRingHom
  haveI instScomm : SMulCommClass L (MonoidAlgebra L G) ↥(T.D ⊤) :=
    ⟨fun k x s => by
      rw [Algebra.smul_def, Algebra.smul_def]
      show (algebraMap L ↥(T.D ⊤)) k
          * ((MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) x * s)
        = (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) x
          * ((algebraMap L ↥(T.D ⊤)) k * s)
      rw [← mul_assoc, ← mul_assoc,
        Algebra.commutes (R := L) (A := ↥(T.D ⊤)) k
          ((MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) x)]⟩
  let C : Type := ↥(Work.ORLyndon.augIdeal L G)
  letI instJ : Module ((MonoidAlgebra L G)ᵐᵒᵖ) ((↥(T.D ⊤)) ⊗[L] C) :=
    Work.ORFlatness.diagRightModule L G ↥(T.D ⊤)
      (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) C
  have hswap : ∀ (M : Type) [AddCommGroup M] [Module L M] [Module (MonoidAlgebra L G) M]
      [IsScalarTower L (MonoidAlgebra L G) M] [SMulCommClass L (MonoidAlgebra L G) M],
      letI := Work.ORFlatness.diagRightModule L G ↥(T.D ⊤)
        (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra L G) ((↥(T.D ⊤)) ⊗[L] M) C ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra L G) ((↥(T.D ⊤)) ⊗[L] C) M) :=
    Work.ORBridgeTor.hswap_of_jl52 L G ↥(T.D ⊤)
      (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) (fun _ _ => rfl) ι hι C rfl
  -- ## the assembly
  have hTor : Work.ORCoherence.TorTwoVanishes
      (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop).toRingHom :=
    Work.ORLyndon.magnus_torTwoVanishes L (Fin n) Y htY hY r u l hcr hnotmem hLyn
      ↥(T.D ⊤) (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) hA hswap
      (hchain L G ↥(T.D ⊤) (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop))
  -- the algebra map of the datum is the one attached to the TorsionData
  have hφval : ∀ x : MonoidAlgebra L G,
      ((MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) x : E.U)
        = ((Work.ORAssembly.LinData.toS Ld) x : E.U) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.lift_of]
        rw [Work.ORAssembly.LinData.toS_apply_coe, Work.ORAssembly.LinData.toU_of]
        rfl
    | add a b ha hb =>
        have ha' : (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) a
            = (Work.ORAssembly.LinData.toS Ld) a := Subtype.ext ha
        have hb' : (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) b
            = (Work.ORAssembly.LinData.toS Ld) b := Subtype.ext hb
        simp only [map_add, ha', hb']
        rfl
    | smul cc a ha =>
        have ha' : (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop) a
            = (Work.ORAssembly.LinData.toS Ld) a := Subtype.ext ha
        simp only [map_smul, ha']
        rfl
  have hφeq : (MonoidAlgebra.lift L ↥(T.D ⊤) G T.genTop)
      = (Work.ORAssembly.LinData.toS Ld : MonoidAlgebra L G →ₐ[L] ↥(T.D ⊤)) :=
    AlgHom.ext fun x => Subtype.ext (hφval x)
  unfold Work.ORFinal.FlatConcl Work.ORFinal.FlatConclAt
  rw [← hφeq]
  exact hTor

end Work.ORFinal.T7
