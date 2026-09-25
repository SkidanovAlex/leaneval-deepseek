import Mathlib
import Submission.Work.RelatorRank.ProP
import Submission.Work.RelatorRank.GeneratorRank.generatorRank_eq_log_card_frattiniQuotient
import Submission.Work.RelatorRank.GeneratorRank.exists_card_frattiniQuotient_eq_two_pow
import Submission.Work.ProPDeficiency.card_homFp_eq_pow_pHomDim
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup
import Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator

/-!
# The continuous dual of a finitely generated pro-`2` group

**Namespace** `Work.RelatorRank.Cohomology`; module
`Submission.Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank`.

`card_continuousHom_eq_two_pow_generatorRank`: for a finitely generated pro-`2` group `Γ`, the
number of *continuous* homomorphisms `Γ → ℤ/2` (written multiplicatively as
`Multiplicative (ZMod 2)`) is `2 ^ GeneratorRank Γ`.  This is the counting form of
`H¹(Γ, 𝔽₂) ≅ (Γ ⧸ Φ(Γ))^*`: both sides are the dual of the elementary abelian quotient
`Γ ⧸ Φ(Γ)`, of order `2 ^ GeneratorRank Γ`.

The proof has two halves.

* **Group-theoretic reduction.**  Every continuous `f : Γ →* ℤ/2` kills the `2`-Frattini subgroup
  `Φ = pFrattini 2 Γ`: the target has exponent `2` and is abelian, so `f` kills all squares and all
  commutators, and `Φ` is the topological closure of the subgroup they generate while `ker f` is
  closed.  Hence the lifts of `f` to `Γ ⧸ Φ` (`QuotientGroup.lift`) are exactly the homs on the
  quotient, and since `Γ ⧸ Φ` is finite, hence discrete, this is a bijection
  `{f continuous} ≃ (Γ ⧸ Φ →* ℤ/2)`.

* **Cardinality of the dual.**  `Γ ⧸ Φ` is a finite `2`-group, so `pHomDim 2 (Γ ⧸ Φ) = dGens (Γ ⧸ Φ)`
  (`Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup`) and
  `Nat.card (HomFp 2 G) = 2 ^ pHomDim 2 G` (`Work.ProPDeficiency.card_homFp_eq_pow_pHomDim`); and
  `2 ^ dGens (Γ ⧸ Φ) = Nat.card (Γ ⧸ Φ) = 2 ^ k`, where `Nat.card (Γ ⧸ Φ) = 2 ^ k` and
  `GeneratorRank Γ = k` come from Burnside's basis theorem
  (`exists_card_frattiniQuotient_eq_two_pow`, `generatorRank_eq_log_card_frattiniQuotient`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.RelatorRank.Cohomology

open Work.RelatorRank

theorem card_continuousHom_eq_two_pow_generatorRank {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (hp : IsProPGroup 2 Γ) (hfg : ∃ d, HasDenseGeneratingFamily Γ d) :
    Nat.card {f : Γ →* Multiplicative (ZMod 2) // Continuous f} = 2 ^ GeneratorRank Γ := by
  classical
  set Φ : Subgroup Γ := Work.RelatorRank.pFrattini 2 Γ with hΦdef
  haveI hΦn : Φ.Normal := by rw [hΦdef]; exact Work.RelatorRank.ProPFrattini.pFrattini_normal 2
  haveI hΦcli : IsClosed (Φ : Set Γ) := by
    rw [hΦdef]; exact Subgroup.isClosed_topologicalClosure _
  obtain ⟨d, gen, hgen⟩ := hfg
  have hfg' : ∃ d, Work.RelatorRank.HasDenseGeneratingFamily Γ d := ⟨d, gen, hgen⟩
  obtain ⟨k, _hkd, hcard⟩ :=
    Work.RelatorRank.GeneratorRank.exists_card_frattiniQuotient_eq_two_pow hp gen hgen
  have hcardΦ : Nat.card (Γ ⧸ Φ) = 2 ^ k := by rw [hΦdef]; exact hcard
  haveI hfin : Finite (Γ ⧸ Φ) := by
    have hpos : 0 < Nat.card (Γ ⧸ Φ) := by rw [hcardΦ]; positivity
    exact (Nat.card_pos_iff.mp hpos).2
  haveI hT1 : T1Space (Γ ⧸ Φ) := inferInstance
  haveI hdisc : DiscreteTopology (Γ ⧸ Φ) := inferInstance
  -- the quotient map is continuous
  have hmkcont : Continuous (QuotientGroup.mk' Φ : Γ → Γ ⧸ Φ) := by
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  -- every continuous homomorphism to `ℤ/2` kills the `2`-Frattini subgroup
  have hker : ∀ f : Γ →* Multiplicative (ZMod 2), Continuous f → Φ ≤ f.ker := by
    intro f hf
    rw [hΦdef]
    refine Work.RelatorRank.pFrattini_le_of_closed 2 ?_ ?_ ?_
    · have hset : (f.ker : Set Γ) = f ⁻¹' ({1} : Set (Multiplicative (ZMod 2))) := by
        ext x
        simp [MonoidHom.mem_ker]
      rw [hset]
      exact isClosed_singleton.preimage hf
    · intro g
      rw [MonoidHom.mem_ker, map_pow]
      have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
        Work.ProPDeficiency.natCard_multiplicative_zmod
      simpa [h2] using pow_card_eq_one' (x := f g)
    · show ⁅(⊤ : Subgroup Γ), ⊤⁆ ≤ f.ker
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  -- continuous homs `Γ → ℤ/2` are the homs on the Frattini quotient
  let e : {f : Γ →* Multiplicative (ZMod 2) // Continuous f}
      ≃ (Γ ⧸ Φ →* Multiplicative (ZMod 2)) :=
    { toFun := fun f => QuotientGroup.lift Φ f.1 (hker f.1 f.2)
      invFun := fun g => ⟨g.comp (QuotientGroup.mk' Φ),
        (continuous_of_discreteTopology (f := g)).comp hmkcont⟩
      left_inv := fun f => Subtype.ext (QuotientGroup.lift_comp_mk' Φ f.1 (hker f.1 f.2))
      right_inv := fun g => MonoidHom.ext fun x => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Φ x
        rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
        rfl }
  have hcardEq : Nat.card {f : Γ →* Multiplicative (ZMod 2) // Continuous f}
      = Nat.card (Γ ⧸ Φ →* Multiplicative (ZMod 2)) := Nat.card_congr e
  -- the Frattini quotient is a finite elementary abelian `2`-group
  have hP : IsPGroup 2 (Γ ⧸ Φ) := (IsPGroup.iff_card (p := 2) (G := Γ ⧸ Φ)).mpr ⟨k, hcardΦ⟩
  have hcommQ : IsMulCommutative (Γ ⧸ Φ) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Φ)).mpr
      (by rw [hΦdef]; exact Work.RelatorRank.commutator_le_pFrattini 2)
  have hsq : ∀ x : Γ ⧸ Φ, x ^ 2 = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Φ x
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mpr
      (by rw [hΦdef]; exact Work.RelatorRank.pow_mem_pFrattini 2 g)
  have hfr : frattini (Γ ⧸ Φ) = ⊥ :=
    Commons.GroupTheory.PGroup.frattini_eq_bot_of_elementary_abelian (p := 2) hsq
  have hdGens : Work.ProPDeficiency.dGens (Γ ⧸ Φ) = k := by
    have h1 : Nat.card (Γ ⧸ Φ) = 2 ^ Work.ProPDeficiency.dGens (Γ ⧸ Φ) := by
      have h := Work.ProPDeficiency.dGens_eq_log_card_frattini (p := 2) (G := Γ ⧸ Φ) hP
      rw [hfr, Nat.card_congr (QuotientGroup.quotientBot (G := Γ ⧸ Φ)).toEquiv] at h
      exact h
    exact (Nat.pow_right_injective (le_refl 2) (hcardΦ.symm.trans h1)).symm
  have hgr : GeneratorRank Γ = k := by
    have h0 : GeneratorRank Γ = Nat.log 2 (Nat.card (Γ ⧸ Φ)) := by
      rw [hΦdef]
      exact Work.RelatorRank.GeneratorRank.generatorRank_eq_log_card_frattiniQuotient hp hfg'
    rw [h0, hcardΦ, Nat.log_pow (by norm_num : 1 < 2)]
  -- counting the homomorphisms on the finite elementary abelian quotient
  have hHom : Nat.card (Γ ⧸ Φ →* Multiplicative (ZMod 2)) = 2 ^ GeneratorRank Γ := by
    have h1 : Nat.card (Γ ⧸ Φ →* Multiplicative (ZMod 2))
        = 2 ^ Work.ProPDeficiency.pHomDim 2 (Γ ⧸ Φ) :=
      Work.ProPDeficiency.card_homFp_eq_pow_pHomDim (p := 2) (by norm_num) (G := Γ ⧸ Φ)
    have h2 : Work.ProPDeficiency.pHomDim 2 (Γ ⧸ Φ) = Work.ProPDeficiency.dGens (Γ ⧸ Φ) :=
      Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup (p := 2) (G := Γ ⧸ Φ) hP
    rw [h1, h2, hdGens, hgr]
  rw [hcardEq, hHom]

end Work.RelatorRank.Cohomology
