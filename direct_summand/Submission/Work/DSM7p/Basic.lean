import Submission.Work.DSMap.Mix2
import Submission.Work.DSAM3.Api
import Submission.Work.DSAM2.Main

/-!
# DSM7p — the model-level Bhatt §4–§5 assembly (M7p of the MIX2 design)

This is the base module of the subproject `DSM7p`, whose deliverable is
`DSMap.Mix2.area_M7p_proved`, with the same type as the frozen interface
`DSMap.Mix2.area_M7p` of `Submission/Work/DSMap/Mix2.lean`:

> Given a `p`-torsion-free perfectoid, faithfully flat `A`-algebra `B`, an element `g ∉ (p)` with a
> compatible system of `p`-power roots `gr`, a pro-uniform quantitative Riemann extension tower `D`
> (`IsQRETp`), and almost splittings of the unit `ε : A → P⁰` over every `D n` modulo every `p ^ m`
> with value `(QD n).ϖ k`, the unit splits *honestly* over `A` (`ModSplit P ε (RingHom.id A) ⊥ 1`).

## The mathematics (Bhatt, arXiv:1608.08882, §4, proof of `thm:DSC`)

Everything is phrased through the **value ideal**

  `valIdeal P ε ψ I = {c : D | ModSplit P ε ψ I c}`

of the splitting problem: `ModSplit P ε ψ I c` says that `ε ⊗ 1 : D → P⁰ ⊗_A D` admits a `D`-linear
splitting modulo `I` killing `d⁻¹` and carrying the unit `ε 1` to `c`.  `valIdeal` is an ideal
(`Basic.lean`), it is the base change of the value ideal over `A` for `B` flat over `A`
(`ValueIdeal.lean`), and the tower plus `IsQRETp` put the almost-elements `(Q.ϖ k) ^ 3 * (gr k) ^ 2`
into the value ideal over `B` (`Transport.lean`).  Krull's intersection theorem plus the faithful
flatness of `A → B` then show that `1` lies in the value ideal modulo every `p ^ m` (`Main.lean`),
and the maximal-ideal form of Krull lifts this to the honest splitting (`Lift.lean`).
-/

set_option linter.style.haveILetI false

open CategoryTheory
open scoped TensorProduct

namespace Work.DSM7p

universe a

variable {A : Type a} [CommRing A]

/-- The **value ideal** of the splitting problem `(P, ε)` over `D` modulo `I`: the set of
`c : D` for which `ε` admits a splitting modulo `I` with value `c`
(`ModSplit P ε ψ I c`, frozen in `Submission/Work/DSMap/Mix.lean`).

Concretely, in the adjoint (`A`-linear) form of `ModSplit`, `c ∈ valIdeal P ε ψ I` iff there is
`t : P⁰ →ₗ[A] D ⧸ I` killing `d⁻¹ : P⁻¹ → P⁰` with `t (ε 1) = c`. -/
def valIdeal (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) : Ideal D where
  carrier := {c | DSMap.Mix.ModSplit P ε ψ I c}
  zero_mem' := by
    letI : Algebra A D := ψ.toAlgebra
    rw [Set.mem_ofPred_eq]
    exact (DSAM3.modSplit_iff_ModSplitA P ε ψ I 0).mpr (DSAM3.modSplitA_zero P ε ψ I)
  add_mem' := by
    letI : Algebra A D := ψ.toAlgebra
    intro c₁ c₂ h₁ h₂
    rw [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    rw [DSAM3.modSplit_iff_ModSplitA] at h₁ h₂ ⊢
    obtain ⟨t₁, ht₁, hval₁⟩ := h₁
    obtain ⟨t₂, ht₂, hval₂⟩ := h₂
    exact ⟨t₁ + t₂, by rw [LinearMap.add_comp, ht₁, ht₂, add_zero],
      by rw [LinearMap.add_apply, hval₁, hval₂, map_add]⟩
  smul_mem' := by
    letI : Algebra A D := ψ.toAlgebra
    intro d c h
    rw [Set.mem_ofPred_eq] at h ⊢
    rw [DSAM3.modSplit_iff_ModSplitA] at h ⊢
    obtain ⟨t, ht, hval⟩ := h
    refine ⟨d • t, ?_, ?_⟩
    · rw [LinearMap.smul_comp, ht, smul_zero]
    · rw [LinearMap.smul_apply, hval, ← Ideal.Quotient.mk_eq_mk (I := I) c,
        ← Ideal.Quotient.mk_eq_mk (I := I) (d • c)]
      exact (Submodule.Quotient.mk_smul I d c).symm

/-- Membership in `valIdeal` is `ModSplit`, by definition. -/
lemma mem_valIdeal (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) (c : D) :
    c ∈ valIdeal P ε ψ I ↔ DSMap.Mix.ModSplit P ε ψ I c := Iff.rfl

/-- The value ideal is monotone in the ideal. -/
lemma valIdeal_mono (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type a} [CommRing D] (ψ : A →+* D) {I J : Ideal D} (hIJ : I ≤ J) :
    valIdeal P ε ψ I ≤ valIdeal P ε ψ J := by
  intro c hc
  rw [mem_valIdeal] at hc ⊢
  exact DSAM3.modSplit_mono P ε ψ hIJ c hc

/-- The ideal `I` itself lies in the value ideal over `D` modulo `I`. -/
lemma valIdeal_le_self (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D) : I ≤ valIdeal P ε ψ I := by
  letI : Algebra A D := ψ.toAlgebra
  intro c hc
  rw [mem_valIdeal, DSAM3.modSplit_iff_ModSplitA]
  refine ⟨0, by simp, ?_⟩
  rw [LinearMap.zero_apply, ← Ideal.Quotient.mk_eq_mk (I := I) c]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hc |>.symm

end Work.DSM7p
