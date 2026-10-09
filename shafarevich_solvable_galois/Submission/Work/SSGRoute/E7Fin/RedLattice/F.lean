import Mathlib
import Submission.Work.ArtinInduction.LatticeModp.Infra
import Submission.Work.ArtinInduction.LatticeModp.coprime_reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne *ADT* I.2.12 with finiteness of `A/pA` instead of finite generation over `ℤ`

Lane `Work.SSGRoute.coker_obstruction_pt`.

The tree's version of Milne's Lemma I.2.12 ("the class of `A/pA` in `R(𝔽_p[G])` depends only on
`A ⊗ ℚ`") is `Work.SSGRoute.ArtinP.Red.lattice_indep`, proved for `ℤ`-submodules
`A ⊆ M` that are *finitely generated over `ℤ`*.  That hypothesis is exactly what fails in the
arithmetic application: the two lattices one wants to compare inside a local field `L` — the ring
of integers `𝒪_L` and the `ℤ_p`-lattice attached to a normal basis of `L/K` — are `ℤ_p`-lattices,
hence *not* finitely generated over `ℤ` (they are `ℤ_p`-modules of finite rank).

What the proofs actually use of `Module.Finite ℤ ↥A` is only *finiteness of `A/pA`* (and
commensurability `A/(A ⊓ A')` finite, which is a property of two lattices with the same `ℚ`-form
and which the caller can supply).  This file provides the interface for the corresponding
parameter-free value of an additive invariant of `A/pA`,

  `redRhoF ρ X A hA hfin` = `ρ (A/pA)`,

together with the transport lemma (`redRhoFP_eq_of_iso`) that lets one pass between two lattices
whose mod-`p` reductions are isomorphic as `𝔽_p[G]`-modules (via `redRhoFP`, the version with the
instances as parameters).

The companions are

* `Work.SSGRoute.E7Fin.RedLattice.Steps.killedByP_reduceF`, `...coprime_reduceF` — the two
  short-exact-sequence reductions, with the finite-generation hypothesis replaced by finiteness of
  the mod-`p` reduction;
* `Work.SSGRoute.E7Fin.RedLattice.Quot` — the finiteness calculus for `A/pA`;
* `Work.SSGRoute.E7Fin.RedLattice.Nested.nested_apF` — the nested (commensurable) step;
* `Work.SSGRoute.E7Fin.RedLattice.LatticeIndep.lattice_indepF` — Milne I.2.12 in this form.

## A pitfall recorded

For `A ≤ R` the natural map `A/pA → R/pR` is **not injective** in general (`A = 2ℤ ⊆ R = ℤ`,
`p = 2`: the class of `2` dies), and `A/pA` is *not* finite merely because `R/pR` is (take
`R = ⊕_{n∈ℕ} ℚ`, `A = ⊕_{n∈ℕ} ℤ`).  The correct statement needs the commensurability hypothesis
`pR ⊆ A`, see `RedLattice.Quot.finite_red_of_le_of_pSmul_le`.

## Contents of this file

* `redRhoFP` — the value of `ρ` on `A/pA`, with the `𝔽_p`-module structure, the `G`-action and the
  compatibility as parameters;
* `redRhoF` — the same with the canonical instances (`redZMod`/`redDMA`/`redSCC`);
* `redRhoF_def`, `redRhoFP_redRhoF`, `redRhoF_eq_redRho` — unfolding lemmas;
* `redRhoF_eq_of_inst_eq` — independence of the proof of finiteness;
* `redRhoFP_eq_of_iso` — invariance under an equivariant `𝔽_p`-linear isomorphism.
-/

open scoped Pointwise

namespace Work.SSGRoute.E7Fin.RedLattice

open Work.ArtinInduction.LatticeModp

variable {p : ℕ} [NeZero p] {G : Type} [Group G]

/-- **The value of an additive invariant on `A/pA`**, with the `𝔽_p`-module structure, the
`G`-action and the compatibility as explicit parameters. -/
noncomputable def redRhoFP (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (m : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A))
    (d : DistribMulAction G (↥A ⧸ pSmulSub p ↥A))
    (k : @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) d.toSMul m.toSMul)
    (hf : Finite (↥A ⧸ pSmulSub p ↥A)) : ℚ :=
  @ρ (↥A ⧸ pSmulSub p ↥A) _ m d k hf

/-- **The value of an additive invariant on `A/pA`** with the canonical instances, asking only for
finiteness of `A/pA` — not for finite generation of `A` over `ℤ`. -/
noncomputable def redRhoF (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (hfin : Finite (↥A ⧸ pSmulSub p ↥A)) : ℚ :=
  redRhoFP ρ X A hA (redZMod p A) (redDMA p A hA) (redSCC p A hA) hfin

/-- Unfolding of `redRhoFP`. -/
lemma redRhoFP_def (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (m : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A))
    (d : DistribMulAction G (↥A ⧸ pSmulSub p ↥A))
    (k : @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) d.toSMul m.toSMul)
    (hf : Finite (↥A ⧸ pSmulSub p ↥A)) :
    redRhoFP ρ X A hA m d k hf
      = @ρ (↥A ⧸ pSmulSub p ↥A) _ m d k hf := rfl

/-- Unfolding of `redRhoF`. -/
lemma redRhoF_def (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (hfin : Finite (↥A ⧸ pSmulSub p ↥A)) :
    redRhoF ρ X A hA hfin
      = @ρ (↥A ⧸ pSmulSub p ↥A) _ (redZMod p A) (redDMA p A hA) (redSCC p A hA) hfin := rfl

/-- `redRhoF` is `redRhoFP` at the canonical instances. -/
lemma redRhoFP_redRhoF (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (hfin : Finite (↥A ⧸ pSmulSub p ↥A)) :
    redRhoFP ρ X A hA (redZMod p A) (redDMA p A hA) (redSCC p A hA) hfin
      = redRhoF ρ X A hA hfin := rfl

/-- **Agreement with `LatticeModp.redRho`** when `A` is finitely generated over `ℤ`: the two
definitions are the same term. -/
lemma redRhoF_eq_redRho (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    (hfg : Module.Finite ℤ ↥A) :
    redRhoF ρ X A hA (redFin p (NeZero.ne p) A hfg) = redRho ρ X A hA hfg := rfl

/-- `redRhoF` does not depend on the proof of finiteness (`Finite` is a proposition). -/
lemma redRhoF_eq_of_inst_eq (ρ : Inv p G) (X : Type) [AddCommGroup X] [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    {hfin hfin' : Finite (↥A ⧸ pSmulSub p ↥A)} :
    redRhoF ρ X A hA hfin = redRhoF ρ X A hA hfin' := by
  have h : hfin = hfin' := Subsingleton.elim _ _
  rw [h]

/-- **Invariance of `redRhoF` under an equivariant `𝔽_p`-linear isomorphism** of the two mod-`p`
reductions: this is `LatticeModp.rho_iso` with the instances made parameters. -/
lemma redRhoFP_eq_of_iso (ρ : Inv p G) (hadd : IsAddInv ρ) {X X' : Type} [AddCommGroup X]
    [DistribMulAction G X] [AddCommGroup X'] [DistribMulAction G X']
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    [mA : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A)]
    [dA : DistribMulAction G (↥A ⧸ pSmulSub p ↥A)]
    [kA : @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) dA.toSMul mA.toSMul]
    (hfinA : Finite (↥A ⧸ pSmulSub p ↥A))
    (A' : Submodule ℤ X') (hA' : ∀ (g : G) (x : X'), x ∈ A' → g • x ∈ A')
    [mA' : Module (ZMod p) (↥A' ⧸ pSmulSub p ↥A')]
    [dA' : DistribMulAction G (↥A' ⧸ pSmulSub p ↥A')]
    [kA' : @SMulCommClass G (ZMod p) (↥A' ⧸ pSmulSub p ↥A') dA'.toSMul mA'.toSMul]
    (hfinA' : Finite (↥A' ⧸ pSmulSub p ↥A'))
    (e : (↥A ⧸ pSmulSub p ↥A) ≃ₗ[ZMod p] (↥A' ⧸ pSmulSub p ↥A'))
    (he : ∀ (g : G) (x : ↥A ⧸ pSmulSub p ↥A), e (g • x) = g • e x) :
    redRhoFP ρ X A hA mA dA kA hfinA
      = redRhoFP ρ X' A' hA' mA' dA' kA' hfinA' := by
  letI := mA
  letI := dA
  letI := kA
  letI := hfinA
  letI := mA'
  letI := dA'
  letI := kA'
  letI := hfinA'
  have h := rho_iso (p := p) ρ hadd e he
  rw [redRhoFP_def, redRhoFP_def]
  exact h.symm

/-- **Invariance of `redRhoFP` under an equivariant `𝔽_p`-linear isomorphism with an arbitrary
finite `𝔽_p[G]`-module** (not necessarily of the form `A'/pA'`): this is the form in which the
arithmetic isomorphism `Λ/pΛ ≅ 𝔽_p[Γ]^n` of `(ε)` is consumed. -/
lemma redRhoFP_eq_of_iso_any (ρ : Inv p G) (hadd : IsAddInv ρ) {X : Type} [AddCommGroup X]
    [DistribMulAction G X]
    (A : Submodule ℤ X) (hA : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)
    [mA : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A)]
    [dA : DistribMulAction G (↥A ⧸ pSmulSub p ↥A)]
    [kA : @SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) dA.toSMul mA.toSMul]
    (hfinA : Finite (↥A ⧸ pSmulSub p ↥A))
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (e : (↥A ⧸ pSmulSub p ↥A) ≃ₗ[ZMod p] N)
    (he : ∀ (g : G) (x : ↥A ⧸ pSmulSub p ↥A), e (g • x) = g • e x) :
    redRhoFP ρ X A hA mA dA kA hfinA = @ρ N _ _ _ _ _ := by
  letI := mA
  letI := dA
  letI := kA
  letI := hfinA
  rw [redRhoFP_def]
  exact (rho_iso (p := p) ρ hadd e he).symm

end Work.SSGRoute.E7Fin.RedLattice
