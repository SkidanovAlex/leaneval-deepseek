import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.e1a_shift
import Submission.Work.SSGRoute.E1aFinal.HasseDefs
import Submission.Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice_split
import Submission.Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice_step
import Submission.Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice_chain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aFinal

open CategoryTheory

/-!
# The `C₂`-lattice Hasse principle — the last leaf of `E1a`

`H = ⟨σ̄⟩` has order `2` (`σ̄ = res k K σ`, `hσ : σ² = 1`, `hnt : σ̄ ≠ 1`) and acts on the finite
free `ℤ`-module `M` (`M` is a `Rep` over `↥H` with `[Module.Finite ℤ M.V]`, `[Module.Free ℤ M.V]`).
The claim is that the coefficient change `Kˣ → 𝕀_K` makes `Ext¹_H(M, Kˣ) → Ext¹_H(M, 𝕀_K)`
**injective**.

**Why this node is on the critical path.** `Submission/Work/SSGRoute/ExtChain/himgIdelesInput_fin.lean`
is `sorry`-free, so E1a's landing clause has exactly one remaining leaf: the `p = 2` involution input
`ExtChain.himg_involution_input_two` (`ExtChain/himgIdelesInput_inf.lean:587`).  That leaf has a
*proved* reduction, `ExtChain.himg_involution_input_two_of_latticeHasse`, whose only hypothesis is
*verbatim* the present statement.  The one-line assembly is on disk and builds green here, as
`Work.SSGRoute.ExtChain.himg_involution_input_two_of_hasseExt1`
(`Submission/Work/SSGRoute/hasseExt1_C2_lattice_leaf.lean`), so **proving the present statement
closes E1a** (modulo E1a's own imports) and hence removes one of the two taints of
`Work.SSGRoute.tatePoitouEmbedding` (the right half of `Ш² ↪ (Ш¹)^∨`).

**Route (corrected after review — the third bullet is the point).**  `M` is `ℤ`-free, so
`Ext¹_H(M, A) = H¹(H, Hom_ℤ(M, A))` exactly (no spectral sequence, no `d₂`).  `Hom_ℤ(M, ·)` is
exact, so the long exact sequence of `0 → Kˣ → 𝕀_K → C_K → 0` shows that the requested injectivity
is *equivalent* to the surjectivity of `H⁰(H, Hom_ℤ(M, 𝕀_K)) → H⁰(H, Hom_ℤ(M, C_K))`, i.e. to the
vanishing of `H¹(H, Hom_ℤ(M, Kˣ))`.

* **Warning, and this is where the content is**: `H¹(H, Hom_ℤ(M, Kˣ))` is **not** zero in general.
  For `M = ℤ` with the sign action, `H¹(H, Hom_ℤ(M, Kˣ)) = (K^{σ̄})ˣ / Nm_{K/K^{σ̄}}(Kˣ)`, which is
  `ℤ/2` for `K = ℚ(i)`; the injectivity of the coefficient change in that case *is* Hasse's norm
  principle, and the non-vanishing is the arithmetic heart, not an obstruction.  Do **not** try to
  prove the vanishing of `H¹(H, Hom_ℤ(M, Kˣ))`.
* Rank one, trivial action (`M = ℤ`): `H¹(C₂, Kˣ) = 0` (Hilbert 90), so the injectivity is trivial.
* Rank one, sign action (`M = ℤ(-1)`): `H¹(C₂, Kˣ)` in the twisted coefficient is the norm quotient,
  and the injectivity is verbatim Hasse's norm principle
  (`NK.GlobalCFTdeep.cyclicHasseInput.hasse_norm`, `NK.GlobalCFTdeep.hbnUnits`).
* The lattice `M` need **not** split into its `±1`-eigenspaces (`M = ℤ²`, `c(x,y) = (x+y,-y)` has
  `[M : M₊ ⊕ M₋] = 2`, as recorded in `ExtChain/hasseExt1_C2_lattice_general.lean`), so `Hom_ℤ(M,Kˣ)`
  is only an *extension* of the two classical pieces by a `μ₂`/`2`-torsion quotient `T`; the quotient
  contributes `K^×/(K^×)² ↪ ∏_v K_v^×/(K_v^×)²` (Hasse–Minkowski in rank `2`).  The general lattice is
  then reduced to these two rank-one cases plus the torsion piece by the `Ĥ⁰/Ĥ⁻¹` exact hexagon for
  `C₂` (`cd(C₂) = 1`), i.e. the long exact sequence of the extension of modules.

The present declaration is the *statement* of
`Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general` (unchanged, verbatim) at a path where it can be
proved without touching that lane's file; proving it also retires the orphan
`ExtChain/hasseExt1_C2_lattice.lean` (same statement, `sorry`).

**Assembly.**  The chain lemma `hasseExt1_C2_lattice_chain` gives an `H`-stable chain
`M₀ ⊆ M₁ ⊆ … ⊆ Mₙ ≅ M` with split bottom term and index-two steps; `HasseStat` is proved for `M₀`
by the split case `hasseExt1_C2_lattice_split`, propagated along the chain by the step lemma
`hasseExt1_C2_lattice_step`, and transported across the final isomorphism by
`HasseStat.of_iso`.
-/

/-- `HasseStat` is invariant under isomorphism of the coefficient module. -/
theorem HasseStat.of_iso {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    {σ : Ω ≃ₐ[k] Ω} {M M' : Rep.{0} SSGRoute.PTExt.Coeff
    ↥(Subgroup.zpowers (SSGRoute.res k K σ))} (e : M ≅ M') (h : HasseStat M) :
    HasseStat M' := by
  intro z hz
  have hz' : (CategoryTheory.Abelian.Ext.mk₀ e.hom).comp z (zero_add 1) = 0 := by
    refine h _ ?_
    rw [CategoryTheory.Abelian.Ext.comp_assoc (a₁ := 0) (a₂ := 1) (a₃ := 0) (a₁₂ := 1)
      (a₂₃ := 1) (a := 1) (CategoryTheory.Abelian.Ext.mk₀ e.hom) z
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (NK.HassePrinciple.ideleIncl k ↥K))) (zero_add 1) (add_zero 1) (by omega)]
    rw [hz, CategoryTheory.Abelian.Ext.comp_zero]
  have hz'' : (CategoryTheory.Abelian.Ext.mk₀ e.inv).comp
      ((CategoryTheory.Abelian.Ext.mk₀ e.hom).comp z (zero_add 1)) (zero_add 1) = z := by
    rw [← CategoryTheory.Abelian.Ext.comp_assoc (a₁ := 0) (a₂ := 0) (a₃ := 1) (a₁₂ := 0)
      (a₂₃ := 1) (a := 1) (CategoryTheory.Abelian.Ext.mk₀ e.inv)
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) z (add_zero 0) (zero_add 1) (by omega),
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      CategoryTheory.Abelian.Ext.mk₀_id_comp]
  rw [← hz'', hz']
  exact CategoryTheory.Abelian.Ext.comp_zero _ _ _ _ _

theorem hasseExt1_C2_lattice (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (M : Rep.{0} SSGRoute.PTExt.Coeff ↥(Subgroup.zpowers (SSGRoute.res k K σ)))
    [Module.Finite ℤ M.V] [Module.Free ℤ M.V] :
    ∀ z : CategoryTheory.Abelian.Ext.{0} M
        (Rep.res (Subgroup.zpowers (SSGRoute.res k K σ)).subtype (SSGRoute.PTExt.unitsK k ↥K)) 1,
      z.comp (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
            (NK.HassePrinciple.ideleIncl k ↥K))) (add_zero 1) = 0 → z = 0 := by
  classical
  obtain ⟨n, Mseq, hfin, hfree, hsplit, hsteps, hiso⟩ :=
    hasseExt1_C2_lattice_chain p k Ω K σ hσ hnt M
  have key : ∀ i : Fin (n + 1), HasseStat (Mseq i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        haveI := hfin 0
        haveI := hfree 0
        exact hasseExt1_C2_lattice_split p k Ω K σ hσ hnt (Mseq 0) hsplit
    | succ i ih =>
        haveI := hfin i.castSucc
        haveI := hfree i.castSucc
        haveI := hfin i.succ
        haveI := hfree i.succ
        exact hasseExt1_C2_lattice_step p k Ω K σ hσ hnt (Mseq i.castSucc) (Mseq i.succ)
          (hsteps i) ih
  exact HasseStat.of_iso hiso.some (key (Fin.last n))

end Work.SSGRoute.E1aFinal
