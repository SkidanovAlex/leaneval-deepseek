import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro cochain vanishes near the identity

For a topological group `G`, an *open* subgroup `U ≤ G` of finite index, and a locally constant
crossed homomorphism `φ : U → M` (into a discrete coefficient module `M`), the Shapiro cochain
`coindCocycle U φ` (`Submission/Work/SSGRoute/PT/shapiro_defs.lean`) vanishes on an open
neighbourhood of `1 ∈ G`.

This is the elementary continuity input behind the Shapiro isomorphism
`H¹(G, Coind^G_U M) ≅ H¹(U, M)`: it shows that the Shapiro cochain of `φ` is *continuous*, hence
represents a class of the continuous cohomology `H¹`.

## The argument

Recall `coindCocycle U φ t` is the function `x ↦ coord U x • φ (A t (x U))`, with
`A t C = secC(C)⁻¹ * t * secC(t⁻¹ • C) ∈ U`.  It is enough to find an open `V ∋ 1` such that
`φ (A t C) = 0` for all `t ∈ V` and all cosets `C ∈ G ⧸ U`; since the action is additive and
`U` has finite index, `V` can be taken to be the finite intersection of the sets `V_C` below.

Since `U` is open, `G ⧸ U` is discrete, so `{t | t⁻¹ • C = C}` is open (`isOpen_setOf_inv_smul_eq`).
On this set `A t C = secC(C)⁻¹ * t * secC(C)`, a *continuous* function of `t`, and it equals `1`
at `t = 1`.  Local constancy of `φ` then gives a neighbourhood `O` of `1` (inside `U`, hence in
`G`) on which `φ` vanishes (`φ 1 = 0` for a crossed homomorphism), and `V_C` is the preimage of
`O` under `t ↦ secC(C)⁻¹ * t * secC(C)`.
-/

set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- If `U ≤ G` is an **open** subgroup of a topological group and `C, C' : G ⧸ U`, then the set
of `t : G` with `t⁻¹ • C = C'` is open in `G`.

Indeed `t⁻¹ • C = secC(C)⁻¹ * t * secC(C') ∈ U` (`secC` being a section of the coset projection),
and the map `t ↦ secC(C)⁻¹ * t * secC(C')` is continuous while `U` is open. -/
theorem isOpen_setOf_inv_smul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C C' : G ⧸ U) :
    IsOpen {t : G | t⁻¹ • C = C'} := by
  have hmem : ∀ t : G, t⁻¹ • C = C' ↔ (secC U C)⁻¹ * t * secC U C' ∈ U := by
    intro t
    have e1 : t⁻¹ • C = (((t⁻¹ * secC U C : G)) : G ⧸ U) := by
      conv_lhs => rw [← secC_mk U C]
      rw [MulAction.Quotient.smul_coe U (t⁻¹) (secC U C), smul_eq_mul]
    rw [e1]
    conv_lhs => rw [← secC_mk U C']
    rw [QuotientGroup.eq]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hset : {t : G | t⁻¹ • C = C'}
      = {t : G | (secC U C)⁻¹ * t * secC U C' ∈ U} := by
    ext t
    exact hmem t
  rw [hset]
  exact hU.preimage (by fun_prop)

theorem coindCocycle_eventually_zero {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (φ : U → M)
    (hφ : Work.GroupCohomology.IsCrossedHom U M φ)
    (hφc : Work.AbsoluteKummer.IsLocallyConstant φ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ t ∈ V, Work.SSGRoute.PT.coindCocycle U φ t = 0 := by
  -- A crossed homomorphism vanishes at the identity.
  have hφ1 : φ 1 = 0 := by
    have h : φ 1 = φ 1 + φ 1 := by
      have := hφ 1 1
      simpa using this
    have h2 : φ 1 + φ 1 = φ 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  -- Local constancy of `φ` gives an open neighbourhood `O` of `1` in `G` on which `φ` vanishes.
  obtain ⟨S, hSopen, hSone, hSconst⟩ := hφc (1 : U)
  let O : Set G := ((↑) : U → G) '' S
  have hOopen : IsOpen O := hU.isOpenMap_subtype_val S hSopen
  have hOone : (1 : G) ∈ O := ⟨1, hSone, rfl⟩
  have hOvan : ∀ w : U, (w : G) ∈ O → φ w = 0 := by
    rintro w ⟨y, hyS, hyw⟩
    have hyw' : y = w := Subtype.ext hyw
    rw [← hyw', hSconst y hyS, hφ1]
  -- For each coset `C`, the set `Vc C` of `t` close to `1` along which `A t C` lies in `O`.
  let Vc : G ⧸ U → Set G := fun C =>
    {t : G | t⁻¹ • C = C} ∩ {t : G | (secC U C)⁻¹ * t * secC U C ∈ O}
  have hVcopen : ∀ C, IsOpen (Vc C) := by
    intro C
    refine (isOpen_setOf_inv_smul_eq U hU C C).inter ?_
    exact hOopen.preimage (by fun_prop)
  have hVc1 : ∀ C, (1 : G) ∈ Vc C := by
    intro C
    refine ⟨?_, ?_⟩
    · show (1 : G)⁻¹ • C = C
      rw [inv_one, one_smul]
    · show (secC U C)⁻¹ * 1 * secC U C ∈ O
      have : (secC U C)⁻¹ * 1 * secC U C = (1 : G) := by group
      rw [this]
      exact hOone
  -- The finite intersection over the (finitely many) cosets is the required neighbourhood.
  refine ⟨⋂ C : G ⧸ U, Vc C, isOpen_iInter_of_finite (fun C => hVcopen C),
    Set.mem_iInter.mpr hVc1, ?_⟩
  intro t ht
  apply Subtype.ext
  funext x
  rw [coindCocycle_apply]
  have hmem := Set.mem_iInter.mp ht (x : G ⧸ U)
  obtain ⟨hfix, hOin⟩ := hmem
  -- On `{t | t⁻¹ • (x U) = (x U)}` the `U`-coordinate `A t (x U)` is continuous in `t`.
  have hA : ((Shapiro.A 0 G U t (x : G ⧸ U) : U) : G)
      = (secC U (x : G ⧸ U))⁻¹ * t * secC U (x : G ⧸ U) := by
    rw [Shapiro.coe_A]
    simp only [secC]
    rw [hfix]
  have hval : φ (Shapiro.A 0 G U t (x : G ⧸ U)) = 0 :=
    hOvan _ (by rw [hA]; exact hOin)
  rw [hval, smul_zero]
  simp

end

end Work.SSGRoute.PT
