import Mathlib
import Submission.NK.NUV2.LC.exists_zeroPreserving_equiv_h2Profinite_of_homeomorph
import Submission.NK.NUV2.LC.RouteB.mapIsoCompMapRes
import Submission.NK.NUV2.LC.RouteB.Defs

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NK.BrauerHasse

namespace NK.NUV2.LC.RouteB

universe u

/-- **Computation rule for the restriction map** `NK.LocalDecomposition.H2Profinite.res` on the
finite levels, in the generality needed here: the base field is an arbitrary field, no
`NumberField` assumption is used.

This is the same statement as `NK.LocalDecomposition.H2Profinite.res_ofLevel`, but that lemma
carries an unused `NumberField` instance argument which the present setting does not provide. -/
theorem res_ofLevel_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {U V : Subgroup Gal(K'/K)} (p : ℕ) (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L) :
    NK.LocalDecomposition.H2Profinite.res p h (H2Profinite.ofLevel L a) =
      H2Profinite.ofLevel L ((H2.map (levelInclHom h L)) a) :=
  Classical.choose_spec (NK.BrauerHasse.exists_restriction_map p h) L a

/-- **Computation of `levelInclHom` on the class of an element**: the level-wise restriction map
sends the class of `x` to the class of `Subgroup.inclusion h x`. -/
theorem levelInclHom_mk' {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (x : ↥V) :
    levelInclHom h L (QuotientGroup.mk' (L.fixingSubgroup.subgroupOf V) x)
      = QuotientGroup.mk' (L.fixingSubgroup.subgroupOf U) (Subgroup.inclusion h x) := by
  rw [levelInclHom, QuotientGroup.map_mk']
  rfl

/-- **The finite-quotient naturality square of the transport `HTX.alphaL`.**

For an isomorphism `e : ↥H ≃* ↥J` of closed subgroups and a compatible isomorphism
`e' : ↥H' ≃* ↥J'` of subgroups `H' ≤ H`, `J' ≤ J`, the transport of the cohomology of a finite
level `L` of `H` commutes with the restriction from `J` to `J'`, on any level `P` of `J'` dominating
both `sigma H J e L` and `sigma H' J' e' L`:
```
LevelGroup J (sigma H J e L) --alphaL--> LevelGroup H L
      |                                        |
levelInclHom                             levelInclHom
      v                                        v
LevelGroup J' P     --levelQuotHom-->  LevelGroup H' L'???
```
(equivalently, the composite `alphaL e` followed by the restriction equals the composite of the
restriction with `alphaL e'`). -/
theorem alphaL_comp_levelInclHom {K K' κ κ' : Type u}
    [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    {H H' : Subgroup Gal(K'/K)} {J J' : Subgroup Gal(κ'/κ)}
    (hH : H' ≤ H) (hJ : J' ≤ J) (e : ↥H ≃ₜ* ↥J) (e' : ↥H' ≃ₜ* ↥J')
    (he : ∀ x : ↥H', (e (Subgroup.inclusion hH x) : ↥J) = Subgroup.inclusion hJ (e' x))
    (L : FiniteGaloisIntermediateField K K')
    (P : FiniteGaloisIntermediateField κ κ')
    (h1 : NK.NUV2.LC.HTX.sigma H J e L ≤ P)
    (h2 : NK.NUV2.LC.HTX.sigma H' J' e' L ≤ P) :
    (NK.NUV2.LC.HTX.alphaL H J e L).comp
        ((levelInclHom hJ (NK.NUV2.LC.HTX.sigma H J e L)).comp
          (NK.BrauerHasse.levelQuotHom (U := J') h1))
      = (levelInclHom hH L).comp
        ((NK.NUV2.LC.HTX.alphaL H' J' e' L).comp
          (NK.BrauerHasse.levelQuotHom (U := J') h2)) := by
  -- the compatibility of `e` with the two inclusions, on the quotients
  have hcompat : ∀ y : ↥J', ((e : ↥H ≃* ↥J).symm (Subgroup.inclusion hJ y))
      = Subgroup.inclusion hH ((e' : ↥H' ≃* ↥J').symm y) := by
    intro y
    have hec : ∀ x : ↥H', (e : ↥H ≃* ↥J) (Subgroup.inclusion hH x)
        = Subgroup.inclusion hJ ((e' : ↥H' ≃* ↥J') x) := fun x => he x
    have h := hec ((e' : ↥H' ≃* ↥J').symm y)
    rw [MulEquiv.apply_symm_apply] at h
    exact (MulEquiv.symm_apply_eq (e : ↥H ≃* ↥J)).mpr h.symm
  refine QuotientGroup.monoidHom_ext (P.fixingSubgroup.subgroupOf J') ?_
  ext y
  simp only [MonoidHom.comp_apply, NK.NUV2.LC.HTX.levelQuotHom_mk',
    levelInclHom_mk', NK.NUV2.LC.HTX.alphaL_mk']
  rw [hcompat y]

/-- **Naturality of the transport `HTX.Phi` with respect to restriction.**  `NK.NUV2.LC.HTX.Phi
H J p e : H²(H, Z/p) → H²(J, Z/p)` is the transport of profinite cohomology along a continuous
group isomorphism `e : ↥H ≃ₜ* ↥J` of closed subgroups of two (possibly different) separable
closures.  If `H' ≤ H`, `J' ≤ J` and `e` maps `H'` onto `J'` compatibly with the inclusions
(`he`), then the transport commutes with restriction:

`res_{J'←J} ∘ Phi_{H→J} = Phi_{H'→J'} ∘ res_{H'←H}`.

(Proof route: both sides are colimit maps of `H2Profinite`; by `H2Profinite.lift_unique` and the
computation rules `HTX.Phi_ofLevel`/`H2Profinite.res_ofLevel` it suffices to check the square on
the level generators `ofLevel L a`, where it reduces -- after enlarging the level, using
`H2Profinite.ofLevel_eq_iff`, to the level-wise square of `HTX.fwd`/`HTX.bwd` against
`BrauerHasse.levelInclHom`, i.e. the finite-quotient naturality of
`NK.NUV2.LC.RouteB.mapIsoCompMapRes` with the compatibility hypothesis `he`.  The same pattern
occurs in the proofs of `HTX.fwd_compat` and `HTX.Psi_Phi` in the same file.) -/
theorem HTX_Phi_res_natural {K K' κ κ' : Type} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    {H H' : Subgroup Gal(K'/K)} {J J' : Subgroup Gal(κ'/κ)}
    (hH : H' ≤ H) (hJ : J' ≤ J) (e : ↥H ≃ₜ* ↥J) (e' : ↥H' ≃ₜ* ↥J')
    (he : ∀ x : ↥H', (e (Subgroup.inclusion hH x) : ↥J) = Subgroup.inclusion hJ (e' x))
    (p : ℕ) (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p H) :
    NK.LocalDecomposition.H2Profinite.res p hJ
      (NK.NUV2.LC.HTX.Phi H J p e x) =
    NK.NUV2.LC.HTX.Phi H' J' p e'
      (NK.LocalDecomposition.H2Profinite.res p hH x) := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [NK.NUV2.LC.HTX.Phi_ofLevel, NK.NUV2.LC.HTX.fwd,
    res_ofLevel_apply, res_ofLevel_apply,
    NK.NUV2.LC.HTX.Phi_ofLevel, NK.NUV2.LC.HTX.fwd]
  set P : FiniteGaloisIntermediateField κ κ' :=
    NK.NUV2.LC.HTX.sigma H J e L ⊔ NK.NUV2.LC.HTX.sigma H' J' e' L with hP
  have h1 : NK.NUV2.LC.HTX.sigma H J e L ≤ P := le_sup_left
  have h2 : NK.NUV2.LC.HTX.sigma H' J' e' L ≤ P := le_sup_right
  rw [NK.BrauerHasse.ofLevel_eq_iff]
  refine ⟨P, h1, h2, ?_⟩
  simp only [NK.BrauerHasse.levelMap]
  rw [← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := levelInclHom hJ (NK.NUV2.LC.HTX.sigma H J e L))
        (g := NK.BrauerHasse.levelQuotHom (U := J') h1)
        (x := (H2.map (NK.NUV2.LC.HTX.alphaL H J e L)).hom a),
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := NK.NUV2.LC.HTX.alphaL H J e L)
        (g := (levelInclHom hJ (NK.NUV2.LC.HTX.sigma H J e L)).comp
          (NK.BrauerHasse.levelQuotHom (U := J') h1))
        (x := a),
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := NK.NUV2.LC.HTX.alphaL H' J' e' L)
        (g := NK.BrauerHasse.levelQuotHom (U := J') h2)
        (x := (H2.map (levelInclHom hH L)).hom a),
      ← NK.LocalCFT.Brauer.H2.map_comp_apply (p := p)
        (f := levelInclHom hH L)
        (g := (NK.NUV2.LC.HTX.alphaL H' J' e' L).comp
          (NK.BrauerHasse.levelQuotHom (U := J') h2))
        (x := a)]
  rw [alphaL_comp_levelInclHom hH hJ e e' he L P h1 h2]

end NK.NUV2.LC.RouteB
