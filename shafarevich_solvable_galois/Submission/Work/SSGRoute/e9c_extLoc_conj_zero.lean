import Mathlib
import Submission.Work.SSGRoute.E9cConj
import Submission.Work.SSGRoute.comp_extCor
import Submission.Work.SSGRoute.extRes_injective_of_mulEquiv
import Submission.Work.SSGRoute.e9c_localUnits_conj

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Generic `Ext` calculus helpers for a degree-`0` `mk₀` factor -/

/-- `extRes` of a class followed by a coefficient map. -/
theorem extRes_comp_mk₀ {H G : Type} [Group H] [Group G] (f : H →* G)
    {X Y Z : Rep.{0, 0, 0} Coeff G} {r : ℕ} (A : Abelian.Ext X Y r) (ι : Y ⟶ Z) :
    extRes f (A.comp (Abelian.Ext.mk₀ ι) (add_zero r))
      = (extRes f A).comp (Abelian.Ext.mk₀ (Rep.resMap f ι)) (add_zero r) := by
  simp only [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]

/-- `extRes` of a class preceded by a coefficient map. -/
theorem extRes_mk₀_comp {H G : Type} [Group H] [Group G] (f : H →* G)
    {X Y Z : Rep.{0, 0, 0} Coeff G} {r : ℕ} (β : X ⟶ Y) (B : Abelian.Ext Y Z r) :
    extRes f ((Abelian.Ext.mk₀ β).comp B (zero_add r))
      = (Abelian.Ext.mk₀ (Rep.resMap f β)).comp (extRes f B) (zero_add r) := by
  simp only [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]

/-- **E9c, the local components of a class at conjugate places.**

For `z ∈ Ext^r_{Gal(K/k)}(M, 𝕀_K)`, an automorphism `σ : K ≃ₐ[k] K` and a place `v` of `K`: if the
`v`-component of `z` vanishes, then so does its `(σ • v)`-component.  (Only this vanishing form is
needed; the underlying statement is that localisation at conjugate places is conjugate,
`extLoc (σ • v) z = conj_σ (extLoc v z)`.)

Route.  `extLoc v z = (extRes (stabilizer v).subtype z) ≫ mk₀ (ideleToLocalUnits k K v)` and the
coefficient maps `ideleToLocalUnits` at `σ • v` and at `v` are intertwined by the action of `σ` on
`𝕀_K` (`NK.HassePrinciple.smul_apply_stabilizer`,
`NK.HassePrinciple.smul_apply_smul_place`), while the stabilisers are conjugate
(`MulAction.stabilizer_smul_eq_stabilizer_map_conj`).  Hence the restriction of `z` to the
stabiliser of `σ • v` is the transport of its restriction to the stabiliser of `v`, and vanishing
transports.  A useful intermediate step is the iso-form statement, with the conjugation
equivalence between the two coefficient modules. -/
theorem e9c_extLoc_conj_zero {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext M (Work.SSGRoute.idelesRepP k K) r) (σ : K ≃ₐ[k] K) (v : Place K)
    (hz : extLoc (k := k) (K := K) v z = 0) :
    extLoc (k := k) (K := K) (σ • v) z = 0 := by
  classical
  obtain ⟨Θ, _hΘu, hΘsq⟩ := e9c_localUnits_conj (k := k) (K := K) σ v
  -- the commuting square for the coefficient maps, transported to `Ext`
  have hBC : (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
        ((conjTwist σ).app (Work.SSGRoute.idelesRepP k K)))).comp
      (Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
        (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (zero_add 0)
      = (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K v)).comp
          (Abelian.Ext.mk₀ Θ) (zero_add 0) := by
    have h1 := Abelian.Ext.mk₀_comp_mk₀
      (Rep.resMap (decompK (k := k) v).subtype
        ((conjTwist σ).app (Work.SSGRoute.idelesRepP k K)))
      (Rep.resMap (conjStabHom k K σ v)
        (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))
    have h2 := Abelian.Ext.mk₀_comp_mk₀ (NK.HassePrinciple.ideleToLocalUnits k K v) Θ
    rw [h1, h2, hΘsq]
  -- Step 1: `extLoc (σ • v) z` restricted along the conjugation
  have hstep1 : extRes (conjStabHom k K σ v) (extLoc (k := k) (K := K) (σ • v) z)
      = (extRes (decompK (k := k) v).subtype
            (extRes ((MulAut.conj σ).toMonoidHom) z)).comp
          (Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
            (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (add_zero r) := by
    rw [extLoc, extRes_comp_mk₀]
    rw [show extRes (conjStabHom k K σ v)
          (extRes (decompK (k := k) (σ • v)).subtype z)
        = extRes (decompK (k := k) v).subtype
            (extRes ((MulAut.conj σ).toMonoidHom) z)
        from (Work.SSGRoute.SylowDesc.extRes_comp_aux
            (decompK (k := k) (σ • v)).subtype (conjStabHom k K σ v) z).symm.trans
          (Work.SSGRoute.SylowDesc.extRes_comp_aux
            ((MulAut.conj σ).toMonoidHom) (decompK (k := k) v).subtype z)]
    rfl
  -- Step 2: apply the conjugation twist to `z` and distribute `extRes`
  have hstep2 : extRes (decompK (k := k) v).subtype (extRes ((MulAut.conj σ).toMonoidHom) z)
      = (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype ((conjTwistInv σ).app M))).comp
          ((extRes (decompK (k := k) v).subtype z).comp
            (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
              ((conjTwist σ).app (Work.SSGRoute.idelesRepP k K)))) (add_zero r))
          (zero_add r) := by
    rw [extRes_conjTwist (σ := σ) (x := z), extRes_mk₀_comp, extRes_comp_mk₀]
  -- Step 3: reassociate the chain and use the commuting square
  have hchain : extRes (conjStabHom k K σ v) (extLoc (k := k) (K := K) (σ • v) z)
      = (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype ((conjTwistInv σ).app M))).comp
          ((extLoc (k := k) (K := K) v z).comp (Abelian.Ext.mk₀ Θ) (add_zero r))
          (zero_add r) := by
    rw [hstep1, hstep2]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero
      (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype ((conjTwistInv σ).app M)))
      ((extRes (decompK (k := k) v).subtype z).comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
          ((conjTwist σ).app (Work.SSGRoute.idelesRepP k K)))) (add_zero r))
      (Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
        (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (zero_add r)]
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero (extRes (decompK (k := k) v).subtype z)
      (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) v).subtype
        ((conjTwist σ).app (Work.SSGRoute.idelesRepP k K))))
      (Abelian.Ext.mk₀ (Rep.resMap (conjStabHom k K σ v)
        (NK.HassePrinciple.ideleToLocalUnits k K (σ • v)))) (add_zero r)]
    rw [hBC]
    rw [(Abelian.Ext.comp_assoc_of_second_deg_zero
      (extRes (decompK (k := k) v).subtype z)
      (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K v))
      (Abelian.Ext.mk₀ Θ) (add_zero r)).symm]
    rfl
  have hzero : extRes (conjStabHom k K σ v) (extLoc (k := k) (K := K) (σ • v) z) = 0 := by
    rw [hchain, hz]
    simp only [Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
    try rfl
  refine Work.SSGRoute.extRes_injective_of_mulEquiv (conjStabEquiv k K σ v)
    (Rep.res (decompK (k := k) (σ • v)).subtype M)
    (localUnitsK (k := k) (K := K) (σ • v)) r ?_
  change extRes (conjStabHom k K σ v) (extLoc (k := k) (K := K) (σ • v) z)
    = extRes (conjStabHom k K σ v)
        (0 : Abelian.Ext (Rep.res (decompK (k := k) (σ • v)).subtype M)
          (localUnitsK (k := k) (K := K) (σ • v)) r)
  rw [hzero]
  exact (Work.SSGRoute.extRes_zero (conjStabHom k K σ v)).symm

end Work.SSGRoute
