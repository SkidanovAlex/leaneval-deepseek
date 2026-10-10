import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.continuous_shapiroCoordinates
import Submission.Work.SSGRoute.PT.isLocallyConstant_shapiroLift
import Submission.Work.SSGRoute.PT.shapiro_H3_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local constancy of the degree-`3` Shapiro cochains

The topological input to the degree-`3` Shapiro isomorphism: for an open subgroup `U ≤ G` of
finite index the Shapiro lift `shapiroLift3 U a` of a locally constant `3`-cochain `a` on `U`,
the correction cochain `s2c U c`, and the primitive `h3Primitive U b c = Ψ₂ b + s₂ c` are
locally constant.  The proofs are the finite-intersection arguments of
`isLocallyConstant_shapiroLift` / `h2Primitive_isLocallyConstant`, one degree up.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- Continuity of the three Shapiro coordinates, valued in `U × U × U`. -/
theorem continuous_shapiroCoordinates3_subtype {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : G ⧸ U) :
    Continuous fun p : G × G × G =>
      ((Shapiro.A 0 G U p.1 C, Shapiro.A 0 G U p.2.1 (p.1⁻¹ • C),
        Shapiro.A 0 G U p.2.2 ((p.1 * p.2.1)⁻¹ • C)) : U × U × U) := by
  have H1 : Continuous fun p : G × G × G =>
      (Shapiro.A 0 G U p.1 C, Shapiro.A 0 G U p.2.1 (p.1⁻¹ • C)) :=
    (continuous_shapiroCoordinates_subtype U hU C).comp
      (continuous_fst.prodMk continuous_snd.fst)
  have H2 : Continuous fun p : G × G × G =>
      (Shapiro.A 0 G U (p.1 * p.2.1) C, Shapiro.A 0 G U p.2.2 ((p.1 * p.2.1)⁻¹ • C)) :=
    (continuous_shapiroCoordinates_subtype U hU C).comp
      ((continuous_fst.mul continuous_snd.fst).prodMk continuous_snd.snd)
  exact Continuous.prodMk H1.fst (Continuous.prodMk H1.snd H2.snd)

theorem isLocallyConstant_shapiroLift3 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M] (a : U × U × U → M)
    (ha : Work.AbsoluteKummer.IsLocallyConstant a) :
    Work.AbsoluteKummer.IsLocallyConstant (shapiroLift3 U a) := by
  classical
  intro p₀
  obtain ⟨g₀, h₀, k₀⟩ := p₀
  choose V hV hmem hconst using fun C : G ⧸ U =>
    ha (Shapiro.A 0 G U g₀ C, Shapiro.A 0 G U h₀ (g₀⁻¹ • C),
      Shapiro.A 0 G U k₀ ((g₀ * h₀)⁻¹ • C))
  refine ⟨⋂ C : G ⧸ U, {p : G × G × G |
      ((Shapiro.A 0 G U p.1 C, Shapiro.A 0 G U p.2.1 (p.1⁻¹ • C),
        Shapiro.A 0 G U p.2.2 ((p.1 * p.2.1)⁻¹ • C)) : U × U × U) ∈ V C}, ?_, ?_, ?_⟩
  · refine isOpen_iInter_of_finite fun C => ?_
    exact (hV C).preimage (continuous_shapiroCoordinates3_subtype U hU C)
  · exact Set.mem_iInter.mpr fun C => hmem C
  · rintro ⟨g, h, k⟩ hp
    apply Subtype.ext
    funext x
    rw [shapiroLift3_apply, shapiroLift3_apply]
    exact congrArg (fun t : M => coord U x • t)
      (hconst (x : G ⧸ U) _ (Set.mem_iInter.mp hp (x : G ⧸ U)))

theorem isLocallyConstant_s2c {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    {c : G × G × G → Coind G U M} (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (s2c U c) := by
  classical
  intro p₀
  have hlc : ∀ C : G ⧸ U, Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G => - (c (secC U C, (Shapiro.A 0 G U p.1 C : G),
            (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)))
          + (c (p.1, secC U (p.1⁻¹ • C), (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)))
          - (c (p.1, p.2, secC U ((p.1 * p.2)⁻¹ • C)))) := by
    intro C
    have h1 : Work.AbsoluteKummer.IsLocallyConstant
        (fun p : G × G => c (secC U C, (Shapiro.A 0 G U p.1 C : G),
          (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G))) :=
      hc.comp (continuous_const.prodMk (continuous_shapiroCoordinates U hU C))
    have h2 : Work.AbsoluteKummer.IsLocallyConstant
        (fun p : G × G => c (p.1, (secC U (p.1⁻¹ • C) : G),
          (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G))) :=
      hc.comp (continuous_fst.prodMk
        (((continuous_secC_inv_smul U hU C).comp continuous_fst).prodMk
          ((continuous_shapiroCoordinates U hU C).snd)))
    have h3 : Work.AbsoluteKummer.IsLocallyConstant
        (fun p : G × G => c (p.1, p.2, (secC U ((p.1 * p.2)⁻¹ • C) : G))) :=
      hc.comp (continuous_fst.prodMk (continuous_snd.prodMk
        ((continuous_secC_inv_smul U hU C).comp
          (continuous_fst.mul continuous_snd))))
    exact (h1.neg.add h2).sub h3
  obtain ⟨g₀, h₀⟩ := p₀
  choose W hW hWmem hWconst using fun C : G ⧸ U => (hlc C) (g₀, h₀)
  refine ⟨⋂ C : G ⧸ U, W C, isOpen_iInter_of_finite hW, Set.mem_iInter.mpr hWmem, ?_⟩
  rintro ⟨g, h⟩ hp
  apply Subtype.ext
  funext x
  have h := hWconst (x : G ⧸ U) (g, h) (Set.mem_iInter.mp hp (x : G ⧸ U))
  simp only [s2c_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_neg,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  exact congrArg (fun (t : Coind G U M) => (t : G → M) x) h

theorem isLocallyConstant_h3Primitive {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    {b : U × U → M} {c : G × G × G → Coind G U M}
    (hb : Work.AbsoluteKummer.IsLocallyConstant b)
    (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G) :
    Work.AbsoluteKummer.IsLocallyConstant (h3Primitive U b c) := by
  have h1 : Work.AbsoluteKummer.IsLocallyConstant (shapiroLift U b) :=
    isLocallyConstant_shapiroLift U hU b hb
  have h2 : Work.AbsoluteKummer.IsLocallyConstant (s2c U c) :=
    isLocallyConstant_s2c U hU ((Work.SSGRoute.mem_Z3_iff (G := G) (M := Coind G U M)).mp hc).2
  have h3 : Work.AbsoluteKummer.IsLocallyConstant (shapiroLift U b + s2c U c) := h1.add h2
  show Work.AbsoluteKummer.IsLocallyConstant (h3Primitive U b c)
  rw [h3Primitive]
  exact h3

end

end Work.SSGRoute.PT
