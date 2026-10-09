import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
import Submission.Work.SSGRoute.PT.isOpen_setOf_inv_smul_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the Shapiro coordinates

For a topological group `G`, an **open** subgroup `U ≤ G` and a coset `C : G ⧸ U`, the two
coordinates of the Shapiro construction,

  `p = (g, g') ↦ ( A g C , A g' (g⁻¹ • C) )`,  `A g C = (secC C)⁻¹ * g * secC (g⁻¹ • C)`,

are continuous `G × G → G × G`.  The only non-trivial input is the continuity of the
"section coordinate" `t ↦ secC U (t⁻¹ • C)`: the coset space `G ⧸ U` is discrete because `U`
is open, and `t ↦ t⁻¹ • C` into a discrete space is locally constant
(`isOpen_setOf_inv_smul_eq`), hence continuous, and so is any map out of `G ⧸ U`.

Everything else is a product of continuous maps together with the continuity of the group
operations.
-/

namespace Work.SSGRoute.PT

/-- For an open subgroup `U` of a topological group `G` and a coset `C : G ⧸ U`, the
"section coordinate" `t ↦ secC U (t⁻¹ • C)` is continuous.

Since `U` is open, the quotient `G ⧸ U` is discrete, so every function out of it is
continuous; and `t ↦ t⁻¹ • C` is locally constant, with the fibres
`{t | t⁻¹ • C = C'}` open by `isOpen_setOf_inv_smul_eq`. -/
theorem continuous_secC_inv_smul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : G ⧸ U) :
    Continuous fun t : G => (secC U (t⁻¹ • C) : G) := by
  have hf : IsLocallyConstant (fun t : G => t⁻¹ • C) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro C'
    show IsOpen {t : G | t⁻¹ • C = C'}
    exact isOpen_setOf_inv_smul_eq U hU C C'
  have hcomp : IsLocallyConstant (fun t : G => (secC U (t⁻¹ • C) : G)) :=
    hf.comp (fun C' => (secC U C' : G))
  exact hcomp.continuous

theorem continuous_shapiroCoordinates {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : G ⧸ U) :
    Continuous fun p : G × G =>
      ((Work.SSGRoute.Shapiro.A 0 G U p.1 C : G),
       (Work.SSGRoute.Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)) := by
  have hdc := continuous_secC_inv_smul U hU C
  -- First coordinate: `A g C = (secC C)⁻¹ * g * secC (g⁻¹ • C)`.
  have h1 : Continuous (fun p : G × G => (Shapiro.A 0 G U p.1 C : G)) := by
    have heq : (fun p : G × G => (Shapiro.A 0 G U p.1 C : G))
        = fun p : G × G => (secC U C)⁻¹ * p.1 * (secC U (p.1⁻¹ • C) : G) := by
      funext p
      rw [Shapiro.coe_A]
      rfl
    rw [heq]
    exact (continuous_const.mul continuous_fst).mul (hdc.comp continuous_fst)
  -- Second coordinate: `A g' (g⁻¹ • C) = (secC (g⁻¹ • C))⁻¹ * g' * secC ((g * g')⁻¹ • C)`.
  have h2 : Continuous (fun p : G × G => (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G)) := by
    have heq : (fun p : G × G => (Shapiro.A 0 G U p.2 (p.1⁻¹ • C) : G))
        = fun p : G × G => (secC U (p.1⁻¹ • C) : G)⁻¹ * p.2
            * (secC U ((p.1 * p.2)⁻¹ • C) : G) := by
      funext p
      rw [Shapiro.coe_A]
      simp only [secC]
      rw [mul_inv_rev, mul_smul]
    rw [heq]
    exact ((hdc.comp continuous_fst).inv.mul continuous_snd).mul
      (hdc.comp (continuous_fst.mul continuous_snd))
  exact Continuous.prodMk h1 h2

end Work.SSGRoute.PT
