/-
# The cusp torus is the graph of the descended ceiling `β`

`Work.Cusp.CuspTorus v = ℝ³/Λ_v` is the truncation torus `T_v` of the `v`-th cusp, and
`beta : E3 → ℝ` is the ceiling of blueprint §1.  Because `β` is invariant under the cusp lattice
`Λ_v` (`beta_lattice_periodic`, proved from the `ℤ³`-periodicity of `off`), it descends to a
continuous function on the quotient, and the graph map

`q ↦ (q, β̄ q) :  ℝ³/Λ_v → (ℝ³/Λ_v) × ℝ`

is a homeomorphism onto the range of `x ↦ ((x + Λ_v), β x)`, i.e. `τ_v` presents the truncation
torus `T_v` as the graph of the ceiling over the cusp torus.

Concretely: the descended ceiling `g` is defined on the quotient by `Quotient.lift`, it is
continuous by `Continuous.quotient_lift`, the graph map is a continuous bijection (its inverse is
the first projection, which is continuous on the subtype), and it sends the class of `x` to the
point `(x + Λ_v, β x)` of the range, as required.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.beta_lattice_periodic
import Submission.Work.Cusp.beta_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

/-- **The truncation torus `T_v` is the graph of the ceiling `β`.**  For each cusp `v` there is a
homeomorphism `ℝ³/Λ_v ≃ₜ range (x ↦ (x + Λ_v, β x))` carried by the class of `x`, which is the
statement that the cusp torus sits over `ℝ³/Λ_v` as the graph of the lattice-periodic ceiling. -/
theorem exists_tauHomeo (v : Fin 5) :
    ∃ Φ : CuspTorus v ≃ₜ Set.range (fun x : E3 => ((Quotient.mk'' x : CuspTorus v), beta x)),
      ∀ x : E3, Φ (Quotient.mk'' x) = ⟨((Quotient.mk'' x : CuspTorus v), beta x), Set.mem_range_self x⟩ := by
  -- `β` is constant on the classes of `Λ_v`, so it descends to the quotient.
  have hper : ∀ a b : E3, QuotientAddGroup.leftRel (lattice v) a b → beta a = beta b := by
    intro a b h
    have hb : -a + b ∈ lattice v := QuotientAddGroup.leftRel_apply.mp h
    have h1 := beta_lattice_periodic v a (-a + b) hb
    rw [show a + (-a + b) = b by abel] at h1
    exact h1.symm
  let g : CuspTorus v → ℝ := Quotient.lift beta hper
  have hgm : ∀ x : E3, g (Quotient.mk'' x) = beta x := fun x => rfl
  have hgcont : Continuous g := beta_continuous.quotient_lift hper
  -- every point of the quotient is the value of the graph map (use a representative).
  have hmem : ∀ t : CuspTorus v,
      (t, g t) ∈ Set.range (fun x : E3 => ((Quotient.mk'' x : CuspTorus v), beta x)) := by
    intro t
    exact ⟨Quotient.out t, Prod.ext (Quotient.out_eq' t)
      ((hgm (Quotient.out t)).symm.trans (congrArg g (Quotient.out_eq' t)))⟩
  refine ⟨{ toFun := fun t => ⟨(t, g t), hmem t⟩,
            invFun := fun q => q.1.1,
            left_inv := fun t => rfl,
            right_inv := fun q => by
              obtain ⟨⟨t, s⟩, x, hx⟩ := q
              obtain ⟨rfl, rfl⟩ := hx
              exact Subtype.ext (Prod.ext rfl (hgm x)),
            continuous_toFun := (continuous_id.prodMk hgcont).subtype_mk hmem,
            continuous_invFun := continuous_subtype_val.fst }, ?_⟩
  intro x
  exact Subtype.ext (Prod.ext rfl (hgm x))

end Work.Cusp
