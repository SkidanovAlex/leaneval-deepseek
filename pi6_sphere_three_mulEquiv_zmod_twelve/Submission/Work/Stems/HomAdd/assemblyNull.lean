import Submission.Work.RatHurewicz.AssemblyDefs
import Submission.Work.RatHurewicz.glue_homotopic_const
import Submission.Work.RatHurewicz.exists_collapse_zero
import Submission.Work.RatHurewicz.glue_class_of_collapse
import Submission.Work.RatHurewicz.Walk.pinchAllViaNet

/-!
# `assembly_null` and `glue_class_of_collapse`, closed

`Work.RatHurewicz.assembly_null` (the geometric core of Hutchings' `(2.5)`) and
`Work.RatHurewicz.glue_class_of_collapse` (the pinch of the gluing) were the two remaining gaps of
the cubical route to the integral Hurewicz theorem modulo torsion in the first non-vanishing degree
(`Work.RatHurewicz.hurewiczModTorsionFirstDegree`, blueprint step S1 for the SERRE subproject).

Both are proved here, in the area STEMS, from the pieces that are already in the workspace:

* `Work.RatHurewicz.glue_class_of_collapse_of_pinch` (proved in the RATHUREWICZ area) reduces the
  pinch to the general cubical homotopy-addition statement `Work.RatHurewicz.PinchAll`, and
* `Work.RatHurewicz.PinchAll` is now **proved** (`Work.RatHurewicz.Walk.pinchAllViaNet`).

The two files `assembly_null.lean` (whose only `sorry` is this theorem) and
`glue_class_of_collapse.lean` (whose only `sorry` is `glue_class_of_collapse`) can therefore both be
closed by replacing the `sorry` with the corresponding theorem of this file:

```
theorem assembly_null ... := Work.Stems.HomAdd.assemblyNull ...
theorem glue_class_of_collapse ... := Work.Stems.HomAdd.glueClassOfCollapse ...
```
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.HomAdd

noncomputable section

/-- **The gluing of the pieces is `x₀` on the `(m+1)`-skeleton and the class of the pinched gluing
is the alternating sum of the classes of the pieces** — `Work.RatHurewicz.glue_class_of_collapse`,
now proved: the only input it needed was the general cubical homotopy-addition statement
`Work.RatHurewicz.PinchAll`, which is proved in `Work.RatHurewicz.Walk.pinchAllViaNet`. -/
theorem glueClassOfCollapse {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) [Nontrivial (Fin (m + 2))]
    (τ : C(IC (m + 3), X))
    (φ : C(IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : glue N m K hN τ (φ 0) = x₀)
    (hinj : ∀ u v : IC (m + 2),
      u ∉ Cube.boundary (Fin (m + 2)) → φ u = φ v → u = v) :
    (cl (m + 2) X x₀
        ⟨(glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b))
    ∨ (cl (m + 2) X x₀
        ⟨(glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b))⁻¹) :=
  glue_class_of_collapse_of_pinch Walk.pinchAllViaNet N m K hN τ φ hφ hv hinj

/-- **The geometric core of Hutchings' `(2.5)`** — `Work.RatHurewicz.assembly_null`, now proved.

The two readings of the alternating sum of the pieces agree: the assembly `A` has class `W`
(`assembly_class`), while the gluing pinched to a cube has class `W` or `W⁻¹` (`glueClassOfCollapse`)
and is at the same time null, being the pull-back of the free null-homotopy of `glue`
(`glue_homotopic_const` and `cl_comp_collapse`).  Hence `W = 1`, so `cl A = 1`, and `A` is
null-homotopic by `Quotient.exact`. -/
theorem assemblyNull (N m : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X}
    (K : Tower x₀ N) (hN : m + 1 ≤ N) [Nontrivial (Fin (m + 2))]
    (τ : C(IC (m + 3), X)) :
    GenLoop.Homotopic (assembly N m K hN τ) GenLoop.const := by
  classical
  obtain ⟨φ, hφ0, _hφz, hφinj⟩ := exists_collapse_zero m
  obtain ⟨H, z, hH0, hH1⟩ := glue_homotopic_const N m K hN τ
  have h0mem : (0 : IC (m + 2)) ∈ Cube.boundary (Fin (m + 2)) := ⟨0, Or.inl rfl⟩
  -- the collapse is constant on the boundary, at the origin
  have hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0 :=
    fun u hu => Subtype.ext ((hφ0 u hu).trans (hφ0 0 h0mem).symm)
  -- and `glue` is `x₀` at the origin, so the pinched gluing is a based cube
  have hv : glue N m K hN τ (φ 0) = x₀ := by
    have hsub : φ 0 = ⟨0, zero_mem_boundary m⟩ := Subtype.ext (hφ0 0 h0mem)
    rw [hsub, glue_zero]
  -- the pinched gluing is null, being the pull-back of the free null-homotopy of `glue`
  have hclass := cl_comp_collapse N m K hN τ H z hH0 hH1 φ hφ hv
  -- so the alternating sum of the pieces is `1`
  have hW : (∏ i : Fin (m + 3), ∏ b : Fin 2,
      (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b)) = 1 := by
    rcases glueClassOfCollapse N m K hN τ φ hφ hv hφinj with h | h
    · exact h.symm.trans hclass
    · exact inv_eq_one.mp (h.symm.trans hclass)
  -- the assembly has the same class, hence is null
  have hone : cl (m + 2) X x₀ (assembly N m K hN τ) = 1 := by
    rw [assembly_class N m K hN τ, hW]
  rw [cl, HomotopyGroup.one_def] at hone
  exact Quotient.exact hone

end

end Work.Stems.HomAdd
