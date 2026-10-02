import Mathlib
import Submission.Work.StemsB.rangeModelDefs
import Submission.Work.Serre.CWModel.Tower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The generator step preserves the invariant of the second structure map

`Work.StemsB.rangeModel_ratH_iso` builds, along the CW model tower of
`Work.Serre.CWModel.towerA`, a *second* structure map `c : C(Y, P)` into the second range model `P`
of `K(A, m+1)`, which is related to the structure map `g : C(Y, Z)` of the tower by
`Work.StemsB.SecondMapInv`: the base points match, `π_{m+1}(c)` and `π_{m+1}(g)` have the same
kernel, and `π_{m+1}(c)` is surjective.

This file proves the **generator step**: if `c` satisfies the invariant over the state `s : StA Z z₀ n`
of the tower, then it can be extended over the `(n+2)`-cells attached in
`Work.Serre.CWModel.genStep s` (which are attached along the *constant* maps at the base point, so
`c` — being constant with value `p₀` there — extends by the constant map) so that the invariant
still holds.

The degree hypothesis `m + 1 < n + 2` is exactly what makes the inclusion
`s.Y → (genStep s).Y` surjective on `π_{m+1}`: the attached cells have dimension `n + 2` (so
`π_{m+1}` is unchanged) and `m + 1 ≤ n + 1`.
-/

namespace Work.StemsB

open Work.Serre.CWModel Work.RatHurewicz

theorem secondMap_genStep {A : Type} [AddCommGroup A] {m : ℕ} {Z : Type} [TopologicalSpace Z]
    {z₀ : Z} {P : Type} [TopologicalSpace P] {p₀ : P} {n : ℕ} (hdeg : m + 1 < n + 2)
    (s : Work.Serre.CWModel.StA Z z₀ n) (c : C(s.Y, P))
    (hc : SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) s.y₀ s.g c) :
    ∃ c' : C((Work.Serre.CWModel.genStep s).Y, P),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) (Work.Serre.CWModel.genStep s).y₀
        (Work.Serre.CWModel.genStep s).g c' := by
  classical
  -- the attachment data of `genStep s`: one `(n+2)`-cell per element of `π_{n+2}`, attached along
  -- the constant map at `s.y₀`
  let ι := HomotopyGroup (Fin (n + 2)) Z (s.g s.y₀)
  let f : ι → C(cellSphere n, s.Y) := fun _ => ContinuousMap.const (cellSphere n) s.y₀
  -- the inclusion is surjective on `π_{m+1}` because the new cells have dimension `n+2 > m+1`
  have hsurj : Function.Surjective (Work.Serre.piMapN (attachIncl n s.Y ι f) (m + 1) s.y₀) := by
    by_cases hm : m + 1 ≤ n
    · exact (Work.Serre.attachIncl_piMap_bijective_of_compress n s.Y ι f s.y₀ (m + 1)
        (by omega) hm).2
    · -- otherwise `m = n`, and `attachIncl` is onto on `π_{n+1}`
      have hmn : m = n := by omega
      rw [hmn]
      exact surjective_πmap_attachIncl n s.Y ι f s.y₀
  -- the extension: `c` is constant `p₀` on the attaching spheres, being so at the base point
  have hC' : ∀ (j : ι) (z : cellSphere n),
      (ContinuousMap.const (cellDisk n) p₀) (cellSphereToDisk n z) = c (f j z) := by
    intro j z
    exact hc.1.symm
  let c' : C(attachCells n s.Y ι f, P) :=
    attachG n s.Y ι f c (fun _ => ContinuousMap.const (cellDisk n) p₀) hC'
  -- on `π_{m+1}`, the two structure maps are computed on the classes in the image of the inclusion
  have hg_eval : ∀ a : HomotopyGroup (Fin (m + 1)) s.Y s.y₀,
      Work.Serre.piMapN (genStep s).g (m + 1) (attachIncl n s.Y ι f s.y₀)
        (Work.Serre.piMapN (attachIncl n s.Y ι f) (m + 1) s.y₀ a)
      = Work.Serre.piMapN s.g (m + 1) s.y₀ a :=
    fun a => (Work.Serre.piMapN_comp (attachIncl n s.Y ι f) (genStep s).g (m + 1) s.y₀ a).symm
  have hc_eval : ∀ a : HomotopyGroup (Fin (m + 1)) s.Y s.y₀,
      Work.Serre.piMapN c' (m + 1) (attachIncl n s.Y ι f s.y₀)
        (Work.Serre.piMapN (attachIncl n s.Y ι f) (m + 1) s.y₀ a)
      = Work.Serre.piMapN c (m + 1) s.y₀ a :=
    fun a => (Work.Serre.piMapN_comp (attachIncl n s.Y ι f) c' (m + 1) s.y₀ a).symm
  refine ⟨c', ?_, ?_, ?_⟩
  · -- the base point: `genStep s` extends `s` and `c'` extends `c`
    exact hc.1
  · -- the kernels agree: transport along the surjectivity of the inclusion
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hsurj x
      have hx₂ : Work.Serre.piMapN s.g (m + 1) s.y₀ a = 1 :=
        (hg_eval a) ▸ ((congrArg (fun z => Work.Serre.piMapN (genStep s).g (m + 1)
          (genStep s).y₀ z) ha.symm) ▸ hx)
      have hx₃ : Work.Serre.piMapN c (m + 1) s.y₀ a = 1 := (hc.2.1 a).mp hx₂
      exact (congrArg (fun z => Work.Serre.piMapN c' (m + 1) (genStep s).y₀ z) ha) ▸
        ((hc_eval a).symm ▸ hx₃)
    · intro hx
      obtain ⟨a, ha⟩ := hsurj x
      have hx₂ : Work.Serre.piMapN c (m + 1) s.y₀ a = 1 :=
        (hc_eval a) ▸ ((congrArg (fun z => Work.Serre.piMapN c' (m + 1)
          (genStep s).y₀ z) ha.symm) ▸ hx)
      have hx₃ : Work.Serre.piMapN s.g (m + 1) s.y₀ a = 1 := (hc.2.1 a).mpr hx₂
      exact (congrArg (fun z => Work.Serre.piMapN (genStep s).g (m + 1) (genStep s).y₀ z) ha) ▸
        ((hg_eval a).symm ▸ hx₃)
  · -- surjectivity on `π_{m+1}`
    intro y
    obtain ⟨a, ha⟩ := hc.2.2 y
    exact ⟨Work.Serre.piMapN (attachIncl n s.Y ι f) (m + 1) s.y₀ a, (hc_eval a).symm ▸ ha⟩

end Work.StemsB
