import Submission.Work.Stems.Hur2c.PsiLin_degen
import Submission.Work.RatHurewicz.CubicalDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Ψ` of a degenerate `2`-cycle vanishes

**(4b)** of `Submission/Work/Stems/Hur2c/STATUS.md`: the filling `Ψ x₀ d` of a degenerate cubical
`2`-cycle `d` is trivial.  This is the correct target (the naive `Ψ` of *every* degenerate `2`-cube
is not provable for the opaque `Ψ`; see `Submission/Work/Stems/PSI_DEG_NOTES.md`).

The proof is structural: the `ℤ`-linear functional

`G := Ψ − Λ ∘ ∂`   (`Λ (single e 1) = −φ (e 0)`, `φ v = T x₀ 0 (cubeOfPath (K₀ x₀ v))`)

vanishes on the generators `single (degenCube k δ) 1` of the degenerate `2`-chains
(`PsiLin_single_degen`), hence on the whole span `Work.Stems.degenSub 2 X = Work.RatHurewicz.Deg 2 X`;
a cycle then has `Ψ d = G d + Λ (∂ d) = 0`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## `Deg` is the span of the degenerate cubes -/

theorem Deg_le_degenSub (n : ℕ) (X : Type) [TopologicalSpace X] :
    Work.RatHurewicz.Deg n X ≤ Work.Stems.degenSub n X := by
  rw [Work.RatHurewicz.Deg]
  refine iSup_le fun i => ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨f, hf, rfl⟩
  exact Submodule.subset_span ⟨f, ⟨i, hf⟩, rfl⟩

theorem degenSub_le_Deg (n : ℕ) (X : Type) [TopologicalSpace X] :
    Work.Stems.degenSub n X ≤ Work.RatHurewicz.Deg n X := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨s, ⟨i, hs⟩, rfl⟩
  rw [Work.RatHurewicz.Deg]
  exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨s, hs, rfl⟩)

/-- The degenerate cubical chains of the workspace's bridge are the span of the degenerate cubes. -/
theorem Deg_eq_degenSub (n : ℕ) (X : Type) [TopologicalSpace X] :
    Work.RatHurewicz.Deg n X = Work.Stems.degenSub n X :=
  le_antisymm (Deg_le_degenSub n X) (degenSub_le_Deg n X)

/-! ## Every degenerate `2`-cube is a `degenCube` -/

/-- A `2`-cube which is independent of the coordinate `j` (i.e. `IsDegenerate 2` witnessed by `j`)
is `degenCube k δ` for the *other* coordinate `k ≠ j`. -/
theorem exists_degenCube_of_indep {s : C(IC 2, X)} {j k : Fin 2} (hjk : j ≠ k)
    (hs : ∀ t t' : IC 2, (∀ i, i ≠ j → t i = t' i) → s t = s t') :
    ∃ δ : C(IC 1, X), s = degenCube k δ := by
  refine ⟨⟨fun u : IC 1 => s (fun _ : Fin 2 => u 0),
    s.continuous.comp (continuous_pi fun _ => continuous_apply (0 : Fin 1))⟩, ?_⟩
  ext t
  show s t = s (fun _ : Fin 2 => t k)
  refine hs t (fun _ : Fin 2 => t k) ?_
  intro i hi
  show t i = t k
  have h2 : i = k := by
    apply Fin.ext
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hi (Fin.ext h)
    have hjk' : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
    have hi2 := i.isLt
    have hj2 := j.isLt
    have hk2 := k.isLt
    omega
  rw [h2]

/-! ## The linear functional whose pull-back along `∂` is `Ψ` on degenerate cubes -/

/-- `G := Ψ − Λ ∘ ∂`.  It vanishes on the degenerate `2`-chains. -/
def G (x₀ : X) : Cub 2 X →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x₀) :=
  Work.Stems.Hur2.PsiLin x₀ - (Lambda x₀).comp (cubD 1 X)

theorem G_degenCube (x₀ : X) (k : Fin 2) (δ : C(IC 1, X)) :
    G x₀ (Finsupp.single (degenCube k δ) 1) = 0 := by
  simp only [G, LinearMap.sub_apply, LinearMap.comp_apply, PsiLin_single_degen, sub_self]

/-- **`Ψ` vanishes on every degenerate cubical `2`-cycle.** -/
theorem PsiLin_eq_zero_of_degen_cycle (x₀ : X) (d : Cub 2 X)
    (hd : d ∈ Work.Stems.degenSub 2 X) (hcyc : cubD 1 X d = 0) :
    Work.Stems.Hur2.PsiLin x₀ d = 0 := by
  have hsub : Work.Stems.degenSub 2 X ≤ LinearMap.ker (G x₀) := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨s, ⟨j, hs⟩, rfl⟩
    change G x₀ (Finsupp.single s 1) = 0
    obtain ⟨δ, hδ⟩ := exists_degenCube_of_indep (X := X) (j := j)
      (k := (⟨1 - j.val, by omega⟩ : Fin 2)) (by
        intro hc
        have h := congrArg Fin.val hc
        simp only [Fin.val_mk] at h
        omega) hs
    rw [hδ]
    exact G_degenCube x₀ _ δ
  have hG : G x₀ d = 0 := LinearMap.mem_ker.mp (hsub hd)
  have hsplit : Work.Stems.Hur2.PsiLin x₀ d = G x₀ d + Lambda x₀ (cubD 1 X d) := by
    simp only [G, LinearMap.sub_apply, LinearMap.comp_apply]
    abel
  rw [hsplit, hG, hcyc, map_zero, zero_add]

/-- The same, in the phrasing of the bridge (`Work.RatHurewicz.Deg`). -/
theorem PsiLin_eq_zero_of_degen_cycle_of_Deg (x₀ : X) (d : Cub 2 X)
    (hd : d ∈ Work.RatHurewicz.Deg 2 X) (hcyc : cubD 1 X d = 0) :
    Work.Stems.Hur2.PsiLin x₀ d = 0 :=
  PsiLin_eq_zero_of_degen_cycle x₀ d (le_of_eq (Deg_eq_degenSub 2 X) hd) hcyc

end

end Work.Stems.Hur2c
