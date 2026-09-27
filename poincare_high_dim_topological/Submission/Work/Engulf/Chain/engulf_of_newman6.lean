import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.subcube_chart
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.exists_cubeChart_subcube

universe u

open Set Metric PL

namespace Work.Engulf.Chain

/-- The empty set is `d`-dominated: it is covered by the empty family of simplices. -/
theorem domDim_empty {N : ℕ} (d : ℤ) : PL.DomDim (∅ : Set (PL.E N)) d :=
  ⟨∅, by intro s hs; exact absurd hs (Finset.notMem_empty s), by simp⟩

/-- Pushing a cube chart of the complement of a closed set into the ambient space gives a cube
chart of the ambient space: the inclusion of the open complement is an open embedding. -/
theorem cubeChart_of_compl {n : ℕ} {M : Type*} [TopologicalSpace M] {A : Set M}
    (hA : IsClosed A) (ψ : PL.CubeChart n ↥(Aᶜ)) :
    ∃ χ : PL.CubeChart n M, ∀ z, χ.toFun z = (ψ.toFun z : M) := by
  have hincl : Topology.IsOpenEmbedding (Subtype.val : ↥(Aᶜ) → M) :=
    hA.isOpen_compl.isOpenEmbedding_subtypeVal
  refine ⟨{ toFun := fun z => (ψ.toFun z : M), cont := ?_, emb := ?_ }, fun z => rfl⟩
  · exact continuous_subtype_val.comp_continuousOn ψ.cont
  · have hcomp : Set.domRestrict (PL.openCube (n := n) 1) (fun z => (ψ.toFun z : M))
        = (Subtype.val : ↥(Aᶜ) → M) ∘ Set.domRestrict (PL.openCube (n := n) 1) ψ.toFun := by
      funext z
      rfl
    rw [hcomp]
    exact hincl.comp ψ.emb

/-- **`engulf_of_newman6`** (contract §8, `E0` = Newman's Theorem 5 from Theorem 6): the final engine of area A9, stated with `newman6` as a hypothesis so that it does not depend on the `Tools` bundle.  Given `newman6` (Theorem 6 for every configuration), prove `Work.Cells.Connell.EngulfForm n`: take the ambient dimension `N := 2 * p + 4`, the empty complex `Γ := ⊥ : PL.Cx N`, `H := L := ∅`, and the constant map `f` at a point of `V`; then `Amb` is the given data, `Cfg` has `fin`/`dimΓ`/`room`/`subH`/`subL`/`dimH`/`cpt`/`ov` immediate (`C := ∅` for `OvCtl`), and `Tame` is built from the domination hypothesis: at `x ∈ X` use its chart and its `DomDim` set; at `x ∉ X` (`X` is closed) shrink a `PL.LocCube` chart (`Work.Engulf.Aux.subcube_chart`) so that its closed unit cube misses `X`, and take the empty polyhedral set (`PL.DomDim ∅ p`).  Apply `h6` with any `ε > 0`; the conclusion `X ∪ g '' ∅ ⊆ h '' V` is `X ⊆ h '' V`. -/
theorem engulf_of_newman6 {n : ℕ}
    (h6 : ∀ (p : ℕ) (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : PL.Cx N)
       (H L : Set (PL.E N)) (f : PL.E N → M), Work.Engulf.Amb n p M V →
       Work.Engulf.Cfg n p V X Γ H L f → ∀ ε > 0, Work.Engulf.Engulfs V X Γ H L f ε) :
    Work.Cells.Connell.EngulfForm.{u} n := by
  intro p Y hY hp loc connM V hVo hVne connV X hXc hXcpt hdom
  classical
  have hAmb : Work.Engulf.Amb n p Y V :=
    { hp := hp
      loc := loc
      connM := connM
      Vo := hVo
      Vne := hVne
      connV := connV }
  obtain ⟨v, _hv⟩ := hVne
  let f : PL.E (2 * p + 4) → Y := fun _ => v
  have hTame : Work.Engulf.Tame n p X (⊥ : PL.Cx (2 * p + 4))
      (∅ : Set (PL.E (2 * p + 4))) f := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨ψ, hxψ, Pd, hPd, hPd'⟩ := hdom x hx
      refine ⟨ψ, hxψ, ⟨Pd, hPd, hPd'⟩, ?_⟩
      intro s hs
      rw [Geometry.SimplicialComplex.faces_bot] at hs
      exact absurd hs (Set.notMem_empty s)
    · obtain ⟨ψ₀, y₀, hy₀, hy₀eq⟩ := loc x
      have hy₀1 : y₀ ∈ PL.openCube (n := n) 1 :=
        Work.Engulf.openCube_mono (by norm_num : (1 / 2 : ℝ) ≤ 1) hy₀
      have hyA : ψ₀.toFun y₀ ∉ X := by rw [hy₀eq]; exact hx
      -- Shrink the local chart so that its closed unit cube misses the closed set `X`.
      -- This is the affine sub-cube chart of `Work.Engulf.Aux.subcube_chart`, packaged (with
      -- the elementary bound `‖z‖ ≤ √n` on `PL.closedCube 1`) as
      -- `Work.Cells.Connell.exists_cubeChart_subcube`, which produces the sub-cube chart on
      -- `↥Xᶜ`; pushing it into `Y` along the open inclusion `↥Xᶜ ↪ Y` (the helper
      -- `cubeChart_of_compl` above) gives the chart of `Y` needed here.
      obtain ⟨r, _hrpos, ψ, hψ1, _hψ2, hψ3⟩ :=
        Work.Cells.Connell.exists_cubeChart_subcube ψ₀ y₀ hy₀1 X hXc hyA ⟨x, hx⟩
      obtain ⟨χ, hχ⟩ := cubeChart_of_compl hXc ψ
      refine ⟨χ, ⟨0, ?_, ?_⟩, ⟨∅, domDim_empty (N := n) (p : ℤ), ?_⟩, ?_⟩
      · intro i; simp
      · rw [hχ 0, hψ1 0 (by intro i; simp)]
        simpa using hy₀eq
      · intro y hy hyX
        by_cases hyopen : y ∈ PL.openCube (n := n) 1
        · rw [hχ y, hψ1 y hyopen] at hyX
          exact (hψ3 y hy).2 hyX
        · rw [hχ y, _hψ2 y hyopen] at hyX
          exact hx hyX
      · intro s hs
        rw [Geometry.SimplicialComplex.faces_bot] at hs
        exact absurd hs (Set.notMem_empty s)
  have hCfg : Work.Engulf.Cfg n p V X (⊥ : PL.Cx (2 * p + 4)) ∅
      (∅ : Set (PL.E (2 * p + 4))) f :=
    { fin := by rw [Geometry.SimplicialComplex.faces_bot]; exact Set.finite_empty
      dimΓ := by
        intro s hs
        rw [Geometry.SimplicialComplex.faces_bot] at hs
        exact absurd hs (Set.notMem_empty s)
      room := le_rfl
      subH := Work.Engulf.isSubSp_empty ⊥
      subL := Work.Engulf.isSubSp_empty ⊥
      dimH := by
        intro s hs
        rw [Geometry.SimplicialComplex.faces_bot] at hs
        exact absurd hs (Set.notMem_empty s)
      cont := by rw [Geometry.SimplicialComplex.space_bot]; exact continuousOn_empty f
      Xc := hXc
      cpt := by rw [Set.image_empty, Set.union_empty]; exact hXcpt
      tame := hTame
      ov := ⟨∅, isCompact_empty, by simp,
        (by intro x hx; exact absurd hx.1 (Set.notMem_empty x)),
        (by intro x hx; exact absurd hx.1 (Set.notMem_empty x))⟩ }
  obtain ⟨g, _hgcont, _hgfrz, _hgdist, h, hsupp, heng⟩ :=
    h6 p Y V X (2 * p + 4) (⊥ : PL.Cx (2 * p + 4)) ∅ ∅ f hAmb hCfg (1 : ℝ) one_pos
  exact ⟨h, hsupp, fun x hx => heng (Or.inl hx)⟩

end Work.Engulf.Chain
