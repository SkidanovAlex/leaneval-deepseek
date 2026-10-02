import Mathlib
import Submission.Work.StemsB.rangeModelDefs
import Submission.Work.StemsB.wedgeCellDefs
import Submission.Work.StemsB.wedgeGenerate
import Submission.Work.Serre.CWModel.Gen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The second structure map at the first generator step of the model tower

`Work.Serre.CWModel.genStep (Work.Serre.CWModel.baseState Z z₀ (m+1) …)` is the space obtained from
a *point* by attaching one `(m+1)`-cell per element of `π_{m+1}(Z)`, i.e. a wedge of
`π_{m+1}(Z)`-many `(m+1)`-spheres; the structure map `g'` sends the cell of `α` to a representative
of `α`.  The lemma below produces the *second* structure map `c : Γ → P` for a space `P` with
`π_{m+1}(P) ≃* π_{m+1}(Z)` (via `Λ`): cell-by-cell it sends the cell of `α` to a representative of
`Λ α`, and it satisfies `Work.StemsB.SecondMapInv` at degree `m+1`:

* `c y₀ = p₀`;
* `ker π_{m+1}(g') = ker π_{m+1}(c)` — because both maps have the same action on the generators of
  `π_{m+1}` of the wedge (`Work.StemsB.wedge_cellClass_generate`) and `Λ` is injective;
* `π_{m+1}(c)` is surjective — because it equals `Λ ∘ π_{m+1}(g')` and `π_{m+1}(g')` is surjective
  (`Work.Serre.CWModel.StG.surj`).

The degree bookkeeping is arranged by writing `m = k + 1`: then the degree of the attached cells
`((k+1+1)-2)+2` and the degree `k+1+1 = m+1` of `SecondMapInv` are *definitionally* equal, so no
transport of homotopy groups is needed anywhere.
-/

namespace Work.StemsB

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

set_option maxHeartbeats 4000000

/-- **The universal property of the cell classes**: two homomorphisms out of `π_{n+2}` of the wedge
which agree on the classes of the cells are equal.  This is the form of
`Work.StemsB.wedge_generate` (`β ∈ Subgroup.closure (Set.range (wCellClass S))`) which is used
below. -/
theorem wedge_homs_eq_of_cellClass {n : ℕ} (S : Type) {G : Type} [Group G]
    (φ ψ : HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S) →* G)
    (h : ∀ s : S, φ (Work.StemsB.wCellClass S s) = ψ (Work.StemsB.wCellClass S s)) :
    φ = ψ := by
  refine MonoidHom.ext (fun β => ?_)
  refine Subgroup.closure_induction (p := fun β _ => φ β = ψ β) ?_ ?_ ?_ ?_
    (Work.StemsB.wedge_generate n S β)
  · intro x hx
    obtain ⟨s, rfl⟩ := hx
    exact h s
  · rw [map_one, map_one]
  · intro x y _ _ hx hy
    rw [map_mul, map_mul, hx, hy]
  · intro x _ hx
    rw [map_inv, map_inv, hx]


theorem secondMap_firstGenStep {A : Type} [AddCommGroup A] {m : ℕ} (hm : 1 ≤ m)
    {Z : Type} [TopologicalSpace Z] {z₀ : Z} {P : Type} [TopologicalSpace P] {p₀ : P}
    (hconn : ∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) Z z₀))
    (Λ : HomotopyGroup (Fin (m + 1)) Z z₀ ≃* HomotopyGroup (Fin (m + 1)) P p₀) :
    ∃ c : C((Work.Serre.CWModel.genStep
        (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega) hconn)).Y, P),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀)
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega) hconn)).y₀
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega) hconn)).g c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- the base state of the tower and the first generator step
  let s : Work.Serre.CWModel.StA Z z₀ ((k + 1 + 1) - 2) :=
    Work.Serre.CWModel.baseState Z z₀ (k + 1 + 1) (by omega) hconn
  let st : Work.Serre.CWModel.StG Z z₀ ((k + 1 + 1) - 2) := Work.Serre.CWModel.genStep s
  -- the index type of the attached cells is `π_{m+1}(Z)`
  let ι := HomotopyGroup (Fin ((k + 1 + 1) - 2 + 2)) Z z₀
  -- the cube/disc homeomorphism of the `genStep` construction and its inverse
  let e : Work.Stems.Cubical.IC ((k + 1 + 1) - 2 + 2) ≃ₜ Work.RatHurewicz.cellDisk ((k + 1 + 1) - 2) :=
    Classical.choose (Work.Serre.cubeDiskHomeo (((k + 1 + 1) - 2) + 2))
  let esym : C(Work.RatHurewicz.cellDisk ((k + 1 + 1) - 2), Work.Stems.Cubical.IC ((k + 1 + 1) - 2 + 2)) :=
    ⟨⇑e.symm, e.continuous_invFun⟩
  have he : ∀ x : Work.Stems.Cubical.IC ((k + 1 + 1) - 2 + 2),
      x ∈ Cube.boundary (Fin ((k + 1 + 1) - 2 + 2)) ↔
        (e x : EuclideanSpace ℝ (Fin ((k + 1 + 1) - 2 + 2))) ∈ Metric.sphere 0 1 :=
    Classical.choose_spec (Work.Serre.cubeDiskHomeo (((k + 1 + 1) - 2) + 2))
  -- the cell maps of the second structure map: a representative of `Λ j` on the cell of `j`
  let GP : ι → C(Work.RatHurewicz.cellDisk ((k + 1 + 1) - 2), P) :=
    fun j => (Quotient.out (Λ j)).1.comp esym
  have hGP : ∀ (j : ι) (z : Work.RatHurewicz.cellSphere ((k + 1 + 1) - 2)),
      GP j (Work.RatHurewicz.cellSphereToDisk _ z) = p₀ := by
    intro j z
    have hzb : e.symm (Work.RatHurewicz.cellSphereToDisk ((k + 1 + 1) - 2) z)
        ∈ Cube.boundary (Fin ((k + 1 + 1) - 2 + 2)) := by
      refine (he _).mpr ?_
      show (e (e.symm (Work.RatHurewicz.cellSphereToDisk ((k + 1 + 1) - 2) z)) :
        EuclideanSpace ℝ (Fin ((k + 1 + 1) - 2 + 2))) ∈ Metric.sphere 0 1
      rw [Homeomorph.apply_symm_apply]
      exact z.2
    show (Quotient.out (Λ j)).1
      (e.symm (Work.RatHurewicz.cellSphereToDisk ((k + 1 + 1) - 2) z)) = p₀
    exact (Quotient.out (Λ j)).2 _ hzb
  -- the second structure map
  let c : C(Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι, P) :=
    Work.Serre.CWModel.attachG ((k + 1 + 1) - 2) PUnit ι (Work.Serre.Wedge.wF ((k + 1 + 1) - 2) ι)
      (ContinuousMap.const PUnit p₀) GP hGP
  -- the cell classes, as elements of `π_{m+1}` of the generator step
  let cc : ι → HomotopyGroup (Fin (k + 1 + 1)) st.Y st.y₀ := fun j => Work.StemsB.wCellClass ι j
  -- the values of the two structure maps on the characteristic maps of the cells
  have hcellA : ∀ (j : ι) (z : Work.RatHurewicz.cellDisk ((k + 1 + 1) - 2)),
      st.g (Work.RatHurewicz.cellMap ((k + 1 + 1) - 2) PUnit ι
          (Work.Serre.Wedge.wF ((k + 1 + 1) - 2) ι) j z)
        = (Quotient.out j).1 (e.symm z) := fun _ _ => rfl
  have hcellB : ∀ (j : ι) (z : Work.RatHurewicz.cellDisk ((k + 1 + 1) - 2)),
      c (Work.RatHurewicz.cellMap ((k + 1 + 1) - 2) PUnit ι
          (Work.Serre.Wedge.wF ((k + 1 + 1) - 2) ι) j z)
        = (Quotient.out (Λ j)).1 (e.symm z) := fun _ _ => rfl
  -- the same, on the loop carried by a cell (i.e. after applying the structural map to `π`)
  have hloopA : ∀ j : ι, Work.StemsB.genLoopMap st.g ((k + 1 + 1) - 2 + 2)
      (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
        Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
          (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι)) = Quotient.out j := by
    intro j
    apply GenLoop.ext
    intro x
    show st.g ((Work.RatHurewicz.cellMap ((k + 1 + 1) - 2) PUnit ι
        (Work.Serre.Wedge.wF ((k + 1 + 1) - 2) ι) j) (e x)) = (Quotient.out j).1 x
    exact (hcellA j (e x)).trans
      (congrArg (Quotient.out j).1 (Homeomorph.symm_apply_apply e x))
  have hloopB : ∀ j : ι, Work.StemsB.genLoopMap c ((k + 1 + 1) - 2 + 2)
      (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
        Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
          (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι)) = Quotient.out (Λ j) := by
    intro j
    apply GenLoop.ext
    intro x
    show c ((Work.RatHurewicz.cellMap ((k + 1 + 1) - 2) PUnit ι
        (Work.Serre.Wedge.wF ((k + 1 + 1) - 2) ι) j) (e x)) = (Quotient.out (Λ j)).1 x
    exact (hcellB j (e x)).trans
      (congrArg (Quotient.out (Λ j)).1 (Homeomorph.symm_apply_apply e x))
  -- on the cell classes themselves
  have hA : ∀ j : ι, Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ (cc j) = j := by
    intro j
    have h1 : Work.Serre.piMapN st.g ((k + 1 + 1) - 2 + 2) st.y₀
        (Quotient.mk _ (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
          Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
            (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι)))
        = Quotient.mk _ (Work.StemsB.genLoopMap st.g ((k + 1 + 1) - 2 + 2)
          (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
            Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
              (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι))) := rfl
    exact h1.trans ((congrArg (Quotient.mk _) (hloopA j)).trans (Quotient.out_eq j))
  have hB : ∀ j : ι, Work.Serre.piMapN c (k + 1 + 1) st.y₀ (cc j) = Λ j := by
    intro j
    have h1 : Work.Serre.piMapN c ((k + 1 + 1) - 2 + 2) st.y₀
        (Quotient.mk _ (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
          Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
            (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι)))
        = Quotient.mk _ (Work.StemsB.genLoopMap c ((k + 1 + 1) - 2 + 2)
          (⟨Work.StemsB.wCellCube ι j, Work.StemsB.wCellCube_boundary ι j⟩ :
            Ω^ (Fin ((k + 1 + 1) - 2 + 2)) (Work.Serre.Wedge.wX ((k + 1 + 1) - 2) ι)
              (Work.Serre.Wedge.wB ((k + 1 + 1) - 2) ι))) := rfl
    exact h1.trans ((congrArg (Quotient.mk _) (hloopB j)).trans (Quotient.out_eq (Λ j)))
  -- the two induced maps on `π_{m+1}` agree: `Λ ∘ π(g') = π(c)` on the cell classes, hence
  -- everywhere, since the cell classes generate `π_{m+1}` of the wedge
  -- (`Work.StemsB.wedge_generate`)
  have hAB : ((Λ : HomotopyGroup (Fin (k + 1 + 1)) Z z₀ →*
        HomotopyGroup (Fin (k + 1 + 1)) P p₀).comp
        (Work.StemsB.πmap st.g ((k + 1 + 1) - 1) st.y₀))
      = Work.StemsB.πmap c ((k + 1 + 1) - 1) st.y₀ := by
    refine wedge_homs_eq_of_cellClass (n := (k + 1 + 1) - 2) ι _ _ ?_
    intro j
    have hA' : Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ (Work.StemsB.wCellClass ι j) = j :=
      hA j
    have hB' : Work.Serre.piMapN c (k + 1 + 1) st.y₀ (Work.StemsB.wCellClass ι j) = Λ j :=
      hB j
    have step1 : ((Λ : HomotopyGroup (Fin (k + 1 + 1)) Z z₀ →*
          HomotopyGroup (Fin (k + 1 + 1)) P p₀).comp
          (Work.StemsB.πmap st.g ((k + 1 + 1) - 1) st.y₀)) (Work.StemsB.wCellClass ι j)
        = Λ (Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ (Work.StemsB.wCellClass ι j)) :=
      MonoidHom.comp_apply _ _ _
    have step4 : (Work.StemsB.πmap c ((k + 1 + 1) - 1) st.y₀) (Work.StemsB.wCellClass ι j)
        = Work.Serre.piMapN c (k + 1 + 1) st.y₀ (Work.StemsB.wCellClass ι j) := rfl
    refine step1.trans ?_
    rw [hA']
    exact hB'.symm.trans step4.symm
  refine ⟨c, ?_, ?_, ?_⟩
  · -- the base point
    exact rfl
  · -- the kernels agree
    show ∀ x : HomotopyGroup (Fin (k + 1 + 1)) st.Y st.y₀,
        Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ x = 1 ↔
          Work.Serre.piMapN c (k + 1 + 1) st.y₀ x = 1
    intro x
    have hx : Λ (Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ x)
        = Work.Serre.piMapN c (k + 1 + 1) st.y₀ x := by
      have h := congrFun (congrArg (fun F : HomotopyGroup (Fin (k + 1 + 1)) st.Y st.y₀ →*
          HomotopyGroup (Fin (k + 1 + 1)) P p₀ => ⇑F) hAB) x
      exact h
    constructor
    · intro hg
      show Work.Serre.piMapN c (k + 1 + 1) st.y₀ x = 1
      rw [← hx, hg]
      exact map_one Λ
    · intro hc
      show Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ x = 1
      exact Λ.injective (by rw [hx, hc]; exact (map_one Λ).symm)
  · -- surjectivity
    intro y
    obtain ⟨z, rfl⟩ := Λ.surjective y
    obtain ⟨x, hx⟩ := st.surj z
    have hx' : Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ x = z := hx
    have hx2 : Λ (Work.Serre.piMapN st.g (k + 1 + 1) st.y₀ x)
        = Work.Serre.piMapN c (k + 1 + 1) st.y₀ x := by
      have h := congrFun (congrArg (fun F : HomotopyGroup (Fin (k + 1 + 1)) st.Y st.y₀ →*
          HomotopyGroup (Fin (k + 1 + 1)) P p₀ => ⇑F) hAB) x
      exact h
    refine ⟨x, ?_⟩
    show Work.Serre.piMapN c (k + 1 + 1) st.y₀ x = Λ z
    rw [← hx2, hx']

end

end Work.StemsB
