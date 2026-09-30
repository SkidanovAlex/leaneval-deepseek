import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Tools
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.relChainsCubeDisc
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.cubeAmbient_isZero

/-!
# The source side of the per-cell computation: the disc pair

For the pullback `π = pullbackSnd q (cellMap i)` of a Serre fibration `q` along the characteristic
map of the `i`-th `(n+2)`-cell, the relative homology over `ℤ` of the preimage of the pair
`(D^{n+2}, S^{n+1})` is the homology of the fibre over the centre of the cell, shifted by `n+2`,

  `H_{k+n+2}(π⁻¹D^{n+2}, π⁻¹S^{n+1};ℤ) ≅ H_k(F_{c_i};ℤ)`,

and it vanishes in degrees `< n+2`.  This is `Work.Serre.serreE2d` applied to the fibration
`π ×_{cellDisk} I^{n+2} → cellDisk` over the cube `I^{n+2}` (through the homeomorphism
`cubeDiscHomeo n`), composed with `Work.Serre.Csr.relChainsCubeDisc` and the bookkeeping between the
several models of the pair (associativity of the pullback, and the closed disc being the whole model
cell).
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.Csr

noncomputable section

/-! ## The bookkeeping homeomorphisms -/

/-- **The associativity homeomorphism of double pullbacks.**  For `q : E → B`, `χ : B' → B` and
`τ : B'' → B'`, the pullback of `pullbackSnd q χ` along `τ` is canonically homeomorphic to the
pullback of `q` along `χ ∘ τ`. -/
def pullbackAssocHomeo {E B B' B'' : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace B'] [TopologicalSpace B''] (q : C(E, B)) (χ : C(B', B)) (τ : C(B'', B')) :
    Work.StemsB.Pullback (Work.StemsB.pullbackSnd q χ) τ ≃ₜ
      Work.StemsB.Pullback q (χ.comp τ) where
  toFun x := ⟨(x.1.1.1.1, x.1.2), by
    have h2 : x.1.1.1.2 = τ x.1.2 := x.2
    rw [ContinuousMap.comp_apply, ← h2]
    exact x.1.1.2⟩
  invFun y := ⟨(⟨(y.1.1, τ y.1.2), y.2⟩, y.1.2), rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact x.2.symm
    · rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (f := fun x : Work.StemsB.Pullback
      (Work.StemsB.pullbackSnd q χ) τ => (x.1.1.1.1, x.1.2)) ?_ _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (f := fun y : Work.StemsB.Pullback q (χ.comp τ) =>
      ((⟨(y.1.1, τ y.1.2), y.2⟩ : Work.StemsB.Pullback q χ), y.1.2)) ?_ _
    fun_prop

/-- **The fibre of a pullback projection is the fibre of the original map.** -/
def fibrePullbackHomeo {E B B' : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace B'] (q : C(E, B)) (χ : C(B', B)) (y : B') :
    Work.StemsB.fibre (Work.StemsB.pullbackSnd q χ) y ≃ₜ Work.StemsB.fibre q (χ y) where
  toFun x := ⟨x.1.1.1, Eq.trans x.1.2 (congrArg χ x.2)⟩
  invFun z := ⟨⟨(z.1, y), z.2⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.2.symm
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (f := fun x : Work.StemsB.fibre
      (Work.StemsB.pullbackSnd q χ) y => x.1.1.1) ?_ _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (f := fun z : Work.StemsB.fibre q (χ y) =>
      (⟨(z.1, y), z.2⟩ : Work.StemsB.Pullback q χ)) ?_ _
    fun_prop

/-- **The preimage of the closed model cell is the whole pullback.**  The closed model cell
`dClosed n 1` is the whole disc, so the two models of the pair `(π⁻¹D, π⁻¹S)` agree. -/
def preClosedHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    ↥(pPre f q i (dClosed n 1)) ≃ₜ csrPull f q i where
  toFun := Subtype.val
  invFun y := ⟨y, by
    show Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) y ∈ dClosed n 1
    rw [mem_dClosed]
    have h := Metric.mem_closedBall.mp
      (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) y).2
    simpa [dist_eq_norm] using h⟩
  left_inv x := Subtype.ext rfl
  right_inv y := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by fun_prop

/-- **The two models of the preimage pair.**  The relative chain complex of the pair
`(π⁻¹dClosed, π⁻¹dSph)` computed inside the subtype `↥(π⁻¹dClosed)` agrees with the relative chain
complex of the same pair computed in the ambient pullback. -/
theorem preClosedPairIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dClosed n 1)))
        {x : ↥(pPre f q i (dClosed n 1)) |
          (x : csrPull f q i) ∈ pPre f q i (dSph n 1)}).homology m)
      ≅ ((Work.Cohomology.relChains (TopCat.of (csrPull f q i))
        {x : csrPull f q i |
          Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) x ∈ dSph n 1}).homology m)) := by
  refine Work.Cohomology.relChainsHomeomorphCompat _ _ _ _ (preClosedHomeo n Y ι f q i) ?_ m
  intro x
  exact Iff.rfl

/-! ## The transports of the E2(d) identification -/

/-- **The bookkeeping transports of the model pair.**  Composing the associativity of the pullback
with `Work.Serre.Csr.relChainsCubeDisc` and with the identification of the two models of the pair
`(π⁻¹dClosed, π⁻¹dSph)`: the relative homology of the double pullback over the cube pair is that of
the preimage of the disc pair. -/
theorem discModelIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of (Work.StemsB.Pullback
          (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
          (homeoToCM (cubeDiscHomeo n))))
        {x | Work.StemsB.pullbackSnd
          (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
          (homeoToCM (cubeDiscHomeo n)) x ∈ Cube.boundary (Fin (n+2))}).homology m)
      ≅ ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dClosed n 1)))
        {x : ↥(pPre f q i (dClosed n 1)) |
          (x : csrPull f q i) ∈ pPre f q i (dSph n 1)}).homology m)) := by
  obtain ⟨eA⟩ := Work.Cohomology.relChainsHomeomorphCompat
    (Work.StemsB.Pullback (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
      (homeoToCM (cubeDiscHomeo n)))
    (Work.StemsB.Pullback q ((Work.RatHurewicz.cellMap n Y ι f i).comp
      (homeoToCM (cubeDiscHomeo n))))
    {x : Work.StemsB.Pullback (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
        (homeoToCM (cubeDiscHomeo n)) |
      Work.StemsB.pullbackSnd (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
        (homeoToCM (cubeDiscHomeo n)) x ∈ Cube.boundary (Fin (n+2))}
    {y : Work.StemsB.Pullback q ((Work.RatHurewicz.cellMap n Y ι f i).comp
        (homeoToCM (cubeDiscHomeo n))) |
      Work.StemsB.pullbackSnd q ((Work.RatHurewicz.cellMap n Y ι f i).comp
        (homeoToCM (cubeDiscHomeo n))) y ∈ Cube.boundary (Fin (n+2))}
    (pullbackAssocHomeo q (Work.RatHurewicz.cellMap n Y ι f i) (homeoToCM (cubeDiscHomeo n)))
    (fun x => Iff.rfl) m
  obtain ⟨eB⟩ := relChainsCubeDisc n Y ι f q i m
  obtain ⟨eC⟩ := preClosedPairIso n Y ι f q i m
  exact ⟨eA ≪≫ eB ≪≫ eC.symm⟩

/-! ## The two consequences -/

/-- **The source side of the per-cell computation, in positive degrees.**  The relative homology of
the preimage of the disc pair, shifted by the dimension `n+2`, is the homology of the fibre of `q`
over the centre of the cell. -/
theorem csrSourceDiscIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (k : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dClosed n 1)))
        {x : ↥(pPre f q i (dClosed n 1)) |
          (x : csrPull f q i) ∈ pPre f q i (dSph n 1)}).homology (k + (n+2)))
      ≅ ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q
          (Work.RatHurewicz.cellOrigin n Y ι f i)))).homology k)) := by
  obtain ⟨e1⟩ := serreE2d (Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i))
    (Work.RatHurewicz.cellDisk n) (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
    (n+2) (fun d => Work.StemsB.hasHLP_pullback q (Work.RatHurewicz.cellMap n Y ι f i) (hq d))
    (homeoToCM (cubeDiscHomeo n))
    ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n)) k
  obtain ⟨e2⟩ := discModelIso n Y ι f q i (k + (n+2))
  obtain ⟨e3⟩ := absHomologyIsoOfHomeo
    (X := TopCat.of (Work.StemsB.fibre
      (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
      (homeoToCM (cubeDiscHomeo n) ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n)))))
    (Y := TopCat.of (Work.StemsB.fibre q
      (Work.RatHurewicz.cellMap n Y ι f i (homeoToCM (cubeDiscHomeo n)
        ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n))))))
    (fibrePullbackHomeo q (Work.RatHurewicz.cellMap n Y ι f i)
      (homeoToCM (cubeDiscHomeo n) ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n)))) k
  have hτ : homeoToCM (cubeDiscHomeo n) ((cubeDiscHomeo n).symm
      (Work.RatHurewicz.cellDiskCentre n)) = Work.RatHurewicz.cellDiskCentre n := by
    rw [homeoToCM_apply, Homeomorph.apply_symm_apply]
  have hχ : Work.RatHurewicz.cellMap n Y ι f i (homeoToCM (cubeDiscHomeo n)
      ((cubeDiscHomeo n).symm (Work.RatHurewicz.cellDiskCentre n)))
      = Work.RatHurewicz.cellOrigin n Y ι f i := by
    rw [hτ]
    rfl
  refine ⟨e2.symm ≪≫ e1 ≪≫ e3 ≪≫ eqToIso ?_⟩
  exact congrArg (fun b => (Work.Cohomology.singularChains ℤ
    (TopCat.of (Work.StemsB.fibre q b))).homology k) hχ

/-- **The source side of the per-cell computation, below the dimension.**  The relative homology of
the preimage of the disc pair vanishes in degrees `< n+2`. -/
theorem csrSourceDisc_isZero (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (m : ℕ) (hm : m < n+2) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pPre f q i (dClosed n 1)))
        {x : ↥(pPre f q i (dClosed n 1)) |
          (x : csrPull f q i) ∈ pPre f q i (dSph n 1)}).homology m) := by
  have h1 := cubeAmbient_isZero (n+2) (Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i))
    (Work.RatHurewicz.cellDisk n) (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i))
    (fun d => Work.StemsB.hasHLP_pullback q (Work.RatHurewicz.cellMap n Y ι f i) (hq d))
    (homeoToCM (cubeDiscHomeo n)) m hm
  obtain ⟨e2⟩ := discModelIso n Y ι f q i m
  exact h1.of_iso e2.symm

end

end Work.Serre.Csr
