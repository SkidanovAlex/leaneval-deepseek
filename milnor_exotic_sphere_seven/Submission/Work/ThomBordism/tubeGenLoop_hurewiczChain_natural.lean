import Mathlib
import Submission.Work.ThomBordism.blowPsi
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.Stems.hurewiczChain_eq_of_homotopic
import Submission.Work.ThomBordism.TubeGenAux
import Submission.Work.ThomBordism.tubeGen_gInfty
import Submission.Work.ThomBordism.tubeGen_margin
import Submission.Work.ThomBordism.tubeGen_estimate
import Submission.Work.ThomBordism.tubeGen_isOpen_goodSet
import Submission.Work.ThomBordism.tubeGen_continuous_thetaHomotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Naturality of the Hurewicz chain of the Pontryagin–Thom cube loop

`Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox` is the Pontryagin–Thom cube loop of a tubular
neighbourhood: the cube `I^{8+k}` is parametrised linearly as the box `[-R,R]^{8+k}`, pushed into
the Thom space `ν⁺` by a collapse `g` which is the basepoint off the open tube.  This file proves
that its Hurewicz chain is the push-forward along `g` of the Hurewicz chain of the *standard*
collapse `Work.Stems.cubeToOnePoint` of the cube onto `S^{8+k} = OnePoint (ℝ^{8+k})`.

Two facts enter, both proved elsewhere in the workspace:

* `Work.ThomBordism.tubeGen_gInfty` — `hg` together with the compactness of the tube forces
  `g ∞ = ∞`, so that the push-forward `g ∘ cubeToOnePoint` is a cube loop based at `∞`;
* the interpolating family `Work.ThomBordism.TubeGen.thetaHomotopyFun`: at time `s` the cube point
  `t` is sent to `∞` if `t` is on the boundary of the cube and to `g (θ_s (cubeCoords t))`
  otherwise, where `θ_s(y) = (1-s)·(R·y/√(1+y²)) + s·y`.  It joins the tube loop (`s = 0`, using
  `θ_0 (cubeCoords t) = cubeToEuc R t`) with the push-forward of `StandardCollapse` (`s = 1`), is
  constant on the boundary of the cube, and is continuous by the estimate `θ_s(y) ≥ R - δ` for
  `|y|` large (`Work.ThomBordism.tubeGen_estimate`).

The conclusion is then the homotopy invariance of the Hurewicz chain
(`Work.Stems.hurewiczChain_eq_of_homotopic`) and its naturality
(`Work.Stems.hurewiczChain_natural`).
-/

open scoped Topology unitInterval

namespace Work.ThomBordism

noncomputable section

/-! ## Two elementary transport lemmas -/

/-- Two maps out of `Sⁿ` which agree after composition with the collapse `Iⁿ → Sⁿ` are equal (the
collapse is a quotient map). -/
theorem tubeGen_csphere_ext_of_comp_collapse (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    {g₁ g₂ : C(Work.Stems.sphere n, X)}
    (h : g₁.comp (Work.Stems.collapseMap n hn) = g₂.comp (Work.Stems.collapseMap n hn)) :
    g₁ = g₂ := by
  ext y
  obtain ⟨q, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective y
  exact congrFun (congrArg DFunLike.coe h) q

/-- The Hurewicz chain of a cube loop depends only on the underlying cube map (the basepoint only
enters the *type* of the loop). -/
theorem tubeGen_hurewiczChain_congr_of_coe (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    {x x' : X} (p : GenLoop (Fin n) X x) (q : GenLoop (Fin n) X x')
    (h : (p : C(Fin n → unitInterval, X)) = (q : C(Fin n → unitInterval, X))) :
    Work.Stems.hurewiczChain n hn x p = Work.Stems.hurewiczChain n hn x' q := by
  have hcomp : (Work.Stems.cubeLift n hn p).comp (Work.Stems.collapseMap n hn)
      = (Work.Stems.cubeLift n hn q).comp (Work.Stems.collapseMap n hn) := by
    rw [Work.Stems.cubeLift_comp, Work.Stems.cubeLift_comp, h]
  have h2 := tubeGen_csphere_ext_of_comp_collapse n hn hcomp
  rw [Work.Stems.hurewiczChain, Work.Stems.hurewiczChain, h2]

/-! ## The two cube loops and the interpolating family -/

/-- The standard collapse of the cube onto `S^{8+k} = OnePoint (ℝ^{8+k})`, as a cube loop. -/
def tubeGenStdLoop (k : ℕ) :
    GenLoop (Fin (8 + k)) (OnePoint (Work.Tubular.Euc (8 + k))) OnePoint.infty :=
  ⟨⟨fun q => Work.Stems.cubeToOnePoint (8 + k) q,
      Work.Stems.cubeToOnePoint_continuous (8 + k)⟩,
    fun t ht => Work.Stems.cubeToOnePoint_eq_infty_of_mem_boundary ht⟩

/-- The standard collapse cube loop, pushed forward by a collapse map `g` with `g ∞ = ∞`. -/
def tubeGenPushLoop {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hginfty : g OnePoint.infty = OnePoint.infty) :
    GenLoop (Fin (8 + k)) (OnePoint (Work.Tubular.NormalTotal E)) OnePoint.infty :=
  ⟨g.comp (tubeGenStdLoop k :
      C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.Euc (8 + k)))),
    fun t ht => by
      rw [ContinuousMap.comp_apply,
        show (tubeGenStdLoop k :
            C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.Euc (8 + k)))) t
          = OnePoint.infty from (tubeGenStdLoop k).2 t ht,
        hginfty]⟩

@[simp] theorem tubeGenPushLoop_coe {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hginfty : g OnePoint.infty = OnePoint.infty) :
    (tubeGenPushLoop C g hginfty :
        C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.NormalTotal E)))
      = g.comp (tubeGenStdLoop k :
          C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.Euc (8 + k)))) := rfl

/-- At `s = 0` the interpolating family is the Pontryagin–Thom tube loop. -/
theorem tubeGen_thetaHomotopyFun_zero {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    ∀ t : Fin (8 + k) → unitInterval,
      TubeGen.thetaHomotopyFun C g R (0, t)
        = (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox :
            C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.NormalTotal E))) t := by
  intro t
  by_cases ht : t ∈ Cube.boundary (Fin (8 + k))
  · rw [TubeGen.thetaHomotopyFun_apply_of_mem C g R 0 t ht]
    exact (Work.Tubular.tubeCollapseCubeOnePoint_boundary C g hg hR hbox ht).symm
  · rw [TubeGen.thetaHomotopyFun_apply_of_notMem C g R 0 t ht]
    show g (OnePoint.some (TubeGen.theta R ((0 : unitInterval) : ℝ)
      (Work.Stems.cubeCoords (8 + k) t))) = _
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, TubeGen.theta_zero_cubeCoords R ht]
    rfl

/-- At `s = 1` the interpolating family is the pushed-forward standard collapse loop. -/
theorem tubeGen_thetaHomotopyFun_one {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hginfty : g OnePoint.infty = OnePoint.infty) {R : ℝ} :
    ∀ t : Fin (8 + k) → unitInterval,
      TubeGen.thetaHomotopyFun C g R (1, t)
        = (tubeGenPushLoop C g hginfty :
            C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.NormalTotal E))) t := by
  intro t
  by_cases ht : t ∈ Cube.boundary (Fin (8 + k))
  · rw [TubeGen.thetaHomotopyFun_apply_of_mem C g R 1 t ht]
    rw [tubeGenPushLoop_coe, ContinuousMap.comp_apply,
      show (tubeGenStdLoop k :
          C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.Euc (8 + k)))) t
        = OnePoint.infty from (tubeGenStdLoop k).2 t ht, hginfty]
  · rw [TubeGen.thetaHomotopyFun_apply_of_notMem C g R 1 t ht]
    rw [tubeGenPushLoop_coe, ContinuousMap.comp_apply]
    rw [show (tubeGenStdLoop k : C(Fin (8 + k) → unitInterval,
        OnePoint (Work.Tubular.Euc (8 + k)))) t = Work.Stems.cubeToOnePoint (8 + k) t from rfl]
    rw [Work.Stems.cubeToOnePoint_eq_coe_of_not_mem_boundary ht]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, TubeGen.theta_one]

/-- The interpolating family is constant on the boundary of the cube, at the tube loop's
basepoint. -/
theorem tubeGen_thetaHomotopyFun_boundary {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (s : unitInterval) :
    ∀ t ∈ Cube.boundary (Fin (8 + k)),
      TubeGen.thetaHomotopyFun C g R (s, t)
        = (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox :
            C(Fin (8 + k) → unitInterval, OnePoint (Work.Tubular.NormalTotal E))) t := by
  intro t ht
  rw [TubeGen.thetaHomotopyFun_apply_of_mem C g R s t ht]
  exact (Work.Tubular.tubeCollapseCubeOnePoint_boundary C g hg hR hbox ht).symm

/-! ## The main theorem -/

theorem tubeGenLoop_hurewiczChain_natural {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
      = (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          (TopCat.ofHom g)) (8 + k))
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (⟨⟨fun q => Work.Stems.cubeToOnePoint (8 + k) q,
              Work.Stems.cubeToOnePoint_continuous (8 + k)⟩,
            fun t ht => Work.Stems.cubeToOnePoint_eq_infty_of_mem_boundary ht⟩ :
              GenLoop (Fin (8 + k)) (OnePoint (Work.Tubular.Euc (8 + k))) OnePoint.infty)) := by
  classical
  -- `g` fixes the basepoint
  have hginfty : g OnePoint.infty = OnePoint.infty := tubeGen_gInfty C g hg
  -- a strict box margin for the tube
  obtain ⟨δ, hδpos, hboxδ⟩ := tubeGen_margin C hbox
  -- the "good set" is open and the interpolating coordinates stay outside the tube there
  have hYpos : 0 < TubeGen.thresh R δ :=
    lt_of_lt_of_le zero_lt_one (TubeGen.one_le_thresh R δ)
  have hopen : IsOpen {t : Fin (8 + k) → unitInterval |
      t ∈ Cube.boundary (Fin (8 + k))
        ∨ ∃ j : Fin (8 + k), TubeGen.thresh R δ
            < |Work.Stems.cubeCoords (8 + k) t j|} :=
    tubeGen_isOpen_goodSet (n := 8 + k) (by omega) hYpos
  have hest : ∀ (s : unitInterval) (t : Fin (8 + k) → unitInterval),
      (∃ j : Fin (8 + k), TubeGen.thresh R δ
        < |Work.Stems.cubeCoords (8 + k) t j|) →
      ∃ j : Fin (8 + k), R - δ
        ≤ |TubeGen.theta R (s : ℝ) (Work.Stems.cubeCoords (8 + k) t) j| := by
    intro s t ⟨j, hj⟩
    exact tubeGen_estimate (hR := hR) (hδ := hδpos) (hs0 := s.2.1) (hs1 := s.2.2)
      (y := Work.Stems.cubeCoords (8 + k) t) ⟨j, le_of_lt hj⟩
  -- continuity of the interpolating family
  have hcont : Continuous (TubeGen.thetaHomotopyFun C g R) :=
    tubeGen_continuous_thetaHomotopy C g hg hboxδ hopen hest
  -- the cube loops are homotopic rel the boundary of the cube
  have hhom : GenLoop.Homotopic (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
      (tubeGenPushLoop C g hginfty) := by
    refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
    · exact { toContinuousMap := ⟨TubeGen.thetaHomotopyFun C g R, hcont⟩
              map_zero_left := tubeGen_thetaHomotopyFun_zero C g hg hR hbox
              map_one_left := tubeGen_thetaHomotopyFun_one C g hginfty }
    · intro s
      exact tubeGen_thetaHomotopyFun_boundary C g hg hR hbox s
  -- homotopy invariance and naturality of the Hurewicz chain
  have h1 := Work.Stems.hurewiczChain_eq_of_homotopic (8 + k) (by omega) hhom
  have h2 : Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (tubeGenPushLoop C g hginfty)
      = (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (OnePoint (Work.Tubular.Euc (8 + k))))
          (TopCat.of (OnePoint (Work.Tubular.NormalTotal E)))
          (TopCat.ofHom g)) (8 + k))
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty (tubeGenStdLoop k)) := by
    rw [tubeGen_hurewiczChain_congr_of_coe (8 + k) (by omega) (tubeGenPushLoop C g hginfty)
      (Work.Stems.genLoopMap g (tubeGenStdLoop k)) (by rfl)]
    exact Work.Stems.hurewiczChain_natural (8 + k) (by omega) g (tubeGenStdLoop k)
  rw [h1, h2]
  rfl

end

end Work.ThomBordism
