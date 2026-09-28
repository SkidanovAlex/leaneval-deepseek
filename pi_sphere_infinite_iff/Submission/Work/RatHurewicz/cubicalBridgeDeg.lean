import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.SimLemmas
import Submission.Work.RatHurewicz.Bridge.SimChainMap
import Submission.Work.RatHurewicz.Bridge.SigmaChain
import Submission.Work.RatHurewicz.Bridge.chainBoundary
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.RatHurewicz.Bridge.HomologyAux

/-!
# The simplicial/cubical bridge (degree `n`)

`Work.RatHurewicz.cubicalBridgeDeg` is the chain-level bridge used by the elementary cubical
proof of the Hurewicz isomorphism theorem: if the Hurewicz image of a based `n`-cube `p` vanishes,
then (up to sign) the cube `p.1` is a boundary in the *normalized* cubical chain complex, i.e. it
is the boundary of an `(n+1)`-chain modulo the degenerate cubes `Work.RatHurewicz.Deg`.

The proof compares the singular chain complex with the cubical one along the cumulative-coordinate
map `H n : Iⁿ → Δⁿ` (the map `Work.RatHurewicz.Bridge.Sim`), applied to the cycle

`γ = simpChain n s - simpChain n (const y)`

carried by the collapse simplex `s : Δⁿ → Sⁿ` (which is constant on the simplicial boundary, so
`γ` is indeed a cycle).  The Hurewicz image of `p` is the push-forward of `γ` under the collapse
`f = cubeLift p`, so its vanishing makes `γ` a boundary; transporting the bounding chain through
`Sim` and using the chain-map property of `Sim` produces the cubical `(n+1)`-chain `c`.
-/

namespace Work.RatHurewicz

open Work.Stems.Cubical
open Bridge
open scoped Topology Topology.Homotopy unitInterval Simplicial
open CategoryTheory AlgebraicTopology

noncomputable section

/-- The constant cube is degenerate in positive dimensions. -/
theorem deg_const_cube {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (y : Y) :
    Finsupp.single (cconst n y) (1 : ℤ) ∈ Deg n Y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact Bridge.Deg_const (m := m) y

theorem cubicalBridgeDeg (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X)
    (p : GenLoop (Fin n) X x₀)
    (hp : Work.Stems.hurewiczMapN n hn x₀
        (show HomotopyGroup (Fin n) X x₀ from Quotient.mk _ p) = 0) :
    ∃ c : Work.Stems.Cubical.Cub (n + 1) X,
      (Work.Stems.Cubical.cubD n X c - Finsupp.single p.1 (1 : ℤ) ∈ Work.RatHurewicz.Deg n X) ∨
      (Work.Stems.Cubical.cubD n X c + Finsupp.single p.1 (1 : ℤ) ∈ Work.RatHurewicz.Deg n X) := by
  -- the collapse simplex `Δⁿ → Sⁿ`
  obtain ⟨s, y, hsH, hsy⟩ := Bridge.exists_collapse_simplex n hn
  -- the descent of the based cube to the sphere
  let f : C(Work.Stems.sphere n, X) := Work.Stems.cubeLift n hn p
  -- the induced chain map
  let φ := Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere n)) (TopCat.of X)
    (TopCat.ofHom f)
  -- the sphere chain complex
  let KS : ChainComplex (ModuleCat ℤ) ℕ :=
    Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))
  -- the simplicial cycle on the sphere
  let γ : KS.X n :=
    simpChain n s - simpChain n (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y)
  have hγ : KS.d n (n - 1) γ = 0 := by
    change KS.d n (n - 1)
      (simpChain n s - simpChain n (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y)) = 0
    exact Bridge.sigmaChain_cycle n s y hsy
  let zγ : KS.cycles n := Bridge.cycleOf KS n hn γ hγ
  have hzγ : (ModuleCat.Hom.hom (KS.iCycles n)) zγ = γ :=
    Bridge.iCycles_cycleOf KS n hn γ hγ
  let zw : (Work.Cohomology.singularChains ℤ (TopCat.of X)).cycles n :=
    HomologicalComplex.cyclesMap φ n zγ
  have hzw' : (ModuleCat.Hom.hom
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).iCycles n)) zw
      = (ModuleCat.Hom.hom (φ.f n)) γ := by
    change (ModuleCat.Hom.hom
        ((Work.Cohomology.singularChains ℤ (TopCat.of X)).iCycles n))
        (HomologicalComplex.cyclesMap φ n zγ) = (ModuleCat.Hom.hom (φ.f n)) γ
    rw [Bridge.iCycles_cyclesMap, hzγ]
  -- the Hurewicz image of `p` vanishes, so `homologyMap φ n` is zero
  have hl : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n))
      (Work.Stems.sphereGenerator n hn) = 0 := by
    simpa only [Work.Stems.hurewiczMapN_mk, Work.Stems.hurewiczChain, Work.Stems.hurewiczClass,
      KS, φ, f] using hp
  have hHom : ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n) = 0 :=
    Bridge.homologyMap_eq_zero_of_sphereGenerator_eq_zero' n hn _ hl
  have hzw : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homologyπ n zw = 0 := by
    change (Work.Cohomology.singularChains ℤ (TopCat.of X)).homologyπ n
        (HomologicalComplex.cyclesMap φ n zγ) = 0
    rw [← Bridge.homologyMap_homologyπ φ n zγ]
    rw [hHom]
    rfl
  obtain ⟨b, hb⟩ := Bridge.chain_homologypi_eq_zero
    (Work.Cohomology.singularChains ℤ (TopCat.of X)) n zw hzw
  -- the bounding chain, pushed to the cube
  have hwb : (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (n + 1) n b
      = (φ.f n).hom γ := by
    change (ModuleCat.Hom.hom
        ((Work.Cohomology.singularChains ℤ (TopCat.of X)).d (n + 1) n)) b
      = (ModuleCat.Hom.hom (φ.f n)) γ
    rw [hb]
    exact hzw'
  -- `Sim` of the collapse cycle
  have hSimγ : Sim n (TopCat.of (Work.Stems.sphere n)) γ
      = (-1 : ℤ) ^ n • Finsupp.single (Work.Stems.collapseMap n hn) (1 : ℤ)
        - (-1 : ℤ) ^ n • Finsupp.single (cconst n y) (1 : ℤ) := by
    have hconst : (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y).comp (H n)
        = cconst n y := by
      ext z; rfl
    change Sim n (TopCat.of (Work.Stems.sphere n))
        (simpChain n s - simpChain n (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y)) = _
    rw [map_sub, Bridge.Sim_simpChain, Bridge.Sim_simpChain, hsH, hconst]
  -- `Sim` of the pushed cycle, in the target
  have hcconst : f.comp (cconst n y) = cconst n (f y) := by ext z; rfl
  have hSimX : Sim n (TopCat.of X) ((φ.f n).hom γ)
      = (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ)
        - (-1 : ℤ) ^ n • Finsupp.single (cconst n (f y)) (1 : ℤ) := by
    change Sim n (TopCat.of X)
        ((Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere n)) (TopCat.of X)
          (TopCat.ofHom f)).f n γ) = _
    rw [Bridge.sim_naturality, hSimγ, map_sub, map_smul, map_smul, Bridge.cubMap_single,
      Bridge.cubMap_single, one_smul, one_smul, hcconst]
    rw [show (ContinuousMap.comp f (Work.Stems.collapseMap n hn))
        = (Work.Stems.cubeLift n hn p).comp (Work.Stems.collapseMap n hn) from rfl,
      Work.Stems.cubeLift_comp]
  have hSimXmem : Sim n (TopCat.of X) ((φ.f n).hom γ)
      - (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ) ∈ Deg n X := by
    rw [hSimX]
    have h2 : (-1 : ℤ) ^ n • Finsupp.single (cconst n (f y)) (1 : ℤ) ∈ Deg n X :=
      Submodule.smul_mem _ _ (deg_const_cube hn (f y))
    rw [show ((-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ)
            - (-1 : ℤ) ^ n • Finsupp.single (cconst n (f y)) (1 : ℤ))
          - (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ)
        = - ((-1 : ℤ) ^ n • Finsupp.single (cconst n (f y)) (1 : ℤ)) by abel]
    exact Submodule.neg_mem _ h2
  -- the cubical chain-map property applied to the bounding chain
  have hcub : cubD n X (Sim (n + 1) (TopCat.of X) b)
      - Sim n (TopCat.of X) ((φ.f n).hom γ) ∈ Deg n X := by
    have h := Bridge.sim_chainMap n (TopCat.of X) b
    rw [hwb] at h
    exact h
  -- combine
  have hA : cubD n X (Sim (n + 1) (TopCat.of X) b)
      - (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ) ∈ Deg n X := by
    have hsum : (cubD n X (Sim (n + 1) (TopCat.of X) b)
          - (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ))
        = (cubD n X (Sim (n + 1) (TopCat.of X) b) - Sim n (TopCat.of X) ((φ.f n).hom γ))
          + (Sim n (TopCat.of X) ((φ.f n).hom γ)
              - (-1 : ℤ) ^ n • Finsupp.single p.1 (1 : ℤ)) := by abel
    rw [hsum]
    exact Submodule.add_mem _ hcub hSimXmem
  refine ⟨Sim (n + 1) (TopCat.of X) b, ?_⟩
  rcases Nat.even_or_odd n with hev | hodd
  · left
    have h : (-1 : ℤ) ^ n = 1 := hev.neg_one_pow
    simpa [h] using hA
  · right
    have h : (-1 : ℤ) ^ n = -1 := hodd.neg_one_pow
    simpa [h] using hA

end

end Work.RatHurewicz
