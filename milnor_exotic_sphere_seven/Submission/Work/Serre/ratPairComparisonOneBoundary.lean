import Mathlib
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.B1Rel.Model
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.ratPullbackComparison
import Submission.Work.Serre.ratSerrePairAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre


/-! ## The square of the three pair maps -/

/-- **The commutative square of the three rational pair maps**: the pair map of `p` is, under the
base change along the model map `g`, the composite of the pair map of the pullback and the pair map
of the model. -/
theorem pullbackSquareRatOne {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Serre.pullbackPairMapRat g p γ₀ b₀ hbase ≫ Work.Serre.relPairMapRat p b₀
      = Work.Serre.stagePairMapRat g p γ₀ ≫ Work.Serre.pairMapOfRat g γ₀ b₀ hbase := by
  have hsecond : Set.MapsTo (Work.StemsB.pullbackSnd g p)
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B)) := by
    intro x hx
    have hx' : (Work.StemsB.pullbackFst g p) x = γ₀ := hx
    show p x.1.2 = b₀
    calc p x.1.2 = g ((Work.StemsB.pullbackFst g p) x) := x.2.symm
      _ = g γ₀ := by rw [hx']
      _ = b₀ := hbase
  have hfirst : Set.MapsTo (Work.StemsB.pullbackFst g p)
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({γ₀} : Set Γ) :=
    fun _ hx => hx
  have hbase' : Set.MapsTo g ({γ₀} : Set Γ) ({b₀} : Set B) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx, hbase]
  exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp_congr
    (Work.StemsB.pullbackSnd g p) p hsecond (fun _ hx => hx)
    (Work.StemsB.pullbackFst g p) g hfirst hbase'
    (Work.Serre.pullbackSnd_comp_eq g p)

/-- **The `b = 1` case of the rational Serre pair comparison.**

For a Serre fibration `p : E → B` over a *path connected* base whose fibres are path connected and
rationally acyclic in degrees `0 < j < f` (`1 ≤ f`), the map of pairs `(E, p⁻¹{b₀}) → (B, {b₀})`
is surjective on rational homology in degree `1 + f`:

  `H_{1+f}(E, p⁻¹{b₀}; ℚ) ↠ H_{1+f}(B, {b₀}; ℚ)`.

This is the `b = 1` (base NOT assumed simply connected) case of the rational Serre pair comparison;
the case `b ≥ 2` (`Work.Serre.ratSerrePairComparison`) is proved, and the integral `b = 1` case is
proved as `Work.Serre.ZeroCase.b1Comparison` in model form. The integral statement cannot be
transported to `ℚ` (ℚ-acyclicity of the fibre does not imply ℤ-acyclicity), so this has to be
proved over ℚ — by mirroring the integral `b = 1` chapter (`Submission/Work/Serre/SPC/*`,
`ZeroCase/*`) with `ℚ` coefficients, or (likely cheaper) via the edge map of the relative Serre
spectral sequence `E²_{p,q} = H_p(B,{b₀};H_q F) ⇒ H_{p+q}(E,p⁻¹b₀)`: the differentials out of
`(f+1, 0)` land in `(f+1-r, r-1)`, zero for `0 < r-1 < f` (fibre acyclicity `hfib`) and
`E^{f+1}_{0,f} = 0` for `r-1 ≥ f` (relative `H_0` of a non-empty pair vanishes), so the edge map
`E²_{f+1,0} → E^∞_{f+1,0}` is onto; that is the conclusion. Build it from the available ℚ-Serre
machinery (`Work.StemsB.SerreExact`, `Work.Serre.serreK2*`, the `SPC`/`ratSerrePairComparison`
assembly); do NOT `declare_false` it because the workspace lacks a spectral sequence.

Mathematical content: the fibre fundamental class `[Z_{b₀}] ∈ H_{1+f}(E, p⁻¹b₀; ℚ)` of the cone on
the fibre over `b₀` is non-zero, i.e. the fibre restriction
`H^{f}(cyl p, range (cylIncl p)) → H^{f}(P_{b₀}, A_{b₀})` is injective — the
transgression/orientation input of the twisted Thom isomorphism, hence the input of
`Work.Serre._opcr.relCoh_cyl_line_of_sphericalFibre` (`r = f-1`) and of the "cellwise non-vanishing"
of the cellular Thom comparison.

No `hE : PathConnectedSpace E` hypothesis: `E` is path connected because `B` and the fibre over
`b₀` are. -/
theorem ratPairComparisonOneBoundary {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (f : ℕ) (hf : 1 ≤ f)
    (hB : PathConnectedSpace B)
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relPairMapRat p b₀) (1 + f)).hom := by
  haveI := hB
  -- the sharp fibre data at every point of the base
  have h0b₀ : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0
      ≅ ModuleCat.of ℚ ℚ) :=
    Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre p b₀)
  have hfib_all : ∀ y : B, ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j) :=
    (Work.Serre.B1Rel.fibreDataBelow_all p hp b₀ f hfib h0b₀).1
  have h0_all : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ) :=
    (Work.Serre.B1Rel.fibreDataBelow_all p hp b₀ f hfib h0b₀).2
  -- the model stage, with `π`-bijectivity up to `f + 2`
  set s := Work.Serre.E3aModel.towerB B b₀ (Work.Serre.E3aModel.baseState B b₀) (f + 3) with hs
  have hgbij : ∀ i : ℕ, i ≤ f + 2 → ∀ x : s.Y,
      Function.Bijective (Work.Serre.piMapN s.g i x) :=
    Work.Serre.E3aModel.towerB_piMapN_bijective B b₀ (Work.Serre.E3aModel.baseState B b₀) (f + 2)
  -- the invariant at the stage, in the boundary degree `1 + f`
  have hmodel : Work.Serre.B1Rel.RelGoodQ p (1 + f) s.y₀ s.g :=
    Work.Serre.B1Rel.relGoodQ_tower p hp b₀ (1 + f) f (by omega) hfib_all h0_all
      (Work.Serre.E3aModel.baseState B b₀)
      (Work.Serre.B1Rel.relGoodQ_base p hp b₀ (1 + f) f (by omega) hfib_all h0_all) (f + 3)
  -- the two end comparisons are isomorphisms in the boundary degree
  haveI hpb : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) (1 + f)) :=
    Work.Serre.ratPullbackComparison s.g p s.y₀ b₀ s.gbase hp (f + 2)
      (fun k hk x => hgbij k hk x) (1 + f) (by omega)
  haveI hpm : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pairMapOfRat s.g s.y₀ b₀ s.gbase) (1 + f)) :=
    Work.Serre.isIso_pairMapOfRat b₀ s hgbij (1 + f) (by omega)
  -- the middle comparison is an epimorphism in the boundary degree
  have hst : CategoryTheory.Epi
      (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat s.g p s.y₀) (1 + f)) :=
    hmodel.2
  -- the square of the three pair maps
  have hsq := congrArg (fun m => HomologicalComplex.homologyMap m (1 + f))
    (pullbackSquareRatOne s.g p s.y₀ b₀ s.gbase)
  simp only [HomologicalComplex.homologyMap_comp] at hsq
  haveI hcomp : CategoryTheory.Epi (HomologicalComplex.homologyMap
      (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) (1 + f)
      ≫ HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) (1 + f)) := by
    rw [hsq]
    exact CategoryTheory.epi_comp _ _
  haveI : CategoryTheory.Epi
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) (1 + f)) := by
    have hb : HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) (1 + f)
        = CategoryTheory.inv (HomologicalComplex.homologyMap
            (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) (1 + f))
          ≫ (HomologicalComplex.homologyMap
              (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) (1 + f)
            ≫ HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) (1 + f)) :=
      (IsIso.inv_hom_id_assoc _ _).symm
    rw [hb]
    exact CategoryTheory.epi_comp _ _
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end Work.Serre
