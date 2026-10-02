/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# The elementary properties of the immediate basin `immBasin` (design `gaps2` §2.1, Q1)

`Work.FatouParabolic.Core.immBasin F z₀ p₀` is the connected component of the *interior* of the
basin `interior (basin F z₀)` through a point `p₀` of an attracting petal of a Leau--Fatou flower.
This file proves the *basic* properties Q1 of the design of
`Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §2.1 needed by all the later steps (the covering
statement Q2, the lifting Q4, the Liouville contradiction Q6):

* it is **open** (it is a connected component of the open set `interior (basin F z₀)`) and
  **preconnected**, and **bounded** under the escape condition `BasinEscape F`;
* it **contains the whole petal** `fl.Pa` (the petal is open, preconnected, meets `p₀`, and is
  contained in the basin, hence in its interior);
* it is **`F`-invariant**: the image of the open `immBasin` under `F` is open (the open mapping
  theorem, `F` being holomorphic and non-constant by the escape condition) and is contained in the
  basin; being preconnected and containing `F p₀`, it lies in the same component;
* it is **relatively closed in the interior of the basin**: if `x` lies in `interior (basin F z₀)`
  and in the closure of `immBasin`, then the component of `x` is an open neighbourhood of `x`, hence
  meets `immBasin`, and two components of the same set which meet are equal.

The counterpart for the (larger, non-open) punctured basin is
`Work.FatouParabolic.Core.immBasinPunct_basics`; the difference is the `F`-invariance argument,
which for a component of the *open* set `interior (basin)` needs the openness of `F` rather than
just its continuity.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.isBounded_puncturedBasin_of_escape
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_basinEscape
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Set Filter

namespace Work.FatouParabolic.Core

/-- **The basin is `F`-invariant.**  If the forward orbit of `z` converges to `z₀`, then so does
the forward orbit of `F z`: it is the tail of the former. -/
theorem Basin.mapsTo_basin {f : ℂ → ℂ} {z₀ z : ℂ}
    (hz : z ∈ Work.FatouParabolic.basin f z₀) :
    f z ∈ Work.FatouParabolic.basin f z₀ := by
  rw [Work.FatouParabolic.mem_basin] at hz ⊢
  rw [show (fun n : ℕ => f^[n] (f z)) = (fun n : ℕ => f^[n + 1] z) from
    funext fun n => (Function.iterate_succ_apply f n z).symm]
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => f^[n] z) 1).mpr hz

/-! ## Q1: the basic properties of the immediate basin -/

theorem immBasin_basics_interior {F g : ℂ → ℂ} {z₀ : ℂ} (hF : Differentiable ℂ F) (hfix : F z₀ = z₀)
    (hesc : Work.FatouParabolic.BasinEscape F)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {p₀ : ℂ} (hp₀ : p₀ ∈ fl.Pa) :
    IsOpen (Work.FatouParabolic.Core.immBasin F z₀ p₀) ∧
    IsPreconnected (Work.FatouParabolic.Core.immBasin F z₀ p₀) ∧
    fl.Pa ⊆ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧
    Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) ∧
    Bornology.IsBounded (Work.FatouParabolic.Core.immBasin F z₀ p₀) ∧
    (∀ x ∈ interior (Work.FatouParabolic.basin F z₀),
      x ∈ closure (Work.FatouParabolic.Core.immBasin F z₀ p₀) →
      x ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀) := by
  -- the ambient set `S = interior (basin F z₀)` is open
  have hSopen : IsOpen (interior (Work.FatouParabolic.basin F z₀)) := isOpen_interior
  -- the petal lies in the basin (its orbits converge to `z₀`), hence in its interior (`Pa` open)
  have hPa_basin : fl.Pa ⊆ Work.FatouParabolic.basin F z₀ :=
    fun z hz => fl.tendsto_Pa z hz
  have hPsub : fl.Pa ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    (fl.isOpen_Pa.subset_interior_iff).mpr hPa_basin
  -- hence the petal lies in the component of its point `p₀`
  have hPimm : fl.Pa ⊆ immBasin F z₀ p₀ :=
    fl.isPreconnected_Pa.subset_connectedComponentIn hp₀ hPsub
  have hp₀S : p₀ ∈ interior (Work.FatouParabolic.basin F z₀) := hPsub hp₀
  have hp₀mem : p₀ ∈ immBasin F z₀ p₀ := mem_connectedComponentIn hp₀S
  have hΩopen : IsOpen (immBasin F z₀ p₀) := hSopen.connectedComponentIn
  have hΩ_sub_S : immBasin F z₀ p₀ ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    connectedComponentIn_subset _ _
  have hΩ_sub_basin : immBasin F z₀ p₀ ⊆ Work.FatouParabolic.basin F z₀ :=
    hΩ_sub_S.trans interior_subset
  -- `F p₀` also lies in the component, being again a point of the petal
  have hFp₀mem : F p₀ ∈ immBasin F z₀ p₀ := hPimm (fl.mapsTo_Pa hp₀)
  -- `F` is non-constant: the escape (doubling) condition forbids it
  have hFnonconst : ¬ ∃ w : ℂ, ∀ z : ℂ, F z = w := by
    rintro ⟨w, hw⟩
    obtain ⟨R, hRpos, hR⟩ := hesc
    set r : ℝ := max R (‖w‖ + 1) with hr
    have hrR : R ≤ r := le_max_left _ _
    have hrz : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact le_trans (le_of_lt hRpos) hrR
    have hstep : 2 * r ≤ ‖w‖ := by
      have h1 := hR (r : ℂ) (by rw [hrz]; exact hrR)
      rw [hrz, hw (r : ℂ)] at h1
      exact h1
    have h4 : ‖w‖ + 1 ≤ r := le_max_right _ _
    nlinarith [hstep, h4]
  -- hence `F` is an open map (open mapping theorem for non-constant holomorphic maps)
  have hAnalytic : AnalyticOnNhd ℂ F univ := (hF.differentiableOn).analyticOnNhd isOpen_univ
  have hIsOpenMap : IsOpenMap F := (hAnalytic.is_constant_or_isOpenMap).resolve_left hFnonconst
  -- `F '' Ω` is open and contained in the basin, hence in the interior, so it lies in `Ω`
  have hOpenFΩ : IsOpen (F '' immBasin F z₀ p₀) := hIsOpenMap _ hΩopen
  have hFΩ_basin : F '' immBasin F z₀ p₀ ⊆ Work.FatouParabolic.basin F z₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact Basin.mapsTo_basin (hΩ_sub_basin hz)
  have hFΩ_interior : F '' immBasin F z₀ p₀ ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    hOpenFΩ.subset_interior_iff.mpr hFΩ_basin
  have hFmapsTo : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀) := by
    have hpre : IsPreconnected (F '' immBasin F z₀ p₀) :=
      isPreconnected_connectedComponentIn.image F hF.continuous.continuousOn
    have himg : F '' immBasin F z₀ p₀ ⊆
        connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) (F p₀) :=
      hpre.subset_connectedComponentIn ⟨p₀, hp₀mem, rfl⟩ hFΩ_interior
    rw [← connectedComponentIn_eq hFp₀mem] at himg
    intro z hz
    exact himg ⟨z, hz, rfl⟩
  refine ⟨hΩopen, isPreconnected_connectedComponentIn, hPimm, hFmapsTo, ?_, ?_⟩
  · -- bounded: a subset of the basin, which is contained in the disc of radius `R`
    obtain ⟨R, hRpos, hR⟩ := hesc
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (norm_lt_of_mem_basin_of_escape hRpos hR (hΩ_sub_basin hz))
  · -- relatively closed in `interior (basin F z₀)`
    intro x hx hxcl
    have hCx_open : IsOpen (connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x) :=
      hSopen.connectedComponentIn
    have hCx_mem : x ∈ connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x :=
      mem_connectedComponentIn hx
    -- the open component of `x` meets the component of `p₀`
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hxcl _ hCx_open hCx_mem
    have h1 : connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x
        = connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) y :=
      connectedComponentIn_eq hy1
    have h2 : connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) p₀
        = connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) y :=
      connectedComponentIn_eq hy2
    have hEq : connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x
        = connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) p₀ := h1.trans h2.symm
    simpa only [Work.FatouParabolic.Core.immBasin] using hEq ▸ hCx_mem

end Work.FatouParabolic.Core
