import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspCocompactDefs
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.ellipticGapOfLattice
import Submission.Work.Mostow.frontierShortBoundCusp
import Submission.Work.Mostow.frontierCocompactOfLattice

/-!
# Cocompactness of the cusp stabiliser of a lattice on the horosphere

`Work.Mostow.cuspStabCocompactOfLattice`: for a lattice `Γ ≤ PO(n,1)` (`n ≥ 3`), a parabolic
fixed point `ξ ∈ parFixed Γ` and `hvan` (every element of `Γ` fixing a parabolic fixed point
preserves the horospheres there), the stabiliser `Γ_ξ` acts cocompactly on the level-one
horosphere `lev ξ · = 1`.

## The argument

The Margulis region `cuspThinRegion Γ ξ ε` is the sublevel set
`{u | lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε}`, so over every flat point `y ∈ ξ^⊥` there is a
*frontier point* `frontierPt Γ ξ ε y`, of level `cEps ε / parDisp Γ ξ y`, sitting exactly on the
boundary of the region.  The pieces proved elsewhere are

* `Work.Mostow.ellipticGapOfLattice`: the nontrivial elliptic elements of `Γ_ξ` have their flat
  linear parts bounded away from `1` by a constant `θ > 0` (the elliptic gap);
* `Work.Mostow.frontierShortBoundCusp`: consequently only `N` group elements are `ε/2`-short at a
  frontier point (Margulis + the elliptic gap + the packing of `θ`-separated rotations);
* `Work.Mostow.frontierCocompactOfLattice`: consequently (`MultThickProp` plus the disjointness of
  the Margulis regions of distinct cusps) every frontier point is `Γ_ξ`-equivalent into a fixed
  compact set.

The assembly here converts the last statement into cocompactness of `Γ_ξ` on the level-one
horosphere: `Γ_ξ` preserves the levels, and the flat coordinate of a level-preserving element is
independent of the level, so the compact set of flat coordinates of the frontier images serves
for every level.
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The flat coordinate `yc ξ ·` is continuous. -/
lemma continuous_yc_cusp (ξ : E n) (hξ : ξ ∈ Sph n) :
    Continuous (fun u : E n => yc ξ u) := by
  have htpart : Continuous (fun u : E n => tpart u) := by
    simp only [tpart]; fun_prop
  have hlevc : Continuous (fun u : E n => lev ξ u) := by
    simp only [lev]
    exact htpart.sub (by fun_prop)
  have hwc : Continuous (fun u : E n => wc ξ u) := by
    simp only [wc]; fun_prop
  have hyc : (fun u : E n => yc ξ u) = fun u => (lev ξ u)⁻¹ • wc ξ u := rfl
  rw [hyc]
  exact (hlevc.inv₀ (fun u => ne_of_gt (lev_pos ξ hξ u))).smul hwc

/-- `hptOf ξ · D` is continuous. -/
lemma continuous_hptOf_cusp (ξ : E n) (D : ℝ) :
    Continuous (fun y : E n => hptOf ξ y D) := by
  simp only [hptOf]
  fun_prop

/-- **Assembly step.**  Given the frontier data — the frontier points of the Margulis region at
`ξ` are `Γ_ξ`-equivalent into a fixed compact set — the stabiliser `Γ_ξ` acts cocompactly on the
level-one horosphere of `ξ`. -/
theorem cuspStabCocompact_of_frontier
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hΓ : Submission.Mostow.HypLattice Γ)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hvan : ∀ (γ : Γ), Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hK₀ : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧
      ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
        ∃ σ : Γ, Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
          (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε y ∈ K) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K := by
  classical
  have hξS : ξ ∈ Sph n := hξ.1
  obtain ⟨K₀, hK₀c, hK₀⟩ := hK₀
  -- level preservation for the stabiliser
  have hlevσ : ∀ (σ : Γ), Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∀ v : Submission.Mostow.E n,
        Work.Mostow.lev ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • v) = Work.Mostow.lev ξ v := by
    intro σ hσ v
    have hb : busemann ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : E n)) = 0 := by
      have h := hvan σ hσ
      rw [Work.Mostow.bCocy, hσ] at h
      exact h
    have h := (HypIsoData.ofProp hI).busemann_cocycle
      (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ v hξS
    rw [hσ, hb, add_zero] at h
    rw [Work.Mostow.lev_eq_exp hξS ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • v),
      Work.Mostow.lev_eq_exp hξS v, h]
  refine ⟨(fun y : Submission.Mostow.E n => Work.Mostow.hptOf ξ y 1) '' (yc ξ '' K₀), ?_, ?_⟩
  · exact ((hK₀c.image (continuous_yc_cusp ξ hξS)).image (continuous_hptOf_cusp ξ 1))
  · intro u hu
    have hy : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξS u
    obtain ⟨σ, hσbd, hσK⟩ := hK₀ (yc ξ u) hy
    refine ⟨σ, hσbd, ?_⟩
    have hpar : 0 < Work.Mostow.parDisp Γ ξ (yc ξ u) :=
      Work.Mostow.parDisp_pos_of_discrete n hA hI Γ hΓ.1 hξS (fun γ hγ => hvan γ hγ) hξ.2 hy
    have hcEps : 0 < Work.Mostow.cEps ε := by
      rw [Work.Mostow.cEps]
      refine Real.sqrt_pos.mpr ?_
      have := Real.one_lt_cosh.mpr (ne_of_gt hε)
      linarith
    have hL : 0 < Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ (yc ξ u) := div_pos hcEps hpar
    have hu' : u = Work.Mostow.hptOf ξ (yc ξ u) 1 := by
      have h := hptOf_yc_lev hξS u
      rw [hu] at h
      exact h.symm
    have hkey : yc ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
        = yc ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) •
            Work.Mostow.frontierPt Γ ξ ε (yc ξ u)) := by
      have h1 := congrArg (fun w : Submission.Mostow.E n =>
        yc ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • w)) hu'
      rw [h1]
      exact yc_smul_hptOf_levelIndep hA hI ξ hξS
        (σ : LeanEval.Geometry.MostowRigidity.PO n 1) hσbd (hlevσ σ hσbd)
        (yc ξ u) hy 1 (Work.Mostow.cEps ε / Work.Mostow.parDisp Γ ξ (yc ξ u))
        one_pos hL
    have hlev1 : Work.Mostow.lev ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) = 1 := by
      rw [hlevσ σ hσbd u, hu]
    refine ⟨yc ξ ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • u),
      ⟨(σ : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.frontierPt Γ ξ ε (yc ξ u),
        hσK, hkey.symm⟩, ?_⟩
    rw [← hlev1]
    exact hptOf_yc_lev hξS ((σ : LeanEval.Geometry.MostowRigidity.PO n 1) • u)

/-- **The cusp stabiliser of a lattice acts cocompactly on the horosphere.**

For a lattice `Γ ≤ PO(n,1)` with `n ≥ 3`, a parabolic fixed point `ξ ∈ parFixed Γ` and `hvan`
(every element of `Γ` fixing a parabolic fixed point preserves the horospheres there), the
stabiliser `Γ_ξ` acts cocompactly on the level-one horosphere `{u | lev ξ u = 1}` at `ξ`. -/
theorem cuspStabCocompactOfLattice (n : ℕ) (hn : 3 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K := by
  -- the elliptic gap for the cusp stabiliser
  obtain ⟨θ, hθ, hgap⟩ := Work.Mostow.ellipticGapOfLattice n hn hA hI Γ hΓ ξ hξ
  -- the short-set bound at the frontier points of the Margulis region
  obtain ⟨ε, hε, N, hshort⟩ :=
    Work.Mostow.frontierShortBoundCusp n hn hA hI Γ hΓ hvan ξ hξ θ hθ hgap
  -- the frontier is `Γ_ξ`-cocompact
  obtain ⟨K₀, hK₀c, hK₀⟩ :=
    Work.Mostow.frontierCocompactOfLattice n hn hA hI Γ hΓ hvan ξ hξ ε hε N hshort
  exact Work.Mostow.cuspStabCocompact_of_frontier hA hI Γ hΓ ξ hξ
    (fun γ hγ => hvan γ ξ hξ hγ) ε hε ⟨K₀, hK₀c, hK₀⟩

end

end Work.Mostow
