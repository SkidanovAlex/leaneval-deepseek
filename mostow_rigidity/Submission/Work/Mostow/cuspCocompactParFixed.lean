import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.cuspShimizuHoroball
import Submission.Work.Mostow.flatTranslationCusp
import Submission.Work.Mostow.flatEmbCocompact
import Submission.Work.Mostow.cuspCocompactAllLevels

/-!
# The cusp stabiliser of a lattice acts cocompactly on the horospheres

This file proves `Work.Mostow.cuspCocompactParFixed`, the statement of
`Work.Mostow.geomFiniteCuspCocompact`, without using the latter.

The proof goes through the classical ingredients:

* `Work.Mostow.flatTranslationCusp` : the cusp stabiliser `Γ_ξ` of a lattice contains a parabolic
  element `δ` which preserves the horospheres at `ξ` and acts on the flat coordinate `yc ξ` by a
  nonzero translation `y ↦ y + v`;
* `Work.Mostow.cuspShimizuHoroball_of_flatTrans` (Shimizu's lemma): with such a `δ`, the level
  sets of `lev ξ` are separation controlled: there is `s > 0` such that no `γ ∈ Γ` with
  `bd γ ξ ≠ ξ` maps a point of level `< s` at `ξ` to a point of level `< s`;
* `disjoint_horoball_of_lev_sep` (below) turns that level statement into the precise invariance of
  the horoball of level `log s`;
* `Work.Mostow.cuspHoro.flatCocompactEmb` converts the embedded horoball and the finite covolume
  of `Γ` (via `packingCount` and the Euclidean Dirichlet-cell argument) into cocompactness of
  `Γ_ξ` on the level-one horosphere;
* `Work.Mostow.cuspCocompactAllLevels` transports cocompactness from one level to every level.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- **Shimizu's lemma in horoball form.**  If `s > 0` and no `γ ∈ Γ` with `bd γ ξ ≠ ξ` maps a
point of level `< s` at `ξ` to a point of level `< s`, then the horoball at `ξ` of level
`Real.log s` is disjoint from its `γ`-translate, i.e. the horoball at `bd γ ξ` of level
`Real.log s + bCocy γ ξ`. -/
lemma disjoint_horoball_of_lev_sep (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ξ : E n) (hξ : ξ ∈ Sph n) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      ∀ u : E n, lev ξ u < s → s ≤ lev ξ ((γ : PO n 1) • u)) :
    ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ (Real.log s))
        (horoball (bd (γ : PO n 1) ξ) (Real.log s + bCocy (γ : PO n 1) ξ)) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  intro γ hγ
  rw [Set.disjoint_left]
  intro u hu1 hu2
  simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
  have hη : bd (γ : PO n 1) ξ ∈ Sph n := hA'.bd_mem _ _ hξ
  -- the level of `u` at `ξ` is `< s`
  have hlevu : lev ξ u < s := by
    rw [lev_eq_exp hξ u, ← Real.exp_log hs]
    exact Real.exp_lt_exp.mpr hu1
  -- the cocycle identity for `γ⁻¹` at `bd γ ξ`
  have hbdinv : bd ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = ξ := by
    have h := hA'.bd_mul ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξ
    rw [inv_mul_cancel, hA'.bd_one ξ hξ] at h
    exact h.symm
  have hcoc : bCocy ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = - bCocy (γ : PO n 1) ξ := by
    have h := bCocy_mul hA hI ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξ
    rw [inv_mul_cancel, bCocy_one hA hI ξ hξ] at h
    linarith
  have hbus := hI'.busemann_cocycle ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) u hη
  rw [hbdinv] at hbus
  have hbc : busemann ξ (((γ : PO n 1)⁻¹) • (0 : E n))
      = bCocy ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) := by
    rw [bCocy, hbdinv]
  rw [hbc, hcoc] at hbus
  -- hence `γ⁻¹ • u` has level `< s`
  have hlevinv : lev ξ (((γ : PO n 1)⁻¹) • u) < s := by
    rw [lev_eq_exp hξ (((γ : PO n 1)⁻¹) • u), ← Real.exp_log hs]
    refine Real.exp_lt_exp.mpr ?_
    linarith
  -- and the separation hypothesis applies
  have hround : (γ : PO n 1) • (((γ : PO n 1)⁻¹) • u) = u := by
    rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]
  have hkey : s ≤ lev ξ ((γ : PO n 1) • (((γ : PO n 1)⁻¹) • u)) :=
    hsep γ hγ (((γ : PO n 1)⁻¹) • u) hlevinv
  rw [hround] at hkey
  linarith

/-- **The cusp stabiliser of a lattice acts cocompactly on the horospheres.**  For a lattice
`Γ`, a parabolic fixed point `ξ ∈ parFixed Γ` and the vanishing of the Busemann cocycle on the
stabilisers of *all* parabolic fixed points (`hvan`), the horospheres at `ξ` have compact
`Γ_ξ`-fundamental sets. -/
theorem cuspCocompactParFixed (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) η = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    Work.Mostow.CuspCocompact Γ ξ := by
  have hξS : ξ ∈ Sph n := hξ.1
  have hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  -- the flat translation in the cusp stabiliser
  obtain ⟨δ, v, hv, hvξ, hδbd, hyc, hlev⟩ :=
    Work.Mostow.flatTranslationCusp n hn hA hI hBb Γ hΓ hvan ξ hξ
  have hδpar : IsParabolic (δ : PO n 1) :=
    Work.Mostow.flatTrans_isParabolic hξS hA hI (δ : PO n 1) v hv hyc hlev
  -- Shimizu's lemma: the levels at `ξ` are separated
  obtain ⟨s, hs, hsep⟩ := Work.Mostow.cuspShimizuHoroball_of_flatTrans n hn hA hI Γ hΓ hvan ξ hξ
    ⟨δ, v, hv, hvξ, hδbd, hyc, hlev⟩
  -- hence the horoball at `ξ` of level `log s` is precisely invariant
  have hemb := disjoint_horoball_of_lev_sep hA hI Γ ξ hξS hs hsep
  -- and the stabiliser is cocompact on the level-one horosphere
  obtain ⟨K, hKc, hK⟩ :=
    Work.Mostow.cuspHoro.flatCocompactEmb n hn hA hI Γ hΓ ξ hξ hvan (Real.log s) hemb
  -- cocompactness at one level gives it at every level
  refine cuspCocompactAllLevels n hA hI Γ ξ hξS hstab 0 ⟨K, hKc, ?_⟩
  intro u hu
  have hlev1 : lev ξ u = 1 := by
    rw [lev_eq_exp hξS u, hu, Real.exp_zero]
  obtain ⟨γ, hγ, hγK⟩ := hK u hlev1
  exact ⟨γ, hγ, hγK⟩

end

end Work.Mostow
