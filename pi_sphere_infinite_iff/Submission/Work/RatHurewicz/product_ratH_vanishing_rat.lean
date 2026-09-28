import Mathlib
import Submission.Work.RatHurewicz.fibreRangeVanishing
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.Defs

set_option linter.style.haveILetI false

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

/-- Path-connectedness transports along a homeomorphism. -/
private theorem pathConnectedSpace_of_homeomorph {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (h : PathConnectedSpace B) : PathConnectedSpace A := by
  rw [pathConnectedSpace_iff_univ] at h ⊢
  have hh := h.image e.symm.continuous
  rwa [Set.image_univ, Set.range_eq_univ.mpr e.symm.surjective] at hh

/-- **The product step of the free part of `EMVan`** (Künneth, only in the vanishing range).

Let `k ≥ 2`, let `X` and `Y` be `(k-1)`-connected (`Work.Serre.Conn`, base points `x₀`, `y₀`), and
suppose that both have vanishing rational reduced homology in the range `k < j ≤ 2k-1`.  Then so
does the product `X × Y`.

This is the same statement as `Work.Stems.product_ratH_vanishing`, but **without** the
`Work.Serre.SerreExactRangeCorrected` hypothesis: that hypothesis is only used there to obtain the
*integral* stable-range Serre exact sequence, whereas the proof below needs only the *rational*
pair comparison in the stable range, which is available (proved, axiom-clean) as
`Work.Serre.ratSerrePairComparison` / `Work.RatHurewicz.ratPairComparison_proof`.

Route: the projection `Prod.fst : X × Y → X` is a Hurewicz fibration with fibre `{x₀} × Y ≅ Y`;
`b = f = k` (both `X` and the fibre are `(k-1)`-connected), so the rational pair comparison gives
`H_i(X × Y, {x₀} × Y; ℚ) ≅ H_i(X, {x₀}; ℚ)` for every `i < 2k`; the long exact sequence of the pair
`(X × Y, {x₀} × Y)` (the rational pair sequence `Work.StemsB.relChainsR_exact₁/₂/₃`) reads
`H̃_j(Y) → H̃_j(X × Y) → H̃_j(X, {x₀})` with the two outer terms zero for `k < j ≤ 2k-1`, forcing
`H̃_j(X × Y;ℚ) = 0` — note that only the vanishing of `H̃_j`, not of `H̃_{j-1}`, is used. -/
theorem product_ratH_vanishing_rat (k : ℕ) (hk : 2 ≤ k) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (hXc : Work.Serre.Conn X x₀ k) (hYc : Work.Serre.Conn Y y₀ k)
    (hX : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) j))
    (hY : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) j)) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (X × Y)) j) := by
  intro j hj1 hj2
  have hjpos : 1 ≤ j := by omega
  have h2k : j < k + k := by omega
  -- path connectedness of the two factors (connectivity, `π₀` included) and of the product
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (hXc 0 (by omega))
  haveI hpcY : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀ (hYc 0 (by omega))
  haveI hpcXY : PathConnectedSpace (X × Y) := inferInstance
  -- the strict fibre of the projection `X × Y → X` over `x₀` is homeomorphic to `Y`
  have hpcFib : PathConnectedSpace
      (Work.StemsB.fibre (ContinuousMap.fst : C(X × Y, X)) x₀) :=
    pathConnectedSpace_of_homeomorph (Work.Stems.fibreHomeo X Y x₀) hpcY
  -- the rational homology of `Y` vanishes below `k`, by `(k-1)`-connectivity
  have hYlow : ∀ n : ℕ, 0 < n → n < k → IsZero (Work.Serre.ratH (TopCat.of Y) n) :=
    fun n hn hnk =>
      Work.Serre.serreE0Range Y y₀ (k - 1) (fun i hi => hYc i (by omega)) n hn (by omega)
  have hfiblow : ∀ n : ℕ, 0 < n → n < k → IsZero (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre (ContinuousMap.fst : C(X × Y, X)) x₀)) n) :=
    fun n hn hnk =>
      Work.Stems.isZero_ratH_of_homeomorph (Work.Stems.fibreHomeo X Y x₀) n (hYlow n hn hnk)
  -- the rational pair comparison in the stable range, with `b = f = k`
  have hpair := (Work.Serre.ratSerrePairComparison
      (ContinuousMap.fst : C(X × Y, X))
      (Work.StemsB.IsHurewiczFibration.isSerreFibration (Work.Stems.isHurewiczFibration_fst X Y))
      x₀ k k hk (by omega) hpcXY hpcX hXc hpcFib hfiblow).1 j h2k
  -- the relative homology of `(X, {x₀})` vanishes in degree `j` over `ℚ`
  have hXrel : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({x₀} : Set X)).homology j) :=
    Work.Stems.isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of X) ({x₀} : Set X) j hjpos
      (hX j hj1 hj2) (Work.Stems.isZero_ratH_singleton X x₀ (j := j - 1) (by omega))
  -- the relative homology of `(X × Y, {x₀} × Y)` vanishes in degree `j` over `ℚ`
  have hrelProd : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (X × Y))
      (Prod.fst ⁻¹' ({x₀} : Set X))).homology j) := by
    obtain ⟨e⟩ := hpair
    exact IsZero.of_iso hXrel e
  -- the absolute homology of the fibre `{x₀} × Y ≅ Y` vanishes in degree `j`
  have hfibH : IsZero ((Work.Cohomology.singularChains ℚ
      (TopCat.of ↥(Prod.fst ⁻¹' ({x₀} : Set X)))).homology j) :=
    Work.Stems.isZero_ratH_of_homeomorph (Work.Stems.fibreHomeo X Y x₀) j (hY j hj1 hj2)
  -- the long exact sequence of the pair `(X × Y, {x₀} × Y)` finishes the job
  have hS := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of (X × Y))
    (Prod.fst ⁻¹' ({x₀} : Set X)) j
  exact hS.isZero_X₂ (hfibH.eq_zero_of_src _) (hrelProd.eq_zero_of_tgt _)

end Work.RatHurewicz
