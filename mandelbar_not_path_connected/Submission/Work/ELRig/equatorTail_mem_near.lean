import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.RayLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology
open Work.EL

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **R-a3.**  Under the contradiction hypothesis `E ⊆ K c` the equator tail `Ψ x`, `x < -R'`,
lies on the *near* side (the band side, away from the attracting petal) of the `α`-pair `P`.

The proof is the exhaustion argument of the two-sides lemma for the two `1`-periodic lift curves
`γ₁, γ₂` of the lift data `L : RayLift`:

* the images of the two regions `U`, `L` (which reach `|Im| > R₀`) are `Pa`, hence lie on the far
  side `pairSide P`; a preconnected set avoiding the pair curve and containing a point of the far
  side lies entirely in it (`PairSides.subset_of_preconnected`);
* a point of the near side near `z₁` exists (`z₁` is on the frontier of `pairSideNear P`), and by
  the flower's `cover` it is the `Ψ`-image of a point of the left half plane; that point avoids the
  two lifts (its image is off the pair curve, and the `Ψ`-preimages of the pair curve are the
  lifts — `RayLift.preimage_subset`), hence lies in `U ∪ M ∪ L`, and since `U`, `L` map into the far
  side it lies in `M`;
* so `Ψ '' M` is a preconnected set avoiding the pair curve which meets the near side, hence lies
  in `pairSideNear P`; and the real axis below `-R` lies in `M`. -/
theorem equatorTail_mem_near {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hP : P.y = d.z₁) (hPa1 : P.a = Work.EL.alpha1)
    (hPb1 : P.b = Work.EL.alpha2) (hside : Work.EL.PairSides d.hN P)
    (L : RayLift d fl)
    (hPa_far : fl.Pa ⊆ Work.EL.pairSide P) (hPa_ne : fl.Pa.Nonempty)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear P := by
  have lift : Work.EL.LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R L.R₀ := L.liftSidesOf hE
  -- the two sides of the pair are disjoint
  have hdisj : ∀ z, z ∈ Work.EL.pairSide P → z ∈ Work.EL.pairSideNear P → False := by
    intro z h1 h2
    have hm : z ∈ Work.EL.pairSide P ∩ Work.EL.pairSideNear P := ⟨h1, h2⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp hside.disjoint] at hm
    exact hm
  -- a point of the left half plane off the two lift curves has `Ψ`-image off the pair curve
  have hunter : ∀ w : ℂ, w.re < -L.R → w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      fl.Ψ w ∉ Work.EL.pairCurve P := by
    intro w hwR hwγ hmem
    exact hwγ (L.preimage_subset hPa1 hPb1 hP w hwR hmem)
  -- a preconnected set of the left half plane off the lifts whose `Ψ`-image reaches `|Im| > R₀`
  -- maps into the far side
  have far_of : ∀ T : Set ℂ, IsPreconnected T → T ⊆ {w : ℂ | w.re < -L.R} →
      T ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) = ∅ → (∃ w ∈ T, L.R₀ < |w.im|) →
      fl.Ψ '' T ⊆ Work.EL.pairSide P := by
    intro T hTconn hTsub hToff hex
    have hTγ : ∀ w ∈ T, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
      intro w hw hmem
      have hmem' : w ∈ T ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) := ⟨hw, hmem⟩
      rw [hToff] at hmem'
      exact hmem'
    have himg : IsPreconnected (fl.Ψ '' T) :=
      hTconn.image fl.Ψ (fl.Ψ_diff.continuous.continuousOn)
    have havoid : fl.Ψ '' T ⊆ (Work.EL.pairCurve P)ᶜ := by
      rintro z ⟨w, hwT, rfl⟩
      exact hunter w (hTsub hwT) (hTγ w hwT)
    rcases hside.subset_of_preconnected himg havoid with h | h
    · exact h
    · obtain ⟨w₀, hw₀T, hw₀abs⟩ := hex
      have hw₀R : w₀.re < -L.R := hTsub hw₀T
      have hw₀re : w₀.re < -L.R₀ := by linarith [lift.hRR₀]
      have hpa : fl.Ψ w₀ ∈ fl.Pa := L.pa_ends w₀ hw₀re hw₀abs
      exact (hdisj _ (hPa_far hpa) (h ⟨w₀, hw₀T, rfl⟩)).elim
  -- `U` and `L` map into the far side
  have hUabs : ∃ w ∈ lift.U, L.R₀ < |w.im| := by
    obtain ⟨w, hwU, hwim⟩ := lift.top_mem_U
    exact ⟨w, hwU, lt_of_lt_of_le hwim (le_abs_self _)⟩
  have hUfar : fl.Ψ '' lift.U ⊆ Work.EL.pairSide P :=
    far_of lift.U lift.U_conn lift.U_sub lift.U_off hUabs
  have hLabs : ∃ w ∈ lift.L, L.R₀ < |w.im| := by
    obtain ⟨w, hwL, hwim⟩ := lift.bottom_mem_L
    exact ⟨w, hwL, lt_of_lt_of_le (by linarith) (neg_le_abs w.im)⟩
  have hLfar : fl.Ψ '' lift.L ⊆ Work.EL.pairSide P :=
    far_of lift.L lift.L_conn lift.L_sub lift.L_off hLabs
  -- a point of the near side near `z₁` is the image of a point of the middle region `M`
  have hM_avoid : ∀ w ∈ lift.M, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro w hw hmem
    have hmem' : w ∈ lift.M ∩ (Set.range L.γ₁ ∪ Set.range L.γ₂) := ⟨hw, hmem⟩
    rw [lift.M_off] at hmem'
    exact hmem'
  have hz1_curve : d.z₁ ∈ Work.EL.pairCurve P :=
    (Work.EL.mem_pairCurve_iff P d.z₁).mpr (Or.inr (Or.inl hP.symm))
  have hz1_cl : d.z₁ ∈ closure (Work.EL.pairSideNear P) := by
    have hfr : d.z₁ ∈ frontier (Work.EL.pairSideNear P) := by
      rw [hside.frontier_near]
      exact hz1_curve
    exact frontier_subset_closure hfr
  obtain ⟨r, hrpos, hcover⟩ := fl.cover L.R
  obtain ⟨q, hq_near, hq_dist⟩ := Metric.mem_closure_iff.mp hz1_cl r hrpos
  have hq_dist' : ‖q - d.z₁‖ < r := by
    simpa [dist_eq_norm, norm_sub_rev] using hq_dist
  have hq_ne : q ≠ d.z₁ := by
    intro hq
    rw [hq] at hq_near
    exact (hside.notMem_curve_of_mem_near hq_near) hz1_curve
  have hq_pos : 0 < ‖q - d.z₁‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hq_ne
  have hq_img : q ∈ fl.Ψ '' lift.M := by
    rcases hcover q hq_pos hq_dist' with hqPa | ⟨w, hwR, hwq⟩
    · exact (hdisj q (hPa_far hqPa) hq_near).elim
    · have hw_cover : w ∈ lift.U ∨ w ∈ lift.M ∨ w ∈ lift.L ∨
          w ∈ Set.range L.γ₁ ∨ w ∈ Set.range L.γ₂ := by
        have h := lift.cover hwR
        simpa only [Set.mem_union, or_assoc] using h
      rcases hw_cover with hwU | hwM | hwL | hwγ1 | hwγ2
      · exact (hdisj q (by rw [← hwq]; exact hUfar ⟨w, hwU, rfl⟩) hq_near).elim
      · exact ⟨w, hwM, hwq⟩
      · exact (hdisj q (by rw [← hwq]; exact hLfar ⟨w, hwL, rfl⟩) hq_near).elim
      · obtain ⟨s, rfl⟩ := hwγ1
        have hcur : q ∈ Work.EL.pairCurve P := by
          rw [← hwq, Work.EL.mem_pairCurve_iff]
          exact Or.inl (hPa1.symm ▸ L.img₁ s)
        exact ((hside.notMem_curve_of_mem_near hq_near) hcur).elim
      · obtain ⟨s, rfl⟩ := hwγ2
        have hcur : q ∈ Work.EL.pairCurve P := by
          rw [← hwq, Work.EL.mem_pairCurve_iff]
          exact Or.inr (Or.inr (hPb1.symm ▸ L.img₂ s))
        exact ((hside.notMem_curve_of_mem_near hq_near) hcur).elim
  -- hence the whole `Ψ`-image of `M` lies in the near side
  have himgM : IsPreconnected (fl.Ψ '' lift.M) :=
    lift.M_conn.image fl.Ψ (fl.Ψ_diff.continuous.continuousOn)
  have havoidM : fl.Ψ '' lift.M ⊆ (Work.EL.pairCurve P)ᶜ := by
    rintro z ⟨w, hwM, rfl⟩
    exact hunter w (lift.M_sub hwM) (hM_avoid w hwM)
  have hMnear : fl.Ψ '' lift.M ⊆ Work.EL.pairSideNear P := by
    rcases hside.subset_of_preconnected himgM havoidM with h | h
    · exact (hdisj q (h hq_img) hq_near).elim
    · exact h
  refine ⟨L.R, fun x hx => hMnear ⟨(x : ℂ), lift.real_mem_M x hx, rfl⟩⟩

end Work.ELRig
