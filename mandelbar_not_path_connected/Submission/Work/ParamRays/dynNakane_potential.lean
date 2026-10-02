import Mathlib
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.ParamRays.isClosed_filledJulia
import Submission.Work.ParamRays.exists_norm_dynPhi_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

open Filter
open scoped Real Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-- The potential of the dynamical Böttcher coordinate is continuous on `ℂ` and tends to `+∞`
at infinity.  Together with `dynPhi_eq_zero_of_mem` and the homeomorphism field of
`DynBottcherHomeo` this is exactly the content of `Work.Top.NakaneData (filledJulia c) (dynPhi c)`
(the interface requested by the lead for the `EL` bridge).

Route:
* `potential (filledJulia c) (dynPhi c) z` equals `0` on `filledJulia c` and `log ‖dynPhiOf c z‖`
  outside it (`dynPhi_of_not_mem`).
* Off the filled Julia set, continuity follows from `ContinuousOn` in `IsDynBottcher` and
  `dynPhiOf ≠ 0` there.
* An a priori bound is needed at the boundary: from the functional equation,
  `‖dynPhiOf c z‖ ^ (2 ^ n) = ‖dynPhiOf c (orbit c z (2 ^ n))‖`, and the cocompact asymptotic
  bounds the right hand side in terms of `‖orbit c z (2 ^ n)‖`; taking `2 ^ n`-th roots gives a
  uniform bound on `dynPhiOf` over bounded sets.
* At `∂(filledJulia c)`: if `zₙ ∉ filledJulia c`, `zₙ → z ∈ filledJulia c` and
  `‖dynPhiOf c zₙ‖ ≥ 1 + δ` along a subsequence, the a priori bound gives a convergent subsequence
  of `dynPhiOf c zₙ`, and then `zₙ = e⁻¹ (dynPhiOf c zₙ)` converges to a point of the complement of
  `filledJulia c`, contradicting `zₙ → z`.
* At infinity: the asymptotic clause gives `‖dynPhiOf c z‖ ≥ ‖z‖ / 2` for large `‖z‖`. -/
theorem dynNakane_potential {c : ℂ} (h : Work.ParamRays.DynBottcherHomeo c) :
    Continuous (Work.Top.potential (Work.ParamRays.filledJulia c) (Work.ParamRays.dynPhi c)) ∧
    (∀ t : ℝ, ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      t ≤ Work.Top.potential (Work.ParamRays.filledJulia c) (Work.ParamRays.dynPhi c) z) := by
  obtain ⟨e, he⟩ := h.homeo
  have hExists : DynBottcherExists c := h.exists
  have hisB : IsDynBottcher c (dynPhiOf c) := isDynBottcher_dynPhiOf hExists
  -- off the filled Julia set the dynamical Böttcher coordinate has modulus `> 1`
  have hgt : ∀ z : ℂ, z ∉ filledJulia c → 1 < ‖dynPhi c z‖ := by
    intro z hz
    rw [he ⟨z, hz⟩]
    exact (e ⟨z, hz⟩).2
  -- the potential is `log ‖dynPhi c ·‖` on the whole plane (`Real.log 0 = 0`)
  have hfun : Work.Top.potential (filledJulia c) (dynPhi c) =
      fun z : ℂ => Real.log ‖dynPhi c z‖ := by
    funext z
    rcases Classical.em (z ∈ filledJulia c) with hz | hz
    · rw [Work.Top.potential_of_mem hz, dynPhi_eq_zero_of_mem hz, norm_zero, Real.log_zero]
    · rw [Work.Top.potential_of_not_mem hz]
  rw [hfun]
  constructor
  · -- continuity
    have hcontOn : ContinuousOn (fun z : ℂ => Real.log ‖dynPhi c z‖) (filledJulia c)ᶜ := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hEqOn : (filledJulia c)ᶜ.domRestrict (fun z : ℂ => Real.log ‖dynPhi c z‖) =
          (fun w : ↥Work.Top.exteriorDisc => Real.log ‖(w : ℂ)‖) ∘ e := by
        funext z
        simp only [Set.domRestrict, Function.comp_apply]
        rw [he z]
      rw [hEqOn]
      refine Continuous.log ?_ ?_
      · exact continuous_subtype_val.norm.comp e.continuous
      · intro w
        exact ne_of_gt (lt_trans zero_lt_one (e w).2)
    -- the potential tends to `0` at every point of the filled Julia set
    have hcontAt : ∀ z ∈ filledJulia c, ContinuousAt (fun z : ℂ => Real.log ‖dynPhi c z‖) z := by
      intro z₀ hz₀
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hε' : 0 < Real.exp ε - 1 := by
        have := Real.one_lt_exp_iff.mpr hε
        linarith
      obtain ⟨δ, hδpos, hδ⟩ := exists_norm_dynPhi_lt h hz₀ hε'
      refine ⟨δ, hδpos, fun z hz => ?_⟩
      have hz00 : Real.log ‖dynPhi c z₀‖ = 0 := by
        rw [dynPhi_eq_zero_of_mem hz₀, norm_zero, Real.log_zero]
      rw [hz00]
      rcases Classical.em (z ∈ filledJulia c) with hzm | hzm
      · rw [dynPhi_eq_zero_of_mem hzm, norm_zero, Real.log_zero, dist_self]
        exact hε
      · have hlt : ‖dynPhi c z‖ < Real.exp ε := by
          have h5 := hδ z hz hzm
          linarith
        have hpos : 0 < ‖dynPhi c z‖ := lt_trans zero_lt_one (hgt z hzm)
        have hlog : Real.log ‖dynPhi c z‖ < ε := by
          rw [← Real.log_exp ε]
          exact Real.log_lt_log hpos hlt
        have hnonneg : 0 ≤ Real.log ‖dynPhi c z‖ :=
          Real.log_nonneg (le_of_lt (hgt z hzm))
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
        exact hlog
    -- paste the exterior part and the boundary values
    have h3 : ContinuousOn (fun z : ℂ => Real.log ‖dynPhi c z‖)
        ((filledJulia c)ᶜ ∪ filledJulia c) :=
      ContinuousOn.union_continuousAt (isClosed_filledJulia c).isOpen_compl hcontOn hcontAt
    rwa [Set.compl_union_self, continuousOn_univ] at h3
  · -- the potential tends to `+∞` at infinity
    intro t
    obtain ⟨K', hK'c, hK'sub⟩ :=
      Filter.mem_cocompact.mp (hisB.2.2 (1 / 2) (by norm_num) :
        {z : ℂ | ‖dynPhiOf c z - z‖ ≤ (1 / 2) * ‖z‖} ∈ Filter.cocompact ℂ)
    obtain ⟨r, hr⟩ := hK'c.isBounded.subset_closedBall 0
    refine ⟨max (max (max 2 ‖c‖) r) (2 * Real.exp t) + 1, fun z hz => ?_⟩
    have hMa : max 2 ‖c‖ ≤ max (max (max 2 ‖c‖) r) (2 * Real.exp t) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hMb : r ≤ max (max (max 2 ‖c‖) r) (2 * Real.exp t) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hMc : 2 * Real.exp t ≤ max (max (max 2 ‖c‖) r) (2 * Real.exp t) :=
      le_max_right _ _
    -- `z` is far outside the filled Julia set
    have hznc : z ∉ filledJulia c := by
      intro hmem
      have h1 : ‖z‖ ≤ max 2 ‖c‖ := norm_le_max_of_bounded c z hmem
      linarith
    -- the asymptotic clause applies
    have hzK : z ∉ K' := by
      intro hzK
      have h1 : z ∈ Metric.closedBall (0 : ℂ) r := hr hzK
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      linarith
    have hasymz : ‖dynPhiOf c z - z‖ ≤ (1 / 2) * ‖z‖ := hK'sub hzK
    have hnorm : ‖z‖ / 2 ≤ ‖dynPhiOf c z‖ := by
      have h2 : ‖z‖ ≤ ‖dynPhiOf c z‖ + ‖dynPhiOf c z - z‖ := by
        have hring : dynPhiOf c z - (dynPhiOf c z - z) = z := by ring
        calc ‖z‖ = ‖dynPhiOf c z - (dynPhiOf c z - z)‖ := by rw [hring]
          _ ≤ ‖dynPhiOf c z‖ + ‖dynPhiOf c z - z‖ := norm_sub_le _ _
      linarith
    have hexp : Real.exp t ≤ ‖z‖ / 2 := by linarith
    change t ≤ Real.log ‖dynPhi c z‖
    rw [dynPhi_of_not_mem hznc]
    have h2 : Real.log (Real.exp t) ≤ Real.log ‖dynPhiOf c z‖ :=
      Real.log_le_log (Real.exp_pos t) (le_trans hexp hnorm)
    rwa [Real.log_exp t] at h2

end Work.ParamRays
