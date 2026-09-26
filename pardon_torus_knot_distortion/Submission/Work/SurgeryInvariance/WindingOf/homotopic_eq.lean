import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.InnermostDisk.homotopic_iff_homotopicClosed

/-!
# The winding vector is a homotopy invariant of closed curves on a parametrised torus

`Work.SurgeryInvariance.windingOf P γ` is the winding vector of a closed curve `γ` on the
surface `F = P.carrier` of a parametrised torus `P`, computed from any lift
(`Work.SurgeryInvariance.windingOf_eq`).

This file proves that it is an invariant of the free homotopy class:
`Work.SurgeryInvariance.WindingOf.homotopic_eq`: if `α` and `β` are homotopic through closed
curves of `F`, then `windingOf P α = windingOf P β`.

The mathematical content is the same as in `Work.TorusCover.hasWinding_eq_of_homotopicClosed`,
but stated for an arbitrary `ParamTorus` rather than a `TorusParam` (which additionally carries
a uniform lower bound for the derivative of the parametrisation, irrelevant here).  The proof
lifts the homotopy through the covering map `psiMapToRange P.psi` of
`Work.TorusCover.isCoveringMap_psiMapToRange_param`; the displacement of the lifted homotopy
over one period takes values in the discrete period lattice `2πℤ²` and is therefore constant in
the homotopy parameter, since the parameter interval is connected.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.SurgeryInvariance.WindingOf

noncomputable section

open Work.TorusCover

/-- A lift `L` of a closed curve `γ` of `P` in the `Work.CoreTopology` sense yields a periodic
lift, in the `Work.TorusCover` sense, with winding vector `L.winding`: the parameter functions
`(Θ, Φ)` of `L` define the lift `Λ t = (L.Θ t, L.Φ t)` of `γ`, and by
`LiftOf.period_shift_winding` it advances by `periodShift L.winding` over one period. -/
theorem hasWinding_of_liftOf {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    HasWinding P.psi γ.γ L.winding := by
  refine ⟨fun t => (L.Θ t, L.Φ t), ⟨⟨L.contΘ.prodMk L.contΦ, ?_⟩, ?_⟩⟩
  · intro t; exact L.lifts t
  · intro t
    obtain ⟨h1, h2⟩ := L.period_shift_winding t
    refine Prod.ext ?_ ?_ <;> simp only [periodShift]
    · simpa using h1
    · simpa using h2

/-- The winding vector of `γ`, as defined by `windingOf`, is a winding vector in the
`Work.TorusCover` sense. -/
theorem hasWinding_windingOf (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) :
    HasWinding P.psi γ.γ (Work.SurgeryInvariance.windingOf P γ) :=
  hasWinding_of_liftOf (Classical.choice (ParamTorus_exists_liftOf P γ))

/-- **The winding vector is unique.**  Two periodic lifts of the same closed curve advance by
the same period shift: their difference is a continuous map into the discrete period lattice
`2πℤ²`, hence constant, so the displacement over one period is the same.

(The `Work.TorusCover` version of this fact, `hasWinding_unique`, asks for a `TorusParam`; here
only the injectivity modulo `2π` of the parametrisation is used, so it applies to any
`ParamTorus`.) -/
theorem hasWinding_unique_param (P : Work.CoreTopology.ParamTorus) {γ : ℝ → R3} {v w : ℤ × ℤ}
    (hv : HasWinding P.psi γ v) (hw : HasWinding P.psi γ w) : v = w := by
  obtain ⟨Λ, hΛ⟩ := hv
  obtain ⟨Λ', hΛ'⟩ := hw
  have hmem : ∀ t, (Λ t - Λ' t) ∈ lattice := fun t =>
    (psiMap_eq_iff_param P).mp (by
      show psiMap P.psi (Λ t) = psiMap P.psi (Λ' t)
      rw [psiMap_apply, psiMap_apply, hΛ.map_eq t, hΛ'.map_eq t])
  have hcont : Continuous (fun t : ℝ => Λ t - Λ' t) := hΛ.continuous.sub hΛ'.continuous
  have hconst := isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice
    hcont.continuousOn (fun t _ => hmem t) (mem_univ (0 : ℝ)) (mem_univ (2 * Real.pi))
  change Λ 0 - Λ' 0 = Λ (2 * Real.pi) - Λ' (2 * Real.pi) at hconst
  rw [hΛ.displacement, hΛ'.displacement] at hconst
  have hdis : periodShift v - periodShift w = 0 := by
    have hab : (Λ 0 + periodShift v) - (Λ' 0 + periodShift w)
        = (Λ 0 - Λ' 0) + (periodShift v - periodShift w) := by abel
    rw [hab] at hconst
    have h2 : (Λ 0 - Λ' 0) + (periodShift v - periodShift w) = (Λ 0 - Λ' 0) + 0 := by
      rw [add_zero]; exact hconst.symm
    exact add_left_cancel h2
  exact periodShift_injective (sub_eq_zero.mp hdis)

/-- **Homotopic closed curves have the same winding vector**, for an arbitrary parametrised
torus.  This is the `ParamTorus` version of
`Work.TorusCover.hasWinding_eq_of_homotopicClosed`. -/
theorem hasWinding_eq_of_homotopicClosed_param (P : Work.CoreTopology.ParamTorus)
    {γ₀ γ₁ : ℝ → R3} {v w : ℤ × ℤ}
    (h : HomotopicClosed P.psi γ₀ γ₁)
    (hv : HasWinding P.psi γ₀ v) (hw : HasWinding P.psi γ₁ w) : v = w := by
  obtain ⟨H, hHcont, hH0, hH1, hHper, hHrange⟩ := h
  obtain ⟨Λ₀, hΛ₀⟩ := hv
  have hcov : IsCoveringMap (psiMapToRange P.psi) := isCoveringMap_psiMapToRange_param P
  -- The homotopy, viewed as a map into the range of the parametrisation.
  let Hbar : C(ℝ × ℝ, Set.range (psiMap P.psi)) :=
    ⟨fun st => ⟨H st, hHrange st.1 st.2⟩, hHcont.subtype_mk (fun st => hHrange st.1 st.2)⟩
  have hHbar_coe : ∀ st : ℝ × ℝ, ((Hbar st : Set.range (psiMap P.psi)) : R3) = H st :=
    fun st => rfl
  -- The homotopy restricted to `[0,1] × ℝ`, with values in the range of the parametrisation.
  let G : C(unitInterval × ℝ, Set.range (psiMap P.psi)) :=
    Hbar.comp (ContinuousMap.prodMap ⟨Subtype.val, continuous_subtype_val⟩ (ContinuousMap.id ℝ))
  have hG_coe : ∀ (s : unitInterval) (t : ℝ),
      ((G (s, t) : Set.range (psiMap P.psi)) : R3) = H ((s : ℝ), t) := by
    intro s t
    rw [show (G (s, t) : Set.range (psiMap P.psi)) = Hbar ((s : ℝ), t) from rfl]
    exact hHbar_coe ((s : ℝ), t)
  -- The given periodic lift `Λ₀`, as a continuous map.
  let Λ₀c : C(ℝ, ℝ × ℝ) := ⟨Λ₀, hΛ₀.continuous⟩
  have h0 : ∀ t : ℝ, G (0, t) = psiMapToRange P.psi (Λ₀c t) := by
    intro t
    have hL : ((G (0, t) : Set.range (psiMap P.psi)) : R3) = γ₀ t := by
      rw [hG_coe]
      simpa using hH0 t
    have hR : ((psiMapToRange P.psi (Λ₀c t) : Set.range (psiMap P.psi)) : R3) = γ₀ t := by
      rw [psiMapToRange_coe]
      exact hΛ₀.map_eq t
    exact Subtype.ext (hL.trans hR.symm)
  -- The lift of the whole homotopy.
  let F : C(unitInterval × ℝ, ℝ × ℝ) := hcov.liftHomotopy G Λ₀c h0
  have hF_lifts : ∀ (s : unitInterval) (t : ℝ), psiMapToRange P.psi (F (s, t)) = G (s, t) :=
    fun s t => congr_fun (hcov.liftHomotopy_lifts G Λ₀c h0) (s, t)
  have hF_zero : ∀ t : ℝ, F (0, t) = Λ₀ t := fun t => hcov.liftHomotopy_zero G Λ₀c h0 t
  -- `F` lies over `H`.
  have hF_psi : ∀ (s : unitInterval) (t : ℝ), psiMap P.psi (F (s, t)) = H ((s : ℝ), t) := by
    intro s t
    have h1 := congrArg (fun x : Set.range (psiMap P.psi) => (x : R3)) (hF_lifts s t)
    rw [hG_coe s t] at h1
    simpa [psiMapToRange_coe] using h1
  -- The displacement of `F` over one period lies in the period lattice.
  have hd_mem : ∀ s : unitInterval, (F (s, 2 * Real.pi) - F (s, 0)) ∈ lattice := by
    intro s
    rw [← psiMap_eq_iff_param P, hF_psi s (2 * Real.pi), hF_psi s 0]
    simpa using hHper (s : ℝ) 0
  have hd_cont : Continuous fun s : unitInterval => F (s, 2 * Real.pi) - F (s, 0) :=
    ((F.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (F.continuous.comp (continuous_id.prodMk continuous_const)))
  -- ... hence is constant in `s`, since the lattice is discrete and `[0,1]` is connected.
  have hd_const : ∀ s : unitInterval,
      F (s, 2 * Real.pi) - F (s, 0) = F (0, 2 * Real.pi) - F (0, 0) := by
    intro s
    exact (isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice hd_cont.continuousOn
      (fun s _ => hd_mem s) (mem_univ (0 : unitInterval)) (mem_univ s)).symm
  have hd_one : F (1, 2 * Real.pi) - F (1, 0) = periodShift v := by
    rw [hd_const 1, hF_zero, hF_zero, hΛ₀.displacement, add_sub_cancel_left]
  -- The lift of `γ₁` obtained from `F`, together with its period displacement.
  let Λ₁ : ℝ → ℝ × ℝ := fun t => F (1, t)
  have hΛ₁cont : Continuous Λ₁ :=
    F.continuous.comp (continuous_const.prodMk continuous_id)
  have hΛ₁psi : ∀ t, P.psi (Λ₁ t).1 (Λ₁ t).2 = γ₁ t := by
    intro t
    have h1 := hF_psi 1 t
    have h2 : psiMap P.psi (Λ₁ t) = γ₁ t := by
      rw [show Λ₁ t = F (1, t) from rfl, h1]
      simpa using hH1 t
    simpa [psiMap_apply] using h2
  have hℓ_mem : ∀ t : ℝ, (F (1, t + 2 * Real.pi) - F (1, t)) ∈ lattice := by
    intro t
    rw [← psiMap_eq_iff_param P, hF_psi 1 (t + 2 * Real.pi), hF_psi 1 t]
    simpa using hHper 1 t
  have hℓ_cont : Continuous fun t : ℝ => F (1, t + 2 * Real.pi) - F (1, t) :=
    ((F.continuous.comp (continuous_const.prodMk (continuous_id.add continuous_const))).sub
      (F.continuous.comp (continuous_const.prodMk continuous_id)))
  have hℓ_const : ∀ t : ℝ, F (1, t + 2 * Real.pi) - F (1, t) = periodShift v := by
    intro t
    have hc : F (1, 2 * Real.pi) - F (1, 0) = F (1, t + 2 * Real.pi) - F (1, t) := by
      simpa using isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice hℓ_cont.continuousOn
        (fun t _ => hℓ_mem t) (mem_univ (0 : ℝ)) (mem_univ t)
    rw [← hc]
    exact hd_one
  refine hasWinding_unique_param P ?_ hw
  refine ⟨Λ₁, ⟨⟨hΛ₁cont, hΛ₁psi⟩, fun t => ?_⟩⟩
  exact eq_add_of_sub_eq' (hℓ_const t)

/-- **The winding vector is invariant under homotopy of closed curves of the torus.** -/
theorem homotopic_eq {P : Work.CoreTopology.ParamTorus}
    {α β : Work.CoreTopology.ClosedCurve P} (h : Work.CoreTopology.Homotopic P α β) :
    Work.SurgeryInvariance.windingOf P α = Work.SurgeryInvariance.windingOf P β := by
  have hclosed : HomotopicClosed P.psi α.γ β.γ :=
    (Work.InnermostDisk.homotopic_iff_homotopicClosed P α β).mp h
  exact hasWinding_eq_of_homotopicClosed_param P hclosed
    (hasWinding_windingOf P α) (hasWinding_windingOf P β)

end

end Work.SurgeryInvariance.WindingOf
