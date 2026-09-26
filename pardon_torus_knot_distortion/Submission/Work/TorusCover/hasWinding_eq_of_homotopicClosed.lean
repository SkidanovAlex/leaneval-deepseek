import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.hasWinding_unique

namespace Work.TorusCover

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal
open unitInterval

/-- **The winding vector is a homotopy invariant of closed curves.**

If `psiMap psi` induces a covering map onto its range and two curves against the same
parametrised torus `psi` are homotopic through closed curves in the range of `psi`, then
their winding vectors coincide.  (Compare `hasWinding_unique`, which handles the case of
two lifts of one curve.)

The proof lifts the homotopy with base point `Λ₀ 0` (`IsCoveringMap.liftHomotopy`), which
by uniqueness of lifts restricts to the given periodic lift `Λ₀` at `s = 0`.  The
displacement `F (s, 2π) - F (s, 0)` takes values in the discrete period lattice, hence is
constant in the connected parameter `s`; thus the lift `t ↦ F (1, t)` of `γ₁` has the same
period displacement `periodShift v` as `Λ₀`.  Uniqueness of the winding vector then gives
`v = w`. -/
theorem hasWinding_eq_of_homotopicClosed (P : Work.TorusCover.TorusParam)
    (hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi))
    {γ₀ γ₁ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {v w : ℤ × ℤ}
    (h : Work.TorusCover.HomotopicClosed P.psi γ₀ γ₁)
    (hv : Work.TorusCover.HasWinding P.psi γ₀ v) (hw : Work.TorusCover.HasWinding P.psi γ₁ w) :
    v = w := by
  obtain ⟨H, hHcont, hH0, hH1, hHper, hHrange⟩ := h
  obtain ⟨Λ₀, hΛ₀⟩ := hv
  -- The homotopy, viewed as a map into the range of `psiMap P.psi`.
  let Hbar : C(ℝ × ℝ, Set.range (psiMap P.psi)) :=
    ⟨fun st => ⟨H st, hHrange st.1 st.2⟩, hHcont.subtype_mk (fun st => hHrange st.1 st.2)⟩
  have hHbar_coe : ∀ st : ℝ × ℝ, ((Hbar st : Set.range (psiMap P.psi)) : R3) = H st :=
    fun st => rfl
  -- The homotopy restricted to `[0,1] × ℝ`.
  let G : C(unitInterval × ℝ, Set.range (psiMap P.psi)) :=
    Hbar.comp (ContinuousMap.prodMap ⟨Subtype.val, continuous_subtype_val⟩ (ContinuousMap.id ℝ))
  have hG_coe : ∀ (s : unitInterval) (t : ℝ), ((G (s, t) : Set.range (psiMap P.psi)) : R3)
      = H ((s : ℝ), t) := by
    intro s t
    rw [show (G (s, t) : Set.range (psiMap P.psi)) = Hbar ((s : ℝ), t) from rfl]
    exact hHbar_coe ((s : ℝ), t)
  -- The given periodic lift `Λ₀`, as a continuous map.
  let Λ₀c : C(ℝ, ℝ × ℝ) := ⟨Λ₀, hΛ₀.continuous⟩
  -- the prescribed lift of the initial curve `{0} × ℝ`
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
    rw [← P.psiMap_eq_iff, hF_psi s (2 * Real.pi), hF_psi s 0]
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
    rw [← P.psiMap_eq_iff, hF_psi 1 (t + 2 * Real.pi), hF_psi 1 t]
    simpa using hHper 1 t
  have hℓ_cont : Continuous fun t : ℝ => F (1, t + 2 * Real.pi) - F (1, t) :=
    ((((F.continuous.comp (continuous_const.prodMk (continuous_id.add continuous_const)))).sub
      (F.continuous.comp (continuous_const.prodMk continuous_id))))
  have hℓ_const : ∀ t : ℝ, F (1, t + 2 * Real.pi) - F (1, t) = periodShift v := by
    intro t
    have hc : F (1, t + 2 * Real.pi) - F (1, t) = F (1, 0 + 2 * Real.pi) - F (1, 0) :=
      isPreconnected_univ.constant_of_mapsTo isDiscrete_lattice hℓ_cont.continuousOn
        (fun t _ => hℓ_mem t) (mem_univ (0 : ℝ)) (mem_univ t)
    rw [hc, zero_add]
    exact hd_one
  refine hasWinding_unique P ?_ hw
  refine ⟨Λ₁, ⟨⟨hΛ₁cont, hΛ₁psi⟩, fun t => ?_⟩⟩
  exact eq_add_of_sub_eq' (hℓ_const t)

end Work.TorusCover
