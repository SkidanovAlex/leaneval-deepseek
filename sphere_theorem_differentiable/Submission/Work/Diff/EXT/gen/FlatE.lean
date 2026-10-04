import Mathlib
import Submission.Work.Diff.EXT.gen.FlatFin
import Submission.Work.Diff.EXT.gen.FlatJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat-indicator lemma for an arbitrary finite-dimensional domain

We prove: if `δ : ℝ × E → F` is `C^∞` on an open neighbourhood `V` of `(T, y₀)` (with `E` a
finite-dimensional real normed space and `F` a complete real normed space) and all its time Taylor
coefficients vanish along the hyperplane over an open set `U ∋ y₀`, then the Heaviside cut
`fun p => if p.1 ≤ T then 0 else δ p` is `C^∞` at `(T, y₀)`.

Route: transport along a continuous linear equivalence `E ≃L ℝⁿ` to the model space `ℝ × ℝⁿ`
(where the induction is universe-stable), use the bump-function reduction
`exists_forall_iteratedFDeriv_eq_zero_of_timeTaylor` and the flat-indicator lemma
`contDiffAt_of_flat_indicator_fin` there, and transport the conclusion back.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

/-- **Flat-indicator lemma for a finite-dimensional domain** (time-Taylor form). -/
theorem flat_indicator_E {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℝ} {y₀ : E} {V : Set (ℝ × E)} (hV : IsOpen V) (hV₀ : (T, y₀) ∈ V)
    {δ : ℝ × E → F} (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ V)
    {U : Set E} (hU : IsOpen U) (hy₀ : y₀ ∈ U)
    (hflat : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => δ (s, x)) T = 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) (T, y₀) := by
  classical
  -- a linear coordinate system on `E`
  set k := Module.finrank ℝ E with hk
  let e : E ≃L[ℝ] (Fin k → ℝ) := ((Module.finBasis ℝ E).equivFun).toContinuousLinearEquiv
  -- the two changes of coordinates
  let Φ : (ℝ × (Fin k → ℝ)) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ (Fin k → ℝ)).prod
      (((e.symm : (Fin k → ℝ) ≃L[ℝ] E) : (Fin k → ℝ) →L[ℝ] E).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin k → ℝ)))
  let Ψ : (ℝ × E) →L[ℝ] (ℝ × (Fin k → ℝ)) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod
      (((e : E ≃L[ℝ] (Fin k → ℝ)) : E →L[ℝ] (Fin k → ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ E))
  have hΦ : ∀ q : ℝ × (Fin k → ℝ), Φ q = (q.1, e.symm q.2) := fun q => rfl
  have hΨ : ∀ p : ℝ × E, Ψ p = (p.1, e p.2) := fun p => rfl
  have hΦΨ : ∀ p : ℝ × E, Φ (Ψ p) = p := by
    intro p
    rw [hΦ, hΨ]
    simp
  -- the transported data
  have hV' : IsOpen (Φ ⁻¹' V) := hV.preimage Φ.continuous
  have hV'₀ : (T, e y₀) ∈ Φ ⁻¹' V := by
    rw [Set.mem_preimage, hΦ]
    simpa using hV₀
  have hδ' : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin k → ℝ) => δ (Φ q)) (Φ ⁻¹' V) :=
    ContDiffOn.comp hδ Φ.contDiff.contDiffOn (fun q hq => hq)
  set U' : Set (Fin k → ℝ) := {x | e.symm x ∈ U} with hU'def
  have hU'open : IsOpen U' := hU.preimage e.symm.continuous
  have hy₀' : e y₀ ∈ U' := by
    rw [hU'def, Set.mem_setOf_eq]
    simpa using hy₀
  have hflat' : ∀ x ∈ U', ∀ i : ℕ,
      iteratedDeriv i (fun s : ℝ => (fun q : ℝ × (Fin k → ℝ) => δ (Φ q)) (s, x)) T = 0 := by
    intro x hx i
    have h1 : (fun s : ℝ => δ (Φ (s, x))) = (fun s : ℝ => δ (s, e.symm x)) := by
      funext s
      rw [hΦ]
    rw [h1]
    exact hflat (e.symm x) hx i
  -- the jet flatness in coordinates
  have hjet' : ∀ᶠ x in nhds (e y₀), ∀ k' : ℕ,
      iteratedFDeriv ℝ k' (fun q : ℝ × (Fin k → ℝ) => δ (Φ q)) (T, x) = 0 :=
    exists_forall_iteratedFDeriv_eq_zero_of_timeTaylor (E := Fin k → ℝ) (F := F)
      hV' hV'₀ hδ' hU'open hy₀' hflat'
  have hδ'at : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin k → ℝ) => δ (Φ q)) (T, e y₀) :=
    hδ'.contDiffAt (hV'.mem_nhds hV'₀)
  have hstep' := contDiffAt_of_flat_indicator_fin (n := k) (T := T) (x₀ := e y₀) hδ'at hjet'
  -- transport the conclusion back
  have hcomp : (fun q : ℝ × (Fin k → ℝ) => if q.1 ≤ T then (0 : F) else δ (Φ q))
      = (fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) ∘ Φ := by
    funext q
    rw [Function.comp_apply, hΦ]
  have hcutΦ : ContDiffAt ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) ∘ Φ) (T, e y₀) := hcomp ▸ hstep'
  have hcomposed : ContDiffAt ℝ (⊤ : ℕ∞)
      (((fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) ∘ Φ) ∘ Ψ) (T, y₀) := by
    refine hcutΦ.comp (T, y₀) ?_
    exact Ψ.contDiff.contDiffAt
  have hEq : (((fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) ∘ Φ) ∘ Ψ)
      = (fun p : ℝ × E => if p.1 ≤ T then (0 : F) else δ p) := by
    funext p
    simp only [Function.comp_apply]
    rw [hΦΨ p]
  rwa [hEq] at hcomposed

end Work.Diff.EXT.gen
