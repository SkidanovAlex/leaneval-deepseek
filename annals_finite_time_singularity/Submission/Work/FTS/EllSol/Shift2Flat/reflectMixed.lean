import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.SpecAux.timFlipData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Time reversal of the *mixed* slot (`∂_θ∂_z u - b ∂_θu`)

The `b ≤ 0` branch of the shifted Agmon passage is handled by the time reversal
`t ↦ -t`: it turns the operator `L_b = ∂_t - b` into `-L_{-b}`, and since every slot of the
estimate is a *square*, the reversal transports the slot to the reflected datum.  This file
proves the transport for the mixed slot, i.e.

`∫⁻_{(t,θ) ∈ ℝ × [0,π/2]} (∂_θ∂_z u - b ∂_θu)² sin(2θ)^{-η}
   = ∫⁻ (∂_θ∂_z ũ + b ∂_θũ)² sin(2θ)^{-η}`,  `ũ(t,θ) = u(-t,θ)`.

The mathematical content is exactly the change of variables `t ↦ -t` (which preserves the
Lebesgue measure of `ℝ × [0,π/2]`) combined with the pointwise derivative identities

* `∂_z ũ(t,θ) = -(∂_z u)(-t,θ)`, hence `∂_θ∂_z ũ(t,θ) = -(∂_θ∂_zu)(-t,θ)`;
* `∂_θ ũ(t,θ) = (∂_θu)(-t,θ)`.

Both hold *unconditionally* (Mathlib's `deriv` is total, and `deriv_comp_neg`/`deriv.neg`
are unconditional), so the hypothesis `hu` — which makes the slot meaningful — is not
needed in the proof.  The assignment is a genuine *lintegral* identity, so no measurability
of the integrand is available; we use `MeasurableEmbedding.lintegral_map`, which applies to
arbitrary `ℝ≥0∞`-valued functions.
-/

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- The time reflection `(t,θ) ↦ (-t,θ)` preserves the restricted Lebesgue measure
`(dz ⊗ dθ)|_{univ ×ˢ Iθ}`: the reflection is the product of the (measure preserving)
negation on `ℝ` with the identity on `Iθ`, and `univ ×ˢ Iθ` is invariant under it. -/
private theorem map_reflect_restrict_Iθ :
    Measure.map (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
        ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ) := by
  -- `univ ×ˢ Iθ` with the product measure is `volume ⊗ (volume|_{Iθ})`.
  have hkey : (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (univ : Set ℝ) Work.Spaces.Iθ
    rwa [Measure.restrict_univ] at h
  have hmap' : Measure.map (Prod.map Neg.neg id)
        ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ))
      = (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ) := by
    have h := (MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (MeasurePreserving.id (volume.restrict Work.Spaces.Iθ)))
    simpa using h.map_eq
  rw [← hkey]
  exact hmap'

/-- Change of variables for the Lebesgue integral over `univ ×ˢ Iθ` under the time
reflection.  The integrand is an arbitrary `ℝ≥0∞`-valued function: no measurability
hypothesis is needed, because the reflection is a measurable embedding
(`MeasurableEmbedding.lintegral_map`). -/
private theorem lintegral_reflect_Iθ (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F (-p.1, p.2))
      = ∫⁻ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := by
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
    MeasurableEmbedding.prodMap (measurableEmbedding_neg)
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hfun : (fun p : ℝ × ℝ => F (-p.1, p.2))
      = fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p) := by
    funext p
    simp [Prod.map_apply', id_eq]
  rw [hfun]
  calc ∫⁻ p, F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p)
        ∂((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      = ∫⁻ p, F p ∂(Measure.map (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
          ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))) :=
        (hemb.lintegral_map F).symm
    _ = ∫⁻ p, F p ∂((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) := by
        rw [map_reflect_restrict_Iθ]

theorem reflectMixed (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2))
      = (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2)) := by
  -- `∂_θ∂_z` of the reflected datum is minus `∂_θ∂_zu` of `u`, evaluated at `-t`.
  have hpthpz : ∀ t θ : ℝ,
      Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) t θ
        = - Work.Spaces.pth (Work.Spaces.pz u) (-t) θ := by
    intro t θ
    have h1 : (fun θ' => Work.Spaces.pz (fun t θ => u (-t) θ) t θ')
        = fun θ' => - Work.Spaces.pz u (-t) θ' := by
      funext θ'
      exact deriv_comp_neg (f := fun s => u s θ') (x := t)
    change deriv (fun θ' => Work.Spaces.pz (fun t θ => u (-t) θ) t θ') θ
      = - deriv (fun θ' => Work.Spaces.pz u (-t) θ') θ
    rw [h1]
    exact deriv.neg
  -- `∂_θ` of the reflected datum is `∂_θu` of `u`, evaluated at `-t` (definitionally).
  have hpth : ∀ t θ : ℝ, Work.Spaces.pth (fun t θ => u (-t) θ) t θ
      = Work.Spaces.pth u (-t) θ := fun t θ => rfl
  -- hence the reflected integrand is the original one composed with the reflection.
  have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2))
      = fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz u) (-p.1) p.2 - b * Work.Spaces.pth u (-p.1) p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) := by
    funext p
    rw [hpthpz p.1 p.2, hpth p.1 p.2]
    congr 1
    ring
  rw [hfun]
  exact (lintegral_reflect_Iθ (fun p : ℝ × ℝ => ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2))).symm

end

end Work.FTS.EllSol.Shift2Flat
