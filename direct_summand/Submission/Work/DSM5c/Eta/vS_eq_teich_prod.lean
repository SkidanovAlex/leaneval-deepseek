import Mathlib
import Submission.Work.DSM5c.Eta.Setup
import Submission.Work.DSM5c.Eta.gLoc_fracU

/-!
# DSM5c / Eta — `v_S = teich(∏_{i ∈ S} u_i)`

The localisation element `vS S = ♯(u_S)` of the chart untilt `D_S` (the image of the honest chart
denominator `t_S = ∏_{i ∈ S} t_i ∈ W`) equals the Teichmüller lift of the product of the tilted
chart generators `u_i = chartTiltGen … i ∈ R_S`.

This is the "denominator dictionary" companion of `Work.DSM5c.Eta.gLoc_fracU`: since
`vS S = untiltOf.algebraMap hθ φ_S (tS t S)` and `tS t S = ∏_{i ∈ S} t i`, and since the
`W`-algebra structure is multiplicative while `teich S (u i) = untiltOf.algebraMap hθ φ_S (t i)`
for every `i` (`Work.DSM5c.Eta.teich_uEl`, which uses the hypothesis `hj₀`), the claim reduces to
multiplicativity of `teich S` (`Work.DSM5c.Eta.teich_mul`) over the finite product.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c.Eta

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

section Setup

variable {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
  (Q : PerfectoidData p W)
  (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **The Teichmüller map `teich S : R_S → D_S` preserves `1`**: both `WittVector.teichmuller p`
and the untilt quotient map `untiltOf.mk φ_S` are ring homomorphisms. -/
theorem teich_one (S : Finset ι) :
    teich Q t tr htr0 htr j₀ e S (1 : tiltChart' Q t tr htr0 htr j₀ e S) = 1 := by
  simp only [teich, map_one]

/-- **The Teichmüller map `teich S` as a monoid homomorphism `R_S →* D_S`.**  It is only
multiplicative (Teichmüller is not additive), which is all that is needed to move it across finite
products. -/
noncomputable def teichHom (S : Finset ι) :
    tiltChart' Q t tr htr0 htr j₀ e S →* DS Q t tr htr0 htr j₀ e S where
  toFun := teich Q t tr htr0 htr j₀ e S
  map_one' := teich_one Q t tr htr0 htr j₀ e S
  map_mul' := fun x y => teich_mul Q t tr htr0 htr j₀ e S x y

/-- **The Teichmüller map `teich S` preserves finite products** (multiplicativity over a finset). -/
theorem teich_prod (S : Finset ι) (f : ι → tiltChart' Q t tr htr0 htr j₀ e S) :
    teich Q t tr htr0 htr j₀ e S (∏ i ∈ S, f i)
      = ∏ i ∈ S, teich Q t tr htr0 htr j₀ e S (f i) :=
  map_prod (teichHom Q t tr htr0 htr j₀ e S) f S

end Setup

/-- **The denominator dictionary of the chart map `η`.**

The localisation element `vS S = ♯(tS t S) = untiltOf.algebraMap hθ φ_S (tS t S)` of the chart
untilt equals the Teichmüller lift of the product of the tilted chart generators `u_i = uEl S i`:

  `vS S = teich S (∏_{i ∈ S} u_i)`.

Indeed `tS t S = ∏_{i ∈ S} t i` (`Work.DSM5c.tS`), the `W`-algebra structure
`untiltOf.algebraMap hθ φ_S` is a ring homomorphism, and `teich S (u i) =
untiltOf.algebraMap hθ φ_S (t i)` for every `i` by `Work.DSM5c.Eta.teich_uEl` (which is where the
hypothesis `hj₀ : t j₀ = Q.ϖ 0 ^ e` enters). -/
theorem vS_eq_teich_prod {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) (S : Finset ι) :
    Work.DSM5c.Eta.vS Q hθ t tr htr0 htr j₀ e S
      = Work.DSM5c.Eta.teich Q t tr htr0 htr j₀ e S
          (∏ i ∈ S, Work.DSM5c.Eta.uEl Q t tr htr0 htr j₀ e S i) := by
  trans (∏ i ∈ S, (Work.DSM5c.untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S)) (t i))
  · rw [vS]
    exact map_prod (Work.DSM5c.untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S))
      (fun i => t i) S
  · trans (∏ i ∈ S, teich Q t tr htr0 htr j₀ e S (uEl Q t tr htr0 htr j₀ e S i))
    · exact Finset.prod_congr rfl
        (fun i _ => (teich_uEl Q hθ t tr htr0 htr j₀ e hj₀ S i).symm)
    · exact (teich_prod Q t tr htr0 htr j₀ e S (fun i => uEl Q t tr htr0 htr j₀ e S i)).symm

end Work.DSM5c.Eta
