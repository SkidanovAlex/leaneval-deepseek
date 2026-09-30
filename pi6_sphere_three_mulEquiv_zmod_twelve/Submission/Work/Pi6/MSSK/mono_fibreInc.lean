import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-!
# `mono_fibreInc`

`fibreInc p σ : T_{σ(s)} ⟶ T_σ` is the inclusion of the part of `T_σ = Δ[s] ×_{Sing B} Sing E` over
the last vertex `σ(s)` of `σ`.  It is induced by the map `lastV s : Δ[0] ⟶ Δ[s]`, and we show it is a
monomorphism of simplicial sets.

The argument is purely categorical and uses no computation on simplices: write
`k = lastV s`, `σ : Δ[s] ⟶ B`, `f = Sing p : E ⟶ B`, `π₁ = pullback.fst σ f`,
`ρ₁ = pullback.fst (k ≫ σ) f`, `ρ₂ = pullback.snd (k ≫ σ) f`.  Then

* `fibreInc p σ ≫ π₁ = ρ₁ ≫ k` and `fibreInc p σ ≫ π₂ = ρ₂` (its two projections),
* `k` is a mono because `Δ[0]` is a terminal object of `SSet` (`SSet.stdSimplex.isTerminalObj₀`),
  so any two maps with target `Δ[0]` are equal.

Hence if `g ≫ fibreInc = h ≫ fibreInc` then `g ≫ ρ₂ = h ≫ ρ₂` (project onto the second factor) and
`g ≫ ρ₁ ≫ k = h ≫ ρ₁ ≫ k`, whence `g ≫ ρ₁ = h ≫ ρ₁` by mono-ness of `k`; two maps into the pullback
`T_{σ(s)}` agreeing on both projections are equal.
-/

theorem mono_fibreInc {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Mono (Work.Pi6.MSSK.fibreInc p σ) := by
  -- `Δ[0]` is terminal in `SSet`, so `lastV s` is a monomorphism.
  have hk : Mono (lastV s) := ⟨fun _ _ _ => SSet.stdSimplex.ext₀⟩
  refine ⟨fun {Z} g h H => ?_⟩
  -- the two projections of `fibreInc`
  have h1 : (fibreInc p σ) ≫ pullback.fst σ (Work.SSSR.sSingP p)
      = pullback.fst (lastV s ≫ σ) (Work.SSSR.sSingP p) ≫ lastV s := by
    rw [fibreInc, pullback.lift_fst]
  have h2 : (fibreInc p σ) ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (lastV s ≫ σ) (Work.SSSR.sSingP p) := by
    rw [fibreInc, pullback.lift_snd]
  apply pullback.hom_ext
  · -- first projection: cancel `lastV s`
    apply hk.right_cancellation
    simpa only [Category.assoc, h1] using
      congrArg (fun t => t ≫ pullback.fst σ (Work.SSSR.sSingP p)) H
  · -- second projection: direct
    simpa only [Category.assoc, h2] using
      congrArg (fun t => t ≫ pullback.snd σ (Work.SSSR.sSingP p)) H

end Work.Pi6.MSSK
