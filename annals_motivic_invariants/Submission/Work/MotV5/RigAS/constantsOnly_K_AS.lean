import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotV5.LamAS.asL2_isGalois
import Submission.Work.MotV5.LamAS.asF_linearDisjoint
import Submission.Work.MotV5.LamAS.asF_transfer
import Submission.Work.MotV5.LamAS.asIota_range
import Submission.Work.MotC.constantsOnly_of_descent
import Submission.Work.MotV.Bridge

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.RigAS

/-! The `K`-linear (`K = RatFunc 𝕜`) constants-only statement for the AS twist field
`F = asTwistFieldTrue D g τ σS`: every `K`-algebra map `F →ₐ[K] RatFunc M` has image in `M`.

ROUTE (everything it needs is already proved; this is an assembly, not new geometry).
Put `f₁ := fAS 𝕜`, `f₂ := 2 • fAS 𝕜`, `L := asL2 f₁ f₂ = K⟮asRoot f₁, asRoot f₂⟯ ⊆ Kb 𝕜` (a finite
Galois extension of `K = RatFunc 𝕜`, via `Work.MotV5.LamAS.asL2_isGalois`, PROVED),
`M0 := asML D f₁ f₂` (the function field of `asE2 D f₁ f₂ = (D.E).baseChange ↥L`), and
`asF D f₁ f₂ g τ σS = (asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂) ⊆ M0` (by definition).

1. `Work.MotV5.LamAS.asF_linearDisjoint` (PROVED) gives `(asF ...).LinearDisjoint ↥(asL2 f₁ f₂)`
   (it needs the `IsGalois`/`FiniteDimensional` instances, supplied by `asL2_isGalois`).
2. `Work.MotV5.LamAS.asF_transfer` (PROVED, with `hRange := asIota_range`) gives
   `asF ⊔ asLImageM D f₁ f₂ = ⊤` and `asF ⊓ asLImageM = ⊥`; the second is not needed here.
3. Apply the PROVED descent engine `Work.MotC.constantsOnly_of_descent` with
   `𝕜 := RatFunc 𝕜`, `L := ↥(asL2 f₁ f₂)`, `W := asE2 D f₁ f₂`, `A := asF ...`, `hΔ` from `hD`
   (`KleinData.Good.elliptic` + `WeierstrassCurve.isUnit_Δ`, base change preserves `Δ ≠ 0`),
   `hLI` from step 1 and `hsup` from step 2 (rewriting `asLImageM` as the `fieldRange` of
   `IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2) (asML)`).  This gives
   `ConstantsOnly (RatFunc 𝕜) ↥(asF D f₁ f₂ g τ σS)`.
4. Transport along the `K`-algebra isomorphism `↥(asF ...) ≃ₐ[K] ↥(asTwistFieldTrue D g τ σS)`
   induced by `asIota` (`Work.MotV5.LamAS.asIota_injective`, PROVED; the isomorphism sends `x` to
   `asIota x` and is well-defined since `asF = comap`): restate `ConstantsOnly` along it directly
   (`ι ↦ ι ∘ e.symm`).  (Do NOT use `Work.MotV.constantsOnly_of_algEquiv`: its constants-only is
   over the outer base, not over `RatFunc 𝕜`.) -/
namespace Work.MotV5.RigAS

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- `ConstantsOnly` is transported *forward* along a surjective `𝕜`-algebra homomorphism: if every
`𝕜`-embedding of `F` into a rational function field has constant image, the same holds for any
quotient (in the sense of a surjective `𝕜`-algebra map) of `F`, because an embedding of the
quotient pulls back to one of `F`. -/
theorem constantsOnly_of_surjective_algHom {𝕜 F F' : Type*} [Field 𝕜] [Field F] [Field F']
    [Algebra 𝕜 F] [Algebra 𝕜 F'] (f : F →ₐ[𝕜] F') (hf : Function.Surjective f)
    (h : Work.MotV.ConstantsOnly 𝕜 F) : Work.MotV.ConstantsOnly 𝕜 F' := by
  intro M _ _ ι x
  obtain ⟨y, rfl⟩ := hf x
  exact h M (ι.comp f) y

theorem constantsOnly_K_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV.ConstantsOnly (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) := by
  classical
  -- ## The Artin–Schreier two-root field `L = K⟮asRoot f₁, asRoot f₂⟯` is finite Galois over `K`.
  obtain ⟨hGal, hFin⟩ :=
    Work.MotV5.LamAS.asL2_isGalois 𝕜 (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)
  haveI : IsGalois (RatFunc 𝕜)
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)) := hGal
  haveI : FiniteDimensional (RatFunc 𝕜)
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)) := hFin
  haveI : Algebra.IsAlgebraic (RatFunc 𝕜)
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- ## The base-changed Klein model over `L` is non-singular.
  haveI : D.E.IsElliptic := hD.1.elliptic
  have hΔE : D.E.Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ D.E).ne_zero
  have hΔ : (Work.MotV5.LamAS.asE2 D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)).Δ ≠ 0 := by
    show (D.E.baseChange
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))).Δ ≠ 0
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h0
    exact hΔE ((algebraMap 𝕜
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))).injective
        (by simpa using h0))
  -- ## The two inputs of the descent engine.
  have hLI : (Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS).LinearDisjoint
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)) :=
    Work.MotV5.LamAS.asF_linearDisjoint 𝕜 D hD (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)
      g τ σS σ h hg
  have htransfer := Work.MotV5.LamAS.asF_transfer 𝕜 D hD (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)
    g τ σS σ h hg
    (Work.MotV5.LamAS.asIota_range 𝕜 D hD (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))
  have hsup : (Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS) ⊔
      (IsScalarTower.toAlgHom (RatFunc 𝕜)
        ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))
        (Work.MotV5.LamAS.asML D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))).fieldRange = ⊤ :=
    htransfer.2.1
  -- ## The descent engine.
  have hCO : Work.MotV.ConstantsOnly (RatFunc 𝕜)
      ↥(Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS) :=
    Work.MotC.constantsOnly_of_descent (𝕜 := RatFunc 𝕜)
      (L := ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)))
      (W := Work.MotV5.LamAS.asE2 D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))
      hΔ (Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS) hLI hsup
  -- ## Transport along `asIota`, which restricts to a surjection `asF ↠ asTwistFieldTrue`.
  let f : ↥(Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS) →ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D g τ σS) :=
    AlgHom.codRestrict
      ((Work.MotV5.LamAS.asIota D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)).comp
        (Work.MotV5.LamAS.asF D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) g τ σS).val)
      (Work.MotV5.asTwistFieldTrue D g τ σS).toSubalgebra (fun x => x.2)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange
      (f := Work.MotV5.LamAS.asIota D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜))).mp
      (htransfer.1 y.2)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show Work.MotV5.LamAS.asIota D (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜) x
      ∈ Work.MotV5.asTwistFieldTrue D g τ σS
    rw [hx]
    exact y.2
  exact constantsOnly_of_surjective_algHom f hsurj hCO

end Work.MotV5.RigAS

set_option linter.dupNamespace false

/-- `Work.MotV5.RigAS.constantsOnly_K_AS`: the canonical (single-namespace) statement,
definitionally equal to the declaration `Work.MotV5.RigAS.Work.MotV5.RigAS.constantsOnly_K_AS`
above, which is kept so that the doubly nested name also resolves. -/
theorem constantsOnly_K_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV.ConstantsOnly (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) :=
  _root_.Work.MotV5.RigAS.Work.MotV5.RigAS.constantsOnly_K_AS 𝕜 D hD g hg τ σS σ h

end Work.MotV5.RigAS
