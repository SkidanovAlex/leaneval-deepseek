import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_constants
import Submission.Work.MotC5N3.LamAS.asF_linearDisjoint
import Submission.Work.MotC5N3.LamAS.asIota_range
import Submission.Work.MotC5N3.LamAS.asF_transfer
import Submission.Work.MotC5N3.LamAS.asL2_isGalois
import Submission.Work.MotC5N3.LamAS.asML
import Submission.Work.MotC5N3.LamAS.Setup
import Submission.Work.MotC.constantsOnly_of_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

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

/-- **G-CO** (node CO_AS at a general base field `K`): the fixed field
`asTwistFieldTrue D g τ σS` of the twisted Artin–Schreier action is constants-only over `K`, for
every `ASTwistData` bundle and every `g ∈ {g₀, 2 g₀}` with `g₀ ∉ ℘(K)`.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.RigAS.constantsOnly_K_AS`
(`Submission/Work/MotV5/RigAS/constantsOnly_K_AS.lean`), whose base field is `RatFunc 𝕜`, whose
class is `Work.MotV.fAS 𝕜 = RatFunc.X ^ 3 + RatFunc.X` and whose support lives in
`Submission/Work/MotV5/LamAS/*.lean` and `Submission/Work/MotV5/RigAS/*.lean` (WP3 of
`MOTIVIC_CHAR5_N3_LEAD.md` §6).  The source proof is the descent engine over the finite Galois
model `K⟮asRoot g, asRoot 2g⟯` (`Work.MotC.constantsOnly_of_descent`, already generic in the base
field): an `M`-valued `K`-embedding `ι : F → RatFunc M` of the twist field has image in the
constants, because the twisted coordinates are the `σ'`-invariants of `K̄(E) = K(y_j/y_0)(asRoot g)`
and every embedding of the finite Galois model lands in a rational function field over a constant
field.

Its `RatFunc 𝕜`-specific inputs are exactly `Work.MotV5.CensusAux.fAS_notMem_pe` (`fAS ∉ ℘`) and
the two algebraic identities `℘(3u) = 3℘(u)`, `℘(-u) = -℘(u)`; here the single hypothesis
`hg₀ : ¬ ∃ u : K, u ^ 5 - u = g₀` replaces the first (and implies `2 g₀ ∉ ℘(K)` since
`℘(c u) = c ℘(u)` in characteristic `5`), and the other two are unchanged.  Nothing about
`fAS = RatFunc.X ^ 3 + RatFunc.X` or about `RatFunc 𝕜` beyond `g ≠ 0` and `g ∉ ℘(K)` may be used
(`MOTIVIC_CHAR5_N3_LEAD.md` §7).  The chain is `constantsOnly_K_AS` + `constantsOnly_transfer_AS`
+ the `LamAS` Galois linear-disjointness lemmas; those must be forked with the base field
generalised (`Submission/Work/MotC5N3/port.py` performs the textual port; the WP1 forks under
`Submission/Work/MotC5N3/TwistField/` are the model).

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/constantsOnly_K_AS.lean` plus
forked support, sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem constantsOnly_K_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g₀ : K) (hg₀ : ¬ ∃ u : K, u ^ 5 - u = g₀) (g : K) (hg : g = g₀ ∨ g = 2 • g₀)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (h : Work.MotC5N3.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV.ConstantsOnly K ↥(Work.MotC5N3.asTwistFieldTrue D g τ σS) := by
  classical
  -- ## The Artin–Schreier two-root field `L = K⟮g₀, 2 g₀⟯` is finite Galois over `K`.
  obtain ⟨hGal, hFin⟩ := Work.MotC5N3.LamAS.asL2_isGalois K g₀ (2 • g₀)
  haveI : IsGalois K ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀)) := hGal
  haveI : FiniteDimensional K ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀)) := hFin
  haveI : Algebra.IsAlgebraic K ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀)) :=
    Algebra.IsAlgebraic.of_finite _ _
  -- ## The base-changed Klein model over `L` is non-singular.
  haveI : D.E.IsElliptic := hD.1.elliptic
  have hΔE : D.E.Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ D.E).ne_zero
  have hΔ : (Work.MotC5N3.LamAS.asE2 D g₀ (2 • g₀)).Δ ≠ 0 := by
    show (D.E.baseChange ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀))).Δ ≠ 0
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h0
    exact hΔE ((algebraMap 𝕜
      ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀))).injective (by simpa using h0))
  -- ## The two inputs of the descent engine.
  have hLI : (Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS).LinearDisjoint
      ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀)) :=
    Work.MotC5N3.LamAS.asF_linearDisjoint 𝕜 D hD g₀ (2 • g₀) g τ σS σ h hg
  have htransfer := Work.MotC5N3.LamAS.asF_transfer 𝕜 D hD g₀ (2 • g₀) g τ σS σ h hg
    (Work.MotC5N3.LamAS.asIota_range 𝕜 D hD g₀ (2 • g₀))
  have hsup : (Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS) ⊔
      (IsScalarTower.toAlgHom K
        ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀))
        (Work.MotC5N3.LamAS.asML D g₀ (2 • g₀))).fieldRange = ⊤ :=
    htransfer.2.1
  -- ## The descent engine.
  have hCO : Work.MotV.ConstantsOnly K
      ↥(Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS) :=
    Work.MotC.constantsOnly_of_descent (𝕜 := K)
      (L := ↥(Work.MotC5N3.LamAS.asL2 g₀ (2 • g₀)))
      (W := Work.MotC5N3.LamAS.asE2 D g₀ (2 • g₀))
      hΔ (Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS) hLI hsup
  -- ## Transport along `asIota`, which restricts to a surjection `asF ↠ asTwistFieldTrue`.
  let f : ↥(Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS) →ₐ[K]
      ↥(Work.MotC5N3.asTwistFieldTrue D g τ σS) :=
    AlgHom.codRestrict
      ((Work.MotC5N3.LamAS.asIota D g₀ (2 • g₀)).comp
        (Work.MotC5N3.LamAS.asF D g₀ (2 • g₀) g τ σS).val)
      (Work.MotC5N3.asTwistFieldTrue D g τ σS).toSubalgebra (fun x => x.2)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange
      (f := Work.MotC5N3.LamAS.asIota D g₀ (2 • g₀))).mp
      (htransfer.1 y.2)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show Work.MotC5N3.LamAS.asIota D g₀ (2 • g₀) x
      ∈ Work.MotC5N3.asTwistFieldTrue D g τ σS
    rw [hx]
    exact y.2
  exact constantsOnly_of_surjective_algHom f hsurj hCO

end Work.MotC5N3
