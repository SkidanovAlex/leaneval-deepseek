import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.exponent_rigidity_AS
import Submission.Work.MotV5.hurwitz_AS
import Submission.Work.MotV5.base_preserved_AS
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.ASUnramified_fAS_of_two_smul
import Submission.Work.MotV5.fifthPowAtPoles_of_asPoint
import Submission.Work.MotV5.RigAS.bridge_twist
import Submission.Work.MotV5.Nodes.lam_AS_alpha
import Submission.Work.MotV5.Nodes.restrict_AS
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MotV5.Nodes

/-!
## Auxiliary structural lemmas for node RIG_AS (characteristic `5`)

Besides the (hard) Artin–Schreier bridge `ASUnramified` of
`Submission.Work.MotV5.Nodes.bridge_AS`, the rigidity node needs

* the *regularity* of the twist fields over `K = 𝕜(t)`: the `hR`-hypotheses of
  `Work.MotV5.base_preserved_AS` (design node REG_AS), proved here as
  `isAlgebraic_mem_base_asTwistFieldTrue`, on top of `isAlgebraic_mem_kb` (`K` is relatively
  algebraically closed in `Om D`), and
* the base-preservation consequence `base_preserved_of_bridge` of
  `Work.MotV5.base_preserved_AS` / `Work.MotV5.hurwitz_AS`, in the form in which the rigidity
  argument consumes it.
-/

/-- **`K` is relatively algebraically closed in `Om D`.**  An element of `Om D = Kb 𝕜(E)`
algebraic over `K = 𝕜(t)` lies in the image of `Kb 𝕜`.

`Kb 𝕜` is algebraically closed and an algebraic extension of an algebraically closed subfield of
a field is trivial (`IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`). -/
theorem isAlgebraic_mem_kb (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (r : Work.MotV.Om D) (hr : IsAlgebraic (RatFunc 𝕜) r) :
    ∃ c : Work.MotV.Kb 𝕜,
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c = r := by
  have hr' : IsAlgebraic (Work.MotV.Kb 𝕜) r := hr.tower_top (Work.MotV.Kb 𝕜)
  let L : IntermediateField (Work.MotV.Kb 𝕜) (Work.MotV.Om D) :=
    IntermediateField.adjoin (Work.MotV.Kb 𝕜) {r}
  have halg : Algebra.IsAlgebraic (Work.MotV.Kb 𝕜) ↥L :=
    IntermediateField.isAlgebraic_adjoin_simple hr'.isIntegral
  have hbot : L = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic L
  have hrL : r ∈ L := IntermediateField.subset_adjoin _ _ (Set.mem_singleton r)
  rw [hbot] at hrL
  rw [IntermediateField.mem_bot] at hrL
  exact hrL

/-- **Node REG_AS.**  The `K`-algebra `F = asTwistFieldTrue D g τ σS` is *regular* over
`K = 𝕜(t)`: every element algebraic over `K` is a constant.  This is the `hR`-hypothesis of
`Work.MotV5.base_preserved_AS`.

An algebraic element of `F` is algebraic inside `Om D`, hence lies in the image of `Kb 𝕜`
(`isAlgebraic_mem_kb`); as an element of `F ∩ Kb 𝕜` it is rational by
`Work.MotV5.asTwistFieldTrue_constants`. -/
theorem isAlgebraic_mem_base_asTwistFieldTrue (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hτ : ∀ c : Work.MotV.Kb 𝕜,
      τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1)
    (r : ↥(Work.MotV5.asTwistFieldTrue D g τ σS))
    (hr : IsAlgebraic (RatFunc 𝕜) r) :
    ∃ c : RatFunc 𝕜,
      algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) c = r := by
  have hrOm : IsAlgebraic (RatFunc 𝕜) (r : Work.MotV.Om D) := by
    obtain ⟨p, hp0, hp⟩ := hr
    exact ⟨p, hp0, by
      have := congrArg
        (fun x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS) => (x : Work.MotV.Om D)) hp
      simpa using this⟩
  obtain ⟨c₀, hc₀⟩ := isAlgebraic_mem_kb 𝕜 D (r : Work.MotV.Om D) hrOm
  have hc₀F : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c₀
      ∈ Work.MotV5.asTwistFieldTrue D g τ σS := by
    rw [hc₀]; exact r.2
  obtain ⟨d, hd⟩ := Work.MotV5.asTwistFieldTrue_constants 𝕜 D hD.1 g τ σS σ hτ hσ c₀ hc₀F
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change algebraMap (RatFunc 𝕜) (Work.MotV.Om D) d = (r : Work.MotV.Om D)
  rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D), hd, hc₀]

/-! ## The two inputs of the assembly

The target is then assembled from

* the *two diagonal bridge instances* — `ASUnramified` for `F₁` at the parameter `fAS 𝕜` and for
  `F₂` at the parameter `2 • fAS 𝕜`, which is exactly the statement of the node
  `Work.MotV5.Nodes.bridge_AS` — fed into
* `Work.MotV5.Nodes.v1_AS_of_bridge` (proved): every `𝕜`-algebra isomorphism `θ : F₁ ≃ₐ[𝕜] F₂`
  induces an automorphism `α` of the base `RatFunc 𝕜` with `θ (algebraMap c) = algebraMap (α c)`;
  the bridge at the parameter `fAS 𝕜` on `F₂`, which V1 needs on the target, is derived from the
  diagonal instance at `2 • fAS 𝕜` by `Work.MotV5.ASUnramified_fAS_of_two_smul` (proved);
* `Work.MotV5.Nodes.lam_AS_alpha` (proved): `α` and `θ` produce `ε = ±1` and a point of the twisted
  Klein curve `C^AS_{fAS - ε · α⁻¹ (2 • fAS)}`;
* `Work.MotV5.fifthPowAtPoles_of_asPoint` (proved) turns the point into the fifth-power pole
  condition for `fAS 𝕜 - m · α⁻¹ (fAS 𝕜)`, `m = 2ε ∈ {±2}`, which is contradicted by
  `Work.MotV5.exponent_rigidity_AS` (proved).

Because `Work.MotV5.Nodes.v1_AS_of_bridge` imports the present file (it consumes the regularity
node REG_AS proved below), the V1 step is reproduced here (as `v1_AS_local`) instead of imported:
importing it would create a cycle.  This is the only duplication, and it is a transcription of the
proved `v1_AS_of_bridge`. -/

/-- The Hurwitz hypothesis of `Work.MotV5.base_preserved_AS` at `f = X³ + X` (the `hH1`-input of
the base-preservation node), isolated in the generic form in which `base_preserved_AS` expects it.
It is `Work.MotV5.hurwitz_AS` at `f = X ^ 3 + X ∈ N[X]`; the bookkeeping is the coefficient ring of
``X ^ 3 + X``, which the `default_instance` `Work.MotV5.instDefaultSemiringInt` resolves to `ℤ`
whereas `hurwitz_AS` needs a polynomial over `N`; both evaluate to `r ^ 3 + r`. -/
theorem asHurwitz_X3_add_X_local {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N) [E.IsElliptic] :
    ∀ r : WeierstrassCurve.Affine.FunctionField E,
      (∀ v : Valuation (WeierstrassCurve.Affine.FunctionField E) (WithZero (Multiplicative ℤ)),
        Work.MotV.TrivOn N v → 1 < v r →
        ∃ u, v (Polynomial.aeval r (Polynomial.X ^ 3 + Polynomial.X) - (u ^ 5 - u)) ≤ 1) →
      ∃ c : N, algebraMap N (WeierstrassCurve.Affine.FunctionField E) c = r := by
  intro r hr
  have hdeg : ((Polynomial.X : Polynomial N) ^ 3 + (Polynomial.X : Polynomial N)).natDegree = 3 := by
    compute_degree!
  refine Work.MotV5.hurwitz_AS (N := N) E
    ((Polynomial.X : Polynomial N) ^ 3 + (Polynomial.X : Polynomial N)) ?_ ?_ r ?_
  · rw [hdeg]; norm_num
  · rw [hdeg]; norm_num
  · intro v hv h1'
    obtain ⟨u, hu⟩ := hr v hv h1'
    exact ⟨u, by
      simpa only [Polynomial.aeval_add, Polynomial.aeval_X_pow, Polynomial.aeval_X] using hu⟩

/-- **Node V1_AS, instantiated over the two twist fields** (transcription of the proved
`Work.MotV5.Nodes.v1_AS_of_bridge`, which imports the present file).  Here `hB₁` is the bridge at
the parameter `fAS 𝕜` on `F₁` and `hB₂` the bridge at the parameter `fAS 𝕜` on `F₂`. -/
theorem v1_AS_local (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂)
    (hB₁ : Work.MotV5.ASUnramified 𝕜
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
        (Work.MotV.fAS 𝕜)))
    (hB₂ : Work.MotV5.ASUnramified 𝕜
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
      (algebraMap (RatFunc 𝕜)
        ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
        (Work.MotV.fAS 𝕜))) :
    ∀ θ : ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
        ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS),
      ∃ α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜, ∀ c : RatFunc 𝕜,
        θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) c)
          = algebraMap (RatFunc 𝕜)
              ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) (α c) := by
  intro θ
  haveI hEll : (D.E.baseChange (Work.MotV.Kb 𝕜)).IsElliptic := by
    haveI := hD.1.elliptic
    exact inferInstanceAs ((D.E.map (algebraMap 𝕜 (Work.MotV.Kb 𝕜))).IsElliptic)
  haveI : IsAlgClosed (Work.MotV.Kb 𝕜) := inferInstance
  haveI : CharP (Work.MotV.Kb 𝕜) 5 := inferInstance
  haveI : Algebra.IsAlgebraic (RatFunc 𝕜) (Work.MotV.Kb 𝕜) := inferInstance
  have hιgen : ∀ (F : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D)) (c : RatFunc 𝕜),
      ((IntermediateField.val F : ↥F →ₐ[RatFunc 𝕜] Work.MotV.Om D) :
          ↥F →+* WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)))
        (algebraMap (RatFunc 𝕜) ↥F c)
      = algebraMap (Work.MotV.Kb 𝕜)
          (WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c) := by
    intro F c
    simp [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
      (WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)))]
  let ι₁ : ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) →+*
      WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
    (IntermediateField.val (Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) :
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) →ₐ[RatFunc 𝕜] Work.MotV.Om D)
  let ι₂ : ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) →+*
      WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
    (IntermediateField.val (Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) :
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) →ₐ[RatFunc 𝕜] Work.MotV.Om D)
  have hι₁ : ∀ c : RatFunc 𝕜, ι₁ (algebraMap (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) c)
      = algebraMap (Work.MotV.Kb 𝕜)
          (WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c) := hιgen _
  have hι₂ : ∀ c : RatFunc 𝕜, ι₂ (algebraMap (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) c)
      = algebraMap (Work.MotV.Kb 𝕜)
          (WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotV.Kb 𝕜)))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) c) := hιgen _
  have hR₁ : ∀ r : ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS),
      IsAlgebraic (RatFunc 𝕜) r →
      ∃ c : RatFunc 𝕜,
        algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) c = r :=
    fun r hr => isAlgebraic_mem_base_asTwistFieldTrue 𝕜 D hD (Work.MotV.fAS 𝕜) τ σS σ
      h1.hτ h1.hσ r hr
  have hR₂ : ∀ r : ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS),
      IsAlgebraic (RatFunc 𝕜) r →
      ∃ c : RatFunc 𝕜,
        algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) c
          = r :=
    fun r hr => isAlgebraic_mem_base_asTwistFieldTrue 𝕜 D hD (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂
      h2.hτ h2.hσ r hr
  have hθ : ∀ c : RatFunc 𝕜, ∃ d : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) c)
        = algebraMap (RatFunc 𝕜)
            ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) d :=
    Work.MotV5.base_preserved_AS (N := Work.MotV.Kb 𝕜)
      (E := D.E.baseChange (Work.MotV.Kb 𝕜))
      (F₁ := ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS))
      (F₂ := ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))
      (asHurwitz_X3_add_X_local (N := Work.MotV.Kb 𝕜) (D.E.baseChange (Work.MotV.Kb 𝕜)))
      ι₁ ι₂ hι₁ hι₂ hB₁ hB₂ hR₁ hR₂ θ
  have hθ' : ∀ d : RatFunc 𝕜, ∃ c : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) c)
        = algebraMap (RatFunc 𝕜)
            ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) d := by
    intro d
    obtain ⟨c, hc⟩ := Work.MotV5.base_preserved_AS (N := Work.MotV.Kb 𝕜)
      (E := D.E.baseChange (Work.MotV.Kb 𝕜))
      (F₁ := ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS))
      (F₂ := ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS))
      (asHurwitz_X3_add_X_local (N := Work.MotV.Kb 𝕜) (D.E.baseChange (Work.MotV.Kb 𝕜)))
      ι₂ ι₁ hι₂ hι₁ hB₂ hB₁ hR₂ hR₁ θ.symm d
    exact ⟨c, by rw [← hc, AlgEquiv.apply_symm_apply]⟩
  exact Work.MotV5.Nodes.restrict_AS 𝕜 D hD (Work.MotV.fAS 𝕜) (2 • Work.MotV.fAS 𝕜)
    τ τ₂ σS σ σ₂ h1 h2 θ hθ hθ'

/-- **Node RIG_AS — rigidity of the Artin–Schreier link.**  The two twist fields of the link,
`F₁ = asTwistFieldTrue D (fAS 𝕜) τ σS` (class `f = t³ + t`) and
`F₂ = asTwistFieldTrue D (2 • fAS 𝕜) τ₂ σS` (class `2f`), are *not* isomorphic as `𝕜`-algebras.
The `𝕜`-algebra structure is via `𝕜 → RatFunc 𝕜 → Fᵢ` (the instance used by `ConstantsOnly` and by
`Work.MotV.certN_of_linkCert`); both fields are subtypes of `Om D`, and both bundles share the
projective fifth-torsion shift `σS` (with `τ`, `τ₂` the coefficient actions of the AS generators
`σ`, `σ₂` of the two classes).

**Route** (design §C5, in the shape of the characteristic-`≠ 5` sibling `Work.MotV`: nodes
V1_AS/REG_AS/NAT_AS/LAM_AS/TP_AS/V4_AS).
1. *The base is preserved* (node V1_AS): by `Work.MotV5.base_preserved_AS` (proved) an isomorphism
   `θ : F₁ ≃ₐ[𝕜] F₂` whose image of `RatFunc.X` is a constant induces
   `α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜` with `θ (algebraMap _ _ t) = algebraMap _ _ (α t)`.
2. *The classes agree up to sign* (node LAM_AS, the C2/cocycle input): comparing the two twists
   through `θ` gives `∃ ε ∈ {1, -1}`, `fAS 𝕜 − ε · α (2 • fAS 𝕜) ∈ ℘(RatFunc 𝕜)`, i.e.
   `∃ u : RatFunc 𝕜, fAS 𝕜 − ε · α (2 • fAS 𝕜) = u ^ 5 - u`.  The `j ≠ 1728` input excluding the
   order-`4` automorphisms of `E` is a field of `Work.MotV5.KleinData.ASGood` (`Good.j_ne`), so
   the "up to `±`" reduction is available.
3. *Exponent count* (node V4_AS = `Work.MotV5.exponent_rigidity_AS`, proved, plus TP): step 2
   contradicts the valuation at the place `t = ∞`.  A solution `u` of `u ^ 5 - u = g` in
   `RatFunc 𝕜` has, at `∞`, either no pole or a pole of order divisible by `5`, whereas
   `fAS 𝕜 − ε · α (2 • fAS 𝕜)` is of the form `fAS 𝕜 − m · α (fAS 𝕜)` with `m = 2ε ∈ {±2}` (or
   `{±3}` after using the inverse isomorphism), and `exponent_rigidity_AS` states exactly that for
   `m ∈ {±2, ±3}` there is a valuation of `RatFunc 𝕜`, trivial on `𝕜`, at which the element has a
   pole and is not fifth-power valued.  This is the contradiction.

If the statement as written is false — in particular if the two bundles do not pin the twist fields
down enough for step 2, or if `L(E)` does not separate them — report the corrected statement and a
counterexample rather than weakening the conclusion. -/
theorem rigidity_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂) :
    IsEmpty (↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) ≃ₐ[𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) := by
  refine ⟨fun θ => ?_⟩
  -- the two diagonal bridge instances (node BR_AS)
  have hdiag₁ : Work.MotV5.ASUnramified 𝕜
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
        (Work.MotV.fAS 𝕜)) :=
    Work.MotV5.RigAS.bridge_twist 𝕜 D hD (Work.MotV.fAS 𝕜) (Or.inl rfl) τ σS σ h1
  have hdiag₂ : Work.MotV5.ASUnramified 𝕜
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
      (algebraMap (RatFunc 𝕜)
        ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
        (2 • Work.MotV.fAS 𝕜)) :=
    Work.MotV5.RigAS.bridge_twist 𝕜 D hD (2 • Work.MotV.fAS 𝕜) (Or.inr rfl) τ₂ σS σ₂ h2
  -- V1_AS: the base automorphism `α` induced by `θ`
  obtain ⟨α, hα⟩ := v1_AS_local 𝕜 D hD τ τ₂ σS σ σ₂ h1 h2 hdiag₁
    (Work.MotV5.ASUnramified_fAS_of_two_smul 𝕜
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)
        RatFunc.X) hdiag₂)
    θ
  -- LAM_AS in `α`-semilinear form: `ε = ±1` and a point of the twisted Klein curve
  obtain ⟨ε, hε, y, hy, heq⟩ := Work.MotV5.Nodes.lam_AS_alpha 𝕜 D hD (Work.MotV.fAS 𝕜)
    (2 • Work.MotV.fAS 𝕜) τ τ₂ σS σ σ₂ h1 h2 α θ hα
  -- TP: the point gives the fifth-power pole condition for the parameter
  set g : RatFunc 𝕜 := Work.MotV.fAS 𝕜
    - algebraMap 𝕜 (RatFunc 𝕜) ((ε : ℤ) : 𝕜) * α.symm (2 • Work.MotV.fAS 𝕜) with hg
  have h5 : Work.MotV5.FifthPowAtPoles 𝕜 (RatFunc 𝕜) g :=
    Work.MotV5.fifthPowAtPoles_of_asPoint 𝕜 D hD g y hy heq
  -- the parameter is `fAS - m · α⁻¹ (fAS)`, `m = 2ε ∈ {2, -2}`
  have hsplit : α.symm (2 • Work.MotV.fAS 𝕜)
      = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) * α.symm (Work.MotV.fAS 𝕜) := by
    have h2 : (2 : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) := by
      rw [map_ofNat]
    have h : (2 : ℕ) • Work.MotV.fAS 𝕜
        = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) * Work.MotV.fAS 𝕜 := by
      rw [nsmul_eq_mul, Nat.cast_ofNat, h2]
    rw [h, map_mul, AlgEquiv.commutes]
  have hform : g = Work.MotV.fAS 𝕜
      - algebraMap 𝕜 (RatFunc 𝕜) (((ε : ℤ) : 𝕜) * 2) * α.symm (Work.MotV.fAS 𝕜) := by
    rw [hg, hsplit, map_mul]
    refl_ring1
  rw [hform] at h5
  -- the exponent count (node V4_AS) contradicts it, for both signs of `ε`
  rcases hε with hε | hε
  · rw [hε] at h5
    refine Work.MotV5.exponent_rigidity_AS 𝕜 α.symm (((1 : ℤ) : 𝕜) * 2) (Or.inl ?_) h5
    push_cast
    refl_ring1
  · rw [hε] at h5
    refine Work.MotV5.exponent_rigidity_AS 𝕜 α.symm (((-1 : ℤ) : 𝕜) * 2)
      (Or.inr (Or.inr (Or.inl ?_))) h5
    push_cast
    refl_ring1

end Work.MotV5.Nodes
