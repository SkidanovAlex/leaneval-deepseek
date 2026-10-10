import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.GenAux_relfinrank_bot_adjoin_genX
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotK.TwCensus.TwistFieldTGTrdeg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.trdeg_twistFieldAS` — the AS twist field is the function field of a curve

The `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.ASLocal.trdeg_twistFieldAS`: for a Klein datum
`D : Work.MotV.KleinData 𝕜` with `ASGood D` and any `g : K` in a `𝕜`-algebra field `K` of
characteristic `5`, the explicit AS twist field `twistFieldAS D g = K(y_j/y_0)` has transcendence
degree `1` over `K`.

The two directions follow the source proof.

* **Upper bound** `≤ 1`: `twistFieldAS D g ≤ OmA K D = K̄(E)` and the function field of a curve has
  transcendence degree one (`Work.MotK.TwCensus.trdeg_functionField_eq_one`).
* **Lower bound** `≥ 1`: `asFieldL D g = K(E) ⊔ K⟮asRoot g⟯` contains `genX`, which is
  transcendental over `K`, and `asFieldL D g = twistFieldAS D g⟮asRoot g⟯` is *algebraic* over
  `twistFieldAS D g` (`asRoot g` is integral).  Hence if `twistFieldAS D g` were algebraic over `K`,
  so would `genX` be — contradiction.  This mirrors
  `Work.MotAS.transcendental_twistFieldAS` and gives an honest transcendental element of the twist
  field, from which the lower bound follows via
  `AlgebraicIndependent.cardinalMk_le_trdeg`.
-/

set_option autoImplicit false

namespace Work.MotC5N3

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- `CharP 𝕜 5` follows from `CharP K 5` because the algebra map `𝕜 → K` of fields is
injective: `(5 : 𝕜) = 0` is detected in `K`.  (The statement of `trdeg_twistFieldAS` does not
carry `CharP 𝕜 5`, but the twist-field vocabulary of `MotC5N3` does.) -/
lemma charP_kappa_of_charP_K (K : Type) [Field K] [Algebra 𝕜 K] [CharP K 5] : CharP 𝕜 5 := by
  have hinj : Function.Injective (algebraMap 𝕜 K) := (algebraMap 𝕜 K).injective
  refine ⟨fun x => ?_⟩
  rw [← map_eq_zero_iff (algebraMap 𝕜 K) hinj, map_natCast, CharP.cast_eq_zero_iff K 5]

/-- **The function field `K̄(E)` has transcendence degree one over `K`.**  This is the tower
`trdeg_K K̄(E) = trdeg_K K̄ + trdeg_K̄ K̄(E) = 0 + 1`. -/
lemma trdeg_OmA (D : Work.MotV.KleinData 𝕜) :
    Algebra.trdeg K (OmA K D) = 1 := by
  have hKb : Algebra.trdeg K (KbA K) = 0 := trdeg_eq_zero
  have hKbL : Algebra.trdeg (KbA K) (OmA K D) = 1 :=
    Work.MotK.TwCensus.trdeg_functionField_eq_one (KbA K) (D.E.baseChange (KbA K))
  have h := trdeg_add_eq K (KbA K) (A := OmA K D)
  rw [hKb, zero_add] at h
  rw [← h]
  exact hKbL

/-- **An explicit transcendental element of the AS twist field.**  `asFieldL D g` is generated over
`twistFieldAS D g` by the integral element `asRoot g`, hence is algebraic over it; it contains
`genX`, which is transcendental over `K`.  So `twistFieldAS D g` cannot be algebraic over `K`.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.transcendental_twistFieldAS`. -/
lemma transcendental_twistFieldAS_general (D : Work.MotV.KleinData 𝕜) (hG : D.Good) (g : K) :
    ∃ x : ↥(twistFieldAS D g), Transcendental K x := by
  classical
  haveI : CharP 𝕜 5 := charP_kappa_of_charP_K (K := K)
  set F : IntermediateField K (OmA K D) := twistFieldAS D g with hF
  -- `genX` is transcendental over `K`
  have hgenXtr : Transcendental K (Work.MotV.genX (D.E.baseChange (KbA K))) :=
    transcendental_genX_ratFunc 𝕜 D
  -- `genX` lies in the Klein field
  have hgenXKlein : Work.MotV.genX (D.E.baseChange (KbA K)) ∈ kleinField K D := by
    rw [kleinField_eq_adjoin_genXY 𝕜 D hG]
    exact IntermediateField.subset_adjoin K _ (by simp)
  -- `asFieldL = F⟮asOM⟯`
  have hRestr : asFieldL D g = IntermediateField.restrictScalars K
      (IntermediateField.adjoin ↥F {asOM D g}) := asFieldL_eq_restrict D g hG
  have hgenXmem : Work.MotV.genX (D.E.baseChange (KbA K))
      ∈ IntermediateField.adjoin ↥F {asOM D g} := by
    have h : Work.MotV.genX (D.E.baseChange (KbA K)) ∈ asFieldL D g :=
      (le_sup_left : kleinField K D ≤ asFieldL D g) hgenXKlein
    rw [hRestr] at h
    simpa using h
  -- `asOM` is integral over `F`, so `F⟮asOM⟯` is algebraic over `F`
  haveI hAlgAdjoin : Algebra.IsAlgebraic ↥F
      ↥(IntermediateField.adjoin ↥F {asOM D g}) :=
    IntermediateField.isAlgebraic_adjoin (S := {asOM D g}) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact asOM_isIntegral D g)
  -- hence `genX` is algebraic over `F`
  have hgenXalg : IsAlgebraic ↥F (Work.MotV.genX (D.E.baseChange (KbA K))) := by
    have h := hAlgAdjoin.isAlgebraic
      (⟨Work.MotV.genX (D.E.baseChange (KbA K)), hgenXmem⟩ :
        ↥(IntermediateField.adjoin ↥F {asOM D g}))
    simpa only [IntermediateField.algebraMap_apply] using
      (IsAlgebraic.algebraMap (R := ↥F)
        (S := ↥(IntermediateField.adjoin ↥F {asOM D g}))
        (A := OmA K D) h)
  -- if `F` were algebraic over `K`, then so would `genX` be
  by_contra hcon
  have hAlgF : Algebra.IsAlgebraic K ↥F := ⟨fun x => by
    by_contra hx
    exact hcon ⟨x, hx⟩⟩
  haveI := hAlgF
  exact hgenXtr ((Algebra.IsAlgebraic.isAlgebraic_iff K ↥F).mpr hgenXalg)

theorem trdeg_twistFieldAS (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Algebra.trdeg K ↥(Work.MotC5N3.twistFieldAS D g) = 1 := by
  have hG : D.Good := hD.1
  have hle : Algebra.trdeg K ↥(twistFieldAS D g) ≤ 1 := by
    have h := trdeg_le_of_injective (IntermediateField.val (twistFieldAS D g))
      (IntermediateField.val (twistFieldAS D g)).injective
    rw [trdeg_OmA D] at h
    exact h
  have hge : (1 : Cardinal) ≤ Algebra.trdeg K ↥(twistFieldAS D g) := by
    obtain ⟨x, hx⟩ := transcendental_twistFieldAS_general D hG g
    have hAI : AlgebraicIndependent K (fun _ : PUnit => x) :=
      (algebraicIndependent_unique_type_iff (R := K)
        (A := ↥(twistFieldAS D g)) (x := fun _ : PUnit => x)).mpr hx
    have h := AlgebraicIndependent.cardinalMk_le_trdeg hAI
    simpa using h
  exact le_antisymm hle hge

end Work.MotC5N3
