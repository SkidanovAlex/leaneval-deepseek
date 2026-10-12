import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Measurability of the partial integral against `conj (etaOf e v)`

The "weak" (measurable) slot calculus of `Work.MB.SlotWeakBase` needs the following
Fubini-style closure fact: if `Θ : (Fin n → E3) → ℂ` is measurable, then so is the
partial integral

`y ↦ ∫ u, conj (η u) · Θ (x[i ↦ y][j ↦ u])`,

where `η = etaOf e v = Σ_l v_l e_l` is a finite superposition of measurable one-particle
functions.  The proof is the joint-measurability route: the coordinate map
`(y,u) ↦ x[i ↦ y][j ↦ u]` is *continuous* (two applications of `Continuous.update`), hence
`(y,u) ↦ conj (η u) · Θ (x[i ↦ y][j ↦ u])` is strongly measurable, and the Bochner integral
of a strongly measurable two-variable function is strongly measurable
(`MeasureTheory.StronglyMeasurable.integral_prod_right'`), which upgrades to `Measurable`
(a strongly measurable function is measurable).

No integrability hypothesis on `Θ` is needed: the joint-measurability theorem is an
identity for the (everywhere defined) Bochner integral.

No hypotheses on `i`, `j` (in particular `i = j` is allowed).
-/

open MeasureTheory

namespace Work.BoseBoxFock

theorem measurable_integral_conjEtaOf_update {m n : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (v : Fin m → ℝ) (Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΘm : Measurable Θ) (x : Fin n → EuclideanSpace ℝ (Fin 3)) (i j : Fin n) :
    Measurable (fun y : EuclideanSpace ℝ (Fin 3) =>
      ∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseDict.etaOf e v u)
        * Θ (Function.update (Function.update x i y) j u)) := by
  have heta : Measurable (Work.BoseDict.etaOf e v) := Work.MB.etaOf_weak_measurable hmeas v
  -- the coordinate map `(y,u) ↦ x[i ↦ y][j ↦ u]` is continuous
  have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Function.update x i p.1) :=
    Continuous.update (continuous_const :
      Continuous (fun _ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => x)) i continuous_fst
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Function.update (Function.update x i p.1) j p.2) := Continuous.update h1 j continuous_snd
  have hΘ : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Θ (Function.update (Function.update x i p.1) j p.2)) := hΘm.comp hcont.measurable
  have hjoint : StronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e v p.2)
        * Θ (Function.update (Function.update x i p.1) j p.2)) :=
    (((continuous_star.measurable.comp (heta.comp measurable_snd)).mul hΘ)).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hjoint).measurable

end Work.BoseBoxFock
