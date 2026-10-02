/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the bifurcation side at a simple parabolic parameter (FBif, main)

Hubbard–Schleicher's Lemma 3.4 (= MNS Theorem 2.1, second half) for the mandelbar: at a simple
parabolic parameter of the period-`5` component, arbitrarily close to `c` there are parameters
`c'` for which `T_{c'}` has **no** point of period dividing `5` in a fixed disc around the
parabolic point `z₁`.

Everything is proved in this area:

* `Work.FBif.exists_goodPerturbation` — the perturbing antipolynomial of HS Lemma 3.4;
* `Work.FBif.fifthIterate_expansion` — the Taylor expansion of `T_c^5` at `z₁`;
* `Work.FBif.hsLocal_bound` — HS's local case analysis;
* `Work.FBif.exists_HSExpansion` — the normalised expansion of the perturbed fifth iterate;
* `Work.FBif.HSEstimate.of_expansion'` — HS's estimate from the expansion and the local bound;
* `Work.FBif.exists_gluingDatum_scaled` — **the gluing construction**: the C¹ gluing of the
  perturbed map with the model `T_c`, its invariant Beltrami coefficient, and the quantitative
  normalisation of the principal solution (MRMT `M1`);
* `Work.FBif.straightening_of_gluingFamily` — the gluing datum plus the *proved* MRMT consumer
  API (`Submission.Work.MRMT.Found`) gives the straightening `Work.FBif.Straightening`;
* `Work.FBif.bifSide_of` — the transfer of "no period-`5` point" across the straightening
  homeomorphism.

The rescaling `q ↦ lam • q` in `Work.FBif.bifSide` is harmless because
`perturb c (lam • q) ε = perturb c q (lam ε)` and both `GoodPerturbation` and `HSEstimate` are
invariant under positive rescaling (`FBif/goodPerturbation_const_mul.lean`,
`FBif/hsEstimate_const_mul.lean`).

## Main results

* `Work.FBif.bifSide` — **the target of the area**, with no remaining hypothesis;
* `Work.FBif.bifSide_of_straightening` — the same from the straightening alone;
* `Work.FBif.bifSide_of_gluingDatum` — the same from the gluing datum family alone.
-/
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Expansion
import Submission.Work.FBif.HSLocal
import Submission.Work.FBif.Cycle
import Submission.Work.FBif.exists_goodPerturbation
import Submission.Work.FBif.exists_HSExpansion
import Submission.Work.FBif.MRMTInput
import Submission.Work.FBif.straightening_of_gluingFamily
import Submission.Work.FBif.GlueAssembly
import Submission.Work.FBif.hsEstimate_const_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `a / (n + 2) → 0`: the sequence of small parameters used to extract a gluing family from a
`∀ ε > 0` statement. -/
theorem tendsto_div_add_two_nhds_zero (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => a / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h0 : Filter.Tendsto (fun _ : ℕ => a) Filter.atTop (nhds a) := tendsto_const_nhds
  exact h0.div_atTop h1

/-- **The bifurcation side, from the normalised expansion and the straightening.** -/
theorem bifSide_of_expansion (c : ℂ) (d : Work.EL.RootParabolic c) {A : ℂ} (hA : 0 < A.re)
    {q : ℂ → ℂ} (hexp : HSExpansion c d.z₁ q A) (hstr : Straightening c d.z₁ q) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball d.z₁ δ, (Tantibar c')^[5] z ≠ z :=
  bifSide_of c d.z₁ q (HSEstimate.of_expansion' hA hexp) hstr

/-- **The bifurcation side, from HS's expansion and the straightening of a good perturbation.** -/
theorem bifSide_of_inputs (c : ℂ) (d : Work.EL.RootParabolic c)
    (hexp : ∃ A : ℂ, 0 < A.re ∧ ∃ q : ℂ → ℂ,
      GoodPerturbation c d.z₁ q ∧ HSExpansion c d.z₁ q A)
    (hstr : ∀ A : ℂ, ∀ q : ℂ → ℂ, 0 < A.re → GoodPerturbation c d.z₁ q →
      HSExpansion c d.z₁ q A → Straightening c d.z₁ q) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball d.z₁ δ, (Tantibar c')^[5] z ≠ z := by
  obtain ⟨A, hA, q, hgood, hexp⟩ := hexp
  exact bifSide_of_expansion c d hA hexp (hstr A q hA hgood hexp)

/-- **FBif with HS's estimate discharged.**  The only remaining input is the straightening of
every good perturbation of `T_c` (which has to hold for the perturbation supplied by
`Work.FBif.exists_HSExpansion`). -/
theorem bifSide_of_straightening (c : ℂ) (d : Work.EL.RootParabolic c)
    (hStr : ∀ A : ℂ, ∀ q : ℂ → ℂ, 0 < A.re → GoodPerturbation c d.z₁ q →
      HSExpansion c d.z₁ q A → Straightening c d.z₁ q) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball d.z₁ δ, (Tantibar c')^[5] z ≠ z :=
  bifSide_of_inputs c d (exists_HSExpansion c d) hStr

/-- **FBif reduced to the gluing datum.**  The straightening input is replaced by the granular
`GluingDatum` (C¹ glued map, admissible invariant Beltrami coefficient, quantitative MRMT `M1`
and `M6`, asymptotic agreement with `T_c`), which together with the *proved* MRMT consumer API
gives the straightening by `Work.FBif.straightening_of_gluingFamily`. -/
theorem bifSide_of_gluingDatum (c : ℂ) (d : Work.EL.RootParabolic c) {δ' R : ℝ} (hδ' : 0 < δ')
    (hR : 0 < R)
    (hglue : ∀ A : ℂ, ∀ q : ℂ → ℂ, 0 < A.re → GoodPerturbation c d.z₁ q →
      HSExpansion c d.z₁ q A → ∀ ε : ℝ, 0 < ε → GluingDatum c d.z₁ q δ' R ε) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball d.z₁ δ, (Tantibar c')^[5] z ≠ z :=
  bifSide_of_straightening c d fun A q hA hgood hexp =>
    straightening_of_gluingFamily hδ' hR (εs := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      (fun n => by positivity)
      (tendsto_div_add_two_nhds_zero 1)
      (fun n => hglue A q hA hgood hexp _ (by positivity))

/-- **The FBif target** (Hubbard–Schleicher Lemma 3.4 / MNS Theorem 2.1, second half): at a
simple parabolic parameter `c` of the period-`5` component, arbitrarily close to `c` there are
parameters `c'` for which `T_{c'}` has **no** point of period dividing `5` in a fixed disc
around the parabolic point `z₁`.  Nothing is assumed: the C¹ gluing, its invariant Beltrami
coefficient and the straightening are all constructed in this area. -/
theorem bifSide (c : ℂ) (d : Work.EL.RootParabolic c) :
    ∃ δ > 0, ∀ r > 0, ∃ c' ∈ Metric.ball c r,
      ∀ z ∈ Metric.ball d.z₁ δ, (Tantibar c')^[5] z ≠ z := by
  obtain ⟨A, hA, q, hgood, hexp⟩ := exists_HSExpansion c d
  obtain ⟨lam, hlam0, δ', hδ', ε₀, hε₀, hglue⟩ :=
    exists_gluingDatum_scaled c d.z₁ q hgood d.per_half d.ne_per
  -- the far radius of the datum is positive
  have hdatum_pos : 0 < datumRad c := (datumRad_spec c).2.1
  -- HS's estimate for the rescaled perturbation
  have hHS : HSEstimate c d.z₁ (fun z => (lam : ℂ) * q z) :=
    hsEstimate_const_mul (HSEstimate.of_expansion' hA hexp) hlam0
  -- the sequence of small parameters
  have hεpos : ∀ n : ℕ, 0 < ε₀ / ((n : ℝ) + 2) := fun n => div_pos hε₀ (by positivity)
  have hεlt : ∀ n : ℕ, ε₀ / ((n : ℝ) + 2) < ε₀ := by
    intro n
    have h1 : (1 : ℝ) < (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ h2]
    nlinarith [hε₀, h1]
  have hεtend : Filter.Tendsto (fun n : ℕ => ε₀ / ((n : ℝ) + 2)) Filter.atTop (nhds 0) :=
    tendsto_div_add_two_nhds_zero ε₀
  -- the straightening for the rescaled perturbation
  have hstr : Straightening c d.z₁ (fun z => (lam : ℂ) * q z) :=
    straightening_of_gluingFamily hδ' hdatum_pos hεpos hεtend
      (fun n => Classical.choice (hglue (ε₀ / ((n : ℝ) + 2)) (hεpos n) (hεlt n)))
  exact bifSide_of c d.z₁ _ hHS hstr

end Work.FBif

end
