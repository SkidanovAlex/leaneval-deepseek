/-
  Area `WilC4aRW`: the reflection step of real Weierstrass preparation.

  `real_preparation` takes a complex-analytic germ `G : Ambient n → ℂ` which on the real points
  equals a real-valued function `g`, together with its complex Weierstrass preparation
  `G =ᶠ u * preparedPolynomial d a`, and produces REAL-analytic data `a'`, `u'` with
  `g =ᶠ u' * wpoly a'`.  The proof: the conjugate germ `star ∘ G ∘ conjAmb` is analytic
  (`Conj.conj_analytic_ambient`), prepares the conjugate data (`WPT.prep_conj`), and agrees with
  `G` near `0` because the two agree on the (maximal totally real) real subspace
  (`Real.eventuallyEq_of_eventuallyEq_ofRealAmbient`); uniqueness of preparation
  (`ClassicalComplexWPT.isWeierstrassPreparation_unique`) then forces the coefficients to be
  conjugation-invariant, i.e. real on real points.
-/
import Submission.Work.WilC4aRW.Defs
import Submission.Work.WilC4aRW.Conj.conj_analytic_ambient
import Submission.Work.WilC4aRW.WPT.prep_conj
import Submission.Work.WilC4aRW.Real.eventuallyEq_of_eventuallyEq_ofRealAmbient

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators ComplexConjugate
namespace Work.WilC4aRW
open ClassicalComplexWPT

theorem isWeierstrassPreparation_congr {n d : ℕ} {f f' : Ambient n → ℂ}
    {a : Fin d → Base n → ℂ} {u : Ambient n → ℂ} (h : f =ᶠ[nhds 0] f')
    (hprep : IsWeierstrassPreparation f d a u) : IsWeierstrassPreparation f' d a u :=
  ⟨hprep.1, hprep.2.1, hprep.2.2.1, hprep.2.2.2.1, h.symm.trans hprep.2.2.2.2⟩

/-- The prepared polynomial of a complex coefficient family that happens to take real values
at the real points equals the complexification of the real Weierstrass polynomial. -/
theorem preparedPolynomial_eq_ofReal_wpoly {n d : ℕ} (a : Fin d → Base n → ℂ)
    (a' : Fin d → (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ)
    (hcoeff : ∀ j, a j (ofRealAmbient x).1 =
      ((a' j (fun k => ((ofRealAmbient x).1 k).re) : ℝ) : ℂ)) :
    preparedPolynomial d a (ofRealAmbient x) =
      ((WilkiesDesign.CG.C4a.wpoly a' x : ℝ) : ℂ) := by
  have h1 : preparedPolynomial d a (ofRealAmbient x)
      = preparedPolynomial d (fun j (y : Base n) => ((a' j (fun k => (y k).re) : ℝ) : ℂ))
          (ofRealAmbient x) := by
    simp only [preparedPolynomial]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoeff i])]
  rw [h1, preparedPolynomial_complexify]

theorem real_preparation {n d : ℕ} {G : Ambient n → ℂ} (hG : AnalyticAt ℂ G 0)
    {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg : ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), G (ofRealAmbient x) = (g x : ℂ))
    {a : Fin d → Base n → ℂ} {u : Ambient n → ℂ} (hprep : IsWeierstrassPreparation G d a u) :
    ∃ (a' : Fin d → (Fin n → ℝ) → ℝ) (u' : (Fin (n + 1) → ℝ) → ℝ),
      (∀ j, AnalyticAt ℝ (a' j) 0 ∧ a' j 0 = 0) ∧ AnalyticAt ℝ u' 0 ∧ u' 0 ≠ 0 ∧
      ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), g x = u' x * WilkiesDesign.CG.C4a.wpoly a' x := by
  have hGeq : G =ᶠ[nhds (0 : Ambient n)] fun z => star (G (conjAmb z)) := by
    refine Work.WilC4aRW.Real.eventuallyEq_of_eventuallyEq_ofRealAmbient hG
      (Conj.conj_analytic_ambient hG) ?_
    filter_upwards [hg] with x hx
    rw [conjAmb_ofRealAmbient, hx]
    simp
  have hprep' : IsWeierstrassPreparation G d (fun i y => star (a i (conjVec y)))
      (fun z => star (u (conjAmb z))) :=
    isWeierstrassPreparation_congr hGeq.symm (WPT.prep_conj hprep)
  obtain ⟨haeq, hueq⟩ := isWeierstrassPreparation_unique hprep hprep'
  have hareal : ∀ i, ∀ᶠ y : Fin n → ℝ in nhds (0 : Fin n → ℝ), (a i (cplxIncl y)).im = 0 := by
    intro i
    have hcont : Tendsto (cplxIncl : (Fin n → ℝ) → Fin n → ℂ) (nhds 0) (nhds 0) :=
      (cplxInclCLM n).continuous.tendsto 0
    have h := (haeq i).comp_tendsto hcont
    filter_upwards [h] with y hy
    simp only [Function.comp_apply, conjVec_ofReal] at hy
    exact Complex.conj_eq_iff_im.mp hy.symm
  have hureal : ∀ᶠ x : Fin (n + 1) → ℝ in nhds (0 : Fin (n + 1) → ℝ),
      (u (ofRealAmbient x)).im = 0 := by
    have hcont : Tendsto (ofRealAmbient : (Fin (n + 1) → ℝ) → Ambient n) (nhds 0) (nhds 0) :=
      (ofRealAmbientCLM n).continuous.tendsto 0
    have h := hueq.comp_tendsto hcont
    filter_upwards [h] with x hx
    simp only [Function.comp_apply, conjAmb_ofRealAmbient] at hx
    exact Complex.conj_eq_iff_im.mp hx.symm
  have hainit : ∀ᶠ x : Fin (n + 1) → ℝ in nhds (0 : Fin (n + 1) → ℝ),
      ∀ j, (a j ((ofRealAmbient x).1)).im = 0 := by
    have hcont : Tendsto (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (nhds 0) (nhds 0) :=
      (initCLM n).continuous.tendsto 0
    have hall : ∀ᶠ y : Fin n → ℝ in nhds (0 : Fin n → ℝ), ∀ j, (a j (cplxIncl y)).im = 0 :=
      Filter.eventually_all.mpr hareal
    have h := hcont.eventually hall
    filter_upwards [h] with x hx
    simpa using hx
  have hpoly : ∀ᶠ x : Fin (n + 1) → ℝ in nhds (0 : Fin (n + 1) → ℝ),
      G (ofRealAmbient x) = u (ofRealAmbient x) * preparedPolynomial d a (ofRealAmbient x) := by
    have hcont : Tendsto (ofRealAmbient : (Fin (n + 1) → ℝ) → Ambient n) (nhds 0) (nhds 0) :=
      (ofRealAmbientCLM n).continuous.tendsto 0
    exact hprep.2.2.2.2.comp_tendsto hcont
  let a' : Fin d → (Fin n → ℝ) → ℝ := fun j y => (a j (cplxIncl y)).re
  let u' : (Fin (n + 1) → ℝ) → ℝ := fun x => (u (ofRealAmbient x)).re
  have ha0 : ∀ j, a' j 0 = 0 := fun j => by simp [a', hprep.2.1 j]
  have hu0 : u' 0 ≠ 0 := by
    have h0 : (u (0 : Ambient n)).im = 0 := hureal.self_of_nhds
    intro hcon
    apply hprep.2.2.2.1
    have hc : (u 0).re = 0 := hcon
    rw [show u 0 = ((u 0).re : ℂ) from Complex.ext rfl h0, hc, Complex.ofReal_zero]
  refine ⟨a', u', fun j => ⟨analyticAt_ofRealBase_re (hprep.1 j), ha0 j⟩,
    analyticAt_ofRealAmbient_re hprep.2.2.1, hu0, ?_⟩
  filter_upwards [hg, hureal, hpoly, hainit] with x hgx hux hpx haint
  have hrealinit : ∀ j, (a j (cplxIncl (Fin.init x))).im = 0 := fun j => by
    have := haint j; simpa [ofRealAmbient_fst] using this
  have hux' : u (ofRealAmbient x) = ((u' x : ℝ) : ℂ) := Complex.ext rfl hux
  have hW : preparedPolynomial d a (ofRealAmbient x) =
      ((WilkiesDesign.CG.C4a.wpoly a' x : ℝ) : ℂ) :=
    preparedPolynomial_eq_ofReal_wpoly a a' x (fun j => by
      rw [ofRealAmbient_fst]
      have hk : (fun k => ((cplxIncl (Fin.init x)) k).re) = Fin.init x := by
        funext k; simp [cplxIncl]
      rw [hk]
      exact Complex.ext rfl (hrealinit j))
  have : (g x : ℂ) = ((u' x * WilkiesDesign.CG.C4a.wpoly a' x : ℝ) : ℂ) := by
    rw [← hgx, hpx, hux', hW]
    simp
  exact Complex.ofReal_injective this

end Work.WilC4aRW
