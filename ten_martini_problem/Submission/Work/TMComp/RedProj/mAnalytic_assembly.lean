import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.MAnalytic.Basic
import Submission.Work.TMComp.MAnalytic.Conj
import Submission.Work.TMComp.MAnalytic.kotani_M_section_of_lt
import Submission.Work.TMComp.RedProj.aks_section

/-!
# C9 (`P_mAnalytic`) — assembly, forked into `Work.TMComp.RedProj`

This is a verbatim copy of `Submission/Work/TMComp/prove_mAnalytic.lean` with the namespace
changed to `Work.TMComp.RedProj` and the analytic input `analytic_kotani_section` taken from the
fork `Submission/Work/TMComp/RedProj/aks_section.lean`, which replaces the three currently
unproved analytic inputs of `MAnalytic`

* `MAnalytic.propagate_smallness`  ↔ `Work.RedProj.growth_propagation`,
* `MAnalytic.amoM_strip_cayley`    ↔ `Work.RedProj.amoM_cayley_strip`,
* `MAnalytic.separately_holomorphic_real_analytic`
                                   ↔ `Work.RedProj.separately_holomorphic_analytic`,

by the corresponding lemmas proved in `Submission/Work/RedProj/`.  It exists so that component
C11 (`Work.TMComp.prove_Reducibility`) can be closed from C7 (`P_BJ`) and C8 (`P_Kotani`) alone,
independently of the state of `MAnalytic`; the statements are identical, so the fork can be
dropped and C9's own file used instead as soon as that file is sorry-free.
-/
open LeanEval.Analysis.TenMartini
open Work.TMContract Set Filter Topology

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- **C7 on a spectral interval for `0 < λ ≤ 1`.**  Bourgain–Jitomirskaya gives
`L(E) = max 0 (log |λ|)` on the spectrum; for `0 < λ ≤ 1` this is `0`. -/
theorem lyap_eq_zero_of_mem_Ioo (hBJ : P_BJ) {α lam : ℝ} (hα : Irrational α) (h0 : 0 < lam)
    (h1 : lam ≤ 1) {a b E : ℝ} (hsub : Ioo a b ⊆ amoSpec α lam) (hE : E ∈ Ioo a b) :
    lyap α lam (E : ℂ) = 0 := by
  have hne : lam ≠ 0 := ne_of_gt h0
  have := hBJ α lam hα hne E (hsub hE)
  have hlog : Real.log |lam| ≤ 0 := by
    rw [abs_of_pos h0]
    exact Real.log_nonpos h0.le h1
  rw [this, max_eq_left hlog]

/-- **C9 from a provider of the invariant section.**  If some `m : (a,b) × ℝ → ℍ` is a jointly
real-analytic invariant section of the almost Mathieu cocycle on the spectral interval `(a,b)`,
then the frozen conclusion of `P_mAnalytic` holds.  (The construction is
`Work.TMComp.MAnalytic.exists_conj_of_analyticSection`; the analytic input is isolated here.) -/
theorem mAnalytic_of_section
    (hsection : ∀ (α lam a b : ℝ), Irrational α → 0 < lam → lam ≤ 1 → a < b →
      Ioo a b ⊆ amoSpec α lam →
      ∃ m : ℝ → ℝ → ℂ, Work.TMComp.MAnalytic.AnalyticSection α lam a b m) :
    P_mAnalytic := by
  intro α lam a b hα h0 h1 hab hsub
  obtain ⟨m, hm⟩ := hsection α lam a b hα h0 h1 hab hsub
  exact Work.TMComp.MAnalytic.exists_conj_of_analyticSection hm


/-- **Assembly**: the invariant section on `(a,b) × ℝ`, from Kotani's `m`-function `M` together
with (i) the section equation on the continued domain and (ii) its joint real-analyticity on
`(a,b) × ℝ`.  The section equation enters through `secEq_iff_mob`. -/
theorem analyticSection_of_M {α lam a b : ℝ} (hα : Irrational α) {M : ℂ → ℝ → ℂ}
    (hana : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => M p.1 p.2) (Ioo a b ×ˢ univ))
    (him : ∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im)
    (hper : ∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x)
    (hsec : ∀ z ∈ kotaniDomain a b, ∀ x : ℝ,
      M z (x + α) = mob (tmC lam z x) (M z x)) :
    ∃ m : ℝ → ℝ → ℂ, Work.TMComp.MAnalytic.AnalyticSection α lam a b m := by
  refine ⟨fun E x => M (E : ℂ) x, ?_, ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_re, Complex.ofReal_im] using hana
  · intro E hE x
    exact him (E : ℂ) (Or.inr ⟨by simp, by simpa using hE.1, by simpa using hE.2⟩) x
  · intro E x
    exact hper (E : ℂ) x
  · intro E hE x
    have hmem : (E : ℂ) ∈ kotaniDomain a b :=
      Or.inr ⟨by simp, by simpa using hE.1, by simpa using hE.2⟩
    have hmob := hsec (E : ℂ) hmem x
    have hne : M (E : ℂ) x ≠ 0 := by
      have := him (E : ℂ) hmem x
      intro h0; rw [h0] at this; simp at this
    exact (Work.TMComp.MAnalytic.secEq_iff_mob hne).mpr hmob.symm

/-- **C9 from C7, C8 and the two analytic inputs.**  Given Bourgain–Jitomirskaya (`P_BJ`, giving
`L = 0` on the spectral interval) and Kotani (`P_Kotani`, giving the `m`-function continued across
the interval), together with

* `hsecOf`: the section equation for the continued `m`-function on `kotaniDomain`,
* `hanaOf`: joint real-analyticity of the continued `m`-function on `(a,b) × ℝ`
  (AJ Thm 3.1/3.2 + Lemma 2.3),

the frozen statement `P_mAnalytic` holds. -/
theorem mAnalytic_of_inputs (hBJ : P_BJ) (hKot : P_Kotani)
    (hanaOf : ∀ (α lam a b : ℝ) (h0 : 0 < lam) (hab : a < b) (M : ℂ → ℝ → ℂ),
      ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ univ) →
      (∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b)) →
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) →
      (∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x) →
      (∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x) →
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, M z (x + α) = mob (tmC lam z x) (M z x)) →
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => M p.1 p.2) (Ioo a b ×ˢ univ)) :
    P_mAnalytic := by
  refine mAnalytic_of_section fun α lam a b hα h0 h1 hab hsub => ?_
  have hlyap : ∀ E ∈ Ioo a b, lyap α lam (E : ℂ) = 0 :=
    fun E hE => lyap_eq_zero_of_mem_Ioo hBJ hα h0 h1 hsub hE
  obtain ⟨M, hcont, hhol, him, hamoM, hper⟩ := hKot α lam a b hα (le_of_lt h0) hab hlyap
  have hsec := Work.TMComp.MAnalytic.kotani_M_section_of_lt h0 hab hcont hhol hamoM him hper
  have hana := hanaOf α lam a b h0 hab M hcont hhol him hamoM hper hsec
  exact analyticSection_of_M hα hana him hper hsec


/-- **C9 from C7 and C8.**  With `P_BJ` (Bourgain–Jitomirskaya) and `P_Kotani` (Kotani theory)
available as theorems, the invariant section on the spectral interval is produced by
`kotani_M_section_of_lt` (the section relation) and `analytic_kotani_section` (joint
real-analyticity, AJ Thm 3.1/3.2 + Lemma 2.3, proved in the `MAnalytic` subproject). -/
theorem mAnalytic_of_BJ_Kotani (hBJ : P_BJ) (hKot : P_Kotani) : P_mAnalytic :=
  mAnalytic_of_inputs hBJ hKot fun α lam a b h0 hab M hcont hhol him hamoM hper hsec =>
    Work.TMComp.RedProj.analytic_kotani_section h0 hab hcont hhol him hamoM hper hsec

end Work.TMComp.RedProj
