import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.MAnalytic.Basic
import Submission.Work.TMComp.MAnalytic.Conj
import Submission.Work.TMComp.MAnalytic.kotani_M_section_of_lt
import Submission.Work.TMComp.MAnalytic.analytic_kotani_section
import Submission.Work.TMComp.prove_BJ
import Submission.Work.TMComp.C9Aux.P_Kotani_own

/-! Guidance from the project lead (the requester):

Component C9 (P_mAnalytic) of the Ten Martini formalisation. The FROZEN statement is Work.TMContract.P_mAnalytic (Submission/Work/TMContract/Components.lean; definitions in TMContract/Defs.lean; read TMContract/README.md). The proof route for C9 is in Submission/Work/TMPlan/ROUTE_LEAD.md (find the section for C9); the source is Avila–Jitomirskaya, The Ten Martini Problem (arXiv math/0503363), plus the references ROUTE_LEAD cites. Any other component's P_* that ROUTE_LEAD lists as an input for C9 may be taken as a HYPOTHESIS inside your proof only if P_mAnalytic's own statement takes it; otherwise prove what you need. Decompose into lemmas right away and dispatch them in parallel with request_lemma (request_review first if unsure a statement is true). Keep every build small; no hour-long files.
-/

/-!
# C9 = `P_mAnalytic`: analytic conjugacy to rotations on a spectral interval

The frozen statement asks: for irrational `α`, `0 < λ ≤ 1` and an interval `(a,b)` contained in
the spectrum `Σ_{λ,α}`, there are `C, φ`, jointly real-analytic on `(a,b) × ℝ`, 1-periodic in
`x`, `det C_E = 1`, `deg C_E = 0`, with `C_E(x+α) S_{λ,E}(x) = R_{φ(E,x)} C_E(x)`.

Route (AJ Thm 3.1, 3.2, Lemma 2.3, (4.11)–(4.13)):

* **Inputs.** C7 (`P_BJ`) gives `L = 0` on `(a,b)` (since `0 < λ ≤ 1`); C8 (`P_Kotani`) then
  continues the `m`-function across `(a,b)`; AJ Thm 3.1/3.2 + Lemma 2.3 upgrade the regularity
  of `m` to joint real-analyticity on `(a,b) × ℝ` (the "section" of `MAnalytic/AnalyticSection`).
* **Construction.** `Submission/Work/TMComp/MAnalytic/Conj.lean` proves, from any such section,
  the existence of `C, φ` with all the required properties
  (`Work.TMComp.MAnalytic.exists_conj_of_analyticSection`).

This file assembles those two halves.  This module contains

* `lyap_eq_zero_of_mem_Ioo`: C7 restricted to `0 < λ ≤ 1` (`L = 0` on the spectral interval),
* `prove_mAnalytic_of_section`: C9 from *any* provider of the invariant section on the interval.
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract Set Filter Topology

noncomputable section

namespace Work.TMComp

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
theorem prove_mAnalytic_of_section
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
theorem prove_mAnalytic_of_inputs (hBJ : P_BJ) (hKot : P_Kotani)
    (hanaOf : ∀ (α lam a b : ℝ) (h0 : 0 < lam) (hab : a < b) (M : ℂ → ℝ → ℂ),
      ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ univ) →
      (∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b)) →
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) →
      (∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x) →
      (∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x) →
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, M z (x + α) = mob (tmC lam z x) (M z x)) →
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => M p.1 p.2) (Ioo a b ×ˢ univ)) :
    P_mAnalytic := by
  refine prove_mAnalytic_of_section fun α lam a b hα h0 h1 hab hsub => ?_
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
theorem prove_mAnalytic_of_BJ_Kotani (hBJ : P_BJ) (hKot : P_Kotani) : P_mAnalytic :=
  prove_mAnalytic_of_inputs hBJ hKot fun α lam a b h0 hab M hcont hhol him hamoM hper hsec =>
    Work.TMComp.MAnalytic.analytic_kotani_section h0 hab hcont hhol him hamoM hper hsec

/-- The requested statement, `Work.TMContract.P_mAnalytic`.

Everything specific to C9 is proved: the (4.11)–(4.13) construction
(`MAnalytic.exists_conj_of_analyticSection`), the invariant section on a spectral interval
(`MAnalytic.kotani_M_section_of_lt`, `MAnalytic.analytic_kotani_section`), the passage from
Bourgain–Jitomirskaya to `lyap = 0` on the interval (`lyap_eq_zero_of_mem_Ioo`), and the
assembly `prove_mAnalytic_of_BJ_Kotani`.

The frozen statement takes no hypotheses, so its two components are imported as black boxes:

* **C8** `Work.TMComp.C9Aux.P_Kotani_own` — assembled inside C9's own area
  (`Submission/Work/TMComp/C9Aux/P_Kotani_own.lean`) from the proved halves of the Kotani
  continuation (`RedC8.ae_jump_of_lyap_eq_zero`, `RedC8.exists_local_continuation_of_ae_jump`)
  and `Kotani.kotani_core_of_local` / `Kotani.prove_Kotani_of_core`.  Axiom-clean: C8 is done.
* **C7** `Work.TMComp.prove_BJ` — proved and axiom-clean
  (`Submission/Work/TMComp/prove_BJ.lean`), via
  `Work.TMC7Core.Scale.p_bj_of_dichotomy` and the three vocabulary bridges.  That assembly is
  the dichotomy route of `TMC7Core/C7_INPUTS_LEAD.md`: Case I (Liouville) uses S3
  `liouville_approx` + S4 `qsc` + S5 `rat_bound_phase` with the crude Lipschitz transfer, and
  Case II (Diophantine) uses S2 `conv_chain_rational` + the finite rational tower S1
  `rat_tower_lower`.  An independent assembly of the same component,
  `Work.TMComp.C9Aux.P_BJ_own`, exists in this area and is superseded.

Both sides are clean: `#print axioms Work.TMComp.prove_mAnalytic` =
`[propext, Classical.choice, Quot.sound]`. -/
theorem prove_mAnalytic : Work.TMContract.P_mAnalytic :=
  prove_mAnalytic_of_BJ_Kotani Work.TMComp.prove_BJ Work.TMComp.C9Aux.P_Kotani_own

end Work.TMComp
