import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.MAnalytic.Basic
import Submission.Work.TMComp.MAnalytic.Conj
import Submission.Work.TMComp.MAnalytic.kotani_M_section_of_lt
import Submission.Work.TMComp.RedProj.aks_section
import Submission.Work.TMComp.RedProj.mAnalytic_assembly

/-!
# C9 (`P_mAnalytic`) restricted to frequencies that are Diophantine with *some* constant

C11 (`P_Reducibility`) carries `DiophBelow` hypotheses and consumes `P_mAnalytic` only through
`RedProj.Extract.joint_analytic_of_mAnalytic`, at the frequencies of its two conjuncts:

* conjunct 1 (`β(α) = 0`) has `∀ b > 0, DiophBelow α b`;
* conjunct 2 (the null-or-interval dichotomy) has a **single** `DiophBelow α b₀` with `b₀ > 0`.

So only the Diophantine case of C7 (`P_BJ`) is needed, in the form: for every `b₀ > 0` and every
`α` with `DiophBelow α b₀`.  This file records that restricted form of C9.

The proof is the one of `RedProj.mAnalytic_of_BJ_Kotani` with the frequency hypothesis
`DiophBelow α b₀` carried along; `P_BJ` is used only to conclude `lyap = 0` on the spectral
interval `(a,b)` **at the given frequency** (whose `DiophBelow`-constant can be chosen freely
there, since `DiophBelow α b` is antitone in `b`).
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract Set Filter Topology

noncomputable section

namespace Work.TMComp.RedC7T

open Work.TMContract

/-- **The Diophantine case of C7 on a spectral interval for `0 < λ ≤ 1`.**  A
Diophantine-only Bourgain--Jitomirskaya gives `L(E) = max 0 (log |λ|)` on the spectrum; for
`0 < λ ≤ 1` this is `0`. -/
theorem lyap_eq_zero_of_mem_Ioo_dioph
    (hBJ : ∀ (α lam : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 →
      ∀ E ∈ amoSpec α lam, lyap α lam (E : ℂ) = max 0 (Real.log |lam|))
    {α lam : ℝ} (hα : Irrational α) {b₀ : ℝ} (hb₀ : 0 < b₀) (hD : DiophBelow α b₀)
    (h0 : 0 < lam) (h1 : lam ≤ 1) {a b E : ℝ} (hsub : Ioo a b ⊆ amoSpec α lam)
    (hE : E ∈ Ioo a b) : lyap α lam (E : ℂ) = 0 := by
  have hne : lam ≠ 0 := ne_of_gt h0
  have := hBJ α lam b₀ hα hb₀ hD hne E (hsub hE)
  have hlog : Real.log |lam| ≤ 0 := by
    rw [abs_of_pos h0]
    exact Real.log_nonpos h0.le h1
  rw [this, max_eq_left hlog]

/-- **C9 restricted to frequencies Diophantine with some constant, from C7 and C8.** -/
theorem mAnalytic_dioph
    (hBJ : ∀ (α lam : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 →
      ∀ E ∈ amoSpec α lam, lyap α lam (E : ℂ) = max 0 (Real.log |lam|))
    (hKot : P_Kotani) :
    ∀ (α lam a b : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → 0 < lam →
      lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
      ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
        (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
        AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
        (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
        (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
        (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
        (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x) := by
  intro α lam a b b₀ hα hb₀ hD h0 h1 hab hsub
  have hlyap : ∀ E ∈ Ioo a b, lyap α lam (E : ℂ) = 0 :=
    fun E hE => lyap_eq_zero_of_mem_Ioo_dioph hBJ hα hb₀ hD h0 h1 hsub hE
  obtain ⟨M, hcont, hhol, him, hamoM, hper⟩ := hKot α lam a b hα (le_of_lt h0) hab hlyap
  have hsec := Work.TMComp.MAnalytic.kotani_M_section_of_lt h0 hab hcont hhol hamoM him hper
  have hana := Work.TMComp.RedProj.analytic_kotani_section h0 hab hcont hhol him hamoM hper hsec
  obtain ⟨m, hm⟩ := Work.TMComp.RedProj.analyticSection_of_M hα hana him hper hsec
  exact Work.TMComp.MAnalytic.exists_conj_of_analyticSection hm

end Work.TMComp.RedC7T
