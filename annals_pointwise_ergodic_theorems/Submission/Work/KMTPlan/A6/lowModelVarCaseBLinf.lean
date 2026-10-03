import Mathlib
import Submission.Work.KMTPlan.A6.lowModRandL2F
import Submission.Work.KMTPlan.A6.LinfLowModelVarCaseBLowHigh
import Submission.Work.KMTPlan.A6.LinfLowModelVarCaseBHighLow

namespace Work.KMTPlan.A6

/-! **Case B with the *provable* (bounded-bump) interface `SSUShapeLinf`.**

Same statement as `Work.KMTPlan.A6.lowModelVarCaseB`
(`Submission/Work/KMTPlan/A6/lowModelVarCaseB.lean`, **already PROVED, sorry-free, axiom-clean**,
via `Submission/Work/KMTPlan/A6/LowModelVarCaseBAux.lean` +
`LowModelVarCaseBMain.lean`), except that the interface `SSUShape` is replaced by
`SSUShapeLinf` (definitionally the same body with the two extra hypotheses
`MemLp (periodize φ) ⊤ circleMeasure`, `MemLp (periodize ψ) ⊤ circleMeasure`).

*Why the change is needed*: the tree's `SSUShape` (no boundedness hypothesis on the bumps) is **not
provable** — two independent provers verified that (the `declare_false` verdicts on
`KMTPlan/A6/ssuBandProjectionF` and `KMTPlan/A6/ssuProjZeroGen`); the obstruction is that for a
measurable bump with `iwSymbolSet (diffFreqs ρ l) (periodize φ) ∈ L¹ ∖ L²` the `tsum` defining
`Tm` takes Mathlib's junk value and the two sides of the estimate are not comparable.  The
provable form `SSUShapeLinf` **is** available: `Work.KMTPlan.A6.ssuBtwistExBdd`
(`Submission/Work/KMTPlan/A6/ssuBtwistExBdd.lean`, sorry-free, axiom-clean) has exactly the
`SSUBodyAtLinf` conclusion.

**What to do**: copy `LowModelVarCaseBMain.lean` (168 lines, one declaration whose proof delegates
to `LowModelVarCaseBAux.lean`'s ~800 lines of kernel-level `integ-ident` identities and local
lemmas) into the new module, replace `hSS : Work.KMTPlan.A6.SSUShape P` by
`hSS : Work.KMTPlan.A6.SSUShapeLinf P`, and at **each** application of `hSS` (the SSU single-scale
estimate) discharge the two extra goals `MemLp (periodize φ) ⊤ circleMeasure` and
`MemLp (periodize ψ) ⊤ circleMeasure` for the bumps in question.  The bumps that occur there are the
modulated bumps `varphiNt`, `varphitildeNt` and their polynomial modifications
`varphiNtj`/`varphitildeNtj`, plus `randSymb` combinations of them — all essentially bounded.
Available facts: `Work.KMTAreas.A7.kmtA7_memLp_periodize_varphiNt`,
`…kmtA7_memLp_periodize_varphitildeNt` (`Submission/Work/KMTAreas/A7/kmtA7_periodize_bumps_memLp.lean`)
for the two base bumps, `Work.Analysis.IonescuWainger.memLp_periodize` for the closure, and
`MeasureTheory.MemLp` closure under finite sums/differences/scalar multiples.  If a bump is the
*randomised* symbol `Work.KMTAreas.A7.randSymb Φ ε K` (a finite linear combination of the `Φ k`),
prove the `MemLp ⊤` fact for the combination directly (that is short). -/
theorem lowModelVarCaseBLinf (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hSS : Work.KMTPlan.A6.SSUShapeLinf P) :
    Work.KMTPlan.A6.LowModelCaseBShape P r C₀ := by
  classical
  obtain ⟨cS, hcS, ρ₀s, hρ₀s, hSSb⟩ := Work.KMTPlan.A6.exists_ssuBodyAtLinf_of_ssuShapeLinf hSS
  obtain ⟨ρ₀F, hρ₀F, hFb⟩ := Work.KMTPlan.A6.lowModRandL2F P C₀
  obtain ⟨ρ₀G, hρ₀G, hGb⟩ := Work.KMTPlan.A6.lowModRandL2G_of' hd hA1 hC₀
    (Work.KMTPlan.A6.lowModRandL2Gh P hd hA1 C₀ hC₀)
  obtain ⟨⟨Cb, hCb, hCbb⟩, _hCbz⟩ := Work.KMTPlan.A6.varphitildeNtjPointwise P hd
  refine ⟨min cS 1 / 2, by positivity,
    min (min ρ₀s (min ρ₀F ρ₀G)) (1 / (8 * (C₀ : ℝ))),
    lt_min (lt_min hρ₀s (lt_min hρ₀F hρ₀G)) (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρs : ρ ≤ ρ₀s := by
    have h2 : min (min ρ₀s (min ρ₀F ρ₀G)) (1 / (8 * (C₀ : ℝ)))
        ≤ min ρ₀s (min ρ₀F ρ₀G) := min_le_left _ _
    have h3 : min ρ₀s (min ρ₀F ρ₀G) ≤ ρ₀s := min_le_left _ _
    linarith
  have hρF : ρ ≤ ρ₀F := by
    have h2 : min (min ρ₀s (min ρ₀F ρ₀G)) (1 / (8 * (C₀ : ℝ)))
        ≤ min ρ₀s (min ρ₀F ρ₀G) := min_le_left _ _
    have h3 : min ρ₀s (min ρ₀F ρ₀G) ≤ min ρ₀F ρ₀G := min_le_right _ _
    have h4 : min ρ₀F ρ₀G ≤ ρ₀F := min_le_left _ _
    linarith
  have hρG : ρ ≤ ρ₀G := by
    have h2 : min (min ρ₀s (min ρ₀F ρ₀G)) (1 / (8 * (C₀ : ℝ)))
        ≤ min ρ₀s (min ρ₀F ρ₀G) := min_le_left _ _
    have h3 : min ρ₀s (min ρ₀F ρ₀G) ≤ min ρ₀F ρ₀G := min_le_right _ _
    have h4 : min ρ₀F ρ₀G ≤ ρ₀G := min_le_right _ _
    linarith
  have hρC : ρ ≤ 1 / (8 * (C₀ : ℝ)) := by
    have h2 : min (min ρ₀s (min ρ₀F ρ₀G)) (1 / (8 * (C₀ : ℝ)))
        ≤ 1 / (8 * (C₀ : ℝ)) := min_le_right _ _
    linarith
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀ : 0 < C₀)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8 := by
    calc ρ * (C₀ : ℝ) ≤ (1 / (8 * (C₀ : ℝ))) * (C₀ : ℝ) :=
          mul_le_mul_of_nonneg_right hρC hC₀0.le
      _ = 1 / 8 := by field_simp
  have hρ8 : 8 * ρ ≤ 1 := by
    have h1 : 1 / (8 * (C₀ : ℝ)) ≤ 1 / 8 := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      have h2 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
      linarith
    linarith
  obtain ⟨Cssu, hCssu, hSSρ⟩ := hSSb ρ hρ hρs
  obtain ⟨B₁, C₁, hFbody⟩ := hFb ρ hρ hρF
  obtain ⟨B₂, C₂, hGbody⟩ := hGb ρ hρ hρG
  have hFmono : Work.KMTPlan.A6.LowModRandL2FBody P C₀ ρ (max B₁ B₂)
      (fun Λ => max (C₁ Λ) (C₂ Λ)) := by
    intro a Λ l₁ l₂ k₁ k₂ K t j ε f hΛ hlac ha1 hε ht hj hkj hBL hf
    refine (hFbody a Λ l₁ l₂ k₁ k₂ K t j ε f hΛ hlac ha1 hε ht hj hkj
      (le_trans (le_max_left _ _) hBL) hf).trans ?_
    refine mul_le_mul' ?_ le_rfl
    exact_mod_cast (le_max_left (C₁ Λ) (C₂ Λ))
  have hGmono : Work.KMTPlan.A6.LowModRandL2GBody P C₀ ρ (max B₁ B₂)
      (fun Λ => max (C₁ Λ) (C₂ Λ)) := by
    intro a Λ l₁ l₂ k₁ k₂ K t j ε g hΛ hlac ha1 hε ht hj hkj hBL hg
    refine (hGbody a Λ l₁ l₂ k₁ k₂ K t j ε g hΛ hlac ha1 hε ht hj hkj
      (le_trans (le_max_right _ _) hBL) hg).trans ?_
    refine mul_le_mul' ?_ le_rfl
    exact_mod_cast (le_max_right (C₁ Λ) (C₂ Λ))
  obtain ⟨Cc₁, Bc₁, h1⟩ := Work.KMTPlan.A6.Linf.lowModelVarCaseBLowHighLinf P hd r hr hA1 ρ hρ hρ8
    C₀ hC₀ hρC₀ hcS hSSρ (max B₁ B₂) (fun Λ => max (C₁ Λ) (C₂ Λ)) hFmono hGmono hCb hCbb
  obtain ⟨Cc₂, Bc₂, h2⟩ := Work.KMTPlan.A6.Linf.lowModelVarCaseBHighLowLinf P hd r hr hA1 ρ hρ hρ8
    C₀ hC₀ hρC₀ hcS hSSρ (max B₁ B₂) (fun Λ => max (C₁ Λ) (C₂ Λ)) hFmono hGmono hCb hCbb
  refine ⟨fun Λ => max (Cc₁ Λ) (Cc₂ Λ), max Bc₁ Bc₂, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ hlac ha1 hk hBL hmaxlt hwin hf hg
  rcases hk with hk1 | hk2
  · subst hk1
    have hlc : Work.KMTPlan.A6.lcL l₁ l₂ 0 k₂ = k₂ := by
      have h : max l₁ l₂ < max (max l₁ l₂) k₂ := by
        have h0 := hmaxlt
        rw [Work.KMTPlan.A6.lcL] at h0
        simpa only [max_eq_right (Nat.zero_le k₂)] using h0
      have h' : max l₁ l₂ < k₂ := by
        rcases lt_max_iff.mp h with h1 | h1
        · exact absurd h1 (lt_irrefl _)
        · exact h1
      rw [Work.KMTPlan.A6.lcL, max_eq_right (Nat.zero_le k₂)]
      exact max_eq_right (le_of_lt h')
    have hmaxlt' : max l₁ l₂ < k₂ := hlc ▸ hmaxlt
    have hBc1 : Bc₁ ≤ k₂ := by
      have h2' : max Bc₁ Bc₂ ≤ k₂ := le_trans hBL (le_of_eq hlc)
      exact le_trans (le_max_left _ _) h2'
    refine (h1 a Λ l₁ l₂ k₂ f g hΛ hlac ha1 hmaxlt' hBc1 hf hg).trans ?_
    refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl) le_rfl
    exact_mod_cast (le_max_left (Cc₁ Λ) (Cc₂ Λ) :
      Cc₁ Λ ≤ max (Cc₁ Λ) (Cc₂ Λ))
  · subst hk2
    have hlc : Work.KMTPlan.A6.lcL l₁ l₂ k₁ 0 = k₁ := by
      have h : max l₁ l₂ < max (max l₁ l₂) k₁ := by
        have h0 := hmaxlt
        rw [Work.KMTPlan.A6.lcL] at h0
        simpa only [max_eq_left (Nat.zero_le k₁)] using h0
      have h' : max l₁ l₂ < k₁ := by
        rcases lt_max_iff.mp h with h1 | h1
        · exact absurd h1 (lt_irrefl _)
        · exact h1
      rw [Work.KMTPlan.A6.lcL, max_eq_left (Nat.zero_le k₁)]
      exact max_eq_right (le_of_lt h')
    have hmaxlt' : max l₁ l₂ < k₁ := hlc ▸ hmaxlt
    have hBc2 : Bc₂ ≤ k₁ := by
      have h2' : max Bc₁ Bc₂ ≤ k₁ := le_trans hBL (le_of_eq hlc)
      exact le_trans (le_max_right _ _) h2'
    refine (h2 a Λ l₁ l₂ k₁ f g hΛ hlac ha1 hmaxlt' hBc2 hf hg).trans ?_
    refine mul_le_mul' (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl) le_rfl
    exact_mod_cast (le_max_right (Cc₁ Λ) (Cc₂ Λ) :
      Cc₂ Λ ≤ max (Cc₁ Λ) (Cc₂ Λ))


end Work.KMTPlan.A6
