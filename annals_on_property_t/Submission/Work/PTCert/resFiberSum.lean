import Mathlib
import Submission.Work.PTCert.labelData

namespace Work.PTCert

/-! Guidance from the project lead (the requester): this is the per-label residual sum in the proof of
`LabelIdentity` (`Submission/Work/PTCert/labelIdentity.lean`).  Read
`Submission/Work/PTCert/labelData.lean` (`icls_lt`, `icls`, `ncls`).

`residualSum` contributes, for each class `c < ncls`, the two terms `of (lprod 5 (canonW c))` (label
`c`) and `of ((lprod 5 (canonW c))⁻¹)` (label `icls c`), each with coefficient `res c/(SCv·Dq)/2`.
So the total coefficient carried by the label `l` is `res l/den/2 + res (icls l)/den/2 = res l/den`
(one term for each sign), where the second equality uses `hres` (and `LabelData.icls_lt hC` to know `icls l` is
in range); for `l ≥ ncls` there are no terms at all (the `true`-terms have label `icls c < ncls`).

Intended route: `Fintype.sum_prod_type` splits `Σ x : Fin ncls × Bool` into the two `Bool` cases,
`Finset.sum_ite_eq'` collapses `Σ_{c : Fin ncls} (if c.1 = l then f c else 0)` to `f ⟨l, hl⟩` (and to
`0` when `l ≥ ncls`), and the `true` branch is reindexed by the involution `c ↦ icls c` on `Fin ncls`
(`icls (icls c) = c` for `c < ncls` from `hres`, so `icls c = l ↔ c = icls l`).

Do NOT unfold the data tables (`canonW`, …) and do not use `decide` on them. -/

open Submission.PTCert Submission.PTCert.G
open scoped BigOperators

theorem resFiberSum (hC : ClassSem) (res : ℕ → ℤ) (den : ℝ) (l : ℕ)
    (hres : ∀ c < ncls, res (icls c) = res c ∧ icls (icls c) = c) :
    (∑ x : Fin ncls × Bool,
        (if (if x.2 then icls x.1.1 else x.1.1) = l then ((res x.1.1 : ℝ) / den / 2) else 0))
      = if l < ncls then (res l : ℝ) / den else 0 := by
  -- The `false` branch of the `Bool` split: `Σ_c [c = l] · res c/den/2`.
  have hS0 : (∑ c : Fin ncls, (if c.1 = l then ((res c.1 : ℝ) / den / 2) else 0))
      = if l < ncls then (res l : ℝ) / den / 2 else 0 := by
    by_cases hl : l < ncls
    · rw [if_pos hl]
      have h1 := Fintype.sum_eq_single (⟨l, hl⟩ : Fin ncls)
        (f := fun c : Fin ncls => if c.1 = l then ((res c.1 : ℝ) / den / 2) else 0)
        (fun c hc => by rw [if_neg]; intro h; exact hc (Fin.ext h))
      simpa using h1
    · rw [if_neg hl]
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg]
      intro h
      exact hl (h ▸ c.2)
  -- The `true` branch equals the `false` branch, by reindexing along the involution `icls`.
  have hS1 : (∑ c : Fin ncls, (if icls c.1 = l then ((res c.1 : ℝ) / den / 2) else 0))
      = (∑ c : Fin ncls, (if c.1 = l then ((res c.1 : ℝ) / den / 2) else 0)) := by
    apply Finset.sum_bij (fun c _ => (⟨icls c.1, LabelData.icls_lt hC c.2⟩ : Fin ncls))
    · intro a ha; simp
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.ext
      have h' : icls a₁.1 = icls a₂.1 := by
        have := congrArg Fin.val h; simpa using this
      have h2 : icls (icls a₁.1) = icls (icls a₂.1) := congrArg icls h'
      rw [(hres a₁.1 a₁.2).2, (hres a₂.1 a₂.2).2] at h2
      exact h2
    · intro b hb
      exact ⟨(⟨icls b.1, LabelData.icls_lt hC b.2⟩ : Fin ncls), Finset.mem_univ _, by
        apply Fin.ext; simp only; exact (hres b.1 b.2).2⟩
    · intro a ha
      show (if icls a.1 = l then ((res a.1 : ℝ) / den / 2) else 0)
          = (if (icls a.1) = l then ((res (icls a.1) : ℝ) / den / 2) else 0)
      rw [(hres a.1 a.2).1]
  rw [Fintype.sum_prod_type]
  -- Split each inner `Bool` sum into its two values.
  have hb : ∀ c : Fin ncls,
      (∑ b : Bool, (if (if b then icls c.1 else c.1) = l then ((res c.1 : ℝ) / den / 2) else 0))
      = (if icls c.1 = l then ((res c.1 : ℝ) / den / 2) else 0)
        + (if c.1 = l then ((res c.1 : ℝ) / den / 2) else 0) := by
    intro c
    rw [Fintype.sum_bool]
    simp
  simp only [hb]
  rw [Finset.sum_add_distrib, hS1, hS0]
  by_cases hl : l < ncls
  · rw [if_pos hl, if_pos hl]
    ring
  · rw [if_neg hl, if_neg hl]
    ring

end Work.PTCert
