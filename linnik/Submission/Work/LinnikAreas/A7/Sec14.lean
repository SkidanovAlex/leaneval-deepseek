/-
# Area 7 — the §14 branch (`λ₁ < 0.348`)

Instantiates `Work.A7.core14` with the row data of `rows14` (Deuring–Heilbronn) and the
logarithmic repulsion, then closes the bracket with the §14 numeric estimates, supplied by the
caller as the two hypotheses `hnum_rows` (the four explicit rows, cf. `Work.A7.sec14_num_rows`)
and `hnum_repel` (the repulsion case, cf. `Work.A7.sec14_num_repel`).
-/
import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.A7.core14
import Submission.Work.A7.box_api7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

/-- The shape of `core14`'s conclusion (its right-hand side), used as the interface for the
numeric closing. -/
def core14RHS (c η εw lam : ℝ) : ℝ :=
  ((9:ℝ)/100) * (Real.exp (-(ac*lam)) * (((1 - Real.exp (-((3:ℝ)/10*lam)))/lam)^2/((9:ℝ)/100))
    + Real.exp (-(ac*c)) * (Bfun ((3:ℝ)/10) lam + η)
    + (Phi c / Wf c) * ((67:ℝ)/6 + εw))
  + ((9:ℝ)/100) * η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1)

/-- **§14 branch of the assembly.**  If `λ₁ = λ(ρ₁) < 0.348` for the minimal pair `(χ₁,ρ₁)`, then the
total box sum over `Aset q R` is at most `(9/100)·(1 - λ₁/9)`. -/
theorem sec14_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R lamS η εw lam : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw)
    (hη1 : η ≤ 1/100000000) (hη2 : η ≤ lamS/10)
    (hlamS0 : 0 < lamS) (hnotSiegel : ¬ SiegelZero q lamS)
    (hmin : IsMin1 χ₁ ρ₁) (hlam : lamOf q ρ₁ = lam) (hlam0 : 0 < lam)
    (hlam348 : lam < (348:ℝ)/1000)
    (hZ1 : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ zeroMult χ₁ ρ₁ = 1 ∧
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) → (348:ℝ)/1000 ≤ lamOf q ρ))
    (h14rows : ∀ r ∈ rows14, lamS ≤ lamOf q ρ₁ → r.1 ≤ lamOf q ρ₁ → lamOf q ρ₁ < r.2.1 →
      Lam0Bound χ₁ ρ₁ r.2.2 ∧ Lam2Bound χ₁ r.2.2)
    (h14repel : lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ < 2/10 →
      Lam0Bound χ₁ ρ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)) ∧
      Lam2Bound χ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ, χ ∈ hS ↔ ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
      (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
      boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hnum_rows : ∀ c : ℝ, ((c = 127/100 ∧ 3/10 ≤ lam) ∨ (c = 141/100 ∧ 25/100 ≤ lam ∧ lam ≤ 3/10)
        ∨ (c = 158/100 ∧ 2/10 ≤ lam ∧ lam ≤ 25/100) ∨ (c = 18/10 ∧ 2/100 ≤ lam ∧ lam ≤ 2/10)) →
      Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2
        + Real.exp (-(ac*c)) * (Bfun Kc lam + η)
        + (Phi c / Wf c) * ((67:ℝ)/6 + εw)
        + η * ((Real.exp (-(ac*c)) / Wf c) * ((67:ℝ)/6 + εw) + 1) ≤ 1 - lam/9)
    (hnum_repel : Real.exp (-(ac*lam)) * ((1 - Real.exp (-(Kc*lam)))/lam)^2 / K2
        + Real.exp (-(ac * (99/100 * Real.log (1/lam)))) * (Bfun Kc lam + η)
        + (Phi (99/100 * Real.log (1/lam)) / Wf (99/100 * Real.log (1/lam))) * ((67:ℝ)/6 + εw)
        + η * ((Real.exp (-(ac * (99/100 * Real.log (1/lam)))) / Wf (99/100 * Real.log (1/lam)))
            * ((67:ℝ)/6 + εw) + 1) ≤ 1 - lam/9) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (1 - lam/9) := by
  classical
  have hlam1 : lam < 1 := by linarith
  have hSle : lamS ≤ lamOf q ρ₁ :=
    Work.A7.box_api7_p4 (q := q) hmin.1.1 hZ1.1 hZ1.2.1 hZ1.2.2.1 hnotSiegel hq
      (by rw [hlam]; linarith)
  have hSle' : lamS ≤ lam := by rw [← hlam]; exact hSle
  -- the interface to `core14`
  have hcore : ∀ c : ℝ, 0 < c → Lam0Bound χ₁ ρ₁ c → Lam2Bound χ₁ c →
      core14RHS c η εw lam ≤ ((9:ℝ)/100) * (1 - lam/9) →
      ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (1 - lam/9) := by
    intro c hcpos hl0 hl2 hnum
    exact le_trans (Work.A7.core14 (q := q) hq (R := R) (c := c) (η := η) (εw := εw) (lam := lam)
      hR hRlog hRmax hη hcpos hmin hlam hlam0 hZ1 hl0 hl2 hS hSiff hD1 hPC) hnum
  have hmem1 : ((3:ℝ)/10, (348:ℝ)/1000, (127:ℝ)/100) ∈ rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem2 : ((25:ℝ)/100, (3:ℝ)/10, (141:ℝ)/100) ∈ rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem3 : ((2:ℝ)/10, (25:ℝ)/100, (158:ℝ)/100) ∈ rows14 := by
    simp [Work.LinnikContract.rows14]
  have hmem4 : ((0:ℝ), (2:ℝ)/10, (18:ℝ)/10) ∈ rows14 := by
    simp [Work.LinnikContract.rows14]
  rcases lt_or_ge lam (2/100) with hlt | hge
  · -- repulsion regime: `c = (99/100)·log(1/λ)`
    obtain ⟨hl0, hl2⟩ := h14repel hSle (by linarith)
    have hlog : (0:ℝ) < Real.log (1/lam) := by
      rw [one_div, Real.log_inv]
      have h := Real.log_neg hlam0 hlam1
      linarith
    have hl0' : Lam0Bound χ₁ ρ₁ (99/100 * Real.log (1/lam)) := by rw [← hlam]; exact hl0
    have hl2' : Lam2Bound χ₁ (99/100 * Real.log (1/lam)) := by rw [← hlam]; exact hl2
    refine hcore _ (mul_pos (show (0:ℝ) < (99:ℝ)/100 by norm_num) hlog) hl0' hl2' ?_
    simp only [core14RHS, Kc, K2, ac] at hnum_repel ⊢
    ring_nf at hnum_repel ⊢
    linarith
  rcases lt_or_ge lam (25/100) with h2 | h2
  · rcases lt_or_ge lam (2/10) with h3 | h3
    · -- `c = 18/10`
      obtain ⟨hl0, hl2⟩ := h14rows _ hmem4 hSle (by rw [hlam]; linarith) (by rw [hlam]; linarith)
      refine hcore (18/10) (by norm_num) hl0 hl2 ?_
      have h10 := mul_le_mul_of_nonneg_left
        (hnum_rows (18/10) (Or.inr (Or.inr (Or.inr ⟨rfl, hge, by linarith⟩))))
        (show (0:ℝ) ≤ (9:ℝ)/100 by norm_num)
      simp only [core14RHS, Kc, K2, ac] at h10 ⊢
      ring_nf at h10 ⊢
      linarith
    · -- `c = 158/100`
      obtain ⟨hl0, hl2⟩ := h14rows _ hmem3 hSle (by rw [hlam]; linarith) (by rw [hlam]; linarith)
      refine hcore (158/100) (by norm_num) hl0 hl2 ?_
      have h10 := mul_le_mul_of_nonneg_left
        (hnum_rows (158/100) (Or.inr (Or.inr (Or.inl ⟨rfl, h3, by linarith⟩))))
        (show (0:ℝ) ≤ (9:ℝ)/100 by norm_num)
      simp only [core14RHS, Kc, K2, ac] at h10 ⊢
      ring_nf at h10 ⊢
      linarith
  rcases lt_or_ge lam (3/10) with h1 | h1
  · -- `c = 141/100`
    obtain ⟨hl0, hl2⟩ := h14rows _ hmem2 hSle (by rw [hlam]; linarith) (by rw [hlam]; linarith)
    refine hcore (141/100) (by norm_num) hl0 hl2 ?_
    have h10 := mul_le_mul_of_nonneg_left
      (hnum_rows (141/100) (Or.inr (Or.inl ⟨rfl, h2, by linarith⟩)))
      (show (0:ℝ) ≤ (9:ℝ)/100 by norm_num)
    simp only [core14RHS, Kc, K2, ac] at h10 ⊢
    ring_nf at h10 ⊢
    linarith
  · -- `c = 127/100`
    obtain ⟨hl0, hl2⟩ := h14rows _ hmem1 hSle (by rw [hlam]; linarith) (by rw [hlam]; linarith)
    refine hcore (127/100) (by norm_num) hl0 hl2 ?_
    have h10 := mul_le_mul_of_nonneg_left
      (hnum_rows (127/100) (Or.inl ⟨rfl, h1⟩))
      (show (0:ℝ) ≤ (9:ℝ)/100 by norm_num)
    simp only [core14RHS, Kc, K2, ac] at h10 ⊢
    ring_nf at h10 ⊢
    linarith

end Work.LinnikAreas.A7
