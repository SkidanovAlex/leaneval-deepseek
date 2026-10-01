/-
# §15 assembly — shared helpers

Small generic lemmas used by the generated numerical layer (`sec15_num.lean`) and by the
§15 assembly: the list-indexed counting function `Nlist`, the tail estimate for
`(Φ(Λ)/w(Λ))·(67/6+εw)`, the `η`-estimate for `(e^{-aΛ}/w(Λ))·(67/6+εw) + N₀ + 4`, the
elementary inequality `c·K⁻²F₂ ≤ B`, and the Table 13 counting bound.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas
import Submission.Work.LinnikAreas.A7.NumPoints
import Submission.Work.LinnikAreas.A7.NumExp
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.LinnikContract.API.Bfun_pos
import Submission.Work.A7.smul_F2K2_le_bfun

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.A7

open Work.LinnikContract
open Work.LinnikAreas.A7

/-- The counting bound read off a list: `N j = l[j]` for `j < l.length`, `0` beyond. -/
def Nlist (l : List ℕ) (j : ℕ) : ℕ := l.getD j 0

lemma Phi_pos {z : ℝ} (hz : 0 < z) : 0 < Phi z := by
  rw [Phi]
  exact mul_pos (Real.exp_pos _)
    (Work.LinnikContract.API.Bfun_pos (K := Kc) (lam := z) (by norm_num [Kc]) hz)

/-- `Bfun (3/10) p` in the form used by `smul_F2K2_le_bfun`. -/
lemma Bfun_expand {p : ℝ} (hp : 0 < p) :
    Bfun ((3:ℝ)/10) p
      = (1 - Real.exp (-((3:ℝ)/5 * p)))/(6*((9:ℝ)/100)*p)
        + (2*((3:ℝ)/10)*p - 1 + Real.exp (-((3:ℝ)/5 * p)))/(2*((9:ℝ)/100)*p^2) := by
  rw [Bfun, if_neg (ne_of_gt hp)]
  norm_num

/-- `c·K⁻²F₂(p) ≤ B(3/10,p)` for `0 ≤ c ≤ 2`, `p > 0` — the form needed for `Aref ≥ 0`. -/
lemma cF2K2_le_Bfun {c p : ℝ} (hp : 0 < p) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    c * (((1 - Real.exp (-((3:ℝ)/10 * p))) / p) ^ 2 / ((9:ℝ)/100))
      ≤ Bfun ((3:ℝ)/10) p := by
  rw [Bfun_expand hp]
  exact smul_F2K2_le_bfun hp hc0 hc2

/-- The tail estimate `(Φ(Λ)/w(Λ))·(67/6+εw) ≤ r` from rational enclosures of `Φ(Λ)`, `w(Λ)`. -/
lemma tail_le {L εw PU WL r : ℝ} (hL : 0 < L) (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hPU : Phi L ≤ PU) (hWL : WL ≤ Wf L) (hWLpos : 0 < WL)
    (hr : PU / WL * ((67:ℝ)/6 + 1/1000) ≤ r) :
    (Phi L / Wf L) * ((67:ℝ)/6 + εw) ≤ r := by
  have hWf : 0 < Wf L := Wf_pos hL
  have hPhi0 : 0 ≤ Phi L := (Phi_pos hL).le
  have hPU0 : 0 ≤ PU := le_trans hPhi0 hPU
  have h1 : Phi L / Wf L ≤ PU / WL := by
    rw [div_le_div_iff₀ hWf hWLpos]
    nlinarith
  have h2 : (67:ℝ)/6 + εw ≤ (67:ℝ)/6 + 1/1000 := by linarith
  have h3 : 0 ≤ PU / WL := div_nonneg hPU0 hWLpos.le
  calc (Phi L / Wf L) * ((67:ℝ)/6 + εw) ≤ (PU / WL) * ((67:ℝ)/6 + 1/1000) :=
        mul_le_mul h1 h2 (by linarith) h3
    _ ≤ r := hr

/-- The `η`-estimate `(e^{-aΛ}/w(Λ))·(67/6+εw) + N₀ + 4 ≤ 1000` from rational enclosures. -/
lemma etab_le {L εw E WL N0 : ℝ} (hL : 0 < L) (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hE : Real.exp (-(ac * L)) ≤ E) (hWL : WL ≤ Wf L) (hWLpos : 0 < WL)
    (hr : E / WL * ((67:ℝ)/6 + 1/1000) + N0 + 4 ≤ 1000) :
    (Real.exp (-(ac * L)) / Wf L) * ((67:ℝ)/6 + εw) + N0 + 4 ≤ 1000 := by
  have hWf : 0 < Wf L := Wf_pos hL
  have hEr : Real.exp (-(ac * L)) / Wf L ≤ E / WL := by
    rw [div_le_div_iff₀ hWf hWLpos]
    nlinarith [Real.exp_pos (-(ac * L)), hE, hWL]
  have h2 : (67:ℝ)/6 + εw ≤ (67:ℝ)/6 + 1/1000 := by linarith
  have h3 : 0 ≤ E / WL := div_nonneg (le_trans (Real.exp_pos _).le hE) hWLpos.le
  have := mul_le_mul hEr h2 (by linarith) h3
  linarith

/-- A `Ncount` bound read off one row of HB's Table 13, given that the table's column bound is at
most `lam₁`. -/
lemma Ncount_le_table {q : ℕ} [NeZero q] {c lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁) (hcol : c ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2)
    {t : ℝ} {N : ℕ} (hmem : (t, c, N) ∈ Work.LinnikContract.table13) : Ncount q t ≤ N :=
  hD2 _ hmem (fun χ ρ hZ => le_trans hcol (hlam1 ▸ hmin.2 χ ρ hZ))

end Work.A7
