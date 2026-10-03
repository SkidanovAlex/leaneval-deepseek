import Mathlib
import Submission.Work.KMTPlan.A6.SsuPhi

namespace Work.KMTPlan.A6

/-- **The `q`-bookkeeping of the paper's Lemma `ssu`.**  Every denominator `q` of a frequency of
the arithmetic set at height `l` is at most `2^{C_π Φ(l)}` (`hCπle` is exactly the sharp element
bound `Work.KMTPlan.A6.iwP_element_le_sharp`).  Hence the product of the two denominators attached
to the two sides of a bilinear expression with heights `l₁, l₂` is at most
`2^{2 C_π Φ(max l₁ l₂)}`, the form in which the `ssu` assembly consumes it.  (The frequency and
vanishing hypotheses are not needed for this step: only the height bound is.) -/
theorem ssuQbBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Cπ : ℝ) (hCπ : 0 < Cπ)
    (hCπle : ∀ (l q : ℕ), q ∈ Work.Analysis.IonescuWainger.iwP ρ l →
      (q : ℝ) ≤ (2 : ℝ) ^ (Cπ * Work.KMTPlan.A6.ssuPhi ρ l))
    (L : ℕ) :
    ∀ (l₁ l₂ : ℕ) (α β : Work.KMTPlan.A6.SsuC) (q₁ q₂ : ℕ),
      max l₁ l₂ = L →
      α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁ → β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂ →
      q₁ ∈ Work.Analysis.IonescuWainger.iwP ρ l₁ → q₂ ∈ Work.Analysis.IonescuWainger.iwP ρ l₂ →
      q₁ • α = 0 → q₂ • β = 0 →
      ((q₁ * q₂ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * Cπ * Work.KMTPlan.A6.ssuPhi ρ L) := by
  intro l₁ l₂ α β q₁ q₂ hL _ _ hq₁ hq₂ _ _
  have h1 : (q₁ : ℝ) ≤ (2 : ℝ) ^ (Cπ * ssuPhi ρ l₁) := hCπle l₁ q₁ hq₁
  have h2 : (q₂ : ℝ) ≤ (2 : ℝ) ^ (Cπ * ssuPhi ρ l₂) := hCπle l₂ q₂ hq₂
  have hl₁ : l₁ ≤ L := by omega
  have hl₂ : l₂ ≤ L := by omega
  have hm₁ : ssuPhi ρ l₁ ≤ ssuPhi ρ L := ssuPhi_mono (le_of_lt hρ) hl₁
  have hm₂ : ssuPhi ρ l₂ ≤ ssuPhi ρ L := ssuPhi_mono (le_of_lt hρ) hl₂
  have hp₁ : (0 : ℝ) < (2 : ℝ) ^ (Cπ * ssuPhi ρ l₁) := Real.rpow_pos_of_pos (by norm_num) _
  have hprod : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * (q₂ : ℝ) := by push_cast; ring
  rw [hprod]
  refine le_trans (mul_le_mul h1 h2 (by positivity) hp₁.le) ?_
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [hm₁, hm₂, hCπ]

end Work.KMTPlan.A6
