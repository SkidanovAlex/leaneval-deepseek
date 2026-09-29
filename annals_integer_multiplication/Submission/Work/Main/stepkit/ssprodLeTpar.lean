import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.stepkit

/-- Two lists of naturals of the same length whose entries compare pointwise (read off with `getD`)
have comparable products. -/
theorem prod_le_prod_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 ≤ l₂.getD i 0) : l₁.prod ≤ l₂.prod := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l₁' ih =>
    cases l₂ with
    | nil => simp_all
    | cons b l₂' =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [List.prod_cons, List.prod_cons]
      refine Nat.mul_le_mul ?_ (ih hlen ?_)
      · simpa using h 0 (by simp)
      · intro i hi
        simpa using h (i + 1) (by simp [hi])

/-- `ParamOK n ts ss` gives `ss.prod ≤ Tpar n = ts.prod`: the size window of §5.1 says
`(1 - 2/(4d)) tᵢ < sᵢ ≤ (1 - 1/(4d)) tᵢ`, in particular `sᵢ ≤ tᵢ` for every `i < d`
(since `1 - 1/(4d) ≤ 1`), and `ss` and `ts` have the same length `d`. -/
theorem ssprodLeTpar {n : ℕ} {ts ss : List ℕ} (hOK : HvdH.ParamOK n ts ss) :
    ss.prod ≤ HvdH.Tpar n := by
  obtain ⟨hlen_t, hlen_s, -, hprod_t, -, hbound, -, -⟩ := hOK
  have hfac : (1 : ℝ) - 1 / (4 * (HvdH.D : ℝ)) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (4 * (HvdH.D : ℝ)) := by positivity
    linarith
  have hpt : ∀ i, i < ss.length → ss.getD i 0 ≤ ts.getD i 0 := by
    intro i hi
    have hiD : i < HvdH.D := by omega
    have h2 := (hbound i hiD).2
    have hle : (ss.getD i 0 : ℝ) ≤ (ts.getD i 0 : ℝ) := by
      calc (ss.getD i 0 : ℝ) ≤ (1 - 1 / (4 * (HvdH.D : ℝ))) * (ts.getD i 0 : ℝ) := h2
        _ ≤ 1 * (ts.getD i 0 : ℝ) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
        _ = (ts.getD i 0 : ℝ) := one_mul _
    exact_mod_cast hle
  calc ss.prod ≤ ts.prod := prod_le_prod_getD (by omega) hpt
    _ = HvdH.Tpar n := hprod_t

end Work.Main.stepkit
