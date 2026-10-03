import Mathlib
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Interfaces.Fatou

/-!
# Backward iteration into the fundamental strip (Shishikura, Prop. A.2.1(i))

`MandelDim.fundStrip F Q x₀ = {z ∈ Q | x₀ ≤ Re z ∧ every F-preimage of z in Q has Re < x₀}`
is the "first-return" fundamental domain of the near-translation `F` for the vertical line
`Re = x₀`.

This file proves `backwardIterate`: every point `z ∈ Q` with `x₀ ≤ Re z` lies on the *forward*
orbit of a point of the fundamental strip, with all intermediate iterates inside `Q`.

The argument is elementary and uses only the estimate `‖F u - (u+1)‖ ≤ 1/32` (no injectivity,
no surjectivity, and no hypothesis on the position of `x₀` relative to the vertices is needed):
if `z ∉ fundStrip` then, by definition of `fundStrip`, `z` has a preimage `v ∈ Q` with
`x₀ ≤ Re v`, and `Re v + 31/32 ≤ Re z`, so `Re` decreases by at least `31/32` at every backward
step while staying `≥ x₀`; hence the descent terminates after at most `N` steps, where
`N · 31/32 > z.re - x₀`.  This is a descending induction, presented here as an ascending
induction on the remaining budget `n · 31/32` for the "potential" `Re w - x₀`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Work.Fatou.Qreg

open Set Metric Complex
open scoped Topology

noncomputable section

variable {Q : Set ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- If `z ∈ Q`, `x₀ ≤ Re z` and `z` is not in the fundamental strip, then `z` has a preimage in
`Q` whose real part is still `≥ x₀`.  This is a direct unfolding of the definition of
`fundStrip`. -/
lemma exists_preimage_of_not_mem_fundStrip {z : ℂ} (hzQ : z ∈ Q) (hzx : x₀ ≤ z.re)
    (hz : z ∉ MandelDim.fundStrip F Q x₀) :
    ∃ w ∈ Q, F w = z ∧ x₀ ≤ w.re := by
  by_contra h
  apply hz
  refine ⟨hzQ, hzx, ?_⟩
  intro w hwQ hFw
  by_contra hlt
  exact h ⟨w, hwQ, hFw, not_lt.mp hlt⟩

/-- **Backward iteration into the fundamental strip.**  If `‖F u - (u+1)‖ ≤ 1/32` on `Q` then
every `z ∈ Q` with `x₀ ≤ Re z` is `F^[k] s` for some `k` and some `s` in the fundamental strip,
and the whole piece of orbit from `s` to `z` stays in `Q`. -/
lemma exists_iterate_eq_of_mem {z : ℂ} (hstep : ∀ u ∈ Q, ‖F u - (u + 1)‖ ≤ (1 / 32 : ℝ))
    (hzQ : z ∈ Q) (hzx : x₀ ≤ z.re) :
    ∃ k : ℕ, ∃ s ∈ MandelDim.fundStrip F Q x₀, F^[k] s = z ∧
      ∀ j ≤ k, F^[j] s ∈ Q := by
  have hd : (0 : ℝ) < 31 / 32 := by norm_num
  -- a budget large enough to exhaust the potential `Re z - x₀`
  obtain ⟨N, hN⟩ := exists_nat_gt ((z.re - x₀) / (31 / 32))
  have hNd : z.re - x₀ < (N : ℝ) * (31 / 32) := (div_lt_iff₀ hd).mp hN
  -- descent: with remaining potential at most `n * 31/32` we reach the fundamental strip in `≤ n`
  -- backward steps
  have key : ∀ n : ℕ, ∀ w ∈ Q, x₀ ≤ w.re → w.re - x₀ ≤ (n : ℝ) * (31 / 32) →
      ∃ k : ℕ, k ≤ n ∧ ∃ s ∈ MandelDim.fundStrip F Q x₀,
        F^[k] s = w ∧ ∀ j ≤ k, F^[j] s ∈ Q := by
    intro n
    induction n with
    | zero =>
      intro w hwQ hwx hwle
      have hw0 : w.re = x₀ := by
        have : w.re - x₀ ≤ 0 := by simpa using hwle
        linarith
      have hmem : w ∈ MandelDim.fundStrip F Q x₀ := by
        refine ⟨hwQ, hwx, ?_⟩
        intro v hvQ hFv
        have hv : v.re + 31 / 32 ≤ w.re := by
          have h := (re_step_bounds (F := F) (hstep v hvQ)).1
          rwa [hFv] at h
        linarith
      exact ⟨0, le_refl 0, w, hmem, by simp, by
        intro j hj
        rw [Nat.le_zero.mp hj]
        simpa using hwQ⟩
    | succ n ih =>
      intro w hwQ hwx hwle
      by_cases hmem : w ∈ MandelDim.fundStrip F Q x₀
      · exact ⟨0, Nat.zero_le _, w, hmem, by simp, by
          intro j hj
          rw [Nat.le_zero.mp hj]
          simpa using hwQ⟩
      · obtain ⟨v, hvQ, hFv, hvx⟩ := exists_preimage_of_not_mem_fundStrip hwQ hwx hmem
        have hv : v.re + 31 / 32 ≤ w.re := by
          have h := (re_step_bounds (F := F) (hstep v hvQ)).1
          rwa [hFv] at h
        have hsplit : ((n : ℝ) + 1) * (31 / 32) - 31 / 32 = (n : ℝ) * (31 / 32) := by ring
        have hvle : v.re - x₀ ≤ (n : ℝ) * (31 / 32) := by
          push_cast at hwle
          linarith
        obtain ⟨k, hk, s, hs, hFs, hiter⟩ := ih v hvQ hvx hvle
        refine ⟨k + 1, Nat.succ_le_succ hk, s, hs, ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hFs, hFv]
        · intro j hj
          rcases lt_or_eq_of_le hj with hlt | heq
          · exact hiter j (Nat.lt_succ_iff.mp hlt)
          · rw [heq, Function.iterate_succ_apply', hFs, hFv]
            exact hwQ
  obtain ⟨k, -, s, hs, hFs, hiter⟩ := key N z hzQ hzx (le_of_lt hNd)
  exact ⟨k, s, hs, hFs, hiter⟩

end

end Work.Fatou.Qreg

namespace Work.Fatou.Qreg

open Set Metric Complex
open scoped Topology

/-- **`Work.Fatou.Qreg.backwardIterate`** (Shishikura, Prop. A.2.1(i), "backward" half): a point
of `𝒬(b₁,b₂)` to the right of the vertical line `Re = x₀` lies on the forward orbit of a point of
the fundamental strip `fundStrip F 𝒬 x₀`, and the orbit piece between them stays in `𝒬`. -/
theorem backwardIterate {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hzx : x₀ ≤ z.re) :
    ∃ k : ℕ, ∃ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀,
      F^[k] s = z ∧ ∀ j ≤ k, F^[j] s ∈ MandelDim.Qreg b₁ b₂ :=
  exists_iterate_eq_of_mem (Q := MandelDim.Qreg b₁ b₂) (x₀ := x₀)
    (fun u hu => (hF.2 u hu).1) hz hzx

end Work.Fatou.Qreg
