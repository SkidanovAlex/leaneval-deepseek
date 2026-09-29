import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.poisson_bound
import Submission.Work.TMC16Core.Basic.tendsto_affine_mul_exp_neg

open scoped Topology
open Filter

namespace Work.TMC16Core.Basic

/-- **AJ §9, `singular_of_ne_zero`.**  A nonzero formal solution of the almost Mathieu
equation `H u = E u` with polynomial growth is `(m,k)`-singular for every fixed `m > 0`
and all sufficiently large `k`. -/
theorem singular_of_ne_zero {α lam θ : ℝ} {E : ℂ} {u : ℤ → ℂ}
    (hsol : Work.TMC16Core.IsFormalSol α lam θ E u) {C : ℝ}
    (hC : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)) {y : ℤ} (hy : u y ≠ 0)
    {m : ℝ} (hm : 0 < m) :
    ∀ᶠ k : ℕ in atTop, Work.TMC16Core.IsSingular α lam θ E m k y := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    linarith [norm_nonneg (u 0)]
  have hypos : 0 < ‖u y‖ := norm_pos_iff.mpr hy
  have hc : 0 < m / 40 := by linarith
  set F : ℕ → ℝ := fun k => 2 * C * ((|(y:ℝ)| + 2 + (k:ℝ)) * Real.exp (-((m/40) * (k:ℝ)))) with hF
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto
        (fun k : ℕ => (|(y:ℝ)| + 2 + (k:ℝ)) * Real.exp (-((m/40) * (k:ℝ))))
        Filter.atTop (nhds 0) := by
      have h := tendsto_affine_mul_exp_neg (|(y:ℝ)| + 2) (m/40) hc
      simpa using h
    have h2 := hbase.const_mul (2*C)
    simpa [hF] using h2
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, F k < ‖u y‖ := by
    have h := hlim.eventually (isOpen_Iio.mem_nhds hypos)
    rw [Filter.eventually_atTop] at h
    exact h
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk hreg => ?_⟩
  rcases hreg with ⟨x₁, x₂, hx2, hx1y, hyx2, hk1, hk2, hdet, hG1, hG2⟩
  have hxk : x₂ - x₁ + 1 = (k:ℤ) := by omega
  have hkn : (x₂ - x₁ + 1).toNat = k := by rw [hxk]; simp
  have hdet' : (Work.TMC16Core.dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat)).det ≠ 0 := by
    rw [hkn]; exact hdet
  have hpoisson' := poisson_bound hsol hdet' hx1y hyx2
  have hD1 : (k:ℝ)/40 ≤ (y:ℝ) - (x₁:ℝ) := by
    have h1 : ((k:ℤ):ℝ) ≤ ((40 * (y - x₁) : ℤ) : ℝ) := by exact_mod_cast hk1
    push_cast at h1
    linarith
  have hD2 : (k:ℝ)/40 ≤ (x₂:ℝ) - (y:ℝ) := by
    have h1 : ((k:ℤ):ℝ) ≤ ((40 * (x₂ - y) : ℤ) : ℝ) := by exact_mod_cast hk2
    push_cast at h1
    linarith
  have hexp1 : Real.exp (-(m * ((y:ℝ) - (x₁:ℝ)))) ≤ Real.exp (-((m/40)*(k:ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h2 := mul_le_mul_of_nonneg_left hD1 (le_of_lt hm)
    have : m * ((k:ℝ)/40) = (m/40) * (k:ℝ) := by ring
    linarith
  have hexp2 : Real.exp (-(m * ((x₂:ℝ) - (y:ℝ)))) ≤ Real.exp (-((m/40)*(k:ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h2 := mul_le_mul_of_nonneg_left hD2 (le_of_lt hm)
    have : m * ((k:ℝ)/40) = (m/40) * (k:ℝ) := by ring
    linarith
  have habs1 : |(((y - x₁ : ℤ)):ℝ)| = (y:ℝ) - (x₁:ℝ) := by
    have h0 : (0:ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
      exact_mod_cast (by omega : (0:ℤ) ≤ y - x₁)
    rw [abs_of_nonneg h0]; push_cast; ring
  have habs2 : |(((y - x₂ : ℤ)):ℝ)| = (x₂:ℝ) - (y:ℝ) := by
    have h0 : (0:ℝ) ≤ ((x₂ - y : ℤ) : ℝ) := by
      exact_mod_cast (by omega : (0:ℤ) ≤ x₂ - y)
    have hneg : ((y - x₂ : ℤ) : ℝ) = -(((x₂ - y : ℤ)) : ℝ) := by push_cast; ring
    rw [hneg, abs_neg, abs_of_nonneg h0]; push_cast; ring
  have hG1' : ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ ≤ Real.exp (-((m/40)*(k:ℝ))) := by
    have h := le_of_lt hG1
    rw [habs1] at h
    exact le_trans h hexp1
  have hG2' : ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ ≤ Real.exp (-((m/40)*(k:ℝ))) := by
    have h := le_of_lt hG2
    rw [habs2] at h
    exact le_trans h hexp2
  have hx1b : |(((x₁ - 1 : ℤ)) : ℝ)| ≤ |(y:ℝ)| + (k:ℝ) := by
    have hle : y - x₁ ≤ (k:ℤ) - 1 := by omega
    rw [abs_le]
    push_cast
    constructor
    · have h2 : (y:ℝ) - (k:ℝ) ≤ ((x₁ : ℤ) : ℝ) - 1 := by
        have : y - (k:ℤ) ≤ x₁ - 1 := by omega
        have hh : ((y - (k:ℤ) : ℤ) : ℝ) ≤ ((x₁ - 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hh
        linarith
      have h3 : -(|(y:ℝ)| + (k:ℝ)) ≤ (y:ℝ) - (k:ℝ) := by
        have := neg_abs_le (y:ℝ)
        linarith
      linarith
    · have h2 : ((x₁ : ℤ) : ℝ) - 1 ≤ (y:ℝ) - 1 := by
        have : x₁ - 1 ≤ y - 1 := by omega
        have hh : ((x₁ - 1 : ℤ) : ℝ) ≤ ((y - 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hh
        linarith
      have h3 : (y:ℝ) ≤ |(y:ℝ)| := le_abs_self _
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
  have hx2b : |(((x₂ + 1 : ℤ)) : ℝ)| ≤ |(y:ℝ)| + (k:ℝ) := by
    have hle : x₂ - y ≤ (k:ℤ) - 1 := by omega
    rw [abs_le]
    push_cast
    constructor
    · have h2 : (y:ℝ) ≤ ((x₂ : ℤ) : ℝ) + 1 := by
        have : y ≤ x₂ + 1 := by omega
        have hh : ((y : ℤ) : ℝ) ≤ ((x₂ + 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hh
        linarith
      have h3 : -(|(y:ℝ)| + (k:ℝ)) ≤ (y:ℝ) := by
        have := neg_abs_le (y:ℝ)
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      linarith
    · have h2 : ((x₂ : ℤ) : ℝ) + 1 ≤ (y:ℝ) + (k:ℝ) := by
        have : x₂ + 1 ≤ y + (k:ℤ) := by omega
        have hh : ((x₂ + 1 : ℤ) : ℝ) ≤ ((y + (k:ℤ) : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at hh
        linarith
      have h3 : (y:ℝ) ≤ |(y:ℝ)| := le_abs_self _
      linarith
  have hu1 : ‖u (x₁-1)‖ ≤ C * (|(y:ℝ)| + 2 + (k:ℝ)) := by
    have h := hC (x₁ - 1)
    have h1 : 1 + |(((x₁-1:ℤ)):ℝ)| ≤ |(y:ℝ)| + 2 + (k:ℝ) := by linarith
    exact le_trans h (mul_le_mul_of_nonneg_left h1 hC0)
  have hu2 : ‖u (x₂+1)‖ ≤ C * (|(y:ℝ)| + 2 + (k:ℝ)) := by
    have h := hC (x₂ + 1)
    have h1 : 1 + |(((x₂+1:ℤ)):ℝ)| ≤ |(y:ℝ)| + 2 + (k:ℝ) := by linarith
    exact le_trans h (mul_le_mul_of_nonneg_left h1 hC0)
  have hterm1 : ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ * ‖u (x₁-1)‖ ≤
      C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ))) := by
    have hE : 0 ≤ Real.exp (-((m/40)*(k:ℝ))) := Real.exp_nonneg _
    have := mul_le_mul hG1' hu1 (norm_nonneg _) hE
    calc ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ * ‖u (x₁-1)‖
        ≤ Real.exp (-((m/40)*(k:ℝ))) * (C * (|(y:ℝ)|+2+(k:ℝ))) := this
      _ = C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ))) := by ring
  have hterm2 : ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ * ‖u (x₂+1)‖ ≤
      C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ))) := by
    have hE : 0 ≤ Real.exp (-((m/40)*(k:ℝ))) := Real.exp_nonneg _
    have := mul_le_mul hG2' hu2 (norm_nonneg _) hE
    calc ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ * ‖u (x₂+1)‖
        ≤ Real.exp (-((m/40)*(k:ℝ))) * (C * (|(y:ℝ)|+2+(k:ℝ))) := this
      _ = C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ))) := by ring
  have hmain : ‖u y‖ ≤ F k := by
    have hsum := add_le_add hterm1 hterm2
    calc ‖u y‖ ≤ ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ * ‖u (x₁-1)‖
                  + ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ * ‖u (x₂+1)‖ := hpoisson'
      _ ≤ C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ)))
            + C * (|(y:ℝ)|+2+(k:ℝ)) * Real.exp (-((m/40)*(k:ℝ))) := hsum
      _ = F k := by simp only [hF]; ring
  have := hK k hk
  linarith

end Work.TMC16Core.Basic
