import Mathlib
import Submission.Work.Peluse.SwapE.slotCount_le
import Submission.Work.Peluse.SwapE.slotDiffCount_le
import Submission.Work.Peluse.SwapE.genPair_gcd_reduce
import Submission.Work.Peluse.SwapE.slotDensity_arith

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

open Work.Peluse
open Work.Peluse.LadderP.Swap

noncomputable section

/-- **`SlotDensity`** — the law of the multiset slot `q₁[M] − q₂[M]` is bounded by the density of
the uniform distribution on the slot box `[−2HM, 2HM]`, up to `K₀ = endgameK0 η H M`
(KKL, arXiv:2407.08636, Corollary 7.2 at `ℓ = 2`).

Proof sketch.  First the fibre identity
`slotCount q₁ q₂ M n = ∑ X ∈ [−(M−1), M−1], ∑ Y ∈ [−(M−1), M−1],
   [q₁ X − q₂ Y = n] · (M − |X|) · (M − |Y|)`
(count the pairs `(X, X')` with `X − X' = a ∈ [1,M]²`: there are `M − |a|` of them).
Then, with `g = gcd q₁ q₂`, `a = q₁/g`, `b = q₂/g` (`gcd a b = 1`), the solutions of
`a X − b Y = n/g` are `(X₀ + b t, Y₀ + a t)`; the constraints `|X₀ + bt| ≤ M`, `|Y₀ + at| ≤ M`
force `|t| ≤ 2M / max |a| |b|`, so there are at most `4M / max(|a|,|b|) + 1` of them and
`slotCount ≤ (4M/ max(|a|,|b|) + 1) · M²`.  `genPair H η` gives `|q i| ≥ ηH`, `g ≤ 1/η`, hence
`|a| = |q₁|/g ≥ η²H` and `max(|a|,|b|) ≥ η²H`; so
`slotLaw ≤ 4/(η² H M) + 1/M²`.  Finally `4/(η²HM) ≤ 24/(η²(4HM+1))` (as `16HM+4 ≤ 24HM`) and
`1/M² ≤ 8H/(M(4HM+1))` (as `4HM+1 ≤ 8HM`), so `slotLaw ≤ endgameK0 η H M / (4HM+1)`. -/
theorem slotDensity : Work.Peluse.SwapE.SlotDensity := by
  intro q₁ q₂ M H η n hM hH hη hη1 hgen
  -- `hred` reduces the count for `(q₁,q₂)` to the count for the primitive direction
  -- `(slotA q₁ q₂, slotB q₁ q₂)`; `hmax` is `max |a| |b| ≥ η²H`.
  obtain ⟨hgpos, hcop, ha0, hb0, hred, hmax⟩ :=
    genPair_gcd_reduce q₁ q₂ H η (M - 1) n hH hη hη1 hgen
  have hA := slotCount_le q₁ q₂ M n
  have hB := slotDiffCount_le (slotA q₁ q₂) (slotB q₁ q₂) (M - 1)
    (n / (Int.gcd q₁ q₂ : ℤ)) hcop ha0 hb0
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hη2pos : (0 : ℝ) < η ^ 2 := by positivity
  set mx : ℝ := max |(slotA q₁ q₂ : ℝ)| |(slotB q₁ q₂ : ℝ)| with hmx_def
  have hmax' : η ^ 2 * (H : ℝ) ≤ mx := by rw [hmx_def]; exact hmax
  have hmxpos : 0 < mx := lt_of_lt_of_le (by positivity : (0:ℝ) < η ^ 2 * (H:ℝ)) hmax'
  have hK1 : (((M - 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
  have hcount : (slotCount q₁ q₂ M n : ℝ)
      ≤ (M : ℝ) ^ 2 * (4 * (M : ℝ) / (η ^ 2 * (H : ℝ)) + 1) := by
    have h1 : (slotCount q₁ q₂ M n : ℝ)
        ≤ (M : ℝ) ^ 2 * (slotDiffCount q₁ q₂ (M - 1) n : ℝ) := by exact_mod_cast hA
    have h2 : (slotDiffCount q₁ q₂ (M - 1) n : ℝ)
        ≤ (slotDiffCount (slotA q₁ q₂) (slotB q₁ q₂) (M - 1)
            (n / (Int.gcd q₁ q₂ : ℤ)) : ℝ) := by exact_mod_cast hred
    have h3 : (slotDiffCount (slotA q₁ q₂) (slotB q₁ q₂) (M - 1)
          (n / (Int.gcd q₁ q₂ : ℤ)) : ℝ)
        ≤ 4 * (((M - 1 : ℕ) : ℝ)) / mx + 1 := by
      rw [hmx_def]; exact hB
    have h41 : 4 * (((M - 1 : ℕ) : ℝ)) / mx ≤ 4 * (M : ℝ) / mx := by
      apply div_le_div_of_nonneg_right _ hmxpos.le
      nlinarith [hK1]
    have h42 : 4 * (M : ℝ) / mx ≤ 4 * (M : ℝ) / (η ^ 2 * (H : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hmax'
    have h4 : 4 * (((M - 1 : ℕ) : ℝ)) / mx + 1 ≤ 4 * (M : ℝ) / (η ^ 2 * (H : ℝ)) + 1 := by
      linarith [h41, h42]
    have h5 : (slotDiffCount (slotA q₁ q₂) (slotB q₁ q₂) (M - 1)
          (n / (Int.gcd q₁ q₂ : ℤ)) : ℝ)
        ≤ 4 * (M : ℝ) / (η ^ 2 * (H : ℝ)) + 1 := le_trans h3 h4
    have h6 := mul_le_mul_of_nonneg_left (le_trans h2 h5) (by positivity : (0:ℝ) ≤ (M:ℝ)^2)
    linarith [h1, h6]
  -- `slotLaw = slotCount / M⁴ ≤ (4M/(η²H) + 1)/M² = 4/(η²HM) + 1/M²`
  have hsl : slotLaw q₁ q₂ M n ≤ 4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2 := by
    rw [slotLaw, div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) ^ 4)]
    have heq : (4 / (η ^ 2 * (H : ℝ) * (M : ℝ)) + 1 / (M : ℝ) ^ 2) * (M : ℝ) ^ 4
        = (M : ℝ) ^ 2 * (4 * (M : ℝ) / (η ^ 2 * (H : ℝ)) + 1) := by
      field_simp
    rw [heq]
    exact hcount
  exact slotDensity_arith η H M (slotLaw q₁ q₂ M n) hH hM hη hsl

end

end Work.Peluse.SwapE
