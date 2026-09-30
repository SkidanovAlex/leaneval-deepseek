import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.liouville.vmvt_stechkin_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parameters and constants for the Ford §5 assembly of `Work.BMF.vk_exp_sum_ford`

`Work.BMF.Ssum N u t R = Σ_{N<n≤R}(n+u)^{-it}` is the exponential sum of Ford's Theorem 2
(`K. Ford, Vinogradov's integral and bounds for the Riemann zeta function, Proc. LMS 85 (2002)`),
and `Work.BMF.VKF.*` collects the *parameters* of the §5 extraction run on the block `(N,R]`:

* `lam = log t / log N` (`λ`),
* `dH lam = ⌈λ⌉`, `dG lam = ⌈5λ⌉`, `dK lam = ⌈5λ⌉+1` (Ford's `h`, `g`, `k`),
* `dRp lam = ⌈300λ²/k⌉`, `dR lam = k·⌈300λ²/k⌉` (Ford's `r = k·r'`),
* `dSp lam = ⌈200λ²/g⌉`, `dS lam = g·⌈200λ²/g⌉` (Ford's `s = g·s'`),
* `dM N = ⌈N^{2/5}⌉`, `dMu N = log (dM N) / log N` (so `M₁ = M₂ = dM N`, `μ₁ = μ₂ = dMu N`),

together with the absolute constants `dK0 = 300(1+K)` (`K = stechK`, the threshold of the trivial
regime `log N ≤ dK0·λ²`), `dC = exp(1000 + 100K)` and `dD = 10⁹` of the final estimate, and the
auxiliary quantities `dKappa` (the accumulated constant of the extraction), `dDelta1`, `dDelta2`
(the Stechkin excesses of the two mean value inputs) and `dHidx N lam` (Ford's `H`).
-/

namespace Work.BMF.VKF

open Finset
open scoped BigOperators

noncomputable section

/-- The absolute constant `K = stechK` of the sharp Vinogradov–Linnik iteration. -/
def sK : ℝ := Work.BMF.liouville.stechK

/-- Ford's `h = ⌈λ⌉`. -/
def dH (lam : ℝ) : ℕ := ⌈lam⌉₊

/-- Ford's `g = ⌈5λ⌉`. -/
def dG (lam : ℝ) : ℕ := ⌈5 * lam⌉₊

/-- Ford's `k = g + 1`. -/
def dK (lam : ℝ) : ℕ := dG lam + 1

/-- The number of Vinogradov steps `r' = ⌈300λ²/k⌉` in the first mean value. -/
def dRp (lam : ℝ) : ℕ := ⌈300 * lam ^ 2 / (dK lam : ℝ)⌉₊

/-- Ford's `r = k·r'` (the number of variables of `J_{r,k}`). -/
def dR (lam : ℝ) : ℕ := dK lam * dRp lam

/-- The number of blocks `s' = ⌈200λ²/g⌉` of the second mean value. -/
def dSp (lam : ℝ) : ℕ := ⌈200 * lam ^ 2 / (dG lam : ℝ)⌉₊

/-- Ford's `s = g·s'` (the number of variables of `J_{s,g}`). -/
def dS (lam : ℝ) : ℕ := dG lam * dSp lam

/-- `M = ⌈N^{2/5}⌉`. -/
def dM (N : ℝ) : ℕ := ⌈N ^ ((2 : ℝ) / 5)⌉₊

/-- `μ = log M / log N`, so that `M = N^μ`. -/
def dMu (N : ℝ) : ℝ := Real.log (dM N) / Real.log N

/-- The threshold `K₀ = 300(1+K)` of the trivial regime `log N ≤ K₀λ²`. -/
def dK0 : ℝ := 300 * (1 + sK)

/-- The absolute constant `C = exp(1000 + 100K)` of the final estimate. -/
def dC : ℝ := Real.exp (1000 + 100 * sK)

/-- The absolute constant `D = 10⁹` of the final estimate. -/
def dD : ℝ := (10 : ℝ) ^ 9

/-- The accumulated constant `κ` of the extraction (before raising to `1/(2rs)`):
`(5r)^k · s^{h-1} · 2^{(g+3)(g-h+1)} · stechF k r' · stechF g s'`. -/
def dKappa (lam : ℝ) : ℝ :=
  (5 * (dR lam : ℝ)) ^ (dK lam) * (dS lam : ℝ) ^ (dH lam - 1)
    * 2 ^ ((dG lam + 3) * (dG lam - dH lam + 1))
    * Work.BMF.liouville.stechF (dK lam) (dRp lam)
    * Work.BMF.liouville.stechF (dG lam) (dSp lam)

/-- The Stechkin excess `Δ₁ = (k²/2)(1-1/k)^{r'}` of the complete-system input `J_{r,k}(M)`. -/
def dDelta1 (lam : ℝ) : ℝ :=
  (dK lam : ℝ) ^ 2 / 2 * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)

/-- The Stechkin excess `Δ₂ = (g²/2)(1-1/g)^{s'}` of the second input `J_{s,g}(M)`. -/
def dDelta2 (lam : ℝ) : ℝ :=
  (dG lam : ℝ) ^ 2 / 2 * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)

/-- Ford's saving exponent `H = Σ_{j=h}^{g} min(jμ, j-λ, λ-j(1-2μ))` (with `μ₁ = μ₂ = μ`). -/
def dHidx (N : ℝ) (lam : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (dH lam) (dG lam),
    min ((j : ℝ) * dMu N) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - dMu N - dMu N)))

lemma sK_pos : 0 < sK := Work.BMF.liouville.stechK_pos

lemma sK_nonneg : 0 ≤ sK := sK_pos.le

lemma dC_pos : 0 < dC := Real.exp_pos _

lemma dD_pos : 0 < dD := by norm_num [dD]

lemma dK0_pos : 0 < dK0 := by
  have := sK_nonneg
  simp only [dK0]; linarith

lemma one_le_dC : 1 ≤ dC := Real.one_le_exp (by
  have := sK_nonneg
  linarith)

lemma dH_ge (lam : ℝ) : lam ≤ (dH lam : ℝ) := Nat.le_ceil lam

lemma dH_le (lam : ℝ) (h0 : 0 ≤ lam) : (dH lam : ℝ) ≤ lam + 1 :=
  le_of_lt (Nat.ceil_lt_add_one h0)

lemma dG_ge (lam : ℝ) : 5 * lam ≤ (dG lam : ℝ) := Nat.le_ceil (5 * lam)

lemma dG_le (lam : ℝ) (h0 : 0 ≤ lam) : (dG lam : ℝ) ≤ 5 * lam + 1 :=
  le_of_lt (Nat.ceil_lt_add_one (by linarith))

lemma dK_eq (lam : ℝ) : (dK lam : ℝ) = (dG lam : ℝ) + 1 := by
  simp only [dK]; push_cast; ring

lemma dK_le (lam : ℝ) (h0 : 0 ≤ lam) : (dK lam : ℝ) ≤ 5 * lam + 2 := by
  have := dG_le lam h0; rw [dK_eq]; linarith

lemma dRp_le (lam : ℝ) (h0 : 0 ≤ lam) (hk : 0 < (dK lam : ℝ)) :
    (dRp lam : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) + 1 :=
  le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by positivity) hk.le))

lemma dSp_le (lam : ℝ) (h0 : 0 ≤ lam) (hg : 0 < (dG lam : ℝ)) :
    (dSp lam : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) + 1 :=
  le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by positivity) hg.le))

lemma dRp_mul (lam : ℝ) (hk : 1 ≤ dK lam) :
    300 * lam ^ 2 ≤ (dRp lam : ℝ) * (dK lam : ℝ) := by
  have hk0 : (0 : ℝ) < (dK lam : ℝ) := by exact_mod_cast (by omega : 0 < dK lam)
  have h : 300 * lam ^ 2 / (dK lam : ℝ) ≤ (dRp lam : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hk0] at h
  linarith

lemma dSp_mul (lam : ℝ) (hg : 1 ≤ dG lam) :
    200 * lam ^ 2 ≤ (dSp lam : ℝ) * (dG lam : ℝ) := by
  have hg0 : (0 : ℝ) < (dG lam : ℝ) := by exact_mod_cast (by omega : 0 < dG lam)
  have h : 200 * lam ^ 2 / (dG lam : ℝ) ≤ (dSp lam : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hg0] at h
  linarith

lemma dH_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dH lam := by
  have h : (1 : ℝ) ≤ (dH lam : ℝ) := le_trans (by linarith : (1:ℝ) ≤ lam) (Nat.le_ceil lam)
  exact_mod_cast h

lemma dG_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dG lam := by
  have h : (1 : ℝ) ≤ (dG lam : ℝ) := le_trans (by linarith : (1:ℝ) ≤ 5 * lam) (Nat.le_ceil _)
  exact_mod_cast h

lemma dK_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dK lam := by
  have := dG_pos lam hlam; simp only [dK]; omega

lemma dRp_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dRp lam := by
  have hk : (0 : ℝ) < (dK lam : ℝ) := by
    have := dK_pos lam hlam; exact_mod_cast (by omega : 0 < dK lam)
  have h : (1 : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) := by
    rw [le_div_iff₀ hk]
    have h2 : (5 : ℝ) * lam + 2 ≤ 300 * lam ^ 2 := by
      nlinarith [sq_nonneg (lam - 13/5), hlam]
    have h3 := dK_le lam (by linarith)
    nlinarith [hk, h2, h3]
  exact_mod_cast le_trans h (Nat.le_ceil _)

lemma dSp_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dSp lam := by
  have hg : (0 : ℝ) < (dG lam : ℝ) := by
    have := dG_pos lam hlam; exact_mod_cast (by omega : 0 < dG lam)
  have h : (1 : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) := by
    rw [le_div_iff₀ hg]
    have h2 : (5 : ℝ) * lam + 1 ≤ 200 * lam ^ 2 := by
      nlinarith [sq_nonneg (lam - 13/5), hlam]
    have h3 := dG_le lam (by linarith)
    nlinarith [hg, h2, h3]
  exact_mod_cast le_trans h (Nat.le_ceil _)

lemma dR_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dR lam := by
  have h1 := dK_pos lam hlam
  have h2 := dRp_pos lam hlam
  simp only [dR]
  calc 1 = 1 * 1 := by ring
    _ ≤ dK lam * dRp lam := Nat.mul_le_mul h1 h2

lemma dS_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 1 ≤ dS lam := by
  have h1 := dG_pos lam hlam
  have h2 := dSp_pos lam hlam
  simp only [dS]
  calc 1 = 1 * 1 := by ring
    _ ≤ dG lam * dSp lam := Nat.mul_le_mul h1 h2

lemma dKappa_pos (lam : ℝ) (hlam : 13 / 5 ≤ lam) : 0 < dKappa lam := by
  have hR : (0 : ℝ) < 5 * (dR lam : ℝ) := by
    have := dR_pos lam hlam
    have : (1:ℝ) ≤ (dR lam : ℝ) := by exact_mod_cast this
    linarith
  have hS : (0 : ℝ) < (dS lam : ℝ) := by
    have := dS_pos lam hlam
    exact_mod_cast (by omega : 0 < dS lam)
  have h4 := Work.BMF.liouville.stechF_pos (dK lam) (dRp lam)
  have h5 := Work.BMF.liouville.stechF_pos (dG lam) (dSp lam)
  have h1 := pow_pos hR (dK lam)
  have h2 := pow_pos hS (dH lam - 1)
  have h3 : (0 : ℝ) < (2 : ℝ) ^ ((dG lam + 3) * (dG lam - dH lam + 1)) :=
    pow_pos (by norm_num) _
  simp only [dKappa]
  exact mul_pos (mul_pos (mul_pos (mul_pos h1 h2) h3) h4) h5

end

end Work.BMF.VKF
