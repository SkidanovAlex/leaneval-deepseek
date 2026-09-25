import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

/-- **A rational point whose denominator divides `Q` is `Q`-torsion.**  For `0 < q` and `q ∣ Q`
the character `fourier Q` takes the value `1` at `a/q ∈ 𝕋 = ℝ/ℤ`:  writing `Q = q * c`, the
exponent `2πi·Q·(a/q)` equals `(c*a)·2πi` with `c*a ∈ ℤ`, and `exp(m·2πi) = 1`. -/
lemma mstTorsion_arcPt_fourier {Q q : ℕ} {a : ℤ} (hq : 0 < q) (hdiv : q ∣ Q) :
    fourier (Q : ℤ) (arcPt q a) = 1 := by
  obtain ⟨c, rfl⟩ := hdiv
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [arcPt, fourier_coe_apply]
  have harg : 2 * ↑Real.pi * Complex.I * ↑((q * c : ℕ) : ℤ) * ↑((a : ℝ) / (q : ℝ)) / ↑(1:ℝ)
      = ↑((c : ℤ) * a) * (2 * ↑Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

/-- **The MST scale in its real exponent form**: with `ρ = mstRho l = 1/(10 l)`,
`(n^l)^ρ = n^{1/10}` for `1 ≤ n` and `1 ≤ l` (the exponent `1/10` is the *real* one). -/
lemma mstTorsion_rho_pow (l : ℕ) (hl : 1 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ l) ^ (mstRho l) = (n : ℝ) ^ (1 / 10 : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    linarith
  rw [mstRho, ← Real.rpow_natCast (n : ℝ) l, ← Real.rpow_mul hn0]
  congr 1
  field_simp

/-- **Every point of the level-`(s+1)` arc set is a `Q_s`-torsion point.**  If
`β = a/Q_A ∈ 𝒰((s+1)^l)` then `Q_A ≤ ⌈e^{(s+1)^{1/10}}⌉` (`sigmaN_denom_le` at `N = (s+1)^l`,
using `mstRho l = 1/(10l)`), so `Q_A` divides `Q_s = (⌈e^{(s+1)^{1/10}}⌉)!` and
`e^{2πi Q_s β} = 1`.  This makes `x ↦ I(x,y)` `Q_sℤ`-periodic and the characters `u ↦ e^{2πi u β}`
orthogonal on `ℤ/Q_s`.  (Note `mstQ'` carries the **real** exponent `(1/10 : ℝ)`.) -/
theorem mstTorsion (l : ℕ) (hl : 1 ≤ l) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1), fourier (Work.BourgainPlan.Maximal.mstQ' s) β = 1 := by
  have hρ : 0 < mstRho l := by
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    unfold mstRho
    positivity
  obtain ⟨N₁, hN₁⟩ := sigmaN_denom_le (mstRho l) hρ
  refine ⟨N₁, fun s hs β hβ => ?_⟩
  have hNle : N₁ ≤ (s + 1) ^ l := by
    have h1 : N₁ ≤ s + 1 := by omega
    calc N₁ ≤ s + 1 := h1
      _ = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ l := Nat.pow_le_pow_right (by omega) hl
  rw [mstU_apply, iwSigma, sigmaLeFinset, Finset.mem_biUnion] at hβ
  obtain ⟨A, hA, hβA⟩ := hβ
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, hAcard⟩ := hA
  rw [sigmaSubAFinset, Finset.mem_image] at hβA
  obtain ⟨a, ha_mem, hβeq⟩ := hβA
  rw [Finset.mem_range] at ha_mem
  have hApos : 0 < QA A := lt_of_le_of_lt (Nat.zero_le a) ha_mem
  have hAcard' : A.card ≤ ⌊2 / mstRho l⌋₊ + 1 := by simpa [iwK] using hAcard
  have hQbound : QA A ≤ ⌈Real.exp ((((s + 1) ^ l : ℕ) : ℝ) ^ (mstRho l))⌉₊ :=
    hN₁ ((s + 1) ^ l) hNle A hAsub hAcard'
  have hpow : ((((s + 1) ^ l : ℕ) : ℝ)) ^ (mstRho l) = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    rw [Nat.cast_pow]
    rw [mstTorsion_rho_pow l hl (s + 1) (by omega)]
    congr 1
    push_cast
    ring
  rw [hpow] at hQbound
  rw [← hβeq]
  exact mstTorsion_arcPt_fourier hApos (by rw [mstQ']; exact Nat.dvd_factorial hApos hQbound)

end Work.BourgainPlan.Maximal
