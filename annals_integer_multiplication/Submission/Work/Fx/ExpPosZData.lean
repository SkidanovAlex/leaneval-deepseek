import Mathlib
import Submission.Work.Fx.ExpPosDefs
import Submission.Work.Fx.ExpPosTdivKit
import Submission.Work.Fx.ExpPosExpBound

/-!
# The numerical data of the positive exponential field (paper Lemma 2.14)

Companion to `Work.Fx.ExpPosDefs`.  Given `P ≈ 2^Q π`, `L ≈ 2^Q log 2` (both within
`1`), `X = tdiv (P j) k`, with `e^{πj/k} ≤ 2^σ` and `σ ≤ 2p`, the derived integer
`Z = X - k₀ L - E` (where `k₀ = σ - τ`, `τ = max (tdiv (Al + L - 1) L) 0`) satisfies:

* `|Z| ≤ 32·2^Q` (so `Z/2^Q` is a bounded argument for the word `expc`);
* `e^{Z/2^Q} + 4/2^Q ≤ 2^τ` (so the truncated output has modulus `≤ 1`);
* `2^p |2^{-τ} e^{Z/2^Q} - 2^{-σ} e^{πj/k}| ≤ 1/2` (so the truncation is accurate
  to `p` bits).

The content is elementary but delicate integer/real arithmetic: the truncations
`tdiv` differ from the exact quotients by at most `1`, the guard `E = 32(p+60)`
absorbs the `p`-dependent errors, and `Q = 2p + 60` leaves 60 guard bits.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

/-! ## Elementary estimates -/

/-- `2^p · (64p + 4096) / 2^{2p+60} ≤ 1/2` for `p ≥ 100`: the `p`-dependent errors
accumulated in `Z` are killed by the 60 guard bits of `Q = 2p + 60`. -/
theorem expPosKeyNumber (p : ℕ) (hp : 100 ≤ p) :
    (2 : ℝ) ^ p * ((64 * (p : ℝ) + 4096) / (2 : ℝ) ^ (2 * p + 60)) ≤ 1 / 2 := by
  have hsplit : (2 : ℝ) ^ (2 * p + 60) = (2 : ℝ) ^ p * (2 : ℝ) ^ (p + 60) := by
    rw [show 2 * p + 60 = p + (p + 60) by ring, pow_add]
  have hnat : 128 * p + 8192 ≤ 2 ^ (p + 60) := by
    have h1 : p + 1 ≤ 2 ^ p := by have := Nat.lt_two_pow_self (n := p); omega
    have h2 : 128 * p + 8192 ≤ 8192 * (p + 1) := by omega
    have h3 : 8192 * (p + 1) ≤ 8192 * 2 ^ p := Nat.mul_le_mul_left 8192 h1
    have h4 : 8192 * 2 ^ p = 2 ^ (p + 13) := by
      rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, ← pow_add]; ring_nf
    have h5 : 2 ^ (p + 13) ≤ 2 ^ (p + 60) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hreal : (64 * (p : ℝ) + 4096) ≤ (2 : ℝ) ^ (p + 59) := by
    have hcast : ((128 * p + 8192 : ℕ) : ℝ) ≤ ((2 ^ (p + 60) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    have h2 : (2 : ℝ) ^ (p + 60) = 2 * (2 : ℝ) ^ (p + 59) := by
      rw [show p + 60 = (p + 59) + 1 by omega, pow_succ]; ring
    rw [h2] at hcast
    linarith
  have hpz : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hz : (0 : ℝ) < (2 : ℝ) ^ (p + 60) := by positivity
  have hsimp : (2 : ℝ) ^ p * ((64 * (p : ℝ) + 4096) / ((2 : ℝ) ^ p * (2 : ℝ) ^ (p + 60)))
      = (64 * (p : ℝ) + 4096) / (2 : ℝ) ^ (p + 60) := by
    field_simp
  rw [hsplit, hsimp, div_le_iff₀ hz]
  have h2 : (1 / 2 : ℝ) * (2 : ℝ) ^ (p + 60) = (2 : ℝ) ^ (p + 59) := by
    rw [show p + 60 = (p + 59) + 1 by omega, pow_succ]; ring
  rw [h2]
  linarith

/-- `2^σ = exp (σ log 2)` for a natural exponent. -/
theorem two_pow_nat_eq_exp (σ : ℕ) : (2 : ℝ) ^ σ = Real.exp ((σ : ℝ) * Real.log 2) := by
  calc (2 : ℝ) ^ σ = (Real.exp (Real.log 2)) ^ σ := by rw [Real.exp_log (by norm_num)]
    _ = Real.exp ((σ : ℝ) * Real.log 2) := (Real.exp_nat_mul (Real.log 2) σ).symm

/-- `2^{-σ} = exp (-(σ log 2))`. -/
theorem zpow_neg_two_nat_eq_exp (σ : ℕ) :
    (2 : ℝ) ^ (-(σ : ℤ)) = Real.exp (-((σ : ℝ) * Real.log 2)) := by
  rw [zpow_neg, zpow_natCast, two_pow_nat_eq_exp, Real.exp_neg]

/-- `exp` is `1`-Lipschitz on `(-∞,0]`, in the form needed below. -/
theorem exp_sub_le_of_le_nonpos {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    Real.exp b - Real.exp a ≤ b - a := by
  have hd : (0 : ℝ) ≤ b - a := by linarith
  have hexp : Real.exp a = Real.exp b / Real.exp (b - a) := by
    rw [← Real.exp_sub]; congr 1; ring
  have heq : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (-(b - a))) := by
    rw [hexp, Real.exp_neg]; field_simp
  have hb1 : Real.exp b ≤ 1 := Real.exp_le_one_iff.mpr hb
  have h1 : 1 - Real.exp (-(b - a)) ≤ b - a := by
    have h := Real.add_one_le_exp (-(b - a)); linarith
  have h2 : (0 : ℝ) ≤ 1 - Real.exp (-(b - a)) := by
    have h : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith); linarith
  rw [heq]
  nlinarith [mul_le_mul hb1 (le_refl (1 - Real.exp (-(b - a)))) h2 (by norm_num : (0 : ℝ) ≤ 1)]

/-- `|exp v - exp u| ≤ |v - u|` when both exponents are `≤ 0`. -/
theorem abs_exp_sub_le_of_nonpos {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp v - Real.exp u| ≤ |v - u| := by
  rcases le_total v u with h | h
  · have hvu : Real.exp v - Real.exp u ≤ 0 := by
      have : Real.exp v ≤ Real.exp u := Real.exp_le_exp.mpr h; linarith
    rw [abs_of_nonpos hvu, abs_of_nonpos (by linarith : v - u ≤ 0)]
    have := exp_sub_le_of_le_nonpos h hu
    linarith
  · have huv : (0 : ℝ) ≤ Real.exp v - Real.exp u := by
      have : Real.exp u ≤ Real.exp v := Real.exp_le_exp.mpr h; linarith
    rw [abs_of_nonneg huv, abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - u)]
    exact exp_sub_le_of_le_nonpos h hv

/-- The final relative-accuracy estimate for the truncated exponential data:
both `2^{-τ} e^{z/D}` and `2^{-σ} e^{πj/k}` are exponentials of nonpositive numbers
differing by at most `(64p+4096)/D`, and `2^p` times that is `≤ 1/2`. -/
theorem expPosApprox (p σ j k : ℕ) (τ : ℤ) (D z : ℝ)
    (_hD : 0 < D) (hτ : 0 ≤ τ)
    (hkey : (2 : ℝ) ^ p * ((64 * (p : ℝ) + 4096) / D) ≤ 1 / 2)
    (hu : Real.pi * (j : ℝ) / (k : ℝ) ≤ (σ : ℝ) * Real.log 2)
    (hv : z / D - (τ : ℝ) * Real.log 2 ≤ 0)
    (hδ : |z / D - (τ : ℝ) * Real.log 2 - (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)|
        ≤ (64 * (p : ℝ) + 4096) / D) :
    (2 : ℝ) ^ p * |(2 : ℝ) ^ (-τ) * Real.exp (z / D) -
        (2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ^ (-τ) * Real.exp (z / D) = Real.exp (z / D - (τ : ℝ) * Real.log 2) := by
    rw [zpow_neg, ← exp_intCast_mul_log_two τ hτ, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h2 : (2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ))
      = Real.exp (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2) := by
    rw [zpow_neg_two_nat_eq_exp, ← Real.exp_add]
    ring_nf
  rw [h1, h2]
  have hu' : Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2 ≤ 0 := by linarith
  have habs : |Real.exp (z / D - (τ : ℝ) * Real.log 2)
        - Real.exp (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)|
      ≤ |(z / D - (τ : ℝ) * Real.log 2) - (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)| :=
    abs_exp_sub_le_of_nonpos hu' hv
  have h3 : (2 : ℝ) ^ p * |Real.exp (z / D - (τ : ℝ) * Real.log 2)
        - Real.exp (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)|
      ≤ (2 : ℝ) ^ p * ((64 * (p : ℝ) + 4096) / D) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_trans habs hδ
  linarith [hkey]

/-- `72p + 3842 ≤ 2^{2p+60}`: the crude exponential bound supplying all the `p`-dependent
slack used below (`p ≥ 100`). -/
theorem expPosDbound (p : ℕ) (hp : 100 ≤ p) :
    72 * (p : ℝ) + 3842 ≤ (2 : ℝ) ^ (2 * p + 60) := by
  have h1 : p + 1 ≤ 2 ^ p := by have := Nat.lt_two_pow_self (n := p); omega
  have hnat : 72 * p + 3842 ≤ 2 ^ (2 * p + 60) := by
    have h2 : 72 * p + 3842 ≤ 4096 * (p + 1) := by omega
    have h3 : 4096 * (p + 1) ≤ 4096 * 2 ^ p := Nat.mul_le_mul_left 4096 h1
    have h4 : 4096 * 2 ^ p = 2 ^ (p + 12) := by
      rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, ← pow_add]; ring_nf
    have h5 : 2 ^ (p + 12) ≤ 2 ^ (2 * p + 60) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact_mod_cast hnat

/-- The numerical data of `Z`: bounds on `X`, `Al`, `τ`, `Z` and the final `δ` estimate. -/
theorem ExpPosZData (p j k σ : ℕ) (P L X : ℤ)
    (hp : 100 ≤ p) (hk : 1 ≤ k)
    (he : Real.exp (Real.pi * (j : ℝ) / (k : ℝ)) ≤ (2 : ℝ) ^ σ)
    (hσ : (σ : ℝ) ≤ 2 * (p : ℝ))
    (hP : |(P : ℝ) - (2 : ℝ) ^ (Work.Fx.epQ p) * Real.pi| ≤ 1)
    (hL : |(L : ℝ) - (2 : ℝ) ^ (Work.Fx.epQ p) * Real.log 2| ≤ 1)
    (hX : X = Work.Fx.epX P j k) :
    |((Work.Fx.epZ p σ X L (Work.Fx.epAl σ L X) : ℤ) : ℝ)| ≤ 32 * (2 : ℝ) ^ (Work.Fx.epQ p) ∧
    Real.exp ((Work.Fx.epZ p σ X L (Work.Fx.epAl σ L X) : ℝ) / (2 : ℝ) ^ (Work.Fx.epQ p)) +
        4 / (2 : ℝ) ^ (Work.Fx.epQ p) ≤ (2 : ℝ) ^ (Work.Fx.epTau (Work.Fx.epAl σ L X) L) ∧
    (2 : ℝ) ^ p * |(2 : ℝ) ^ (-(Work.Fx.epTau (Work.Fx.epAl σ L X) L)) *
        Real.exp ((Work.Fx.epZ p σ X L (Work.Fx.epAl σ L X) : ℝ) / (2 : ℝ) ^ (Work.Fx.epQ p)) -
        (2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 1 / 2 := by
  -- abbreviations
  set D : ℝ := (2 : ℝ) ^ (epQ p) with hDdef
  set Al : ℤ := epAl σ L X with hAldef
  set T : ℤ := epT Al L with hTdef
  set τ : ℤ := epTau Al L with hτdef
  set Z : ℤ := epZ p σ X L Al with hZdef
  -- ### constants
  have hpR : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hσnn : (0 : ℝ) ≤ (σ : ℝ) := by positivity
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkposZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  -- ### D
  have hDval : D = (2 : ℝ) ^ (2 * p + 60) := by
    rw [hDdef, show epQ p = ((2 * p + 60 : ℕ) : ℤ) from by simp [epQ], zpow_natCast]
  have hDbound : 72 * (p : ℝ) + 3842 ≤ D := by rw [hDval]; exact expPosDbound p hp
  have hDbig : (2000 : ℝ) ≤ D := by nlinarith [hDbound, hpR]
  have hDpos : (0 : ℝ) < D := by linarith
  have hDhalf : 36 * (p : ℝ) + 1921 ≤ D / 2 := by linarith [hDbound]
  have hD4p : 4 * (p : ℝ) + 1 ≤ D := by linarith [hDbound, hpR]
  have hD16p : 16 * (p : ℝ) + 4 ≤ D := by linarith [hDbound, hpR]
  -- ### P
  have hPabs := abs_le.mp hP
  have hDpi : (1 : ℝ) ≤ D * Real.pi := by
    have h1 : (2000 : ℝ) * 3 ≤ D * Real.pi :=
      mul_le_mul hDbig (le_of_lt hpi3) (by norm_num) (by linarith)
    linarith
  have hPge : (0 : ℝ) ≤ (P : ℝ) := by linarith [hPabs.1, hDpi]
  have hPgeZ : (0 : ℤ) ≤ P := by exact_mod_cast hPge
  -- ### L
  have hLabs := abs_le.mp hL
  have hLlow : D * Real.log 2 - 1 ≤ (L : ℝ) := by linarith [hLabs.1]
  have hLhigh : (L : ℝ) ≤ D * Real.log 2 + 1 := by linarith [hLabs.2]
  have hDlog : (3 : ℝ) ≤ D * Real.log 2 := by
    have h1 : (2000 : ℝ) * (1 / 2) ≤ D * Real.log 2 :=
      mul_le_mul hDbig hlog2half (by norm_num) (by linarith)
    linarith
  have hLge2 : (2 : ℤ) ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  have hLge1 : (1 : ℤ) ≤ L := by omega
  have hLge1r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLge1
  have hLposR : (0 : ℝ) < (L : ℝ) := by linarith
  have hLbig : (4 * (p : ℝ) + 1) ≤ (L : ℝ) := by
    have h2 : D / 2 ≤ D * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hlog2half (le_of_lt hDpos); linarith
    have h3 : 4 * (p : ℝ) + 1 ≤ D / 2 - 1 := by linarith [hDhalf, hpR]
    linarith
  have hLq : D / 4 ≤ (L : ℝ) := by
    have h2 : D / 2 ≤ D * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hlog2half (le_of_lt hDpos); linarith
    have h4 : D / 4 ≤ D / 2 - 1 := by linarith [hDbig]
    linarith
  -- ### X
  have hXval : X = Int.tdiv (P * (j : ℤ)) (k : ℤ) := by rw [hX]; rfl
  have hXnn : (0 : ℤ) ≤ P * (j : ℤ) := mul_nonneg hPgeZ (Int.natCast_nonneg j)
  have hkitX := ExpPosTdivKit (P * (j : ℤ)) (k : ℤ) hkposZ
  have hXle : (X : ℝ) ≤ (P : ℝ) * (j : ℝ) / (k : ℝ) := by
    have h := (hkitX.2.2.1 hXnn).1
    rw [hXval]
    push_cast at h ⊢
    exact h
  have hXlb : (P : ℝ) * (j : ℝ) / (k : ℝ) - (X : ℝ) ≤ 1 := by
    have h := (hkitX.2.2.1 hXnn).2
    rw [hXval]
    push_cast at h ⊢
    exact h
  have hX1 : |(X : ℝ) - (P : ℝ) * (j : ℝ) / (k : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  -- ### `π j / k ≤ σ log 2` and `j/k ≤ 2p`
  have hlogj : Real.pi * (j : ℝ) / (k : ℝ) ≤ (σ : ℝ) * Real.log 2 := by
    have h := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp, Real.log_pow] at h
    exact h
  have hjdiv : (j : ℝ) / (k : ℝ) ≤ 2 * (p : ℝ) := by
    have hxnn : (0 : ℝ) ≤ (j : ℝ) / (k : ℝ) := by positivity
    have h2p : (σ : ℝ) * Real.log 2 ≤ 2 * (p : ℝ) := by nlinarith [hσ, hlog2lt1, hσnn]
    have h1 : Real.pi * ((j : ℝ) / (k : ℝ)) ≤ 2 * (p : ℝ) := by
      have heq : Real.pi * (j : ℝ) / (k : ℝ) = Real.pi * ((j : ℝ) / (k : ℝ)) := by ring
      linarith [hlogj, h2p, heq.symm.le, heq.le]
    have h3x : 3 * ((j : ℝ) / (k : ℝ)) ≤ 2 * (p : ℝ) := by nlinarith [h1, hpi3, hxnn]
    nlinarith [h3x, hpnn]
  have hX2 : |(P : ℝ) * (j : ℝ) / (k : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 2 * (p : ℝ) := by
    have hjnn : (0 : ℝ) ≤ (j : ℝ) / (k : ℝ) := by positivity
    have heq : (P : ℝ) * (j : ℝ) / (k : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))
        = ((P : ℝ) - D * Real.pi) * ((j : ℝ) / (k : ℝ)) := by ring
    rw [heq, abs_mul, abs_of_nonneg hjnn]
    calc |(P : ℝ) - D * Real.pi| * ((j : ℝ) / (k : ℝ)) ≤ 1 * (2 * (p : ℝ)) :=
          mul_le_mul hP hjdiv hjnn (by norm_num)
      _ = 2 * (p : ℝ) := by ring
  have hXc : |(X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 2 * (p : ℝ) + 1 := by
    have heq : (X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))
        = ((X : ℝ) - (P : ℝ) * (j : ℝ) / (k : ℝ))
          + ((P : ℝ) * (j : ℝ) / (k : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))) := by ring
    have h := abs_add_le ((X : ℝ) - (P : ℝ) * (j : ℝ) / (k : ℝ))
      ((P : ℝ) * (j : ℝ) / (k : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
    rw [heq]
    linarith [h, hX1, hX2]
  -- ### Al
  have hAlval : (Al : ℝ) = (σ : ℝ) * (L : ℝ) - (X : ℝ) := by
    rw [hAldef]; simp only [epAl]; push_cast; ring
  have hAlD : |(Al : ℝ) - D * ((σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ))|
      ≤ 4 * (p : ℝ) + 1 := by
    have heq : (Al : ℝ) - D * ((σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ))
        = (σ : ℝ) * ((L : ℝ) - D * Real.log 2)
          + (D * (Real.pi * (j : ℝ) / (k : ℝ)) - (X : ℝ)) := by
      rw [hAlval]; ring
    have h1 : |(σ : ℝ) * ((L : ℝ) - D * Real.log 2)| ≤ 2 * (p : ℝ) := by
      rw [abs_mul, abs_of_nonneg hσnn]
      calc (σ : ℝ) * |(L : ℝ) - D * Real.log 2| ≤ (σ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hL hσnn
        _ = (σ : ℝ) := by ring
        _ ≤ 2 * (p : ℝ) := hσ
    have h2 : |D * (Real.pi * (j : ℝ) / (k : ℝ)) - (X : ℝ)| ≤ 2 * (p : ℝ) + 1 := by
      rw [abs_sub_comm]; exact hXc
    have h := abs_add_le ((σ : ℝ) * ((L : ℝ) - D * Real.log 2))
      (D * (Real.pi * (j : ℝ) / (k : ℝ)) - (X : ℝ))
    rw [heq]
    linarith [h, h1, h2]
  have hAlLB : -(4 * (p : ℝ) + 1) ≤ (Al : ℝ) := by
    have hnn : (0 : ℝ) ≤ (σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ) := by linarith [hlogj]
    have hmono : 0 ≤ D * ((σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ)) :=
      mul_nonneg (le_of_lt hDpos) hnn
    have h := abs_le.mp hAlD
    linarith [h.1]
  have hAlUB : (Al : ℝ) ≤ D * (2 * (p : ℝ)) + (4 * (p : ℝ) + 1) := by
    have hle : (σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ) ≤ 2 * (p : ℝ) := by
      have hzx : (0 : ℝ) ≤ Real.pi * (j : ℝ) / (k : ℝ) := by positivity
      have h2p : (σ : ℝ) * Real.log 2 ≤ 2 * (p : ℝ) := by nlinarith [hσ, hlog2lt1, hσnn]
      linarith
    have h := abs_le.mp hAlD
    have hmono : D * ((σ : ℝ) * Real.log 2 - Real.pi * (j : ℝ) / (k : ℝ)) ≤ D * (2 * (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hDpos)
    linarith [h.2]
  -- ### τ
  have hkitT := ExpPosTdivKit (Al + L - 1) L hLge1
  have hTval : T = Int.tdiv (Al + L - 1) L := by rw [hTdef]; rfl
  have hTabs : |(T : ℝ) * (L : ℝ) - ((Al : ℝ) + (L : ℝ) - 1)| ≤ (L : ℝ) := by
    have h := hkitT.1
    rw [hTval]
    have h3 : |((Int.tdiv (Al + L - 1) L * L - (Al + L - 1) : ℤ) : ℝ)| ≤ ((L : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h3
    exact h3
  have hτval : τ = max T 0 := by rw [hτdef]; rfl
  have hτnn : (0 : ℤ) ≤ τ := by rw [hτval]; exact le_max_right _ _
  have hτT : (T : ℝ) ≤ (τ : ℝ) := by
    rw [hτval]; exact_mod_cast (le_max_left T 0)
  have hτLlow : (Al : ℝ) - 1 ≤ (τ : ℝ) * (L : ℝ) := by
    have h := abs_le.mp hTabs
    have h1 : (Al : ℝ) - 1 ≤ (T : ℝ) * (L : ℝ) := by linarith [h.1]
    have h2 : (T : ℝ) * (L : ℝ) ≤ (τ : ℝ) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hτT (le_of_lt hLposR)
    linarith
  have hτLup : (τ : ℝ) * (L : ℝ) ≤ (Al : ℝ) + 2 * (L : ℝ) := by
    rcases le_total (0 : ℤ) T with hT | hT
    · have hτT' : τ = T := by rw [hτval, max_eq_left hT]
      have h := abs_le.mp hTabs
      rw [hτT']; linarith [h.2]
    · have hτ0 : τ = 0 := by rw [hτval, max_eq_right hT]
      rw [hτ0]; push_cast
      linarith [hAlLB, hLbig, hpR]
  have hτ1Al : 1 ≤ τ → (1 : ℝ) ≤ (Al : ℝ) := by
    intro h1
    have hT1 : 1 ≤ T := by
      rw [hτval] at h1
      rcases le_total (0 : ℤ) T with hT | hT
      · rwa [max_eq_left hT] at h1
      · rw [max_eq_right hT] at h1; omega
    have hy0 : (0 : ℤ) ≤ Al + L - 1 := by
      have h := abs_le.mp hTabs
      have hTL : (1 : ℝ) * (L : ℝ) ≤ (T : ℝ) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hT1) (le_of_lt hLposR)
      have : (0 : ℝ) ≤ (Al : ℝ) + (L : ℝ) - 1 := by linarith [h.1, hTL]
      exact_mod_cast this
    have hiff := hkitT.2.2.2.1 hy0
    have hT1' : 1 ≤ Int.tdiv (Al + L - 1) L := by rw [← hTval]; exact hT1
    have hLle : L ≤ Al + L - 1 := hiff.mp hT1'
    have : (1 : ℤ) ≤ Al := by omega
    exact_mod_cast this
  have hτ0Al : τ = 0 → (Al : ℝ) < 1 := by
    intro h0
    have hTle : T ≤ 0 := by rw [hτval] at h0; omega
    by_contra hcon
    have hcon' : (1 : ℝ) ≤ (Al : ℝ) := not_lt.mp hcon
    have hAl1 : (1 : ℤ) ≤ Al := by exact_mod_cast hcon'
    have hy0 : (0 : ℤ) ≤ Al + L - 1 := by omega
    have hiff := hkitT.2.2.2.1 hy0
    have h1 : 1 ≤ Int.tdiv (Al + L - 1) L := hiff.mpr (by omega)
    rw [← hTval] at h1
    omega
  have hτ8p : (τ : ℝ) ≤ 8 * (p : ℝ) + 8 := by
    rcases le_total (0 : ℤ) T with hT | hT
    · have hτT' : τ = T := by rw [hτval, max_eq_left hT]
      have hTLup : (T : ℝ) * (L : ℝ) ≤ (Al : ℝ) + 2 * (L : ℝ) := by
        have h := abs_le.mp hTabs; linarith [h.2]
      have h1 : (τ : ℝ) ≤ (Al : ℝ) / (L : ℝ) + 2 := by
        rw [hτT']
        have h2 : (T : ℝ) ≤ ((Al : ℝ) + 2 * (L : ℝ)) / (L : ℝ) := by
          rw [le_div_iff₀ hLposR]; linarith [hTLup]
        have h3 : ((Al : ℝ) + 2 * (L : ℝ)) / (L : ℝ) = (Al : ℝ) / (L : ℝ) + 2 := by
          field_simp
        linarith
      have h2 : (Al : ℝ) / (L : ℝ) ≤ 8 * (p : ℝ) + 4 := by
        have hAlD2 : (Al : ℝ) ≤ 2 * (p : ℝ) * D + (4 * (p : ℝ) + 1) := by linarith [hAlUB]
        rw [div_le_iff₀ hLposR]
        have h1 : (2 * (p : ℝ) + 1) * D ≤ (8 * (p : ℝ) + 4) * (L : ℝ) := by
          nlinarith [hLq, hDpos]
        have h2 : 2 * (p : ℝ) * D + (4 * (p : ℝ) + 1) ≤ (2 * (p : ℝ) + 1) * D := by
          linarith [hD4p]
        linarith [hAlD2, h1, h2]
      linarith [h1, h2]
    · have hτ0 : τ = 0 := by rw [hτval, max_eq_right hT]
      rw [hτ0]; push_cast; nlinarith [hpR]
  -- ### Z
  have hZval : (Z : ℝ) = (X : ℝ) - ((σ : ℝ) - (τ : ℝ)) * (L : ℝ) - (32 * (p : ℝ) + 1920) := by
    have h1 : Z = X - ((σ : ℤ) - τ) * L - epE p := by
      rw [hZdef]; simp only [epZ, epK0]; rw [← hτdef]
    rw [h1]
    have h2 : (epE p : ℤ) = 32 * ((p : ℤ) + 60) := by simp [epE, epA]
    rw [h2]
    push_cast
    ring
  have hZval' : (Z : ℝ) = (τ : ℝ) * (L : ℝ) - (Al : ℝ) - (32 * (p : ℝ) + 1920) := by
    rw [hZval, hAlval]; ring
  have hZ0 : τ = 0 → (Z : ℝ) ≤ -2000 := by
    intro h0
    have hZ0' : (Z : ℝ) = -(Al : ℝ) - (32 * (p : ℝ) + 1920) := by
      rw [hZval, h0]; push_cast; rw [hAlval]; ring
    rw [hZ0']
    nlinarith [hAlLB, hpR]
  have hZmain : (Z : ℝ) ≤ (τ : ℝ) * Real.log 2 * D - 4 := by
    rcases eq_or_lt_of_le hτnn with h0 | hpos
    · have := hZ0 h0.symm
      rw [← h0]; push_cast; linarith
    · have hAl1 : (1 : ℝ) ≤ (Al : ℝ) := hτ1Al (by omega)
      have hτE : (τ : ℝ) ≤ 32 * (p : ℝ) + 1916 := by linarith [hτ8p, hpR]
      have hZeq : (Z : ℝ) = (τ : ℝ) * ((L : ℝ) - D * Real.log 2)
          + (τ : ℝ) * Real.log 2 * D - (Al : ℝ) - (32 * (p : ℝ) + 1920) := by
        rw [hZval']; ring
      have hLm : (L : ℝ) - D * Real.log 2 ≤ 1 := by linarith [hLhigh]
      have h1 : (τ : ℝ) * ((L : ℝ) - D * Real.log 2) ≤ (τ : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hLm (by positivity)
      nlinarith [hZeq, h1, hAl1, hτE]
  have hZabs : |(Z : ℝ)| ≤ 32 * D := by
    rw [abs_le]; constructor
    · have hτLnn : (0 : ℝ) ≤ (τ : ℝ) * (L : ℝ) := by positivity
      nlinarith [hAlLB, hZval', hτLnn, hDbound, hpR]
    · have hZup : (Z : ℝ) ≤ 2 * (L : ℝ) := by nlinarith [hZval', hτLup]
      have hLup : 2 * (L : ℝ) ≤ 2 * (D * Real.log 2 + 1) := by linarith [hLhigh]
      have h2 : 2 * (D * Real.log 2 + 1) ≤ 32 * D := by nlinarith [hDbig, hlog2lt1, hDpos]
      linarith
  -- ### the final `δ` estimate
  have hv : (Z : ℝ) / D - (τ : ℝ) * Real.log 2 ≤ 0 := by
    have h : (Z : ℝ) / D ≤ (τ : ℝ) * Real.log 2 := by
      rw [div_le_iff₀ hDpos]; nlinarith [hZmain]
    linarith
  have hδ : |(Z : ℝ) / D - (τ : ℝ) * Real.log 2
        - (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)| ≤ (64 * (p : ℝ) + 4096) / D := by
    have hid : (Z : ℝ) / D - (τ : ℝ) * Real.log 2
          - (Real.pi * (j : ℝ) / (k : ℝ) - (σ : ℝ) * Real.log 2)
        = ((σ : ℝ) * (D * Real.log 2 - (L : ℝ)) + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
            + (τ : ℝ) * ((L : ℝ) - D * Real.log 2) - (32 * (p : ℝ) + 1920)) / D := by
      rw [hZval]; field_simp; ring
    rw [hid, abs_div, abs_of_pos hDpos]
    have h1 : |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))| ≤ 2 * (p : ℝ) := by
      rw [abs_mul, abs_of_nonneg hσnn, abs_sub_comm]
      calc (σ : ℝ) * |(L : ℝ) - D * Real.log 2| ≤ (σ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hL hσnn
        _ = (σ : ℝ) := by ring
        _ ≤ 2 * (p : ℝ) := hσ
    have h3 : |(τ : ℝ) * ((L : ℝ) - D * Real.log 2)| ≤ 8 * (p : ℝ) + 8 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (τ : ℝ))]
      calc (τ : ℝ) * |(L : ℝ) - D * Real.log 2| ≤ (τ : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hL (by positivity)
        _ = (τ : ℝ) := by ring
        _ ≤ 8 * (p : ℝ) + 8 := hτ8p
    have hE : |(32 * (p : ℝ) + 1920)| = 32 * (p : ℝ) + 1920 := abs_of_nonneg (by positivity)
    have hAB : |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
        + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))| ≤ 4 * (p : ℝ) + 1 := by
      have h := abs_add_le ((σ : ℝ) * (D * Real.log 2 - (L : ℝ)))
        ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
      linarith [h, h1, hXc]
    have hABC : |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
        + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
        + (τ : ℝ) * ((L : ℝ) - D * Real.log 2)| ≤ 12 * (p : ℝ) + 9 := by
      have h := abs_add_le ((σ : ℝ) * (D * Real.log 2 - (L : ℝ))
          + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ))))
        ((τ : ℝ) * ((L : ℝ) - D * Real.log 2))
      linarith [h, hAB, h3]
    have hnum : |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
        + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
        + (τ : ℝ) * ((L : ℝ) - D * Real.log 2) - (32 * (p : ℝ) + 1920)| ≤ 44 * (p : ℝ) + 1929 := by
      have h := abs_add_le ((σ : ℝ) * (D * Real.log 2 - (L : ℝ))
          + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
          + (τ : ℝ) * ((L : ℝ) - D * Real.log 2)) (-(32 * (p : ℝ) + 1920))
      rw [abs_neg, hE] at h
      have h3 : |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
          + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
          + (τ : ℝ) * ((L : ℝ) - D * Real.log 2) - (32 * (p : ℝ) + 1920)|
          = |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
          + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
          + (τ : ℝ) * ((L : ℝ) - D * Real.log 2) + (-(32 * (p : ℝ) + 1920))| := by
        rw [sub_eq_add_neg]
      rw [h3]
      linarith [h, hABC]
    calc |(σ : ℝ) * (D * Real.log 2 - (L : ℝ))
          + ((X : ℝ) - D * (Real.pi * (j : ℝ) / (k : ℝ)))
          + (τ : ℝ) * ((L : ℝ) - D * Real.log 2) - (32 * (p : ℝ) + 1920)| / D
        ≤ (44 * (p : ℝ) + 1929) / D := div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
      _ ≤ (64 * (p : ℝ) + 4096) / D := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hDpos)
          linarith [hpR]
  have hkey : (2 : ℝ) ^ p * ((64 * (p : ℝ) + 4096) / D) ≤ 1 / 2 := by
    rw [hDval]; exact expPosKeyNumber p hp
  refine ⟨hZabs, ?_, ?_⟩
  · exact ExpPosExpBound (Z : ℝ) D τ hDbig hτnn hZmain hZ0
  · exact expPosApprox p σ j k τ D (Z : ℝ) hDpos hτnn hkey hlogj hv hδ

end Work.Fx
