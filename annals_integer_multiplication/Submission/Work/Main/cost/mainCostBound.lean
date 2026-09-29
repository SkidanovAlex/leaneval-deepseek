import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.param.tsSum_pow_le
import Submission.Work.Main.param.smallCosts
import Submission.Work.MainP.TparFacts
import Submission.Work.MainP.AparFacts

set_option maxHeartbeats 4000000

/-!
# `totalCost ≤ mainCost` for the main step (paper Prop 5.4)

The target `Work.Main.cost.mainCostBound` is a pure arithmetic estimate: every summand of
`totalCost` (the four stage costs produced by `step.setup`, `step.prep`, `step.finalize`,
`final.finalWord`) is dominated either by the `Cm`-term of `HvdH.mainCost` (via monotonicity of
`Cm` and `K53 ≤ K0`) or by `K0 · n · log₂ n` (via `KX ≤ K0/10⁷` for the stage constants `KX`).

The supporting arithmetic (`T·b < 8n`, `b = log₂ n ≥ 2^61`, `S = ∏ss ≤ T`, `α⁴ ≥ 12d²b`, the
`vsz`/`envsz` bounds) is isolated in the lemmas below.
-/

namespace Work.Main.cost

open HvdH

/-- The sum of the six stage constants (plus one). -/
def Ksum (KPar Ksetup Kprep Kfin Kepi K53 : ℕ) : ℕ :=
  KPar + Ksetup + Kprep + Kfin + Kepi + K53 + 1

/-- `bpar n ≤ n.size`. -/
theorem bpar_le_size (n : ℕ) : HvdH.bpar n ≤ n.size := by
  rw [HvdH.bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact le_of_lt (Nat.lt_size_self n)

/-- `n.size ≤ n` (for `n ≥ 1`; for `n ≤ 1` it is trivial). -/
theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- `1 ≤ n` from the hypothesis `T·b < 8n`. -/
theorem one_le_n {n : ℕ} (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) : 1 ≤ n := by
  have h := Nat.zero_le (HvdH.Tpar n * HvdH.bpar n)
  omega

/-- `Tpar n ≤ n` (from `T·b < 8n` and `b ≥ 8`). -/
theorem tpar_le_n {n : ℕ} (h261 : 2 ^ 61 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) : HvdH.Tpar n ≤ n := by
  have hb8 : 8 ≤ HvdH.bpar n := by omega
  have h1 : HvdH.Tpar n * 8 ≤ HvdH.Tpar n * HvdH.bpar n := Nat.mul_le_mul_left _ hb8
  have h2 : HvdH.Tpar n * 8 < 8 * n := lt_of_le_of_lt h1 hTb
  omega

/-- `T · (√p+1) · α · p ≤ 1000 · n · log₂ n` for `b = bpar n ≥ 2^61`, `p = ppar n`, `α = apar n`.
From `α² < p`: `(√p+1)·α ≤ (√p+1)·√p ≤ 2p`; and `T·p = 6·(T·b) ≤ 48n`, so the product is at most
`2·48·p = 576·b` times `n`, and `b ≤ n.size`. -/
theorem alphaTermLe {n : ℕ} (h261 : 2 ^ 61 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) :
    HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n
      ≤ 1000 * (n * n.size) := by
  have ha2 : HvdH.apar n ^ 2 < HvdH.ppar n := (Work.MainP.AparFacts n h261).2.2.1
  have hle : HvdH.apar n ≤ Nat.sqrt (HvdH.ppar n) := Nat.le_sqrt'.mpr (le_of_lt ha2)
  have hn1 : 1 ≤ n := one_le_n hTb
  have hbs : HvdH.bpar n ≤ n.size := bpar_le_size n
  have hTp : HvdH.Tpar n * HvdH.ppar n ≤ 48 * n := by
    have h : HvdH.Tpar n * HvdH.ppar n = 6 * (HvdH.Tpar n * HvdH.bpar n) := by
      rw [HvdH.ppar]; ring
    rw [h]; omega
  have hsq : (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n ≤ 2 * HvdH.ppar n := by
    have h1 : Nat.sqrt (HvdH.ppar n) ^ 2 ≤ HvdH.ppar n := Nat.sqrt_le' _
    have h2 : Nat.sqrt (HvdH.ppar n) ≤ HvdH.ppar n := Nat.sqrt_le_self _
    nlinarith [hle, h1, h2, Nat.zero_le (Nat.sqrt (HvdH.ppar n))]
  calc HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n
      = (HvdH.Tpar n * HvdH.ppar n) * ((Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n) := by ring
    _ ≤ (48 * n) * (2 * HvdH.ppar n) := Nat.mul_le_mul hTp hsq
    _ = 576 * (n * HvdH.bpar n) := by rw [HvdH.ppar]; ring
    _ ≤ 576 * (n * n.size) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n hbs)
    _ ≤ 1000 * (n * n.size) := Nat.mul_le_mul_right _ (by norm_num)

/-- The dominating preparation term:
`(S+1)·(V+V'+b+p+1)·(S.size+1) ≤ 5600000·n·log₂n` for `S ≤ T`, `V,V' ≤ 115200·(log₂n+1)`.
`(T+1)·(log₂n+1) ≤ 12n` and `V+V'+7b+1 ≤ 460816·log₂n`. -/
theorem prepTermLe {n S V V' : ℕ} (h261 : 2 ^ 61 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) (hS : S ≤ HvdH.Tpar n)
    (hV : V ≤ 115200 * (n.size + 1)) (hV' : V' ≤ 115200 * (n.size + 1)) :
    (S + 1) * (V + V' + HvdH.bpar n + HvdH.ppar n + 1) * (S.size + 1)
      ≤ 5600000 * (n * n.size) := by
  have hn1 : 1 ≤ n := one_le_n hTb
  have hnspos : 1 ≤ n.size := Nat.size_pos.mpr hn1
  have hbs : HvdH.bpar n ≤ n.size := bpar_le_size n
  have hTle : HvdH.Tpar n ≤ n := tpar_le_n h261 hTb
  have hSsize : S.size ≤ n.size := Nat.size_le_size (le_trans hS hTle)
  have hnZ : n ≤ n * n.size := Nat.le_mul_of_pos_right n hnspos
  -- middle factor
  have hmid : V + V' + HvdH.bpar n + HvdH.ppar n + 1 ≤ 460816 * n.size := by
    have hpp : HvdH.ppar n = 6 * HvdH.bpar n := rfl
    have h1 : V + V' ≤ 230400 * (n.size + 1) := by omega
    have h2 : 230400 * (n.size + 1) + 7 * HvdH.bpar n + 1 ≤ 230408 * (n.size + 1) := by
      nlinarith [hbs]
    have h3 : 230408 * (n.size + 1) ≤ 460816 * n.size := by nlinarith [hnspos]
    rw [hpp]
    omega
  -- outer factors
  have hout : (S + 1) * (S.size + 1) ≤ 12 * n := by
    have hTb' : HvdH.Tpar n * HvdH.bpar n ≤ 8 * n := le_of_lt hTb
    have hnb1 : n.size ≤ HvdH.bpar n + 1 := by
      rw [Nat.size_le]
      have h : n ≤ 2 ^ HvdH.bpar n := by
        simpa [HvdH.bpar] using Nat.le_pow_clog (by norm_num : 1 < 2) n
      exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))
    have h1 : S + 1 ≤ HvdH.Tpar n + 1 := by omega
    have h2 : S.size + 1 ≤ n.size + 1 := by omega
    have h3 : (HvdH.Tpar n + 1) * (n.size + 1) ≤ 12 * n := by
      have hTnb : HvdH.Tpar n * n.size ≤ 9 * n := by
        have h4 : HvdH.Tpar n * (HvdH.bpar n + 1) ≤ 9 * n := by nlinarith [hTb']
        exact (Nat.mul_le_mul_left _ hnb1).trans h4
      nlinarith [hTnb, hTle, size_le_self n, hn1]
    exact (Nat.mul_le_mul h1 h2).trans h3
  calc (S + 1) * (V + V' + HvdH.bpar n + HvdH.ppar n + 1) * (S.size + 1)
      = ((S + 1) * (S.size + 1)) * (V + V' + HvdH.bpar n + HvdH.ppar n + 1) := by ring
    _ ≤ (12 * n) * (460816 * n.size) := Nat.mul_le_mul hout hmid
    _ = 5529792 * (n * n.size) := by ring
    _ ≤ 5600000 * (n * n.size) := Nat.mul_le_mul_right _ (by norm_num)

/-- The four `S`-linear `Kfin`/`Kepi`/`Kprep` factors, all dominated by
`(S+1)·b² ≤ 9·n·log₂n` (with `b = bpar n`, `p = ppar n = 6b`, `d = D = 1729`). -/
theorem kinTerms {n S : ℕ} (h261 : 2 ^ 61 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n) (hS : S ≤ HvdH.Tpar n) :
    (S + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1) ≤ 441 * (n * n.size) ∧
    (S + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1) ≤ 763000 * (n * n.size) ∧
    (S + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1) ≤ 220000 * (n * n.size) ∧
    (S + 1) * (HvdH.bpar n + 1) ≤ 18 * (n * n.size) := by
  have hn1 : 1 ≤ n := one_le_n hTb
  have hnspos : 1 ≤ n.size := Nat.size_pos.mpr hn1
  have hbs : HvdH.bpar n ≤ n.size := bpar_le_size n
  have hbn : HvdH.bpar n ≤ n := le_trans hbs (size_le_self n)
  have hb1 : 1 ≤ HvdH.bpar n := by omega
  have hZ1 : n.size ≤ n * n.size := by
    calc n.size = n.size * 1 := (Nat.mul_one _).symm
      _ ≤ n.size * n := Nat.mul_le_mul_left _ hn1
      _ = n * n.size := Nat.mul_comm _ _
  have hZn : 1 ≤ n * n.size := by
    have := Nat.mul_le_mul hn1 hnspos
    simpa using this
  -- the core estimate
  have hbb : HvdH.bpar n * HvdH.bpar n ≤ n * n.size := by nlinarith [hbs, hbn]
  have hTbb : HvdH.Tpar n * (HvdH.bpar n * HvdH.bpar n) ≤ 8 * (n * n.size) := by
    nlinarith [hTb, hbs]
  have hcore : (S + 1) * (HvdH.bpar n * HvdH.bpar n) ≤ 9 * (n * n.size) := by
    have hSbb : S * (HvdH.bpar n * HvdH.bpar n) ≤ HvdH.Tpar n * (HvdH.bpar n * HvdH.bpar n) :=
      Nat.mul_le_mul_right _ hS
    have h3 : (S + 1) * (HvdH.bpar n * HvdH.bpar n)
        = S * (HvdH.bpar n * HvdH.bpar n) + HvdH.bpar n * HvdH.bpar n := by ring
    rw [h3]
    calc S * (HvdH.bpar n * HvdH.bpar n) + HvdH.bpar n * HvdH.bpar n
        ≤ HvdH.Tpar n * (HvdH.bpar n * HvdH.bpar n) + n * n.size := add_le_add hSbb hbb
      _ ≤ 8 * (n * n.size) + n * n.size := add_le_add hTbb le_rfl
      _ = 9 * (n * n.size) := by ring
  -- `(p+1)² ≤ 49b²`, `p+1 ≤ 7b`, `b+1 ≤ 2b`
  have hpp49 : (HvdH.ppar n + 1) * (HvdH.ppar n + 1) ≤ 49 * (HvdH.bpar n * HvdH.bpar n) := by
    rw [HvdH.ppar]
    nlinarith [hb1]
  have hpp7 : HvdH.ppar n + 1 ≤ 7 * HvdH.bpar n := by
    rw [HvdH.ppar]; omega
  have hpb2 : HvdH.bpar n + 1 ≤ 2 * HvdH.bpar n := by omega
  have hD : HvdH.D + 1 = 1730 := by norm_num [HvdH.D]
  have hk1 : (S + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1) ≤ 441 * (n * n.size) := by
    calc (S + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        = (S + 1) * ((HvdH.ppar n + 1) * (HvdH.ppar n + 1)) := by ring
      _ ≤ (S + 1) * (49 * (HvdH.bpar n * HvdH.bpar n)) := Nat.mul_le_mul_left _ hpp49
      _ = 49 * ((S + 1) * (HvdH.bpar n * HvdH.bpar n)) := by ring
      _ ≤ 49 * (9 * (n * n.size)) := Nat.mul_le_mul_left _ hcore
      _ = 441 * (n * n.size) := by ring
  refine ⟨hk1, ?_, ?_, ?_⟩
  · calc (S + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        = 1730 * ((S + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)) := by rw [hD]; ring
      _ ≤ 1730 * (441 * (n * n.size)) := Nat.mul_le_mul_left _ hk1
      _ = 762930 * (n * n.size) := by ring
      _ ≤ 763000 * (n * n.size) := Nat.mul_le_mul_right _ (by norm_num)
  · calc (S + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1)
        = 1730 * ((S + 1) * ((HvdH.ppar n + 1) * (HvdH.bpar n + 1))) := by rw [hD]; ring
      _ ≤ 1730 * ((S + 1) * ((7 * HvdH.bpar n) * (2 * HvdH.bpar n))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul hpp7 hpb2))
      _ = 24220 * ((S + 1) * (HvdH.bpar n * HvdH.bpar n)) := by ring
      _ ≤ 24220 * (9 * (n * n.size)) := Nat.mul_le_mul_left _ hcore
      _ = 217980 * (n * n.size) := by ring
      _ ≤ 220000 * (n * n.size) := Nat.mul_le_mul_right _ (by norm_num)
  · have h2 : 2 * HvdH.bpar n ≤ 2 * (n * n.size) :=
      Nat.mul_le_mul_left 2 (le_trans hbs hZ1)
    calc (S + 1) * (HvdH.bpar n + 1)
        ≤ (HvdH.Tpar n + 1) * (2 * HvdH.bpar n) :=
          Nat.mul_le_mul (by omega) hpb2
      _ = 2 * (HvdH.Tpar n * HvdH.bpar n) + 2 * HvdH.bpar n := by ring
      _ ≤ 2 * (8 * n) + 2 * (n * n.size) := add_le_add (by omega) h2
      _ = 16 * n + 2 * (n * n.size) := by ring
      _ ≤ 18 * (n * n.size) := by nlinarith [Nat.le_mul_of_pos_right n hnspos, hZn]

/-- The product of two parameters bounded by `K0/10⁷` is at most `log₂ n` (given `256K0² ≤ bpar n`). -/
theorem factorSmall {n K0 K K' : ℕ} (hbK : 256 * K0 ^ 2 ≤ HvdH.bpar n) (h1 : K ≤ K0)
    (h2 : K' ≤ K0) : K * K' ≤ n.size := by
  have h3 : K * K' ≤ K0 ^ 2 := by
    calc K * K' ≤ K0 * K0 := Nat.mul_le_mul h1 h2
      _ = K0 ^ 2 := by ring
  have h4 : K0 ^ 2 ≤ 256 * K0 ^ 2 := Nat.le_mul_of_pos_left _ (by norm_num)
  exact le_trans h3 (le_trans h4 (le_trans hbK (bpar_le_size n)))

/-- A power of `log₂ n` is dominated by `n`: for `m ≤ n` and `256K² ≤ bpar n`,
`(m.size + 1)^K ≤ n`. -/
theorem powSizeLe {n m K : ℕ} (h261 : 2 ^ 61 ≤ HvdH.bpar n) (hm : m ≤ n)
    (hbK : 256 * K ^ 2 ≤ HvdH.bpar n) : (m.size + 1) ^ K ≤ n := by
  have hb1 : 1 ≤ HvdH.bpar n := by omega
  have hn2 : 1 < n := Work.MainP.one_lt_of_bpar_pos n hb1
  have hn1 : 1 ≤ n := le_of_lt hn2
  rcases Nat.eq_zero_or_pos K with hK | hK
  · rw [hK, pow_zero]; exact hn1
  · have h1 : m.size ≤ HvdH.bpar n + 1 := by
      rw [Nat.size_le]
      have h2 : m ≤ 2 ^ HvdH.bpar n := le_trans hm (Nat.le_pow_clog (by norm_num : 1 < 2) n)
      exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))
    have h3 : (m.size + 1) ^ K ≤ (HvdH.bpar n + 3) ^ K := Nat.pow_le_pow_left (by omega) K
    have h4 : (HvdH.bpar n + 3) ^ K ≤ 2 ^ (HvdH.bpar n - 1) := Work.Main.param.pow3_le _ _ hK hbK
    have h5 : 2 ^ (HvdH.bpar n - 1) ≤ n := by
      have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num : 1 < 2) hn2
      simp only [Nat.pred_eq_sub_one] at h
      have hbpar : HvdH.bpar n = Nat.clog 2 n := rfl
      rw [hbpar]
      exact le_of_lt h
    exact h3.trans (h4.trans h5)

theorem mainCostBound {n KPar Ksetup Kprep Kfin Kepi K53 K0 : ℕ} {Cm : ℕ → ℕ} {sp : SP}
    (hmono : Monotone Cm)
    (hK0 : 10000000 * (KPar + Ksetup + Kprep + Kfin + Kepi + K53 + 1) ≤ K0)
    (hb : sp.b = HvdH.bpar n) (hp : sp.p = HvdH.ppar n) (ha : sp.α = HvdH.apar n)
    (hN : sp.N' = Work.Main.nchunks n (HvdH.bpar n))
    (hS : sp.S = sp.ss.prod)
    (hlmax : HvdH.lmax sp.ts = HvdH.rpar n) (hT : sp.ts.prod = HvdH.Tpar n)
    (hx : sp.x.size ≤ n) (hy : sp.y.size ≤ n)
    (hbK : 256 * K0 ^ 2 ≤ HvdH.bpar n)
    (h261 : 2 ^ 61 ≤ HvdH.bpar n)
    (hTb : HvdH.Tpar n * HvdH.bpar n < 8 * n)
    (hnb : n ≤ 2 ^ HvdH.bpar n)
    (hSle : sp.ss.prod ≤ HvdH.Tpar n)
    (hN2 : 2 * sp.N' ≤ sp.ss.prod + 1)
    (hvszts : HvdH.vsz (HvdH.intList sp.ts) ≤ 115200 * (n.size + 1))
    (hvszss : HvdH.vsz (HvdH.intList sp.ss) ≤ 115200 * (n.size + 1))
    (henv : envsz sp ≤ 300000 * (n.size + 1) + 3 * n)
    (hOK : HvdH.ParamOK n sp.ts sp.ss) :
    totalCost KPar Ksetup Kprep Kfin Kepi K53 Cm sp ≤ HvdH.mainCost K0 Cm n := by
  -- ## basic facts
  have hn1 : 1 ≤ n := one_le_n hTb
  have hnspos : 1 ≤ n.size := Nat.size_pos.mpr hn1
  have hbs : HvdH.bpar n ≤ n.size := bpar_le_size n
  have hszle : n.size ≤ n := size_le_self n
  have hbn : HvdH.bpar n ≤ n := le_trans hbs hszle
  have hTle : HvdH.Tpar n ≤ n := tpar_le_n h261 hTb
  have hZ1 : n.size ≤ n * n.size := by
    calc n.size = n.size * 1 := (Nat.mul_one _).symm
      _ ≤ n.size * n := Nat.mul_le_mul_left _ hn1
      _ = n * n.size := Nat.mul_comm _ _
  have hnZ : n ≤ n * n.size := Nat.le_mul_of_pos_right n hnspos
  have hZn : 1 ≤ n * n.size := by
    have := Nat.mul_le_mul hn1 hnspos
    simpa using this
  -- ## the constant `Ksum`
  have hKS : 10000000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 ≤ K0 := hK0
  have hKS1 : 1 ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by
    simp only [Ksum]; omega
  have hParK0 : KPar ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hSetupK0 : Ksetup ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hPrepK0 : Kprep ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hFinK0 : Kfin ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hEpiK0 : Kepi ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hK53K0 : K53 ≤ K0 := by
    simp only [Ksum] at hKS
    omega
  have hParS : KPar ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hSetupS : Ksetup ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hPrepS : Kprep ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hFinS : Kfin ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hEpiS : Kepi ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hK53S : K53 ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := by simp only [Ksum]; omega
  have hbKpar : 256 * KPar ^ 2 ≤ HvdH.bpar n := by nlinarith [hbK, hParK0]
  have hbK53 : 256 * K53 ^ 2 ≤ HvdH.bpar n := by nlinarith [hbK, hK53K0]
  -- ## unfold the goal
  simp only [totalCost, HvdH.mainCost, HvdH.fsCost, HvdH.resCost]
  rw [hb, hp, ha, hS, hN, hlmax, hT]
  -- ## the `Cm`-term of the resampling cost
  have hQ1a : 6 * (K53 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n
        * Cm (K53 * HvdH.ppar n))
      ≤ K0 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * Cm (K0 * HvdH.ppar n) := by
    have h6 : 6 * K53 ≤ K0 := by omega
    have hcm : Cm (K53 * HvdH.ppar n) ≤ Cm (K0 * HvdH.ppar n) :=
      hmono (Nat.mul_le_mul_right _ hK53K0)
    calc 6 * (K53 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n
          * Cm (K53 * HvdH.ppar n))
        = (6 * K53) * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n
          * Cm (K53 * HvdH.ppar n) := by ring
      _ ≤ K0 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n
          * Cm (K0 * HvdH.ppar n) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h6 le_rfl) le_rfl)
            le_rfl) hcm
  -- ## the small terms
  have hP1 : KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * Ksetup
      ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have hpow : ((max sp.x.size sp.y.size).size + 1) ^ KPar ≤ n :=
      powSizeLe h261 (Nat.max_le.mpr ⟨hx, hy⟩) hbKpar
    have hKK : KPar * Ksetup ≤ n.size := factorSmall hbK hParK0 hSetupK0
    have h1 : KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * Ksetup ≤ n.size * n := by
      calc KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * Ksetup
          = (KPar * Ksetup) * ((max sp.x.size sp.y.size).size + 1) ^ KPar := by ring
        _ ≤ n.size * n := Nat.mul_le_mul hKK hpow
    calc KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * Ksetup ≤ n.size * n := h1
      _ = n * n.size := Nat.mul_comm _ _
      _ = 1 * (n * n.size) := (Nat.one_mul _).symm
      _ ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) :=
          Nat.mul_le_mul_right _ hKS1
  have hP2 : Ksetup * (sp.x.size + sp.y.size + 1)
      ≤ 3 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h1 : sp.x.size + sp.y.size + 1 ≤ 3 * (n * n.size) := by
      have h2 : sp.x.size + sp.y.size + 1 ≤ 3 * n := by omega
      calc sp.x.size + sp.y.size + 1 ≤ 3 * n := h2
        _ ≤ 3 * (n * n.size) := Nat.mul_le_mul_left 3 hnZ
    calc Ksetup * (sp.x.size + sp.y.size + 1)
        ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (3 * (n * n.size)) := Nat.mul_le_mul hSetupS h1
      _ = 3 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP3 : Kprep * (sp.ss.prod + 1)
        * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + HvdH.bpar n
            + HvdH.ppar n + 1) * (sp.ss.prod.size + 1)
      ≤ 5600000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h3a := prepTermLe (n := n) (S := sp.ss.prod) (V := HvdH.vsz (HvdH.intList sp.ss))
      (V' := HvdH.vsz (HvdH.intList sp.ts)) h261 hTb hSle hvszss hvszts
    calc Kprep * (sp.ss.prod + 1)
          * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + HvdH.bpar n
              + HvdH.ppar n + 1) * (sp.ss.prod.size + 1)
        = Kprep * ((sp.ss.prod + 1)
          * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + HvdH.bpar n
              + HvdH.ppar n + 1) * (sp.ss.prod.size + 1)) := by ring
      _ ≤ Kprep * (5600000 * (n * n.size)) := Nat.mul_le_mul_left _ h3a
      _ = (5600000 * Kprep) * (n * n.size) := by ring
      _ ≤ (5600000 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5600000 hPrepS)
      _ = 5600000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP4 : Kprep * (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1)
      ≤ 220000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h4a : (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1)
        ≤ 220000 * (n * n.size) := (kinTerms (n := n) (S := sp.ss.prod) h261 hTb hSle).2.2.1
    calc Kprep * (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1)
        = Kprep * ((sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.bpar n + 1) * (HvdH.D + 1)) := by ring
      _ ≤ Kprep * (220000 * (n * n.size)) := Nat.mul_le_mul_left _ h4a
      _ = (220000 * Kprep) * (n * n.size) := by ring
      _ ≤ (220000 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 220000 hPrepS)
      _ = 220000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP5 : Kprep * (sp.x.size + sp.y.size + HvdH.bpar n + Work.Main.nchunks n (HvdH.bpar n)
        + sp.ss.prod + 1)
      ≤ 6 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have hSsp : sp.ss.prod ≤ n := le_trans hSle hTle
    have hNle : Work.Main.nchunks n (HvdH.bpar n) ≤ n := by
      have h1 : sp.ss.prod + 1 ≤ 2 * n := by omega
      omega
    have h1 : sp.x.size + sp.y.size + HvdH.bpar n + Work.Main.nchunks n (HvdH.bpar n)
        + sp.ss.prod + 1 ≤ 6 * (n * n.size) := by
      have h2 : sp.x.size + sp.y.size + HvdH.bpar n + Work.Main.nchunks n (HvdH.bpar n)
          + sp.ss.prod + 1 ≤ 6 * n := by omega
      calc sp.x.size + sp.y.size + HvdH.bpar n + Work.Main.nchunks n (HvdH.bpar n)
            + sp.ss.prod + 1 ≤ 6 * n := h2
        _ ≤ 6 * (n * n.size) := Nat.mul_le_mul_left 6 hnZ
    calc Kprep * (sp.x.size + sp.y.size + HvdH.bpar n + Work.Main.nchunks n (HvdH.bpar n)
          + sp.ss.prod + 1)
        ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53
          * (6 * (n * n.size)) := Nat.mul_le_mul hPrepS h1
      _ = 6 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have henv1 : envsz sp + 1 ≤ 610000 * (n * n.size) := by
    have h1 : envsz sp + 1 ≤ 300000 * (n.size + 1) + 3 * n + 1 := by omega
    have h3 : 300000 * (n.size + 1) ≤ 600000 * n.size := by
      have h4 : n.size + 1 ≤ 2 * n.size := by omega
      calc 300000 * (n.size + 1) ≤ 300000 * (2 * n.size) := Nat.mul_le_mul_left _ h4
        _ = 600000 * n.size := by ring
    have h4 : 3 * n ≤ 3 * (n * n.size) := Nat.mul_le_mul_left 3 hnZ
    nlinarith [h1, h3, h4, hZ1, hZn]
  have hP6 : Kprep * (envsz sp + 1)
      ≤ 610000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    calc Kprep * (envsz sp + 1) ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (610000 * (n * n.size)) :=
          Nat.mul_le_mul hPrepS henv1
      _ = 610000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hQ1b : 6 * (K53 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n)
      ≤ 6000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have hAT := alphaTermLe h261 hTb
    calc 6 * (K53 * HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n)
        = (6 * K53) * (HvdH.Tpar n * (Nat.sqrt (HvdH.ppar n) + 1) * HvdH.apar n * HvdH.ppar n) := by
          ring
      _ ≤ (6 * K53) * (1000 * (n * n.size)) := Nat.mul_le_mul_left _ hAT
      _ = 6000 * (K53 * (n * n.size)) := by ring
      _ ≤ 6000 * (Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hK53S)
      _ = 6000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hQ3 : 9 * (K53 * HvdH.Tpar n * HvdH.ppar n ^ 2)
      ≤ 2700 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have hTp2 : HvdH.Tpar n * HvdH.ppar n ^ 2 ≤ 300 * (n * n.size) :=
      (Work.Main.param.smallCosts (n := n) (K := 0) hn1 (by omega) hTb).2.2.1
    calc 9 * (K53 * HvdH.Tpar n * HvdH.ppar n ^ 2)
        = (9 * K53) * (HvdH.Tpar n * HvdH.ppar n ^ 2) := by ring
      _ ≤ (9 * K53) * (300 * (n * n.size)) := Nat.mul_le_mul_left _ hTp2
      _ = 2700 * (K53 * (n * n.size)) := by ring
      _ ≤ 2700 * (Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hK53S)
      _ = 2700 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hQ4 : 9 * (K53 * sp.ts.sum * (HvdH.ppar n + 1) ^ K53)
      ≤ 9 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have hts : sp.ts.sum * (HvdH.ppar n + 1) ^ K53 ≤ n * n.size :=
      Work.Main.param.tsSum_pow_le (n := n) (K := K53) (ts := sp.ts) (ss := sp.ss) hOK hTb hbK53
    calc 9 * (K53 * sp.ts.sum * (HvdH.ppar n + 1) ^ K53)
        = (9 * K53) * (sp.ts.sum * (HvdH.ppar n + 1) ^ K53) := by ring
      _ ≤ (9 * K53) * (n * n.size) := Nat.mul_le_mul_left _ hts
      _ = 9 * (K53 * (n * n.size)) := by ring
      _ ≤ 9 * (Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hK53S)
      _ = 9 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP7 : K53 ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    calc K53 ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 := hK53S
      _ = Ksum KPar Ksetup Kprep Kfin Kepi K53 * 1 := (Nat.mul_one _).symm
      _ ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) :=
          Nat.mul_le_mul_left _ hZn
  have hP8 : Kfin * (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
      ≤ 441 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h8a : (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        ≤ 441 * (n * n.size) := (kinTerms (n := n) (S := sp.ss.prod) h261 hTb hSle).1
    calc Kfin * (sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        = Kfin * ((sp.ss.prod + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)) := by ring
      _ ≤ Kfin * (441 * (n * n.size)) := Nat.mul_le_mul_left _ h8a
      _ = (441 * Kfin) * (n * n.size) := by ring
      _ ≤ (441 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 441 hFinS)
      _ = 441 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP9 : Kfin * (sp.ss.prod + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
      ≤ 763000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h9a : (sp.ss.prod + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        ≤ 763000 * (n * n.size) := (kinTerms (n := n) (S := sp.ss.prod) h261 hTb hSle).2.1
    calc Kfin * (sp.ss.prod + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)
        = Kfin * ((sp.ss.prod + 1) * (HvdH.D + 1) * (HvdH.ppar n + 1) * (HvdH.ppar n + 1)) := by ring
      _ ≤ Kfin * (763000 * (n * n.size)) := Nat.mul_le_mul_left _ h9a
      _ = (763000 * Kfin) * (n * n.size) := by ring
      _ ≤ (763000 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 763000 hFinS)
      _ = 763000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP10 : Kepi * (sp.ss.prod + 1) * (HvdH.bpar n + 1)
      ≤ 18 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    have h10a : (sp.ss.prod + 1) * (HvdH.bpar n + 1) ≤ 18 * (n * n.size) :=
      (kinTerms (n := n) (S := sp.ss.prod) h261 hTb hSle).2.2.2
    calc Kepi * (sp.ss.prod + 1) * (HvdH.bpar n + 1)
        = Kepi * ((sp.ss.prod + 1) * (HvdH.bpar n + 1)) := by ring
      _ ≤ Kepi * (18 * (n * n.size)) := Nat.mul_le_mul_left _ h10a
      _ = (18 * Kepi) * (n * n.size) := by ring
      _ ≤ (18 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 18 hEpiS)
      _ = 18 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hP11 : Kepi * (envsz sp + 1)
      ≤ 610000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by
    calc Kepi * (envsz sp + 1) ≤ Ksum KPar Ksetup Kprep Kfin Kepi K53 * (610000 * (n * n.size)) :=
          Nat.mul_le_mul hEpiS henv1
      _ = 610000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size) := by ring
  have hC0le : 10000000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size)
      ≤ K0 * n * n.size := by
    have h := Nat.mul_le_mul_right (n * n.size) hKS
    calc 10000000 * Ksum KPar Ksetup Kprep Kfin Kepi K53 * (n * n.size)
        = (10000000 * Ksum KPar Ksetup Kprep Kfin Kepi K53) * (n * n.size) := by ring
      _ ≤ K0 * (n * n.size) := h
      _ = K0 * n * n.size := by ring
  -- ## combine
  linarith [hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8, hP9, hP10, hP11, hQ1a, hQ1b, hQ3, hQ4, hC0le]

end Work.Main.cost
