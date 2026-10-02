import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs

/-!
# The retention recurrence of one round of Kahn's nibble

This module proves `Work.Deep.Kahn.retention_recurrence`: the *bookkeeping* lemma that lets the
iteration of the colour-degree nibble (Kang--Kelly--Kühn--Methuku--Osthus) pass from one round
outcome to the next state.

Given a state with common list size `Λ` and colour-degree bound `D`, one round produces
(`Work.Deep.Kahn.RoundStepStatement`) lists of size at least `newLambda Λ C D K - η Λ` and
colour degrees at most `newDeg Λ C D K + η D`.  Truncating the lists downwards to a common size
and rounding the colour degrees upwards gives the next state

* `Λ' = ⌊Λ · retention Λ C D K - η Λ⌋₊`,
* `D' = ⌈newDeg Λ C D K + η D⌉₊`.

Writing `s = retention` (the list retention) and
`den = (1 - 1/K) · retentionU + (1/K) · (1 - retention)` (the colour-degree retention factor, so
that `newDeg = D · den`), the hypotheses of the lemma are exactly the *single-round* conclusions
available at that point:

* `s/den ≥ 1 + γ` (`hgain`), `s/den ≤ 256/225` (`hgain2`),
* `1/2 ≤ s` (`hs`), `1/2 ≤ den` (`hQ`), `den ≤ 1 - 1/(4K)` (`hQ1`),

together with the round's regime (`(1+ε) D ≤ Λ ≤ 8 C D`, `16 K ≤ D`) and the smallness of the
error `η` (`16 η K ≤ 1`, `η ≤ γ/32`) and the fact that the error is *not* smaller than `1/Λ`
resp. `1/D` (`1 ≤ η Λ`, `1 ≤ η D`), which is what lets the additive errors be absorbed by the
multiplicative gain.

The conclusion is that the next state again lies in the regime
(`1 ≤ Λ'`, `1 ≤ D'`, `(1+ε) D' ≤ Λ'`, `Λ' ≤ 10 C D'`), that the colour-degree bound does not
increase (`D' ≤ D`), and that the ratio `Λ/D` improves by a factor `1 + γ/2` without ever
exceeding `256/225` of its old value.

The mathematical content is entirely scalar: the three ingredients are

* `⌊x⌋₊ > x - 1`, `⌈y⌉₊ < y + 1` (the rounding errors),
* `s ≥ (1+γ) den ≥ den + γ/2` (the gain, and `den ≥ 1/2`),
* `γ ≥ 32 η ≥ 32/Λ, 32/D` (the error is dominated by the gain).

The verification of the numerical constants is done in `recurrence_core` below; the theorem
`retention_recurrence` is then the purely definitional instantiation
`Λ ↦ L`, `s ↦ retention Λ C D K`, `den ↦ (1 - 1/K) retentionU + (1/K) (1 - retention)`.
-/

set_option maxHeartbeats 1000000

namespace Work.Deep.Kahn

/-- The scalar core of `retention_recurrence`, in the abstract parameters
`L = Λ`, `d = D`, `k = K`, `c = C`, `s = retention`, `den` with `newDeg = d · den`.  All the
numerical consequences of the round are passed in as hypotheses; the floor/ceil terms are the
next state's `Λ'` resp. `D'`. -/
private lemma recurrence_core {L d k c ε η γ s den : ℝ}
    (hL4 : 4 ≤ L) (hd1 : 1 ≤ d) (hk2 : 2 ≤ k)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hε0 : 0 < ε)
    (h1 : (1 + ε) * d ≤ L) (h8 : L ≤ 8 * c * d) (hc : 0 ≤ c)
    (h4 : 16 * η * k ≤ 1) (h5 : 32 * η ≤ γ)
    (h6 : 1 ≤ η * L) (h7 : 1 ≤ η * d) (h8K : 16 * k ≤ d)
    (hgain : 1 + γ ≤ s / den) (hgain2 : s / den ≤ 256 / 225)
    (hs : 1 / 2 ≤ s) (hQ : 1 / 2 ≤ den) (hQ1 : den ≤ 1 - 1 / (4 * k)) :
    1 ≤ ⌊L * s - η * L⌋₊ ∧ 1 ≤ ⌈d * den + η * d⌉₊ ∧
      (1 + ε) * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) ∧
      ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) ≤ 10 * c * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ∧
      ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ d ∧
      (1 + γ / 2) * (L / d) ≤ ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) / ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ∧
      ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) / ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ (256 / 225) * (L / d) := by
  -- ## basic positivity
  have hLp : (0 : ℝ) < L := by linarith
  have hdp : (0 : ℝ) < d := by linarith
  have hkp : (0 : ℝ) < k := by linarith
  have hdenp : (0 : ℝ) < den := by linarith
  have hη0 : (0 : ℝ) < η := by nlinarith [h6, hLp]
  have hε0' : (0 : ℝ) < 1 + ε := by linarith
  have hε1' : (1 : ℝ) ≤ 1 + ε := by linarith
  have hdc : 0 ≤ d * den := mul_nonneg hdp.le hdenp.le
  -- ## smallness of the error `η`
  have hηk : η ≤ 1 / (16 * k) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * k)]
    nlinarith [h4]
  have hη32 : η ≤ 1 / 32 := by
    have h1' : (1 : ℝ) / (16 * k) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * k) (by norm_num : (0 : ℝ) < 32)]
      linarith [hk2]
    linarith
  have hηγ : η ≤ γ / 32 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    nlinarith [h5]
  have hinvL : 1 / L ≤ γ / 32 := by
    have h1' : 1 / L ≤ η := by
      rw [div_le_iff₀ hLp]
      exact h6
    linarith
  have hinvd : 1 / d ≤ γ / 32 := by
    have h1' : 1 / d ≤ η := by
      rw [div_le_iff₀ hdp]
      exact h7
    linarith
  -- ## the gain hypotheses, cleared of their divisions
  have hsge : den + γ * den ≤ s := by
    have h := hgain
    rw [le_div_iff₀ hdenp] at h
    linarith [h]
  have hsle : s ≤ (256 / 225) * den := by
    have h := hgain2
    rw [div_le_iff₀ hdenp] at h
    exact h
  have hs225 : 225 * s ≤ 256 * den := by linarith [hsle]
  have hsg : (15 / 32 : ℝ) ≤ s - η := by linarith [hs, hη32]
  have hsη : (0 : ℝ) ≤ s - η := by linarith
  have hgd : γ / 2 ≤ γ * den := by
    have h2inv : (2 : ℝ)⁻¹ ≤ den := by linarith [hQ]
    exact mul_le_mul_of_nonneg_left h2inv hγ0.le
  have hγη : γ * η ≤ η := mul_le_of_le_one_left hη0.le hγ1
  have hγL32 : (32 : ℝ) ≤ γ * L := by
    have h' : (32 * η) * L ≤ γ * L := mul_le_mul_of_nonneg_right h5 hLp.le
    have h2 : (32 : ℝ) ≤ 32 * (η * L) := by linarith [h6]
    linarith [h', h2]
  have hγd32 : (32 : ℝ) ≤ γ * d := by
    have h' : (32 * η) * d ≤ γ * d := mul_le_mul_of_nonneg_right h5 hdp.le
    have h2 : (32 : ℝ) ≤ 32 * (η * d) := by linarith [h7]
    linarith [h', h2]
  -- ## the rounding bounds
  have hxΛpos : (0 : ℝ) < L * s - η * L := by nlinarith [hL4, hsg]
  have hxDNpos : (0 : ℝ) < d * den + η * d := by positivity
  have hΛle : ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) ≤ L * s - η * L := Nat.floor_le hxΛpos.le
  have hΛgt : L * s - η * L - 1 < ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have hDge : d * den + η * d ≤ ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hDlt : ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) < d * den + η * d + 1 :=
    Nat.ceil_lt_add_one hxDNpos.le
  have hD'pos : (0 : ℝ) < ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) := by linarith [hDge, hxDNpos]
  -- ## `1 ≤ Λ'` and `1 ≤ D'`
  have hG1 : 1 ≤ ⌊L * s - η * L⌋₊ := by
    rw [Nat.one_le_floor_iff]
    nlinarith [hL4, hsg]
  have hG2 : 1 ≤ ⌈d * den + η * d⌉₊ := by
    have h : 0 < ⌈d * den + η * d⌉₊ := Nat.ceil_pos.mpr hxDNpos
    omega
  -- ## `(1+ε) D' ≤ Λ'`
  -- the error absorbed by the gain: `d (s - den - 2η) - 1 ≥ 14`
  have hlow3 : 13 * γ / 32 + 1 / d ≤ s - den - 2 * η := by
    linarith [hsge, hgd, h5, hinvd]
  have hd3 : 14 ≤ d * (s - den - 2 * η) := by
    have hm : d * (13 * γ / 32 + 1 / d) ≤ d * (s - den - 2 * η) :=
      mul_le_mul_of_nonneg_left hlow3 hdp.le
    have he : d * (13 * γ / 32 + 1 / d) = 13 * γ * d / 32 + 1 := by field_simp
    have h13 : (13 : ℝ) ≤ 13 * γ * d / 32 := by
      have h := mul_le_mul_of_nonneg_left hγd32 (by norm_num : (0 : ℝ) ≤ 13 / 32)
      have he2 : (13 : ℝ) / 32 * (γ * d) = 13 * γ * d / 32 := by ring
      linarith [h, he2]
    linarith [hm, he, h13]
  have hkey3 : (1 + ε) * ((d * den + η * d) + 1) ≤ L * s - η * L - 1 := by
    have hLs : (1 + ε) * d * (s - η) ≤ L * (s - η) := mul_le_mul_of_nonneg_right h1 hsη
    have hid : (1 + ε) * d * (s - η) - (1 + ε) * ((d * den + η * d) + 1)
        = (1 + ε) * (d * (s - den - 2 * η) - 1) := by ring
    have hfin : (1 : ℝ) ≤ (1 + ε) * (d * (s - den - 2 * η) - 1) := by nlinarith [hd3, hε0]
    linarith [hLs, hid, hfin]
  have hG3 : (1 + ε) * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) := by
    have h1' : (1 + ε) * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ (1 + ε) * ((d * den + η * d) + 1) :=
      mul_le_mul_of_nonneg_left hDlt.le hε0'.le
    linarith [h1', hkey3, hΛgt]
  -- ## `Λ' ≤ 10 C D'`
  have hkey4 : L * s - η * L ≤ 10 * c * (d * den + η * d) := by
    have hLη : 0 ≤ η * L := mul_nonneg hη0.le hLp.le
    have hLs : L * s ≤ (2048 / 225) * (c * (d * den)) := by
      have hs1 : L * s ≤ L * ((256 / 225) * den) := mul_le_mul_of_nonneg_left hsle hLp.le
      have hs2 : L * ((256 / 225) * den) ≤ (8 * c * d) * ((256 / 225) * den) :=
        mul_le_mul_of_nonneg_right h8 (by positivity)
      have hs3 : (8 * c * d) * ((256 / 225) * den) = (2048 / 225) * (c * (d * den)) := by ring
      linarith [hs1, hs2]
    have hkey : (2048 / 225) * (c * (d * den)) ≤ 10 * c * (d * den + η * d) := by
      have h1' : (2048 / 225) * (c * (d * den)) ≤ 10 * (c * (d * den)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      have h2' : 10 * (c * (d * den)) ≤ 10 * c * (d * den + η * d) := by
        have h3' : d * den ≤ d * den + η * d := by linarith [mul_nonneg hη0.le hdp.le]
        have h4' := mul_le_mul_of_nonneg_left h3' (by positivity : (0 : ℝ) ≤ 10 * c)
        linarith [h4']
      linarith [h1', h2']
    linarith [hLη, hLs, hkey]
  have hG4 : ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) ≤ 10 * c * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) := by
    have hD'mul : 10 * c * (d * den + η * d) ≤ 10 * c * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hDge (by positivity : (0 : ℝ) ≤ 10 * c)
    linarith [hΛle, hkey4, hD'mul]
  -- ## `D' ≤ D`
  have hG5 : ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ d := by
    have h1den : 1 / (4 * k) ≤ 1 - den := by linarith [hQ1]
    have h3k : 3 / (16 * k) ≤ 1 - den - η := by
      have heq : (3 : ℝ) / (16 * k) = 1 / (4 * k) - 1 / (16 * k) := by field_simp; ring
      linarith [h1den, hηk, heq]
    have hd3' : 3 ≤ d * (1 - den - η) := by
      have h := mul_le_mul h8K h3k (by positivity : (0 : ℝ) ≤ 3 / (16 * k)) hdp.le
      have he : (16 * k) * (3 / (16 * k)) = 3 := by field_simp
      linarith [h, he]
    have hkey5 : d * den + η * d + 1 ≤ d := by linarith [hd3']
    linarith [hDlt, hkey5]
  -- ## the per-round gain `1 + γ/2` on the ratio `Λ/D`
  have hlow6 : 11 * γ / 64 ≤ s - η - (1 + γ / 2) * (den + η) := by
    linarith [hsge, hgd, hγη, h5]
  have hmul6 : L * d * (11 * γ / 64) ≤ L * d * (s - η - (1 + γ / 2) * (den + η)) :=
    mul_le_mul_of_nonneg_left hlow6 (by positivity)
  have hsplit6 : d + (1 + γ / 2) * L ≤ L * d * (11 * γ / 64) := by
    have e1 : 4 * d ≤ (8 / 64) * (γ * L * d) := by
      have h : (32 : ℝ) * d ≤ γ * L * d := by
        have hm : (32 : ℝ) * d ≤ (γ * L) * d := mul_le_mul_of_nonneg_right hγL32 hdp.le
        linarith [hm]
      linarith [h]
    have e2 : (3 / 2) * L ≤ (3 / 64) * (γ * L * d) := by
      have h : (32 : ℝ) * L ≤ γ * L * d := by
        have hm : (32 : ℝ) * L ≤ (γ * d) * L := mul_le_mul_of_nonneg_right hγd32 hLp.le
        linarith [hm]
      linarith [h]
    have e3 : d + (1 + γ / 2) * L ≤ 4 * d + (3 / 2) * L := by
      have h : γ * L ≤ L := mul_le_of_le_one_left hLp.le hγ1
      linarith [h]
    have e4 : (8 / 64) * (γ * L * d) + (3 / 64) * (γ * L * d) = L * d * (11 * γ / 64) := by ring
    linarith [e1, e2, e3, e4]
  have hkey6 : (1 + γ / 2) * L * ((d * den + η * d) + 1) ≤ (L * s - η * L - 1) * d := by
    have hid6 : (L * s - η * L - 1) * d - (1 + γ / 2) * L * ((d * den + η * d) + 1)
        = L * d * (s - η - (1 + γ / 2) * (den + η)) - d - (1 + γ / 2) * L := by ring
    linarith [hid6, hmul6, hsplit6]
  have hG6 : (1 + γ / 2) * (L / d) ≤
      ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) / ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) := by
    rw [le_div_iff₀ hD'pos]
    have t1 : (1 + γ / 2) * (L / d) * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ)
        ≤ (1 + γ / 2) * (L / d) * ((d * den + η * d) + 1) :=
      mul_le_mul_of_nonneg_left hDlt.le (by positivity)
    have t2 : (1 + γ / 2) * (L / d) * ((d * den + η * d) + 1) ≤ L * s - η * L - 1 := by
      have he : (1 + γ / 2) * (L / d) * ((d * den + η * d) + 1)
          = (1 + γ / 2) * L * ((d * den + η * d) + 1) / d := by field_simp
      rw [he, div_le_iff₀ hdp]
      exact hkey6
    linarith [t1, t2, hΛgt]
  -- ## the ratio never grows by more than `256/225`
  have hG7 : ((⌊L * s - η * L⌋₊ : ℕ) : ℝ) / ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) ≤ (256 / 225) * (L / d) := by
    rw [div_le_iff₀ hD'pos]
    have h7core : s - η ≤ (256 / 225) * (den + η) := by linarith [hs225]
    have key7 : (L * s - η * L) * d ≤ (256 / 225) * L * (d * den + η * d) := by
      have hLd : (0 : ℝ) ≤ L * d := by positivity
      have hm : L * d * (s - η) ≤ L * d * ((256 / 225) * (den + η)) :=
        mul_le_mul_of_nonneg_left h7core hLd
      have he2 : (256 / 225) * L * (d * den + η * d) = L * d * ((256 / 225) * (den + η)) := by ring
      linarith [hm, he2]
    have e2 : L * s - η * L ≤ (256 / 225) * L * (den + η) := by
      have h := key7
      have he : (256 / 225) * L * (d * den + η * d) = ((256 / 225) * L * (den + η)) * d := by ring
      rw [he] at h
      exact le_of_mul_le_mul_right h hdp
    have e1 : (256 / 225) * L * (den + η) ≤
        (256 / 225) * (L / d) * ((⌈d * den + η * d⌉₊ : ℕ) : ℝ) := by
      have heq : (256 / 225) * (L / d) * (d * den + η * d) = (256 / 225) * L * (den + η) := by
        field_simp
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hDge (by positivity)
    linarith [hΛle, e2, e1]
  exact ⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7⟩

theorem retention_recurrence {C D Λ K : ℕ} {ε η γ : ℝ}
    (hC : 2 ≤ C) (hK : 2 ≤ K) (hD : 1 ≤ D) (hΛ : 4 ≤ Λ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hη0 : 0 < η) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (h1 : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (h8 : (Λ : ℝ) ≤ 8 * (C : ℝ) * (D : ℝ))
    (h4 : 16 * η * (K : ℝ) ≤ 1) (h5 : 32 * η ≤ γ)
    (h6 : 1 ≤ η * (Λ : ℝ)) (h7 : 1 ≤ η * (D : ℝ)) (h8K : 16 * (K : ℝ) ≤ (D : ℝ))
    (hgain : 1 + γ ≤ retention Λ C D K /
      ((1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K)))
    (hgain2 : retention Λ C D K /
      ((1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K))
        ≤ 256 / 225)
    (hs : (1 / 2 : ℝ) ≤ retention Λ C D K)
    (hQ : (1 / 2 : ℝ) ≤
      (1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K))
    (hQ1 : (1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K)
      ≤ 1 - 1 / (4 * (K : ℝ))) :
    let Λ' : ℕ := ⌊(Λ : ℝ) * retention Λ C D K - η * (Λ : ℝ)⌋₊
    let D' : ℕ := ⌈newDeg Λ C D K + η * (D : ℝ)⌉₊
    1 ≤ Λ' ∧ 1 ≤ D' ∧ (1 + ε) * (D' : ℝ) ≤ (Λ' : ℝ) ∧ (Λ' : ℝ) ≤ 10 * (C : ℝ) * (D' : ℝ) ∧
    (D' : ℝ) ≤ (D : ℝ) ∧
    (1 + γ / 2) * ((Λ : ℝ) / (D : ℝ)) ≤ (Λ' : ℝ) / (D' : ℝ) ∧
    (Λ' : ℝ) / (D' : ℝ) ≤ (256 / 225) * ((Λ : ℝ) / (D : ℝ)) := by
  exact recurrence_core (L := (Λ : ℝ)) (d := (D : ℝ)) (k := (K : ℝ)) (c := (C : ℝ))
    (s := retention Λ C D K)
    (den := (1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K))
    (by exact_mod_cast hΛ) (by exact_mod_cast hD) (by exact_mod_cast hK)
    hγ0 hγ1 hε0 h1 h8 (by positivity) h4 h5 h6 h7 h8K hgain hgain2 hs hQ hQ1

end Work.Deep.Kahn
