import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.payPortLedger2` — the scalar ledger of the payment + port rung

Pure-real closing arithmetic of the per-box ledger (FS `thm:smallbox`, rungs `a0Main` and
`lp:appinteractionestimate` at the sliding box).  With `σ := S/V`, `t = (S+Q)/V` (`hSQ`) the
target reads

  `(1/4)(t-μ)²M₁ - ½μ²M₁ - C(μ²aΓM₁ + μa)  ≤  A₀(σ) - ½μ²M₁ + ½MΔPc/V² + bgQ
      - Ca(μ+σ)Q - Ca(μ+t)Q - ½(1+κΓ)G(t² + t/V) - Ca·caT`,

where `A₀(σ) = ¼(σ-μ)²M₁ - M₁σ/V - μM₁/(2V) - M₁/(4V²)` is `a0MainLocBox`'s underlying form.
The left side is the demand at the *box* density `t`, the right side the paid rows, so the whole
content is that the demand's `O(1/V)` "defect" rows `M₁t/V + μM₁/(2V) + M₁/(4V²)` (the difference
`A₀(t) - A₀(σ)` produces exactly them) are covered by the credit slot `C(μ²aΓM₁ + μa)` and by the
quadratic exchange `Q ↔ (σ - t)`.

The proof is a five-row ledger, each row paid by exactly one hypothesis:

* **Q-row** (`colQ`, from `hbg`): `bgQ - Ca(μ+σ)Q - Ca(μ+t)Q ≥ Q(D₂+D₁/2)at + QCat(4Cn-2) + CaQ²/V`
  (use `σ + t = 2t - Q/V`).
* **condensate row** (`colPc`, from `hM2m` and `S²-S ≤ Pc`):
  `½MΔPc/V² ≥ ½(1-Kδ)Gσ² - ½(1-Kδ)Gσ/V`.
* **credit row** (`colCred`, from `hR3`): `C(μ²aΓM₁+μa) - Ca·caT ≥ ½Cμ²aΓM₁ + Cμa`.
* **kinetic identity** (`colKin`): `¼M₁((σ-μ)² - (t-μ)²) = -¼M₁(t²-σ²) + ½M₁(t-σ)μ`.
* the `G`-rows: `gRow1` (`½G(Q/V)(t+σ) ≤ D₂atQ`), `gRow2` (`¼M₁(t²-σ²) ≤ ½D₁atQ`),
  `gRow3` (`-½G(Q/V)(t+σ) - ½G(2K+κ)Γt² ≤ ½(1-Kδ)Gσ² - ½(1+κΓ)Gt²`, the identity
  `2Γt² - δσ² = K(2Γ-δ)t² + Kδ(Q/V)(t+σ)` after `σ² = t² - (Q/V)(t+σ)`),
  `gRow4` (`½G(2K+κ)Γt² ≤ ½Cμ²aΓM₁`, uses `hCa` + `hGle` + `t ≤ 2Cnμ`),
  `gRow5` (`½(1+κΓ)G(t/V) + ½(1-Kδ)Gσ/V + M₁σ/V + μM₁/(2V) + M₁/(4V²) ≤ Cμa`, uses
  `hGub`, `hM1ub`, `hKδ`, `hκΓ`, `1/V ≤ μ`, `hCred`).

The two structural inequalities are `δ ≤ 2Γ` (`hδΓ`, turning `Kδ` into `2KΓ`) together with
`G ≤ D₀M₁` + `4D₀(2K+κ)Cn² ≤ Ca` (`hCa`), which bound `G(2K+κ)Γ` against the Γ-credit
`½Cμ²aΓM₁`; and `hCred`, which matches the `D₁(2Cn + 3/4) + 4D₂Cn` constants against `C`.
-/

set_option maxHeartbeats 1000000

namespace Work.BoseB1Cube


private lemma auxMulDiv {x y V : ℝ} (hV : V ≠ 0) : (x * V) * (y / V) = x * y := by
  have h : V * (y / V) = y := by
    rw [mul_comm]; exact div_mul_cancel₀ y hV
  calc (x * V) * (y / V) = x * (V * (y / V)) := by ring
    _ = x * y := by rw [h]

private lemma colQ {S Q t V D₁ D₂ a bg C Cn μ : ℝ}
    (hbg : (D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t ≤ bg)
    (hQ : 0 ≤ Q) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (htsum : S / V + t = 2 * t - Q / V) :
    Q * (D₂ + D₁ / 2) * a * t + Q * C * a * t * (4 * Cn - 2) + C * a * Q ^ 2 / V
      ≤ bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q := by
  have h1 : ((D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t) * Q ≤ bg * Q :=
    mul_le_mul_of_nonneg_right hbg hQ
  have h2 : (μ + S / V) + (μ + t) = 2 * μ + 2 * t - Q / V := by linarith [htsum]
  have h3 : 0 ≤ C * a * Q := mul_nonneg (mul_nonneg hC ha) hQ
  ring_nf at h1 h2 h3 ⊢
  nlinarith [h1, h2, h3]

private lemma colPc {S V G K δ MΔ Pc : ℝ} (hKδ : K * δ ≤ 1 / 2) (hG : 0 ≤ G)
    (hM2m : (1 - K * δ) * G ≤ MΔ) (hPc : S ^ 2 - S ≤ Pc) (hPcnn : 0 ≤ Pc) :
    (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 - K * δ) * G * (S / V) / V
      ≤ (1 / 2) * MΔ * Pc / V ^ 2 := by
  have hG0 : 0 ≤ (1 - K * δ) * G := mul_nonneg (by linarith [hKδ]) hG
  have ht1 : (1 / 2) * ((1 - K * δ) * G) * Pc / V ^ 2 ≤ (1 / 2) * MΔ * Pc / V ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * Pc / V ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hPcnn) (by positivity)
    have h := mul_le_mul_of_nonneg_right hM2m h0
    ring_nf at h ⊢
    linarith [h]
  have ht2 : (1 / 2) * ((1 - K * δ) * G) * (S ^ 2 - S) / V ^ 2
      ≤ (1 / 2) * ((1 - K * δ) * G) * Pc / V ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * ((1 - K * δ) * G) / V ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hG0) (by positivity)
    have h := mul_le_mul_of_nonneg_left hPc h0
    ring_nf at h ⊢
    linarith [h]
  ring_nf at ht1 ht2 ⊢
  linarith [ht1, ht2]

private lemma colCred {C μ a Γ M₁ caT : ℝ} (hR3 : 2 * C * a * caT ≤ C * μ ^ 2 * a * Γ * M₁) :
    (1 / 2) * C * μ ^ 2 * a * Γ * M₁ + C * μ * a
      ≤ C * (μ ^ 2 * a * Γ * M₁ + μ * a) - C * a * caT := by
  linarith [hR3]

private lemma gRow1 {G D₂ D₁ a V Q t S : ℝ} (hGub : G ≤ D₂ * a * V) (hQ : 0 ≤ Q)
    (hV : 0 < V) (hSVt : S / V ≤ t) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t)
    (hD₂ : 0 ≤ D₂) (ha : 0 ≤ a) :
    (1 / 2) * G * (Q / V) * (t + S / V) ≤ D₂ * a * t * Q := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have h1 : G * (Q / V) ≤ D₂ * a * Q := by
    have h := mul_le_mul_of_nonneg_right hGub hQd0
    have he : (D₂ * a * V) * (Q / V) = D₂ * a * Q := auxMulDiv (ne_of_gt hV)
    linarith [h, he]
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have htxt2 : t + S / V ≤ 2 * t := by linarith [hSVt]
  have h2 : (0 : ℝ) ≤ D₂ * a * Q := mul_nonneg (mul_nonneg hD₂ ha) hQ
  have h5 : (1 / 2) * (G * (Q / V) * (t + S / V)) ≤ (1 / 2) * ((D₂ * a * Q) * (2 * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul h1 htxt2 htxt0 h2) (by norm_num)
  have h6 : (1 / 2) * ((D₂ * a * Q) * (2 * t)) = D₂ * a * t * Q := by ring
  linarith [h5, h6]

private lemma gRow2 {M₁ D₁ a V Q t S : ℝ} (hM1ub : M₁ ≤ D₁ * a * V)
    (hQ : 0 ≤ Q) (hV : 0 < V) (htsub : t - S / V = Q / V) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t)
    (hSVt : S / V ≤ t) (hD₁ : 0 ≤ D₁) (ha : 0 ≤ a) :
    (1 / 4) * M₁ * (t ^ 2 - (S / V) ^ 2) ≤ (1 / 2) * D₁ * a * t * Q := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have htxt2 : t + S / V ≤ 2 * t := by linarith [hSVt]
  have hfac : t ^ 2 - (S / V) ^ 2 = (Q / V) * (t + S / V) := by nlinarith [htsub, htxt0]
  have hD1aQ : (0 : ℝ) ≤ D₁ * a * Q := mul_nonneg (mul_nonneg hD₁ ha) hQ
  have h6a : M₁ * ((Q / V) * (t + S / V)) ≤ (D₁ * a * Q) * (t + S / V) := by
    calc M₁ * ((Q / V) * (t + S / V)) = (M₁ * (Q / V)) * (t + S / V) := by ring
      _ ≤ ((D₁ * a * V) * (Q / V)) * (t + S / V) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM1ub hQd0) htxt0
      _ = (D₁ * a * Q) * (t + S / V) := by rw [auxMulDiv (x := D₁ * a) (y := Q) (ne_of_gt hV)]
  have h6b : (D₁ * a * Q) * (t + S / V) ≤ (D₁ * a * Q) * (2 * t) :=
    mul_le_mul_of_nonneg_left htxt2 hD1aQ
  have h6 : M₁ * ((Q / V) * (t + S / V)) ≤ (D₁ * a * Q) * (2 * t) := le_trans h6a h6b
  have h7 : (1 / 4) * (M₁ * ((Q / V) * (t + S / V))) ≤ (1 / 4) * ((D₁ * a * Q) * (2 * t)) :=
    mul_le_mul_of_nonneg_left h6 (by norm_num)
  have h8 : (1 / 4) * ((D₁ * a * Q) * (2 * t)) = (1 / 2) * D₁ * a * t * Q := by ring
  rw [hfac]
  linarith [h7, h8]

private lemma gRow3 {G K κ Γ δ S Q t V : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hδΓ : δ ≤ 2 * Γ)
    (hV : 0 < V) (hQ : 0 ≤ Q) (hSV0 : 0 ≤ S / V) (ht : 0 ≤ t) (hG : 0 ≤ G)
    (hSVt : S / V ≤ t)
    (htsub : t - S / V = Q / V) :
    -(1 / 2) * G * (Q / V) * (t + S / V) - (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      ≤ (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2 := by
  have hQd0 : 0 ≤ Q / V := div_nonneg hQ hV.le
  have htxt0 : 0 ≤ t + S / V := by linarith [hSV0, ht]
  have hfac : (S / V) ^ 2 = t ^ 2 - (Q / V) * (t + S / V) := by nlinarith [htsub, htxt0]
  have hsq : (S / V) ^ 2 ≤ t ^ 2 := by nlinarith [hSVt, htxt0]
  have hpos : (0 : ℝ) ≤ 2 * Γ * t ^ 2 - δ * (S / V) ^ 2 := by nlinarith [hδΓ, hsq, hδ]
  have hmain : (0 : ℝ) ≤ (1 / 2) * G * (K * (2 * Γ * t ^ 2 - δ * (S / V) ^ 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) hG) (mul_nonneg hK hpos)
  have hid : (1 / 2) * (1 - K * δ) * G * (S / V) ^ 2 - (1 / 2) * (1 + κ * Γ) * G * t ^ 2
        + (1 / 2) * G * (Q / V) * (t + S / V) + (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2
      = (1 / 2) * G * (K * (2 * Γ * t ^ 2 - δ * (S / V) ^ 2)) := by
    rw [hfac]; ring
  linarith [hid, hmain]

private lemma gRow4 {G D₀ M₁ C μ a Γ K κ Cn t : ℝ}
    (hCa : 4 * D₀ * (2 * K + κ) * Cn ^ 2 ≤ C * a) (hGle : G ≤ D₀ * M₁)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ) (hG : 0 ≤ G) (hM1 : 0 ≤ M₁) (hD₀ : 0 ≤ D₀)
    (hCn0 : 0 ≤ Cn) (hμ0 : 0 ≤ μ) (ht : 0 ≤ t) (htw : t ≤ 2 * Cn * μ) :
    (1 / 2) * G * (2 * K + κ) * Γ * t ^ 2 ≤ (1 / 2) * C * μ ^ 2 * a * Γ * M₁ := by
  have h2K : (0 : ℝ) ≤ 2 * K + κ := by linarith
  have hKΓ : (0 : ℝ) ≤ (2 * K + κ) * Γ := mul_nonneg h2K hΓ
  have h2Cnμ : 0 ≤ 2 * Cn * μ := mul_nonneg (by linarith) hμ0
  have hs1 : G * ((2 * K + κ) * Γ) ≤ (D₀ * M₁) * ((2 * K + κ) * Γ) :=
    mul_le_mul_of_nonneg_right hGle hKΓ
  have ht2 : t ^ 2 ≤ 4 * Cn ^ 2 * μ ^ 2 := by
    have hs : (0 : ℝ) ≤ t + 2 * Cn * μ := by linarith [ht, h2Cnμ]
    nlinarith [htw, ht, h2Cnμ, hs]
  have h4 : (0 : ℝ) ≤ (D₀ * M₁) * ((2 * K + κ) * Γ) :=
    mul_nonneg (mul_nonneg hD₀ hM1) hKΓ
  have hs2 : (G * ((2 * K + κ) * Γ)) * t ^ 2
      ≤ ((D₀ * M₁) * ((2 * K + κ) * Γ)) * (4 * Cn ^ 2 * μ ^ 2) :=
    mul_le_mul hs1 ht2 (sq_nonneg t) h4
  have hs3 : ((D₀ * M₁) * ((2 * K + κ) * Γ)) * (4 * Cn ^ 2 * μ ^ 2) ≤ C * a * M₁ * Γ * μ ^ 2 := by
    have h0 : (0 : ℝ) ≤ M₁ * Γ * μ ^ 2 := mul_nonneg (mul_nonneg hM1 hΓ) (sq_nonneg μ)
    have h := mul_le_mul_of_nonneg_right hCa h0
    nlinarith [h]
  have hfin := le_trans hs2 hs3
  ring_nf at hfin ⊢
  linarith [hfin]

private lemma gRow5 {G D₁ D₂ M₁ C μ a Γ κ K δ Cn V t S Q : ℝ}
    (hκΓ : κ * Γ ≤ 1 / 8) (hKδ : K * δ ≤ 1 / 2) (hGub : G ≤ D₂ * a * V)
    (hM1ub : M₁ ≤ D₁ * a * V) (htw : t ≤ 2 * Cn * μ) (hμV : 1 ≤ μ * V)
    (hCred : 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn ≤ C)
    (hV : 0 < V) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (ht : 0 ≤ t) (hSQ : S + Q = t * V)
    (hCn0 : 0 ≤ Cn) (hμ0 : 0 ≤ μ) (ha : 0 ≤ a)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hG : 0 ≤ G) (hM₁ : 0 ≤ M₁) (hδ : 0 ≤ δ) (hK : 0 ≤ K) :
    (1 / 2) * (1 + κ * Γ) * G * (t / V) + (1 / 2) * (1 - K * δ) * G * (S / V) / V
      + M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2) ≤ C * μ * a := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hSV0 : 0 ≤ S / V := div_nonneg hS hV.le
  have hκΓ9 : 1 + κ * Γ ≤ 9 / 8 := by linarith [hκΓ]
  have hD2a : (0 : ℝ) ≤ D₂ * a := mul_nonneg hD₂ ha
  have htv0 : (0 : ℝ) ≤ t / V := div_nonneg ht hV.le
  -- e1
  have he1 : (1 / 2) * (1 + κ * Γ) * G * (t / V) ≤ (9 / 8) * D₂ * Cn * a * μ := by
    have hGV : G * (t / V) ≤ D₂ * a * t := by
      calc G * (t / V) ≤ (D₂ * a * V) * (t / V) := mul_le_mul_of_nonneg_right hGub htv0
        _ = D₂ * a * t := auxMulDiv (x := D₂ * a) (y := t) hVne
    have hGt0 : (0 : ℝ) ≤ G * (t / V) := mul_nonneg hG htv0
    have hstep : (1 + κ * Γ) * (G * (t / V)) ≤ (9 / 8) * (D₂ * a * t) :=
      mul_le_mul hκΓ9 hGV hGt0 (by norm_num)
    ring_nf at hstep ⊢
    nlinarith [hstep, htw, hD2a, hCn0, hμ0]
  -- e2
  have he2 : (1 / 2) * (1 - K * δ) * G * (S / V) / V ≤ D₂ * Cn * a * μ := by
    have hGS : G * (S / V) ≤ D₂ * a * S := by
      calc G * (S / V) ≤ (D₂ * a * V) * (S / V) := mul_le_mul_of_nonneg_right hGub hSV0
        _ = D₂ * a * S := auxMulDiv (x := D₂ * a) (y := S) hVne
    have hGS0 : (0 : ℝ) ≤ G * (S / V) := mul_nonneg hG hSV0
    have hstep : (1 - K * δ) * (G * (S / V)) ≤ 1 * (D₂ * a * S) :=
      mul_le_mul (by linarith [mul_nonneg hK hδ, hKδ]) hGS hGS0 (by norm_num)
    have hSle : S ≤ 2 * Cn * μ * V := by nlinarith [hSQ, htw, hQ, hV]
    have hdiv : (1 / 2) * (1 - K * δ) * G * (S / V) / V
        = (1 / 2) * ((1 - K * δ) * (G * (S / V))) / V := by ring
    rw [hdiv, div_le_iff₀ hV]
    ring_nf at hstep ⊢
    nlinarith [hstep, hSle, hD2a, hCn0, hμ0]
  -- e3
  have he3 : M₁ * (S / V) / V ≤ 2 * D₁ * Cn * a * μ := by
    have hSle : S ≤ 2 * Cn * μ * V := by nlinarith [hSQ, htw, hQ, hV]
    have hD1aV : (0 : ℝ) ≤ D₁ * a * V := mul_nonneg (mul_nonneg hD₁ ha) hV.le
    have hMS : M₁ * S ≤ (D₁ * a * V) * (2 * Cn * μ * V) := mul_le_mul hM1ub hSle hS hD1aV
    have he : M₁ * (S / V) / V = M₁ * S / V ^ 2 := by field_simp
    rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < V ^ 2)]
    ring_nf at hMS ⊢
    linarith [hMS]
  -- e4
  have he4 : μ * M₁ / (2 * V) ≤ D₁ * a * μ / 2 := by
    have h : μ * M₁ ≤ (D₁ * a * μ) * V := by
      have h1 := mul_le_mul_of_nonneg_left hM1ub hμ0
      ring_nf at h1 ⊢
      linarith [h1]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * V)]
    ring_nf at h ⊢
    linarith [h]
  -- e5
  have he5 : M₁ / (4 * V ^ 2) ≤ D₁ * a * μ / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * V ^ 2)]
    have hDV : (0 : ℝ) ≤ D₁ * a * V := mul_nonneg (mul_nonneg hD₁ ha) hV.le
    have h2 : D₁ * a * V ≤ D₁ * a * μ * (V * V) := by nlinarith [hμV, hDV]
    have h3 : (D₁ * a * μ / 4) * (4 * V ^ 2) = D₁ * a * μ * (V * V) := by ring
    linarith [hM1ub, h2, h3]
  have hcred2 : (17 / 8) * D₂ * Cn + (2 * D₁ * Cn + 3 * D₁ / 4) ≤ C := by
    nlinarith [hCred, hD₂, hCn0]
  have haμ : (0 : ℝ) ≤ a * μ := mul_nonneg ha hμ0
  ring_nf at he1 he2 he3 he4 he5 hcred2 ⊢
  nlinarith [he1, he2, he3, he4, he5, hcred2, haμ]

theorem payPortLedger2 {V μ a Γ κ K D₀ D₁ D₂ δ G M₁ MΔ S Q t Pc bg C Cn caT : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCn : 4 ≤ Cn) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hSQ : S + Q = t * V) (ht : 0 ≤ t) (htw : t ≤ 2 * Cn * μ)
    (hPc : S ^ 2 - S ≤ Pc) (hPcnn : 0 ≤ Pc)
    (hGle : G ≤ D₀ * M₁) (hM2m : (1 - K * δ) * G ≤ MΔ)
    (hM1ub : M₁ ≤ D₁ * a * V) (hGub : G ≤ D₂ * a * V)
    (hδ : 0 ≤ δ) (hδΓ : δ ≤ 2 * Γ) (hK : 0 ≤ K) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hκΓ : κ * Γ ≤ 1 / 8) (hKδ : K * δ ≤ 1 / 2) (hμV : 1 ≤ μ * V)
    (hCa : 4 * D₀ * (2 * K + κ) * Cn ^ 2 ≤ C * a)
    (hbg : (D₂ + D₁ / 2) * a * t + 2 * C * a * μ + 4 * Cn * C * a * t ≤ bg)
    (hR3 : 2 * C * a * caT ≤ C * μ ^ 2 * a * Γ * M₁)
    (hCred : 2 * D₁ * Cn + 3 * D₁ / 4 + 4 * D₂ * Cn ≤ C) :
    (1 / 4) * (t - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ - C * (μ ^ 2 * a * Γ * M₁ + μ * a)
      ≤ (1 / 4) * (S / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁ - M₁ * (S / V) / V
        - μ * M₁ / (2 * V) - M₁ / (4 * V ^ 2)
        + (1 / 2) * MΔ * Pc / V ^ 2
        + bg * Q - C * a * (μ + S / V) * Q - C * a * (μ + t) * Q
        - (1 / 2) * (1 + κ * Γ) * G * (t ^ 2 + t / V)
        - C * a * caT:= by
  have hμ0 : 0 ≤ μ := le_of_lt hμ
  have hCn0 : 0 ≤ Cn := by linarith
  have hVne : V ≠ 0 := ne_of_gt hV
  have htV : t = (S + Q) / V := by rw [eq_div_iff hVne]; linarith [hSQ]
  have htsum : S / V + t = 2 * t - Q / V := by rw [htV]; ring
  have htsub : t - S / V = Q / V := by rw [htV]; ring
  have hSV0 : 0 ≤ S / V := div_nonneg hS hV.le
  have hSVt : S / V ≤ t := by rw [div_le_iff₀ hV]; linarith [hSQ, hQ]
  have hQcol := colQ (D₁ := D₁) (D₂ := D₂) (S := S) (Q := Q) (t := t) (V := V) (a := a)
    (bg := bg) (C := C) (Cn := Cn) (μ := μ) hbg hQ hC ha htsum
  have hPcrow := colPc (S := S) (V := V) (G := G) (K := K) (δ := δ) (MΔ := MΔ) (Pc := Pc)
    hKδ hG hM2m hPc hPcnn
  have hcred := colCred (C := C) (μ := μ) (a := a) (Γ := Γ) (M₁ := M₁) (caT := caT) hR3
  have hG1 := gRow1 (G := G) (D₂ := D₂) (D₁ := D₁) (a := a) (V := V) (Q := Q) (t := t) (S := S)
    hGub hQ hV hSVt hSV0 ht hD₂ ha
  have hG2 := gRow2 (M₁ := M₁) (D₁ := D₁) (a := a) (V := V) (Q := Q) (t := t) (S := S)
    hM1ub hQ hV htsub hSV0 ht hSVt hD₁ ha
  have hG3 := gRow3 (G := G) (K := K) (κ := κ) (Γ := Γ) (δ := δ) (S := S) (Q := Q) (t := t) (V := V)
    hK hδ hδΓ hV hQ hSV0 ht hG hSVt htsub
  have hG4 := gRow4 (G := G) (D₀ := D₀) (M₁ := M₁) (C := C) (μ := μ) (a := a) (Γ := Γ) (K := K)
    (κ := κ) (Cn := Cn) (t := t) hCa hGle hK hκ hΓ hG hM1 hD₀ hCn0 hμ0 ht htw
  have hG5 := gRow5 (G := G) (D₁ := D₁) (D₂ := D₂) (M₁ := M₁) (C := C) (μ := μ) (a := a) (Γ := Γ)
    (κ := κ) (K := K) (δ := δ) (Cn := Cn) (V := V) (t := t) (S := S)
    hκΓ hKδ hGub hM1ub htw hμV hCred hV hS hQ ht hSQ hCn0 hμ0 ha hD₁ hD₂ hG hM1 hδ hK
  -- the spare nonnegative rows of the chain
  have hsp1 : (0 : ℝ) ≤ Q * C * a * t * (4 * Cn - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hQ hC) ha) ht) (by linarith [hCn])
  have hsp2 : (0 : ℝ) ≤ C * a * Q ^ 2 / V :=
    div_nonneg (mul_nonneg (mul_nonneg hC ha) (sq_nonneg Q)) hV.le
  have hsp3 : (0 : ℝ) ≤ (1 / 2) * μ * M₁ * (Q / V) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hμ0) hM1) (div_nonneg hQ hV.le)
  have hpm : (0 : ℝ) ≤ (1 / 2) * μ * M₁ := mul_nonneg (mul_nonneg (by norm_num) hμ0) hM1
  ring_nf at hQcol hPcrow hcred hG1 hG2 hG3 hG4 hG5 hsp1 hsp2 hsp3 hpm htsub ⊢
  nlinarith [hQcol, hPcrow, hcred, hG1, hG2, hG3, hG4, hG5, hsp1, hsp2, hsp3, hpm, htsub]


end Work.BoseB1Cube
