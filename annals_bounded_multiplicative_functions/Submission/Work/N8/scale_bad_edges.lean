import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.threshold_bigX
import Submission.Work.N8.window_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.scale_bad_edges`

The count of "bad" edges coming out of `bad_edges_le`,

`16 · #A.fam · K · (B + 1) · (π₀(P₁) + 1)` with `#A.fam ≤ X/H/10` and `B + 1 ≤ log(X/(P₁P₂))/δ + 2`,

is at most `c · π₀(P₁)² · (X/H)` once `X` is sufficiently large (in terms of `θ, ε, c, δ, K`).

The proof is purely a matter of scales: on the range `X^{ε²/2} ≤ P₁ ≤ X^ε` the logarithmic factor
`log(X/(P₁P₂))/δ + 2` is `≪ log X`, while `π₀(P₁) = P₁ / log P₁ ≥ X^{ε²/2} / log X`, which grows
faster than any fixed power of `log X`; hence for large `X` the factor `π₀(P₁)²` dominates the loss
`K · (log X)² / δ` incurred in the counting.
-/

namespace Work.N8

/-- Elementary arithmetic core of the scaling estimate: if `Nf ≤ A/10`, `q ≤ (1/δ+2)L`, `p ≥ 1`
and `(32/5)·K·(1/δ+2)·L ≤ c·p`, then `2·16·Nf·K·q·(p+1) ≤ c·p²·A`. -/
private lemma arith_core (c δ : ℝ) (K : ℕ) (A Nf p q L : ℝ)
    (hδ : 0 < δ) (hK : 0 < K) (hA : 0 < A)
    (hNf : Nf ≤ A / 10) (hq0 : 0 ≤ q) (hqL : q ≤ (1 / δ + 2) * L)
    (hp1 : 1 ≤ p) (hL0 : 0 ≤ L)
    (hF : (32 / 5) * (K : ℝ) * (1 / δ + 2) * L ≤ c * p) :
    2 * (16 * Nf * (K : ℝ) * q * (p + 1)) ≤ c * p ^ 2 * A := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hD0 : 0 ≤ 1 / δ + 2 := by positivity
  have hDL : 0 ≤ (1 / δ + 2) * L := mul_nonneg hD0 hL0
  have hp10 : 0 ≤ p + 1 := by linarith
  have hs : q * (p + 1) ≤ ((1 / δ + 2) * L) * (2 * p) :=
    mul_le_mul hqL (by linarith) hp10 hDL
  have hs2 : (K : ℝ) * (q * (p + 1)) ≤ (K : ℝ) * (((1 / δ + 2) * L) * (2 * p)) :=
    mul_le_mul_of_nonneg_left hs (le_of_lt hK0)
  have hcore : (16 / 5) * (K : ℝ) * q * (p + 1) ≤ c * p ^ 2 := by
    have h3 : (16 / 5) * ((K : ℝ) * (q * (p + 1))) ≤
        (16 / 5) * ((K : ℝ) * (((1 / δ + 2) * L) * (2 * p))) :=
      mul_le_mul_of_nonneg_left hs2 (by norm_num)
    have h4 : (16 / 5) * ((K : ℝ) * (((1 / δ + 2) * L) * (2 * p))) =
        (32 / 5) * (K : ℝ) * (1 / δ + 2) * L * p := by ring
    have h5 : (32 / 5) * (K : ℝ) * (1 / δ + 2) * L * p ≤ c * p ^ 2 := by
      have := mul_le_mul_of_nonneg_right hF (le_of_lt hp0)
      nlinarith [this]
    linarith [h3, h4, h5]
  have hnn : 0 ≤ (K : ℝ) * q * (p + 1) := by positivity
  have hA1 : Nf * ((K : ℝ) * q * (p + 1)) ≤ (A / 10) * ((K : ℝ) * q * (p + 1)) :=
    mul_le_mul_of_nonneg_right hNf hnn
  nlinarith [hcore, hA1, hA]

theorem scale_bad_edges (θ ε c δ : ℝ) (K : ℕ) (hK : 0 < K)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100)
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ X₀ : ℝ, ∀ X H P₁ P₂ Nf : ℝ, X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      Nf ≤ X / H / 10 →
      2 * (16 * Nf * (K : ℝ) * (Real.log (X / (P₁ * P₂)) / δ + 2) *
          (Work.BMF.pi0 P₁ + 1)) ≤ c * Work.BMF.pi0 P₁ ^ 2 * (X / H) := by
  obtain ⟨X₀, hX₀⟩ := threshold_bigX ε c δ K hK hε hc hδ
  refine ⟨X₀, ?_⟩
  intro X H P₁ P₂ Nf hX hH1 hH2 hP₁1 hP₁2 hP₂1 hP₂2 hNf
  obtain ⟨hX1, hL1, hy3, hLle, hMb⟩ := hX₀ X hX
  obtain ⟨hP₁X, hP₁gt1, hlogP₁L, hP₁P₂X, h1ratio, hratioX, hlogr0, hlogrL, hpi0, h1ydL⟩ :=
    window_bounds θ ε X P₁ P₂ hθ₁ hε hεθ hX1 hL1 hLle hy3 hP₁1 hP₁2 hP₂1 hP₂2
  set L : ℝ := Real.log X with hLdef
  set y : ℝ := X ^ (ε ^ 2 / 2) with hydef
  set p : ℝ := Work.BMF.pi0 P₁ with hpdef
  set A : ℝ := X / H with hAdef
  set q : ℝ := Real.log (X / (P₁ * P₂)) / δ + 2 with hqdef
  have hLpos : 0 < L := by linarith
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < H := by
    have h1 : 1 ≤ X ^ θ := Real.one_le_rpow hX1 (le_of_lt hθ₀)
    linarith
  have hApos : 0 < A := by
    rw [hAdef]
    exact div_pos hXpos hHpos
  have hq0 : 0 ≤ q := by
    rw [hqdef]
    have h := div_nonneg hlogr0 (le_of_lt hδ)
    linarith
  have hqL : q ≤ (1 / δ + 2) * L := by
    rw [hqdef]
    have h1 : Real.log (X / (P₁ * P₂)) / δ ≤ L / δ :=
      div_le_div_of_nonneg_right hlogrL (le_of_lt hδ)
    have h2 : (2 : ℝ) ≤ 2 * L := by linarith
    have he : L / δ + 2 * L = (1 / δ + 2) * L := by ring
    linarith [h1, h2, he]
  have hp1 : 1 ≤ p := le_trans h1ydL hpi0
  have hF : (32 / 5) * (K : ℝ) * (1 / δ + 2) * L ≤ c * p := by
    have hML : (32 / 5) * (K : ℝ) * (1 / δ + 2) * L ≤ c * y / L := by
      rw [le_div_iff₀ hLpos]
      have he : (32 / 5) * (K : ℝ) * (1 / δ + 2) * L * L =
          (32 / 5) * (K : ℝ) * (1 / δ + 2) * L ^ 2 := by ring
      linarith [hMb, he]
    have h2 : c * y / L ≤ c * p := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hpi0 (le_of_lt hc)
    linarith [hML, h2]
  exact arith_core c δ K A Nf p q L hδ hK hApos hNf hq0 hqL hp1 (le_of_lt hLpos) hF

end Work.N8
