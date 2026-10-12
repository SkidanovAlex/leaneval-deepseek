import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBoxFock.PCFU.chAimg_arith5
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAimg_arith6` — the pure-real slot arithmetic at the `(A)`-images,
third shape (the kinetic slot)

With `fsXp t c = t ^ (c / 323)` (FS's monomial `(μa³)^{c/323}`) and the box side / chemical
potential tied to the diluteness by

`ℓ = fsXp t (−3/2)·(t/a²)^{−1/2} = a·t^{−163/323}`,   `μ = t/a³`,   `d = fsXp t 6`,

the target is the slot estimate

    C0·d^{192}/ℓ³ · (Cs(1+R)³ℓ³(√(2ℓ/π) + √a)) ·
        ( √(ℓ³nB) · √(2 (Ck μ² a ℓ³ nB) + 2 M² (ℓ²)⁻¹ nB) )
      ≤ K0 · a/(8μ(1+ℓ³)) · nB .

The `ℓ³/ℓ³` cancels and the second factor is split with `√(x+y) ≤ √x + √y`:

    √(ℓ³nB)·√(2 (Ck μ² a ℓ³ nB) + 2 M² (ℓ²)⁻¹ nB)
      = nB·√(2 Ck μ² a ℓ⁶ + 2 M² ℓ)
      ≤ nB·(√(2Ck)·μ√a ℓ³ + √2·M·√ℓ)
      ≤ nB·max (√(2Ck)) (√2 M)·(√a μ ℓ³ + √ℓ) ,

so the whole claim reduces to

    C0·Cs(1+R)³·d^{192}·(√(2ℓ/π)+√a) · (√a μ ℓ³ + √ℓ) ≤ K0·a/(8μ(1+ℓ³)) ,

which is exactly the *proved* `chAimg_arith5` (with `C := C0·Cs(1+R)³·max (√(2Ck)) (√2 M)`),
multiplied by the non-negative factor `nB`.

The two algebraic steps are isolated as `chAimg_arith6_sqrt_core` (the square-root identity and
split) and `chAimg_arith6_reduce_aux` (the cancellation of `ℓ³` and the passage to the
`chAimg_arith5` shape).
-/

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 3200000

/-- **The square-root core of `chAimg_arith6`.**  With `K = max (√(2Ck)) (√2·M)`,

    √(ℓ³nB)·√(2 (Ck μ² a ℓ³ nB) + 2 M² (ℓ²)⁻¹ nB) ≤ nB·K·(√a·μ·ℓ³ + √ℓ) .

Indeed `ℓ³nB·(2 Ck μ² a ℓ³ nB + 2 M² (ℓ²)⁻¹ nB) = nB²·(2 Ck μ² a ℓ⁶ + 2 M² ℓ)`, so the left
side is `nB·√(2 Ck μ² a ℓ⁶ + 2 M² ℓ)`, and `√(x+y) ≤ √x + √y` together with
`√(2 Ck μ² a ℓ⁶) = √(2Ck)·μ·√a·ℓ³` and `√(2 M² ℓ) = √2·M·√ℓ` gives the claim. -/
lemma chAimg_arith6_sqrt_core {a Ck M ℓ μ nB : ℝ} (ha : 0 ≤ a) (hCk : 0 ≤ Ck) (hM : 0 ≤ M)
    (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) (hnB : 0 ≤ nB) :
    Real.sqrt (ℓ ^ 3 * nB)
        * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)
      ≤ nB * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) := by
  -- the `ℓ³·(ℓ²)⁻¹ = ℓ` simplification
  have hlinv : ℓ ^ 3 * (ℓ ^ 2)⁻¹ = ℓ := by
    rcases eq_or_ne ℓ 0 with h | h
    · simp [h]
    · field_simp
  -- the product identity `ℓ³nB·X = nB²·Z`
  have hXY : ℓ ^ 3 * nB * (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)
      = nB ^ 2 * (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ) := by
    have h1 : ℓ ^ 3 * nB * (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB))
        = 2 * Ck * μ ^ 2 * a * ℓ ^ 6 * nB ^ 2 := by
      ring
    have h2 : ℓ ^ 3 * nB * (2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB) = 2 * M ^ 2 * ℓ * nB ^ 2 := by
      rw [show ℓ ^ 3 * nB * (2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)
            = 2 * M ^ 2 * (ℓ ^ 3 * (ℓ ^ 2)⁻¹) * nB ^ 2 from by ring, hlinv]
    rw [mul_add, h1, h2]
    ring
  have hZ : 0 ≤ 2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ := by positivity
  have hmainsq : nB ^ 2 * (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)
      = (nB * Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hZ]
  -- the split `√(x+y) ≤ √x + √y` and the identification of the two pieces
  have hB : Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)
      ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) := by
    have hX0 : 0 ≤ 2 * Ck * μ ^ 2 * a * ℓ ^ 6 := by positivity
    have hY0 : 0 ≤ 2 * M ^ 2 * ℓ := by positivity
    have hsplit : Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)
        ≤ Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6) + Real.sqrt (2 * M ^ 2 * ℓ) := by
      refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq (by positivity)))
      nlinarith [Real.sq_sqrt hX0, Real.sq_sqrt hY0,
        mul_nonneg (Real.sqrt_nonneg (2 * Ck * μ ^ 2 * a * ℓ ^ 6))
          (Real.sqrt_nonneg (2 * M ^ 2 * ℓ))]
    have e1 : Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6)
        = Real.sqrt (2 * Ck) * μ * Real.sqrt a * ℓ ^ 3 := by
      have h : (Real.sqrt (2 * Ck) * μ * Real.sqrt a * ℓ ^ 3) ^ 2 = 2 * Ck * μ ^ 2 * a * ℓ ^ 6 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ha]
        ring
      rw [← h, Real.sqrt_sq (by positivity)]
    have e2 : Real.sqrt (2 * M ^ 2 * ℓ) = Real.sqrt 2 * M * Real.sqrt ℓ := by
      have h : (Real.sqrt 2 * M * Real.sqrt ℓ) ^ 2 = 2 * M ^ 2 * ℓ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hℓ.le]
      rw [← h, Real.sqrt_sq (by positivity)]
    have hK1 : Real.sqrt (2 * Ck) ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) := le_max_left _ _
    have hK2 : Real.sqrt 2 * M ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) := le_max_right _ _
    have e3 : Real.sqrt (2 * Ck) * μ * Real.sqrt a * ℓ ^ 3
        ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) * (Real.sqrt a * μ * ℓ ^ 3) := by
      rw [show Real.sqrt (2 * Ck) * μ * Real.sqrt a * ℓ ^ 3
            = Real.sqrt (2 * Ck) * (μ * Real.sqrt a * ℓ ^ 3) from by ring]
      exact le_trans (mul_le_mul_of_nonneg_right hK1
        (show (0 : ℝ) ≤ μ * Real.sqrt a * ℓ ^ 3 by positivity)) (le_of_eq (by ring))
    have e4 : Real.sqrt 2 * M * Real.sqrt ℓ
        ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) * Real.sqrt ℓ :=
      mul_le_mul_of_nonneg_right hK2 (Real.sqrt_nonneg ℓ)
    calc Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)
        ≤ Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6) + Real.sqrt (2 * M ^ 2 * ℓ) := hsplit
      _ = Real.sqrt (2 * Ck) * μ * Real.sqrt a * ℓ ^ 3 + Real.sqrt 2 * M * Real.sqrt ℓ := by
            rw [e1, e2]
      _ ≤ max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) * (Real.sqrt a * μ * ℓ ^ 3)
            + max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M) * Real.sqrt ℓ := add_le_add e3 e4
      _ = max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
            * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) := by ring
  calc Real.sqrt (ℓ ^ 3 * nB)
        * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)
      = Real.sqrt (ℓ ^ 3 * nB
          * (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)) := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ ℓ ^ 3 * nB by positivity)]
    _ = Real.sqrt (nB ^ 2 * (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ)) := by rw [hXY]
    _ = nB * Real.sqrt (2 * Ck * μ ^ 2 * a * ℓ ^ 6 + 2 * M ^ 2 * ℓ) := by
        rw [hmainsq, Real.sqrt_sq (by positivity)]
    _ ≤ nB * (max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := mul_le_mul_of_nonneg_left hB hnB
    _ = nB * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) := by ring

/-- **The reduction step of `chAimg_arith6`.**  Cancelling the common factor `ℓ³` (and replacing
`d^{2·96}` by `d^{192}`) reduces the target's left-hand side to the product of
`C0·Cs(1+R)³·d^{192}·(√(2ℓ/π)+√a) ≥ 0` with `√(ℓ³nB)·√(2 (Ck μ² a ℓ³ nB) + 2 M² (ℓ²)⁻¹ nB)`,
whose bound is `chAimg_arith6_sqrt_core`; this is exactly the shape of the proved
`chAimg_arith5`. -/
lemma chAimg_arith6_reduce_aux {a C0 Cs Ck M R nB ℓ μ d : ℝ} (ha : 0 ≤ a) (hC0 : 0 ≤ C0)
    (hCs : 0 ≤ Cs) (hCk : 0 ≤ Ck) (hM : 0 ≤ M) (hR : 0 ≤ R) (hnB : 0 ≤ nB)
    (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) :
    C0 * d ^ (2 * 96 : ℕ) / ℓ ^ 3
        * (Cs * (1 + R) ^ 3 * ℓ ^ 3 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
        * (Real.sqrt (ℓ ^ 3 * nB)
            * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB))
      ≤ nB * (C0 * Cs * (1 + R) ^ 3 * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
            * d ^ (192 : ℕ)
            * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
            * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := by
  have hd192 : d ^ (2 * 96 : ℕ) = d ^ (192 : ℕ) := by norm_num
  have hT := chAimg_arith6_sqrt_core ha hCk hM hℓ hμ hnB
  have hcoef : 0 ≤ C0 * Cs * (1 + R) ^ 3 * d ^ 192
      * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a) := by
    positivity
  rw [hd192]
  calc C0 * d ^ 192 / ℓ ^ 3
        * (Cs * (1 + R) ^ 3 * ℓ ^ 3 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
        * (Real.sqrt (ℓ ^ 3 * nB)
            * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB))
      = (C0 * Cs * (1 + R) ^ 3 * d ^ 192 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
          * (Real.sqrt (ℓ ^ 3 * nB)
            * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB)) := by
        field_simp
    _ ≤ (C0 * Cs * (1 + R) ^ 3 * d ^ 192 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
          * (nB * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
              * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := mul_le_mul_of_nonneg_left hT hcoef
    _ = nB * (C0 * Cs * (1 + R) ^ 3 * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
            * d ^ (192 : ℕ)
            * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
            * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := by ring

theorem chAimg_arith6 {a ε₀ C0 Cs Ck M R nB : ℝ} (ha : 0 < a) (hC0 : 0 ≤ C0) (hCs : 0 ≤ Cs)
    (hCk : 0 ≤ Ck) (hM : 0 ≤ M) (hR : 0 ≤ R) (hnB : 0 ≤ nB) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ t ℓ μ d : ℝ, 0 < t → t ≤ ε₀ →
      ℓ = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / a ^ 2) ^ (-(1 / 2 : ℝ)) →
      μ = t / a ^ 3 → d = Work.BoseBox.fsXp t 6 →
      C0 * d ^ (2 * 96 : ℕ) / ℓ ^ 3
          * (Cs * (1 + R) ^ 3 * ℓ ^ 3 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
          * (Real.sqrt (ℓ ^ 3 * nB)
              * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB))
        ≤ K0 * a / (8 * μ * (1 + ℓ ^ 3)) * nB := by
  -- the `chAimg_arith5` slot bound at the constant `C0·Cs(1+R)³·max (√(2Ck)) (√2 M)`
  obtain ⟨K5, hK5pos, h5⟩ := chAimg_arith5 (a := a) (ε₀ := ε₀)
      (C := C0 * Cs * (1 + R) ^ 3 * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M))
      ha (by positivity)
  refine ⟨K5, hK5pos, ?_⟩
  intro t ℓ μ d ht htε hℓ hμ hd
  have hℓk : 0 < ℓ := by
    rw [hℓ, Work.BoseBox.fsXp]
    exact mul_pos (Real.rpow_pos_of_pos ht _)
      (Real.rpow_pos_of_pos (show (0 : ℝ) < t / a ^ 2 by positivity) _)
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  have hred' := chAimg_arith6_reduce_aux (d := d) ha.le hC0 hCs hCk hM hR hnB hℓk hμ0
  have h5' := h5 t ℓ μ ht htε hℓ hμ
  have hdeq : d ^ (192 : ℕ) = (Work.BoseBox.fsXp t 6) ^ (192 : ℕ) := by rw [hd]
  calc C0 * d ^ (2 * 96 : ℕ) / ℓ ^ 3
        * (Cs * (1 + R) ^ 3 * ℓ ^ 3 * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a))
        * (Real.sqrt (ℓ ^ 3 * nB)
            * Real.sqrt (2 * (Ck * μ ^ 2 * a * ℓ ^ 3 * nB) + 2 * M ^ 2 * (ℓ ^ 2)⁻¹ * nB))
      ≤ nB * (C0 * Cs * (1 + R) ^ 3 * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
            * d ^ (192 : ℕ)
            * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
            * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := hred'
    _ = nB * (C0 * Cs * (1 + R) ^ 3 * max (Real.sqrt (2 * Ck)) (Real.sqrt 2 * M)
            * (Work.BoseBox.fsXp t 6) ^ (192 : ℕ)
            * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
            * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)) := by rw [hdeq]
    _ ≤ nB * (K5 * a / (8 * μ * (1 + ℓ ^ 3))) := mul_le_mul_of_nonneg_left h5' hnB
    _ = K5 * a / (8 * μ * (1 + ℓ ^ 3)) * nB := by ring

end Work.BoseBoxFock.PCFU
