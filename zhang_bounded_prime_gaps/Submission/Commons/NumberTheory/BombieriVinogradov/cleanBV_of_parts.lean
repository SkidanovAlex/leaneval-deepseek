import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset Filter
open Classical

/-- The primitive-character Bombieri--Vinogradov sum cut off at `R`. -/
noncomputable def primBVSum (X R : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ * primSup q X

/-- The full (all characters) Bombieri--Vinogradov sum cut off at `Q`. -/
noncomputable def fullBVSum (X Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiSup q χ X

/-- The primitive Bombieri--Vinogradov sum over the range `R < q ≤ Q`. -/
noncomputable def tailBVSum (X R Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ * primSup q X

lemma primBVSum_eq_hSW (X R : ℕ) :
    primBVSum X R
      = ∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X) := rfl

lemma fullBVSum_eq_target (X Q : ℕ) :
    fullBVSum X Q
      = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X) := rfl

lemma tailBVSum_eq_hTail (X R Q : ℕ) :
    tailBVSum X R Q
      = ∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X) := rfl

lemma primBVSum_nonneg (X Q : ℕ) : 0 ≤ primBVSum X Q := by
  apply Finset.sum_nonneg
  intro q _
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · unfold primSup
    exact Finset.sum_nonneg (fun χ _ => chiSup_nonneg q X χ)

lemma primBVSum_split (X R Q : ℕ) (hRQ : R ≤ Q) :
    primBVSum X Q = primBVSum X R + tailBVSum X R Q := by
  unfold primBVSum tailBVSum
  have hset : Finset.Icc 1 Q = Finset.Icc 1 R ∪ Finset.Ioc R Q := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 R) (Finset.Ioc R Q) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ioc] at hy
    omega
  rw [hset, Finset.sum_union hdisj]

/-- For `1 ≤ L` and two exponents bounded by `-A`, the two powers absorb into `2 L^{-A}`. -/
lemma rpow_add_le_two_mul {L a b A : ℝ} (hL : 1 ≤ L) (ha : a ≤ -A) (hb : b ≤ -A) :
    L ^ a + L ^ b ≤ 2 * L ^ (-A) := by
  have h1 := Real.rpow_le_rpow_of_exponent_le hL ha
  have h2 := Real.rpow_le_rpow_of_exponent_le hL hb
  linarith

/-- `2 √X L^{K-A} ≤ X L^{-A}` whenever `2 L^K ≤ √X`. -/
lemma sqrt_absorb {L X K A : ℝ} (hL : 0 < L) (hX : 0 ≤ X)
    (hK : 2 * L ^ K ≤ Real.sqrt X) :
    2 * Real.sqrt X * L ^ (K - A) ≤ X * L ^ (-A) := by
  have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hLn : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL.le _
  rw [show K - A = K + (-A) by ring, Real.rpow_add hL]
  have hstep : 2 * L ^ K * (Real.sqrt X * L ^ (-A))
      ≤ Real.sqrt X * (Real.sqrt X * L ^ (-A)) :=
    mul_le_mul_of_nonneg_right hK (mul_nonneg hs hLn)
  calc 2 * Real.sqrt X * (L ^ K * L ^ (-A))
      = 2 * L ^ K * (Real.sqrt X * L ^ (-A)) := by ring
    _ ≤ Real.sqrt X * (Real.sqrt X * L ^ (-A)) := hstep
    _ = X * L ^ (-A) := by rw [← mul_assoc, Real.mul_self_sqrt hX]

/-- The "trivial" term `C₀ Q (log(2Q+2))² log(X+2)` is absorbed by `C₀ X L^{-A}`
once `Q L^B ≤ √X` and `2 L^K ≤ √X` with `3 - B = K - A`. -/
lemma termB_bound {L X Q B C0 K A : ℝ}
    (hL : 0 < L) (hC0 : 0 < C0) (hQ : 0 ≤ Q)
    (hQb : Q * L ^ B ≤ Real.sqrt X)
    (hK : 2 * L ^ K ≤ Real.sqrt X)
    (hKB : 3 - B = K - A)
    (hLq_nn : 0 ≤ Real.log (2*Q+2)) (hLqL : Real.log (2*Q+2) ≤ L)
    (hlog_nn : 0 ≤ Real.log (X+2)) (hlogX2 : Real.log (X+2) ≤ 2*L)
    (hX : 0 ≤ X) :
    C0 * Q * (Real.log (2*Q+2))^2 * Real.log (X+2) ≤ C0 * X * L ^ (-A) := by
  have hsq : (Real.log (2*Q+2))^2 ≤ L^2 := pow_le_pow_left₀ hLq_nn hLqL 2
  have hC0Q : 0 ≤ C0 * Q := mul_nonneg hC0.le hQ
  have hB1 : C0 * Q * (Real.log (2*Q+2))^2 * Real.log (X+2) ≤ C0 * Q * L^2 * (2*L) := by
    have h1 : C0 * Q * (Real.log (2*Q+2))^2 ≤ C0 * Q * L^2 :=
      mul_le_mul_of_nonneg_left hsq hC0Q
    calc C0 * Q * (Real.log (2*Q+2))^2 * Real.log (X+2)
        = (C0 * Q * (Real.log (2*Q+2))^2) * Real.log (X+2) := by ring
      _ ≤ (C0 * Q * L^2) * (2*L) :=
            mul_le_mul h1 hlogX2 hlog_nn (mul_nonneg hC0Q (sq_nonneg L))
      _ = C0 * Q * L^2 * (2*L) := by ring
  have hB2 : C0 * Q * L^2 * (2*L) ≤ C0 * X * L ^ (-A) := by
    have h2L : C0 * Q * L^2 * (2*L) = 2 * C0 * Q * L^3 := by ring
    rw [h2L]
    have hQB : Q * L^3 ≤ Real.sqrt X * L^(3 - B) := by
      have h1 : L ^ (3 - B) * L ^ B = L ^ 3 := by
        rw [← Real.rpow_add hL, show (3 - B) + B = 3 by ring, Real.rpow_ofNat]
      calc Q * L^3 = (Q * L^B) * L^(3 - B) := by rw [← h1]; ring
        _ ≤ Real.sqrt X * L^(3 - B) := mul_le_mul_of_nonneg_right hQb (Real.rpow_nonneg hL.le _)
    have step1 : 2 * C0 * Q * L^3 ≤ 2 * C0 * Real.sqrt X * L^(3 - B) := by
      calc 2 * C0 * Q * L^3 = 2 * C0 * (Q * L^3) := by ring
        _ ≤ 2 * C0 * (Real.sqrt X * L^(3 - B)) := mul_le_mul_of_nonneg_left hQB (by positivity)
        _ = 2 * C0 * Real.sqrt X * L^(3 - B) := by ring
    have step2 : 2 * C0 * Real.sqrt X * L^(3 - B) ≤ C0 * X * L ^ (-A) := by
      rw [hKB]
      calc 2 * C0 * Real.sqrt X * L ^ (K - A)
          = C0 * (2 * Real.sqrt X * L ^ (K - A)) := by ring
        _ ≤ C0 * (X * L ^ (-A)) := mul_le_mul_of_nonneg_left (sqrt_absorb hL hX hK) hC0.le
        _ = C0 * X * L ^ (-A) := by ring
    linarith [step1, step2]
  linarith [hB1, hB2]

/-- The primitive-sum contribution is absorbed by `2 C₀ X L^{-A}`. -/
lemma main_term_bound {L Lq X P C0 A A' : ℝ}
    (hL : 0 < L) (hL1 : 1 < L) (hC0 : 0 < C0) (hX : 0 ≤ X) (hP : 0 ≤ P)
    (hLq_nn : 0 ≤ Lq) (hLqL : Lq ≤ L)
    (hPbound : P ≤ X * (L ^ (-(3*A+42)) + L ^ (-(A'+12))))
    (ha : 2 + -(3*A+42) ≤ -A) (hb : 2 + -(A'+12) ≤ -A) :
    C0 * Lq^2 * P ≤ 2 * C0 * X * L ^ (-A) := by
  have hsq : Lq^2 ≤ L^2 := pow_le_pow_left₀ hLq_nn hLqL 2
  have h1 : C0 * Lq^2 * P ≤ C0 * L^2 * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC0.le) hP
  have h2 : C0 * L^2 * P ≤ C0 * L^2 * (X * (L ^ (-(3*A+42)) + L ^ (-(A'+12)))) :=
    mul_le_mul_of_nonneg_left hPbound (by positivity)
  have h3 : C0 * L^2 * (X * (L ^ (-(3*A+42)) + L ^ (-(A'+12))))
      = C0 * X * (L ^ (2 + -(3*A+42)) + L ^ (2 + -(A'+12))) := by
    have hcast : L ^ (2:ℝ) = L ^ 2 := Real.rpow_natCast L 2
    rw [← hcast]
    calc C0 * L ^ (2:ℝ) * (X * (L ^ (-(3*A+42)) + L ^ (-(A'+12))))
        = C0 * X * (L ^ (2:ℝ) * L ^ (-(3*A+42)) + L ^ (2:ℝ) * L ^ (-(A'+12))) := by ring
      _ = C0 * X * (L ^ ((2:ℝ) + -(3*A+42)) + L ^ ((2:ℝ) + -(A'+12))) := by
            simp_rw [← Real.rpow_add hL]
  have h4 : C0 * X * (L ^ (2 + -(3*A+42)) + L ^ (2 + -(A'+12))) ≤ C0 * X * (2 * L ^ (-A)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0.le hX)
    exact rpow_add_le_two_mul hL1.le ha hb
  calc C0 * Lq^2 * P
      ≤ C0 * L^2 * P := h1
    _ ≤ C0 * L^2 * (X * (L ^ (-(3*A+42)) + L ^ (-(A'+12)))) := h2
    _ = C0 * X * (L ^ (2 + -(3*A+42)) + L ^ (2 + -(A'+12))) := h3
    _ ≤ C0 * X * (2 * L ^ (-A)) := h4
    _ = 2 * C0 * X * L ^ (-A) := by ring

/-- **Assembly of the Bombieri--Vinogradov result from its two range pieces.**

`hSW` is the Siegel--Walfisz contribution (the range `q ≤ (log X)^{2A+40}`, the
output of `Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_primEventual`)
and `hTail` is the large-moduli contribution (`(log X)^{2A+40}/2 ≤ R ≤ q ≤ Q`,
the output of `Commons.NumberTheory.BombieriVinogradov.bmvt_tail_bound`).

Assuming both, the classical Bombieri--Vinogradov bound

`Σ_{q ≤ Q} φ(q)⁻¹ Σ_{χ mod q} sup_{y ≤ X} ‖Σ_{n ≤ y} Λ(n)χ(n) − δ(χ)y‖
   ≪_A X (log X)^{-A}`  for  `Q ≤ √X/(log X)^B`

holds for every `A ≥ 1`.  The route is: the primitive-character reduction
`Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive`, the
split `Σ_{q ≤ Q} ≤ Σ_{q ≤ R} + Σ_{R < q ≤ Q}` at `R = ⌊(log X)^{2A+40}⌋`, and the
absorption of the factors `(log(2Q+2))²` and `log(X+2)` (all `≪ (log X)^{10}`)
into the exponents `3A + 42` and `A + 12` of the two pieces. -/
theorem cleanBV_of_parts
    (hSW : ∀ A : ℝ, 0 < A → ∀ᶠ X : ℕ in Filter.atTop, ∀ R : ℕ,
        (R : ℝ) ≤ (Real.log (X : ℝ)) ^ (2 * A + 40) →
        (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(3 * A + 42)))
    (hTail : ∀ A : ℝ, 0 < A → ∀ᶠ X : ℕ in Filter.atTop, ∀ R Q : ℕ, 1 ≤ R → R ≤ Q →
        (Real.log (X : ℝ)) ^ (2 * A + 40) ≤ 2 * (R : ℝ) →
        (Q : ℝ) ≤ Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ (2 * A + 40) →
        (∑ q ∈ Finset.Ioc R Q, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + 12))) :
    ∀ A : ℝ, 1 ≤ A → ∃ B C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ B →
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
      ≤ C * (X : ℝ) * (Real.log (X : ℝ)) ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0pos, hC0⟩ := sum_charSup_le_log_mul_primitive
  set A' : ℝ := max (A - 10) 1 with hA'def
  have hA'pos : 0 < A' := by rw [hA'def]; exact lt_max_iff.mpr (Or.inr zero_lt_one)
  have hA'le : A' ≤ A := by rw [hA'def]; exact max_le_iff.mpr ⟨by linarith, hA⟩
  have hA'ge : A - 10 ≤ A' := by rw [hA'def]; exact le_max_left _ _
  refine ⟨2 * A' + 40, 3 * C0, by positivity, ?_⟩
  have hSWX := hSW A (by linarith)
  have hTailX := hTail A' hA'pos
  have hKpoly : ∀ᶠ X : ℕ in Filter.atTop,
      2 * (Real.log (X:ℝ)) ^ (3 - (2 * A' + 40) + A) ≤ Real.sqrt (X:ℝ) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (3 - (2 * A' + 40) + A)
      (by norm_num : (0:ℝ) < 1/2)
    have hbR := (Asymptotics.isLittleO_iff.mp hlo) (by norm_num : (0:ℝ) < 1/2)
    have hb := hbR.natCast_atTop
    filter_upwards [hb, eventually_ge_atTop (1:ℕ)] with x hx hx1
    have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
    have hlogx : 0 ≤ Real.log (x:ℝ) := Real.log_nonneg hx1'
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogx _),
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _)] at hx
    rw [Real.sqrt_eq_rpow]
    linarith
  have hbig : ∀ᶠ X : ℕ in Filter.atTop, 9 ≤ X ∧ 2 ≤ Real.log (X:ℝ) := by
    filter_upwards [eventually_ge_atTop (9:ℕ),
        (Real.tendsto_log_atTop.eventually_ge_atTop 2).natCast_atTop] with x hx hl
    exact ⟨hx, hl⟩
  filter_upwards [hSWX, hTailX, hKpoly, hbig] with X hSWX hTailX hKX hbig
  obtain ⟨hX9, hL2⟩ := hbig
  intro Q hQ
  let L : ℝ := Real.log (X:ℝ)
  have hL2' : 2 ≤ L := hL2
  have hLpos : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hXnn : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have hX9' : (9:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX9
  have hSW' : ∀ R : ℕ, (R:ℝ) ≤ L ^ (2*A+40) → primBVSum X R ≤ (X:ℝ) * L ^ (-(3*A+42)) := by
    intro R hR
    rw [primBVSum_eq_hSW]
    exact hSWX R hR
  have hTail' : ∀ R Q : ℕ, 1 ≤ R → R ≤ Q → L ^ (2*A'+40) ≤ 2*(R:ℝ) →
      (Q:ℝ) ≤ Real.sqrt (X:ℝ) / L ^ (2*A'+40) →
      tailBVSum X R Q ≤ (X:ℝ) * L ^ (-(A'+12)) := by
    intro R Q hR1 hRQ hrange hQb
    rw [tailBVSum_eq_hTail]
    exact hTailX R Q hR1 hRQ hrange hQb
  rw [← fullBVSum_eq_target X Q]
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · subst hQ0
    rw [show fullBVSum X 0 = 0 by
      simp only [fullBVSum, Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1),
        Finset.sum_empty]]
    have hLn : 0 ≤ L ^ (-A) := Real.rpow_nonneg hLpos.le _
    positivity
  · have hQ1 : 1 ≤ Q := by omega
    have hQnn : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
    have hQb : (Q:ℝ) * L ^ (2*A'+40) ≤ Real.sqrt (X:ℝ) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)).mp hQ
    have hQle : (Q:ℝ) ≤ Real.sqrt (X:ℝ) := by
      have h1 : (1:ℝ) ≤ L^(2*A'+40) := Real.one_le_rpow hL1.le (by linarith)
      calc (Q:ℝ) = (Q:ℝ) * 1 := by ring
        _ ≤ (Q:ℝ) * L^(2*A'+40) := mul_le_mul_of_nonneg_left h1 hQnn
        _ ≤ Real.sqrt (X:ℝ) := hQb
    set Rf : ℕ := Nat.floor (L ^ (2*A+40)) with hRfdef
    have hRf_le : (Rf:ℝ) ≤ L^(2*A+40) := by
      rw [hRfdef]; exact Nat.floor_le (Real.rpow_nonneg hLpos.le _)
    have hRf_ge1 : 1 ≤ Rf := by
      rw [hRfdef, Nat.one_le_floor_iff]
      exact Real.one_le_rpow hL1.le (by linarith)
    have hLbig : (2:ℝ) ≤ L ^ (2*A+40) := by
      have h1 : (2:ℝ) ^ (2*A+40) ≤ L ^ (2*A+40) :=
        Real.rpow_le_rpow (by norm_num) hL2 (by linarith)
      have h2 : (2:ℝ) ≤ (2:ℝ) ^ (2*A+40) := by
        calc (2:ℝ) = (2:ℝ) ^ (1:ℝ) := (Real.rpow_one 2).symm
          _ ≤ (2:ℝ) ^ (2*A+40) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      linarith
    have hRf_half : L ^ (2*A+40) / 2 ≤ (Rf:ℝ) := by
      have ht : L ^ (2*A+40) < (Rf:ℝ) + 1 := by
        rw [hRfdef]; exact Nat.lt_floor_add_one _
      linarith
    have hRf2 : L ^ (2*A'+40) ≤ 2 * (Rf:ℝ) := by
      have h2A' : L ^ (2*A'+40) ≤ L ^ (2*A+40) :=
        Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)
      linarith
    have hP : primBVSum X Q ≤ (X:ℝ) * (L ^ (-(3*A+42)) + L ^ (-(A'+12))) := by
      by_cases hcase : Q ≤ Rf
      · have hQRf : (Q:ℝ) ≤ L^(2*A+40) := by
          have : (Q:ℝ) ≤ (Rf:ℝ) := by exact_mod_cast hcase
          linarith [hRf_le]
        have h1 := hSW' Q hQRf
        have h2 : 0 ≤ (X:ℝ) * L^(-(A'+12)) :=
          mul_nonneg hXnn (Real.rpow_nonneg hLpos.le _)
        have hthis : (X:ℝ) * L^(-(3*A+42)) ≤ (X:ℝ) * (L^(-(3*A+42)) + L^(-(A'+12))) := by
          rw [mul_add]; exact le_add_of_nonneg_right h2
        exact le_trans h1 hthis
      · simp only [not_le] at hcase
        have hRfQ : Rf ≤ Q := le_of_lt hcase
        have h1 := hSW' Rf hRf_le
        have h2 := hTail' Rf Q hRf_ge1 hRfQ hRf2 hQ
        have hsplit := primBVSum_split X Rf Q hRfQ
        rw [hsplit, mul_add]
        exact add_le_add h1 h2
    have hLq_nn : 0 ≤ Real.log (2*(Q:ℝ)+2) := by
      apply Real.log_nonneg; linarith
    have hLqL : Real.log (2*(Q:ℝ)+2) ≤ L := by
      rw [show L = Real.log (X:ℝ) from rfl]
      apply Real.log_le_log
      · linarith
      · have hs3 : (3:ℝ) ≤ Real.sqrt (X:ℝ) := by
          rw [Real.le_sqrt (by norm_num) hXnn, show (3:ℝ)^2 = 9 by norm_num]
          exact hX9'
        have hsq := Real.sq_sqrt hXnn
        nlinarith [hQle, hs3, hsq]
    have hlog_nn : 0 ≤ Real.log ((X:ℝ)+2) := by
      apply Real.log_nonneg; linarith
    have hlogX2 : Real.log ((X:ℝ)+2) ≤ 2*L := by
      have hX2 : (X:ℝ) + 2 ≤ (X:ℝ)^2 := by nlinarith [hX9']
      calc Real.log ((X:ℝ)+2) ≤ Real.log ((X:ℝ)^2) :=
            Real.log_le_log (by linarith) hX2
        _ = 2 * Real.log (X:ℝ) := by rw [Real.log_pow]; push_cast; ring
        _ = 2 * L := by rfl
    have hC0X : fullBVSum X Q ≤ C0 * (Real.log (2*(Q:ℝ)+2))^2 * primBVSum X Q
        + C0 * (Q:ℝ) * (Real.log (2*(Q:ℝ)+2))^2 * Real.log ((X:ℝ)+2) := by
      have h := hC0 X Q hQ1
      rw [← fullBVSum_eq_target X Q, ← primBVSum_eq_hSW X Q] at h
      exact h
    calc fullBVSum X Q
        ≤ C0 * (Real.log (2*(Q:ℝ)+2))^2 * primBVSum X Q
            + C0 * (Q:ℝ) * (Real.log (2*(Q:ℝ)+2))^2 * Real.log ((X:ℝ)+2) := hC0X
      _ ≤ 2 * C0 * (X:ℝ) * L^(-A) + C0 * (X:ℝ) * L^(-A) := by
            apply add_le_add
            · exact main_term_bound hLpos hL1 hC0pos hXnn (primBVSum_nonneg X Q)
                hLq_nn hLqL hP (by linarith) (by linarith)
            · exact termB_bound hLpos hC0pos hQnn hQb hKX (by ring)
                hLq_nn hLqL hlog_nn hlogX2 hXnn
      _ = 3 * C0 * (X:ℝ) * L^(-A) := by ring

end Commons.NumberTheory.BombieriVinogradov
