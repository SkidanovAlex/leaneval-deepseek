import Mathlib
import ChallengeDeps
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.liouville.chi_primeRecips_bounded
import Submission.Work.BMF.liouville.sum_char_recip_re_eq


namespace Work.BMF.liouville

open Polynomial BoundedMultiplicativeFunctions
open Finset

/-!
# Uniform-in-the-modulus lower bound for `∑_{p ≤ x, p ≡ 1 (mod q)} 1/p`

The per-modulus statement `∑_{p ≤ x, p ≡ 1 (mod q)} 1/p ≥ φ(q)⁻¹ log log x - O_q(1)` follows from
* character orthogonality: summing `∑_p χ(p)/p` over all characters mod `q` and taking real parts
  recovers `φ(q) ∑_{p ≤ x, p ≡ 1 (mod q)} 1/p`;
* Mertens' second theorem `∑_{p ≤ x} 1/p = log log x + O(1)` for the principal character;
* boundedness of `∑_p χ(p)/p` for every nonprincipal `χ` (a fixed-modulus Siegel–Walfisz-type
  input).
Taking the maximum over the finitely many moduli `q ≤ Q` makes the constant uniform in `q ≤ Q`.
-/

/-- The primes dividing `Q` contribute at most `Q + 1` to a reciprocal prime sum. -/
private lemma sum_inv_primes_dvd_le {Q : ℕ} (hQ : 1 ≤ Q) (x : ℝ) :
    ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ∣ Q), (1 : ℝ) / p ≤ (Q : ℝ) + 1 := by
  classical
  set S := (⌊x⌋₊).primesLE.filter (fun p ↦ p ∣ Q) with hS
  have hsub : S ⊆ Finset.range (Q + 1) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    obtain ⟨hpP, hpdvd⟩ := hp
    have hle : p ≤ Q := Nat.le_of_dvd (by omega) hpdvd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hterm : ∀ p ∈ S, (1 : ℝ) / p ≤ 1 := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp.1)
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have : (1 : ℕ) ≤ p := by omega
      exact_mod_cast this
    rw [div_le_one (by linarith)]
    exact hp1
  calc ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) := by simp
    _ ≤ (Q : ℝ) + 1 := by
        have hcard : S.card ≤ Q + 1 := by
          have h := Finset.card_le_card hsub
          simpa using h
        exact_mod_cast hcard

/-- The principal character contributes `Σ_{p ≤ x, p ∤ Q} 1/p`. -/
private lemma principal_char_sum_re (Q : ℕ) (x : ℝ) :
    (∑ p ∈ (⌊x⌋₊).primesLE, ((1 : DirichletCharacter ℂ Q) p : ℂ) / (p : ℂ)).re
      = ∑ p ∈ (⌊x⌋₊).primesLE, (if p ∣ Q then 0 else (1 : ℝ) / p) := by
  classical
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hval : ((1 : DirichletCharacter ℂ Q) p : ℂ) = if p ∣ Q then 0 else 1 := by
    by_cases h : p ∣ Q
    · rw [if_pos h]
      have hnu : ¬ IsUnit ((p : ℕ) : ZMod Q) := by
        intro hu
        rw [ZMod.isUnit_iff_coprime, hpprime.coprime_iff_not_dvd] at hu
        exact hu h
      rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ Q) hnu]
    · rw [if_neg h]
      have hu : IsUnit ((p : ℕ) : ZMod Q) := by
        rw [ZMod.isUnit_iff_coprime, hpprime.coprime_iff_not_dvd]
        exact h
      rw [MulChar.one_apply hu]
  rw [hval]
  by_cases h : p ∣ Q
  · simp [h]
  · rw [if_neg h, if_neg h]
    rw [← Complex.ofReal_one, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re]

/-- `log log x ≤ 2` on `[2, 11]`. -/
private lemma loglog_le_two {x : ℝ} (hx2 : 2 ≤ x) (hx : x ≤ 11) :
    Real.log (Real.log x) ≤ 2 := by
  have hx1 : 1 < x := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogxpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hx16 : x ≤ 16 := by linarith
  have h1 : Real.log (Real.log x) ≤ Real.log (Real.log 16) :=
    Real.log_le_log hlogxpos (Real.log_le_log (by linarith) hx16)
  have h2 : Real.log (Real.log 16) = Real.log (4 * Real.log 2) := by rw [hlog16]
  have h3 : Real.log (4 * Real.log 2) ≤ Real.log 4 :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith [h1, h2.le, h2.ge, h3, h4.le, h4.ge]

/-- `φ(q)⁻¹ log log x ≤ 2` for `2 ≤ x ≤ 11`. -/
private lemma inv_totient_mul_loglog_le_two (q : ℕ+) {x : ℝ} (hx2 : 2 ≤ x) (hx : x ≤ 11) :
    ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) ≤ 2 := by
  have hphi1 : (1 : ℝ) ≤ ((q : ℕ).totient : ℝ) := by
    have h1 : 1 ≤ (q : ℕ).totient := Nat.totient_pos.mpr (by simpa using q.pos)
    exact_mod_cast h1
  have hphi0 : (0 : ℝ) < ((q : ℕ).totient : ℝ) := lt_of_lt_of_le one_pos hphi1
  have hinv1 : ((q : ℕ).totient : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hphi1
  have hinv0 : 0 ≤ ((q : ℕ).totient : ℝ)⁻¹ := inv_nonneg.mpr hphi0.le
  have hll : Real.log (Real.log x) ≤ 2 := loglog_le_two hx2 hx
  rcases lt_or_ge 0 (Real.log (Real.log x)) with h | h
  · calc ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x)
        ≤ 1 * Real.log (Real.log x) := mul_le_mul_of_nonneg_right hinv1 h.le
      _ = Real.log (Real.log x) := one_mul _
      _ ≤ 2 := hll
  · calc ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hinv0 h
      _ ≤ 2 := by norm_num

/-- **Per-modulus lower bound for `x ≥ 11`, conditional on the two character inputs.** -/
private theorem perModulus_core (q : ℕ+)
    (hbound : ∀ (χ : DirichletCharacter ℂ (q : ℕ)), χ ≠ 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
        ‖∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)‖ ≤ C)
    (horth : ∀ x : ℝ, (∑ χ : DirichletCharacter ℂ (q : ℕ),
        (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re)
        = ((q : ℕ).totient : ℝ) *
          ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 11 ≤ x →
      ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) - C ≤
        ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p := by
  classical
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hphi : (0 : ℝ) < ((q : ℕ).totient : ℝ) := by
    have : 0 < (q : ℕ).totient := Nat.totient_pos.mpr (by simpa using q.pos)
    exact_mod_cast this
  have hQ1 : 1 ≤ (q : ℕ) := q.one_le
  let G : DirichletCharacter ℂ (q : ℕ) → ℝ :=
    fun χ => if h : χ = 1 then 0 else Classical.choose (hbound χ h)
  have hG : ∀ χ : DirichletCharacter ℂ (q : ℕ), χ ≠ 1 →
      0 ≤ G χ ∧ ∀ x : ℝ, 2 ≤ x → ‖∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)‖ ≤ G χ := by
    intro χ hχ
    have hval : G χ = Classical.choose (hbound χ hχ) := by
      show (if h : χ = 1 then 0 else Classical.choose (hbound χ h)) = _
      rw [dif_neg hχ]
    rw [hval]
    exact Classical.choose_spec (hbound χ hχ)
  set B : ℝ := Finset.univ.sup' ⟨1, Finset.mem_univ 1⟩ G with hBdef
  have hB0 : 0 ≤ B := by
    have hle : G (1 : DirichletCharacter ℂ (q : ℕ)) ≤ B :=
      Finset.le_sup' G (Finset.mem_univ 1)
    have hG1 : G (1 : DirichletCharacter ℂ (q : ℕ)) = 0 := by
      show (if h : (1 : DirichletCharacter ℂ (q : ℕ)) = 1 then 0
        else Classical.choose (hbound 1 h)) = 0
      rw [dif_pos rfl]
    linarith [hle, hG1.le, hG1.ge]
  refine ⟨(Cm + (((q : ℕ) : ℝ) + 1) + ((q : ℕ).totient : ℝ) * B) / ((q : ℕ).totient : ℝ),
    ?_, ?_⟩
  · apply div_nonneg _ hphi.le
    have h1 : (0 : ℝ) ≤ ((q : ℕ) : ℝ) + 1 := by positivity
    linarith [hCmpos.le, h1, mul_nonneg hphi.le hB0]
  · intro x hx11
    have hMertens := hCm x hx11
    have htriv : (∑ p ∈ (⌊x⌋₊).primesLE,
        ((1 : DirichletCharacter ℂ (q : ℕ)) p : ℂ) / (p : ℂ)).re
        ≥ Real.log (Real.log x) - Cm - (((q : ℕ) : ℝ) + 1) := by
      rw [principal_char_sum_re]
      have hsplit1 : ∑ p ∈ (⌊x⌋₊).primesLE, (if p ∣ (q : ℕ) then 0 else (1 : ℝ) / p)
          = ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ ¬ p ∣ (q : ℕ)), (1 : ℝ) / p := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun p _ => by by_cases h : p ∣ (q : ℕ) <;> simp [h])
      have hsplit2 : ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ ¬ p ∣ (q : ℕ)), (1 : ℝ) / p
          = (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p)
            - ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ∣ (q : ℕ)), (1 : ℝ) / p := by
        have h := Finset.sum_filter_add_sum_filter_not (s := (⌊x⌋₊).primesLE)
          (p := fun p ↦ p ∣ (q : ℕ)) (f := fun p : ℕ => (1 : ℝ) / p)
        linarith
      rw [hsplit1, hsplit2]
      have hbound_dvd := sum_inv_primes_dvd_le hQ1 x
      have := neg_le_of_abs_le hMertens
      linarith
    have hsum_ge : (∑ χ : DirichletCharacter ℂ (q : ℕ),
        (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re)
        ≥ (Real.log (Real.log x) - Cm - (((q : ℕ) : ℝ) + 1))
          - ((q : ℕ).totient : ℝ) * B := by
      rw [← Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ)))
        (fun χ => (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re) (Finset.mem_univ 1)]
      have hrest : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1,
          (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re ≥
          -(((q : ℕ).totient : ℝ) * B) := by
        have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1,
            -B ≤ (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re := by
          intro χ hχ
          have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
          have hb := (hG χ hχ1).2 x (by linarith : (2 : ℝ) ≤ x)
          have hGB : G χ ≤ B := Finset.le_sup' G (Finset.mem_univ χ)
          have h2 := neg_le_of_abs_le
            (Complex.abs_re_le_norm (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)))
          linarith
        have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1).card
            ≤ (q : ℕ).totient := by
          have h1 := Finset.card_le_univ
            ((Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1)
          have h2 : Fintype.card (DirichletCharacter ℂ (q : ℕ)) = (q : ℕ).totient := by
            rw [← Nat.card_eq_fintype_card]
            exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q : ℕ)
          omega
        calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1,
              (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re
            ≥ ∑ _χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1, (-B) :=
              Finset.sum_le_sum hterm
          _ = -(((((Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1).card : ℝ)) * B) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
          _ ≥ -(((q : ℕ).totient : ℝ) * B) := by
              have hc : ((((Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))).erase 1).card : ℝ))
                  ≤ ((q : ℕ).totient : ℝ) := by exact_mod_cast hcard
              nlinarith [hB0, hc]
      linarith [htriv, hrest]
    have hS : ((q : ℕ).totient : ℝ) *
        (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p)
        ≥ (Real.log (Real.log x) - Cm - (((q : ℕ) : ℝ) + 1))
          - ((q : ℕ).totient : ℝ) * B := by
      rw [← horth x]
      exact hsum_ge
    have hkey : (∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p)
        ≥ ((q : ℕ).totient : ℝ)⁻¹ *
            (Real.log (Real.log x) - Cm - (((q : ℕ) : ℝ) + 1)
              - ((q : ℕ).totient : ℝ) * B) := by
      have h := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hphi.le)
      rw [← mul_assoc, inv_mul_cancel₀ hphi.ne', one_mul] at h
      exact h
    have heq : ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x)
        - (Cm + (((q : ℕ) : ℝ) + 1) + ((q : ℕ).totient : ℝ) * B) / ((q : ℕ).totient : ℝ)
        = ((q : ℕ).totient : ℝ)⁻¹ *
            (Real.log (Real.log x) - Cm - (((q : ℕ) : ℝ) + 1)
              - ((q : ℕ).totient : ℝ) * B) := by
      field_simp
      ring
    rw [heq]
    exact hkey

/-- **The uniform statement, conditional on the two character inputs.** -/
private theorem main_of_inputs (Q : ℕ+)
    (hbound : ∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)), χ ≠ 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
        ‖∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)‖ ≤ C)
    (horth : ∀ (q : ℕ+) (x : ℝ), (∑ χ : DirichletCharacter ℂ (q : ℕ),
        (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re)
        = ((q : ℕ).totient : ℝ) *
          ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ+) (x : ℝ), q ≤ Q → 2 ≤ x →
      ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) - C ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p := by
  classical
  have perMod2 : ∀ q : ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) - C ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p := by
    intro q
    obtain ⟨C0, hC00, hC0⟩ := perModulus_core q (fun χ hχ => hbound q χ hχ) (horth q)
    refine ⟨max C0 2, le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right _ _), ?_⟩
    intro x hx
    rcases lt_or_ge 11 x with hxlt' | hx11
    · have := hC0 x (le_of_lt hxlt')
      linarith [le_max_left C0 (2 : ℝ)]
    · have hle : ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) ≤ 2 :=
        inv_totient_mul_loglog_le_two q hx hx11
      have hsum0 : 0 ≤ ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]),
          (1 : ℝ) / p :=
        Finset.sum_nonneg (fun p _ => by positivity)
      linarith [le_max_right C0 (2 : ℝ)]
  let H : ℕ → ℝ := fun n => if hn : n = 0 then 0
    else Classical.choose (perMod2 ⟨n, Nat.pos_of_ne_zero hn⟩)
  have key : ∀ q : ℕ+, H (q : ℕ) =
      Classical.choose (perMod2 q) := by
    intro q
    have hne : (q : ℕ) ≠ 0 := ne_of_gt q.pos
    show (if hn : (q : ℕ) = 0 then 0
      else Classical.choose (perMod2 ⟨(q : ℕ), Nat.pos_of_ne_zero hn⟩))
      = Classical.choose (perMod2 q)
    rw [dif_neg hne]
    rw [show (⟨(q : ℕ), Nat.pos_of_ne_zero hne⟩ : ℕ+) = q from Subtype.ext rfl]
  have hH : ∀ q : ℕ+, 0 ≤ H (q : ℕ) ∧ ∀ x : ℝ, 2 ≤ x →
      ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) - H (q : ℕ) ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p := by
    intro q
    rw [key q]
    exact Classical.choose_spec (perMod2 q)
  refine ⟨max 0 ((Finset.Icc 1 (Q : ℕ)).sup' (Finset.nonempty_Icc.mpr Q.one_le) H),
    le_max_left _ _, ?_⟩
  intro q x hq hx
  have hmem : (q : ℕ) ∈ Finset.Icc 1 (Q : ℕ) := by
    rw [Finset.mem_Icc]
    exact ⟨q.one_le, by exact_mod_cast hq⟩
  have hle : H (q : ℕ) ≤ (Finset.Icc 1 (Q : ℕ)).sup' (Finset.nonempty_Icc.mpr Q.one_le) H :=
    Finset.le_sup' H hmem
  have hle2 : H (q : ℕ) ≤
      max 0 ((Finset.Icc 1 (Q : ℕ)).sup' (Finset.nonempty_Icc.mpr Q.one_le) H) :=
    le_trans hle (le_max_right _ _)
  have := (hH q).2 x hx
  linarith

/-- Uniform-in-the-modulus form of `∑_{p ≤ x, p ≡ 1 (mod q)} 1/p ≥ (1/φ(q)) log log x - O(1)`:
one constant `C` works for every modulus `q ≤ Q`.

Either redo the route through `Work.BMF.vk_prime_sums` (with a single exponent `A` chosen so
that `Q ≤ (log x)^A` for large `x`, so that all constants depend only on `Q`), or — cheaper —
take `C = max_{q ≤ Q} C_q` from the per-modulus statement
`Work.BMF.liouville.prime_recip_mod_one` (the set of moduli is finite, and the inequality is
monotone in `C`). -/
theorem prime_recip_mod_one_uniform (Q : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ+) (x : ℝ), q ≤ Q → 2 ≤ x →
      ((q : ℕ).totient : ℝ)⁻¹ * Real.log (Real.log x) - C ≤
        ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / p := by
  refine main_of_inputs Q ?_ (fun q x => sum_char_recip_re_eq q x)
  intro q χ hχ
  haveI : NeZero (q : ℕ) := ⟨q.pos.ne'⟩
  exact chi_primeRecips_bounded χ hχ

end Work.BMF.liouville
