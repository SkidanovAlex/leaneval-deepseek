import Submission.Work.Fx.FxAddChain

/-!
# `addHalf` and `subHalf` (paper Lemma 2.1)
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Fx

open HvdH

theorem normSq_re_im (P Q : ℝ) :
    Complex.normSq ((P : ℂ) + (Q : ℂ) * Complex.I) = P ^ 2 + Q ^ 2 := by
  first
    | (rw [Complex.normSq_apply]; simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring)
    | (rw [Complex.normSq_apply]; simp; ring)
    | (rw [Complex.normSq_apply]; simp only [RCLike.add_re, RCLike.add_im, RCLike.mul_re,
        RCLike.mul_im, RCLike.ofReal_re, RCLike.ofReal_im, Complex.I_re, Complex.I_im]; ring)
    | (simp [Complex.normSq_apply, Complex.ext_iff]; ring)

theorem norm_add_mul_I_lt_one (P Q : ℝ) (hP : |P| ≤ 1 / 2) (hQ : |Q| ≤ 1 / 2) :
    ‖(P : ℂ) + (Q : ℂ) * Complex.I‖ < 1 := by
  have hle : Complex.normSq ((P : ℂ) + (Q : ℂ) * Complex.I) ≤ 1 / 2 := by
    rw [normSq_re_im]
    nlinarith [abs_le.mp hP, abs_le.mp hQ]
  have h2 : ‖(P : ℂ) + (Q : ℂ) * Complex.I‖ ^ 2 =
      Complex.normSq ((P : ℂ) + (Q : ℂ) * Complex.I) := (Complex.normSq_eq_norm_sq _).symm
  nlinarith [norm_nonneg ((P : ℂ) + (Q : ℂ) * Complex.I)]

/-- Additive/subtractive half: the fixed-point value equals a scaled numerator. -/
theorem half_identity_add (p : ℕ) (a b c d : ℤ) :
    fxC p ((a + c).tdiv 2, (b + d).tdiv 2) - (fxC p (a, b) + fxC p (c, d)) / 2 =
      ((((a + c).tdiv 2 : ℤ) : ℂ) - ((a : ℂ) + (c : ℂ)) / 2 +
        ((((b + d).tdiv 2 : ℤ) : ℂ) - ((b : ℂ) + (d : ℂ)) / 2) * Complex.I) / (2 : ℂ) ^ p := by
  first
    | (simp only [fxC]; ring)
    | (rw [fxC, fxC, fxC]; field_simp; ring)
    | (simp only [fxC]; field_simp; ring)
    | (simp only [fxC]; push_cast; ring)

theorem half_identity_sub (p : ℕ) (a b c d : ℤ) :
    fxC p ((a - c).tdiv 2, (b - d).tdiv 2) - (fxC p (a, b) - fxC p (c, d)) / 2 =
      ((((a - c).tdiv 2 : ℤ) : ℂ) - ((a : ℂ) - (c : ℂ)) / 2 +
        ((((b - d).tdiv 2 : ℤ) : ℂ) - ((b : ℂ) - (d : ℂ)) / 2) * Complex.I) / (2 : ℂ) ^ p := by
  first
    | (simp only [fxC]; ring)
    | (rw [fxC, fxC, fxC]; field_simp; ring)
    | (simp only [fxC]; field_simp; ring)
    | (simp only [fxC]; push_cast; ring)

/-- Scaled error estimate from coordinatewise `tdiv 2` errors. -/
theorem scaled_half_err (p : ℕ) (P Q : ℝ) (hP : |P| ≤ 1 / 2) (hQ : |Q| ≤ 1 / 2) :
    (2 : ℝ) ^ p * ‖((P : ℂ) + (Q : ℂ) * Complex.I) / (2 : ℂ) ^ p‖ < 1 := by
  have hnorm : ‖((P : ℂ) + (Q : ℂ) * Complex.I) / (2 : ℂ) ^ p‖ =
      ‖(P : ℂ) + (Q : ℂ) * Complex.I‖ / 2 ^ p := by
    rw [norm_div, norm_pow]
    congr 1
    first
      | exact Complex.norm_ofNat 2
      | norm_num
  rw [hnorm, mul_div_assoc']
  have h2p : (2 : ℝ) ^ p ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ h2p]
  exact norm_add_mul_I_lt_one P Q hP hQ

theorem add_half_err (p : ℕ) (a b c d : ℤ) :
    (2 : ℝ) ^ p * ‖fxC p ((a + c).tdiv 2, (b + d).tdiv 2) -
      (fxC p (a, b) + fxC p (c, d)) / 2‖ < 1 := by
  rw [half_identity_add]
  set P : ℝ := ((a + c).tdiv 2 : ℝ) - ((a : ℝ) + (c : ℝ)) / 2 with hP
  set Q : ℝ := ((b + d).tdiv 2 : ℝ) - ((b : ℝ) + (d : ℝ)) / 2 with hQ
  have hcast : ((((a + c).tdiv 2 : ℤ) : ℂ) - ((a : ℂ) + (c : ℂ)) / 2) = (P : ℂ) := by
    rw [hP]; push_cast; ring
  have hcast2 : ((((b + d).tdiv 2 : ℤ) : ℂ) - ((b : ℂ) + (d : ℂ)) / 2) = (Q : ℂ) := by
    rw [hQ]; push_cast; ring
  rw [hcast, hcast2]
  exact scaled_half_err p P Q (by rw [hP]; simpa using tdiv_two_err (a + c))
    (by rw [hQ]; simpa using tdiv_two_err (b + d))

theorem sub_half_err (p : ℕ) (a b c d : ℤ) :
    (2 : ℝ) ^ p * ‖fxC p ((a - c).tdiv 2, (b - d).tdiv 2) -
      (fxC p (a, b) - fxC p (c, d)) / 2‖ < 1 := by
  rw [half_identity_sub]
  set P : ℝ := ((a - c).tdiv 2 : ℝ) - ((a : ℝ) - (c : ℝ)) / 2 with hP
  set Q : ℝ := ((b - d).tdiv 2 : ℝ) - ((b : ℝ) - (d : ℝ)) / 2 with hQ
  have hcast : ((((a - c).tdiv 2 : ℤ) : ℂ) - ((a : ℂ) - (c : ℂ)) / 2) = (P : ℂ) := by
    rw [hP]; push_cast; ring
  have hcast2 : ((((b - d).tdiv 2 : ℤ) : ℂ) - ((b : ℂ) - (d : ℂ)) / 2) = (Q : ℂ) := by
    rw [hQ]; push_cast; ring
  rw [hcast, hcast2]
  exact scaled_half_err p P Q (by rw [hP]; simpa using tdiv_two_err (a - c))
    (by rw [hQ]; simpa using tdiv_two_err (b - d))

/-- **Lemma 2.1, additive case.** -/
theorem addHalf_spec (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
        vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
        vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
        inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u + fxC p v) / 2‖ < 1)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil))) := by
  obtain ⟨cAd, KAd, hAd⟩ := hi.add
  obtain ⟨prog, K, hhalf⟩ := halfChain hk hi cAd KAd (fun a b => a + b) hAd
    isz_add_le'
    (fun p u v hu hv => inDisc_add_half hu hv)
    (fun p a b c d => (fxC p (a, b) + fxC p (c, d)) / 2)
    (fun p a b c d => add_half_err p a b c d)
  refine ⟨prog, K, ?_⟩
  intro main p
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
      vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (P' := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
      vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (Q := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧ inDisc p w ∧
      w = ((u.1 + v.1).tdiv 2, (u.2 + v.2).tdiv 2) ∧
      (2 : ℝ) ^ p * ‖fxC p w - (fxC p u + fxC p v) / 2‖ < 1)
    (Q' := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u + fxC p v) / 2‖ < 1)
    (C := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
    (C' := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
    (hhalf main p) (fun vs h => h) ?_ (fun vs _ => le_rfl)
  · intro vs out hvs hQ
    rcases hQ with ⟨u, v, rest, w, h1, h2, h3, h4, h5⟩
    exact ⟨u, v, rest, w, h1, h2, h3, h5⟩

/-- **Lemma 2.1, subtractive case.** -/
theorem subHalf_spec (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
        vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
        vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
        inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u - fxC p v) / 2‖ < 1)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil))) := by
  obtain ⟨cSb, KSb, hSb⟩ := hi.sub
  obtain ⟨prog, K, hhalf⟩ := halfChain hk hi cSb KSb (fun a b => a - b) hSb
    isz_sub_le'
    (fun p u v hu hv => inDisc_sub_half hu hv)
    (fun p a b c d => (fxC p (a, b) - fxC p (c, d)) / 2)
    (fun p a b c d => sub_half_err p a b c d)
  refine ⟨prog, K, ?_⟩
  intro main p
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
      vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (P' := fun vs => ∃ (u v : ℤ × ℤ) (rest : List Val),
      vs = cfxVal u :: cfxVal v :: rest ∧ inDisc p u ∧ inDisc p v)
    (Q := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧ inDisc p w ∧
      w = ((u.1 - v.1).tdiv 2, (u.2 - v.2).tdiv 2) ∧
      (2 : ℝ) ^ p * ‖fxC p w - (fxC p u - fxC p v) / 2‖ < 1)
    (Q' := fun vs out => ∃ (u v : ℤ × ℤ) (rest : List Val) (w : ℤ × ℤ),
      vs = cfxVal u :: cfxVal v :: rest ∧ out = cfxVal w :: rest ∧
      inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - (fxC p u - fxC p v) / 2‖ < 1)
    (C := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
    (C' := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil)))
    (hhalf main p) (fun vs h => h) ?_ (fun vs _ => le_rfl)
  · intro vs out hvs hQ
    rcases hQ with ⟨u, v, rest, w, h1, h2, h3, h4, h5⟩
    exact ⟨u, v, rest, w, h1, h2, h3, h5⟩

end Work.Fx
