import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_gexp
import Submission.Work.BW.tijdeman_rat
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.est17_Pi_int
import Submission.Work.BW.one_div_pow_le_exp
import Submission.Work.BW.est17_rat_exp_arg_le
import Submission.Work.BW.finitePlace_mul_le_inv_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- At a finite place `w` of a number field, the value at an integer is at most `1`
(the `w`-adic absolute value of an integer is `≤ 1` since `w` is non-archimedean). -/
lemma finitePlace_intCast_le_one {L : Type*} [Field L] [NumberField L]
    (w : NumberField.FinitePlace L) (N : ℤ) : w (N : L) ≤ 1 := by
  have hv : IsNonarchimedean (w ·) := NumberField.FinitePlace.add_le w
  exact hv.apply_intCast_le_one (by simp) (by simp) (by simp)

/-- The rational factor of the `est17_gexp` expansion of `g(s/2)` is bounded at a finite place
`w` of the Kummer extension by the Kummer/2-adic term.  Writing `Q` for the rational factor, the
`Π`-factor `∏_m Δ(γ_m(λ);t_m)` is an integer (`deltaRat_int`), `ulcm h` is a natural number, and
`tijdeman_rat (2^{J+1})` applied at `x = s + λ₋₁·2^{J+1}` gives
`(2^{J+1})^{2h(λ₀+1)}·u(h)^{t₀}·Θ((s/2^{J+1})+λ₋₁) ∈ ℤ`, whence
`w(u(h)^{t₀}Θ) ≤ w(2)^{-(J+1)·2h(λ₀+1)}`; since `w(2:L) ≤ 1` this is
`exp((J+1)·2h(λ₀+1)·|log w(2)|) ≤ exp(2(J+1)h(D₀+1)|log w(2)|)` as `λ₀+1 ≤ D₀+1`. -/
theorem est17_rat_fin_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (w : NumberField.FinitePlace (EL φ (rhoC φ α v Lm)))
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) :
    w (algebraMap ℚ (EL φ (rhoC φ α v Lm))
        ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
              (deltaPoly (t m)))
          * (ulcm (acH K b v) : ℚ) ^ t0
          * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
              (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))))
      ≤ Real.exp (2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
          * |Real.log (w (inclE φ (rhoC φ α v Lm) (2 : K)))|) := by
  classical
  -- the hypothesis bundle `H` is not needed for this place-by-place bound
  have _hH := H
  -- the `Π`-factor is an integer
  obtain ⟨N1, hN1⟩ := est17_Pi_int (K := K) (n := n) (r := r) (v := v) (b := b) (k := k)
      (Lm := Lm) (σl := σl) (ι := ι) (t := t) lm
  -- the 2-adic/Tijdeman contribution is an integer after multiplying by `(2^{J+1})^{2h(λ₀+1)}`
  obtain ⟨N2, hN2⟩ := tijdeman_rat (2 ^ (J + 1)) (Nat.one_le_pow (J + 1) 2 (by norm_num))
      (s + (lm.1 : ℤ) * (2 : ℤ) ^ (J + 1)) (acH K b v) ((lm.2.1 : ℕ) + 1) t0
  set Pi : ℚ := ∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
      (deltaPoly (t m)) with hPidef
  set U : ℚ := (ulcm (acH K b v) : ℚ) ^ t0 with hUdef
  set Th : ℚ := Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
      (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))) with hThdef
  have hxq : (((s + (lm.1 : ℤ) * (2 : ℤ) ^ (J + 1) : ℤ)) : ℚ) / ((2 ^ (J + 1) : ℕ) : ℚ)
      = (s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ) := by
    push_cast
    field_simp
    ring
  rw [hxq, ← hThdef] at hN2
  have hW2 : inclE φ (rhoC φ α v Lm) (2 : K) = (2 : EL φ (rhoC φ α v Lm)) := by
    rw [map_ofNat]
  -- push `hN2` through `algebraMap ℚ L`
  have hN2A : algebraMap ℚ (EL φ (rhoC φ α v Lm))
          (((2 ^ (J + 1) : ℕ) : ℚ) ^ (2 * acH K b v * ((lm.2.1 : ℕ) + 1)))
        * algebraMap ℚ (EL φ (rhoC φ α v Lm)) U
        * algebraMap ℚ (EL φ (rhoC φ α v Lm)) Th
      = (N2 : EL φ (rhoC φ α v Lm)) := by
    have h := congrArg (algebraMap ℚ (EL φ (rhoC φ α v Lm))) hN2
    simpa only [map_mul, map_intCast] using h
  have hQ0 : algebraMap ℚ (EL φ (rhoC φ α v Lm))
        (((2 ^ (J + 1) : ℕ) : ℚ) ^ (2 * acH K b v * ((lm.2.1 : ℕ) + 1)))
      = (inclE φ (rhoC φ α v Lm) (2 : K))
          ^ ((J + 1) * (2 * acH K b v * ((lm.2.1 : ℕ) + 1))) := by
    rw [map_pow]
    have hm : algebraMap ℚ (EL φ (rhoC φ α v Lm)) (((2 ^ (J + 1) : ℕ) : ℚ))
        = inclE φ (rhoC φ α v Lm) (2 : K) ^ (J + 1) := by
      rw [map_natCast]
      push_cast
      rw [← hW2]
    rw [hm]
    exact (pow_mul _ (J + 1) (2 * acH K b v * ((lm.2.1 : ℕ) + 1))).symm
  have hPi_le : w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) Pi) ≤ 1 := by
    have hN1' : Pi = (N1 : ℚ) := by rw [hPidef]; exact hN1
    rw [hN1', map_intCast]
    exact finitePlace_intCast_le_one w N1
  have hWpos : 0 < w (inclE φ (rhoC φ α v Lm) (2 : K)) := by
    refine NumberField.FinitePlace.pos_iff.mpr ?_
    rw [hW2]
    norm_num
  have hWle : w (inclE φ (rhoC φ α v Lm) (2 : K)) ≤ 1 := by
    have h2 : inclE φ (rhoC φ α v Lm) (2 : K) = ((2 : ℤ) : EL φ (rhoC φ α v Lm)) := by
      rw [hW2]; norm_num
    rw [h2]; exact finitePlace_intCast_le_one w 2
  have hyz : w ((inclE φ (rhoC φ α v Lm) (2 : K))
          ^ ((J + 1) * (2 * acH K b v * ((lm.2.1 : ℕ) + 1)))
        * algebraMap ℚ (EL φ (rhoC φ α v Lm)) U
        * algebraMap ℚ (EL φ (rhoC φ α v Lm)) Th) ≤ 1 := by
    rw [← hQ0, hN2A]
    exact finitePlace_intCast_le_one w N2
  have hl : (lm.2.1 : ℕ) ≤ pD0 r (dK K) σl := Nat.lt_succ_iff.mp lm.2.1.isLt
  have hMn : ((((J + 1) * (2 * acH K b v * ((lm.2.1 : ℕ) + 1)) : ℕ) : ℝ))
      ≤ 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1) :=
    est17_rat_exp_arg_le (h := acH K b v) (l := (lm.2.1 : ℕ)) hl
  have hkey := finitePlace_mul_le_inv_pow w hWpos hPi_le hyz
  calc w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) (Pi * U * Th))
      = w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) Pi
            * algebraMap ℚ (EL φ (rhoC φ α v Lm)) U
            * algebraMap ℚ (EL φ (rhoC φ α v Lm)) Th) := by simp only [map_mul]
    _ ≤ 1 / (w (inclE φ (rhoC φ α v Lm) (2 : K)))
            ^ ((J + 1) * (2 * acH K b v * ((lm.2.1 : ℕ) + 1))) := hkey
    _ ≤ Real.exp (((((J + 1) * (2 * acH K b v * ((lm.2.1 : ℕ) + 1)) : ℕ) : ℝ))
            * |Real.log (w (inclE φ (rhoC φ α v Lm) (2 : K)))|) :=
        one_div_pow_le_exp hWpos hWle le_rfl
    _ ≤ Real.exp (2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * |Real.log (w (inclE φ (rhoC φ α v Lm) (2 : K)))|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hMn (abs_nonneg _))

end Work.BW
