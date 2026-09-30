import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.bprodOdd_pow_le_exp_neg_evW
import Submission.Work.BW.acH_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `4S^{(J)} ≤ X + 2` with `X = evX r J S = 2⌊2ξ^{-rJ}S⌋`: the floor loses at most `1`, so
`X ≥ 4ξ^{-rJ}S - 2`. This is where the `+2` in the `X`-hypothesis of `(23')` comes from. -/
private lemma even_step_W_four_SJ_le_X_add_two {r J : ℕ} {S : ℝ} :
    4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S) ≤ (evX r J S : ℝ) + 2 := by
  have h := Nat.lt_floor_add_one (2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S))
  have hX : (evX r J S : ℝ)
      = 2 * ((⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℕ) : ℝ) := by
    rw [evX, evSP]; push_cast; ring
  rw [hX]
  have h' : 2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)
      < ((⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊ : ℕ) : ℝ) + 1 := h
  linarith

/-- `S = pS r d h ≥ 1` for `r ≥ 2`, `d ≥ 1`, `h ≥ 1`. -/
private lemma one_le_pS {r d h : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) :
    1 ≤ pS r d h := by
  rw [pS]
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (show (1:ℕ) ≤ 16 by norm_num) hr) hd) hh
  simpa using h

/-- The `W`-hypothesis of `extrap_core` in the even step in the `Finset`-product form used by the
assembly: `(23')` for the lacunary Blaschke product `B'(·;X)` with `X = 2S'`, `R = 7.2S'`,
`T' = ⌊(1−ξ)ξ^rT^{(J)}⌋`, from `|s| ≤ 4S^{(J)}`. -/
theorem even_step_W {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) ≤ 4 * SJ K r b v J) :
    ‖∏ l ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ)) ((evX r J (acS K r b v)) : ℕ)).filter Odd,
        bfac (evR r J (acS K r b v)) l (s : ℂ) ^ (evTp r J (acT K σ) + 1)‖
      ≤ Real.exp (-(evW r (dK K) (acH K b v) σ J)) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := Module.finrank_pos
  have h19 : 19 ≤ acH K b v := (acH_lower H).1
  -- `S = pS r (dK K) (acH K b v) ≥ 1`, needed by `(23')`.
  have hS1 : (1 : ℝ) ≤ (pS r (dK K) (acH K b v) : ℝ) := by
    exact_mod_cast one_le_pS (by omega : 1 ≤ r) hd (by omega : 1 ≤ acH K b v)
  -- `|s| ≤ 4S^{(J)} ≤ X + 2`.
  have hszX : |((s : ℤ) : ℝ)| ≤ (evX r J (pS r (dK K) (acH K b v) : ℝ) : ℝ) + 2 := by
    rw [← Int.cast_abs]
    refine le_trans ?_ (even_step_W_four_SJ_le_X_add_two (r := r) (J := J)
      (S := (pS r (dK K) (acH K b v) : ℝ)))
    simpa only [SJ, acS] using hs
  -- Raising the lacunary product to a power multiplies the exponents in.
  have hprod :
      (∏ l ∈ (Finset.Icc (-(((evX r J (acS K r b v)) : ℕ) : ℤ))
            ((evX r J (acS K r b v)) : ℕ)).filter Odd,
          bfac (evR r J (acS K r b v)) l (s : ℂ) ^ (evTp r J (acT K σ) + 1))
        = bprodOdd (evR r J (acS K r b v)) (evX r J (acS K r b v)) (s : ℂ)
            ^ (evTp r J (acT K σ) + 1) := by
    rw [Finset.prod_pow]
    rfl
  rw [hprod]
  have hchild := bprodOdd_pow_le_exp_neg_evW (r := r) hr (d := dK K) (h := acH K b v) (J := J)
    (σ := σ) (sz := ((s : ℤ) : ℝ)) hszX hS1
  have hcast : ((((s : ℤ) : ℝ)) : ℂ) = (s : ℂ) := by simp
  rw [← hcast]
  exact hchild

end Work.BW
