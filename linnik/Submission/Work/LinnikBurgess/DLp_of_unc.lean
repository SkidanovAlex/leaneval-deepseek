import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

set_option linter.unusedVariables false

namespace Work.LinnikBurgess

/-- A support point `y` of Lemma A with `nval y < T` witnesses `DLp p (nval y) a b`.

Hints: `bval_transfer`'s content (`SuppTransfer`) gives `b_y = min (nval y) T = nval y` and
`p^(m + nval y) ∣ N(y)`, hence `p^(nval y) ∣ N(y)`; and `nval y < T` forces `N'(y) ≠ 0` with
`v_p(N'(y)) = nval y`, hence `p^(nval y) ∣ N'(y)`.  Take `y` itself as the witness (it is a unit at
`p` by `suppPred`). -/
theorem DLp_of_unc {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) {y : ℕ} (hy : suppPred p e a b y) (hbt : SuppTransfer p e a b)
    (hlt : nval p e a b y < capLevel p e) :
    DLp p (nval p e a b y) a b := by
  obtain ⟨hbval, hNdvd⟩ := hbt y hy
  obtain ⟨hunit, _⟩ := hy
  -- `b_y = min (nval y) T = nval y` because `nval y < T`.
  have hmin : min (nval p e a b y) (capLevel p e) = nval p e a b y :=
    min_eq_left (le_of_lt hlt)
  have hbv : bval p e a b y = nval p e a b y := by rw [hbval, hmin]
  -- `p ^ (nval y) ∣ N(y)` from `p ^ (m + b_y) ∣ N(y)` and `nval y ≤ m + b_y`.
  have hN : ((p ^ nval p e a b y : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
    rw [hbv] at hNdvd
    exact dvd_trans
      (Nat.cast_dvd_cast (pow_dvd_pow p (Nat.le_add_left (nval p e a b y) (cubeLevel p e)))) hNdvd
  -- `nval y < T` forces `N'(y) ≠ 0`.
  have hN'ne : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
    intro h
    rw [nval, if_pos h] at hlt
    omega
  have hnval : nval p e a b y
      = padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs := by
    rw [nval, if_neg hN'ne]
  -- `p ^ (nval y) ∣ N'(y)`.
  have hN' : ((p ^ nval p e a b y : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
    have hk : (p ^ padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ)
        ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs := pow_padicValNat_dvd
    have hkz : ((p ^ padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ) : ℤ)
        ∣ (critN a b).derivative.eval (y : ℤ) :=
      dvd_trans (Nat.cast_dvd_cast hk) (Int.natAbs_dvd.mpr (dvd_refl _))
    rwa [hnval]
  exact ⟨y, hunit, hN, hN'⟩

end Work.LinnikBurgess
