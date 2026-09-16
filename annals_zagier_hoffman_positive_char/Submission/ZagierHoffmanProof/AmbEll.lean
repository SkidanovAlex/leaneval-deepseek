import Submission.ZagierHoffmanProof.AmbPeriodEll
import Submission.ZagierHoffmanProof.AmbPure
import Submission.ZagierHoffmanProof.PowerSum
import Submission.ZagierHoffmanProof.AmbTransferVal

/-!
# The elements `ℓ_d` of `Ambient F` and the pure case of the bridge

The paper's `ℓ_d := ∏_{i=1}^{d}(θ - θ^{q^i}) ∈ K` (`ℓ_0 := 1`) is the degree-`d` "power-sum"
denominator: for `1 ≤ n ≤ q` one has `P_d(n) = ∑_{deg a = d, a monic} a^{-n} = ℓ_d^{-n}` (the
*pure case*, `StepL199.P_eq_pow_of_le_card` + `StepL195.Hsum_closed`).  This file transfers that
statement to `Ambient F`, where it becomes

  `ambInfHom (P_d(n)) = ambEll d ^ (-(n : ℤ))`,   `ambEll d := ∏_{i<d}(θ - θ^{q^{i+1}})`.

It is the per-degree input of the `ζ_A ↔ CMPL` bridge (Dac (4.2)).

## Main results

* `ambTheta_pow_card_pow_ne` — `θ^{q^k} ≠ θ` for `k ≥ 1`.
* `ambEll`, `ambEll_ne_zero`, `ambEll_eq_prod`, `ambEll_eq_evalSeriesGen_ellSh`.
* ★★★ `ambInfHom_P_eq_ambEll` — the pure case in `Ambient F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. `θ^{q^k} ≠ θ` -/

/-- `θ^{q^k} ≠ θ` for `k ≥ 1`: the two have different valuations. -/
lemma ambTheta_pow_card_pow_ne (k : ℕ) (hk : 1 ≤ k) :
    (ambTheta F) ^ (Nat.card F ^ k) ≠ ambTheta F := by
  intro h
  have hv : Valued.v ((ambTheta F) ^ (Nat.card F ^ k)) = Valued.v (ambTheta F) := by rw [h]
  rw [map_pow, v_ambTheta, ← WithZero.exp_nsmul] at hv
  rw [show ((Nat.card F : ℚ) - 1) = 1 • ((Nat.card F : ℚ) - 1) from (one_nsmul _).symm] at hv
  have hq1 : (1 : ℚ) < Nat.card F := by
    have h2 : (2 : ℕ) ≤ Nat.card F := two_le_ambCard F
    exact_mod_cast (by omega : 1 < Nat.card F)
  have hqm : ((Nat.card F : ℚ) - 1) ≠ 0 := by linarith
  have h4 : (((Nat.card F ^ k : ℕ)) : ℚ) * ((Nat.card F : ℚ) - 1)
      = ((Nat.card F : ℚ) - 1) := by
    have h5 := WithZero.exp_injective hv
    rwa [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_one, one_mul] at h5
  have h2 : ((Nat.card F : ℚ) ^ k) = 1 := by
    have h5 : (((Nat.card F ^ k : ℕ)) : ℚ) * ((Nat.card F : ℚ) - 1)
        = (1 : ℚ) * ((Nat.card F : ℚ) - 1) := by
      rw [one_mul]; exact h4
    have h6 := mul_right_cancel₀ hqm h5
    push_cast at h6
    exact h6
  have h3 : (1 : ℚ) < (Nat.card F : ℚ) ^ k := one_lt_pow₀ hq1 (by omega)
  rw [h2] at h3
  exact lt_irrefl 1 h3

/-! ## §2. The element `ℓ_d` -/

/-- `ℓ_d = ∏_{i=1}^{d}(θ-θ^{q^i})` in `Ambient F` (the paper's `ℓ_d`). -/
noncomputable def ambEll (K : Type*) [Field K] [Finite K] : ℕ → Ambient K
  | 0 => 1
  | (d + 1) => ambEll K d * ((ambTheta K) - (ambTheta K) ^ (Nat.card K ^ (d + 1)))

@[simp] lemma ambEll_zero : ambEll F 0 = 1 := rfl

lemma ambEll_succ (d : ℕ) :
    ambEll F (d + 1) = ambEll F d * ((ambTheta F) - (ambTheta F) ^ (Nat.card F ^ (d + 1))) :=
  rfl

/-- `ℓ_d` as an explicit product. -/
lemma ambEll_eq_prod (d : ℕ) :
    ambEll F d = ∏ i ∈ Finset.range d,
      ((ambTheta F) - (ambTheta F) ^ (Nat.card F ^ (i + 1))) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ambEll_succ, ih, Finset.prod_range_succ]

/-- **`ℓ_d ≠ 0`** for every `d` (the factors have pairwise different valuations). -/
lemma ambEll_ne_zero (d : ℕ) : ambEll F d ≠ 0 := by
  rw [ambEll_eq_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact sub_ne_zero.mpr (ambTheta_pow_card_pow_ne F (i + 1) (by omega)).symm

/-- `ℓ_d` is the evaluation at `θ` of the polynomial `ellSh q θ 1 d`. -/
lemma ambEll_eq_evalSeriesGen_ellSh (d : ℕ) :
    ambEll F d = evalSeriesGen
      (ellSh (Nat.card F) (ambTheta F) 1 d : PowerSeries (Ambient F)) (ambTheta F) := by
  rw [ambEll_eq_prod, evalSeriesGen_ellSh (q := Nat.card F) (θ := ambTheta F)
    (γ := ambGamma) ambGamma_lt_one gammaArchimedean_rat ambGamma_pos 1 d]

/-! ## §3. The pure case of the bridge -/

/-- ★★★ **The pure case of the `ζ_A ↔ CMPL` bridge, per degree**: for `1 ≤ n ≤ q`,
`ambInfHom (P_d(n)) = ℓ_d^{-n}` in `Ambient F`. -/
theorem ambInfHom_P_eq_ambEll (d : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    ambInfHom F (P F d n) = (ambEll F d) ^ (-(n : ℤ)) := by
  have key : ambInfHom F (P F d oneExp)
      = (∏ i ∈ Finset.range d,
          ((ambTheta F) - (ambTheta F) ^ (Nat.card F ^ (i + 1))))⁻¹ := by
    rw [ambInfHom_P_one F d, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ambKEquiv_Afac]
  rw [ambInfHom_P F d n hn, key, ambEll_eq_prod, inv_pow, zpow_neg, zpow_natCast]

end ZagierHoffmanPositiveChar
