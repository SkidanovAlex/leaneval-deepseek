import Submission.ZagierHoffmanProof.ATPoly
import Submission.ZagierHoffmanProof.PowerSumSecondBlock
import Submission.ZagierHoffmanProof.AmbEll
import Submission.ZagierHoffmanProof.AmbInf

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma ambInfHom_ratfuncX :
    ambInfHom F ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) = ambTheta F := by
  rw [ambInfHom_coe]
  exact ambKHom_X F

theorem ambH_interp {k d : ℕ} (hk : 2 ≤ k) (hk2 : k ≤ Nat.card F - 1) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambH F (Nat.card F + k - 1) : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
        (ambTheta F)
      = ((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (Nat.card F + k - 1)
        * ambInfHom F (P F d ⟨Nat.card F + k - 1, by omega⟩) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  set n0 : ℕ+ := ⟨Nat.card F + k - 1, by omega⟩ with hn0
  have key : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambH F (n0 : ℕ) : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
        (ambTheta F)
      = ((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (n0 : ℕ)
        * ambInfHom F (P F d n0) := by
    have hA := PSB.second_block F d k (by omega) hk2
    have hP : (∑' a : {p : Polynomial F // p.Monic ∧ p.natDegree = d},
        (((algebraMap (Polynomial F) (RatFunc F) a.1 : RatFunc F) : RatFunc.CompletionAtInfty F)
          ^ (Nat.card F + k - 1))⁻¹) = P F d n0 := by
      have hb : P F d n0 = (∑' b : {p : Polynomial F // p ∈ MonicDeg F d},
          (((b.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n0 : ℕ))⁻¹) := rfl
      rw [hb, ← Equiv.tsum_eq
        (Equiv.subtypeEquivRight
          (p := fun p : Polynomial F => p.Monic ∧ p.natDegree = d)
          (q := fun p : Polynomial F => p ∈ MonicDeg F d) (fun p => Iff.rfl))
        (fun b : {p : Polynomial F // p ∈ MonicDeg F d} =>
          (((b.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n0 : ℕ))⁻¹)]
      exact tsum_congr (fun a => rfl)
    rw [hP] at hA
    have hmap := congrArg (ambInfHom F) hA
    simp only [map_mul, map_pow, map_sub, map_prod, map_natCast, map_div₀] at hmap
    simp only [ambInfHom_ratfuncX F] at hmap
    rw [← ambEll_eq_prod F d] at hmap
    have hD : (ambTheta F) ^ Nat.card F - ambTheta F ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => ambTheta_pow_card_pow_ne F 1 le_rfl (by simpa using h)
    have hclear : ((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (n0 : ℕ)
          * ambInfHom F (P F d n0)
        = (k : Ambient F) * ((ambTheta F) ^ Nat.card F - (ambTheta F))
          - ((k - 1 : ℕ) : Ambient F)
            * ((ambTheta F) ^ (Nat.card F ^ (d + 1)) - (ambTheta F)) := by
      have h3 : ambInfHom F (P F d n0) * (ambEll F d) ^ (n0 : ℕ)
          = (k : Ambient F) - ((k - 1 : ℕ) : Ambient F)
              * (((ambTheta F) ^ (Nat.card F ^ (d + 1)) - (ambTheta F))
                  / ((ambTheta F) ^ Nat.card F - (ambTheta F))) := hmap
      calc ((ambTheta F) ^ Nat.card F - (ambTheta F)) * (ambEll F d) ^ (n0 : ℕ)
              * ambInfHom F (P F d n0)
          = ((ambTheta F) ^ Nat.card F - (ambTheta F))
              * (ambInfHom F (P F d n0) * (ambEll F d) ^ (n0 : ℕ)) := by ring
        _ = ((ambTheta F) ^ Nat.card F - (ambTheta F))
              * ((k : Ambient F) - ((k - 1 : ℕ) : Ambient F)
                * (((ambTheta F) ^ (Nat.card F ^ (d + 1)) - (ambTheta F))
                    / ((ambTheta F) ^ Nat.card F - (ambTheta F)))) := by rw [h3]
        _ = (k : Ambient F) * ((ambTheta F) ^ Nat.card F - (ambTheta F))
          - ((k - 1 : ℕ) : Ambient F)
            * ((ambTheta F) ^ (Nat.card F ^ (d + 1)) - (ambTheta F)) := by
              field_simp
    rw [evalSeriesGen_frobTwist_ambH F (n := (n0 : ℕ)) (d := d) (by
      have : (n0 : ℕ) = Nat.card F + k - 1 := rfl
      omega)]
    rw [hclear]
    have hk1 : (n0 : ℕ) - Nat.card F = k - 1 := by
      have : (n0 : ℕ) = Nat.card F + k - 1 := rfl
      omega
    rw [hk1]
    have hk2' : ((k - 1 + 1 : ℕ) : Ambient F) = (k : Ambient F) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [hk2']
    have hk3 : ((k - 1 : ℕ) : Ambient F) = (k : Ambient F) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    rw [hk3]
    ring
  simpa [hn0] using key



/-- **The `H_n`-interpolation in the first block** (`n ≤ q`): `H_n = 1`, `Γ_n = 1` and
`P_d(n) = ambEll(d)^{-n}`, so `(H_n)^{(d)}(θ) = ambEll(d)^n·P_d(n)`. -/
theorem ambH_interp_le {d : ℕ} (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambH F (n : ℕ) : Polynomial (Ambient F)) : PowerSeries (Ambient F))) (ambTheta F)
      = (ambEll F d) ^ (n : ℕ) * ambInfHom F (P F d n) := by
  rw [ambH_of_le F hn]
  simp only [Polynomial.coe_one, frobTwist_one, evalSeriesGen_one]
  have hpure : ambInfHom F (P F d n) = ((ambEll F d) ^ (n : ℕ))⁻¹ := by
    rw [ambInfHom_P F d n hn]
    have h1 : ambInfHom F (P F d oneExp) = (ambEll F d)⁻¹ := by
      rw [ambInfHom_P_one F d, ambEll_eq_prod F d, Finset.prod_inv_distrib]
      exact congrArg Inv.inv (Finset.prod_congr rfl (fun i _ => ambKEquiv_Afac F (i + 1)))
    rw [h1, ← inv_pow]
  rw [hpure]
  exact (mul_inv_cancel₀ (pow_ne_zero _ (ambEll_ne_zero F d))).symm

end ZagierHoffmanPositiveChar
