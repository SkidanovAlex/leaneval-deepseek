import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-!
## The pointwise product bound `HkIntegrand α 4 (R·g) ≤ C K² HkIntegrand α 4 g`

`R` is a coefficient whose `D_z`-iterates are bounded by `K` and whose mixed derivatives of
angular order `≥ 1` are bounded by `K · sin 2θ`; `g` is an arbitrary function.  The claim is
the pointwise domination of the `H⁴`-integrand of the product `R·g` by `K²` times that of `g`.

The proof is the binomial expansion of `D_z^i (R·g)` resp. `D_z^j D_θ^i (R·g)`
(`leibniz_open_Dz`, `leibniz_open_mixed`), Cauchy–Schwarz on the resulting finite sums
(`sq_sum_le_card_mul_sum_sq`), and the two facts that each Leibniz summand is (i) bounded by
`K` or `K sin 2θ` in its `R`-factor and (ii) a genuine summand of `HkIntegrand α 4 g`.
The single analytic input is
`(sin 2θ · Wt α z θ)² ≤ (w z / sin(2θ)^{η/2})²`, which makes up the deficit of one power of
`sin 2θ` left over by the `R`-factor in the case where every angular derivative falls on `R`.
-/

/-- `n.choose k ≤ 2^n ≤ 16` for `n ≤ 4`, hence `(n.choose k : ℝ)² ≤ 256`. -/
private theorem binom_sq_le_256_local (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := by
    have h := Finset.single_le_sum (f := fun j => n.choose j) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rwa [Nat.sum_range_choose] at h
  have h16 : ((n.choose k : ℕ) : ℝ) ≤ 16 := by
    have h2 : n.choose k ≤ 2 ^ 4 := le_trans h1 (pow_le_pow_right₀ (by norm_num) hn)
    have h3 : ((n.choose k : ℕ) : ℝ) ≤ ((2 ^ 4 : ℕ) : ℝ) := by exact_mod_cast h2
    simpa using h3
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((n.choose k : ℕ) : ℝ) ^ 2 = ((n.choose k : ℕ) : ℝ) * ((n.choose k : ℕ) : ℝ) := by ring
    _ ≤ 16 * 16 := mul_self_le_mul_self h0 h16
    _ = 256 := by norm_num

/-- The one analytic input: the angular weight `Wt` is dominated by the `η`-weight once the
extra power of `sin 2θ` supplied by the hypothesis on the `R`-factor is paid. -/
private theorem sin_mul_Wt_sq_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Real.sin (2 * θ) * Wt α z θ) ^ 2
      ≤ (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2 := by
  have hs2p : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [Real.pi_pos]
  have hs2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(eta / 2) ≤ 1 - gam α / 2 := by
    rw [eta, gam]; linarith
  have hle : Real.sin (2 * θ) ^ (1 - gam α / 2)
      ≤ Real.sin (2 * θ) ^ (-(eta / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hs2p hs2le hexp
  have hw : 0 ≤ w z := by
    rw [w]; positivity
  have hsp : Real.sin (2 * θ) ^ (1 - gam α / 2)
      = Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(gam α / 2)) := by
    rw [show (1 : ℝ) - gam α / 2 = 1 + (-(gam α / 2)) from by ring,
      Real.rpow_add hs2p, Real.rpow_one]
  have h1 : Real.sin (2 * θ) * Wt α z θ
      = w z * Real.sin (2 * θ) ^ (1 - gam α / 2) := by
    calc Real.sin (2 * θ) * Wt α z θ
        = Real.sin (2 * θ) * (w z * Real.sin (2 * θ) ^ (-(gam α / 2))) := by
          rw [Wt, wTheta]
      _ = w z * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(gam α / 2))) := by ring
      _ = w z * Real.sin (2 * θ) ^ (1 - gam α / 2) := by rw [← hsp]
  have h2 : w z / (Real.sin (2 * θ)) ^ (eta / 2)
      = w z * Real.sin (2 * θ) ^ (-(eta / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hs2p.le (eta / 2)]
  rw [h1, h2]
  have h := mul_self_le_mul_self (mul_nonneg hw (Real.rpow_nonneg hs2p.le _))
    (mul_le_mul_of_nonneg_left hle hw)
  simpa [pow_two] using h

/-- The pure `D_z`-slots of `HkIntegrand α 4 (R·g)`. -/
private theorem zslot {α K : ℝ} {R g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hKnn : 0 ≤ K) (hRsm : Work.FTS.EllipticEst.SmoothOpen R)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hK1 : ∀ c : ℕ, c ≤ 4 → |DzIter c R z θ| ≤ K)
    (i : ℕ) (hi : i ≤ 4) :
    (DzIter i (fun z θ => R z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ 6400 * K ^ 2 * HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ HkIntegrand α 4 g z θ := HkIntegrand_nonneg α 4 g z θ
  have hXnn : 0 ≤ K ^ 2 * HkIntegrand α 4 g z θ := mul_nonneg (sq_nonneg K) hHk
  have hcs : (DzIter i (fun z θ => R z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
              * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) ^ 2 := by
    have hsum : DzIter i (fun z θ => R z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))
        = ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
              * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) := by
      rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i R g hRsm hgsm z θ hz hθ0 hθ1,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsum]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => ((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
        * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))))
    simpa using h
  have hterm : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
          * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) ^ 2
        ≤ 256 * (K ^ 2 * HkIntegrand α 4 g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb4 : b ≤ 4 := le_trans hbi hi
    have hib : i - b ≤ 4 := le_trans (Nat.sub_le i b) hi
    have hcb : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 :=
      binom_sq_le_256_local i b hbi hi
    have hR : (DzIter b R z θ) ^ 2 ≤ K ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hKnn]
      exact hK1 b hb4
    have hG : (DzIter (i - b) g z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ HkIntegrand α 4 g z θ :=
      sq_le_HkIntegrand_z α 4 g z θ (i - b) hib
    have hY : (DzIter b R z θ
        * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))) ^ 2
        ≤ K ^ 2 * HkIntegrand α 4 g z θ := by
      rw [show (DzIter b R z θ
            * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))) ^ 2
          = (DzIter b R z θ) ^ 2
            * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 from by ring]
      exact mul_le_mul hR hG (sq_nonneg _) (sq_nonneg _)
    rw [show (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
          * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (DzIter b R z θ
          * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))) ^ 2 from by ring]
    exact mul_le_mul hcb hY (sq_nonneg _) (by norm_num)
  have hbound : ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
              * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) ^ 2
      ≤ 6400 * (K ^ 2 * HkIntegrand α 4 g z θ) := by
    calc ((i + 1 : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              (((i.choose b : ℕ) : ℝ) * (DzIter b R z θ
                * (DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))))) ^ 2
        ≤ ((i + 1 : ℕ) : ℝ) * ∑ _b ∈ Finset.range (i + 1),
            (256 * (K ^ 2 * HkIntegrand α 4 g z θ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * (K ^ 2 * HkIntegrand α 4 g z θ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 6400 * (K ^ 2 * HkIntegrand α 4 g z θ) := by
          have hi5 : (((i + 1 : ℕ)) : ℝ) ≤ 5 := by
            have : i + 1 ≤ 5 := by omega
            exact_mod_cast this
          have h0 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
          nlinarith [hi5, h0, hXnn, mul_nonneg h0 hXnn]
  linarith [hcs, hbound]

/-- The mixed (`1 ≤ θ`-order) slots of `HkIntegrand α 4 (R·g)`. -/
private theorem mslot {α K : ℝ} {R g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hKnn : 0 ≤ K) (hRsm : Work.FTS.EllipticEst.SmoothOpen R)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hK1 : ∀ c : ℕ, c ≤ 4 → |DzIter c R z θ| ≤ K)
    (hK2 : ∀ b i : ℕ, 1 ≤ i → b + i ≤ 4 →
      |mixed b i R z θ| ≤ K * Real.sin (2 * θ))
    (hsin : (Real.sin (2 * θ) * Wt α z θ) ^ 2
      ≤ (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ) ^ 2
      ≤ 40960000 * K ^ 2 * HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ HkIntegrand α 4 g z θ := HkIntegrand_nonneg α 4 g z θ
  have hXnn : 0 ≤ K ^ 2 * HkIntegrand α 4 g z θ := mul_nonneg (sq_nonneg K) hHk
  have hcst : 0 ≤ 65536 * (K ^ 2 * HkIntegrand α 4 g z θ) :=
    mul_nonneg (by norm_num) hXnn
  have hs2pos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    linarith [Real.pi_pos]
  have hs2nn : 0 ≤ Real.sin (2 * θ) := hs2pos.le
  have hs2sq : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    have := Real.sin_le_one (2 * θ)
    nlinarith [hs2nn]
  have hlei := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i R g hRsm hgsm
    z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => ((i.choose a : ℕ) : ℝ) * ((j.choose b : ℕ) : ℝ)
    * (mixed b a R z θ * (mixed (j - b) (i - a) g z θ * Wt α z θ)) with hYdef
  have hYsplit : (mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2 := by
    have hkey : mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b := by
      rw [hlei, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      simp only [hYdef]
      ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (Y a b) ^ 2 ≤ 65536 * (K ^ 2 * HkIntegrand α 4 g z θ) := by
    intro a ha b hb
    have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hi4 : i ≤ 4 := le_trans (Nat.le_add_right i j) hij
    have hj4 : j ≤ 4 := le_trans (Nat.le_add_left j i) hij
    have hb4 : b ≤ 4 := le_trans hbj hj4
    have hba : b + a ≤ 4 :=
      le_trans (Nat.add_le_add hbj hai) (by rw [Nat.add_comm]; exact hij)
    have hsum4 : i + (j - b) ≤ 4 :=
      le_trans (Nat.add_le_add_left (Nat.sub_le j b) i) hij
    have hsub4 : (i - a) + (j - b) ≤ 4 :=
      le_trans (Nat.add_le_add (Nat.sub_le i a) (Nat.sub_le j b)) hij
    have hjb4 : j - b ≤ 4 := le_trans (Nat.sub_le j b) hj4
    have hch : (((i.choose a : ℕ) : ℝ)) ^ 2 * (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 65536 := by
      have h1 : (((i.choose a : ℕ) : ℝ)) ^ 2 ≤ 256 :=
        binom_sq_le_256_local i a hai hi4
      have h2 : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 :=
        binom_sq_le_256_local j b hbj hj4
      calc (((i.choose a : ℕ) : ℝ)) ^ 2 * (((j.choose b : ℕ) : ℝ)) ^ 2
          ≤ 256 * 256 := mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hcore : (mixed b a R z θ
        * (mixed (j - b) (i - a) g z θ * Wt α z θ)) ^ 2
        ≤ K ^ 2 * HkIntegrand α 4 g z θ := by
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · -- all angular derivatives fall on `g`
        simp only [ha0, mixed_zero_right, Nat.sub_zero]
        have hR : (DzIter b R z θ) ^ 2 ≤ K ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hKnn]
          exact hK1 b hb4
        have hG : (mixed (j - b) i g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 g z θ :=
          sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hi hsum4
        rw [show (DzIter b R z θ * (mixed (j - b) i g z θ * Wt α z θ)) ^ 2
            = (DzIter b R z θ) ^ 2 * (mixed (j - b) i g z θ * Wt α z θ) ^ 2 from by ring]
        exact mul_le_mul hR hG (sq_nonneg _) (sq_nonneg _)
      · -- `1 ≤ a`: the `R`-factor carries an angular derivative
        have hKa : (mixed b a R z θ) ^ 2 ≤ K ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
          have h := hK2 b a hapos hba
          have h' : |mixed b a R z θ| ≤ |K * Real.sin (2 * θ)| := by
            rwa [abs_of_nonneg (mul_nonneg hKnn hs2nn)]
          calc (mixed b a R z θ) ^ 2 ≤ (K * Real.sin (2 * θ)) ^ 2 := sq_le_sq.mpr h'
            _ = K ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
        rcases Nat.eq_zero_or_pos (i - a) with hia0 | hiapos
        · -- `a = i`: all angular derivatives fall on `R`, the `g`-factor is a `D_z`-slot
          rw [hia0, mixed_zero_right]
          have hG : (DzIter (j - b) g z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ HkIntegrand α 4 g z θ :=
            sq_le_HkIntegrand_z α 4 g z θ (j - b) hjb4
          rw [show (mixed b a R z θ * (DzIter (j - b) g z θ * Wt α z θ)) ^ 2
              = (mixed b a R z θ) ^ 2 * (DzIter (j - b) g z θ * Wt α z θ) ^ 2 from by ring]
          calc (mixed b a R z θ) ^ 2 * (DzIter (j - b) g z θ * Wt α z θ) ^ 2
              ≤ (K ^ 2 * (Real.sin (2 * θ)) ^ 2)
                * (DzIter (j - b) g z θ * Wt α z θ) ^ 2 :=
                mul_le_mul_of_nonneg_right hKa (sq_nonneg _)
            _ = K ^ 2 * (DzIter (j - b) g z θ
                  * (Real.sin (2 * θ) * Wt α z θ)) ^ 2 := by ring
            _ ≤ K ^ 2 * (DzIter (j - b) g z θ
                  * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
                refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
                rw [show (DzIter (j - b) g z θ * (Real.sin (2 * θ) * Wt α z θ)) ^ 2
                    = (DzIter (j - b) g z θ) ^ 2 * (Real.sin (2 * θ) * Wt α z θ) ^ 2
                    from by ring,
                  show (DzIter (j - b) g z θ
                      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
                    = (DzIter (j - b) g z θ) ^ 2
                      * (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2 from by ring]
                exact mul_le_mul_of_nonneg_left hsin (sq_nonneg _)
            _ ≤ K ^ 2 * HkIntegrand α 4 g z θ :=
                mul_le_mul_of_nonneg_left hG (sq_nonneg K)
        · -- `1 ≤ i - a`: both factors are genuine slots of `HkIntegrand α 4 g`
          have hG : (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
              ≤ HkIntegrand α 4 g z θ :=
            sq_le_HkIntegrand_mixed α 4 g z θ (i - a) (j - b) hiapos hsub4
          rw [show (mixed b a R z θ * (mixed (j - b) (i - a) g z θ * Wt α z θ)) ^ 2
              = (mixed b a R z θ) ^ 2
                * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 from by ring]
          calc (mixed b a R z θ) ^ 2 * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
              ≤ (K ^ 2 * (Real.sin (2 * θ)) ^ 2)
                * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 :=
                mul_le_mul_of_nonneg_right hKa (sq_nonneg _)
            _ ≤ (K ^ 2 * 1) * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
                refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
                exact mul_le_mul_of_nonneg_left hs2sq (sq_nonneg K)
            _ = K ^ 2 * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by ring
            _ ≤ K ^ 2 * HkIntegrand α 4 g z θ :=
                mul_le_mul_of_nonneg_left hG (sq_nonneg K)
    rw [show (Y a b) ^ 2 = (((i.choose a : ℕ) : ℝ)) ^ 2 * (((j.choose b : ℕ) : ℝ)) ^ 2
        * (mixed b a R z θ * (mixed (j - b) (i - a) g z θ * Wt α z θ)) ^ 2 from by
      rw [hYdef]; ring]
    exact mul_le_mul hch hcore (sq_nonneg _) (by norm_num)
  have hcardI : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hij25 : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 25 := by
    have hi44 : i ≤ 4 := le_trans (Nat.le_add_right i j) hij
    have hj44 : j ≤ 4 := le_trans (Nat.le_add_left j i) hij
    have hi4 : (i : ℝ) ≤ 4 := by exact_mod_cast hi44
    have hj4 : (j : ℝ) ≤ 4 := by exact_mod_cast hj44
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2
      ≤ ∑ _a ∈ Finset.range (i + 1), ∑ _b ∈ Finset.range (j + 1),
          (65536 * (K ^ 2 * HkIntegrand α 4 g z θ)) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ _a ∈ Finset.range (i + 1), ∑ _b ∈ Finset.range (j + 1),
        (65536 * (K ^ 2 * HkIntegrand α 4 g z θ))
      = ((i : ℝ) + 1) * ((j : ℝ) + 1) * (65536 * (K ^ 2 * HkIntegrand α 4 g z θ)) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  rw [hYsplit]
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun a => ∑ b ∈ Finset.range (j + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ _a ∈ Finset.range (i + 1), ∑ _b ∈ Finset.range (j + 1),
              (65536 * (K ^ 2 * HkIntegrand α 4 g z θ)) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
          * (65536 * (K ^ 2 * HkIntegrand α 4 g z θ)) := by
        rw [hsumconst]; ring
    _ ≤ 625 * (65536 * (K ^ 2 * HkIntegrand α 4 g z θ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hcst
        have h0 : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
        nlinarith [hij25, h0]
    _ = 40960000 * K ^ 2 * HkIntegrand α 4 g z θ := by ring

theorem starProdPt :
    ∃ C : ℝ, 0 < C ∧ ∀ (α K : ℝ) (R g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen R →
      Work.FTS.EllipticEst.SmoothOpen g →
      (∀ c : ℕ, c ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter c R z θ| ≤ K) →
      (∀ b i : ℕ, 1 ≤ i → b + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b i R z θ| ≤ K * Real.sin (2 * θ)) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => R z θ * g z θ) z θ
          ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨2000000000, by norm_num, ?_⟩
  intro α K R g hα hα1 hKnn hRsm hgsm hK1 hK2 z θ hz hθ0 hθ1
  have hHk : 0 ≤ HkIntegrand α 4 g z θ := HkIntegrand_nonneg α 4 g z θ
  have h1 : ∀ c : ℕ, c ≤ 4 → |DzIter c R z θ| ≤ K := fun c hc => hK1 c hc z θ hz hθ0 hθ1
  have h2 : ∀ b i : ℕ, 1 ≤ i → b + i ≤ 4 →
      |mixed b i R z θ| ≤ K * Real.sin (2 * θ) :=
    fun b i hi hib => hK2 b i hi hib z θ hz hθ0 hθ1
  have hsin : (Real.sin (2 * θ) * Wt α z θ) ^ 2
      ≤ (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2 :=
    sin_mul_Wt_sq_le (z := z) (θ := θ) hα hα1 hθ0 hθ1
  have hZ : ∀ i : ℕ, i ≤ 4 →
      (DzIter i (fun z θ => R z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ 6400 * K ^ 2 * HkIntegrand α 4 g z θ :=
    fun i hi => zslot hKnn hRsm hgsm hz hθ0 hθ1 h1 i hi
  have hM : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
      (mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 40960000 * K ^ 2 * HkIntegrand α 4 g z θ :=
    fun i j hi hij => mslot hKnn hRsm hgsm hz hθ0 hθ1 h1 h2 hsin i j hi hij
  have hZnn : 0 ≤ 6400 * K ^ 2 * HkIntegrand α 4 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hHk
  have hMnn : 0 ≤ 40960000 * K ^ 2 * HkIntegrand α 4 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hHk
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  have hA : (∑ i ∈ Finset.range (4 + 1),
        (DzIter i (fun z θ => R z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
      ≤ 5 * (6400 * K ^ 2 * HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1),
          (DzIter i (fun z θ => R z θ * g z θ) z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1), (6400 * K ^ 2 * HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (6400 * K ^ 2 * HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hB : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0))
      ≤ 25 * (40960000 * K ^ 2 * HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (mixed j i (fun z θ => R z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
            (40960000 * K ^ 2 * HkIntegrand α 4 g z θ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]; exact hM i j hc.1 hc.2
          · rw [if_neg hc]; exact hMnn
      _ = 25 * (40960000 * K ^ 2 * HkIntegrand α 4 g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hfin : 5 * (6400 * K ^ 2 * HkIntegrand α 4 g z θ)
      + 25 * (40960000 * K ^ 2 * HkIntegrand α 4 g z θ)
      ≤ 2000000000 * K ^ 2 * HkIntegrand α 4 g z θ := by
    have h0 : 0 ≤ K ^ 2 * HkIntegrand α 4 g z θ := mul_nonneg (sq_nonneg K) hHk
    nlinarith [h0]
  linarith [hA, hB, hfin]

end Work.FTS.NonlinRows.NRow10aux
