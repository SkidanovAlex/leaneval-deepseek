import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ProdOpen.ProdDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option maxHeartbeats 1600000

open Work.Spaces

/-
IMPORTANT: do NOT import `Submission.Work.FTS.OpenPkg.ProdOpen.prod_majorant` (that module
contains a `sorry`); prove this from scratch.

Route.  `Hv z θ = w z / sin(2θ)^{η/2}` and `SInv`, `Texc` are in
`Submission/Work/FTS/OpenPkg/ProdOpen/ProdDefs.lean`.  Write `fg := fun z θ => f z θ * g z θ`.
1. `leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1` expands `DzIter i fg z θ` as a binomial sum;
   multiply by `Hv z θ`, use `Finset.sum_mul`, and Cauchy–Schwarz
   (`sq_sum_le_card_mul_sum_sq`) to get
   `(DzIter i fg z θ * Hv z θ)^2 ≤ (i+1) * ∑_{b ≤ i} (C(i,b))^2 * (DzIter b f * DzIter (i-b) g * Hv)^2`.
2. For each `b`, `b + (i-b) = i ≤ 4`, so `min b (i-b) ≤ 2`.  Put `x := DzIter b f z θ`,
   `y := DzIter (i-b) g z θ`, `ρ := Hv z θ`.
   * if `b ≤ i - b` (so `b ≤ 2`): `PwAny` (in `PwOpen.lean`) applied with `(b,a) = (b,0)` gives
     `x² ≤ CPw/(gam α - 1) * HkSq α 4 f` (note `mixed b 0 f = DzIter b f`), and
     `Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i-b) (by omega)` gives `(y*ρ)² ≤ HkIntegrand α 4 g z θ`;
   * if `i - b ≤ b`: symmetrically `PwAny` on `g` and `sq_le_HkIntegrand_z` on `f`.
   In both cases `(x*y*ρ)² = x² * (y*ρ)² ≤ CPw * SInv α f g z θ` (use
   `Work.FTS.OpenPkg.ProdOpen.mul_inv_mul_le_SInv_left/right` and the nonnegativity lemmas).
3. `(C(i,b) : ℝ)^2 ≤ 256` for `i ≤ 4` (bound `i.choose b ≤ 2^i ≤ 16`), and `∑_{b ≤ i} 1 = i+1 ≤ 5`,
   so `C := 6400 * CPw` works: the term in step 1 is `≤ (i+1) * 5 * 256 * CPw * Maj`, and
   `(i+1) * 5 * 256 ≤ 5*5*256 = 6400`; finally `CPw * SInv ≤ CPw * (SInv + Texc)`.
-/
theorem z_sum_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.FTS.OpenPkg.ProdOpen.SInv α f g z θ
            + Work.FTS.OpenPkg.ProdOpen.Texc α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPw⟩ := PwAny
  refine ⟨6400 * CPw, by positivity, ?_⟩
  intro α f g hα hα1 hF hFmem hG hGmem i hi z θ hz hθ0 hθ1
  change (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ 6400 * CPw * (SInv α f g z θ + Texc α f g z θ)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hSl : 0 ≤ SInv α f g z θ := SInv_nonneg hα f g z θ
  have hTl : 0 ≤ Texc α f g z θ := Texc_nonneg α f g z θ
  have hγ : 0 < gam α - 1 := gam_sub_one_pos hα
  have hKnn : ∀ (u : ℝ → ℝ → ℝ), 0 ≤ CPw / (gam α - 1) * HkSq α 4 u := fun u =>
    mul_nonneg (div_nonneg hCPwpos.le hγ.le) (HkSq_nonneg α 4 u)
  -- ### Step 1: Leibniz plus Cauchy–Schwarz
  have hcs : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2 := by
    have hsum : Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ
        = ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) := by
      rw [leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsum]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ))
    simpa using h
  -- ### Step 2: each Leibniz summand is dominated by `CPw * SInv`
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        ≤ 256 * (CPw * SInv α f g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 256 := by
      have h16 : i.choose b ≤ 16 := by
        calc i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
          _ = 16 := by norm_num
      have h16' : (i.choose b : ℝ) ≤ 16 := by exact_mod_cast h16
      have hnn : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hcore : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
        ≤ CPw * SInv α f g z θ := by
      by_cases hcase : b ≤ i - b
      · -- the `f`-factor is the one of low order `b ≤ 2`
        have hb2 : b ≤ 2 := by omega
        have hx : (DzIter b f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 f := by
          have h := hPw α f b 0 hα hα1 hF hFmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hy : (DzIter (i - b) g z θ * Hv z θ) ^ 2 ≤ HkIntegrand α 4 g z θ := by
          have h := sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega)
          simpa only [Hv] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
            = (DzIter b f z θ) ^ 2 * (DzIter (i - b) g z θ * Hv z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hy (hKnn f))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 4 f * HkIntegrand α 4 g z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkIntegrand α 4 g z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_left hα f g z θ) hCPwpos.le
      · -- the `g`-factor is the one of low order `i - b ≤ 2`
        have hib2 : i - b ≤ 2 := by omega
        have hy : (DzIter (i - b) g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 g := by
          have h := hPw α g (i - b) 0 hα hα1 hG hGmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hx : (DzIter b f z θ * Hv z θ) ^ 2 ≤ HkIntegrand α 4 f z θ := by
          have h := sq_le_HkIntegrand_z α 4 f z θ b (by omega)
          simpa only [Hv] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
            = (DzIter (i - b) g z θ) ^ 2 * (DzIter b f z θ * Hv z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hy (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx (hKnn g))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 4 g * HkIntegrand α 4 f z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkIntegrand α 4 f z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_right hα f g z θ) hCPwpos.le
    have h1 : ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2 := by
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  -- ### Step 3: sum the terms
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        ≤ ((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have hm : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
    have : (i : ℝ) ≤ 4 := by exact_mod_cast hi
    push_cast
    linarith
  have hKnn' : 0 ≤ 256 * (CPw * SInv α f g z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hCPwpos.le hSl)
  have hstep : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)))
      ≤ 6400 * (CPw * SInv α f g z θ) := by
    have hmnn : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ))
        ≤ 5 * (256 * (CPw * SInv α f g z θ)) := mul_le_mul_of_nonneg_right hm hKnn'
    have h2 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)))
        ≤ 5 * (5 * (256 * (CPw * SInv α f g z θ))) :=
      mul_le_mul hm h1 (mul_nonneg hmnn hKnn') (by norm_num)
    have h3 : 5 * (5 * (256 * (CPw * SInv α f g z θ))) = 6400 * (CPw * SInv α f g z θ) := by
      ring
    linarith [h2, h3]
  calc (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ)
          * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 6400 * (CPw * SInv α f g z θ) := hstep
    _ ≤ 6400 * (CPw * (SInv α f g z θ + Texc α f g z θ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCPwpos.le) (by norm_num)
    _ = 6400 * CPw * (SInv α f g z θ + Texc α f g z θ) := by ring

end Work.FTS.OpenPkg.ProdOpen
