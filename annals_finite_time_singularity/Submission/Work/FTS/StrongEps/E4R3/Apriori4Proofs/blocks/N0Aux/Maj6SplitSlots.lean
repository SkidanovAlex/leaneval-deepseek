/-
# `N0Aux.Maj6Split` — the level-matched radial majorant at level `6`

`Work.FTS.StrongPersist.H6Pair6Aux.radialMaj6` bounds the `ℋ⁶`-integrand of a product
`X z · f z θ` (with `X` radial, `C⁶` on `(0,∞)`) by a *single* constant `B` dominating the
`D_z`-iterates of `X` up to order `6`.  For the pieces of `N₀` the two regimes are different:
the low iterates (`j ≤ 4`) of `X = L₁₂(w)` are priced by the *small* quantity `|w|_{ℋ⁴}` (which
is `≤ C₀ α²` in the applications), while only the top iterates `j = 5, 6` are priced by
`|w|_{ℋ⁶}`.  Because the top iterates only occur in slots where *all but at most two*
derivatives fall on `f`, the lossy constant `B` can be replaced by the level-matched pair
`(Blo, Bhi)`:

  `HkSq α 6 (X · f) ≤ C (Blo² |f|²_{ℋ⁶} + Bhi² |f|²_{ℋ²})`,

with `C` universal.  This is the engine that makes the `α`-uniform estimates of the `N₀`-block
possible (a single `B` would produce the bound `B² |f|²_{ℋ⁶}` and lose the small factor).

The proof is copied from `radialMaj6`: the Leibniz expansion `leibniz_radial_mul` of each slot,
the single-slot bounds `sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed` (used at level `6` when
the derivative on `X` is `≤ 4` and at level `2` when it is `≥ 5`), binomial bounds
`b.choose k ≤ 2^b ≤ 64` and Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary bounds -/

/-- `b.choose k ≤ 2^b ≤ 64` for `b ≤ 6`, hence `((b.choose k : ℝ))² ≤ 4096`. -/
theorem choose_sq_le_4096 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 6) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
    have h : b.choose k ≤ 64 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

/-- At `z = 0` the weight vanishes, so every term of the weighted integrand vanishes there. -/
theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The value of the universal constant of the pointwise majorant. -/
def MajC : ℝ := 20000000

theorem MajC_pos : 0 < MajC := by norm_num [MajC]

/-! ## A single pure `D_z`-slot -/

theorem zslot6_split {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0 (by omega) z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    by_cases hb4 : b ≤ 4
    · have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Blo ^ 2 := by
        have hx := hLo b hb4
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBlo]
      have hG : (Work.Spaces.DzIter (i - b) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (i - b) (by omega)
      calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ 4096 * Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Blo ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Blo)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
              mul_nonneg (sq_nonneg Bhi) hHk2
            nlinarith [h1, hHk6, sq_nonneg Blo]
    · have hb5 : 5 ≤ b := by omega
      have hib : i - b ≤ 1 := by omega
      have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Bhi ^ 2 := by
        have hx := hHi b (by omega)
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBhi]
      have hG : (Work.Spaces.DzIter (i - b) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ (i - b) (by omega)
      calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ 4096 * Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Bhi ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Bhi)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_nonneg (sq_nonneg Blo) hHk6
            nlinarith [h1, hHk2, sq_nonneg Bhi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hMnn : 0 ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 7)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring

/-! ## A single mixed slot -/

theorem mslot6_split {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hj6 : j ≤ 6 := by omega
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj6 z θ hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 j b hbj hj6
    by_cases hb4 : b ≤ 4
    · have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Blo ^ 2 := by
        have hx := hLo b hb4
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBlo]
      have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i (j - b) hi (by omega)
      calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
          = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            ring
        _ ≤ 4096 * Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Blo ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Blo)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
              mul_nonneg (sq_nonneg Bhi) hHk2
            nlinarith [h1, hHk6, sq_nonneg Blo]
    · have hb5 : 5 ≤ b := by omega
      have hji : i + (j - b) ≤ 2 := by omega
      have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ Bhi ^ 2 := by
        have hx := hHi b (by omega)
        rw [← sq_abs]
        nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hBhi]
      have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i (j - b) hi hji
      calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
          = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            ring
        _ ≤ 4096 * Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ := by
            have hc : (0 : ℝ) ≤ 4096 * Bhi ^ 2 :=
              mul_nonneg (by norm_num) (sq_nonneg Bhi)
            exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
              (sq_nonneg _) hc
        _ ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
            have h1 : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_nonneg (sq_nonneg Blo) hHk6
            nlinarith [h1, hHk2, sq_nonneg Bhi]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hMnn : 0 ≤ 4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 7)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (7 * (4096 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
