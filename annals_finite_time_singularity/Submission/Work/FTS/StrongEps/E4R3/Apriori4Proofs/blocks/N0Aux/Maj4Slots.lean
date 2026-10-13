/-
# `N0Aux.Maj4` — the radial majorant for the `ℋ⁴`-integrand

This is the level-`4` companion of `N0Aux.Maj6Split`: for a radial `C⁶` factor `X` with
`|D_z^j X| ≤ B` for `j ≤ 4` and a datum `f` of class `C^∞` on the open quadrant,

  `HkSq α 4 (X · f) ≤ C · B² · HkSq α 4 f`

with `C` universal.  The proof is the level-`4` part of the argument of
`H6Pair6Aux.radialMaj6`: Leibniz (`leibniz_radial_mul`), the single-slot bounds
`sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed` at level `4`, binomial bounds and
Cauchy–Schwarz.
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

/-- `b.choose k ≤ 2^b ≤ 16` for `b ≤ 4`, hence `((b.choose k : ℝ))² ≤ 256`. -/
private theorem choose_sq_le_256 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 4) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 16 := by
    have h : b.choose k ≤ 16 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

theorem HkIntegrand_zero4 (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The universal constant of the level-`4` majorant. -/
def Maj4C : ℝ := 1000000

theorem Maj4C_pos : 0 < Maj4C := by norm_num [Maj4C]

/-- A single pure `D_z`-slot of the `ℋ⁴`-integrand of the radial product `X · f`. -/
theorem zslot4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
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
      ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
      _ ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hc : (0 : ℝ) ≤ 256 * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 5)
  have hMnn : 0 ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 5)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 5 * (5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁴`-integrand of the radial product `X · f`. -/
theorem mslot4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hj4 : j ≤ 4 := by omega
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i (by omega) z θ hz hθ0 hθ1
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
      ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 j b hbj hj4
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hc : (0 : ℝ) ≤ 256 * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 5)
  have hMnn : 0 ≤ 256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 5)) hMnn
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 5 * (5 * (256 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
