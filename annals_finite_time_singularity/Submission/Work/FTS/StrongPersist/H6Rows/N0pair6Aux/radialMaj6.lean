import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

noncomputable section

open scoped Real Topology
open Set Filter

set_option maxHeartbeats 1600000

/-!
## Multiplication by a `C^6` radial factor with bounded `D_z`-iterates costs a constant

The `ℋ⁶`-integrand of the product `(z,θ) ↦ X z · f z θ` (with `X` radial, `C⁶` on `(0,∞)`,
all of whose `D_z`-iterates up to order `6` are bounded by `B`) is pointwise dominated by a
multiple of the `ℋ⁶`-integrand of `f`, the constant depending only on `B` (not on `α`, `z`, `θ`).

The proof: the Leibniz rule `leibniz_radial_mul` expands `D_z^bD_θ^a (X·f)` as
`Σ_k C(b,k) (D_z^k X)(D_z^{b-k}D_θ^a f)` (all angular derivatives fall on `f`, since `X` is
radial); Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) together with the binomial bound
`b.choose k ≤ 2^b ≤ 64` (for `b ≤ 6`) gives, for each slot, the bound
`4096 · B² · HkIntegrand α 6 f`; summing over the at most `7` resp. `7 × 7` slots yields the
constant `2·10⁷·B² + 1`.
-/

/-- At `z = 0` the weight `w` vanishes (`w 0 = (1+0)²/0² = 1/0 = 0`, Lean's totalised
division), so every term of the weighted integrand vanishes there. -/
private theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- `b.choose k ≤ 2^b ≤ 64` for `b ≤ 6`, hence `((b.choose k : ℝ))² ≤ 4096`. -/
private theorem choose_sq_le_4096 (b k : ℕ) (_hk : k ≤ b) (hb : b ≤ 6) :
    ((b.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
  have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
  have h3 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
    have h : b.choose k ≤ 64 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (b.choose k)]

/-- A single pure `D_z`-slot of the `ℋ⁶`-integrand of the radial product `X · f`. -/
private theorem zslot6 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hlei :=
    Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0 hi z θ hz hθ0 hθ1
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
      ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 :=
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (i + 1),
            (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)) hHk
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i + 1 ≤ 7)) hc
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁶`-integrand of the radial product `X · f`. -/
private theorem mslot6 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
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
      ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 j b hbj hj6
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B ^ 2 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b X z), hB]
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 :=
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
              * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ _b ∈ Finset.range (j + 1),
            (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
          have hc : (0 : ℝ) ≤ 4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) (sq_nonneg B)) hHk
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : j + 1 ≤ 7)) hc
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (7 * (4096 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by ring

/-- **Multiplication by a bounded radial `C^6` factor is bounded on the `ℋ⁶`-integrand.** -/
theorem radialMaj6 (α B : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hbnd : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j X z| ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
        ≤ K * Work.Spaces.HkIntegrand α 6 f z θ := by
  refine ⟨20000000 * B ^ 2 + 1, by nlinarith [sq_nonneg B], ?_⟩
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, HkIntegrand_zero, HkIntegrand_zero, mul_zero]
  · have hHk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.Spaces.HkIntegrand_nonneg α 6 f z θ
    have hR : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b X z| ≤ B :=
      fun b hb => hbnd b hb z hzpos
    conv_lhs => rw [Work.Spaces.HkIntegrand]
    have hA : (∑ i ∈ Finset.range (6 + 1), (Work.Spaces.DzIter i
          (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 7 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
      calc (∑ i ∈ Finset.range (6 + 1), (Work.Spaces.DzIter i
            (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (6 + 1),
              (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
            Finset.sum_le_sum fun i hi =>
              zslot6 hB hX hf hzpos hθ.1 hθ.2 hR i
                (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 7 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hB' : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 49 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
      calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
              (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 6
            · rw [if_pos hc]
              exact mslot6 hB hX hf hzpos hθ.1 hθ.2 hR i j hc.1 hc.2
            · rw [if_neg hc]
              exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 200704) (sq_nonneg B)) hHk
        _ = 49 * (200704 * B ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    linarith [hA, hB', hHk, mul_nonneg (sq_nonneg B) hHk]

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
