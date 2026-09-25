
import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.minor_arc_decay_pre
import Submission.Work.BourgainPlan.Maximal.poly_kernel_minor_arc
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

/-!
# Minor-arc decay of the polynomial Weyl kernel, with a free exponent `δ`

`poly_kernel_minor_arc` proves the minor-arc decay of the Weyl kernel of an integer polynomial
`P` of degree `d ≥ 2` for the single exponent `δ = 1/4` (the arcs of denominator `q ≤ N^{1/4}`
are removed and the kernel decays like a fixed negative power of `N`).

Many of the "dressing"/budget arguments of the `1 < p < 2` range need the *same* statement for an
arbitrary exponent `δ ∈ (0, 1/4]`, with the quantitative shape

`‖polyWeylKernel P N θ‖ ≤ C_δ · N^{−ν δ}`,  `ν = 2^{−(d+2)}` a constant depending only on `d`,

whenever `c·θ` is at distance `> N^{−(d−δ)}` from every arc centre `a/q + l` with
`1 ≤ q ≤ N^δ`, `a < q`, `gcd a q = 1`, `l ∈ [−1, c]`.  This is the content of
`polyWeylKernel_minorArcDecay` below.

The proof has three pieces.

* `weyl_minor_arc_decay_exp` — the quantitative form of the classical minor-arc estimate
  `weyl_minor_arc_decay (k) (hk) (δ)`: for a real polynomial `f` of degree `k ≥ 2` whose leading
  coefficient avoids `a/q` with `q ≤ N^δ` by more than `N^{−k+δ}`, one has
  `‖N⁻¹ ∑_{x<N} e(f(x))‖ ≤ C · N^{−(δ 2^{−(k+1)})}`.  Unlike the existential form in the
  commons, the *exponent* `δ 2^{−(k+1)}` is produced explicitly, which is what allows a single
  `ν` to serve all `δ ∈ (0,1/4]` at once.  The proof is Dirichlet's approximation theorem plus
  Weyl's inequality, exactly as in `weyl_minor_arc_decay`, with the final bookkeeping changed
  from `N^{−ν}` to `N^{−ν/2}`.

* `poly_minor_arc_reduce_gen` — the reduction of the `(a/q + l)`-form of the circle-method
  hypothesis (only coprime `a < q` are excluded) to the all-`a` form required by the Weyl
  estimate, for a general `δ`.  This is `poly_minor_arc_reduce` with `1/4 ↦ δ`.

* `polyWeylKernel_eq_eval_toRealPoly` — the identification of the Weyl kernel of `P` with the
  normalized Weyl sum of the real polynomial `θ • P`, already used in `minor_arc_decay_pre`.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

set_option autoImplicit false

/-- **Quantitative minor-arc decay for the Weyl sum.**  Let `k ≥ 2`, `0 < δ ≤ 1/4` and let
`f : ℝ[X]` have `natDegree = k`.  If the leading coefficient of `f` is at distance
`> N^{−k+δ}` from every rational `a/q` with `1 ≤ q ≤ N^δ`, then

`‖N⁻¹ ∑_{x<N} e(f(x))‖ ≤ C · N^{−(δ·2^{−(k+1)})}`

with `C` depending only on `k` and `δ`.  (Bourgain 1989, §5: Dirichlet + Weyl; the exponent
`δ 2^{−(k+1)}` is half of the `δ 2^{−k}` produced by the standard estimate, and is kept
deliberately small so that a single `ν = 2^{−(k+2)}` works for every `δ ≤ 1/4`.) -/
theorem weyl_minor_arc_decay_exp (k : ℕ) (hk : 2 ≤ k) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (f : Polynomial ℝ), f.natDegree = k → 2 ≤ N →
        (∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ →
          (N : ℝ) ^ (-(k : ℝ) + δ) < |f.leadingCoeff - (a : ℝ) / (q : ℝ)|) →
        ‖(N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ))‖
          ≤ C * (N : ℝ) ^ (-(δ * (2 : ℝ) ^ (-(k : ℝ) - 1))) := by
  set ν : ℝ := δ * (2 : ℝ) ^ (-(k : ℝ)) with hνdef
  have hνpos : 0 < ν := by
    rw [hνdef]; exact mul_pos hδ0 (Real.rpow_pos_of_pos (by norm_num) _)
  have hνhalf_pos : 0 < ν / 2 := by linarith
  obtain ⟨Cw, hCwpos, hCw⟩ :=
    Commons.Analysis.ExponentialSums.weyl_inequality k (by omega) (ε := ν / 2) hνhalf_pos (t := 1) (by norm_num)
  refine ⟨6 * Cw, by linarith, ?_⟩
  intro N f hf hN hminor
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkexp_pos : 0 < (k : ℝ) - δ := by linarith
  have hNrpow_pos : 0 < (N : ℝ) ^ ((k : ℝ) - δ) := Real.rpow_pos_of_pos hNpos _
  have hNrpow_ge1 : 1 ≤ (N : ℝ) ^ ((k : ℝ) - δ) :=
    Real.one_le_rpow hN1.le hkexp_pos.le
  -- Dirichlet parameter
  set M : ℕ := Nat.ceil ((N : ℝ) ^ ((k : ℝ) - δ)) + 1 with hMdef
  have hM_gt : (N : ℝ) ^ ((k : ℝ) - δ) < (M : ℝ) := by
    have h := Nat.le_ceil ((N : ℝ) ^ ((k : ℝ) - δ))
    rw [hMdef]; push_cast; linarith
  have hMpos : 0 < M := by rw [hMdef]; exact Nat.succ_pos _
  have hM_le : (M : ℝ) ≤ 3 * (N : ℝ) ^ ((k : ℝ) - δ) := by
    have h := Nat.ceil_lt_add_one (le_of_lt hNrpow_pos)
    rw [hMdef]; push_cast
    linarith [h, hNrpow_ge1]
  -- Dirichlet's theorem
  obtain ⟨r, hrbound, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (f.leadingCoeff) (n := M) hMpos
  have hrc : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
  have hdenpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hden1 : (1 : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  -- denominator exceeds N^δ
  have hy_gt : (N : ℝ) ^ δ < (r.den : ℝ) := by
    by_contra hle
    rw [not_lt] at hle
    have hmin := hminor (r.den : ℤ) (r.num) (by exact_mod_cast r.pos) (by exact_mod_cast hle)
    have hmin' : (N : ℝ) ^ (-(k : ℝ) + δ) < |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)| := by
      simpa using hmin
    have hb1 : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)|
        ≤ 1 / (((M : ℝ) + 1) * (r.den : ℝ)) := by
      have h := hrbound
      rw [hrc] at h
      simpa using h
    have hbig : (N : ℝ) ^ ((k : ℝ) - δ) < ((M : ℝ) + 1) * (r.den : ℝ) := by
      have h1 : (N : ℝ) ^ ((k : ℝ) - δ) < (M : ℝ) + 1 := by linarith
      nlinarith [h1, hden1, hMpos]
    have hstep : 1 / (((M : ℝ) + 1) * (r.den : ℝ)) < (N : ℝ) ^ (-(k : ℝ) + δ) := by
      have hNexp : (N : ℝ) ^ (-(k : ℝ) + δ) = 1 / ((N : ℝ) ^ ((k : ℝ) - δ)) := by
        rw [show (-(k : ℝ) + δ) = -((k : ℝ) - δ) by ring, Real.rpow_neg hNpos.le, one_div]
      rw [hNexp]
      exact one_div_lt_one_div_of_lt hNrpow_pos hbig
    linarith [hmin', lt_of_le_of_lt hb1 hstep]
  -- coprimality
  have hgcd : Int.gcd r.num (r.den : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.Coprime.gcd_eq_one (by simpa using r.reduced)
  -- Weyl applies
  have hb : |f.leadingCoeff - ((r.num : ℤ) : ℝ) / ((r.den : ℤ) : ℝ)| ≤ 1 / (((r.den : ℤ) : ℝ)) ^ 2 := by
    have hb1 : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)|
        ≤ 1 / (((M : ℝ) + 1) * (r.den : ℝ)) := by
      have h := hrbound
      rw [hrc] at h
      simpa using h
    have hdenM : (r.den : ℝ) ≤ (M : ℝ) + 1 := by
      have h : (r.den : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrden
      linarith
    have hle : 1 / (((M : ℝ) + 1) * (r.den : ℝ)) ≤ 1 / (r.den : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hdenM, hdenpos]
    have hmain : |f.leadingCoeff - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2 :=
      le_trans hb1 hle
    simpa using hmain
  have hWeyl := hCw 0 N r.num (r.den : ℤ) f (by exact_mod_cast r.pos) hgcd hf hb
  -- bracket
  set Br : ℝ := 1 / (r.den : ℝ) + 1 / (N : ℝ) + 1 / ((N : ℝ) ^ (k - 1)) + (r.den : ℝ) / (N : ℝ) ^ k with hBr
  have hbreq : (1 / ((r.den : ℤ) : ℝ) + 1 / ((N : ℝ)) + 1 / ((N : ℝ) ^ (k - 1)) + ((r.den : ℤ) : ℝ) / (N : ℝ) ^ k) = Br := by
    rw [hBr]; push_cast; ring
  have hA : 1 / (r.den : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : 1 / (r.den : ℝ) < (N : ℝ) ^ (-δ) := by
      have hNexp : (N : ℝ) ^ (-δ) = 1 / ((N : ℝ) ^ δ) := by
        rw [Real.rpow_neg hNpos.le, one_div]
      rw [hNexp]
      exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hNpos δ) hy_gt
    exact h1.le
  have hB : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
    simpa [Real.rpow_neg_one, one_div] using h1
  have hC : 1 / ((N : ℝ) ^ (k - 1)) ≤ (N : ℝ) ^ (-δ) := by
    have hexp : -(((k - 1 : ℕ) : ℝ)) ≤ -δ := by
      have : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
        have : 1 ≤ k - 1 := by omega
        exact_mod_cast this
      linarith
    have h1 : (N : ℝ) ^ (-(((k - 1 : ℕ) : ℝ))) ≤ (N : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le hexp
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast] at h1
    simpa using h1
  have hD : (r.den : ℝ) / (N : ℝ) ^ k ≤ 3 * (N : ℝ) ^ (-δ) := by
    have hyden : (r.den : ℝ) ≤ 3 * (N : ℝ) ^ ((k : ℝ) - δ) :=
      le_trans (by exact_mod_cast hrden) hM_le
    calc (r.den : ℝ) / (N : ℝ) ^ k
        ≤ (3 * (N : ℝ) ^ ((k : ℝ) - δ)) / (N : ℝ) ^ k :=
          div_le_div_of_nonneg_right hyden (by positivity)
      _ = 3 * (N : ℝ) ^ (-δ) := by
          rw [mul_div_assoc, ← Real.rpow_natCast (N : ℝ) k,
            ← Real.rpow_sub hNpos ((k : ℝ) - δ) (k : ℝ)]
          congr 1
          ring
  have hbr_le : Br ≤ 6 * (N : ℝ) ^ (-δ) := by
    rw [hBr]; linarith [hA, hB, hC, hD]
  have hbr_nn : 0 ≤ Br := by rw [hBr]; positivity
  -- combine
  have hWeyl' : ‖∑ x ∈ Finset.range N,
      Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I)‖
      ≤ Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) := by
    rw [hbreq] at hWeyl
    simpa using hWeyl
  have hsum_eq : (∑ x ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ)))
      = ∑ x ∈ Finset.range N,
        Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    push_cast
    ring
  have hpow_le : Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ 6 * (N : ℝ) ^ (-(2 * ν)) := by
    have h2pos : 0 ≤ (2 : ℝ) ^ (1 - (k : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h61 : (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ 6 := by
      have hle1 : (2 : ℝ) ^ (1 - (k : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      calc (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) ≤ (6 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hle1
        _ = 6 := Real.rpow_one 6
    calc Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))
        ≤ (6 * (N : ℝ) ^ (-δ)) ^ ((2:ℝ) ^ (1 - (k : ℝ))) := Real.rpow_le_rpow hbr_nn hbr_le h2pos
      _ = (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) * ((N : ℝ) ^ (-δ)) ^ ((2:ℝ) ^ (1 - (k : ℝ))) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _)
      _ = (6 : ℝ) ^ ((2:ℝ) ^ (1 - (k : ℝ))) * (N : ℝ) ^ (-δ * (2:ℝ) ^ (1 - (k : ℝ))) := by
            rw [← Real.rpow_mul hNpos.le]
      _ ≤ 6 * (N : ℝ) ^ (-δ * (2:ℝ) ^ (1 - (k : ℝ))) := by
            apply mul_le_mul_of_nonneg_right h61 (Real.rpow_nonneg hNpos.le _)
      _ = 6 * (N : ℝ) ^ (-(2 * ν)) := by
            have hexp : -δ * (2:ℝ) ^ (1 - (k : ℝ)) = -(2 * ν) := by
              rw [hνdef]
              have h2e : (2 : ℝ) ^ (1 - (k : ℝ)) = 2 * (2 : ℝ) ^ (-(k : ℝ)) := by
                rw [show (1 : ℝ) - (k : ℝ) = 1 + (-(k : ℝ)) by ring]
                rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
              rw [h2e]; ring
            rw [hexp]
  have hνhalf : ν / 2 = δ * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
    rw [hνdef]
    have h2 : (2 : ℝ) ^ (-(k : ℝ) - 1) = (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-1 : ℝ) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-(k : ℝ)) (-1))
    rw [h2, Real.rpow_neg_one]
    ring
  have hkey : (N : ℝ) ^ (1 + ν / 2) * (N : ℝ)⁻¹ = (N : ℝ) ^ (ν / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hkey2 : (N : ℝ) ^ (ν / 2) * (N : ℝ) ^ (-(2 * ν)) = (N : ℝ) ^ (ν / 2 - 2 * ν) := by
    rw [← Real.rpow_add hNpos]
    congr 1
  have hfin : (N : ℝ) ^ (ν / 2 - 2 * ν) ≤ (N : ℝ) ^ (-(ν / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  calc ‖(N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((Polynomial.eval (x : ℝ) f : ℝ)) : ℂ))‖
      = ‖∑ x ∈ Finset.range N,
        Complex.exp (↑(2 * Real.pi * Polynomial.eval ((0 : ℤ) + (x : ℝ)) f) * Complex.I)‖ * (N : ℝ)⁻¹ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast, hsum_eq, mul_comm]
    _ ≤ (Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hWeyl' (by positivity)
    _ = Cw * (N : ℝ) ^ (ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) := by
          rw [show (Cw * (N : ℝ) ^ (1 + ν / 2) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ)))) * (N : ℝ)⁻¹
                = Cw * ((N : ℝ) ^ (1 + ν / 2) * (N : ℝ)⁻¹) * Br ^ ((2:ℝ) ^ (1 - (k : ℝ))) by ring,
            hkey]
    _ ≤ Cw * (N : ℝ) ^ (ν / 2) * (6 * (N : ℝ) ^ (-(2 * ν))) :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = 6 * Cw * (N : ℝ) ^ (ν / 2 - 2 * ν) := by
          rw [show Cw * (N : ℝ) ^ (ν / 2) * (6 * (N : ℝ) ^ (-(2 * ν)))
                = 6 * Cw * ((N : ℝ) ^ (ν / 2) * (N : ℝ) ^ (-(2 * ν))) by ring, hkey2]
    _ ≤ 6 * Cw * (N : ℝ) ^ (-(ν / 2)) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 6 * Cw * (N : ℝ) ^ (-(δ * (2 : ℝ) ^ (-(k : ℝ) - 1))) := by rw [hνhalf]

/-- **Reduction of the arc-form minor-arc hypothesis to the Weyl form** (general exponent `δ`).

`weyl_minor_arc_decay_exp` requires the leading coefficient `c·θ` to be far from *every* rational
`a/q` with `q ≤ N^δ`, while the circle-method hypothesis only excludes the arc centres
`a/q + l` with `1 ≤ q ≤ N^δ`, `0 ≤ a < q`, `gcd a q = 1` and `l ∈ [-1, c]`.  The reduction is the
standard one: write an arbitrary `a/q` (`a : ℤ`) as `m + r/q` with `0 ≤ r < q`, cancel the common
divisor of `r` and `q`, and appeal to the hypothesis; the integer part `m` lies in `[-1, c]`
exactly when the corresponding arc is one of the excluded ones, and otherwise the distance
`|cθ − a/q| ≥ 1` already exceeds the threshold `N^{−(d−δ)} < 1` (here `0 ≤ θ ≤ 1` confines
`cθ − r/q ∈ (−1, c]`). -/
lemma poly_minor_arc_reduce_gen (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    {N : ℕ} (hN : 3 ≤ N) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hnoarc : ∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ → a < q →
      Nat.gcd a q = 1 → l ∈ Finset.Icc (-1) P.leadingCoeff →
      (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) <
        |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|) :
    ∀ (q : ℕ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ →
      (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) <
        |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)| := by
  intro q a hq hqle
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : 0 < q := by omega
  have hqZne : ((q : ℤ)) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hqZpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hcR : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  -- Euclidean division of `a` by `q`
  set r : ℤ := a % (q : ℤ) with hr
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg a hqZne
  have hrlt : r < (q : ℤ) := hr ▸ Int.emod_lt_of_pos a hqZpos
  set m : ℤ := a / (q : ℤ) with hm
  have hdecZ : a = (q : ℤ) * m + r := by
    have h := Int.mul_ediv_add_emod a (q : ℤ)
    rw [← hm, ← hr] at h
    exact h.symm
  set rn : ℕ := r.toNat with hrn
  have hrcast : (rn : ℤ) = r := hrn ▸ Int.toNat_of_nonneg hr0
  have hrnlt : rn < q := by
    have h : ((rn : ℤ)) < (q : ℤ) := by rw [hrcast]; exact hrlt
    exact_mod_cast h
  -- cancel the common divisor of `rn` and `q`
  set D : ℕ := Nat.gcd rn q with hD
  have hDq : D ∣ q := hD ▸ Nat.gcd_dvd_right rn q
  have hDr : D ∣ rn := hD ▸ Nat.gcd_dvd_left rn q
  have hDpos : 0 < D := Nat.pos_of_dvd_of_pos hDq hqpos
  set q₁ : ℕ := q / D with hq1
  set r₁ : ℕ := rn / D with hr1
  have hq1D : q₁ * D = q := hq1 ▸ Nat.div_mul_cancel hDq
  have hr1D : r₁ * D = rn := hr1 ▸ Nat.div_mul_cancel hDr
  have hcop : Nat.gcd r₁ q₁ = 1 := by
    have h := Nat.coprime_div_gcd_div_gcd (m := rn) (n := q) (by rw [← hD]; exact hDpos)
    rw [hq1, hr1]
    exact Nat.coprime_iff_gcd_eq_one.mp h
  have hr1lt : r₁ < q₁ := by
    have h := Nat.div_lt_div_of_lt_of_dvd hDq hrnlt
    rw [hq1, hr1]; exact h
  have hq1le : q₁ ≤ q := hq1 ▸ Nat.div_le_self q D
  have hq1leN : (q₁ : ℝ) ≤ (N : ℝ) ^ δ := by
    have h1 : (q₁ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1le
    linarith
  have hfr : (r₁ : ℝ) / (q₁ : ℝ) = (rn : ℝ) / (q : ℝ) := by
    have h1 : (rn : ℝ) = (r₁ : ℝ) * (D : ℝ) := by rw [← hr1D]; push_cast; ring
    have h2 : (q : ℝ) = (q₁ : ℝ) * (D : ℝ) := by rw [← hq1D]; push_cast; ring
    rw [h1, h2]
    have hDne : (D : ℝ) ≠ 0 := by positivity
    field_simp
  have haq : (a : ℝ) / (q : ℝ) = (m : ℝ) + (r₁ : ℝ) / (q₁ : ℝ) := by
    have h1 : (a : ℝ) = (q : ℝ) * (m : ℝ) + (rn : ℝ) := by
      have hZ : a = (q : ℤ) * m + ((rn : ℤ)) := by rw [hrcast]; exact hdecZ
      exact_mod_cast hZ
    rw [h1, add_div, mul_div_cancel_left₀ _ (ne_of_gt hqRpos), hfr]
  have hq1pos : 1 ≤ q₁ := by
    rcases Nat.eq_zero_or_pos q₁ with h0 | hp
    · rw [h0, zero_mul] at hq1D; omega
    · exact hp
  have hq1Rpos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast (by omega : 0 < q₁)
  have habs : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)|
      = |(P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ)| := by
    rw [haq]; congr 1; ring
  by_cases hml : m ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff
  · -- the arc is one of the excluded ones: apply the hypothesis
    rw [habs]
    exact hnoarc q₁ r₁ m hq1pos hq1leN hr1lt hcop hml
  · -- otherwise `|cθ − a/q| ≥ 1 > N^{−(d−δ)}`
    have hml' : m < -1 ∨ P.leadingCoeff < m := by
      by_contra hcon
      rw [not_or] at hcon
      exact hml (Finset.mem_Icc.mpr
        ⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2⟩)
    have hsmall : (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) < 1 := by
      have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      have hexp : (0 : ℝ) < (P.natDegree : ℝ) - δ := by linarith
      have h1 : (1 : ℝ) < (N : ℝ) ^ ((P.natDegree : ℝ) - δ) := by
        have h2 := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
          (by exact_mod_cast (by omega : 1 < N) : (1 : ℝ) < (N : ℝ)) hexp
        rwa [Real.one_rpow] at h2
      rw [Real.rpow_neg hNr.le]
      exact inv_lt_one_of_one_lt₀ h1
    have hge1 : (1 : ℝ) ≤
        |(P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ)| := by
      have hr1q1lt : (r₁ : ℝ) / (q₁ : ℝ) < 1 := by
        rw [div_lt_one hq1Rpos]; exact_mod_cast hr1lt
      have hr1q1nn : (0 : ℝ) ≤ (r₁ : ℝ) / (q₁ : ℝ) := by positivity
      have hcθnn : (0 : ℝ) ≤ (P.leadingCoeff : ℝ) * θ := mul_nonneg hcR.le hθ0
      have hcθle : (P.leadingCoeff : ℝ) * θ ≤ (P.leadingCoeff : ℝ) := by nlinarith [hcR, hθ1]
      rcases hml' with hlt | hgt
      · have hm2 : (m : ℝ) ≤ -2 := by
          have h : m ≤ (-2 : ℤ) := by omega
          exact_mod_cast h
        have hβgt : (-1 : ℝ) < (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) := by linarith
        have hpos : (0 : ℝ) <
            (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ) := by linarith
        rw [abs_of_pos hpos]; linarith
      · have hmge : (P.leadingCoeff : ℝ) + 1 ≤ (m : ℝ) := by
          have h : P.leadingCoeff + 1 ≤ m := by omega
          exact_mod_cast h
        have hβle : (P.leadingCoeff : ℝ) * θ - (r₁ : ℝ) / (q₁ : ℝ) - (m : ℝ) ≤ -1 := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
    rw [habs]
    linarith

/-- The Weyl kernel of `P` is the normalized Weyl sum of the real polynomial `θ • P`. -/
lemma polyWeylKernel_eq_eval_toRealPoly (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    polyWeylKernel P N θ = (N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I *
        ((Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P) : ℝ) : ℂ)) := by
  unfold polyWeylKernel
  rw [show ((N : ℝ)⁻¹ : ℂ) = (N : ℂ)⁻¹ by push_cast; ring]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have he : Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P)
      = θ * ((P.eval (x : ℤ) : ℤ) : ℝ) := by
    rw [Polynomial.eval_C_mul, eval_toRealPoly_natCast]
  rw [he]

/-- **Minor-arc decay of the polynomial Weyl kernel, with a free exponent `δ ≤ 1/4`.**

For an integer polynomial `P` of degree `d ≥ 2` with `c = P.leadingCoeff > 0` there is a
constant `ν > 0` (namely `2^{−(d+2)}`) such that for every `δ ∈ (0, 1/4]` there is `C = C_δ > 0`
with: whenever `c·θ` is at distance `> N^{−(d−δ)}` from every arc centre `a/q + l`
(`1 ≤ q ≤ N^δ`, `0 ≤ a < q`, `gcd a q = 1`, `l ∈ [−1, c]`), the Weyl kernel obeys

`‖polyWeylKernel P N θ‖ ≤ C · N^{−ν δ}`. -/
theorem polyWeylKernel_minorArcDecay (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
        (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ → a < q →
          Nat.gcd a q = 1 → l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
          (N : ℝ) ^ (-((P.natDegree : ℝ) - δ))
            < |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|) →
        ‖Work.BourgainPlan.Maximal.polyWeylKernel P N θ‖ ≤ C * (N : ℝ) ^ (-(ν * δ)) := by
  refine ⟨(2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro δ hδ0 hδ1
  obtain ⟨C, hCpos, hmain⟩ := weyl_minor_arc_decay_exp P.natDegree hd δ hδ0 hδ1
  refine ⟨C, hCpos, ?_⟩
  intro N hN3 θ hθ0 hθ1 hnoarc
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hNδ1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1.le hδ0.le
  -- `θ ≠ 0`, since otherwise the arc `a/q + l = 0/1 + 0` would violate the hypothesis
  have hθne : θ ≠ 0 := by
    intro h0
    have h := hnoarc 1 0 0 le_rfl (by simpa using hNδ1) (by norm_num) (by decide)
      (by rw [Finset.mem_Icc]; omega)
    rw [h0] at h
    simp only [mul_zero, Int.cast_zero, zero_div, sub_zero, abs_zero] at h
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) := Real.rpow_pos_of_pos hNr _
    linarith
  have hfdeg : (Polynomial.C θ * toRealPoly P).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_C_mul hθne, natDegree_toRealPoly]
  have hlead : (Polynomial.C θ * toRealPoly P).leadingCoeff = θ * (P.leadingCoeff : ℝ) :=
    leadingCoeff_C_toRealPoly P θ hθne
  -- reduce the arc-form hypothesis to the all-`a` form used by the Weyl estimate
  have hred := poly_minor_arc_reduce_gen P hc hd hN3 hθ0 hθ1 hδ0 hδ1 hnoarc
  have hminor : ∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ δ →
      (N : ℝ) ^ (-(P.natDegree : ℝ) + δ)
        < |(Polynomial.C θ * toRealPoly P).leadingCoeff - (a : ℝ) / (q : ℝ)| := by
    intro q a hq hqle
    have hq0 : (0 : ℤ) ≤ q := by omega
    have hqnatZ : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
    have hqnat : (q.toNat : ℝ) = (q : ℝ) := by exact_mod_cast hqnatZ
    have hq1 : 1 ≤ q.toNat := by omega
    have hle' : (q.toNat : ℝ) ≤ (N : ℝ) ^ δ := by rw [hqnat]; exact hqle
    have h := hred q.toNat a hq1 hle'
    have hexp : -(P.natDegree : ℝ) + δ = -((P.natDegree : ℝ) - δ) := by ring
    have hcomm : |θ * (P.leadingCoeff : ℝ) - (a : ℝ) / (q.toNat : ℝ)|
        = |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q.toNat : ℝ)| := by
      congr 1; ring
    rw [hexp, hlead, ← hqnat, hcomm]
    exact h
  have hmain' := hmain N (Polynomial.C θ * toRealPoly P) hfdeg (by omega) hminor
  -- the two exponents `δ·2^{−(d+1)}` and `ν·δ = δ·2^{−(d+2)}`
  have hNu : (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hcmp : (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) * δ
      ≤ δ * (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 1) := by
    calc (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) * δ
        = δ * (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) := by ring
      _ ≤ δ * (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 1) := mul_le_mul_of_nonneg_left hNu hδ0.le
  have hpow_le : (N : ℝ) ^ (-(δ * (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 1)))
      ≤ (N : ℝ) ^ (-((2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) * δ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  calc ‖polyWeylKernel P N θ‖
      = ‖(N : ℂ)⁻¹ * ∑ x ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I *
            ((Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P) : ℝ) : ℂ))‖ := by
        rw [polyWeylKernel_eq_eval_toRealPoly P N θ]
    _ ≤ C * (N : ℝ) ^ (-(δ * (2 : ℝ) ^ (-((P.natDegree : ℝ)) - 1))) := hmain'
    _ ≤ C * (N : ℝ) ^ (-((2 : ℝ) ^ (-((P.natDegree : ℝ)) - 2) * δ)) :=
        mul_le_mul_of_nonneg_left hpow_le hCpos.le

end Work.BourgainPlan.Maximal
