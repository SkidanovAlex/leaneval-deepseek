import Mathlib
import Submission.Work.BourgainPlan.Maximal.subtwo_of_dyadic_z
import Submission.Work.BourgainPlan.Maximal.deg_le_one
import Submission.Commons.Analysis.HardyLittlewood.forward_maximal_z
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_count_residue

namespace Work.BourgainPlan.Maximal

open Finset MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

/-- The `enorm` of a complex number is the `ofReal` of its norm. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm

/-- The `enorm` of a real number is the `ofReal` of its norm. -/
lemma enorm_real_eq_ofReal (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal ‖r‖ := by
  rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]

/-!
# The dyadic `ℤ`-form of the maximal inequality for polynomials of degree `≤ 1`

`Work.BourgainPlan.Maximal.DyadicZStatement P p` is the shape in which the circle method
delivers its estimates: the dyadic polynomial averages
`T_k g (m) = (2^k)⁻¹ ∑_{i < 2^k} g (m + P i)` on `ℤ`, for `ℂ`-valued finitely supported `g`,
satisfy the `ℓᵖ(ℤ)` maximal inequality.

For a polynomial `P = c₁ X + c₀` nonnegative on `ℕ` the dyadic averages are the dyadic members of
the arithmetic-progression averages of step `c₁` and offset `c₀`, so the statement is a consequence
of the `ℓᵖ` maximal inequality for arithmetic-progression averages on `ℤ`.  The latter is obtained
from the one-sided forward discrete maximal inequality on `ℤ`
(`Commons.Analysis.HardyLittlewood.forward_maximal_z`) by splitting `ℤ` into the residue classes
modulo the step (`Work.BourgainPlan.IonescuWainger.lintegral_count_residue`).
-/

/-- **The one-sided forward discrete maximal inequality on `ℤ`, `ℂ`-valued functions.**
For `1 < p` there is `C` with
`∫⁻_ℤ (sup_N ‖N⁻¹ ∑_{j<N} g(x+j)‖)^p ≤ C^p ∫⁻_ℤ ‖g‖^p`
for every finitely supported `g : ℤ → ℂ`.  The modulus `‖g‖ : ℤ → ℝ` is a nonnegative real
function, so `Commons.Analysis.HardyLittlewood.forward_maximal_z` (proved there for real-valued
functions) applies. -/
theorem forward_z_complex {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℤ → ℂ,
      (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p
          ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.HardyLittlewood.forward_maximal_z hp
  refine ⟨C, hCpos, fun g hg => ?_⟩
  obtain ⟨s, hs⟩ := hg
  have hh : ∃ s' : Finset ℤ, ∀ n, n ∉ s' → (fun x : ℤ => ‖g x‖) n = 0 :=
    ⟨s, fun n hn => by simpa using hs n hn⟩
  have hbound := hC (fun x : ℤ => ‖g x‖) hh
  have hpt : ∀ x : ℤ, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ)
      ≤ (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ₑ) := by
    intro x
    apply iSup_le; intro N
    have hle : ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖
        ≤ ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ := by
      have hN : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
      calc ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖
          = ((N : ℝ))⁻¹ * ‖∑ j ∈ Finset.range N, g (x + j)‖ := by
            rw [norm_mul, Complex.norm_real ((N : ℝ)⁻¹), Real.norm_of_nonneg hN]
        _ ≤ ((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_sum_le (Finset.range N) (fun j => g (x + j))) hN
        _ = ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ := by
            rw [norm_mul, Real.norm_of_nonneg hN,
              Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))]
    have hgoal : ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ
        ≤ ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ₑ := by
      rw [enorm_complex_eq_ofReal, enorm_real_eq_ofReal]
      exact ENNReal.ofReal_le_ofReal hle
    exact le_trans hgoal (le_iSup (fun N : ℕ =>
      ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ₑ) N)
  have h1 : ∫⁻ x : ℤ, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p
        ∂Measure.count
      ≤ ∫⁻ x : ℤ, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, ‖g (x + j)‖‖ₑ) ^ p
        ∂Measure.count :=
    lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) (le_of_lt (lt_trans zero_lt_one hp)))
  have hnorm : ∀ x : ℤ, ‖(fun x : ℤ => ‖g x‖) x‖ₑ = ‖g x‖ₑ := by
    intro x
    rw [enorm_real_eq_ofReal, Real.norm_of_nonneg (norm_nonneg _)]
    exact ofReal_norm (g x)
  refine le_trans h1 ?_
  refine le_trans hbound ?_
  refine le_of_eq ?_
  congr 1
  refine lintegral_congr (fun x => ?_)
  rw [hnorm x]

/-- **The `ℓᵖ` maximal inequality for arithmetic-progression averages on `ℤ`.**  For `1 < p`,
`a ≥ 1`, `b : ℕ` there is `C` with
`∫⁻_ℤ (sup_N ‖N⁻¹ ∑_{i<N} g(m + a i + b)‖)^p ≤ C^p ∫⁻_ℤ ‖g‖^p`
for every finitely supported `g : ℤ → ℂ`.

Route: shifting `m ↦ m + b` (an injection of `ℤ`), the `a` residue classes of `m` modulo `a`
decompose `ℤ` into the arithmetic progressions `r + a ℤ`, on each of which the progression
average is a forward window of the subsequence `m ↦ g (a m + r)`; the residue decomposition is
`lintegral_count_residue` and the forward maximal inequality is `forward_z_complex`. -/
theorem ap_maximal_z {p : ℝ} (hp : 1 < p) (a : ℕ) (ha : 1 ≤ a) (b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ) + (b : ℤ))‖ₑ) ^ p
          ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := forward_z_complex hp
  refine ⟨C, hCpos, fun g hg => ?_⟩
  obtain ⟨s, hs⟩ := hg
  have haZ : (a : ℤ) ≠ 0 := by
    have ha0 : a ≠ 0 := by omega
    exact_mod_cast ha0
  have hsub : ∀ r : ℤ, (∃ t : Finset ℤ, ∀ m, m ∉ t → g ((a : ℤ) * m + r) = 0) := by
    intro r
    refine ⟨s.image (fun z : ℤ => (z - r) / (a : ℤ)), fun m hm => ?_⟩
    exact hs _ (fun hmem => hm (Finset.mem_image.mpr ⟨(a : ℤ) * m + r, hmem, by
      rw [add_sub_cancel_right]; exact Int.mul_ediv_cancel_left m haZ⟩))
  have hclass : ∀ r : ℤ, ∑' N : ℤ,
        (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
          g ((a : ℤ) * (N + (i : ℤ)) + r)‖ₑ) ^ p
      ≤ ENNReal.ofReal (C ^ p) * ∑' N : ℤ, ‖g ((a : ℤ) * N + r)‖ₑ ^ p := by
    intro r
    have h := hC (fun m : ℤ => g ((a : ℤ) * m + r)) (hsub r)
    rwa [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count] at h
  -- the progression average at `a*N + r` is the forward window at `N` of the subsequence
  have hpt : ∀ (N r : ℤ), (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
        g ((a : ℤ) * N + r + (a : ℤ) * (i : ℤ))‖ₑ) ^ p
      = (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
        g ((a : ℤ) * (N + (i : ℤ)) + r)‖ₑ) ^ p := by
    intro N r
    have hsum : ∀ K : ℕ, (∑ i ∈ Finset.range K,
          g ((a : ℤ) * N + r + (a : ℤ) * (i : ℤ)))
        = (∑ i ∈ Finset.range K, g ((a : ℤ) * (N + (i : ℤ)) + r)) := by
      intro K
      apply Finset.sum_congr rfl; intro i _
      congr 1
      ring
    simp only [hsum]
  -- shifting by `b`
  have hshift : ∑' m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ) + (b : ℤ))‖ₑ) ^ p
      ≤ ∑' m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p := by
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun m : ℤ => m + (b : ℤ)) (fun x _ hxy => add_right_cancel hxy)
      (fun m : ℤ => (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p))
    apply tsum_congr; intro m
    have hsum : ∀ N : ℕ, (∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ) + (b : ℤ)))
        = (∑ i ∈ Finset.range N, g ((m + (b : ℤ)) + (a : ℤ) * (i : ℤ))) := by
      intro N
      apply Finset.sum_congr rfl; intro i _
      congr 1; ring
    simp only [hsum]
  -- the residue decomposition of the progression sum
  have hres : ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p ∂Measure.count
      = ∑ r ∈ Finset.range a, ∑' N : ℤ,
          (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
            g ((a : ℤ) * (N + (i : ℤ)) + (r : ℤ))‖ₑ) ^ p := by
    rw [Work.BourgainPlan.IonescuWainger.lintegral_count_residue ha (fun m : ℤ =>
      (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p)]
    have hconv : ∀ r : ℕ, (∫⁻ N : ℤ, (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
          g (((a : ℤ) * N + (r : ℤ)) + (a : ℤ) * (i : ℤ))‖ₑ) ^ p ∂Measure.count)
        = ∑' N : ℤ, (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
          g (((a : ℤ) * N + (r : ℤ)) + (a : ℤ) * (i : ℤ))‖ₑ) ^ p :=
      fun r => MeasureTheory.lintegral_count _
    simp only [hconv]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    apply tsum_congr; intro N
    rw [hpt N (r : ℤ)]
  -- the residue decomposition of the `ℓᵖ` norm
  have hR : ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count
      = ∑ r ∈ Finset.range a, ∑' N : ℤ, ‖g ((a : ℤ) * N + (r : ℤ))‖ₑ ^ p := by
    rw [Work.BourgainPlan.IonescuWainger.lintegral_count_residue ha (fun m : ℤ => ‖g m‖ₑ ^ p)]
    have hconv : ∀ r : ℕ, (∫⁻ N : ℤ, ‖g ((a : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂Measure.count)
        = ∑' N : ℤ, ‖g ((a : ℤ) * N + (r : ℤ))‖ₑ ^ p :=
      fun r => MeasureTheory.lintegral_count _
    simp only [hconv]
  calc ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ) + (b : ℤ))‖ₑ) ^ p
          ∂Measure.count
      = ∑' m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ) + (b : ℤ))‖ₑ) ^ p :=
        MeasureTheory.lintegral_count _
    _ ≤ ∑' m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p := hshift
    _ = ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ *
          ∑ i ∈ Finset.range N, g (m + (a : ℤ) * (i : ℤ))‖ₑ) ^ p ∂Measure.count :=
        (MeasureTheory.lintegral_count _).symm
    _ = ∑ r ∈ Finset.range a, ∑' N : ℤ,
          (⨆ K : ℕ, ‖(K : ℝ)⁻¹ * ∑ i ∈ Finset.range K,
            g ((a : ℤ) * (N + (i : ℤ)) + (r : ℤ))‖ₑ) ^ p := hres
    _ ≤ ∑ r ∈ Finset.range a, ENNReal.ofReal (C ^ p) *
          ∑' N : ℤ, ‖g ((a : ℤ) * N + (r : ℤ))‖ₑ ^ p :=
        Finset.sum_le_sum (fun r _ => hclass (r : ℤ))
    _ = ENNReal.ofReal (C ^ p) * ∑ r ∈ Finset.range a,
          ∑' N : ℤ, ‖g ((a : ℤ) * N + (r : ℤ))‖ₑ ^ p := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by rw [hR]

/-- **The dyadic `ℤ`-form for polynomials of degree `≤ 1`** (for all `1 < p < 2`; in fact for all
`1 < p`).  Writing `P = c₁ X + c₀` with `0 ≤ c₁, c₀`, the dyadic averages are the dyadic members of
the arithmetic-progression averages of step `c₁` and offset `c₀`; when `c₁ ≥ 1` the maximal
inequality `ap_maximal_z` bounds their `sup` over all `N` (hence over the dyadic `N`), and when
`c₁ = 0` the average is the single translate `g (· + c₀)`, whose `ℓᵖ` norm is `‖g‖_{ℓᵖ}` by
translation invariance. -/
theorem dyadic_z_deg_le_one (P : Polynomial ℤ)
    (hP : ∀ n : ℕ, 0 ≤ P.eval (n : ℤ)) (hdeg : P.natDegree ≤ 1)
    (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Work.BourgainPlan.Maximal.DyadicZStatement P p := by
  obtain ⟨c1, c0, hPc⟩ : ∃ c1 c0 : ℤ, P = Polynomial.C c1 * Polynomial.X + Polynomial.C c0 :=
    ⟨P.coeff 1, P.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg⟩
  have hc0 : 0 ≤ c0 := by
    have h := hP 0
    rw [hPc] at h
    simpa using h
  have hc1 : 0 ≤ c1 := by
    by_contra hcon
    have hlt : c1 ≤ -1 := by omega
    have h := hP (c0.natAbs + 1)
    rw [hPc] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
    have hmpos : (0 : ℤ) ≤ (((c0.natAbs + 1 : ℕ)) : ℤ) := by positivity
    have h1 : c1 * (((c0.natAbs + 1 : ℕ)) : ℤ) ≤ -((((c0.natAbs + 1 : ℕ)) : ℤ)) := by
      have := mul_le_mul_of_nonneg_right hlt hmpos
      simpa using this
    have h2 : c0 ≤ (c0.natAbs : ℤ) := Int.le_natAbs
    have hmcast : (((c0.natAbs + 1 : ℕ)) : ℤ) = (c0.natAbs : ℤ) + 1 := by push_cast; ring
    linarith
  have heval : ∀ i : ℤ, P.eval i = c1 * i + c0 := by
    intro i; rw [hPc]; simp
  rcases Nat.eq_zero_or_pos c1.toNat with hzero | hpos
  · -- constant polynomial
    have hc1z : c1 = 0 := by
      have h := Int.toNat_eq_zero.mp hzero
      omega
    have hval : ∀ i : ℕ, P.eval (i : ℤ) = c0 := by
      intro i; rw [heval]; rw [hc1z]; ring
    refine ⟨1, zero_le_one, fun g _ => ?_⟩
    have hterm : ∀ (m : ℤ) (k : ℕ), ((2 : ℝ) ^ k)⁻¹ *
        ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ)) = g (m + c0) := by
      intro m k
      simp only [hval]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      have hnat : ((2 ^ k : ℕ) : ℂ) = (((2 : ℝ) ^ k : ℝ) : ℂ) := by
        rw [Nat.cast_pow, Complex.ofReal_pow]
        congr 1
      have hcast : ((2 : ℝ) ^ k)⁻¹ * ((2 ^ k : ℕ) : ℂ) = 1 := by
        rw [hnat, ← Complex.ofReal_mul, inv_mul_cancel₀ h2k, Complex.ofReal_one]
      rw [← mul_assoc, hcast, one_mul]
    have hsup : ∀ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
          ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) = ‖g (m + c0)‖ₑ := by
      intro m
      refine le_antisymm (iSup_le (fun k => by rw [hterm m k])) ?_
      have h0 := le_iSup (fun k : ℕ => ‖((2 : ℝ) ^ k)⁻¹ *
          ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) 0
      rwa [hterm m 0] at h0
    have heq1 : (∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
            ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) ^ p ∂Measure.count)
        = ∫⁻ m : ℤ, ‖g (m + c0)‖ₑ ^ p ∂Measure.count :=
      MeasureTheory.lintegral_congr (fun m => by rw [hsup m])
    have heq2 : (∫⁻ m : ℤ, ‖g (m + c0)‖ₑ ^ p ∂Measure.count)
        = ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
      rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
      exact Equiv.tsum_eq (Equiv.addRight c0) (fun m : ℤ => ‖g m‖ₑ ^ p)
    rw [heq1, heq2, Real.one_rpow, ENNReal.ofReal_one, one_mul]
  · -- nondegenerate slope
    have ha1 : 1 ≤ c1.toNat := hpos
    have hc1cast : ((c1.toNat : ℕ) : ℤ) = c1 := Int.toNat_of_nonneg hc1
    have hc0cast : ((c0.toNat : ℕ) : ℤ) = c0 := Int.toNat_of_nonneg hc0
    obtain ⟨C, hCpos, hC⟩ := ap_maximal_z hp c1.toNat ha1 c0.toNat
    refine ⟨C, hCpos.le, fun g hg => ?_⟩
    have hevalnat : ∀ i : ℕ, P.eval (i : ℤ) = (((c1.toNat * i + c0.toNat : ℕ)) : ℤ) := by
      intro i
      rw [heval]
      have hthis : c1 * (i : ℤ) + c0
          = (((c1.toNat : ℕ) : ℤ) * (i : ℤ) + ((c0.toNat : ℕ) : ℤ)) := by
        rw [hc1cast, hc0cast]
      rw [hthis]
      push_cast
      ring
    have hpt : ∀ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
          ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ)
        ≤ (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
            g (m + (c1.toNat : ℤ) * (i : ℤ) + (c0.toNat : ℤ))‖ₑ) := by
      intro m
      apply iSup_le; intro k
      have hsum : (∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ)))
          = (∑ i ∈ Finset.range (2 ^ k),
              g (m + (c1.toNat : ℤ) * (i : ℤ) + (c0.toNat : ℤ))) := by
        apply Finset.sum_congr rfl; intro i _
        congr 1
        rw [hevalnat i]
        push_cast
        ring
      rw [hsum]
      have hpow : ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) := by
        rw [Nat.cast_pow]
        congr 1
      rw [hpow]
      exact le_iSup (fun N : ℕ => ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
        g (m + (c1.toNat : ℤ) * (i : ℤ) + (c0.toNat : ℤ))‖ₑ) (2 ^ k)
    calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
            ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) ^ p ∂Measure.count
        ≤ ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
            g (m + (c1.toNat : ℤ) * (i : ℤ) + (c0.toNat : ℤ))‖ₑ) ^ p
            ∂Measure.count :=
          MeasureTheory.lintegral_mono
            (fun m => ENNReal.rpow_le_rpow (hpt m) (le_of_lt (by linarith)))
      _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := hC g hg

end Work.BourgainPlan.Maximal
