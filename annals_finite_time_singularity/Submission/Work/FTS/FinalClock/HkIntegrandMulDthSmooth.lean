import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.Coercivity.CommutZ_mult
import Submission.Work.FTS.FinalClock.ZopIterLeibniz
import Submission.Work.FTS.FinalClock.PhiZopBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The comparison `HkIntegrand α 4 (3·D_θh/(1+z)) ≤ C·HkIntegrand α 5 h` for `h` locally `C⁵`

`Work.FTS.FinalClock.HkIntegrandMulDthSmooth` is the weighted Leibniz estimate behind the
`τ`-Lipschitz clause of the third `L₁₂`-functional in `Work.FTS.FinalClock.MuHolder`
(the `D_θ` in `3D_θg/(1+z)` costs one order in `ℋ`, so the comparison must use `ℋ⁵`).

The multiplier is `φ(z) = 3/(1+z)`, a `z`-only factor, and the two ingredients are

* `ZopIterLeibniz` — the iterated Leibniz rule for `Zop = z ∂_z` at finite order (the
  `C^∞`-version `Work.Spaces.DerivLike.iterate_mul` needs `C^∞`, and the version
  `Work.Spaces.DzIter_mul` needs analyticity in the `WithTop ℕ∞`-order of this Mathlib);
* the pointwise Cauchy–Schwarz layer `HkIntegrand_zmul_le_pointwise`, which turns the two
  Leibniz expansions into the stated bound, using the bounds `|Zop^b φ| ≤ 100` (`b ≤ 4`)
  of `PhiZopBound`.

The target needs no global smoothness: the hypothesis is only `ContDiffAt ℝ 5` at the point
`(z,θ)`, which is exactly the order needed (`D_θ^i h` with `i ≤ 5` must be differentiated
`j` more times in `z`, `i + j ≤ 5`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.FinalClock

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Plumbing: neighbourhoods and slices -/

/-- The `z`-slice of a function which is `C^k` on a product `V ×ˢ W` is `C^k` on `V`. -/
theorem contDiffOn_zslice {F : ℝ → ℝ → ℝ} {V W : Set ℝ} {θ : ℝ} {k : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry F) (V ×ˢ W)) (hθ : θ ∈ W) :
    ContDiffOn ℝ k (fun z' => F z' θ) V := by
  have hmap : ContDiffOn ℝ k (fun z' : ℝ => (z', θ)) V := by
    have h1 : ContDiff ℝ k (fun z' : ℝ => (z', θ)) := by fun_prop
    exact h1.contDiffOn
  have := ContDiffOn.comp h hmap (fun z' _ => ⟨by assumption, hθ⟩)
  simpa [Function.comp_def] using this

/-- **A product neighbourhood of smoothness.**  A function which is `C^n` at `(z,θ)` (with
`z > 0`, `0 < θ < π/2`) is `C^n` on a product `V ×ˢ W` of open sets with `z ∈ V ⊆ (0,∞)` and
`θ ∈ W ⊆ (0,π/2)`. -/
theorem exists_nbhd_prod_of_contDiffAt {h : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hcd : ContDiffAt ℝ n (Function.uncurry h) (z, θ)) :
    ∃ V W : Set ℝ, IsOpen V ∧ IsOpen W ∧ z ∈ V ∧ θ ∈ W ∧ V ⊆ Set.Ioi 0 ∧
      W ⊆ Set.Ioo 0 (Real.pi / 2) ∧ ContDiffOn ℝ n (Function.uncurry h) (V ×ˢ W) := by
  obtain ⟨s, hs, hsd⟩ := hcd.contDiffOn (m := (n : WithTop ℕ∞)) le_rfl (by
    intro hh; exact absurd hh (by
      have h1 : (n : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        change ((n : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)
      exact ne_of_lt h1))
  rw [nhds_prod_eq] at hs
  obtain ⟨V₀, hV₀, W₀, hW₀, hsub⟩ := Filter.mem_prod_iff.mp hs
  obtain ⟨V₁, hV₁sub, hV₁open, hz₁⟩ := mem_nhds_iff.mp hV₀
  obtain ⟨W₁, hW₁sub, hW₁open, hθ₁⟩ := mem_nhds_iff.mp hW₀
  refine ⟨V₁ ∩ Set.Ioi (0 : ℝ), W₁ ∩ Set.Ioo (0 : ℝ) (Real.pi / 2), hV₁open.inter isOpen_Ioi,
    hW₁open.inter isOpen_Ioo, ⟨hz₁, hz⟩, ⟨hθ₁, hθ0, hθ1⟩, ?_, ?_, ?_⟩
  · exact fun _ hx => hx.2
  · exact fun _ hx => hx.2
  · refine hsd.mono (fun p hp => hsub ⟨hV₁sub hp.1.1, hW₁sub hp.2.1⟩)

/-- The multiplier `φ(z) = 3/(1+z)` is `C^k` on `(-1,∞)`. -/
theorem contDiffOn_phiThree (k : ℕ) :
    ContDiffOn ℝ k (fun z : ℝ => 3 / (1 + z)) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ k (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by fun_prop
  have h3 : ContDiffOn ℝ k (fun _ : ℝ => (3 : ℝ)) (Set.Ioi (-1)) := contDiffOn_const
  exact h3.div hden (fun x hx => by
    have hx' : (-1 : ℝ) < x := hx
    intro hc; linarith)

/-- If both weights of the `H^k`-integrand vanish then the integrand is `0`. -/
theorem HkIntegrand_eq_zero_of_weights (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0)
    (hW : Work.Spaces.Wt α z θ = 0) : Work.Spaces.HkIntegrand α k F z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have h1 : ∀ i : ℕ,
      (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [hH, mul_zero]; norm_num
  have h2 : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro i j; split_ifs with hh
    · rw [hW, mul_zero]; norm_num
    · rfl
  rw [Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => h2 i j)), add_zero]

/-! ## The pointwise Cauchy–Schwarz layer -/

/-- `|i.choose b| ≤ 16` for `i ≤ 4` (in `ℝ`). -/
theorem choose_abs_le_16 (i b : ℕ) (hi : i ≤ 4) : |((i.choose b : ℕ) : ℝ)| ≤ 16 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi
  have h3 : ((i.choose b : ℕ) : ℝ) ≤ ((2 ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  norm_num at h3 ⊢
  linarith

/-- **The numerical core.**  If at the point `(z,θ)` the two Leibniz expansions of
`D_z^i (m·f)` and `D_z^jD_θ^i (m·f)` hold (with the `z`-only multiplier `m`), and the
iterated `Zop`-derivatives of `m` at `z` are bounded by `K`, then the `H⁴`-integrand of `m·f`
is bounded by `10⁶K²` times the `H⁴`-integrand of `f`. -/
theorem HkIntegrand_zmul_le_pointwise (α : ℝ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) {K : ℝ}
    (hK : 0 ≤ K) {z θ : ℝ}
    (hB : ∀ b ≤ 4, |Work.Spaces.Zop^[b] m z| ≤ K)
    (hexpZ : ∀ i ≤ 4, Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ =
      ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
        (Work.Spaces.Zop^[b] m z * Work.Spaces.DzIter (i - b) f z θ))
    (hexpM : ∀ j i, 1 ≤ i → i + j ≤ 4 →
      Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ =
      ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
        (Work.Spaces.Zop^[b] m z * Work.Spaces.mixed (j - b) i f z θ)) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => m z * f z θ) z θ
      ≤ 1000000 * K ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  set HI : ℝ := Work.Spaces.HkIntegrand α 4 f z θ with hHI
  have hHInn : 0 ≤ HI := by rw [hHI]; exact Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  -- ### the pure `D_z`-terms
  have hzt : ∀ i, i ≤ 4 →
      (Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (80 * K) ^ 2 * HI := by
    intro i hi
    have h1 : Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
            (Work.Spaces.Zop^[b] m z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
      rw [hexpZ i hi, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [h1]
    refine le_trans (Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := i) (D := 16) (K := K)
      hK (x := fun b => Work.Spaces.Zop^[b] m z)
      (y := fun b => Work.Spaces.DzIter b f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (fun b _ => hB b (by omega)) (fun b _ => choose_abs_le_16 i b hi)) ?_
    have hsub : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ HI := by
      rw [hHI, Work.Spaces.HkIntegrand]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α 4 f z θ))
      · intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      · intro x _ _; exact sq_nonneg _
    have hconst : ((i + 1 : ℝ) * 16 * K) ^ 2 ≤ (80 * K) ^ 2 := by
      have hi5 : ((i : ℝ) + 1) * 16 ≤ 80 := by
        have : (i : ℝ) ≤ 4 := by exact_mod_cast hi
        linarith
      have h1 : ((i : ℝ) + 1) * 16 * K ≤ 80 * K := by
        nlinarith [mul_le_mul_of_nonneg_right hi5 hK]
      exact pow_le_pow_left₀ (by positivity) h1 2
    calc ((i + 1 : ℝ) * 16 * K) ^ 2
          * ∑ b ∈ Finset.range (i + 1),
              (Work.Spaces.DzIter b f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ((i + 1 : ℝ) * 16 * K) ^ 2 * HI := mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
      _ ≤ (80 * K) ^ 2 * HI := mul_le_mul_of_nonneg_right hconst hHInn
  -- ### the mixed terms
  have hrown : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
      ∑ b ∈ Finset.range (j + 1),
          (Work.Spaces.mixed b i f z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ (j + 1) * HI := by
    intro i j hi hij
    have h := Finset.sum_le_sum (s := Finset.range (j + 1)) (fun b hb =>
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i b hi (by
        have := Finset.mem_range.mp hb; omega))
    rw [← hHI] at h
    refine le_trans h ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  have hmt : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ 5 * ((80 * K) ^ 2 * HI) := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc]
      have h1 : Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ
            * Work.Spaces.Wt α z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.Zop^[b] m z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ)) := by
        rw [hexpM j i hc.1 hc.2, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      rw [h1]
      refine le_trans (Work.FTS.CoercivityFix.E2Bound.binom_sum_sq_le (i := j) (D := 16) (K := K)
        hK (x := fun b => Work.Spaces.Zop^[b] m z)
        (y := fun b => Work.Spaces.mixed b i f z θ * Work.Spaces.Wt α z θ)
        (fun b _ => hB b (by omega))
        (fun b _ => choose_abs_le_16 j b (by omega))) ?_
      have hconst : ((j + 1 : ℝ) * 16 * K) ^ 2 ≤ (80 * K) ^ 2 := by
        have hj5 : ((j : ℝ) + 1) * 16 ≤ 80 := by
          have hj : j + 1 ≤ 5 := by omega
          have hj' : (j : ℝ) + 1 ≤ 5 := by exact_mod_cast hj
          linarith
        have h1 : ((j : ℝ) + 1) * 16 * K ≤ 80 * K := by
          nlinarith [mul_le_mul_of_nonneg_right hj5 hK]
        exact pow_le_pow_left₀ (by positivity) h1 2
      have hle : (j + 1 : ℝ) * HI ≤ 5 * HI := by
        have hj : j + 1 ≤ 5 := by omega
        have hj' : (j : ℝ) + 1 ≤ 5 := by exact_mod_cast hj
        nlinarith [hHInn]
      have hstep : ((j + 1 : ℝ) * 16 * K) ^ 2 * ∑ b ∈ Finset.range (j + 1),
            (Work.Spaces.mixed b i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (80 * K) ^ 2 * (5 * HI) := by
        refine le_trans (mul_le_mul_of_nonneg_left (hrown i j hc.1 hc.2) (sq_nonneg _)) ?_
        refine le_trans (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) ?_
        exact mul_le_mul_of_nonneg_right hconst (by nlinarith [hHInn])
      calc ((j + 1 : ℝ) * 16 * K) ^ 2 * ∑ b ∈ Finset.range (j + 1),
              (Work.Spaces.mixed b i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (80 * K) ^ 2 * (5 * HI) := hstep
        _ = 5 * ((80 * K) ^ 2 * HI) := by ring
    · rw [if_neg hc]
      exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hHInn)
  -- ### assembling the two sums
  have hZsum : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * ((80 * K) ^ 2 * HI) := by
    refine le_trans (Finset.sum_le_sum (s := Finset.range 5) (fun i hi => hzt i (by
      simp only [Finset.mem_range] at hi; omega))) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have hMsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 25 * (5 * ((80 * K) ^ 2 * HI)) := by
    refine le_trans (Finset.sum_le_sum (s := Finset.range 5)
      (fun i _ => Finset.sum_le_sum (s := Finset.range 5) (fun j _ => hmt i j))) ?_
    have h1 : (∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5, (5 * ((80 * K) ^ 2 * HI)))
        = 25 * (5 * ((80 * K) ^ 2 * HI)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    exact le_of_eq h1
  rw [Work.Spaces.HkIntegrand]
  have hfinal : (5 * ((80 * K) ^ 2 * HI)) + 25 * (5 * ((80 * K) ^ 2 * HI))
      ≤ 1000000 * K ^ 2 * HI := by
    nlinarith [sq_nonneg K, hHInn]
  linarith [hZsum, hMsum, hfinal]

/-! ## The two Leibniz expansions -/

/-- The Leibniz expansion of `D_z^i (m·f)` for a `z`-only multiplier `m`, at finite order,
on an open set `V` on which the `θ`-slice of `f` is `C^i`. -/
theorem DzIter_mul_of_contDiffOn (i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) {V : Set ℝ}
    (hV : IsOpen V) {θ : ℝ} (hm : ContDiffOn ℝ i m V)
    (hf : ContDiffOn ℝ i (fun z' => f z' θ) V) :
    ∀ z ∈ V, Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (Work.Spaces.Zop^[b] m z * Work.Spaces.DzIter (i - b) f z θ) := by
  intro z hz
  have hsl : (fun z' => Work.Spaces.DzIter i (fun z θ => m z * f z θ) z' θ)
      = Work.Spaces.Zop^[i] (fun z' => m z' * f z' θ) :=
    Work.FTS.LocData.Zop_iterate_slice i _ θ
  rw [congrFun hsl z]
  change Work.Spaces.Zop^[i] (m * (fun z' => f z' θ)) z = _
  rw [ZopIterLeibniz hV hm hf hz]
  simp only
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← congrFun (Work.FTS.LocData.Zop_iterate_slice (i - b) f θ) z]

/-- The Leibniz expansion of `D_z^jD_θ^i (m·f)` for a `z`-only multiplier `m`, at finite
order, on an open set `V` on which the `θ`-slice of `D_θ^i f` is `C^j`. -/
theorem mixed_mul_of_contDiffOn (j i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) {V : Set ℝ}
    (hV : IsOpen V) {θ : ℝ} (hm : ContDiffOn ℝ j m V)
    (hf : ContDiffOn ℝ j (fun z' => Work.Spaces.DthIter i f z' θ) V) :
    ∀ z ∈ V, Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] m z * Work.Spaces.mixed (j - b) i f z θ) := by
  intro z hz
  have hcomm : Work.Spaces.DthIter i (fun z θ => m z * f z θ)
      = fun z θ => m z * Work.Spaces.DthIter i f z θ :=
    Work.Coercivity.DthIter_mulZm i m f
  have hmain := DzIter_mul_of_contDiffOn j m (Work.Spaces.DthIter i f) hV hm hf z hz
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => m z * f z θ)) z θ = _
  rw [hcomm]
  exact hmain

theorem HkIntegrandMulDthSmooth : ∃ C : ℝ, 0 < C ∧
    ∀ (α z θ : ℝ) (h : ℝ → ℝ → ℝ), 0 < α → 0 ≤ z → θ ∈ Set.Icc 0 (Real.pi / 2) →
      ContDiffAt ℝ 5 (Function.uncurry h) (z, θ) →
      Work.Spaces.HkIntegrand α 4 (fun z' θ' => 3 * Work.Spaces.Dth h z' θ' / (1 + z')) z θ
        ≤ C * Work.Spaces.HkIntegrand α 5 h z θ := by
  refine ⟨1000000 * 100 ^ 2 + 1, by norm_num, ?_⟩
  intro α z θ h hα hz hθI hcd
  -- the multiplier `φ(z) = 3/(1+z)`
  have hF_eq : (fun z' θ' => 3 * Work.Spaces.Dth h z' θ' / (1 + z'))
      = fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ := by
    funext z θ
    ring
  have hRHSnn : 0 ≤ Work.Spaces.HkIntegrand α 5 h z θ :=
    Work.Spaces.HkIntegrand_nonneg α 5 h z θ
  by_cases hs : Real.sin (2 * θ) = 0
  · -- the angular weight vanishes
    have hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
    have hWt : Work.Spaces.Wt α z θ = 0 := by
      rw [Work.Spaces.Wt, Work.Spaces.wTheta, hs,
        Real.zero_rpow (by have := Work.Spaces.gam_pos hα; intro hc; linarith), mul_zero]
    rw [hF_eq, HkIntegrand_eq_zero_of_weights α 4
      (fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ) z θ hH hWt]
    exact mul_nonneg (by norm_num) hRHSnn
  · -- `0 < θ < π/2`
    have hθ0 : 0 < θ := by
      rcases lt_or_eq_of_le hθI.1 with hlt | heq
      · exact hlt
      · exact absurd (by rw [← heq]; simp) hs
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hθI.2 with hlt | heq
      · exact hlt
      · refine absurd ?_ hs
        rw [heq]
        have : 2 * (Real.pi / 2) = Real.pi := by ring
        rw [this, Real.sin_pi]
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes
      subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      have hH : Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rw [hw0, zero_div]
      have hWt : Work.Spaces.Wt α 0 θ = 0 := by
        rw [Work.Spaces.Wt, hw0, zero_mul]
      rw [hF_eq, HkIntegrand_eq_zero_of_weights α 4
        (fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ) 0 θ hH hWt]
      exact mul_nonneg (by norm_num) hRHSnn
    · -- the main case: `z > 0` and `0 < θ < π/2`
      obtain ⟨V, W, hVopen, hWopen, hzV, hθW, hVsub, _hWsub, hsm⟩ :=
        exists_nbhd_prod_of_contDiffAt (h := h) (n := 5) hzpos hθ0 hθ1 hcd
      have hU : IsOpen (V ×ˢ W) := hVopen.prod hWopen
      have hphi : ∀ k : ℕ, k ≤ 4 → ContDiffOn ℝ k (fun z' => 3 / (1 + z')) V := fun k _ =>
        (contDiffOn_phiThree k).mono (fun x hx => by
          have hx' : (0 : ℝ) < x := hVsub hx
          exact show (-1 : ℝ) < x by linarith)
      -- smoothness of `D_θ h` (and of its `θ`-derivatives) on the product
      have hDth4 : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dth h)) (V ×ˢ W) :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le hU 1 4
          (by norm_num) hsm
      -- the two Leibniz expansions at `(z,θ)`
      have hexpZ : ∀ i ≤ 4, Work.Spaces.DzIter i
            (fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ) z θ =
          ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
            (Work.Spaces.Zop^[b] (fun z' => 3 / (1 + z')) z
              * Work.Spaces.DzIter (i - b) (Work.Spaces.Dth h) z θ) := by
        intro i hi
        have hslice : ContDiffOn ℝ i (fun z' => Work.Spaces.Dth h z' θ) V :=
          contDiffOn_zslice (hDth4.of_le (Nat.cast_le.mpr hi)) hθW
        exact DzIter_mul_of_contDiffOn i (fun z' => 3 / (1 + z')) (Work.Spaces.Dth h)
          hVopen (hphi i hi) hslice z hzV
      have hexpM : ∀ j i, 1 ≤ i → i + j ≤ 4 → Work.Spaces.mixed j i
            (fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ) z θ =
          ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (Work.Spaces.Zop^[b] (fun z' => 3 / (1 + z')) z
              * Work.Spaces.mixed (j - b) i (Work.Spaces.Dth h) z θ) := by
        intro j i _hi hij
        have hDthij : ContDiffOn ℝ j
            (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dth h))) (V ×ˢ W) :=
          Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le hU i j hij hDth4
        have hslice : ContDiffOn ℝ j
            (fun z' => Work.Spaces.DthIter i (Work.Spaces.Dth h) z' θ) V :=
          contDiffOn_zslice hDthij hθW
        exact mixed_mul_of_contDiffOn j i (fun z' => 3 / (1 + z')) (Work.Spaces.Dth h)
          hVopen (hphi j (by omega)) hslice z hzV
      -- the pointwise bound, with the bound on the `Zop`-iterates of `φ`
      have hB : ∀ b ≤ 4, |Work.Spaces.Zop^[b] (fun z' => 3 / (1 + z')) z| ≤ 100 :=
        fun b hb => PhiZopBound b hb z (le_of_lt hzpos)
      have hpoint := HkIntegrand_zmul_le_pointwise α (fun z' => 3 / (1 + z'))
        (Work.Spaces.Dth h) (K := 100) (by norm_num) hB hexpZ hexpM
      rw [hF_eq]
      calc Work.Spaces.HkIntegrand α 4
            (fun z θ => (3 / (1 + z)) * Work.Spaces.Dth h z θ) z θ
          ≤ 1000000 * 100 ^ 2 * Work.Spaces.HkIntegrand α 4 (Work.Spaces.Dth h) z θ := hpoint
        _ ≤ 1000000 * 100 ^ 2 * Work.Spaces.HkIntegrand α 5 h z θ :=
            mul_le_mul_of_nonneg_left
              (Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α (by linarith) 4 h z θ hz hθI)
              (by norm_num)
        _ ≤ (1000000 * 100 ^ 2 + 1) * Work.Spaces.HkIntegrand α 5 h z θ := by
            nlinarith [hRHSnn]

end Work.FTS.FinalClock
