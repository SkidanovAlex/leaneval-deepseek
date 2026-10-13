/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `α`-uniform `ℋⁿ`-bound for the `D_z`-commutator defect `Ê₂`

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)² = φ(z)·(2f + 3D_θf)` with
`φ(z) = z/(1+z)²` is the `D_z`-commutator defect of the clean operator `Lhat`
(`CoercivityFix.Basic`); this file proves the **uniform** slot estimate

  `HkSq α n (Ê₂ f) ≤ Cn · (HkSq α n f + HkSq α n (D_θ f))`  for all `α ≥ -1/10`,

with a constant `Cn` depending only on `n` — *not* on `α`.

## Why uniformity in `α` is the point

The sibling `E2hat_HkSq_le_of_ge` proves the same inequality with a constant that is
allowed to depend on `α`; it routes through `E2hat_slice_le α n`, whose constant comes from
the existential `HkIntegrand_zmul_uniform α n` and is therefore opaque in `α`.  The target of
this file needs *one* number `Cn` valid for the whole range `α ≥ -1/10`.

The way to get it is to keep the two angular weights of the integrand apart.  Writing

* `zblk n g z θ := ∑_{i ≤ n} (D_z^i g · w(z)/sin(2θ)^{η/2})²` (the pure block, weight
  `w/sin^{η/2}` — **independent of `α`**),
* `mblk n g z θ := ∑_{1 ≤ i, i+j ≤ n} (D_z^jD_θ^i g)²` (the mixed block, *unweighted*),

one has the exact identity (for every `α`, `z`, `θ`)

  `HkIntegrand α n g z θ = zblk n g z θ + (Wt α z θ)² · mblk n g z θ`,

because in `HkIntegrand` the weight `Wt α z θ = w(z)·sin(2θ)^{-γ(α)/2}` is constant in the
summation indices and can be pulled out of the (mixed) sum of squares.

The multiplier `φ(z) = z/(1+z)²` is a function of `z` alone, so the Leibniz rule
`mixed_zmul` says

  `D_z^jD_θ^i (φ·g) = ∑_{b≤j} C(j,b) (Zop^b φ)(D_z^{j-b}D_θ^i g)`,

i.e. the `θ`-derivatives fall only on `g`.  Consequently the multiplier estimate can be
*split over the two blocks with their own weights*: the pure block carries the `α`-free
weight `w/sin^{η/2}` (so its estimate is manifestly `α`-free), and in the mixed block the
weight `Wt α` factors out of *both* sides, so that estimate is `α`-free as well.  This gives

  `HkIntegrand α n (φ·g) ≤ C(n) · HkIntegrand α n g`   for **every** `α`

with `C(n)` explicit, and the target follows by splitting
`Ê₂ f = 2·(φ·f) + 3·(φ·D_θ f)` with the subadditivity `HkIntegrand_add_le` and the
homogeneity `HkIntegrand_const_mul`.

## Layout

* `zblk`, `mblk` and the identity `HkIntegrand_eq_zblk_add`; vanishing of `HkIntegrand` at
  `z = 0`;
* the slot extraction lemmas `zslot_le`, `mslot_le`;
* the two α-free multiplier estimates `zblk_zmul_le`, `mblk_zmul_le`, and their combination
  `HkIntegrand_phi_mul_le`;
* the pointwise defect estimate `E2hat_HkIntegrand_le_uniform_pt` (no hypothesis on `α`);
* the assembly `E2hat_HkSq_le_uniform` (monotonicity of the two iterated integrals).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkSq_le
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.CoercivityFix.E2Bound.mixed_zmul
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound
import Submission.Work.FTS.LocData.HkIntegrand_add_le
import Submission.Work.FTS.LocData.HkIntegrand_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two blocks of the `ℋⁿ`-integrand -/

/-- The pure (`D_z`-only) block of the `ℋⁿ`-integrand: without the angular weight
`Wt α` this block is *independent of `α`*. -/
private def zblk (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed block of the `ℋⁿ`-integrand, **without** the angular weight: the sum of the
squares of the genuinely mixed derivatives `D_z^jD_θ^i g`, `1 ≤ i`, `i + j ≤ n`. -/
private def mblk (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0)

private lemma zblk_nonneg (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ zblk n g z θ :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma mblk_nonneg (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ mblk n g z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- **The exact identity** expressing `HkIntegrand` through the two blocks: the angular
weight `Wt α z θ` is constant in the summation indices of the mixed block, hence it can be
pulled out of the sum of squares. -/
private lemma HkIntegrand_eq_zblk_add (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α n g z θ
      = zblk n g z θ + (Work.Spaces.Wt α z θ) ^ 2 * mblk n g z θ := by
  have hpt : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.Wt α z θ) ^ 2
        * (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0) := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  have hkey : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (Work.Spaces.Wt α z θ) ^ 2 * mblk n g z θ := by
    simp only [mblk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  simp only [Work.Spaces.HkIntegrand, zblk]
  rw [hkey]

/-- At `z = 0` the radial weight `w 0 = 0` kills every summand of the integrand. -/
private lemma HkIntegrand_zero_z (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α n g 0 θ = 0 := by
  rw [HkIntegrand_eq_zblk_add]
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hz : zblk n g 0 θ = 0 := by
    simp only [zblk, hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero]
  have hW : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, Work.Spaces.w]
  rw [hz, hW]
  ring

/-! ## Extracting single slots -/

/-- Each pure summand of `zblk` is at most the whole of `zblk`. -/
private lemma zslot_le (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) {r : ℕ} (hr : r ≤ n) :
    (Work.Spaces.DzIter r g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ zblk n g z θ :=
  Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun i => (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))

/-- Each mixed summand of `mblk` is at most the whole of `mblk`. -/
private lemma mslot_le (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a + b ≤ n) :
    (Work.Spaces.mixed b a g z θ) ^ 2 ≤ mblk n g z θ := by
  have han : a ≤ n := le_trans (Nat.le_add_right a b) hab
  have hbn : b ≤ n := le_trans (Nat.le_add_left b a) hab
  have h1 : (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ ∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ a ∧ a + j ≤ n then (Work.Spaces.mixed j a g z θ) ^ 2 else 0) := by
    have h := Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j => (if 1 ≤ a ∧ a + j ≤ n
        then (Work.Spaces.mixed j a g z θ) ^ 2 else 0))
      (fun j _ => by split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hbn))
    rwa [if_pos ⟨ha, hab⟩] at h
  have h2 : (∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ a ∧ a + j ≤ n then (Work.Spaces.mixed j a g z θ) ^ 2 else 0))
      ≤ mblk n g z θ := by
    simp only [mblk]
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0))
      (fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le han))
  exact le_trans h1 h2

/-- The binomial coefficients of order `≤ n` have square at most `4ⁿ`. -/
private lemma choose_sq_le_four_pow (n i b : ℕ) (hi : i ≤ n) :
    (((i.choose b : ℕ)) : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : (((i.choose b : ℕ)) : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast h1
  have h3 : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hi
  have h4 : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ i) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have h5 : ((2 : ℝ) ^ i) ^ 2 = (4 : ℝ) ^ i := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    ring
  have h6 : (4 : ℝ) ^ i ≤ (4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hi
  linarith [h4, h6, h5.le]

/-! ## The α-free multiplier estimate for the pure block -/

/-- `mixed_zmul` at `i = 0`: the Leibniz rule for `D_z^j` acting on `φ(z)·g`. -/
private lemma DzIter_zmul_eq (j : ℕ) (a : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ha : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z))
    (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.Spaces.DzIter j (fun z θ : ℝ => a z * g z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (((j.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] a z * Work.Spaces.DzIter (j - b) g z θ) := by
  have h := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j 0 a g hz hθ ha hg
  simpa only [Work.Spaces.mixed_zero_right] using h

/-- **The pure block of `φ·g` is dominated by the pure block of `g`**, with a constant
depending only on `n` (and not on `α`, `z`, `θ`). -/
private theorem zblk_zmul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ ≤ C * zblk n f z θ := by
  obtain ⟨K, _hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1, by positivity, ?_⟩
  intro f hf z hz θ hθ
  have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hZnn : 0 ≤ zblk n f z θ := zblk_nonneg n f z θ
  have hper : ∀ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hDz := DzIter_zmul_eq i (fun z : ℝ => z / (1 + z) ^ 2) f hz1 hθ hphi hf
    -- insert the radial weight and reassociate
    have hsplit : Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (((i.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
      rw [hDz, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsplit]
    -- Cauchy–Schwarz on the binomial sum
    have hcs : (∑ b ∈ Finset.range (i + 1), (((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2 := by
      have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun b => (((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))))
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]; push_cast; ring
      simpa only [hcard] using h0
    refine le_trans hcs ?_
    have hterm : ∀ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        ≤ (4 : ℝ) ^ n * K ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      intro b hb
      have hbn : b ≤ n :=
        le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hin
      have hZb : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K :=
        hKbd b hbn z hz
      have hZb2 : (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
      have hcb := choose_sq_le_four_pow n i b hin
      calc ((((i.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ)) : ℝ) ^ 2
              * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ (4 : ℝ) ^ n * K ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul hcb hZb2 (sq_nonneg _) (by positivity)
    have hslot : ∀ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ zblk n f z θ :=
      fun b hb => zslot_le n f z θ (r := i - b) (by
        have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        omega)
    have hsum : (∑ b ∈ Finset.range (i + 1), ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
      Finset.sum_le_sum fun b hb => le_trans (hterm b hb)
        (mul_le_mul_of_nonneg_left (hslot b hb) (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have := Nat.succ_le_succ hin
      exact_mod_cast this
    have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
      mul_nonneg (by positivity) hZnn
    calc ((i : ℝ) + 1) * (((i : ℝ) + 1) * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ))
        = ((i : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) := by ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hi1 2) hA
      _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ := by ring
  calc zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      = ∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
          (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
        Finset.sum_le_sum hper
    _ = ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * zblk n f z θ := by
        have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
          mul_nonneg (by positivity) hZnn
        have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hfac : (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * zblk n f z θ
            - ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ)
            = ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ
              + zblk n f z θ := by ring
        have hlead : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n := by positivity
        have hnn : 0 ≤ ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
          mul_nonneg (mul_nonneg hlead (sq_nonneg K)) hZnn
        linarith [hfac, hnn, hZnn]

/-! ## The α-free multiplier estimate for the mixed block -/

/-- **The mixed block of `φ·g` is dominated by the mixed block of `g`**, with a constant
depending only on `n`.  Here the Leibniz rule `mixed_zmul` is applied directly: the
`z`-only factor `φ` is differentiated only in `z`, so each term of the expansion is a slot
of the mixed block of `g`. -/
private theorem mblk_zmul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ ≤ C * mblk n f z θ := by
  obtain ⟨K, _hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1, by positivity, ?_⟩
  intro f hf z hz θ hθ
  have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hMnn : 0 ≤ mblk n f z θ := mblk_nonneg n f z θ
  have hper : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ) ^ 2
        else 0)
      ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      obtain ⟨hi1, hij⟩ := hc
      have hin : i ≤ n := by omega
      have hjn : j ≤ n := by omega
      have hlei := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j i
        (fun z : ℝ => z / (1 + z) ^ 2) f hz1 hθ hphi hf
      rw [hlei]
      have hcs : (∑ b ∈ Finset.range (j + 1), (((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
          ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2 := by
        have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
          (f := fun b => (((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ))
        have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        simpa only [hcard] using h0
      refine le_trans hcs ?_
      have hterm : ∀ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
          ≤ (4 : ℝ) ^ n * K ^ 2 * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by
        intro b hb
        have hbn : b ≤ n :=
          le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hjn
        have hZb : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K :=
          hKbd b hbn z hz
        have hZb2 : (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
        have hcb := choose_sq_le_four_pow n j b hjn
        calc ((((j.choose b : ℕ)) : ℝ)
              * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
                * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
            = (((j.choose b : ℕ)) : ℝ) ^ 2
                * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2
                * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by ring
          _ ≤ (4 : ℝ) ^ n * K ^ 2 * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact mul_le_mul hcb hZb2 (sq_nonneg _) (by positivity)
      have hslot : ∀ b ∈ Finset.range (j + 1),
          (Work.Spaces.mixed (j - b) i f z θ) ^ 2 ≤ mblk n f z θ :=
        fun b hb => mslot_le n f z θ hi1 (by
          have hb' : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          omega)
      have hsum : (∑ b ∈ Finset.range (j + 1), ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2)
          ≤ ∑ _b ∈ Finset.range (j + 1), ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
        Finset.sum_le_sum fun b hb => le_trans (hterm b hb)
          (mul_le_mul_of_nonneg_left (hslot b hb) (by positivity))
      refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hj1 : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have := Nat.succ_le_succ hjn
        exact_mod_cast this
      have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ :=
        mul_nonneg (by positivity) hMnn
      calc ((j : ℝ) + 1) * (((j : ℝ) + 1) * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ))
          = ((j : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) := by ring
        _ ≤ ((n : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hj1 2) hA
        _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ := by ring
    · rw [if_neg hc]
      positivity
  calc mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ) ^ 2
            else 0) := rfl
    _ ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1),
          (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj
    _ = ((n : ℝ) + 1)
          * (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * mblk n f z θ := by
        have hfac : (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * mblk n f z θ
            - ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ))
            = mblk n f z θ := by ring
        linarith [hfac, hMnn]

/-! ## The α-free multiplier estimate for `φ` -/

/-- **Multiplication by `φ(z) = z/(1+z)²` does not increase the `ℋⁿ`-integrand**, with a
constant uniform in `α`.  The two blocks are estimated separately, each with its own weight;
both estimates are `α`-free because the weight `Wt α z θ` is constant in the summation
indices and factors out. -/
private theorem HkIntegrand_phi_mul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α n f z θ := by
  obtain ⟨Kp, _hKppos, hKp⟩ := zblk_zmul_le n
  obtain ⟨Km, _hKmpos, hKm⟩ := mblk_zmul_le n
  refine ⟨max Kp Km + 1, by positivity, ?_⟩
  intro α f hf z hz θ hθ
  have h1 := hKp f hf z hz θ hθ
  have h2 := hKm f hf z hz θ hθ
  rw [HkIntegrand_eq_zblk_add α n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ,
    HkIntegrand_eq_zblk_add α n f z θ]
  have hZp : 0 ≤ zblk n f z θ := zblk_nonneg n f z θ
  have hMp : 0 ≤ mblk n f z θ := mblk_nonneg n f z θ
  have hW : 0 ≤ (Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
  have hKpm : Kp ≤ max Kp Km + 1 := by
    have := le_max_left Kp Km
    linarith
  have hKmm : Km ≤ max Kp Km + 1 := by
    have := le_max_right Kp Km
    linarith
  have hs1 : zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      ≤ (max Kp Km + 1) * zblk n f z θ :=
    le_trans h1 (mul_le_mul_of_nonneg_right hKpm hZp)
  have hs3 : (Work.Spaces.Wt α z θ) ^ 2
        * mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Km * mblk n f z θ) :=
    mul_le_mul_of_nonneg_left h2 hW
  have hs4 : (Work.Spaces.Wt α z θ) ^ 2 * (Km * mblk n f z θ)
      ≤ (max Kp Km + 1) * ((Work.Spaces.Wt α z θ) ^ 2 * mblk n f z θ) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKmm hMp) hW
    linarith [h]
  linarith [hs1, hs3, hs4]

/-! ## The pointwise defect estimate, uniform in `α` -/

/-- **The `ℋⁿ`-slot bound for the `D_z`-commutator defect, with a constant independent of
`α`.**  Splitting `Ê₂ f = 2·(φ·f) + 3·(φ·D_θf)` with the subadditivity and homogeneity of
the integrand reduces the claim to the α-free multiplier estimate for `φ`. -/
private theorem E2hat_HkIntegrand_le_uniform_pt (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ Cn * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_phi_mul_le n
  refine ⟨18 * C, by positivity, ?_⟩
  intro α f hf z hz θ hθ
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hDth : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
    simpa using Work.FTS.LocData.SmoothQuad.DthIter hf 1
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hA : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 (Work.FTS.LocData.smoothQuad_mul hphi hf)
  have hB : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul 3 (Work.FTS.LocData.smoothQuad_mul hphi hDth)
  rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
  have h1 := Work.FTS.LocData.HkIntegrand_add_le α n hA hB hzIz hθIθ
  have h1' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
        + 2 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ := by
    simpa only [Pi.add_apply] using h1
  have h2 := Work.FTS.LocData.HkIntegrand_const_mul α n 2
    (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
  have h3 := Work.FTS.LocData.HkIntegrand_const_mul α n 3
    (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ
  have h2' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
      = 4 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ := by
    rw [h2]; norm_num
  have h3' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
      = 9 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ := by
    rw [h3]; norm_num
  have h4 := hC α f hf z hz θ hθ
  have h5 := hC α (Work.Spaces.Dth f) hDth z hz θ hθ
  have hX : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hY : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
    Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
  have hCX : 0 ≤ C * Work.Spaces.HkIntegrand α n f z θ := mul_nonneg hCpos.le hX
  have hCY : 0 ≤ C * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
    mul_nonneg hCpos.le hY
  nlinarith [h1', h2', h3', h4, h5, hX, hY, hCX, hCY]

/-! ## The iterated-integral assembly -/

/-- `Iθ = [0,π/2]` and `(0,π/2)` differ by a null set. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0)
    (b := π / 2)).symm

/-- **The α-uniform `ℋⁿ`-defect estimate.**  For every `α ≥ -1/10` and every
`f ∈ RegQ α (n+1)`,

`HkSq α n (Ê₂ f) ≤ Cn · (HkSq α n f + HkSq α n (D_θ f))`

with a constant `Cn` depending only on `n`.  The two `ℋⁿ`-memberships needed for the
monotonicity of the integrals are `HkMem α n f` (monotonicity of `HkMem`, from
`RegQ α (n+1) f`) and `HkMem α n (D_θ f)` (`HkMem_dth_of_RegQ_ge`, whose range is exactly
`α ≥ -1/10`). -/
theorem E2hat_HkSq_le_uniform (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ α : ℝ, -(1 / 10 : ℝ) ≤ α → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.RegQ α (n + 1) f →
      Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
        ≤ Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCnpos, hpt⟩ := E2hat_HkIntegrand_le_uniform_pt n
  refine ⟨Cn, hCnpos, ?_⟩
  intro α hα f hf
  have hmf : Work.Spaces.HkMem α n f :=
    Work.FTS.LocDataExt.HkMem_mono (Nat.le_succ n) hf.1 hf.2.1
  have hmth : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α n hα hf
  -- the angular slice inequality, for every `z ∈ Iz`
  have hsl : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ≤ Cn * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)) := by
    intro z hz
    have hzge : 0 ≤ z := hz
    rw [restrict_Iθ_eq_Ioo]
    rcases eq_or_lt_of_le hzge with hz0 | hzpos
    · subst hz0
      simp only [HkIntegrand_zero_z, integral_zero, mul_zero, add_zero]
      exact le_refl 0
    · have h1 : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmf.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have h2 : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmth.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)))
        (f := fun θ => Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        (g := fun θ => Cn * (Work.Spaces.HkIntegrand α n f z θ
            + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ))
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ((h1.add h2).const_mul Cn)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => hpt α f hf.1 z hzpos θ hθ))
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2] at hmono
      exact hmono
  -- the outer integral, by monotonicity
  have hint : Integrable (fun z => Cn *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)))
      ((volume : Measure ℝ).restrict Work.Spaces.Iz) := (hmf.2.add hmth.2).const_mul Cn
  have hout := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ))
    hint (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
      (fun z hz => hsl z hz))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmth.2] at hout
  simpa only [Work.Spaces.HkSq] using hout

end Work.FTS.CoercivityFix.Assembly
