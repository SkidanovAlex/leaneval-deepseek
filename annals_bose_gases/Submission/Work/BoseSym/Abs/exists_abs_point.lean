import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Abs.exists_absPoint_graphPoint
import Submission.Work.BoseSym.Abs.exists_lp_abs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kato's inequality on the energy space `Hsub N L`

This file proves that the Dirichlet energy space `Hsub N L` (the closure, in the
ambient space `Amb N = L²(Conf N) × ∏_j L²(Conf N)`, of the graph of the gradient
over the test functions supported in the open box) is closed under the pointwise
absolute value: for every `p : Hsub N L` there is `q : Hsub N L` whose function
part is a.e. the absolute value of the function part of `p`, and whose gradient
energy does not increase: `gSq q ≤ gSq p`.

## The argument

`Hsub N L` is the closure of the graph points `F ↦ (F, ∇F)` of the test functions
(`exists_graphPoint_close`).  For a test function `F` the approximate absolute
value `√(F² + δ²) - δ` is again a test function, and as `δ → 0` its graph point
converges to the pair `(|F|, sgn(F)·∇F)`, which therefore belongs to `Hsub N L`
with gradient energy at most that of `(F, ∇F)`
(`exists_absPoint_graphPoint`).

The passage to a general `p : Hsub N L` is *not* by extracting a weak limit
(which would need reflexivity of the ambient space and a Banach–Alaoglu type
argument).  Instead note that `hSq = ‖·.1‖² + ∑_j ‖·.2 j‖²` is the square of a
Hilbert norm on `Amb N`, whose parallelogram law is available componentwise.
Writing `φ` for the `L²`-class of `|p.1|` and `M = gSq p`, the nested family of
closed convex sets

`E n = {q ∈ Hsub N L | ‖q.1 - φ‖ ≤ 1/(n+1) ∧ gSq q ≤ M + 1/(n+1)}`

is nonempty (by the graph-point case applied to the approximants of `p`), and
`exists_mem_iInter_of_nested` extracts a point of `⋂ n, E n` from any nested
family of nonempty closed convex sets that is bounded in the graph norm: taking
`m n = inf {hSq q | q ∈ E n}` and `q n ∈ E n` with `hSq (q n) ≤ m n + 1/(n+1)`,
the parallelogram law gives `hSq (q a - q b) ≤ 2(m b - m a) + 2/(a+1) + 2/(b+1)`
for `a ≤ b`, so the `q n` are Cauchy; their limit lies in every `E n`.

## Main result

* `exists_abs_point` : Kato's inequality on the energy space.
-/

namespace Work.BoseSym.Abs

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ENNReal

noncomputable section

set_option autoImplicit false

/-! ### Elementary algebra of the graph norm `hSq` -/

/-- The graph norm squared is nonnegative. -/
lemma hSq_nonneg {N : ℕ} (z : Amb N) : 0 ≤ hSq z := by
  simp only [hSq, l2Sq, gSq]
  positivity

/-- The parallelogram law for the graph norm squared: componentwise, `hSq` is the
square of the Hilbert norm on the product of the `L²` spaces. -/
lemma hSq_parallelogram {N : ℕ} (x y : Amb N) :
    hSq (x + y) + hSq (x - y) = 2 * hSq x + 2 * hSq y := by
  have h1 : ‖x.1 + y.1‖ ^ 2 + ‖x.1 - y.1‖ ^ 2 = 2 * ‖x.1‖ ^ 2 + 2 * ‖y.1‖ ^ 2 := by
    have := parallelogram_law_with_norm ℝ x.1 y.1
    linarith
  have h2 : ∀ j : GIdx N, ‖x.2 j + y.2 j‖ ^ 2 + ‖x.2 j - y.2 j‖ ^ 2
      = 2 * ‖x.2 j‖ ^ 2 + 2 * ‖y.2 j‖ ^ 2 := by
    intro j
    have := parallelogram_law_with_norm ℝ (x.2 j) (y.2 j)
    linarith
  have hsum : (∑ j : GIdx N, ‖x.2 j + y.2 j‖ ^ 2) + (∑ j : GIdx N, ‖x.2 j - y.2 j‖ ^ 2)
      = 2 * (∑ j : GIdx N, ‖x.2 j‖ ^ 2) + 2 * (∑ j : GIdx N, ‖y.2 j‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.mul_sum]
  simp only [hSq, l2Sq, gSq, Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub,
    Pi.add_apply, Pi.sub_apply]
  linarith

/-- Homogeneity of the graph norm squared. -/
lemma hSq_smul {N : ℕ} (c : ℝ) (x : Amb N) : hSq (c • x) = c ^ 2 * hSq x := by
  have h1 : ‖(c • x).1‖ ^ 2 = c ^ 2 * ‖x.1‖ ^ 2 := by
    rw [Prod.smul_fst, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h2 : ∀ j : GIdx N, ‖(c • x).2 j‖ ^ 2 = c ^ 2 * ‖x.2 j‖ ^ 2 := by
    intro j
    rw [Prod.smul_snd, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [hSq, l2Sq, gSq]
  rw [Finset.sum_congr rfl (fun j _ => h2 j), h1, mul_add, Finset.mul_sum]

/-- Evenness of the graph norm squared. -/
lemma hSq_neg {N : ℕ} (z : Amb N) : hSq (-z) = hSq z := by
  rw [← neg_one_smul ℝ z, hSq_smul]
  norm_num

/-- The ambient norm is controlled by the graph norm squared: `hSq` sees all
components whereas `‖·‖` is the maximum of their norms. -/
lemma norm_sq_le_hSq {N : ℕ} (z : Amb N) : ‖z‖ ^ 2 ≤ hSq z := by
  have hSq0 : 0 ≤ hSq z := hSq_nonneg z
  have h1 : ‖z.1‖ ^ 2 ≤ hSq z := by
    have hs : 0 ≤ ∑ j : GIdx N, ‖z.2 j‖ ^ 2 := Finset.sum_nonneg (fun j _ => by positivity)
    simp only [hSq, l2Sq, gSq]
    linarith
  have h2 : ∀ j : GIdx N, ‖z.2 j‖ ^ 2 ≤ hSq z := by
    intro j
    have hs := Finset.single_le_sum (f := fun j : GIdx N => ‖z.2 j‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
    have h0 : (0:ℝ) ≤ ‖z.1‖ ^ 2 := by positivity
    simp only [hSq, l2Sq, gSq]
    linarith
  have h3 : ‖z.2‖ ^ 2 ≤ hSq z := by
    have hle : ‖z.2‖ ≤ Real.sqrt (hSq z) := by
      rw [Pi.norm_def]
      rw [show Real.sqrt (hSq z) = ↑((Real.sqrt (hSq z)).toNNReal) from
        (Real.coe_toNNReal _ (Real.sqrt_nonneg _)).symm]
      exact NNReal.coe_le_coe.mp (Finset.sup_le fun j _ => NNReal.coe_le_coe.mp (by
        rw [coe_nnnorm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
        exact Real.le_sqrt_of_sq_le (h2 j)))
    nlinarith [Real.sq_sqrt hSq0, Real.sqrt_nonneg (hSq z), norm_nonneg z.2]
  rw [Prod.norm_def]
  refine le_trans (pow_le_pow_left₀ ?_ (max_le (Real.le_sqrt_of_sq_le h1)
    (Real.le_sqrt_of_sq_le h3)) 2) ?_
  · exact le_trans (norm_nonneg z.1) (le_max_left _ _)
  · rw [Real.sq_sqrt hSq0]

/-- The gradient energy `gSq` is continuous (a finite sum of squares of norms of
the continuous coordinate maps). -/
lemma continuous_gSq_amb {N : ℕ} : Continuous (fun q : Amb N => gSq q) := by
  have h : ∀ j : GIdx N, Continuous (fun q : Amb N => ‖q.2 j‖ ^ 2) := fun j =>
    (((continuous_apply j).comp continuous_snd).norm).pow 2
  simpa only [gSq] using continuous_finsetSum Finset.univ (fun j _ => h j)

/-- The elementary bound `1/(n+1) ≤ 1` for `n : ℕ`. -/
lemma one_div_nat_succ_le_one (n : ℕ) : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith
  calc (1:ℝ)/((n:ℝ)+1) ≤ (1:ℝ)/1 := by gcongr
    _ = 1 := by norm_num

/-! ### Convexity of the constraints defining the sets `E n` -/

/-- Convexity of the constraint `gSq · ≤ M + δ`. -/
lemma convex_setOf_gSq_le {N : ℕ} (M δ : ℝ) : Convex ℝ {q : Amb N | gSq q ≤ M + δ} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  have hx' : gSq x ≤ M + δ := hx
  have hy' : gSq y ≤ M + δ := hy
  change gSq (a • x + b • y) ≤ M + δ
  have h1 : ∀ j : GIdx N, ‖(a • x + b • y).2 j‖ ^ 2 ≤ a * ‖x.2 j‖ ^ 2 + b * ‖y.2 j‖ ^ 2 := by
    intro j
    have h2 : (a • x + b • y).2 j = a • x.2 j + b • y.2 j := by
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply]
    rw [h2]
    have h3 : ‖a • x.2 j + b • y.2 j‖ ≤ a * ‖x.2 j‖ + b * ‖y.2 j‖ := by
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg hb]
    have h4 : 0 ≤ a * ‖x.2 j‖ + b * ‖y.2 j‖ := by positivity
    have h5 : (a * ‖x.2 j‖ + b * ‖y.2 j‖) ^ 2 ≤ a * ‖x.2 j‖ ^ 2 + b * ‖y.2 j‖ ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖x.2 j‖ - ‖y.2 j‖)), hab]
    nlinarith [h3, h4, h5, norm_nonneg (a • x.2 j + b • y.2 j)]
  have h6 : gSq (a • x + b • y) ≤ a * gSq x + b * gSq y := by
    simp only [gSq]
    calc ∑ j : GIdx N, ‖(a • x + b • y).2 j‖ ^ 2
        ≤ ∑ j : GIdx N, (a * ‖x.2 j‖ ^ 2 + b * ‖y.2 j‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => h1 j)
      _ = a * (∑ j : GIdx N, ‖x.2 j‖ ^ 2) + b * (∑ j : GIdx N, ‖y.2 j‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc gSq (a • x + b • y) ≤ a * gSq x + b * gSq y := h6
    _ ≤ a * (M + δ) + b * (M + δ) := add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hb)
    _ = M + δ := by rw [← add_mul, hab, one_mul]

/-- Convexity of the constraint `‖·.1 - φ‖ ≤ δ`. -/
lemma convex_setOf_norm_fst_sub_le {N : ℕ} (φ : L2 N) (δ : ℝ) :
    Convex ℝ {q : Amb N | ‖q.1 - φ‖ ≤ δ} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  have hx' : ‖x.1 - φ‖ ≤ δ := hx
  have hy' : ‖y.1 - φ‖ ≤ δ := hy
  have hkey : (a • x + b • y).1 - φ = a • (x.1 - φ) + b • (y.1 - φ) := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_sub]
    rw [show a • x.1 - a • φ + (b • y.1 - b • φ) = a • x.1 + b • y.1 - (a • φ + b • φ) from by
        abel]
    rw [← add_smul, hab, one_smul]
  change ‖(a • x + b • y).1 - φ‖ ≤ δ
  rw [hkey]
  calc ‖a • (x.1 - φ) + b • (y.1 - φ)‖ ≤ a * ‖x.1 - φ‖ + b * ‖y.1 - φ‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb]
    _ ≤ a * δ + b * δ := add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hb)
    _ = δ := by rw [← add_mul, hab, one_mul]

/-! ### Extraction from a nested family of closed convex sets -/

/-- **Extraction from a nested family of closed convex sets.**  If `E n` is a
decreasing sequence of nonempty closed convex subsets of `Amb N` which together
meet some sublevel set of the graph norm `hSq`, then the intersection of the
`E n` is nonempty.

The proof uses only the parallelogram law for `hSq` (the square of the Hilbert
norm on the ambient product) and completeness; no weak compactness is involved. -/
lemma exists_mem_iInter_of_nested {N : ℕ} (E : ℕ → Set (Amb N))
    (hne : ∀ n, (E n).Nonempty) (hcl : ∀ n, IsClosed (E n)) (hcv : ∀ n, Convex ℝ (E n))
    (hmono : ∀ ⦃a b : ℕ⦄, a ≤ b → E b ⊆ E a)
    (hbdd : ∃ C, ∀ n, ∃ q ∈ E n, hSq q ≤ C) :
    (⋂ n, E n).Nonempty := by
  have hbddBelow : ∀ n, BddBelow (hSq '' E n) := fun n =>
    ⟨0, by rintro _ ⟨q, -, rfl⟩; exact hSq_nonneg q⟩
  set m : ℕ → ℝ := fun n => sInf (hSq '' E n) with hmdef
  have hm_mono : Monotone m := by
    intro a b hab
    exact csInf_le_csInf (hbddBelow a) ((hne b).image _) (Set.image_mono (hmono hab))
  have hchoice : ∀ n, ∃ q : Amb N, q ∈ E n ∧ hSq q ≤ m n + 1/((n:ℝ)+1) := by
    intro n
    have hlt : sInf (hSq '' E n) < sInf (hSq '' E n) + 1/((n:ℝ)+1) := by
      have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      linarith
    obtain ⟨y, hy, hylt⟩ := (csInf_lt_iff (hbddBelow n) ((hne n).image _)).1 hlt
    obtain ⟨q, hqE, rfl⟩ := hy
    exact ⟨q, hqE, le_of_lt hylt⟩
  choose q hq using hchoice
  have hqmem : ∀ n, q n ∈ E n := fun n => (hq n).1
  have hqbd : ∀ n, hSq (q n) ≤ m n + 1/((n:ℝ)+1) := fun n => (hq n).2
  have hmBdd : BddAbove (Set.range m) := by
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨q', hq'E, hq'C⟩ := hC n
    exact le_trans (csInf_le (hbddBelow n) ⟨q', hq'E, rfl⟩) hq'C
  have hL : Tendsto m atTop (𝓝 (⨆ n, m n)) := tendsto_atTop_ciSup hm_mono hmBdd
  have hkey : ∀ a b : ℕ, a ≤ b →
      hSq (q a - q b) ≤ 2 * (m b - m a) + 2 * (1/((a:ℝ)+1)) + 2 * (1/((b:ℝ)+1)) := by
    intro a b hab
    have hmid : (2:ℝ)⁻¹ • (q a + q b) ∈ E a := by
      have h := hcv a (hqmem a) (hmono hab (hqmem b)) (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = 1)
      convert h using 1
      rw [smul_add]
    have hmin : m a ≤ hSq ((2:ℝ)⁻¹ • (q a + q b)) :=
      csInf_le (hbddBelow a) ⟨_, hmid, rfl⟩
    have hsm := hSq_smul (2:ℝ)⁻¹ (q a + q b)
    have hqab : 4 * m a ≤ hSq (q a + q b) := by
      rw [hsm] at hmin
      nlinarith
    have hpar := hSq_parallelogram (q a) (q b)
    linarith [hpar, hqab, hqbd a, hqbd b]
  have hδle : ∀ k N : ℕ, N ≤ k → 1/((k:ℝ)+1) ≤ 1/((N:ℝ)+1) := by
    intro k N hk
    apply one_div_le_one_div_of_le (by positivity)
    have : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hmain : ∀ k l N : ℕ, k ≤ l → N ≤ k → N ≤ l →
      hSq (q k - q l) ≤ 2 * ((⨆ n, m n) - m N) + 4 * (1/((N:ℝ)+1)) := by
    intro k l N hkl hk hl
    have h1 := hkey k l hkl
    have h2 : m l ≤ ⨆ n, m n := le_ciSup hmBdd l
    have h3 : m N ≤ m k := hm_mono hk
    have h4 := hδle l N hl
    have h5 := hδle k N hk
    linarith
  have hcauchy : CauchySeq q := by
    rw [cauchySeq_iff_le_tendsto_0]
    refine ⟨fun N => Real.sqrt (2 * ((⨆ n, m n) - m N) + 4 * (1/((N:ℝ)+1))), ?_, ?_, ?_⟩
    · intro N; exact Real.sqrt_nonneg _
    · intro n mm N hn hm
      have hsqrt : Real.sqrt (hSq (q n - q mm)) ≤
          Real.sqrt (2 * ((⨆ n, m n) - m N) + 4 * (1/((N:ℝ)+1))) := by
        apply Real.sqrt_le_sqrt
        rcases le_total n mm with h | h
        · exact hmain n mm N h hn hm
        · have h1 := hmain mm n N h hm hn
          rwa [show q mm - q n = -(q n - q mm) from by abel, hSq_neg] at h1
      have hdist : dist (q n) (q mm) ≤ Real.sqrt (hSq (q n - q mm)) := by
        rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
        exact Real.sqrt_le_sqrt (norm_sq_le_hSq _)
      exact hdist.trans hsqrt
    · have h1 : Tendsto (fun N : ℕ => (⨆ n, m n) - m N) atTop (𝓝 0) := by
        have := hL.const_sub (⨆ n, m n)
        simpa using this
      have h2 : Tendsto (fun N : ℕ => 4 * (1/((N:ℝ)+1))) atTop (𝓝 0) := by
        have h0 : Tendsto (fun N : ℕ => (1:ℝ)/((N:ℝ)+1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h0.const_mul 4
      have h3 : Tendsto (fun N : ℕ => 2 * ((⨆ n, m n) - m N) + 4 * (1/((N:ℝ)+1)))
          atTop (𝓝 0) := by
        have := (h1.const_mul 2).add h2
        simpa using this
      have h4 := (Real.continuous_sqrt.tendsto 0).comp h3
      simpa [Function.comp_def] using h4
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨v, Set.mem_iInter.2 fun n => ?_⟩
  exact (hcl n).mem_of_tendsto hv (eventually_atTop.2 ⟨n, fun k hk => hmono hk (hqmem k)⟩)

/-! ### The absolute value on the energy space -/

theorem exists_abs_point {N : ℕ} {L : ℝ} (p : Hsub N L) :
    ∃ q : Hsub N L,
      AEEq N (q : Amb N).1 (fun x => |((p : Amb N).1 : Conf N → ℝ) x|) ∧
      gSq (q : Amb N) ≤ gSq (p : Amb N) := by
  obtain ⟨Φ, hΦae, hΦnorm, hΦlip⟩ := exists_lp_abs N
  -- approximants of `p` by graph points of test functions
  have hF : ∀ n : ℕ, ∃ F : testSub N L,
      hSq (graphPoint N L F - (p : Amb N)) ≤ 1/((n:ℝ)+1) :=
    fun n => Work.BoseSym.Basic.exists_graphPoint_close p (by positivity)
  choose F hFspec using hF
  set φ : L2 N := Φ (p : Amb N).1 with hφdef
  set M : ℝ := gSq (p : Amb N) with hMdef
  have hδpos : ∀ n : ℕ, (0:ℝ) < 1/((n:ℝ)+1) := fun n => by positivity
  have hnorm : ∀ n : ℕ, ‖graphPoint N L (F n) - (p : Amb N)‖ ≤ Real.sqrt (1/((n:ℝ)+1)) := by
    intro n
    calc ‖graphPoint N L (F n) - (p : Amb N)‖
        = Real.sqrt (‖graphPoint N L (F n) - (p : Amb N)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (hSq (graphPoint N L (F n) - (p : Amb N))) :=
          Real.sqrt_le_sqrt (norm_sq_le_hSq _)
      _ ≤ Real.sqrt (1/((n:ℝ)+1)) := Real.sqrt_le_sqrt (hFspec n)
  have hsqrt0 : Tendsto (fun n : ℕ => Real.sqrt (1/((n:ℝ)+1))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def] using h1
  have hgtend : Tendsto (fun n : ℕ => graphPoint N L (F n)) atTop (𝓝 (p : Amb N)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hnorm hsqrt0
  have hconv1 : Tendsto (fun n : ℕ => (graphPoint N L (F n)).1) atTop (𝓝 (p : Amb N).1) :=
    continuous_fst.tendsto _ |>.comp hgtend
  have hconv2 : Tendsto (fun n : ℕ => gSq (graphPoint N L (F n))) atTop (𝓝 M) := by
    have h := (continuous_gSq_amb.tendsto (p : Amb N)).comp hgtend
    simpa [hMdef, Function.comp_def] using h
  -- the nested family of closed convex sets
  let E : ℕ → Set (Amb N) := fun n =>
    ((Hsub N L : Set (Amb N)) ∩ {q : Amb N | ‖q.1 - φ‖ ≤ 1/((n:ℝ)+1)}) ∩
      {q : Amb N | gSq q ≤ M + 1/((n:ℝ)+1)}
  have hE1 : ∀ (n : ℕ) (q : Amb N), q ∈ E n → q ∈ Hsub N L := fun n q hq => hq.1.1
  have hE2 : ∀ (n : ℕ) (q : Amb N), q ∈ E n → ‖q.1 - φ‖ ≤ 1/((n:ℝ)+1) := fun n q hq => hq.1.2
  have hE3 : ∀ (n : ℕ) (q : Amb N), q ∈ E n → gSq q ≤ M + 1/((n:ℝ)+1) := fun n q hq => hq.2
  have hEne : ∀ n, (E n).Nonempty := by
    intro n
    have h1 : ∀ᶠ k in atTop, ‖(graphPoint N L (F k)).1 - (p : Amb N).1‖ < 1/((n:ℝ)+1) := by
      have ht : Tendsto (fun k : ℕ => ‖(graphPoint N L (F k)).1 - (p : Amb N).1‖)
          atTop (𝓝 0) := by
        have h := hconv1.sub (tendsto_const_nhds (x := (p : Amb N).1))
        simpa using h.norm
      exact ht.eventually_lt_const (hδpos n)
    have h2 : ∀ᶠ k in atTop, gSq (graphPoint N L (F k)) < M + 1/((n:ℝ)+1) :=
      hconv2.eventually_lt_const (by linarith [hδpos n])
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨q, hqae, hqg⟩ := exists_absPoint_graphPoint (F k)
    refine ⟨(q : Amb N), ⟨⟨q.2, ?_⟩, ?_⟩⟩
    · have hqeq : (q : Amb N).1 = Φ ((graphPoint N L (F k)).1) := by
        refine Lp.ext ?_
        have hA : ((q : Amb N).1 : Conf N → ℝ) =ᵐ[volC N]
            fun x => |(F k : Conf N → ℝ) x| := hqae
        have hB : ((Φ ((graphPoint N L (F k)).1) : L2 N) : Conf N → ℝ) =ᵐ[volC N]
            fun x => |((graphPoint N L (F k)).1 : Conf N → ℝ) x| := hΦae _
        have hC : (((graphPoint N L (F k)).1 : L2 N) : Conf N → ℝ) =ᵐ[volC N]
            (F k : Conf N → ℝ) :=
          MemLp.coeFn_toLp (memLp_of_contDiff_hasCompactSupport (F k).2.1
            (hasCompactSupport_of_testFun (F k).2))
        have hD : (fun x => |((graphPoint N L (F k)).1 : Conf N → ℝ) x|) =ᵐ[volC N]
            (fun x => |(F k : Conf N → ℝ) x|) := hC.mono (fun x hx => by simp only [hx])
        exact ((hB.trans hD).trans hA.symm).symm
      change ‖(q : Amb N).1 - φ‖ ≤ 1/((n:ℝ)+1)
      rw [hqeq]
      calc ‖Φ ((graphPoint N L (F k)).1) - φ‖
          = ‖Φ ((graphPoint N L (F k)).1) - Φ ((p : Amb N).1)‖ := by rw [hφdef]
        _ ≤ ‖(graphPoint N L (F k)).1 - (p : Amb N).1‖ := hΦlip _ _
        _ ≤ 1/((n:ℝ)+1) := le_of_lt hk1
    · exact hqg.trans (le_of_lt hk2)
  have hEclosed : ∀ n, IsClosed (E n) := by
    intro n
    have h1 : IsClosed (Hsub N L : Set (Amb N)) := Submodule.isClosed_topologicalClosure _
    have h2 : IsClosed {q : Amb N | ‖q.1 - φ‖ ≤ 1/((n:ℝ)+1)} :=
      isClosed_le ((continuous_fst.sub continuous_const).norm) continuous_const
    have h3 : IsClosed {q : Amb N | gSq q ≤ M + 1/((n:ℝ)+1)} :=
      isClosed_le continuous_gSq_amb continuous_const
    exact (h1.inter h2).inter h3
  have hEconv : ∀ n, Convex ℝ (E n) := fun n =>
    ((Submodule.convex (Hsub N L)).inter (convex_setOf_norm_fst_sub_le φ _)).inter
      (convex_setOf_gSq_le M _)
  have hEmono : ∀ ⦃a b : ℕ⦄, a ≤ b → E b ⊆ E a := by
    intro a b hab q hq
    have hδ : 1/((b:ℝ)+1) ≤ 1/((a:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
      linarith
    refine ⟨⟨hE1 b q hq, le_trans (hE2 b q hq) hδ⟩, ?_⟩
    calc gSq q ≤ M + 1/((b:ℝ)+1) := hE3 b q hq
      _ ≤ M + 1/((a:ℝ)+1) := by linarith
  have hEbdd : ∃ C, ∀ n, ∃ q ∈ E n, hSq q ≤ C := by
    refine ⟨(‖φ‖ + 1)^2 + (M + 1), fun n => ?_⟩
    obtain ⟨q, hq⟩ := hEne n
    refine ⟨q, hq, ?_⟩
    have h1 : ‖q.1‖ ≤ ‖φ‖ + 1 := by
      have h2 : ‖q.1 - φ‖ ≤ 1 := by
        refine le_trans (hE2 n q hq) ?_
        exact one_div_nat_succ_le_one n
      calc ‖q.1‖ ≤ ‖q.1 - φ‖ + ‖φ‖ := by
            have h3 := norm_add_le (q.1 - φ) φ
            rwa [sub_add_cancel] at h3
        _ ≤ 1 + ‖φ‖ := by linarith
        _ = ‖φ‖ + 1 := by ring
    have h2 : gSq q ≤ M + 1 := by
      refine le_trans (hE3 n q hq) ?_
      have h3 : 1/((n:ℝ)+1) ≤ 1 := one_div_nat_succ_le_one n
      linarith
    simp only [hSq, l2Sq]
    nlinarith [h1, h2, norm_nonneg q.1]
  obtain ⟨v, hv⟩ := exists_mem_iInter_of_nested E hEne hEclosed hEconv hEmono hEbdd
  have hv' : ∀ n, v ∈ E n := Set.mem_iInter.1 hv
  have hvH : v ∈ Hsub N L := hE1 0 v (hv' 0)
  have hv1 : v.1 = φ := by
    have h : ‖v.1 - φ‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      exact le_trans (hE2 n v (hv' n)) (by linarith)
    exact sub_eq_zero.mp (norm_eq_zero.mp h)
  have hgSq : gSq v ≤ M := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact le_trans (hE3 n v (hv' n)) (by linarith)
  refine ⟨⟨v, hvH⟩, ?_, ?_⟩
  · show AEEq N v.1 (fun x => |((p : Amb N).1 : Conf N → ℝ) x|)
    rw [hv1]
    exact hΦae (p : Amb N).1
  · show gSq v ≤ gSq (p : Amb N)
    rw [← hMdef]
    exact hgSq

end

end Work.BoseSym.Abs
