import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.wt_pow_le_monomialSum
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.conv_l2_sq_le
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.seriesFun_mul
import Submission.Work.Diff.STE.elliptic_lower
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.Comp.phi_derivBound
import Submission.Work.Diff.STE.Comp.summable_wt_fourierCoeff
import Submission.Work.Diff.STE.Comp.weighted_lp_le
import Submission.Work.Diff.STE.Comp.young_conv_lp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Moser composition estimate `CSq s (Φ ∘ seriesFun c) ≤ C (1 + CSq s c)`

This file proves `Work.Diff.STE.CSq_comp_le` (design note `DESIGN.md`, item A7): for a smooth
`Φ : ℂ → ℂ`, a coefficient family `γ` with `CSq ρ γ ≤ B²` (`2ρ > card ι`, so that the series
`v = seriesFun γ` is bounded by `C·B` in sup-norm and `γ ∈ ℓ¹`) and all moments summable, the
composition `Φ ∘ v` again has finite weighted `ℓ²`-Fourier coefficients, bounded by a constant
(depending only on `Φ, B, s, ρ, ι`) times `1 + CSq s γ`.

The strategy (Moser's composition estimate in the torus/Fourier setting):

* **Faà di Bruno** (`faaDiBruno_pdVec`): for an ordered partition `π` of the `s` coordinate
  directions into blocks of sizes `β_m`, the term of `∂^s (Φ ∘ v)` belonging to `π` is
  `(D^{π.length}Φ)(v x)(w_1, …, w_r)` where `w_m = ∂^{β_m}_{dirs_m} v` is a directional
  derivative of `v`; by `pdList_seriesFun` each `w_m` is itself the Fourier series of the
  coefficient family `d_m = dmulV dirs_m γ`.
* **Products are convolutions** (`seriesFun_mul`) and **Parseval for series**
  (`ens_integral_normSq_seriesFun`): the `L²`-norm of `∏_m w_m` is the `ℓ²`-norm of the iterated
  convolution `iConv r d`.
* **Young's inequality** (`Work.Diff.STE.Comp.young_conv_lp`) bounds that `ℓ²`-norm by
  `∏_m ‖d_m‖_{p_m}` with `p_m = 2s/(2s-β_m)` (the exponents satisfy `∑_m 1/p_m = r - 1/2`
  because `∑_m β_m = s`).
* **Weighted Hölder** (`Work.Diff.STE.Comp.weighted_lp_le`) turns each factor into
  `(2π)^{β_m} (1+Λ)^{1-β_m/s} (1+CSq s γ)^{β_m/(2s)}` where `Λ = ∑_k ‖γ k‖ ≤ C·B`; the exponents
  telescope: `∏_m … = (2π)^s (1+Λ)^{r-1} (1+CSq s γ)^{1/2}`, linear in `√(CSq s γ)`.

All constants depend only on `B, s, ι` and the sup-norms of the derivatives of `Φ` on a ball.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary helpers -/

/-- The block sizes of an ordered finpartition sum to `n`. -/
lemma sum_partSize {n : ℕ} (c : OrderedFinpartition n) : ∑ m, c.partSize m = n := by
  have h : ∑ m, c.partSize m = Fintype.card ((m : Fin c.length) × Fin (c.partSize m)) := by
    rw [Fintype.card_sigma]
    simp
  rw [h, Fintype.card_congr c.equivSigma, Fintype.card_fin]

/-- `‖k‖ ^ 2 ≤ wt k` for `k : ι → ℤ`: the norm on `ι → ℤ` is the sup norm, and the weight
`wt k = 1 + ∑ kᵢ²` dominates every coordinate square. -/
lemma sq_norm_le_wt (k : ι → ℤ) : (‖k‖ : ℝ) ^ 2 ≤ wt k := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hk : k = 0 := funext fun i => (hι.false i).elim
    rw [hk]
    simp [wt]
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖k i‖)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
    have hmax : ‖k‖ ≤ |((k i₀ : ℤ) : ℝ)| :=
      (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => by
        have h := hi₀ i (Finset.mem_univ i)
        rw [Int.norm_eq_abs] at h
        rwa [Int.norm_eq_abs]
    have h1 : (‖k‖ : ℝ) ^ 2 ≤ (((k i₀ : ℤ) : ℝ)) ^ 2 := by
      have h2 := pow_le_pow_left₀ (norm_nonneg k) hmax 2
      rwa [sq_abs] at h2
    have h3 : (((k i₀ : ℤ) : ℝ)) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i₀)
    simp only [wt]
    linarith [h1, h3]

/-- The Fourier character is periodic. -/
lemma periodic_fourierExp (k : ι → ℤ) : Periodic1 (fourierExp k) := by
  intro i x
  set e : ι → ℝ := Pi.single i 1 with he
  have hsplit : (∑ j, (k j : ℂ) * (((x + e) j : ℝ) : ℂ))
      = (∑ j, (k j : ℂ) * (x j : ℂ)) + (k i : ℂ) := by
    have h1 : ∀ j, (k j : ℂ) * (((x + e) j : ℝ) : ℂ)
        = (k j : ℂ) * (x j : ℂ) + (k j : ℂ) * ((e j : ℝ) : ℂ) := by
      intro j
      rw [Pi.add_apply]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib]
    congr 1
    rw [he, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hfun : fourierExp k (x + e) = fourierExp k x := by
    simp only [fourierExp]
    rw [hsplit]
    rw [show (2 * (Real.pi : ℂ) * Complex.I) * ((∑ j, (k j : ℂ) * (x j : ℂ)) + (k i : ℂ))
        = (2 * (Real.pi : ℂ) * Complex.I) * (∑ j, (k j : ℂ) * (x j : ℂ))
          + (k i : ℤ) * (2 * ↑Real.pi * Complex.I) from by ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simpa [he] using hfun

/-- The Fourier series of a coefficient family is periodic. -/
lemma periodic_seriesFun (γ : (ι → ℤ) → ℂ) : Periodic1 (seriesFun γ) := by
  intro i x
  simp only [seriesFun]
  exact tsum_congr fun k => congrArg (fun z => γ k * z) (periodic_fourierExp k i x)

/-- Composition with a periodic function is periodic. -/
lemma periodic_comp {Φ : ℂ → ℂ} {v : (ι → ℝ) → ℂ} (hv : Periodic1 v) :
    Periodic1 (fun x => Φ (v x)) := fun i x => by
  simp only [Function.comp_apply]
  rw [hv i x]

/-! ## Faà di Bruno -/

/-- **Faà di Bruno formula**, evaluated at a tuple of coordinate directions of the torus.
The `s`-th directional derivative of `Φ ∘ v` along the directions `l` is the sum over ordered
partitions `π` of the position set `{0, …, s-1}` of `(D^{π.length}Φ)(v x)` applied to the block
derivatives `∂^{π.partSize m}_{l ∘ π.emb m} v (x)`. -/
theorem faaDiBruno_pdVec (s : ℕ) (Φ : ℂ → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (v : (ι → ℝ) → ℂ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : ι → ℝ) (l : Fin s → ι) :
    pdVec s l (fun y => Φ (v y)) x =
      ∑ c : OrderedFinpartition s,
        (iteratedFDeriv ℝ c.length Φ (v x))
          (fun m => pdVec (c.partSize m) (fun i => l (c.emb m i)) v x) := by
  have hid := Comp.pdVec_eq_iteratedFDeriv s (fun y => Φ (v y)) (hΦ.comp hv) x l
  rw [hid]
  have hcomp : HasFTaylorSeriesUpToOn (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun y => Φ (v y))
      (fun y => ((ftaylorSeries ℝ Φ) (v y)).taylorComp ((ftaylorSeries ℝ v) y)) Set.univ :=
    ((hΦ.ftaylorSeries).hasFTaylorSeriesUpToOn Set.univ).comp
      ((hv.ftaylorSeries).hasFTaylorSeriesUpToOn Set.univ) (Set.mapsTo_univ _ _)
  have h2 := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := s) (by simp) uniqueDiffOn_univ
    (Set.mem_univ x)
  rw [iteratedFDerivWithin_univ] at h2
  rw [← h2]
  simp only [FormalMultilinearSeries.taylorComp]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]
  congr 1
  funext m
  exact (Comp.pdVec_eq_iteratedFDeriv (c.partSize m) v hv x (fun i => l (c.emb m i))).symm

/-! ## The coefficient families of the block derivatives -/

/-- The coefficient family of the block derivative attached to the block `m` of the ordered
partition `c` and the direction tuple `l`.  The derivative `∂^{β}_{l ∘ c.emb m} (seriesFun γ)`
is the Fourier series of this family. -/
def blockFam (γ : (ι → ℤ) → ℂ) {s : ℕ} (l : Fin s → ι) (c : OrderedFinpartition s)
    (m : Fin c.length) : (ι → ℤ) → ℂ :=
  dmulV (List.ofFn fun i => l (c.emb m i)) γ

/-- Sharp bound for the multiplier of an iterated directional derivative: the norm of
`dmulV l γ k` is at most `(2π ‖k‖)^{|l|} ‖γ k‖`. -/
theorem norm_dmulV_le_norm (l : List ι) (γ : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    ‖dmulV l γ k‖ ≤ (2 * Real.pi * ‖k‖) ^ l.length * ‖γ k‖ := by
  induction l with
  | nil => simp [dmulV]
  | cons i l ih =>
    rw [dmulV_cons]
    have h1 : |((k i : ℤ) : ℝ)| ≤ ‖k‖ := by
      have h := norm_le_pi_norm k i
      rwa [Int.norm_eq_abs] at h
    have h2 : ‖dmul i (dmulV l γ) k‖
        = 2 * Real.pi * |((k i : ℤ) : ℝ)| * ‖dmulV l γ k‖ := by
      have h0 : dmul i (dmulV l γ) k
          = (2 * Real.pi * Complex.I * (k i : ℂ)) * (dmulV l γ k) := rfl
      rw [h0, norm_mul]
      congr 1
      rw [show (2 * Real.pi * Complex.I * (k i : ℂ))
          = (((2 * Real.pi * ((k i : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp
    rw [h2, List.length_cons, pow_succ]
    calc 2 * Real.pi * |((k i : ℤ) : ℝ)| * ‖dmulV l γ k‖
        ≤ 2 * Real.pi * ‖k‖ * ((2 * Real.pi * ‖k‖) ^ l.length * ‖γ k‖) := by gcongr
      _ = (2 * Real.pi * ‖k‖) ^ l.length * (2 * Real.pi * ‖k‖) * ‖γ k‖ := by ring

lemma blockFam_norm_le (γ : (ι → ℤ) → ℂ) {s : ℕ} (l : Fin s → ι) (c : OrderedFinpartition s)
    (m : Fin c.length) (k : ι → ℤ) :
    ‖blockFam γ l c m k‖ ≤ (2 * Real.pi * ‖k‖) ^ (c.partSize m) * ‖γ k‖ := by
  simpa only [blockFam, List.length_ofFn] using
    norm_dmulV_le_norm (List.ofFn fun i => l (c.emb m i)) γ k

lemma blockFam_seriesFun (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)
    {s : ℕ} (l : Fin s → ι) (c : OrderedFinpartition s) (m : Fin c.length) (x : ι → ℝ) :
    pdVec (c.partSize m) (fun i => l (c.emb m i)) (seriesFun γ) x
      = seriesFun (blockFam γ l c m) x :=
  pdList_seriesFun _ _ hmom x

/-! ## Summability of the block families -/

/-- A moment of `γ` dominates any polynomial weight in `‖k‖`. -/
lemma summable_moment_mul (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖) (M : ℕ) :
    Summable fun k : ι → ℤ => (1 + ‖k‖) ^ M * ‖γ k‖ := by
  have hwt : ∀ k : ι → ℤ, (1 + ‖k‖) ^ M ≤ (2 : ℝ) ^ M * (wt k) ^ M := by
    intro k
    have h1 : ‖k‖ ≤ wt k := by
      have h2 : ‖k‖ = Real.sqrt (‖k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg k)).symm
      rw [h2]
      exact (Real.sqrt_le_sqrt (sq_norm_le_wt k)).trans
        (Real.sqrt_le_self_iff.mpr (Or.inr (wt_one_le k)))
    have h3 : (1 : ℝ) ≤ wt k := wt_one_le k
    have h4 : (1 + ‖k‖) ≤ 2 * wt k := by linarith
    calc (1 + ‖k‖) ^ M ≤ (2 * wt k) ^ M := pow_le_pow_left₀ (by positivity) h4 M
      _ = (2 : ℝ) ^ M * (wt k) ^ M := by rw [mul_pow]
  refine Summable.of_nonneg_of_le
    (g := fun k : ι → ℤ => (1 + ‖k‖) ^ M * ‖γ k‖)
    (f := fun k : ι → ℤ => (2 : ℝ) ^ M * ((wt k) ^ M * ‖γ k‖))
    (fun k => by positivity) (fun k => ?_) ((hmom M).mul_left ((2 : ℝ) ^ M))
  exact (mul_le_mul_of_nonneg_right (hwt k) (norm_nonneg _)).trans_eq (by ring)

lemma summable_blockFam_one (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)
    {s : ℕ} (l : Fin s → ι) (c : OrderedFinpartition s) (m : Fin c.length) :
    Summable fun k : ι → ℤ => ‖blockFam γ l c m k‖ := by
  refine Summable.of_nonneg_of_le
    (g := fun k : ι → ℤ => ‖blockFam γ l c m k‖)
    (f := fun k : ι → ℤ => (2 * Real.pi) ^ (c.partSize m) * ((1 + ‖k‖) ^ (c.partSize m) * ‖γ k‖))
    (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_moment_mul γ hmom (c.partSize m)).mul_left ((2 * Real.pi) ^ (c.partSize m)))
  calc ‖blockFam γ l c m k‖ ≤ (2 * Real.pi * ‖k‖) ^ (c.partSize m) * ‖γ k‖ :=
        blockFam_norm_le γ l c m k
    _ = (2 * Real.pi) ^ (c.partSize m) * ((‖k‖) ^ (c.partSize m) * ‖γ k‖) := by rw [mul_pow]; ring
    _ ≤ (2 * Real.pi) ^ (c.partSize m) * ((1 + ‖k‖) ^ (c.partSize m) * ‖γ k‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg k) (by linarith) _

/-- Summability of the `ℓ^p`-norm of a block family. -/
lemma summable_blockFam_rpow (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)
    (hΛ : Summable fun k : ι → ℤ => ‖γ k‖)
    {s : ℕ} (l : Fin s → ι) (c : OrderedFinpartition s) (m : Fin c.length)
    (p : ℝ) (hp : 1 ≤ p) :
    Summable fun k : ι → ℤ => ‖blockFam γ l c m k‖ ^ p := by
  set L : ℝ := (1 : ℝ) + ∑' k : ι → ℤ, ‖γ k‖ with hL
  have hL1 : 1 ≤ L := by
    rw [hL]; exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hbdd : ∀ k : ι → ℤ, ‖γ k‖ ≤ L := by
    intro k; rw [hL]
    exact (hΛ.le_tsum k fun j _ => norm_nonneg _).trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (c.partSize m : ℝ) * p ≤ M :=
    ⟨⌈(c.partSize m : ℝ) * p⌉₊, Nat.le_ceil _⟩
  have hpt : ∀ k : ι → ℤ, ‖blockFam γ l c m k‖ ^ p
      ≤ ((2 * Real.pi) ^ (M : ℝ) * L ^ (p - 1)) * ((1 + ‖k‖) ^ M * ‖γ k‖) := by
    intro k
    have h3 : ‖blockFam γ l c m k‖ ^ p
        ≤ ((2 * Real.pi * ‖k‖) ^ (c.partSize m) * ‖γ k‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (blockFam_norm_le γ l c m k) (by linarith)
    have h4 : ((2 * Real.pi * ‖k‖) ^ (c.partSize m) * ‖γ k‖) ^ p
        = (2 * Real.pi) ^ ((c.partSize m : ℝ) * p)
          * ((‖k‖ : ℝ) ^ ((c.partSize m : ℝ) * p)) * ‖γ k‖ ^ p := by
      have e1 : ((2 * Real.pi * ‖k‖) ^ (c.partSize m) * ‖γ k‖) ^ p
          = ((2 * Real.pi * ‖k‖) ^ (c.partSize m)) ^ p * ‖γ k‖ ^ p :=
        Real.mul_rpow (x := (2 * Real.pi * ‖k‖) ^ (c.partSize m)) (y := ‖γ k‖) (z := p)
          (by positivity) (norm_nonneg _)
      have e2 : ((2 * Real.pi * ‖k‖) ^ (c.partSize m)) ^ p
          = (2 * Real.pi) ^ ((c.partSize m : ℝ) * p)
            * ((‖k‖ : ℝ) ^ ((c.partSize m : ℝ) * p)) := by
        rw [mul_pow,
          Real.mul_rpow (x := (2 * Real.pi) ^ (c.partSize m)) (y := ‖k‖ ^ (c.partSize m))
            (z := p) (by positivity) (by positivity),
          ← Real.rpow_natCast (2 * Real.pi) (c.partSize m),
          ← Real.rpow_natCast (‖k‖) (c.partSize m),
          ← Real.rpow_mul (x := 2 * Real.pi) (by positivity) (c.partSize m : ℝ) p,
          ← Real.rpow_mul (x := ‖k‖) (norm_nonneg k) (c.partSize m : ℝ) p]
      rw [e1, e2]
    refine h3.trans ?_
    rw [h4]
    have h5 : (2 * Real.pi) ^ ((c.partSize m : ℝ) * p) ≤ (2 * Real.pi) ^ (M : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hM
    have h6 : (‖k‖ : ℝ) ^ ((c.partSize m : ℝ) * p) ≤ (1 + ‖k‖) ^ M := by
      have h7 : (‖k‖ : ℝ) ^ ((c.partSize m : ℝ) * p) ≤ (1 + ‖k‖) ^ ((c.partSize m : ℝ) * p) :=
        Real.rpow_le_rpow (norm_nonneg k) (by linarith) (by positivity)
      rw [← Real.rpow_natCast (1 + ‖k‖) M]
      exact h7.trans (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg k]) hM)
    have h11 : ‖γ k‖ ^ p ≤ L ^ (p - 1) * ‖γ k‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (γ k)) with h | h
      · rw [← h, Real.zero_rpow (by linarith : p ≠ 0)]
        simp
      · have hp1 : 0 ≤ p - 1 := by linarith
        have h1 : ‖γ k‖ ^ p = ‖γ k‖ * ‖γ k‖ ^ (p - 1) := by
          have hp : p = (p - 1) + 1 := by ring
          rw [hp, Real.rpow_add h, Real.rpow_one]
          ring
        rw [h1]
        calc ‖γ k‖ * ‖γ k‖ ^ (p - 1) ≤ ‖γ k‖ * L ^ (p - 1) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt h) (hbdd k) hp1)
                (le_of_lt h)
          _ = L ^ (p - 1) * ‖γ k‖ := by ring
    calc (2 * Real.pi) ^ ((c.partSize m : ℝ) * p) * (‖k‖ : ℝ) ^ ((c.partSize m : ℝ) * p)
          * ‖γ k‖ ^ p
        ≤ (2 * Real.pi) ^ (M : ℝ) * (1 + ‖k‖) ^ M * (L ^ (p - 1) * ‖γ k‖) := by
          gcongr
      _ = ((2 * Real.pi) ^ (M : ℝ) * L ^ (p - 1)) * ((1 + ‖k‖) ^ M * ‖γ k‖) := by ring
  refine Summable.of_nonneg_of_le
    (g := fun k : ι → ℤ => ‖blockFam γ l c m k‖ ^ p)
    (f := fun k : ι → ℤ =>
      ((2 * Real.pi) ^ (M : ℝ) * L ^ (p - 1)) * ((1 + ‖k‖) ^ M * ‖γ k‖))
    (fun k => Real.rpow_nonneg (norm_nonneg _) p) hpt ?_
  exact (summable_moment_mul γ hmom M).mul_left _

/-! ## The Young exponents attached to the blocks of a partition -/

/-- The Young exponent attached to a block of size `β`: `p = 2s/(2s-β)`. -/
def yExp (s β : ℕ) : ℝ := (2 * (s : ℝ)) / (2 * (s : ℝ) - (β : ℝ))

lemma yExp_denom_pos (s : ℕ) (hs : 0 < s) (β : ℕ) (hβ : β ≤ s) :
    0 < 2 * (s : ℝ) - (β : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : (β : ℝ) ≤ s := by exact_mod_cast hβ
  linarith

lemma one_le_yExp (s : ℕ) (hs : 0 < s) (β : ℕ) (hβ : β ≤ s) : 1 ≤ yExp s β := by
  rw [yExp, le_div_iff₀ (yExp_denom_pos s hs β hβ)]
  linarith

lemma yExp_inv (s β : ℕ) : (yExp s β)⁻¹ = (2 * (s : ℝ) - (β : ℝ)) / (2 * (s : ℝ)) := by
  rw [yExp, inv_div]

lemma yExp_eq (s β : ℕ) : yExp s β = (2 * (s : ℝ)) / (2 * (s : ℝ) - (β : ℝ)) := rfl

lemma yExp_ne_zero (s : ℕ) (hs : 0 < s) (β : ℕ) (hβ : β ≤ s) : yExp s β ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_yExp s hs β hβ))

lemma sum_yExp_inv (s : ℕ) (hs : 0 < s) (c : OrderedFinpartition s) :
    ∑ m, (yExp s (c.partSize m))⁻¹ = (c.length : ℝ) - 1 / 2 := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  have h1 : ∀ m, (yExp s (c.partSize m))⁻¹ = 1 - (c.partSize m : ℝ) / (2 * (s : ℝ)) := by
    intro m
    rw [yExp_inv]
    field_simp
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div, Fintype.card_fin,
    show ∑ m, (c.partSize m : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, sum_partSize c]]
  field_simp

/-! ## Summability of the sharp majorant -/

lemma summable_majorant_rpow (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)
    (hΛ : Summable fun k : ι → ℤ => ‖γ k‖) (β : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    Summable fun k : ι → ℤ => ((‖k‖ : ℝ) ^ β * ‖γ k‖) ^ p := by
  set L : ℝ := (1 : ℝ) + ∑' k : ι → ℤ, ‖γ k‖ with hL
  have hbdd : ∀ k : ι → ℤ, ‖γ k‖ ≤ L := by
    intro k; rw [hL]
    exact (hΛ.le_tsum k fun j _ => norm_nonneg _).trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (β : ℝ) * p ≤ M := ⟨⌈(β : ℝ) * p⌉₊, Nat.le_ceil _⟩
  have hpt : ∀ k : ι → ℤ, ((‖k‖ : ℝ) ^ β * ‖γ k‖) ^ p
      ≤ L ^ (p - 1) * ((1 + ‖k‖) ^ M * ‖γ k‖) := by
    intro k
    have e : ((‖k‖ : ℝ) ^ β * ‖γ k‖) ^ p
        = (‖k‖ : ℝ) ^ ((β : ℝ) * p) * ‖γ k‖ ^ p := by
      rw [Real.mul_rpow (x := (‖k‖ : ℝ) ^ β) (y := ‖γ k‖) (z := p) (by positivity) (norm_nonneg _),
        ← Real.rpow_natCast (‖k‖) β, ← Real.rpow_mul (x := ‖k‖) (norm_nonneg k) (β : ℝ) p]
    rw [e]
    have h6 : (‖k‖ : ℝ) ^ ((β : ℝ) * p) ≤ (1 + ‖k‖) ^ M := by
      have h7 : (‖k‖ : ℝ) ^ ((β : ℝ) * p) ≤ (1 + ‖k‖) ^ ((β : ℝ) * p) :=
        Real.rpow_le_rpow (norm_nonneg k) (by linarith) (by positivity)
      rw [← Real.rpow_natCast (1 + ‖k‖) M]
      exact h7.trans (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg k]) hM)
    have h11 : ‖γ k‖ ^ p ≤ L ^ (p - 1) * ‖γ k‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (γ k)) with h | h
      · rw [← h, Real.zero_rpow (by linarith : p ≠ 0)]
        simp
      · have hp1 : 0 ≤ p - 1 := by linarith
        have h1 : ‖γ k‖ ^ p = ‖γ k‖ * ‖γ k‖ ^ (p - 1) := by
          have hp' : p = (p - 1) + 1 := by ring
          rw [hp', Real.rpow_add h, Real.rpow_one]
          ring
        rw [h1]
        calc ‖γ k‖ * ‖γ k‖ ^ (p - 1) ≤ ‖γ k‖ * L ^ (p - 1) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt h) (hbdd k) hp1)
                (le_of_lt h)
          _ = L ^ (p - 1) * ‖γ k‖ := by ring
    calc (‖k‖ : ℝ) ^ ((β : ℝ) * p) * ‖γ k‖ ^ p
        ≤ (1 + ‖k‖) ^ M * (L ^ (p - 1) * ‖γ k‖) := by gcongr
      _ = L ^ (p - 1) * ((1 + ‖k‖) ^ M * ‖γ k‖) := by ring
  refine Summable.of_nonneg_of_le
    (g := fun k : ι → ℤ => ((‖k‖ : ℝ) ^ β * ‖γ k‖) ^ p)
    (f := fun k : ι → ℤ => L ^ (p - 1) * ((1 + ‖k‖) ^ M * ‖γ k‖))
    (fun k => Real.rpow_nonneg (by positivity) p) hpt ?_
  exact (summable_moment_mul γ hmom M).mul_left _

/-! ## Products of series -/

/-- The ℓ¹-norm of the iterated convolution is summable when all factors are. -/
lemma summable_iConv : ∀ (r : ℕ) (d : Fin r → (ι → ℤ) → ℂ),
    (∀ m, Summable fun k : ι → ℤ => ‖d m k‖) →
    Summable fun k : ι → ℤ => ‖Comp.iConv r d k‖ := by
  intro r
  induction r with
  | zero => intro d hd; simp [Comp.iConv]
  | succ r ih =>
    intro d hd
    match r with
    | 0 => simpa [Comp.iConv] using hd 0
    | (n + 1) =>
      rw [show Comp.iConv (n + 1 + 1) d
          = conv (d 0) (Comp.iConv (n + 1) (fun i => d i.succ)) from rfl]
      exact summable_conv_norm _ _ (hd 0) (ih _ fun i => hd i.succ)

/-- The product of the Fourier series of the block families is the Fourier series of the
iterated convolution of their coefficient families. -/
lemma prod_seriesFun_iConv : ∀ (r : ℕ) (d : Fin r → (ι → ℤ) → ℂ), 1 ≤ r →
    (∀ m, Summable fun k : ι → ℤ => ‖d m k‖) →
    (fun x => ∏ m, seriesFun (d m) x) = fun x => seriesFun (Comp.iConv r d) x := by
  intro r
  induction r with
  | zero => intro d hr; exact absurd hr (by norm_num)
  | succ r ih =>
    intro d hr hd
    match r with
    | 0 =>
      funext x
      rw [Fin.prod_univ_one]
      rfl
    | (n + 1) =>
      funext x
      rw [Fin.prod_univ_succ]
      have h2 : (∏ m : Fin (n + 1), seriesFun (d m.succ) x)
          = seriesFun (Comp.iConv (n + 1) (fun i => d i.succ)) x :=
        congrFun (ih (fun i => d i.succ) (by omega) (fun i => hd i.succ)) x
      rw [h2]
      rw [seriesFun_mul _ _ (hd 0) (summable_iConv _ _ fun i => hd i.succ)]
      rfl


/-! ## The per-term estimate -/

/-- **Per-term estimate.** The `L²`-norm over the cube of one Faà di Bruno term (a product of
block derivatives of `seriesFun γ`) is bounded by `((2π)^s (1+Λ)^s)^2 (1 + CSq s γ)`, where
`Λ = ∑ ‖γ k‖`. -/
lemma integral_prod_blockFam_le (s : ℕ) (hs : 0 < s) (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)
    (hΛ : Summable fun k : ι → ℤ => ‖γ k‖)
    (hQ : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2)
    (c : OrderedFinpartition s) (l : Fin s → ι) :
    ∫ x in unitCube, ‖∏ m, seriesFun (blockFam γ l c m) x‖ ^ 2
      ≤ (((2 * Real.pi) ^ s * (1 + ∑' k : ι → ℤ, ‖γ k‖) ^ s) ^ 2) * (1 + CSq s γ) := by
  set Λ : ℝ := ∑' k : ι → ℤ, ‖γ k‖ with hΛdef
  set Q : ℝ := ∑' k : ι → ℤ, (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2 with hQdef
  have hΛ0 : (0 : ℝ) ≤ Λ := tsum_nonneg fun k => norm_nonneg (γ k)
  have hQ0 : (0 : ℝ) ≤ Q :=
    tsum_nonneg fun k => mul_nonneg (pow_nonneg (norm_nonneg k) _) (sq_nonneg _)
  have hΛ1 : 1 ≤ 1 + Λ := by linarith
  have hQ_le : Q ≤ CSq s γ := by
    rw [hQdef, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_) hQ (summable_wt_pow_mul_norm_sq γ hmom s)
    have h1 : (‖k‖ : ℝ) ^ (2 * s) ≤ (wt k) ^ s := by
      have h2 : (‖k‖ : ℝ) ^ 2 ≤ wt k := sq_norm_le_wt k
      calc (‖k‖ : ℝ) ^ (2 * s) = ((‖k‖ : ℝ) ^ 2) ^ s := by rw [← pow_mul]
        _ ≤ (wt k) ^ s := pow_le_pow_left₀ (sq_nonneg _) h2 s
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hr : 1 ≤ c.length := c.length_pos hs
  have hd : ∀ m, Summable fun k : ι → ℤ => ‖blockFam γ l c m k‖ :=
    fun m => summable_blockFam_one γ hmom l c m
  have hprod := prod_seriesFun_iConv c.length (blockFam γ l c) hr hd
  have hp1 : ∀ m, 1 ≤ yExp s (c.partSize m) :=
    fun m => one_le_yExp s hs (c.partSize m) (c.partSize_le m)
  have hsum : ∑ m, (yExp s (c.partSize m))⁻¹ = (c.length : ℝ) - 1 / 2 := sum_yExp_inv s hs c
  have hsm : ∀ m, Summable fun k : ι → ℤ => ‖blockFam γ l c m k‖ ^ (yExp s (c.partSize m)) :=
    fun m => summable_blockFam_rpow γ hmom hΛ l c m _ (hp1 m)
  obtain ⟨hsumm2, hyoung⟩ := Comp.young_conv_lp hr (blockFam γ l c)
    (fun m => yExp s (c.partSize m)) hp1 hsum hsm
  have hfac : ∀ m, (∑' k : ι → ℤ, ‖blockFam γ l c m k‖ ^ (yExp s (c.partSize m)))
        ^ ((yExp s (c.partSize m))⁻¹)
      ≤ (2 * Real.pi) ^ (c.partSize m) * (1 + Λ) ^ (1 - (c.partSize m : ℝ) / s)
        * (1 + CSq s γ) ^ ((c.partSize m : ℝ) / (2 * s)) := by
    intro m
    have hβm : c.partSize m ≤ s := c.partSize_le m
    have hmaj : Summable fun k : ι → ℤ =>
        ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)) :=
      summable_majorant_rpow γ hmom hΛ (c.partSize m) _ (hp1 m)
    have hpt : ∀ k : ι → ℤ, ‖blockFam γ l c m k‖ ^ (yExp s (c.partSize m))
        ≤ (2 * Real.pi) ^ ((c.partSize m : ℝ) * (yExp s (c.partSize m)))
          * ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)) := by
      intro k
      have hdom2 : ‖blockFam γ l c m k‖
          ≤ (2 * Real.pi) ^ (c.partSize m) * ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) := by
        have h := blockFam_norm_le γ l c m k
        rw [mul_pow] at h
        calc ‖blockFam γ l c m k‖
            ≤ (2 * Real.pi) ^ (c.partSize m) * (‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖ := h
          _ = (2 * Real.pi) ^ (c.partSize m) * ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) := by ring
      have h := Real.rpow_le_rpow (norm_nonneg _) hdom2
        (x := ‖blockFam γ l c m k‖)
        (y := (2 * Real.pi) ^ (c.partSize m) * ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖))
        (z := yExp s (c.partSize m)) (by linarith [hp1 m])
      rw [Real.mul_rpow (x := (2 * Real.pi) ^ (c.partSize m))
          (y := (‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) (z := yExp s (c.partSize m))
          (by positivity) (by positivity),
        ← Real.rpow_natCast (2 * Real.pi) (c.partSize m),
        ← Real.rpow_mul (x := 2 * Real.pi) (by positivity) (c.partSize m : ℝ)
          (yExp s (c.partSize m))] at h
      exact h
    have hcmp : (∑' k : ι → ℤ, ‖blockFam γ l c m k‖ ^ (yExp s (c.partSize m)))
        ≤ (2 * Real.pi) ^ ((c.partSize m : ℝ) * (yExp s (c.partSize m)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum hpt (hsm m) (hmaj.mul_left _)
    have h2 : ((2 * Real.pi) ^ ((c.partSize m : ℝ) * (yExp s (c.partSize m)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
          ^ ((yExp s (c.partSize m))⁻¹)
        = (2 * Real.pi) ^ (c.partSize m)
          * (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
              ^ ((yExp s (c.partSize m))⁻¹) := by
      rw [Real.mul_rpow (x := (2 * Real.pi) ^ ((c.partSize m : ℝ) * (yExp s (c.partSize m))))
          (y := ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
          (z := (yExp s (c.partSize m))⁻¹) (by positivity)
          (tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (x := 2 * Real.pi) (by positivity) ((c.partSize m : ℝ) * (yExp s (c.partSize m)))
          ((yExp s (c.partSize m))⁻¹)]
      congr 1
      have hyne : yExp s (c.partSize m) ≠ 0 := yExp_ne_zero s hs _ hβm
      field_simp
      rw [Real.rpow_natCast]
    have hstep := (Real.rpow_le_rpow (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _) hcmp
      (y := (2 * Real.pi) ^ ((c.partSize m : ℝ) * (yExp s (c.partSize m)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
      (z := (yExp s (c.partSize m))⁻¹) (inv_nonneg.mpr (by linarith [hp1 m]))).trans (le_of_eq h2)
    have hw := Comp.weighted_lp_le s (c.partSize m) hβm hs γ hΛ hQ
    have heq1 : (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
        = (∑' k : ι → ℤ,
            (‖γ k‖ * (‖k‖ : ℝ) ^ (c.partSize m)) ^ ((2 * (s : ℝ)) / (2 * (s : ℝ) - (c.partSize m : ℝ)))) := by
      refine tsum_congr fun k => ?_
      rw [yExp_eq, mul_comm]
    have hw' : (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (c.partSize m) * ‖γ k‖) ^ (yExp s (c.partSize m)))
          ^ ((yExp s (c.partSize m))⁻¹)
        ≤ (1 + Λ) ^ (1 - (c.partSize m : ℝ) / s) * (1 + Q) ^ ((c.partSize m : ℝ) / (2 * s)) := by
      rw [heq1, yExp_inv]
      exact hw
    have hle1 : (1 + Q) ^ ((c.partSize m : ℝ) / (2 * s))
        ≤ (1 + CSq s γ) ^ ((c.partSize m : ℝ) / (2 * s)) :=
      Real.rpow_le_rpow (by positivity) (by linarith [hQ_le]) (by positivity)
    have hfin : (2 * Real.pi) ^ (c.partSize m)
          * ((1 + Λ) ^ (1 - (c.partSize m : ℝ) / s) * (1 + Q) ^ ((c.partSize m : ℝ) / (2 * s)))
        ≤ (2 * Real.pi) ^ (c.partSize m)
          * ((1 + Λ) ^ (1 - (c.partSize m : ℝ) / s) * (1 + CSq s γ) ^ ((c.partSize m : ℝ) / (2 * s))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg (by linarith [hQ0]) _)) (by positivity)
    refine hstep.trans ((mul_le_mul_of_nonneg_left hw' (by positivity)).trans ?_)
    exact hfin.trans (le_of_eq (by ring))
  have hmul : ∏ m : Fin c.length,
        ((2 * Real.pi) ^ (c.partSize m) * (1 + Λ) ^ (1 - (c.partSize m : ℝ) / s)
          * (1 + CSq s γ) ^ ((c.partSize m : ℝ) / (2 * s)))
      = (2 * Real.pi) ^ s * (1 + Λ) ^ (c.length - 1) * (1 + CSq s γ) ^ (1 / 2 : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have h1 : ∏ m : Fin c.length, (2 * Real.pi) ^ (c.partSize m) = (2 * Real.pi) ^ s := by
      rw [Finset.prod_pow_eq_pow_sum, sum_partSize]
    have h2 : ∏ m : Fin c.length, (1 + Λ) ^ (1 - (c.partSize m : ℝ) / s)
        = (1 + Λ) ^ ((c.length : ℝ) - 1) := by
      rw [← Real.rpow_sum_of_pos (by linarith : (0 : ℝ) < 1 + Λ)]
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div,
        Fintype.card_fin,
        show ∑ m, (c.partSize m : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, sum_partSize c]]
      field_simp
    have h3 : ∏ m : Fin c.length, (1 + CSq s γ) ^ ((c.partSize m : ℝ) / (2 * s))
        = (1 + CSq s γ) ^ (1 / 2 : ℝ) := by
      have hCSq0 : (0 : ℝ) ≤ CSq s γ :=
        tsum_nonneg fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
      rw [← Real.rpow_sum_of_pos (by linarith : (0 : ℝ) < 1 + CSq s γ)]
      congr 1
      rw [← Finset.sum_div,
        show ∑ m, (c.partSize m : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, sum_partSize c]]
      field_simp
    have hc : (↑c.length - 1 : ℝ) = ↑(c.length - 1) := by
      rw [Nat.cast_sub hr, Nat.cast_one]
    rw [h1, h2, h3, hc, Real.rpow_natCast]
  have hy2 : (∑' k : ι → ℤ, ‖Comp.iConv c.length (blockFam γ l c) k‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * Real.pi) ^ s * (1 + Λ) ^ (c.length - 1) * (1 + CSq s γ) ^ (1 / 2 : ℝ) := by
    refine hyoung.trans ?_
    rw [← hmul]
    exact Finset.prod_le_prod₀ (fun m _ => Real.rpow_nonneg (tsum_nonneg fun k =>
      Real.rpow_nonneg (norm_nonneg _) _) _) fun m _ => hfac m
  have hsq : ∑' k : ι → ℤ, ‖Comp.iConv c.length (blockFam γ l c) k‖ ^ 2
      ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + CSq s γ) := by
    set A : ℝ := ∑' k : ι → ℤ, ‖Comp.iConv c.length (blockFam γ l c) k‖ ^ 2 with hA
    have hA0 : 0 ≤ A := tsum_nonneg fun k => sq_nonneg _
    set B : ℝ := (2 * Real.pi) ^ s * (1 + Λ) ^ (c.length - 1) * (1 + CSq s γ) ^ (1 / 2 : ℝ)
      with hB
    have hA_sq : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA0]
    have hZ : ((1 + CSq s γ) ^ (1 / 2 : ℝ)) ^ 2 = 1 + CSq s γ := by
      have hCSq0 : (0 : ℝ) ≤ 1 + CSq s γ := by
        have h0 : (0 : ℝ) ≤ CSq s γ :=
          tsum_nonneg fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
        linarith
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hCSq0]
    have hB_sq : B ^ 2 = ((2 * Real.pi) ^ s * (1 + Λ) ^ (c.length - 1)) ^ 2 * (1 + CSq s γ) := by
      rw [hB, mul_pow, mul_pow, hZ]
    have hAB : A ^ (1 / 2 : ℝ) ≤ B := by rw [hA, hB]; exact hy2
    calc A = (A ^ (1 / 2 : ℝ)) ^ 2 := hA_sq.symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) hAB 2
      _ = ((2 * Real.pi) ^ s * (1 + Λ) ^ (c.length - 1)) ^ 2 * (1 + CSq s γ) := hB_sq
      _ ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + CSq s γ) := by
          have hCSq0' : (0 : ℝ) ≤ 1 + CSq s γ := by
            have h0 : (0 : ℝ) ≤ CSq s γ := le_trans hQ0 hQ_le
            linarith
          refine mul_le_mul_of_nonneg_right ?_ hCSq0'
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hΛ1 ((Nat.sub_le _ _).trans c.length_le))
            (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) s)
  have hpt : ∀ x : ι → ℝ, ‖∏ m, seriesFun (blockFam γ l c m) x‖ ^ 2
      = ‖seriesFun (Comp.iConv c.length (blockFam γ l c)) x‖ ^ 2 := by
    intro x
    rw [show (∏ m, seriesFun (blockFam γ l c m) x)
        = seriesFun (Comp.iConv c.length (blockFam γ l c)) x from congrFun hprod x]
  calc ∫ x in unitCube, ‖∏ m, seriesFun (blockFam γ l c m) x‖ ^ 2
      = ∫ x in unitCube, ‖seriesFun (Comp.iConv c.length (blockFam γ l c)) x‖ ^ 2 := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑' k : ι → ℤ, ‖Comp.iConv c.length (blockFam γ l c) k‖ ^ 2 :=
        ens_integral_normSq_seriesFun _ (summable_iConv _ _ hd)
    _ ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + CSq s γ) := hsq


theorem CSq_comp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s ρ : ℕ) (hρ : Fintype.card ι < 2 * ρ) (hρs : ρ ≤ s)
    (Φ : ℂ → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ,
      (∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) →
      Work.Diff.STE.CSq ρ c ≤ B ^ 2 →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s *
        ‖Work.Diff.STE.fourierCoeff (fun x => Φ (Work.Diff.STE.seriesFun c x)) k‖ ^ 2) ∧
      Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff (fun x => Φ (Work.Diff.STE.seriesFun c x)))
        ≤ C * (1 + Work.Diff.STE.CSq s c) := by
  classical
  obtain ⟨C_l1, hC_l1nn, hC_l1⟩ := l1_le_sqrt_CSq (ι := ι) ρ hρ
  obtain ⟨M, hMnn, hM⟩ := Comp.phi_derivBound Φ hΦ (C_l1 * B) s
  obtain ⟨C0, hC0nn, hC0⟩ := CSq_le_ENormSq (ι := ι) s
  set KL : ℝ := 1 + C_l1 * B with hKL
  set K2 : ℝ := ((2 * Real.pi) ^ s * KL ^ s) ^ 2 with hK2
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  set X : ℝ := (Fintype.card (Fin s → ι) : ℝ)
      * ((Fintype.card (OrderedFinpartition s) : ℝ)
        * ((Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2))) with hX
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  refine ⟨C0 * (X + M ^ 2), ?_, fun c hmom hCSq => ?_⟩
  · exact mul_nonneg hC0nn (add_nonneg hXnn (sq_nonneg M))
  set Λ : ℝ := ∑' k : ι → ℤ, ‖c k‖ with hΛdef
  have hs0 : 0 < s := by
    have h1 : 0 < ρ := by omega
    omega
  have hCSq_summ : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖c k‖ ^ 2) :=
    summable_wt_pow_mul_norm_sq c hmom s
  have hQsumm : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖c k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hCSq_summ
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h2 : (‖k‖ : ℝ) ^ 2 ≤ wt k := sq_norm_le_wt k
    calc (‖k‖ : ℝ) ^ (2 * s) = ((‖k‖ : ℝ) ^ 2) ^ s := by rw [← pow_mul]
      _ ≤ (wt k) ^ s := pow_le_pow_left₀ (sq_nonneg _) h2 s
  have hΛsum : Summable fun k : ι → ℤ => ‖c k‖ := by simpa using hmom 0
  have hΛ0' : (0 : ℝ) ≤ Λ := tsum_nonneg fun k => norm_nonneg _
  have hCSqnn0 : (0 : ℝ) ≤ CSq s c :=
    tsum_nonneg fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)
  have hΛb : Λ ≤ C_l1 * B := by
    have h := hC_l1 c (by simpa using summable_wt_pow_mul_norm_sq c hmom ρ)
    rw [hΛdef]
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC_l1nn
    rw [Real.sqrt_le_iff]
    exact ⟨hB, hCSq⟩
  have hvnn : ∀ x : ι → ℝ, ‖seriesFun c x‖ ≤ Λ := by
    intro x
    have hsumm : Summable fun k : ι → ℤ => ‖c k * fourierExp k x‖ :=
      hΛsum.congr fun k => by rw [norm_mul, norm_fourierExp, mul_one]
    rw [hΛdef, seriesFun]
    refine (norm_tsum_le_tsum_norm hsumm).trans (le_of_eq ?_)
    exact tsum_congr fun k => by rw [norm_mul, norm_fourierExp, mul_one]
  have hΛKL : 1 + Λ ≤ KL := by rw [hKL]; linarith
  have hvR : ∀ x : ι → ℝ, ‖seriesFun c x‖ ≤ C_l1 * B := fun x => (hvnn x).trans hΛb
  have hvdiff : ContDiff ℝ (⊤ : ℕ∞) (seriesFun c) := contDiff_seriesFun c hmom
  have hper : Periodic1 (fun x => Φ (seriesFun c x)) :=
    periodic_comp (periodic_seriesFun c)
  have hfdiff : ContDiff ℝ s (fun x => Φ (seriesFun c x)) :=
    (hΦ.comp hvdiff).of_le (by simp)
  have hmain : ∀ l : Fin s → ι,
      ∫ x in unitCube, ‖pdVec s l (fun x => Φ (seriesFun c x)) x‖ ^ 2
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ)
          * ((Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2)) * (1 + CSq s c) := by
    intro l
    have hpt : ∀ x : ι → ℝ, pdVec s l (fun x => Φ (seriesFun c x)) x
        = ∑ p : OrderedFinpartition s,
            (iteratedFDeriv ℝ p.length Φ (seriesFun c x))
              (fun m => seriesFun (blockFam c l p m) x) := by
      intro x
      rw [faaDiBruno_pdVec s Φ hΦ (seriesFun c) hvdiff x l]
      exact Finset.sum_congr rfl fun p _ => congrArg _ (funext fun m =>
        blockFam_seriesFun c hmom l p m x)
    have hbd : ∀ x : ι → ℝ, ‖pdVec s l (fun x => Φ (seriesFun c x)) x‖ ^ 2
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ) *
            ∑ p : OrderedFinpartition s, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2 := by
      intro x
      rw [hpt x]
      have h1 : ‖∑ p : OrderedFinpartition s,
            (iteratedFDeriv ℝ p.length Φ (seriesFun c x))
              (fun m => seriesFun (blockFam c l p m) x)‖
          ≤ ∑ p : OrderedFinpartition s, M * ‖∏ m, seriesFun (blockFam c l p m) x‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have h2 : ‖iteratedFDeriv ℝ p.length Φ (seriesFun c x)‖ ≤ M :=
          hM (seriesFun c x) (hvR x) p.length p.length_le
        have h3 : (∏ m : Fin p.length, ‖seriesFun (blockFam c l p m) x‖)
            = ‖∏ m : Fin p.length, seriesFun (blockFam c l p m) x‖ := (norm_prod _ _).symm
        rw [h3]
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
        (sq_sum_le_card_mul_sum_sq.trans ?_)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (by positivity)
      rw [mul_pow]
    have hcont_fac : ∀ (p : OrderedFinpartition s) (m : Fin p.length),
        Continuous fun x : ι → ℝ => seriesFun (blockFam c l p m) x := by
      intro p m
      refine (contDiff_seriesFun _ fun N => ?_).continuous
      simpa only [blockFam] using
        summable_dmulV (List.ofFn fun i => l (p.emb m i)) c hmom N
    have hcontR : Continuous fun x : ι → ℝ =>
        (Fintype.card (OrderedFinpartition s) : ℝ) *
          ∑ p : OrderedFinpartition s, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2 := by
      refine continuous_const.mul (continuous_finsetSum _ fun p _ => ?_)
      refine continuous_const.mul ?_
      refine (continuous_finsetProd _ fun m _ => hcont_fac p m).norm.pow 2
    have hcontL : Continuous fun x : ι → ℝ =>
        ‖pdVec s l (fun x => Φ (seriesFun c x)) x‖ ^ 2 :=
      ((Work.Diff.STE.continuous_pdVec s l _ hfdiff).norm).pow 2
    refine le_trans (MeasureTheory.integral_mono_ae
      (el_integrableOn_unitCube_of_continuous_real hcontL)
      (el_integrableOn_unitCube_of_continuous_real hcontR)
      (Filter.Eventually.of_forall hbd)) ?_
    have hint : ∀ p : OrderedFinpartition s, MeasureTheory.Integrable
        (fun x : ι → ℝ => M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2)
        (volume.restrict unitCube) := by
      intro p
      refine MeasureTheory.Integrable.const_mul ?_ _
      refine el_integrableOn_unitCube_of_continuous_real ?_
      refine (continuous_finsetProd _ fun m _ => hcont_fac p m).norm.pow 2
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum Finset.univ (fun p _ => hint p)]
    have hsum_le : (∑ p : OrderedFinpartition s,
          ∫ x in unitCube, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2)
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2) * (1 + CSq s c) := by
      have hM2 : (0 : ℝ) ≤ M ^ 2 := by nlinarith [hMnn]
      have hterm : ∀ p : OrderedFinpartition s,
          ∫ x in unitCube, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2
            ≤ M ^ 2 * K2 * (1 + CSq s c) := by
        intro p
        have hmain_term : ∫ x in unitCube, ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2
            ≤ K2 * (1 + CSq s c) := by
          refine (integral_prod_blockFam_le s hs0 c hmom hΛsum hQsumm p l).trans ?_
          have h2 : (2 * Real.pi) ^ s * (1 + Λ) ^ s ≤ (2 * Real.pi) ^ s * KL ^ s :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [hΛ0'] : (0:ℝ) ≤ 1 + Λ) hΛKL s) (by positivity)
          calc (((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2) * (1 + CSq s c)
              ≤ (((2 * Real.pi) ^ s * KL ^ s) ^ 2) * (1 + CSq s c) := by
                refine mul_le_mul_of_nonneg_right ?_ (by linarith [hCSqnn0])
                exact pow_le_pow_left₀ (by positivity) h2 2
            _ = K2 * (1 + CSq s c) := by rw [hK2]
        calc ∫ x in unitCube, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2
            = M ^ 2 * ∫ x in unitCube, ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2 :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ M ^ 2 * (K2 * (1 + CSq s c)) := mul_le_mul_of_nonneg_left hmain_term hM2
          _ = M ^ 2 * K2 * (1 + CSq s c) := by ring
      calc (∑ p : OrderedFinpartition s,
            ∫ x in unitCube, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2)
          ≤ ∑ _p : OrderedFinpartition s, M ^ 2 * K2 * (1 + CSq s c) :=
            Finset.sum_le_sum fun p _ => hterm p
        _ = (Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2) * (1 + CSq s c) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    calc (Fintype.card (OrderedFinpartition s) : ℝ) *
          (∑ p : OrderedFinpartition s,
            ∫ x in unitCube, M ^ 2 * ‖∏ m, seriesFun (blockFam c l p m) x‖ ^ 2)
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ)
            * ((Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2) * (1 + CSq s c)) :=
          mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg _)
      _ = (Fintype.card (OrderedFinpartition s) : ℝ)
            * ((Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2)) * (1 + CSq s c) := by
          ring
  have hEN : ENormSq s (fun x => Φ (seriesFun c x)) ≤ X * (1 + CSq s c) := by
    rw [ENormSq]
    calc ∑ l : Fin s → ι, ∫ x in unitCube, ‖pdVec s l (fun x => Φ (seriesFun c x)) x‖ ^ 2
        ≤ ∑ _l : Fin s → ι,
            (Fintype.card (OrderedFinpartition s) : ℝ)
              * ((Fintype.card (OrderedFinpartition s) : ℝ) * (M ^ 2 * K2))
              * (1 + CSq s c) :=
          Finset.sum_le_sum fun l _ => hmain l
      _ = X * (1 + CSq s c) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hX]
          ring
  have hEN0 : ENormSq 0 (fun x => Φ (seriesFun c x)) ≤ M ^ 2 := by
    rw [ENormSq_zero]
    have h1 : ∀ x : ι → ℝ, ‖Φ (seriesFun c x)‖ ≤ M := by
      intro x
      have hx := hM (seriesFun c x) (hvR x) 0 (Nat.zero_le s)
      simpa using hx
    have hcontL : Continuous fun x : ι → ℝ => ‖Φ (seriesFun c x)‖ ^ 2 :=
      ((hΦ.comp hvdiff).continuous.norm).pow 2
    calc ∫ x in unitCube, ‖Φ (seriesFun c x)‖ ^ 2
        ≤ ∫ _x in unitCube, M ^ 2 := by
          refine MeasureTheory.integral_mono_ae
            (el_integrableOn_unitCube_of_continuous_real hcontL)
            (el_integrableOn_unitCube_of_continuous_real continuous_const)
            (Filter.Eventually.of_forall fun x =>
              pow_le_pow_left₀ (norm_nonneg (Φ (seriesFun c x))) (h1 x) 2)
      _ = M ^ 2 := by
          have hvol : (volume.restrict unitCube : Measure (ι → ℝ)).real Set.univ = 1 := by
            show ((volume.restrict unitCube : Measure (ι → ℝ)) Set.univ).toReal = 1
            rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube,
              Real.volume_pi_Ioc]
            simp
          rw [MeasureTheory.integral_const, smul_eq_mul, hvol, one_mul]
  refine ⟨Comp.summable_wt_fourierCoeff s _ hfdiff hper, ?_⟩
  refine (hC0 _ hfdiff hper).trans ?_
  have h1 : ENormSq s (fun x => Φ (seriesFun c x)) + ENormSq 0 (fun x => Φ (seriesFun c x))
      ≤ (X + M ^ 2) * (1 + CSq s c) := by
    have h3 : (1 : ℝ) ≤ 1 + CSq s c := by linarith
    nlinarith [hEN, hEN0, hXnn, sq_nonneg M, h3]
  calc C0 * (ENormSq s (fun x => Φ (seriesFun c x))
        + ENormSq 0 (fun x => Φ (seriesFun c x)))
      ≤ C0 * ((X + M ^ 2) * (1 + CSq s c)) := mul_le_mul_of_nonneg_left h1 hC0nn
    _ = C0 * (X + M ^ 2) * (1 + CSq s c) := by ring

end Work.Diff.STE
