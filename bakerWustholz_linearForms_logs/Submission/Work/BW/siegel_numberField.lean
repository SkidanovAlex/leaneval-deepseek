import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.siegelCoordFin
import Submission.Work.BW.exists_independent_rows
import Submission.Work.BW.siegelKernelFamily
import Submission.Work.BW.sieg2_coord_sum
import Submission.Work.BW.sieg2_gram_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# siegel_numberField — BW L1 (p. 23) = Bombieri–Vaaler; 8–15k lines (B–V) or 3–6k (elementary variant), high risk

**Claim.** Take `M < N` equations over `F` of degree `d`. There is a nonzero `x ∈ 𝓞_F^N` with
`h(x) ≤ ½log|D_F| + (N-M)⁻¹∑ᵢ(½ d log N + h(Lᵢ))`, where `h(Lᵢ)` is the projective height of
row `i`.

* It holds for any `M < N`. For rank `< M`, drop dependent rows: every summand is `≥ 0` and
  `1/(N-M') ≤ 1/(N-M)`.
* `M = 0` is trivial.

**Tightness warning.** The **row-wise sum** `∑ᵢ h(Lᵢ)` is essential.
* BW (12) sums `|s|D` over `|s| ≤ S`, which gives the factor `0.501`.
* With `M·max h(Lᵢ)` instead, `h(p) ≤ 1.145SD`. That breaks (12) (`0.85SD`), and the §19
  margins are only `0.05 S'D`.
* The per-place structure also matters. A house-and-denominator reduction to ℤ loses a factor up to
  `d` in `h(Lᵢ)`, which is fatal.
* Only an **additive** error `E` is affordable, about `E ≤ 10⁻⁴·S·D` in (12). The margin is
  `0.85 - 0.8497` of `SD`, and `SD ≥ 10⁵ d² log(4d)·d^r∏σ`. Additive errors of order
  `d³∑σⱼ + d² log d` fit.

**Routes.**
1. **Bombieri–Vaaler.** Use Thm 9 and Cor. 11 (Invent. 73): adelic Minkowski II (McFeat), plus
   duality and Vaaler's cube-slicing. Faithful, but heavy.
2. **Elementary variant (recommended).** The additive loss replaces `½log|D_F|`. If you use
   it, restate this lemma with explicit `E`, and re-verify BW (12) in `aux_poly`.
   1. Scale each row by `cᵢ ∈ 𝔞ᵢ⁻¹`, chosen by Minkowski I in the fractional ideal
      (Mathlib `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt` with per-place radii
      `∝ 1/max_j|σaᵢⱼ|`). This makes rows integral, with archimedean size at most
      `h(Lᵢ) + ½log|D| + O(d)`.
   2. Run the Dirichlet box principle per (row, archimedean place). The unknowns are
      `ξ ∈ ℤ^{Nd}` in a small ℤ-basis of `𝓞_F`, or of an order `ℤ[θ]`. Mathlib's
      `Int.Matrix.exists_ne_zero_int_vec_norm_le` is the max-norm version, and the row-wise
      variant is a short modification.
-/

namespace Work.BW

open NumberField

noncomputable section

/-- BW L1 (Siegel's box principle, from Bombieri–Vaaler, Invent. 73, no. 9): `M < N` homogeneous equations
over a number field `F` of degree `d` have a nonzero solution in `𝓞 F` with
`h(x) ≤ ½ log|D_F| + (N-M)⁻¹ ∑ᵢ (½ d log N + h(Lᵢ))` (relative projective heights). -/
theorem siegel_numberField {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) :
    ∃ x : Fin N → NumberField.RingOfIntegers F, x ≠ 0 ∧
      (∀ i, ∑ j, a i j * (x j : F) = 0) ∧
      Height.logHeight (fun j => (x j : F)) ≤
        (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
          (1 / ((N : ℝ) - M)) * ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log N +
            Height.logHeight (a i)) := by
  classical
  -- Reduce to `F`-linearly independent rows.
  obtain ⟨M', σ, hσinj, hli', hspan⟩ := exists_independent_rows a
  have hM'le : M' ≤ M := by
    simpa using Fintype.card_le_of_injective σ hσinj
  have hM'lt : M' < N := lt_of_le_of_lt hM'le hMN
  have hν'nat : 1 ≤ N - M' := by omega
  -- Notation.
  set dd : ℝ := (Module.finrank ℚ F : ℝ) with hdd
  set r2 : ℝ := (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) with hr2
  set Δ : ℝ := |((NumberField.discr F : ℤ) : ℝ)| with hΔ
  set c : ℝ := (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) * Real.sqrt Δ
    with hc
  set γ : ℝ := c ^ (N - M') * ∏ i : Fin M',
    ((N : ℝ) ^ (dd / 2) * Height.mulHeight (a (σ i))) with hγ
  set S' : ℝ := ∑ i : Fin M', ((1 / 2) * dd * Real.log N + Height.logHeight (a (σ i))) with hS'
  set k : ℕ := Module.finrank ℚ F * (N - M') with hk
  set r : ℝ := γ ^ (1 / (k : ℝ)) with hrr
  have hΔpos : 0 < Δ := by
    rw [hΔ]
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hddpos : 0 < dd := by
    rw [hdd]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hγeq : γ = ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
      Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ (N - M') *
      ∏ i : Fin M', ((N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
        Height.mulHeight (a (σ i))) := by
    simp only [hγ, hc, hdd, hΔ]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcpos : 0 < c := by
    rw [hc]
    exact mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr hΔpos)
  have hγpos : 0 < γ := by
    rw [hγeq]
    refine mul_pos (pow_pos (mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr hΔpos)) _)
      (Finset.prod_pos fun i _ => ?_)
    exact mul_pos (Real.rpow_pos_of_pos hNpos _) (Height.mulHeight_pos _)
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.mul_pos (Module.finrank_pos (R := ℚ) (M := F)) (by omega)
  have hrpos : 0 < r := by
    rw [hrr]
    exact Real.rpow_pos_of_pos hγpos _
  have hrpow : r ^ k = γ := by
    rw [hrr, ← Real.rpow_natCast, ← Real.rpow_mul hγpos.le]
    have h1 : (1 / (k : ℝ)) * (k : ℝ) = 1 := by
      field_simp
    rw [h1, Real.rpow_one]
  have hvol : ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
        Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ (N - M') *
      ∏ i : Fin M', ((N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
        Height.mulHeight (a (σ i))) ≤ r ^ (Module.finrank ℚ F * (N - M')) := by
    rw [← hγeq, ← hrpow, hk]
  -- Sharp Bombieri–Vaaler family of integral kernel vectors.
  obtain ⟨v, hvker, hvli, hvgram⟩ :=
    siegelKernelFamily (F := F) hM'lt (fun i => a (σ i)) hli'
  have hvgram' : siegGramDet v ≤ γ := by
    rw [hγeq]
    exact hvgram
  -- Its mixed coordinates, reindexed into `Fin (N * d)`.
  set w : Fin k → (Fin (N * Module.finrank ℚ F) → ℝ) :=
    fun i => siegelNormCoord (F := F) N (v i) with hw
  have hw_eq : ∀ (i : Fin k) (l : Fin (N * Module.finrank ℚ F)),
      w i l = siegCoord (v i) ((siegelCoordIdxEquiv (F := F) N).symm l).1
        ((siegelCoordIdxEquiv (F := F) N).symm l).2 := by
    intro i l
    simp only [hw]
    simp [siegelNormCoord, siegCoord]
  have hw_li : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff] at hvli ⊢
    intro c hsum
    refine hvli c ?_
    funext j q
    have h := congrFun hsum (siegelCoordIdxEquiv (F := F) N (j, q))
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h ⊢
    have hswap : (∑ i, c i * w i (siegelCoordIdxEquiv (F := F) N (j, q)))
        = ∑ i, c i * siegCoord (v i) j q := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show w i (siegelCoordIdxEquiv (F := F) N (j, q)) = siegCoord (v i) j q from by
        rw [hw_eq i]; simp]
    rw [← hswap]
    exact h
  have hw_gram : siegelGramDet w = siegGramDet v := by
    have hmat : Matrix.of (fun i i' : Fin k => ∑ l, w i l * w i' l) =
        Matrix.of (fun i i' : Fin k => siegInner (siegCoord (v i)) (siegCoord (v i'))) := by
      ext i i'
      simp only [Matrix.of_apply]
      calc ∑ l : Fin (N * Module.finrank ℚ F), w i l * w i' l
          = ∑ l, siegCoord (v i) ((siegelCoordIdxEquiv (F := F) N).symm l).1
                ((siegelCoordIdxEquiv (F := F) N).symm l).2 *
              (siegCoord (v i') ((siegelCoordIdxEquiv (F := F) N).symm l).1
                ((siegelCoordIdxEquiv (F := F) N).symm l).2) := by
              refine Finset.sum_congr rfl fun l _ => by rw [hw_eq i l, hw_eq i' l]
        _ = ∑ p : Fin N × NumberField.mixedEmbedding.index F,
              siegCoord (v i) p.1 p.2 * siegCoord (v i') p.1 p.2 :=
              Equiv.sum_comp (siegelCoordIdxEquiv (F := F) N).symm
                (fun p : Fin N × NumberField.mixedEmbedding.index F =>
                  siegCoord (v i) p.1 p.2 * siegCoord (v i') p.1 p.2)
        _ = siegInner (siegCoord (v i)) (siegCoord (v i')) :=
              sieg2_gram_eq (F := F) v i i'
    rw [siegelGramDet, siegGramDet, hmat]
  have hgram_le : siegelGramDet w ≤ r ^ k := by
    rw [hw_gram, hrpow]
    exact hvgram'
  obtain ⟨t, htne, ht⟩ := siegelVaalerMinkowskiFin (F := F) (N := N) (k := k) hkpos w hw_li
    hrpos hgram_le
  set x : Fin N → 𝓞 F := fun j => ∑ i, (t i) • (v i j) with hx_def
  have hx_coord : ∀ (j : Fin N) (q : NumberField.mixedEmbedding.index F),
      siegelNormCoord (F := F) N x (siegelCoordIdxEquiv (F := F) N (j, q))
        = ∑ i, (t i : ℝ) * siegCoord (v i) j q := by
    intro j q
    rw [siegelNormCoord_apply, hx_def]
    exact sieg2_coord_sum (F := F) t v j q
  have hx_lin : ∀ l : Fin (N * Module.finrank ℚ F),
      siegelNormCoord (F := F) N x l = ∑ i, (t i : ℝ) * w i l := by
    intro l
    obtain ⟨p, hp⟩ : ∃ p : Fin N × NumberField.mixedEmbedding.index F,
        siegelCoordIdxEquiv (F := F) N p = l :=
      ⟨(siegelCoordIdxEquiv (F := F) N).symm l, Equiv.apply_symm_apply _ l⟩
    rw [← hp, hx_coord p.1 p.2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw_eq i (siegelCoordIdxEquiv (F := F) N p)]
    simp
  have hxcoord : ∀ l : Fin (N * Module.finrank ℚ F),
      |siegelNormCoord (F := F) N x l| ≤ r := by
    intro l
    rw [hx_lin l]
    exact ht l
  have hxne : x ≠ 0 := by
    intro h0
    have hsum0 : (∑ i : Fin k, (t i : ℝ) • w i) = 0 := by
      funext l
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      rw [← hx_lin l, h0]
      simp [siegelNormCoord]
    have hcoe := Fintype.linearIndependent_iff.mp hw_li (fun i => (t i : ℝ)) (by simpa using hsum0)
    exact htne (funext fun i => Int.cast_eq_zero.mp (hcoe i))
  have hxann : ∀ n : Fin M', ∑ j, a (σ n) j * (x j : F) = 0 := by
    intro n
    have hcoe : ∀ j, (x j : F) = ∑ i, (t i : F) * ((v i j : 𝓞 F) : F) := by
      intro j
      rw [hx_def]
      simp only [Finset.sum_apply]
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]
    calc ∑ j, a (σ n) j * (x j : F)
        = ∑ j, a (σ n) j * (∑ i, (t i : F) * ((v i j : 𝓞 F) : F)) :=
          Finset.sum_congr rfl fun j _ => by rw [hcoe j]
      _ = ∑ j, ∑ i, a (σ n) j * ((t i : F) * ((v i j : 𝓞 F) : F)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, a (σ n) j * ((t i : F) * ((v i j : 𝓞 F) : F)) := Finset.sum_comm
      _ = ∑ i, (t i : F) * (∑ j, a (σ n) j * ((v i j : 𝓞 F) : F)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hvker]
  -- Every row is in the span of the selected rows, hence also annihilates `x`.
  have hmem : ∀ i : Fin M, a i ∈ Submodule.span F (Set.range fun n : Fin M' => a (σ n)) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hann : ∀ i : Fin M, ∑ j, a i j * (x j : F) = 0 := by
    intro i
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hmem i)
    have h1 : ∀ j, a i j = ∑ n, cf n * a (σ n) j := by
      intro j
      have h2 := congrFun hcf j
      rw [← h2]
      simp [Finset.sum_apply, Pi.smul_apply]
    calc ∑ j, a i j * (x j : F)
        = ∑ j, (∑ n, cf n * a (σ n) j) * (x j : F) :=
          Finset.sum_congr rfl fun j _ => by rw [h1 j]
      _ = ∑ j, ∑ n, (cf n * a (σ n) j) * (x j : F) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ n, ∑ j, (cf n * a (σ n) j) * (x j : F) := Finset.sum_comm
      _ = ∑ n, cf n * (∑ j, a (σ n) j * (x j : F)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hxann]
  -- Height bound.
  have hheight := siegelLogHeightLeOfNormCoordOfPos (F := F) x hxne hrpos hxcoord
  -- Arithmetic.
  have h1d : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have h2d : (0 : ℝ) < (N : ℝ) - M' := by
    have h3 : (M' : ℝ) < (N : ℝ) := by exact_mod_cast hM'lt
    linarith
  have hlogr : dd * Real.log r = (1 / ((N : ℝ) - M')) * Real.log γ := by
    rw [hrr, Real.log_rpow hγpos, ← mul_assoc]
    congr 1
    rw [hk, hdd, Nat.cast_mul, Nat.cast_sub hM'lt.le]
    field_simp
  have hprodpos : 0 < ∏ i : Fin M', ((N : ℝ) ^ (dd / 2) * Height.mulHeight (a (σ i))) :=
    Finset.prod_pos fun i _ => mul_pos (Real.rpow_pos_of_pos hNpos _) (Height.mulHeight_pos _)
  have hsumlog : (∑ i : Fin M',
        Real.log ((N : ℝ) ^ (dd / 2) * Height.mulHeight (a (σ i)))) = S' := by
    rw [hS']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_mul (Real.rpow_pos_of_pos hNpos _).ne' (Height.mulHeight_pos _).ne',
      Real.log_rpow hNpos, hdd, Height.logHeight_eq_log_mulHeight]
    ring
  have hlogγ : Real.log γ = ((N : ℝ) - M') * Real.log c + S' := by
    rw [hγ, Real.log_mul (pow_pos hcpos _).ne' hprodpos.ne', Real.log_pow]
    rw [Real.log_prod (s := Finset.univ) fun i _ =>
      (mul_pos (Real.rpow_pos_of_pos hNpos _) (Height.mulHeight_pos _)).ne']
    rw [hsumlog, Nat.cast_sub hM'lt.le]
  have hlogcΔ : Real.log c + r2 * Real.log 2 = (1 / 2) * Real.log Δ := by
    rw [hc, Real.log_mul (by positivity) (Real.sqrt_pos.mpr hΔpos).ne', Real.log_pow,
      Real.log_sqrt hΔpos.le,
      show Real.log ((1 : ℝ) / 2) = -Real.log 2 from by rw [one_div, Real.log_inv], hr2]
    push_cast
    ring
  have hS'nn : 0 ≤ S' := by
    rw [hS']
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : 0 ≤ (1 / 2) * dd * Real.log N := by
      have h2 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      nlinarith [hddpos]
    linarith [h1, Height.logHeight_nonneg (a (σ i))]
  have hSumMnn : 0 ≤ ∑ i : Fin M, ((1 / 2) * dd * Real.log N + Height.logHeight (a i)) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have h1 : 0 ≤ (1 / 2) * dd * Real.log N := by nlinarith [hddpos]
    linarith [h1, Height.logHeight_nonneg (a i)]
  have hSmono : S' ≤ ∑ i : Fin M, ((1 / 2) * dd * Real.log N + Height.logHeight (a i)) := by
    have hfin : ∀ i : Fin M, 0 ≤ (1 / 2) * dd * Real.log N + Height.logHeight (a i) := by
      intro i
      have h2 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
      have h1 : 0 ≤ (1 / 2) * dd * Real.log N := by nlinarith [hddpos]
      linarith [h1, Height.logHeight_nonneg (a i)]
    have himg : (∑ i ∈ Finset.univ.image σ,
          ((1 / 2) * dd * Real.log N + Height.logHeight (a i)))
        = ∑ i : Fin M', ((1 / 2) * dd * Real.log N + Height.logHeight (a (σ i))) := by
      rw [Finset.sum_image]
      exact fun x _ y _ hxy => hσinj hxy
    rw [hS', ← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _) ?_
    intro i _ _
    exact hfin i
  have hνpos : 0 < (N : ℝ) - M := by
    have h : (M : ℝ) < (N : ℝ) := by exact_mod_cast hMN
    linarith
  have hν'pos : 0 < (N : ℝ) - M' := h2d
  have hνle : (N : ℝ) - M ≤ (N : ℝ) - M' := by
    have h : (M' : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM'le
    linarith
  have hcompare : (1 / ((N : ℝ) - M')) * S' ≤
      (1 / ((N : ℝ) - M)) * (∑ i : Fin M,
        ((1 / 2) * dd * Real.log N + Height.logHeight (a i))) := by
    have hkey : (1 / ((N : ℝ) - M)) * (∑ i : Fin M,
          ((1 / 2) * dd * Real.log N + Height.logHeight (a i))) -
        (1 / ((N : ℝ) - M')) * S'
        = (1 / ((N : ℝ) - M)) * ((∑ i : Fin M,
              ((1 / 2) * dd * Real.log N + Height.logHeight (a i))) - S') +
          (1 / ((N : ℝ) - M) - 1 / ((N : ℝ) - M')) * S' := by
      ring
    have h1 : 0 ≤ (1 / ((N : ℝ) - M)) * ((∑ i : Fin M,
        ((1 / 2) * dd * Real.log N + Height.logHeight (a i))) - S') :=
      mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ (1 / ((N : ℝ) - M) - 1 / ((N : ℝ) - M')) * S' := by
      refine mul_nonneg ?_ hS'nn
      have hle := one_div_le_one_div_of_le hνpos hνle
      linarith
    linarith [hkey, h1, h2]
  -- Final assembly.
  refine ⟨x, hxne, hann, ?_⟩
  have hsum2 : (∑ i : Fin M, ((1 / 2) * dd * Real.log N + Height.logHeight (a i)))
      = ∑ i : Fin M, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log N +
          Height.logHeight (a i)) := by
    rw [hdd]
  have hΔlog : Real.log Δ = Real.log |((NumberField.discr F : ℤ) : ℝ)| := by rw [hΔ]
  calc Height.logHeight (fun j => (x j : F))
      ≤ dd * Real.log r + r2 * Real.log 2 := hheight
    _ = (1 / ((N : ℝ) - M')) * Real.log γ + r2 * Real.log 2 := by rw [hlogr]
    _ = Real.log c + (1 / ((N : ℝ) - M')) * S' + r2 * Real.log 2 := by
          have hstep : (1 / ((N : ℝ) - M')) * (((N : ℝ) - M') * Real.log c + S') +
              r2 * Real.log 2
              = Real.log c + (1 / ((N : ℝ) - M')) * S' + r2 * Real.log 2 := by
            field_simp
          rw [hlogγ, hstep]
    _ = (1 / 2) * Real.log Δ + (1 / ((N : ℝ) - M')) * S' := by
          linarith [hlogcΔ]
    _ ≤ (1 / 2) * Real.log Δ + (1 / ((N : ℝ) - M)) * (∑ i : Fin M,
          ((1 / 2) * dd * Real.log N + Height.logHeight (a i))) := by
          linarith [hcompare]
    _ = (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
          (1 / ((N : ℝ) - M)) * ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log N +
            Height.logHeight (a i)) := by
          rw [← hΔlog, ← hsum2]

end

end Work.BW
