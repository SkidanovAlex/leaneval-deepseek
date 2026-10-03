import Mathlib
import Submission.Work.KMTAreas.A4.kmtProjSelfAdjoint
import Submission.Work.KMTAreas.A5.iwSymbolSet_prod_kmtEta
import Submission.Work.KMTAreas.A7.varShiftDiffPrep
import Submission.Work.KMTAreas.A7G.maximalLowpass
import Submission.Work.KMTAreas.A7Hi.FiberVarSampling
import Submission.Work.KMTAreas.A7Hi.rpow_sum_le_rpow_sum_of_le
import Submission.Port.Aesm

/-!
# `Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo` — in-file state of the target

## What this file proves (sorry-free, axiom-clean)

* `partSum_le_partSq_uniform` — the per-block Littlewood--Paley bound (P1, i.e.
  `Work.KMTAreas.A7Hi.bandSumSqRep`) in the `partSum`/`partSq` vocabulary, *uniform* in the
  arithmetic height `l₁`, the base level `m₀` and the block `I`.
* `eLpNorm_lpf_zero_le_sqFun` — `‖T_0 f‖_{ℓᵖ} ≤ C ‖sqFun f‖_{ℓᵖ}` with `C` free of `l₁` and `m₀` on
  the good major arcs.  This is the "Littlewood--Paley half" of the crux: the limit `K → ∞` of (P1)
  along the blocks `I = Finset.range K`, the telescoping `partSum (range K) f = T_K f − T_0 f`, and
  the vanishing `T_K f → 0` in `ℓᵖ` (`Work.KMTAreas.A7Hi.lpf_eventually_lt`).  No
  `α`-decomposition is used, so no factor `#(iwArithFreqs ρ l₁)` appears.

## The reduction the target reduces to

`walk f` and `walk (T_0 f)` agree from scale `1` on (`Work.KMTAreas.A7Hi.lpf_nesting`), and their
increments are *equal* (`Δ_m(T_0 f) = T_{m+1}f − T_m f = Δ_m f`, `m ≥ 0`), so
`sqFun ρ l₁ m₀ (T_0 f) = sqFun ρ l₁ m₀ f`.  With the second bullet (which gives
`‖T_0 f‖_{ℓᵖ} ≲ ‖sqFun f‖_{ℓᵖ}`) the target is therefore *equivalent* to

  `‖ chainPart r (m ↦ T_m h) ‖_{ℓᵖ} ≤ C ‖ h ‖_{ℓᵖ}`  for every `h` in the image of `T_0`,

with `C` free of `l₁` --- i.e. to the `l₁`-uniform sharp form of `A7Hi2.ChainPiece` /
`A7Hi.LowpassVar` (the tree proves the latter only with the constant `(1+l₁)²`, through
`LowpassMaximal` and `LowpassSqFun`).

## Why the route described in the target's docstring does not close it

The suggested route is (i) `Work.KMTAreas.A7Hi.fkrInterchangeGen` at `R < s ≤ p ≤ 2`, (ii) the
per-block bound (P1) on each jump, and (iii) the "disjoint-frequency-support comparison"

  `(∑_i ‖S_{I_i}‖_{L^p}^R)^{1/R} ≤ C ‖ (∑_i S_{I_i}²)^{1/2} ‖_{L^p}`,   `S_I = (∑_{k∈I}|Δ_k f|²)^{1/2}`.

Step (iii) is **false for arbitrary families** — it is exactly the `ℓ^R ↮ ℓ²` reversal (on a family
of `M` terms the `ℓ^R` norm dominates the `ℓ²` norm, so the comparison needs the terms to be
*spread*, and pairwise disjointness of the *frequency* supports does not by itself force that).
The natural candidate realising the failure inside the family at hand: fix `M` scales
`m_1 < ⋯ < m_M` with `2^{m₀+m_1} ≫ R` and `f` whose increments satisfy
`Δ_{m_i} f ≡ M^{-1/2} ω_i` on the window `[0,R]`, `|ω_i| = 1` incoherent; then for the single-scale
blocks `I_i = {m_i}` the left-hand side is `≈ M^{1/R-1/2} R^{1/p}` while
`(∑_i S_{I_i}²)^{1/2} = S f ≈ R^{1/p}`, so the ratio is `M^{1/R-1/2} → ∞` for `R < 2`.  Incoherent
phases keep this compatible with (P1) (`T_0 f = −∑_i Δ_{m_i}f` is `O(1)` on `[0,R]`, so
`‖T_0 f‖_{L^p} ≈ R^{1/p} ≈ ‖S f‖_{L^p}`), while the *target itself* holds on this family: the walk
is a random walk with `M` steps of size `M^{-1/2}`, so
`chainPart r (walk) ≈ max(M^{1/r-1/2},1) ≈ 1 ≈ S`.  (The realisation of the increments by a single
`f` is heuristic; the rigorous content is that (iii) does not follow from disjointness alone, and
that the `R = 2` route through `fkrInterchangeGen` needs `R < s ≤ p`, hence `p > 2` --- precisely
the sibling `chainPartSqFunGeTwo`, where (iii) *is* a pointwise inequality.)

## What a proof would need

Either the `l₁`-uniform JSW/Lépingle good-`λ` measure-domination argument for the IW comb (the
workspace's registered crux `A7Hi.lpf_chainPart_sparsity`, see `NOTES_A7Hi_LowpassChainLe_STATE.md`,
`NOTES_chainPartLowpass_SESSION*.md`), or, along the paper's route, an `l₁`-free *vector-valued*
Ionescu--Wainger multiplier theorem: the registered MSZ3 Theorem 2.1
(`Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even`) carries an `⟨l⟩` loss, which is
exactly what makes the tree's `LowpassVar` / `SupPiece` / `lacunaryMaxPiece` carry `(1+l₁)^{O(1)}`.
Every `l₁`-uniform statement in the tree is single-scale or uniform-in-signs
(`A7.kmtProj_lp_bound_uniform`, `A7Lpd.uniformSignsAnnuliOfReal`, `A7Lpd.bandSquareUnif`,
`A7Lpd.singleChain_blockSqSum_le`); the sup-over-chains step is the missing one.  Two further dead
ends (recorded so they are not retried): the `α`-decomposition route loses the exponential
`#(iwArithFreqs ρ l₁)`; the deep-regime coset/fibre reduction (`A7Hi.kmtKernel_eq_iwQ0_mul_KW`)
expresses the walk on a coset as the `KW ρ l (−Q·)`-weighted plain dilation family, but
`KW ρ l (−Q·)` is *not* an `ℓ^∞`-small perturbation of `1` (its symbol is `≈ 1` on each of the
`#(iwW ρ l)` torsion arcs, e.g. at `ξ = 1/2`), so the fibre walk is again an IW-type comb (with the
denominator set `iwW ρ l`), and the `#(iwW ρ l)` loss persists.

## Sub-range reached (PROVED)

For **bounded arithmetic height** `l₁ ≤ iwC0 ρ` the target *is* proved, sorry-free and axiom-clean,
as `Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo_smallHeight`
(`Submission/Work/KMTAreas/A7HiRep/chainPartSqFunLeTwo_smallHeight.lean`), by the elementary
argument: `A7Hi2.chainPart_le_smallHeight` (whose loss `#(iwArithFreqs ρ l) ≤ 4^{l+1}` is `l`-free
for `l ≤ iwC0 ρ`) bounds the chain part of the walk of `T_0 f` by `‖T_0 f‖_{ℓᵖ}`; the walk
comparison is `A7Hi.chainPart_le_chainPart_add_defect` + `A7Hi.lpf_nesting`; the defect is paid by
`A7HiRep.eLpNorm_lpf_zero_le_sqFun` above; and `A7.kmtProj_lp_bound_uniform` (which is `l₁`-free)
supplies `‖T_0 f‖_{ℓᵖ} < ⊤`.  The general `l₁ > iwC0 ρ` regime is the missing step described above.
-/

namespace Work.KMTAreas.A7HiRep

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## Elementary interface lemmas for the `p ≤ 2` half (valid, but *not* a reduction)

Three elementary lemmas used by any attack on the target:

* `memLp_two_of_summable_sq'`, `memLp_two_of_memLp_of_le_two` — on the counting measure an
  `ℓᵖ` sequence with `p ≤ 2` is bounded, hence `ℓ²`;
* `sqFun_le_chainPart_two` — `sqFun` is the chain value of the *identity* chain, so it is
  dominated pointwise by `chainPart 2` of the walk;
* `chainPart_two_mono_exp` — `chainPart r ≤ chainPart 2` for `2 ≤ r` (the pointwise
  `ℓ^r ⊆ ℓ²` on the finite chain vectors).

## A REFUTED ROUTE (recorded so that it is not retried)

A natural hope (and the "mirror" of the route of `chainPartSqFunGeTwo.lean` for `p > 2`) is that
the `p ≤ 2` case follows from the `2`-endpoint `‖chainPart 2 (walk f)‖_{ℓ²} ≤ C‖sqFun f‖_{ℓ²}`
plus an elementary pointwise input, by "interpolation downwards" between `L²` and `L^∞`.  **This is
FALSE**, and the error is worth recording precisely, because the *upward* version (used for
`p > 2`) is valid.

The tempting step is `∫ h^p ≤ K^{p-2} ∫ h²` for a pointwise majorant `h ≤ K` and `p ≤ 2`, obtained
from `h^p = h^{p-2}h²` and `h^{p-2} ≤ K^{p-2}`.  **The comparison is backwards**: for `p - 2 < 0`
the map `u ↦ u^{p-2}` is *decreasing*, so `h ≤ K` gives `h^{p-2} ≥ K^{p-2}` and hence
`h^p ≥ K^{p-2}h²`, i.e. an upper bound on `h^p` in terms of `h²` and `K` is not available this way
(and is false in general: `h = 1_A`, `A` of measure `V`, `S = 1_B`, `B ⊆ A` of measure `1`, gives
`h ≤ K`, `S ≤ h`, `∫h² ≤ 2∫S²` with a *common* bound `K`, while
`‖h‖_p/‖S‖_p ≈ V^{1/p-1/2} → ∞` for `p < 2`).  Consistently, the `L²`–`L^∞` pair determines
`‖·‖_q` only for `q ≥ 2`: `‖g‖_q ≤ ‖g‖_∞^{1-2/q}‖g‖_2^{2/q}` holds for `q ≥ 2`, and the analogous
inequality for `q < 2` is false.

So the `2`-endpoint does *not* imply the target for `p < 2`, and the genuinely hard content of the
target (the good-`λ`/window-sparsity of `A7Hi.lpf_chainPart_sparsity`, i.e. the JSW
[Thm 1.1 + Lemma 3.2] square-function argument) is not reduced by this route. -/

/-- **`sqFun` is the chain value of the identity chain.**  Pointwise, `sqFun ρ l m₀ f x` is
dominated by the `2`-chain part of the low-pass walk `m ↦ lpf ρ l m₀ m f x`: the identity chain
`N i = i` contributes exactly the partial sums of the squared increments. -/
theorem sqFun_le_chainPart_two (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7Hi.sqFun ρ l m₀ f x
      ≤ Work.KMTAreas.A7Hi.chainPart 2 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x) := by
  have hsum : Work.KMTAreas.A7Hi.sqFun ρ l m₀ f x
      = (⨆ K : ℕ, ∑ i ∈ Finset.range K,
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [Work.KMTAreas.A7Hi.sqFun, ENNReal.tsum_eq_iSup_nat]
  rw [hsum, Work.KMTAreas.A7.rpow_iSup_ennreal _ (by norm_num : (0 : ℝ) < 1 / 2)]
  refine iSup_le fun K => ?_
  have hterm : (∑ i ∈ Finset.range K,
        ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal ‖WithLp.toLp ((2 : NNReal) : ℝ≥0∞)
          (fun i : Fin K => Work.KMTAreas.A7Hi.lpf ρ l m₀ ((i : ℕ) + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ (i : ℕ) f x)‖ := by
    rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum (2 : NNReal) (by norm_num)
      (fun i : Fin K => Work.KMTAreas.A7Hi.lpf ρ l m₀ ((i : ℕ) + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l m₀ (i : ℕ) f x)]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (j + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l m₀ j f x‖ₑ ^ (2 : ℝ)) K).symm
  rw [hterm]
  refine le_iSup_of_le K (le_iSup_of_le (fun i : ℕ => i) (le_iSup_of_le monotone_id ?_))
  exact le_of_eq (congrArg (fun v : Fin K → ℂ =>
    ENNReal.ofReal ‖WithLp.toLp ((2 : NNReal) : ℝ≥0∞) v‖) (by
      funext i
      rfl))

/-- **`chainPart r ≤ chainPart 2` for `2 ≤ r`** (the pointwise inclusion `ℓ^r ⊆ ℓ²` on the finite
chain vectors). -/
theorem chainPart_two_mono_exp (r : NNReal) (hr : 2 ≤ r) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r a ≤ Work.KMTAreas.A7Hi.chainPart 2 a := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr
  unfold Work.KMTAreas.A7Hi.chainPart
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have hL := Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr1
    (fun i : Fin J => a (N (i + 1)) - a (N i))
  have hR := Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum (2 : NNReal) (by norm_num)
    (fun i : Fin J => a (N (i + 1)) - a (N i))
  rw [hL]
  refine le_trans (Work.KMTAreas.A7Lpd.sum_rpow_le_sum_rpow' _ (p := 2) (q := (r : ℝ))
    (by norm_num) hrR) ?_
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN (le_of_eq hR.symm)))

/-- **`MemLp` at `2` from `∑_n ‖g n‖² < ∞`** on `ℤ` with the counting measure (a local copy of
`Work.KMTAreas.A7Hi2.memLp_two_of_summable_sq`, whose module cannot be imported here because of an
unrelated name clash). -/
theorem memLp_two_of_summable_sq' {g : ℤ → ℂ}
    (h : Summable fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) :
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count := by
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) (by norm_num) (by norm_num),
    MeasureTheory.lintegral_count]
  simp only [ENNReal.toReal_ofNat]
  have hpt : ∀ a : ℤ, ‖g a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g a‖ ^ (2 : ℝ)) :=
    fun a => Work.KMTAreas.A7Hi2.enorm_rpow_eq_ofReal (g a) 2 (by norm_num)
  rw [show (∑' a : ℤ, ‖g a‖ₑ ^ (2 : ℝ))
      = ∑' a : ℤ, ENNReal.ofReal (‖g a‖ ^ (2 : ℝ)) from tsum_congr fun a => hpt a,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) _) h]
  exact ENNReal.ofReal_lt_top

/-- **Per-block Cauchy–Schwarz (the block-energy inequality).**

For a finite set of scales `I` and any family `d : ℕ → ℂ`,

  `‖∑_{k ∈ I} d k‖ₑ ^ 2 ≤ |I| · ∑_{k ∈ I} ‖d k‖ₑ ^ 2`.

This is the pointwise input of the `p = 2` endpoint (`EndTwo`, see
`NOTES_A7HiRep_chainPartSqFunLeTwo_SESSION2.md` §9): applied to the blocks
`d k = a (k+1) - a k` of a monotone chain it turns the chain energy
`∑_i ‖∑_{k ∈ I_i} d k‖²` into the *block-length-weighted* square function
`∑_k |I_{κ(k)}| · ‖d k‖²`, whose `|I| = 1` case is the ordinary square function. -/
theorem blockEnergy_sq_le_card_mul (I : Finset ℕ) (d : ℕ → ℂ) :
    ‖∑ k ∈ I, d k‖ₑ ^ (2 : ℝ) ≤ (I.card : ℝ≥0∞) * ∑ k ∈ I, ‖d k‖ₑ ^ (2 : ℝ) := by
  have hCS : (∑ k ∈ I, ‖d k‖) ^ (2 : ℝ)
      ≤ ((I.card : ℕ) : ℝ) * ∑ k ∈ I, ‖d k‖ ^ (2 : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ : ℕ => (1 : ℝ)) (fun k => ‖d k‖)
    have h1 : (∑ k ∈ I, (1 : ℝ) * ‖d k‖) = ∑ k ∈ I, ‖d k‖ := by simp
    have h2 : (∑ k ∈ I, (1 : ℝ) ^ 2) = ((I.card : ℕ) : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2] at hcs
    rw [show (∑ k ∈ I, ‖d k‖ ^ 2) = ∑ k ∈ I, ‖d k‖ ^ (2 : ℝ) from
      Finset.sum_congr rfl fun k _ => (Real.rpow_natCast (‖d k‖) 2).symm] at hcs
    rw [show (∑ k ∈ I, ‖d k‖) ^ 2 = (∑ k ∈ I, ‖d k‖) ^ (2 : ℝ) from
      (Real.rpow_natCast (∑ k ∈ I, ‖d k‖) 2).symm] at hcs
    exact hcs
  calc ‖∑ k ∈ I, d k‖ₑ ^ (2 : ℝ)
      ≤ (∑ k ∈ I, ‖d k‖ₑ) ^ (2 : ℝ) := ENNReal.rpow_le_rpow (enorm_sum_le I d) (by norm_num)
    _ = (∑ k ∈ I, ENNReal.ofReal ‖d k‖) ^ (2 : ℝ) := by
        rw [Finset.sum_congr rfl (fun k _ => (ofReal_norm (d k)).symm)]
    _ = (ENNReal.ofReal (∑ k ∈ I, ‖d k‖)) ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)]
    _ = ENNReal.ofReal ((∑ k ∈ I, ‖d k‖) ^ (2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _) (by norm_num)
    _ ≤ ENNReal.ofReal (((I.card : ℕ) : ℝ) * ∑ k ∈ I, ‖d k‖ ^ (2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hCS
    _ = (I.card : ℝ≥0∞) * ∑ k ∈ I, ‖d k‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg _) _)]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← ofReal_norm]
        exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).symm


/-- **The block-length-weighted chain energy.**  For a walk `a` and a truncation `J`, the supremum
over monotone chains with at most `J` blocks of the *block-length-weighted* square sum

  `∑_{i<K} |I_i| · ∑_{k ∈ I_i} ‖a(k+1) - a k‖ₑ²`,   `I_i = [N i, N(i+1))`.

This is the object into which `chainEnergy_le_blockWeighted` converts the chain energy, and it is the
object the localisation step of the `p = 2` endpoint (`EndTwo`) has to bound by `∫ (sqFun)²`: for a
chain selected at a point `x`, the weight of the increment at scale `k` is exactly the length
`|I_{κ(k)}(x)|` of the block of the selected chain containing `k` (see
`NOTES_A7HiRep_chainPartSqFunLeTwo_SESSION2.md` §9 and the session-12 note §8). -/
noncomputable def weightedChainEnergy (a : ℕ → ℂ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ (K : ℕ) (_ : K ≤ J) (N : ℕ → ℕ) (_ : Monotone N),
    ∑ i : Fin K, ((N ((i : ℕ) + 1) - N (i : ℕ) : ℕ) : ℝ≥0∞)
      * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)), ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)

/-- **The block-length-bounded weighted chain energy**: `weightedChainEnergy` with the additional
constraint that every block of the chain has length at most `M`.

This isolates the *only* dangerous part of the `p = 2` endpoint `(W-TARGET)`
(`NOTES_A7HiRep_chainPartSqFunLeTwo_SESSION2.md` §9c): with all block lengths `≤ M` the weights
`w_k = |I_{κ(k)}|` are bounded by `M`, hence the weighted square sum is at most
`M · ∑_k ‖Δ_k a‖²` and the whole difficulty collapses into the unbounded block lengths.  The
corresponding `w ≡ 1` template is the proved Plancherel bound for the disjoint annuli. -/
noncomputable def weightedChainEnergyBdd (a : ℕ → ℂ) (J M : ℕ) : ℝ≥0∞ :=
  ⨆ (K : ℕ) (_ : K ≤ J) (N : ℕ → ℕ) (_ : Monotone N)
    (_ : ∀ i : Fin K, N ((i : ℕ) + 1) - N (i : ℕ) ≤ M),
    ∑ i : Fin K, ((N ((i : ℕ) + 1) - N (i : ℕ) : ℕ) : ℝ≥0∞)
      * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)), ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)


/-- **The block-length-bounded case of the weighted square-function estimate** (the template beside
`(W-TARGET)`): if every block of the chain has length at most `M`, the block-length-weighted chain
energy is at most `M` times the ordinary square sum of the increments.

Elementary: the weight of each increment is at most `M`, and the blocks of a monotone chain are
pairwise disjoint.  It shows that the whole difficulty of the `p = 2` endpoint is carried by the
*unbounded* block lengths. -/
theorem weightedChainEnergyBdd_le (a : ℕ → ℂ) (J M : ℕ) :
    Work.KMTAreas.A7HiRep.weightedChainEnergyBdd a J M
      ≤ (M : ENNReal) * tsum (fun k : ℕ => ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)) := by
  unfold Work.KMTAreas.A7HiRep.weightedChainEnergyBdd
  refine iSup_le fun K => iSup_le fun _hK => iSup_le fun N => iSup_le fun hN => iSup_le fun hlen => ?_
  have hterm : ∀ i : Fin K, ((N ((i : ℕ) + 1) - N (i : ℕ) : ℕ) : ENNReal)
        * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)), ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)
      ≤ (M : ENNReal) * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)),
          ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ) := by
    intro i
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    exact_mod_cast hlen i
  have hdisj : ∀ i j : Fin K, i ≠ j →
      Disjoint (Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)))
        (Finset.Ico (N (j : ℕ)) (N ((j : ℕ) + 1))) := by
    intro i j hij
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · have h1 : N ((i : ℕ) + 1) ≤ N (j : ℕ) := hN (by omega)
      exact Finset.disjoint_left.mpr fun m hm hm' => by
        simp only [Finset.mem_Ico] at hm hm'
        omega
    · have h1 : N ((j : ℕ) + 1) ≤ N (i : ℕ) := hN (by omega)
      exact Finset.disjoint_left.mpr fun m hm hm' => by
        simp only [Finset.mem_Ico] at hm hm'
        omega
  calc ∑ i : Fin K, ((N ((i : ℕ) + 1) - N (i : ℕ) : ℕ) : ENNReal)
        * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)), ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)
      ≤ ∑ i : Fin K, (M : ENNReal) * ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)),
          ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
    _ = (M : ENNReal) * ∑ i : Fin K, ∑ k ∈ Finset.Ico (N (i : ℕ)) (N ((i : ℕ) + 1)),
          ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M : ENNReal) * tsum (fun k : ℕ => ‖a (k + 1) - a k‖ₑ ^ (2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
        exact ENNReal.sum_le_tsum _


/-- **The energy of the chains that have a block longer than `M`** — the exceptional object of the
truncation step: the same squared-jump sum as `chainEnergyUpTo`, but restricted to chains some block
of which has length `> M`.  For a chain *selected at a point* `x` this is exactly the event "the
selected chain has a long block", i.e. the set whose measure the localisation step has to estimate
(`NOTES_A7HiRep_chainPartSqFunLeTwo_SESSION2.md` §10). -/
noncomputable def chainEnergyLongBlock (a : ℕ → ℂ) (J M : ℕ) : ℝ≥0∞ :=
  ⨆ (K : ℕ) (_ : K ≤ J) (N : ℕ → ℕ) (_ : Monotone N)
    (_ : ∃ i : Fin K, M < N ((i : ℕ) + 1) - N (i : ℕ)),
    ∑ i : Fin K, ‖a (N ((i : ℕ) + 1)) - a (N (i : ℕ))‖ₑ ^ (2 : ℝ)


/-- **The jump-count mechanism of the good-λ step** (elementary, no measure theory).

Let a chain have jumps `b 0, …, b (J-1)` with every jump of size at most `2εt` (which is what the
`sup`-constraint of the good-`λ` set gives, a jump being a difference of two walk values) and suppose
that the chain's `ℓ^r` energy exceeds `(2t)^r` while the number of scales satisfies
`J·(εt)^r ≤ (2t)^r/2`.  Then at least `(1/2)ε^{-r}` of the jumps exceed `εt`.

This is the input the counting argument of the good-λ/window-sparsity step consumes; it is a finite
combinatorial statement about one chain (no measures, no `f`), hence a strict sub-statement of the
endpoint — see `NOTES_A7HiRep_chainPartSqFunLeTwo_SESSION2.md` §13. -/
theorem card_bigJumps_ge (r : ℝ) (hr : 1 ≤ r) {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (J : ℕ) (b : ℕ → ℂ) (hsup : ∀ i < J, ‖b i‖ ≤ 2 * (ε * t))
    (hscale : (J : ℝ) * (ε * t) ^ r ≤ (2 * t) ^ r / 2)
    (henergy : (2 * t) ^ r < ∑ i ∈ Finset.range J, ‖b i‖ ^ r) :
    (1 / 2) * ε ^ (-r) ≤ (((Finset.range J).filter fun i => ε * t < ‖b i‖).card : ℝ) := by
  have hrn : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range J)
    (p := fun i : ℕ => ε * t < ‖b i‖) (f := fun i : ℕ => ‖b i‖ ^ r)
  have hbig : ∑ i ∈ (Finset.range J).filter (fun i : ℕ => ε * t < ‖b i‖), ‖b i‖ ^ r
      ≤ (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) * (2 * (ε * t)) ^ r := by
    calc ∑ i ∈ (Finset.range J).filter (fun i : ℕ => ε * t < ‖b i‖), ‖b i‖ ^ r
        ≤ ∑ _i ∈ (Finset.range J).filter (fun i : ℕ => ε * t < ‖b i‖), (2 * (ε * t)) ^ r := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact Real.rpow_le_rpow (norm_nonneg _)
            (hsup i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)) hrn
      _ = (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) * (2 * (ε * t)) ^ r := by
          simp only [Finset.sum_const, nsmul_eq_mul]
  have hsmall : ∑ i ∈ (Finset.range J).filter (fun i : ℕ => ¬ (ε * t < ‖b i‖)), ‖b i‖ ^ r
      ≤ (J : ℝ) * (ε * t) ^ r := by
    calc ∑ i ∈ (Finset.range J).filter (fun i : ℕ => ¬ (ε * t < ‖b i‖)), ‖b i‖ ^ r
        ≤ ∑ _i ∈ (Finset.range J).filter (fun i : ℕ => ¬ (ε * t < ‖b i‖)), (ε * t) ^ r := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact Real.rpow_le_rpow (norm_nonneg _)
            (not_lt.mp (Finset.mem_filter.mp hi).2) hrn
      _ = (((Finset.range J).filter fun i : ℕ => ¬ (ε * t < ‖b i‖)).card : ℝ) * (ε * t) ^ r := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ) * (ε * t) ^ r := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          have hc : ((Finset.range J).filter (fun i : ℕ => ¬ (ε * t < ‖b i‖))).card ≤ J :=
            le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
          exact_mod_cast hc
  have hkey : (2 * t) ^ r / 2
      < (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) * (2 * (ε * t)) ^ r := by
    have h1 : ∑ i ∈ Finset.range J, ‖b i‖ ^ r
        ≤ (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) * (2 * (ε * t)) ^ r
          + (J : ℝ) * (ε * t) ^ r := by
      rw [← hsplit]
      exact add_le_add hbig hsmall
    linarith [henergy, h1, hscale]
  have hA : (2 * (ε * t)) ^ r = 2 ^ r * (ε ^ r * t ^ r) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ ε * t),
      Real.mul_rpow hε.le ht.le]
  have hBt : (2 * t) ^ r = 2 ^ r * t ^ r :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le
  have h2r : (0 : ℝ) < 2 ^ r := Real.rpow_pos_of_pos (by norm_num) _
  have her : (0 : ℝ) < ε ^ r := Real.rpow_pos_of_pos hε _
  have htr : (0 : ℝ) < t ^ r := Real.rpow_pos_of_pos ht _
  have h1 : (1 / 2 : ℝ) < (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) * ε ^ r := by
    rw [hA, hBt] at hkey
    nlinarith [hkey, h2r, her, htr, mul_pos h2r htr]
  rw [Real.rpow_neg hε.le r]
  have hmul : ε ^ r * (ε ^ r)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt her)
  have hinv : (0 : ℝ) < (ε ^ r)⁻¹ := inv_pos.mpr her
  have h2 : (1 / 2 : ℝ) * (ε ^ r)⁻¹
      ≤ (((Finset.range J).filter fun i : ℕ => ε * t < ‖b i‖).card : ℝ) := by
    nlinarith [h1, hmul, hinv]
  exact h2

/-- **The chain-part Lépingle bound for the low-pass Ionescu--Wainger walk, for `1 < p ≤ 2`**:
there are `Cρ > 0` and `C > 0` such that on the good major arcs `GoodMajorArcs ρ Cρ l₁ (-(m₀:ℤ))`
and for every `f ∈ ℓᵖ(ℤ)`,

  `‖ chainPart r (m ↦ lpf ρ l₁ m₀ m f) ‖_{ℓᵖ} ≤ C ‖ sqFun ρ l₁ m₀ f ‖_{ℓᵖ}`,

with `C` free of the arithmetic height `l₁` and of the base level `m₀`.

**DO NOT prove this by calling the `sorry`-carrying declarations**
`Work.KMTAreas.A7HiRep.chainPartSqFun`, `A7MixedG.chainLe`, `A7G.chainPartLowpass`,
`A7Hi.LowpassChainLe`, `A7Fix.chainLe`, …: a proof that goes through one of them is *tainted* and
worthless here.  The point of this target is a proof whose axiom closure is
`[propext, Classical.choice, Quot.sound]`.  Sanity check before finishing:
`#print axioms Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo`.

This is the `p ≤ 2` half of `chainPartSqFun` (the Lépingle / Jones--Seeger--Wright step of KMT §8),
the half that is genuinely hard; the `2 < p` half is proved separately as
`Work.KMTAreas.A7HiRep.chainPartSqFunGeTwo` from `A7Hi.bandSumSqRep` + `A7Hi.fkrInterchangeGen`.

**Intended route (read `NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` §4(b) and §5 first).**
Use `Work.KMTAreas.A7Hi.fkrInterchangeGen` at `s := p` and some `R` with `1 ≤ R < p`
(so `R < s ≤ p`; its constant depends only on `R, s`), which gives

  `‖chainPart r (walk)‖_p ≤ ‖varPart p (walk)‖_p ≤ C ⨆_{chains} (∑_i ‖jump_i‖_{ℓᵖ}^R)^{1/R}`,

then `A7Hi.bandSumSqRep` (P1, proved for every `1 < p < ∞`, uniform in `l₁, m₀, I`) on each block
`jump_i = ∑_{k ∈ Finset.Ico a b} Δ_k f`, and finally the *disjoint-frequency-support* comparison

  `(∑_i ‖S_{I_i}‖_{ℓᵖ}^R)^{1/R} ≤ C ‖ (∑_i S_{I_i}²)^{1/2} ‖_{ℓᵖ}`,
  `S_I = (∑_{k∈I} |Δ_k f|²)^{1/2}`,

which is the **Rubio de Francia** phenomenon: it is FALSE for a general family (take `M` disjoint
blocks of `L^p`-norm `M^{-1/2}`; the `ℓ^R ↮ ℓ²` reversal), and it is exactly where the disjointness
of the frequency supports enters.  `Work.Analysis.RubioDeFrancia` is the tree's chapter for it;
note carefully its REFUTED shortcuts in `NOTES_RF_square_function.md` (the signed-sup / linearised
form is FALSE), its PROVED parts (`square_function_l2`, the Khintchine randomisation
`Work.KMTAreas.RFVec.randomizedSqSum_eLpNorm`, and `sqSum_le_eLpNorm_of_maximal`), and the
`Work.KMTAreas.A7.lattice_sq_le_maximal`-style lattice reductions.

If the full `p ≤ 2` range is out of reach, prove the sub-range that your argument reaches and say
so — but do not close the target by appealing to a `sorry`-carrying declaration.

`Work.KMTAreas.A7Hi.chainPart`, `lpf`, `sqFun` and the interface lemmas are in
`A7Hi/LowpassDefs.lean`; `Work.KMTAreas.A7Hi.chainPart_le_iSup_VtrC` and
`Work.KMTAreas.A7Lpd.lacunaryMaxAux` contain the two-point/telescoping reductions that are already
proved. -/
theorem chainPartSqFunLeTwo (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hp2 : p ≤ 2) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.MemLp f p MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7HiRep
