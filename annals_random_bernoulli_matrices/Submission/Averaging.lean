import Mathlib
import Submission.RoughDecayFinal
import Submission.RefineExport
import Submission.Reduction
import Submission.PropRefineExport
import Submission.PropRefinePhase2
import Submission.Sec3Tower
import Submission.ProdCount
import Submission.IntFun
import Submission.Refine2
import Submission.Ell2Greedy
import Submission.Commons.Analysis.Real.ceil_pow_drop
import Submission.Commons.Analysis.Real.exists_geom_pow_le_one_div

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Theorem `th: averaging` (Tikhomirov 2020) — assembly

STEP 1 (this file): level-function relations on prefixes/blocks — averaging
extra coordinates can only lower `esup`, and restriction/pre-composition
round-trips on `pre`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure

namespace Submission.Averaging

/-!
## Roadmap to `averaging` (th: averaging, Tikhomirov 2020, lines 1470-1526)

DONE in this file (all verified, axiom-clean):
- §1: esup decreases when coordinates are added (`esup_lvl_decreasing`).
- §3/4/5/6/7: prefix families (`prefam`, `admissible_prefam`, ...), esup⇔pointwise
  utilities, `rough_step0` (Event₀ bound at a level-ℓ family, rate ε/2, −2Mn),
  `exists_alpha_level` (α ∈ [1/2,1) with b^⌈αn⌉ ≤ a^n/√n, b := 1−p+ε/2,
  a := 1−p+ε), `ceil_alpha_le/ge_half/alpha_level_bounds`, `hmax_from_level`.
- §8: prefix/suffix Finset-count machinery: `filter_prefix_card` (ℕ equality:
  |{x ∈ prodFinset n A : P (pre x b hb)}| = |prefix-filter| · ∏_{Fin(n−b)}|A⟨b+·⟩|),
  `prod_factor`, real forms `filter_prefix_card_real`/`prod_factor_real`.
- §9: block-split via `Refine2.cat`: `cat_pre_head`, `cat_tailVec`,
  `cat_split_eq`, `cat_injective`, `cat_mem_prodFinset`, `prodFinset_cat_image`,
  `filter_cat_split_real` (|{p ∈ ∏(a+s) C : P(pre p a) ∧ Q p}|_ℝ =
  Σ_{p0 ∈ head-prod.filter P} |block-filter Q(cat p0 ·)|_ℝ).
- §10: `kernel_window_mass` (level-k kernel window mass ≤ (C₂/√(δ₀p))/√n for
  any tuple of the admissible product, given δ₀ ≤ δ, k ≥ δ₀n, slack
  (δ−δ₀)n ≥ 1, via `RoughDecay.aux_simple_ac2` + `bigCoordSet_card`).
- §11: `e0_full_bound` (Event₀ full-product bound at level ℓ := ⌈αn⌉:
  |{x : L/(N√n) < esup(lvl f p ℓ (pre x ℓ))}|_ℝ ≤ e^{−2Mn}·∏_Fin n|A|_ℝ).
- §12: chain: `esup_gt_mono_pre`, `first_failure_subset`, `first_failure_card_le`.
- §13: block identities: `sqrtDen`, `fcard`, `allAll`, `cast_card_prod`, `blkFam`,
  `blkAll`, `pre_self_any`, `lvl_esup_cat_eq`, `blk_prod_factor`,
  `prod_fin_congr_equiv_real`.
- §17: `export_hpre` (PER-PREFIX EXPORT INSTANTIATION DONE): given the export
  pair-count bound `hExp` for every kernel `lvl f p a u` and the block interval
  data (c,d,loS,hiS with A⟨a+·⟩ = Icc(c)(d), A⟨a+m+·⟩ = Icc(loS)(hiS), length
  bounds), derives `refine_block_bound`'s hpre: per prefix p0 (with kernel
  sup-bound) bad-z-count ≤ e2·blkAll.  Assembles: lvl_nonneg/lvl_sq_summable/
  lvl_summable/lvl_ratioLip/norm₁_lvl_le_one/kernel_window_mass_pre/esup_le_iff
  → hExp; pair_filter_card (fam halves ↔ Icc halves via hfam1eq/hfam2eq) +
  pre_self filter-congruence + blkAll_split + hint1/2 for the products.
- §14: `refine_block_bound` (PER-BLOCK BOUND DONE): for prefixes p0 of length a
  with esup(lvl f p a p0) ≤ Lp/D, if per-prefix bad-block counts (level-2m
  kernel esup > θ·Lp/D) are ≤ e2·∏_block (this is exactly what the export
  gives), then |{x : esup(g_a) ≤ Lp/D ∧ Lc/D < esup(g_{a+2m})}|_ℝ ≤ e2·∏all
  (θ·Lp ≤ Lc).  Pure combinatorics: filter_cat_split_real + filter_prefix_card
  (unfold the let-predicates with `simpa [fcard, C, Pfun, Phead, Q]`) +
  cast_card_prod/blk_prod_factor.

The target `averaging` (th: averaging, counting form) is now PROVED (see the bottom of this file).  Its proof assembly was:
plan (dependency order) — see Session-21/22 notes in the project log:

(1) constants in `averaging`: rcases `rough_step0` (M := M, δ, ε) → ⟨Lr, nr⟩;
    rcases `RoughDecay.aux_simple_ac2` → ⟨C₂⟩; R̃ := max 1 (C₂/√((δ/2)·p));
    θ := p/√2+1−p ∈ (0,1); q : ℕ ≥ 1 with θ^q ≤ 1/Lr via
    `Commons.Analysis.Real.exists_geom_pow_le_one_div`; α ∈ [1/2,1) and nα via
    `exists_alpha_level`; ε̃ := (1−α)/(4·q) (0 < ε̃ ≤ 1/8; factor 4 = safety);
    m := ⌊ε̃·(n:ℝ)/2⌋; export constants: rcases
    `RefineExport.prop_refinement_even (M := 2·M)(ε := ε̃)(Rt := R̃)
     (L0 := max (16·R̃) Lr)(p := p)` → ⟨nRef⟩; output L := 16·R̃, η :=
     (PropRefine3.mu0 (2·M) ε̃)^4, n₀ := max of all n₀'s (incl. n ≥ 2/δ for
     the mass-slack, n ≥ ln(Q+1)/M-absorption, ⌊(n−ℓ)/(2m)⌋ ≥ ⌈q⌉, ε̃n ≥ 2, ...).
(2) Event₀ full product: |{x ∈ X : L/(N√n) < esup (lvl f p ℓ (pre x ℓ))}|_ℝ
    ≤ e^{−2Mn}·∏_Fin n|A| via `filter_prefix_card_real` at b := ℓ (ℓ := ⌈αn⌉)
    + `rough_step0` on the ℓ-prefix family + `hmax_from_level` fed by
    `exists_alpha_level`'s hαn (needs n ≥ nα) + hNa from
    (N:ℝ) ≤ (1/(1−p+ε))^n ⟺ N·(1−p+ε)^n ≤ 1.
(3) Instantiate `refine_block_bound` per block j (levels
    i_j := ℓ + j·(2·m), j ≤ Q' := ⌊(n−ℓ)/(2·m)⌋):
    |{x ∈ X : E_{j−1}(x) ∧ ¬E_j(x)}|_ℝ ≤ e^{−2Mn}·∏_Fin n|A|_ℝ where
    E_j x := esup(lvl f p i_j (pre x i_j)) ≤ L_j/(N√n),
    L_j := max (16·R̃) (θ^j·Lr), L₀ := max (16·R̃) Lr.
    Steps: filter_prefix_card_real at b := i_j gives the ∏_{after}-factor and a
    prefix count over prodFinset i_j (prefam A h); decompose the prefix count
    via `filter_cat_split_real` (head := first a coords, block := next 2·m);
    per head p0 ∈ E_{j−1}-filter the kernel g := lvl f p a p0 satisfies the
    export hypotheses: hlip via `lvl_ratioLip` (ratioLip (mu0(2M)ε̃^4) g from
    f's ratioLip η — η := (mu0 (2M) ε̃)^4), hmass via `kernel_window_mass`
    (δ₀ := δ/2, n-slack), hnorm1 via `norm₁_lvl_le_one`, hfsupL from E_{j−1};
    instantiate `prop_refinement_even` (L := L_{j−1}, m := ⌊ε̃n/2⌋) with the
    block's first-m and second-m single intervals (from
    `single_interval_of_large` + `not_smallIndex_of_ge_half`, since block
    coords ≥ ℓ ≥ n/2) as c,d/loS,hiS and N ≤ |Icc| (single_interval gives
    (N:ℤ) ≤ d−c+1; convert to ℝ); the export's predicate is exactly
    {esup(lvl g p (2·m) (catTwo pz)) > (√2p+2(1−p))·L_{j−1}/(2N√n)} =
    {θ·L_{j−1}/(N√n) < ...} and ¬E_j ⊆ that (θ·L_{j−1} ≤ L_j since
    θ ≤ 1: max(16θR̃, θ^j Lr) ≤ max(16R̃, θ^j Lr)); per-prefix count of bad
    block vectors ≤ e^{−2Mn}·∏_block|A|; sum over p0 ∈ E_{j−1}-filter
    (≤ ∏_{<a}|A| by prodFinset_card + filter_subset) gives ≤ e^{−2Mn}·∏_{<i_j}|A|;
    multiply by ∏_{after} → ≤ e^{−2Mn}·∏_all|A|.
    NOTE: block values z ∈ block product correspond 1-1 to (u,w)-pairs under
    catTwo via `tailVec`/`pre`/`catTwo`-splitting (u := pre z m,
    w := (last-m coords); membership in ∏ block intervals ⟺ pair membership),
    reuse `filter_cat_split_real` at both levels or a 3-part split.
(4) Chain: ¬E_{Q'} ⊆ ¬E₀ ∪ ⋃_{j=1}^{Q'} (E_{j−1}∧¬E_j) (first-failure, pure
    Finset; Q' := ⌊(n−ℓ)/(2·m)⌋ ≥ ⌈q⌉ for n large so L_{Q'} = 16·R̃).
    Level-n event ⊆ level-i_{Q'} event via `esup_lvl_decreasing`
    (n ≥ i_{Q'}).  Final: |{x : 16R̃/(N√n) < esup(lvl f p n x)}|_ℝ
    ≤ (Q'+1)·e^{−2Mn}·∏_all|A|_ℝ ≤ e^{−Mn}·∏_all|A|_ℝ since Q'+1 ≤ n+1 ≤ e^{Mn}.
(5) Assemble `averaging` (N ≤ (1−p+ε)^{−n} hypothesis gives both hNpow
    (N ≤ 2^n: 1/(1−p+ε) ≤ 2 since ε < p ≤ 1/2) and hNa).
Watch: `2 * m` ≠ `m + m`; balanced parens in filter-card statements; `ℓ + j·(2*m)`
levels written additively for `pre_cat_tail`; proof-args bridged by
pre_irrel/W.t_irrel-style rfl; use `exact_mod_cast` for card casts.
-/


attribute [local instance] Classical.propDecidable

open Submission.Sec3
open Submission.Sec3Tower
open Submission.IntFun
open Submission.ProdCount
open Submission.PropRefineExport
open Submission.Ell2Greedy
open Submission.Sec3
open Submission.PropRefinePhase2
open Submission.Refine2
open Submission.Reduction
open Submission.Admissible
open Submission.Ell2Update
open Submission.RoughDecay
open Submission.RefineExport

/-! ## 1. esup decreases when coordinates are added -/

/-- Restricting twice: `pre (pre x s hs) k hks = pre x k (hks ∘ hs)`. -/
lemma pre_pre_general {ℓ : ℕ} (x : Fin ℓ → ℤ) {s k : ℕ}
    (hks : k ≤ s) (hsℓ : s ≤ ℓ) :
    pre (pre x s hsℓ) k hks = pre x k (le_trans hks hsℓ) := by
  funext j
  dsimp [pre]
  have hj : Fin.castLE hsℓ (Fin.castLE hks j) = Fin.castLE (le_trans hks hsℓ) j := by
    apply Fin.ext
    rfl
  rw [hj]

/-- One extra averaging step never raises the supremum (clean `lvl` form). -/
lemma esup_step_le {f : ℤ → ℝ} {p : unitInterval} {k : ℕ}
    (x : Fin (k + 1) → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    esup (lvl f p (k + 1) x) ≤ esup (lvl f p k (pre x k (Nat.le_succ k))) := by
  have hmain := esup_lvl_step_le (f := f) (p := p) (ℓ := k) (x := x) hfpos hf
  have hpre : pre x (k + 1) (Nat.succ_le_of_lt (Nat.lt_succ_self k)) = x := by
    calc
      pre x (k + 1) (Nat.succ_le_of_lt (Nat.lt_succ_self k)) = pre x (k + 1) (le_refl (k + 1)) := by
        exact pre_irrel x
      _ = x := pre_self x
  have hmain' : esup (lvl f p (k + 1) x) ≤
      esup (lvl f p k (pre x k (le_of_lt (Nat.lt_succ_self k)))) := by
    simpa [hpre] using hmain
  calc
    esup (lvl f p (k + 1) x) ≤ esup (lvl f p k (pre x k (le_of_lt (Nat.lt_succ_self k)))) := hmain'
    _ = esup (lvl f p k (pre x k (Nat.le_succ k))) := by
          exact congrArg (fun g => esup (lvl f p k g)) (pre_irrel x)

/-- helper for `esup_lvl_decreasing`: recursion-friendly layout. -/
private lemma esup_lvl_decreasing_aux {f : ℤ → ℝ} {p : unitInterval}
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    ∀ s : ℕ, ∀ (k : ℕ) (hk : k ≤ s), ∀ (x : Fin s → ℤ),
      esup (lvl f p s x) ≤ esup (lvl f p k (pre x k hk)) := by
  intro s
  induction s with
  | zero =>
      intro k hk x
      have hk0 : k = 0 := by omega
      subst hk0
      have hEq : lvl f p 0 (pre x 0 hk) = lvl f p 0 x := by
        rw [lvl_zero, lvl_zero]
      rw [hEq]
  | succ s ih =>
      intro k hk x
      by_cases hks : k = s + 1
      · subst k
        have hpre' : pre x (s + 1) hk = x := by
          calc
            pre x (s + 1) hk = pre x (s + 1) (le_refl (s + 1)) := pre_irrel x
            _ = x := pre_self x
        rw [hpre']
      · have hk' : k ≤ s := by omega
        have hstep := esup_step_le (f := f) (p := p) (k := s) (x := x) hfpos hf
        have hi := ih k hk' (pre x s (Nat.le_succ s))
        calc
          esup (lvl f p (s + 1) x) ≤ esup (lvl f p s (pre x s (Nat.le_succ s))) := hstep
          _ ≤ esup (lvl f p k (pre (pre x s (Nat.le_succ s)) k hk')) := hi
          _ = esup (lvl f p k (pre x k hk)) := by
                have hg := pre_pre_general (x := x) (s := s) (k := k) hk' (Nat.le_succ s)
                have hg' : pre (pre x s (Nat.le_succ s)) k hk' = pre x k hk := by
                  calc
                    pre (pre x s (Nat.le_succ s)) k hk' = pre x k (le_trans hk' (Nat.le_succ s)) := hg
                    _ = pre x k hk := pre_irrel x
                rw [hg']

/-- Averaging more coordinates never raises the supremum: for `k ≤ s`,
`esup` of the level-`s` function of `x` is at most the level-`k` function of its
`k`-prefix. -/
lemma esup_lvl_decreasing {f : ℤ → ℝ} {p : unitInterval} {s k : ℕ} (hk : k ≤ s)
    (x : Fin s → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) :
    esup (lvl f p s x) ≤ esup (lvl f p k (pre x k hk)) := by
  have h := esup_lvl_decreasing_aux (f := f) (p := p) hfpos hf s k hk x
  simpa using h


/-! ## 2. The counting-form theorem (paper Theorem `th: averaging`) -/

/-! (theorem `averaging` — th: averaging, counting form — is stated and proved at the
bottom of this file, after all machinery it uses.) -/


/-! ## 3. Prefix coordinate families: admissibility and products -/

/-- The first `ℓ` coordinates of a length-`n` coordinate family. -/
def prefam {n : ℕ} (A : Fin n → Finset ℤ) {ℓ : ℕ} (hℓ : ℓ ≤ n) : Fin ℓ → Finset ℤ :=
  fun j => A (Fin.castLE hℓ j)

/-- membership of the prefix family. -/
lemma mem_prefam {n ℓ : ℕ} {A : Fin n → Finset ℤ} {hℓ : ℓ ≤ n} {j : Fin ℓ} {a : ℤ} :
    a ∈ prefam A hℓ j ↔ a ∈ A (Fin.castLE hℓ j) := by
  rfl

/-- The prefix of a tuple in the full product lies in the prefix product. -/
lemma pre_mem_prodFinset {n ℓ : ℕ} {A : Fin n → Finset ℤ} (hℓ : ℓ ≤ n)
    {x : Fin n → ℤ} (hx : x ∈ prodFinset n A) :
    pre x ℓ hℓ ∈ prodFinset ℓ (prefam A hℓ) := by
  rw [mem_prodFinset]
  intro j
  change x (Fin.castLE hℓ j) ∈ A (Fin.castLE hℓ j)
  exact (mem_prodFinset A x).1 hx (Fin.castLE hℓ j)

/-- `smallIndex` at a prefix coordinate agrees with the same index in `Fin n`. -/
lemma smallIndex_prefam {n ℓ : ℕ} (δ : ℝ) {hℓ : ℓ ≤ n} {j : Fin ℓ} :
    smallIndex n δ (j.val) = smallIndex n δ ((Fin.castLE hℓ j).val) := by
  rfl

/-- The prefix of an admissible family is admissible at the same `(N,n,δ)`. -/
lemma admissible_prefam {N n ℓ : ℕ} {δ : ℝ} {A : Fin n → Finset ℤ} (hℓ : ℓ ≤ n)
    (hA : Admissible N n n δ A) :
    Admissible N n ℓ δ (prefam A hℓ) := by
  constructor
  · intro i hi
    rcases (hA.1 (Fin.castLE hℓ i)) (by simpa [smallIndex] using hi) with ⟨c₁, d₁, c₂, d₂, hcov, h₁, h₂, hd, hbig⟩
    refine ⟨c₁, d₁, c₂, d₂, ?_, h₁, h₂, hd, ?_⟩
    · ext a
      rw [mem_prefam]
      rw [hcov]
    · intro a ha
      exact hbig a ha
  · intro i hi
    rcases (hA.2 (Fin.castLE hℓ i)) (by simpa [smallIndex] using hi) with ⟨c, d, hcov, h₁⟩
    refine ⟨c, d, ?_, h₁⟩
    ext a
    rw [mem_prefam]
    rw [hcov]

/-- The radius bound restricts to prefixes. -/
lemma hrad_prefam {n ℓ : ℕ} {A : Fin n → Finset ℤ} {hℓ : ℓ ≤ n} {r : ℤ}
    (hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → |a| ≤ r) :
    ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ prefam A hℓ j → |a| ≤ r := by
  intro j a ha
  exact hrad (Fin.castLE hℓ j) a (by simpa [mem_prefam] using ha)

/-- The symmetry bound restricts to prefixes. -/
lemma hsym_prefam {n ℓ : ℕ} {A : Fin n → Finset ℤ} {hℓ : ℓ ≤ n}
    (hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → -a ∈ A j) :
    ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ prefam A hℓ j → -a ∈ prefam A hℓ j := by
  intro j a ha
  rw [mem_prefam]
  exact hsym (Fin.castLE hℓ j) a (by simpa [mem_prefam] using ha)

/-- Coordinates strictly above `ℓ ≥ δn` are not small (`δ ≤ 1/2`, `ℓ ≥ n/2`). -/
lemma not_smallIndex_of_ge_half {n : ℕ} {δ : ℝ} (hδ : δ ≤ 1 / 2) {ℓ : ℕ} (hℓ : n ≤ 2 * ℓ)
    {j : ℕ} (hj : ℓ ≤ j) (hjn : j < n) : ¬ smallIndex n δ j := by
  intro hsm
  have hj1 : (j : ℝ) + 1 ≤ δ * (n : ℝ) := hsm
  have hjnR : (j : ℝ) < (n : ℝ) := by exact_mod_cast hjn
  have hℓR : (ℓ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hn2ℓ : (n : ℝ) ≤ 2 * (ℓ : ℝ) := by exact_mod_cast hℓ
  have hδn : δ * (n : ℝ) ≤ (1 / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hδ (by exact_mod_cast (Nat.zero_le n))
  nlinarith


/-! ## 4. esup ⇔ pointwise utilities -/

/-- `esup g ≤ c` iff every point value is `≤ c` (for nonnegative summable
`g`). -/
lemma esup_le_iff {g : ℤ → ℝ} (hgpos : ∀ t : ℤ, 0 ≤ g t) (hg : Summable g) {c : ℝ} :
    esup g ≤ c ↔ ∀ t : ℤ, g t ≤ c := by
  constructor
  · intro h t
    exact le_trans (le_esup hgpos hg t) h
  · intro h
    dsimp [esup]
    exact csSup_le (s := Set.range g) (a := c) ⟨g 0, ⟨0, rfl⟩⟩ (by
      intro b hb
      rcases hb with ⟨t, rfl⟩
      exact h t)

/-- `esup g > c` iff some point value is `> c` (for nonnegative summable
`g`). -/
lemma esup_gt_iff {g : ℤ → ℝ} (hgpos : ∀ t : ℤ, 0 ≤ g t) (hg : Summable g) {c : ℝ} :
    c < esup g ↔ ∃ t : ℤ, c < g t := by
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    have hle : esup g ≤ c := (esup_le_iff hgpos hg).2 hnot
    exact (not_lt_of_ge hle) h
  · intro h
    rcases h with ⟨t, ht⟩
    exact lt_of_lt_of_le ht (le_esup hgpos hg t)

/-- Negation of `esup g > c` is `∀ t, g t ≤ c`. -/
lemma not_esup_gt {g : ℤ → ℝ} (hgpos : ∀ t : ℤ, 0 ≤ g t) (hg : Summable g) {c : ℝ} :
    (¬ c < esup g) ↔ ∀ t : ℤ, g t ≤ c := by
  rw [← esup_le_iff hgpos hg]
  exact not_lt


/-! ## 5. Event₀: rough decay at level ℓ with the max eliminated -/

/-- Event₀ (prefix level `ℓ`) bound: with `((1−p+ε/2)^ℓ)·esup f ≤ L/(N√n)`, the
rough-decay bound at rate `ε/2` counts exactly the prefixes whose level-`ℓ`
average exceeds `L/(N√n)` somewhere, giving `≤ e^{−2Mn}·∏|A_j|`. -/
theorem rough_step0 {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ))
    {M : ℝ} (hM1 : 1 ≤ M) :
    ∃ (L : ℝ) (n₀ : ℕ), 1 ≤ L ∧ 2 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N),
        (N : ℝ) ≤ (2 : ℝ) ^ n →
        ∀ (ℓ : ℕ) (hℓge : n ≤ 2 * ℓ) (hℓle : ℓ ≤ n),
        ∀ (A : Fin ℓ → Finset ℤ)
          (hAdm : Admissible N n ℓ δ A)
          (hrad : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
        ∀ (f : ℤ → ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1)
          (hmax : ((1 - (p : ℝ) + ε / 2) ^ ℓ) * esup f ≤
            L / ((N : ℝ) * Real.sqrt (n : ℝ))),
          (((prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
            L / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ x))).card : ℝ) ≤
            Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  have hMpos : 0 < 2 * M := by linarith
  have hε2pos : 0 < ε / 2 := div_pos hε₀ (by norm_num : (0 : ℝ) < 2)
  have hε2p : ε / 2 < (p : ℝ) := by linarith
  rcases RoughDecayFinal.rough_decay (M := 2 * M) hMpos (p := p) hp₀ hp₁
      (δ := δ) hδ₀ hδ₁₂ (ε := ε / 2) hε2pos hε2p with ⟨L, n₁, hL1, hn₁2, hR⟩
  refine ⟨L, max n₁ 2, hL1, by simp, ?_⟩
  intro n hn₀ N hN1 hNpow ℓ hℓge hℓle A hAdm hrad hsym f hfpos hfsum hfmass hmax
  have hn₁ : n₁ ≤ n := by
    have h1 : n₁ ≤ max n₁ 2 := le_max_left n₁ 2
    exact le_trans h1 hn₀
  have h2n : 2 ≤ n := le_trans (by simp : 2 ≤ max n₁ 2) hn₀
  have hb := hR n hn₁ N hN1 hNpow ℓ hℓge hℓle A hAdm hrad hsym f hfpos hfsum hfmass
  -- eventPred with ε/2 equals the esup>threshold event once the max is the
  -- threshold itself
  have hev : (prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        Submission.RoughAssembly.eventPred f p L (N : ℝ) (n : ℝ) (ε / 2) x) =
      (prodFinset ℓ A).filter (fun x : Fin ℓ → ℤ =>
        L / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ x)) := by
    apply Finset.filter_congr
    intro x hx
    dsimp [Submission.RoughAssembly.eventPred]
    have hlm : max (L / ((N : ℝ) * Real.sqrt (n : ℝ)))
          ((1 - (p : ℝ) + ε / 2) ^ ℓ * esup f) = L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
      exact max_eq_left hmax
    rw [hlm]
    rw [esup_gt_iff (g := lvl f p ℓ x) (lvl_nonneg ℓ x hfpos) (lvl_summable ℓ x hfsum)]
    apply exists_congr
    intro t
    have hfl : flvl f p x ℓ (le_refl ℓ) t = lvl f p ℓ x t := by
      simp [flvl, lvl, pre_self]
    rw [hfl]
  rw [hev] at hb
  simpa [mul_assoc] using hb


/-! ## 6. Level choice: `α` and `ℓ := ⌈αn⌉` -/

/-- The `α`-level choice: for `p ∈ (0,1/2]`, `0 < ε < p`, `b := 1−p+ε/2`,
`a := 1−p+ε`: there is `α ∈ [1/2,1)` such that `b^⌈αn⌉ ≤ a^n/√n` eventually. -/
lemma exists_alpha_level {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ)) :
    ∃ (α : ℝ), 1 / 2 ≤ α ∧ α < 1 ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (1 - (p : ℝ) + ε / 2) ^ (Nat.ceil (α * (n : ℝ))) ≤
          (1 - (p : ℝ) + ε) ^ n / Real.sqrt (n : ℝ) := by
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  let a : ℝ := 1 - (p : ℝ) + ε
  have hb0 : 0 < b := by
    dsimp [b]
    have h1 : (p : ℝ) ≤ 1 := by linarith
    nlinarith [hε₀]
  have hba : b < a := by
    dsimp [b, a]
    nlinarith [hε₀]
  have ha1 : a < 1 := by
    dsimp [a]
    nlinarith [hp₀, hεp]
  rcases Commons.Analysis.Real.ceil_pow_drop (a := a) (b := b) hb0 hba ha1 with ⟨α, hα₁, hα₂, hres⟩
  refine ⟨α, hα₁, hα₂, ?_⟩
  rcases hres with ⟨n₀, h⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  simpa [b, a] using h n hn

/-- `⌈αn⌉ ≤ n` when `α < 1`. -/
lemma ceil_alpha_le {n : ℕ} {α : ℝ} (hα₁ : α < 1) :
    Nat.ceil (α * (n : ℝ)) ≤ n := by
  have hαn : α * (n : ℝ) ≤ (n : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    calc
      α * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right (le_of_lt hα₁) hn0
      _ = (n : ℝ) := by simp
  exact (Nat.ceil_le (a := α * (n : ℝ)) (n := n)).mpr hαn

/-- `2·⌈αn⌉ ≥ n` when `α ≥ 1/2`. -/
lemma ceil_alpha_ge_half {n : ℕ} {α : ℝ} (hα₀ : 1 / 2 ≤ α) :
    n ≤ 2 * Nat.ceil (α * (n : ℝ)) := by
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hαn : (n : ℝ) ≤ 2 * (α * (n : ℝ)) := by
    calc
      (n : ℝ) = 2 * ((1 / 2) * (n : ℝ)) := by ring
      _ ≤ 2 * (α * (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hα₀ hn0) (by norm_num : (0 : ℝ) ≤ 2)
  have hceil : α * (n : ℝ) ≤ (Nat.ceil (α * (n : ℝ)) : ℝ) := Nat.le_ceil (α * (n : ℝ))
  have hmul : 2 * (α * (n : ℝ)) ≤ 2 * (Nat.ceil (α * (n : ℝ)) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hceil (by norm_num : (0 : ℝ) ≤ 2)
  have hR : (n : ℝ) ≤ ((2 * Nat.ceil (α * (n : ℝ)) : ℕ) : ℝ) := by
    calc
      (n : ℝ) ≤ 2 * (α * (n : ℝ)) := hαn
      _ ≤ 2 * (Nat.ceil (α * (n : ℝ)) : ℝ) := hmul
      _ = ((2 * Nat.ceil (α * (n : ℝ)) : ℕ) : ℝ) := by
            have hc : ((2 * Nat.ceil (α * (n : ℝ)) : ℕ) : ℝ) = 2 * (Nat.ceil (α * (n : ℝ)) : ℝ) := by
              norm_num [Nat.cast_mul]
            exact hc.symm
  exact_mod_cast hR

/-- `ℓ := ⌈αn⌉` has `ℓ ≤ n` and `n ≤ 2ℓ`. -/
lemma alpha_level_bounds {n : ℕ} {α : ℝ} (hα₀ : 1 / 2 ≤ α) (hα₁ : α < 1) :
    Nat.ceil (α * (n : ℝ)) ≤ n ∧ n ≤ 2 * Nat.ceil (α * (n : ℝ)) := by
  constructor
  · exact ceil_alpha_le hα₁
  · exact ceil_alpha_ge_half hα₀


/-! ## 7. Deriving the Event₀ sup-bound from the level inequality -/

/-- With `1 ≤ N·a^n`-style bound (`hNa : N·a^n ≤ 1`) and `b^ℓ ≤ a^n/√n`, the
level-`ℓ` multiplier satisfies `b^ℓ · esup f ≤ L/(N√n)` for `L ≥ 1` and
`esup f ≤ 1`. -/
lemma hmax_from_level {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ))
    {α : ℝ} (hα₀ : 1 / 2 ≤ α) (hα₁ : α < 1) (n : ℕ) (hn1 : 1 ≤ n)
    (hαn : (1 - (p : ℝ) + ε / 2) ^ (Nat.ceil (α * (n : ℝ))) ≤
      (1 - (p : ℝ) + ε) ^ n / Real.sqrt (n : ℝ))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hNa : (N : ℝ) * (1 - (p : ℝ) + ε) ^ n ≤ 1)
    {L : ℝ} (hL1 : 1 ≤ L)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f) (hfmass : norm₁ f ≤ 1) :
    ((1 - (p : ℝ) + ε / 2) ^ (Nat.ceil (α * (n : ℝ)))) * esup f ≤
      L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
  let b : ℝ := 1 - (p : ℝ) + ε / 2
  let a : ℝ := 1 - (p : ℝ) + ε
  have hb0 : 0 < b := by dsimp [b]; nlinarith [hε₀]
  have ha0 : 0 < a := by dsimp [a]; nlinarith
  have ha1 : a < 1 := by dsimp [a]; nlinarith [hp₀, hεp]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hbpos : 0 < b ^ Nat.ceil (α * (n : ℝ)) := pow_pos hb0 _
  have hesup1 : esup f ≤ 1 := by
    calc
      esup f ≤ norm₁ f := esup_le_norm₁ hfpos hfsum
      _ ≤ 1 := hfmass
  have hb0' : 0 ≤ b := le_of_lt hb0
  have hmult : b ^ Nat.ceil (α * (n : ℝ)) * esup f ≤ b ^ Nat.ceil (α * (n : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hesup1 (pow_nonneg hb0' (Nat.ceil (α * (n : ℝ))))
    simpa using h
  have hchain1 : b ^ Nat.ceil (α * (n : ℝ)) * esup f ≤ a ^ n / Real.sqrt (n : ℝ) := by
    calc
      b ^ Nat.ceil (α * (n : ℝ)) * esup f ≤ b ^ Nat.ceil (α * (n : ℝ)) := hmult
      _ ≤ a ^ n / Real.sqrt (n : ℝ) := by
            simpa [b, a] using hαn
  have hNpos' : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have han0 : 0 ≤ a ^ n := pow_nonneg ha0.le n
  have hNa' : (N : ℝ) * a ^ n ≤ L := by
    calc
      (N : ℝ) * a ^ n ≤ 1 := by simpa [a] using hNa
      _ ≤ L := hL1
  have haLn : a ^ n / Real.sqrt (n : ℝ) ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ hsqrt (mul_pos hNpos hsqrt)]
    -- a^n · (N·√n) ≤ L · √n
    have hdiv : a ^ n * (N : ℝ) ≤ L := by
      calc
        a ^ n * (N : ℝ) = (N : ℝ) * a ^ n := by ring
        _ ≤ L := hNa'
    have hmul : a ^ n * ((N : ℝ) * Real.sqrt (n : ℝ)) ≤ L * Real.sqrt (n : ℝ) := by
      calc
        a ^ n * ((N : ℝ) * Real.sqrt (n : ℝ)) = (a ^ n * (N : ℝ)) * Real.sqrt (n : ℝ) := by ring
        _ ≤ L * Real.sqrt (n : ℝ) := by
              exact mul_le_mul_of_nonneg_right hdiv hsqrt.le
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  exact le_trans hchain1 haLn



/-! ## 8. Prefix / suffix Finset-count machinery -/

def finEquivOfEq {n m : ℕ} (h : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by
    intro a
    apply Fin.ext
    simp [Fin.cast]
  right_inv := by
    intro b
    apply Fin.ext
    simp [Fin.cast]



/-- Reindexing a real-valued product over `Fin` by an equality of the lengths. -/
lemma prod_fin_congr_equiv_real {n m : ℕ} (h : n = m) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : ∀ j : Fin n, f j = g (Fin.cast h j)) :
    (∏ j : Fin n, f j) = (∏ j : Fin m, g j) := by
  exact Fintype.prod_equiv (e := finEquivOfEq h) (f := f) (g := g) (by intro j; exact hfg j)

lemma prod_fin_congr_equiv_nat {n m : ℕ} (h : n = m) (f : Fin n → ℕ) (g : Fin m → ℕ)
    (hfg : ∀ j : Fin n, f j = g (Fin.cast h j)) :
    (∏ j : Fin n, f j) = (∏ j : Fin m, g j) := by
  exact Fintype.prod_equiv (e := finEquivOfEq h) (f := f) (g := g) (by intro j; exact hfg j)

lemma prod_tail_succ_nat {n b : ℕ} (hbn : b ≤ n) (A : Fin (n + 1) → Finset ℤ) :
    (∏ t : Fin (n - b), (A (Fin.castSucc ⟨b + t.val, by omega⟩)).card) *
        (A ⟨n, by omega⟩).card
      = (∏ t : Fin (n + 1 - b), (A ⟨b + t.val, by omega⟩).card) := by
  have hAr : n + 1 - b = (n - b) + 1 := by omega
  let G : Fin ((n - b) + 1) → ℕ := fun t => (A ⟨b + t.val, by omega⟩).card
  have hcast : (∏ t : Fin (n + 1 - b), (A ⟨b + t.val, by omega⟩).card)
      = ∏ t : Fin ((n - b) + 1), G t := by
    apply prod_fin_congr_equiv_nat (h := hAr)
      (f := fun t : Fin (n + 1 - b) => (A ⟨b + t.val, by omega⟩).card) (g := G)
    intro j
    dsimp [G]
  have hfac1 : (∏ t : Fin (n - b), (A (Fin.castSucc ⟨b + t.val, by omega⟩)).card)
      = ∏ t : Fin (n - b), G (Fin.castSucc t) := by
    apply Finset.prod_congr rfl
    intro t ht
    dsimp [G]
  have hfac2 : (A ⟨n, by omega⟩).card = G (Fin.last (n - b)) := by
    dsimp [G]
    apply congrArg (fun u : Fin (n + 1) => (A u).card)
    apply Fin.ext
    simp
    omega
  calc
    (∏ t : Fin (n - b), (A (Fin.castSucc ⟨b + t.val, by omega⟩)).card) * (A ⟨n, by omega⟩).card
        = (∏ t : Fin (n - b), G (Fin.castSucc t)) * G (Fin.last (n - b)) := by
          rw [hfac1, hfac2]
    _ = ∏ t : Fin ((n - b) + 1), G t := by
          rw [Fin.prod_univ_castSucc]
    _ = (∏ t : Fin (n + 1 - b), (A ⟨b + t.val, by omega⟩).card) := hcast.symm

/-- The full product factors as the `b`-prefix product times the tail. -/
lemma prod_factor {n b : ℕ} (hb : b ≤ n) (A : Fin n → Finset ℤ) :
    (∏ j : Fin n, (A j).card) =
      (∏ j : Fin b, ((prefam A hb) j).card) *
        (∏ j : Fin (n - b), (A ⟨b + j.val, by omega⟩).card) := by
  classical
  induction n with
  | zero =>
      have hb0 : b = 0 := by omega
      subst b
      simp
  | succ n ih =>
      by_cases h : b = n + 1
      · subst b
        have hfam : prefam A (le_refl (n + 1)) = A := by
          funext j
          rfl
        have htail : (∏ j : Fin ((n + 1) - (n + 1)), (A ⟨(n + 1) + j.val, by omega⟩).card) = 1 := by
          have huniv : (Finset.univ : Finset (Fin ((n + 1) - (n + 1)))) = ∅ := by
            apply Finset.ext
            intro a
            constructor
            · intro h
              have ha0 : (a : ℕ) < (n + 1) - (n + 1) := a.isLt
              omega
            · intro h
              simp at h
          rw [huniv]
          simp
        calc
          (∏ j : Fin (n + 1), (A j).card)
              = (∏ j : Fin (n + 1), ((prefam A (le_refl (n + 1))) j).card) := by
                rw [hfam]
          _ = (∏ j : Fin (n + 1), ((prefam A (le_refl (n + 1))) j).card) * 1 := by ring
          _ = (∏ j : Fin (n + 1), ((prefam A (le_refl (n + 1))) j).card) *
                (∏ j : Fin ((n + 1) - (n + 1)), (A ⟨(n + 1) + j.val, by omega⟩).card) := by rw [htail]
      · have hbn : b ≤ n := by omega
        have hb' : b ≤ n + 1 := le_trans hbn (Nat.le_succ n)
        let A' : Fin n → Finset ℤ := fun j => A (Fin.castSucc j)
        have htop : (∏ j : Fin (n + 1), (A j).card) =
            (∏ j : Fin n, (A' j).card) * (A ⟨n, by omega⟩).card := by
          rw [Fin.prod_univ_castSucc]
          congr 1
        have hih := ih hbn A'
        have hmid : (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) * (A ⟨n, by omega⟩).card
            = (∏ t : Fin (n + 1 - b), (A ⟨b + t.val, by omega⟩).card) := by
          have hbridge : (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) * (A ⟨n, by omega⟩).card
              = (∏ j : Fin (n - b), (A (Fin.castSucc ⟨b + j.val, by omega⟩)).card) * (A ⟨n, by omega⟩).card := by
                congr 1
          rw [hbridge]
          exact prod_tail_succ_nat (n := n) (b := b) hbn (A := A)
        calc
          (∏ j : Fin (n + 1), (A j).card)
              = (∏ j : Fin n, (A' j).card) * (A ⟨n, by omega⟩).card := htop
          _ = ((∏ j : Fin b, ((prefam A' hbn) j).card) *
                (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card)) * (A ⟨n, by omega⟩).card := by rw [hih]
          _ = (∏ j : Fin b, ((prefam A' hbn) j).card) *
                ((∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) * (A ⟨n, by omega⟩).card) := by ring
          _ = (∏ j : Fin b, ((prefam A' hbn) j).card) *
                (∏ j : Fin (n + 1 - b), (A ⟨b + j.val, by omega⟩).card) := by rw [hmid]
          _ = (∏ j : Fin b, ((prefam A hb') j).card) *
                (∏ j : Fin (n + 1 - b), (A ⟨b + j.val, by omega⟩).card) := by
                congr 1

/-- `pre` of an extension by a new coordinate, restricted below the extension
level, is the `pre` of the base. -/
lemma pre_extend_le {ℓ b : ℕ} (hb : b ≤ ℓ) (y : Fin ℓ → ℤ) (a : ℤ) :
    pre (extendFin y a) b (le_trans hb (Nat.le_succ ℓ)) = pre y b hb := by
  funext j
  dsimp [pre, extendFin]
  have hij : Fin.castLE hb j = (⟨j.val, by omega⟩ : Fin ℓ) := by
    apply Fin.ext
    rfl
  have hlt : (j : ℕ) < ℓ := lt_of_lt_of_le j.isLt hb
  rw [hij]
  simp [hlt]


lemma card_filter_singleton {α : Type} (z : α) (Q : α → Prop) :
    (({z} : Finset α).filter Q).card = if Q z then 1 else 0 := by
  classical
  by_cases hq : Q z
  · have hfilter : ({z} : Finset α).filter Q = {z} := by
      apply Finset.ext
      intro a
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact h.1
      · intro h
        rw [h]
        exact ⟨rfl, hq⟩
    rw [hfilter, Finset.card_singleton]
    simp [hq]
  · have hfilter : ({z} : Finset α).filter Q = ∅ := by
      apply Finset.ext
      intro a
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        rcases h with ⟨ha, hQ⟩
        have : a = z := by simpa using ha
        subst a
        exact False.elim (hq hQ)
      · intro h
        exact False.elim (by simpa using h)
    rw [hfilter]
    simp [hq]

/-- Cardinality of tuples in a length-`n` product whose `b`-prefix satisfies
`P`, with the free suffix factored out. -/

lemma filter_prefix_card {n b : ℕ} (hb : b ≤ n) (A : Fin n → Finset ℤ)
    (P : (Fin b → ℤ) → Prop) :
    ((prodFinset n A).filter (fun x : Fin n → ℤ => P (pre x b hb))).card
      = ((prodFinset b (prefam A hb)).filter P).card *
          (∏ j : Fin (n - b), (A ⟨b + j.val, by omega⟩).card) := by
  classical
  induction n with
  | zero =>
      have hb0 : b = 0 := by omega
      subst b
      let z0 : Fin 0 → ℤ := fun _ : Fin 0 => (0 : ℤ)
      have hsingL : (prodFinset 0 A) = ({z0} : Finset (Fin 0 → ℤ)) := rfl
      have hsingR : (prodFinset 0 (prefam A hb)) = ({z0} : Finset (Fin 0 → ℤ)) := rfl
      have hpre : pre z0 0 hb = z0 := by
        funext j
        exact Fin.elim0 j
      calc
        ((prodFinset 0 A).filter (fun x : Fin 0 → ℤ => P (pre x 0 hb))).card
            = (({z0} : Finset (Fin 0 → ℤ)).filter (fun x : Fin 0 → ℤ => P (pre x 0 hb))).card := by rw [hsingL]
        _ = if P (pre z0 0 hb) then 1 else 0 := by rw [card_filter_singleton]
        _ = if P z0 then 1 else 0 := by rw [hpre]
        _ = (({z0} : Finset (Fin 0 → ℤ)).filter P).card := by rw [card_filter_singleton]
        _ = ((prodFinset 0 (prefam A hb)).filter P).card := by rw [hsingR]
        _ = ((prodFinset 0 (prefam A hb)).filter P).card * 1 := by simp
        _ = ((prodFinset 0 (prefam A hb)).filter P).card *
              (∏ j : Fin (0 - 0), (A ⟨0 + j.val, by omega⟩).card) := by simp
  | succ n ih =>
      by_cases h : b = n + 1
      · subst b
        have hfam : prefam A (le_refl (n + 1)) = A := by
          funext j
          rfl
        have htail : (∏ j : Fin ((n + 1) - (n + 1)), (A ⟨(n + 1) + j.val, by omega⟩).card) = 1 := by
          have huniv : (Finset.univ : Finset (Fin ((n + 1) - (n + 1)))) = ∅ := by
            apply Finset.ext
            intro a
            constructor
            · intro h
              have ha0 : (a : ℕ) < (n + 1) - (n + 1) := a.isLt
              omega
            · intro h
              simp at h
          rw [huniv]
          simp
        calc
          ((prodFinset (n + 1) A).filter (fun x : Fin (n + 1) → ℤ => P (pre x (n + 1) hb))).card
              = ((prodFinset (n + 1) A).filter (fun x : Fin (n + 1) → ℤ => P x)).card := by
                apply congrArg Finset.card
                apply Finset.filter_congr
                intro x hx
                rw [pre_self x]
          _ = ((prodFinset (n + 1) (prefam A (le_refl (n + 1)))).filter P).card := by
                congr 1
          _ = ((prodFinset (n + 1) (prefam A (le_refl (n + 1)))).filter P).card * 1 := by simp
          _ = ((prodFinset (n + 1) (prefam A (le_refl (n + 1)))).filter P).card *
                (∏ j : Fin ((n + 1) - (n + 1)), (A ⟨(n + 1) + j.val, by omega⟩).card) := by rw [htail]
      · have hbn : b ≤ n := by omega
        have hb' : b ≤ n + 1 := le_trans hbn (Nat.le_succ n)
        let A' : Fin n → Finset ℤ := fun j => A (Fin.castSucc j)
        have hpeel := Submission.RoughProduct.filter_card_fiber (A := A) (k := n)
          (P := fun x : Fin (n + 1) → ℤ => P (pre x b hb'))
        have hlast : (A (Fin.last n)) = A ⟨n, by omega⟩ := by
          congr 1
        have hfiber : ∀ y ∈ prodFinset n A', ((A (Fin.last n)).filter
              (fun a : ℤ => P (pre (extendFin y a) b hb'))).card
            = if P (pre y b hbn) then (A (Fin.last n)).card else 0 := by
          intro y hy
          by_cases hp : P (pre y b hbn)
          · have hpred : ∀ a : ℤ, P (pre (extendFin y a) b hb') := by
              intro a
              have he : pre (extendFin y a) b hb' = pre y b hbn := pre_extend_le hbn y a
              simpa [he] using hp
            have hfset : (A (Fin.last n)).filter (fun a : ℤ => P (pre (extendFin y a) b hb')) =
                A (Fin.last n) := by
              apply Finset.ext
              intro a
              rw [Finset.mem_filter]
              constructor
              · intro ha
                exact ha.1
              · intro ha
                exact ⟨ha, hpred a⟩
            rw [hfset]
            simp [hp]
          · have hfalse : ∀ a : ℤ, ¬ P (pre (extendFin y a) b hb') := by
              intro a
              have he : pre (extendFin y a) b hb' = pre y b hbn := pre_extend_le hbn y a
              intro h
              exact hp (by simpa [he] using h)
            have hfset : (A (Fin.last n)).filter (fun a : ℤ => P (pre (extendFin y a) b hb')) = ∅ := by
              apply Finset.ext
              intro a
              rw [Finset.mem_filter]
              constructor
              · intro ha
                exact (hfalse a ha.2).elim
              · intro ha
                simp at ha
            rw [hfset]
            simp [hp]
        have hsum : (∑ y ∈ prodFinset n (fun j : Fin n => A (Fin.castSucc j)),
              ((A (Fin.last n)).filter (fun a : ℤ => P (pre (extendFin y a) b hb'))).card)
            = (A (Fin.last n)).card *
                (((prodFinset n A').filter (fun y : Fin n → ℤ => P (pre y b hbn))).card) := by
          calc
            (∑ y ∈ prodFinset n (fun j : Fin n => A (Fin.castSucc j)),
                ((A (Fin.last n)).filter (fun a : ℤ => P (pre (extendFin y a) b hb'))).card)
                = ∑ y ∈ prodFinset n A',
                    (if P (pre y b hbn) then (A (Fin.last n)).card else 0) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      exact hfiber y hy
            _ = ∑ y ∈ prodFinset n A',
                    (A (Fin.last n)).card * (if P (pre y b hbn) then 1 else 0) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      by_cases hp : P (pre y b hbn) <;> simp [hp]
            _ = (A (Fin.last n)).card * (∑ y ∈ prodFinset n A',
                    (if P (pre y b hbn) then 1 else 0)) := by
                      rw [Finset.mul_sum]
            _ = (A (Fin.last n)).card * (((prodFinset n A').filter
                    (fun y : Fin n → ℤ => P (pre y b hbn))).card) := by
                      congr 1
                      exact Finset.sum_boole (s := prodFinset n A')
                        (p := fun y : Fin n → ℤ => P (pre y b hbn))
        have hih := ih hbn A'
        have hih' : (((prodFinset n A').filter (fun y : Fin n → ℤ => P (pre y b hbn))).card)
            = ((prodFinset b (prefam A' hbn)).filter P).card *
                (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) := by
          simpa [A'] using hih
        have hfamA : prodFinset b (prefam A' hbn) = prodFinset b (prefam A hb') := by
          apply Submission.RoughProduct.prodFinset_congr
          intro j
          dsimp [prefam, A']
        have htail : (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) * (A (Fin.last n)).card
            = (∏ j : Fin (n + 1 - b), (A ⟨b + j.val, by omega⟩).card) := by
          have hbridge : (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) * (A (Fin.last n)).card
              = (∏ j : Fin (n - b), (A (Fin.castSucc ⟨b + j.val, by omega⟩)).card) * (A (Fin.last n)).card := by
                congr 1
          rw [hbridge]
          rw [hlast]
          exact prod_tail_succ_nat (n := n) (b := b) hbn (A := A)
        calc
          ((prodFinset (n + 1) A).filter (fun x : Fin (n + 1) → ℤ => P (pre x b hb'))).card
              = (A (Fin.last n)).card *
                  (((prodFinset n A').filter (fun y : Fin n → ℤ => P (pre y b hbn))).card) := by
                rw [hpeel]
                exact hsum
          _ = (A (Fin.last n)).card *
              (((prodFinset b (prefam A' hbn)).filter P).card *
                (∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card)) := by rw [hih']
          _ = (((prodFinset b (prefam A' hbn)).filter P).card) *
              ((∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) *
                (A (Fin.last n)).card) := by ring
          _ = (((prodFinset b (prefam A hb')).filter P).card) *
              ((∏ j : Fin (n - b), (A' ⟨b + j.val, by omega⟩).card) *
                (A (Fin.last n)).card) := by rw [hfamA]
          _ = (((prodFinset b (prefam A hb')).filter P).card) *
              (∏ j : Fin (n + 1 - b), (A ⟨b + j.val, by omega⟩).card) := by
                rw [← htail]


/-- Real-valued form of `filter_prefix_card`. -/
lemma filter_prefix_card_real {n b : ℕ} (hb : b ≤ n) (A : Fin n → Finset ℤ)
    (P : (Fin b → ℤ) → Prop) :
    (((prodFinset n A).filter (fun x : Fin n → ℤ => P (pre x b hb))).card : ℝ)
      = ((((prodFinset b (prefam A hb)).filter P).card : ℕ) : ℝ) *
          (∏ j : Fin (n - b), (((A ⟨b + j.val, by omega⟩).card : ℕ) : ℝ)) := by
  exact_mod_cast (filter_prefix_card hb A P)

/-- Real-valued form of `prod_factor`. -/
lemma prod_factor_real {n b : ℕ} (hb : b ≤ n) (A : Fin n → Finset ℤ) :
    (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) =
      (∏ j : Fin b, ((((prefam A hb) j).card : ℕ) : ℝ)) *
        (∏ j : Fin (n - b), (((A ⟨b + j.val, by omega⟩).card : ℕ) : ℝ)) := by
  exact_mod_cast (prod_factor hb A)




/-! ## 9. Block-split (via `Refine2.cat`) counting -/

lemma cat_pre_head {a s : ℕ} (v : Fin a → ℤ) (w : Fin s → ℤ) :
    pre (cat v w) a (by omega : a ≤ a + s) = v := by
  funext j
  dsimp [pre, cat]
  have hj : (j : ℕ) < a := j.isLt
  rw [dif_pos hj]

lemma cat_tailVec {a s : ℕ} (v : Fin a → ℤ) (w : Fin s → ℤ) :
    tailVec (cat v w) a s (by omega : a + s ≤ a + s) = w := by
  funext t
  dsimp [tailVec, cat]
  have hj : ¬ (a + t.val) < a := by omega
  rw [dif_neg hj]
  have harg : (⟨(a + t.val) - a, by omega⟩ : Fin s) = t := by
    apply Fin.ext
    simp
  rw [harg]

lemma cat_split_eq {a s : ℕ} (p : Fin (a + s) → ℤ) :
    cat (pre p a (by omega : a ≤ a + s)) (tailVec p a s (by omega : a + s ≤ a + s)) = p := by
  have h := pre_cat_tail (x := p) (i₀ := a) (s := s) (hs := (by omega : a + s ≤ a + s))
  calc
    cat (pre p a (by omega : a ≤ a + s)) (tailVec p a s (by omega : a + s ≤ a + s))
        = pre p (a + s) (by omega : a + s ≤ a + s) := by
          rw [← h]
    _ = p := by
          apply pre_self

lemma cat_injective {a s : ℕ} :
    Function.Injective (fun q : (Fin a → ℤ) × (Fin s → ℤ) => cat q.1 q.2) := by
  intro q₁ q₂ h
  apply Prod.ext
  · have hpre := congrArg (fun p : Fin (a + s) → ℤ => pre p a (by omega : a ≤ a + s)) h
    simpa [cat_pre_head] using hpre
  · have htail := congrArg (fun p : Fin (a + s) → ℤ => tailVec p a s (by omega : a + s ≤ a + s)) h
    simpa [cat_tailVec] using htail

lemma cat_mem_prodFinset {a s : ℕ} (C : Fin (a + s) → Finset ℤ)
    (p0 : Fin a → ℤ) (z : Fin s → ℤ) :
    cat p0 z ∈ prodFinset (a + s) C ↔
      (∀ j : Fin a, p0 j ∈ C (Fin.castAdd s j)) ∧
        (∀ t : Fin s, z t ∈ C ⟨a + t.val, by omega⟩) := by
  rw [mem_prodFinset]
  constructor
  · intro h
    constructor
    · intro j
      have hmem := h (Fin.castAdd s j)
      have hval : (cat p0 z) (Fin.castAdd s j) = p0 j := by
        dsimp [cat]
        rw [dif_pos j.isLt]
      rwa [hval] at hmem
    · intro t
      have hmem := h ⟨a + t.val, by omega⟩
      have hval : (cat p0 z) ⟨a + t.val, by omega⟩ = z t := by
        dsimp [cat]
        have hq : ¬ (⟨a + t.val, by omega⟩ : Fin (a + s)).val < a := by
          dsimp
          omega
        rw [dif_neg hq]
        have harg : (⟨(a + t.val) - a, by omega⟩ : Fin s) = t := by
          apply Fin.ext
          simp
        rw [harg]
      rwa [hval] at hmem
  · intro h q
    by_cases hq : q.val < a
    · have hq' : (cat p0 z) q = p0 ⟨q.val, hq⟩ := by
        dsimp [cat]
        rw [dif_pos hq]
      have hmem := h.1 ⟨q.val, hq⟩
      have hfam : C q = C (Fin.castAdd s ⟨q.val, hq⟩) := by
        congr 1
      rw [hq', hfam]
      exact hmem
    · have hqa : a ≤ q.val := le_of_not_gt hq
      have hmem := h.2 ⟨q.val - a, by omega⟩
      have hq' : (cat p0 z) q = z ⟨q.val - a, by omega⟩ := by
        dsimp [cat]
        rw [dif_neg hq]
      have hfam : C q = C ⟨a + (q.val - a), by omega⟩ := by
        congr 1
        apply Fin.ext
        simp
        omega
      rw [hq', hfam]
      exact hmem

lemma prodFinset_cat_image {a s : ℕ} (C : Fin (a + s) → Finset ℤ) :
    prodFinset (a + s) C =
      ((prodFinset a (fun j : Fin a => C (Fin.castAdd s j))).product
        (prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩))).image
        (fun q : (Fin a → ℤ) × (Fin s → ℤ) => cat q.1 q.2) := by
  apply Finset.ext
  intro p
  rw [Finset.mem_image]
  constructor
  · intro hp
    refine ⟨(pre p a (by omega : a ≤ a + s), tailVec p a s (by omega : a + s ≤ a + s)), ?_, ?_⟩
    · have hm1 : (pre p a (by omega : a ≤ a + s)) ∈
          prodFinset a (fun j : Fin a => C (Fin.castAdd s j)) := by
        rw [mem_prodFinset]
        intro j
        have hmem := (mem_prodFinset C p).1 hp (Fin.castAdd s j)
        have hcoord : p (Fin.castAdd s j) = (pre p a (by omega : a ≤ a + s)) j := by
          dsimp [pre]
          have hcast : Fin.castAdd s j = Fin.castLE (by omega : a ≤ a + s) j := by
            apply Fin.ext
            simp
          rw [hcast]
        rwa [← hcoord]
      have hm2 : tailVec p a s (by omega : a + s ≤ a + s) ∈
          prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩) := by
        rw [mem_prodFinset]
        intro t
        have hmem := (mem_prodFinset C p).1 hp ⟨a + t.val, by omega⟩
        have hcoord : p ⟨a + t.val, by omega⟩ = (tailVec p a s (by omega : a + s ≤ a + s)) t := by
          dsimp [tailVec]
        rwa [← hcoord]
      exact (Finset.mem_product (s := prodFinset a (fun j : Fin a => C (Fin.castAdd s j)))
          (t := prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩))).mpr ⟨hm1, hm2⟩
    · exact cat_split_eq p
  · intro h
    rcases h with ⟨q, hq, hpq⟩
    rw [← hpq]
    have hq' := (Finset.mem_product (s := prodFinset a (fun j : Fin a => C (Fin.castAdd s j)))
          (t := prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩))).mp hq
    rcases hq' with ⟨h1, h2⟩
    have h1' : ∀ j : Fin a, q.1 j ∈ C (Fin.castAdd s j) := (mem_prodFinset _ q.1).1 h1
    have h2' : ∀ t : Fin s, q.2 t ∈ C ⟨a + t.val, by omega⟩ := (mem_prodFinset _ q.2).1 h2
    exact (cat_mem_prodFinset C q.1 q.2).2 ⟨h1', h2'⟩

/-- Filter over the `(a+s)`-product (predicate splitting at `a`) decomposes into
the head-filter sum of block filters via `cat`. -/
lemma filter_cat_split_real {a s : ℕ} (C : Fin (a + s) → Finset ℤ)
    (P : (Fin a → ℤ) → Prop) (Q : (Fin (a + s) → ℤ) → Prop) :
    ((((prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
        P (pre p a (by omega : a ≤ a + s)) ∧ Q p)).card : ℕ) : ℝ)
      = (∑ p0 ∈ (((prodFinset a (fun j : Fin a => C (Fin.castAdd s j))).filter P)),
          ((((prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩)).filter
              (fun z : Fin s → ℤ => Q (cat p0 z))).card : ℕ) : ℝ)) := by
  classical
  let H : Finset (Fin a → ℤ) := prodFinset a (fun j : Fin a => C (Fin.castAdd s j))
  let B : Finset (Fin s → ℤ) := prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩)
  let L : Finset (Fin (a + s) → ℤ) := (prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
      P (pre p a (by omega : a ≤ a + s)) ∧ Q p)
  let R : Finset ((Fin a → ℤ) × (Fin s → ℤ)) := (H.product B).filter
      (fun q : (Fin a → ℤ) × (Fin s → ℤ) => P q.1 ∧ Q (cat q.1 q.2))
  have hcard : L.card = R.card := by
    apply Finset.card_bij (s := L) (t := R)
      (fun p hp => (pre p a (by omega : a ≤ a + s), tailVec p a s (by omega : a + s ≤ a + s)))
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_filter]
      constructor
      · have hm1 : pre p a (by omega : a ≤ a + s) ∈ H := by
          dsimp [H]
          rw [mem_prodFinset]
          intro j
          have hmem := (mem_prodFinset C p).1 hp.1 (Fin.castAdd s j)
          have hcoord : p (Fin.castAdd s j) = (pre p a (by omega : a ≤ a + s)) j := by
            dsimp [pre]
            have hcast : Fin.castAdd s j = Fin.castLE (by omega : a ≤ a + s) j := by
              apply Fin.ext
              simp
            rw [hcast]
          rwa [← hcoord]
        have hm2 : tailVec p a s (by omega : a + s ≤ a + s) ∈ B := by
          dsimp [B]
          rw [mem_prodFinset]
          intro t
          have hmem := (mem_prodFinset C p).1 hp.1 ⟨a + t.val, by omega⟩
          have hcoord : p ⟨a + t.val, by omega⟩ = (tailVec p a s (by omega : a + s ≤ a + s)) t := by
            dsimp [tailVec]
          rwa [← hcoord]
        exact (Finset.mem_product (s := H) (t := B)).mpr ⟨hm1, hm2⟩
      · constructor
        · exact hp.2.1
        · rw [cat_split_eq p]
          exact hp.2.2
    · intro p₁ hp₁ p₂ hp₂ h
      have hcat := congrArg (fun q : (Fin a → ℤ) × (Fin s → ℤ) => cat q.1 q.2) h
      have h1 := cat_split_eq p₁
      have h2 := cat_split_eq p₂
      rwa [h1, h2] at hcat
    · intro q hq
      rw [Finset.mem_filter] at hq
      refine ⟨cat q.1 q.2, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rcases (Finset.mem_product (s := H) (t := B)).mp hq.1 with ⟨hq1, hq2⟩
          exact (cat_mem_prodFinset C q.1 q.2).2
            ⟨(mem_prodFinset _ q.1).1 hq1, (mem_prodFinset _ q.2).1 hq2⟩
        · have hhead : pre (cat q.1 q.2) a (by omega : a ≤ a + s) = q.1 := cat_pre_head q.1 q.2
          constructor
          · simpa [hhead] using hq.2.1
          · exact hq.2.2
      · have h1 := cat_pre_head q.1 q.2
        have h2 := cat_tailVec q.1 q.2
        exact Prod.ext h1 h2
  have hmain : ((((prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
        P (pre p a (by omega : a ≤ a + s)) ∧ Q p)).card : ℕ) : ℝ)
      = (∑ p0 ∈ (((prodFinset a (fun j : Fin a => C (Fin.castAdd s j))).filter P)),
          ((((prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩)).filter
              (fun z : Fin s → ℤ => Q (cat p0 z))).card : ℕ) : ℝ)) := by
    have hc : (((prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
          P (pre p a (by omega : a ≤ a + s)) ∧ Q p)).card : ℕ)
        = (((H.product B).filter (fun q : (Fin a → ℤ) × (Fin s → ℤ) =>
            P q.1 ∧ Q (cat q.1 q.2))).card : ℕ) := by
      simpa [L, R] using hcard
    have hc1 : ((((prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
          P (pre p a (by omega : a ≤ a + s)) ∧ Q p)).card : ℕ) : ℝ)
        = ((((H.product B).filter (fun q : (Fin a → ℤ) × (Fin s → ℤ) =>
            P q.1 ∧ Q (cat q.1 q.2))).card : ℕ) : ℝ) := by
      exact_mod_cast hc
    calc
      ((((prodFinset (a + s) C).filter (fun p : Fin (a + s) → ℤ =>
          P (pre p a (by omega : a ≤ a + s)) ∧ Q p)).card : ℕ) : ℝ)
          = ((((H.product B).filter (fun q : (Fin a → ℤ) × (Fin s → ℤ) =>
              P q.1 ∧ Q (cat q.1 q.2))).card : ℕ) : ℝ) := hc1
      _ = (∑ p0 ∈ (((prodFinset a (fun j : Fin a => C (Fin.castAdd s j))).filter P)),
            ((((prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩)).filter
                (fun z : Fin s → ℤ => Q (cat p0 z))).card : ℕ) : ℝ)) := by
            dsimp [H, B]
            exact Commons.Data.Finset.fiber_filter_product_card_real
              (s := prodFinset a (fun j : Fin a => C (Fin.castAdd s j)))
              (t := prodFinset s (fun t : Fin s => C ⟨a + t.val, by omega⟩))
              (P := P) (Q := fun p0 z => Q (cat p0 z))
  exact hmain



/-! ## 10. Kernel window-mass bound (aux simple ac over level kernels) -/

lemma kernel_window_mass {n k : ℕ} (hn1 : 1 ≤ n) (hkn : k ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδ₀leδ : δ₀ ≤ δ) (hkbig : δ₀ * (n : ℝ) ≤ k) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {N : ℕ} (hN1 : 1 ≤ N) {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {A : Fin n → Finset ℤ} (hAdm : Admissible N n n δ A)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1)
    (C₂ : ℝ) (hC₂pos : 0 < C₂)
    (hC₂ : ∀ {n₁ : ℕ} (hn1 : 1 ≤ n₁) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {p₁ : unitInterval}
        (hp₁₀ : 0 < (p₁ : ℝ)) (hp₁₁ : (p₁ : ℝ) ≤ 1 / 2) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) {ℓ₁ : ℕ}
        {f₁ : ℤ → ℝ} (hfpos₁ : ∀ t : ℤ, 0 ≤ f₁ t) (hfsum₁ : Summable f₁)
        (hfmass₁ : norm₁ f₁ ≤ 1),
        ∀ (x : Fin ℓ₁ → ℤ) (S : Finset (Fin ℓ₁))
          (hScard : δ₁ * (n₁ : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin ℓ₁, j ∈ S → (N₁ : ℝ) < |(x j : ℝ)|),
          ∀ (a b : ℤ) (hlen : (N₁ : ℤ) ≤ (b : ℤ) - a + 1),
            (∑ t ∈ Finset.Icc a b, avgF f₁ p₁ ℓ₁ x t) ≤
              C₂ * (((b : ℝ) - (a : ℝ) + 1) / (N₁ : ℝ)) /
                Real.sqrt (δ₁ * (n₁ : ℝ) * (p₁ : ℝ)))
    {x : Fin n → ℤ} (hx : x ∈ prodFinset n A) :
    ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p k (pre x k hkn) t) ≤
      C₂ / Real.sqrt (δ₀ * (p : ℝ)) / Real.sqrt (n : ℝ) := by
  intro lo
  classical
  let S : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
    (fun j : Fin k => smallIndex n δ (j.val))
  have hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ) := by
    dsimp [S]
    exact bigCoordSet_card (n := n) (k := k) (δ₀ := δ₀) (δ := δ) hδ₀ hδ₀leδ hkbig hslack
  have hSbig : ∀ j : Fin k, j ∈ S → (N : ℝ) < |(((pre x k hkn) j) : ℝ)| := by
    intro j hj
    dsimp [S] at hj
    rw [Finset.mem_filter] at hj
    have hjS : smallIndex n δ (j.val) := hj.2
    have hmem : x (Fin.castLE hkn j) ∈ A (Fin.castLE hkn j) := (mem_prodFinset A x).1 hx (Fin.castLE hkn j)
    have hbig := big_of_small (hA := hAdm) (i := Fin.castLE hkn j) (hi := by
      simpa [smallIndex] using hjS) (a := x (Fin.castLE hkn j)) hmem
    have hcoord : ((pre x k hkn) j : ℝ) = (x (Fin.castLE hkn j) : ℝ) := by
      dsimp [pre]
    rwa [hcoord]
  have hAux := hC₂ (hn1 := hn1) (hδ₁ := hδ₀) (hp₁₀ := hp₀) (hp₁₁ := hp₁)
      (hN₁ := hN1) (hfpos₁ := hfpos) (hfsum₁ := hfsum) (hfmass₁ := hfmass)
      (x := pre x k hkn) (S := S) (hScard := hScard) (hSbig := hSbig)
      (a := lo) (b := lo + (N : ℤ) - 1) (hlen := (by omega))
  have hEq : (∑ t ∈ Finset.Icc lo (lo + (N : ℤ) - 1), avgF f p k (pre x k hkn) t)
      = (∑ t ∈ I0 lo N, lvl f p k (pre x k hkn) t) := by
    rfl
  have hbound : C₂ * ((((lo + (N : ℤ) - 1 : ℤ) : ℝ) - (lo : ℝ) + 1) / (N : ℝ)) /
        Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))
      ≤ C₂ / Real.sqrt (δ₀ * (p : ℝ)) / Real.sqrt (n : ℝ) := by
    have hnum : (((lo + (N : ℤ) - 1 : ℤ) : ℝ) - (lo : ℝ) + 1) / (N : ℝ) = 1 := by
      have hZ : ((lo + (N : ℤ) - 1 : ℤ) : ℝ) = (lo : ℝ) + (N : ℝ) - 1 := by
        rw [Int.cast_sub, Int.cast_add, Int.cast_one]
        simp
      rw [hZ]
      have hNne : (N : ℝ) ≠ 0 := by positivity
      field_simp [hNne]
      ring_nf
    have hNne : (N : ℝ) ≠ 0 := by positivity
    rw [hnum]
    have hδp0 : 0 < δ₀ * (p : ℝ) := mul_pos hδ₀ hp₀
    have hsqrt : Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) = Real.sqrt (δ₀ * (p : ℝ)) * Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) = Real.sqrt ((δ₀ * (p : ℝ)) * (n : ℝ)) := by congr 1; ring
        _ = Real.sqrt (δ₀ * (p : ℝ)) * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_mul (by positivity : 0 ≤ δ₀ * (p : ℝ)) (n : ℝ)]
    have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    rw [hsqrt]
    field_simp [ne_of_gt hδp0, ne_of_gt hnpos]
    norm_num
  exact le_trans (by simpa [hEq] using hAux) hbound

lemma kernel_window_mass_pre {n k : ℕ} (hn1 : 1 ≤ n) (hkn : k ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδ₀leδ : δ₀ ≤ δ) (hkbig : δ₀ * (n : ℝ) ≤ k) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {N : ℕ} (hN1 : 1 ≤ N) {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {A : Fin n → Finset ℤ} (hAdm : Admissible N n n δ A)
    {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1)
    (C₂ : ℝ) (hC₂pos : 0 < C₂)
    (hC₂ : ∀ {n₁ : ℕ} (hn1 : 1 ≤ n₁) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {p₁ : unitInterval}
        (hp₁₀ : 0 < (p₁ : ℝ)) (hp₁₁ : (p₁ : ℝ) ≤ 1 / 2) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) {ℓ₁ : ℕ}
        {f₁ : ℤ → ℝ} (hfpos₁ : ∀ t : ℤ, 0 ≤ f₁ t) (hfsum₁ : Summable f₁)
        (hfmass₁ : norm₁ f₁ ≤ 1),
        ∀ (x : Fin ℓ₁ → ℤ) (S : Finset (Fin ℓ₁))
          (hScard : δ₁ * (n₁ : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin ℓ₁, j ∈ S → (N₁ : ℝ) < |(x j : ℝ)|),
          ∀ (a b : ℤ) (hlen : (N₁ : ℤ) ≤ (b : ℤ) - a + 1),
            (∑ t ∈ Finset.Icc a b, avgF f₁ p₁ ℓ₁ x t) ≤
              C₂ * (((b : ℝ) - (a : ℝ) + 1) / (N₁ : ℝ)) /
                Real.sqrt (δ₁ * (n₁ : ℝ) * (p₁ : ℝ)))
    {u : Fin k → ℤ} (hu : u ∈ prodFinset k (prefam A hkn)) :
    ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p k u t) ≤
      C₂ / Real.sqrt (δ₀ * (p : ℝ)) / Real.sqrt (n : ℝ) := by
  intro lo
  classical
  let S : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
    (fun j : Fin k => smallIndex n δ (j.val))
  have hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ) := by
    dsimp [S]
    exact bigCoordSet_card (n := n) (k := k) (δ₀ := δ₀) (δ := δ) hδ₀ hδ₀leδ hkbig hslack
  have hSbig : ∀ j : Fin k, j ∈ S → (N : ℝ) < |(u j : ℝ)| := by
    intro j hj
    dsimp [S] at hj
    rw [Finset.mem_filter] at hj
    have hjS : smallIndex n δ (j.val) := hj.2
    have hmem : u j ∈ A (Fin.castLE hkn j) := by
      have h := (mem_prodFinset (prefam A hkn) u).1 hu j
      simpa [prefam] using h
    have hbig := big_of_small (hA := hAdm) (i := Fin.castLE hkn j) (hi := by
      simpa [smallIndex] using hjS) (a := u j) hmem
    rwa [← (show (u j : ℝ) = (u j : ℝ) by rfl)]
  have hAux := hC₂ (hn1 := hn1) (hδ₁ := hδ₀) (hp₁₀ := hp₀) (hp₁₁ := hp₁)
      (hN₁ := hN1) (hfpos₁ := hfpos) (hfsum₁ := hfsum) (hfmass₁ := hfmass)
      (x := u) (S := S) (hScard := hScard) (hSbig := hSbig)
      (a := lo) (b := lo + (N : ℤ) - 1) (hlen := (by omega))
  have hEq : (∑ t ∈ Finset.Icc lo (lo + (N : ℤ) - 1), avgF f p k u t)
      = (∑ t ∈ I0 lo N, lvl f p k u t) := by
    rfl
  have hbound : C₂ * ((((lo + (N : ℤ) - 1 : ℤ) : ℝ) - (lo : ℝ) + 1) / (N : ℝ)) /
        Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))
      ≤ C₂ / Real.sqrt (δ₀ * (p : ℝ)) / Real.sqrt (n : ℝ) := by
    have hnum : (((lo + (N : ℤ) - 1 : ℤ) : ℝ) - (lo : ℝ) + 1) / (N : ℝ) = 1 := by
      have hZ : ((lo + (N : ℤ) - 1 : ℤ) : ℝ) = (lo : ℝ) + (N : ℝ) - 1 := by
        rw [Int.cast_sub, Int.cast_add, Int.cast_one]
        simp
      rw [hZ]
      have hNne : (N : ℝ) ≠ 0 := by positivity
      field_simp [hNne]
      ring_nf
    have hNne : (N : ℝ) ≠ 0 := by positivity
    rw [hnum]
    have hδp0 : 0 < δ₀ * (p : ℝ) := mul_pos hδ₀ hp₀
    have hsqrt : Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) = Real.sqrt (δ₀ * (p : ℝ)) * Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) = Real.sqrt ((δ₀ * (p : ℝ)) * (n : ℝ)) := by congr 1; ring
        _ = Real.sqrt (δ₀ * (p : ℝ)) * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_mul (by positivity : 0 ≤ δ₀ * (p : ℝ)) (n : ℝ)]
    have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    rw [hsqrt]
    field_simp [ne_of_gt hδp0, ne_of_gt hnpos]
    norm_num
  exact le_trans (by simpa [hEq] using hAux) hbound



/-! ## 11. Event₀ full-product bound -/

lemma e0_full_bound {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ))
    {M : ℝ} (hM1 : 1 ≤ M) :
    ∀ (α : ℝ) (hα₀ : 1 / 2 ≤ α) (hα₁ : α < 1) (nα : ℕ)
      (hαn : ∀ n₁ : ℕ, nα ≤ n₁ →
        (1 - (p : ℝ) + ε / 2) ^ (Nat.ceil (α * (n₁ : ℝ))) ≤
          (1 - (p : ℝ) + ε) ^ n₁ / Real.sqrt (n₁ : ℝ)),
    ∃ (L : ℝ) (n₀ : ℕ), 1 ≤ L ∧ 2 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N),
        (N : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n →
        ∀ (A : Fin n → Finset ℤ)
          (hAdm : Admissible N n n δ A)
          (hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
        ∀ (f : ℤ → ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        let ℓ : ℕ := Nat.ceil (α * (n : ℝ))
        (((prodFinset n A).filter (fun x : Fin n → ℤ =>
            L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
              esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hα₁))))).card : ℝ) ≤
          Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
  classical
  intro α hα₀ hα₁ nα hαn
  rcases rough_step0 (p := p) hp₀ hp₁ (δ := δ) hδ₀ hδ₁₂ (ε := ε) hε₀ hεp (M := M) hM1 with
    ⟨L, nR, hL1, hnR2, hR⟩
  refine ⟨L, max (max nR 2) nα, hL1, ?_, ?_⟩
  · have h2 : 2 ≤ max nR 2 := le_max_right nR 2
    exact le_trans h2 (le_max_left (max nR 2) nα)
  · intro n hn₀ N hN1 hNa A hAdm hrad hsym f hfpos hfsum hfmass
    let ℓ : ℕ := Nat.ceil (α * (n : ℝ))
    have hnR : nR ≤ n := by
      have h1 : nR ≤ max nR 2 := le_max_left nR 2
      have h2 : max nR 2 ≤ max (max nR 2) nα := le_max_left (max nR 2) nα
      exact le_trans h1 (le_trans h2 hn₀)
    have hnα₀ : nα ≤ n := le_trans (le_max_right (max nR 2) nα) hn₀
    have h2n : 2 ≤ n := by
      have h2a : 2 ≤ max nR 2 := le_max_right nR 2
      have h2b : max nR 2 ≤ max (max nR 2) nα := le_max_left (max nR 2) nα
      exact le_trans h2a (le_trans h2b hn₀)
    have hn1 : 1 ≤ n := by omega
    have hℓle : ℓ ≤ n := by
      dsimp [ℓ]
      exact ceil_alpha_le hα₁
    have hℓge : n ≤ 2 * ℓ := by
      dsimp [ℓ]
      exact ceil_alpha_ge_half hα₀
    let a : ℝ := 1 - (p : ℝ) + ε
    have ha0 : 0 < a := by dsimp [a]; nlinarith
    have h1le2 : 1 / a ≤ 2 := by
      dsimp [a]
      have ha : 0 < 1 - (p : ℝ) + ε := by linarith
      rw [div_le_iff₀ ha]
      nlinarith
    have hNpow : (N : ℝ) ≤ (2 : ℝ) ^ n := by
      have h1 : (N : ℝ) ≤ (1 / a) ^ n := by
        simpa [a] using hNa
      calc
        (N : ℝ) ≤ (1 / a) ^ n := h1
        _ ≤ (2 : ℝ) ^ n := by
              apply pow_le_pow_left₀ (by positivity : 0 ≤ 1 / a) h1le2
    have hNinv : (N : ℝ) ≤ 1 / a ^ n := by
      calc
        (N : ℝ) ≤ (1 / a) ^ n := by simpa [a] using hNa
        _ = 1 / a ^ n := by
              rw [one_div, inv_pow]
              field_simp [ne_of_gt (pow_pos ha0 n)]
    have hNa' : (N : ℝ) * a ^ n ≤ 1 := by
      exact (le_div_iff₀ (pow_pos ha0 n)).1 hNinv
    have hmax := hmax_from_level (p := p) hp₀ hp₁ (ε := ε) hε₀ hεp
      (α := α) hα₀ hα₁ n hn1 (hαn := by simpa using (hαn n hnα₀))
      (N := N) hN1 hNa' (L := L) hL1 (f := f) hfpos hfsum hfmass
    -- hmax : (1 - (p:ℝ) + ε/2)^(⌈α·n⌉) * esup f ≤ L/((N:ℝ)*√(n:ℝ))
    have hAdmL : Admissible N n ℓ δ (prefam A hℓle) := admissible_prefam hℓle hAdm
    have hradL : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ prefam A hℓle j → |a| ≤ ((n * N : ℕ) : ℤ) :=
      hrad_prefam (hℓ := hℓle) hrad
    have hsymL : ∀ j : Fin ℓ, ∀ a : ℤ, a ∈ prefam A hℓle j → -a ∈ prefam A hℓle j :=
      hsym_prefam (hℓ := hℓle) hsym
    have hbnd := hR n hnR N hN1 hNpow ℓ hℓge hℓle (prefam A hℓle) hAdmL hradL hsymL f hfpos hfsum hfmass (by
      dsimp [ℓ] at hmax ⊢
      simpa using hmax)
    -- hbnd : count over prodFinset ℓ (prefam A hℓle) ≤ exp(−2Mn)·∏_Fin ℓ
    have hlift := filter_prefix_card_real (hb := hℓle) A
      (P := fun p0 : Fin ℓ → ℤ => L / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ p0))
    have hfac := prod_factor_real (hb := hℓle) A
    have hprod0 : 0 ≤ (∏ j : Fin (n - ℓ), (((A ⟨ℓ + j.val, by omega⟩).card : ℕ) : ℝ)) := by
      apply Finset.prod_nonneg
      intro j hj
      exact_mod_cast (Nat.zero_le _)
    calc
      (((prodFinset n A).filter (fun x : Fin n → ℤ =>
          L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
            esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hα₁))))).card : ℝ)
          = ((((prodFinset ℓ (prefam A hℓle)).filter (fun p0 : Fin ℓ → ℤ =>
              L / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ p0))).card : ℕ) : ℝ) *
              (∏ j : Fin (n - ℓ), (((A ⟨ℓ + j.val, by omega⟩).card : ℕ) : ℝ)) := by
            rw [← hlift]
      _ ≤ (Real.exp (-2 * M * (n : ℝ)) *
              (∏ j : Fin ℓ, ((((prefam A hℓle) j).card : ℕ) : ℝ))) *
              (∏ j : Fin (n - ℓ), (((A ⟨ℓ + j.val, by omega⟩).card : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hbnd hprod0
      _ = Real.exp (-2 * M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
            rw [hfac]
            ring



/-! ## 12. Event-chain counting (first-failure decomposition) -/

lemma esup_gt_mono_pre {f : ℤ → ℝ} {p : unitInterval} {n k : ℕ} (hk : k ≤ n)
    (x : Fin n → ℤ) (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {T : ℝ}
    (hgt : T < esup (lvl f p n x)) :
    T < esup (lvl f p k (pre x k hk)) := by
  have hdec := esup_lvl_decreasing (f := f) (p := p) (s := n) (k := k) hk x hfpos hf
  exact lt_of_lt_of_le hgt hdec

/-- first-failure decomposition of a finite event chain. -/
lemma first_failure_subset {α : Type} (X : Finset α) (Q : ℕ) (P : ℕ → α → Prop) :
    (X.filter (fun x : α => ¬ P Q x)) ⊆
      (X.filter (fun x : α => ¬ P 0 x)) ∪
        ((Finset.Icc 1 Q).biUnion (fun j : ℕ =>
          (X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)))) := by
  classical
  induction Q with
  | zero =>
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_union]
      left
      rw [Finset.mem_filter]
      exact ⟨hx.1, hx.2⟩
  | succ Q ih =>
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_union]
      by_cases hPQ : P Q x
      · right
        rw [Finset.mem_biUnion]
        refine ⟨Q + 1, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨Nat.succ_pos Q, le_rfl⟩
        · rw [Finset.mem_filter]
          exact ⟨hx.1, hPQ, hx.2⟩
      · have hmem : x ∈ (X.filter (fun x : α => ¬ P Q x)) := by
          rw [Finset.mem_filter]
          exact ⟨hx.1, hPQ⟩
        have hih' := ih hmem
        rw [Finset.mem_union] at hih'
        rcases hih' with hA | hB
        · left
          exact hA
        · right
          rw [Finset.mem_biUnion] at hB ⊢
          rcases hB with ⟨j, hj, hbj⟩
          refine ⟨j, ?_, hbj⟩
          rw [Finset.mem_Icc] at hj ⊢
          exact ⟨hj.1, le_trans hj.2 (Nat.le_succ Q)⟩

/-- real-cardinality form of the first-failure decomposition. -/
lemma first_failure_card_le {α : Type} (X : Finset α) (Q : ℕ) (P : ℕ → α → Prop) :
    (((X.filter (fun x : α => ¬ P Q x)).card : ℕ) : ℝ)
      ≤ ((((X.filter (fun x : α => ¬ P 0 x)).card : ℕ) : ℝ) +
        (∑ j ∈ Finset.Icc 1 Q,
          ((((X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)).card : ℕ) : ℝ)))) := by
  classical
  have hsub := first_failure_subset X Q P
  let A : Finset α := X.filter (fun x : α => ¬ P 0 x)
  let B : Finset α := (Finset.Icc 1 Q).biUnion (fun j : ℕ =>
    (X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)))
  have hc1 : (((X.filter (fun x : α => ¬ P Q x)).card : ℕ) : ℝ)
      ≤ (((A ∪ B).card : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub)
  have hc2 : ((((A ∪ B).card : ℕ) : ℝ)
      ≤ (((A.card : ℕ) : ℝ) + (((B.card : ℕ) : ℝ)))) := by
    exact_mod_cast (Finset.card_union_le A B)
  have hc3 : ((((B.card : ℕ) : ℝ)) ≤
      (∑ j ∈ Finset.Icc 1 Q,
        ((((X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)).card : ℕ) : ℝ)))) := by
    have hb := Finset.card_biUnion_le (s := Finset.Icc 1 Q)
      (t := fun j : ℕ => (X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)))
    dsimp [B] at hb ⊢
    exact_mod_cast hb
  calc
    (((X.filter (fun x : α => ¬ P Q x)).card : ℕ) : ℝ)
        ≤ (((A ∪ B).card : ℕ) : ℝ) := hc1
    _ ≤ (((A.card : ℕ) : ℝ) + (((B.card : ℕ) : ℝ))) := hc2
    _ ≤ (((A.card : ℕ) : ℝ) +
        (∑ j ∈ Finset.Icc 1 Q,
          ((((X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)).card : ℕ) : ℝ)))) := by
          linarith
    _ = (((X.filter (fun x : α => ¬ P 0 x)).card : ℕ) : ℝ) +
        (∑ j ∈ Finset.Icc 1 Q,
          ((((X.filter (fun x : α => P (j - 1) x ∧ ¬ P j x)).card : ℕ) : ℝ))) := by
          dsimp [A]



/-! ## 13. Block identities (`sqrtDen`, `blkFam`, level-identity via `cat`) -/


/-- cardinality as a real. -/
noncomputable def fcard {α : Type} (X : Finset α) : ℝ := (X.card : ℝ)

/-- product of all coordinate cardinalities. -/
noncomputable def allAll {n : ℕ} (A : Fin n → Finset ℤ) : ℝ :=
  ∏ j : Fin n, (((A j).card : ℕ) : ℝ)

/-- cardinality-cast distributes over the coordinate product. -/
lemma cast_card_prod {ℓ : ℕ} (B : Fin ℓ → Finset ℤ) :
    (((prodFinset ℓ B).card : ℕ) : ℝ) = ∏ j : Fin ℓ, (((B j).card : ℕ) : ℝ) := by
  rw [prodFinset_card]
  simpa using (map_prod (Nat.castRingHom ℝ) (fun j : Fin ℓ => (B j).card))


noncomputable def sqrtDen (N : ℕ) (n : ℕ) : ℝ := (N : ℝ) * Real.sqrt (n : ℝ)

/-- the coordinate family of the length-`2m` block starting at index `a`. -/
def blkFam {n : ℕ} (A : Fin n → Finset ℤ) (a m : ℕ) (han : a + 2 * m ≤ n) :
    Fin (2 * m) → Finset ℤ :=
  fun t => A ⟨a + t.val, by omega⟩

/-- product of the block cardinalities. -/
noncomputable def blkAll {n : ℕ} (A : Fin n → Finset ℤ) (a m : ℕ) (han : a + 2 * m ≤ n) : ℝ :=
  ∏ j : Fin (2 * m), ((((blkFam A a m han) j).card : ℕ) : ℝ)


/-- `pre x k h = x` when `h : k ≤ k` (proof irrelevance + `pre_self`). -/
lemma pre_self_any {k : ℕ} (x : Fin k → ℤ) (h : k ≤ k) : pre x k h = x := by
  calc
    pre x k h = pre x k (le_refl k) := by
      exact pre_irrel x
    _ = x := pre_self x

/-- the level-`(a+s)` supremum of `cat p0 z` equals the level-`s` supremum of
the level-`a` kernel on `z`. -/
lemma lvl_esup_cat_eq {a s : ℕ} (p0 : Fin a → ℤ) (z : Fin s → ℤ)
    (f : ℤ → ℝ) (p : unitInterval) :
    esup (lvl f p (a + s) (cat p0 z)) =
      esup (lvl (lvl f p a p0) p s z) := by
  have hsplit := lvl_split (f := f) (p := p) (x := cat p0 z) (i₀ := a) (s := s)
    (hs := (by omega : a + s ≤ a + s))
  have hpre_eq : lvl f p (a + s) (cat p0 z)
      = avgF (lvl f p a (pre (cat p0 z) a (by omega : a ≤ a + s))) p s
          (tailVec (cat p0 z) a s (by omega : a + s ≤ a + s)) := by
    calc
      lvl f p (a + s) (cat p0 z)
          = lvl f p (a + s) (pre (cat p0 z) (a + s) (by omega : a + s ≤ a + s)) := by
            congr 1
      _ = avgF (lvl f p a (pre (cat p0 z) a (by omega : a ≤ a + s))) p s
            (tailVec (cat p0 z) a s (by omega : a + s ≤ a + s)) := hsplit
  have hpre_a : pre (cat p0 z) a (by omega : a ≤ a + s) = p0 := cat_pre_head p0 z
  have htail : tailVec (cat p0 z) a s (by omega : a + s ≤ a + s) = z := cat_tailVec p0 z
  have hEq : lvl f p (a + s) (cat p0 z) = lvl (lvl f p a p0) p s z := by
    calc
      lvl f p (a + s) (cat p0 z)
          = avgF (lvl f p a (pre (cat p0 z) a (by omega : a ≤ a + s))) p s
              (tailVec (cat p0 z) a s (by omega : a + s ≤ a + s)) := hpre_eq
      _ = avgF (lvl f p a p0) p s z := by rw [hpre_a, htail]
      _ = lvl (lvl f p a p0) p s z := rfl
  rw [hEq]

lemma blk_prod_factor {n a m : ℕ} (han : a + 2 * m ≤ n) (A : Fin n → Finset ℤ) :
    (∏ j : Fin (a + 2 * m), (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) =
      (∏ j : Fin a, (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) * blkAll A a m han := by
  classical
  let C : Fin (a + 2 * m) → Finset ℤ := prefam (ℓ := a + 2 * m) A han
  have hfac := prod_factor_real (hb := (Nat.le_add_right a (2 * m))) C
  have hC1 : (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ))
      = (∏ j : Fin (a + 2 * m), (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rfl
  have hhead : (∏ j : Fin a, (((C (Fin.castAdd (2 * m) j)).card : ℕ) : ℝ))
      = (∏ j : Fin a, (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rfl
  have hprefam : (∏ j : Fin a, ((((prefam (ℓ := a) C (Nat.le_add_right a (2 * m))) j).card : ℕ) : ℝ))
      = (∏ j : Fin a, (((C (Fin.castAdd (2 * m) j)).card : ℕ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rfl
  have hAr : (a + 2 * m) - a = 2 * m := by omega
  have htail : (∏ j : Fin ((a + 2 * m) - a), (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ))
      = blkAll A a m han := by
    have hconv := prod_fin_congr_equiv_real (h := hAr)
      (f := fun j : Fin ((a + 2 * m) - a) => (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ))
      (g := fun j : Fin (2 * m) => (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ))
      (by intro j; rfl)
    have hblk : (∏ j : Fin (2 * m), (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ))
        = blkAll A a m han := by
      dsimp [blkAll]
      apply Finset.prod_congr rfl
      intro j hj
      rfl
    exact hconv.trans hblk
  calc
    (∏ j : Fin (a + 2 * m), (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ))
        = (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) := hC1.symm
    _ = (∏ j : Fin a, ((((prefam (ℓ := a) C (Nat.le_add_right a (2 * m))) j).card : ℕ) : ℝ)) *
          (∏ j : Fin ((a + 2 * m) - a), (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ)) := hfac
    _ = (∏ j : Fin a, (((C (Fin.castAdd (2 * m) j)).card : ℕ) : ℝ)) *
          (∏ j : Fin ((a + 2 * m) - a), (((C ⟨a + j.val, by omega⟩).card : ℕ) : ℝ)) := by
          rw [hprefam]
    _ = (∏ j : Fin a, (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) * blkAll A a m han := by
          rw [hhead, htail]



/-! ## 14. Per-block counting bound (`refine_block_bound`) -/

lemma refine_block_bound {n a m : ℕ} (hn1 : 1 ≤ n) (han : a + 2 * m ≤ n)
    (f : ℤ → ℝ) (p : unitInterval)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (N : ℕ) (hN1 : 1 ≤ N) (A : Fin n → Finset ℤ)
    (Lp Lc θ : ℝ) (hLθ : θ * Lp ≤ Lc)
    (e2 : ℝ) (he2 : 0 ≤ e2)
    (hpre : ∀ p0 : Fin a → ℤ,
        p0 ∈ prodFinset a (fun j : Fin a => (prefam (ℓ := a + 2 * m) A han) (Fin.castAdd (2 * m) j)) →
        esup (lvl f p a p0) ≤ Lp / sqrtDen N n →
        fcard ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
            θ * Lp / sqrtDen N n < esup (lvl (lvl f p a p0) p (2 * m) z)))
          ≤ e2 * blkAll A a m han) :
    fcard ((prodFinset n A).filter (fun x : Fin n → ℤ =>
        esup (lvl f p a (pre x a (le_trans (Nat.le_add_right a (2 * m)) han))) ≤ Lp / sqrtDen N n ∧
        Lc / sqrtDen N n < esup (lvl f p (a + 2 * m) (pre x (a + 2 * m) han))))
      ≤ e2 * allAll A := by
  classical
  let D : ℝ := sqrtDen N n
  let ha : a ≤ n := le_trans (Nat.le_add_right a (2 * m)) han
  have hDpos : 0 < D := by
    dsimp [D, sqrtDen]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    positivity
  have hD0 : 0 ≤ D := le_of_lt hDpos
  let C : Fin (a + 2 * m) → Finset ℤ := prefam (ℓ := a + 2 * m) A han
  let Phead : (Fin a → ℤ) → Prop := fun p0 => esup (lvl f p a p0) ≤ Lp / D
  let Q : (Fin (a + 2 * m) → ℤ) → Prop := fun u => Lc / D < esup (lvl f p (a + 2 * m) u)
  let Pfun : (Fin (a + 2 * m) → ℤ) → Prop := fun u =>
    Phead (pre u a (Nat.le_add_right a (2 * m))) ∧ Q u
  have hXeq : ((prodFinset n A).filter (fun x : Fin n → ℤ =>
        esup (lvl f p a (pre x a ha)) ≤ Lp / D ∧
        Lc / D < esup (lvl f p (a + 2 * m) (pre x (a + 2 * m) han))))
      = (prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (pre x (a + 2 * m) han)) := by
    apply Finset.filter_congr
    intro x hx
    have hprepre : pre (pre x (a + 2 * m) han) a (Nat.le_add_right a (2 * m))
        = pre x a ha := by
      have h1 := pre_pre_general (x := x) (s := a + 2 * m) (k := a)
        (hks := Nat.le_add_right a (2 * m)) (hsℓ := han)
      calc
        pre (pre x (a + 2 * m) han) a (Nat.le_add_right a (2 * m))
            = pre x a (le_trans (Nat.le_add_right a (2 * m)) han) := h1
        _ = pre x a ha := pre_irrel x
    have heq1 : esup (lvl f p a (pre (pre x (a + 2 * m) han) a (Nat.le_add_right a (2 * m))))
        = esup (lvl f p a (pre x a ha)) := by
      congr 1
    dsimp [Pfun, Phead, Q]
    rw [heq1]
  have hL1 := filter_prefix_card_real (hb := han) A (P := Pfun)
  have hmain := filter_cat_split_real (C := C) (P := Phead) (Q := Q)
  have hmain' : fcard ((prodFinset (a + 2 * m) C).filter (fun u : Fin (a + 2 * m) → ℤ => Pfun u))
      = (∑ p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead),
          fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
              (fun z : Fin (2 * m) → ℤ => Q (cat p0 z)))) := by
    dsimp [fcard, Pfun]
    simpa using hmain
  have hblkeq : prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)
      = prodFinset (2 * m) (blkFam A a m han) := by
    apply Submission.RoughProduct.prodFinset_congr
    intro t
    dsimp [C, blkFam]
    congr 1
  have hterm : ∀ p0 : Fin a → ℤ,
      p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead) →
      fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
          (fun z : Fin (2 * m) → ℤ => Q (cat p0 z)))
        ≤ e2 * blkAll A a m han := by
    intro p0 hp0
    rw [Finset.mem_filter] at hp0
    have hzconv : ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
          (fun z : Fin (2 * m) → ℤ => Q (cat p0 z)))
        = (prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
            Lc / D < esup (lvl (lvl f p a p0) p (2 * m) z)) := by
      rw [hblkeq]
      apply Finset.filter_congr
      intro z hz
      dsimp [Q]
      rw [lvl_esup_cat_eq p0 z f p]
    have hcontain : ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
            Lc / D < esup (lvl (lvl f p a p0) p (2 * m) z)))
        ⊆ ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
            θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) z))) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      have hthr : θ * Lp / D ≤ Lc / D := by
        exact div_le_div_of_nonneg_right hLθ hD0
      exact lt_of_le_of_lt hthr hz.2
    have hprec := hpre p0 hp0.1 hp0.2
    calc
      fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
          (fun z : Fin (2 * m) → ℤ => Q (cat p0 z)))
          = fcard ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
              Lc / D < esup (lvl (lvl f p a p0) p (2 * m) z))) := by
            rw [hzconv]
      _ ≤ fcard ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
              θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) z))) := by
            dsimp [fcard]
            exact_mod_cast (Finset.card_le_card hcontain)
      _ ≤ e2 * blkAll A a m han := hprec
  -- sum over prefixes of the per-prefix bound
  have hsum : (∑ p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead),
        fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
            (fun z : Fin (2 * m) → ℤ => Q (cat p0 z))))
      ≤ e2 * (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) := by
    have hb0 : 0 ≤ e2 * blkAll A a m han := by
      have hb1 : 0 ≤ blkAll A a m han := by
        dsimp [blkAll]
        apply Finset.prod_nonneg
        intro j hj
        exact_mod_cast (Nat.zero_le _)
      exact mul_nonneg he2 hb1
    calc
      (∑ p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead),
          fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
              (fun z : Fin (2 * m) → ℤ => Q (cat p0 z))))
          ≤ ∑ p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead),
              (e2 * blkAll A a m han) := by
            apply Finset.sum_le_sum
            intro p0 hp0
            exact hterm p0 hp0
      _ = fcard ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead)
            * (e2 * blkAll A a m han) := by
            dsimp [fcard]
            rw [Finset.sum_const]
            rw [nsmul_eq_mul]
      _ ≤ fcard (prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j)))
            * (e2 * blkAll A a m han) := by
            have hf : fcard ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead)
                ≤ fcard (prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))) := by
              dsimp [fcard]
              exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
            exact mul_le_mul_of_nonneg_right hf hb0
      _ = e2 * (fcard (prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))) * blkAll A a m han) := by
            ring
      _ = e2 * (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) := by
            congr 1
            have hfacC : fcard (prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))) * blkAll A a m han
                = (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) := by
              have h1 := cast_card_prod (fun j : Fin a => C (Fin.castAdd (2 * m) j))
              have hfacB := blk_prod_factor (han := han) (A := A)
              calc
                fcard (prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))) * blkAll A a m han
                    = (∏ j : Fin a, (((C (Fin.castAdd (2 * m) j)).card : ℕ) : ℝ)) * blkAll A a m han := by
                      dsimp [fcard]
                      rw [h1]
                _ = (∏ j : Fin a, (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) * blkAll A a m han := by
                      congr 1
                _ = (∏ j : Fin (a + 2 * m), (((A ⟨j.val, by omega⟩).card : ℕ) : ℝ)) := hfacB.symm
                _ = (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) := by
                      rfl
            exact hfacC
  -- final assembly
  have htail0 : 0 ≤ (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ)) := by
    apply Finset.prod_nonneg
    intro j hj
    exact_mod_cast (Nat.zero_le _)
  have hfacAll := prod_factor_real (hb := han) A
  calc
    fcard ((prodFinset n A).filter (fun x : Fin n → ℤ =>
        esup (lvl f p a (pre x a ha)) ≤ Lp / D ∧
        Lc / D < esup (lvl f p (a + 2 * m) (pre x (a + 2 * m) han))))
        = fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (pre x (a + 2 * m) han))) := by
          rw [hXeq]
    _ = fcard ((prodFinset (a + 2 * m) C).filter Pfun) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ)) := by
          -- from filter_prefix_card_real
          have hc := filter_prefix_card_real (hb := han) A (P := Pfun)
          simpa [fcard, C, Pfun, Phead, Q] using hc
    _ = ((∑ p0 ∈ ((prodFinset a (fun j : Fin a => C (Fin.castAdd (2 * m) j))).filter Phead),
            fcard ((prodFinset (2 * m) (fun t : Fin (2 * m) => C ⟨a + t.val, by omega⟩)).filter
                (fun z : Fin (2 * m) → ℤ => Q (cat p0 z))))) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ)) := by
          rw [hmain']
    _ ≤ (e2 * (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ))) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hsum htail0
    _ = e2 * (∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ)) := by ring
    _ = e2 * ((∏ j : Fin (a + 2 * m), (((C j).card : ℕ) : ℝ)) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ))) := by ring
    _ = e2 * ((∏ j : Fin (a + 2 * m), ((((prefam (ℓ := a + 2 * m) A han) j).card : ℕ) : ℝ)) *
          (∏ j : Fin (n - (a + 2 * m)), (((A ⟨(a + 2 * m) + j.val, by omega⟩).card : ℕ) : ℝ))) := by
          dsimp [C]
    _ = e2 * allAll A := by
          -- ∏_{Fin(a+2m)} |prefam A han| · ∏tail = ∏_Fin n |A|
          have hfacA := prod_factor_real (hb := han) A
          dsimp [allAll]
          rw [hfacA]



/-! ## 15. Block-vector ↔ (first-half, tailOf) pair bridge -/

lemma catTwo_pre_tailOf {m : ℕ} (z : Fin (2 * m) → ℤ) :
    catTwo (pre z m (by omega : m ≤ 2 * m), tailOf z) = z := by
  funext q
  dsimp [catTwo, tailOf]
  by_cases hq : q.val < m
  · rw [dif_pos hq]
    rfl
  · rw [dif_neg hq]
    have harg : (⟨m + (q.val - m), by omega⟩ : Fin (2 * m)) = q := by
      apply Fin.ext
      simp
      omega
    rw [harg]

/-- the block product over `Fin (2m)` is the pair product under `catTwo`. -/
lemma prodFinset_catTwo_image {m : ℕ} (B : Fin (2 * m) → Finset ℤ) :
    prodFinset (2 * m) B =
      ((prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k))).product
        (prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))).image
        (fun q : (Fin m → ℤ) × (Fin m → ℤ) => catTwo q) := by
  apply Finset.ext
  intro z
  rw [Finset.mem_image]
  constructor
  · intro hz
    refine ⟨(pre z m (by omega : m ≤ 2 * m), tailOf z), ?_, ?_⟩
    · have hm1 : pre z m (by omega : m ≤ 2 * m) ∈
          prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)) := by
        rw [mem_prodFinset]
        intro k
        have hmem := (mem_prodFinset B z).1 hz (Fin.castLE (by omega : m ≤ 2 * m) k)
        rwa [← (show z (Fin.castLE (by omega : m ≤ 2 * m) k) = (pre z m (by omega : m ≤ 2 * m)) k by rfl)]
      have hm2 : tailOf z ∈
          prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩) := by
        rw [mem_prodFinset]
        intro k
        have hmem := (mem_prodFinset B z).1 hz ⟨m + k.val, by omega⟩
        rwa [← (show z ⟨m + k.val, by omega⟩ = (tailOf z) k by rfl)]
      exact (Finset.mem_product (s := prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)))
        (t := prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))).mpr ⟨hm1, hm2⟩
    · exact catTwo_pre_tailOf z
  · intro h
    rcases h with ⟨q, hq, hz⟩
    rw [← hz]
    rw [mem_prodFinset]
    intro j
    by_cases hj : j.val < m
    · have hmem := (mem_prodFinset (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)) q.1).1
          (Finset.mem_product.mp hq).1 ⟨j.val, hj⟩
      have hq' : (catTwo q) j = q.1 ⟨j.val, hj⟩ := by
        dsimp [catTwo]
        rw [dif_pos hj]
      rw [hq']
      have hfam : B j = B (Fin.castLE (by omega : m ≤ 2 * m) ⟨j.val, hj⟩) := by
        congr 1
      rwa [hfam]
    · have hmem := (mem_prodFinset (fun k : Fin m => B ⟨m + k.val, by omega⟩) q.2).1
          (Finset.mem_product.mp hq).2 ⟨j.val - m, by omega⟩
      have hq' : (catTwo q) j = q.2 ⟨j.val - m, by omega⟩ := by
        dsimp [catTwo]
        rw [dif_neg hj]
      rw [hq']
      have hfam : B j = B ⟨m + (j.val - m), by omega⟩ := by
        congr 1
        apply Fin.ext
        simp
        omega
      rwa [hfam]

/-- filter-card over the `2m`-block product equals the pair-filter under
`catTwo` (first half / `tailOf`). -/
lemma pair_filter_card {m : ℕ} (B : Fin (2 * m) → Finset ℤ)
    (P : (Fin (2 * m) → ℤ) → Prop) :
    fcard ((prodFinset (2 * m) B).filter (fun z : Fin (2 * m) → ℤ => P z)) =
      fcard (((prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k))).product
        (prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))).filter
          (fun q : (Fin m → ℤ) × (Fin m → ℤ) => P (catTwo q))) := by
  classical
  let R : Finset ((Fin m → ℤ) × (Fin m → ℤ)) :=
    (prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k))).product
      (prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))
  have hcard : ((prodFinset (2 * m) B).filter (fun z : Fin (2 * m) → ℤ => P z)).card
      = (R.filter (fun q : (Fin m → ℤ) × (Fin m → ℤ) => P (catTwo q))).card := by
    apply Finset.card_bij (s := (prodFinset (2 * m) B).filter (fun z => P z))
      (t := R.filter (fun q => P (catTwo q)))
      (fun z hz => (pre z m (by omega : m ≤ 2 * m), tailOf z))
    · intro z hz
      rw [Finset.mem_filter] at hz
      rw [Finset.mem_filter]
      constructor
      · -- (pre z m, tailOf z) ∈ R
        have hm1 : pre z m (by omega : m ≤ 2 * m) ∈
            prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)) := by
          rw [mem_prodFinset]
          intro k
          have hmem := (mem_prodFinset B z).1 hz.1 (Fin.castLE (by omega : m ≤ 2 * m) k)
          rwa [← (show z (Fin.castLE (by omega : m ≤ 2 * m) k) = (pre z m (by omega : m ≤ 2 * m)) k by rfl)]
        have hm2 : tailOf z ∈ prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩) := by
          rw [mem_prodFinset]
          intro k
          have hmem := (mem_prodFinset B z).1 hz.1 ⟨m + k.val, by omega⟩
          rwa [← (show z ⟨m + k.val, by omega⟩ = (tailOf z) k by rfl)]
        exact (Finset.mem_product (s := prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)))
          (t := prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))).mpr ⟨hm1, hm2⟩
      · simpa [catTwo_pre_tailOf] using hz.2
    · intro z₁ hz₁ z₂ hz₂ h
      have hcat := congrArg (fun q : (Fin m → ℤ) × (Fin m → ℤ) => catTwo q) h
      -- hcat : catTwo (pre z₁ m, tailOf z₁) = catTwo (pre z₂ m, tailOf z₂)
      rw [catTwo_pre_tailOf, catTwo_pre_tailOf] at hcat
      exact hcat
    · intro q hq
      rw [Finset.mem_filter] at hq
      refine ⟨catTwo q, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rcases (Finset.mem_product (s := prodFinset m (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)))
            (t := prodFinset m (fun k : Fin m => B ⟨m + k.val, by omega⟩))).mp hq.1 with ⟨h1, h2⟩
          rw [mem_prodFinset]
          intro j
          by_cases hj : j.val < m
          · have hmem := (mem_prodFinset (fun k : Fin m => B (Fin.castLE (by omega : m ≤ 2 * m) k)) q.1).1 h1 ⟨j.val, hj⟩
            have hq' : (catTwo q) j = q.1 ⟨j.val, hj⟩ := by
              dsimp [catTwo]
              rw [dif_pos hj]
            rw [hq']
            have hfam : B j = B (Fin.castLE (by omega : m ≤ 2 * m) ⟨j.val, hj⟩) := by
              congr 1
            rwa [hfam]
          · have hmem := (mem_prodFinset (fun k : Fin m => B ⟨m + k.val, by omega⟩) q.2).1 h2 ⟨j.val - m, by omega⟩
            have hq' : (catTwo q) j = q.2 ⟨j.val - m, by omega⟩ := by
              dsimp [catTwo]
              rw [dif_neg hj]
            rw [hq']
            have hfam : B j = B ⟨m + (j.val - m), by omega⟩ := by
              congr 1
              apply Fin.ext
              simp
              omega
            rwa [hfam]
        · exact hq.2
      · have h1 := pre_catTwo_fst q
        have h2 := tailOf_catTwo q
        exact Prod.ext h1 h2
  simpa [fcard, R] using hcard



/-! ## 16. Block-all split into first/second m-halves -/

lemma blkAll_split {n a m : ℕ} (han : a + 2 * m ≤ n) (A : Fin n → Finset ℤ) :
    blkAll A a m han =
      (∏ k : Fin m, (((A ⟨a + k.val, by omega⟩).card : ℕ) : ℝ)) *
        (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ)) := by
  classical
  let B : Fin (2 * m) → Finset ℤ := blkFam A a m han
  have hfac := prod_factor_real (hb := (by omega : m ≤ 2 * m)) B
  -- hfac: ∏_Fin(2m)|B| = ∏_Fin m |prefam B (m≤2m)| · ∏_Fin(2m−m)|B⟨m+·⟩|
  have hB1 : (∏ j : Fin (2 * m), (((B j).card : ℕ) : ℝ)) = blkAll A a m han := by
    rfl
  have hAr : (2 * m) - m = m := by omega
  have hpref : (∏ k : Fin m, ((((prefam (ℓ := m) B (by omega : m ≤ 2 * m)) k).card : ℕ) : ℝ))
      = (∏ k : Fin m, (((A ⟨a + k.val, by omega⟩).card : ℕ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rfl
  have htail : (∏ j : Fin ((2 * m) - m), (((B ⟨m + j.val, by omega⟩).card : ℕ) : ℝ))
      = (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ)) := by
    have hconv := prod_fin_congr_equiv_real (h := hAr)
      (f := fun j : Fin ((2 * m) - m) => (((B ⟨m + j.val, by omega⟩).card : ℕ) : ℝ))
      (g := fun j : Fin m => (((B ⟨m + j.val, by omega⟩).card : ℕ) : ℝ))
      (by intro j; rfl)
    have hB2 : (∏ j : Fin m, (((B ⟨m + j.val, by omega⟩).card : ℕ) : ℝ))
        = (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      congr 1
      dsimp [B, blkFam]
      congr 1
      apply congrArg A
      apply Fin.ext
      simp
      omega
    exact hconv.trans hB2
  calc
    blkAll A a m han = (∏ j : Fin (2 * m), (((B j).card : ℕ) : ℝ)) := hB1.symm
    _ = (∏ k : Fin m, ((((prefam (ℓ := m) B (by omega : m ≤ 2 * m)) k).card : ℕ) : ℝ)) *
          (∏ j : Fin ((2 * m) - m), (((B ⟨m + j.val, by omega⟩).card : ℕ) : ℝ)) := hfac
    _ = (∏ k : Fin m, (((A ⟨a + k.val, by omega⟩).card : ℕ) : ℝ)) *
          (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ)) := by
          rw [hpref, htail]



/-! ## 17. Per-prefix export instantiation (`export_hpre`) -/

lemma export_hpre {n a m : ℕ} (hn1 : 1 ≤ n) (han : a + 2 * m ≤ n)
    (p : unitInterval) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (N : ℕ) (hN1 : 1 ≤ N) (A : Fin n → Finset ℤ)
    (Lp θ : ℝ) (e2 μm Rt : ℝ)
    (f : ℤ → ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hfsum : Summable f)
    (hlipf : Submission.Ell2Update.ratioLip μm f) (hfmass : norm₁ f ≤ 1)
    (hMass : ∀ u : Fin a → ℤ,
        u ∈ prodFinset a (prefam (ℓ := a) A (le_trans (Nat.le_add_right a (2 * m)) han)) →
        ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ))
    (c d loS hiS : Fin m → ℤ)
    (hint1 : ∀ k : Fin m, A ⟨a + k.val, by omega⟩ = Finset.Icc (c k) (d k))
    (hint2 : ∀ k : Fin m, A ⟨a + m + k.val, by omega⟩ = Finset.Icc (loS k) (hiS k))
    (hJlen : ∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (c k) (d k)).card : ℕ) : ℝ))
    (hSlen : ∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (loS k) (hiS k)).card : ℕ) : ℝ))
    (hExp : ∀ {u : Fin a → ℤ}, (∀ t : ℤ, 0 ≤ lvl f p a u t) →
        (Summable (fun t : ℤ => (lvl f p a u t) ^ 2)) → (Summable (lvl f p a u)) →
        Submission.Ell2Update.ratioLip μm (lvl f p a u) →
        (∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ)) →
        norm₁ (lvl f p a u) ≤ 1 →
        (∀ t : ℤ, lvl f p a u t ≤ Lp / sqrtDen N n) →
        ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            θ * Lp / sqrtDen N n <
              esup (lvl (lvl f p a u) p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℝ) ≤
          e2 * (∏ j : Fin m, ((((Finset.Icc (c j) (d j)).card : ℕ) : ℝ))) *
            (∏ j : Fin m, ((((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)))) :
    ∀ p0 : Fin a → ℤ,
      p0 ∈ prodFinset a (fun j : Fin a => (prefam (ℓ := a + 2 * m) A han) (Fin.castAdd (2 * m) j)) →
      esup (lvl f p a p0) ≤ Lp / sqrtDen N n →
      fcard ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
        θ * Lp / sqrtDen N n < esup (lvl (lvl f p a p0) p (2 * m) z))) ≤
        e2 * blkAll A a m han := by
  classical
  let D : ℝ := sqrtDen N n
  let ha' : a ≤ n := le_trans (Nat.le_add_right a (2 * m)) han
  intro p0 hp0mem hE
  -- membership in the `prefam A ha'`-form of the head product
  have hmemA : p0 ∈ prodFinset a (prefam (ℓ := a) A ha') := by
    apply (mem_prodFinset (prefam (ℓ := a) A ha') p0).2
    intro j
    have hmj := (mem_prodFinset (fun j : Fin a => (prefam (ℓ := a + 2 * m) A han) (Fin.castAdd (2 * m) j)) p0).1 hp0mem j
    have hcoord : (prefam (ℓ := a + 2 * m) A han) (Fin.castAdd (2 * m) j) = prefam (ℓ := a) A ha' j := by
      dsimp [prefam]
      congr 1
    have hmj' : p0 j ∈ prefam (ℓ := a) A ha' j := by
      rwa [hcoord] at hmj
    exact hmj'
  have hgpos : ∀ t : ℤ, 0 ≤ lvl f p a p0 t := lvl_nonneg a p0 hfpos
  have hg2 : Summable (fun t : ℤ => (lvl f p a p0 t) ^ 2) := lvl_sq_summable a hf2 p0
  have hgsum : Summable (lvl f p a p0) := lvl_summable a p0 hfsum
  have hgLip : Submission.Ell2Update.ratioLip μm (lvl f p a p0) := lvl_ratioLip a hlipf p0
  have hgNorm : norm₁ (lvl f p a p0) ≤ 1 := norm₁_lvl_le_one a p0 hfsum hfmass
  have hgMass : ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a p0 t) ≤ Rt / Real.sqrt (n : ℝ) := hMass p0 hmemA
  have hgSup : ∀ t : ℤ, lvl f p a p0 t ≤ Lp / D := by
    dsimp [D]
    exact (esup_le_iff hgpos hgsum).1 hE
  have hb := hExp hgpos hg2 hgsum hgLip hgMass hgNorm hgSup
  -- z-filter predicate
  let Pz : (Fin (2 * m) → ℤ) → Prop := fun z =>
    θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) z)
  have hpc := pair_filter_card (B := blkFam A a m han) (P := Pz)
  -- family equalities between blkFam-halves and Icc(c)(d)/Icc(loS)(hiS)
  have hfam1eq : prodFinset m (fun k : Fin m => blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k))
      = prodFinset m (fun k : Fin m => Finset.Icc (c k) (d k)) := by
    apply Submission.RoughProduct.prodFinset_congr
    intro k
    have hc : blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k) = A ⟨a + k.val, by omega⟩ := by
      dsimp [blkFam]
    calc
      blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k) = A ⟨a + k.val, by omega⟩ := hc
      _ = Finset.Icc (c k) (d k) := hint1 k
  have hfam2eq : prodFinset m (fun k : Fin m => blkFam A a m han ⟨m + k.val, by omega⟩)
      = prodFinset m (fun k : Fin m => Finset.Icc (loS k) (hiS k)) := by
    apply Submission.RoughProduct.prodFinset_congr
    intro k
    have hc : blkFam A a m han ⟨m + k.val, by omega⟩ = A ⟨a + m + k.val, by omega⟩ := by
      dsimp [blkFam]
      congr 1
      apply Fin.ext
      simp
      omega
    calc
      blkFam A a m han ⟨m + k.val, by omega⟩ = A ⟨a + m + k.val, by omega⟩ := hc
      _ = Finset.Icc (loS k) (hiS k) := hint2 k
  -- pair-filter z ↔ (first-half, tailOf) conversion
  let Pz : (Fin (2 * m) → ℤ) → Prop := fun z =>
    θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) z)
  have hpc := pair_filter_card (B := blkFam A a m han) (P := Pz)
  have hEqIcc : ((prodFinset m (fun k : Fin m => blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k))).product
        (prodFinset m (fun k : Fin m => blkFam A a m han ⟨m + k.val, by omega⟩)))
      = ((prodFinset m (fun k : Fin m => Finset.Icc (c k) (d k))).product
          (prodFinset m (fun k : Fin m => Finset.Icc (loS k) (hiS k)))) := by
    rw [hfam1eq, hfam2eq]
  have hpreEq : ((prodFinset m (fun k : Fin m => blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k))).product
        (prodFinset m (fun k : Fin m => blkFam A a m han ⟨m + k.val, by omega⟩))).filter
          (fun q : (Fin m → ℤ) × (Fin m → ℤ) => Pz (catTwo q))
      = ((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
          (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun q : (Fin m → ℤ) × (Fin m → ℤ) =>
            θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) (pre (catTwo q) (2 * m) (le_refl (2 * m))))) := by
    rw [hEqIcc]
    apply Finset.filter_congr
    intro q hq
    dsimp [Pz]
    have hpre2 : pre (catTwo q) (2 * m) (le_refl (2 * m)) = catTwo q := pre_self (catTwo q)
    rw [hpre2]
  -- export bound on the Icc-pair filter equals hb applied at u := p0
  have hb' : fcard (((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
          (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun q : (Fin m → ℤ) × (Fin m → ℤ) =>
            θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) (pre (catTwo q) (2 * m) (le_refl (2 * m))))))
      ≤ e2 * (∏ j : Fin m, ((((Finset.Icc (c j) (d j)).card : ℕ) : ℝ))) *
          (∏ j : Fin m, ((((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))) := by
    dsimp [D]
    exact hb
  calc
    fcard ((prodFinset (2 * m) (blkFam A a m han)).filter (fun z : Fin (2 * m) → ℤ =>
        θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) z)))
        = fcard (((prodFinset m (fun k : Fin m => blkFam A a m han (Fin.castLE (by omega : m ≤ 2 * m) k))).product
            (prodFinset m (fun k : Fin m => blkFam A a m han ⟨m + k.val, by omega⟩))).filter
            (fun q : (Fin m → ℤ) × (Fin m → ℤ) => Pz (catTwo q))) := by
          dsimp [Pz] at hpc
          simpa [Pz] using hpc
    _ = fcard (((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
            (fun q : (Fin m → ℤ) × (Fin m → ℤ) =>
              θ * Lp / D < esup (lvl (lvl f p a p0) p (2 * m) (pre (catTwo q) (2 * m) (le_refl (2 * m)))))) := by
          rw [hpreEq]
    _ ≤ e2 * (∏ j : Fin m, ((((Finset.Icc (c j) (d j)).card : ℕ) : ℝ))) *
          (∏ j : Fin m, ((((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ))) := hb'
    _ = e2 * blkAll A a m han := by
          -- blkAll_split + hint1/hint2
          have hbs := blkAll_split (han := han) (A := A)
          have h1 : (∏ k : Fin m, (((A ⟨a + k.val, by omega⟩).card : ℕ) : ℝ))
              = (∏ k : Fin m, ((((Finset.Icc (c k) (d k)).card : ℕ) : ℝ))) := by
            apply Finset.prod_congr rfl
            intro k hk
            congr 1
            rw [hint1 k]
          have h2 : (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ))
              = (∏ k : Fin m, ((((Finset.Icc (loS k) (hiS k)).card : ℕ) : ℝ))) := by
            apply Finset.prod_congr rfl
            intro k hk
            congr 1
            rw [hint2 k]
          calc
            e2 * (∏ j : Fin m, ((((Finset.Icc (c j) (d j)).card : ℕ) : ℝ))) *
                (∏ j : Fin m, ((((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)))
                = e2 * ((∏ k : Fin m, (((A ⟨a + k.val, by omega⟩).card : ℕ) : ℝ)) *
                    (∏ k : Fin m, (((A ⟨a + m + k.val, by omega⟩).card : ℕ) : ℝ))) := by
                  rw [← h1, ← h2]
                  ring
            _ = e2 * blkAll A a m han := by
                  rw [← hbs]



set_option maxHeartbeats 6000000

/-- esup at level `k₁` (pre x) equals esup at an equal level `k₂`. -/
lemma esup_lvl_pre_congr_level {f : ℤ → ℝ} {p : unitInterval} {n k₁ k₂ : ℕ}
    (hk₁ : k₁ ≤ n) (hk₂ : k₂ ≤ n) (h : k₁ = k₂) (x : Fin n → ℤ) :
    esup (lvl f p k₁ (pre x k₁ hk₁)) = esup (lvl f p k₂ (pre x k₂ hk₂)) := by
  subst k₂
  congr 1

/-- pre with different proof arguments are equal (proof irrelevance). -/
lemma filter_pre_irrel {n k : ℕ} (hk₁ hk₂ : k ≤ n) (A : Fin n → Finset ℤ)
    (Q : (Fin k → ℤ) → Prop) :
    (prodFinset n A).filter (fun x : Fin n → ℤ => Q (pre x k hk₁)) =
      (prodFinset n A).filter (fun x : Fin n → ℤ => Q (pre x k hk₂)) := by
  apply Finset.filter_congr
  intro x hx
  have hpre : pre x k hk₁ = pre x k hk₂ := pre_irrel x
  rw [hpre]

/-- interval with `(N:ℤ) ≤ d−c+1` has real cardinality `≥ N`. -/
lemma Icc_card_real_of_ge {c d : ℤ} {N : ℕ} (hN1 : 1 ≤ N) (h : (N : ℤ) ≤ d - c + 1) :
    (N : ℝ) ≤ (((Finset.Icc c d).card : ℕ) : ℝ) := by
  have hpos : 0 ≤ d + 1 - c := by omega
  have hcardz : ((Finset.Icc c d).card : ℤ) = d - c + 1 := by
    calc
      ((Finset.Icc c d).card : ℤ) = ((d + 1 - c : ℤ).toNat : ℤ) := by rw [Int.card_Icc]
      _ = d + 1 - c := by rw [Int.toNat_of_nonneg hpos]
      _ = d - c + 1 := by omega
  have hZi : (N : ℤ) ≤ ((Finset.Icc c d).card : ℤ) := by
    rwa [hcardz]
  have hNnat : N ≤ (Finset.Icc c d).card := (Int.ofNat_le.mp hZi)
  exact_mod_cast hNnat

/-- A length-`2m` block of single-interval (large) coordinates splits into two
`m`-families of intervals `c,d` (first half) and `loS,hiS` (second half). -/
lemma exists_block_intervals {n ℓ a m : ℕ} {δ : ℝ} (hδ₁₂ : δ ≤ 1 / 2)
    (hℓge : n ≤ 2 * ℓ) (hℓa : ℓ ≤ a) (han : a + 2 * m ≤ n)
    {N : ℕ} (hN1 : 1 ≤ N) {A : Fin n → Finset ℤ}
    (hAdm : Admissible N n n δ A) :
    ∃ (c d loS hiS : Fin m → ℤ),
      (∀ k : Fin m, A ⟨a + k.val, by omega⟩ = Finset.Icc (c k) (d k)) ∧
      (∀ k : Fin m, A ⟨a + m + k.val, by omega⟩ = Finset.Icc (loS k) (hiS k)) ∧
      (∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (c k) (d k)).card : ℕ) : ℝ)) ∧
      (∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (loS k) (hiS k)).card : ℕ) : ℝ)) := by
  classical
  have hns1 : ∀ k : Fin m, ¬ smallIndex n δ (a + k.val) := by
    intro k
    exact not_smallIndex_of_ge_half hδ₁₂ hℓge (by omega) (by omega)
  have hns2 : ∀ k : Fin m, ¬ smallIndex n δ (a + m + k.val) := by
    intro k
    exact not_smallIndex_of_ge_half hδ₁₂ hℓge (by omega) (by omega)
  let g1 : (k : Fin m) → ∃ c d : ℤ,
      A ⟨a + k.val, by omega⟩ = Finset.Icc c d ∧ (N : ℤ) ≤ d - c + 1 := by
    intro k
    exact single_interval_of_large (hA := hAdm) (i := ⟨a + k.val, by omega⟩) (hns1 k)
  let g2 : (k : Fin m) → ∃ c d : ℤ,
      A ⟨a + m + k.val, by omega⟩ = Finset.Icc c d ∧ (N : ℤ) ≤ d - c + 1 := by
    intro k
    exact single_interval_of_large (hA := hAdm) (i := ⟨a + m + k.val, by omega⟩) (hns2 k)
  refine ⟨(fun k => (g1 k).choose), (fun k => (g1 k).choose_spec.choose),
    (fun k => (g2 k).choose), (fun k => (g2 k).choose_spec.choose), ?_, ?_, ?_, ?_⟩
  · intro k
    exact (g1 k).choose_spec.choose_spec.1
  · intro k
    exact (g2 k).choose_spec.choose_spec.1
  · intro k
    exact Icc_card_real_of_ge hN1 (g1 k).choose_spec.choose_spec.2
  · intro k
    exact Icc_card_real_of_ge hN1 (g2 k).choose_spec.choose_spec.2

/-- Assemble `export_hpre` + `refine_block_bound`: a per-block bound.
All export-level inputs (`hMass`, interval data, `hExp`) are parameters. -/
lemma block_bound_export {n a m : ℕ} (hn1 : 1 ≤ n) (han : a + 2 * m ≤ n)
    (f : ℤ → ℝ) (p : unitInterval) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
    (hfsum : Summable f) {μm : ℝ} (hlipf : Submission.Ell2Update.ratioLip μm f)
    (hfmass : norm₁ f ≤ 1)
    (N : ℕ) (hN1 : 1 ≤ N) (A : Fin n → Finset ℤ)
    (Lp θ Lc : ℝ) (hLθ : θ * Lp ≤ Lc)
    (e2 : ℝ) (he2 : 0 ≤ e2) (Rt : ℝ)
    (hMass : ∀ u : Fin a → ℤ,
        u ∈ prodFinset a (prefam (ℓ := a) A (le_trans (Nat.le_add_right a (2 * m)) han)) →
        ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ))
    (c d loS hiS : Fin m → ℤ)
    (hint1 : ∀ k : Fin m, A ⟨a + k.val, by omega⟩ = Finset.Icc (c k) (d k))
    (hint2 : ∀ k : Fin m, A ⟨a + m + k.val, by omega⟩ = Finset.Icc (loS k) (hiS k))
    (hJlen : ∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (c k) (d k)).card : ℕ) : ℝ))
    (hSlen : ∀ k : Fin m, (N : ℝ) ≤ (((Finset.Icc (loS k) (hiS k)).card : ℕ) : ℝ))
    (hExp : ∀ {u : Fin a → ℤ}, (∀ t : ℤ, 0 ≤ lvl f p a u t) →
        (Summable (fun t : ℤ => (lvl f p a u t) ^ 2)) → (Summable (lvl f p a u)) →
        Submission.Ell2Update.ratioLip μm (lvl f p a u) →
        (∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ)) →
        norm₁ (lvl f p a u) ≤ 1 →
        (∀ t : ℤ, lvl f p a u t ≤ Lp / sqrtDen N n) →
        ((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            θ * Lp / sqrtDen N n <
              esup (lvl (lvl f p a u) p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℝ) ≤
          e2 * (∏ j : Fin m, ((((Finset.Icc (c j) (d j)).card : ℕ) : ℝ))) *
            (∏ j : Fin m, ((((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)))) :
    fcard ((prodFinset n A).filter (fun x : Fin n → ℤ =>
        esup (lvl f p a (pre x a (le_trans (Nat.le_add_right a (2 * m)) han))) ≤ Lp / sqrtDen N n ∧
        Lc / sqrtDen N n < esup (lvl f p (a + 2 * m) (pre x (a + 2 * m) han))))
      ≤ e2 * allAll A := by
  classical
  refine refine_block_bound (hn1 := hn1) (han := han) (f := f) (p := p) hfpos hfsum
    (N := N) hN1 (A := A) (Lp := Lp) (Lc := Lc) (θ := θ) hLθ (e2 := e2) he2 ?_
  apply export_hpre (hn1 := hn1) (han := han) (p := p) hp₀ hp₁ (N := N) hN1 (A := A)
    (Lp := Lp) (θ := θ) (e2 := e2) (μm := μm) (Rt := Rt) (f := f) hfpos hf2 hfsum
    (hlipf := hlipf) hfmass (hMass := hMass) (c := c) (d := d) (loS := loS) (hiS := hiS)
    hint1 hint2 hJlen hSlen (hExp := hExp)

theorem averaging {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ)) :
    ∃ (L : ℝ), 0 < L ∧
      ∀ (M : ℝ) (hM : 1 ≤ M), ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧ 1 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N),
        (N : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n →
        ∀ (A : Fin n → Finset ℤ)
          (hAdm : Admissible N n n δ A)
          (hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
        ∀ (f : ℤ → ℝ) (hfpos : ∀ t : ℤ, 0 ≤ f t)
          (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1)
          (hlip : Submission.Ell2Update.ratioLip η f),
          (((prodFinset n A).filter (fun x : Fin n → ℤ =>
            L / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p n x))).card : ℝ) ≤
            Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, ((A j).card : ℝ)) := by
  classical
  -- α-level data
  rcases exists_alpha_level hp₀ hp₁ hε₀ hεp with ⟨α, hαge, hαlt, hαrest⟩
  rcases hαrest with ⟨nα, hαn⟩
  have h1mα : 0 < 1 - α := by linarith
  -- mass constant C₂
  rcases Submission.RoughDecay.aux_simple_ac2 with ⟨C₂, hC₂pos, hC₂body⟩
  let Rt : ℝ := max 1 (C₂ / Real.sqrt ((δ / 2) * (p : ℝ)))
  have hRt1 : 1 ≤ Rt := by
    dsimp [Rt]
    exact le_max_left _ _
  -- theta and q (export-compatible form θ := (√2 p + 2(1−p))/2, so
  -- prop_refinement's threshold ((√2p+2(1−p))·L/(2D)) equals θ·L/D)
  let th : ℝ := (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) / 2
  have hsqrt_lt2 : Real.sqrt 2 < 2 := by
    have hsq : (Real.sqrt 2) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have habs := (sq_lt_sq.mp hsq)
    have h1 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at habs
  have hth0 : 0 < th := by
    dsimp [th]
    have hnum : 0 < Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ)) := by
      have h1 : 0 ≤ 1 - (p : ℝ) := by linarith
      have h2 : 0 ≤ Real.sqrt 2 * (p : ℝ) := by positivity
      nlinarith [hsqrt_lt2]
    positivity
  have hth1 : th < 1 := by
    dsimp [th]
    -- th = 1 − p·(2−√2)/2 < 1 since p > 0, √2 < 2
    have hcalc : (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) / 2
        = 1 - (p : ℝ) * (2 - Real.sqrt 2) / 2 := by
      ring_nf
    rw [hcalc]
    have h2ms : 0 < 2 - Real.sqrt 2 := by linarith
    nlinarith
  refine ⟨16 * Rt, ?_, ?_⟩
  · have hRt0 : 0 < Rt := lt_of_lt_of_le (by norm_num) hRt1
    positivity
  · intro M hM
    -- Event₀ (rough) constants
    rcases e0_full_bound hp₀ hp₁ hδ₀ hδ₁₂ hε₀ hεp hM (α := α) hαge hαlt nα hαn with ⟨Lr, nE0, hLr1, hnE0, hE0⟩
    rcases Commons.Analysis.Real.exists_geom_pow_le_one_div (θ := th) hth0 hth1 (L := Lr) hLr1 with ⟨q, hq1, hθq⟩
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    -- eps tilde
    let ee : ℝ := (1 - α) / (4 * (q : ℝ))
    have hee0 : 0 < ee := by
      dsimp [ee]
      positivity
    have hee12 : ee ≤ 1 / 2 := by
      dsimp [ee]
      have h1a : 1 - α ≤ 1 / 2 := by linarith
      have h4q : (0 : ℝ) < 4 * (q : ℝ) := by positivity
      calc
        (1 - α) / (4 * (q : ℝ)) ≤ (1 / 2) / (4 * (q : ℝ)) := div_le_div_of_nonneg_right h1a h4q.le
        _ ≤ 1 / 2 := by
              have hqge : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
              have h4q1 : 1 ≤ 4 * (q : ℝ) := by nlinarith
              exact (div_le_iff₀ h4q).2 (by nlinarith)
    let eta : ℝ := (Submission.PropRefine3.mu0 (2 * M) ee) ^ 4
    have h2M : 1 ≤ 2 * M := by nlinarith
    have hEta : 0 < eta := by
      dsimp [eta]
      exact pow_pos (mu0_pos (2 * M) ee) 4
    -- export body
    let L0exp : ℝ := max (16 * Rt) Lr
    have hL016 : 16 * Rt ≤ L0exp := by
      dsimp [L0exp]
      exact le_max_left _ _
    rcases Submission.RefineExport.prop_refinement_even (M := 2 * M) h2M (ε := ee) hee0 hee12
        (Rt := Rt) hRt1 (L0 := L0exp) hL016 (p := p) hp₀ hp₁ with ⟨nRef, hRef⟩
    -- n₀: all thresholds (named levels, avoids whnf blowup)
    let n1 : ℕ := max nE0 nRef
    let n2 : ℕ := max n1 nα
    let n3 : ℕ := max n2 q
    let n4 : ℕ := max n3 2
    let n5 : ℕ := max n4 (Nat.ceil (2 / δ))
    let n6 : ℕ := max n5 (Nat.ceil (2 / ee))
    let n7 : ℕ := max n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α))))
    let nBig : ℕ := max n7 2
    refine ⟨eta, nBig, ?_, ?_, ?_⟩
    · exact hEta
    · dsimp [nBig]
      norm_num
    · intro n hn₀ N hN1 hNa A hAdm hrad hsym f hfpos hf2 hfsum hfmass hlip
      -- 1. per-n facts from nBig ≤ n
      have hn₀' : nBig ≤ n := hn₀
      have h2n : 2 ≤ n := by
        exact le_trans (le_max_right n7 2) hn₀
      have h1n : 1 ≤ n := by omega
      have hnE0' : nE0 ≤ n := by
        exact le_trans (le_max_left nE0 nRef)
          (le_trans (le_max_left n1 nα) (le_trans (le_max_left n2 q)
          (le_trans (le_max_left n3 2) (le_trans (le_max_left n4 (Nat.ceil (2 / δ)))
          (le_trans (le_max_left n5 (Nat.ceil (2 / ee))) (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α)))))
          (le_trans (le_max_left n7 2) hn₀)))))))
      have hnRef' : nRef ≤ n := by
        exact le_trans (le_trans (le_max_right nE0 nRef) (le_max_left n1 nα))
          (le_trans (le_max_left n2 q) (le_trans (le_max_left n3 2)
          (le_trans (le_max_left n4 (Nat.ceil (2 / δ))) (le_trans (le_max_left n5 (Nat.ceil (2 / ee)))
          (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α))))) (le_trans (le_max_left n7 2) hn₀))))))
      have hnα' : nα ≤ n := by
        exact le_trans (le_max_right n1 nα) (le_trans (le_max_left n2 q)
          (le_trans (le_max_left n3 2) (le_trans (le_max_left n4 (Nat.ceil (2 / δ)))
          (le_trans (le_max_left n5 (Nat.ceil (2 / ee))) (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α)))))
          (le_trans (le_max_left n7 2) hn₀))))))
      have hnq' : q ≤ n := by
        exact le_trans (le_max_right n2 q) (le_trans (le_max_left n3 2)
          (le_trans (le_max_left n4 (Nat.ceil (2 / δ))) (le_trans (le_max_left n5 (Nat.ceil (2 / ee)))
          (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α))))) (le_trans (le_max_left n7 2) hn₀)))))
      have hnslackc : Nat.ceil (2 / δ) ≤ n := by
        exact le_trans (le_max_right n4 (Nat.ceil (2 / δ)))
          (le_trans (le_max_left n5 (Nat.ceil (2 / ee))) (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α)))))
          (le_trans (le_max_left n7 2) hn₀)))
      have hnslack : (1 : ℝ) ≤ (δ / 2) * (n : ℝ) := by
        have h2d : (2 / δ : ℝ) ≤ (n : ℝ) := (Nat.ceil_le (a := 2 / δ) (n := n)).mp hnslackc
        have hδpos : 0 < δ := hδ₀
        -- 2/δ ≤ n ⟹ δ·n ≥ 2 ⟹ (δ/2)·n ≥ 1
        have hmul := (div_le_iff₀ hδpos).1 h2d  -- hmm: a ≤ b/c ↔ a·c ≤ b with c := δ: 2 ≤ δ·n
        nlinarith
      have hneec : Nat.ceil (2 / ee) ≤ n := by
        exact le_trans (le_max_right n5 (Nat.ceil (2 / ee)))
          (le_trans (le_max_left n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α))))) (le_trans (le_max_left n7 2) hn₀))
      have hnee : (2 / ee : ℝ) ≤ (n : ℝ) := (Nat.ceil_le (a := 2 / ee) (n := n)).mp hneec
      have heen2 : 2 ≤ ee * (n : ℝ) := by
        have h := (div_le_iff₀ hee0).1 hnee  -- 2/ee ≤ n ⟹ 2 ≤ ee·n
        linarith
      let m0 : ℕ := Nat.floor (ee * (n : ℝ) / 2)
      have hm0ge1 : 1 ≤ m0 := by
        dsimp [m0]
        have hx : (1 : ℝ) ≤ ee * (n : ℝ) / 2 := by linarith [heen2]
        have hc : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
        exact Nat.le_floor (by rwa [hc])
      have hm0le : (m0 : ℝ) ≤ ee * (n : ℝ) / 2 := by
        dsimp [m0]
        exact Nat.floor_le (by positivity : 0 ≤ ee * (n : ℝ) / 2)
      have h2m0r : (2 * m0 : ℝ) ≤ ee * (n : ℝ) := by
        have h : 2 * (m0 : ℝ) ≤ ee * (n : ℝ) := by linarith
        simpa [two_mul] using h
      have h1mαn : (1 : ℝ) ≤ (3 / 4) * (1 - α) * (n : ℝ) := by
        have hc : Nat.ceil ((4 : ℝ) / (3 * (1 - α))) ≤ n := by
          exact le_trans (le_max_right n6 (Nat.ceil ((4 : ℝ) / (3 * (1 - α))))) (le_trans (le_max_left n7 2) hn₀)
        have h4 : ((4 : ℝ) / (3 * (1 - α))) ≤ (n : ℝ) := (Nat.ceil_le (a := (4 : ℝ) / (3 * (1 - α))) (n := n)).mp hc
        have hd : 0 < 3 * (1 - α) := by positivity
        have hmul := (div_le_iff₀ hd).1 h4
        nlinarith
      let ℓ : ℕ := Nat.ceil (α * (n : ℝ))
      have hℓle : ℓ ≤ n := ceil_alpha_le hαlt
      have hℓge : n ≤ 2 * ℓ := ceil_alpha_ge_half hαge
      have hℓub : (ℓ : ℝ) ≤ α * (n : ℝ) + 1 := by
        dsimp [ℓ]
        have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ α * (n : ℝ))
        linarith
      have hqee : (q : ℝ) * (ee * (n : ℝ)) ≤ ((1 - α) / 4) * (n : ℝ) := by
        have hqpos' : (q : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hq1))
        calc
          (q : ℝ) * (ee * (n : ℝ)) = ((1 - α) / 4) * (n : ℝ) := by
            dsimp [ee]
            field_simp [hqpos']
          _ ≤ ((1 - α) / 4) * (n : ℝ) := le_rfl
      have hiq_le : ℓ + q * (2 * m0) ≤ n := by
        have hr : ((ℓ : ℝ) + ((q * (2 * m0) : ℕ) : ℝ)) ≤ (n : ℝ) := by
          calc
            ((ℓ : ℝ) + ((q * (2 * m0) : ℕ) : ℝ))
                ≤ (α * (n : ℝ) + 1) + ((q * (2 * m0) : ℕ) : ℝ) := by
                  exact add_le_add_left hℓub ((q * (2 * m0) : ℕ) : ℝ)
            _ ≤ (α * (n : ℝ) + 1) + (q : ℝ) * (ee * (n : ℝ)) := by
                  have hqle : ((q * (2 * m0) : ℕ) : ℝ) ≤ (q : ℝ) * (ee * (n : ℝ)) := by
                    have h1 : (q : ℝ) * (2 * m0 : ℝ) ≤ (q : ℝ) * (ee * (n : ℝ)) :=
                      mul_le_mul_of_nonneg_left h2m0r (by positivity)
                    have hcast : ((q * (2 * m0) : ℕ) : ℝ) = (q : ℝ) * (2 * m0 : ℝ) := by
                      norm_num [Nat.cast_mul]
                    rwa [hcast]
                  exact add_le_add_right hqle (α * (n : ℝ) + 1)
            _ ≤ (α * (n : ℝ) + 1) + ((1 - α) / 4) * (n : ℝ) := by
                  exact add_le_add_right hqee (α * (n : ℝ) + 1)
            _ ≤ (n : ℝ) := by nlinarith [h1mαn]
        exact_mod_cast hr

      -- ============ FINAL ASSEMBLY ============
      let D : ℝ := sqrtDen N n
      have hDpos : 0 < D := by
        dsimp [D, sqrtDen]
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN1)
        have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1n)
        positivity
      have hD0 : 0 ≤ D := le_of_lt hDpos
      let T : ℕ → ℝ := fun j => max (16 * Rt) (th ^ j * Lr)
      let iLev : ℕ → ℕ := fun j => ℓ + min j q * (2 * m0)
      have hilev : ∀ j : ℕ, iLev j ≤ n := by
        intro j
        dsimp [iLev]
        have hmul : min j q * (2 * m0) ≤ q * (2 * m0) :=
          Nat.mul_le_mul_right (2 * m0) (min_le_right j q)
        exact le_trans (Nat.add_le_add_left hmul ℓ) hiq_le
      have hTq : T q = 16 * Rt := by
        dsimp [T]
        have hLr0 : 0 < Lr := by linarith
        have hθqL : th ^ q * Lr ≤ 1 := by
          calc
            th ^ q * Lr ≤ (1 / Lr) * Lr := mul_le_mul_of_nonneg_right hθq hLr0.le
            _ = 1 := by field_simp [ne_of_gt hLr0]
        have h16 : (1 : ℝ) ≤ 16 * Rt := by nlinarith [hRt1]
        exact max_eq_left (le_trans hθqL h16)
      let Pfun : ℕ → (Fin n → ℤ) → Prop := fun j x =>
        esup (lvl f p (iLev j) (pre x (iLev j) (hilev j))) ≤ T j / D
      let e2 : ℝ := Real.exp (-(2 * M) * (n : ℝ))
      have he2 : 0 ≤ e2 := by
        dsimp [e2]
        positivity
      have hilev0 : iLev 0 = ℓ := by
        dsimp [iLev]
        simp
      have hT0geLr : Lr ≤ T 0 := by
        dsimp [T]
        simpa using (le_max_right (16 * Rt) Lr)
      have hE0b : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun 0 x)) ≤ e2 * allAll A := by
        have hEv0 := hE0 n hnE0' N hN1 hNa A hAdm hrad hsym f hfpos hfsum hfmass
        let roughFilter : Finset (Fin n → ℤ) := (prodFinset n A).filter (fun x : Fin n → ℤ =>
          Lr / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))))
        have hb0 : fcard roughFilter ≤ Real.exp (-2 * M * (n : ℝ)) * allAll A := by
          dsimp [fcard, allAll]
          simpa [roughFilter, ℓ] using hEv0
        have hsub0 : (prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun 0 x) ⊆ roughFilter := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          dsimp [Pfun] at hx
          have heqsup : esup (lvl f p (iLev 0) (pre x (iLev 0) (hilev 0))) =
              esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))) := by
            exact esup_lvl_pre_congr_level (hk₁ := hilev 0) (hk₂ := ceil_alpha_le (n := n) hαlt) hilev0 x
          have hgt0 : ¬ (esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))) ≤ T 0 / D) := by
            rw [← heqsup]
            exact hx.2
          have hgt : T 0 / D < esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))) :=
            lt_of_not_ge hgt0
          have hgt1 : Lr / D < esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))) := by
            have hdiv : Lr / D ≤ T 0 / D := div_le_div_of_nonneg_right hT0geLr hD0
            exact lt_of_le_of_lt hdiv hgt
          have hgt2 : Lr / ((N : ℝ) * Real.sqrt (n : ℝ)) < esup (lvl f p ℓ (pre x ℓ (ceil_alpha_le (n := n) hαlt))) := by
            have hD : D = (N : ℝ) * Real.sqrt (n : ℝ) := by dsimp [D, sqrtDen]
            rw [hD] at hgt1
            exact hgt1
          exact ⟨hx.1, hgt2⟩
        calc
          fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun 0 x))
              ≤ fcard roughFilter := by
                dsimp [fcard]
                exact_mod_cast (Finset.card_le_card hsub0)
          _ ≤ Real.exp (-2 * M * (n : ℝ)) * allAll A := hb0
          _ ≤ e2 * allAll A := by
                have hE : Real.exp (-2 * M * (n : ℝ)) = e2 := by
                  dsimp [e2]
                  congr 1
                  ring
                rw [hE]
      have hblock : ∀ (j : ℕ), 1 ≤ j → j ≤ q →
          fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x)) ≤ e2 * allAll A := by
        intro j hj1 hjq
        let a : ℕ := iLev (j - 1)
        have hmin1 : min (j - 1) q = j - 1 := by
          apply min_eq_left
          omega
        have hmin2 : min j q = j := by
          apply min_eq_left
          exact hjq
        have hilev_step : iLev j = a + 2 * m0 := by
          dsimp [a]
          dsimp [iLev]
          rw [hmin1, hmin2]
          have hj1' : 1 ≤ j := hj1
          have hc : j * (2 * m0) = (j - 1) * (2 * m0) + 2 * m0 := by
            calc
              j * (2 * m0) = ((j - 1) + 1) * (2 * m0) := by rw [Nat.sub_add_cancel hj1']
              _ = (j - 1) * (2 * m0) + 1 * (2 * m0) := by rw [Nat.add_mul]
              _ = (j - 1) * (2 * m0) + 2 * m0 := by rw [one_mul]
          rw [hc]
          rw [← Nat.add_assoc]
        have hanj : a + 2 * m0 ≤ n := by
          rw [← hilev_step]
          exact hilev j
        have hkn : a ≤ n := le_trans (Nat.le_add_right a (2 * m0)) hanj
        have hℓa : ℓ ≤ a := by
          dsimp [a, iLev]
          rw [hmin1]
          exact Nat.le_add_right ℓ ((j - 1) * (2 * m0))
        -- mass slack parameters
        let δ₀ : ℝ := δ / 2
        have hδ₀ : 0 < δ₀ := by
          dsimp [δ₀]
          positivity
        have hδ₀leδ : δ₀ ≤ δ := by
          dsimp [δ₀]
          linarith
        have hδδ₀ : δ - δ₀ = δ / 2 := by
          dsimp [δ₀]
          ring
        have hslackδ : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ) := by
          rw [hδδ₀]
          exact hnslack
        have hkbiga : δ₀ * (n : ℝ) ≤ (a : ℝ) := by
          have hℓR : (n : ℝ) / 2 ≤ (ℓ : ℝ) := by
            have hcR : (n : ℝ) ≤ ((2 * ℓ : ℕ) : ℝ) := (Nat.cast_le.mpr hℓge)
            have h2 : ((2 * ℓ : ℕ) : ℝ) = 2 * (ℓ : ℝ) := by norm_num [Nat.cast_mul]
            have hcR' : (n : ℝ) ≤ 2 * (ℓ : ℝ) := by simpa [h2] using hcR
            nlinarith
          have hδhalf : δ₀ ≤ 1 / 2 := by
            dsimp [δ₀]
            linarith
          have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          have hd1 : δ₀ * (n : ℝ) ≤ (n : ℝ) / 2 := by nlinarith [hδhalf]
          have hℓaR : (ℓ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hℓa
          calc
            δ₀ * (n : ℝ) ≤ (n : ℝ) / 2 := hd1
            _ ≤ (ℓ : ℝ) := hℓR
            _ ≤ (a : ℝ) := hℓaR
        -- prefix window-mass bound
        have hMass : ∀ u : Fin a → ℤ,
            u ∈ prodFinset a (prefam (ℓ := a) A (le_trans (Nat.le_add_right a (2 * m0)) hanj)) →
            ∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ) := by
          intro u hu lo
          have hpre := kernel_window_mass_pre (hn1 := h1n) (k := a)
            (hkn := (le_trans (Nat.le_add_right a (2 * m0)) hanj)) (δ₀ := δ₀) hδ₀
            (hδ₀leδ := hδ₀leδ) (hkbig := hkbiga) (hslack := hslackδ) (N := N) hN1
            (p := p) hp₀ hp₁ (A := A) hAdm (f := f) hfpos hfsum hfmass (C₂ := C₂)
            hC₂pos (hC₂ := hC₂body) (u := u) hu lo
          have hRt : C₂ / Real.sqrt (δ₀ * (p : ℝ)) ≤ Rt := by
            dsimp [Rt, δ₀]
            exact le_max_right 1 (C₂ / Real.sqrt ((δ / 2) * (p : ℝ)))
          have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h1n)
          have hbnd : C₂ / Real.sqrt (δ₀ * (p : ℝ)) / Real.sqrt (n : ℝ) ≤
              Rt / Real.sqrt (n : ℝ) := by
            exact div_le_div_of_nonneg_right hRt hsqrtn.le
          exact le_trans hpre hbnd
        -- interval data for this block
        rcases exists_block_intervals (hδ₁₂ := hδ₁₂) (hℓge := hℓge) (hℓa := hℓa) (han := hanj)
            (hN1 := hN1) (hAdm := hAdm) with ⟨c, d, loS, hiS, hint1, hint2, hJlen, hSlen⟩
        -- export body: hExp (pass-through of the fixed-n export)
        have hNpow : (N : ℝ) ≤ (2 : ℝ) ^ n := by
          have ha : 0 < 1 - (p : ℝ) + ε := by linarith
          have h1le2 : 1 / (1 - (p : ℝ) + ε) ≤ 2 := by
            rw [div_le_iff₀ ha]
            nlinarith
          calc
            (N : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n := hNa
            _ ≤ (2 : ℝ) ^ n := by
                  apply pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (1 - (p : ℝ) + ε)) h1le2
        have hL16j : 16 * Rt ≤ T (j - 1) := by
          dsimp [T]
          exact le_max_left _ _
        have hLL0j : T (j - 1) ≤ L0exp := by
          dsimp [T, L0exp]
          have hpow : th ^ (j - 1) ≤ 1 := pow_le_one₀ hth0.le hth1.le
          have hLr0 : 0 ≤ Lr := by linarith
          have hLr : th ^ (j - 1) * Lr ≤ Lr := by
            nlinarith
          exact max_le_max le_rfl hLr
        have hLθj : th * T (j - 1) ≤ T j := by
          dsimp [T]
          by_cases h : th ^ (j - 1) * Lr ≤ 16 * Rt
          · rw [max_eq_left h]
            have h1 : th * (16 * Rt) ≤ 16 * Rt := by nlinarith [hth1]
            exact le_trans h1 (le_max_left (16 * Rt) (th ^ j * Lr))
          · have hl : 16 * Rt ≤ th ^ (j - 1) * Lr := le_of_lt (lt_of_not_ge h)
            rw [max_eq_right hl]
            have h1 : th * th ^ (j - 1) = th ^ j := by
              rw [mul_comm]
              rw [← pow_succ]
              congr 1
              omega
            have hstep : th * (th ^ (j - 1) * Lr) = th ^ j * Lr := by
              calc
                th * (th ^ (j - 1) * Lr) = (th * th ^ (j - 1)) * Lr := by ring
                _ = th ^ j * Lr := by rw [h1]
            rw [hstep]
            exact le_max_right (16 * Rt) (th ^ j * Lr)
        -- hExp: per-kernel export bound via the fixed-n export body
        have hExp : ∀ {u : Fin a → ℤ}, (∀ t : ℤ, 0 ≤ lvl f p a u t) →
            (Summable (fun t : ℤ => (lvl f p a u t) ^ 2)) → (Summable (lvl f p a u)) →
            Submission.Ell2Update.ratioLip eta (lvl f p a u) →
            (∀ lo : ℤ, (∑ t ∈ I0 lo N, lvl f p a u t) ≤ Rt / Real.sqrt (n : ℝ)) →
            norm₁ (lvl f p a u) ≤ 1 →
            (∀ t : ℤ, lvl f p a u t ≤ T (j - 1) / sqrtDen N n) →
            ((((prodFinset m0 (fun jj : Fin m0 => Finset.Icc (c jj) (d jj))).product
                (prodFinset m0 (fun jj : Fin m0 => Finset.Icc (loS jj) (hiS jj)))).filter
              (fun pz : (Fin m0 → ℤ) × (Fin m0 → ℤ) =>
                th * T (j - 1) / sqrtDen N n <
                  esup (lvl (lvl f p a u) p (2 * m0) (pre (catTwo pz) (2 * m0) (le_refl (2 * m0)))))).card : ℝ) ≤
              e2 * (∏ jj : Fin m0, ((((Finset.Icc (c jj) (d jj)).card : ℕ) : ℝ))) *
                (∏ jj : Fin m0, ((((Finset.Icc (loS jj) (hiS jj)).card : ℕ) : ℝ))) := by
          intro u hgpos hg2 hgsum hgLip hgMass hgNorm hgSup
          have hsup' : ∀ t : ℤ, lvl f p a u t ≤ T (j - 1) / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
            intro t
            simpa [sqrtDen] using hgSup t
          have hb := hRef n hnRef' N hN1 hNpow (L := T (j - 1)) hL16j hLL0j (m := m0) (by rfl)
            (f := lvl f p a u) hgpos hg2 hgsum (hlip := hgLip) (hmass := hgMass)
            (hnorm1 := hgNorm) (hfsupL := hsup') (c := c) (d := d) hJlen (loS := loS) (hiS := hiS) hSlen
          have hthr : th * T (j - 1) / sqrtDen N n =
              (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * (T (j - 1) / (2 * sqrtDen N n)) := by
            dsimp [th, sqrtDen]
            ring
          let F1 : Finset ((Fin m0 → ℤ) × (Fin m0 → ℤ)) :=
            ((prodFinset m0 (fun jj : Fin m0 => Finset.Icc (c jj) (d jj))).product
              (prodFinset m0 (fun jj : Fin m0 => Finset.Icc (loS jj) (hiS jj)))).filter
                (fun pz : (Fin m0 → ℤ) × (Fin m0 → ℤ) =>
                  th * T (j - 1) / sqrtDen N n <
                    esup (lvl (lvl f p a u) p (2 * m0) (pre (catTwo pz) (2 * m0) (le_refl (2 * m0)))))
          let F2 : Finset ((Fin m0 → ℤ) × (Fin m0 → ℤ)) :=
            ((prodFinset m0 (fun jj : Fin m0 => Finset.Icc (c jj) (d jj))).product
              (prodFinset m0 (fun jj : Fin m0 => Finset.Icc (loS jj) (hiS jj)))).filter
                (fun pz : (Fin m0 → ℤ) × (Fin m0 → ℤ) =>
                  (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) * (T (j - 1) / (2 * sqrtDen N n)) <
                    esup (lvl (lvl f p a u) p (2 * m0) (pre (catTwo pz) (2 * m0) (le_refl (2 * m0)))))
          have hsub12 : F1 ⊆ F2 := by
            intro pz hpz
            rw [Finset.mem_filter] at hpz ⊢
            refine ⟨hpz.1, ?_⟩
            rw [hthr] at hpz
            exact hpz.2
          have hsub21 : F2 ⊆ F1 := by
            intro pz hpz
            rw [Finset.mem_filter] at hpz ⊢
            refine ⟨hpz.1, ?_⟩
            rw [← hthr] at hpz
            exact hpz.2
          have hb' : fcard F1 ≤ e2 * (∏ jj : Fin m0, ((((Finset.Icc (c jj) (d jj)).card : ℕ) : ℝ))) *
                (∏ jj : Fin m0, ((((Finset.Icc (loS jj) (hiS jj)).card : ℕ) : ℝ))) := by
            dsimp [fcard]
            calc
              ((F1).card : ℝ) ≤ ((F2).card : ℝ) := by
                exact_mod_cast (Finset.card_le_card hsub12)
              _ ≤ e2 * (∏ jj : Fin m0, ((((Finset.Icc (c jj) (d jj)).card : ℕ) : ℝ))) *
                (∏ jj : Fin m0, ((((Finset.Icc (loS jj) (hiS jj)).card : ℕ) : ℝ))) := by
                dsimp [F2, e2]
                exact hb
          exact hb'
        -- assemble the per-block bound via block_bound_export
        have hbb := block_bound_export (hn1 := h1n) (han := hanj) (f := f) (p := p) hp₀ hp₁
          hfpos hf2 hfsum (μm := eta) hlip hfmass (N := N) hN1 (A := A)
          (Lp := T (j - 1)) (θ := th) (Lc := T j) hLθj (e2 := e2) he2 (Rt := Rt)
          (hMass := hMass) (c := c) (d := d) (loS := loS) (hiS := hiS) hint1 hint2 hJlen hSlen
          (hExp := hExp)
        have hev : (prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x)
            = (prodFinset n A).filter (fun x : Fin n → ℤ =>
                esup (lvl f p a (pre x a (le_trans (Nat.le_add_right a (2 * m0)) hanj))) ≤ T (j - 1) / sqrtDen N n ∧
                T j / sqrtDen N n < esup (lvl f p (a + 2 * m0) (pre x (a + 2 * m0) hanj))) := by
          apply Finset.filter_congr
          intro x hx
          constructor
          · intro hP
            rcases hP with ⟨hA, hB⟩
            have heq1 : esup (lvl f p (iLev (j - 1)) (pre x (iLev (j - 1)) (hilev (j - 1)))) =
                esup (lvl f p a (pre x a (le_trans (Nat.le_add_right a (2 * m0)) hanj))) := by
              dsimp [a]
            have heq2 : esup (lvl f p (iLev j) (pre x (iLev j) (hilev j))) =
                esup (lvl f p (a + 2 * m0) (pre x (a + 2 * m0) hanj)) := by
              exact esup_lvl_pre_congr_level (hk₁ := hilev j) (hk₂ := hanj) hilev_step x
            dsimp [Pfun] at hA hB
            constructor
            · rw [heq1] at hA
              exact hA
            · have hbig : T j / D < esup (lvl f p (iLev j) (pre x (iLev j) (hilev j))) := lt_of_not_ge hB
              rw [heq2] at hbig
              exact hbig
          · intro hB
            rcases hB with ⟨hA, hbig⟩
            have heq1 : esup (lvl f p (iLev (j - 1)) (pre x (iLev (j - 1)) (hilev (j - 1)))) =
                esup (lvl f p a (pre x a (le_trans (Nat.le_add_right a (2 * m0)) hanj))) := by
              dsimp [a]
            have heq2 : esup (lvl f p (iLev j) (pre x (iLev j) (hilev j))) =
                esup (lvl f p (a + 2 * m0) (pre x (a + 2 * m0) hanj)) := by
              exact esup_lvl_pre_congr_level (hk₁ := hilev j) (hk₂ := hanj) hilev_step x
            constructor
            · dsimp [Pfun]
              rw [← heq1] at hA
              exact hA
            · dsimp [Pfun]
              have hbig' : T j / D < esup (lvl f p (iLev j) (pre x (iLev j) (hilev j))) := by
                rw [← heq2] at hbig
                exact hbig
              exact not_le_of_gt hbig'
        have hbb' : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x))
            ≤ e2 * allAll A := by
          rw [hev]
          exact hbb
        exact hbb'

      have hsub : (prodFinset n A).filter (fun x : Fin n → ℤ => (16 * Rt) / D < esup (lvl f p n x))
          ⊆ (prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hgt := hx.2
        have hdec := esup_lvl_decreasing (f := f) (p := p) (s := n) (k := iLev q) (hilev q) x hfpos hfsum
        have hgt2 : (16 * Rt) / D < esup (lvl f p (iLev q) (pre x (iLev q) (hilev q))) :=
          lt_of_lt_of_le hgt hdec
        dsimp [Pfun]
        rw [hTq]
        exact not_le_of_gt hgt2
      have hcard_sub : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => (16 * Rt) / D < esup (lvl f p n x)))
          ≤ fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x)) := by
        dsimp [fcard]
        exact_mod_cast (Finset.card_le_card hsub)
      have hff := first_failure_card_le (X := prodFinset n A) (Q := q) (P := Pfun)
      have hblockb : ∀ j : ℕ, j ∈ Finset.Icc 1 q →
          fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x)) ≤ e2 * allAll A := by
        intro j hj
        exact hblock j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      have hall0 : 0 ≤ allAll A := by
        dsimp [allAll]
        apply Finset.prod_nonneg
        intro j hj
        exact_mod_cast (Nat.zero_le _)
      have hprod0 : 0 ≤ e2 * allAll A := mul_nonneg he2 hall0
      have hsum : (∑ j ∈ Finset.Icc 1 q,
            fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x)))
          ≤ ((Finset.Icc 1 q).card : ℝ) * (e2 * allAll A) := by
        calc
          (∑ j ∈ Finset.Icc 1 q,
              fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x)))
              ≤ ∑ j ∈ Finset.Icc 1 q, (e2 * allAll A) := by
                exact Finset.sum_le_sum hblockb
          _ = ((Finset.Icc 1 q).card : ℝ) * (e2 * allAll A) := by
                rw [Finset.sum_const]
                rw [nsmul_eq_mul]
      have hmain : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x))
          ≤ ((((Finset.Icc 1 q).card : ℕ) : ℝ) + 1) * (e2 * allAll A) := by
        calc
          fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x))
              ≤ fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun 0 x)) +
                  (∑ j ∈ Finset.Icc 1 q,
                    fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x))) := by
                dsimp [fcard]
                exact hff
          _ ≤ e2 * allAll A +
                  (∑ j ∈ Finset.Icc 1 q,
                    fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => Pfun (j - 1) x ∧ ¬ Pfun j x))) := by
                exact add_le_add_left hE0b _
          _ ≤ e2 * allAll A + (((Finset.Icc 1 q).card : ℝ) * (e2 * allAll A)) := by
                exact add_le_add_right hsum (e2 * allAll A)
          _ = ((((Finset.Icc 1 q).card : ℕ) : ℝ) + 1) * (e2 * allAll A) := by ring
      have hcard1q : ((Finset.Icc 1 q).card : ℕ) = q := by
        simp
      have hmain' : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x))
          ≤ ((q : ℝ) + 1) * (e2 * allAll A) := by
        have hc := hmain
        rw [hcard1q] at hc
        norm_num at hc
        exact hc
      have habsorb : ((q : ℝ) + 1) * (e2 * allAll A) ≤ Real.exp (-M * (n : ℝ)) * allAll A := by
        have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
        have hnq : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnq'
        have hq1 : (q : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
        have hn1exp : (n : ℝ) + 1 ≤ Real.exp (n : ℝ) := by
          simpa using (Real.add_one_le_exp (n : ℝ))
        have hqexp : (q : ℝ) + 1 ≤ Real.exp (n : ℝ) := le_trans hq1 hn1exp
        have hnle : (n : ℝ) ≤ M * (n : ℝ) := by
          have hMn : (1 : ℝ) ≤ M := hM
          have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          nlinarith
        have hexpmono : Real.exp (n : ℝ) ≤ Real.exp (M * (n : ℝ)) := Real.exp_le_exp.mpr hnle
        have hqexpM : (q : ℝ) + 1 ≤ Real.exp (M * (n : ℝ)) := le_trans hqexp hexpmono
        have hpos3 : 0 ≤ Real.exp (-M * (n : ℝ)) := (Real.exp_pos _).le
        have hlin : ((q : ℝ) + 1) * e2 ≤ Real.exp (-M * (n : ℝ)) := by
          dsimp [e2]
          have hsplit : Real.exp (-(2 * M) * (n : ℝ)) =
              Real.exp (-M * (n : ℝ)) * Real.exp (-M * (n : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            ((q : ℝ) + 1) * Real.exp (-(2 * M) * (n : ℝ))
                = (((q : ℝ) + 1) * Real.exp (-M * (n : ℝ))) * Real.exp (-M * (n : ℝ)) := by
                    rw [hsplit]
                    ring
            _ ≤ (Real.exp (M * (n : ℝ)) * Real.exp (-M * (n : ℝ))) *
                  Real.exp (-M * (n : ℝ)) := by
                  have h1 : ((q : ℝ) + 1) * Real.exp (-M * (n : ℝ))
                      ≤ Real.exp (M * (n : ℝ)) * Real.exp (-M * (n : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hqexpM hpos3
                  exact mul_le_mul_of_nonneg_right h1 hpos3
            _ = Real.exp (-M * (n : ℝ)) := by
                  have hcancel : Real.exp (M * (n : ℝ)) * Real.exp (-M * (n : ℝ)) = 1 := by
                    rw [← Real.exp_add]
                    have h0 : M * (n : ℝ) + -M * (n : ℝ) = 0 := by ring
                    rw [h0]
                    simp
                  rw [hcancel]
                  simp
        calc
          ((q : ℝ) + 1) * (e2 * allAll A) = (((q : ℝ) + 1) * e2) * allAll A := by ring
          _ ≤ (Real.exp (-M * (n : ℝ))) * allAll A := mul_le_mul_of_nonneg_right hlin hall0
      have hfinal : fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => (16 * Rt) / D < esup (lvl f p n x)))
          ≤ Real.exp (-M * (n : ℝ)) * allAll A := by
        calc
          fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => (16 * Rt) / D < esup (lvl f p n x)))
              ≤ fcard ((prodFinset n A).filter (fun x : Fin n → ℤ => ¬ Pfun q x)) := hcard_sub
          _ ≤ ((q : ℝ) + 1) * (e2 * allAll A) := hmain'
          _ ≤ Real.exp (-M * (n : ℝ)) * allAll A := habsorb
      simpa [D, sqrtDen, fcard, allAll] using hfinal


end Submission.Averaging
