import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsTPrime
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiDeep2
import Submission.MultiFrag1

/-!
# TASK (child): prove `Submission.Multi.MSys.nb_le_tM` (multiset obs.T') below.
All other gaps in this file are helper lemmas YOU must also prove (no gaps may remain).

## Goal: the multiset analogue of Submission/ObsTPrime.lean's theorem_obsTp.
READ FIRST (in this order): Submission/ObsTPrime.lean (the PROVEN single-draw proof you port),
Submission/MultiFrag1.lean and Submission/MultiDeep2.lean (the multiset fragment API),
Submission/MultiDeep.lean (multiset level counts/weights), Submission/Multi.lean (multiset ops).
ALL of those compile.  Your file compiles iff your port is right.

## Translation dictionary (set world -> multiset world)
- `(A ∩ N.levelSet S' j).ncard`  ->  `N.countAt S' A j`  (a ℕ; count with multiplicity of
  level-j occurrences of S' inside A: Σ_x if lv S' x = j then min (A x) (S' x) else 0).
- `N.levelSet S' j` elements  ->  level-j occurrences; `x ∈ levelSet S' j` ~ "x at level j with
  S' x > 0".  Sets W,U,S' become multisets `X → ℕ`; `∈` becomes multiplicity `> 0` per coordinate.
- union `W ∪ U` of multisets -> `addM W U` (pointwise +); difference/truncation `subMM`;
  min-intersection `minM`.
- `N.sCount S' j` (count)  ->  `N.sCount S' j` ALREADY counts multiplicity (Σ_x if lv=j then S' x).
- `N.unionBelow S' c`  ->  `N.prefixM S' c` (prefix multiset).
- `N.weightAbove S' A b`  ->  `N.weightAboveM S' A b` (level b+1..τ, real, countAt·wlev j);
  `N.weight S' A` -> `N.weightM S' A` (levels 0..τ); `N.totalWeight S'` -> `N.totalWeightM S'`.
- Fragments: set-world `N.IsFragment S W U b S'` -> `N.IsFragmentM S W U b S'`; note the multiset
  IsFragmentM ALREADY requires `subM U (subMM S W)` (U ⊆ S∖W).  A "minimum fragment" is
  `N.MinFragmentAtM S W U b hS hB`; the chosen witness S' is available via `N.IsFragmentM`.
- Badness: `N.BadM ((10:ℝ)^10)⁻¹ W` means `N.procValM W < ((10:ℝ)^10)⁻¹` where
  `procValM W = mSup (fun S => weightM S W) N`; use `le_mSup (v := fun T => N.weightM T W) N hS'F`
  to bound any member's weight above by procValM.
- `T' := N.unionBelow S' c ∩ U` (set world) becomes `N.lowLevel S' c U` defined below =
  fun x => if N.lv S' x ≤ c then U x else 0   (U restricted to levels ≤ c).

## KEY multiset facts already proved (use them; do NOT reprove):
from Submission/MultiFrag1.lean (namespace Submission.Multi.MSys):
- `N.minFragM_subM_sdiff_of_witness S W U b hS hB hmin hfr : subM U (subMM S' W)`
- `N.obsMaxM ... : W x < S' x` when `0 < U x`
- `N.level_le_b_of_minFragM ... : N.lv S' x ≤ b` when `0 < U x`
- `N.minFragM_subM_prefixM ... : subM U (N.prefixM S' b)`
- `N.obsTM S W U b hS hB hmin hfr : subMM (N.prefixM S' b) W = U`   [function equality!]
- `N.t_le_nbM ... : sizeM U ≤ N.prefixCount S b`
from MultiDeep/MultiDeep2/Multi.lean: countAt_le_sCount, countAt_eq_sizeM_minM,
  sizeM_prefixM, prefixM_pointwise, prefixM_subM, subM_prefixM_iff, weightAboveM_mono,
  prefixCount_eq_of_FPartial, IsFragmentM accessors (IsFragmentM_wit/_subM/_levM/_weight),
  eraseOne lemmas etc. as needed.

## PURE REAL lemmas you may reuse VERBATIM from namespace ObsTPrime (file imports it):
ObsTPrime.abel_identity b d; ObsTPrime.exists_neg_tail b d hneg;
ObsTPrime.sum_Icc_split / sum_Icc_split_at / sum_range_split c b h f;
ObsTPrime.sum_range_eq_sum_Icc0 b f; ObsTPrime.wlev_mul_pow j; ObsTPrime.wlev_bound b j hj;
ObsTPrime.wlev_succ_hundred b; ObsTPrime.frag2_aux (pure algebra); ObsTPrime.u_diff;
ObsTPrime.coef_tel; ObsTPrime.sum_Icc1_eq_range_pred.
(These are PROVEN; use unqualified after `open ObsTPrime`.)

## THEOREM TO PROVE (final, keep exact name/signature):
  theorem nb_le_tM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
      (hB : N.LevelBounded) (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeightM T)
      (hbad : N.BadM ((10 : ℝ) ^ 10)⁻¹ W) (hmin : N.MinFragmentAtM S W U b hS hB)
      {S' : X → ℕ} (hfr : N.IsFragmentM S W U b S') :
      (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ (sizeM U : ℝ)

## PROOF SKETCH (port ObsTPrime.theorem_obsTp lines 778-1375 mechanically):
let sCnt j : ℝ := (N.sCount S' j : ℝ); let uCnt j : ℝ := (N.countAt S' U j : ℝ).
Have hS'F, hprof (∀j≤b, sCount S j = sCount S' j) from hfr.1; hfrag1 := hfr.2.2.1
(∀ j≤b, subM (levM S' j) (addM W U)); hfr2 := hfr.2.2.2 (the fragment2 weight inequality).
hbτ: b ≤ N.τ (min-index ≤ τ: minIndexM ≤ τ since S∖W is a fragment at τ: use
N.minIndexM_min with the sdiff witness; hmin.1: b = MinIndexM).
hs_count : Σ_{j ∈ range(b+1)} sCnt j = (prefixCount S b : ℝ)   [rw prefixCount, Nat.cast_sum,
  use hprof; note prefixCount sums sCount S j and sCount S' j = sCount S j for j ≤ b]
ht_count : Σ_{j ∈ range(b+1)} uCnt j = (sizeM U : ℝ)
  [use: (a) subM U S' via subM_trans (minFragM_subM_sdiff_of_witness ...) (subM_subMM_of_subM ...);
   (b) hlevel: ∀ x, 0 < U x → N.lv S' x ≤ b = level_le_b_of_minFragM;
   then sizeM U = Σ_x U x = Σ_x U x · [lv ≤ b] = Σ_{j ≤ b} (countAt S' U j): prove as a ℝ
   equality mirroring sizeM_lowLevel with c := b (apply sizeM_lowLevel with U, S', b when the
   lowLevel = U pointwise because levels of U are ≤ b: prove N.lowLevel S' b U = U by funext x;
   by_cases on 0 < U x and level_le_b).]
hs_nonneg / hu_le_s: 0 ≤ sCnt j; uCnt j ≤ sCnt j (countAt_le_sCount).
by_contra hnot; htlt : (sizeM U : ℝ) < (9/10)·(prefixCount S b : ℝ).
hC : Σ_{range(b+1)} (uCnt j − (9/10)·sCnt j) < 0   [sum_sub_distrib, ← sum_mul, linarith].
hsumneg: Σ 100^j·(wlev j·(uCnt j − .9 sCnt j)) < 0  [per-j: 100^j·(wlev j·x) = x via wlev_mul_pow].
rcases ObsTPrime.exists_neg_tail b (fun j => wlev j·(uCnt j − (9/10)·sCnt j)) hsumneg
  with ⟨b', hb'le, hneg_b'⟩   (hneg_b' : Σ_{j∈Icc b' b} wlev j·(uCnt j − (9/10)·sCnt j) < 0)
by_cases hb'pos : 0 < b'
CASE b' ≥ 1:
  let c : ℕ := b' − 1  (hc1 : c+1 = b'; hcle : c ≤ b; hc_lt : c < b)
  let T' : X → ℕ := N.lowLevel S' c U; let tT : ℝ := (sizeM T' : ℝ)
  let Gb : ℝ := Σ_{j∈Icc b' b} sCnt j * wlev j; let Sc : ℝ := Σ_{j∈Icc b' b} sCnt j
  let nB : ℝ := (prefixCount S b : ℝ); let nC : ℝ := (prefixCount S c : ℝ); tU := (sizeM U : ℝ)
  sublemmas (mirror lines ~1000-1180):
   - subM T' U (lowLevel_subM_U), subM T' S' (lowLevel_subM_S' with U⊆S'), subM T' (subMM S W)
     (T' ⊆ U ⊆ S∖W: use lowLevel_subM_U and hfr.2.1 or minFragM_subM_sdiff; the W-U-disjointness
      needed only to justify countAt identities: instead prove per-level countAt identities using
      obsTM as below).
   - htT_count : (sizeM T' : ℝ) = Σ_{j∈range(c+1)} uCnt j  := sizeM_lowLevel N S' U c hUS'
   - htT_le_tU : tT ≤ tU; htT_le_nC : tT ≤ nC [each uCnt j ≤ sCnt j and hnc_count]
   - hnB : nB = nC + Sc  [sum_range_split c b (by omega) sCnt; rewrite Icc (c+1) b = Icc b' b]
   - hWcount : ∀ j ∈ Icc b' b, (N.countAt S' W j : ℝ) = sCnt j − uCnt j
       := from countAt_W_eq_sCount_sub_u N S W U b hS hB hmin hfr (j:=j) hjb  [Nat eq → cast];
        (you must PROVE countAt_W_eq_sCount_sub_u below — its outline is there)
   - hWb_ge : (1/10)·Gb ≤ Σ_{j∈Icc b' b} wlev j·(countAt S' W j : ℝ)
       [mirror lines 995-1030: rewrite countAt W j = sCnt−uCnt; from hneg_b' get
        Σ wlev·uCnt·wlev < (9/10)·Σ sCnt·wlev via the heq/heq2 real-sum algebra (use
        Finset.sum_sub_distrib and ← Finset.mul_sum); nlinarith]
   - weight splits (mirror lines 1040-1130 with countAt, NO disjointness lemmas needed since
     T' has NO occurrences at levels ≥ b' (countAt_lowLevel_zero) and U has NO occurrences at
     levels ≥ b+1 (level_le_b_of_minFragM)):
       hWAc : weightAboveM S' S' c = Gb + weightAboveM S' S' b
          [weightAboveM S' A c = Σ_{j∈Icc (c+1) τ} countAt S' A j·wlev j; split at b via
           ObsTPrime.sum_Icc_split_at (a:=b')(b:=b)(c:=N.τ) hb'le hbτ applied to a function of j;
           countAt S' S' j = sCount S' j (sCount_eq_countAt_self) → real casts]
       hWA_eq : weightAboveM S' (addM W T') c =
           Σ_{j∈Icc b' b} (countAt S' W j : ℝ) * wlev j + weightAboveM S' (addM W U) b
          [split the LHS at b as above; for j ∈ Icc b' b: countAt S' (W+T') j = countAt S' W j
           since T' has no level-j occurrences (countAt_lowLevel_zero c < j when j ≥ b' > c:
           use countAt_lowLevel_zero with h : c < j and the fact min with addM: prove
           countAt_addM_left_zero: if countAt S' A j = 0 then countAt S' (addM W A) j =
           countAt S' W j — additive: countAt S' (addM W A) j = countAt S' W j + countAt S' A j
           (summands are min(Wx + Ax, S'x) = min(Wx,S'x)+min(Ax,S'x) when min(Wx,Ax)=0?? NOT in
           general — INSTEAD use the per-coordinate fact T' x = 0 at levels ≥ b' directly via
           countAt_lowLevel_zero + a lemma: countAt of addM W A when A has no occurrence at level
           j: prove `countAt_addM_eq_of_zero` below: countAt S' (addM W A) j = countAt S' W j
           given ∀ x, lv S' x = j → A x = 0  (so W+A = W at those x)].
           For the top part (j ≥ b+1): countAt S' (addM W T') j = countAt S' (addM W U) j
           since BOTH T' and U have no occurrences at level j (T': c < j; U: level_le_b ⇒ U x=0
           for lv x = j > b): use the same zero-lemma twice.]
   - hG1 : (1/100)·wlev b·Sc ≤ (9/100)·Gb  [per j ∈ Icc b' b: (1/100)·wlev b ≤ (9/100)·wlev j
       via wlev_bound (see ObsTPrime hG1); mul_le_mul_of_nonneg_right with sCnt nonneg; sum]
   - hnew2 (fragment2 inequality for T' at c):
       weightAboveM S' (addM W T') c ≥ (100)⁻¹·(weightAboveM S' S' c − wlev c·(nC − tT))
       [mirror lines ~1115-1160: hchain1: (1/10)Gb + (100)⁻¹·(weightAbove S'S' b − wlev b·(nB−tU))
        ≤ weightAboveM S' (addM W T') c via hWb_ge and hfr2 (rw [hWA_eq], add_le_add);
        hD ≥ 0 := frag2_aux Gb Sc nB tU nC tT (wlev b) (wlev c) hG1 hnB (wlev_nonneg b)
          htT_le_tU htT_le_nC (wlev_le_of_le hcle);
        hdiff real identity (rw [hWAc]; ring_nf after (100)⁻¹ = 1/100);
        hBleA via sub_nonneg; exact le_trans hBleA hchain1]
   - fragment: IsFragmentM S W T' c S':
       witness ∈ FPartialM S c (hfr.1 + profile downshift);
       subM T' (subMM S W) [T' ⊆ U and U ⊆ S∖W];  ← NOTE: IsFragmentM's second field;
       fragment1: ∀ j ≤ c, subM (levM S' j) (addM W T')  [pointwise: x at level j ≤ c < b:
         levM S' j x ≤ Wx + Ux from hfrag1 j (by omega); and T' x = U x since lv x = j ≤ c
         (lowLevel_self_of_lv_le)];  weight := hnew2
   - contradiction: minIndexM_min N S W hS hB T' S' hTfrag : MinIndexM ≤ c; with hmin.1
     (b = MinIndexM) and c < b: omega.
CASE b' = 0:
  let G0 := Σ_{j∈Icc 0 b} sCnt j·wlev j; S0 := Σ sCnt j over Icc 0 b; tU := (sizeM U:ℝ);
  nB := (prefixCount S b : ℝ).
  - hneg0 := hneg_b' after rw [hb'0] (simpa [hb'0])
  - hW0_ge : (1/10)·G0 ≤ Σ_{Icc 0 b} wlev j·(countAt S' W j : ℝ)  [as hWb_ge with Icc 0 b]
  - weightM S' W = (Σ_{Icc 0 b} wlev j·(countAt S' W j : ℝ)) + weightAboveM S' W b
      [split weightM at b via ObsTPrime.sum_Icc_split_at (a:=0)(b:=b)(c:=N.τ) (by omega) hbτ on
       countAt terms: weightM S' A = Σ_{j∈range(τ+1)} ... = Σ_{Icc 0 τ} ... (sum_range_eq_sum_Icc0)
       then split; the middle and top parts: countAt S' W j for top (j ≥ b+1) equals
       countAt S' (addM W U) j because U has no occurrences at level ≥ b+1 (level_le_b) → use
       countAt_addM_eq_of_zero]
  - weightM S' S' = G0 + weightAboveM S' S' b   [countAt S' S' j = sCount S' j; G0]
  - hlow : (1/100)·weightM S' S' ≤ weightM S' W
      [mirror lines ~1240-1330: hfr2 gives (100)⁻¹·(weightAboveM S'S' b − wlev b·(nB−tU)) ≤
       weightAboveM S' (addM W U) b = weightAboveM S' W b (U zero high: countAt_addM_eq_of_zero);
       add with hW0_ge; then hD0 : 0 ≤ (9/100)G0 − (1/100)wlev b·(nB − tU) with nB ≤ S0
       (nB = Σ_{Icc 0 b} sCnt via sum_range_eq_sum_Icc0; tU ≥ 0), hG0_le (as hG1), linarith;
       final sub_nonneg identity as in ObsTPrime hdiff0/hchain]
  - contradiction: weightM S' W ≤ procValM W := le_mSup (v := fun T => N.weightM T W) N hS'F
    (S' ∈ N.F via hfr); hbad: procValM W < (10^10)⁻¹; hTot S' hS'F : (10^8)⁻¹ ≤ weightM S' S';
    and ((10:ℝ)^10)⁻¹ = (1/100)·((10:ℝ)^8)⁻¹ (pow algebra, field_simp) →
    (10^10)⁻¹ ≤ (1/100)·weightM S' S' ≤ weightM S' W ≤ procValM W < (10^10)⁻¹: linarith.
That completes nb_le_tM.

## HELPER LEMMAS YOU MUST ALSO PROVE (given below with their statements; no sorries at the end):
- countAt_eq_sum_lv (multiset counts: with U ⊆ S' the countAt is a plain level sum)
- countAt_addM_eq_of_zero : if ∀ x, lv S' x = j → A x = 0 then
      N.countAt S' (addM W A) j = N.countAt S' W j
  [unfold countAt/addM; by_cases lv = j per x: in the pos case A x = 0 so W x + 0 = W x]
- lowLevel basics (subM_U, self_of_lv_le, eq_zero_of_lv_gt, subM_S'), sizeM_lowLevel,
  countAt_lowLevel, countAt_lowLevel_zero  (statements in the file; the sizeM_lowLevel proof
  needs care with ℝ casts: use `Nat.cast_sum` and pointwise `apply Finset.sum_congr rfl` steps;
  a clean route: prove a Nat-level identity first:
    sizeM (lowLevel S' c U) = ∑ j ∈ range(c+1), countAt S' U j  [Nat]
  (by unfolding sizeM/countAt and double-sum reordering with the collapse
   Σ_{j∈range(c+1)} [lv x = j] = [lv x ≤ c], proved by Finset.sum_ite_eq and by_cases),
  then cast to ℝ (Nat.cast_sum).)
- countAt_W_eq_sCount_sub_u : for a MINIMUM fragment (hmin at index b) with witness S'
  (hfr), j ≤ b ⇒ N.countAt S' W j = N.sCount S' j − N.countAt S' U j
  [pointwise per x at level j: from N.obsTM (subMM (prefixM S' b) W = U) get U x = S' x − W x
   (prefixM S' b x = S' x at level j ≤ b via prefixM_pointwise);
   then min (W x) (S' x) = S' x − U x (Nat identity: by_cases S' x ≤ W x <;> simp/omega);
   sum over x and use Finset.sum_sub_distrib over ℕ carefully: prove the equality of ℕ sums by
   `apply le_antisymm` with two Finset.sum_le_sum steps where the pointwise term inequality
   min(W,S') ≤ S' − U is derived and the other inequality S'−U ≤ min(W,S') likewise
   (so each summand is EQUAL pointwise; do sum_congr with the pointwise equality), then
   `simp`-style with the sum of differences: you may use
   (∑ x, (S' x − U x)) = (∑ x, S' x) − (∑ x, U x) — prove via Nat casts to ℝ then cast back,
   or prove with `Finset.sum_sub_distrib` on ℤ, or provide a small helper:
   lemma sum_sub_nat {f g : X → ℕ} (h : ∀ x, g x ≤ f x) :
      (∑ x, (f x − g x)) = (∑ x, f x) − (∑ x, g x) := by
        apply Nat.cast_injective (R := ℤ)  -- or: rw [← Nat.cast_sub ...] etc.
   (feel free to use exact_mod_cast / omega at the ℕ level after establishing the pointwise
   summand equalities).  SIMPLER: prove the ℝ version
      (N.countAt S' W j : ℝ) = (sCnt-style difference)
   directly by per-x congr: (min (W x)(S' x) : ℝ) = (S' x : ℝ) − (U x : ℝ) then Nat.cast_sum.]
You may add any additional helper lemmas.  Do NOT import Mathlib wholesale
(keep the imports at the top of this file exactly).  Keep the final theorem name and signature
`nb_le_tM`; put it at the end of namespace Submission.Multi.MSys.  No gaps, no axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep
open ObsTPrime

variable {X : Type*} [Fintype X]

namespace MSys

/-- level ≤ c part of U (levels measured by S') -/
def lowLevel (N : MSys X) (S' : X → ℕ) (c : ℕ) (U : X → ℕ) : X → ℕ :=
  fun x => if N.lv S' x ≤ c then U x else 0

lemma lowLevel_subM_U (N : MSys X) (S' : X → ℕ) (c : ℕ) (U : X → ℕ) :
    subM (N.lowLevel S' c U) U := by
  intro x
  unfold lowLevel
  by_cases h : N.lv S' x ≤ c <;> simp [h]

lemma lowLevel_self_of_lv_le (N : MSys X) (S' : X → ℕ) (c : ℕ) (U : X → ℕ) {x : X}
    (h : N.lv S' x ≤ c) : N.lowLevel S' c U x = U x := by
  simp [lowLevel, h]

lemma lowLevel_eq_zero_of_lv_gt (N : MSys X) (S' : X → ℕ) (c : ℕ) (U : X → ℕ) {x : X}
    (h : c < N.lv S' x) : N.lowLevel S' c U x = 0 := by
  simp [lowLevel, (not_le_of_gt h)]

/-- lowLevel is a sub-multiset of S' (when U ⊆ S') -/
lemma lowLevel_subM_S' (N : MSys X) (S' : X → ℕ) (c : ℕ) (U : X → ℕ) (hUS : subM U S') :
    subM (N.lowLevel S' c U) S' := by
  intro x
  by_cases h : N.lv S' x ≤ c
  · have hU := hUS x
    simp [lowLevel, h]
    exact hU
  · simp [lowLevel, h]

/-- countAt S' U j = number of level-j copies of U (when U ⊆ S') -/
lemma countAt_eq_sum_lv (N : MSys X) (S' U : X → ℕ) (j : ℕ) (hUS : subM U S') :
    N.countAt S' U j = ∑ x : X, if N.lv S' x = j then U x else 0 := by
  classical
  unfold countAt
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : N.lv S' x = j
  · have hmin : min (U x) (S' x) = U x := by
      exact min_eq_left (hUS x)
    simp [h, hmin]
  · simp [h]

/-- countAt of addM is addM of countAts when the second multiset has no level-j occurrences -/
lemma countAt_addM_eq_of_zero (N : MSys X) (S' W A : X → ℕ) (j : ℕ)
    (hA : ∀ x, N.lv S' x = j → A x = 0) :
    N.countAt S' (addM W A) j = N.countAt S' W j := by
  classical
  unfold countAt addM
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : N.lv S' x = j
  · have hAx : A x = 0 := hA x h
    simp [h, hAx]
  · simp [h]

/-- |lowLevel S' c U| = Σ_{j ≤ c} countAt S' U j (when U ⊆ S') -/
lemma sizeM_lowLevel (N : MSys X) (S' U : X → ℕ) (c : ℕ) (hUS : subM U S') :
    (sizeM (N.lowLevel S' c U) : ℝ) = ∑ j ∈ Finset.range (c + 1), (N.countAt S' U j : ℝ) := by
  classical
  have hNat : sizeM (N.lowLevel S' c U) = ∑ j ∈ Finset.range (c + 1), N.countAt S' U j := by
    calc
      sizeM (N.lowLevel S' c U) = ∑ x : X, (if N.lv S' x ≤ c then U x else 0) := by
        simp [sizeM, lowLevel]
      _ = ∑ x : X, (∑ j ∈ Finset.range (c + 1), (if N.lv S' x = j then U x else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : N.lv S' x ≤ c
        · have hmem : N.lv S' x ∈ Finset.range (c + 1) := by
            exact Finset.mem_range.mpr (by omega)
          have h1 := Finset.sum_ite_eq (Finset.range (c + 1)) (N.lv S' x) (fun _ => U x)
          rw [h1]
          simp [h, hmem]
        · have hnot : N.lv S' x ∉ Finset.range (c + 1) := by
            exact fun hm => h (by have hm' := (Finset.mem_range.mp hm); omega)
          have h1 := Finset.sum_ite_eq (Finset.range (c + 1)) (N.lv S' x) (fun _ => U x)
          rw [h1]
          simp [h, hnot]
      _ = ∑ j ∈ Finset.range (c + 1), (∑ x : X, (if N.lv S' x = j then U x else 0)) := by
        rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range (c + 1), N.countAt S' U j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [N.countAt_eq_sum_lv S' U j hUS]
  exact_mod_cast hNat

/-- countAt of a lowLevel of U at level j (j ≤ c) equals countAt of U -/
lemma countAt_lowLevel (N : MSys X) (S' U : X → ℕ) {c j : ℕ} (hjc : j ≤ c) :
    N.countAt S' (N.lowLevel S' c U) j = N.countAt S' U j := by
  classical
  unfold countAt
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : N.lv S' x = j
  · have hll : N.lowLevel S' c U x = U x := N.lowLevel_self_of_lv_le S' c U (by omega)
    simp [h, hll]
  · simp [h]

/-- countAt of a lowLevel of U at level j with c < j is 0 -/
lemma countAt_lowLevel_zero (N : MSys X) (S' U : X → ℕ) {c j : ℕ} (h : c < j) :
    N.countAt S' (N.lowLevel S' c U) j = 0 := by
  classical
  unfold countAt
  rw [Finset.sum_eq_zero]
  intro x hx
  by_cases hlv : N.lv S' x = j
  · have hll : N.lowLevel S' c U x = 0 := N.lowLevel_eq_zero_of_lv_gt S' c U (by omega)
    simp [hlv, hll]
  · simp [hlv]

/-- countAt of W at level j equals s_j − t_j for a minimum fragment (j ≤ b) -/
lemma countAt_W_eq_sCount_sub_u (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') {j : ℕ} (hjb : j ≤ b) :
    N.countAt S' W j = N.sCount S' j - N.countAt S' U j := by
  classical
  have hpoint : ∀ x, (if N.lv S' x = j then min (W x) (S' x) else 0) +
      (if N.lv S' x = j then min (U x) (S' x) else 0) = if N.lv S' x = j then S' x else 0 := by
    intro x
    by_cases hlv : N.lv S' x = j
    · have hobs := congrFun (N.obsTM S W U b hS hB hmin hfr) x
      change N.prefixM S' b x - W x = U x at hobs
      have hpre : N.prefixM S' b x = S' x := by
        rw [N.prefixM_pointwise]
        simp [hlv, hjb]
      rw [hpre] at hobs
      have hUeq : U x = S' x - W x := hobs.symm
      have hmain : min (W x) (S' x) + min (U x) (S' x) = S' x := by
        rw [hUeq]
        by_cases hw : W x ≤ S' x
        · have hminW : min (W x) (S' x) = W x := min_eq_left hw
          have hsub_le : S' x - W x ≤ S' x := Nat.sub_le (S' x) (W x)
          have hminU : min (S' x - W x) (S' x) = S' x - W x := min_eq_left hsub_le
          rw [hminW, hminU]
          omega
        · have hgt : S' x < W x := Nat.lt_of_not_ge hw
          have hminW : min (W x) (S' x) = S' x := min_eq_right (le_of_lt hgt)
          have hz : S' x - W x = 0 := by omega
          rw [hminW, hz]
          simp
      simp [hlv, hmain]
    · simp [hlv]
  have hsum : N.countAt S' W j + N.countAt S' U j = N.sCount S' j := by
    unfold countAt sCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  omega

/-- (9/10)·n_b ≤ t for a minimum fragment of a BAD W (the multiset obs.T') -/
theorem nb_le_tM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeightM T)
    (hbad : N.BadM ((10 : ℝ) ^ 10)⁻¹ W) (hmin : N.MinFragmentAtM S W U b hS hB)
    {S' : X → ℕ} (hfr : N.IsFragmentM S W U b S') :
    (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ (sizeM U : ℝ) := by
  classical
  let sCnt : ℕ → ℝ := fun j => (N.sCount S' j : ℝ)
  let uCnt : ℕ → ℝ := fun j => (N.countAt S' U j : ℝ)
  have hS'F : S' ∈ N.F := hfr.1.1
  have hprof : ∀ j, j ≤ b → N.sCount S j = N.sCount S' j := hfr.1.2
  have hfrag1 : ∀ j ≤ b, subM (N.levM S' j) (addM W U) := hfr.2.2.1
  have hfr2 : N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
      (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))) := hfr.2.2.2
  have hbτ : b ≤ N.τ := by
    have hminle : N.MinIndexM S W hS hB ≤ N.τ :=
      N.minIndexM_min S W hS hB (subMM S W) S (N.sdiff_isFragmentM S W hS hB)
    rw [hmin.1]
    exact hminle
  -- every element of the minimal fragment U has level ≤ b in the witness S'
  have hUS' : subM U S' := by
    exact subM_trans (N.minFragM_subM_sdiff_of_witness S W U b hS hB hmin hfr)
      (subM_subMM (m := S') (m' := W))
  have hUzero : ∀ {j : ℕ}, b + 1 ≤ j → ∀ x, N.lv S' x = j → U x = 0 := by
    intro j hj x hx
    by_contra hne
    have hpos : 0 < U x := Nat.pos_of_ne_zero hne
    have hle := N.level_le_b_of_minFragM S W U b hS hB hmin hfr hpos
    omega
  have hs_count : (∑ j ∈ Finset.range (b + 1), sCnt j) = (N.prefixCount S b : ℝ) := by
    unfold sCnt prefixCount
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hprof j (by simpa using hj)]
  have hLL : N.lowLevel S' b U = U := by
    funext x
    by_cases hb : N.lv S' x ≤ b
    · exact N.lowLevel_self_of_lv_le S' b U hb
    · have hUx : U x = 0 := hUzero (j := N.lv S' x) (by omega) x rfl
      simp [lowLevel, hb, hUx]
  have ht_count : (∑ j ∈ Finset.range (b + 1), uCnt j) = (sizeM U : ℝ) := by
    have h1 := N.sizeM_lowLevel S' U b hUS'
    rw [hLL] at h1
    simpa [uCnt] using h1.symm
  have hs_nonneg : ∀ j, 0 ≤ sCnt j := by
    intro j
    unfold sCnt
    positivity
  have hu_le_s : ∀ j, uCnt j ≤ sCnt j := by
    intro j
    unfold uCnt sCnt
    exact_mod_cast N.countAt_le_sCount S' U j
  by_contra hnot
  have htlt : (sizeM U : ℝ) < (9 / 10) * (N.prefixCount S b : ℝ) := lt_of_not_ge hnot
  have hC : (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j)) < 0 := by
    have hsum : (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j))
        = (∑ j ∈ Finset.range (b + 1), uCnt j) - (9 / 10) * (∑ j ∈ Finset.range (b + 1), sCnt j) := by
      calc
        (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.range (b + 1), uCnt j) - (∑ j ∈ Finset.range (b + 1), (9 / 10) * sCnt j) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ j ∈ Finset.range (b + 1), uCnt j) - (9 / 10) * (∑ j ∈ Finset.range (b + 1), sCnt j) := by
              rw [← Finset.mul_sum]
    rw [hsum, ht_count, hs_count]
    linarith
  have hsumneg : (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j))) < 0 := by
    have hterm : ∀ j, j ∈ Finset.range (b + 1) →
        (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j)) = uCnt j - (9 / 10) * sCnt j := by
      intro j hj
      calc
        (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j))
            = ((100 : ℝ) ^ j * wlev j) * (uCnt j - (9 / 10) * sCnt j) := by ring
        _ = uCnt j - (9 / 10) * sCnt j := by rw [wlev_mul_pow j]; ring
    calc
      (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j)))
          = (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j)) := by
            exact Finset.sum_congr rfl hterm
      _ < 0 := hC
  rcases exists_neg_tail b (fun j => wlev j * (uCnt j - (9 / 10) * sCnt j)) hsumneg with ⟨b', hb'le, hneg_b'⟩
  by_cases hb'pos : 0 < b'
  · -- case b' ≥ 1: the tail produces a fragment at the smaller index c = b'-1
    let c : ℕ := b' - 1
    let T' : X → ℕ := N.lowLevel S' c U
    let Gb : ℝ := ∑ j ∈ Finset.Icc b' b, sCnt j * wlev j
    let Sc : ℝ := ∑ j ∈ Finset.Icc b' b, sCnt j
    let nB : ℝ := (N.prefixCount S b : ℝ)
    let nC : ℝ := (N.prefixCount S c : ℝ)
    let tU : ℝ := (sizeM U : ℝ)
    let tT : ℝ := (sizeM T' : ℝ)
    have hc1 : c + 1 = b' := by unfold c; omega
    have hcle : c ≤ b := by unfold c; omega
    have hc_lt : c < b := by unfold c; omega
    have hT'subU : subM T' U := by
      simpa [T'] using (N.lowLevel_subM_U S' c U)
    have htT_le_tU : tT ≤ tU := by
      unfold tT tU
      exact_mod_cast sizeM_mono hT'subU
    have hnc_count : (∑ j ∈ Finset.range (c + 1), sCnt j) = (N.prefixCount S c : ℝ) := by
      unfold sCnt prefixCount
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hprof j (by have hj' := (Finset.mem_range.mp hj); omega)]
    have htT_count : (sizeM T' : ℝ) = ∑ j ∈ Finset.range (c + 1), uCnt j := by
      dsimp [T']
      have h1 := N.sizeM_lowLevel S' U c hUS'
      simpa [uCnt] using h1
    have htT_le_nC : tT ≤ nC := by
      calc
        tT = ∑ j ∈ Finset.range (c + 1), uCnt j := htT_count
        _ ≤ ∑ j ∈ Finset.range (c + 1), sCnt j := by
          apply Finset.sum_le_sum
          intro j hj
          exact hu_le_s j
        _ = nC := by
          unfold nC
          exact hnc_count
    have hnB : nB = nC + Sc := by
      unfold nB nC Sc
      calc
        (N.prefixCount S b : ℝ) = (∑ j ∈ Finset.range (b + 1), sCnt j) := by rw [hs_count]
        _ = (∑ j ∈ Finset.range (c + 1), sCnt j) + (∑ j ∈ Finset.Icc (c + 1) b, sCnt j) :=
              sum_range_split c b (by omega : c + 1 ≤ b) sCnt
        _ = (∑ j ∈ Finset.range (c + 1), sCnt j) + (∑ j ∈ Finset.Icc b' b, sCnt j) := by rw [hc1]
        _ = (N.prefixCount S c : ℝ) + (∑ j ∈ Finset.Icc b' b, sCnt j) := by rw [hnc_count]
    have hT'zero : ∀ j, b' ≤ j → ∀ x, N.lv S' x = j → T' x = 0 := by
      intro j hj x hx
      have h : c < N.lv S' x := by omega
      have hz := N.lowLevel_eq_zero_of_lv_gt S' c U h
      dsimp [T']
      exact hz
    have hWcount : ∀ j, j ∈ Finset.Icc b' b → (N.countAt S' W j : ℝ) = sCnt j - uCnt j := by
      intro j hj
      have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
      have hle : N.countAt S' U j ≤ N.sCount S' j := N.countAt_le_sCount S' U j
      have hc := N.countAt_W_eq_sCount_sub_u S W U b hS hB hmin hfr hjb
      have hcR : (N.countAt S' W j : ℝ) = (N.sCount S' j : ℝ) - (N.countAt S' U j : ℝ) := by
        rw [← Nat.cast_sub hle]
        exact_mod_cast hc
      unfold sCnt uCnt
      exact hcR
    have hWb_ge : (1 / 10 : ℝ) * Gb ≤ ∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j := by
      have h1 : (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
          = (∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hWcount j hj]
      have h2 : (1 / 10 : ℝ) * Gb ≤ (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j) := by
        unfold Gb
        have heq : (∑ j ∈ Finset.Icc b' b, wlev j * (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc b' b, wlev j * (uCnt j - (9 / 10) * sCnt j))
                = (∑ j ∈ Finset.Icc b' b, (uCnt j * wlev j - (9 / 10) * (sCnt j * wlev j))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, (9 / 10) * (sCnt j * wlev j)) := by
                  rw [Finset.sum_sub_distrib]
            _ = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
                  congr 1
                  rw [← Finset.mul_sum]
        have heq2 : (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
            = (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
                = (∑ j ∈ Finset.Icc b' b, (sCnt j * wlev j - uCnt j * wlev j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) := by
                  rw [Finset.sum_sub_distrib]
        have hneg'' : (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) < (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
          rw [heq] at hneg_b'
          linarith
        nlinarith
      rw [← h1]
      exact h2
    -- weight-above decompositions
    have hWAc : N.weightAboveM S' S' c = Gb + N.weightAboveM S' S' b := by
      unfold weightAboveM Gb
      calc
        (∑ j ∈ Finset.Icc (c + 1) N.τ, (N.countAt S' S' j : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc b' N.τ, (N.countAt S' S' j : ℝ) * wlev j) := by rw [hc1]
        _ = (∑ j ∈ Finset.Icc b' b, (N.countAt S' S' j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' S' j : ℝ) * wlev j) :=
              sum_Icc_split_at (a := b') (b := b) (c := N.τ) hb'le hbτ
                (fun j => (N.countAt S' S' j : ℝ) * wlev j)
        _ = (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' S' j : ℝ) * wlev j) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              simp [sCnt, N.sCount_eq_countAt_self S' j]
        _ = Gb + N.weightAboveM S' S' b := by
              unfold weightAboveM
              rfl
    have hG1 : (1 / 100 : ℝ) * wlev b * Sc ≤ (9 / 100) * Gb := by
      calc
        (1 / 100 : ℝ) * wlev b * Sc = (∑ j ∈ Finset.Icc b' b, ((1 / 100 : ℝ) * wlev b) * sCnt j) := by
          unfold Sc
          rw [Finset.mul_sum]
        _ ≤ (∑ j ∈ Finset.Icc b' b, (9 / 100) * (sCnt j * wlev j)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
          have hb1 := wlev_bound b j hjb
          have hb2 : (1 / 100 : ℝ) * wlev b ≤ (9 / 100) * wlev j := by
            rw [← wlev_succ_hundred b]
            exact hb1
          have hs : 0 ≤ sCnt j := hs_nonneg j
          calc
            ((1 / 100 : ℝ) * wlev b) * sCnt j ≤ ((9 / 100) * wlev j) * sCnt j := mul_le_mul_of_nonneg_right hb2 hs
            _ = (9 / 100) * (sCnt j * wlev j) := by ring
        _ = (9 / 100) * Gb := by
          unfold Gb
          rw [Finset.mul_sum]
    have hMid : (∑ j ∈ Finset.Icc b' b, (N.countAt S' (addM W T') j : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjb' : b' ≤ j := (Finset.mem_Icc.mp hj).1
      have hE := N.countAt_addM_eq_of_zero S' W T' j (hT'zero j hjb')
      rw [hE]
    have hTop1 : (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' (addM W T') j : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' (addM W U) j : ℝ) * wlev j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have h1 := N.countAt_addM_eq_of_zero S' W T' j (hT'zero j (by omega))
      have h2 := N.countAt_addM_eq_of_zero S' W U j (hUzero hjge)
      rw [h1, h2]
    have hWA_eq : N.weightAboveM S' (addM W T') c =
        (∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j)
          + N.weightAboveM S' (addM W U) b := by
      unfold weightAboveM
      calc
        (∑ j ∈ Finset.Icc (c + 1) N.τ, (N.countAt S' (addM W T') j : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc b' N.τ, (N.countAt S' (addM W T') j : ℝ) * wlev j) := by rw [hc1]
        _ = (∑ j ∈ Finset.Icc b' b, (N.countAt S' (addM W T') j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' (addM W T') j : ℝ) * wlev j) :=
              sum_Icc_split_at (a := b') (b := b) (c := N.τ) hb'le hbτ
                (fun j => (N.countAt S' (addM W T') j : ℝ) * wlev j)
        _ = (∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' (addM W U) j : ℝ) * wlev j) := by
              rw [hMid, hTop1]
        _ = (∑ j ∈ Finset.Icc b' b, (N.countAt S' W j : ℝ) * wlev j)
            + N.weightAboveM S' (addM W U) b := by
              unfold weightAboveM
              rfl
    have hnew2 : N.weightAboveM S' (addM W T') c ≥ (100 : ℝ)⁻¹ *
        (N.weightAboveM S' S' c - wlev c * (nC - tT)) := by
      have hchain1 : (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ *
            (N.weightAboveM S' S' b - wlev b * (nB - tU)) ≤ N.weightAboveM S' (addM W T') c := by
        rw [hWA_eq]
        have h2 : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU)) ≤
            N.weightAboveM S' (addM W U) b := by
          simpa [nB, tU] using hfr2
        exact add_le_add hWb_ge h2
      have hD : 0 ≤ (9 / 100) * Gb - (1 / 100) * wlev b * (nB - tU)
          + (1 / 100) * wlev c * (nC - tT) := by
        exact frag2_aux Gb Sc nB tU nC tT (wlev b) (wlev c) hG1 hnB (wlev_nonneg b)
          htT_le_tU htT_le_nC (wlev_le_of_le hcle)
      have hdiff : (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU))
            - (100 : ℝ)⁻¹ * (N.weightAboveM S' S' c - wlev c * (nC - tT))
          = (9 / 100) * Gb - (1 / 100) * wlev b * (nB - tU) + (1 / 100) * wlev c * (nC - tT) := by
        rw [hWAc]
        have hinv : (100 : ℝ)⁻¹ = (1 / 100 : ℝ) := by norm_num
        rw [hinv]
        ring_nf
      have hBleA : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' c - wlev c * (nC - tT)) ≤
          (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU)) := by
        exact (sub_nonneg.mp (by rw [hdiff]; exact hD))
      exact le_trans hBleA hchain1
    have hnew1 : ∀ j ≤ c, subM (N.levM S' j) (addM W T') := by
      intro j hj y
      by_cases hlv : N.lv S' y = j
      · have hT : T' y = U y := by
          dsimp [T']
          exact N.lowLevel_self_of_lv_le S' c U (by omega)
        have hlev : N.levM S' j y = S' y := N.levM_pos_of_lv_eq S' j hlv
        have hsub1 := hfrag1 j (by omega : j ≤ b) y
        have hsub2 : S' y ≤ W y + U y := by
          simpa [hlev, addM] using hsub1
        change N.levM S' j y ≤ W y + T' y
        rw [hlev, hT]
        exact hsub2
      · have hz : N.levM S' j y = 0 := N.levM_eq_zero_of_lv_ne S' j hlv
        rw [hz]
        exact Nat.zero_le _
    have hTfrag : N.IsFragmentM S W T' c S' := by
      constructor
      · constructor
        · exact hS'F
        · intro j hj
          exact hprof j (by omega)
      · constructor
        · intro x
          exact le_trans (hT'subU x) (hfr.2.1 x)
        · constructor
          · exact hnew1
          · simpa [nC, tT] using hnew2
    have hminle : N.MinIndexM S W hS hB ≤ c := N.minIndexM_min S W hS hB T' S' hTfrag
    have hcmin : c < N.MinIndexM S W hS hB := by
      rw [← hmin.1]
      exact hc_lt
    omega
  · -- case b' = 0: W∩S' alone would carry 1% of the weight of S'
    have hb'0 : b' = 0 := by omega
    let tU : ℝ := (sizeM U : ℝ)
    let nB : ℝ := (N.prefixCount S b : ℝ)
    let G0 : ℝ := ∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j
    let S0 : ℝ := ∑ j ∈ Finset.Icc 0 b, sCnt j
    have htU_nonneg : 0 ≤ tU := by
      unfold tU
      positivity
    have hWcount0 : ∀ j, j ∈ Finset.Icc 0 b → (N.countAt S' W j : ℝ) = sCnt j - uCnt j := by
      intro j hj
      have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
      have hle : N.countAt S' U j ≤ N.sCount S' j := N.countAt_le_sCount S' U j
      have hc := N.countAt_W_eq_sCount_sub_u S W U b hS hB hmin hfr hjb
      have hcR : (N.countAt S' W j : ℝ) = (N.sCount S' j : ℝ) - (N.countAt S' U j : ℝ) := by
        rw [← Nat.cast_sub hle]
        exact_mod_cast hc
      unfold sCnt uCnt
      exact hcR
    have hneg0 : (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j)) < 0 := by
      simpa [hb'0] using hneg_b'
    have hW0_ge : (1 / 10 : ℝ) * G0 ≤ ∑ j ∈ Finset.Icc 0 b, (N.countAt S' W j : ℝ) * wlev j := by
      have h1 : (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
          = (∑ j ∈ Finset.Icc 0 b, (N.countAt S' W j : ℝ) * wlev j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hWcount0 j hj]
      have h2 : (1 / 10 : ℝ) * G0 ≤ (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j) := by
        unfold G0
        have heq : (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j))
                = (∑ j ∈ Finset.Icc 0 b, (uCnt j * wlev j - (9 / 10) * (sCnt j * wlev j))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, (9 / 10) * (sCnt j * wlev j)) := by
                  rw [Finset.sum_sub_distrib]
            _ = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
                  congr 1
                  rw [← Finset.mul_sum]
        have heq2 : (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
            = (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
                = (∑ j ∈ Finset.Icc 0 b, (sCnt j * wlev j - uCnt j * wlev j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) := by
                  rw [Finset.sum_sub_distrib]
        have hneg'' : (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) < (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
          rw [heq] at hneg0
          linarith
        nlinarith
      rw [← h1]
      exact h2
    have hWAU0 : N.weightAboveM S' (addM W U) b = N.weightAboveM S' W b := by
      unfold weightAboveM
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have h1 := N.countAt_addM_eq_of_zero S' W U j (hUzero hjge)
      rw [h1]
    have hpart : N.weightM S' W =
        (∑ j ∈ Finset.Icc 0 b, (N.countAt S' W j : ℝ) * wlev j) + N.weightAboveM S' W b := by
      unfold weightM weightAboveM
      calc
        (∑ j ∈ Finset.range (N.τ + 1), (N.countAt S' W j : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc 0 N.τ, (N.countAt S' W j : ℝ) * wlev j) := sum_range_eq_sum_Icc0 N.τ _
        _ = (∑ j ∈ Finset.Icc 0 b, (N.countAt S' W j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' W j : ℝ) * wlev j) :=
              sum_Icc_split_at (a := 0) (b := b) (c := N.τ) (by omega) hbτ _
        _ = (∑ j ∈ Finset.Icc 0 b, (N.countAt S' W j : ℝ) * wlev j) + N.weightAboveM S' W b := by
              unfold weightAboveM
              rfl
    have htotal : N.totalWeightM S' = G0 + N.weightAboveM S' S' b := by
      unfold totalWeightM weightM weightAboveM G0
      calc
        (∑ j ∈ Finset.range (N.τ + 1), (N.countAt S' S' j : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc 0 N.τ, (N.countAt S' S' j : ℝ) * wlev j) := sum_range_eq_sum_Icc0 N.τ _
        _ = (∑ j ∈ Finset.Icc 0 b, (N.countAt S' S' j : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' S' j : ℝ) * wlev j) :=
              sum_Icc_split_at (a := 0) (b := b) (c := N.τ) (by omega) hbτ _
        _ = (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (N.countAt S' S' j : ℝ) * wlev j) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              simp [sCnt, N.sCount_eq_countAt_self S' j]
        _ = G0 + N.weightAboveM S' S' b := by
              unfold weightAboveM
              rfl
    have hnB_S0 : nB = S0 := by
      unfold nB S0
      calc
        (N.prefixCount S b : ℝ) = (∑ j ∈ Finset.range (b + 1), sCnt j) := by rw [hs_count]
        _ = (∑ j ∈ Finset.Icc 0 b, sCnt j) := sum_range_eq_sum_Icc0 b sCnt
    have hG0_le : (1 / 100 : ℝ) * wlev b * S0 ≤ (9 / 100) * G0 := by
      calc
        (1 / 100 : ℝ) * wlev b * S0 = (∑ j ∈ Finset.Icc 0 b, ((1 / 100 : ℝ) * wlev b) * sCnt j) := by
          unfold S0
          rw [Finset.mul_sum]
        _ ≤ (∑ j ∈ Finset.Icc 0 b, (9 / 100) * (sCnt j * wlev j)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
          have hb1 := wlev_bound b j hjb
          have hb2 : (1 / 100 : ℝ) * wlev b ≤ (9 / 100) * wlev j := by
            rw [← wlev_succ_hundred b]
            exact hb1
          have hs : 0 ≤ sCnt j := hs_nonneg j
          calc
            ((1 / 100 : ℝ) * wlev b) * sCnt j ≤ ((9 / 100) * wlev j) * sCnt j := mul_le_mul_of_nonneg_right hb2 hs
            _ = (9 / 100) * (sCnt j * wlev j) := by ring
        _ = (9 / 100) * G0 := by
          unfold G0
          rw [Finset.mul_sum]
    have hD0 : 0 ≤ (9 / 100) * G0 - (1 / 100) * wlev b * (nB - tU) := by
      have hle1 : (1 / 100 : ℝ) * wlev b * (nB - tU) ≤ (1 / 100 : ℝ) * wlev b * S0 := by
        have h1 : nB - tU ≤ S0 := by nlinarith [hnB_S0, htU_nonneg]
        have hle : wlev b * (nB - tU) ≤ wlev b * S0 := mul_le_mul_of_nonneg_left h1 (wlev_nonneg b)
        have hle' : (1 / 100 : ℝ) * (wlev b * (nB - tU)) ≤ (1 / 100 : ℝ) * (wlev b * S0) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        simpa [mul_assoc] using hle'
      linarith
    have hlow : (1 / 100 : ℝ) * N.totalWeightM S' ≤ N.weightM S' W := by
      have hc0 : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU)) ≤ N.weightAboveM S' (addM W U) b := by
        simpa [nB, tU] using hfr2
      have hc0' : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU)) ≤ N.weightAboveM S' W b := by
        rw [← hWAU0]
        exact hc0
      have hmid : (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU))
          ≤ N.weightM S' W := by
        rw [hpart]
        exact add_le_add hW0_ge hc0'
      have hchain : (1 / 100 : ℝ) * N.totalWeightM S' ≤
          (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU)) := by
        have hdiff0 : (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * (nB - tU))
              - (1 / 100) * N.totalWeightM S'
            = (9 / 100) * G0 - (1 / 100) * wlev b * (nB - tU) := by
          rw [htotal]
          have hinv : (100 : ℝ)⁻¹ = (1 / 100 : ℝ) := by norm_num
          rw [hinv]
          ring_nf
        exact (sub_nonneg.mp (by rw [hdiff0]; exact hD0))
      exact le_trans hchain hmid
    have hwle : N.weightM S' W ≤ N.procValM W := by
      unfold procValM
      exact N.le_mSup (v := fun T : X → ℕ => N.weightM T W) hS'F
    have hTotS' : ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeightM S' := hTot S' hS'F
    have hten : ((10 : ℝ) ^ 10)⁻¹ ≤ (1 / 100 : ℝ) * N.totalWeightM S' := by
      have heq : ((10 : ℝ) ^ 10)⁻¹ = (1 / 100 : ℝ) * ((10 : ℝ) ^ 8)⁻¹ := by
        have hpow : (10 : ℝ) ^ 10 = (10 : ℝ) ^ 8 * 100 := by
          rw [show (10 : ℕ) = 8 + 2 by norm_num]
          rw [pow_add]
          norm_num
        rw [hpow]
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hTotS' (by norm_num)
    have hbad' : N.procValM W < ((10 : ℝ) ^ 10)⁻¹ := hbad
    linarith

end MSys

end Multi
end Submission
