import Mathlib
import Submission.Work.PTCert.Checks.C1All
import Submission.Work.PTCert.cert1Aux
import Submission.Work.PTCert.targetExpansions
import Submission.Work.PTCert.targetInvariance
import Submission.Work.PTCert.cert1Sym
import Submission.Work.PTCert.cert1RowCheck
import Submission.Work.PTCert.cert1Ldl0
import Submission.Work.PTCert.cert1Ldl1
import Submission.Work.PTCert.cert1Ldl2
import Submission.Work.PTCert.cert1Ldl3
import Submission.Work.PTCert.cert1Ldl4
import Submission.Work.PTCert.cert1ClassSum

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects and the semantic Props of the data) and
`Glue3.lean` (math steps), `KernelShared.lean`/`KernelCert.lean` (the Bool check functions), the data
modules `Data/*.lean` (namespace `Submission.PTCert.D`) and the kernel theorems `Checks/*.lean`
(namespace `Submission.PTCert.C`, each `theorem xxx : <check> = true := by decide +kernel`, ALREADY BUILT).
Design notes: `NOTES_LEAD_glue.md` at the workspace root.
HARD RULES: never `decide`/`native_decide`/`simp`/`rfl` over the big data definitions (eAll, eM, the trees,
the class lists …) — they are thousands of entries; all data facts come from the Checks theorems. The only
kernel evaluation you may add is `decide +kernel` on genuinely small facts (≤ a few hundred table lookups,
e.g. `ngL.getD 0 0 = 18`, 18 row codes, `eAll = eC0 ++ … ++ eC7` IS allowed as `by decide +kernel` only
if it runs in < 60 s — otherwise prove it by `rfl`/unfolding at the list level). Never edit Checks/, Data/,
Kernel*.lean, Glue*.lean. The soundness proofs are "unfold the Bool function, turn `&&`/`allL`/`allR`/
`Nat.beq`/`bif` into ∀/∧/=/if (lemmas: Bool.and_eq_true, Nat.beq_eq, List.all_eq_true-style lemmas you prove
for allL/allR/allIdx by induction), then instantiate". Write small reusable lemmas (e.g. `allL_iff`, `allR_iff`,
`allIdx_iff`, `eqL_iff`, `strictInc → Nodup/Sorted`) in your own helper file first.
Certificate data (namespace D1 resp. D2): valT, rowT0..17 (rowTs), Cs{k}/Ws{k}/acc{k}_{j} (k ≤ 4), resT, resBound.
Kernel theorems (namespace C1K resp. C2K, modules Checks.C1.* / C2.*, aggregated by Checks.C1All / C2All):
sym_ok{r}_{j} (symOK …), rw_ok{r}_{j} (rowCheck … on rep chunks), ldldata_ok{k}, ldl_ok{k}_{j}
(ldlSeg … rows acc{k}_{j} = some acc{k}_{j+1}), cs_ok{j} (classSumOK … kl{j} tl{j} (500 j)), ressym_ok, resbound_ok.
Constants: C1: q = qC1, Dq = 20, SC = 2^80, λ = 13/10, λ' = 1, c = λ - λ' = 3/10 (resBound = (3/10)·2^80·20).
          C2: q = qC2, Dq = 200, μ = 7/25, μ' = 1/20, c = 23/100 (resBound = c·2^80·200).
Plan (pv := fun k => sv (p8 valT k), res := fun c => sv (p8 resT c)):
(1) SymHyp pv from sym_ok (unfold symOK; allL over the group chunks covers g < ngE r — ngE r values by small decide).
(2) RowTabHyp pv rowTs from rw_ok via hRT (RowTabSound needs rowCheck on singletons: allL over a chunk ⇒ each t;
    the chunks cover t < 611). rowTs here must be D1.rowTs (RWAll) and olTs.getD r = olT{r}.
(3) LdlData rowTs k for k ≤ 4: Cs := Cs{k}, Ws := Ws{k}, segs := the row lists of the ldl_ok{k}_{j} theorems in order
    (write the list literal), accs j := acc{k}_{j} (define by match on j, junk beyond); segs.flatten = List.range (nK k)
    and accs 0 = replicate … by small `decide +kernel`/`rfl` (nK k = ks{k}.length: 161, 88, 59, 27, 6 — check);
    ldldata_ok{k} gives the Ws/Cs shape clause.
(4) hPA ⇒ (Pmat pv).PosSemidef.
(5) Class sums from cs_ok{j} (unfold classSumOK: the List.rec over kl{j} with tl{j} in lockstep; class c = 500 j + i;
    klist.getD c [] = (kl{j}).getD i [] since klist = kl0 ++ …; foldr sums = List.sum of maps); residual symmetry
    and Σ res = 0, 16 Σ|res| ≤ bound from ressym_ok / resbound_ok (List.range foldr ↔ Finset.range sums; Int → ℝ casts).
(6) hFS with T := deltaSub 5 5 ^ 2 - (1:ℝ) • deltaSub 5 5 (C1) resp. AdjPair 5 5 + 2 • OpPair 5 5 - (1/20) • deltaSub 5 5 (C2),
    c as above: T = targetSum q Dq + c • Δ by `targetExpansions 5` (TargetExpansions: Δ² - λΔ = gramL 5 (QDelta 5 λ),
    Adj + k Op - μΔ = gramL 5 (QAdjOp 5 k μ)) and hT1/hT2, plus algebra (λ-linearity). T invariant: `targetInvariance 5`.
    Conclude SAut5DeltaCert := ⟨1, one_pos, …⟩ resp. SAut5Adj2OpCert := ⟨1/20, _, …⟩.
C2 ONLY: the class-sum checks use the verified table q := fun p => sv (p8 qT p) (data Data/C2/Q.lean), and
C2K.q_ok{j} : qTabOK qT qC2 (List.range' (81 j) 81) = true (j < 81, modules Checks.C2.Q0..Q8) give
∀ p < 6561, sv (p8 qT p) = qC2 p, hence targetSum (fun p => sv (p8 qT p)) 200 = targetSum qC2 200 (Finset.sum_congr).
qTabOK is in KernelExtra.lean. Pass this table q to FinalStep.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1 Submission.PTCert.C1K
open scoped BigOperators

set_option maxRecDepth 10000

noncomputable section

/-! ## Auxiliary facts used by the C1 assembly (residual and target) -/

/-- A `foldr` of additive values over `List.range`, with accumulator. -/
lemma foldr_range_add (n : ℕ) (f : ℕ → ℤ) (b : ℤ) :
    (List.range n).foldr (fun i acc => acc + f i) b = b + ∑ i ∈ Finset.range n, f i := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ,
      show List.foldr (fun i acc => acc + f i) b [n] = b + f n by simp [List.foldr_cons],
      ih (b + f n)]
    ring

/-- A `foldr` of additive values over `List.range` is the `Finset` sum over `Finset.range`. -/
lemma sum_range_foldr (n : ℕ) (f : ℕ → ℤ) :
    (List.range n).foldr (fun i acc => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  rw [foldr_range_add n f 0, zero_add]

/-- The residual symmetry check `resSymOK`: residuals come in inverse pairs. -/
lemma cert1res_icl (c : ℕ) (hc : c < ncls) :
    cert1res (icls c) = cert1res c ∧ icls (icls c) = c := by
  have h0 : allL (List.range ncls) (fun c => let ic := w34 iclT c / 1048576
      (Nat.beq (p8 resT ic) (p8 resT c) && Nat.beq (w34 iclT ic / 1048576) c)) = true :=
    ressym_ok
  have h := (allL_range_iff.mp h0) c hc
  rw [bool_and_iff, Nat.beq_eq, Nat.beq_eq] at h
  refine ⟨?_, ?_⟩
  · show sv (p8 resT (w34 iclT c / 1048576)) = sv (p8 resT c)
    rw [h.1]
  · show w34 iclT (w34 iclT c / 1048576) / 1048576 = c
    exact h.2

/-- The residual sums to zero. -/
lemma cert1res_sum : ∑ c ∈ Finset.range ncls, cert1res c = 0 := by
  have h := resbound_ok
  unfold resBoundOK at h
  rw [bool_and_iff, decide_eq_true_iff] at h
  have h1 : (List.range ncls).foldr (fun c acc => acc + cert1res c) 0 = 0 := by
    simpa [cert1res, ncls] using h.1
  rwa [sum_range_foldr ncls cert1res] at h1

/-- The residual ℓ¹-bound `16 Σ|res| ≤ (3/10) · 2^80 · 20` of certificate 1. -/
lemma cert1res_bound :
    16 * (∑ c ∈ Finset.range ncls, |(cert1res c : ℝ)|) ≤ (3 / 10 : ℝ) * (cert1SC : ℝ) * 20 := by
  have h := resbound_ok
  unfold resBoundOK at h
  rw [bool_and_iff, decide_eq_true_iff] at h
  have hb : 16 * ((List.range ncls).foldr (fun c acc => acc + |cert1res c|) 0) ≤ D1.resBound := by
    simpa [cert1res, ncls] using h.2
  rw [sum_range_foldr ncls (fun c => |cert1res c|)] at hb
  have hcast : (∑ c ∈ Finset.range ncls, |(cert1res c : ℝ)|)
      = ((∑ c ∈ Finset.range ncls, |cert1res c| : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hcast, show (3 / 10 : ℝ) * (cert1SC : ℝ) * 20 = (D1.resBound : ℝ) by
    norm_num [cert1SC, D1.resBound]]
  exact_mod_cast hb

/-- The target of certificate 1 as `Γ(λ')`: `Δ² - 1·Δ = targetSum qC1 20 + (3/10)·Δ`. -/
lemma cert1target (hT1 : targetSum qC1 20 = gramL 5 (QDelta 5 (13 / 10))) :
    Submission.RouteB.Edge.deltaSub 5 5 ^ 2 - (1 : ℝ) • Submission.RouteB.Edge.deltaSub 5 5
      = targetSum qC1 20 + (3 / 10 : ℝ) • Submission.RouteB.Edge.deltaSub 5 5 := by
  have h := (targetExpansions 5).1 (13 / 10 : ℚ)
  rw [show ((13 / 10 : ℚ) : ℝ) = (13 / 10 : ℝ) by norm_num] at h
  rw [← hT1] at h
  rw [← h]
  module

/-! ## Conjugation by a signed permutation -/

/-- `MonoidAlgebra.of` is multiplicative. -/
lemma of_mul_G5 (a b : G5) :
    MonoidAlgebra.of ℝ G5 (a * b) = MonoidAlgebra.of ℝ G5 a * MonoidAlgebra.of ℝ G5 b :=
  map_mul _ a b

/-- `of s⁻¹ * of s = 1`. -/
lemma of_inv_mul_G5 (s : G5) : MonoidAlgebra.of ℝ G5 s⁻¹ * MonoidAlgebra.of ℝ G5 s = 1 := by
  rw [← of_mul_G5, inv_mul_cancel, map_one]

/-- Conjugation by `of s` is multiplicative. -/
lemma conj_mul_G5 (s : G5) (x y : MonoidAlgebra ℝ G5) :
    MonoidAlgebra.of ℝ G5 s * (x * y) * MonoidAlgebra.of ℝ G5 s⁻¹
      = (MonoidAlgebra.of ℝ G5 s * x * MonoidAlgebra.of ℝ G5 s⁻¹)
        * (MonoidAlgebra.of ℝ G5 s * y * MonoidAlgebra.of ℝ G5 s⁻¹) := by
  calc MonoidAlgebra.of ℝ G5 s * (x * y) * MonoidAlgebra.of ℝ G5 s⁻¹
      = MonoidAlgebra.of ℝ G5 s * x * y * MonoidAlgebra.of ℝ G5 s⁻¹ := by noncomm_ring
    _ = MonoidAlgebra.of ℝ G5 s * x
          * (MonoidAlgebra.of ℝ G5 s⁻¹ * MonoidAlgebra.of ℝ G5 s) * y
          * MonoidAlgebra.of ℝ G5 s⁻¹ := by
        rw [of_inv_mul_G5 s, mul_one]
    _ = (MonoidAlgebra.of ℝ G5 s * x * MonoidAlgebra.of ℝ G5 s⁻¹)
          * (MonoidAlgebra.of ℝ G5 s * y * MonoidAlgebra.of ℝ G5 s⁻¹) := by noncomm_ring

/-- Conjugation by `of s` commutes with squaring. -/
lemma conj_sq_G5 (s : G5) (x : MonoidAlgebra ℝ G5) :
    MonoidAlgebra.of ℝ G5 s * x ^ 2 * MonoidAlgebra.of ℝ G5 s⁻¹
      = (MonoidAlgebra.of ℝ G5 s * x * MonoidAlgebra.of ℝ G5 s⁻¹) ^ 2 := by
  rw [pow_two, conj_mul_G5, pow_two]

/-- `Δ₅² - 1·Δ₅` is invariant under conjugation by the signed permutations. -/
lemma cert1inv : ∀ σ ∈ Sg, MonoidAlgebra.of ℝ G5 σ
      * (Submission.RouteB.Edge.deltaSub 5 5 ^ 2
        - (1 : ℝ) • Submission.RouteB.Edge.deltaSub 5 5)
      * MonoidAlgebra.of ℝ G5 σ⁻¹
    = Submission.RouteB.Edge.deltaSub 5 5 ^ 2
      - (1 : ℝ) • Submission.RouteB.Edge.deltaSub 5 5 := by
  intro σ hσ
  set Δ : MonoidAlgebra ℝ G5 := Submission.RouteB.Edge.deltaSub 5 5 with hΔdef
  have hΔ : MonoidAlgebra.of ℝ G5 σ * Δ * MonoidAlgebra.of ℝ G5 σ⁻¹ = Δ :=
    ((targetInvariance 5) σ hσ).1
  have h1 : MonoidAlgebra.of ℝ G5 σ * (Δ ^ 2 - (1 : ℝ) • Δ) * MonoidAlgebra.of ℝ G5 σ⁻¹
      = MonoidAlgebra.of ℝ G5 σ * Δ ^ 2 * MonoidAlgebra.of ℝ G5 σ⁻¹
        - MonoidAlgebra.of ℝ G5 σ * ((1 : ℝ) • Δ) * MonoidAlgebra.of ℝ G5 σ⁻¹ := by
    rw [mul_sub, sub_mul]
  have h2 : MonoidAlgebra.of ℝ G5 σ * Δ ^ 2 * MonoidAlgebra.of ℝ G5 σ⁻¹ = Δ ^ 2 := by
    rw [conj_sq_G5, hΔ]
  have h3 : MonoidAlgebra.of ℝ G5 σ * ((1 : ℝ) • Δ) * MonoidAlgebra.of ℝ G5 σ⁻¹
      = (1 : ℝ) • Δ := by
    rw [one_smul, hΔ]
  rw [h1, h2, h3]

theorem cert1Final (hPA : PsdAssembly) (hRT : RowTabSound) (hFS : FinalStep) (hC : ClassSem)
    (hK : ∀ k ≤ 5, KleinSem k) (hT1 : targetSum qC1 20 = gramL 5 (QDelta 5 (13 / 10))) :
    Submission.RouteB.Edge.SAut5DeltaCert := by
  -- the shape hypothesis of `Pmat cert1pv`
  have hsym : SymHyp cert1pv := symHyp_cert1pv_iff.mpr cert1Sym
  -- the row tables of `Pmat cert1pv`
  have hrow : RowTabHyp cert1pv D1.rowTs := hRT valT D1.rowTs cert1RowCheck
  -- the LDL data of the five base characters
  have hldl : ∀ k ≤ 4, LdlData D1.rowTs k := by
    intro k hk
    interval_cases k
    · exact cert1Ldl0
    · exact cert1Ldl1
    · exact cert1Ldl2
    · exact cert1Ldl3
    · exact cert1Ldl4
  -- `Pmat cert1pv ⪰ 0`
  have hPSD : (Pmat cert1pv).PosSemidef := hPA cert1pv D1.rowTs hsym hrow hldl
  -- the certificate `Λ = 1`
  refine ⟨1, one_pos, ?_⟩
  exact hFS cert1pv qC1 cert1res 20 cert1SC
    (Submission.RouteB.Edge.deltaSub 5 5 ^ 2 - (1 : ℝ) • Submission.RouteB.Edge.deltaSub 5 5)
    (3 / 10) (by norm_num) cert1SC_pos hPSD cert1ClassSum cert1res_icl cert1res_sum
    cert1res_bound cert1inv (cert1target hT1)

end

end Work.PTCert
