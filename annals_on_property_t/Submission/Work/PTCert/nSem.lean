import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.permCheckKSound

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
Checks: C.echunk_ok{j} (eChunkOK cmT eM nT repT eCj: for z in the chunk, with v := eG eM z - 1:
eG eM z ≠ 0, actC cmT (nT.get (v % 32)) (cG repT (v / 32)) = z — note eChunkOK's `nT.get (v % 32)` = ntab and
`cG repT` = rp), C.repself_ok (repSelfOK eM repT (List.range 611): rp t < 10368, em (rp t) = 32 t + 1),
C.repinv_ok (repInvOK cmT eM nT repT (List.range 611)).
Also (em z - 1)/32 < 611: C.ebound_ok{j} (eBoundOK eM eCj, KernelExtra.lean; module Checks.X).
rp t ∈ eAll: rp t < 10368 and em (rp t) ≠ 0, and the membership ↔ from eExactOK (as in eSem; you may take
C.eexact_ok as well).
-/

set_option maxRecDepth 100000

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ### Boolean-combinator lemmas for the kernel check functions -/

namespace NSemAux

lemma allL_nil (p : ℕ → Bool) : allL [] p = true := rfl

lemma allL_cons (a : ℕ) (t : List ℕ) (p : ℕ → Bool) : allL (a :: t) p = (p a && allL t p) := rfl

lemma allL_iff (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL_nil]
  | cons a t ih =>
    rw [allL_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨ha, ht⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact ht b hb
    · intro h
      exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)), fun b hb => h b (List.mem_cons.mpr (Or.inr hb))⟩

lemma allR_zero (p : ℕ → Bool) : allR 0 p = true := rfl

lemma allR_succ (n : ℕ) (p : ℕ → Bool) : allR (n + 1) p = (p n && allR n p) := rfl

lemma allR_iff (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR_zero]
  | succ n ih =>
    rw [allR_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, ht⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ht k hk
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

lemma eqL_nil_nil : eqL [] [] = true := rfl

lemma eqL_nil_cons (b : ℕ) (t : List ℕ) : eqL [] (b :: t) = false := rfl

lemma eqL_cons_nil (a : ℕ) (t : List ℕ) : eqL (a :: t) [] = false := rfl

lemma eqL_cons_cons (a b : ℕ) (t t' : List ℕ) :
    eqL (a :: t) (b :: t') = (Nat.beq a b && eqL t t') := rfl

lemma eqL_iff : ∀ (l m : List ℕ), eqL l m = true ↔ l = m := by
  intro l
  induction l with
  | nil =>
    intro m
    cases m with
    | nil => simp [eqL_nil_nil]
    | cons b t => simp [eqL_nil_cons]
  | cons a t ih =>
    intro m
    cases m with
    | nil => simp [eqL_cons_nil]
    | cons b t' => rw [eqL_cons_cons, Bool.and_eq_true, Nat.beq_eq, ih]; simp

lemma not_beq_zero_eq_true {n : ℕ} : (!(Nat.beq n 0)) = true ↔ n ≠ 0 := by
  by_cases h : n = 0
  · subst h; decide
  · have hb : Nat.beq n 0 = false := by
      by_contra hf
      exact h (Nat.beq_eq.mp (by simpa using hf))
    rw [hb]; simp [h]

/-! ### The chunks of `eAll` -/

lemma eAll_chunks : eAll = eC0 ++ eC1 ++ eC2 ++ eC3 ++ eC4 ++ eC5 ++ eC6 ++ eC7 := rfl

lemma mem_chunks {z : ℕ} (hz : z ∈ eAll) :
    ((((((z ∈ eC0 ∨ z ∈ eC1) ∨ z ∈ eC2) ∨ z ∈ eC3) ∨ z ∈ eC4) ∨ z ∈ eC5) ∨ z ∈ eC6) ∨ z ∈ eC7 := by
  rw [eAll_chunks] at hz
  simpa only [List.mem_append] using hz

/-! ### Extraction of the data facts from the kernel checks -/

/-- The two facts about a code of a chunk of `eAll` supplied by `eChunkOK` and `eBoundOK`: the code has
a nonzero `eM`-value, its N-representative number is `< 611`, and it is `ν_sc · rep_t` with
`sc = (em z - 1) % 32`, `t = (em z - 1) / 32`. -/
lemma chunk_data (l : List ℕ) (hc : eChunkOK cmT eM nT repT l = true) (hb : eBoundOK eM l = true) :
    ∀ z ∈ l, 1 ≤ em z ∧ (em z - 1) / 32 < 611 ∧
      actC cmT (ntab ((em z - 1) % 32)) (rp ((em z - 1) / 32)) = z := by
  intro z hz
  have h' := hc
  simp only [eChunkOK, allL_iff] at h'
  have hz' := h' z hz
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hz'
  have hb' := hb
  simp only [eBoundOK, allL_iff, Nat.blt_eq] at hb'
  exact ⟨Nat.one_le_iff_ne_zero.mpr (not_beq_zero_eq_true.mp hz'.1.2), hb' z hz, hz'.2⟩

/-- `repSelfOK`: every representative number `t < 611` is a code of `eAll` with `em (rp t) = 32 t + 1`. -/
lemma repSelf_data (t : ℕ) (ht : t < 611) : rp t < 10368 ∧ em (rp t) = 32 * t + 1 := by
  have h' := repself_ok
  simp only [repSelfOK, allL_iff, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.mem_range] at h'
  exact h' t ht

/-- `repInvOK`: the sign flips do not change the representative number of `rp t`. -/
lemma repInv_data (t : ℕ) (ht : t < 611) (sc : ℕ) (hsc : sc < 32) :
    (em (actC cmT (ntab sc) (rp t)) - 1) / 32 = t := by
  have h' := repinv_ok
  simp only [repInvOK, allL_iff, allR_iff, Nat.beq_eq, List.mem_range] at h'
  exact h' t ht sc hsc

/-- `eExactOK`: on `z < 10368` the `eM`-value does not vanish exactly on the codes of `eAll`. -/
lemma mem_eAll_of_em_ne_zero {z : ℕ} (hz : z < 10368) (h : em z ≠ 0) : z ∈ eAll := by
  have h0 := eexact_ok
  unfold eExactOK at h0
  have h1 : eqL ((List.range 10368).filter (fun c => !(Nat.beq (eG eM c) 0))) (msortK 40 eAll) = true :=
    (Bool.and_eq_true _ _).mp h0 |>.1
  have hlist : (List.range 10368).filter (fun c => !(Nat.beq (eG eM c) 0)) = msortK 40 eAll :=
    (eqL_iff _ _).mp h1
  have hmem : z ∈ msortK 40 eAll := by
    rw [← hlist, List.mem_filter]
    exact ⟨List.mem_range.mpr hz, not_beq_zero_eq_true.mpr h⟩
  exact (msortK_perm 40 eAll).mem_iff.mp hmem

end NSemAux

open NSemAux

theorem nSem : NSem := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases mem_chunks hz with ((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7
    · exact chunk_data eC0 echunk_ok0 ebound_ok0 z h0
    · exact chunk_data eC1 echunk_ok1 ebound_ok1 z h1
    · exact chunk_data eC2 echunk_ok2 ebound_ok2 z h2
    · exact chunk_data eC3 echunk_ok3 ebound_ok3 z h3
    · exact chunk_data eC4 echunk_ok4 ebound_ok4 z h4
    · exact chunk_data eC5 echunk_ok5 ebound_ok5 z h5
    · exact chunk_data eC6 echunk_ok6 ebound_ok6 z h6
    · exact chunk_data eC7 echunk_ok7 ebound_ok7 z h7
  · intro t ht
    have hr := repSelf_data t ht
    exact ⟨mem_eAll_of_em_ne_zero hr.1 (by rw [hr.2]; omega), hr.2⟩
  · intro t ht sc hsc
    exact repInv_data t ht sc hsc

end Work.PTCert
