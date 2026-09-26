import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.codeFacts

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
for allL/allR/allIdx by induction), then instantiate". Write small reusable lemmas (e.g. `allL_iff_tabSem`, `allR_iff_tabSem`,
`allIdx_iff_tabSem`, `eqL_iff`, `strictInc → Nodup/Sorted`) in your own helper file first.
Checks: C.ntab_ok (tabsOK nCodes nT), C.pitab_ok (tabsOK piCodes piT), C.piitab_ok (tabsOK piICodes piIT),
C.piinv_ok (piInvOK piT piIT 120). `tabsOK codes T` = ∀ i, tabOK (c/32) (c%32) (T.get i) for c = codes[i]:
validPC, sc < 32, lk tab k = actL 5 pc sc k for k < 81.
- sign flips: nCodes[sc] = 32 * idPC 5 + sc (small decide: nCodes has 32 entries) and CodeFacts: codeElt of it is
  sigAut 1 (scBits sc) = signAut (scBits sc) (permAut 1 = 1) and acts by actL; TabOf follows. Values < 81 by CodeFacts.
- π tables similarly with codeElt (piCodes[i]) directly; piCodes[i] % 32 = 0 (decide on the 120-list).
- inverse tables: piInvOK ⇒ lk t (lk t' k) = k and lk t' (lk t k) = k for k < 81 (t = piT.get i, t' = piIT.get i).
  Then TabOf σ⁻¹ t': σ⁻¹ b1 k σ = b1 (lk t' k) ⟸ σ b1 (lk t' k) σ⁻¹ = b1 (lk t (lk t' k)) = b1 k.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## Soundness of the `Bool` check combinators (`KernelShared`, `Kernel`) as `Prop`s

These turn `&&` / `allR` / `allL` / `allIdx` / `Nat.beq` / `Nat.blt` / `List.all` into `∀ ∧ =`,
following the design notes; they are the only place where the kernel checks are unfolded. -/

/-- `allR n p` means `p k` for all `k < n`. -/
lemma allR_iff_tabSem (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n + 1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hpn, hlt⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact hlt k h
      · subst h; exact hpn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- `allL l p` means `p a` for all `a ∈ l`. -/
lemma allL_iff_tabSem (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    rw [show allL (a :: t) p = (p a && allL t p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hpa, htl⟩ b hb
      rcases List.mem_cons.mp hb with h | h
      · subst h; exact hpa
      · exact htl b h
    · intro h
      exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem a hb)⟩

/-- `allIdx l p i0` means `p (i0 + i) (l[i])` for all `i < l.length` (read with `getD`). -/
lemma allIdx_iff_tabSem (l : List ℕ) (p : ℕ → ℕ → Bool) (i0 : ℕ) :
    allIdx l p i0 = true ↔ ∀ i < l.length, p (i0 + i) (l.getD i 0) = true := by
  induction l generalizing i0 with
  | nil => simp [allIdx]
  | cons a t ih =>
    rw [show allIdx (a :: t) p i0 = (p i0 a && allIdx t p (i0 + 1)) from rfl, Bool.and_eq_true]
    constructor
    · rintro ⟨hpa, htl⟩ i hi
      rcases i with _ | j
      · simpa using hpa
      · have hj : j < t.length := by simpa using hi
        rw [List.getD_cons_succ, show i0 + (j + 1) = (i0 + 1) + j from by omega]
        exact (ih (i0 + 1)).mp htl j hj
    · intro h
      refine ⟨?_, (ih (i0 + 1)).mpr ?_⟩
      · simpa using h 0 (by simp)
      · intro j hj
        have hh := h (j + 1) (by simpa using hj)
        rw [List.getD_cons_succ, show i0 + (j + 1) = (i0 + 1) + j from by omega] at hh
        exact hh

/-- Meaning of one letter-table check `tabOK pc sc tab`. -/
lemma tabOK_iff (pc sc tab : ℕ) :
    tabOK pc sc tab = true ↔ validPC 5 pc = true ∧ sc < 32 ∧ ∀ k < 81, lk tab k = actL 5 pc sc k := by
  unfold tabOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true]
  exact ⟨fun h => ⟨h.1.1, h.1.2, fun k hk => Nat.beq_eq.mp (h.2 k (List.mem_range.mpr hk))⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, fun k hk => Nat.beq_eq.mpr (h.2.2 k (List.mem_range.mp hk))⟩⟩

/-- Extraction of the `i`-th `tabOK` fact from `tabsOK codes T`. -/
lemma tabsOK_ith (codes : List ℕ) (T : NT) (i : ℕ) (h : i < codes.length)
    (hchk : tabsOK codes T = true) :
    tabOK (codes.getD i 0 / 32) (codes.getD i 0 % 32) (T.get i) = true := by
  have := (allIdx_iff_tabSem codes (fun i c => tabOK (c / 32) (c % 32) (T.get i)) 0).mp hchk i h
  simpa using this

/-- Meaning of the mutual-inverse letter-table check `invTabOK t t'`. -/
lemma invTabOK_iff (t t' : ℕ) :
    invTabOK t t' = true ↔ ∀ k < 81, lk t (lk t' k) = k ∧ lk t' (lk t k) = k := by
  unfold invTabOK
  rw [allR_iff_tabSem]
  exact ⟨fun h k hk => by
      have hh := h k hk
      rw [Bool.and_eq_true] at hh
      exact ⟨Nat.beq_eq.mp hh.1, Nat.beq_eq.mp hh.2⟩,
    fun h k hk => by
      rw [Bool.and_eq_true]
      exact ⟨Nat.beq_eq.mpr (h k hk).1, Nat.beq_eq.mpr (h k hk).2⟩⟩

/-- Extraction of `piInvOK` at the index `i < 120`. -/
lemma piInvOK_ith (i : ℕ) (h : i < 120) : invTabOK (piT.get i) (piIT.get i) = true :=
  (allR_iff_tabSem 120 (fun i => invTabOK (piT.get i) (piIT.get i))).mp C.piinv_ok i h

/-- **(GL, generic)** A letter table `t'` that is a left inverse of a letter table `t` of `σ`
gives a letter table of `σ⁻¹`: `σ⁻¹ b₁ k σ = b₁ (lk t' k)` because
`σ b₁ (lk t' k) σ⁻¹ = b₁ (lk t (lk t' k)) = b₁ k`. -/
lemma tabOf_inv (σ : G5) (t t' : ℕ) (h : TabOf σ t) (hb : ∀ k < 81, lk t' k < 81)
    (hinv : ∀ k < 81, lk t (lk t' k) = k) : TabOf σ⁻¹ t' := by
  intro k hk
  have h1 : σ * b1 5 (lk t' k) * σ⁻¹ = b1 5 k := by
    rw [h (lk t' k) (hb k hk), hinv k hk]
  rw [inv_inv, ← h1]
  group

/-! ## Small computations on the emitted data (allowed: `nCodes` has `32`, `piCodes` has `120`
entries).  `nCodes = [32 * 18056 + sc]_{sc < 32}` with `18056 = idPC 5`, and the π-codes are
multiples of `32` (sign code `0`). -/

/-- The base-8 digits of `18056 = idPC 5` are the identity permutation. -/
lemma pdig_18056 (i : Fin 5) : pdig 18056 i.val = i.val := by fin_cases i <;> decide +kernel

/-- `18056` is a valid permutation code. -/
lemma validPC_18056 : validPC 5 18056 = true := by decide +kernel

lemma nCodes_len : nCodes.length = 32 := by decide +kernel
lemma piCodes_len : piCodes.length = 120 := by decide +kernel
lemma piICodes_len : piICodes.length = 120 := by decide +kernel

/-- The `N`-codes are `32 * idPC 5 + sc`. -/
lemma nCodes_getD (sc : ℕ) (hsc : sc < 32) : nCodes.getD sc 0 = 32 * 18056 + sc := by
  have h : ((List.range 32).all (fun i => Nat.beq (nCodes.getD i 0) (32 * 18056 + i))) = true := by
    decide +kernel
  exact Nat.beq_eq.mp (List.all_eq_true.mp h sc (List.mem_range.mpr hsc))

/-- The π-codes are multiples of `32` (trivial sign code). -/
lemma piCodes_mod (i : ℕ) (hi : i < 120) : piCodes.getD i 0 % 32 = 0 := by
  have h : ((List.range 120).all (fun i => Nat.beq (piCodes.getD i 0 % 32) 0)) = true := by
    decide +kernel
  exact Nat.beq_eq.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))

/-- With `p = 1` and `pc = idPC 5`, the signed permutation `sigAut 1 (scBits sc)` of
`letterActionPerm` is the sign flip `signAut (scBits sc)`. -/
lemma sigAut_one_eq_signAut (sc : ℕ) :
    sigAut (1 : Equiv.Perm (Fin 5)) (fun i => decide (sbit sc i.val = 1)) = signAut (scBits sc) := by
  rw [sigAut, Submission.RouteB.permAut_one, mul_one]
  rfl

/-! ## The tables -/

theorem tabSem (hCF : CodeFacts) : TabSem := by
  obtain ⟨hCF1, -, -, -, -⟩ := hCF
  refine ⟨?_, ?_⟩
  · -- the sign-flip tables `ntab sc`: `nCodes[sc]` has permutation code `18056 = idPC 5`
    intro sc hsc
    have hchk : tabOK (nCodes.getD sc 0 / 32) (nCodes.getD sc 0 % 32) (ntab sc) = true :=
      tabsOK_ith nCodes nT sc (by rw [nCodes_len]; exact hsc) C.ntab_ok
    rw [nCodes_getD sc hsc, thirtytwo_div 18056 sc hsc, thirtytwo_mod 18056 sc hsc] at hchk
    obtain ⟨hvpc, -, hlk⟩ := (tabOK_iff 18056 sc (ntab sc)).mp hchk
    constructor
    · intro k hk
      have hLA := Work.PTCert.codeFactsAux.letterActionPerm 5 18056 sc 1 hvpc
        (fun i => (pdig_18056 i).symm) k hk
      rw [hlk k hk, ← sigAut_one_eq_signAut sc]
      exact hLA
    · intro k hk
      rw [hlk k hk]
      exact Work.PTCert.codeFactsAux.actLBound 18056 sc hvpc k hk
  · -- the row-transport tables `piT i` / their inverses `piIT i`
    intro i hi
    have hchkT : tabOK (piCodes.getD i 0 / 32) (piCodes.getD i 0 % 32) (piT.get i) = true :=
      tabsOK_ith piCodes piT i (by rw [piCodes_len]; exact hi) C.pitab_ok
    have hchkI : tabOK (piICodes.getD i 0 / 32) (piICodes.getD i 0 % 32) (piIT.get i) = true :=
      tabsOK_ith piICodes piIT i (by rw [piICodes_len]; exact hi) C.piitab_ok
    obtain ⟨hvpc, -, hlk⟩ :=
      (tabOK_iff (piCodes.getD i 0 / 32) (piCodes.getD i 0 % 32) (piT.get i)).mp hchkT
    obtain ⟨hvpcI, -, hlkI⟩ :=
      (tabOK_iff (piICodes.getD i 0 / 32) (piICodes.getD i 0 % 32) (piIT.get i)).mp hchkI
    obtain ⟨-, hb1⟩ := hCF1 (piCodes.getD i 0) hvpc
    obtain ⟨-, hb2⟩ := hCF1 (piICodes.getD i 0) hvpcI
    have hTabT : TabOf (codeElt (piCodes.getD i 0)) (piT.get i) := by
      intro k hk
      rw [hlk k hk]
      exact (hb1 k hk).2
    have hinv : ∀ k < 81, lk (piT.get i) (lk (piIT.get i) k) = k :=
      fun k hk => ((invTabOK_iff (piT.get i) (piIT.get i)).mp (piInvOK_ith i hi) k hk).1
    have hTabI : TabOf (codeElt (piCodes.getD i 0))⁻¹ (piIT.get i) :=
      tabOf_inv _ _ _ hTabT (fun k hk => by rw [hlkI k hk]; exact (hb2 k hk).1) hinv
    refine ⟨hvpc, piCodes_mod i hi, hTabT, hTabI, fun k hk => ⟨?_, ?_⟩⟩
    · rw [hlk k hk]; exact (hb1 k hk).1
    · rw [hlkI k hk]; exact (hb2 k hk).1

end Work.PTCert
