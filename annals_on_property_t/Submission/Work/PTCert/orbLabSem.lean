import Mathlib
import Submission.Work.PTCert.Checks.SharedAll

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
for allL/allR/allIdx by induction), then instantiate. Write small reusable lemmas (e.g. `allL_iff`, `allR_iff`,
`allIdx_iff`, `eqL_iff`, `strictInc → Nodup/Sorted`) in your own helper file first.
Checks: C.ol_ok{r}_{j} (orbLabOK cmT nT repT olT{r} labOf ts) for r < 18 and rep chunks [0..205], [206..411],
[412..610]; labOf = lab0 eM repInfoT for r = 0 and lG labT{r} for r ≥ 1 (= labE r). olTs.getD r = olT{r}.
orbLabOK: ∀ t ∈ ts, ∀ sc < 32 (allR 32), ((olT.get t >>> (11 * sc)) &&& 2047) = labOf (actC cmT (nT.get sc) (cG repT t)).

Proof note (this file): the three chunk checks of row `r` cover `{0,…,610} = [0..205] ∪ [206..411] ∪ [412..610]`,
and on row `r` the `labOf` argument of the check is definitionally `labE r` (`lab0 eM repInfoT` for `r = 0`,
`lG labT{r}` otherwise), while `olT{r}` is `olTs.getD r (NT.leaf 0)`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## Helpers: the meaning of the `allL`/`allR` combinators and of `orbLabOK` -/

/-- `allL l p = true` says that `p` holds on every element of `l`. -/
private lemma allL_iff (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    rw [show allL (a :: t) p = (p a && allL t p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨ha, ht⟩ b hb
      rcases List.mem_cons.mp hb with h | h
      · subst h; exact ha
      · exact ht b h
    · intro h
      exact ⟨h a (by simp), fun b hb => h b (by simp [hb])⟩

/-- `allR n p = true` says that `p k` holds for every `k < n`. -/
private lemma allR_iff (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    rw [show allR (n + 1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, ht⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact ht k h
      · subst h; exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- The plain meaning of `orbLabOK`: for every entry `t` of `ts`, the `sc`-th field (`sc < 32`, `11` bits)
of `olT.get t` is the label of `ν_sc · rep_t`. -/
private lemma orbLabOK_iff (olT : NT) (labOf : ℕ → ℕ) (ts : List ℕ) :
    orbLabOK cmT nT repT olT labOf ts = true ↔
      ∀ t ∈ ts, ∀ sc < 32,
        ((olT.get t >>> (11 * sc)) &&& 2047) = labOf (actC cmT (nT.get sc) (cG repT t)) := by
  rw [show orbLabOK cmT nT repT olT labOf ts =
      allL ts (fun t => let v := olT.get t
        allR 32 (fun sc => Nat.beq ((v >>> (11 * sc)) &&& 2047)
          (labOf (actC cmT (nT.get sc) (cG repT t))))) from rfl]
  rw [allL_iff]
  constructor
  · intro h t ht sc hsc
    have h2 : allR 32 (fun sc => Nat.beq ((olT.get t >>> (11 * sc)) &&& 2047)
        (labOf (actC cmT (nT.get sc) (cG repT t)))) = true := h t ht
    rw [allR_iff] at h2
    exact Nat.beq_eq.mp (h2 sc hsc)
  · intro h a ha
    have h2 : ∀ sc < 32, Nat.beq ((olT.get a >>> (11 * sc)) &&& 2047)
        (labOf (actC cmT (nT.get sc) (cG repT a))) = true :=
      fun sc hsc => Nat.beq_eq.mpr (h a ha sc hsc)
    rw [allR_iff]
    exact h2

/-- Three chunk checks (`t ∈ [0,205]`, `t ∈ [206,411]`, `t ∈ [412,610]`) cover all `t < 611`. -/
private lemma orbLabSem_aux (olT : NT) (labOf : ℕ → ℕ)
    (h0 : orbLabOK cmT nT repT olT labOf (List.range 206) = true)
    (h1 : orbLabOK cmT nT repT olT labOf (List.range' 206 206) = true)
    (h2 : orbLabOK cmT nT repT olT labOf (List.range' 412 199) = true) :
    ∀ t < 611, ∀ sc < 32,
      ((olT.get t >>> (11 * sc)) &&& 2047) = labOf (actC cmT (nT.get sc) (cG repT t)) := by
  rw [orbLabOK_iff] at h0 h1 h2
  intro t ht sc hsc
  rcases lt_or_ge t 206 with h | h
  · exact h0 t (List.mem_range.mpr h) sc hsc
  rcases lt_or_ge t 412 with h' | h'
  · refine h1 t ?_ sc hsc
    rw [List.mem_range']
    exact ⟨t - 206, by omega, by omega⟩
  · refine h2 t ?_ sc hsc
    rw [List.mem_range']
    exact ⟨t - 412, by omega, by omega⟩

/-! ## The statement -/

theorem orbLabSem : OrbLabSem := by
  intro r hr
  interval_cases r
  · exact orbLabSem_aux olT0 (lab0 eM repInfoT) ol_ok0_0 ol_ok0_1 ol_ok0_2
  · exact orbLabSem_aux olT1 (lG labT1) ol_ok1_0 ol_ok1_1 ol_ok1_2
  · exact orbLabSem_aux olT2 (lG labT2) ol_ok2_0 ol_ok2_1 ol_ok2_2
  · exact orbLabSem_aux olT3 (lG labT3) ol_ok3_0 ol_ok3_1 ol_ok3_2
  · exact orbLabSem_aux olT4 (lG labT4) ol_ok4_0 ol_ok4_1 ol_ok4_2
  · exact orbLabSem_aux olT5 (lG labT5) ol_ok5_0 ol_ok5_1 ol_ok5_2
  · exact orbLabSem_aux olT6 (lG labT6) ol_ok6_0 ol_ok6_1 ol_ok6_2
  · exact orbLabSem_aux olT7 (lG labT7) ol_ok7_0 ol_ok7_1 ol_ok7_2
  · exact orbLabSem_aux olT8 (lG labT8) ol_ok8_0 ol_ok8_1 ol_ok8_2
  · exact orbLabSem_aux olT9 (lG labT9) ol_ok9_0 ol_ok9_1 ol_ok9_2
  · exact orbLabSem_aux olT10 (lG labT10) ol_ok10_0 ol_ok10_1 ol_ok10_2
  · exact orbLabSem_aux olT11 (lG labT11) ol_ok11_0 ol_ok11_1 ol_ok11_2
  · exact orbLabSem_aux olT12 (lG labT12) ol_ok12_0 ol_ok12_1 ol_ok12_2
  · exact orbLabSem_aux olT13 (lG labT13) ol_ok13_0 ol_ok13_1 ol_ok13_2
  · exact orbLabSem_aux olT14 (lG labT14) ol_ok14_0 ol_ok14_1 ol_ok14_2
  · exact orbLabSem_aux olT15 (lG labT15) ol_ok15_0 ol_ok15_1 ol_ok15_2
  · exact orbLabSem_aux olT16 (lG labT16) ol_ok16_0 ol_ok16_1 ol_ok16_2
  · exact orbLabSem_aux olT17 (lG labT17) ol_ok17_0 ol_ok17_1 ol_ok17_2

end Work.PTCert
