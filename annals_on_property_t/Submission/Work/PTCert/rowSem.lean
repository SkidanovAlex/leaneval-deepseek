import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.rowHelp
import Submission.Work.PTCert.nSem
import Submission.Work.PTCert.tabSem
import Submission.Work.PTCert.scanRowMem
import Submission.Work.PTCert.stabLScan
import Submission.Work.PTCert.stabTabFacts
import Submission.Work.PTCert.x0cMem
import Submission.Work.PTCert.lab0Lt
import Submission.Work.PTCert.cntFacts

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
Checks: C.rowself_ok, C.rowidx_ok, C.reprow_ok, C.cnt_ok, C.pc_ok (eqL allPCk pcL), C.scan_ok{r}, C.stabtab_ok{r}
(r = 1..17), C.eexact_ok for memberships.
- x0c 0 = 0 and the row codes: small facts (18 values) — `decide +kernel` on `cG rowT r` for r < 18 is fine.
- labE 0 = lab0 eM repInfoT (labOf with r = 0).
- counts: cntOK uses countL (a List.rec count) — relate to List.filter length.
- scan: `scanRow cmT rowIdxT a b x0 pcL = stabL r` (a, b the letters of x0). Prove a general lemma about scanRow:
  its output lists, for pc ∈ pcL (in order) and sc = 31 … 0 (Nat.rec order), the code 32 pc + sc when the
  image y := normC cmT (actL 5 pc sc a) (actL 5 pc sc b) equals x0, and a 0 when y ≠ x0 but rG rowIdx y ≠ 0.
  Hence: c ∈ stabL ↔ (c valid ∧ actCode c x0 = x0) — every valid c is 32 pc + sc with pc ∈ allPCk = pcL
  (allPCk = filter validPC (range 32768)); and no 0 occurs in stabL (0 is not a valid code: validPC 5 0 = false),
  so for every valid c, rG rowIdxT (actCode c x0) ≠ 0 → actCode c x0 = x0; with rowIdxOK (rowIdx (x0c r') = r' + 1 ≠ 0)
  this gives the ↔ and the "another row ⇒ same row" clause (rows have distinct codes by rowSelfOK labels).
- stabiliser tables: tabsOK stabL stabT.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## Local helpers -/

/-- A valid permutation code is below `8^r`. -/
private theorem validPC_lt {r pc : ℕ} (h : validPC r pc = true) : pc < 8 ^ r := by
  rw [validPC, Bool.and_eq_true, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp h.2

/-- The two facts about the row codes supplied by `rowSelfOK`. -/
private theorem rowSelf_facts (r : ℕ) (hr : r < 18) :
    lab0 eM repInfoT (cG rowT r) = r ∧ cG rowT r < 10368 ∧ eG eM (cG rowT r) ≠ 0 := by
  have h0 : rowSelfOK eM rowT repInfoT 18 = true := C.rowself_ok
  unfold rowSelfOK at h0
  have h := (allR_eq_true 18 _).mp h0 r hr
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.beq_eq.mp h.1.1, Nat.blt_eq.mp h.1.2, NSemAux.not_beq_zero_eq_true.mp h.2⟩

/-- The row transport of the representatives, from `repRowOK`. -/
private theorem repRow_facts (t : ℕ) (ht : t < 611) :
    actC cmT (piT.get (rinfo t % 128)) (cG rowT (rinfo t / 128)) = rp t := by
  have h0 : repRowOK cmT piT rowT repT repInfoT (List.range 611) = true := C.reprow_ok
  unfold repRowOK at h0
  have h := (allL_eq_true _ _).mp h0 t (List.mem_range.mpr ht)
  exact Nat.beq_eq.mp h

/-- The row-index tree marks the row codes, from `rowIdxOK`. -/
private theorem rowIdx_facts (r : ℕ) (hr : r < 18) : rG rowIdxT (cG rowT r) = r + 1 := by
  have h0 : rowIdxOK rowT rowIdxT 18 = true := C.rowidx_ok
  unfold rowIdxOK at h0
  exact Nat.beq_eq.mp ((allR_eq_true 18 _).mp h0 r hr)

/-- No stabiliser list contains the sentinel `0` (so no valid code maps a row onto another row). -/
private theorem stabL_nozero (r : ℕ) (hr : r < 18) : 0 ∉ stabL r := by
  have h : allR 18 (fun r => allL (stabL r) (fun x => !(Nat.beq x 0))) = true := by
    decide +kernel
  have h2 := (allR_eq_true 18 _).mp h r hr
  intro hmem
  exact (NSemAux.not_beq_zero_eq_true.mp ((allL_eq_true _ _).mp h2 0 hmem)) rfl

/-- `labE` in row `0` is `lab0`. -/
private theorem labE_zero (z : ℕ) : labE 0 z = lab0 eM repInfoT z := rfl

/-- **The scan step**: for a valid code `c` and a row `r ≥ 1`, `c` fixes the row code exactly when
it is a stabiliser code, and no other row code can be hit. -/
private theorem stabSem (r : ℕ) (hr : r < 18) (hr1 : 1 ≤ r) (c : ℕ) (hc : validPC 5 (c / 32) = true) :
    (actCode c (cG rowT r) = cG rowT r ↔ c ∈ stabL r) ∧
    ∀ r' < 18, actCode c (cG rowT r) = cG rowT r' → r' = r := by
  have hstab : stabL r = scanRow cmT rowIdxT (cG rowT r / 128) (cG rowT r % 128) (cG rowT r) pcL :=
    stabLScan r hr hr1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Nat.zero_div, validPC_five_zero] at hc
    exact Bool.false_ne_true hc
  have hpc : c / 32 ∈ pcL := by
    rw [pcL_allPCk, allPCk, List.mem_filter]
    refine ⟨List.mem_range.mpr ?_, hc⟩
    have hlt := validPC_lt hc
    rw [show (8 : ℕ) ^ 5 = 32768 from by norm_num] at hlt
    exact hlt
  have hsc : c % 32 < 32 := Nat.mod_lt _ (by norm_num)
  -- a stabiliser code fixes the row code
  have hfix : c ∈ stabL r → actCode c (cG rowT r) = cG rowT r := by
    intro hmem
    rw [hstab] at hmem
    rcases (scanRowMem cmT rowIdxT (cG rowT r / 128) (cG rowT r % 128) (cG rowT r) pcL c).mp hmem with
      ⟨pc, -, sc, hsc', hy, hceq⟩ | ⟨h0, -⟩
    · have hcd : c / 32 = pc := by omega
      have hcm : c % 32 = sc := by omega
      have : actCode c (cG rowT r) =
          normC cmT (actL 5 pc sc (cG rowT r / 128)) (actL 5 pc sc (cG rowT r % 128)) := by
        unfold actCode
        rw [hcd, hcm]
      rw [this, hy]
    · exact absurd h0 hc0
  -- a code fixing the row code is a stabiliser code
  have hmem : actCode c (cG rowT r) = cG rowT r → c ∈ stabL r := by
    intro h
    rw [hstab]
    exact (scanRowMem cmT rowIdxT (cG rowT r / 128) (cG rowT r % 128) (cG rowT r) pcL c).mpr
      (Or.inl ⟨c / 32, hpc, c % 32, hsc, h, (Nat.div_add_mod c 32).symm⟩)
  refine ⟨⟨hmem, hfix⟩, ?_⟩
  intro r' hr' heq
  by_cases h : actCode c (cG rowT r) = cG rowT r
  · have hsame : cG rowT r' = cG rowT r := heq.symm.trans h
    have h1 : lab0 eM repInfoT (cG rowT r') = r' := (rowSelf_facts r' hr').1
    have h2 : lab0 eM repInfoT (cG rowT r) = r := (rowSelf_facts r hr).1
    rw [hsame] at h1
    rw [h2] at h1
    exact h1.symm
  · -- the image is another row code, so the scan pushes a `0`, contradicting `stabL_nozero`
    have hz : 0 ∈ stabL r := by
      rw [hstab]
      refine (scanRowMem cmT rowIdxT (cG rowT r / 128) (cG rowT r % 128) (cG rowT r) pcL 0).mpr
        (Or.inr ⟨rfl, c / 32, hpc, c % 32, hsc, ?_, ?_⟩)
      · change actCode c (cG rowT r) ≠ cG rowT r
        exact h
      · change rG rowIdxT (actCode c (cG rowT r)) ≠ 0
        rw [heq, rowIdx_facts r' hr']
        omega
    exact absurd hz (stabL_nozero r hr)

/-- The two label filters agree. -/
private theorem filter_label (r : ℕ) :
    eAll.filter (fun z => Nat.beq (lab0 eM repInfoT z) r) = eAll.filter (fun z => labE 0 z = r) := by
  refine filter_congr' fun z _ => ?_
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, decide_eq_true_eq, labE_zero]

/-! ## The theorem -/

theorem rowSem : RowSem := by
  unfold RowSem
  refine ⟨x0c_zero, x0cMem, ?_, ?_, ?_, ?_, ?_, stabTabFacts⟩
  · intro t ht
    exact ⟨rinfo_div t ht, rinfo_mod t ht, repRow_facts t ht⟩
  · intro r hr
    exact (rowSelf_facts r hr).1
  · intro z hz
    exact lab0Lt z hz
  · intro r hr
    rw [← filter_label r]
    exact cntFacts r hr
  · intro r hr hr1 c hc
    exact stabSem r hr hr1 c hc

end Work.PTCert
