import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.eAux
import Submission.Work.PTCert.eCmSound
import Submission.Work.PTCert.eExactFacts
import Submission.Work.PTCert.eChunkMem
import Submission.Work.PTCert.eInjFacts
import Submission.Work.PTCert.eClosure

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
for allL/allR/allIdx by induction), then instantiate". Write small reusable lemmas (e.g. `allL_iff_eAux`, `allR_iff_eAux`,
`allIdx_iff`, `eqL_iff_eAux`, `strictInc → Nodup/Sorted`) in your own helper file first.
Checks used: C.cm_ok (cmOK cmT), C.eexact_ok (eExactOK eM eAll), C.efaith_ok (eFaithfulOK eAll), C.ecompl_ok{0,1,2}
(eCompleteOK on letter chunks [0..26],[27..53],[54..80]), C.echunk_ok{0..7} (eChunkOK on eC0..eC7).
- CmSound: cmOK ⇒ for a,b < 81 with commB, modelEq 5 [a,b] [b,a] = true ⇒ (modelSound 5) lprod equal ⇒ b1 a * b1 b = b1 b * b1 a.
- eAll = eC0 ++ … ++ eC7 (emitter chunks of 600) — prove it once.
- letters/normal form: eChunkOK gives z < 10368, z%128 < 81, z/128 < 81, normC cmT (z/128) (z%128) = z, eG eM z ≠ 0.
- Nodup: eExactOK: strictInc (msortK 40 eAll) and msortK is a permutation (permCheckKSound.lean: msortK_perm);
  strictly increasing ⇒ Nodup; Perm preserves Nodup.
- closure: eCompleteOK: eG eM (normC cmT a b) ≠ 0 for a,b < 81; normC output < 10368; then the membership ↔.
- membership ↔ (z < 10368): eExactOK's first conjunct: (List.range 10368).filter (em ≠ 0) = msortK 40 eAll,
  so em z ≠ 0 ↔ z ∈ msortK 40 eAll ↔ z ∈ eAll.
- injectivity: eFaithfulOK: strictInc (msortK 40 (eAll.map modelKey)) ⇒ modelKey injective on eAll;
  ModelKeyFaithful (hMK): eltC z = eltC z' ⇒ modelKey z = modelKey z' (with a = z/128 etc., z = 128·(z/128) + z%128).

## Actual proof (this file)

`ESem` is the conjunction of six facts about the emitted data.  Each is a consequence of one
kernel check, proved in a separate module (see `NOTES_LEAD_glue.md` and `eAux.lean`):

* `eCmSound : CmSound cmT` — from `C.cm_ok` and `modelSound 5`;
* `eExactFacts C.eexact_ok : eAll.Nodup ∧ ∀ z < 10368, z ∈ eAll ↔ em z ≠ 0` — from `C.eexact_ok`;
* `eChunkMem : ∀ z ∈ eAll, z < 10368 ∧ z % 128 < 81 ∧ z / 128 < 81 ∧ normC cmT (z/128) (z%128) = z`
  — from `C.echunk_ok{0..7}` and `eAll = eC0 ++ … ++ eC7`;
* `eClosure : ∀ a < 81, ∀ b < 81, normC cmT a b ∈ eAll` — from `C.ecompl_ok{0,1,2}` and the
  membership characterisation (output of `normC` is `< 10368`);
* `eInjFacts hMK : eltC` is injective on `eAll` — from `C.efaith_ok` (the model key is injective on
  `eAll`, `modelKeyFaithful.lean`) and the hypothesis `ModelKeyFaithful` (`hMK`).

This file only assembles them.
-/

set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

theorem eSem (hMK : ModelKeyFaithful) : ESem := by
  obtain ⟨hnodup, hmem⟩ := eExactFacts eexact_ok
  have hlb : ∀ z ∈ eAll, z / 128 < 81 ∧ z % 128 < 81 := by
    intro z hz
    obtain ⟨_, hb, ha, _⟩ := eChunkMem z hz
    exact ⟨ha, hb⟩
  refine ⟨eCmSound, hnodup, ?_, ?_, ?_, hmem⟩
  · intro z hz
    obtain ⟨_, hb, ha, hc⟩ := eChunkMem z hz
    exact ⟨ha, hb, hc⟩
  · exact eClosure hmem
  · exact eInjFacts hMK hlb

end Work.PTCert
