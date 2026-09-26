import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.RedWDefs
import Submission.Work.PTCert.WordModel
import Submission.Work.PTCert.redWStack
import Submission.Work.PTCert.decPMap

/-!
# **(GL7)** Free reduction is canonical: `redWCanonical`

`Submission.PTCert.redW` reduces a `ℕ`-word of the `PTCert` word model by the stack algorithm
`foldl redStep []` (followed by a reversal), and `Submission.PTCert.evalW` evaluates a word in the
free group on `Fin r` by reading the letter `c` as the generator `c / 2` raised to the parity of `c`.

The lemma proved here says that on words whose letters are all `< 2 * r` (i.e. words that the model
really interprets as words in the free group, with no letter collapsed to `1`), `redW` is a function
of the group element: `evalW u = evalW v → redW u = redW v`.

The proof is Mathlib's free-group reduction theory, routed through the explicit decoding
`decP r hr c = (⟨c / 2, _⟩, c % 2 == 0)` of a letter as a Mathlib free-group letter.

* `wc_wv_eq_mk`, `wc_evalW_eq_mk`: on letters `< 2r` the evaluation is `FreeGroup.mk` of the
  decoded word;
* `Work.PTCert.redWStack` (imported): every letter of `redW w` occurs in `w`, and `redW w` is
  reduced (`RedP`);
* `Work.PTCert.decPMap` (imported): decoding carries `RedP` to `FreeGroup.IsReduced`, and is
  injective on words with letters `< 2r`.

Given `evalW u = evalW v`, the decoded words have the same `FreeGroup.mk`. Since `FreeGroup.reduce`
is invariant under `mk` (`FreeGroup.reduce.sound`) and fixes reduced words
(`FreeGroup.IsReduced.reduce_eq`), the decoded words are the two maximal reductions, hence equal;
the injectivity of decoding recovers `redW u = redW v`.

The case `r = 0` is degenerate: the hypotheses force `u = v = []`.
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- For a letter `c < 2r` the decoder is in its "in range" branch. -/
theorem wc_decP_of {r : ℕ} (hr : 0 < r) {c : ℕ} (hc : c < 2 * r) :
    decP r hr c = (⟨c / 2, by omega⟩, c % 2 == 0) := by
  unfold decP
  rw [dif_pos (by omega : c / 2 < r)]

/-- The evaluation of a single letter `c < 2r` is the free-group letter it decodes to. -/
theorem wc_wv_eq_mk {r : ℕ} (hr : 0 < r) {c : ℕ} (hc : c < 2 * r) :
    wv r c = FreeGroup.mk [decP r hr c] := by
  unfold wv
  rw [dif_pos (by omega : c / 2 < r), wc_decP_of hr hc]
  rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
  · rw [h2]; simp [FreeGroup.of]
  · rw [h2]; simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

/-- On words whose letters are all `< 2r` the evaluation is `FreeGroup.mk` of the decoded word. -/
theorem wc_evalW_eq_mk {r : ℕ} (hr : 0 < r) (w : List ℕ) (hw : ∀ c ∈ w, c < 2 * r) :
    evalW (r := r) w = FreeGroup.mk (w.map (decP r hr)) := by
  induction w with
  | nil => simp [evalW_eq, FreeGroup.one_eq_mk]
  | cons c t ih =>
    rw [evalW_cons, List.map_cons, ih (fun x hx => hw x (List.mem_cons_of_mem c hx)),
        wc_wv_eq_mk hr (hw c (by simp))]
    rw [FreeGroup.mul_mk, List.singleton_append]

/-- **(GL7) Free reduction is canonical.** -/
theorem redWCanonical : RedWCanonical := by
  intro r u v hu hv hev
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · -- `r = 0`: there are no letters `< 0`, so both words are empty
    subst h0
    have hu' : u = [] := by
      rcases u with _ | ⟨a, t⟩
      · rfl
      · exact absurd (hu a (by simp)) (by omega)
    have hv' : v = [] := by
      rcases v with _ | ⟨a, t⟩
      · rfl
      · exact absurd (hv a (by simp)) (by omega)
    rw [hu', hv']
  · have hmu : evalW (r := r) u = FreeGroup.mk (u.map (decP r hr)) := wc_evalW_eq_mk hr u hu
    have hmv : evalW (r := r) v = FreeGroup.mk (v.map (decP r hr)) := wc_evalW_eq_mk hr v hv
    have hmk : FreeGroup.mk (u.map (decP r hr)) = FreeGroup.mk (v.map (decP r hr)) := by
      rw [← hmu, ← hmv]; exact hev
    have hred : FreeGroup.reduce (u.map (decP r hr)) = FreeGroup.reduce (v.map (decP r hr)) :=
      FreeGroup.reduce.sound hmk
    -- the reduced words of `u` and `v` stay in range
    have hmemu : ∀ c ∈ Submission.PTCert.redW u, c < 2 * r :=
      fun c hc => hu c (redWStack.1 u c hc)
    have hmemv : ∀ c ∈ Submission.PTCert.redW v, c < 2 * r :=
      fun c hc => hv c (redWStack.1 v c hc)
    have hRu : FreeGroup.IsReduced ((Submission.PTCert.redW u).map (decP r hr)) :=
      (decPMap r hr).1 (l := Submission.PTCert.redW u) hmemu (redWStack.2 u)
    have hRv : FreeGroup.IsReduced ((Submission.PTCert.redW v).map (decP r hr)) :=
      (decPMap r hr).1 (l := Submission.PTCert.redW v) hmemv (redWStack.2 v)
    -- `redW` does not change the group element
    have hmkRu : FreeGroup.mk ((Submission.PTCert.redW u).map (decP r hr))
        = FreeGroup.mk (u.map (decP r hr)) := by
      rw [← wc_evalW_eq_mk hr (Submission.PTCert.redW u) hmemu, ← hmu, evalW_redW]
    have hmkRv : FreeGroup.mk ((Submission.PTCert.redW v).map (decP r hr))
        = FreeGroup.mk (v.map (decP r hr)) := by
      rw [← wc_evalW_eq_mk hr (Submission.PTCert.redW v) hmemv, ← hmv, evalW_redW]
    -- both decoded reduced words are the maximal reduction
    have e1 : (Submission.PTCert.redW u).map (decP r hr)
        = FreeGroup.reduce (u.map (decP r hr)) := by
      have h := FreeGroup.reduce.sound hmkRu
      rwa [FreeGroup.IsReduced.reduce_eq hRu] at h
    have e2 : (Submission.PTCert.redW v).map (decP r hr)
        = FreeGroup.reduce (v.map (decP r hr)) := by
      have h := FreeGroup.reduce.sound hmkRv
      rwa [FreeGroup.IsReduced.reduce_eq hRv] at h
    have hmap : (Submission.PTCert.redW u).map (decP r hr)
        = (Submission.PTCert.redW v).map (decP r hr) := by
      rw [e1, hred, e2]
    exact (decPMap r hr).2 hmemu hmemv hmap

end Work.PTCert
