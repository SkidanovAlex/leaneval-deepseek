import Mathlib
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtBijection
import Submission.Work.MainP.permOfGetD
import Submission.Work.MainP.invLabLab

/-!
# `Work.MainP.crtSorted` — the sorted label list is the CRT reindexing

The label-and-sort word that implements the Agarwal–Cooley reindexing (paper Prop 5.4 step (2))
labels the payload `xs[i]` with the key `lab.getD i 0`, sorts the resulting records by their key,
strips the keys and returns the payloads. This lemma identifies the result of that word: if `lab`
is injective on `[0,S)` with values `< S` (so `lab` is a permutation of `[0,S)`), then the `m`-th
payload of the sorted list is the payload of the record carrying the label `m`, i.e. `xs` read at
the position `invLab lab m`.

The argument, with `target` the list whose `m`-th entry is the record with key `m` and payload
`xs.getD (invLab lab m)`:

* `zipped := zipRec xs (labVals lab)` has `i`-th entry the record with key `lab.getD i 0` and
  payload `xs.getD i`; the map `i ↦ lab.getD i 0` is an injective self-map of `[0,S)`, hence a
  permutation `σ` of `Fin S` (`Work.MainP.crtBijection`), and the entry of `zipped` at `i` is the
  entry of `target` at `σ i` because `invLab` inverts `lab` (`Work.MainP.invLabLab`);
* hence `zipped ~ target` (`Work.MainP.permOfGetD`);
* `target` is sorted by `pairKey` (its keys are `0, 1, …, S-1`), and two permutations that are
  both strictly sorted by `pairKey` are equal (`List.Perm.eq_of_pairwise`), so `rs' = target`;
* reading the `m`-th entry of `rs' = target` gives the claim.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

theorem crtSorted {S : ℕ} {xs : List HvdH.Val} {lab : List ℕ}
    (hxs : xs.length = S) (hlab : lab.length = S)
    (hinj : ∀ i < S, ∀ j < S, lab.getD i 0 = lab.getD j 0 → i = j)
    (hlt : ∀ i < S, lab.getD i 0 < S)
    {rs' : List HvdH.Val}
    (hperm : rs'.Perm (Work.MainP.zipRec xs (Work.MainP.labVals lab)))
    (hsort : rs'.Pairwise fun a b => HvdH.pairKey a < HvdH.pairKey b) :
    ∀ m < S, (rs'.map Work.MainP.recPayload).getD m HvdH.Val.nil
      = xs.getD (Work.MainP.invLab lab m) HvdH.Val.nil := by
  -- the labelling `i ↦ lab.getD i 0` is a permutation of `[0,S)`
  obtain ⟨σ, hσ⟩ := crtBijection hinj hlt
  have hwlen : (labVals lab).length = S := by simpa [labVals] using hlab
  have hzlen : (zipRec xs (labVals lab)).length = S := by
    rw [zipRec_length (by rw [hxs, hwlen])]
    exact hxs
  -- the sorted target list: entry `m` is the record with key `m`
  let target : List Val :=
    (List.range S).map (fun k : ℕ => Val.cons (.int (k : ℤ)) (xs.getD (invLab lab k) .nil))
  have htarget_len : target.length = S := by simp [target]
  have htarget_get : ∀ j < S, target.getD j .nil
      = .cons (.int (j : ℤ)) (xs.getD (invLab lab j) .nil) := by
    intro j hj
    have hj' : j < (List.range S).length := by simpa using hj
    have hj'' : j < target.length := by rw [htarget_len]; exact hj
    rw [List.getD_eq_getElem _ _ hj'']
    simp only [target, List.getElem_map, List.getElem_range hj']
  have htarget_sorted : target.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) := by
    rw [show target = (List.range S).map
        (fun k : ℕ => Val.cons (.int (k : ℤ)) (xs.getD (invLab lab k) .nil)) from rfl,
      List.pairwise_map]
    refine List.Pairwise.imp (fun {a b} hab => ?_) List.pairwise_lt_range
    show HvdH.pairKey (Val.cons (.int (a : ℤ)) (xs.getD (invLab lab a) .nil))
      < HvdH.pairKey (Val.cons (.int (b : ℤ)) (xs.getD (invLab lab b) .nil))
    rw [pairKey_cons, pairKey_cons]
    exact_mod_cast hab
  -- the `i`-th record of `zipRec xs (labVals lab)`
  have hzget : ∀ i < S, (zipRec xs (labVals lab)).getD i .nil =
      .cons (.int ((lab.getD i 0 : ℕ) : ℤ)) (xs.getD i .nil) := by
    intro i hi
    rw [zipRec_getD (xs := xs) (ws := labVals lab) (by rw [hxs, hwlen]) (by rw [hxs]; exact hi),
      labVals_getD (by rw [hlab]; exact hi)]
  -- it is the record of `target` at position `lab.getD i 0 = σ i`
  have hper : ∀ i : Fin S, (zipRec xs (labVals lab)).getD (i : ℕ) .nil
      = target.getD ((σ i : Fin S) : ℕ) .nil := by
    intro i
    rw [hzget (i : ℕ) i.isLt, htarget_get ((σ i : Fin S) : ℕ) (σ i).isLt]
    have h1 : (((lab.getD (i : ℕ) 0 : ℕ) : ℤ)) = (((σ i : Fin S) : ℕ) : ℤ) := by rw [hσ i]
    have h2 : invLab lab ((σ i : Fin S) : ℕ) = (i : ℕ) := by
      rw [hσ i]
      exact invLabLab hlab hinj i.isLt
    rw [h1, h2]
  have hperm_zt : (zipRec xs (labVals lab)).Perm target :=
    permOfGetD σ .nil hzlen htarget_len hper
  -- a permutation of `zipRec` sorted by key is `target`
  have hrs : rs' = target := by
    refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd hab (not_lt.mpr hba.le))
      hsort htarget_sorted ?_
    exact hperm.trans hperm_zt
  intro m hm
  have hm' : m < target.length := by rw [htarget_len]; exact hm
  rw [hrs, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm'), List.getElem_map]
  rw [show target[m] = target.getD m .nil from (List.getD_eq_getElem target _ hm').symm,
    htarget_get m hm]
  rfl

end Work.MainP
