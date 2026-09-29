import Mathlib
import Submission.Work.Resample.buQWSelDefs
import Submission.Work.Resample.buQWsort
import Submission.Work.Resample.buQWkey

/-!
# `Work.Resample.buSelSorted`: the sorted selection record list is the `C̃ ∘ P̃_t` selection

Paper Prop. 4.7(ii) (`B̃` one-dimensional word): the selection stage reads the input vector `u`
(of length `t`), labels the entry `i < t` with the destination key `egLam s t i` (an integer, the
inverse of the injective map `ν = egNu s t` on its image and `s + i` off it), sorts the labelled
records by their label, and keeps the first `s` records.

This lemma identifies the sorted list `ys`: for every `ℓ < s` the `ℓ`-th record of `ys` is the record
labelled `ℓ`, i.e. the record of the source index `egNu s t ℓ`:

`ys.getD ℓ .nil = cons (int ℓ) (cfxVal (u.getD (egNu s t ℓ) (0,0)))`.

The argument is `Work.Resample.buQWsort` (a strictly increasing list of naturals covering
`{0,…,s-1}` has `ℓ`-th entry `ℓ`) applied to the `ℕ`-valued key `(pairKey ·).toNat`:
* the labels of the records are pairwise distinct (`buQWkey`), so the keys are `Nodup`;
* they cover `{0,…,s-1}` (`buQWkey`'s last item);
* `pairKey` is nonnegative on the records, so `pairKey a < pairKey b` upgrades to
  `(pairKey a).toNat < (pairKey b).toNat`;
and then the record with label `ℓ` is identified by injectivity of `egLam` on `{0,…,t-1}` and
`egNu_egLam`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `Int.toNat` is strictly increasing on nonnegative integers. -/
lemma int_toNat_lt_iff_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.toNat < b.toNat ↔ a < b := by
  rw [← Nat.cast_lt (α := ℤ), Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]

/-- The `zip`-form of the selection record list is the `ofFn`-form, as soon as `u` has length `t`:
the `i`-th record is `cons (int (egLam s t i)) (cfxVal uᵢ)`. -/
lemma buSelRecs_eq' (s t : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = t) :
    buSelRecs s t u = buSelRecs' s t u := by
  unfold buSelRecs buSelRecs' buSelKeys
  apply List.ext_getElem
  · simp [hu]
  · intro i h1 h2
    simp only [List.length_map, List.length_zip, List.length_ofFn] at h1 h2
    rw [List.getElem_map, List.getElem_zip, List.getElem_map, List.getElem_ofFn, List.getElem_map,
      List.getElem_ofFn, List.getD_eq_getElem u (0,0) (by rw [hu]; exact h2)]

/-- The `ofFn`-form of the record list has length `t`. -/
lemma buSelRecs'_length (s t : ℕ) (u : List (ℤ × ℤ)) : (buSelRecs' s t u).length = t := by
  unfold buSelRecs'; simp

/-- The label (`pairKey`) of the `i`-th record is `egLam s t i`. -/
lemma buSelRecs'_map_pairKey (s t : ℕ) (u : List (ℤ × ℤ)) :
    (buSelRecs' s t u).map HvdH.pairKey =
      List.ofFn (fun i : Fin t => ((egLam s t (i:ℕ) : ℕ) : ℤ)) := by
  unfold buSelRecs'
  rw [List.map_ofFn]
  congr 1

/-- Every member of the record list is the record of some index `i < t`. -/
lemma mem_buSelRecs' (s t : ℕ) {u : List (ℤ × ℤ)} {x : HvdH.Val} (hx : x ∈ buSelRecs' s t u) :
    ∃ i < t, x = HvdH.Val.cons (HvdH.Val.int ((egLam s t i : ℕ) : ℤ))
      (HvdH.cfxVal (u.getD i (0,0))) := by
  unfold buSelRecs' at hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, i.isLt, hi.symm⟩

theorem buSelSorted (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (u : List (ℤ × ℤ)) (hu : u.length = t) (ys : List HvdH.Val)
    (hperm : ys.Perm (Work.Resample.buSelRecs s t u))
    (hsort : ys.Pairwise fun a b => HvdH.pairKey a < HvdH.pairKey b) :
    ∀ ℓ < s, ys.getD ℓ HvdH.Val.nil
      = HvdH.Val.cons (HvdH.Val.int (ℓ : ℤ)) (HvdH.cfxVal (u.getD (Work.Resample.egNu s t ℓ) (0, 0))) := by
  classical
  obtain ⟨_, _, _, hlam_lt_iff, _, _, _, _, hcov_lam⟩ := buQWkey s t hs hst hcop
  set rcs : List HvdH.Val := buSelRecs s t u with hrcs
  set key : HvdH.Val → ℕ := fun v => (HvdH.pairKey v).toNat with hkey
  have hperm' : ys.Perm rcs := by rw [hrcs]; exact hperm
  have hrcs'_eq : rcs = buSelRecs' s t u := by rw [hrcs]; exact buSelRecs_eq' s t u hu
  have hrcs_len : rcs.length = t := by rw [hrcs'_eq, buSelRecs'_length]
  have hys_len : ys.length = t := by rw [hperm'.length_eq, hrcs_len]
  -- the key of a record `cons (int k) v` is `k`
  have hkey_cons : ∀ (k : ℕ) (v : HvdH.Val),
      key (HvdH.Val.cons (HvdH.Val.int (k:ℤ)) v) = k := by
    intro k v; simp [hkey, HvdH.pairKey]
  have hmap_key : rcs.map key = List.ofFn (fun i : Fin t => egLam s t (i:ℕ)) := by
    rw [hrcs'_eq]
    unfold buSelRecs'
    rw [List.map_ofFn]
    congr 1
  -- the labels of the records are pairwise distinct
  have hnd : (rcs.map key).Nodup := by
    rw [hmap_key, List.nodup_ofFn]
    intro i j hij
    exact Fin.ext (egLam_inj s t (by omega) hst hcop i.val j.val i.isLt j.isLt hij)
  -- the labels of the records are nonnegative
  have hkey_nonneg : ∀ x ∈ rcs, 0 ≤ HvdH.pairKey x := by
    intro x hx
    rw [hrcs'_eq] at hx
    obtain ⟨i, hi, rfl⟩ := mem_buSelRecs' (s := s) (t := t) hx
    simp [HvdH.pairKey]
  -- the labels cover `{0,…,s-1}`
  have hcov : ∀ ℓ < s, ∃ x ∈ rcs, key x = ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, hieq⟩ := hcov_lam ℓ hℓ
    refine ⟨HvdH.Val.cons (HvdH.Val.int ((egLam s t i : ℕ) : ℤ)) (HvdH.cfxVal (u.getD i (0,0))),
      ?_, ?_⟩
    · rw [hrcs'_eq]
      unfold buSelRecs'
      rw [List.mem_ofFn]
      exact ⟨⟨i, hi⟩, rfl⟩
    · rw [hkey_cons, hieq]
  have hsort' : ys.Pairwise (fun a b => key a < key b) := by
    apply List.Pairwise.imp_of_mem _ hsort
    intro a b ha hb hab
    rw [hkey]
    exact (int_toNat_lt_iff_of_nonneg (hkey_nonneg a ((hperm'.mem_iff).mp ha))
      (hkey_nonneg b ((hperm'.mem_iff).mp hb))).mpr hab
  have hsel := buQWsort key rcs ys s hperm' hsort' hnd hcov
  intro ℓ hℓ
  obtain ⟨hmem, hkeyeq⟩ := hsel ℓ hℓ
  have hℓys : ℓ < ys.length := by rw [hys_len]; exact lt_trans hℓ hst
  have hdefault : ys.getD ℓ default = ys.getD ℓ HvdH.Val.nil := by
    rw [List.getD_eq_getElem ys default hℓys, List.getD_eq_getElem ys HvdH.Val.nil hℓys]
  rw [hdefault] at hmem hkeyeq
  rw [hrcs'_eq] at hmem
  obtain ⟨i, hi, hxeq⟩ := mem_buSelRecs' (s := s) (t := t) hmem
  -- the record with label `ℓ` is indexed by `egNu s t ℓ`
  have hk_eq : egLam s t i = ℓ := by
    rw [hxeq] at hkeyeq
    simpa [hkey, HvdH.pairKey] using hkeyeq
  have hi_eq : i = egNu s t ℓ := by
    have him : ∃ ℓ' : Fin s, egNu s t (ℓ' : ℕ) = i :=
      (hlam_lt_iff i hi).mp (by rw [hk_eq]; exact hℓ)
    have h2 := egNu_egLam s t i him
    rw [hk_eq] at h2
    exact h2.symm
  rw [hxeq, hk_eq, hi_eq]

end Work.Resample
