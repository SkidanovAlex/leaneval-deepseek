import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample

open HvdH

/-! ## List-level facts about the record list `buScRecs`

`buScRecs s t d` is `zipWith cons (buScKeys s t) (d.map cfxVal)`; since `d.length = s` it is
literally the `ofFn` list whose `i`-th entry is `cons (int (egKeyS s t i)) (cfxVal dᵢ)`.  These
lemmas expose that normal form (length, `getD`, and the `pairKey` map), so that the combinatorial
argument below can work with `Fin s` indices. -/

lemma buScKeys_ofFn (s t : ℕ) :
    buScKeys s t = List.ofFn (fun i : Fin s => Val.int (((egKeyS s t (i:ℕ) : ℕ) : ℤ))) := by
  unfold buScKeys
  rw [List.map_ofFn]
  rfl

lemma buScRecs_eq_ofFn (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    buScRecs s t d = List.ofFn (fun i : Fin s =>
      Val.cons (Val.int ((egKeyS s t (i:ℕ) : ℕ) : ℤ)) (cfxVal (d.getD (i:ℕ) (0,0)))) := by
  unfold buScRecs
  rw [buScKeys_ofFn]
  apply List.ext_getElem
  · rw [List.length_zipWith, List.length_ofFn, List.length_map, List.length_ofFn, hd]
    simp
  · intro i h1 h2
    have hi : i < s := by rw [List.length_ofFn] at h2; exact h2
    rw [List.getElem_zipWith]
    simp only [List.getElem_ofFn]
    rw [List.getElem_map]
    congr 1
    rw [List.getD_eq_getElem d (0,0) (by rw [hd]; exact hi)]

lemma buScRecs_length (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    (buScRecs s t d).length = s := by
  rw [buScRecs_eq_ofFn s t d hd, List.length_ofFn]

lemma buScRecs_getD (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    ∀ i < s, (buScRecs s t d).getD i Val.nil =
      Val.cons (Val.int ((egKeyS s t i : ℕ) : ℤ)) (cfxVal (d.getD i (0,0))) := by
  intro i hi
  rw [buScRecs_eq_ofFn s t d hd]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi)]
  rw [List.getElem_ofFn]

lemma buScRecs_map_pairKey (s t : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s) :
    (buScRecs s t d).map pairKey = List.ofFn (fun i : Fin s => ((egKeyS s t (i:ℕ) : ℕ) : ℤ)) := by
  rw [buScRecs_eq_ofFn s t d hd, List.map_ofFn]
  rfl

namespace Work.Resample
open HvdH

/-- The sorted record list, read at position `ℓ < s`, is the record whose key is `ℓ`: the entry at
position `ℓ` is `cons (int ℓ) (cfxVal dᵢ)` where `i < s` is the source index with `(t·i) % s = ℓ`.
(Use `Work.Resample.buQWsort` with the `ℕ`-valued key `(pairKey ·).toNat`; the keys are `≥ 0`.) -/
theorem buScSorted (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (ys : List Val)
    (hperm : ys.Perm (buScRecs s t d))
    (hsort : ys.Pairwise fun a b => pairKey a < pairKey b) :
    ∀ ℓ < s, ∃ i < s, egKeyS s t i = ℓ ∧
      ys.getD ℓ Val.nil = Val.cons (Val.int (ℓ : ℤ)) (cfxVal (d.getD i (0, 0))) := by
  have hs0 : 0 < s := by omega
  have hlen : (buScRecs s t d).length = s := buScRecs_length s t d hd
  have hget := buScRecs_getD s t d hd
  have hylen : ys.length = s := by rw [hperm.length_eq, hlen]
  -- every element of `ys` carries a non-negative integer key
  have hnonneg : ∀ y ∈ ys, 0 ≤ pairKey y := by
    intro y hy
    have hyx : y ∈ buScRecs s t d := (hperm.mem_iff).mp hy
    obtain ⟨i, hi, hgeti⟩ := List.mem_iff_getElem.mp hyx
    have his : i < s := by rw [← hlen]; exact hi
    have hgd : (buScRecs s t d).getD i Val.nil = y := by
      rw [List.getD_eq_getElem _ _ hi, hgeti]
    rw [← hgd, hget i his]
    exact Int.natCast_nonneg _
  -- the `ℕ`-valued key list of `buScRecs` is `i ↦ egKeyS s t i`, which is injective and surjective
  have hinj : Function.Injective (fun i : Fin s => egKeyS s t (i:ℕ)) := by
    intro a b hab
    exact Fin.ext (egKeyS_inj s t hs0 hcop.symm a.isLt b.isLt hab)
  have hmapnat : (buScRecs s t d).map (fun v => (pairKey v).toNat)
      = List.ofFn (fun i : Fin s => egKeyS s t (i:ℕ)) := by
    have h1 : (fun v : Val => (pairKey v).toNat) = Int.toNat ∘ pairKey := rfl
    rw [h1, ← List.map_map, buScRecs_map_pairKey s t d hd, List.map_ofFn]
    rfl
  have hnd : ((buScRecs s t d).map (fun v => (pairKey v).toNat)).Nodup := by
    rw [hmapnat]; exact List.nodup_ofFn.mpr hinj
  have hcov : ∀ ℓ < s, ∃ x ∈ buScRecs s t d, (pairKey x).toNat = ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi⟩ := egKeyS_surj s t hs0 hcop.symm ⟨ℓ, hℓ⟩
    refine ⟨(buScRecs s t d).getD (i:ℕ) Val.nil, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
      exact List.getElem_mem _
    · rw [hget (i:ℕ) i.isLt]
      simp [pairKey, hi]
  -- strict monotonicity transfers from `pairKey` to `toNat` on `ys`
  have hsort' : ys.Pairwise (fun a b => (pairKey a).toNat < (pairKey b).toNat) :=
    hsort.imp_of_mem (fun {a b} ha hb hab => by
      rw [Int.toNat_lt_toNat (lt_of_le_of_lt (hnonneg a ha) hab)]
      exact hab)
  intro ℓ hℓ
  obtain ⟨hxmem, hxkey⟩ :=
    buQWsort (fun v : Val => (pairKey v).toNat) (buScRecs s t d) ys s hperm hsort' hnd hcov ℓ hℓ
  have hℓlen : ℓ < ys.length := by rw [hylen]; exact hℓ
  have hgetnil : ys.getD ℓ Val.nil = ys.getD ℓ default := by
    rw [List.getD_eq_getElem _ _ hℓlen, List.getD_eq_getElem _ _ hℓlen]
  obtain ⟨i, hi, hgeti⟩ := List.mem_iff_getElem.mp hxmem
  have his : i < s := by rw [← hlen]; exact hi
  have hshape : ys.getD ℓ default
      = Val.cons (Val.int (((egKeyS s t i : ℕ) : ℤ))) (cfxVal (d.getD i (0,0))) := by
    rw [← hgeti, ← List.getD_eq_getElem (buScRecs s t d) Val.nil hi, hget i his]
  have hkeyeq : egKeyS s t i = ℓ := by
    have h1 : (pairKey (ys.getD ℓ default)).toNat = ((egKeyS s t i : ℕ) : ℤ).toNat := by
      rw [hshape]; rfl
    rw [hxkey] at h1
    rw [h1, Int.toNat_natCast]
  refine ⟨i, his, hkeyeq, ?_⟩
  rw [hgetnil, hshape, hkeyeq]

end Work.Resample

/-- The same statement in the namespace `Work.Resample` itself, i.e. under the name requested by the
caller (`Work.Resample.buScSorted`); the body above lives in the namespace block of the stub. -/
theorem buScSorted (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (ys : List Val)
    (hperm : ys.Perm (buScRecs s t d))
    (hsort : ys.Pairwise fun a b => pairKey a < pairKey b) :
    ∀ ℓ < s, ∃ i < s, egKeyS s t i = ℓ ∧
      ys.getD ℓ Val.nil = Val.cons (Val.int (ℓ : ℤ)) (cfxVal (d.getD i (0, 0))) :=
  _root_.Work.Resample.Work.Resample.buScSorted s t hs hst hcop d hd ys hperm hsort

end Work.Resample
