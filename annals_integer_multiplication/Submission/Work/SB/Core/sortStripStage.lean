import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.SB.Core.vszFacts
import Submission.Work.SB.P3.stripFromKernel

/-!
# `Work.SB.Core.sortStripStage`: sort a labelled list by key and strip the keys

`hSo : Work.Layout.SortSpec` is the merge-sort word of the `Layout` area: it sorts a list of records
`cons (int k) v` whose keys `k` are **nonnegative** (`∃ (k : ℕ)`, the shape `SortSpec` itself
requires, since `sortByKeyWord` uses the keys as indices) and pairwise distinct, at cost
`K * (vsz (ofList xs) + 1) * (xs.length.size + 1)`.  `stripMapStage` below maps the key-dropping
word `Work.Layout.unlab` over such a list (its per-element word is `Work.SB.P3.stripFromKernel`,
applied through `KernelLib.mapList`).

Composing the two gives the stage below, whose cost `K * (N+1) * (L + N.size + 1) * (N.size + 1)` is
the standard per-stage budget of the `SB` route: `es.length = A*m*B ≤ N` bounds the list length and
`∀ x ∈ es, vsz x ≤ L` bounds the element sizes, so both the sort cost and the per-element strip cost
fit (see `sortStripArith`).

Note on the key hypothesis: it is `∃ (k : ℕ)`, matching `Work.Layout.SortSpec`, the only sorting
device in scope.  With `∃ (k : ℤ)` the statement would be strictly stronger and is *not* derivable
from `hK` and `hSo`: `KernelLib` provides no integer arithmetic or comparison, so negative keys could
not be re-labelled order-preservingly into nonnegative ones.
-/

set_option autoImplicit false

namespace Work.SB.Core

open HvdH

/-- Cost arithmetic of the two stages: if the elements of a list of length `len ≤ N` have size at
most `L` (so that `vsz (ofList es) ≤ (len + 1) * (L + 1)`), then the sort cost
`Kc * (S + 1) * (len.size + 1)` plus the strip cost `Ks * (N + 1) * (L + 1)` is dominated by
`K * (N + 1) * (L + N.size + 1) * (N.size + 1)`.  Witness: `K = 2 * Kc + Ks`. -/
theorem sortStripArith (Kc Ks : ℕ) : ∃ K : ℕ, ∀ (N L S len : ℕ),
    S ≤ (len + 1) * (L + 1) → len ≤ N →
    Kc * (S + 1) * (len.size + 1) + Ks * (N + 1) * (L + 1)
      ≤ K * (N + 1) * (L + N.size + 1) * (N.size + 1) := by
  refine ⟨2 * Kc + Ks, ?_⟩
  intro N L S len hS hlen
  have hsz : len.size ≤ N.size := Nat.size_le_size hlen
  have hlen1 : len + 1 ≤ N + 1 := by omega
  have hL1 : L + 1 ≤ L + N.size + 1 := by omega
  have hS1 : S ≤ (N + 1) * (L + 1) := le_trans hS (Nat.mul_le_mul_right (L + 1) hlen1)
  have hS2 : S + 1 ≤ 2 * ((N + 1) * (L + N.size + 1)) := by
    have h0 : (N + 1) * (L + 1) ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul_left _ hL1
    have h1 : 1 ≤ (N + 1) * (L + N.size + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have A : Kc * (S + 1) * (len.size + 1) ≤
      2 * Kc * ((N + 1) * (L + N.size + 1)) * (N.size + 1) := by
    calc Kc * (S + 1) * (len.size + 1)
        ≤ Kc * (2 * ((N + 1) * (L + N.size + 1))) * (N.size + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hS2) (by omega)
      _ = 2 * Kc * ((N + 1) * (L + N.size + 1)) * (N.size + 1) := by ring
  have B : Ks * (N + 1) * (L + 1) ≤ Ks * (N + 1) * (L + N.size + 1) * (N.size + 1) := by
    calc Ks * (N + 1) * (L + 1) ≤ Ks * (N + 1) * (L + N.size + 1) :=
          Nat.mul_le_mul_left _ hL1
      _ = Ks * (N + 1) * (L + N.size + 1) * 1 := by ring
      _ ≤ Ks * (N + 1) * (L + N.size + 1) * (N.size + 1) := Nat.mul_le_mul_left _ (by omega)
  calc Kc * (S + 1) * (len.size + 1) + Ks * (N + 1) * (L + 1)
      ≤ 2 * Kc * ((N + 1) * (L + N.size + 1)) * (N.size + 1)
        + Ks * (N + 1) * (L + N.size + 1) * (N.size + 1) := add_le_add A B
    _ = (2 * Kc + Ks) * (N + 1) * (L + N.size + 1) * (N.size + 1) := by ring

/-- **The key-stripping map stage.**  Applied to a list of labelled records `cons (int k) v` (`k : ℕ`,
elements of size `≤ L`, length `≤ N`), the word `p` produces the payload list, i.e. the image of the
`Work.Layout.unlab` map, at cost `≤ K * (N + 1) * (L + 1)`.

Route: `Work.SB.P3.stripFromKernel` gives the per-element word `cons (int k) v :: tail ↦ v :: tail`
(the key `k` is dropped) at cost `Kst * (L + 1)`; `KernelLib.mapList` runs it over the list, costs
being bounded by `xs.length ≤ N`. -/
theorem stripMapStage (hK : HvdH.KernelLib) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (L N : ℕ) (tail xs : List HvdH.Val),
      (∀ x ∈ xs, ∃ (k : ℕ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v) →
      (∀ x ∈ xs, HvdH.vsz x ≤ L) → xs.length ≤ N →
      HvdH.WordR main p
        (fun vs => vs = HvdH.ofList xs :: tail)
        (fun _ out => ∃ ys : List HvdH.Val, out = HvdH.ofList ys :: tail ∧
          ys = xs.map Work.Layout.unlab)
        (fun _ => K * (N + 1) * (L + 1)) := by
  obtain ⟨pElem, Kst, hElem⟩ := (Work.SB.P3.stripFromKernel hK : Work.Layout.StripSpec)
  obtain ⟨pMl, Kml, hMl⟩ := hK.mapList
  refine ⟨pMl pElem, Kst + Kml, ?_⟩
  intro main L N tail xs hshape hsz hlen
  -- the per-element word, as required by `mapList` (its precondition carries the size bound)
  have helem : ∀ x, ((∃ (k : ℕ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v) ∧
        HvdH.vsz x ≤ L) →
      HvdH.WordR main pElem (fun vs => vs = x :: tail)
        (fun _ out => ∃ y : HvdH.Val, out = y :: tail ∧ y = Work.Layout.unlab x ∧
          HvdH.vsz y ≤ L)
        (fun _ => Kst * (L + 1)) := by
    intro x hx
    obtain ⟨⟨k, v, hxv⟩, hxsz⟩ := hx
    subst hxv
    obtain ⟨hvsz, hword⟩ := hElem main L (k : ℤ) v tail hxsz
    refine hK.conseq main pElem _ _ _ _ _ _ hword ?_ ?_ (fun _ _ => le_rfl)
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      exact ⟨v, hpost, rfl, hvsz⟩
  have hmain := hMl main pElem tail
    (fun x => (∃ (k : ℕ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v) ∧
      HvdH.vsz x ≤ L)
    (fun x y => y = Work.Layout.unlab x) (Kst * (L + 1)) L helem xs
    (fun x hx => ⟨⟨hshape x hx, hsz x hx⟩, hsz x hx⟩)
  refine hK.conseq main (pMl pElem) _ _ _ _ _ _ hmain ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hpost
    obtain ⟨zs, hout, hF⟩ := hpost
    exact ⟨zs, hout, forall₂_eq_map hF⟩
  · intro vs hvs
    calc xs.length * (Kst * (L + 1) + Kml * (L + 1)) + Kml
        = xs.length * ((Kst + Kml) * (L + 1)) + Kml := by ring
      _ ≤ N * ((Kst + Kml) * (L + 1)) + Kml := Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _
      _ ≤ N * ((Kst + Kml) * (L + 1)) + (Kst + Kml) * (L + 1) := by
          refine Nat.add_le_add_left ?_ _
          calc Kml ≤ Kst + Kml := Nat.le_add_left _ _
            _ = (Kst + Kml) * 1 := (Nat.mul_one _).symm
            _ ≤ (Kst + Kml) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (Kst + Kml) * (N + 1) * (L + 1) := by ring

/-- **The sort-and-strip stage.**  From a labelled list `ofList es` (keys nonnegative, distinct,
elements of size `≤ L`, length `A*m*B ≤ N`) produce a key-sorted permutation `ys` of `es`, with the
keys stripped: the output value is `ofList (ys.map Work.Layout.unlab)`.

Route: `hSo` (merge sort on the key, cost `Ks * (vsz (ofList es) + 1) * (es.length.size + 1)`)
followed by `stripMapStage` (cost `Kst * (N + 1) * (L + 1)`); `sortStripArith` bounds the sum. -/
theorem sortStripStage (hK : HvdH.KernelLib) (hSo : Work.Layout.SortSpec) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A m B N L : ℕ) (es rest : List HvdH.Val),
      A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, HvdH.vsz x ≤ L) →
      (∀ x ∈ es, ∃ (k : ℕ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v) →
      ((es.map HvdH.pairKey).Nodup) →
      HvdH.WordR main p
        (fun vs => vs = HvdH.ofList es ::
          HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => ∃ ys : List HvdH.Val,
          ys.Perm es ∧ ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b) ∧
          out = HvdH.ofList (ys.map Work.Layout.unlab) ::
            HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  obtain ⟨pSort, Ks, hSort⟩ := hSo
  obtain ⟨pStrip, Kstrip, hStripAll⟩ := stripMapStage hK
  obtain ⟨K, hArith⟩ := sortStripArith Ks Kstrip
  refine ⟨HvdH.Cmd.seq pSort pStrip, K, ?_⟩
  intro main A m B N L es rest hN hlen hvsz hshape hnodup
  set T : List HvdH.Val :=
    HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest with hT
  -- stage 1: sort by key (the `rest` of `SortSpec` is pinned down to `T` by the precondition)
  have hS : HvdH.WordR main pSort (fun vs => vs = HvdH.ofList es :: T)
      (fun _ out => ∃ ys : List HvdH.Val, out = HvdH.ofList ys :: T ∧ ys.Perm es ∧
        ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b))
      (fun _ => Ks * (HvdH.vsz (HvdH.ofList es) + 1) * (es.length.size + 1)) := by
    refine hK.conseq main pSort _ _ _ _ _ _ (hSort main es hshape hnodup) ?_ ?_ ?_
    · intro vs hvs; exact ⟨T, hvs⟩
    · intro vs out hvs hpost
      obtain ⟨r, ys, hvs', hout, hperm, hsrt⟩ := hpost
      rw [hvs] at hvs'
      obtain ⟨-, hr⟩ := List.cons.inj hvs'
      rw [hr.symm] at hout
      exact ⟨ys, hout, hperm, hsrt⟩
    · intro vs hvs; exact le_rfl
  -- stage 2: strip the keys
  intro vs hvs s R hs
  obtain ⟨out₁, s₁, n₁, hpost₁, hev₁, hn₁, hstk₁, hfr₁⟩ := hS vs hvs s R hs
  obtain ⟨ys, hout₁, hperm, hsrt⟩ := hpost₁
  have hshape' : ∀ x ∈ ys,
      ∃ (k : ℕ) (v : HvdH.Val), x = HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v :=
    fun x hx => hshape x ((hperm.mem_iff).mp hx)
  have hsz' : ∀ x ∈ ys, HvdH.vsz x ≤ L := fun x hx => hvsz x ((hperm.mem_iff).mp hx)
  have hlen' : ys.length ≤ N := by rw [hperm.length_eq, hlen]; exact hN
  obtain ⟨out₂, s₂, n₂, hpost₂, hev₂, hn₂, hstk₂, hfr₂⟩ :=
    hStripAll main L N T ys hshape' hsz' hlen' out₁ hout₁ s₁ R hstk₁
  obtain ⟨zs, hout₂, hmap⟩ := hpost₂
  refine ⟨out₂, s₂, n₁ + n₂, ?_, HvdH.Eval.seq hev₁ hev₂, ?_, hstk₂, ?_⟩
  · exact ⟨ys, hperm, hsrt, by rw [hout₂, hmap]⟩
  · have hbd : HvdH.vsz (HvdH.ofList es) ≤ (es.length + 1) * (L + 1) := vsz_ofList_le hvsz
    have hlenN : es.length ≤ N := by rw [hlen]; exact hN
    have hle' := hArith N L (HvdH.vsz (HvdH.ofList es)) es.length hbd hlenN
    have hsum : n₁ + n₂ ≤ Ks * (HvdH.vsz (HvdH.ofList es) + 1) * (es.length.size + 1)
        + Kstrip * (N + 1) * (L + 1) := add_le_add hn₁ hn₂
    exact le_trans hsum hle'
  · intro k hk; exact (hfr₂ k hk).trans (hfr₁ k hk)

end Work.SB.Core
