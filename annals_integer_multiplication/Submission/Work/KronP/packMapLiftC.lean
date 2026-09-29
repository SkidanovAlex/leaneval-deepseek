import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.Kernel.mapList

namespace Work.KronP

open HvdH

/-!
# Lifting a word on one integer to a word on a list of integers, tight cost

This is the "tight" companion of `Work.KronP.packMapLift`: instead of the padded bound
`K * (n * (c + L + 1) + L + 1)` we ask for `K * (n * (c + L + 1)) + K`, i.e. the `+ L` of the
multiplied constant disappears.

The point is that the *Kernel* library `Work.Kernel.mapList` proves its field with the bound
`xs.length * (c + K * (L + 1)) + K` (a per-element cost `c + K * (L + 1)`, exactly what the
implementation spends, plus an `L`-independent constant `K`).  The interface’s `mapList` field
records the weaker statement obtained from it, whose constant term is `K * (L + 1)`, which blows up
for large `L` when `xs = []`.  Here we do the whole lifting directly on top of the tight lemma, so
that the constant term really is a constant.
-/

/-- Cost arithmetic: `n` elements at cost `c + K * (L + 1)` each plus a constant `K` still fit in
`(K + 1) * (n * (c + L + 1)) + (K + 1)`. -/
theorem packMapLiftC_cost (n c L K : ℕ) :
    n * (c + K * (L + 1)) + K ≤ (K + 1) * (n * (c + L + 1)) + (K + 1) := by
  have hmain : c + K * (L + 1) ≤ (K + 1) * (c + L + 1) := by
    have hc : c ≤ (K + 1) * c := by
      calc c = 1 * c := by ring
        _ ≤ (K + 1) * c := Nat.mul_le_mul_right c (by omega)
    have hkl : K * (L + 1) ≤ (K + 1) * (L + 1) := Nat.mul_le_mul_right _ (Nat.le_succ K)
    calc c + K * (L + 1) ≤ (K + 1) * c + (K + 1) * (L + 1) := Nat.add_le_add hc hkl
      _ = (K + 1) * (c + (L + 1)) := (Nat.mul_add (K + 1) c (L + 1)).symm
      _ = (K + 1) * (c + L + 1) := by ring
  have h1 : n * (c + K * (L + 1)) ≤ (K + 1) * (n * (c + L + 1)) := by
    calc n * (c + K * (L + 1)) ≤ n * ((K + 1) * (c + L + 1)) := Nat.mul_le_mul_left n hmain
      _ = (K + 1) * (n * (c + L + 1)) := by ring
  exact Nat.add_le_add h1 (Nat.le_succ K)

/-- If a `List.Forall₂` relates `xs.map Val.int` to `ys` through the graph of `f`, then
`ys = xs.map f`. -/
theorem forall₂_map_int_eqC (f : ℤ → Val) :
    ∀ (xs : List ℤ) (ys : List Val),
      List.Forall₂ (fun x y => ∃ z : ℤ, x = Val.int z ∧ y = f z)
        (xs.map Val.int) ys → ys = xs.map f := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      rw [List.map_nil] at h
      rw [List.forall₂_nil_left_iff] at h
      rw [List.map_nil]
      exact h
  | cons a as ih =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons b t =>
          rw [List.map_cons, List.forall₂_cons] at h
          obtain ⟨⟨z, hz, hb⟩, h2⟩ := h
          have haz : a = z := (Val.int.injEq a z).mp hz
          subst z
          rw [List.map_cons, hb, ih t h2]

theorem packMapLiftC (hK : HvdH.KernelLib) :
    ∃ (comb : HvdH.Cmd → HvdH.Cmd) (K : ℕ),
      ∀ (main q : HvdH.Cmd) (rest : List HvdH.Val) (f : ℤ → HvdH.Val) (c L : ℕ),
        (∀ z : ℤ, HvdH.isz z ≤ L → HvdH.WordR main q
          (fun vs => vs = HvdH.Val.int z :: rest) (fun _ out => out = f z :: rest)
          (fun _ => c)) →
        (∀ z : ℤ, HvdH.isz z ≤ L → HvdH.vsz (f z) ≤ L) →
        ∀ (xs : List ℤ), (∀ x ∈ xs, HvdH.isz x ≤ L) →
          HvdH.WordR main (comb q) (fun vs => vs = Work.KronP.zsVal xs :: rest)
            (fun _ out => out = HvdH.ofList (xs.map f) :: rest)
            (fun _ => K * (xs.length * (c + L + 1)) + K) := by
  obtain ⟨comb, K₀, hmap⟩ := Work.Kernel.mapList
  refine ⟨comb, K₀ + 1, ?_⟩
  intro main q rest f c L hq hsz xs hxs
  -- The per-element body: given `int z` on top of `rest`, produce `f z`.
  have hbody : ∀ x : HvdH.Val,
      (∃ z : ℤ, x = HvdH.Val.int z ∧ HvdH.isz z ≤ L) →
      HvdH.WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧
          (∃ z : ℤ, x = HvdH.Val.int z ∧ y = f z) ∧ HvdH.vsz y ≤ L) (fun _ => c) := by
    rintro x ⟨z, rfl, hz⟩
    exact hK.conseq main q (fun vs => vs = HvdH.Val.int z :: rest)
      (fun vs => vs = HvdH.Val.int z :: rest) (fun _ out => out = f z :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧
        (∃ z' : ℤ, HvdH.Val.int z = HvdH.Val.int z' ∧ y = f z') ∧ HvdH.vsz y ≤ L)
      (fun _ => c) (fun _ => c) (hq z hz) (fun vs hv => hv)
      (fun vs out _ hout => ⟨f z, hout, ⟨z, rfl, rfl⟩, hsz z hz⟩) (fun vs _ => le_rfl)
  -- The list hypothesis for `mapList`.
  have hxs' : ∀ x ∈ xs.map HvdH.Val.int,
      (∃ z : ℤ, x = HvdH.Val.int z ∧ HvdH.isz z ≤ L) ∧ HvdH.vsz x ≤ L := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨⟨z, rfl, hxs z hz⟩, by rw [vsz_int_eq]; exact hxs z hz⟩
  have key := hmap main q rest (fun x : HvdH.Val => ∃ z : ℤ, x = HvdH.Val.int z ∧ HvdH.isz z ≤ L)
    (fun x y => ∃ z : ℤ, x = HvdH.Val.int z ∧ y = f z) c L hbody (xs.map HvdH.Val.int) hxs'
  -- Transport the pre/post/cost to the `zsVal`/`ofList (xs.map f)` shape.
  refine hK.conseq main (comb q)
    (fun vs => vs = HvdH.ofList (xs.map HvdH.Val.int) :: rest)
    (fun vs => vs = Work.KronP.zsVal xs :: rest)
    (fun _ out => ∃ ys, out = HvdH.ofList ys :: rest ∧
      List.Forall₂ (fun x y => ∃ z : ℤ, x = HvdH.Val.int z ∧ y = f z) (xs.map HvdH.Val.int) ys)
    (fun _ out => out = HvdH.ofList (xs.map f) :: rest)
    (fun _ => (xs.map HvdH.Val.int).length * (c + K₀ * (L + 1)) + K₀)
    (fun _ => (K₀ + 1) * (xs.length * (c + L + 1)) + (K₀ + 1))
    key ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    rfl
  · rintro vs out _ ⟨ys, hout, hfor⟩
    rw [forall₂_map_int_eqC f xs ys hfor] at hout
    exact hout
  · intro vs _
    simp only [List.length_map]
    exact packMapLiftC_cost xs.length c L K₀

end Work.KronP
