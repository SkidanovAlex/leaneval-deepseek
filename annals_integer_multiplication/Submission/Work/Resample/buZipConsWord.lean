import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buZipWithFun

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buZipConsWord`

The `zipWith`-with-`cons` specialisation of the `KernelLib.zipWith` field: given two lists `xs`, `ys`
of equal length, produce the list `(xs.zip ys).map (fun p => .cons p.1 p.2)`, i.e. pair the two
lists elementwise into `cons`-cells, without recursion (`∀ main`).

It is assembled from

* `Work.Resample.buZipWithFun` (the functional form of `KernelLib.zipWith`), with the element word
  `KL.consV` (`Work.Resample.buZipCons_consV_elem` below), element bound `2 * L + 2`;
* and pure arithmetic on the cost, `Work.Resample.buZipCons_cost`.
-/

/-- size of a `cons` cell. -/
theorem buZipCons_vsz_cons (a b : Val) : vsz (.cons a b) = 1 + vsz a + vsz b := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]
  omega

/-- `List.zip` followed by the `cons` map is the corresponding `List.zipWith`. -/
theorem buZipCons_map_zip (xs ys : List Val) :
    (xs.zip ys).map (fun p : Val × Val => Val.cons p.1 p.2)
      = List.zipWith (fun x y => Val.cons x y) xs ys := by
  rw [List.zip_eq_zipWith, List.map_zipWith]

/-- `KL.consV` with the element-level pre/post used by `zipWith`
(`a :: b :: rest ↦ .cons a b :: rest`, constant cost). -/
theorem buZipCons_consV_elem (KL : HvdH.KernelLib) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main p (fun vs => vs = a :: b :: rest)
        (fun _ out => out = HvdH.Val.cons a b :: rest) (fun _ => K) := by
  obtain ⟨p, K, h⟩ := KL.consV
  refine ⟨p, K, ?_⟩
  intro main a b rest vs hvs s R hR
  obtain ⟨out, s', n, hpost, hev, hn, h0, hfr⟩ := h main vs (by rw [hvs]; simp) s R hR
  obtain ⟨a', b', r, heq, hout⟩ := hpost
  have h1 : a = a' ∧ b = b' ∧ rest = r := by
    have h2 : a :: b :: rest = a' :: b' :: r := by rw [← hvs]; exact heq
    simpa [List.cons.injEq] using h2
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact ⟨out, s', n, by rw [hout], hev, hn, h0, hfr⟩

/-- the cost arithmetic: the `zipWith` bound with element bound `2 * L + 2` is dominated by
`(Kc + 3 Kz + 1) * (n + 1) * (L + 1)`. -/
theorem buZipCons_cost (a b c L : ℕ) :
    a * (b + c * (2 * L + 2 + 1)) + c ≤ (b + 3 * c + 1) * (a + 1) * (L + 1) := by
  set A := b + 3 * c + 1 with hA
  have h1 : b + c * (2 * L + 2 + 1) ≤ A * (L + 1) := by
    have hb : b ≤ b * (L + 1) := by
      calc b = b * 1 := (Nat.mul_one b).symm
        _ ≤ b * (L + 1) := Nat.mul_le_mul_left b (by omega)
    have hc : c * (2 * L + 2 + 1) ≤ 3 * c * (L + 1) := by
      have h4 : 2 * L + 2 + 1 ≤ 3 * (L + 1) := by omega
      calc c * (2 * L + 2 + 1) ≤ c * (3 * (L + 1)) := Nat.mul_le_mul_left c h4
        _ = 3 * c * (L + 1) := by ring
    calc b + c * (2 * L + 2 + 1) ≤ b * (L + 1) + 3 * c * (L + 1) := Nat.add_le_add hb hc
      _ = (b + 3 * c) * (L + 1) := by ring
      _ ≤ A * (L + 1) := by
          rw [hA]; exact Nat.mul_le_mul_right (L + 1) (by omega)
  have h8 : c ≤ A * (L + 1) := by
    have : c ≤ A := by rw [hA]; omega
    exact le_trans this (by
      calc A = A * 1 := (Nat.mul_one A).symm
        _ ≤ A * (L + 1) := Nat.mul_le_mul_left A (by omega))
  calc a * (b + c * (2 * L + 2 + 1)) + c
      ≤ a * (A * (L + 1)) + A * (L + 1) := Nat.add_le_add (Nat.mul_le_mul_left a h1) h8
    _ = A * (a + 1) * (L + 1) := by ring

theorem buZipConsWord (KL : HvdH.KernelLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (L : ℕ) (xs ys : List HvdH.Val), xs.length = ys.length →
      (∀ x ∈ xs ++ ys, HvdH.vsz x ≤ L) →
      HvdH.WordR main q
        (fun vs => ∃ rest, vs = HvdH.ofList xs :: HvdH.ofList ys :: rest)
        (fun vs out => ∃ rest, vs = HvdH.ofList xs :: HvdH.ofList ys :: rest ∧
          out = HvdH.ofList ((xs.zip ys).map (fun p : HvdH.Val × HvdH.Val => HvdH.Val.cons p.1 p.2)) :: rest)
        (fun _ => K * (xs.length + 1) * (L + 1)) := by
  obtain ⟨comb, Kz, hZip⟩ := buZipWithFun KL
  obtain ⟨consP, Kc, hCons⟩ := buZipCons_consV_elem KL
  refine ⟨comb consP, Kc + 3 * Kz + 1, ?_⟩
  intro main L xs ys hlen hLall
  -- the `zipWith` bound with element bound `2 * L + 2`, for every fixed `rest`
  have hkey : ∀ (rest : List Val), WordR main (comb consP)
      (fun vs => vs = ofList xs :: ofList ys :: rest)
      (fun _ out => out = ofList (List.zipWith (fun x y => Val.cons x y) xs ys) :: rest)
      (fun _ => xs.length * (Kc + Kz * (2 * L + 2 + 1)) + Kz) := by
    intro rest
    refine hZip main consP rest (fun x y => vsz x ≤ L ∧ vsz y ≤ L)
      (fun x y => Val.cons x y) Kc (2 * L + 2) ?_ ?_ xs ys hlen ?_ ?_
    · -- element word: `consV`
      intro x y _
      exact hCons main x y rest
    · -- size of the produced cell
      intro x y ⟨hx, hy⟩
      rw [buZipCons_vsz_cons]
      omega
    · -- elementwise precondition
      intro i hi
      have hmem1 : xs.getD i Val.nil ∈ xs := by
        rw [List.getD_eq_getElem xs Val.nil hi]; exact List.getElem_mem hi
      have hmem2 : ys.getD i Val.nil ∈ ys := by
        have hi' : i < ys.length := by rw [← hlen]; exact hi
        rw [List.getD_eq_getElem ys Val.nil hi']; exact List.getElem_mem hi'
      exact ⟨hLall _ (List.mem_append.mpr (Or.inl hmem1)),
             hLall _ (List.mem_append.mpr (Or.inr hmem2))⟩
    · -- input size bound
      intro x hx
      have := hLall x hx
      omega
  intro vs hvs s R hR
  obtain ⟨rest, hvs'⟩ := hvs
  obtain ⟨out, s', n, hpost, hev, hn, h0, hfr⟩ := hkey rest vs hvs' s R hR
  refine ⟨out, s', n, ⟨rest, hvs', ?_⟩, hev, ?_, h0, hfr⟩
  · rw [hpost]
    exact congrArg (fun l => ofList l :: rest) (buZipCons_map_zip xs ys).symm
  · calc n ≤ xs.length * (Kc + Kz * (2 * L + 2 + 1)) + Kz := hn
      _ ≤ (Kc + 3 * Kz + 1) * (xs.length + 1) * (L + 1) := buZipCons_cost xs.length Kc Kz L

end Work.Resample
