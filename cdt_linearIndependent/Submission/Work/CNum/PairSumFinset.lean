import Mathlib

namespace Work.CNum

lemma pairSum_foldl_add (L : List ℤ) (acc : ℤ) (S : ℤ → ℤ) :
    List.foldl (fun a x => a + S x) acc L = acc + (L.map S).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

lemma pairSum_foldl_double (L : List ℤ) :
    List.foldl (fun (acc : ℤ) (x : ℤ) =>
      List.foldl (fun (a : ℤ) (y : ℤ) => a + max x y) acc L) 0 L
    = (L.map (fun x => (L.map (fun y => max x y)).sum)).sum := by
  rw [show (fun (acc : ℤ) (x : ℤ) =>
      List.foldl (fun (a : ℤ) (y : ℤ) => a + max x y) acc L)
    = (fun (acc : ℤ) (x : ℤ) => acc + (L.map (fun y => max x y)).sum) from by
      funext acc x
      exact pairSum_foldl_add L acc (fun y => max x y)]
  rw [pairSum_foldl_add L 0 (fun x => (L.map (fun y => max x y)).sum)]
  simp

lemma pairSum_finset_range (N : ℕ) (h : ℕ → ℤ) :
    (Finset.range N).sum h = ((List.range N).map h).sum := by
  rw [← List.toFinset_range N, List.sum_toFinset h (l := List.range N) List.nodup_range]

lemma pairSum_map_map_max (N : ℕ) (f : ℕ → ℤ) (x : ℤ) :
    (List.map f (List.range N)).map (fun y => max x y)
      = (List.range N).map (fun j => max x (f j)) := by
  rw [List.map_map]
  rfl

lemma pairSum_lhs (N : ℕ) (f : ℕ → ℤ) :
    (Finset.range N).sum (fun i => (Finset.range N).sum (fun j => max (f i) (f j)))
    = ((List.map f (List.range N)).map
        (fun x => ((List.map f (List.range N)).map (fun y => max x y)).sum)).sum := by
  rw [pairSum_finset_range N (fun i => (Finset.range N).sum (fun j => max (f i) (f j)))]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [pairSum_finset_range N (fun j => max (f i) (f j))]
  rw [pairSum_map_map_max N f (f i)]

theorem PairSumFinset (N : ℕ) (f : ℕ → ℤ) : Finset.sum (Finset.range N) (fun i => Finset.sum (Finset.range N) (fun j => max (f i) (f j))) = List.foldl (fun (acc : ℤ) (x : ℤ) => List.foldl (fun (a : ℤ) (y : ℤ) => a + max x y) acc (List.map f (List.range N))) 0 (List.map f (List.range N)) := by
  rw [pairSum_foldl_double, pairSum_lhs]

end Work.CNum
