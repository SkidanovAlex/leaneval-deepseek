import Mathlib
import Submission.Work.SynFFT.kit

namespace Work.SynFFT

/-- Pointwise description of `(w.drop s).map (·*sg) ++ (w.take s).map (·*(-sg))`:
for a valid index `j`, the entry comes from `w` at position `s + j` (if that is in range),
scaled by `sg`, and otherwise from position `s + j - w.length`, scaled by `-sg`. -/
private lemma getD_drop_take (w : List (ℤ × ℤ)) (s j : ℕ) (hs : s ≤ w.length) (hj : j < w.length)
    (sg : ℤ) :
    ((w.drop s).map (fun z => (sg * z.1, sg * z.2)) ++
      (w.take s).map (fun z => (-sg * z.1, -sg * z.2))).getD j (0,0) =
      (if s + j < w.length
        then (sg * (w.getD (s + j) (0,0)).1, sg * (w.getD (s + j) (0,0)).2)
        else (-(sg * (w.getD (s + j - w.length) (0,0)).1),
              -(sg * (w.getD (s + j - w.length) (0,0)).2))) := by
  have hd : (w.drop s).length = w.length - s := List.length_drop
  have ht : (w.take s).length = s := by rw [List.length_take, Nat.min_eq_left hs]
  have hlen : ((w.drop s).map (fun z => (sg * z.1, sg * z.2)) ++
      (w.take s).map (fun z => (-sg * z.1, -sg * z.2))).length = w.length := by
    rw [List.length_append, List.length_map, List.length_map, hd, ht, Nat.sub_add_cancel hs]
  rw [List.getD_eq_getElem _ (0,0) (by rw [hlen]; exact hj)]
  by_cases hcase : s + j < w.length
  · rw [ite_eq_left hcase, List.getElem_append_left (by rw [List.length_map, hd]; omega)]
    simp only [List.getElem_map, List.getElem_drop]
    rw [List.getD_eq_getElem _ (0,0) hcase]
  · rw [ite_eq_right hcase, List.getElem_append_right (by rw [List.length_map, hd]; omega)]
    simp only [List.getElem_map, List.getElem_take, List.length_map, hd]
    rw [List.getD_eq_getElem _ (0,0) (by omega)]
    have hk : j - (w.length - s) = s + j - w.length := by omega
    simp only [hk, neg_mul]

theorem yMulListGetD (r : ℕ) (hr : 0 < r) (e : ℤ) (w : List (ℤ × ℤ)) (hw : w.length = r)
    (j : ℕ) (hj : j < r) :
    (Work.SynFFT.yMulList r e w).getD j (0, 0) =
      (if j + ((-e).fmod (r : ℤ)).toNat < r
        then ((if e + (-e).fmod (r : ℤ) = 0 then (1 : ℤ) else -1) *
                (w.getD (j + ((-e).fmod (r : ℤ)).toNat) (0, 0)).1,
              (if e + (-e).fmod (r : ℤ) = 0 then (1 : ℤ) else -1) *
                (w.getD (j + ((-e).fmod (r : ℤ)).toNat) (0, 0)).2)
        else (-((if e + (-e).fmod (r : ℤ) = 0 then (1 : ℤ) else -1) *
                (w.getD (j + ((-e).fmod (r : ℤ)).toNat - r) (0, 0)).1),
              -((if e + (-e).fmod (r : ℤ) = 0 then (1 : ℤ) else -1) *
                (w.getD (j + ((-e).fmod (r : ℤ)).toNat - r) (0, 0)).2))) := by
  simp only [yMulList]
  have hRle : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr.le
  have hRne : (r : ℤ) ≠ 0 := by omega
  set f : ℤ := (-e).fmod (r : ℤ) with hfdef
  set s : ℕ := f.toNat with hsdef
  set sg : ℤ := if e + f = 0 then (1 : ℤ) else -1 with hsgdef
  have hfmod : f = (-e) % (r : ℤ) := by
    rw [hfdef, Int.fmod_eq_emod, ite_eq_left (Or.inl hRle), add_zero]
  have hfnn : 0 ≤ f := by rw [hfmod]; exact Int.emod_nonneg (-e) hRne
  have hflt : f < (r : ℤ) := by rw [hfmod]; exact Int.emod_lt_of_pos (-e) (by exact_mod_cast hr)
  have hsr : s < r := by
    rw [hsdef, Int.toNat_lt' hr]
    exact hflt
  have hsw : s ≤ w.length := by rw [hw]; exact hsr.le
  rw [getD_drop_take w s j hsw (by rw [hw]; exact hj) sg, hw,
    show s + j = j + s by omega]

end Work.SynFFT
