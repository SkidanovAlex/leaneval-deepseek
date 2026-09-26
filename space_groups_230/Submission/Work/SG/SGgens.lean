import Submission.Work.SG.SGfacts

/-! Identification of the `ℚ`-side generators of `Defs` with the `ℤ`-side ones. -/

namespace Work.SG

theorem sgGenTrans_eq (k : Fin 230) :
    sgGenTrans k = (sgGenTransZ k).map (toPairL (sgDen k)) := by
  simp only [sgGenTrans, sgGenTransZ, sgDen]
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  simp only [Function.comp_apply, toPairL, List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

theorem zip_toPair (l m : List (List ℤ)) (d : ℕ) :
    (l.zip m).map (fun p => (p.1, toPairL d p.2)) = l.zip (m.map (toPairL d)) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
      cases m with
      | nil => simp
      | cons b m => simp [ih m]

theorem gensQ_eq_gensZ (k : Fin 230) : gensQ k = (gensZ k).map (toPair (sgDen k)) := by
  simp only [gensQ, gensZ, sgGenTrans_eq k, toPair]
  exact (zip_toPair (arithGens (sgArith k)) (sgGenTransZ k) (sgDen k)).symm

theorem gensQ_length_eq (k : Fin 230) :
    (arithGens (sgArith k)).length = (sgGenTransZ k).length := by
  simp only [sgGenTransZ, arithGens, List.length_map, List.length_range, idxCheck_eq k]

theorem map_fst_zip_take {α : Type*} (l m : List α) : (l.zip m).map Prod.fst = l.take m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => cases m <;> simp [ih]

theorem fst_gensQ (k : Fin 230) : (gensQ k).map (·.1) = arithGens (sgArith k) := by
  rw [gensQ_eq_gensZ k]
  have hfun : ((fun q : List ℤ × List ℚ => q.1) ∘ toPair (sgDen k)) = Prod.fst := by
    funext p
    rfl
  rw [List.map_map, hfun, gensZ]
  rw [map_fst_zip_take, ← gensQ_length_eq k]
  exact List.take_of_length_le le_rfl

end Work.SG
