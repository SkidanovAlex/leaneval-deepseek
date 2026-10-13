import Mathlib
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Basic

namespace Work.WilE8.Star

/-- The first `n+1` coordinates of `insCoord n m w t` are the first `n` coordinates of `w`,
followed by `t`. -/
lemma projFirst_insCoord {n m : ℕ} (w : Fin (n+m) → ℝ) (t : ℝ) :
    WilkiesDesign.E.projFirst (n+1) m (Work.WilE8.Star.insCoord n m w t) =
      Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (WilkiesDesign.E.projFirst n m w) t := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · show Work.WilE8.Star.insCoord n m w t (Fin.castAdd m (Fin.last n)) =
      Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (WilkiesDesign.E.projFirst n m w) t (Fin.last n)
    rw [Work.WilE8.Star.insCoord_new, Fin.snoc_last]
  · intro j
    show Work.WilE8.Star.insCoord n m w t (Fin.castAdd m j.castSucc) =
      Fin.snoc (α := fun _ : Fin (n+1) => ℝ) (WilkiesDesign.E.projFirst n m w) t j.castSucc
    rw [Fin.snoc_castSucc]
    show Fin.append (Fin.snoc (fun i : Fin n => w (Fin.castAdd m i)) t)
        (fun j : Fin m => w (Fin.natAdd n j)) (Fin.castAdd m j.castSucc) = w (Fin.castAdd m j)
    rw [Fin.append_left, Fin.snoc_castSucc]

theorem projFirst_cyl {n m : ℕ} {C : Set (Fin (n+m) → ℝ)}
    (hC : C ⊆ WilkiesDesign.E.cubeC (n+m)) :
    WilkiesDesign.E.projFirst (n+1) m ''
      ({x : Fin (n + 1 + m) → ℝ | (fun i => x (Work.WilE8.skipInj n m i)) ∈ C} ∩
        WilkiesDesign.E.cubeC (n + 1 + m))
    = {z : Fin (n+1) → ℝ | Fin.init z ∈ WilkiesDesign.E.projFirst n m '' C} ∩
        WilkiesDesign.E.cubeC (n+1) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hxmem, hxeq⟩
    rcases hxmem with ⟨hxC, hxcube⟩
    constructor
    · refine ⟨fun i => x (Work.WilE8.skipInj n m i), hxC, ?_⟩
      funext i
      show x (Work.WilE8.skipInj n m (Fin.castAdd m i)) = z i.castSucc
      rw [Work.WilE8.Star.skipInj_castAdd_castSucc]
      rw [← hxeq]
      rfl
    · intro i
      show |z i| ≤ 1
      rw [show z i = x (Fin.castAdd m i) from by rw [← hxeq]; rfl]
      exact hxcube _
  · intro hz
    rcases hz with ⟨hz1, hz2⟩
    rcases hz1 with ⟨c, hcC, hceq⟩
    refine ⟨Work.WilE8.Star.insCoord n m c (z (Fin.last n)), ⟨?_, ?_⟩, ?_⟩
    · show (fun i => Work.WilE8.Star.insCoord n m c (z (Fin.last n))
          (Work.WilE8.skipInj n m i)) ∈ C
      rw [show (fun i => Work.WilE8.Star.insCoord n m c (z (Fin.last n))
            (Work.WilE8.skipInj n m i)) = c
          from funext (Work.WilE8.Star.insCoord_skipInj n m c (z (Fin.last n)))]
      exact hcC
    · exact Work.WilE8.Star.insCoord_cube (n := n) (m := m) (hC hcC) (hz2 (Fin.last n))
    · show WilkiesDesign.E.projFirst (n+1) m
          (Work.WilE8.Star.insCoord n m c (z (Fin.last n))) = z
      rw [projFirst_insCoord, hceq, Fin.snoc_init_self]

end Work.WilE8.Star
