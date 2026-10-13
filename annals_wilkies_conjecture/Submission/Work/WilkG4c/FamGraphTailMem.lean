import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Reindex3

namespace Work.WilkG4c

theorem FamGraphTailMem (S : WilkiesDesign.SOMin) {p n a Dg : ℕ}
    {ψ : (Fin p → ℝ) → (Fin n → ℝ) → ℝ}
    (hψ : WilkiesDesign.CG.famGraph ψ ∈ S.Ω a Dg (p + n + 1)) :
    WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => ψ l (Fin.tail t)) ∈
      S.Ω (a + 64 * ((p + (n + 1) + 1) + (p + n + 1)) + 64)
        (Dg + 32 * ((p + (n + 1) + 1) + (p + n + 1)) + 32) (p + (n + 1) + 1) := by
  -- `famGraph (fun l t => ψ l (tail t))` is the coordinate preimage of `famGraph ψ` along the
  -- insertion `ι` of a gap at position `p` (the dropped coordinate `t 0` of the `n+1` variables).
  -- The `Ω`-bound is then exactly `Work.WilG5.coordPre_mem`.
  set ι : Fin (p + n + 1) → Fin (p + (n + 1) + 1) :=
      Fin.succAbove (⟨p, by omega⟩ : Fin (p + n + 1 + 1)) with hι
  have hset : WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => ψ l (Fin.tail t))
      = Work.WilG5.coordPre ι (WilkiesDesign.CG.famGraph ψ) := by
    ext w
    change (w (Fin.last (p + (n + 1))) =
          ψ (fun i : Fin p => Fin.init w (Fin.castAdd (n + 1) i))
            (Fin.tail (fun j : Fin (n + 1) => Fin.init w (Fin.natAdd p j))))
        ↔ ((w ∘ ι) (Fin.last (p + n)) =
            ψ (fun i : Fin p => Fin.init (w ∘ ι) (Fin.castAdd n i))
              (fun j : Fin n => Fin.init (w ∘ ι) (Fin.natAdd p j)))
    -- `ι` fixes the value coordinate ...
    have hιlast : ι (Fin.last (p + n)) = Fin.last (p + (n + 1)) := by
      rw [hι]
      rw [Fin.succAbove_of_le_castSucc (⟨p, by omega⟩ : Fin (p+n+1+1)) (Fin.last (p+n)) (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega)]
      apply Fin.ext
      simp [Fin.val_last]
      omega
    have hlast : (w ∘ ι) (Fin.last (p + n)) = w (Fin.last (p + (n + 1))) := by
      rw [Function.comp_apply, hιlast]
    -- ... sends the `p` parameters to the first `p` coordinates ...
    have hpar : (fun i : Fin p => Fin.init (w ∘ ι) (Fin.castAdd n i)) =
        (fun i : Fin p => Fin.init w (Fin.castAdd (n + 1) i)) := by
      funext i
      show (w ∘ ι) ((Fin.castAdd n i).castSucc) = w ((Fin.castAdd (n + 1) i).castSucc)
      have hid : ι ((Fin.castAdd n i).castSucc) = (Fin.castAdd (n + 1) i).castSucc := by
        rw [hι]
        rw [Fin.succAbove_of_castSucc_lt (⟨p, by omega⟩ : Fin (p+n+1+1))
          ((Fin.castAdd n i).castSucc) (by
            simp only [Fin.lt_def, Fin.val_castSucc]; exact i.isLt)]
        rfl
      rw [Function.comp_apply, hid]
    -- ... and shifts the `n` surviving variables by one, i.e. drops `t 0` (a `tail`).
    have hx : (fun j : Fin n => Fin.init (w ∘ ι) (Fin.natAdd p j)) =
        (Fin.tail (fun j : Fin (n + 1) => Fin.init w (Fin.natAdd p j))) := by
      funext k
      show (w ∘ ι) ((Fin.natAdd p k).castSucc) =
        Fin.tail (fun j : Fin (n + 1) => w ((Fin.natAdd p j).castSucc)) k
      have hid : ι ((Fin.natAdd p k).castSucc) = (Fin.natAdd p (Fin.succ k)).castSucc := by
        rw [hι]
        rw [Fin.succAbove_of_le_castSucc (⟨p, by omega⟩ : Fin (p+n+1+1))
          ((Fin.natAdd p k).castSucc) (by
            simp only [Fin.le_def, Fin.val_castSucc, Fin.val_natAdd]; omega)]
        apply Fin.ext
        simp [Fin.val_natAdd]
        omega
      rw [Function.comp_apply, hid]
      rfl
    rw [hlast, hpar, hx]
  rw [hset]
  exact Work.WilG5.coordPre_mem (S := S) (m := p + n + 1) (N := p + (n + 1) + 1) (ι := ι) hψ

end Work.WilkG4c
