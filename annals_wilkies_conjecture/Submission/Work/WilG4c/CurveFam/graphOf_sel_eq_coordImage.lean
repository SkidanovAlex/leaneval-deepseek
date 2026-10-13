import Mathlib
import Submission.Work.WilG5.Basic

namespace Work.WilG4c.CurveFam

theorem graphOf_sel_eq_coordImage {p n : ℕ} (F : (Fin (p + 1) → ℝ) → (Fin n → ℝ)) (j : Fin n) :
    WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ => F (Fin.snoc (Fin.init w) (w (Fin.last p))) j) =
      Work.WilG5.coordImage (Fin.snoc (fun i : Fin (p + 1) => Fin.castAdd n i) (Fin.natAdd (p + 1) j))
        {z : Fin ((p + 1) + n) → ℝ | ∀ k : Fin n,
          z (Fin.natAdd (p + 1) k) = F (fun i => z (Fin.castAdd n i)) k} := by
  -- The left-hand function is `w ↦ F w j` (via `Fin.snoc_init_self`), so the left-hand set is
  -- `{u : Fin ((p+1)+1) → ℝ | u (last) = F (init u) j}`.  The right-hand index map `ι` keeps
  -- the first `p+1` coordinates (via `Fin.castAdd n`) and the `j`-th coordinate of the last
  -- `n`-block (via `Fin.natAdd (p+1) j`); the middle set `A` records that the last `n`
  -- coordinates of `z` are `F` of the first `p+1`.
  ext u
  simp only [WilkiesDesign.graphOf, Work.WilG5.coordImage, Set.mem_ofPred_eq]
  constructor
  · intro hu
    rw [Fin.snoc_init_self] at hu
    refine ⟨Fin.append (Fin.init u) (F (Fin.init u)), ?_, ?_⟩
    · intro k
      rw [Fin.append_right]
      have hfun : (fun i : Fin (p + 1) =>
          Fin.append (Fin.init u) (F (Fin.init u)) (Fin.castAdd n i)) = Fin.init u := by
        funext i
        rw [Fin.append_left]
      rw [hfun]
    · funext t
      revert t
      refine Fin.addCases (motive := fun t => Fin.append (Fin.init u) (F (Fin.init u))
        (Fin.snoc (α := fun _ => Fin ((p+1)+n)) (fun i : Fin (p+1) => Fin.castAdd n i)
          (Fin.natAdd (p+1) j) t) = u t) ?_ ?_
      · intro i
        rw [show (Fin.castAdd 1 i : Fin ((p+1)+1)) = Fin.castSucc i from rfl,
          Fin.snoc_castSucc, Fin.append_left]
        rfl
      · intro k
        have hk : k = 0 := Fin.eq_zero k
        subst hk
        rw [show Fin.natAdd (p+1) (0 : Fin 1) = Fin.last (p+1) from Fin.ext rfl,
          Fin.snoc_last, Fin.append_right]
        exact hu.symm
  · rintro ⟨x, hx, hxu⟩
    rw [Fin.snoc_init_self]
    have hxinit : (fun i : Fin (p+1) => x (Fin.castAdd n i)) = Fin.init u := by
      funext i
      have h := congrFun hxu (Fin.castAdd 1 i)
      simp only [Function.comp_apply] at h
      rw [show (Fin.castAdd 1 i : Fin ((p+1)+1)) = Fin.castSucc i from rfl,
        Fin.snoc_castSucc] at h
      rw [h]
      rfl
    have hlast : u (Fin.last (p+1)) = x (Fin.natAdd (p+1) j) := by
      have h := congrFun hxu (Fin.last (p+1))
      simp only [Function.comp_apply] at h
      rw [Fin.snoc_last] at h
      exact h.symm
    rw [hlast, hx j, hxinit]

end Work.WilG4c.CurveFam
