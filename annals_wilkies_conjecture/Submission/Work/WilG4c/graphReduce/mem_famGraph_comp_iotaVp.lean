import Mathlib
import Submission.Work.WilG4c.SliceNilDefs

namespace Work.WilG4c.graphReduce

theorem mem_famGraph_comp_iotaVp (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (Work.WilkG4c.Kz p n + 2) → ℝ) :
    (u ∘ Work.WilkG4c.iotaVp p n) ∈ WilkiesDesign.CG.famGraph f ↔
      u (Work.WilkG4c.vpPos p n) =
        f (fun i : Fin p => u (Work.WilkG4c.lPos p n i))
          (fun j : Fin (n + 1) => u (Work.WilkG4c.ypPos p n j)) := by
  -- The three coordinate computations.  `famGraph f` reads the parameter `l` off the
  -- first `p` coordinates, the cube point `y` off the next `n+1`, and the value off the
  -- last one; `iotaVp` sends those coordinates to `lPos`, `ypPos` and `vpPos` respectively.
  have hfun_i : (fun i : Fin p => Fin.init (u ∘ Work.WilkG4c.iotaVp p n)
        (Fin.castAdd (n + 1) i))
      = fun i : Fin p => u (Work.WilkG4c.lPos p n i) := by
    funext i
    show u (Work.WilkG4c.iotaVp p n ((Fin.castAdd (n + 1) i).castSucc))
      = u (Work.WilkG4c.lPos p n i)
    rw [show Work.WilkG4c.iotaVp p n (Fin.castAdd (n + 1) i).castSucc
        = Work.WilkG4c.lPos p n i from by
      rw [Fin.castSucc_castAdd]
      simp only [Work.WilkG4c.iotaVp, Work.WilkG4c.lPos, Fin.append_left]]
  have hfun_j : (fun j : Fin (n + 1) => Fin.init (u ∘ Work.WilkG4c.iotaVp p n)
        (Fin.natAdd p j))
      = fun j : Fin (n + 1) => u (Work.WilkG4c.ypPos p n j) := by
    funext j
    show u (Work.WilkG4c.iotaVp p n ((Fin.natAdd p j).castSucc))
      = u (Work.WilkG4c.ypPos p n j)
    rw [show Work.WilkG4c.iotaVp p n (Fin.natAdd p j).castSucc
        = Work.WilkG4c.ypPos p n j from by
      rw [Fin.castSucc_natAdd]
      simp only [Work.WilkG4c.iotaVp, Work.WilkG4c.ypPos, Fin.append_right]
      rw [show j.castSucc = Fin.castAdd 1 j from by ext; rfl]
      simp only [Fin.append_left]]
  have hlast : (u ∘ Work.WilkG4c.iotaVp p n) (Fin.last (p + (n + 1)))
      = u (Work.WilkG4c.vpPos p n) := by
    show u (Work.WilkG4c.iotaVp p n (Fin.last (p + (n + 1))))
      = u (Work.WilkG4c.vpPos p n)
    rw [show Work.WilkG4c.iotaVp p n (Fin.last (p + (n + 1)))
        = Work.WilkG4c.vpPos p n from by
      rw [← Fin.natAdd_last]
      simp only [Work.WilkG4c.iotaVp, Fin.append_right]
      rw [show Fin.last (n + 1) = Fin.natAdd (n + 1) (Fin.last 0) from by
        rw [Fin.natAdd_last]]
      simp only [Fin.append_right, Work.WilkG4c.vpPos]]
  rw [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf]
  show ((u ∘ Work.WilkG4c.iotaVp p n) (Fin.last (p + (n + 1)))
        = f (fun i : Fin p => Fin.init (u ∘ Work.WilkG4c.iotaVp p n)
              (Fin.castAdd (n + 1) i))
            (fun j : Fin (n + 1) => Fin.init (u ∘ Work.WilkG4c.iotaVp p n)
              (Fin.natAdd p j)))
    ↔ u (Work.WilkG4c.vpPos p n) = f (fun i : Fin p => u (Work.WilkG4c.lPos p n i))
        (fun j : Fin (n + 1) => u (Work.WilkG4c.ypPos p n j))
  rw [hlast, hfun_i, hfun_j]

end Work.WilG4c.graphReduce
