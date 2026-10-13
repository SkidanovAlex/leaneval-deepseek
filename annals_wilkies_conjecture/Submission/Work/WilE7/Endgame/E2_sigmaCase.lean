import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.DimAPI.cylDecomp_fiber
import Submission.Work.WilE7.coreLT_succ.SigmaCase

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)

theorem E2_sigmaCase {n m s : ℕ} (B : Finset (Set (Fin (n + 1) → ℝ)))
    (hB : WilkiesDesign.E.IsCylDecompOn (n + 1) (WilkiesDesign.E.cubeC (n + 1)) B)
    (b : Set (Fin n → ℝ)) (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (T : WilkiesDesign.E.Stratum 0 ((n + 1) + m)) (S : WilkiesDesign.E.SemiPf (n + s))
    (Z : WilkiesDesign.E.SemiPf ((n + 1) + (m + s)))
    (hZ : WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set =
      WilkiesDesign.E.projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T ∩
        {y : Fin (n + 1) → ℝ | Fin.init y ∈ WilkiesDesign.E.projFirst n s '' S.set})
    (hS : b ⊆ WilkiesDesign.E.projFirst n s '' S.set)
    (hcompat : ∀ κ ∈ B.filter (fun κ => Fin.init '' κ = b),
      κ ⊆ WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set ∨
        Disjoint κ (WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set)) :
    WilkiesDesign.E.IsCylDecompOn (n + 1) (WilkiesDesign.E.cubeC (n + 1) ∩ {z | Fin.init z ∈ b})
        (B.filter (fun κ => Fin.init '' κ = b)) ∧
      (∀ κ ∈ B.filter (fun κ => Fin.init '' κ = b), κ ∈ B) ∧
      (∀ κ ∈ B.filter (fun κ => Fin.init '' κ = b), Fin.init '' κ = b) ∧
      (∀ κ ∈ B.filter (fun κ => Fin.init '' κ = b),
        κ ⊆ WilkiesDesign.E.projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T ∨
          Disjoint κ (WilkiesDesign.E.projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the cells of `B` lying over `b` decompose the fibre over `b`
    exact Work.WilE7.DimAPI.cylDecomp_fiber (WilkiesDesign.E.cubeC (n + 1)) B hB b hb
  · intro κ hκ; exact Finset.mem_of_mem_filter κ hκ
  · intro κ hκ; exact (Finset.mem_filter.mp hκ).2
  · -- Σ-case: the fibre product `Z` cuts out exactly the part of `π_{n+1}(T)` over `b`
    intro κ hκ
    have hbκ : Fin.init '' κ ⊆ WilkiesDesign.E.projFirst n s '' S.set := by
      rw [(Finset.mem_filter.mp hκ).2]; exact hS
    exact Work.WilE7.coreLT_succ.compat_of_fibreProd T S Z hZ hbκ (hcompat κ hκ)

end Work.WilE7.Endgame
