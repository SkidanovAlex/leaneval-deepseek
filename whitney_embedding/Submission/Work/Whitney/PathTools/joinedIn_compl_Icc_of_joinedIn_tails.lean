import Mathlib
import Submission.Work.Whitney.PathTools.arc_complement_interval_of_inter_singleton
import Submission.Work.Whitney.PathTools.minimal_separator_no_cut_point

namespace Work.Whitney.PathTools

open Set

theorem joinedIn_compl_Icc_of_joinedIn_tails {σ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hσ : Continuous σ) (hinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ σ '' Set.Icc (0:ℝ) 1)
    (hy : y ∉ σ '' Set.Icc (0:ℝ) 1)
    (h : ∀ u ∈ Set.Ioc (0:ℝ) 1, JoinedIn ((σ '' Set.Icc u 1))ᶜ x y) :
    JoinedIn ((σ '' Set.Icc (0:ℝ) 1))ᶜ x y := by
  have hT : ∀ {K L : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hL : IsCompact L)
      {p : EuclideanSpace ℝ (Fin 2)}, K ∩ L = {p} → ∀ {x y : EuclideanSpace ℝ (Fin 2)},
      x ∉ K ∪ L → y ∉ K ∪ L → JoinedIn (Kᶜ) x y → JoinedIn (Lᶜ) x y →
      JoinedIn ((K ∪ L)ᶜ) x y := by
    intro K L hK hL p hKL x y hx' hy' h₁ h₂
    exact Grid.janis_singleton_plane hK hL (p := p) hKL hx' hy' h₁ h₂
  exact (arc_complement_interval_of_inter_singleton hT hσ hinj).joinedIn x
    (by simpa only [mem_compl_iff] using hx) y (by simpa only [mem_compl_iff] using hy)

end Work.Whitney.PathTools
