import Mathlib
import Submission.Work.WilE7.Endgame.E2_union_compat

namespace Work.WilE7.Endgame
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)

theorem E2_union_compat_sub {n m r K : ℕ} {b : Set (Fin n → ℝ)}
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    (S : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (k : Fin r → ℕ) (s : (t : Fin r) → Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ b →
      Fin.append x (s t j x) ∈ Work.WilE7.MainDesign.absSet (S t))
    (hcovS : ∀ (t : Fin r), ∀ z ∈ Work.WilE7.MainDesign.absSet (S t),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
      ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (hcovT : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
      ∃ t : Fin r, Work.WilE7.MainDesign.absSet (S t) ⊆ Work.WilE7.MainDesign.absSet T ∧
        z ∈ Work.WilE7.MainDesign.absSet (S t))
    (TT : Fin K → (Fin n → ℝ) → ℝ)
    (hgr : ∀ κ ∈ Work.WilE7.cfs b TT, ∀ (t : Fin r) (j : Fin (k t)),
      κ ⊆ Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)) ∨
        Disjoint κ (Work.WilE7.gr b (fun x => (s t j x) (Fin.last m))))
    (hcell : ∀ κ ∈ Work.WilE7.cfs b TT, Fin.init '' κ = b) :
    ∀ κ ∈ Work.WilE7.cfs b TT,
      κ ⊆ Work.WilE7.CoreStep.projTopSet T ∨
        Disjoint κ (Work.WilE7.CoreStep.projTopSet T) := by
  intro κ hκ
  by_cases h : (κ ∩ Work.WilE7.CoreStep.projTopSet T).Nonempty
  · left
    obtain ⟨w, hwκ, hwT⟩ := h
    rw [Work.WilE7.CoreStep.projTopSet, Set.mem_image] at hwT
    obtain ⟨z, hzT, hzw⟩ := hwT
    have hbw : Fin.init w ∈ b := by
      have hmem : Fin.init w ∈ Fin.init '' κ := ⟨w, hwκ, rfl⟩
      rwa [hcell κ hκ] at hmem
    have hb : projFirst n (m + 1) z ∈ b := by
      rw [← Work.WilE7.CoreStep.projTop_init n m z, hzw]; exact hbw
    obtain ⟨t, hSTt, hzt⟩ := hcovT z hzT hb
    obtain ⟨j, hjs⟩ := hcovS t z hzt hb
    have hlastw : w (Fin.last n) = (s t j (Fin.init w)) (Fin.last m) := by
      rw [← hzw, Work.WilE7.CoreStep.projTop_last, Work.WilE7.CoreStep.projTop_init, hjs]
    have hwgr : w ∈ Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)) := by
      rw [Work.WilE7.gr, Set.mem_ofPred_eq]
      exact ⟨hbw, hlastw⟩
    rcases hgr κ hκ t j with hsubgr | hdis
    · intro y hy
      exact E2_gr_subset_projTopSet (fun x => s t j x) (fun x hx => hsub t j x hx) hSTt
        (hsubgr hy)
    · exact absurd hwgr (Set.disjoint_left.mp hdis hwκ)
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp h

end Work.WilE7.Endgame
