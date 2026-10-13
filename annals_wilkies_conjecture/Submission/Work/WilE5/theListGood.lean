import Mathlib
import Submission.Work.WilE5.CellList
import Submission.Work.WilE5.Strat.flatLeafGoodP
import Submission.Work.WilE5.Strat.stateInvP
import Submission.Work.WilE5.Strat.levelData

namespace Work.WilE5

theorem theListGood {p q F : ℕ} (Me : Polynomial ℕ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hX : X.fmt ≤ F)
    (hE3 : ∀ (j : ℕ) (h : Fin j → WilkiesDesign.E.EAPoly (p + q) X.r) (ι : Fin j → Fin (p + q))
      (f : WilkiesDesign.E.EAPoly (p + q) X.r) (x : Fin (p + q) → ℝ),
      (∀ a, WilkiesDesign.E.eaEval X.c (h a) x = 0) →
      (Matrix.of fun a b => WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (ι b) (h a)) x).det ≠ 0 →
      (∀ m : Fin (p + q) → ℕ, (∀ a, m (ι a) = 0) →
        (∑ l, m l ≤ Me.eval (∑ a, WilkiesDesign.E.atomDeg (h a) + WilkiesDesign.E.atomDeg f)) →
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.opMono X.c h ι m f) x = 0) →
      ∀ᶠ y in nhds x, (∀ a, WilkiesDesign.E.eaEval X.c (h a) y = 0) →
        WilkiesDesign.E.eaEval X.c f y = 0) :
    ∀ S ∈ Work.WilE5.theList Me X, WilkiesDesign.E.Stratum.Good S := by
  intro S hS
  obtain ⟨σ, -, hSσ⟩ := (Work.WilE5.mem_theList).mp hS
  obtain ⟨k, hk, τ, hτ, rfl⟩ := Work.WilE5.exists_state_of_mem_cellStrata hSσ
  have hkF : k ∈ Finset.range (q + 1) := Finset.mem_range.mpr (List.mem_range.mp hk)
  have hInv := Work.WilE5.Strat.stateInvP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ))
    (MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q)
    (NPhi Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) k hkF τ hτ
  obtain ⟨⟨A, hA, hAΞ, hAν, hAΦ⟩, hΦΞ, hΞΦ, _, hcube, hdet⟩ := hInv
  obtain rfl : A = Work.WilE5.cell X σ := List.mem_singleton.mp hA
  obtain ⟨_, _, _, _, _, hΦN, hMuP, _⟩ :=
    Work.WilE5.Strat.levelData (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)) Me k hkF τ hτ
  have hMu : ∀ ψ ∈ τ.Φ, Me.eval ((∑ a : Fin τ.B.length,
      WilkiesDesign.E.atomDeg (Work.WilE5.hFun τ.B a)) + 2 * p +
      WilkiesDesign.E.atomDeg ψ) ≤
      (MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) τ.B.length := by
    intro ψ hψ
    exact hMuP ψ hψ
  exact Work.WilE5.Strat.flatLeafGoodP (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)) Me
    (MlOf Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q)
    (NPhi Me (Work.WilE5.cellSemi X (Work.WilE5.cell X σ)).deg p q) τ
    (Work.WilE5.cell X σ) (List.mem_singleton_self _) hE3 hΦN hMu hcube hAΞ hAν hAΦ hΞΦ hΦΞ hdet

end Work.WilE5
