import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.SigmaAux
import Submission.Work.WilE7.CoreStep.GermDefs

namespace Work.CoreStep

/-- The base projection of the pair point `pairPtUp u v` (in unsplit coordinates `ℝ^{pPair n m}`)
is the common base point `π_n` of `u`. -/
theorem pairBaseFst_absPt_pairPtUp {n m : ℕ} (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) :
    pairBaseFst n m (Work.WilE7.MainDesign.absPt (Work.WilE7.CoreStep.pairPtUp u v)) =
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) := by
  have hpt : Work.WilE7.MainDesign.absPt (Work.WilE7.CoreStep.pairPtUp u v)
      = Work.WilE7.CoreStep.pairPt u v := by
    funext j
    exact congrArg (Work.WilE7.CoreStep.pairPt u v) (Fin.ext rfl)
  rw [hpt]
  funext i
  simp only [pairBaseFst, Work.WilE7.CoreStep.pairPt,
    WilkiesDesign.E.projFirst, Work.WilE7.CoreStep.absPtInv]
  rw [show (Fin.castLE (le_pPair n m) i : Fin (Work.WilE7.CoreStep.pPair n m))
      = Fin.castLE (by omega : (n + (m+1)) ≤ (n + (m+1)) + (n + (m+1)))
          (Fin.castLE (by omega : n ≤ n + (m+1)) i) from Fin.ext rfl]
  rw [Fin.append_left']
  exact congrArg (Work.WilE7.MainDesign.absPt u) (Fin.ext rfl)

theorem havoid_of_sigma {n m s : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (Sig : List (WilkiesDesign.E.SemiPf (n + s)))
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hW : ∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
      Work.CoreStep.pairSubBaseFst n m W ⊆
        ⋃ S ∈ Sig, WilkiesDesign.E.projFirst n s '' S.set)
    (C : Set (Fin n → ℝ))
    (hdisj : ∀ S ∈ Sig, Disjoint C (WilkiesDesign.E.projFirst n s '' S.set)) :
    ∀ (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (x₀ : Fin n → ℝ),
      u ∈ T.X.set → v ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ → x₀ ∈ C →
      Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      ∀ W ∈ Wl, Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j := by
  intro u v x₀ hu hv hbaseu hbasev hx₀C huv W hWl hWmem
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : pPair n m - W.j < n + (m+1) - T.j`, so `hW` covers the base projection of `W`.
  have hsub := hW W hWl hcon
  -- The pair point lies in `W`, so its base projection lies in `pairSubBaseFst n m W`,
  -- and that base projection is exactly `x₀`.
  have hbase : pairBaseFst n m
      (Work.WilE7.MainDesign.absPt (Work.WilE7.CoreStep.pairPtUp u v)) ∈
      pairSubBaseFst n m W := ⟨_, ⟨_, hWmem, rfl⟩, rfl⟩
  rw [pairBaseFst_absPt_pairPtUp u v, hbaseu] at hbase
  -- Hence `x₀ ∈ ⋃ S ∈ Sig, π_n(S)`, contradicting the disjointness of `C` and the Σ-family.
  obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp (hsub hbase)
  exact (Set.disjoint_left.mp (hdisj S hS)) hx₀C hxS

end Work.CoreStep
