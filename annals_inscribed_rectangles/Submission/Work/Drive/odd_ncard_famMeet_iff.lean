import Mathlib
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.FamBox.Smooth
import Submission.Work.Drive.FamBox.Engine
import Submission.Work.Drive.FamBox.famMeet_parity_of_even_boxBMeet

namespace Work.Drive

/-- **L6: the parity of the loop-vs-3-chain count is invariant under a jointly smooth family of
(loop, 3-chain) pairs.**  `L (t, s)` is the `t`-th loop of the family (closed for every `t`, `hloop`),
`N (t, x)` the `t`-th 3-chain (seam-invariant in `x`, `hseam`); the meet set
`Work.Drive.famMeet L N t` is `{p ∈ [0,1]^5 : p 0 = t ∧ L (p 0, p 1) = N (p 0, p 2, p 3, p 4)}`.
The five coordinates of `p` are `(t, s, x0, x1, x2)`.  `havoid` forbids meets on the slice faces
`x2 ∈ {0,1}`; `htrans` says the derivative of the difference map of the two sides is onto at every meet
(the two maps `famLoop L` and `famChain N` live on the *same* box, so this is the surjectivity of
`d(famLoop L) - d(famChain N)`, not the weaker sum of the two ranges); `hface` says that at a boundary
meet exactly one coordinate of the five-box is on a face, and the meet curve crosses that face
transversally (a common tangent vector `σ` of the two sides with nonzero `i`-th component). -/
theorem odd_ncard_famMeet_iff (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 4) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, L (Work.Drive.mk2 t 0) = L (Work.Drive.mk2 t 1))
    (hseam : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      N (Work.Drive.famPt t (Work.Drive.seamInv x)) = N (Work.Drive.famPt t x))
    (havoid : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L p = Work.Drive.famChain N p → (p 4 = 0 ∨ p 4 = 1) → False)
    (htrans : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L p = Work.Drive.famChain N p →
      Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
        (show EuclideanSpace ℝ (Fin 4) from mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
            (Work.Drive.famLoop L) p v)
          - (show EuclideanSpace ℝ (Fin 4) from mfderiv
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
            (Work.Drive.famChain N) p v)))
    (hface : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L p = Work.Drive.famChain N p → p ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 5),
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
            (Work.Drive.famLoop L) p σ
            = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
              (Work.Drive.famChain N) p σ ∧ σ i ≠ 0) :
    Odd ((Work.Drive.famMeet L N 0).ncard) ↔ Odd ((Work.Drive.famMeet L N 1).ncard) := by
  -- the two sides of the family are smooth
  have hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.famLoop L) :=
    Work.Drive.FamBox.contMDiff_famLoop L hL
  have hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.famChain N) :=
    Work.Drive.FamBox.contMDiff_famChain N hN
  -- the transversality hypothesis in the `Lf`-form
  have htransL : ∀ x : EuclideanSpace ℝ (Fin 5), x ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L x = Work.Drive.famChain N x →
      Function.Surjective (Work.Drive.FamBox.Lf (Work.Drive.famLoop L)
        (Work.Drive.famChain N) x) := by
    intro x hxbox heq w
    obtain ⟨v, hv⟩ := htrans x hxbox heq w
    exact ⟨v, hv⟩
  -- the face hypothesis in the `Lf`-form
  have hfaceL : ∀ b : EuclideanSpace ℝ (Fin 5), b ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop L b = Work.Drive.famChain N b →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 5),
          Work.Drive.FamBox.Lf (Work.Drive.famLoop L) (Work.Drive.famChain N) b σ = 0 ∧
            σ i ≠ 0 := by
    intro b hbox heq hbd
    obtain ⟨i, hi, hother, σ, hσ, hσi⟩ := hface b hbox heq hbd
    exact ⟨i, hi, hother, σ, by rw [Work.Drive.FamBox.Lf_apply, hσ, sub_self], hσi⟩
  -- the parity engine
  obtain ⟨hfin, heven⟩ :=
    Work.Drive.FamBox.even_ncard_boxBMeet (Work.Drive.famLoop L) (Work.Drive.famChain N)
      hF hG htransL hfaceL
  -- the single-face form of the face hypothesis
  have hfaceSet : ∀ b ∈ Work.Drive.FamBox.boxBMeet (Work.Drive.famLoop L) (Work.Drive.famChain N),
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) := by
    intro b hb
    obtain ⟨hbox, heq, hbd⟩ := hb
    obtain ⟨i, hi, hother, -⟩ := hfaceL b hbox heq hbd
    exact ⟨i, hi, hother⟩
  exact Work.Drive.FamBox.famMeet_parity_of_even_boxBMeet L N hloop hseam havoid hfin heven hfaceSet

end Work.Drive