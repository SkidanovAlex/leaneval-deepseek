import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.bessel_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.FRK

/-!
# `Work.BoseBoxFock.FRK.honestChiFrame`

The honest **frame bound** of the χ-modes of the box model: for the coordinate vectors
`(HM μ).f k : Fin m → ℝ` of the `L²(Λ)`-vectors `ℓ^{-3/2} Q(e^{ikx}χ_Λ)`, the frame operator
`Σ_k |f k⟩⟨f k|` is dominated by `(48/π)·1` in the quadratic-form sense:

  `Σ_k ⟪f k, w⟫² ≤ (48/π)·Σ_l (w l)²`.

This is one half of `Work.BoseBoxFock.bessel_honest` (its `frame_of_synthesis` step, fed by the
lattice Parseval bound `frame_int_bound`), restated as a standalone lemma about the honest mode
family.  The Fock-space Bessel inequality is *not* needed here.
-/

theorem honestChiFrame {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∀ w : Fin (HM μ).m → ℝ,
      ∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseB4.gram ((HM μ).f k) w) ^ 2
        ≤ (48 / Real.pi) * ∑ l : Fin (HM μ).m, (w l) ^ 2 := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- the Gram matrix of the honest χ-modes is the corpus `χ̂²`-kernel (minus the condensate row)
  have hgram : ∀ k k' : Work.BoseBoxFock.Lab (HM μ).N,
      Work.BoseB4.gram ((HM μ).f k) ((HM μ).f k')
        = Work.BoseK15.corpusBox.hatChiSq
            (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k
              - Work.BoseBoxFock.labVec (HM μ).N k'))
          - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k))
            * Work.BoseK15.corpusBox.hatChi
                (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k')) := by
    intro k k'
    rw [(HM μ).hf k k', Work.BoseB7.ccrKernel,
      Work.BoseBoxFock.smul_kmomLab_sub (ne_of_gt hℓ) (HM μ).N k k',
      Work.BoseBoxFock.smul_kmomLab (ne_of_gt hℓ) (HM μ).N k,
      Work.BoseBoxFock.smul_kmomLab (ne_of_gt hℓ) (HM μ).N k']
  -- the "synthesis" bound: the lattice frame bound of `frame_int_bound`
  have hsyn : ∀ c : Work.BoseBoxFock.Lab (HM μ).N → ℝ,
      ∑ l : Fin (HM μ).m, (∑ k : Work.BoseBoxFock.Lab (HM μ).N, c k * (HM μ).f k l) ^ 2
        ≤ (48 / Real.pi) * ∑ k : Work.BoseBoxFock.Lab (HM μ).N, (c k) ^ 2 := by
    intro c
    rw [(Work.BoseB4.gram_quadForm_eq_sum_sq (HM μ).f c).symm]
    have hcongr : ∑ i : Work.BoseBoxFock.Lab (HM μ).N,
          ∑ j : Work.BoseBoxFock.Lab (HM μ).N,
            c i * Work.BoseB4.gram ((HM μ).f i) ((HM μ).f j) * c j
        = ∑ i : Work.BoseBoxFock.Lab (HM μ).N,
            ∑ j : Work.BoseBoxFock.Lab (HM μ).N, c i * c j *
              (Work.BoseK15.corpusBox.hatChiSq
                  (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N i
                    - Work.BoseBoxFock.labVec (HM μ).N j))
                - Work.BoseK15.corpusBox.hatChi
                    (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N i))
                  * Work.BoseK15.corpusBox.hatChi
                      (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hgram i j]
      ring
    rw [hcongr]
    exact Work.BoseBoxFock.frame_int_bound (HM μ).N c
  exact Work.BoseBoxFock.frame_of_synthesis (HM μ).f (48 / Real.pi) (by positivity) hsyn

end Work.BoseBoxFock.FRK
