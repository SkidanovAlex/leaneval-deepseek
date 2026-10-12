import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.exists_jointGramLab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.corpusBox_gram_values` — the Gram matrix of the corpus box modes

The honest box modes of FS §8 at the corpus localization function
`Work.BoseK15.corpusBox` are

* the χ-modes `qVec ℓ (kmomLab ℓ N k) = Q(e^{ikx}χ_Λ)` for the cube labels `k : Lab N`,
* the θ-modes `thetaExp ℓ (kmomLab ℓ N s) = e^{isx}1_Λ` for the nonzero labels,
* the condensate `thetaFun ℓ = 1_Λ`.

This module computes their whole Gram matrix, entry by entry, in the exact
normalisation used by FS (`realIP f g = ∫ Re(conj f · g)`):

| row | value | source |
|---|---|---|
| `⟨qVec k, θ⟩` | `0` | `realIP_qVec_thetaFun` (below) |
| `⟨qVec k, qVec k'⟩` | `ℓ³·χ̂²((k−k')ℓ) − ℓ³·χ̂(kℓ)χ̂(k'ℓ)` | `Work.BoseB4.realIP_qVec_qVec` |
| `⟨thetaExp s, qVec k⟩` | `ℓ³·χ̂(ℓ(k−s))` | `Work.BoseB4.BoxData.realIP_thetaExp_qVec` |
| `⟨thetaExp s, thetaExp t⟩` | `ℓ³·δ_{st}` | `Work.BoseB4.realIP_thetaExp_thetaExp_of_cell` |
| `⟨thetaExp s, θ⟩` | `0` | `Work.BoseB4.realIP_thetaExp_thetaFun_of_cell` |
| `⟨θ, θ⟩` | `ℓ³` | `Work.BoseB4.realIP_thetaFun_thetaFun` |

The first row, `Q(e^{ikx}χ_Λ) ⊥ θ`, is the one entry that was not yet in the corpus:
`qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)·θ` is *by definition* the `Q`-projection of the
localised plane wave, so its θ-overlap vanishes, but only the two pieces
`⟨e^{ikx}χ_Λ, θ⟩ = ℓ³χ̂(kℓ)` and `⟨θ, θ⟩ = ℓ³` were proved.  It is supplied here as
the general one-liner `Work.BoseB4.realIP_qVec_thetaFun`, since it is a natural
addition to the `Work.BoseB4` Gram dictionary.  The θ/θ mode rows (rows 4 and 5) and
the fingerprint of the cube's momenta are exactly `corpusBox_theta_rows`
(`Submission.Work.BoseBoxFock.exists_jointGramLab`, itself proved from the unit-cube
Fourier orthogonality by rewriting `kmomLab ℓ N n = ℓ⁻¹ • vec (labVec N n)`).

Everything is a genuine `L²(Λ)` computation; no hypothesis beyond `0 < ℓ` is used.
-/

noncomputable section

namespace Work.BoseB4

open MeasureTheory Classical

/-- The real part of `conj(a − c·b)·d` for a real scalar `c` splits:
`Re(conj(a − c b)·d) = Re(conj a·d) − c·Re(conj b·d)`.  (The mirror image of
`Work.BoseB4.BoxData.conj_mul_sub_re`.) -/
private lemma re_conj_sub_mul (a b d : ℂ) (c : ℝ) :
    ((starRingEnd ℂ) (a - (c : ℂ) * b) * d).re
      = ((starRingEnd ℂ) a * d).re - c * ((starRingEnd ℂ) b * d).re := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.sub_re,
    Complex.mul_im, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **FS `def:projections` on `qVec`: `Q(e^{ikx}χ_Λ) ⊥ θ`.**

`qVec ℓ k = e^{ikx}χ_Λ − χ̂(kℓ)·θ` is the localised plane wave with its condensate
component subtracted, so its overlap with the condensate vanishes; the computation
is the two proved overlaps `⟨e^{ikx}χ_Λ, θ⟩ = ℓ³χ̂(kℓ)`
(`realIP_modeVec_thetaFun`) and `⟨θ, θ⟩ = ℓ³` (`realIP_thetaFun_thetaFun`). -/
theorem realIP_qVec_thetaFun (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    B.realIP (B.qVec ℓ k) (B.thetaFun ℓ) = 0 := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((starRingEnd ℂ) (B.qVec ℓ k x) * B.thetaFun ℓ x).re
        = ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.thetaFun ℓ x).re
          - B.hatChi (ℓ • k) * ((starRingEnd ℂ) (B.thetaFun ℓ x) * B.thetaFun ℓ x).re := by
    intro x
    rw [BoxData.qVec_apply]
    exact re_conj_sub_mul _ _ _ _
  have hexp : B.realIP (B.qVec ℓ k) (B.thetaFun ℓ)
      = B.realIP (B.modeVec ℓ k) (B.thetaFun ℓ)
        - B.hatChi (ℓ • k) * B.realIP (B.thetaFun ℓ) (B.thetaFun ℓ) := by
    rw [BoxData.realIP_apply, BoxData.realIP_apply, BoxData.realIP_apply, funext hpt,
      MeasureTheory.integral_sub (B.integrable_conj_modeVec_thetaFun hℓ k)
        ((B.integrable_conj_thetaFun_thetaFun ℓ).const_mul _),
      MeasureTheory.integral_const_mul]
  rw [hexp, realIP_modeVec_thetaFun B hℓ k, realIP_thetaFun_thetaFun B hℓ]
  ring

end Work.BoseB4

namespace Work.BoseBoxFock

open _root_.Work.BoseB4 GramLab

/-- **The Gram matrix of the corpus box modes** at a cube `Lab N` and box side `ℓ > 0`:
the χ-modes `Q(e^{ikx}χ_Λ)` are orthogonal to the condensate `θ`, their Gram matrix is
`ℓ³` times FS's box kernel `χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`, the θ-modes are orthogonal to
the χ-modes with overlap `ℓ³χ̂(ℓ(k−s))`, orthonormal (`ℓ³δ_{st}`) among themselves,
orthogonal to the condensate, and the condensate has norm `ℓ³`. -/
theorem corpusBox_gram_values (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) : (∀ k : Lab N, Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k)) (Work.BoseK15.corpusBox.thetaFun ℓ) = 0) ∧ (∀ k k' : Lab N, Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k)) (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k')) = ℓ ^ 3 * Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi (kmomLab ℓ N k) (kmomLab ℓ N k')) ∧ (∀ s k : Lab N, s ≠ 0 → Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s)) (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k)) = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • (kmomLab ℓ N k - kmomLab ℓ N s))) ∧ (∀ s t : Lab N, s ≠ 0 → t ≠ 0 → Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s)) (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N t)) = if s = t then ℓ ^ 3 else 0) ∧ (∀ s : Lab N, s ≠ 0 → Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s)) (Work.BoseK15.corpusBox.thetaFun ℓ) = 0) ∧ Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.thetaFun ℓ) (Work.BoseK15.corpusBox.thetaFun ℓ) = ℓ ^ 3 := by
  -- the θ-mode rows of the cube and the momentum fingerprint of `kmomLab`
  obtain ⟨hEE, hEF⟩ := corpusBox_theta_rows ℓ hℓ N
  refine ⟨?_, ?_, ?_, hEE, hEF, ?_⟩
  · -- `Q(e^{ikx}χ_Λ) ⊥ θ`
    intro k
    exact realIP_qVec_thetaFun Work.BoseK15.corpusBox hℓ (kmomLab ℓ N k)
  · -- the box kernel (FS `eq:Commutator_general`), in the `ccrKernel` form
    intro k k'
    rw [realIP_qVec_qVec Work.BoseK15.corpusBox hℓ]
    rfl
  · -- the θ/χ cross Gram product (only the lattice condition `s ≠ 0` is used)
    intro s k hs
    exact Work.BoseB4.BoxData.realIP_thetaExp_qVec Work.BoseK15.corpusBox hℓ
      (kmomLab ℓ N s) (kmomLab ℓ N k) (hEF s hs)
  · -- the norm of the condensate
    exact realIP_thetaFun_thetaFun Work.BoseK15.corpusBox hℓ

end Work.BoseBoxFock
