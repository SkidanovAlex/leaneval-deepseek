import Mathlib
import Submission.Work.Drive.Mono.g3Wrapper
import Submission.Work.Drive.Mono.g3WitnessDefs
import Submission.Work.Drive.Mono.geom3_witnessData_Q
import Submission.Work.Drive.Mono.edgeFreeBox_of_margin
import Submission.Work.Drive.Mono.g3_assembly

/-!
# The single-level producer `Work.Drive.Mono.geom3DataAtU_exists`

The composition of the three pieces of the producer of `Work.Drive.Mono.Geom3Data` at one cutting
level `u`:

* the witness with `Q`-provenance, `Work.Drive.Mono.geom3_witnessData_Q`
  (`Submission/Work/Drive/Mono/geom3_witnessData_Q.lean`), which draws its tilt direction `V` from
  the countable family `Q` carried by `Work.Drive.Mono.G3Pointwise` and returns
  `Work.Drive.Mono.WitnessData3`;
* the transport of the one-event slice nullity of `Work.Drive.Mono.G3OneEv` from the family member
  `ng ∈ Q` to the datum's own direction triple `(V, a₀, b₀)`
  (`= (orthDir (shiftVσ σ 1) (unitDir ng), af ng, bf ng)` by construction of the witness);
* the assembly `Work.Drive.Mono.g3_assembly`
  (`Submission/Work/Drive/Mono/g3_assembly.lean`), which turns the witness bundle plus the
  pointwise facts into `Work.Drive.Mono.Geom3Data` at the prescribed `V`, given
  `Work.Drive.Mono.EdgeFree` for every half-width of the window — supplied here by
  `Work.Drive.Mono.edgeFreeBox_of_margin`
  (`Submission/Work/Drive/Mono/edgeFreeBox_of_margin.lean`) with the box radius `5/2*s`, i.e. from
  the witness's `A = ‖V - shiftVσ σ 1‖*(5/2*s) < h`, `h < B ≤ mE/2` and
  `h < B ≤ (boxSide 2 * s - |u|)/2`.

The result is the `hAtU` argument of `Work.Drive.Mono.geom3Data_exists_of_atU`, so that
`Work.Drive.Mono.geom3Data_exists = geom3Data_exists_of_atU g3_ae_oneEv geom3DataAtU_exists`.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Work.Drive.Mono

noncomputable section

set_option maxHeartbeats 1000000

theorem geom3DataAtU_exists
    (ψ : Submission.Diffeo) (K : Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (d : ℝ) (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (hBG : Work.Drive.Mono.BoxGenE ψ c σ s)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (hP : Work.Drive.Mono.G3Pointwise ψ K s u c σ) :
    ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      Work.Drive.Mono.Geom3Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q := by
  have hP0 := hP
  obtain ⟨hcut, ⟨δg, hδg, _hδgp⟩, hFC, hFB, ⟨εg, δg', hεg, hδg', _hε16, _hδ16, hnog⟩, hnb,
    ⟨mE, hmE, hhedge⟩, hOneEv⟩ := hP0
  obtain ⟨Q, af, bf, hQc, hQH, hQd, hQnv, hframe, hnullQ⟩ := hOneEv
  obtain ⟨V, n, a₀, b₀, ρ, A, B, N, γ, η, m, ng, hng, hn, hVe, ha, hb, hW⟩ :=
    Work.Drive.Mono.geom3_witnessData_Q ψ K hr hrs hs hu c σ hcut hFC hFB
      (εg := εg) (δg := δg') hεg hδg' hnog hnb (mE := mE) hmE hhedge
      Q hQc hQH hQd hQnv af bf hframe
  have hW0 := hW
  obtain ⟨_hV1, _haxis, _hV8, _hn1, _hVn, _hgood, _ha1, _hb1, _hab, _hVa, _hVb, _hnb,
    _hρ, _hApos, _hAB, hAdef, _hBwin, _hBδg, hBmE, hBbs, _hcl1, _hcl2, _hcl3, _hcl4,
    _hη, _hm, _hBm, _hγ, _hγh, _hγβ, _hcov, _harc1, _harc2, _hsliver⟩ := hW0
  have hnull : MeasureTheory.volume {y : ℝ × ℝ |
      Work.Drive.Mono.OneEvBad ψ s c σ V a₀ b₀ u y.1 y.2} = 0 := by
    have h := hnullQ ng hng
    rwa [← hn, ← hVe, ← ha, ← hb] at h
  have hEF : ∀ h ∈ Set.Ioo A B, Work.Drive.Mono.EdgeFree ψ s c σ u V h := by
    intro h hh
    have h1 : h + ‖V - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < mE := by
      rw [← hAdef]
      linarith [hh.1, hh.2, hBmE]
    have h2 : h + ‖V - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) <
        Submission.boxSide 2 * s - |u| := by
      rw [← hAdef]
      linarith [hh.1, hh.2, hBbs]
    exact Work.Drive.Mono.edgeFreeBox_of_margin ψ c σ V (lt_trans hr hrs) hhedge h1 h2
  obtain ⟨h, R, ℓ, lam0, lam1, exc, hD⟩ :=
    Work.Drive.Mono.g3_assembly ψ K hr hrs hs hu c σ p q hp hq d hd hbound hsmall
      hbox hslice hBG hS hsub hU hP V n a₀ b₀ ρ A B N γ η m δg' mE hW hmE hhedge hnull hEF
  exact ⟨V, h, R, ℓ, lam0, lam1, exc, hD⟩

end

end Work.Drive.Mono
