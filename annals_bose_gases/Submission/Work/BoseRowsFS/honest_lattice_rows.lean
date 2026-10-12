import ChallengeDeps
import Submission.Work.BoseBoxFock.exists_jointGramLab
import Submission.Work.BoseK15.lattice_rows
import Submission.Work.BoseRowsFS.Hon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology

theorem honest_lattice_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
      0 < μ → Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ) →
      1 ≤ Work.BoseBoxFock.ellH v μ →
      (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => ¬ (1 / (2 * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
                ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖)),
            1 / ‖Work.BoseRowsFS.honKmom v HM μ k‖ ^ 2
          ≤ K₀ / ((Work.BoseRowsFS.honE v h fc fu HM μ).KH
              * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
      ∧ (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => 1 / (2 * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
                ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖),
            1 / ‖Work.BoseRowsFS.honKmom v HM μ k‖ ^ 4
          ≤ K₀ * ((Work.BoseRowsFS.honE v h fc fu HM μ).KH
              * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
      ∧ (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => 1 / (2 * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
                ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖),
            1 / ‖Work.BoseRowsFS.honKmom v HM μ k‖ ^ 6
          ≤ K₀ * ((Work.BoseRowsFS.honE v h fc fu HM μ).KH
              * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat) ^ 3
      ∧ (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ ((Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
              (fun k => 1 / (2 * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                  * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
                ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖)).filter
              (fun k => ‖Work.BoseRowsFS.honKmom v HM μ k‖
                ≤ 1 / (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
            1 / ‖Work.BoseRowsFS.honKmom v HM μ k‖ ^ 3
          ≤ K₀ * (1 + Real.log (Work.BoseRowsFS.honE v h fc fu HM μ).KH) := by
  -- The four rows are the pure lattice rows `Work.BoseK15.lattice_rows` at the honest
  -- data: the mode set is the cube `Lab N`, whose momentum map `kmomLab ℓ N` is a
  -- dual-lattice assignment (`Work.BoseBoxFock.GramLab.kmomLab_onDualLattice`), and the
  -- scalars `ℓ, K_H, a` are the honest ones.
  obtain ⟨K₀, hK₀, hrows⟩ := Work.BoseK15.lattice_rows
  refine ⟨K₀, hK₀, ?_⟩
  intro HM μ hμ hview hℓ
  -- the honest scalars: `aScat = a v` (definitionally) and `ell = ellH v μ`
  have hpos : 0 < _root_.BoseGases.a v := hview.a_pos
  have hell : (honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ :=
    honE_ell v h fc fu HM μ hμ hpos
  have hlat : Work.BoseK15.OnDualLattice (Work.BoseBoxFock.ellH v μ) (honKmom v HM μ) :=
    Work.BoseBoxFock.GramLab.kmomLab_onDualLattice (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) (HM μ).N
  have hmain := hrows (Mode := Work.BoseBoxFock.Lab (HM μ).N) (ℓ := Work.BoseBoxFock.ellH v μ) (hℓ := hℓ)
    (kmom := honKmom v HM μ) (hlat := hlat)
    (KH := (honE v h fc fu HM μ).KH) (a := (honE v h fc fu HM μ).aScat)
    (hKH := hview.one_le_KH) (ha := hview.a_pos)
  rw [hell]
  -- row 2 of `lattice_rows` reads `K₀ * K_H * a`, the target `K₀ * (K_H * a)`
  simpa only [mul_assoc] using hmain

end Work.BoseRowsFS
