import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.pairing_bound
import Submission.Work.Diff.STE.flat.energy_deriv_local
import Submission.Work.Diff.STE.flat.Phi_decomp_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

theorem level_step {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (s : ℕ) (hs : Fintype.card (Fin n) + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ Bs ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          deriv (fun σ => Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM (c σ))) t
            ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
                (Work.Diff.STE.Flat.seriesFunM (c t))) := by
  classical
  obtain ⟨C, hCnn, hC⟩ :=
    pairing_bound (n := n) (s := s) hn (by simpa using hs) Φ hshape lam hlam Bs hBs
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro Tc hc N c hderiv hsupp hell hen t ht
  have hmom : ∀ (i j : Fin n) (M : ℕ),
      Summable (fun m : Fin n → ℤ => (wt m) ^ M * ‖c t m i j‖) :=
    fun i j M => summable_moment_box (c t) (hsupp t) i j M
  obtain ⟨Nfun, hNsm, hNdec, hNper⟩ := hshape.2
  obtain ⟨hdecomp, hfsm, hfper⟩ :=
    Phi_decomp_smooth Φ Nfun hNdec hNsm hNper hshape.1 hlam (hell t ht) hmom
  have hfsmM : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x)) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hfsm i j))
  have hfperM : Work.Diff.STE.Periodic1
      (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x)) := by
    intro i x
    funext i' j'
    exact hfper i' j' i x
  have hEd := energy_deriv_local (k := s + 1) (N := N) c (fun σ k' => hsupp σ k')
    (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x))
    hfsmM hfperM (hderiv t ht)
  rw [hEd.deriv]
  have hpair := hC N (c t) (hsupp t) (hen t ht) (hell t ht)
  nlinarith [hpair, hCnn,
    Work.Diff.STE.flat.ENormSqFull_nonneg (s + 1) (Work.Diff.STE.Flat.seriesFunM (c t))]

end

end Work.Diff.STE.flat
