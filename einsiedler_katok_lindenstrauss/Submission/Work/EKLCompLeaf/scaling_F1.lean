import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.nuR_conj_phi_Icc
import Submission.Work.EKLCompLeaf.map_conj_aPrime_eq_self

/-!
# `scaling_F1`: (U7) ⇒ (F1) + (F2) for the leafwise system of `U_01`

From the `A`-covariance clause `U7clause μ ν X'` of the frozen `P_Leafwise` contract we extract
the two facts about the leafwise measures used by the low-entropy method (EKL §4.3–4.5,
`ROUTE_LEAD.md` §5, Facts (F1), (F2)):

* **(F1)** `ν_{φ_w x}([-σ,σ]) / ν_{φ_w x}([-1,1]) = ν_x([-σ e^{2w}, σ e^{2w}]) / ν_x([-e^{2w}, e^{2w}])`
  for the contracting flow `φ_w = diag(e^{-w}, e^{w}, 1)` and `x, φ_w x` in the conull set
  `X''` of (U7).  Writing it as a cross-multiplied identity of `ℝ`-valued measures it reads
  `nuR (ν (φ_w x)) ([-σ,σ]) * nuR (ν x) ([-e^{2w},e^{2w}])
     = nuR (ν x) ([-σ e^{2w}, σ e^{2w}]) * nuR (ν (φ_w x)) ([-1,1])`.
  Indeed (U7) gives `ν_{φ_w x} = c · (ν_x ∘ conj_{φ_w})` and conjugation by `φ_w` rescales the
  parameter `par` by `e^{-2w}` (F1); both sides are then `c · A(σ e^{2w}) · A(e^{2w})` with
  `A(R) = nuR (ν x) ([-R,R])`, so they agree; the exact scalar `c` cancels.
* **(F2)** `ν_{α^s x} = ν_x` for `α^s = a'_{01}(s) = diag(e^s, e^s, e^{-2s})` (which
  centralises `U_01`): (U7) gives `ν_{α^s x} = c · (ν_x ∘ conj_{α^s})` with `conj_{α^s} = id`
  on `U_01`, and the normalisation `ν_y(B₁^{U_01}) = 1` at both points forces `c = 1`.

Everything is proved for the single conull measurable set `X'' ⊆ X'` delivered by (U7).
-/

open MeasureTheory
open scoped Matrix
open Work.EKLContract

noncomputable section

namespace Work.EKLCompLeaf

theorem scaling_F1 {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hU7 : Work.EKLComp.U7clause μ ν X') :
    ∃ X'' : Set Work.EKLContract.X3, X'' ⊆ X' ∧ MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
      (∀ x ∈ X'', ∀ w σ : ℝ, Work.EKLComp.phi w • x ∈ X'' →
        (Work.EKLComp.nuR (ν (Work.EKLComp.phi w • x))).real (Set.Icc (-σ) σ)
            * (Work.EKLComp.nuR (ν x)).real
                (Set.Icc (-(Real.exp (2 * w))) (Real.exp (2 * w)))
          = (Work.EKLComp.nuR (ν x)).real
              (Set.Icc (-(σ * Real.exp (2 * w))) (σ * Real.exp (2 * w)))
            * (Work.EKLComp.nuR (ν (Work.EKLComp.phi w • x))).real (Set.Icc (-1) 1)) ∧
      (∀ x ∈ X'', ∀ s : ℝ, Work.EKLContract.aPrime 2 s • x ∈ X'' →
        ν (Work.EKLContract.aPrime 2 s • x) = ν x) := by
  obtain ⟨X'', hX''sub, hX''meas, hX''null, hcov⟩ := hU7
  refine ⟨X'', hX''sub, hX''meas, hX''null, ?_, ?_⟩
  -- (F1): the scaling relation for `nuR` under the flow `φ_w`
  · intro x hx w σ hxw
    obtain ⟨c, _hc0, _hctop, hceq⟩ := hcov (w • ![-1,1,0]) x hx hxw
    have hceq' : ν (Work.EKLComp.phi w • x)
        = c • (ν x).map (fun g => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹) := hceq
    have hcar : ν x (Uij Work.EKLComp.h01 : Set SL3)ᶜ = 0 := hL.carried x (hX''sub hx)
    have hM : Work.EKLComp.nuR (ν (Work.EKLComp.phi w • x))
        = c • (Work.EKLComp.nuR
            ((ν x).map (fun g => Work.EKLComp.phi w * g * (Work.EKLComp.phi w)⁻¹))) := by
      rw [hceq', Work.EKLComp.nuR_smul]
    have h1 : (Work.EKLComp.nuR (ν (Work.EKLComp.phi w • x))).real (Set.Icc (-σ) σ)
        = c.toReal * (Work.EKLComp.nuR (ν x)).real
            (Set.Icc (-(σ * Real.exp (2 * w))) (σ * Real.exp (2 * w))) := by
      rw [hM, MeasureTheory.measureReal_ennreal_smul_apply,
        nuR_conj_phi_Icc (ν x) hcar w σ]
    have h2 : (Work.EKLComp.nuR (ν (Work.EKLComp.phi w • x))).real (Set.Icc (-1) 1)
        = c.toReal * (Work.EKLComp.nuR (ν x)).real
            (Set.Icc (-(1 * Real.exp (2 * w))) (1 * Real.exp (2 * w))) := by
      rw [hM, MeasureTheory.measureReal_ennreal_smul_apply,
        nuR_conj_phi_Icc (ν x) hcar w 1]
    rw [h1, h2]
    simp only [one_mul]
    ring
  -- (F2): exact invariance of the leafwise measure under `α' = aPrime 2 s`
  · intro x hx s hxs
    obtain ⟨c, _hc0, _hctop, hceq⟩ :=
      hcov (fun i : Fin 3 => if i = 2 then -2 * s else s) x hx hxs
    have hceq' : ν (Work.EKLContract.aPrime 2 s • x)
        = c • (ν x).map
            (fun g => Work.EKLContract.aPrime 2 s * g * (Work.EKLContract.aPrime 2 s)⁻¹) := hceq
    have hcar : ν x (Uij Work.EKLComp.h01 : Set SL3)ᶜ = 0 := hL.carried x (hX''sub hx)
    have hmap := map_conj_aPrime_eq_self (ν x) hcar s
    have hc : ν (Work.EKLContract.aPrime 2 s • x) = c • ν x := by rw [hceq', hmap]
    have hx' : Work.EKLContract.aPrime 2 s • x ∈ X' := hX''sub hxs
    have hx0 : x ∈ X' := hX''sub hx
    have h1 : ν (Work.EKLContract.aPrime 2 s • x) (Box1 (Uij Work.EKLComp.h01)) = 1 :=
      hL.normalised _ hx'
    have h2 : ν x (Box1 (Uij Work.EKLComp.h01)) = 1 := hL.normalised _ hx0
    have h3 : c = 1 := by
      have h := congrArg (fun m : Measure SL3 => m (Box1 (Uij Work.EKLComp.h01))) hc
      rw [h1, Measure.smul_apply, h2, smul_eq_mul, mul_one] at h
      exact h.symm
    rw [h3, one_smul] at hc
    exact hc

end Work.EKLCompLeaf
