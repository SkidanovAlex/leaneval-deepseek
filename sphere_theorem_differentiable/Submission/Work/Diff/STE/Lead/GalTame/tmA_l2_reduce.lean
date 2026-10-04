import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.B3.tmAjetsTmPerGerm
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.Lead.GalTame.cutEnergyLeibnizOnSupport
import Submission.Work.Diff.STE.Lead.GalTame.perEnergy
import Submission.Work.Diff.STE.Lead.GalTame.CoeffKit
import Submission.Work.Diff.STE.Lead.GalTame.tmAball_le_R

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat `L²` reduction for the tame coefficient matrix `tmA`

The coefficient matrix of the (tame) transport step is
`tmA φ lam' Γ z p q = (if p = q then lam' else 0) + tmPer (gm φ Γ lam' p q) z`, where `tmPer` is
the real `1`-periodisation and `gm φ Γ lam' p q = φ · (Γ · p q - (if p = q then lam' else 0))` is
its (compactly supported) summand.

The target bounds the `L²` norm of one order-`m` jet `∂^β` of a matrix entry of `tmA` over the unit
cube by the `Hᵐ` energy of the *un-periodised* entry `Γ · p q` over the ball `ball 0 R` on which
the cutoff `φ` is supported (in particular `R ≤ 1/2`, so that the periodisation has at most one
non-vanishing lattice translate at every point).  The constant is uniform in `R`, `φ`, `Γ`, `p`,
`q`, `β`.

## Route

1. For `m ≥ 1` the additive constant `c := (if p = q then lam' else 0)` is annihilated by
   differentiation (`Work.Diff.STE.Lead.GalTame.Kit.pdVec_const_add`), so the left-hand side is
   `ENormSq 0 (∂^β (ofReal ∘ tmPer g))` with `g := gm φ Γ lam' p q`.
2. The complexification of `tmPer g` agrees, near every point of the unit cube, with the complex
   periodisation `Per` of `ofReal ∘ g` (`Work.Diff.STE.B3.tmAjetsTmPerGerm` +
   `Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx`), hence the two `ENormSq 0` agree
   (`Work.Diff.STE.ENormSq_zero` + `MeasureTheory.setIntegral_congr_fun`).
3. `Work.Diff.STE.Lead.GalTame.perEnergy` bounds `ENormSq 0 (∂^β Per)` by the *full* integral of
   `‖∂^β (ofReal ∘ g)‖²` over `ball 0 R` (the lattice translates of the summand do not overlap).
4. `Work.Diff.STE.Lead.GalTame.tmAball_le_R` (delegated, proved in the sibling module) bounds that
   ball integral by the energies of the jets of `Γ · p q`, using the Leibniz estimate
   `Work.Diff.STE.Lead.GalTame.cutEnergyLeibnizOnSupport` and the observation that the constant `c`
   is killed by differentiation of positive order, while the order-`0` term costs `2‖Γ‖² + 2c²`,
   absorbed by the `1 +` of the right-hand side (the volume of `ball 0 R` is `≤ 1` because
   `R ≤ 1/2`).
-/

namespace Work.Diff.STE.Lead.GalTame

theorem tmA_l2_reduce {n : ℕ} (m : ℕ) (hm : 1 ≤ m) (Mφ lam' : ℝ) (hMφ : 0 ≤ Mφ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : ℝ) (hR : 0 < R) (hR2 : R ≤ 1 / 2)
        (φ : (Fin n → ℝ) → ℝ)
        (hφ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ)
        (hφ0 : ∀ z : Fin n → ℝ, 0 ≤ φ z)
        (hφ1 : ∀ z : Fin n → ℝ, φ z ≤ 1)
        (hφd : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
          |Work.Diff.STE.pdRVec r γ φ z| ≤ Mφ)
        (hφts : tsupport φ ⊆ Metric.ball 0 R)
        (Γ : (Fin n → ℝ) → Fin n → Fin n → ℝ)
        (hΓ : ∀ p q : Fin n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Fin n → ℝ => Γ z p q))
        (p q : Fin n) (β : Fin m → Fin n),
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun y : Fin n → ℝ =>
              ((Work.Diff.STE.B3.tmA φ lam' Γ y p q : ℝ) : ℂ)))
          ≤ C * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball (0 : Fin n → ℝ) R,
                ‖Work.Diff.STE.pdVec j γ
                  (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) := by
  classical
  obtain ⟨Cper, hCper0, hCper⟩ := Work.Diff.STE.Lead.GalTame.perEnergy n m
  obtain ⟨Kb, hKb0, hKb⟩ := Work.Diff.STE.Lead.GalTame.tmAball_le_R (n := n) m Mφ lam' hMφ
  refine ⟨Cper * Kb, mul_nonneg hCper0 hKb0, ?_⟩
  intro R hR hR2 φ hφ hφ0 hφ1 hφd hφts Γ hΓ p q β
  set c : ℝ := (if p = q then lam' else 0) with hc
  set g : (Fin n → ℝ) → ℝ := Work.Diff.STE.B3.gm φ Γ lam' p q with hgdef
  have hgval : ∀ z : Fin n → ℝ, g z = φ z * (Γ z p q - c) := by
    intro z
    simp only [hgdef, Work.Diff.STE.B3.gm, hc]
  have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [show g = fun z : Fin n → ℝ => φ z * (Γ z p q - c) from funext hgval]
    exact hφ.mul ((hΓ p q).sub contDiff_const)
  have hgsupp : Function.support g ⊆ Metric.ball 0 R := by
    intro z hz
    refine hφts (subset_tsupport φ (Function.mem_support.mpr ?_))
    intro h0
    exact hz (by rw [hgval z, h0, zero_mul])
  have hgsupp_open : Function.support g ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    hgsupp.trans (Work.Diff.STE.B3.ball_subset_cube hR2)
  set F : (Fin n → ℝ) → ℂ := fun z : Fin n → ℝ => ((g z : ℝ) : ℂ) with hFdef
  have hFsm : ContDiff ℝ (⊤ : ℕ∞) F := Complex.ofRealCLM.contDiff.comp hgsm
  have hFsupp : Function.support F ⊆ Metric.ball 0 R := by
    intro z hz
    refine hgsupp (fun h0 => hz ?_)
    show ((g z : ℝ) : ℂ) = 0
    rw [h0]
    simp
  have hFsupp_open : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    hFsupp.trans (Work.Diff.STE.B3.ball_subset_cube hR2)
  set Per : (Fin n → ℝ) → ℂ :=
    fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k) with hPerdef
  -- the periodisation has the full-space energy of `F`
  have hper := hCper F R hFsm hFsupp hR2 β
  have hper' : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β Per)
      ≤ Cper * ∫ z in Metric.ball 0 R,
          ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((g z : ℝ) : ℂ)) z‖ ^ 2 := by
    rw [hPerdef]
    exact hper
  -- the complexification of `tmPer g` agrees with `Per` near every point of the cube
  have hbridge : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ)) x
        = Work.Diff.STE.pdVec m β Per x := by
    intro x hx
    have h1 := Work.Diff.STE.B3.tmAjetsTmPerGerm g hgsupp_open x hx
    have h2 := Work.Diff.STE.csqp_periodization_eventuallyEq_sum_boxIdx (ι := Fin n)
      hFsupp_open hx
    rw [hPerdef]
    exact (Work.Diff.STE.csqp_pdVec_congr β h1).trans
      ((Work.Diff.STE.csqp_pdVec_congr β h2).symm)
  have hEN : Work.Diff.STE.ENormSq 0
        (Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ)))
      = Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β Per) := by
    rw [Work.Diff.STE.ENormSq_zero, Work.Diff.STE.ENormSq_zero]
    refine MeasureTheory.setIntegral_congr_fun Work.Diff.STE.BesselCont.measSet_unitCube
      (fun x hx => ?_)
    rw [hbridge x hx]
  -- the ball estimate
  have hball : ∫ z in Metric.ball 0 R,
        ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((g z : ℝ) : ℂ)) z‖ ^ 2
      ≤ Kb * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R,
                ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) :=
    hKb R hR hR2 φ hφ hφ0 hφ1 hφd hφts Γ hΓ p q β
  have hmain : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β Per)
      ≤ Cper * (Kb * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R,
                ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2)) :=
    hper'.trans (mul_le_mul_of_nonneg_left hball hCper0)
  -- the additive constant is killed by the `m`-th derivative
  have hfun : (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmA φ lam' Γ y p q : ℝ) : ℂ))
      = fun y : Fin n → ℝ => ((c : ℝ) : ℂ) + ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ) := by
    funext y
    have h1 : Work.Diff.STE.B3.tmA φ lam' Γ y p q = c + Work.Diff.STE.B3.tmPer g y := by
      rw [hc]
      rfl
    rw [h1, Complex.ofReal_add]
  have hLHS : Work.Diff.STE.ENormSq 0
        (Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ =>
          ((Work.Diff.STE.B3.tmA φ lam' Γ y p q : ℝ) : ℂ)))
      = Work.Diff.STE.ENormSq 0
        (Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ))) := by
    rw [hfun, Work.Diff.STE.Lead.GalTame.Kit.pdVec_const_add hm β ((c : ℝ) : ℂ)
      (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ))]
  calc Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmA φ lam' Γ y p q : ℝ) : ℂ)))
      = Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer g y : ℝ) : ℂ))) := hLHS
    _ = Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β Per) := hEN
    _ ≤ Cper * (Kb * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R,
                ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2)) :=
        hmain
    _ = Cper * Kb * (1 + ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R,
                ‖Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ((Γ y p q : ℝ) : ℂ)) z‖ ^ 2) := by
        ring

end Work.Diff.STE.Lead.GalTame
