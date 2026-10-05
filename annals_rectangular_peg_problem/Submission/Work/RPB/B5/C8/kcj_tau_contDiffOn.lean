import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kA0_spec
import Submission.Work.RPB.B5.tauSlabExtend
import Submission.Work.RPB.B5.chordSurf_rhoChart
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_left
import Submission.Work.RPB.B5.rho_range_kappa
import Submission.Work.RPB.B5.C8.levelPhase_C16
import Submission.Work.RPB.B5.C8.levelInverse_C16
import Submission.Work.RPB.B5.C8.iteratedDeriv_slice

/-!
# B5/C8: `τ ↦ kcj W ρh τ j` is `C⁸` on `[0,1]`

The `σ`-jets of the phase of the `ρ = r²`-chart at `t = 0`,

`kcj W ρh τ j = ∂_σ^j (σ ↦ (W τ 0 (ρh τ 0 σ)).1.2) (0)`,

are `C⁸` in `τ` on `[0,1]`, for `j ≤ 8`.

The point is that the chart `W` and the level inverse `ρh` are only assumed `C¹²`, so the naive
bound would give only `C^{12-j}`.  The extra regularity comes from the *left* side `σ < 0`: there
`ρh τ 0 σ > 0` is the distance to the chord annulus, and the chart is *not* the given `W` but the
exact chord surface, whose phase, read as a function of `ρ = r²`, is the `C¹⁶` level phase `Θ`
(`Work.RPB.B5.C8.levelPhase_C16`), while `ρh τ 0 ·` itself is the `C¹⁶` smooth level inverse `rh`
of that same level function (`Work.RPB.B5.C8.levelInverse_C16`).  Hence on `σ < 0` the model
function `Ψ τ σ = Θ τ 0 (rh τ σ)` coincides with the chart phase, and since two functions that
agree to the left of `0` have the same iterated derivatives at `0`
(`Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_left`), the `σ`-jets of the chart phase are the
`σ`-jets of the globally `C¹⁶` model.  Those are `C⁸` in `τ`
(`Work.RPB.B5.C8.iteratedDeriv_slice`).
-/

open Set Filter
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5.C8

/-- The `σ`-slice of the chart phase at `t = 0` is `C¹²` at `σ = 0`. -/
private lemma contDiffAt_kcj_raw {ρ₀ κ : ℝ} {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hκ : 0 < κ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 12 (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0 := by
  have hψ : ContDiffOn ℝ 12 (fun σ : ℝ => (τ, (0 : ℝ), σ)) (Set.Ioo (-κ) κ) := by fun_prop
  have hslice : ContDiffOn ℝ 12 (fun σ : ℝ => ρh τ 0 σ) (Set.Ioo (-κ) κ) :=
    (hρh.comp hψ (fun σ hσ => ⟨hτ, trivial, hσ⟩)).congr (fun σ _ => rfl)
  have hpair : ContDiffOn ℝ 12 (fun σ : ℝ => (τ, (0 : ℝ), ρh τ 0 σ)) (Set.Ioo (-κ) κ) :=
    contDiffOn_const.prodMk (contDiffOn_const.prodMk hslice)
  have hWslice : ContDiffOn ℝ 12 (fun σ : ℝ => W τ 0 (ρh τ 0 σ)) (Set.Ioo (-κ) κ) :=
    (hW.comp hpair (fun σ hσ => ⟨hτ, trivial, hρhv τ hτ 0 σ hσ⟩)).congr (fun σ _ => rfl)
  have hproj : ContDiffOn ℝ 12 (fun x : Work.RPV.PS => x.1.2) Set.univ := by fun_prop
  have hfinal : ContDiffOn ℝ 12 (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) (Set.Ioo (-κ) κ) :=
    hproj.comp hWslice (fun σ _ => trivial)
  exact hfinal.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, hκ⟩)

/-- The `σ`-slice of the model function `σ ↦ Θ τ 0 (rh τ σ)` is `C¹⁶` at `σ = 0`. -/
private lemma contDiffAt_slice_model {Θ : ℝ → ℝ → ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hΘ : ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => Θ z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ))
    (hrh : ContDiffOn ℝ 16 (fun z : ℝ × ℝ => rh z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioo (-s) s))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 16 (fun σ : ℝ => Θ τ 0 (rh τ σ)) 0 := by
  have hrhm : ContDiffOn ℝ 16 (fun σ : ℝ => rh τ σ) (Set.Ioo (-s) s) :=
    (hrh.comp (contDiffOn_const.prodMk contDiffOn_id) (fun σ hσ => ⟨hτ, hσ⟩)).congr
      (fun σ _ => rfl)
  have hpair : ContDiffOn ℝ 16 (fun σ : ℝ => (τ, (0 : ℝ), rh τ σ)) (Set.Ioo (-s) s) :=
    contDiffOn_const.prodMk (contDiffOn_const.prodMk hrhm)
  exact (hΘ.comp hpair (fun σ _ => ⟨hτ, trivial, trivial⟩)).contDiffAt
    (isOpen_Ioo.mem_nhds ⟨by linarith, hs⟩)

theorem kcj_tau_contDiffOn (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (j : ℕ) (hj : j ≤ 8) :
    ContDiffOn ℝ 8 (fun τ : ℝ => Work.RPB.B5.kcj W ρh τ j) (Set.Icc (0 : ℝ) 1) := by
  -- the `C¹⁶` level phase of the chord surface
  obtain ⟨s₁, hs₁, Θ, hΘsm, hΘval⟩ := levelPhase_C16 CI a ha
  -- the `C¹⁶` level inverse on the negative side
  have hεpos : 0 < min (min s₁ (Real.pi ^ 2 / 4)) ρ₀ :=
    lt_min (lt_min hs₁ (by positivity)) hρ₀
  obtain ⟨s, hs, -, -, rh, hrhsm, -, hrheq, hrhb⟩ :=
    levelInverse_C16 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl _ hεpos
  -- the model function
  set Ψ : ℝ → ℝ → ℝ := fun τ σ => Θ τ 0 (rh τ σ) with hΨdef
  have hΨsm : ContDiffOn ℝ 16 (fun z : ℝ × ℝ => Ψ z.1 z.2) (Set.Icc 0 1 ×ˢ Set.Ioo (-s) s) := by
    have hpair : ContDiffOn ℝ 16 (fun z : ℝ × ℝ => (z.1, (0 : ℝ), rh z.1 z.2))
        (Set.Icc 0 1 ×ˢ Set.Ioo (-s) s) :=
      contDiffOn_fst.prodMk (contDiffOn_const.prodMk hrhsm)
    exact (hΘsm.comp hpair (fun z hz => ⟨hz.1, trivial, trivial⟩)).congr (fun z _ => rfl)
  -- its `σ`-jets at `0` are `C⁸` in `τ`
  have hslice := iteratedDeriv_slice (uniqueDiffOn_Icc (by norm_num)) (uniqueDiffOn_Ioo (-s) s)
    (by rw [interior_Ioo]; exact ⟨by linarith, hs⟩) Ψ j
    (hΨsm.of_le (by exact_mod_cast (by omega : j + 8 ≤ 16)))
  refine hslice.congr (fun τ hτ => ?_)
  -- on the left the chart phase *is* the model
  have hraw : ContDiffAt ℝ 12 (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0 :=
    contDiffAt_kcj_raw hW hρh hρhv hκ hτ
  have hmod : ContDiffAt ℝ 12 (fun σ : ℝ => Ψ τ σ) 0 :=
    (contDiffAt_slice_model hs hΘsm hrhsm hτ).of_le (by norm_num)
  have hagree : ∀ σ ∈ Set.Ioo (0 - s) 0,
      (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) σ = (fun σ : ℝ => Ψ τ σ) σ := by
    intro σ hσ
    have hσI : σ ∈ Set.Ioo (-s) (0 : ℝ) := by simpa only [zero_sub] using hσ
    obtain ⟨hrhpos, hrheps⟩ := hrhb τ hτ σ hσI
    have hrhs₁ : rh τ σ < s₁ :=
      lt_of_lt_of_le hrheps (le_trans (min_le_left _ _) (min_le_left _ _))
    have hrhpi : rh τ σ < Real.pi ^ 2 / 4 :=
      lt_of_lt_of_le hrheps (le_trans (min_le_left _ _) (min_le_right _ _))
    have hsq : Real.sqrt (rh τ σ) ^ 2 = rh τ σ := Real.sq_sqrt hrhpos.le
    have hsqle : Real.sqrt (rh τ σ) ≤ Real.pi / 2 := by
      have hpi : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
        rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      have h := Real.sqrt_lt_sqrt hrhpos.le hrhpi
      rw [hpi] at h
      exact h.le
    have hwch := hWchord τ hτ 0 (Real.sqrt (rh τ σ)) ⟨Real.sqrt_pos.mpr hrhpos, hsqle⟩
    have heq : ρh τ 0 σ = rh τ σ := (hrheq τ hτ σ hσI).symm
    calc (W τ 0 (ρh τ 0 σ)).1.2
        = (W τ 0 (rh τ σ)).1.2 := by rw [heq]
      _ = (W τ 0 ((Real.sqrt (rh τ σ)) ^ 2)).1.2 := by rw [hsq]
      _ = (Work.RPB.chordSurf CI.c a τ 0 (Real.sqrt (rh τ σ))).1.2 := by rw [hwch]
      _ = a τ 0 (Real.sqrt (rh τ σ)) := rfl
      _ = Θ τ 0 (rh τ σ) := (hΘval τ hτ 0 (rh τ σ) ⟨hrhpos, hrhs₁⟩).symm
      _ = Ψ τ σ := rfl
  have hkey := iteratedDeriv_eq_of_eqOn_Ioo_left (f := fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2)
    (g := fun σ : ℝ => Ψ τ σ) (x₀ := 0) (δ := s) hs hraw hmod hagree (k := j)
    (by omega : j ≤ 12)
  simpa only [Work.RPB.B5.kcj] using hkey

end Work.RPB.B5.C8
