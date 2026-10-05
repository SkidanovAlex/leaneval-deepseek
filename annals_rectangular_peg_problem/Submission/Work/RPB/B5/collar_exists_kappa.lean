import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_tau0
import Submission.Work.RPB.B5.kshape_periodic
import Submission.Work.RPB.B5.kappa_collar_jets
import Submission.Work.RPB.B5.kappa_collar_area_emb
import Submission.Work.RPB.B5.kappa_collar_far_tau0
import Submission.Work.RPB.B5.kappa_collar_mono_flux
import Submission.Work.RPB.B5.kappa_collar_C8

/-!
# `Work.RPB.B5.collar_exists_kappa`

The `κ`-parametrised collar existence theorem.  The construction is in
`Submission/Work/RPB/B5/kappaDefs.lean`; the inputs are the sibling lemmas

* `kappa_tau0` (the `τ = 0` chord phase and the flatness of the chart at the diagonal),
* `kappa_collar_area_emb` (area law and embeddedness for `σ ≥ 0`, `τ ∈ [0,1]`),
* `kappa_collar_far_tau0` (the far end and the `τ = 0` zero-section statement),
* `kappa_collar_mono_flux` (the `+2π` monodromy and the flux identity),
* `kappa_collar_jets` (the `σ`-jets at `0⁺`),
* plus the elementary facts of `kappa_shape_basic` (`kshape_far`, `kshape_zero_slice`, …).

The two `C⁸` conjuncts come from the sibling `kappa_collar_C8` (the `C⁸` half of the combined
`kappa_collar_smooth_tau`).

## The `τ`-clamp

The hypotheses constrain the data `W`, `ρh`, `CI.c` only for `τ ∈ [0,1]`, while the statement's
conjuncts (2), (2') and (3) quantify over *all* `τ : ℝ` (this is the defect recorded in
`Submission/Work/RPB/B5/kappa_collar_smooth.lean`).  Accordingly the witnesses are the
`τ`-clamped families `Γc τ σ t = kgam … (ktauClamp τ) σ t`, `Ac τ σ t = kac … (ktauClamp τ) σ t`
with `ktauClamp τ = τ` on `[0,1]` and `ktauClamp τ ∈ [0,1]` for every `τ`.
-/

namespace Work.RPB.B5

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

/-! ## The `τ`-clamp -/

/-- A map which is the identity on `[0,1]` and maps `ℝ` into `[0,1]`. -/
def ktauClamp (τ : ℝ) : ℝ := if τ ≤ 0 then 0 else if 1 ≤ τ then 1 else τ

theorem ktauClamp_of_mem {τ : ℝ} (h : τ ∈ Set.Icc (0 : ℝ) 1) : ktauClamp τ = τ := by
  rw [ktauClamp]
  split_ifs with h1 h2
  · exact (le_antisymm h1 h.1).symm
  · exact le_antisymm h2 h.2
  · rfl

theorem ktauClamp_mem (τ : ℝ) : ktauClamp τ ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ktauClamp]
  split_ifs with h1 h2
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_of_lt (lt_of_not_ge h1), le_of_not_ge h2⟩

/-! ## The collar -/

/-- **The `κ`-parametrised collar.** -/
theorem collar_exists_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hπ : Real.pi ^ 2 / 4 < ρ₀)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ) :
    ∃ σ₂ : ℝ, 0 < σ₂ ∧ ∃ Γc : ℝ → ℝ → ℝ → ℂ, ∃ Ac : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Γc z.1 z.2.1 z.2.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ac z.1 z.2.1 z.2.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
      (∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t) ∧
      (∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi) ∧
      (∀ τ σ t, deriv (fun s => Ac τ σ s) t
        = Work.RPV.ωC (deriv (fun s => Γc τ s t) σ) (deriv (fun s => Γc τ σ s) t)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
        Work.RPB.signedArea (Γc τ σ) = 2 * Real.pi * (1 + σ)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
        (∀ t, deriv (fun s => Γc τ σ s) t ≠ 0) ∧
        (∀ t t', Γc τ σ t = Γc τ σ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, σ₂ ≤ σ → ∀ t,
        Γc τ σ t = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) ∧
        Ac τ σ t = t) ∧
      (∀ σ, 0 ≤ σ → ∀ t, (Work.RPV.levelPt (Γc 0 σ t) σ (Ac 0 σ t)).2 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ k : ℕ, k ≤ 8 →
        iteratedDerivWithin k (fun σ : ℝ => Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t))
            (Set.Ioi 0) 0
          = iteratedDeriv k (fun σ : ℝ => W τ t (ρh τ t σ)) 0) := by
  classical
  -- the integer `k` of the `τ = 0` chord phase, and the `σ`-jets of the chart phase at `0⁺`
  obtain ⟨k, hk, -⟩ := kappa_tau0 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl
  obtain ⟨δJ, hδJpos, -, hjets⟩ :=
    kappa_collar_jets CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
      k hk
  obtain ⟨δA, hδApos, -, hareaemb⟩ :=
    kappa_collar_area_emb CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
      k
  obtain ⟨δF, hδFpos, -, hfartau0⟩ :=
    kappa_collar_far_tau0 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
      k
  obtain ⟨δM, hδMpos, -, hmonoflux⟩ :=
    kappa_collar_mono_flux CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
      k
  obtain ⟨δC, hδCpos, -, hC8⟩ :=
    kappa_collar_C8 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
      k
  -- ### the scale: everything below is uniform in `δ` on `(0, δ₀)`
  set δ : ℝ := min (min δJ δA) (min δF (min δM δC)) / 2 with hδdef
  have hminpos : 0 < min (min δJ δA) (min δF (min δM δC)) :=
    lt_min (lt_min hδJpos hδApos) (lt_min hδFpos (lt_min hδMpos hδCpos))
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos hminpos (by norm_num)
  have hδltJ : δ < δJ := by
    rw [hδdef]
    have h1 := min_le_left (min δJ δA) (min δF (min δM δC))
    have h2 := min_le_left δJ δA
    linarith
  have hδltA : δ < δA := by
    rw [hδdef]
    have h1 := min_le_left (min δJ δA) (min δF (min δM δC))
    have h2 := min_le_right δJ δA
    linarith
  have hδltF : δ < δF := by
    rw [hδdef]
    have h1 := min_le_right (min δJ δA) (min δF (min δM δC))
    have h2 := min_le_left δF (min δM δC)
    linarith
  have hδltM : δ < δM := by
    rw [hδdef]
    have h1 := min_le_right (min δJ δA) (min δF (min δM δC))
    have h2 := min_le_right δF (min δM δC)
    have h3 := min_le_left δM δC
    linarith
  have hδltC : δ < δC := by
    rw [hδdef]
    have h1 := min_le_right (min δJ δA) (min δF (min δM δC))
    have h2 := min_le_right δF (min δM δC)
    have h3 := min_le_right δM δC
    linarith
  -- the sibling lemmas at the chosen scale
  have hJ := hjets δ ⟨hδpos, hδltJ⟩
  have hA := hareaemb δ ⟨hδpos, hδltA⟩
  have hF := hfartau0 δ ⟨hδpos, hδltF⟩
  have hM := hmonoflux δ ⟨hδpos, hδltM⟩
  have hC := hC8 δ ⟨hδpos, hδltC⟩
  refine ⟨2 * δ, by linarith,
    (fun τ σ t => kgam CI W ρh δ k (ktauClamp τ) σ t),
    (fun τ σ t => kac CI W ρh δ k (ktauClamp τ) σ t),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `C⁸` of the collar
    refine hC.1.congr ?_
    intro z hz
    show kgam CI W ρh δ k (ktauClamp z.1) z.2.1 z.2.2 = kgam CI W ρh δ k z.1 z.2.1 z.2.2
    rw [ktauClamp_of_mem hz.1]
  · -- (1') `C⁸` of the phase
    refine hC.2.congr ?_
    intro z hz
    show kac CI W ρh δ k (ktauClamp z.1) z.2.1 z.2.2 = kac CI W ρh δ k z.1 z.2.1 z.2.2
    rw [ktauClamp_of_mem hz.1]
  · -- (2) `2π`-periodicity in `t`
    intro τ σ t
    show kdiagM (kg CI W ρh δ k (ktauClamp τ) σ)
        (kshape CI W ρh δ k (ktauClamp τ) σ (t + 2 * Real.pi))
      = kdiagM (kg CI W ρh δ k (ktauClamp τ) σ) (kshape CI W ρh δ k (ktauClamp τ) σ t)
    rw [kshape_periodic CI W ρh δ k hWper hρhper]
  · -- (2') the monodromy of the phase
    intro τ σ t
    exact (hM (ktauClamp τ) (ktauClamp_mem τ)).1 σ t
  · -- (3) the flux identity
    intro τ σ t
    exact (hM (ktauClamp τ) (ktauClamp_mem τ)).2 σ t
  · -- (4) the area law
    intro τ hτ σ hσ
    show Work.RPB.signedArea (fun t => kgam CI W ρh δ k (ktauClamp τ) σ t)
      = 2 * Real.pi * (1 + σ)
    rw [ktauClamp_of_mem hτ]
    exact (hA τ hτ σ hσ).1
  · -- (5) embeddedness for `σ ≥ 0`
    intro τ hτ σ hσ
    have h := hA τ hτ σ hσ
    constructor
    · intro t
      show deriv (fun s => kgam CI W ρh δ k (ktauClamp τ) σ s) t ≠ 0
      rw [ktauClamp_of_mem hτ]
      exact h.2.1 t
    · intro t t' htt'
      have htt'' : kgam CI W ρh δ k (ktauClamp τ) σ t
          = kgam CI W ρh δ k (ktauClamp τ) σ t' := htt'
      show ∃ m : ℤ, t' = t + 2 * Real.pi * m
      rw [ktauClamp_of_mem hτ] at htt''
      exact h.2.2 t t' htt''
  · -- (6) the far end
    intro τ hτ σ hσ t
    have h := hF.1 τ hτ σ hσ t
    constructor
    · show kgam CI W ρh δ k (ktauClamp τ) σ t = _
      rw [ktauClamp_of_mem hτ]
      exact h.1
    · show kac CI W ρh δ k (ktauClamp τ) σ t = t
      rw [ktauClamp_of_mem hτ]
      exact h.2
  · -- (7) the `τ = 0` slice lies in the zero section
    intro σ hσ t
    show (Work.RPV.levelPt (kgam CI W ρh δ k (ktauClamp 0) σ t) σ
      (kac CI W ρh δ k (ktauClamp 0) σ t)).2 = 0
    rw [ktauClamp_of_mem (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
    exact hF.2 σ hσ t
  · -- (8) the `σ`-jets at `0⁺`
    intro τ hτ t j hj
    have hfun : (fun σ : ℝ => Work.RPV.levelPt
          ((fun τ σ t => kgam CI W ρh δ k (ktauClamp τ) σ t) τ σ t) σ
          ((fun τ σ t => kac CI W ρh δ k (ktauClamp τ) σ t) τ σ t))
        = fun σ : ℝ => Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ
            (kac CI W ρh δ k τ σ t) := by
      funext σ
      show Work.RPV.levelPt (kgam CI W ρh δ k (ktauClamp τ) σ t) σ
          (kac CI W ρh δ k (ktauClamp τ) σ t)
        = Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ (kac CI W ρh δ k τ σ t)
      rw [ktauClamp_of_mem hτ]
    rw [hfun]
    exact hJ τ hτ t j hj

end

end Work.RPB.B5
