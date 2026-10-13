/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/ConvLocUnifH6_JfamP.lean` — the convergence package of the
# *projected* family

After the `L₁₂(g₀)(0) = 0` repair of `EpsUniformMem` (`NOTES_session13.md` §6), the scheme's
slices satisfy `L₁₂ (slice g τ)(0) = L₁₂ g₀ 0 = 0`, so along the scheme
`L₁₂ (J_ε (slice g τ))(0) → 0` (`EpsCorr_tendsto_zero`), i.e. the `P₀`-correction of the projected
family vanishes in the limit and the **projected** and **unprojected** families have *the same
limit*.  That is what makes the `bd4`/`mem4`/`limApprox`/`dbd` clauses runnable along the projected
family `Pn := slice (JfamP ρ (ε n) (G n)) τ`, whose per-`z` and `ℋ⁴` bounds are *literally* in the
interface.

This module puts the convergence package in place: from the slot-wise (locally uniform) convergence
of the mollified family `J_ε (slice (G n) τ) → slice g τ` and the vanishing of the correction
scalar `c n = L₁₂(J_ε (slice (G n) τ))(0)/pzNorm`, the projected family has the *same*
`ConvLocUnifH6` package as `slice (G n) τ`.  The ingredient is the pointwise identity

  `D_z^jD_θ^i (P₀ f) = D_z^jD_θ^i f − (L₁₂ f 0 / pzNorm)·D_z^jD_θ^i bump`   (`PZeroAux.mixed_Pz`)

together with the uniform bound on the mixed derivatives of the fixed profile `bump` on compacts
(`exists_bound_mixed_bump`).

The uniform convergence of the slots of `J_ε (G n)` is taken as a hypothesis here: it is exactly
the conclusion of the delegated `Work.FTS.StrongEps.E5Aux.mixed_Jeps_tendstoUniformlyOn`, and
keeping it as a hypothesis keeps this module independent of that one.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.EpsE5Facts
import Submission.Work.FTS.StrongEps.E5Clamp
import Submission.Work.FTS.StrongEps.E5Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The convergence package of the projected family.**  From

* the slot-wise locally uniform convergence of the mollified family
  `J_ε (slice (G n) τ) → slice g τ` (the `hJ` hypothesis, supplied by
  `E5Aux.mixed_Jeps_tendstoUniformlyOn`),
* the vanishing of the correction scalars `L₁₂ (J_ε (slice (G n) τ)) 0 → 0` (`hl12`),
* the all-order smoothness of the profiles `slice (G n) τ` on the open quadrant (`hsm`), and
* the data of `ConvLocUnifH6` for the *unprojected* family (`hconv`),

the projected family `slice (JfamP ρ (ε n) (G n)) τ` satisfies the same `ConvLocUnifH6` package
with the same limit `slice g τ` and the same constant `B`. -/
theorem ConvLocUnifH6_JfamP {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    {α B : ℝ} {G : ℕ → Fam} {g : Fam} {ε : ℕ → ℝ} {τ : ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G n) τ)) Quad)
    (hconv : ConvLocUnifH6 α B (fun n => slice (G n) τ) (slice g τ))
    (hεpos : ∀ n : ℕ, 0 < ε n)
    (hJ : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn
          (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (slice g τ) p.1 p.2) Filter.atTop K)
    (hl12 : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0)
      Filter.atTop (nhds 0)) :
    ConvLocUnifH6 α B (fun n => slice (JfamP ρ (ε n) (G n)) τ) (slice g τ) := by
  refine ⟨?_, hconv.contDiffOn, hconv.hkNorm_le⟩
  intro K hK hKQ j i hji
  rw [Metric.tendstoUniformlyOn_iff]
  intro d hdpos
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  have hCb1 : (0 : ℝ) < Cb + 1 := by linarith
  -- the correction scalars tend to `0`
  have hc0 : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
    have := hl12.div_const pzNorm
    simpa using this
  have hcev : ∀ᶠ n : ℕ in Filter.atTop,
      |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm| * (Cb + 1)
        < d / 2 := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm|
          * (Cb + 1)) Filter.atTop (nhds (|(0 : ℝ)| * (Cb + 1))) :=
      hc0.abs.mul_const (Cb + 1)
    have h2 : |(0 : ℝ)| * (Cb + 1) = 0 := by simp
    rw [h2] at h1
    simpa [Real.dist_eq, abs_of_pos hCb1] using Metric.tendsto_nhds.mp h1 (d / 2) (by linarith)
  -- the slots of the mollified family converge uniformly on `K`
  have hjev : ∀ᶠ n : ℕ in Filter.atTop, ∀ p ∈ K,
      dist (Work.Spaces.mixed j i (slice g τ) p.1 p.2)
        (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2) < d / 2 :=
    Metric.tendstoUniformlyOn_iff.mp (hJ K hK hKQ j i hji) (d / 2) (by linarith)
  filter_upwards [hcev, hjev] with n hcn hjn
  intro p hp
  have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
  have hz : 0 < p.1 := hpQ.1
  have hθ : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
  -- the pointwise identity of the projected slot
  have hsplit : Work.Spaces.mixed j i (slice (JfamP ρ (ε n) (G n)) τ) p.1 p.2
      = Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2 := by
    rw [slice_JfamP]
    exact PZeroAux.mixed_Pz (smoothOpen_Jeps ρ hρ (hεpos n) (hsm n)) hz hθ j i
  rw [hsplit, dist_comm]
  -- `dist (X - t) Y ≤ |t| + dist X Y`
  have htri : dist (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2)
      (Work.Spaces.mixed j i (slice g τ) p.1 p.2)
      ≤ |(Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2|
        + dist (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2)
            (Work.Spaces.mixed j i (slice g τ) p.1 p.2) := by
    have h := dist_triangle
      (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2)
      (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2)
      (Work.Spaces.mixed j i (slice g τ) p.1 p.2)
    have hd : dist (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
          - (Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2)
        (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2)
        = |(Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2| := by
      rw [Real.dist_eq,
        show Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
            - (Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
              * Work.Spaces.mixed j i bump p.1 p.2
            - Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2
          = -((Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
              * Work.Spaces.mixed j i bump p.1 p.2) from by ring, abs_neg]
    rw [hd] at h
    exact h
  refine lt_of_le_of_lt htri ?_
  have hb : |(Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm)
      * Work.Spaces.mixed j i bump p.1 p.2| < d / 2 := by
    rw [abs_mul]
    have h1 : |Work.Spaces.mixed j i bump p.1 p.2| ≤ Cb := hbump j i hji p hp
    have h2 : |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm| * Cb
        ≤ |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm| * (Cb + 1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith
    calc |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm|
          * |Work.Spaces.mixed j i bump p.1 p.2|
        ≤ |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm| * Cb :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |Work.Construction.L12 (Jeps ρ (ε n) (slice (G n) τ)) 0 / pzNorm| * (Cb + 1) := h2
      _ < d / 2 := hcn
  have hd2 : dist (Work.Spaces.mixed j i (Jeps ρ (ε n) (slice (G n) τ)) p.1 p.2)
      (Work.Spaces.mixed j i (slice g τ) p.1 p.2) < d / 2 := by
    rw [dist_comm]
    exact hjn p hp
  linarith

/-! ## The `bd4` clause of `EpsLimPkg` for the *projected* family -/

/-- **`bd4` along the projected family.**  Once the extraction has produced the slot-wise locally
uniform convergence of `slice (G (φ n)) τ` (`hconv`), the slot convergence of the mollified family
(`hJ`), the vanishing of the correction scalars (`hl12`) and the interface's `ℋ⁴`-clauses for the
projected slices (`hmem`, `hb`), the `ℋ⁴`-bound of the limit follows at the *same* constant `C₀ α²`
(`E5_bd4` applied along `slice (JfamP ρ (ε (φ n)) (G (φ n))) τ`, whose convergence package is
`ConvLocUnifH6_JfamP`). -/
theorem E5_bd4_JfamP {α B C₀ T : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ}
    {ε : ℕ → ℝ} {F : ℝ → Fn}
    (hρ : IsSmoothKernel ρ)
    (hsm : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G (φ n)) τ)) Quad)
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ))
    (hεpos : ∀ n : ℕ, 0 < ε n)
    (hJ : ∀ τ ∈ Set.Icc 0 T, ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn
          (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F τ) p.1 p.2) Filter.atTop K)
    (hl12 : ∀ τ ∈ Set.Icc 0 T, Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12 (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) 0)
      Filter.atTop (nhds 0))
    (hmem : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
      Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ))
    (hb : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ) ≤ C₀ * α ^ 2) :
    ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (clampQ F g₀) τ) ≤ C₀ * α ^ 2 :=
  fun τ hτ => E5_bd4 (g₀ := g₀) (G := fun n => JfamP ρ (ε (φ n)) (G (φ n))) (φ := id) (F := F)
    (fun σ hσ => ConvLocUnifH6_JfamP (hρ := hρ) (G := fun n => G (φ n))
      (g := fun z θ _ => F σ z θ) (τ := σ)
      (hsm := hsm σ hσ) (hconv := hconv σ hσ)
      (hεpos := fun n => hεpos (φ n)) (hJ := hJ σ hσ) (hl12 := hl12 σ hσ))
    (fun σ hσ n => hmem σ hσ n) (fun σ hσ n => hb σ hσ n) τ hτ


/-! ## The `mem4` clause of `EpsLimPkg` for the *projected* family -/

/-- **`mem4` along the projected family.**  The honest `ℋ⁴`-membership of the limit slice, from
`EpsLimMem4` (`E5_mem4`), applied along the projected family — whose convergence package is
`ConvLocUnifH6_JfamP`.

The per-`z` bound `hz` is *not* removable: `HkMem` is a per-`z` condition and Fatou gives it only
a.e. in `z` (`NOTES_session14.md` §3 (G-A)).  Its production is the open interface question of the
area; here it is an explicit hypothesis of the assembly. -/
theorem E5_mem4_JfamP {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ}
    {ε : ℕ → ℝ} {F : ℝ → Fn}
    (hρ : IsSmoothKernel ρ)
    (hsmG : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G (φ n)) τ)) Quad)
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ))
    (hεpos : ∀ n : ℕ, 0 < ε n)
    (hJ : ∀ τ ∈ Set.Icc 0 T, ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn
          (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
            (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) p.1 p.2)
          (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F τ) p.1 p.2) Filter.atTop K)
    (hl12 : ∀ τ ∈ Set.Icc 0 T, Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12 (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) 0)
      Filter.atTop (nhds 0))
    (hsmJ : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ))
        Work.FTS.EllipticEst.Q0)
    (hmem : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
      Work.Spaces.HkMem α 6 (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ))
    (hb : ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
      Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ) ≤ B)
    (hz : ∀ τ ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (slice (JfamP ρ (ε (φ n)) (G (φ n))) τ) z θ) ≤ Bz) :
    ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice (clampQ F g₀) τ) ∧
      Work.FTS.Nonlin.Xn α (slice (clampQ F g₀) τ) ≤ B := by
  intro τ hτ
  have hconvP : ConvLocUnifH6 α B
      (fun n => slice (JfamP ρ (ε (φ n)) (G (φ n))) τ) (F τ) :=
    ConvLocUnifH6_JfamP (hρ := hρ) (G := fun n => G (φ n)) (g := fun z θ _ => F τ z θ) (τ := τ)
      (hsm := hsmG τ hτ) (hconv := hconv τ hτ) (hεpos := fun n => hεpos (φ n))
      (hJ := hJ τ hτ) (hl12 := hl12 τ hτ)
  exact E5_mem4 (g₀ := g₀) hconvP (hsmJ τ hτ) (hmem τ hτ) (hb τ hτ) (hz τ hτ)


end Work.FTS.StrongEps
