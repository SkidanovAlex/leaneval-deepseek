/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The localised a priori Schauder estimate with **free regions**

`Work.NN.Final.aPrioriEstimate_local_L2` states

`‖u‖_{C^{1,α}(pd n ρ 1)} ≤ C·(Σ_j ‖(∂̄_Ju)·e_j‖_{C^{0,α}(pd n ρ 2)} + ‖u‖_{L²(pd n ρ 2)})`

for `J = JstdCn n + A` small on `pd n ρ 4`: the *conclusion* region `pd n ρ 1` and the *data*
region `pd n ρ 2` are hard-wired (the ratio is `1 : 2`).

For the frame theorem (`Work.NN.Final.FrameHol`, i.e. `Submission/Work/NN/Final/frameHol.lean`) the
region arithmetic of the fixed point requires a *much better* ratio: the frame has to be produced on
`pd n ρ σ` for `σ ≥ 13/5 + 1/400 = 2.6025`, while the perturbation `A` is only small on
`pd n ρ 4`, so the usable ratio in the a priori estimate has to exceed `2.6025/4 = 0.6506`, which
the fixed ratio `1 : 2` of `aPrioriEstimate_local_L2` cannot deliver.

The two pillars that `aPrioriEstimate_local_L2` is assembled from are, however, *region-parametric*:

* `Work.NN.Final.LevJ.supRemainderSchauder_v (ρ) (ρ')`, `ρ' < ρ` — the `∂A`-free a priori Schauder
  estimate `‖u‖_{1,α}(polydisc 0 ρ') ≤ C(Σ_j ‖(∂̄_Ju)e_j‖_{0,α}(polydisc 0 ρ) + sup_{polydisc 0 ρ}‖u‖)`;
* `Work.NN.Final.LevJLoc.supEstimateL2_v (σ) (ρ)`, `σ < ρ` — the level-`0` sup estimate with the
  `L²` remainder.

This file re-assembles them with the three radii left free: for `0 < a < b < c ≤ 4`

`‖u‖_{C^{1,α}(pd n ρ a)} ≤ C·(Σ_j ‖(∂̄_Ju)·e_j‖_{C^{0,α}(pd n ρ c)} + ‖u‖_{L²(pd n ρ c)})`,

with `C` and the smallness threshold `ε₀` depending on `n, α, ρ, a, b, c` (and *not* on `A` or
`ε`).  Since `a` may be taken arbitrarily close to `c`, the a priori estimate is available at *any*
ratio `< 1`: the a priori step is therefore **not** the obstruction to the region arithmetic of the
frame fixed point; the obstruction lies in the *existence* input (the weak `L²` solution and its
`WEAK→CLASS` upgrade), which is where `Work.NN.Final.L2SolvabilityHyp` sits.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.LevJ.SupRemainder
import Submission.Work.NN.Final.LevJLoc.SupEstimate

namespace Work.NN.Final

open scoped ENNReal
open Work.NN.Core

/-! ## Auxiliary lemmas (copied from `aPrioriEstimate_local_L2.lean`) -/

/-- A `VecHolder` bound on a `Cn n`-valued map gives the componentwise `C^{0,α}` bound
(up to the harmless factor `2`, since `holderNorm 0 = sup + Hölder seminorm`). -/
private lemma vecHolder_comp_holderNorm_zero {n : ℕ} {φ : Cn n → Cn n} {α ε : ℝ}
    {Ω : Set (Cn n)} (h : VecHolder φ α ε Ω) (hε : 0 ≤ ε) (j : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal (2 * ε) := by
  have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.iDN_zero_deriv]
    exact iSup₂_le fun z hz =>
      ENNReal.ofReal_le_ofReal (le_trans (norm_le_pi_norm (φ z) j) (h.1 z hz))
  have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
      ENNReal.ofReal_le_ofReal ?_
    have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
    rw [div_le_iff₀ hdα]
    calc ‖φ x j - φ y j‖ = ‖(φ x - φ y) j‖ := by rw [Pi.sub_apply]
      _ ≤ ‖φ x - φ y‖ := norm_le_pi_norm (φ x - φ y) j
      _ ≤ ε * ‖x - y‖ ^ α := h.2 x hx y hy
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  calc Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω
        + Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω
      ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε hε]
        congr 1
        ring

/-- The `ℝ≥0∞` bookkeeping of the assembly (copied from `aPrioriEstimate_local_L2.lean`). -/
private lemma ennreal_chain {C₁ C₂ : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (a b : ℝ≥0∞) :
    ENNReal.ofReal C₁ * (a + ENNReal.ofReal C₂ * (a + b))
      ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * (a + b) := by
  have hstep1 : a + ENNReal.ofReal C₂ * (a + b) ≤ ENNReal.ofReal (1 + C₂) * (a + b) := by
    have h2 : (1 : ℝ≥0∞) + ENNReal.ofReal C₂ = ENNReal.ofReal (1 + C₂) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one h₂]
    calc a + ENNReal.ofReal C₂ * (a + b)
        ≤ (a + b) + ENNReal.ofReal C₂ * (a + b) := by gcongr; exact le_add_right le_rfl
      _ = (1 + ENNReal.ofReal C₂) * (a + b) := by rw [add_mul, one_mul]
      _ = ENNReal.ofReal (1 + C₂) * (a + b) := by rw [h2]
  calc ENNReal.ofReal C₁ * (a + ENNReal.ofReal C₂ * (a + b))
      ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (1 + C₂) * (a + b)) := by gcongr
    _ = (ENNReal.ofReal C₁ * ENNReal.ofReal (1 + C₂)) * (a + b) := by rw [mul_assoc]
    _ = ENNReal.ofReal (C₁ * (1 + C₂)) * (a + b) := by
        rw [← ENNReal.ofReal_mul h₁]

/-! ## The estimate with free radii -/

/-- **The `∂A`-free, localised a priori Schauder estimate with free radii.**  For `A` smooth,
`VecHolder`-small on `pd n ρ 4`, with `J = JstdCn n + A` almost complex on `pd n ρ 4`, and every
`u ∈ C¹(pd n ρ c)` with `0 < a < b < c ≤ 4`,

`‖u‖_{C^{1,α}(pd n ρ a)} ≤ C·(Σ_j ‖(∂̄_Ju)·e_j‖_{C^{0,α}(pd n ρ c)} + ‖u‖_{L²(pd n ρ c)})`

with `C` depending only on `n, α, ρ, a, b, c` (uniform in `A` and `ε`). -/
theorem aPrioriEstimate_local_L2_flex {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (A : Cn n → Cn n →L[ℝ] Cn n),
        (∀ m : ℕ, ContDiff ℝ m A) →
        ∀ {ε : ℝ}, ε ≤ ε₀ →
        VecHolder (fun z => A z) α ε (pd n ρ 4) →
        (∀ z, z ∈ pd n ρ 4 → ∀ v : Cn n,
          (JstdCn n + A) z ((JstdCn n + A) z v) = -v) →
        ∀ u : Cn n → ℂ, ContDiffOn ℝ 1 u (pd n ρ c) →
          Work.CR.Flat.holderNorm 1 α u (pd n ρ a)
            ≤ ENNReal.ofReal C *
                ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
                    (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (pd n ρ c))
                  + MeasureTheory.eLpNorm u 2
                      (MeasureTheory.volume.restrict (pd n ρ c))) := by
  -- the two pillars, at the radii `bρ` (data/sup) and `aρ` (conclusion), `cρ` (data/`L²`)
  obtain ⟨ε₁, hε₁, C₁, hC₁, H₁⟩ :=
    LevJ.supRemainderSchauder_v (n := n) hn hα0 hα1
      (ρ := fun j => b * ρ j) (ρ' := fun j => a * ρ j)
      (fun j => by have := hρ j; nlinarith)
      (fun j => by have := hρ j; nlinarith)
      (fun j => by have := hρ j; nlinarith)
  obtain ⟨ε₂, hε₂, C₂, hC₂, H₂⟩ :=
    LevJLoc.supEstimateL2_v (n := n) hn hα0 hα1
      (σ := fun j => b * ρ j) (ρ := fun j => c * ρ j)
      (fun j => by have := hρ j; nlinarith)
      (fun j => by have := hρ j; nlinarith)
      (fun j => by have := hρ j; nlinarith)
  refine ⟨max 1 (C₁ * (1 + C₂)), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    ⟨min (ε₁ / 2) (min (ε₂ / 2) (1 / 2)), lt_min (by linarith) (lt_min (by linarith)
      (by norm_num)), ?_⟩⟩
  intro A hAsm ε hε hV hJ u hu
  -- `0 ≤ ε`, from `‖A 0‖ ≤ ε`
  have hε0 : 0 ≤ ε := by
    have h0 : (0 : Cn n) ∈ pd n ρ 4 := by
      rw [mem_pd]
      intro j
      have hj := hρ j
      simp only [Pi.zero_apply, norm_zero]
      nlinarith
    exact le_trans (norm_nonneg (A 0)) (hV.1 0 h0)
  have hε₁' : 2 * ε ≤ ε₁ := by
    have h := le_trans hε (min_le_left (ε₁ / 2) (min (ε₂ / 2) (1 / 2)) : _)
    linarith
  have hε₂' : 2 * ε ≤ ε₂ := by
    have h := le_trans hε (le_trans (min_le_right (ε₁ / 2) (min (ε₂ / 2) (1 / 2)))
      (min_le_left (ε₂ / 2) (1 / 2)) : _)
    linarith
  -- the per-column `VecHolder`, from the operator-valued hypothesis
  have hcol : ∀ i : Fin n, VecHolder (fun z => A z (Pi.single i 1)) α ε (pd n ρ 4) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro z hz
      calc ‖A z (Pi.single i 1)‖ ≤ ‖A z‖ * ‖(Pi.single i (1 : ℂ) : Cn n)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖A z‖ := by rw [Pi.norm_single, norm_one, mul_one]
        _ ≤ ε := hV.1 z hz
    · intro z hz z' hz'
      calc ‖(A z - A z') (Pi.single i 1)‖
          ≤ ‖A z - A z'‖ * ‖(Pi.single i (1 : ℂ) : Cn n)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖A z - A z'‖ := by rw [Pi.norm_single, norm_one, mul_one]
        _ ≤ ε * ‖z - z'‖ ^ α := hV.2 z hz z' hz'
  -- the componentwise level-`0` smallness, on the two polydiscs of the pillars
  have hcompb : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (pd n ρ b) ≤ ENNReal.ofReal ε₁ := by
    intro i j
    have h1 := vecHolder_comp_holderNorm_zero (n := n) (φ := fun z => A z (Pi.single i 1))
      (hcol i) hε0 j
    have h2 : Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (pd n ρ b)
        ≤ Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (pd n ρ 4) :=
      Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 4) (isOpen_pd ρ b)
        (pd_mono hρ (by linarith)) 0 α _
    refine h2.trans (h1.trans ?_)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcompc : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => A z (Pi.single i 1) j) (pd n ρ c) ≤ ENNReal.ofReal ε₂ := by
    intro i j
    have h1 := vecHolder_comp_holderNorm_zero (n := n) (φ := fun z => A z (Pi.single i 1))
      (hcol i) hε0 j
    have h2 : Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (pd n ρ c)
        ≤ Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j) (pd n ρ 4) :=
      Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 4) (isOpen_pd ρ c)
        (pd_mono hρ hc) 0 α _
    refine h2.trans (h1.trans ?_)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the almost-complexity, restricted to the two pillars' regions
  have hJb : ∀ z : Cn n, z ∈ Work.CR.Flat.polydisc 0 (fun j => b * ρ j) → ∀ v : Cn n,
      (JstdCn n + A) z ((JstdCn n + A) z v) = -v :=
    fun z hz v => hJ z (pd_mono hρ (by linarith) hz) v
  have hJc : ∀ z : Cn n, z ∈ Work.CR.Flat.polydisc 0 (fun j => c * ρ j) → ∀ v : Cn n,
      (JstdCn n + A) z ((JstdCn n + A) z v) = -v :=
    fun z hz v => hJ z (pd_mono hρ hc hz) v
  -- the two estimates
  have hA1 : Work.CR.Flat.holderNorm 1 α u (pd n ρ a)
      ≤ ENNReal.ofReal C₁ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ b))
          + ⨆ z ∈ pd n ρ b, ENNReal.ofReal ‖u z‖) :=
    H₁ hAsm (ε := ε₁) le_rfl hcompb hJb u (hu.mono (pd_mono hρ (by linarith)))
  have hZ : (⨆ z ∈ pd n ρ b, ENNReal.ofReal ‖u z‖)
      ≤ ENNReal.ofReal C₂ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ c))
          + MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (pd n ρ c))) :=
    H₂ hAsm (ε := ε₂) le_rfl hcompc hJc u hu
  have hmono : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
        (pd n ρ b))
      ≤ (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
        (pd n ρ c)) :=
    Finset.sum_le_sum fun j _ =>
      Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ c) (isOpen_pd ρ b)
        (pd_mono hρ (by linarith)) 0 α _
  calc Work.CR.Flat.holderNorm 1 α u (pd n ρ a)
      ≤ ENNReal.ofReal C₁ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ b))
          + ⨆ z ∈ pd n ρ b, ENNReal.ofReal ‖u z‖) := hA1
    _ ≤ ENNReal.ofReal C₁ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ c))
          + ENNReal.ofReal C₂ * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
              (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
              (pd n ρ c))
            + MeasureTheory.eLpNorm u 2
                (MeasureTheory.volume.restrict (pd n ρ c)))) := by
        gcongr
    _ ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ c))
          + MeasureTheory.eLpNorm u 2
              (MeasureTheory.volume.restrict (pd n ρ c))) :=
        ennreal_chain hC₁.le hC₂.le _ _
    _ ≤ ENNReal.ofReal (max 1 (C₁ * (1 + C₂))) * ((∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (pd n ρ c))
          + MeasureTheory.eLpNorm u 2
              (MeasureTheory.volume.restrict (pd n ρ c))) := by
        gcongr
        exact le_max_right _ _

end Work.NN.Final
