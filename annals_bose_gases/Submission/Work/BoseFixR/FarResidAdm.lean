import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.FarBogPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarResidAdm.lean` — FS §9's residual word at the honest family

The target `Work.BoseFixR.FarResidAdm` is FS `lem:Roughbounds`'s residual estimate
(`eq:Rough2` + `eq:Rough0` + `eq:Rough1`) at the honest model `HonestBoxFam`:

```
-(ErrRes v μ ρ)‖f‖² ≤ ½ρ²ℓ³Ŵ₁ω(0)‖f‖² + ⟨KzBogFS F E ρ⟩ + ⟨linOpT⟩ + ⟨Q2ex⟩ + ⟨Q3T⟩ .
```

The reduction (this file) splits `KzBogFS` at FS's `eq:ChoiceEpsilon` parameter
`ε = epsFar v μ ρ`, so that

* `qw (KzBogFS F E ρ) = qw (KzBogFS F (farEnv E v μ ρ) ρ) + Σ_k ½(ετ_k − ρε^{-1/2}a)⟨(n_k+n_{-k})f,f⟩`
  (`KzBogFS_sub_farEnv`, `KzBogFS_epsSplit`), and the correction is `≥ −ρε^{-1/2}a·Σ_k⟨(n_k+n_{-k})f,f⟩`
  (`epsCorr_lower`);
* at `farEnv E v μ ρ` the pair form has diagonal `𝒜₁ = (1−ε)τ + ρε^{-1/2}a + ρŴ₁` and
  off-diagonal `ℬ = ρŴ₁`, so `FarBogPair` applies and gives
  `−zpSumOf (farEnv E v μ ρ) ρ‖f‖² ≤ qw (KzBogFS F (farEnv E v μ ρ) ρ)`.

The two residual estimates are FS `eq:Rough2` (`Work.BoseFixR.FarMassFix`) and FS
`eq:Rough0`+`eq:Rough1` (`Work.BoseFixR.FarThreeQFix`); see `FINDING_FarResidAdm.md`.

**SKELETON — the target is not derivable from the stated hypotheses.**
The file keeps the requested statement *verbatim* with its single `sorry`, as this directory
does for a target whose hypotheses do not supply what the conclusion needs
(`HonW1sqRowAbs.lean`, `FarQ3Wedge.lean`, `FarMassFix.lean`, `FarThreeQ.lean`).
Session 4 (`FINDING_FarResidAdm_S4.md`) established that the conclusion requires an
`N`-free numerical bound on the lattice sum `Σ_{k∈Lab N}Ŵ₁(k)²` (equivalently
`Σ_k Ŵ₁(k)²/τ_k`): the cube size `N` is a *free field* of `HM : ∀ μ, HonestModes v μ` with no
upper bound in the hypotheses, while the conclusion is `N`-free; `hW1` is only *pointwise*
(`|Ŵ₁(k)| ≤ 16πa`, itself a consequence of `hview`), and the view's gate carries the row only
with an existential, monotone `K₀`.  Every `K₀`-free supplier in the corpus needs an input the
hypotheses lack (`SumW1sqRow`: the refuted pointwise decay of `Ŵ₁`; `SamplingSqSumLeChiR0`:
an a.e. bound on `W1fun` and the overlap count `(2χ+1)³` with `χ = chiR0` opaque; the Ewald
chapter `SmallBoxEwald`/`SmallBoxSpectral`: the opposite direction with a relative slack
`≥ 1` and the `δ`-inner-region condition; `BoseB6Est.fsZeroPoint_le`: FS's own mesh relation).
The two sibling rows from the same hypothesis list (`HonW1sqRowAbs`, `FarQ3Wedge` = FS's
`eq:Rough1`) were declared not derivable for exactly this reason.  See
`FINDING_FarResidAdm_S4.md` §5 for the repair (add the lattice row / an explicit `R ≤ c·ℓ`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The projections of the ε-split environment `farEnv` -/

section Projections

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

@[simp] lemma farEnv_tau (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).tau k
      = (1 - epsFar v μ ρ) * E.tau k + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := rfl

@[simp] lemma farEnv_W1 (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).W1 k = E.W1 k := rfl

@[simp] lemma farEnv_mu (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) :
    (farEnv E v μ ρ).mu = E.mu := rfl

@[simp] lemma farEnv_ell (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) :
    (farEnv E v μ ρ).ell = E.ell := rfl

@[simp] lemma farEnv_hatChi (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).hatChi k = E.hatChi k := rfl

@[simp] lemma farEnv_hatChiSq (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).hatChiSq k = E.hatChiSq k := rfl

@[simp] lemma farEnv_A (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).A k
      = (1 - epsFar v μ ρ) * E.tau k + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v
        + ρ * E.W1 k := rfl

@[simp] lemma farEnv_B (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (farEnv E v μ ρ).B k = ρ * E.W1 k := rfl

@[simp] lemma KzEnvAt_farEnv_A (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (KzEnvAt (farEnv E v μ ρ) ρ).A k
      = (1 - epsFar v μ ρ) * E.tau k + ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v
        + ρ * E.W1 k := rfl

@[simp] lemma KzEnvAt_farEnv_B (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (k : Mode) :
    (KzEnvAt (farEnv E v μ ρ) ρ).B k = ρ * E.W1 k := rfl

@[simp] lemma KzEnvAt_farEnv_z (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) :
    (KzEnvAt (farEnv E v μ ρ) ρ).z = (KzEnvAt E ρ).z := rfl

end Projections

/-! ## 2. The `ε`-split of the Bogoliubov quadratic -/

/-- `KzBogFS` depends on the environment only through `tau`, `W1`, `mu`, `ell` and
`hatChi`; the difference of the two quadratic forms at `E` and at the `ε`-split
environment is therefore purely the diagonal correction `(E.tau k − (farEnv E v μ ρ).tau k)`. -/
theorem KzBogFS_sub_farEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) :
    KzBogFS F E ρ - KzBogFS F (farEnv E v μ ρ) ρ
      = ∑ k : Mode, (1 / 2 : ℝ) •
          ((E.tau k - (farEnv E v μ ρ).tau k) • (F.nOp k + F.nOp (-k))) := by
  simp only [KzBogFS]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [farEnv_tau, farEnv_W1, farEnv_mu, farEnv_hatChi, farEnv_ell]
  module

/-- **FS `eq:ChoiceEpsilon`'s split of the residual Bogoliubov word.** -/
theorem KzBogFS_epsSplit {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (f : F.H) :
    F.qw f (KzBogFS F E ρ)
      = F.qw f (KzBogFS F (farEnv E v μ ρ) ρ)
        + ∑ k : Mode, (1 / 2 : ℝ) * ((E.tau k - (farEnv E v μ ρ).tau k)
            * F.qw f (F.nOp k + F.nOp (-k))) := by
  have h := KzBogFS_sub_farEnv F E v μ ρ
  have hsum : (∑ k : Mode, (1 / 2 : ℝ) •
        ((E.tau k - (farEnv E v μ ρ).tau k) • (F.nOp k + F.nOp (-k))))
      = ∑ k : Mode, ((1 / 2 : ℝ) * (E.tau k - (farEnv E v μ ρ).tau k)) •
          (F.nOp k + F.nOp (-k)) :=
    Finset.sum_congr rfl fun k _ => smul_smul _ _ _
  have hD : F.qw f (∑ k : Mode, (1 / 2 : ℝ) •
        ((E.tau k - (farEnv E v μ ρ).tau k) • (F.nOp k + F.nOp (-k))))
      = ∑ k : Mode, ((1 / 2 : ℝ) * (E.tau k - (farEnv E v μ ρ).tau k))
          * F.qw f (F.nOp k + F.nOp (-k)) := by
    rw [hsum, qw_sum_finset_zp F Finset.univ
      (fun k => (1 / 2 : ℝ) * (E.tau k - (farEnv E v μ ρ).tau k))
      (fun k => F.nOp k + F.nOp (-k)) f]
  have h2 : F.qw f (KzBogFS F E ρ) - F.qw f (KzBogFS F (farEnv E v μ ρ) ρ)
      = ∑ k : Mode, ((1 / 2 : ℝ) * (E.tau k - (farEnv E v μ ρ).tau k))
          * F.qw f (F.nOp k + F.nOp (-k)) := by
    rw [← F.qw_sub f, h, hD]
  have h2' : F.qw f (KzBogFS F E ρ) = F.qw f (KzBogFS F (farEnv E v μ ρ) ρ)
      + ∑ k : Mode, ((1 / 2 : ℝ) * (E.tau k - (farEnv E v μ ρ).tau k))
          * F.qw f (F.nOp k + F.nOp (-k)) := by
    linarith [h2]
  rw [h2']
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## 3. The `ε`-split correction -/

/-- The quadratic form of `F.nOp k + F.nOp (-k)` is nonnegative. -/
lemma qw_nOp_add_neg_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (k : Mode) (f : F.H) :
    0 ≤ F.qw f (F.nOp k + F.nOp (-k)) := by
  rw [FockData.qw_add]
  have h1 : F.qw f (F.nOp k) = F.bp (F.a k f) (F.a k f) := by
    simp only [FockData.qw, FockData.nOp, LinearMap.comp_apply]
    exact F.aDag_adjoint k (F.a k f) f
  have h2 : F.qw f (F.nOp (-k)) = F.bp (F.a (-k) f) (F.a (-k) f) := by
    simp only [FockData.qw, FockData.nOp, LinearMap.comp_apply]
    exact F.aDag_adjoint (-k) (F.a (-k) f) f
  rw [h1, h2]
  exact add_nonneg (F.bp_nonneg _) (F.bp_nonneg _)

/-- **FS `eq:Rough0` (`ε`-split correction).**  With `ε = epsFar v μ ρ > 0` and `τ ≥ 0`, the
`ε`-split correction of the Bogoliubov quadratic is bounded below by
`−ρ ε^{-1/2} a · Σ_k⟨(n_k+n_{-k})f,f⟩` (the positive part `ετ_kn_k` is dropped). -/
theorem epsCorr_lower {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (v : E3 → ℝ) (μ ρ : ℝ) (f : F.H)
    (hav : 0 ≤ a v) (hε : 0 < epsFar v μ ρ) (hτ : ∀ k : Mode, 0 ≤ E.tau k) :
    -(∑ k : Mode, (1 / 2 : ℝ) * ((E.tau k - (farEnv E v μ ρ).tau k)
        * F.qw f (F.nOp k + F.nOp (-k))))
      ≤ ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v
          * (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (F.nOp k + F.nOp (-k))) := by
  have hεnn : 0 ≤ epsFar v μ ρ := le_of_lt hε
  have hterm : ∀ k : Mode,
      -((1 / 2 : ℝ) * ((E.tau k - (farEnv E v μ ρ).tau k)
          * F.qw f (F.nOp k + F.nOp (-k))))
        ≤ (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)
            * ((1 / 2 : ℝ) * F.qw f (F.nOp k + F.nOp (-k))) := by
    intro k
    have hq := qw_nOp_add_neg_nonneg F k f
    have hkey : (0 : ℝ) ≤ (1 / 2) * epsFar v μ ρ * E.tau k
        * F.qw f (F.nOp k + F.nOp (-k)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεnn) (hτ k)) hq
    have hsplit : E.tau k - (farEnv E v μ ρ).tau k
        = epsFar v μ ρ * E.tau k - ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v := by
      rw [farEnv_tau]; ring
    have hgoal : -((1 / 2 : ℝ) * ((epsFar v μ ρ * E.tau k
          - ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v) * F.qw f (F.nOp k + F.nOp (-k))))
        = (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v)
            * ((1 / 2 : ℝ) * F.qw f (F.nOp k + F.nOp (-k)))
          - ((1 / 2) * epsFar v μ ρ * E.tau k * F.qw f (F.nOp k + F.nOp (-k))) := by
      ring
    rw [hsplit, hgoal]
    linarith [hkey]
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact h

/-! ## 4. The cheap half of FS `eq:Rough0`/`eq:Rough1`: the `Q₂^ex` word -/

/-- `F.bp ((Σ_{k∈s} n_k) f) f` as a sum of quadratic forms. -/
lemma bp_sum_nOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (s : Finset Mode) (f : F.H) :
    F.bp ((∑ k ∈ s, F.nOp k) f) f = ∑ k ∈ s, F.qw f (F.nOp k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, map_add,
        LinearMap.add_apply, ih]
      rfl

/-- **The quadratic word `Q₂^ex` against the window.**  `Q₂^ex = Σ_k ρ(Ŵ₁ω_k+Ŵ₁ω(0))n_k`
is bounded below by `−ρ·32πa·Cn·𝓜‖f‖²`: pointwise `|Ŵ₁ω| ≤ 16πa` and Cauchy–Schwarz on
the window (`⟨n₊^χf,f⟩ ≤ Cn⟨n₊f,f⟩ ≤ Cn𝓜‖f‖²`). -/
theorem qw_Q2ex_lower {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (f : F.H) (Cn M : ℝ)
    (hCn0 : 0 ≤ Cn)
    (hCn : ∀ g : F.H, F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g)
    (hM : 0 ≤ M) (hwin : T.NWindow M f)
    (ha : 0 ≤ E.aScat) (hρ : 0 ≤ E.rho)
    (hW1o : ∀ k : Mode, |E.W1omega k| ≤ 16 * Real.pi * E.aScat)
    (hW1o0 : |E.W1omega0| ≤ 16 * Real.pi * E.aScat) :
    -(E.rho * (32 * Real.pi * E.aScat) * Cn * M) * F.normSq f ≤ F.qw f (F.Q2ex E) := by
  have hqnn : ∀ k : Mode, 0 ≤ F.qw f (F.nOp k) := by
    intro k
    simp only [FockData.qw, FockData.nOp, LinearMap.comp_apply]
    rw [F.aDag_adjoint k (F.a k f) f]
    exact F.bp_nonneg _
  have hsum_le : (∑ k ∈ Work.BoseB7.excited Mode, F.qw f (F.nOp k))
      ≤ ∑ k : Mode, F.qw f (F.nOp k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
    intro k _ _
    exact hqnn k
  have hfull : (∑ k : Mode, F.qw f (F.nOp k))
      = F.bp ((∑ k : Mode, F.nOp k) f) f := (bp_sum_nOp F _ f).symm
  have hbnd : (∑ k ∈ Work.BoseB7.excited Mode, F.qw f (F.nOp k)) ≤ Cn * M * F.normSq f := by
    have h1 : F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := hCn f
    have h2 : F.bp (T.N f) f ≤ M * F.normSq f := NWindow_bp_N_le F T hM hwin
    calc (∑ k ∈ Work.BoseB7.excited Mode, F.qw f (F.nOp k))
        ≤ ∑ k : Mode, F.qw f (F.nOp k) := hsum_le
      _ = F.bp ((∑ k : Mode, F.nOp k) f) f := hfull
      _ ≤ Cn * F.bp (T.N f) f := h1
      _ ≤ Cn * (M * F.normSq f) := mul_le_mul_of_nonneg_left h2 hCn0
      _ = Cn * M * F.normSq f := by ring
  have hq2 : F.qw f (F.Q2ex E)
      = ∑ k ∈ Work.BoseB7.excited Mode,
          (E.rho * (E.W1omega k + E.W1omega0)) * F.qw f (F.nOp k) := by
    rw [FockData.Q2ex]
    exact qw_sum_finset_zp F (Work.BoseB7.excited Mode)
      (fun k => E.rho * (E.W1omega k + E.W1omega0)) (fun k => F.nOp k) f
  rw [hq2]
  have hterm : ∀ k ∈ Work.BoseB7.excited Mode,
      -(E.rho * (32 * Real.pi * E.aScat)) * F.qw f (F.nOp k)
        ≤ (E.rho * (E.W1omega k + E.W1omega0)) * F.qw f (F.nOp k) := by
    intro k _
    have hk := hqnn k
    have hω : 0 ≤ E.W1omega k + E.W1omega0 + 32 * Real.pi * E.aScat := by
      have h1 := neg_le_of_abs_le (hW1o k)
      have h2 := neg_le_of_abs_le hW1o0
      linarith
    have hkey : (0 : ℝ) ≤ E.rho * (E.W1omega k + E.W1omega0 + 32 * Real.pi * E.aScat)
        * F.qw f (F.nOp k) := mul_nonneg (mul_nonneg hρ hω) hk
    nlinarith [hkey]
  calc -(E.rho * (32 * Real.pi * E.aScat) * Cn * M) * F.normSq f
      = -(E.rho * (32 * Real.pi * E.aScat)) * (Cn * M * F.normSq f) := by ring
    _ ≤ -(E.rho * (32 * Real.pi * E.aScat))
          * (∑ k ∈ Work.BoseB7.excited Mode, F.qw f (F.nOp k)) := by
        have hneg : -(E.rho * (32 * Real.pi * E.aScat)) ≤ 0 := by
          have : (0:ℝ) ≤ E.rho * (32 * Real.pi * E.aScat) :=
            mul_nonneg hρ (mul_nonneg (by positivity) ha)
          linarith
        nlinarith [hneg, hbnd]
    _ = ∑ k ∈ Work.BoseB7.excited Mode,
          -(E.rho * (32 * Real.pi * E.aScat)) * F.qw f (F.nOp k) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Work.BoseB7.excited Mode,
          (E.rho * (E.W1omega k + E.W1omega0)) * F.qw f (F.nOp k) :=
        Finset.sum_le_sum hterm

/-! ## 4b. The linear word `linOpT` against the window -/

/-- **`linOpT` against the window.**  `linOpT E = ρzŴ₁ω(0)Σ_s χ̂²_s(ã_s†+ã_s)` is bounded
below by `−2ρz(16πa)(Σ_s|χ̂²_s|)√𝓜‖f‖²` (`Work.BoseB7A.NWindow_linear_bound` plus
`√(Σc²) ≤ Σ|c|`). -/
theorem qw_linOpT_lower {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (f : F.H) (M : ℝ)
    (hM : 0 ≤ M) (hwin : T.NWindow M f)
    (hχ : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| ≤ 10 ^ 100)
    (hω : |E.W1omega0| ≤ 16 * Real.pi * E.aScat)
    (hρ : 0 ≤ E.rho) (hz : 0 ≤ E.z) (ha : 0 ≤ E.aScat) :
    -(E.rho * E.z * (16 * Real.pi * E.aScat) * 2 * 10 ^ 100 * Real.sqrt M) * F.normSq f
      ≤ F.qw f (T.linOpT E) := by
  have hxz : ∀ s ∈ Work.BoseB7.excited Mode, s ≠ 0 := by
    intro s hs
    rw [Work.BoseB7.excited, Finset.mem_erase] at hs
    exact hs.1
  have hlin := NWindow_linear_bound F T hM hwin (Work.BoseB7.excited Mode) hxz
    (fun s => E.hatChiSq s)
  have hq : F.qw f (T.linOpT E)
      = (E.rho * E.z * E.W1omega0)
          * F.qw f (∑ s ∈ Work.BoseB7.excited Mode,
              (E.hatChiSq s) • (T.taDag s + T.ta s)) := by
    rw [TildeData.linOpT, FockData.qw_smul]
  -- `√(Σc²) ≤ Σ|c|`
  have hsq : Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)
      ≤ ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq ?_))
    · have h3 : (∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s|) ^ 2
          = ∑ s ∈ Work.BoseB7.excited Mode, ∑ t ∈ Work.BoseB7.excited Mode,
              |E.hatChiSq s| * |E.hatChiSq t| := by
        rw [sq, Finset.sum_mul_sum]
      rw [h3]
      calc ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2
          = ∑ s ∈ Work.BoseB7.excited Mode,
              |E.hatChiSq s| * |E.hatChiSq s| := by
            exact Finset.sum_congr rfl fun s _ => by rw [← sq_abs]; ring
        _ ≤ ∑ s ∈ Work.BoseB7.excited Mode, ∑ t ∈ Work.BoseB7.excited Mode,
              |E.hatChiSq s| * |E.hatChiSq t| := by
            refine Finset.sum_le_sum fun s hs => ?_
            exact Finset.single_le_sum (s := Work.BoseB7.excited Mode)
              (f := fun t => |E.hatChiSq s| * |E.hatChiSq t|)
              (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hs
    · exact Finset.sum_nonneg fun s _ => abs_nonneg _
  have hXn : |F.qw f (∑ s ∈ Work.BoseB7.excited Mode,
        (E.hatChiSq s) • (T.taDag s + T.ta s))|
      ≤ 2 * 10 ^ 100 * Real.sqrt M * F.normSq f := by
    have h1 : Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2) ≤ 10 ^ 100 :=
      le_trans hsq hχ
    have hM' : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have hnsq : 0 ≤ F.normSq f := F.normSq_nonneg f
    have h2 : 2 * Real.sqrt M * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          E.hatChiSq s ^ 2) ≤ 2 * 10 ^ 100 * Real.sqrt M := by
      nlinarith [h1, hM']
    have hY : 2 * Real.sqrt M * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s ^ 2)
          * F.normSq f ≤ 2 * 10 ^ 100 * Real.sqrt M * F.normSq f := by
      nlinarith [h2, hnsq]
    exact le_trans hlin hY
  rw [hq]
  have hCabs : |E.rho * E.z * E.W1omega0| ≤ E.rho * E.z * (16 * Real.pi * E.aScat) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hρ, abs_of_nonneg hz]
    have hρz : 0 ≤ E.rho * E.z := mul_nonneg hρ hz
    nlinarith [hω, hρz, Real.pi_pos, ha]
  have hCX : |(E.rho * E.z * E.W1omega0)
        * F.qw f (∑ s ∈ Work.BoseB7.excited Mode,
            (E.hatChiSq s) • (T.taDag s + T.ta s))|
      ≤ (E.rho * E.z * (16 * Real.pi * E.aScat))
          * (2 * 10 ^ 100 * Real.sqrt M * F.normSq f) := by
    rw [abs_mul]
    have h1 := abs_nonneg (E.rho * E.z * E.W1omega0)
    have h2 := abs_nonneg (F.qw f (∑ s ∈ Work.BoseB7.excited Mode,
      (E.hatChiSq s) • (T.taDag s + T.ta s)))
    nlinarith [hXn, hCabs, h1, h2]
  have hfin := neg_abs_le ((E.rho * E.z * E.W1omega0)
        * F.qw f (∑ s ∈ Work.BoseB7.excited Mode,
            (E.hatChiSq s) • (T.taDag s + T.ta s)))
  have hgoal : -(E.rho * E.z * (16 * Real.pi * E.aScat) * 2 * 10 ^ 100 * Real.sqrt M)
        * F.normSq f
      = -((E.rho * E.z * (16 * Real.pi * E.aScat))
          * (2 * 10 ^ 100 * Real.sqrt M * F.normSq f)) := by
    ring
  rw [hgoal]
  linarith [hfin, hCX]

/-! ## 4c. The `ε`-smallness of FS `eq:ChoiceEpsilon` at FS's parameters -/

/-- **`ε² = 𝓜/((ρ+μ)ℓ³) ≤ (μa³)^{337/1292}` in the dilute regime.**  At FS's parameters
`𝓜 = (μa³)^{-327/1292}` (`bigM_paramsAt`) and `μℓ³ = (μa³)^{-166/323}`
(`mu_ell_cube_fsParams`), so `𝓜/(μℓ³) = (μa³)^{337/1292}`; the estimate follows from
`ρ + μ ≥ μ`.  This is the row that makes the `ε`-split usable (`ε^{1/2} ≤ t^{337/2584}`,
so `ε^{-1/2} ≫ 16π` and the `κ`-error is `ε^{1/2}`-suppressed). -/
theorem epsFar_sq_le {v : E3 → ℝ} {μ ρ : ℝ} (hμ : 0 < μ) (ha : 0 < a v) (hρ : 0 ≤ ρ) :
    (epsFar v μ ρ) ^ 2 ≤ Work.BoseBox.fsXp (dil v μ) (337 / 4) := by
  have ht : 0 < dil v μ := by
    rw [dil]; exact mul_pos hμ (pow_pos ha 3)
  have hℓ : 0 < ell v μ := by
    rw [ell, sideAt]
    exact Work.BoseBox.boxSide_pos hμ ha (Work.BoseBox.fsXp_pos ht)
  have hℓ3 : 0 < (ell v μ) ^ 3 := pow_pos hℓ 3
  have hnum : 0 ≤ bigMV v μ := bigMV_nonneg hμ ha
  have hden : μ * (ell v μ) ^ 3 ≤ (ρ + μ) * (ell v μ) ^ 3 := by
    nlinarith [hρ, hℓ3]
  have hdenpos : 0 < μ * (ell v μ) ^ 3 := mul_pos hμ hℓ3
  have hSpos : 0 < (ρ + μ) * (ell v μ) ^ 3 := by
    have : 0 < ρ + μ := by linarith
    exact mul_pos this hℓ3
  rw [epsFar, Real.sq_sqrt (div_nonneg hnum (le_of_lt hSpos))]
  have h1 : bigMV v μ = Work.BoseBox.fsXp (dil v μ) (-(327 / 4)) := by
    rw [bigMV, Work.BoseBox.bigM_paramsAt hμ ha]
    rfl
  have h2 : μ * (ell v μ) ^ 3 = Work.BoseBox.fsXp (dil v μ) (-166) := by
    have h := Work.BoseBox.mu_ell_cube_fsParams (a := a v) hμ ha
    rw [dil, ell, sideAt, Work.BoseBox.paramsAt]
    simp only [Work.BoseBox.fsXp]
    rw [h]
    congr 1
    norm_num
  have hle : bigMV v μ / ((ρ + μ) * (ell v μ) ^ 3) ≤ bigMV v μ / (μ * (ell v μ) ^ 3) :=
    div_le_div_of_nonneg_left hnum hdenpos hden
  refine le_trans hle ?_
  rw [h1, h2, div_eq_mul_inv, Work.BoseBox.fsXp_inv ht (-166)]
  simp only [neg_neg]
  rw [Work.BoseBox.fsXp_mul ht (-(327 / 4)) 166]
  congr 1
  norm_num

/-! ## 5. The target -/

theorem FarResidAdm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    (hW1o : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k|
          ≤ 16 * Real.pi * BoseGases.a v)
    (hchi : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 10 ^ 100)
    (hchiSq : ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k| ≤ 10 ^ 100)
    (hNfL : ((∑ s ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (f : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H)
    (hf : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM f) :
    -Work.BoseFixR.ErrRes v μ ρ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
      ≤ (1 / 2) * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
          * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq f
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (Work.BoseBoxFock.KzBogFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.linOpT
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.Q2ex
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))
        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.Q3T
              (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)) := by
  sorry

end Work.BoseFixR
