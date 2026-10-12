import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Closure
import Submission.ConcaveUniformR
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the closure: Ingredient 1 implies the upper side `gcSup_upper`.

INGREDIENT 1 (`gcExcess_witness_aux v ρmax ρ`, `Submission.Excess`): the
canonical ground state at density `ρ` is asymptotically `μ`-optimal, i.e. the
canonical excess `diag(ρ,L) − sSup_μ h_L(μ)` vanishes as `L → ∞` (T = 0
equivalence of ensembles).  This module proves that Ingredient 1 at every
`ρ ∈ (0,ρmax)` yields `gcSup_upper v ρmax`, i.e.

    ∀ ρ ∈ (0,ρmax):  diagLimsup v ρ ≤ gcSup v ρmax ρ

(the equivalence-of-ensembles UPPER side).  With the lower leg
`diagLiminf ≥ gcSup` (`GCPressure.diagLiminf_ge_gcSup`) and the continuity of
`gcSup` this closes Layer 2: the diagonal limit exists at each `ρ ∈ (0,ρmax)`
and equals `gcSup`, and (`GCPressure.eventually_hconv_of_gcSup_upper`) the box
densities converge along the joint filter at every small density.

PROOF PLAN (for the main theorem below).  Fix `ρ` with `0 < ρ < ρmax`.

STEP 1 — excess reduction.  Ingredient 1 at `ρ` gives, for every `ε > 0`,
eventually `diag(ρ,L) − canonSup(ρ,L) ≤ ε` (`Excess.gcExcess_vanishes_of_witness_aux`),
where `canonSup(ρ,L) := sSup_μ h_L(μ)`.  Passing to limsups over `atTop`
(`limsup` inequalities in the style of `DiagLimits`, both sides bounded since
`0 ≤ canonSup ≤ diag` and `0 ≤ diag ≤ C`) yields
`diagLimsup v ρ ≤ limsup_L canonSup(ρ,L)`.

STEP 2 — compact truncation.  `hL_tail_decay` gives `M > 0` with eventually
`h_L(μ) ≤ h_L(0)` for all `μ ≥ M`; since `h_L(0) ≥ 0` lies in the range,
`canonSup_eq_sSup_Icc` gives eventually
`canonSup(ρ,L) = sSup (h_L '' [0,M])`, hence
`limsup_L canonSup(ρ,L) = limsup_L sSup(h_L '' [0,M])`.

STEP 3 — sup-limsup exchange on `[0,M]`.  Fix `0 < a ≤ M`.  Write
`[0,M] = [0,a] ∪ [a,M]`.  On the interior part `[a,M]`, the family
`h_L` is concave (`hL_concaveOn`) and converges pointwise to the concave
`g := gVal` (`hL_tendsto`), so `limsup_sup_le_sup_of_concaveOn_R` bounds
`limsup sup_{[a,M]} h_L ≤ sup_{[a,M]} g`.  On the boundary strip `[0,a]`,
`hL_lipschitz_zero` (`|h_L(μ)−h_L(0)| ≤ 2μρmax`) and the convergence of
`h_L(0)` to `g(0)` bound `limsup sup_{[0,a]} h_L ≤ g(0) + 2aρmax`.
Since `sup_{[0,M]} g ≥ g(0)` and `≥ sup_{[a,M]} g`, one obtains
`limsup sup_{[0,M]} h_L ≤ sup_{[0,M]} g + 2aρmax`; letting `a → 0⁺`
(`∀ a > 0`) gives `limsup_L sup_{[0,M]} h_L ≤ sup_{[0,M]} g`.

STEP 4 — bound by the Legendre supremum.  `[0,M] ⊆ [0,∞)`, so
`sup_{[0,M]} g ≤ gcSup v ρmax ρ` (`gcSupSet_bddAbove` for `ρ < ρmax`).
Assembling Steps 1–4: `diagLimsup v ρ ≤ gcSup v ρmax ρ`.

Steps 3–4 are combined below into the single lemma
`limsup_sSup_hL_Icc_le_gcSup` (bounding every element of `h_L '' [0,M]`
pointwise by `gcSup + slack`, first on the boundary strip `[0,a]` via
`hL_lipschitz_zero` and on `[a,M]` via uniform convergence — Steps 3–4 — and
then shrinking the strip width `a` and the slacks).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary analytic facts for the closure -/

/-- `limsup u ≤ limsup v + ε` from the eventual pointwise inequality
`u ≤ v + ε` (both families nonnegative / bounded above as in `DiagLimits`). -/
lemma limsup_le_add_of_eventually_le {u v : ℝ → ℝ} {ε : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, u L ≤ v L + ε)
    (hu0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L)
    (hvB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, v L ≤ B) :
    limsup u atTop ≤ limsup v atTop + ε := by
  rw [limsup_eq]
  let S_u : Set ℝ := {a | ∀ᶠ L : ℝ in atTop, u L ≤ a}
  let S_v : Set ℝ := {a | ∀ᶠ L : ℝ in atTop, v L ≤ a}
  change sInf S_u ≤ sInf S_v + ε
  have hSu_bdd : BddBelow S_u := by
    refine ⟨0, ?_⟩
    intro a ha
    exact atTop_le_of_eventually (u := u) hu0 ha
  have hSmem : ∀ a : ℝ, a ∈ S_v → a + ε ∈ S_u := by
    intro a ha
    have hvle : ∀ᶠ L : ℝ in atTop, v L ≤ a := ha
    filter_upwards [h, hvle] with L hL hvL
    exact le_trans hL (by linarith)
  have hSb : ∀ a : ℝ, a ∈ S_v → sInf S_u ≤ a + ε := by
    intro a ha
    exact csInf_le hSu_bdd (hSmem a ha)
  rcases hvB with ⟨B, hB⟩
  have hSnon : S_v.Nonempty := ⟨B, hB⟩
  have hbase : sInf S_u - ε ≤ sInf S_v := by
    apply le_csInf hSnon
    intro b hb
    have hx := hSb b hb
    linarith
  linarith

/-- `canonSup(ρ,L)` is eventually bounded above (it is below the diagonal). -/
lemma canonSup_eventually_bdd_above {v : ℝ³ → ℝ} {ρ ρmax : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax) :
    ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, canonSup v ρmax ρ L ≤ B := by
  rcases diag_eventually_bdd_above (v := v) (ρ := ρ) hv1 hρ0 with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with L hLB hL1
  have hLpos : 0 < L := by linarith
  have hle : canonSup v ρmax ρ L ≤ diag v ρ L := by
    unfold canonSup
    apply csSup_le (gcCanonSet_nonempty v ρmax ρ L)
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    exact gcDensity_add_mu_rho_L_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
      hv hρmax hLpos hρ0 (le_of_lt hρm) hμ
  exact le_trans hle hLB

/-- `g := gVal` is concave in the chemical potential on `[0,∞)` (a concave
pressure plus the affine term `μ·ρ`). -/
lemma gVal_concaveOn {v : ℝ³ → ℝ} {ρmax ρ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => gVal v ρmax ρ μ) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simp only [smul_eq_mul]
  have hineq := gcPressure_concave_ineq (v := v) (ρmax := ρmax) (μ₁ := x) (μ₂ := y) (t := a)
    hv hv1 hρmax hR hsupp hx0 hy0 ha ha1
  calc
    a * gVal v ρmax ρ x + (1 - a) * gVal v ρmax ρ y
        = a * (gcPressure v ρmax x + x * ρ) + (1 - a) * (gcPressure v ρmax y + y * ρ) := by
            simp [gVal]
    _ = a * gcPressure v ρmax x + (1 - a) * gcPressure v ρmax y +
          (a * (x * ρ) + (1 - a) * (y * ρ)) := by ring
    _ ≤ gcPressure v ρmax (a * x + (1 - a) * y) + (a * (x * ρ) + (1 - a) * (y * ρ)) := by
            exact add_le_add hineq le_rfl
    _ = gcPressure v ρmax (a * x + (1 - a) * y) + (a * x + (1 - a) * y) * ρ := by
            have hlin : (a * x + (1 - a) * y) * ρ = a * (x * ρ) + (1 - a) * (y * ρ) := by ring
            rw [hlin]
    _ = gVal v ρmax ρ (a * x + (1 - a) * y) := by
            simp [gVal]

/-- Uniform convergence of `h_L` to `g` on the interior compact interval
`[a,M]` (`0 < a ≤ M`): the concave family converges uniformly there
(`ConcaveUniformR`; the per-box concavity needs only `L ≥ 1`, so the family is
truncated by the concave constant `0` on `L < 1`). -/
lemma uniform_hL_Icc_interior {v : ℝ³ → ℝ} {ρ ρmax a M : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) (hρmax : 0 < ρmax)
    (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax) (h0a : 0 < a) (haM : a ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ μ : ℝ, μ ∈ Set.Icc a M →
      |hL v ρmax ρ μ L - gVal v ρmax ρ μ| < ε := by
  intro ε hε
  let F : ℝ → ℝ → ℝ := fun L μ => if 1 ≤ L then hL v ρmax ρ μ L else 0
  have hf : ∀ L : ℝ, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (F L) := by
    intro L
    by_cases hL1 : 1 ≤ L
    · have hLpos : 0 < L := by linarith
      have hEq : F L = (fun μ : ℝ => hL v ρmax ρ μ L) := by
        ext μ
        simp [F, hL1]
      rw [hEq]
      exact hL_concaveOn (v := v) (ρmax := ρmax) (ρ := ρ) (L := L) hv hρmax.le hLpos
    · have hEq : F L = (fun _ : ℝ => (0 : ℝ)) := by
        ext μ
        simp [F, hL1]
      rw [hEq]
      refine ⟨convex_Ici (0 : ℝ), ?_⟩
      intro x hx y hy a b ha hb hab
      simp [smul_eq_mul]
  have hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => gVal v ρmax ρ μ) :=
    gVal_concaveOn (v := v) (ρmax := ρmax) (ρ := ρ) hv hv1 hρmax.le hR hsupp
  have hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun L : ℝ => F L x) atTop (𝓝 (gVal v ρmax ρ x)) := by
    intro x hx
    have ht := hL_tendsto (v := v) (ρ := ρ) (ρmax := ρmax) (μ := x) hx hρmax.le hρ0 hR hv hv1 hsupp
    have hFEq : (fun L : ℝ => F L x) =ᶠ[atTop] (fun L : ℝ => hL v ρmax ρ x L) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
      simp [F, hL1]
    exact ht.congr' hFEq.symm
  have hunif := concaveOn_uniformOn_Icc_R (f := F) (g := fun μ : ℝ => gVal v ρmax ρ μ)
    h0a haM hf hg hpt ε hε
  filter_upwards [hunif, eventually_ge_atTop (1 : ℝ)] with L hLunif hL1
  intro μ hμ
  have hx : |F L μ - gVal v ρmax ρ μ| < ε := hLunif μ hμ
  simpa [F, hL1] using hx

/-- Sup-limsup exchange on `[0,M]` against the Legendre supremum (Steps 3–4
of the plan): for `0 < ρ < ρmax`, `0 < M`,

    limsup_L (sup_{μ∈[0,M]} h_L(μ)) ≤ gcSup v ρmax ρ

Proof.  For slack `η > 0` choose `a ∈ (0,M]` so narrow that the boundary
strip `[0,a]` contributes less than `η/2` (via `hL_lipschitz_zero` and the
convergence of `h_L(0)` to `g(0)`).  On the interior `[a,M]` the family
converges uniformly to `g` (`uniform_hL_Icc_interior`), and `g ≤ gcSup` on
`μ ≥ 0`.  Every element of `h_L '' [0,M]` is therefore eventually below
`gcSup + η`, giving the limsup bound by `gcSup`. -/
lemma limsup_sSup_hL_Icc_le_gcSup {v : ℝ³ → ℝ} {ρ ρmax M : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hρmax : 0 < ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax) (hM : 0 < M) :
    Filter.limsup (fun L : ℝ => sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M)) atTop
      ≤ gcSup v ρmax ρ := by
  apply le_of_forall_pos_le_add
  intro η hη
  let a : ℝ := min M (η / (4 * ρmax + 1))
  have hden : 0 < 4 * ρmax + 1 := by nlinarith [hρmax]
  have hηpos : 0 < η / (4 * ρmax + 1) := div_pos hη hden
  have hapos : 0 < a := by
    dsimp [a]
    exact lt_min hM hηpos
  have haM : a ≤ M := by
    dsimp [a]
    exact min_le_left M (η / (4 * ρmax + 1))
  have h2a : 2 * a * ρmax < η / 2 := by
    have hamin : a ≤ η / (4 * ρmax + 1) := by
      dsimp [a]
      exact min_le_right M (η / (4 * ρmax + 1))
    have hlin : (4 * ρmax + 1) * a ≤ η := by
      have hmul : a * (4 * ρmax + 1) ≤ η / (4 * ρmax + 1) * (4 * ρmax + 1) :=
        mul_le_mul_of_nonneg_right hamin hden.le
      have hx : a * (4 * ρmax + 1) ≤ η := by
        rwa [div_mul_cancel₀ η hden.ne'] at hmul
      nlinarith
    have h4a : 4 * ρmax * a < η := by
      have h1 : 4 * ρmax * a + a ≤ η := by nlinarith [hapos]
      nlinarith [hapos]
    nlinarith
  -- uniform convergence on [a,M] with slack η/4
  have hcv := uniform_hL_Icc_interior (v := v) (ρ := ρ) (ρmax := ρmax) (a := a) (M := M)
    hv hv1 hR hsupp hρmax hρ0 hρm hapos haM (η / 4) (by positivity : 0 < η / 4)
  -- pointwise convergence of h_L(0) to g(0), slack η/4
  have ht0 := hL_tendsto (v := v) (ρ := ρ) (ρmax := ρmax) (μ := 0) (by norm_num) hρmax.le hρ0 hR hv hv1 hsupp
  have h0ev : ∀ᶠ L : ℝ in atTop, |hL v ρmax ρ 0 L - gVal v ρmax ρ 0| < η / 4 := by
    exact ht0.eventually (Metric.ball_mem_nhds (gVal v ρmax ρ 0) (by positivity : 0 < η / 4))
  have hbd : ∀ᶠ L : ℝ in atTop,
      sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M) ≤ gcSup v ρmax ρ + η := by
    filter_upwards [hcv, h0ev, eventually_ge_atTop (1 : ℝ)] with L hcvL h0L hL1
    have hLpos : 0 < L := by linarith
    apply csSup_le
    · refine ⟨hL v ρmax ρ 0 L, 0, ⟨le_rfl, hM.le⟩, rfl⟩
    · intro y hy
      rcases hy with ⟨μ, hμI, rfl⟩
      have hμ0 : 0 ≤ μ := hμI.1
      have hμM : μ ≤ M := hμI.2
      by_cases hμa : μ ≤ a
      · -- boundary strip [0,a]
        have hl := hL_lipschitz_zero (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
          hv hρmax.le hLpos hρ0 (le_of_lt hρm) hμ0
        have hmain1 : hL v ρmax ρ μ L ≤ hL v ρmax ρ 0 L + a * (2 * ρmax) := by
          have hb' : hL v ρmax ρ μ L - hL v ρmax ρ 0 L ≤ μ * (2 * ρmax) := (abs_le.mp hl).2
          have hμ2 : μ * (2 * ρmax) ≤ a * (2 * ρmax) :=
            mul_le_mul_of_nonneg_right hμa (by positivity : 0 ≤ 2 * ρmax)
          nlinarith
        have h0b : hL v ρmax ρ 0 L ≤ gVal v ρmax ρ 0 + η / 4 := by
          have hx : |hL v ρmax ρ 0 L - gVal v ρmax ρ 0| < η / 4 := h0L
          have hlo : hL v ρmax ρ 0 L - gVal v ρmax ρ 0 < η / 4 := (abs_lt.mp hx).2
          linarith
        have hg0 : gVal v ρmax ρ 0 ≤ gcSup v ρmax ρ := by
          simpa [gVal] using le_gcSup (v := v) (ρmax := ρmax) (ρ := ρ) (μ := 0) hv hv1 hρmax.le hρm (by norm_num) hR hsupp
        have hsum : a * (2 * ρmax) + η / 4 ≤ η := by nlinarith [h2a]
        nlinarith [hmain1, h0b, hg0, hsum]
      · -- interior [a,M]
        have haμ : a ≤ μ := le_of_lt (lt_of_not_ge hμa)
        have hmem : μ ∈ Set.Icc a M := ⟨haμ, hμM⟩
        have hcvμ : |hL v ρmax ρ μ L - gVal v ρmax ρ μ| < η / 4 := hcvL μ hmem
        have hb : hL v ρmax ρ μ L ≤ gVal v ρmax ρ μ + η / 4 := by
          have hlo : hL v ρmax ρ μ L - gVal v ρmax ρ μ < η / 4 := (abs_lt.mp hcvμ).2
          linarith
        have hg : gVal v ρmax ρ μ ≤ gcSup v ρmax ρ := by
          simpa [gVal] using le_gcSup (v := v) (ρmax := ρmax) (ρ := ρ) (μ := μ) hv hv1 hρmax.le hρm hμ0 hR hsupp
        nlinarith [hb, hg, hη]
  have hnonneg : ∀ᶠ L : ℝ in atTop,
      (0 : ℝ) ≤ sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    have hLpos : 0 < L := by linarith
    have hz : hL v ρmax ρ 0 L ∈ (fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M :=
      ⟨0, ⟨le_rfl, hM.le⟩, rfl⟩
    have hbdd : BddAbove ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M) := by
      refine ⟨diag v ρ L, ?_⟩
      intro y hy
      rcases hy with ⟨μ, hμI, rfl⟩
      exact hL_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
        hv hρmax.le hLpos hρ0 (le_of_lt hρm) hμI.1
    have h0z : 0 ≤ hL v ρmax ρ 0 L := hL_zero_nonneg (v := v) (ρmax := ρmax) (ρ := ρ) (L := L) hρmax.le hLpos hv
    exact le_trans h0z (le_csSup hbdd hz)
  exact limsup_le_of_eventually_le (u := fun L : ℝ =>
      sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M))
    (B := gcSup v ρmax ρ + η) hbd hnonneg

/-- Ingredient 1 at every density of `(0,ρmax)` implies the upper side. -/
theorem gcSup_upper_of_excess {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) {ρmax : ℝ}
    (hρmax : 0 < ρmax) (haux : ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ) :
    gcSup_upper v ρmax := by
  unfold gcSup_upper
  intro ρ hρpos hρlt
  have hρ0 : 0 ≤ ρ := le_of_lt hρpos
  -- STEP 1: excess reduction, diagLimsup ≤ limsup canonSup
  have hstep1 : diagLimsup v ρ ≤ Filter.limsup (fun L : ℝ => canonSup v ρmax ρ L) atTop := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hvan := gcExcess_vanishes_of_witness_aux (v := v) (ρmax := ρmax) (ρ := ρ)
      hv hρmax.le hρpos hρlt (haux ρ hρpos hρlt)
    have hev : ∀ᶠ L : ℝ in atTop, diag v ρ L ≤ canonSup v ρmax ρ L + ε := by
      filter_upwards [hvan ε hε] with L hL
      have hx : diag v ρ L - canonSup v ρmax ρ L ≤ ε := by
        simpa [gcExcess, canonSup] using hL
      linarith
    have hineq := limsup_le_add_of_eventually_le (u := fun L : ℝ => diag v ρ L)
      (v := fun L : ℝ => canonSup v ρmax ρ L) hev
      (diag_eventually_nonneg (v := v) (ρ := ρ) hv)
      (canonSup_eventually_bdd_above (v := v) (ρ := ρ) (ρmax := ρmax) hv hv1 hρmax.le hρ0 hρlt)
    simpa [diagLimsup] using hineq
  -- STEP 2: compact truncation of the supremum
  rcases hL_tail_decay (v := v) hv hv1 (ρmax := ρmax) (ρ := ρ) hρmax hρ0 hρlt with ⟨M, hMpos, hdecay⟩
  have hIcc : ∀ᶠ L : ℝ in atTop,
      canonSup v ρmax ρ L = sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M) :=
    canonSup_eq_sSup_Icc (v := v) hv hv1 (ρmax := ρmax) (ρ := ρ) (M := M)
      hρmax hρ0 hρlt hMpos hdecay
  have hlimEq : Filter.limsup (fun L : ℝ => canonSup v ρmax ρ L) atTop =
      Filter.limsup (fun L : ℝ =>
        sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M)) atTop :=
    Filter.limsup_congr hIcc
  -- STEPS 3–4: limsup of the truncated suprema is below the Legendre supremum
  have hstep34 : Filter.limsup (fun L : ℝ =>
        sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M)) atTop ≤ gcSup v ρmax ρ :=
    limsup_sSup_hL_Icc_le_gcSup (v := v) (ρ := ρ) (ρmax := ρmax) (M := M)
      hv hv1 hR hsupp hρmax hρ0 hρlt hMpos
  calc
    diagLimsup v ρ ≤ Filter.limsup (fun L : ℝ => canonSup v ρmax ρ L) atTop := hstep1
    _ = Filter.limsup (fun L : ℝ =>
          sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M)) atTop := hlimEq
    _ ≤ gcSup v ρmax ρ := hstep34

end BoseGases

end Submission
