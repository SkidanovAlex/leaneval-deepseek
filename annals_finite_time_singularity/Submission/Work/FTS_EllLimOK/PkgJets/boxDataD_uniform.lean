import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.BoxReg_of_uniform
import Submission.Work.FTS_EllLimOK.ClosedUniq3_small
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_EllLimOK.HkMem_zero_diff
import Submission.Work.FTS_EllLimOK.HkMem_fatou
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_EllLimOK.PkgJets.clusterExtract
import Submission.Work.FTS_EllLimOK.PkgJets.thetaBound
import Submission.Work.FTS_EllLimOK.PkgJets.slotSliceData
import Submission.Work.FTS_EllLimOK.PkgJets.pinningBoundClean
import Submission.Work.FTS_EllLimOK.PkgJets.hkBundleTools
import Submission.Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.HkNorm_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PkgJets/boxDataD_uniform` — `BoxDataD` over the repaired packages

The proof decomposes into the five ingredient statements
`clusterExtract`, `pinningBound`, `thetaBound`, `hkMemOfJConv`, `slotSliceData`
(each delegated separately) and the assembly `boxDataD_of_clusterData` below.
-/

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Subsequences of a `LimSeq4` -/

/-- A subsequence of a `LimSeq4` is again a `LimSeq4` with the same limit. -/
theorem LimSeq4.subseq {α : ℝ} {fn : ℕ → Fn} {f : Fn} (h : Work.FTS_EllLimOK.LimSeq4 α fn f)
    {σ : ℕ → ℕ} (hσ : Filter.Tendsto σ Filter.atTop Filter.atTop) :
    Work.FTS_EllLimOK.LimSeq4 α (fun n => fn (σ n)) f where
  classC n := h.classC (σ n)
  bound := by obtain ⟨B, hB⟩ := h.bound; exact ⟨B, fun n => hB (σ n)⟩
  c4 := h.c4
  conv j i hji z θ hzθ := (h.conv j i hji z θ hzθ).comp hσ

/-! ## `ℋ⁰` is inherited from the `/cos θ`-slot -/

/-- Pointwise, on the angular interval, `|f · w/sin^{η/2}| ≤ |(f/cos θ) · w/sin^{η/2}|`
(the two sides coincide when `cos θ = 1`, and both vanish at `θ = π/2`). -/
theorem abs_mul_slot_le_cosDiv {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))|
      ≤ |f z θ / Real.cos θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))| := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · -- `θ = 0`: both sides vanish
    subst h0
    rw [show Real.sin (2 * 0) = 0 by norm_num, Real.zero_rpow
        (by norm_num [Work.Spaces.eta]), div_zero, mul_zero, abs_zero, Real.cos_zero,
      div_one, mul_zero, abs_zero]
  · rcases eq_or_lt_of_le hθ.2 with h | h
    · -- `θ = π/2`: both sides vanish
      subst h
      rw [show Real.sin (2 * (π / 2)) = 0 by
          rw [show 2 * (π / 2) = π by ring, Real.sin_pi],
        Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero, mul_zero, abs_zero,
        mul_zero, abs_zero]
    · have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hcos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hw : 0 ≤ Work.Spaces.w z := by
        unfold Work.Spaces.w
        positivity
      have hwt : 0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
        div_nonneg hw (Real.rpow_nonneg hsin.le _)
      have h2 : |f z θ| ≤ |f z θ / Real.cos θ| := by
        rw [abs_div, abs_of_pos hcos, le_div_iff₀ hcos]
        calc |f z θ| * Real.cos θ ≤ |f z θ| * 1 :=
              mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (abs_nonneg _)
          _ = |f z θ| := mul_one _
      rw [abs_mul, abs_mul, abs_of_nonneg hwt]
      exact mul_le_mul_of_nonneg_right h2 hwt

/-- The level-`0` `ℋ⁰`-membership is inherited from the `/cos θ`-slot, provided the integrand
of `f` is continuous on the open quadrant (which supplies its a.e. measurability). -/
theorem HkMem_zero_of_cosDiv {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (h : Work.Spaces.HkMem α 0 (fun z θ => f z θ / Real.cos θ)) :
    Work.Spaces.HkMem α 0 f := by
  refine Work.FTS.LocData.HkMem_of_majorant α 0 hcont
    (M := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => f z θ / Real.cos θ) z θ)
    (fun z hz => h.1 z hz) h.2 ?_
  intro z hz θ hθ
  rw [Work.FTS_EllLimOK.HkIntegrand_zero_eq, Work.FTS_EllLimOK.HkIntegrand_zero_eq]
  exact sq_le_sq.mpr (abs_mul_slot_le_cosDiv (f := f) (z := z) (θ := θ) hθ)

/-! ## The assembly -/

/-- **The main argument**, with the five ingredient statements as explicit hypotheses.

`hA` is `clusterExtract`: along a cofinal `σ` the sequence `E (fn ·)` has a cluster limit `Ψ`
which is `BoxReg` and satisfies the law.  `hB`/`hC` are `pinningBound`/`thetaBound`: the
source-scaled `ℋ⁰`-bounds for the two pieces `Φ̃ = PhiTil α g (E g)` and `Θ α g` of `E g`.
`hD` is `hkMemOfJConv`: Fatou for the `ℋ⁰`-membership along a pointwise convergent sequence,
given the slice integrability of the limit.  `hE` is `slotSliceData`: that slice integrability
plus the joint a.e.-measurability for a `BoxReg` function with the Dirichlet value at `π/2`. -/
theorem boxDataD_of_clusterData {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (E : Fn →ₗ[ℝ] Fn), Work.FTS_EllLimOK.HasPkgE α Ce E →
      ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0
        (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0
        (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ)
        ≤ C * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
    (hC : ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
        ≤ C * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
    (hE : ∀ {Ψ : ℝ → ℝ → ℝ}, Work.FTS_EllLimOK.BoxReg Ψ →
      (∀ z ∈ Set.Ioi (0 : ℝ), Ψ z (π / 2) = 0) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) z θ)
        Work.Spaces.Iθ) ∧
      AEMeasurable (fun p : ℝ × ℝ =>
          Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ / Real.cos θ) p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    : Work.FTS_EllLimOK.BoxDataD α Ce := by
  intro E hE' fn f hL a b ha hab
  obtain ⟨CB, hCBpos, hBbd⟩ := hB
  obtain ⟨CC, hCCpos, hCbd⟩ := hC
  obtain ⟨B₀, hB₀⟩ := hL.bound
  have hXL : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B₀ 0 :=
    fun n => le_trans (hB₀ n) (le_max_left _ _)
  -- the memberships of the members
  have hmemb (g : Fn) (hg : Work.FTS.ClassC.ClassC α g) :
      Work.Spaces.HkMem α 0 (fun z θ => E g z θ / Real.cos θ) := by
    have hGo := (hE'.toHasPkgD.toHasPkg g hg).1
    have hsum : (fun z θ => E g z θ / Real.cos θ)
        = fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
            + Work.Construction.Theta α g z θ / Real.cos θ := by
      funext z θ
      simp only [Work.Construction.PhiTil]
      ring
    refine Work.FTS_EllLimOK.PkgJets.hkMem_zero_of_abs_le_two
      (f := fun z θ => E g z θ / Real.cos θ)
      (Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hGo.smooth)
      (hBbd E hE' g hg).1 (hCbd g hg).1 ?_
    intro z hz θ hθ
    have hpt : E g z θ / Real.cos θ
        = Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
          + Work.Construction.Theta α g z θ / Real.cos θ := by
      simp only [Work.Construction.PhiTil]
      ring
    rw [hpt]
    exact abs_add_le _ _
  -- the uniform `HkSq` bound for the members
  have hsqi (g : Fn) (hg : Work.FTS.ClassC.ClassC α g)
      (hX : Work.FTS.StrongGlobal.Xn6 α g ≤ max B₀ 0) :
      Work.Spaces.HkSq α 0 (fun z θ => E g z θ / Real.cos θ)
        ≤ 2 * (CB + CC) * (1 + max B₀ 0) ^ 2 := by
    have hsum : (fun z θ => E g z θ / Real.cos θ)
        = fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
            + Work.Construction.Theta α g z θ / Real.cos θ := by
      funext z θ
      simp only [Work.Construction.PhiTil]
      ring
    rw [hsum]
    refine le_trans (Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α 0
      (hBbd E hE' g hg).1 (hCbd g hg).1 ?_) ?_
    · intro z hz θ hθ
      rw [Work.FTS_EllLimOK.HkIntegrand_zero_eq, Work.FTS_EllLimOK.HkIntegrand_zero_eq,
        Work.FTS_EllLimOK.HkIntegrand_zero_eq]
      nlinarith [sq_nonneg ((Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
          - Work.Construction.Theta α g z θ / Real.cos θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))]
    · have h1 : Work.Spaces.HkSq α 0
          (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ)
          ≤ CB * (1 + max B₀ 0) ^ 2 :=
        le_trans (hBbd E hE' g hg).2 (mul_le_mul_of_nonneg_left
          (by nlinarith [Work.Spaces.HkNorm_nonneg α 6 g, hX,
            le_max_right B₀ 0]) (le_of_lt hCBpos))
      have h2 : Work.Spaces.HkSq α 0
          (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
          ≤ CC * (1 + max B₀ 0) ^ 2 :=
        le_trans (hCbd g hg).2 (mul_le_mul_of_nonneg_left
          (by nlinarith [Work.Spaces.HkNorm_nonneg α 6 g, hX,
            le_max_right B₀ 0]) (le_of_lt hCCpos))
      nlinarith [h1, h2]
  -- the key: the memberships of any cluster limit
  have key : ∀ (σ : ℕ → ℕ) (Ψ : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => E (fn (σ n)) z θ) Filter.atTop (𝓝 (Ψ z θ))) →
      Work.FTS_EllLimOK.BoxReg Ψ →
      Work.FTS.StrongGlobal.IsBslSolPos α f Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
        Work.Spaces.HkMem α 0 Ψ ∧
        Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ)
          ≤ 2 * (CB + CC) * (1 + max B₀ 0) ^ 2 := by
    intro σ Ψ hconv hbox hsol
    have hdir : ∀ z ∈ Set.Ioi (0 : ℝ), Ψ z (π / 2) = 0 :=
      fun z hz => hsol.2.2.1 z (le_of_lt hz)
    have hslice := (hE hbox hdir).1
    have hmeas := (hE hbox hdir).2
    have hcomp : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Filter.Tendsto (fun n => E (fn (σ n)) z θ / Real.cos θ) Filter.atTop
          (𝓝 (Ψ z θ / Real.cos θ)) := by
      intro z θ hzθ
      exact ((hconv z θ hzθ).div_const _)
    have hD' := Work.FTS_EllLimOK.PkgJets.hkMemOfJConv (C := 2 * (CB + CC) * (1 + max B₀ 0) ^ 2)
      (un := fun n z θ => E (fn (σ n)) z θ / Real.cos θ)
      (u := fun z θ => Ψ z θ / Real.cos θ)
      (fun n => hmemb (fn (σ n)) (hL.classC (σ n)))
      (fun n => hsqi (fn (σ n)) (hL.classC (σ n)) (hXL (σ n))) hslice hmeas hcomp
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 Ψ p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS_EllLimOK.continuousOn_HkIntegrand_zero α
        hbox.contDiffOn_Qd.continuousOn
    exact ⟨hD'.1, HkMem_zero_of_cosDiv hcont hD'.1, hD'.2⟩
  obtain ⟨σ, Ψ, hσ, hboxΨ, hsolΨ, hconvΨ⟩ := Work.FTS_EllLimOK.PkgJets.clusterExtract hα hα1 hE' hL
  obtain ⟨hHkcΨ, hHkΨ, -⟩ := key σ Ψ hconvΨ hboxΨ hsolΨ
  refine ⟨Ψ, hboxΨ a b ha hab, ?_, ?_⟩
  · -- the full convergence on the box
    intro z hz θ hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · -- the line `θ = 0`: every member vanishes
      subst hθ0
      have hmem : ∀ n : ℕ, E (fn n) z 0 = 0 :=
        fun n => ((hE'.toHasPkgD.toHasPkg (fn n) (hL.classC n)).1).sol.2.1 z
      have hlim : Ψ z 0 = 0 := hsolΨ.2.1 z (le_of_lt (lt_of_lt_of_le ha hz.1))
      rw [hlim, show (fun n : ℕ => E (fn n) z 0) = fun _ => (0 : ℝ) from funext hmem]
      exact tendsto_const_nhds
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθ2
      · -- the line `θ = π/2`
        subst hθ2
        have hmem : ∀ n : ℕ, E (fn n) z (π / 2) = 0 :=
          fun n => ((hE'.toHasPkgD.toHasPkg (fn n) (hL.classC n)).1).sol.2.2.1 z
        have hlim : Ψ z (π / 2) = 0 := hsolΨ.2.2.1 z (le_of_lt (lt_of_lt_of_le ha hz.1))
        rw [hlim, show (fun n : ℕ => E (fn n) z (π / 2)) = fun _ => (0 : ℝ) from funext hmem]
        exact tendsto_const_nhds
      · -- an interior point: every subsequence has a sub-subsequence with the *same* limit
        have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
        have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hzpos, hθ0, hθ2⟩
        refine Filter.tendsto_of_subseq_tendsto ?_
        intro ns hns
        obtain ⟨τ, Φ, hτ, hboxΦ, hsolΦ, hconvΦ⟩ :=
          Work.FTS_EllLimOK.PkgJets.clusterExtract hα hα1 hE' (LimSeq4.subseq hL hns)
        obtain ⟨hHkcΦ, hHkΦ, -⟩ := key (fun n => ns (τ n)) Φ hconvΦ hboxΦ hsolΦ
        have heq : Φ z θ = Ψ z θ :=
          Work.FTS_EllLimOK.eqOn_of_same_law hα hsolΦ hsolΨ hboxΦ hboxΨ hHkΦ hHkcΦ hHkΨ
            hHkcΨ (Work.FTS_EllLimOK.HkMem_zero_diff hHkΦ hHkΨ hboxΦ hboxΨ) z θ hQd
        exact ⟨τ, by simpa only [heq] using hconvΦ z θ hQd⟩
  · -- the Dirichlet data on the box
    intro z hz
    exact ⟨hsolΨ.2.1 z (le_of_lt (lt_of_lt_of_le ha hz.1)),
      hsolΨ.2.2.1 z (le_of_lt (lt_of_lt_of_le ha hz.1))⟩

/- **Alias repairing the constant name used in the requested statement.**  The area's vocabulary
lives in the underscore namespace `Work.FTS_EllLimOK` (`PkgRepair.lean`); the requested statement
below spells the target `Work.FTS.EllLimOK.BoxDataD`, which is not a name in this development
(`FTS_EllLimOK/NOTES.md` §10.4 records exactly this trap).  This definitions-only alias makes the
requested text elaborate to the intended `Prop`. -/
namespace Work.FTS.EllLimOK

/-- Alias of `Work.FTS_EllLimOK.BoxDataD` under the (otherwise unused) dot-namespace. -/
abbrev BoxDataD (α Ce : ℝ) : Prop := _root_.Work.FTS_EllLimOK.BoxDataD α Ce

end Work.FTS.EllLimOK

theorem boxDataD_uniform {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllLimOK.BoxDataD α Ce :=
  boxDataD_of_clusterData hα hα1
    (Work.FTS_EllLimOK.PkgJets.pinningBoundClean hα hα1)
    (Work.FTS_EllLimOK.PkgJets.thetaBound hα hα1)
    (fun hbox hdir => Work.FTS_EllLimOK.PkgJets.slotSliceData (α := α) hbox hdir)

end Work.FTS_EllLimOK.PkgJets
