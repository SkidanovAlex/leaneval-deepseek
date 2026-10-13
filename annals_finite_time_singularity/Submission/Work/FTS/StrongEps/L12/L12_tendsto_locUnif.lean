/-
# `L12_tendsto_locUnif`: local uniform convergence of the datum gives convergence of `L₁₂`

`Work.FTS.StrongEps.L12.L12_tendsto_locUnif`: if `f n → g` uniformly on every compact subset of the
open quadrant `Q0`, the data are of class `HQo α 4 = SmoothOpen ∧ HkMem α 4` and the `ℋ⁴`-sizes are
uniformly bounded by `B`, then for every `z ≥ 0` the `L₁₂`-functionals converge:
`L₁₂ (f n) z → L₁₂ g z`.

## Route

* `L₁₂(f n) z − L₁₂ g z = L₁₂ (f n − g) z` on `Iz` (`EComparison.L12_sub_HkMem`), so it suffices to
  show `L₁₂ (D n) z → 0` for `D n = f n − g`.
* `D n` is `ℋ⁰` with `HkSq α 0 (D n) ≤ 4B²` (`HkMemZeroSub`: `HkIntegrand α 0 h = (Gaz h)²` and
  `(Gaz a − Gaz b)² ≤ 2(Gaz a² + Gaz b²) ≤ 2(HkIntegrand α 4 a + HkIntegrand α 4 b)`).
* The local uniform convergence of `f n` to `g` gives, on every box `[δ,R] × [ε,π/2−ε]`
  (compact in `Q0`), the uniform smallness of the weighted datum `Gaz (D n)`: the weight
  `w s / Sw θ` is bounded on the box by `w δ / Sw ε` (`WSwBound`).
* `LocUnifTendsto.L12_tendsto_zero_of_GazBox` then produces the limit `0` for every `z ≥ 0`.

`LocUnifAux`, `LocUnifMaster` and `LocUnifTendsto` carry the auxiliary estimates, the master bound
and the `ε`-argument; the delegated lemmas are `DensSplit`, `WlamCS`, `WlamSqIoo`, `WlamSqIoi`,
`EndsBound`, `HkMemZeroSub` and `WSwBound`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.L12.LocUnifTendsto
import Submission.Work.FTS.StrongEps.L12.HkMemZeroSub
import Submission.Work.FTS.StrongEps.L12.WSwBound
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem L12_tendsto_locUnif : ∀ (α : ℝ), 0 < α → ∀ (f : ℕ → Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fn) (B : ℝ),
    (∀ n, Work.FTS.VocabO.HQo α 4 (f n)) → (∀ n, Work.FTS.Nonlin.Xn α (f n) ≤ B) →
    Work.FTS.VocabO.HQo α 4 g → Work.FTS.Nonlin.Xn α g ≤ B →
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n zθ => f n zθ.1 zθ.2) (fun zθ => g zθ.1 zθ.2) Filter.atTop K) →
    ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun n => Work.Construction.L12 (f n) z) Filter.atTop
        (nhds (Work.Construction.L12 g z)) := by
  intro α hα f g B hf hBf hg hBg hconv z hz
  have hB0 : 0 ≤ B :=
    le_trans (by simp only [Work.Spaces.HkNorm]; exact Real.sqrt_nonneg _) hBg
  set D : ℕ → ℝ → ℝ → ℝ := fun n z θ => f n z θ - g z θ with hD
  have hDmem : ∀ n, Work.Spaces.HkMem α 0 (D n) :=
    fun n => (HkMemZeroSub (hf n).1 hg.1 (hf n).2 hg.2).1
  have hDbd : ∀ n, Work.Spaces.HkSq α 0 (D n) ≤ 4 * B ^ 2 := by
    intro n
    have h1 := (HkMemZeroSub (hf n).1 hg.1 (hf n).2 hg.2).2
    have hsq : ∀ x : ℝ → ℝ → ℝ, Work.FTS.Nonlin.Xn α x ≤ B →
        Work.Spaces.HkSq α 4 x ≤ B ^ 2 := by
      intro x hx
      have hnn : 0 ≤ Work.Spaces.HkNorm α 4 x := by
        simp only [Work.Spaces.HkNorm]
        exact Real.sqrt_nonneg _
      have hsqnn : 0 ≤ Work.Spaces.HkSq α 4 x := by
        rw [Work.Spaces.HkSq]
        exact integral_nonneg fun s =>
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 x s θ
      have h2 : Work.Spaces.HkNorm α 4 x ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hnn hx 2
      rwa [show Work.Spaces.HkNorm α 4 x = Real.sqrt (Work.Spaces.HkSq α 4 x) from rfl,
        Real.sq_sqrt hsqnn] at h2
    have h2 := hsq (f n) (hBf n)
    have h3 := hsq g hBg
    linarith
  have hGazBox : ∀ δ R ε : ℝ, 0 < δ → δ ≤ R → 0 < ε → ε ≤ Real.pi / 4 → ∀ η > 0,
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Set.Icc δ R, ∀ θ ∈ Set.Icc ε (Real.pi / 2 - ε),
        |Work.FTS.GalBasis.cc.Gaz (D n) s θ| ≤ η := by
    intro δ R ε hδ hδR hε hε4 η hη
    have hsub : Set.Icc δ R ×ˢ Set.Icc ε (Real.pi / 2 - ε) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have hp1 : p.1 ∈ Set.Icc δ R := hp.1
      have hp2 : p.2 ∈ Set.Icc ε (Real.pi / 2 - ε) := hp.2
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨lt_of_lt_of_le hδ hp1.1, lt_of_lt_of_le hε hp2.1,
        by linarith [hp2.2, Real.pi_pos]⟩
    have hcomp : IsCompact (Set.Icc δ R ×ˢ Set.Icc ε (Real.pi / 2 - ε)) :=
      isCompact_Icc.prod isCompact_Icc
    have hunif := hconv _ hcomp hsub
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    set cw : ℝ := Work.Spaces.w δ / Work.FTS.GalBasis.cc.Sw ε with hcw
    have hcwpos : 0 < cw := by
      rw [hcw]
      refine div_pos ?_ (Work.FTS.GalBasis.cc.Sw_pos_of_mem_Ioo hε
        (by linarith [hε4, Real.pi_pos]))
      rw [Work.Spaces.w]
      positivity
    have hcw0 : 0 ≤ cw := le_of_lt hcwpos
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp (hunif (η / (cw + 1)) (div_pos hη (by linarith)))
    refine ⟨N, fun n hn s hs θ hθ => ?_⟩
    have h1 : |D n s θ| ≤ η / (cw + 1) := by
      have h := hN n hn (s, θ) ⟨hs, hθ⟩
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact h.le
    have h2 : Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ ≤ cw := by
      rw [hcw]
      exact WSwBound δ ε hδ hε hε4 s θ hs.1 hθ.1 hθ.2
    have h2nn : 0 ≤ Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ := by
      refine div_nonneg ?_ ?_
      · rw [Work.Spaces.w]
        positivity
      · exact le_of_lt (Work.FTS.GalBasis.cc.Sw_pos_of_mem_Ioo (lt_of_lt_of_le hε hθ.1)
          (by linarith [hθ.2, Real.pi_pos]))
    show |Work.FTS.GalBasis.cc.Gaz (D n) s θ| ≤ η
    rw [Work.FTS.GalBasis.cc.Gaz, abs_mul, abs_of_nonneg h2nn]
    calc |D n s θ| * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ)
        ≤ (η / (cw + 1)) * cw := mul_le_mul h1 h2 h2nn (by positivity)
      _ ≤ η := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [hcw0, hη]
  have hkey := L12_tendsto_zero_of_GazBox (α := α) (D := D) (C := 4 * B ^ 2)
    hDmem hDbd (by positivity) hGazBox hz
  have heq : ∀ n, Work.Construction.L12 (D n) z
      = Work.Construction.L12 (f n) z - Work.Construction.L12 g z := by
    intro n
    exact Work.FTS.StrongEps.EComparison.L12_sub_HkMem (hf n).1 hg.1 (hf n).2 hg.2 z (by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact hz)
  have h2 : Filter.Tendsto (fun n => Work.Construction.L12 (D n) z + Work.Construction.L12 g z)
      Filter.atTop (nhds (0 + Work.Construction.L12 g z)) := hkey.add_const _
  have h3 : (fun n => Work.Construction.L12 (D n) z + Work.Construction.L12 g z)
      = fun n => Work.Construction.L12 (f n) z := by
    funext n
    rw [heq n]
    ring
  rw [h3] at h2
  simpa using h2

end Work.FTS.StrongEps.L12
