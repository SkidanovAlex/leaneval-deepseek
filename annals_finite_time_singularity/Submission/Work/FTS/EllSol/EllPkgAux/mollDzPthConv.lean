/-
# `Work.FTS.EllSol.EllPkgAux.mollDzPthConv`

The mixed derivative identity for the doubly-mollified datum

  `Φ := zmoll G δ ε`,   `Φ z θ = ∫ t, sKer δ (log z - t) * (∫ s, sKer ε (θ - s) * Qext G (eᵗ) s)`

of the trace-class interpolation package: both derivatives may be moved onto the two
mollifying kernels,

  `D_z ∂_θ Φ(z,θ) = ∫ t, sKerd δ (log z - t) * (∫ s, sKerd ε (θ - s) * Hxyc G t s)`
  (`z > 0`, `θ ∈ Iθ`).

The proof does **not** differentiate under the integral sign again.  Instead it invokes the
already proved identity

`Work.FTS.ClassC.UopGenAux.MollConvAux.zmollDzPthEq`,

which computes the same quantity as a *two-dimensional convolution* of the uncurried
integrand `Hxy (Gquad G)` (`Gquad` kills `G` outside the open quadrant) against the product
kernel `Kd δ ε`:

  `D_z ∂_θ Φ(z,θ) = ∫ u, ∫ v, sKerd δ u * sKerd ε v * Hxy (Gquad G) (log z - u, θ - v)`.

Two reductions then give the stated *iterated* form.

* **Reflection.**  Both reflections `x ↦ a - x` preserve Lebesgue measure, so the iterated
  integral can be written with the arguments of the datum reflected: this is the elementary
  `integral_reflect_pair_two` below (the two-kernel version of
  `Work.FTS.EllSol.EllPkgAux.integral_reflect_pair`).
* **Cutoff insensitivity.**  The angular kernel `sKerd ε` is supported in `|θ - s| < ε ≤ 1/2`,
  and on that window the doubly-odd extension of `Gquad G` coincides with that of `G`
  (`MollSmooth.Qext_Gquad_eq_Qext`), because the only places where `Gquad G` differs from `G`
  on `(-π/2, π)` are the boundary lines `s = 0`, `s = π/2`, where `TraceClass` supplies the
  value `0`.  So the two integrands agree off the two-point set `{θ - ε, θ + ε}` (on which
  the kernel vanishes anyway), which is what `sKerd_mul_Hxy_Gquad_ae` records.

The local integrability `hloc` needed by `zmollDzPthEq` — and hence the hypothesis `hdom` of
the statement — is obtained from the trace-class hypotheses alone, by dominating the datum on
the quadrant with the locally integrable slice bound `MG G`
(`MollSmooth.sliceDom` + `MollSmooth.MG_integrableOn` + `MollSmooth.Hxy_quad_locallyIntegrable`);
the hypothesis `hdom` itself is therefore not needed and is carried along unused.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.ClassC.UopGenAux.MollConvAux.zmollDzPthEq
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Change of variables in the double convolution, with two different kernels -/

/-- **Change of variables in the double convolution.**  For arbitrary kernels `k₁`, `k₂` and
datum `H`, the iterated integral written with the reflected arguments of `H` equals the
iterated integral of the kernels against `H` at the reflected arguments:

  `∫ t', k₁ (a - t') * (∫ s, k₂ (b - s) * H t' s)
     = ∫ u, ∫ v, k₁ u * k₂ v * H (a - u) (b - v)`.

This is the two-kernel version of `Work.FTS.EllSol.EllPkgAux.integral_reflect_pair`; the proof
is the same and uses only that the reflections `x ↦ a - x`, `x ↦ b - x` preserve Lebesgue
measure (`MeasureTheory.integral_sub_left_eq_self`, which needs no integrability hypothesis)
and that a constant may be pulled out of an integral (`MeasureTheory.integral_const_mul`). -/
private theorem integral_reflect_pair_two (k₁ k₂ : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (a b : ℝ) :
    (∫ t' : ℝ, k₁ (a - t') * (∫ s : ℝ, k₂ (b - s) * H t' s))
      = ∫ u : ℝ, ∫ v : ℝ, k₁ u * k₂ v * H (a - u) (b - v) := by
  have hinner : ∀ t' : ℝ, (∫ s : ℝ, k₂ (b - s) * H t' s)
      = ∫ v : ℝ, k₂ v * H t' (b - v) := by
    intro t'
    simpa using (MeasureTheory.integral_sub_left_eq_self
      (fun v : ℝ => k₂ v * H t' (b - v)) MeasureTheory.volume b)
  have hstep1 : (∫ t' : ℝ, k₁ (a - t') * (∫ s : ℝ, k₂ (b - s) * H t' s))
      = ∫ t' : ℝ, k₁ (a - t') * (∫ v : ℝ, k₂ v * H t' (b - v)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
    simp only [hinner t']
  rw [hstep1]
  have hstep2 : (∫ t' : ℝ, k₁ (a - t') * (∫ v : ℝ, k₂ v * H t' (b - v)))
      = ∫ u : ℝ, k₁ u * (∫ v : ℝ, k₂ v * H (a - u) (b - v)) := by
    simpa using (MeasureTheory.integral_sub_left_eq_self
      (fun u : ℝ => k₁ u * (∫ v : ℝ, k₂ v * H (a - u) (b - v))) MeasureTheory.volume a)
  rw [hstep2]
  have hpt : ∀ u : ℝ, k₁ u * (∫ v : ℝ, k₂ v * H (a - u) (b - v))
      = ∫ v : ℝ, k₁ u * k₂ v * H (a - u) (b - v) := by
    intro u
    rw [← MeasureTheory.integral_const_mul (k₁ u) (fun v : ℝ => k₂ v * H (a - u) (b - v))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    ring
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

/-! ## The quadrant cutoff is invisible to the angular derivative kernel -/

/-- **The angular kernel sees only the open quadrant.**  For `G` vanishing on the two angular
boundary lines and `ε ≤ 1/2`, the two functions

  `s ↦ sKerd ε (θ - s) * Qext (Gquad G) (eᵗ) s`   and   `s ↦ sKerd ε (θ - s) * Qext G (eᵗ) s`

agree almost everywhere: the support condition `|θ - s| < ε ≤ 1/2` forces `s ∈ (-π/2, π)`, on
which `Qext (Gquad G) = Qext G` (`MollSmooth.Qext_Gquad_eq_Qext`), and the only remaining
points are the two where `|θ - s| = ε`, a set of measure zero. -/
private lemma sKerd_mul_Hxy_Gquad_ae (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) {ε θ t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (fun s : ℝ => sKerd ε (θ - s) * Hxy (Gquad G) (t, s))
      =ᵐ[MeasureTheory.volume] (fun s : ℝ => sKerd ε (θ - s) * Hxyc G t s) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({(θ - ε), (θ + ε)} : Set ℝ)) ?_ ?_
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    push_neg at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hne : |θ - s| ≠ ε := by
      intro heq
      rcases eq_or_eq_neg_of_abs_eq heq with h | h
      · exact hne1 (by linarith)
      · exact hne2 (by linarith)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- the strict window: `Qext` is insensitive to the cutoff here
      have hlt' := abs_lt.mp hlt
      have hθ0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
      have hθπ : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
      have hmem : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi :=
        ⟨by linarith [hlt'.1, hθ0, hε1, Real.pi_gt_three],
         by linarith [hlt'.2, hθπ, hε1, Real.pi_gt_three]⟩
      refine hs ?_
      simp only [Hxy, Hxyc]
      rw [MollSmooth.Qext_Gquad_eq_Qext G h0 hπ (Real.exp t) s hmem]
    · -- outside the window the kernel vanishes
      refine hs ?_
      simp only [Hxy, Hxyc]
      rw [MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hgt]
      ring
  · exact Set.Finite.measure_zero (Set.Finite.insert _ (Set.finite_singleton _)) _

/-! ## The mixed derivative identity -/

theorem mollDzPthConv (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume) (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s) := by
  intro z hz θ hθIθ
  obtain ⟨hS, h0, hπ, -, -, -, -, hH⟩ := hT
  -- `θ ∈ Iθ = [0, π/2]` lies inside the window of `zmollDzPthEq`
  have hθ' : θ ∈ Set.Ioo (-(1 : ℝ) / 2) (Real.pi / 2 + 1 / 2) :=
    ⟨by linarith [(Set.mem_Icc.mp hθIθ).1],
     by linarith [(Set.mem_Icc.mp hθIθ).2]⟩
  -- local integrability of the uncurried integrand of the quadrant-killed datum
  have hloc : MeasureTheory.LocallyIntegrable (Hxy (Gquad G)) MeasureTheory.volume :=
    MollSmooth.Hxy_quad_locallyIntegrable G hS
      (MollSmooth.sliceDom G hS hH) (MollSmooth.MG_integrableOn G hS hF)
  -- the already proved identity, in its two-dimensional-convolution form
  rw [Work.FTS.ClassC.UopGenAux.MollConvAux.zmollDzPthEq G hloc h0 hπ δ ε hδ0 hε0 hε1 z hz θ hθ']
  -- reflect the arguments of the datum, and factor the outer kernel out of the inner integral
  refine (integral_reflect_pair_two (sKerd δ) (sKerd ε)
    (fun t s => Hxy (Gquad G) (t, s)) (Real.log z) θ).symm.trans ?_
  -- replace the quadrant-killed datum by `G` itself (a.e. in the angular variable)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
  have hinner : (∫ s : ℝ, sKerd ε (θ - s) * Hxy (Gquad G) (t', s))
      = ∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t' s :=
    MeasureTheory.integral_congr_ae (sKerd_mul_Hxy_Gquad_ae G h0 hπ hε0 hε1 hθIθ)
  dsimp only
  rw [hinner]

end Work.FTS.EllSol.EllPkgAux
