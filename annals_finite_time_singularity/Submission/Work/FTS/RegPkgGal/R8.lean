/-
# `Work.FTS.RegPkgGal.R8` — `hH4` of the extension (design §4, R8)

R8 of `FTS_PHYS_BRIDGE.md` §4 is "immediate from `mem4`": the extension `g̃ = extG g` differs from
`g` only on `{z ≤ 0} ∪ {τ < 0}`, and the `ℋ⁴`-integrand of a slice carries the factor
`w(z) = (1+z)²/z²`, which vanishes at `z = 0`; so at every `τ ≥ 0` the `ℋ⁴`-integrand of the
`g̃`-slice agrees with that of the `g`-slice pointwise on `Iz × Iθ`.  Hence
`RegPkgMin.mem4` transfers verbatim.

The proof needs the derived operators (`DzIter`, `mixed`) to agree, which is a congruence on the
*open* set `Ioi 0` (where the two slices do agree); the two private lemmas below are the generic
version of `Work.Spaces.DzIter_congr` for an arbitrary open set.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Congruence of the derived operators on an open set -/

private lemma pz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry f (z', θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry f' (z', θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pz, Function.uncurry] using this

private lemma pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry f (z, θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry f' (z, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pth, Function.uncurry] using this

/-- Congruence of `DzIter` on an open set. -/
lemma DzIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j f')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro y hy
      have hp := pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j f') y.1 y.2
      rw [hp]

/-- Congruence of `mixed` on an open set. -/
lemma mixed_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i f')) V := by
  have hth : EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i f')) V := by
    induction i with
    | zero => exact h
    | succ i ih =>
        intro y hy
        have hp := pth_congr_of_isOpen hV ih hy
        show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i f') y.1 y.2
        rw [hp]
  exact DzIter_congr_of_isOpen hV hth j

/-! ## R8: the `ℋ⁴`-membership of the extended slice -/

/-- On `Iz ×ˢ univ` the `ℋ⁴`-integrand of the extended slice agrees with that of the original
slice, at every `τ ≥ 0`.  For `z > 0` this is the congruence of the derived operators on the open
set `Ioi 0`; at `z = 0` both integrands vanish because of the factor `w 0 = 0`. -/
lemma HkIntegrand_extG_eq {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 ≤ z) :
    Work.Spaces.HkIntegrand (pExp α) 4 (fun z θ => extG g z θ τ) z θ
      = Work.Spaces.HkIntegrand (pExp α) 4 (fun z θ => g z θ τ) z θ := by
  by_cases hz0 : z = 0
  · subst hz0
    have hw : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
    simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, hw]
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hagree : EqOn (Function.uncurry (fun z θ => extG g z θ τ))
        (Function.uncurry (fun z θ => g z θ τ)) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
      rintro ⟨z', θ'⟩ ⟨hz', -⟩
      simp only [Function.uncurry]
      exact extG_of_pos hz' hτ
    have hmem : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hzpos, trivial⟩
    simp only [Work.Spaces.HkIntegrand]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      have h := DzIter_congr_of_isOpen hV hagree i hmem
      simp only [Function.uncurry] at h
      rw [h]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hij : 1 ≤ i ∧ i + j ≤ 4
      · simp only [hij]
        have h := mixed_congr_of_isOpen hV hagree j i hmem
        simp only [Function.uncurry] at h
        rw [h]
      · simp only [hij, ite_false]

/-- **R8.** The `ℋ⁴`-membership of the extended slice, for every `τ` in the strip: this is
`RegPkgMin.mem4` transported along `HkIntegrand_extG_eq`. -/
theorem mem4_extG {α : ℝ} {S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hmin : RegPkgMin (pExp α) g) :
    ∀ τ ∈ Set.Icc 0 S, Work.Spaces.HkMem (pExp α) 4 (fun z θ => extG g z θ τ) := by
  intro τ hτ
  obtain ⟨h1, h2⟩ := hmin.mem4 τ hτ.1
  refine ⟨fun z hz => ?_, ?_⟩
  · refine IntegrableOn.congr_fun (h1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_extG_eq (α := α) (g := g) (τ := τ) hτ.1 (z := z) (θ := θ) hz).symm
  · refine IntegrableOn.congr_fun h2 (fun z hz => ?_) measurableSet_Ici
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun θ => (HkIntegrand_extG_eq (α := α) (g := g) (τ := τ) hτ.1 (z := z) (θ := θ) hz).symm))

end Work.FTS.RegPkgGal
