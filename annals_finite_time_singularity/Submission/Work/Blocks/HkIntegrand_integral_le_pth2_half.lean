import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Blocks.SmoothHalfAux
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.HkIntegrand_le_slice_sum
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.Blocks.slice_data_integrable_of_HkIntegrand
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
**The per-`z` angular Poincaré comparison `f` vs `∂_θ²f` in the half-strip class.**

This is the port of the *already proved* `Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2`
(`Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_integral_le_pth2.lean`, sorry-free) from the
hypothesis `Work.Spaces.SmoothNbhd f` to the weaker, provable hypothesis
`Work.FTS.EllipticEst.SmoothHalf f` (see `Submission/Work/FTS/EllipticEst/HalfSmooth.lean`).

WHY it is needed: `SmoothNbhd` (`C^∞` on a 2D neighbourhood of the closed quadrant, hence on
`z < 0`) is FALSE for the straightened residual `Ξ = EllResid α F Ψ`, while `SmoothHalf Ξ` holds.

ROUTE: copy the proof of the original file and replace the hypothesis `SmoothNbhd f` by
`SmoothHalf f`, using the half-strip layer `Submission/Work/Blocks/SmoothHalfAux.lean`
(namespace `Work.FTS.EllipticEst.HalfU`, all sorry-free).  In the original proof everything after
the split `rcases eq_or_lt_of_le hz0 with hzeq | hzpos` runs in the branch `0 < z`, exactly the
regime in which the half-strip layer applies; `hsm.halfAn : HalfU.HalfAn f` is the second
conjunct of `SmoothHalf` (`ContDiffOn ℝ ⊤ (Function.uncurry f) (Ioi 0 ×ˢ Ioo (-1) (π/2+1))`).
Dictionary of replacements:

* `SmoothNbhd.DzIter hsm j` + `sliceSmooth_of_SmoothNbhd … hz` ↦ `HalfU.HalfAn.slice_DzIter hsm.halfAn j hzpos`;
* `sliceV_DzIter hsm j hz hθ` ↦ `HalfU.sliceV_DzIter hsm.halfAn j hzpos hθ`;
* `LopIter_sliceV_DzIter_eq_mixed hsm j m hz hθ` ↦ `HalfU.LopIter_sliceV_DzIter_eq_mixed hsm.halfAn j m hzpos hθ`;
* the private `mixed_eq_LopIter` (built from `DthIter_DzIter`) ↦ `HalfU.LopIter_DzIter_eq_mixed hsm.halfAn j i hzpos hθ`;
* `integrableOn_HkIntegrand_terms α k (pthIter 2 f) (hsm.pth.pth) hz …` ↦
  `HalfU.integrableOn_HkIntegrand_terms_half α k (pthIter 2 f) (hsm.halfAn.pthIter 2) hzpos …`;
* `Blocks.slice_data_integrable_of_HkIntegrand α k f hsm hzpos j hj …` ↦
  `HalfU.slice_data_integrable_of_HkIntegrand_half α k f hsm.halfAn hzpos j hj …`.

Everything else (`DzIter_boundary_zero hvan j`, `HkIntegrand_eq_slice_sum`, `sliceGroup`, `sliceA`,
`slicePhi`, `Sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed`, `integral_mono_of_nonneg`, the
`Sfun`/`Bdom` helpers and the arithmetic) is unchanged, and so is the `hC1` hypothesis verbatim:
the angular slices of `DzIter j f` at a level `z > 0` ARE `SliceSmooth` because `SmoothHalf`'s
second conjunct is smoothness on the half-strip `(0,∞) × (-1, π/2+1)`.
-/
/-! ## Auxiliary vocabulary for the proof

`Sfun` is the sum of the three fixed integrable angular weights produced by the boundary
conditions in `slicePhi`; `Bdom` is the dominating function by which a single angular
integrand (at a fixed radial level `z`, with a fixed value `M` of the `H^k`-integral of
`∂_θ² f`) is bounded. -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
private def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)

/-- `sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}` is nonnegative on `Iθ`. -/
private lemma Sfun_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Sfun α θ := by
  rw [Sfun]
  exact add_nonneg (add_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
    (Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _))
    (Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _)

private lemma gam_le_two {α : ℝ} (hα : α ≤ 1) : 0 ≤ 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

private lemma gam_le_four {α : ℝ} (hα : α ≤ 1) : 0 ≤ 4 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

private lemma integrableOn_Sfun {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (Sfun α) Work.Spaces.Iθ := by
  have h1 := Work.FTS.EllipticEst.integrableOn_thEta.1
  have h2 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_two hα1)).1
  have h3 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_four hα1)).1
  unfold Sfun
  exact (h1.add h2).add h3

private lemma integral_Sfun_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ 10000 + Real.pi := by
  have h1 := Work.FTS.EllipticEst.integrableOn_thEta
  have h2 := Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_two hα1)
  have h3 := Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_four hα1)
  have h12 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ := h1.1.add h2.1
  unfold Sfun
  rw [MeasureTheory.integral_add (f := fun θ =>
        Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (g := fun θ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) h12 h3.1,
    MeasureTheory.integral_add (f := Work.FTS.EllipticEst.thEta)
      (g := fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) h1.1 h2.1]
  linarith [h1.2, h2.2, h3.2, Real.pi_pos]

/-- The angular weight `(u * w(z)/sin(2θ)^{η/2})²` is `w(z)²` times the `η`-weighted
square of `u`. -/
private lemma rad_term_eq_aux {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z u : ℝ) :
    (u * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (u ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθ z]
  ring

/-- The angular weight `(v * Wt α z θ)²` is `w(z)²` times the `γ`-weighted square of `v`. -/
private lemma mix_term_eq_aux {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (α z v : ℝ) :
    (v * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (v ^ 2 * Work.FTS.EllipticEst.thGam α θ) := by
  rw [mul_pow, Work.FTS.EllipticEst.Wt_sq hθ α z]
  ring

/-- The dominating function of the per-`z` estimate: the sum over the radial slices
`0 ≤ j ≤ k` of the `(k-j+1)`-fold multiple of `(max C1 0)` times the `j`-th slice group of
`∂_θ² f` together with the boundary weight `M · Sfun α`. -/
private def Bdom (α : ℝ) (k : ℕ) (C1 M : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (((k - j : ℕ) : ℝ) + 1) *
    (max C1 0 * (Work.FTS.EllipticEst.sliceGroup α k j f z θ + M * Sfun α θ))

/-- **Per-`z` comparison of the angular integrals (the `∂_θ²`-part of the angular Poincaré
estimate).**  `hC1` is the slice estimate `Blocks.slice_f_bound`, *uniformly in the level*
`K ≤ k` and with the constant `C1` passed as a parameter (so this file need not import that
module).  From it one deduces that for every `z` in the quadrant the angular integral of the
`H^k`-integrand of `f` is bounded by a universal constant times the angular integral of the
`H^k`-integrand of `∂_θ² f`:

`∫_{Iθ} HkIntegrand α k f z θ ≤ C · ∫_{Iθ} HkIntegrand α k (∂_θ² f) z θ`.

PLACEMENT.  The file `Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_integral_le_pth2.lean`
must declare this in namespace `Work.FTS.EllipticEst.Blocks` (write
`namespace Work.FTS.EllipticEst.Blocks` before the statement and `end Work.FTS.EllipticEst.Blocks`
after it), so that the fully qualified name is
`Work.FTS.EllipticEst.Blocks.HkIntegrand_integral_le_pth2`.  A declaration with this statement
already exists in the `sorry`-containing sibling
`Submission/Work/FTS/EllipticEst/HkIntegrand_integral_le_pth2.lean`: do NOT import it; its proof
(with the same route) is there to be read and reused.  The `hC1` that `theta_poincare_Hk.lean`
builds from `Blocks.slice_f_bound` is exactly the hypothesis here.

ROUTE (fixed `z`; `u_j(θ) = D_z^j f z θ`, `v_j = u_j'' = D_z^j (∂_θ² f) z θ`):
* `HkIntegrand_le_slice_sum` bounds the left integrand by `∑_{j ≤ k}` of the `j`-th group
  `(u_j·w/s^{η/2})² + ∑_{1≤i≤k-j}(mixed j i f·Wt)²`; rewrite `mixed j i f z θ` as `LopIter i u_j θ`
  and the weights as `w z²·thEta θ`, `w z²·thGam α θ`;
* for each `j ≤ k` apply `hC1` with level `K = k - j` to `u_j` (slice smoothness, boundary
  vanishing and the two integrability hypotheses come from `sliceSmooth_of_SmoothNbhd`,
  the boundary vanishing of the `D_z`-iterates and `integrableOn_HkIntegrand_terms` applied to
  `∂_θ² f`: for `1 ≤ m ≤ k-j` one has `m + j ≤ k`, so `(LopIter m v_j θ)² thGam α θ` is
  `w z^{-2}·(mixed j m (∂_θ² f) z θ · Wt)²`, a summand of the right-hand integrand; the factor
  `w z^{-2}` is legitimate because at `z = 0` both sides vanish);
* multiply by `w z² ≥ 0`, integrate over `Iθ` (`integral_mono_of_nonneg`; the dominating
  function is integrable) and bound `∫_{Iθ} slicePhi α (k-j) u_j θ` by a universal multiple of
  `w z^{-2}·∫_{Iθ} HkIntegrand α k (∂_θ² f) z θ` (data groups are summands of the right
  integrand; the third group is `sliceA u_j·(∫thEta + ∫sin^{2-γ} + ∫sin^{4-γ})`, and
  `sliceA u_j` is a summand of the right-hand integrand up to `w z^{-2}`);
* sum over the `k+1` values of `j`. -/
theorem HkIntegrand_integral_le_pth2_half (k : ℕ) (C1 : ℝ)
    (hC1 : ∀ (K : ℕ), K ≤ k → ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SliceSmooth u → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ,
          (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ C1 * Work.FTS.EllipticEst.slicePhi α K u θ) ∧
        (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
            ≤ C1 * Work.FTS.EllipticEst.slicePhi α K u θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothHalf f → Work.Spaces.VanishTheta f →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)  := by
  classical
  refine ⟨((k : ℝ) + 1) ^ 2 * max C1 0 * ((k : ℝ) + 10001 + Real.pi) + 1, ?_, ?_⟩
  · positivity
  · intro α f hα0 hα1 hsm hvan hInt z hz
    have hz0 : 0 ≤ z := hz
    rcases eq_or_lt_of_le hz0 with hzeq | hzpos
    · rw [← hzeq]
      simp [Work.FTS.EllipticEst.HkIntegrand_zero_left]
    · -- from now on `0 < z`
      have hAn : Work.FTS.EllipticEst.HalfU.HalfAn f :=
        Work.FTS.EllipticEst.SmoothHalf.halfAn hsm
      set M : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ
        with hM
      have hM0 : 0 ≤ M := by
        rw [hM]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) z θ)
      have hsm2 : Work.FTS.EllipticEst.HalfU.HalfAn (Work.Spaces.pthIter 2 f) :=
        hAn.pthIter 2
      have hterms := Work.FTS.EllipticEst.HalfU.integrableOn_HkIntegrand_terms_half α k
        (Work.Spaces.pthIter 2 f) hsm2 hzpos (hInt z hz)
      have hSint : MeasureTheory.IntegrableOn (Sfun α) Work.Spaces.Iθ :=
        integrableOn_Sfun hα0 hα1
      have hSle : (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ 10000 + Real.pi :=
        integral_Sfun_le hα0 hα1
      -- integrability of the individual summands of the right-hand integrand
      have hterm_rad : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn (fun θ' =>
          (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ'
            * (Work.Spaces.w z / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2))) ^ 2)
          Work.Spaces.Iθ := fun j hj => hterms.1 j hj
      have hterm_mix : ∀ j m : ℕ, 1 ≤ m → m + j ≤ k → MeasureTheory.IntegrableOn (fun θ' =>
          (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ' * Work.Spaces.Wt α z θ') ^ 2)
          Work.Spaces.Iθ := fun j m hm hmj => hterms.2 m j hm hmj
      -- integrability of the slice groups of `∂_θ² f`
      have hintG : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
          (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z) Work.Spaces.Iθ := by
        intro j hjle
        have hmix : MeasureTheory.IntegrableOn (fun θ' => ∑ m ∈ Finset.Icc 1 (k - j),
            (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ' * Work.Spaces.Wt α z θ') ^ 2)
            Work.Spaces.Iθ :=
          MeasureTheory.integrable_finsetSum _ (fun m hm =>
            hterm_mix j m (Finset.mem_Icc.mp hm).1
              (by have h2 := (Finset.mem_Icc.mp hm).2; omega))
        unfold Work.FTS.EllipticEst.sliceGroup
        exact (hterm_rad j hjle).add hmix
      -- the two integrability hypotheses required by `hC1` for the slice `u_j`
      have hslice : ∀ j : ℕ, j ≤ k →
          Work.FTS.EllipticEst.SliceSmooth (fun θ' => Work.Spaces.DzIter j f z θ') ∧
          (fun θ' => Work.Spaces.DzIter j f z θ') 0 = 0 ∧
          (fun θ' => Work.Spaces.DzIter j f z θ') (Real.pi / 2) = 0 ∧
          MeasureTheory.IntegrableOn (fun θ' =>
            (Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') ^ 2
              * Work.FTS.EllipticEst.thEta θ') Work.Spaces.Iθ ∧
          (∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ' =>
            (Work.FTS.EllipticEst.LopIter m
                (Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'')) θ') ^ 2
              * Work.FTS.EllipticEst.thGam α θ') Work.Spaces.Iθ) := by
        intro j hj
        have hz1 : (-1 : ℝ) < z := by linarith
        have hbnd := Work.FTS.EllipticEst.DzIter_boundary_zero hvan j
        refine ⟨Work.FTS.EllipticEst.HalfU.HalfAn.slice_DzIter hAn j hzpos, hbnd.1 z hz1, hbnd.2 z hz1, ?_, ?_⟩
        · have hb := (Work.FTS.EllipticEst.HalfU.slice_data_integrable_of_HkIntegrand_half α k f hAn hzpos j hj (hInt z hz)).1
          refine hb.congr_fun (fun θ' hθ' => ?_) measurableSet_Icc
          rw [Work.FTS.EllipticEst.HalfU.sliceV_DzIter hAn j hzpos hθ']
        · intro m hm
          have hb := (Work.FTS.EllipticEst.HalfU.slice_data_integrable_of_HkIntegrand_half α k f hAn hzpos j hj (hInt z hz)).2 m hm
          refine hb.congr_fun (fun θ' hθ' => ?_) measurableSet_Icc
          rw [Work.FTS.EllipticEst.HalfU.LopIter_sliceV_DzIter_eq_mixed hAn j m hzpos hθ']
      -- the pointwise comparison of the slice groups
      have hgroup : ∀ j ∈ Finset.range (k + 1), ∀ θ ∈ Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α k j (f) z θ
            ≤ (((k - j : ℕ) : ℝ) + 1)
              * (max C1 0 * (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)) := by
        intro j hj θ hθ
        have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        set Y : ℝ := max C1 0 * (Work.FTS.EllipticEst.sliceGroup α k j
            (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ) with hY
        obtain ⟨hC1a, hC1b⟩ := hC1 (k - j) (Nat.sub_le k j) α
          (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
          (hslice j hjle).1 (hslice j hjle).2.1 (hslice j hjle).2.2.1
          (hslice j hjle).2.2.2.1 (hslice j hjle).2.2.2.2
        have hsliceA_nn : 0 ≤ Work.FTS.EllipticEst.sliceA
            (fun θ' => Work.Spaces.DzIter j f z θ') := by
          rw [Work.FTS.EllipticEst.sliceA]
          exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ' hθ' =>
            mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ'))
        have hPhi_nn : 0 ≤ Work.FTS.EllipticEst.slicePhi α (k - j)
            (fun θ' => Work.Spaces.DzIter j f z θ') θ := by
          rw [Work.FTS.EllipticEst.slicePhi]
          refine add_nonneg (add_nonneg
            (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)) ?_) ?_
          · exact Finset.sum_nonneg (fun m _ =>
              mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
          · exact mul_nonneg hsliceA_nn (Sfun_nonneg hθ)
        -- the second-derivative slices are `≤ w(z)^{-2} M`
        have hA : (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sliceA
            (fun θ' => Work.Spaces.DzIter j f z θ') ≤ M := by
          rw [Work.FTS.EllipticEst.sliceA, hM, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg ?_ (hInt z hz) ?_
          · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' =>
              mul_nonneg (sq_nonneg _)
                (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ')))
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' => ?_)
            dsimp only
            rw [Work.FTS.EllipticEst.HalfU.sliceV_DzIter hAn j hzpos hθ',
              ← rad_term_eq_aux hθ' z (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ')]
            exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ' j hjle
        -- `slicePhi` of the slice is dominated by the slice group of `∂_θ² f`
        have hY' : (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
            (fun θ' => Work.Spaces.DzIter j f z θ') θ
            ≤ Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
              + M * Sfun α θ := by
          rw [Work.FTS.EllipticEst.slicePhi, Work.FTS.EllipticEst.sliceGroup]
          calc (Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ
                  + (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                        * Work.FTS.EllipticEst.thGam α θ)
                  + Work.FTS.EllipticEst.sliceA (fun θ' => Work.Spaces.DzIter j f z θ') * Sfun α θ)
              = (Work.Spaces.w z) ^ 2
                  * ((Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                      * Work.FTS.EllipticEst.thEta θ)
                + (Work.Spaces.w z) ^ 2 * (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                        * Work.FTS.EllipticEst.thGam α θ)
                + (Work.Spaces.w z) ^ 2
                    * (Work.FTS.EllipticEst.sliceA (fun θ' => Work.Spaces.DzIter j f z θ')
                        * Sfun α θ) := by ring
            _ ≤ (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
                + (∑ m ∈ Finset.Icc 1 (k - j),
                      (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                        * Work.Spaces.Wt α z θ) ^ 2)
                + M * Sfun α θ := by
                  refine add_le_add (add_le_add ?_ ?_) ?_
                  · refine le_of_eq ?_
                    rw [Work.FTS.EllipticEst.HalfU.sliceV_DzIter hAn j hzpos hθ,
                      ← rad_term_eq_aux hθ z (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ)]
                  · rw [Finset.mul_sum]
                    refine Finset.sum_le_sum (fun m _ => le_of_eq ?_)
                    rw [← mix_term_eq_aux hθ α z (Work.FTS.EllipticEst.LopIter m
                          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ),
                      Work.FTS.EllipticEst.HalfU.LopIter_sliceV_DzIter_eq_mixed hAn j m hzpos hθ]
                  · rw [show (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sliceA
                          (fun θ' => Work.Spaces.DzIter j f z θ') * Sfun α θ)
                        = ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sliceA
                            (fun θ' => Work.Spaces.DzIter j f z θ')) * Sfun α θ from by ring]
                    exact mul_le_mul_of_nonneg_right hA (Sfun_nonneg hθ)
            _ = Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                + M * Sfun α θ := by
                  rw [Work.FTS.EllipticEst.sliceGroup]
        -- the pure `D_z` summand of the group of `∂_θ f`
        have hrad_le : (Work.Spaces.DzIter j (f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ Y := by
          rw [rad_term_eq_aux hθ z (Work.Spaces.DzIter j (f) z θ)]
          calc (Work.Spaces.w z) ^ 2
                * (((fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ)
              ≤ (Work.Spaces.w z) ^ 2 * (C1 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left (hC1a θ hθ) (sq_nonneg _)
            _ ≤ (Work.Spaces.w z) ^ 2 * (max C1 0 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (le_max_left C1 0) hPhi_nn) (sq_nonneg _)
            _ = max C1 0 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) := by ring
            _ ≤ Y := by
                rw [hY]
                exact mul_le_mul_of_nonneg_left hY' (le_max_right C1 0)
        -- the mixed summands of the group of `∂_θ f`
        have hmix_le : ∀ i ∈ Finset.Icc 1 (k - j),
            (Work.Spaces.mixed j i (f) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ Y := by
          intro i hi
          have h1 := hC1b i hi θ hθ
          have e0 : (Work.Spaces.mixed j i (f) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ
              = (Work.FTS.EllipticEst.LopIter i
                    ((fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ := by
            rw [← Work.FTS.EllipticEst.HalfU.LopIter_DzIter_eq_mixed hAn j i hzpos hθ]
          rw [mix_term_eq_aux hθ α z (Work.Spaces.mixed j i (f) z θ), e0]
          calc (Work.Spaces.w z) ^ 2
                * ((Work.FTS.EllipticEst.LopIter i
                      ((fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
                    * Work.FTS.EllipticEst.thGam α θ)
              ≤ (Work.Spaces.w z) ^ 2 * (C1 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
            _ ≤ (Work.Spaces.w z) ^ 2 * (max C1 0 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (le_max_left C1 0) hPhi_nn) (sq_nonneg _)
            _ = max C1 0 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.slicePhi α (k - j)
                    (fun θ' => Work.Spaces.DzIter j f z θ') θ) := by ring
            _ ≤ Y := by
                rw [hY]
                exact mul_le_mul_of_nonneg_left hY' (le_max_right C1 0)
        have hdecomp : Work.FTS.EllipticEst.sliceGroup α k j (f) z θ
            = (Work.Spaces.DzIter j (f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (f) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Work.FTS.EllipticEst.sliceGroup]
        rw [hdecomp]
        have hsum : (∑ i ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j i (f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k - j : ℕ) : ℝ)) * Y := by
          calc (∑ i ∈ Finset.Icc 1 (k - j),
                (Work.Spaces.mixed j i (f) z θ * Work.Spaces.Wt α z θ) ^ 2)
              ≤ ∑ i ∈ Finset.Icc 1 (k - j), Y := Finset.sum_le_sum (fun i hi => hmix_le i hi)
            _ = (Finset.Icc 1 (k - j)).card • Y := Finset.sum_const Y
            _ = (((k - j : ℕ) : ℝ)) * Y := by rw [Nat.card_Icc, nsmul_eq_mul]; simp
        calc (Work.Spaces.DzIter j (f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + (∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ Y + (((k - j : ℕ) : ℝ)) * Y := add_le_add hrad_le hsum
          _ = (((k - j : ℕ) : ℝ) + 1) * Y := by ring
      have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (f) z θ
            ≤ Bdom α k C1 M (Work.Spaces.pthIter 2 f) z θ := by
        intro θ hθ
        rw [Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum, Bdom]
        exact Finset.sum_le_sum (fun j hj => hgroup j hj θ hθ)
      -- integrability of the dominating function
      have hBint : MeasureTheory.IntegrableOn
          (Bdom α k C1 M (Work.Spaces.pthIter 2 f) z) Work.Spaces.Iθ := by
        unfold Bdom
        refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
        have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hG1 : MeasureTheory.IntegrableOn (fun θ =>
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ)
            Work.Spaces.Iθ := (hintG j hjle).add (hSint.const_mul M)
        have hG2 : MeasureTheory.IntegrableOn (fun θ => max C1 0 *
            (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ + M * Sfun α θ))
            Work.Spaces.Iθ := hG1.const_mul (max C1 0)
        exact hG2.const_mul (((k - j : ℕ) : ℝ) + 1)
      have hstep1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (f) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Bdom α k C1 M (Work.Spaces.pthIter 2 f) z θ :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k (f) z θ)
          hBint (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpoint)
      -- the integral of a slice group is at most `(k-j+1) M`
      have hGint : ∀ j : ℕ, j ≤ k →
          (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
            ≤ (((k - j : ℕ) : ℝ) + 1) * M := by
        intro j hjle
        have hradM : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ M := by
          rw [hM]
          exact MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
            (hInt z hz) (Eventually.of_forall fun θ =>
              Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ j hjle)
        have hmixM : ∀ m ∈ Finset.Icc 1 (k - j),
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                * Work.Spaces.Wt α z θ) ^ 2) ≤ M := by
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmj : m + j ≤ k := by have h2 := (Finset.mem_Icc.mp hm).2; omega
          rw [hM]
          exact MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
            (hInt z hz) (Eventually.of_forall fun θ =>
              Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 f) z θ m j hm1 hmj)
        have hmixS : (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (((k - j : ℕ) : ℝ)) * M := by
          rw [MeasureTheory.integral_finsetSum (s := Finset.Icc 1 (k - j))
            (f := fun m θ =>
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            (hf := fun m hm => hterm_mix j m (Finset.mem_Icc.mp hm).1
              (by have h2 := (Finset.mem_Icc.mp hm).2; omega))]
          calc (∑ m ∈ Finset.Icc 1 (k - j),
                (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2))
              ≤ ∑ m ∈ Finset.Icc 1 (k - j), M := Finset.sum_le_sum (fun m hm => hmixM m hm)
            _ = (Finset.Icc 1 (k - j)).card • M := Finset.sum_const M
            _ = (((k - j : ℕ) : ℝ)) * M := by rw [Nat.card_Icc, nsmul_eq_mul]; simp
        have hmix_int : MeasureTheory.IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2)
            Work.Spaces.Iθ :=
          MeasureTheory.integrable_finsetSum _ (fun m hm => hterm_mix j m
            (Finset.mem_Icc.mp hm).1 (by have h2 := (Finset.mem_Icc.mp hm).2; omega))
        have hGsplit : (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
            = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2) := by
          unfold Work.FTS.EllipticEst.sliceGroup
          exact MeasureTheory.integral_add (hterm_rad j hjle) hmix_int
        rw [hGsplit]
        calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ∑ m ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)
            ≤ M + (((k - j : ℕ) : ℝ)) * M := add_le_add hradM hmixS
          _ = (((k - j : ℕ) : ℝ) + 1) * M := by ring
      -- integral bound for the dominating function
      have hBval : (∫ θ in Work.Spaces.Iθ, Bdom α k C1 M (Work.Spaces.pthIter 2 f) z θ)
          ≤ (((k : ℝ) + 1) ^ 2 * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
        unfold Bdom
        have hsummand_int : ∀ j ∈ Finset.range (k + 1), MeasureTheory.Integrable
            (fun θ => (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
              (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                + M * Sfun α θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          intro j hj
          have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact (((hintG j hjle).add (hSint.const_mul M)).const_mul (max C1 0)).const_mul
            (((k - j : ℕ) : ℝ) + 1)
        rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := hsummand_int)]
        have hper : ∀ j ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ, (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)))
              ≤ (((k : ℝ) + 1) * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
          intro j hj
          have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hv : (∫ θ in Work.Spaces.Iθ, (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ)))
              = (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                  ((∫ θ in Work.Spaces.Iθ,
                      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
                    + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ))) := by
            rw [MeasureTheory.integral_const_mul]
            congr 1
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add (hintG j hjle) (hSint.const_mul M),
              MeasureTheory.integral_const_mul]
          rw [hv]
          have hG := hGint j hjle
          have hb0 : (∫ θ in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
              + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ)
              ≤ M * (((k - j : ℕ) : ℝ) + 10001 + Real.pi) := by
            have h2 : M * (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ M * (10000 + Real.pi) :=
              mul_le_mul_of_nonneg_left hSle hM0
            nlinarith [hG, h2, hM0]
          have hmax0 : 0 ≤ max C1 0 := le_max_right _ _
          have hc : (((k - j : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 1 := by
            have h : ((k - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k j
            linarith
          have hK : (((k - j : ℕ) : ℝ) + 10001 + Real.pi) ≤ ((k : ℝ) + 10001 + Real.pi) := by
            have h : ((k - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k j
            linarith
          have hKj0 : 0 ≤ (((k - j : ℕ) : ℝ) + 10001 + Real.pi) := by
            have h : (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by positivity
            linarith [Real.pi_pos]
          calc (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                ((∫ θ in Work.Spaces.Iθ,
                    Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
                  + M * (∫ θ in Work.Spaces.Iθ, Sfun α θ)))
              ≤ (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                  (M * (((k - j : ℕ) : ℝ) + 10001 + Real.pi))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb0 hmax0) (by positivity)
            _ ≤ ((k : ℝ) + 1) * (max C1 0 * (M * ((k : ℝ) + 10001 + Real.pi))) := by
                refine mul_le_mul hc ?_ ?_ ?_
                · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hM0) hmax0
                · exact mul_nonneg hmax0 (mul_nonneg hM0 hKj0)
                · positivity
            _ = (((k : ℝ) + 1) * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by ring
        calc (∑ j ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ,
              (((k - j : ℕ) : ℝ) + 1) * (max C1 0 *
                (Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ
                  + M * Sfun α θ))))
            ≤ ∑ j ∈ Finset.range (k + 1),
                ((((k : ℝ) + 1) * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M) :=
              Finset.sum_le_sum hper
          _ = ((k + 1 : ℕ) : ℝ) * ((((k : ℝ) + 1) * max C1 0
                * ((k : ℝ) + 10001 + Real.pi)) * M) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ = (((k : ℝ) + 1) ^ 2 * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M := by
              push_cast; ring
      calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (f) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Bdom α k C1 M (Work.Spaces.pthIter 2 f) z θ := hstep1
        _ ≤ (((k : ℝ) + 1) ^ 2 * max C1 0 * ((k : ℝ) + 10001 + Real.pi)) * M := hBval
        _ ≤ (((k : ℝ) + 1) ^ 2 * max C1 0 * ((k : ℝ) + 10001 + Real.pi) + 1) * M := by
              nlinarith [hM0]

end Work.Blocks
