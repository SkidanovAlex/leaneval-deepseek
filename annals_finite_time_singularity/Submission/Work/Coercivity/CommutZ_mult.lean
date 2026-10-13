/-
# Boundedness of multiplication by a function of `z` alone on `ℋ^n`

Given a function `m : ℝ → ℝ` which is `C^∞` on `(0,∞)` and whose iterated `D_z`-derivatives
`DzIterZ j m` (`j ≤ n`) are bounded by `B` on `[0,∞)`, multiplication by `m` is a bounded
operator on `ℋ^n`: there is `C = C(n,B) > 0` with

  `HkSq α n (fun z θ => m z * f z θ) ≤ C * HkSq α n f`

for every `SmoothNbhd f` with `HkMem α n f`.

The proof has three layers.

* The algebraic layer: `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` are derivations, so with a
  `z`-only factor `m`
  `DzIter i (m·f) = ∑_{b≤i} (i.choose b) · (DzIterZ b m) · (DzIter (i-b) f)`
  (`DzIter_mulZm`) and
  `mixed j i (m·f) = ∑_{b≤j} (j.choose b) · (DzIterZ b m) · (mixed (j-b) i f)`
  (`mixed_mulZm`), while `D_θ^i (m·f) = m·D_θ^i f` (`DthIter_mulZm`).
* The pointwise layer: Cauchy–Schwarz on each expansion and the term bounds
  `sq_le_HkIntegrand_z`, `sq_le_HkIntegrand_mixed` bound the `H^n`-integrand of `m·f` by a
  constant times the `H^n`-integrand of `f` (`HkIntegrand_mulZm_le`, assembled from the two
  halves `CommutZ_mult_Zsum_le` and `CommutZ_mult_Msum_le`).
* The integral layer: `setIntegral_iterated_le_of_pointwise` upgrades that to the iterated
  integrals, using the integrability contained in `HkMem α n f`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Coercivity.DzRIter_mul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.setIntegral_iterated_le_of_pointwise
import Submission.Work.Coercivity.CommutZ_mult_Zsum_le
import Submission.Work.Coercivity.CommutZ_mult_Msum_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The one-variable operator `DzR` of `CTDefs` is `z ↦ z ∂_z` -/

theorem Zop_eq_DzR : Work.Spaces.Zop = CT.DzR := rfl

/-- `CT.DzRIter` is the iterate `DzIterZ` of `z ↦ z ∂_z` on functions of `z` alone. -/
theorem DzRIter_eq_DzIterZ (j : ℕ) (m : ℝ → ℝ) :
    CT.DzRIter j m = CommutZ.DzIterZ j m := by
  induction j with
  | zero => rfl
  | succ j ih => rw [CT.DzRIter_succ, ih, CommutZ.DzIterZ_succ]; rfl

/-- The iterate of `z ↦ z ∂_z` on a `θ`-slice is the slice of `DzIter`. -/
theorem DzRIter_eq_DzIter_slice (j : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    CT.DzRIter j (fun z => f z θ) = fun z => Work.Spaces.DzIter j f z θ := by
  rw [DzRIter_eq_iterate, ← Zop_eq_DzR, ← Work.Spaces.Zop_slice j f θ]

/-! ## The angular Leibniz rule -/

/-- `D_θ^i` commutes with multiplication by a function of `z` alone. -/
theorem DthIter_mulZm (i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => m z * f z θ)
      = fun z θ => m z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.pth,
        deriv_const_mul_field]
      ring

/-! ## The radial Leibniz rule -/

/-- `D_z^i` applied to `m(z)·f`: the binomial (Leibniz) expansion, with `DzIterZ` acting on
the `z`-only multiplier. -/
theorem DzIter_mulZm (i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hm : ContDiffOn ℝ ⊤ m (Set.Ioi 0)) (hf : Work.Spaces.SmoothNbhd f) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ =
        ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (CommutZ.DzIterZ b m z * Work.Spaces.DzIter (i - b) f z θ) := by
  intro z hz θ hθ
  have hslice : ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi 0) :=
    (Work.Spaces.hardyZ_contDiffOn_slice f hf hθ).mono (Set.Ioi_subset_Ioi (by norm_num))
  have hbridge : (fun z => Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ)
      = CT.DzRIter i (fun z => m z * f z θ) :=
    (DzRIter_eq_DzIter_slice i (fun z θ => m z * f z θ) θ).symm
  have h2 : CT.DzRIter i (fun z => m z * f z θ) z
      = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
          (CT.DzRIter k (fun z => m z) z * CT.DzRIter (i - k) (fun z => f z θ) z) := by
    simpa only [mul_assoc] using DzRIter_mul i (fun z => m z) (fun z => f z θ) hm hslice z hz
  rw [congrFun hbridge z, h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [DzRIter_eq_DzIterZ k m, DzRIter_eq_DzIter_slice (i - k) f θ]

/-! ## Locality of `D_z`-iterates in the `z`-variable -/

/-- `D_z^j` at a point only depends on the values of the function in a neighbourhood of that
point *at the fixed angle* `θ`. -/
theorem DzIter_congr_on (j : ℕ) (F G : ℝ → ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) {θ : ℝ}
    (h : ∀ z ∈ U, F z θ = G z θ) :
    ∀ z ∈ U, Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z hz; exact h z hz
  | succ j ih =>
      intro z hz
      show z * deriv (fun z' => Work.Spaces.DzIter j F z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter j G z' θ) z
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hU.mem_nhds hz] with z' hz'
      exact ih z' hz'

/-! ## The mixed Leibniz rule -/

/-- `D_z^j D_θ^i` applied to `m(z)·f`, using that `m` does not depend on `θ`. -/
theorem mixed_mulZm (j i : ℕ) (m : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hm : ContDiffOn ℝ ⊤ m (Set.Ioi 0)) (hf : Work.Spaces.SmoothNbhd f) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ =
        ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (CommutZ.DzIterZ b m z * Work.Spaces.mixed (j - b) i f z θ) := by
  intro z hz θ hθ
  have hloc : Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => m z * f z θ)) z θ
      = Work.Spaces.DzIter j (fun z θ => m z * Work.Spaces.DthIter i f z θ) z θ :=
    DzIter_congr_on j _ _ isOpen_Ioi
      (fun z' hz' => congrFun (congrFun (DthIter_mulZm i m f) z') θ) z hz
  have hexp := DzIter_mulZm j m (Work.Spaces.DthIter i f) hm
    (Work.Spaces.SmoothNbhd.DthIter hf i) z hz θ hθ
  have h1 : Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ
      = Work.Spaces.DzIter j (fun z θ => m z * Work.Spaces.DthIter i f z θ) z θ := by
    show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => m z * f z θ)) z θ = _
    exact hloc
  rw [h1, hexp]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Work.Spaces.mixed]

/-! ## The pointwise bound for the `H^n`-integrand -/

/-- Pointwise bound of the `H^n`-integrand of `m·f` by a constant times the `H^n`-integrand
of `f`, with a constant independent of `f`. -/
theorem HkIntegrand_mulZm_le (α : ℝ) (n : ℕ) (m : ℝ → ℝ) {B : ℝ}
    (hm : ContDiffOn ℝ ⊤ m (Set.Ioi 0))
    (hB : ∀ j ≤ n, ∀ z ∈ Set.Ici (0 : ℝ), |CommutZ.DzIterZ j m z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Spaces.SmoothNbhd f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n (fun z θ => m z * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α n f z θ := by
  obtain ⟨K1, hK1nn, hZ⟩ := CommutZ_mult_Zsum_le α n m hB
  obtain ⟨K2, hK2nn, hM⟩ := CommutZ_mult_Msum_le α n m hB
  refine ⟨K1 + K2 + 1, by linarith, fun f hf z hz θ hθ => ?_⟩
  have hZexp : ∀ i ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ =
        ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
          (CommutZ.DzIterZ b m z * Work.Spaces.DzIter (i - b) f z θ) :=
    fun i _ z hz θ hθ => DzIter_mulZm i m f hm hf z hz θ hθ
  have hMexp : ∀ j i : ℕ, 1 ≤ i → i + j ≤ n → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ =
        ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (CommutZ.DzIterZ b m z * Work.Spaces.mixed (j - b) i f z θ) :=
    fun j i hi hij z hz θ hθ => mixed_mulZm j i m f hm hf z hz θ (by
      rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h1 := hZ f hZexp z hz θ hθ
  have h2 := hM f hMexp z hz θ hθ
  have hFnn := Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hsplit : Work.Spaces.HkIntegrand α n (fun z θ => m z * f z θ) z θ
      = (∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ => m z * f z θ) z θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i (fun z θ => m z * f z θ) z θ *
                Work.Spaces.Wt α z θ) ^ 2
            else 0 := rfl
  rw [hsplit]
  linarith

/-! ## The target lemma -/

theorem CommutZ_mult (α : ℝ) (n : ℕ) (m : ℝ → ℝ) {B : ℝ}
    (hm : ContDiffOn ℝ ⊤ m (Set.Ioi 0))
    (hB : ∀ j ≤ n, ∀ z ∈ Set.Ici (0 : ℝ), |Work.Coercivity.CommutZ.DzIterZ j m z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ, Work.Spaces.SmoothNbhd f → Work.Spaces.HkMem α n f →
      Work.Spaces.HkSq α n (fun z θ => m z * f z θ) ≤ C * Work.Spaces.HkSq α n f := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_mulZm_le α n m hm hB
  refine ⟨C, hCpos, fun f hf hmem => ?_⟩
  have h := setIntegral_iterated_le_of_pointwise (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ)
    measurableSet_Ici measurableSet_Icc
    (fun z θ => Work.Spaces.HkIntegrand α n (fun z θ => m z * f z θ) z θ)
    (fun z θ => Work.Spaces.HkIntegrand α n f z θ) (le_of_lt hCpos)
    hmem
    (fun z _ θ _ => Work.Spaces.HkIntegrand_nonneg α n (fun z θ => m z * f z θ) z θ)
    (fun z hz θ hθ => hC f hf z hz θ hθ)
  simpa only [Work.Spaces.HkSq] using h

end Work.Coercivity
