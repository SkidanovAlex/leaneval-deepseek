/-
# Helper kit for `Work.Diff.STE.Lead.GalTame.sharpCoeff`

Generic lemmas used in the proof of the coefficient estimate `sharpCoeff`:

* `exists_cut_kit` — a smooth cutoff with values in `[0,1]`, equal to `1` on a closed ball and
  supported in a slightly larger open ball (the statement of `Work.Diff.STE.B3.transport_exists_cutoff`
  with the upper bound `≤ 1` kept);
* `pdVec_congr_nhds` — functions that agree near a point have the same iterated partial derivatives
  there (the `pdVec` form of `Work.Diff.STE.Lead.Gal.iteratedFDeriv_congr_W`), needed to compare the
  jets of a cut function with the jets of the function itself where the cutoff is `1`;
* `matrix_inv_quadForm` — for a symmetric matrix field squeezed between the quadratic forms
  `mlo · ‖·‖²` and `Mhi · ‖·‖²` (`mlo > 0`), the pointwise (Mathlib) inverse is *genuine*
  (`det ≠ 0`), is bounded entrywise and satisfies a quadratic-form lower bound.  This is the
  quantitative input of the whole-space Moser step (`invEnergyWhole`), fed by
  `Work.Diff.STE.B3.tmw_matrix_inv_bounds`.
-/
import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.B3.tmGamma_uniform
import Submission.Work.Diff.STE.B3.tmw_bgwin
import Submission.Work.Diff.STE.B3.transport_exists_cutoff
import Submission.Work.Diff.STE.B3.jet_bound_of_tsupport
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.tmw_matrix_inv_bounds
import Submission.Work.Diff.STE.Lead.Gal.transportExistsAUniformGal
import Submission.Work.Diff.STE.Lead.Gal.gardADefs
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Man.isDeTurckNonlin_chartNonlin
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.B3.pdVec_inv_le
import Submission.Work.Diff.STE.B3.ENormSq_basic
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory BigOperators Metric
open scoped Matrix BigOperators Manifold

namespace Work.Diff.STE.Lead.GalTame

namespace Kit

/-- **A smooth cutoff with values in `[0,1]`**, equal to `1` on the closed ball of radius `r > -1`
and supported in the open ball of radius `R > r`. -/
lemma exists_cut_kit {n : ℕ} {r R : ℝ} (hrR : r < R) :
    ∃ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ z, 0 ≤ φ z) ∧ (∀ z, φ z ≤ 1) ∧
      (∀ z : Fin n → ℝ, ‖z‖ ≤ r → φ z = 1) ∧
      tsupport φ ⊆ Metric.ball (0 : Fin n → ℝ) R := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := (isCompact_closedBall (0 : Fin n → ℝ) r).exists_cthickening_subset_open
    Metric.isOpen_ball (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith)
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, Fin n → ℝ)) (M := Fin n → ℝ) (n := ⊤)
      (s := (Metric.thickening δ (Metric.closedBall (0 : Fin n → ℝ) r))ᶜ)
      (t := Metric.closedBall (0 : Fin n → ℝ) r)
      Metric.isOpen_thickening.isClosed_compl (isCompact_closedBall _ _).isClosed
      (Set.disjoint_left.mpr fun x hx hxK => hx (Metric.self_subset_thickening hδpos _ hxK))
  refine ⟨fun z => f z, contMDiff_iff_contDiff.mp f.contMDiff, fun z => (hf01 z).1,
    fun z => (hf01 z).2, fun z hz => hf1 (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz), ?_⟩
  intro z hz
  have hsupp : Function.support (fun z => f z) ⊆
      Metric.thickening δ (Metric.closedBall (0 : Fin n → ℝ) r) := by
    intro w hw
    by_contra hw'
    exact hw (hf0 hw')
  exact hδ (Metric.closure_thickening_subset_cthickening δ _ (closure_mono hsupp hz))

/-- **Jet congruence for `pdVec`.**  Functions that agree on a neighbourhood of `z` (and are smooth
there) have the same iterated partial derivatives at `z`. -/
lemma pdVec_congr_nhds {n m : ℕ} {f g : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (h : f =ᶠ[nhds z] g) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g z)
    (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β f z = Work.Diff.STE.pdVec m β g z := by
  rw [Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at hf m β,
    Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at hg m β,
    Work.Diff.STE.Lead.Gal.iteratedFDeriv_congr_W (m := m) h]

/-- **The pointwise inverse of a uniformly definite symmetric matrix field.**
For a symmetric matrix field `A` whose quadratic form is squeezed between `mlo · ‖·‖²` and
`Mhi · ‖·‖²` with `mlo > 0`, the entries of the Mathlib inverse `(Matrix.of (A z))⁻¹` are uniformly
bounded by a constant `C ≥ 0`, the inverse satisfies the quadratic-form lower bound `c`, the
determinant is a unit (`det ≠ 0`), and `Matrix.of (A z) * (Matrix.of (A z))⁻¹ = 1`. -/
lemma matrix_inv_quadForm {n : ℕ} {mlo Mhi : ℝ} (hmlo : 0 < mlo) (hn : 0 < n) :
    ∃ (c C : ℝ), 0 < c ∧ 0 ≤ C ∧
      ∀ (A : (Fin n → ℝ) → Fin n → Fin n → ℝ),
        (∀ z p q, A z p q = A z q p) →
        (∀ (z : Fin n → ℝ) (ξ : Fin n → ℝ),
          mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) →
        (∀ (z : Fin n → ℝ) (ξ : Fin n → ℝ),
          (∑ p, ∑ q, A z p q * ξ p * ξ q) ≤ Mhi * ∑ i, (ξ i) ^ 2) →
        (∀ z, IsUnit (Matrix.of (A z)).det) ∧
        (∀ z p q, |(Matrix.of (A z))⁻¹ p q| ≤ C) ∧
        (∀ z, Matrix.of (A z) * (Matrix.of (A z))⁻¹ = 1) ∧
        (∀ (z : Fin n → ℝ) (ξ : Fin n → ℝ), c * ∑ i, (ξ i) ^ 2 ≤
          ∑ p, ∑ q, (Matrix.of (A z))⁻¹ p q * ξ p * ξ q) := by
  obtain ⟨c, C, hc, hC, hmat⟩ := Work.Diff.STE.B3.tmw_matrix_inv_bounds n mlo Mhi hmlo
  refine ⟨c, C, hc, hC, ?_⟩
  intro A hsym hlo hhi
  have hdet : ∀ z, IsUnit (Matrix.of (A z)).det := by
    intro z
    rw [isUnit_iff_ne_zero]
    intro hzero
    have hnotunit : ¬ IsUnit (Matrix.of (A z)).det := by
      rw [isUnit_iff_ne_zero]; exact fun h => h hzero
    have hinv : (Matrix.of (A z))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ hnotunit
    have hq := (hmat (A z) (hsym z) (hlo z) (hhi z)).1
    specialize hq (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ)
    have h1 : (∑ i : Fin n, (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) i ^ 2) = 1 := by
      rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, mul_one] at hq
    have hz0 : (∑ p : Fin n, ∑ q : Fin n, (Matrix.of (A z))⁻¹ p q
        * (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) p
        * (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) q) = 0 := by
      rw [hinv]; simp
    rw [hz0] at hq
    linarith
  refine ⟨hdet, fun z p q => (hmat (A z) (hsym z) (hlo z) (hhi z)).2 p q,
    fun z => Matrix.mul_nonsing_inv _ (hdet z),
    fun z ξ => (hmat (A z) (hsym z) (hlo z) (hhi z)).1 ξ⟩

/-- **A uniform jet bound for a finite family of compactly supported smooth functions.**  If every
`Φ j` is `C^∞` with topological support in the closed ball of radius `Rb j`, then there is one
constant `K ≥ 0` bounding all iterated derivatives and all iterated partial derivatives of order
`≤ N` of every `Φ j` on the whole space. -/
lemma exists_uniform_jet_bound {ι : Type*} [Fintype ι] (n N : ℕ) :
    ∀ (Φ : ι → (Fin n → ℝ) → ℝ) (Rb : ι → ℝ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Φ j)) →
      (∀ j, tsupport (Φ j) ⊆ Metric.closedBall (0 : Fin n → ℝ) (Rb j)) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ j,
        (∀ (m : ℕ), m ≤ N → ∀ z : Fin n → ℝ, ‖iteratedFDeriv ℝ m (Φ j) z‖ ≤ K) ∧
        (∀ (r : ℕ), r ≤ N → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
          |Work.Diff.STE.pdRVec r γ (Φ j) z| ≤ K) := by
  classical
  intro Φ Rb hsm hts
  choose M hM0 hM using fun j : ι =>
    Work.Diff.STE.B3.jet_bound_of_tsupport (Φ j) (Rb j) (hsm j) (hts j)
  refine ⟨∑ j, M j, Finset.sum_nonneg (fun j _ => hM0 j), fun j => ⟨?_, ?_⟩⟩
  · intro m hm z
    exact le_trans ((hM j).1 m hm z)
      (Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ j))
  · intro r hr γ z
    exact le_trans ((hM j).2 r hr γ z)
      (Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ j))

/-- **`pdVec` kills an additive constant, in positive order.**  For `d ≥ 1` the `d`-th iterated
partial derivative of `z ↦ c + g z` equals that of `g`. -/
lemma pdList_const_add {n : ℕ} (l : List (Fin n)) (hl : l ≠ []) (c : ℂ)
    (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdList l (fun z => c + g z) = Work.Diff.STE.pdList l g := by
  induction l with
  | nil => exact absurd rfl hl
  | cons i t ih =>
    by_cases ht : t = []
    · subst ht
      simp only [Work.Diff.STE.pdList, List.foldr_cons, List.foldr_nil]
      funext z
      simp only [Work.Diff.STE.pd]
      rw [fderiv_const_add]
    · have h1 : Work.Diff.STE.pdList t (fun z => c + g z) = Work.Diff.STE.pdList t g := ih ht
      change Work.Diff.STE.pd i (Work.Diff.STE.pdList t (fun z => c + g z))
        = Work.Diff.STE.pd i (Work.Diff.STE.pdList t g)
      rw [h1]

/-- **`pdVec` kills an additive constant, in positive order.** -/
lemma pdVec_const_add {n d : ℕ} (hd : 1 ≤ d) (β : Fin d → Fin n) (c : ℂ)
    (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec d β (fun z => c + g z) = Work.Diff.STE.pdVec d β g := by
  have hne : List.ofFn β ≠ [] := by
    intro h
    have h2 := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at h2
    omega
  exact pdList_const_add (List.ofFn β) hne c g

/-- The pointwise bound `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
lemma normSq_sub_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  nlinarith [h2, norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-- The integral form of `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
lemma setIntegral_normSq_sub_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (F G : α → ℂ) (hF : IntegrableOn (fun x => ‖F x‖ ^ 2) s μ)
    (hG : IntegrableOn (fun x => ‖G x‖ ^ 2) s μ) :
    ∫ x in s, ‖F x - G x‖ ^ 2 ∂μ
      ≤ 2 * (∫ x in s, ‖F x‖ ^ 2 ∂μ) + 2 * (∫ x in s, ‖G x‖ ^ 2 ∂μ) := by
  calc ∫ x in s, ‖F x - G x‖ ^ 2 ∂μ
      ≤ ∫ x in s, (2 * ‖F x‖ ^ 2 + 2 * ‖G x‖ ^ 2) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          ((hF.const_mul 2).add (hG.const_mul 2))
          (Filter.Eventually.of_forall fun x => normSq_sub_le (F x) (G x))
    _ = 2 * (∫ x in s, ‖F x‖ ^ 2 ∂μ) + 2 * (∫ x in s, ‖G x‖ ^ 2 ∂μ) := by
        rw [integral_add (hF.const_mul 2) (hG.const_mul 2), integral_const_mul, integral_const_mul]

end Kit

end Work.Diff.STE.Lead.GalTame
