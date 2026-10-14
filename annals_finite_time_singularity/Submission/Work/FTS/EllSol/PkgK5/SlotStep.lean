import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The bundled level-`i` statement -/

/-- **The bundled level-`i` statement.**  For every level `i ≥ 1` there is a single constant
`C` such that, for all data satisfying the standing hypotheses and the honest data at levels
`≤ i`, every quotient level `j ∈ [1, i]` is `γ`-weighted integrable with
`∫ (D_θ^j (h/sin 2θ))² s^{-γ} ≤ C (η-data + ∑_{m ≤ i} γ-data m)`. -/
def LevelBnd (i : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
      Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
      (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
      ∀ j : ℕ, 1 ≤ j → j ≤ i →
        MeasureTheory.IntegrableOn (lhsInt α j h) Work.Spaces.Iθ ∧
        pLhs α j h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)

/-- The base case `i = 1` of the induction: the proved `Work.FTS.H2.DivSinQR.mixedSlotBoundIθ`. -/
theorem levelBnd_one : LevelBnd 1 := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.DivSinQR.mixedSlotBoundIθ
  refine ⟨C, hCpos, ?_⟩
  intro α h hα hα1 hsm h0 hπ hD hG j hj1 hji
  have hj : j = 1 := by omega
  subst hj
  have hG' : ∀ m : ℕ, m ∈ Finset.Icc 1 1 → MeasureTheory.IntegrableOn (gamInt α m h)
      Work.Spaces.Iθ := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact hG m hm1 (by omega)
  obtain ⟨hint, hbd⟩ := hC α h hα hα1 hsm h0 hπ hD 1 (Finset.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) hG'
  have hfun1 : ∀ θ : ℝ, Work.Elliptic.Dth1Iter 1 (Work.Elliptic.SinQ h) θ
      = Work.Elliptic.Dth1Iter 1 (fun θ' => h θ' / Real.sin (2 * θ')) θ := fun θ => rfl
  have h1 : lhsInt α 1 h = fun θ : ℝ =>
      (Work.Elliptic.Dth1Iter 1 (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    funext θ
    exact congrArg (fun x : ℝ => x ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (hfun1 θ)
  have h2 : pLhs α 1 h = ∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter 1 (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pLhs]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => congrArg (fun x : ℝ => x ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (hfun1 θ))
  have hbd' : (∫ θ in Work.Spaces.Iθ,
        (Work.Elliptic.Dth1Iter 1 (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ C * ((∫ θ in Work.Spaces.Iθ,
            (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + pGam α 1 h) := by
    simpa only [pGam, Finset.Icc_self, Finset.sum_singleton] using hbd
  refine ⟨?_, ?_⟩
  · rw [h1]; exact hint
  · rw [h2, pEta, Finset.Icc_self, Finset.sum_singleton]; exact hbd'

/-! ## The pointwise recursion bound -/

/-- The angular cut-off coefficients are bounded on `Iθ`: for every `l ≥ 1` there is a
nonnegative constant dominating `(D_θ^{i-1-l}(2 cos 2θ))²` on `Iθ`. -/
theorem bdd_coeff (i l : ℕ) (hl : 1 ≤ l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - l) cfun θ) ^ 2 ≤ K := by
  by_cases h0 : i - l = 0
  · refine ⟨4, by norm_num, fun θ => ?_⟩
    rw [h0, Work.Elliptic.Dth1Iter_zero]
    have hc : |cfun θ| ≤ 2 := by
      rw [cfun]
      have := Real.abs_cos_le_one (2 * θ)
      calc |2 * Real.cos (2 * θ)| = 2 * |Real.cos (2 * θ)| := by rw [abs_mul]; norm_num
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 2 := by norm_num
    nlinarith [abs_le.mp hc]
  · have hpos : 1 ≤ i - l := Nat.pos_of_ne_zero h0
    obtain ⟨M, hMpos, hM⟩ := Work.FTS.EllipticEst.Dth1IterTwoCosBoundN (i - l) hpos
    refine ⟨M ^ 2, by positivity, fun θ => ?_⟩
    have h := hM θ
    have hb : |Work.Elliptic.Dth1Iter (i - l) cfun θ| ≤ M := by
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        nlinarith [Real.sin_le_one (2 * θ), Real.neg_one_le_sin (2 * θ),
          sq_nonneg (Real.sin (2 * θ))]
      calc |Work.Elliptic.Dth1Iter (i - l) cfun θ| ≤ M * (Real.sin (2 * θ)) ^ 2 := h
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hs2 (le_of_lt hMpos)
        _ = M := mul_one M
    nlinarith [abs_le.mp hb]


def zTerm (α : ℝ) (M0 : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The `l`-th lower quotient term of the recursion bound. -/
def qTerm (α : ℝ) (i l : ℕ) (Kl : ℕ → ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
    * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-! ## The a.e. pointwise bound at level `i` -/

/-- **The pointwise recursion bound.**  Off the endpoints, the `i`-th quotient iterate is
controlled by the `(i-1)`-st derivative of `h'`, the sharpened level-zero term
(`M0 · sin(2θ)^4 · (h/sin 2θ)² sin(2θ)^{-γ}`) and the lower quotient iterates `1, …, i-1`. -/
theorem step_pointwise {i : ℕ} (hi2 : 2 ≤ i) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    {Kl : ℕ → ℝ} {M0 : ℝ} {α : ℝ}
    (hKl : ∀ l : ℕ, 1 ≤ l → l ≤ i - 1 → ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ) ^ 2 ≤ Kl l)
    (hM0 : ∀ θ : ℝ,
      (Work.Elliptic.Dth1Iter (i - 1) cfun θ) ^ 2 ≤ M0 * (Real.sin (2 * θ)) ^ 4)
    (hKl0 : ∀ l : ℕ, 0 ≤ Kl l) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      lhsInt α i h θ ≤ 2 * gamInt α (i - 1) h θ
        + 2 * (i : ℝ) * zTerm α M0 h θ
        + 2 * (i : ℝ) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ := by
  refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
  have hs := sin_two_pos_Ioo hθ
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg (le_of_lt hs) _
  have hi1 : 1 ≤ i := by omega
  have hrec := Work.FTS.EllSol.PkgK5.dthRecOpen i hi1 h hsm θ hθ
  set S : ℝ := ∑ l ∈ Finset.range i, (Nat.choose (i - 1) l : ℝ) *
    (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
      * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ with hSdef
  have hDQ : Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ
      = Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ - S := by rw [hrec]
  have hsq : (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
      ≤ 2 * (Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2 := by
    rw [hDQ]
    nlinarith [sq_nonneg (Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ + S)]
  have hS2 : S ^ 2 ≤ (i : ℝ) * ∑ l ∈ Finset.range i,
      ((Nat.choose (i - 1) l : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
        * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
      (f := fun l => (Nat.choose (i - 1) l : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
        * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ)
    rw [hSdef]
    simpa only [Finset.card_range, nsmul_eq_mul] using h
  have hsplit : ∑ l ∈ Finset.range i,
        ((Nat.choose (i - 1) l : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
          * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) ^ 2
      = ((Nat.choose (i - 1) 0 : ℝ) * (Work.Elliptic.Dth1Iter (i - 1) cfun θ)
          * Work.Elliptic.Dth1Iter 0 (Work.Elliptic.SinQ h) θ) ^ 2
        + ∑ l ∈ Finset.range (i - 1),
            ((Nat.choose (i - 1) (l + 1) : ℝ)
              * (Work.Elliptic.Dth1Iter (i - 1 - (l + 1)) cfun θ)
              * Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2 := by
    have h := Finset.sum_range_succ'
      (fun l => ((Nat.choose (i - 1) l : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
        * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) ^ 2) (i - 1)
    rw [show i - 1 + 1 = i from by omega] at h
    exact h.trans (add_comm _ _)
  have hterm0 : ((Nat.choose (i - 1) 0 : ℝ) * (Work.Elliptic.Dth1Iter (i - 1) cfun θ)
        * Work.Elliptic.Dth1Iter 0 (Work.Elliptic.SinQ h) θ) ^ 2
      ≤ M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2 := by
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Work.Elliptic.Dth1Iter_zero]
    calc (Work.Elliptic.Dth1Iter (i - 1) cfun θ * Work.Elliptic.SinQ h θ) ^ 2
        = (Work.Elliptic.Dth1Iter (i - 1) cfun θ) ^ 2 * (Work.Elliptic.SinQ h θ) ^ 2 := by
          ring
      _ ≤ (M0 * (Real.sin (2 * θ)) ^ 4) * (Work.Elliptic.SinQ h θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (hM0 θ) (sq_nonneg _)
      _ = M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2 := by ring
  have hterm : ∀ l ∈ Finset.range (i - 1),
      ((Nat.choose (i - 1) (l + 1) : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - (l + 1)) cfun θ)
        * Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2
      ≤ ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
          * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2 := by
    intro l hl
    have hli : l + 1 ≤ i - 1 := by have := Finset.mem_range.mp hl; omega
    have h1 : (Work.Elliptic.Dth1Iter (i - 1 - (l + 1)) cfun θ) ^ 2 ≤ Kl (l + 1) :=
      hKl (l + 1) (by omega) hli θ
    have hQ : 0 ≤ (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2 := sq_nonneg _
    calc ((Nat.choose (i - 1) (l + 1) : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - (l + 1)) cfun θ)
          * Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2
        = ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2
            * ((Work.Elliptic.Dth1Iter (i - 1 - (l + 1)) cfun θ) ^ 2
              * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2) := by ring
      _ ≤ ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * (Kl (l + 1)
            * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hQ) (sq_nonneg _)
      _ = ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
            * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2 := by ring
  have hsum : ∑ l ∈ Finset.range i,
        ((Nat.choose (i - 1) l : ℝ) * (Work.Elliptic.Dth1Iter (i - 1 - l) cfun θ)
          * Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) ^ 2
      ≤ M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ l ∈ Finset.range (i - 1),
            ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
              * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2 := by
    rw [hsplit]
    exact add_le_add hterm0 (Finset.sum_le_sum hterm)
  have hnni : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hfirst : 2 * S ^ 2 ≤ 2 * ((i : ℝ) *
      (M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ l ∈ Finset.range (i - 1),
            ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
              * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2)) := by
    nlinarith [hS2, hsum, hnni]
  have e2 : (2 * ((i : ℝ) * (M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
          + ∑ l ∈ Finset.range (i - 1),
              ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
                * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2)))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 * (i : ℝ) * zTerm α M0 h θ
        + 2 * (i : ℝ) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ := by
    have hQ : (∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ)
        = (∑ l ∈ Finset.range (i - 1),
              ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
                * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l hl => by rw [qTerm]; try ring)
    rw [hQ, zTerm]
    ring
  have e1 : (2 * (Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 * gamInt α (i - 1) h θ
        + 2 * (S ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    simp only [gamInt]
    ring
  have hmain : lhsInt α i h θ ≤ 2 * gamInt α (i - 1) h θ
        + 2 * (i : ℝ) * zTerm α M0 h θ
        + 2 * (i : ℝ) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ := by
    have hs1 : lhsInt α i h θ ≤ (2 * (Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      simp only [lhsInt]
      exact mul_le_mul_of_nonneg_right hsq hsnn
    calc lhsInt α i h θ
        ≤ (2 * (Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hs1
      _ = 2 * gamInt α (i - 1) h θ
            + 2 * (S ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := e1
      _ ≤ 2 * gamInt α (i - 1) h θ
            + (2 * ((i : ℝ) * (M0 * (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
                + ∑ l ∈ Finset.range (i - 1),
                    ((Nat.choose (i - 1) (l + 1) : ℝ)) ^ 2 * Kl (l + 1)
                      * (Work.Elliptic.Dth1Iter (l + 1) (Work.Elliptic.SinQ h) θ) ^ 2)))
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          refine add_le_add le_rfl ?_
          calc 2 * (S ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              = (2 * S ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hfirst hsnn
      _ = 2 * gamInt α (i - 1) h θ + (2 * (i : ℝ) * zTerm α M0 h θ
            + 2 * (i : ℝ) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ) := by
          rw [e2]
      _ = 2 * gamInt α (i - 1) h θ
            + 2 * (i : ℝ) * zTerm α M0 h θ
            + 2 * (i : ℝ) * ∑ l ∈ Finset.range (i - 1), qTerm α i l Kl h θ := by ring
  exact hmain

theorem lhsInt_nonneg_of_Ioo {α : ℝ} {i : ℕ} {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ lhsInt α i h θ := by
  rw [lhsInt]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (sin_two_pos_Ioo hθ)) _)

end Work.FTS.EllSol.PkgK5
