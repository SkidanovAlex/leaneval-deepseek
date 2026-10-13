import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.bCoeff_expansion
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.FTS.H2.DivQ.DthIter_sliceX
import Submission.Work.FTS.H2.DivQ.paperHardyIter
import Submission.Work.FTS.H2.DivQ.inversionNear
import Submission.Work.FTS.H2.DivQ.divSinPrimitive
import Submission.Work.FTS.H2.DivQ.powerHardyBoundary
import Submission.Work.FTS.H2.DivQ.hardyA_le_W
import Submission.Work.FTS.H2.DivQ.W_integrable
import Submission.Work.FTS.H2.DivQ.nearRegionLHS
import Submission.Work.FTS.H2.DivQ.NRI.LevelDefs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-- `Dth1Iter` of a function smooth on an open set is smooth there. -/
lemma contDiffOn_Dth1Iter_nri {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m f) s := by
  intro m
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Work.Elliptic.Dth1Iter_succ]
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter m f) θ) s
      have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) s :=
        (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
      exact hsin.mul (contDiffOn_deriv_of_isOpen s hs ih)

/-- **Honesty of the `Wide` integrands at a variable level.**

`Work.FTS.H2.DivQ.W_integrable` proves the integrability of
`Wide α h l = x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` on `(0,x₁)` for `1 ≤ l ≤ 4`, but it consumes
the honest angular data at *all* levels `1 ≤ m ≤ 4`.  For the region lemmas applied to the slices
`h_b = fun θ => DzIter b Φ z θ` (`b ≥ 1`) only the data with `m ≤ i = 4 - b` are available, so the
hypothesis must be weakened to the levels `1 ≤ m ≤ N` actually used.  The proof is that of
`W_integrable`: `Wide α h l ≤ Dom α h Cm l` pointwise (`Wide_le_Dom`), `Dom α h Cm l` is a
nonnegative combination of the `x`-pullbacks `SubEta`, `HonGam m` (`m ≤ l`) of the honest data,
hence integrable (`NRI.nrDom_integrable_le`, the level-parametric form of `dom_integrable`), and
`Wide` is continuous on `(0,x₁)` and nonnegative. -/
lemma wide_integrable_le_nri {α : ℝ} {h : ℝ → ℝ} (N : ℕ) (hN : N ≤ 4)
    (hα1 : α ≤ 1) (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDenEta : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ)
    (hDenGam : ∀ m : ℕ, m ∈ Finset.Icc 1 N →
      MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    ∀ l : ℕ, 1 ≤ l → l ≤ N →
      MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioc 0 xNear) := by
  intro l hl1 hlN
  obtain ⟨Cm, hCmnn, hCb, hC0⟩ := exists_Cm_aCoeffBnd
  have hEta : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
    subEta_integrable hDenEta
  have hGam : ∀ m ∈ Finset.Icc 1 N,
      MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) :=
    fun m hm => honGam_integrable (hDenGam m hm)
  have hDomInt : MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) :=
    (NRI.nrDom_integrable_le N hEta hGam).1 l hlN
  have hle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Wide α h l x ≤ Dom α h Cm l x :=
    fun x hx => Wide_le_Dom hα1 hCmnn hsm hCb hC0 hl1 (le_trans hlN hN) hx
  have hcont : ContinuousOn (Wide α h l) (Set.Ioo (0 : ℝ) xNear) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul
      ((contDiffOn_iteratedDeriv_sliceX hsm (l + 1)).continuousOn.pow 2)
  have hIoo : MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioo 0 xNear) := by
    refine Integrable.mono' hDomInt (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun x hx => by
      rw [Real.norm_of_nonneg (Wide_nonneg α h l (le_of_lt hx.1))]
      exact hle x hx)
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hIoo

/-- **Honesty (integrability) of the left-hand integrand on the near region** (route:
`Submission/Work/FTS/H2/DivQ/NOTES.md` §9.1).

The per-slice conjunct of `HkMem` requires the left-hand integrand itself to be integrable — an
integral inequality alone does not certify that, since a non-integrable integrand silently gives
the junk value `0`.  For `0 < α ≤ 1`, `h` of class `C^∞` on `(0,π/2)` with `h(θ) → 0` at `0⁺`,
honest `∫_{Iθ}(∂_θh)² sin(2θ)^{-η}`, and honest `∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}` for
`1 ≤ m ≤ i` (`η = 99/100`, `γ = 1+α/10`, `D_θ^m = Work.Elliptic.Dth1Iter m`), the integrand
`(D_θ^i (fun θ => h θ / sin(2θ)) θ)² sin(2θ)^{-γ}` is integrable on the near region
`(0, π/8]`.

ROUTE.  Substitute `x = sin 2θ`; by `DthIter_sliceX` (slice `fun θ => h θ/sin(2θ)`, whose `x`-form
is `f/x`, `f := sliceX h`) the near integrand is `(G^i(f/x))²x^{-γ}/(2κ)`.  `bCoeff_expansion`
gives `G^i(f/x) = Σ_{j=1}^{i} b i j x·x^j ∂_x^j(f/x)` (no `j = 0` term), so pointwise
Cauchy–Schwarz and `1/(2κ) ≤ 1/(2κ₁)` reduce to the *honesty* of
`A_j := ∫_0^{x₁}x^{2j-γ}(∂_x^j(f/x))²dx`.  Expand `∂_x^j(f/x) = Σ_{m≤j}c_{j,m}x^{m-j-1}f^{(m)}`
(Leibniz), so `x^{2j-γ}(∂_x^j(f/x))² ≤ C_jΣ_{m≤j}x^{2m-γ-2}(f^{(m)})²`; for `m ≥ 1` the honesty of
`x^{2m-γ-2}(f^{(m)})²` follows from `powerHardyBoundary` (`p = 2m-γ-2`) applied to `f^{(m)}`, whose
right-hand side `∫_0^{x₁}x^{2m-γ}(f^{(m+1)})²` is honest by `inversionNear` (its right-hand side is
honest) and whose boundary hypothesis `x^{2m-γ-1}(f^{(m)})² → 0` is `divSinPrimitive` with
`k = m-1`; the `m = 0` term `f²x^{-2-γ}` is `divSinPrimitive` with `k = 0` (`x·(f/x) = ∫_0^x∂_xf`,
using `f → 0`) together with the `η`-control `∫_0^{x₁}x^{4-γ}(∂_xf)² ≤ C∫x^{-η}(∂_xf)² ≤ C'Denη`.
The result transfers back to the `θ`-variable. -/
theorem nearRegionIntegrable (α : ℝ) (h : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDenη : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 4)
    (hDenγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioc 0 (Real.pi / 8)) := by
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  have hγneg : -1 < Work.Spaces.gam α := by linarith [Work.Spaces.one_lt_gam hα]
  -- the quotient slice and its `x`-form
  have hsm_div : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsm.div (contDiffOn_const.mul contDiffOn_id).sin ?_
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hquot : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) :=
    (contDiffOn_sliceX_Ioo_nr hsm).div contDiffOn_id (fun x hx => ne_of_gt hx.1)
  -- the honest data at the levels actually needed
  have hWide : ∀ l : ℕ, 1 ≤ l → l ≤ i →
      MeasureTheory.IntegrableOn (Wide α h l) (Set.Ioc 0 xNear) :=
    wide_integrable_le_nri i hi4 hα1 hsm hDenη (fun m hm => hDenγ m hm)
  obtain ⟨CH, hCHpos, hH⟩ := hardyA_le_W
  have hAint : ∀ k : ℕ, 1 ≤ k → k ≤ i → MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        * (iteratedDeriv k (fun y : ℝ => sliceX h y / y) x) ^ 2) (Set.Ioc 0 xNear) := by
    intro k hk1 hki
    exact (hH k (Work.Spaces.gam α) xNear xNear_pos hγneg (sliceX h)
      (contDiffOn_sliceX_Ioc_nr hsm) (tendsto_sliceX_nr h0) (hWide k hk1 hki)).1
  -- a uniform bound on the coefficients `bCoeff i j`, `j ≤ i`
  obtain ⟨B₁, hB₁nn, hb₁⟩ := (aCoeff_bounds 1).1
  obtain ⟨B₂, hB₂nn, hb₂⟩ := (aCoeff_bounds 2).1
  obtain ⟨B₃, hB₃nn, hb₃⟩ := (aCoeff_bounds 3).1
  obtain ⟨B₄, hB₄nn, hb₄⟩ := (aCoeff_bounds 4).1
  set B : ℝ := max B₁ (max B₂ (max B₃ B₄)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact le_trans hB₁nn (le_max_left _ _)
  have hbB : ∀ j ≤ i, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |bCoeff i j x| ≤ B := by
    intro j hj x hx
    have h1 : B₁ ≤ B := by rw [hBdef]; exact le_max_left _ _
    have h2 : B₂ ≤ B := by
      rw [hBdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : B₃ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have h4 : B₄ ≤ B := by
      rw [hBdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    interval_cases i
    · exact le_trans (hb₁ j hj x hx) h1
    · exact le_trans (hb₂ j hj x hx) h2
    · exact le_trans (hb₃ j hj x hx) h3
    · exact le_trans (hb₄ j hj x hx) h4
  -- the dominating function on the `x`-side
  set P : ℝ → ℝ := fun x => (i : ℝ) * B ^ 2 * ∑ j ∈ Finset.range i,
      x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
        * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 with hPdef
  -- the `x`-side integrand
  set K : ℝ → ℝ := fun x =>
      (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) with hKdef
  -- integrability of the dominating function
  have hPint : MeasureTheory.IntegrableOn P (Set.Ioc (0 : ℝ) xNear) := by
    have hSumInt : MeasureTheory.IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)
        (Set.Ioc (0 : ℝ) xNear) :=
      MeasureTheory.integrable_finsetSum _ (fun j hj => by
        have hjlt : j < i := Finset.mem_range.mp hj
        exact hAint (j + 1) (by omega) (by omega))
    have hPeq : P = fun x : ℝ => ((i : ℝ) * B ^ 2) * (∑ j ∈ Finset.range i,
        x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      rw [hPdef]
    rw [hPeq]
    exact hSumInt.const_mul _
  -- continuity and nonnegativity of the `x`-side integrand
  have hKcont : ContinuousOn K (Set.Ioo (0 : ℝ) xNear) := by
    have hDth : ContinuousOn (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_Dth1Iter_nri isOpen_Ioo hsm_div i).continuousOn
    have hcomp : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2)
        (Set.Ioo (0 : ℝ) xNear) :=
      (hDth.comp (Real.continuous_arcsin.div_const 2).continuousOn
        (fun x hx => thetaOf_mem_Ioo hx)).pow 2
    have hk : ContinuousOn (fun x : ℝ => 1 / (2 * kappa x)) (Set.Ioo (0 : ℝ) xNear) :=
      continuousOn_const.div (continuousOn_const.mul contDiffOn_kappa_b.continuousOn)
        (fun x hx => by
          have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
          positivity)
    have hmono : ContinuousOn (fun x : ℝ => x ^ (-(Work.Spaces.gam α)))
        (Set.Ioo (0 : ℝ) xNear) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
    have h4 : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) xNear) := hcomp.mul hmono
    have h5 : ContinuousOn (fun x : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) (Set.Ioo (0 : ℝ) xNear) :=
      h4.mul hk
    exact h5
  have hKnonneg : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, 0 ≤ K x := by
    intro x hx
    have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
    have h1 : (0 : ℝ) ≤ (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ))
        (thetaOf x)) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hx.1.le _
    have h3 : (0 : ℝ) ≤ 1 / (2 * kappa x) := div_nonneg zero_le_one (by linarith)
    rw [hKdef]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  -- the pointwise domination `K ≤ P` on `(0,x₁)`
  have hKle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, K x ≤ P x := by
    intro x hx
    have hpos : (0 : ℝ) < x := hx.1
    have hxIcc : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
    have hk1 : (1 : ℝ) ≤ 2 * kappa x := two_kappa_ge_one_nr x hxIcc
    have hknn : (0 : ℝ) ≤ 2 * kappa x := le_trans zero_le_one hk1
    have hident : Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)
        = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x :=
      (DthIter_sliceX i hsm_div hx).trans
        (Gop_iter_eqOn_nr i isOpen_Ioo (sliceX_divSin_eqOn_nr h) hx)
    have hKw : K x = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
      change (Work.Elliptic.Dth1Iter i (fun θ : ℝ => h θ / Real.sin (2 * θ)) (thetaOf x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      rw [hident]
    rw [hKw]
    have h0c : bCoeff i 0 = fun _ => (0 : ℝ) := bCoeff_zero_of_pos_nr i hi1
    have he : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x
        = ∑ j ∈ Finset.range i, bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) := by
      rw [bCoeff_expansion i hquot hx, Finset.sum_range_succ']
      rw [show bCoeff i 0 x
            * (x ^ 0 * iteratedDeriv 0 (fun y : ℝ => sliceX h y / y) x) = 0 by
        rw [h0c]
        simp]
      rw [add_zero]
    have hcs : ((Gop^[i] (fun y : ℝ => sliceX h y / y)) x) ^ 2
        ≤ (i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2 := by
      rw [he]
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
        (f := fun j : ℕ => bCoeff i (j + 1) x
          * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x))
      simpa using h
    have hterm : ∀ j ∈ Finset.range i,
        (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α))
        ≤ B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
      intro j hj
      have hj1 : j + 1 ≤ i := by have := Finset.mem_range.mp hj; omega
      have hb : |bCoeff i (j + 1) x| ≤ B := hbB (j + 1) hj1 x hxIcc
      have hb2 : (bCoeff i (j + 1) x) ^ 2 ≤ B ^ 2 := by
        rw [show (bCoeff i (j + 1) x) ^ 2 = |bCoeff i (j + 1) x| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have hxsq : x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
          = ((x ^ (j + 1)) ^ 2) * x ^ (-(Work.Spaces.gam α)) := by
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α
              = 2 * (((j + 1 : ℕ) : ℝ)) + (-(Work.Spaces.gam α)) by ring, Real.rpow_add hpos]
        congr 1
        rw [show 2 * (((j + 1 : ℕ) : ℝ)) = ((2 * (j + 1) : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
        rw [pow_mul]
        ring
      rw [show (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
            * x ^ (-(Work.Spaces.gam α))
          = (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 from by ring]
      have hnn : (0 : ℝ) ≤ (x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)) :=
        mul_nonneg (pow_nonneg (pow_nonneg hpos.le (j + 1)) 2) (Real.rpow_nonneg hpos.le _)
      have hnn2 : (0 : ℝ) ≤ (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
        sq_nonneg _
      calc (bCoeff i (j + 1) x) ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2
          ≤ B ^ 2 * ((x ^ (j + 1)) ^ 2 * x ^ (-(Work.Spaces.gam α)))
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 hnn) hnn2
        _ = B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← hxsq]; ring
    have hstep1 : (Gop^[i] (fun y : ℝ => sliceX h y / y)) x ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hpos.le _))
        (div_nonneg zero_le_one hknn)
    have hinv : 1 / (2 * kappa x) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < 2 * kappa x)]
      linarith
    have hstep2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
          (bCoeff i (j + 1) x
            * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) ≤ P x := by
      have h1 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ ((i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
            * x ^ (-(Work.Spaces.gam α)) * 1 :=
        mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
            (Real.rpow_nonneg hpos.le _))
      refine h1.trans ?_
      rw [mul_one]
      have hPeq : P x = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
          x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by rw [hPdef]
      rw [hPeq]
      have h2 : ((i : ℝ) * ∑ j ∈ Finset.range i,
            (bCoeff i (j + 1) x
              * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2)
          * x ^ (-(Work.Spaces.gam α))
          = (i : ℝ) * ∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)) := by
        rw [mul_assoc, Finset.sum_mul]
      rw [h2]
      have h3 : (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ ∑ j ∈ Finset.range i, B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      calc (i : ℝ) * (∑ j ∈ Finset.range i,
              (bCoeff i (j + 1) x
                * (x ^ (j + 1) * iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x)) ^ 2
              * x ^ (-(Work.Spaces.gam α)))
          ≤ (i : ℝ) * (∑ j ∈ Finset.range i,
              B ^ 2 * (x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (i : ℝ) * B ^ 2 * (∑ j ∈ Finset.range i,
              x ^ (2 * (((j + 1 : ℕ) : ℝ)) - Work.Spaces.gam α)
                * (iteratedDeriv (j + 1) (fun y : ℝ => sliceX h y / y) x) ^ 2) := by
            rw [← Finset.mul_sum]
            ring
    exact hstep1.trans hstep2
  -- integrability of `K` on `(0,x₁]`
  have hKint : MeasureTheory.IntegrableOn K (Set.Ioc (0 : ℝ) xNear) := by
    have hIoo : MeasureTheory.IntegrableOn K (Set.Ioo (0 : ℝ) xNear) := by
      have hPintIoo : MeasureTheory.IntegrableOn P (Set.Ioo (0 : ℝ) xNear) :=
        hPint.mono_set Set.Ioo_subset_Ioc_self
      refine Integrable.mono' hPintIoo (hKcont.aestronglyMeasurable measurableSet_Ioo) ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall (fun x hx => by
        rw [Real.norm_of_nonneg (hKnonneg x hx)]
        exact hKle x hx)
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIoo
  -- the `x`-side integrand of the change of variables, and the change of variables itself
  have hKs : MeasureTheory.IntegrableOn (fun x : ℝ => ((fun θ : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ∘ thetaOf) x * (1 / (2 * kappa x)))
      (Set.Ioc (0 : ℝ) xNear) := by
    refine hKint.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hs : Real.sin (2 * thetaOf x) = x :=
      sin_two_thetaOf_Icc_nr x ⟨hx.1.le, hx.2⟩
    simp only [hKdef, Function.comp_apply, hs]
  have hIntComp : IntervalIntegrable (fun x : ℝ => ((fun θ : ℝ =>
        (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ∘ thetaOf) x * (1 / (2 * kappa x)))
      volume 0 xNear := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le xNear_pos.le]
    exact hKs
  have hcθ : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  have hdθ : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    exact hasDerivAt_thetaOf_nr ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hkθ : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left xNear_pos.le, max_eq_right xNear_pos.le] at hx
    have hkpos : 0 < kappa x := kappa_pos_of_mem ⟨hx.1.le, hx.2.le⟩
    positivity
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x : ℝ => 1 / (2 * kappa x))
    (g := fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) hcθ hdθ hkθ
  have hF : IntervalIntegrable (fun θ : ℝ =>
      (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) volume 0 (Real.pi / 8) := by
    have h := hiff.mp hIntComp
    rwa [thetaOf_zero_nr, thetaOf_xNear_nr] at h
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)] at hF
  exact hF

end Work.FTS.H2.DivQ
