import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.H2.DivQ.NRI.W_integrable_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ.NRI

set_option maxHeartbeats 1000000

/-! ## The level-indexed integral bounds

The two pieces of the variable-level inversion are

  `∫_{0}^{x₁} AccDom l ≤ nrKT Cm l · nrSS l`,   `∫_{0}^{x₁} Dom l ≤ nrKC Cm l · nrSS l`   (`1 ≤ l ≤ N`),

proved by induction on the level: `AccDom (l+1) = AccDom l + Dom l` and
`Dom (l+1) = 2 · HonGam (l+1) + 2(l+1)Cm² · AccDom (l+1)`, so the one-step recursion
`nrLevel_bound` applies once the previous level is known. -/

/-- `AccDom α h Cm 1` is the base term `SubEta h` of the recursion. -/
private lemma nrAccDom_one_eq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    AccDom α h Cm 1 = SubEta h := by
  have h1 : AccDom α h Cm (0 + 1) = fun x => AccDom α h Cm 0 x + Dom α h Cm 0 x :=
    AccDom_succ α h Cm 0
  rw [show (1 : ℕ) = 0 + 1 from rfl, h1, AccDom_zero, Dom_zero]
  funext x
  simp

/-- **The level bounds at a variable level `N`.**  From the integrability and the pullback bound of
the honest data at the levels `1 ≤ m ≤ N` (`hEtaI`, `hGamI`, `hEtaBd`, `hGamBd`) one gets the two
level-indexed integral bounds for every `1 ≤ l ≤ N`. -/
private lemma nrLevel_bounds {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} {N : ℕ}
    (hEtaI : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear))
    (hGamI : ∀ m ∈ Finset.Icc 1 N, MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear))
    (hEtaBd : (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ nrDenEta h)
    (hGamBd : ∀ m ∈ Finset.Icc 1 N,
      (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h m x) ≤ nrDenGam α h m) :
    ∀ l, 1 ≤ l → l ≤ N →
      ((∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm l x) ≤ nrKT Cm l * nrSS α h l ∧
       (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm l x) ≤ nrKC Cm l * nrSS α h l) := by
  have hint := nrDom_integrable_le (α := α) (h := h) (Cm := Cm) N hEtaI hGamI
  have hDomInt : ∀ l ≤ N, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) := hint.1
  have hAccInt : ∀ l ≤ N, MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear) := hint.2
  -- the base level `l = 1`
  have hbase : 1 ≤ N →
      ((∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x) ≤ nrKT Cm 1 * nrSS α h 1 ∧
       (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm 1 x) ≤ nrKC Cm 1 * nrSS α h 1) := by
    intro hN1
    have hmem1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
    have hAcc1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x)
        = ∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x := by
      rw [nrAccDom_one_eq]
    have hA1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm 1 x)
        ≤ nrKT Cm 1 * nrSS α h 1 := by
      rw [hAcc1, nrKT_one, one_mul]
      exact le_trans hEtaBd (nrDenEta_le_SS α h 1)
    refine ⟨hA1, ?_⟩
    have hL := nrLevel_bound (α := α) (h := h) (Cm := Cm) (T := nrKT Cm 1) (k := 0)
      (hGamI 1 hmem1) (hAccInt 1 hN1) (hGamBd 1 hmem1) (nrDenGam_le_SS α h le_rfl) hA1
    have hKC : nrKC Cm 1 = 2 + 2 * (((0 + 1 : ℕ)) : ℝ) * Cm ^ 2 * nrKT Cm (0 + 1) := by
      simp [nrKC]
    rw [hKC]
    exact hL
  -- the induction step `l → l + 1`
  have hstep : ∀ n, 1 ≤ n → (n ≤ N →
        ((∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm n x) ≤ nrKT Cm n * nrSS α h n ∧
         (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm n x) ≤ nrKC Cm n * nrSS α h n)) →
      (n + 1 ≤ N →
        ((∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (n + 1) x)
            ≤ nrKT Cm (n + 1) * nrSS α h (n + 1) ∧
         (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (n + 1) x)
            ≤ nrKC Cm (n + 1) * nrSS α h (n + 1))) := by
    intro n hn1 ih hnN
    have ih' := ih (by omega)
    have hmem : n + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hnN⟩
    -- `AccDom (n+1) = AccDom n + Dom n`
    have hsplit : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (n + 1) x)
        = (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm n x)
          + (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm n x) := by
      rw [AccDom_succ]
      exact MeasureTheory.integral_add (hAccInt n (by omega)) (hDomInt n (by omega))
    have hAn1 : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (n + 1) x)
        ≤ nrKT Cm (n + 1) * nrSS α h (n + 1) := by
      rw [hsplit, nrKT_succ_eq Cm hn1]
      have hSS : nrSS α h n ≤ nrSS α h (n + 1) := nrSS_mono α h (by omega)
      have hnn : 0 ≤ nrKT Cm n + nrKC Cm n := by
        have h1 := nrKT_nonneg Cm n
        have h2 := nrKC_nonneg Cm (l := n) hn1
        linarith
      calc (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm n x)
              + (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm n x)
          ≤ nrKT Cm n * nrSS α h n + nrKC Cm n * nrSS α h n := by linarith [ih'.1, ih'.2]
        _ = (nrKT Cm n + nrKC Cm n) * nrSS α h n := by ring
        _ ≤ (nrKT Cm n + nrKC Cm n) * nrSS α h (n + 1) :=
            mul_le_mul_of_nonneg_left hSS hnn
    have hDn1 : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (n + 1) x)
        ≤ nrKC Cm (n + 1) * nrSS α h (n + 1) := by
      have hL := nrLevel_bound (α := α) (h := h) (Cm := Cm) (T := nrKT Cm (n + 1)) (k := n)
        (hGamI (n + 1) hmem) (hAccInt (n + 1) hnN) (hGamBd (n + 1) hmem)
        (nrDenGam_le_SS α h (by omega)) hAn1
      have hKC : nrKC Cm (n + 1)
          = 2 + 2 * (((n + 1 : ℕ)) : ℝ) * Cm ^ 2 * nrKT Cm (n + 1) := by
        simp [nrKC]
      rw [hKC]
      exact hL
    exact ⟨hAn1, hDn1⟩
  intro l hl1 hlN
  have key := Nat.le_induction (m := 1)
    (P := fun n _ => n ≤ N →
      ((∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm n x) ≤ nrKT Cm n * nrSS α h n ∧
       (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm n x) ≤ nrKC Cm n * nrSS α h n))
    hbase hstep l hl1
  exact key hlN

/-- **The near-region inversion `B_j ≤ C(Denη + Σ_{m≤j} Denγ m)` at a variable level `N ≤ 4`.**

This is `Work.FTS.H2.DivQ.W_integrable` / `Work.FTS.H2.DivQ.inversionNear` with the data
hypothesis `∀ m ∈ Icc 1 4, IntegrableOn (PsiGam α h m) Iθ` *weakened* to `∀ m ∈ Icc 1 N`, and the
conclusion restricted to levels `m ∈ Icc 1 N`.

ROUTE (all the ingredients are proved, `sorry`-free, in
`Submission/Work/FTS/H2/DivQ/NRI/LevelDefs.lean`, namespace `Work.FTS.H2.DivQ.NRI`;
the objects `PsiEta`, `PsiGam`, `SubEta`, `HonGam`, `Wide`, `Dom`, `AccDom`, `aCoeff`,
`Wide_le_Dom`, `aCoeff_bounds`, `xNear` are the public ones of
`Submission/Work/FTS/H2/DivQ/{WDefs,Wide_le_Dom,aCoeff_bounds,Defs}.lean`):

* `nrSS α h m = nrDenEta h + Σ_{n ∈ Icc 1 m} nrDenGam α h n` is the right-hand side
  (`nrDenEta`, `nrDenGam`, `nrSS`, `nrSS_eq`, `nrSS_mono`, `nrSS_nonneg`); here
  `nrDenEta h = ∫_{Iθ} PsiEta h`, `nrDenGam α h n = ∫_{Iθ} PsiGam α h n`;
* `nrHonGam_data : IntegrableOn (HonGam α h m) (Ioo 0 xNear) ∧ ∫_{Ioo 0 xNear} HonGam α h m ≤ nrDenGam α h m`
  (also `nrSubEta_data` for `SubEta`/`nrDenEta`), proved from `thetaOfSubst`;
* `nrDom_integrable_le N` gives the integrability of `Dom α h Cm l` and `AccDom α h Cm l` for
  all `l ≤ N` from exactly the data at levels `1 ≤ m ≤ N`;
* `nrLevel_bound` is the one-step recursion
  `∫ Dom (k+1) ≤ (2 + 2(k+1)Cm²T)·nrSS (k+1)` from `∫ AccDom (k+1) ≤ T·nrSS (k+1)`, the
  integrability of `HonGam (k+1)`/`AccDom (k+1)` and the bounds
  `∫ HonGam (k+1) ≤ nrDenGam (k+1) ≤ nrSS (k+1)`;
* `nrKT`/`nrKC`/`nrKCTot` are the explicit recursion constants for the level-indexed bounds
  `∫ AccDom l ≤ nrKT Cm l · nrSS l`, `∫ Dom l ≤ nrKC Cm l · nrSS l` (`1 ≤ l ≤ N`), with
  `nrKT Cm 1 = 1`, `nrKT_succ_eq : nrKT Cm (l+1) = nrKT Cm l + nrKC Cm l` (`1 ≤ l`) and
  `nrKC Cm l = 2 + 2·l·Cm²·nrKT Cm l`; `nrKCTot_pos` and `nrKC_le_tot` (for `l ≤ 4`) give a
  single constant dominating all four levels.

Concretely: pick `Cm` from `aCoeff_bounds` (`Cm := CG1 + CD1 + CG2 + CD2 + CG3 + CD3 + CG4 + CD4`
as in `W_integrable.lean`), set `C := nrKCTot Cm`, and prove by induction on `l` (base `l = 1`,
step `l → l+1` using `nrLevel_bound`) that `∫ AccDom l ≤ nrKT Cm l · nrSS α h l` and
`∫ Dom l ≤ nrKC Cm l · nrSS α h l`; then
`∫ Wide α h m ≤ ∫ Dom α h Cm m ≤ nrKCTot Cm · nrSS α h m` by `Wide_le_Dom` +
`setIntegral_mono_of_nonneg`, and finally the integrability of `Wide α h m` on `Ioc 0 xNear`
follows from its continuity on `Ioo 0 xNear` (`contDiffOn_iteratedDeriv_sliceX`),
the pointwise domination `Wide ≤ Dom` and `Integrable.mono'`, as at the end of
`W_integrable.lean` (`integrableOn_Ioc_iff_integrableOn_Ioo`). -/
theorem W_integrable_le (N : ℕ) (hN : N ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) →
      ∀ m : ℕ, m ∈ Finset.Icc 1 N →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) (Set.Ioc 0 xNear) ∧
        (∫ x in (0 : ℝ)..xNear, x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) ≤ C * nrSS α h m := by
  obtain ⟨Cm, hCmnn, hCb, hC0⟩ := exists_Cm_aCoeffBnd
  refine ⟨nrKCTot Cm, nrKCTot_pos Cm, ?_⟩
  intro α h hα0 hα1 hsm hDenEta hDenGam m hm
  have _ := hα0
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm4 : m ≤ 4 := le_trans hmN hN
  -- the two pullbacks of the honest data at the levels `1 ≤ n ≤ N`
  obtain ⟨hSubI, hSubB⟩ := nrSubEta_data hDenEta
  have hHonI : ∀ n ∈ Finset.Icc 1 N,
      MeasureTheory.IntegrableOn (HonGam α h n) (Set.Ioo 0 xNear) :=
    fun n hn => (nrHonGam_data (hDenGam n hn)).1
  have hHonB : ∀ n ∈ Finset.Icc 1 N,
      (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h n x) ≤ nrDenGam α h n :=
    fun n hn => (nrHonGam_data (hDenGam n hn)).2
  -- the level-indexed integral bounds
  have hkey := nrLevel_bounds (α := α) (h := h) (Cm := Cm) (N := N) hSubI hHonI hSubB hHonB
    m hm1 hmN
  have hDomInt : MeasureTheory.IntegrableOn (Dom α h Cm m) (Set.Ioo 0 xNear) :=
    (nrDom_integrable_le (α := α) (h := h) (Cm := Cm) N hSubI hHonI).1 m hmN
  -- `Wide α h m` is continuous on the near interval and dominated by `Dom`
  have hcont : ContinuousOn (Wide α h m) (Set.Ioo (0 : ℝ) xNear) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx.1))
    · exact ((contDiffOn_iteratedDeriv_sliceX hsm (m + 1)).continuousOn).pow 2
  have hle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Wide α h m x ≤ Dom α h Cm m x :=
    fun x hx => Wide_le_Dom hα1 hCmnn hsm hCb hC0 hm1 hm4 hx
  have hWideIoo : MeasureTheory.IntegrableOn (Wide α h m) (Set.Ioo 0 xNear) := by
    refine Integrable.mono' hDomInt (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_of_nonneg (Wide_nonneg α h m (le_of_lt hx.1))]
      exact hle x hx)
  have hWideIoc : MeasureTheory.IntegrableOn (Wide α h m) (Set.Ioc 0 xNear) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hWideIoo
  refine ⟨hWideIoc, ?_⟩
  show (∫ x in (0 : ℝ)..xNear, Wide α h m x) ≤ nrKCTot Cm * nrSS α h m
  -- the integral bound
  have hmono : (∫ x in Set.Ioo (0 : ℝ) xNear, Wide α h m x)
      ≤ ∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm m x :=
    setIntegral_mono_on hWideIoo hDomInt measurableSet_Ioo (fun x hx => hle x hx)
  have heq : (∫ x in (0 : ℝ)..xNear, Wide α h m x)
      = ∫ x in Set.Ioo (0 : ℝ) xNear, Wide α h m x := by
    rw [intervalIntegral.integral_of_le xNear_pos.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [heq]
  exact le_trans hmono (le_trans hkey.2
    (mul_le_mul_of_nonneg_right (nrKC_le_tot Cm hm1 hm4) (nrSS_nonneg α h m)))

end Work.FTS.H2.DivQ.NRI
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.nearRegionLHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter

set_option autoImplicit false

/-! ### Elementary facts on the near interval -/

lemma xNear_sq_nr : xNear ^ 2 = 1 / 2 := by
  rw [xNear, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma two_kappa_ge_one_nr : ∀ x ∈ Set.Icc (0 : ℝ) xNear, (1 : ℝ) ≤ 2 * kappa x := by
  intro x hx
  have hx2 : x ^ 2 ≤ (1 : ℝ) / 2 := by
    nlinarith [hx.1, hx.2, xNear_sq_nr, sq_nonneg x]
  have hk : (1 : ℝ) / 2 ≤ kappa x := by
    rw [kappa_eq_sqrt, Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith [hx2])]
    nlinarith [hx2]
  linarith

lemma thetaOf_zero_nr : thetaOf 0 = 0 := by simp [thetaOf]

lemma thetaOf_xNear_nr : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

lemma sin_two_thetaOf_Icc_nr : ∀ x ∈ Set.Icc (0 : ℝ) xNear, Real.sin (2 * thetaOf x) = x := by
  intro x hx
  rw [show 2 * thetaOf x = Real.arcsin x by rw [thetaOf]; ring, Real.sin_arcsin]
  · linarith [hx.1]
  · linarith [hx.2, xNear_le_one]

lemma contDiffOn_thetaOf_nr : ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo (-1 : ℝ) 1) := by
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ ({-1, 1} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) Real.arcsin (Set.Ioo (-1 : ℝ) 1) :=
    (Real.contDiffOn_arcsin (n := (⊤ : ℕ∞))).mono hsub
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.arcsin x / 2) (Set.Ioo (-1 : ℝ) 1) :=
    h1.div_const 2
  exact h2

lemma hasDerivAt_thetaOf_nr {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y : ℝ => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have hv : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
    rw [kappa_eq_sqrt]; ring
  exact h2.congr_deriv hv

lemma contDiffOn_sliceX_Ioc_nr {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioc 0 xNear) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => h (thetaOf x)) (Set.Ioc 0 xNear)
  refine hsm.comp (contDiffOn_thetaOf_nr.mono ?_) ?_
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx.1) (by norm_num)
    · rw [thetaOf]
      have h := (Real.arcsin_lt_pi_div_two).mpr (by linarith [hx.2, xNear_lt])
      linarith [h, Real.pi_pos]

lemma contDiffOn_sliceX_Ioo_nr {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) :=
  (contDiffOn_sliceX_Ioc_nr hsm).mono Set.Ioo_subset_Ioc_self

lemma tendsto_sliceX_nr {h : ℝ → ℝ}
    (hh : Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (sliceX h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 : Tendsto thetaOf (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt thetaOf (0 : ℝ) := (Real.continuous_arcsin.div_const 2).continuousAt
      have hct := hc.tendsto
      simp only [thetaOf_zero_nr] at hct
      exact hct.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [thetaOf]
      exact div_pos (Real.arcsin_pos.mpr hx) (by norm_num)
  exact hh.comp h1

/-! ### Congruence lemmas for the Euler-type operator `Gop` -/

lemma Gop_congr_eqOn_nr {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : Set.EqOn u v s) :
    Set.EqOn (Gop u) (Gop v) s := by
  intro x hx
  have hev : u =ᶠ[nhds x] v := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, h⟩
  simp only [Gop]
  rw [hev.deriv_eq]

lemma Gop_iter_eqOn_nr (i : ℕ) {u v : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn u v s) :
    Set.EqOn ((Gop^[i]) u) ((Gop^[i]) v) s := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Gop_congr_eqOn_nr hs ih hx

/-! ### The quotient slice in the `x`-variable -/

lemma sliceX_divSin_eqOn_nr (h : ℝ → ℝ) :
    Set.EqOn (sliceX (fun θ : ℝ => h θ / Real.sin (2 * θ)))
      (fun x : ℝ => sliceX h x / x) (Set.Ioo 0 xNear) := by
  intro x hx
  have hxI : x ∈ Set.Icc (0 : ℝ) xNear := ⟨hx.1.le, hx.2.le⟩
  change h (thetaOf x) / Real.sin (2 * thetaOf x) = h (thetaOf x) / x
  rw [sin_two_thetaOf_Icc_nr x hxI]

/-! ### Vanishing of the `j = 0` coefficient of `bCoeff` -/

lemma bCoeff_zero_of_pos_nr : ∀ i : ℕ, 1 ≤ i → bCoeff i 0 = fun _ => (0 : ℝ) := by
  have key : ∀ k : ℕ, genCoeff (fun _ : ℝ => 1) (k + 1) 0 = fun _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero =>
        rw [genCoeff_succ_zero, genCoeff_init_zero]
        funext x
        simp
    | succ k ih =>
        rw [genCoeff_succ_zero, ih]
        funext x
        simp
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [bCoeff_eq_genCoeff]
  exact key k


end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS_EllLimOK.EnergyGap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/- The nonexistent name `Work.FTS.EllLimOK.PhiD` occurring in the transmitted text of
`EnergyGap`, made definitionally equal to the real thing `Work.FTS_EllLimOK.PhiD`. -/
namespace Work.FTS
namespace EllLimOK
/-- Alias (definitionally equal) of `Work.FTS_EllLimOK.PhiD`, for the transmitted spelling. -/
abbrev PhiD := _root_.Work.FTS_EllLimOK.PhiD
end EllLimOK
end Work.FTS

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- On a fixed radial line `z > 0`, a box-regular function and its first two `z`-derivatives
have continuous slices on the angular interval `Iθ`. -/
theorem boxReg_slice_continuous {F : ℝ → ℝ → ℝ} (hbox : BoxReg F) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => F z θ) Work.Spaces.Iθ ∧
      ContinuousOn (fun θ => Work.Spaces.pz F z θ) Work.Spaces.Iθ ∧
      ContinuousOn (fun θ => Work.Spaces.pzIter 2 F z θ) Work.Spaces.Iθ := by
  have ha : 0 < z / 2 := by linarith
  have hab : z / 2 < 2 * z := by linarith
  have hab' : z / 2 ≤ 2 * z := le_of_lt hab
  have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  obtain ⟨-, -, hpz, hpz2⟩ :=
    boxReg_facts (F := F) (a := z / 2) (b := 2 * z) hab (hbox (z / 2) (2 * z) ha hab')
  have hcont : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ := by fun_prop
  have hmap : Set.MapsTo (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) Work.Spaces.Iθ
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := fun θ hθ => ⟨hzmem, hθ⟩
  have hF : ContinuousOn (fun θ => F z θ) Work.Spaces.Iθ := by
    have := ((hbox (z / 2) (2 * z) ha hab').continuousOn :
      ContinuousOn (Function.uncurry F) (cbox (z / 2) (2 * z)))
    exact this.comp hcont (fun θ hθ => ⟨⟨le_of_lt (hmap hθ).1.1, le_of_lt (hmap hθ).1.2⟩,
      (hmap hθ).2⟩)
  refine ⟨hF, ?_, ?_⟩
  · exact hpz.comp hcont hmap
  · exact hpz2.comp hcont hmap

theorem EnergyGap {α : ℝ} (hα : 0 < α) {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hboxΨ : Work.FTS_EllLimOK.BoxReg Ψ) (hboxΨ' : Work.FTS_EllLimOK.BoxReg Ψ')
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α (Work.FTS_EllLimOK.diff Ψ Ψ') z θ = 0)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.diff Ψ Ψ' z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.diff Ψ Ψ' z (π / 2) = 0)
    (horth : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Elliptic.Fstar (Work.FTS_EllLimOK.diff Ψ Ψ') z = 0)
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ)
    (hHkcΨ : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ))
    (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hHkcΨ' : Work.Spaces.HkMem α 0 (fun z θ => Ψ' z θ / Real.cos θ)) :
    (∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.FTS_EllLimOK.PhiD Ψ Ψ') (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ') z) z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ'))
          (deriv (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ')) z) z) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Work.FTS_EllLimOK.PhiD Ψ Ψ' z) ∧
      MeasureTheory.IntegrableOn (Work.FTS.EllLimOK.PhiD Ψ Ψ') (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z * z ^ (-4 : ℝ))
        (Set.Ioo (0 : ℝ) 1) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ α ^ 2 * z ^ 2
          * deriv (deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ')) z
        + α * (5 + α) * z * deriv (Work.FTS_EllLimOK.PhiD Ψ Ψ') z) := by
  have hboxδ : BoxReg (diff Ψ Ψ') := hboxΨ.diff hboxΨ'
  obtain ⟨hPhi1, hPhi2⟩ := Phi_deriv (δ := diff Ψ Ψ') hboxδ
  obtain ⟨hintPhi, hintPhiW⟩ :=
    Work.FTS_EllLimOK.EGap.integrableOn_PhiD (α := α) hHkΨ hHkΨ'
      (Work.FTS_EllLimOK.EGap.aemeasurable_uncurry_of_boxReg hboxδ)
  refine ⟨?_, ?_, ?_, hintPhi, hintPhiW, ?_⟩
  · -- first derivative
    intro z hz
    have h2 : HasDerivAt (PhiD Ψ Ψ')
        (2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ) z := hPhi1 z hz
    rw [h2.deriv]
    exact h2
  · -- second derivative
    intro z hz
    have hev : deriv (PhiD Ψ Ψ') =ᶠ[𝓝 z]
        (fun s => 2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' s θ * Work.Spaces.pz (diff Ψ Ψ') s θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
      exact (hPhi1 s hs).deriv
    have h := (hPhi2 z hz).congr_of_eventuallyEq hev
    rw [h.deriv]
    exact h
  · -- nonnegativity
    intro z hz
    exact PhiD_nonneg Ψ Ψ' z
  · -- the Euler gap inequality
    intro z hz
    obtain ⟨hs0, hs1, hs2⟩ := boxReg_slice_continuous hboxδ hz
    have hint1 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) Work.Spaces.Iθ :=
      (hs1.pow 2).integrableOn_compact isCompact_Icc
    have hint2 : MeasureTheory.IntegrableOn
        (fun θ => diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ) Work.Spaces.Iθ :=
      (hs0.mul hs2).integrableOn_compact isCompact_Icc
    have hd1 : deriv (PhiD Ψ Ψ') z
        = 2 * (∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ) := (hPhi1 z hz).deriv
    have hev : deriv (PhiD Ψ Ψ') =ᶠ[𝓝 z]
        (fun s => 2 * ∫ θ in Work.Spaces.Iθ,
          diff Ψ Ψ' s θ * Work.Spaces.pz (diff Ψ Ψ') s θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
      exact (hPhi1 s hs).deriv
    have hd2 : deriv (deriv (PhiD Ψ Ψ')) z
        = 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev, (hPhi2 z hz).deriv]
      rw [MeasureTheory.integral_add hint1 hint2]
      ring
    -- the equation integrated against the slice, and the angular self form
    have hLz := Work.FTS_EllLimOK.EGap.Lzero_integral_eq_boxReg α (diff Ψ Ψ') z hz hboxδ (hsol z hz)
    have hcomm1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        = ∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pzIter 2 (diff Ψ Ψ') z θ :=
      setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
    have hcomm2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        = ∫ θ in Work.Spaces.Iθ,
            diff Ψ Ψ' z θ * Work.Spaces.pz (diff Ψ Ψ') z θ :=
      setIntegral_congr_fun measurableSet_Icc fun θ _ => mul_comm _ _
    have hself := Work.FTS.EllipticEst.Lzero_self_form (diff Ψ Ψ') z
      (BoxReg.slice hboxδ hz) (h0 z hz) (h1 z hz)
    -- the constrained slice Poincaré gap
    obtain ⟨c, hcpos, hclt, hcf⟩ := Work.FTS.EllipticEst.coercive_slice_fts
    have hle : (∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ) ^ 2)
        ≤ c * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => diff Ψ Ψ' z θ') θ) ^ 2) :=
      hcf (fun θ => diff Ψ Ψ' z θ) (BoxReg.slice hboxδ hz) (h0 z hz) (h1 z hz) (horth z hz)
    have hnn1 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' => diff Ψ Ψ' z θ') θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (diff Ψ Ψ' z θ / Real.cos θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    have hQnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ := by
      rw [hself]
      nlinarith [hle, hnn1, hnn2, hcpos, hclt]
    have hA1n : 0 ≤ α ^ 2 * z ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg z))
        (integral_nonneg fun θ => sq_nonneg _)
    have hident : (α ^ 2 * z ^ 2 / 2) * deriv (deriv (PhiD Ψ Ψ')) z
        + (α * (5 + α) * z / 2) * deriv (PhiD Ψ Ψ') z
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
          + α ^ 2 * z ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) := by
      rw [hd1, hd2, hLz, hcomm1, hcomm2]
      ring
    have hsum : 0 ≤ (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero (diff Ψ Ψ') z θ * diff Ψ Ψ' z θ)
        + α ^ 2 * z ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (diff Ψ Ψ') z θ) ^ 2) :=
      add_nonneg hQnn hA1n
    nlinarith [hident, hsum]

end Work.FTS_EllLimOK
end
end
