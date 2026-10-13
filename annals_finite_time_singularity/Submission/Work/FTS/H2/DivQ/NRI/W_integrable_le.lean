import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.NRI.LevelDefs
import Submission.Work.FTS.H2.DivQ.exists_Cm_aCoeffBnd

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
