/-
Copyright: work module for the Elgindi finite-time singularity project.

# The near-region inversion at a *variable* level `N ≤ 4`

`Submission/Work/FTS/H2/DivQ/inversionNear.lean` (and its consumer `W_integrable.lean`) prove the
triangular inversion of §4 of `Submission/Work/FTS/H2/DivQ/NOTES.md`

  `B_j := ∫_0^{x₁} x^{2j-γ}(∂_x^{j+1}(sliceX h))² dx ≤ C (Denη + Σ_{1≤m≤j} Denγ m)`

*uniformly for `1 ≤ j ≤ 4`*, but they take the honest angular data at **every** level `1 ≤ m ≤ 4`
as a hypothesis.  For the region lemmas applied to the slices `h_b = fun θ => DzIter b Φ z θ`
(`b ≥ 1`) only the data with `m + b ≤ 4` are certified, while the bound is needed at level
`i ≤ 4 - b`; hence the hypothesis is only available for `m ≤ i`.

This file re-exports that machinery in a form *parametric in the level*: the data functionals
`nrDenEta`, `nrDenGam m` and `nrSS j = nrDenEta + Σ_{1≤m≤j} nrDenGam m`, the pullback lemmas
`nrSubEta_data`/`nrHonGam_data`, the integrability of the dominating functions at a variable level
(`nrDom_integrable_le`), the per-level integral recursion (`nrLevel_bound`) and the explicit
recursion constants `nrKT`/`nrKC`/`nrKCTot` for the *level-indexed* bounds
`∫ AccDom l ≤ nrKT Cm l · nrSS l`, `∫ Dom l ≤ nrKC Cm l · nrSS l` (`l ≤ N`).

The assembly of these pieces into the variable-level inversion

  `Work.FTS.H2.DivQ.NRI.W_integrable_le (N) (hN : N ≤ 4)`

lives in the sibling module `Submission/Work/FTS/H2/DivQ/NRI/W_integrable_le.lean`.

All declarations are new (`nr`-prefixed) names: the `private` copies inside
`inversionNear.lean` are not reachable, and the *public* ones in `WDefs.lean`/`Wide_le_Dom.lean`
(`PsiEta`, `PsiGam`, `SubEta`, `HonGam`, `Wide`, `Dom`, `AccDom`, `Wide_le_Dom`,
`dom_integrable`, …) keep their statements (with the uniform bound `4`), which is exactly what
this file makes parametric.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.WDefs
import Submission.Work.FTS.H2.DivQ.Wide_le_Dom
import Submission.Work.FTS.H2.DivQ.thetaOfSubst
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ.NRI

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The data functionals at a variable level -/

/-- The honest `η`-data `Denη = ∫_{Iθ}(∂_θh)² sin(2θ)^{-η}`. -/
def nrDenEta (h : ℝ → ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiEta h θ

/-- The honest `γ`-data at angular order `m`: `Denγ m = ∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}`. -/
def nrDenGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ := ∫ θ in Work.Spaces.Iθ, PsiGam α h m θ

/-- The right-hand side `Denη + Σ_{1 ≤ m ≤ j} Denγ m` of the inversion at level `j`. -/
def nrSS (α : ℝ) (h : ℝ → ℝ) (j : ℕ) : ℝ :=
  nrDenEta h + ∑ m ∈ Finset.Icc 1 j, nrDenGam α h m

/-- `nrSS` in the raw form in which the region lemmas state their right-hand sides. -/
lemma nrSS_eq (α : ℝ) (h : ℝ → ℝ) (j : ℕ) :
    nrSS α h j
      = (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ m ∈ Finset.Icc 1 j, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := rfl

lemma nrDenEta_nonneg {h : ℝ → ℝ} : 0 ≤ nrDenEta h := by
  rw [nrDenEta]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiEta_nonneg h θ hθ)

lemma nrDenGam_nonneg {α : ℝ} {h : ℝ → ℝ} (m : ℕ) : 0 ≤ nrDenGam α h m := by
  rw [nrDenGam]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => psiGam_nonneg α h m θ hθ)

lemma nrSS_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : 0 ≤ nrSS α h l :=
  add_nonneg nrDenEta_nonneg (Finset.sum_nonneg (fun m _ => nrDenGam_nonneg m))

lemma nrSS_mono (α : ℝ) (h : ℝ → ℝ) {m l : ℕ} (hml : m ≤ l) : nrSS α h m ≤ nrSS α h l := by
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hml⟩
  · intro x _ _
    exact nrDenGam_nonneg x

lemma nrDenGam_le_SS (α : ℝ) (h : ℝ → ℝ) {l : ℕ} (hl : 1 ≤ l) :
    nrDenGam α h l ≤ nrSS α h l := by
  have hmem : l ∈ Finset.Icc 1 l := Finset.mem_Icc.mpr ⟨hl, le_rfl⟩
  have h := Finset.single_le_sum (f := fun m => nrDenGam α h m)
    (fun m _ => nrDenGam_nonneg m) hmem
  exact le_trans h (le_add_of_nonneg_left nrDenEta_nonneg)

lemma nrDenEta_le_SS (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : nrDenEta h ≤ nrSS α h l := by
  simp only [nrSS]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => nrDenGam_nonneg m))

/-! ## The two pullbacks of the honest data -/

/-- The `x`-pullback of the `η`-data is integrable on `(0,x₁)` and its integral is at most
`Denη`. -/
lemma nrSubEta_data {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, SubEta h x) ≤ nrDenEta h := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiEta h) hint (psiEta_nonneg h)
  have h1' : MeasureTheory.IntegrableOn
      (fun x : ℝ => PsiEta h (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h1
  have h2' : (∫ x in Set.Ioo (0 : ℝ) xNear,
        PsiEta h (thetaOf x) * (1 / (2 * kappa x))) ≤ nrDenEta h := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2
  exact ⟨h1'.congr_fun (fun x _ => rfl) measurableSet_Ioo,
    by rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => rfl)]; exact h2'⟩

/-- The `x`-pullback of the `γ`-data at order `m` is integrable on `(0,x₁)` and its integral is
at most `Denγ m`. -/
lemma nrHonGam_data {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) ∧
      (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h m x) ≤ nrDenGam α h m := by
  obtain ⟨h1, h2⟩ := thetaOfSubst (Ψ := PsiGam α h m) hint (psiGam_nonneg α h m)
  have h1' : MeasureTheory.IntegrableOn
      (fun x : ℝ => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h1
  have heq : Set.EqOn (HonGam α h m)
      (fun x : ℝ => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) (Set.Ioo 0 xNear) := by
    intro x hx
    have hs : Real.sin (2 * thetaOf x) = x := sin_two_thetaOf_Ioo hx
    simp only [HonGam, PsiGam, hs]
  have h2' : (∫ x in Set.Ioo (0 : ℝ) xNear,
        PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))) ≤ nrDenGam α h m := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le xNear_pos.le]
    exact h2
  exact ⟨h1'.congr_fun heq.symm measurableSet_Ioo,
    by rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo heq]; exact h2'⟩

/-! ## Integrability of the dominating functions at a variable level -/

/-- **Integrability of `Dom`/`AccDom` up to level `N`**, from the data at levels `1 ≤ m ≤ N`.
This is `Work.FTS.H2.DivQ.dom_integrable` with the uniform bound `4` replaced by `N` (its
inductive proof consumes `hGam` only at the next level). -/
lemma nrDom_integrable_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (N : ℕ)
    (hEta : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear))
    (hGam : ∀ m ∈ Finset.Icc 1 N,
      MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear)) :
    (∀ l ≤ N, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear)) ∧
      (∀ l ≤ N, MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear)) := by
  have key : ∀ l ≤ N,
      MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm l) (Set.Ioo 0 xNear) ∧
      MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
    intro l
    induction l with
    | zero =>
        intro _
        have h0 : MeasureTheory.IntegrableOn (Dom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [Dom_zero]; exact hEta
        have h1 : MeasureTheory.IntegrableOn (AccDom α h Cm 0) (Set.Ioo 0 xNear) := by
          rw [AccDom_zero]; exact MeasureTheory.integrableOn_zero
        have h2 : MeasureTheory.IntegrableOn (AccDom α h Cm (0 + 1)) (Set.Ioo 0 xNear) := by
          rw [AccDom_succ]
          exact h1.add h0
        exact ⟨h0, h1, h2⟩
    | succ l ih =>
        intro hl
        obtain ⟨hDl, hAl, hAl1⟩ := ih (by omega)
        have hG : MeasureTheory.IntegrableOn (HonGam α h (l + 1)) (Set.Ioo 0 xNear) :=
          hGam (l + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hD : MeasureTheory.IntegrableOn (Dom α h Cm (l + 1)) (Set.Ioo 0 xNear) := by
          rw [Dom_succ]
          exact (hG.const_mul 2).add (hAl1.const_mul (2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2))
        have hA : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 1)) (Set.Ioo 0 xNear) := hAl1
        have hA2 : MeasureTheory.IntegrableOn (AccDom α h Cm (l + 2)) (Set.Ioo 0 xNear) := by
          rw [show l + 2 = (l + 1) + 1 from rfl, AccDom_succ]
          exact hA.add hD
        exact ⟨hD, hA, hA2⟩
  exact ⟨fun l hl => (key l hl).1, fun l hl => (key l hl).2.1⟩

/-! ## The per-level integral recursion -/

/-- **The integral step at level `k+1`.**  If the partial sum `AccDom (k+1)` has already been
bounded by `T · nrSS (k+1)`, then the level-`k+1` member `Dom (k+1)` of the recursion is bounded
by `(2 + 2(k+1)Cm²T) · nrSS (k+1)`. -/
lemma nrLevel_bound {α : ℝ} {h : ℝ → ℝ} {Cm T : ℝ} {k : ℕ}
    (hGamInt : MeasureTheory.IntegrableOn (HonGam α h (k + 1)) (Set.Ioo 0 xNear))
    (hAccInt : MeasureTheory.IntegrableOn (AccDom α h Cm (k + 1)) (Set.Ioo 0 xNear))
    (hGamBd : (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x)
        ≤ nrDenGam α h (k + 1))
    (hGamSS : nrDenGam α h (k + 1) ≤ nrSS α h (k + 1))
    (hAccBd : (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x)
        ≤ T * nrSS α h (k + 1)) :
    (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      ≤ (2 + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * T) * nrSS α h (k + 1) := by
  have hI1 : MeasureTheory.IntegrableOn (fun x => 2 * HonGam α h (k + 1) x)
      (Set.Ioo 0 xNear) := hGamInt.const_mul 2
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2) * AccDom α h Cm (k + 1) x)
      (Set.Ioo 0 xNear) := hAccInt.const_mul _
  have hEq : (∫ x in Set.Ioo (0 : ℝ) xNear, Dom α h Cm (k + 1) x)
      = 2 * (∫ x in Set.Ioo (0 : ℝ) xNear, HonGam α h (k + 1) x)
        + (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) xNear, AccDom α h Cm (k + 1) x) := by
    simp only [Dom_succ_eq]
    rw [MeasureTheory.integral_add hI1 hI2,
      MeasureTheory.integral_const_mul 2 (fun x => HonGam α h (k + 1) x),
      MeasureTheory.integral_const_mul (2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
        (fun x => AccDom α h Cm (k + 1) x)]
  rw [hEq]
  have hstep := mul_le_mul_of_nonneg_left hAccBd
    (by positivity : (0 : ℝ) ≤ 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2)
  linarith [hGamBd, hGamSS, hstep]

/-! ## The explicit recursion constants

The level-indexed bounds are `∫ AccDom l ≤ nrKT Cm l · nrSS l` and `∫ Dom l ≤ nrKC Cm l · nrSS l`,
where the recurrences are

  `nrKT Cm 1 = 1`,   `nrKT Cm (l+1) = nrKT Cm l + nrKC Cm l`   (`l ≥ 1`),
  `nrKC Cm l = 2 + 2·l·Cm²·nrKT Cm l`   (`l ≥ 1`),

solved explicitly (`nrKT` is the single recursion below). -/

/-- The accumulated constant for `∫ AccDom l`. -/
def nrKT (Cm : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) => nrKT Cm (n + 1) * (1 + 2 * ((n + 1 : ℕ) : ℝ) * Cm ^ 2) + 2

/-- The constant for `∫ Dom l`. -/
def nrKC (Cm : ℝ) (l : ℕ) : ℝ := 2 + 2 * (l : ℝ) * Cm ^ 2 * nrKT Cm l

/-- A universal constant dominating all `nrKC Cm l`, `l ≤ 4`. -/
def nrKCTot (Cm : ℝ) : ℝ := nrKC Cm 1 + nrKC Cm 2 + nrKC Cm 3 + nrKC Cm 4

@[simp] lemma nrKT_zero (Cm : ℝ) : nrKT Cm 0 = 0 := rfl

@[simp] lemma nrKT_one (Cm : ℝ) : nrKT Cm 1 = 1 := rfl

lemma nrKT_succ_succ (Cm : ℝ) (n : ℕ) :
    nrKT Cm (n + 2) = nrKT Cm (n + 1) * (1 + 2 * ((n + 1 : ℕ) : ℝ) * Cm ^ 2) + 2 := rfl

lemma nrKT_nonneg (Cm : ℝ) : ∀ l, 0 ≤ nrKT Cm l := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
      rcases l with _ | m
      · simp
      · rw [show m + 1 + 1 = m + 2 from rfl, nrKT_succ_succ]
        have h2 : (0 : ℝ) ≤ 1 + 2 * ((m + 1 : ℕ) : ℝ) * Cm ^ 2 := by positivity
        nlinarith [ih, h2]

lemma nrKT_ge_one (Cm : ℝ) : ∀ l, 1 ≤ l → 1 ≤ nrKT Cm l := by
  intro l hl
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rcases m with _ | k
  · simp
  · rw [show k + 1 + 1 = k + 2 from rfl, nrKT_succ_succ]
    have h2 : (0 : ℝ) ≤ 1 + 2 * ((k + 1 : ℕ) : ℝ) * Cm ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ nrKT Cm (k + 1) := nrKT_nonneg Cm (k + 1)
    nlinarith [h2, h3]

lemma nrKC_nonneg (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : 0 ≤ nrKC Cm l := by
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (l : ℝ) * Cm ^ 2 * nrKT Cm l :=
    mul_nonneg (mul_nonneg hl' (sq_nonneg Cm)) (nrKT_nonneg Cm l)
  simp only [nrKC]
  linarith

lemma nrKC_ge_two (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : 2 ≤ nrKC Cm l := by
  have hl' : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (l : ℝ) * Cm ^ 2 * nrKT Cm l :=
    mul_nonneg (mul_nonneg hl' (sq_nonneg Cm)) (nrKT_nonneg Cm l)
  simp only [nrKC]
  linarith

/-- The recurrence satisfied by `nrKT`. -/
lemma nrKT_succ_eq (Cm : ℝ) {l : ℕ} (hl : 1 ≤ l) : nrKT Cm (l + 1) = nrKT Cm l + nrKC Cm l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [nrKT, nrKC]
  push_cast
  ring

lemma nrKC_le_tot (Cm : ℝ) {l : ℕ} (hl1 : 1 ≤ l) (hl4 : l ≤ 4) : nrKC Cm l ≤ nrKCTot Cm := by
  have h1 := nrKC_nonneg Cm (l := 1) le_rfl
  have h2 := nrKC_nonneg Cm (l := 2) (by norm_num)
  have h3 := nrKC_nonneg Cm (l := 3) (by norm_num)
  have h4 := nrKC_nonneg Cm (l := 4) (by norm_num)
  simp only [nrKCTot]
  interval_cases l <;> linarith

lemma nrKCTot_pos (Cm : ℝ) : 0 < nrKCTot Cm := by
  have h1 := nrKC_ge_two Cm (l := 1) le_rfl
  have h2 := nrKC_ge_two Cm (l := 2) (by norm_num)
  have h3 := nrKC_ge_two Cm (l := 3) (by norm_num)
  have h4 := nrKC_ge_two Cm (l := 4) (by norm_num)
  simp only [nrKCTot]
  linarith

end Work.FTS.H2.DivQ.NRI
