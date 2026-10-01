import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.pairCount_dom
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The working-region (`|Im ρ| ≤ 1`) part of the Siegel zero sum

`Work.LinnikAreas.Siegel.restLowZeroSum` is the multiplicity-weighted sum of the kernel values
`‖Hk (11/2) (3/10) ((1-ρ)log q)‖` over all zero-pairs `(χ,ρ)`, `χ` any character mod `q`
(principal included), `|Im ρ| ≤ 1`, other than the exceptional pair `(χ₁,β₁)`.  This file proves
that it is `O(λ₁^{1+δ})` for a `δ > 0` (`λ₁ = lamOf q β₁`), from the two Deuring--Heilbronn
inputs `RepulsionInput` and `PairDensityInput`:

* the kernel bound `‖Hk L K ((1-ρ)𝓛)‖ ≤ K²e^{-a₀λ(ρ)}` (`a₀ = 49/10`, `λ(ρ) = (1-Re ρ)·𝓛`), valid
  on every zero of a completed `L`-function (`Siegel.Hk_norm_le_exp_lamOf` needs `Re ρ < 1`, which
  is `boxMaxZeroAux.zeroMult_re_lt_one`);
* every zero-pair in the sum is repelled by the exceptional zero:
  `Λ := c_r log (1/λ₁) ≤ λ(ρ)` (Deuring--Heilbronn);
* the `λ₁`-saving log-free zero count bounds the multiplicity-weighted number of pairs with
  `λ(ρ) ≤ t` by `C λ₁ e^{ct}` (`c < 49/10`).

A layer-cake summation (`sum_mul_exp_neg_le_of_count`) then gives
`K²·C λ₁ e^{cΛ} e^{(c-a₀)Λ}/(1-e^{c-a₀}) = O(λ₁ λ₁^{(a₀-c)c_r}) = O(λ₁^{1+δ})` with
`δ = (49/10 - max c 0)·c_r > 0`.
-/

/-- Every zero counted by `zeroMult` has positive real part: for a non-principal character this is
the lower half of `Commons…zerosInStrip`; for the principal character `zeroMult 1 ρ ≠ 0` means that
`ρ` is a zero of the completed Riemann zeta function, and `ζ` has no zero with `Re ≥ 1`
(`completedRiemannZeta_one_sub` transports such a zero to `Re ≥ 1`). -/
theorem zeroMult_re_pos_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (h : zeroMult χ ρ ≠ 0) : 0 < ρ.re := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta q ρ] at h
    have hΛ : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero h
    by_contra hc
    push_neg at hc
    have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
      rw [completedRiemannZeta_one_sub ρ]; exact hΛ
    have hs1 : 1 ≤ (1 - ρ).re := by simp; linarith
    have hs0 : (1 - ρ) ≠ 0 := by
      intro h0
      have h1 : ρ = 1 := by linear_combination -h0
      rw [h1] at hc; norm_num at hc
    have hz : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hΛ']; simp
    exact riemannZeta_ne_zero_of_one_le_re hs1 hz
  · haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ
        ≠ 0 := h
    have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero h2
    exact (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
      (boxMaxZeroAux.primitiveCharacter_ne_one_of_ne_one χ hχ)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hz).1

/-- The summand of `restLowZeroSum` as a function of a pair `(χ, ρ)`. -/
noncomputable def lowTerm {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    (z : DirichletCharacter ℂ q × ℂ) : ℝ :=
  if zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧ ¬(z.1 = χ₁ ∧ z.2 = β₁) then
    (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0

theorem siegelRestLow (hrep : Work.LinnikAreas.Siegel.RepulsionInput)
    (hden : Work.LinnikAreas.Siegel.PairDensityInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 2 →
      Work.LinnikAreas.Siegel.restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        ≤ C * (Work.LinnikContract.lamOf q (β₁ : ℂ)) ^ (1 + δ) := by
  obtain ⟨cr, hcrpos, qR, hRep⟩ := hrep
  obtain ⟨Cd, hCdpos, c, hc49, qD, hDen⟩ := hden
  set cs : ℝ := max c 0 with hcsdef
  have hcs0 : 0 ≤ cs := le_max_right _ _
  have hcslt : cs < 49 / 10 := max_lt hc49 (by norm_num)
  have hcsc : c ≤ cs := le_max_left _ _
  set δ : ℝ := (49 / 10 - cs) * cr with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact mul_pos (by linarith) hcrpos
  have hDfac : 0 < 1 - Real.exp (cs - 49 / 10) := by
    rw [sub_pos, Real.exp_lt_one_iff]; linarith
  set Cfin : ℝ := (3 / 10 : ℝ) ^ 2 * Cd * Real.exp cs / (1 - Real.exp (cs - 49 / 10)) + 1
    with hCfindef
  have hCfinpos : 0 < Cfin := by
    rw [hCfindef]
    have h1 : 0 < (3 / 10 : ℝ) ^ 2 * Cd * Real.exp cs := by positivity
    have h2 : 0 < (3 / 10 : ℝ) ^ 2 * Cd * Real.exp cs / (1 - Real.exp (cs - 49 / 10)) :=
      div_pos h1 hDfac
    linarith
  refine ⟨Cfin, hCfinpos, δ, hδpos, max (max qR qD) 2, ?_⟩
  intro q hq hqne χ₁ β₁ hχ hsq hβ1 hz hle
  haveI := hqne
  have hq2 : 2 ≤ q := le_trans (le_max_right (max qR qD) 2) hq
  have hq1 : 1 < q := by omega
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hqR : qR ≤ q := le_trans (le_trans (le_max_left qR qD) (le_max_left (max qR qD) 2)) hq
  have hqD : qD ≤ q := le_trans (le_trans (le_max_right qR qD) (le_max_left (max qR qD) 2)) hq
  set lam : ℝ := lamOf q (β₁ : ℂ) with hlamdef
  have hlampos : 0 < lam := Siegel.lamOf_pos hχ hβ1 hz
  have hlamlt : lam < 1 := by linarith
  have hinv1 : 1 < 1 / lam := by rw [lt_div_iff₀ hlampos]; simpa using hlamlt
  set Λ : ℝ := cr * Real.log (1 / lam) with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; exact mul_pos hcrpos (Real.log_pos hinv1)
  -- the repulsion in the form used below
  have hrep' : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ := by
    intro χ ρ hzρ him hne
    rw [hΛdef, hlamdef]
    exact hRep q hqR χ₁ β₁ hχ hsq hβ1 hz hle χ ρ hzρ him hne
  -- the finite set of zeros with `|Im| ≤ 1`, for each character
  set W : DirichletCharacter ℂ q → Finset ℂ :=
    fun χ => (boxMaxZeroAux.finite_zeroMult_box χ 0 1).toFinset with hWdef
  have hWmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      ρ ∈ W χ ↔ zeroMult χ ρ ≠ 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ 1 := by
    intro χ ρ
    rw [hWdef]
    exact Set.Finite.mem_toFinset (boxMaxZeroAux.finite_zeroMult_box χ 0 1)
  have hWzero : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ∈ W χ :=
    fun χ ρ hzm him => (hWmem χ ρ).mpr
      ⟨hzm, le_of_lt (zeroMult_re_pos_aux χ hzm),
        le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ hzm), him⟩
  set Wall : Finset ℂ := Finset.univ.biUnion W with hWalldef
  have hWallmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ∈ W χ → ρ ∈ Wall := by
    intro χ ρ h
    rw [hWalldef, Finset.mem_biUnion]
    exact ⟨χ, Finset.mem_univ χ, h⟩
  set S : Finset (DirichletCharacter ℂ q × ℂ) :=
    (Finset.univ : Finset (DirichletCharacter ℂ q)) ×ˢ Wall with hSdef
  have hlow_term : ∀ z, lowTerm χ₁ (β₁ : ℂ) z
      = (if zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) then
          (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
          else 0) := fun z => rfl
  -- step 1: `restLowZeroSum` as a sum over pairs
  have hstep1 : Siegel.restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      = ∑ z ∈ S, lowTerm χ₁ (β₁ : ℂ) z := by
    have h1 : Siegel.restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
            ∑ ρ ∈ Wall, lowTerm χ₁ (β₁ : ℂ) (χ, ρ) := by
      rw [Siegel.restLowZeroSum]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [← Finset.sum_subset (hWallmem χ) ?_]
      · refine tsum_eq_sum (fun ρ hρ => ?_)
        rw [if_neg]
        rintro ⟨hzm, him, -⟩
        exact hρ (hWzero χ ρ hzm him)
      · intro ρ hρWall hρnot
        rw [hlow_term (χ, ρ)]
        rw [if_neg]
        rintro ⟨hzm, him, -⟩
        exact hρnot (hWzero χ ρ hzm him)
    rw [h1, hSdef, Finset.sum_product]
  -- step 2: the terms outside the "good" set vanish
  have hstep2 : ∑ z ∈ S, lowTerm χ₁ (β₁ : ℂ) z
      = ∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
            ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
          (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
    calc ∑ z ∈ S, lowTerm χ₁ (β₁ : ℂ) z
        = ∑ z ∈ S, (if (zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
              ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))) then
            (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
            else 0) := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [hlow_term z]
        _ = ∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
              ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
            (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ :=
          (Finset.sum_filter (s := S) (p := fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
              ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))
            (f := fun z => (zeroMult z.1 z.2 : ℝ) *
              ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)).symm
  -- step 3: pointwise kernel bound
  have hgoodmem : ∀ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
      ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
      zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
    fun z hz => (Finset.mem_filter.mp hz).2
  have hker : (∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
        ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
        (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ (3 / 10 : ℝ) ^ 2 * ∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
          ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun z hz => ?_)
    have hzm : zeroMult z.1 z.2 ≠ 0 := (hgoodmem z hz).1
    have hρ : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 hzm
    have hb := Siegel.Hk_norm_le_exp_lamOf (q := q) (L := 11 / 2) (K := 3 / 10) (ρ := z.2)
      (by norm_num) hq1 hρ
    have h49 : -(11 / 2 - 2 * (3 / 10)) * lamOf q z.2 = -(49 / 10) * lamOf q z.2 := by norm_num
    rw [h49] at hb
    calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
        ≤ (zeroMult z.1 z.2 : ℝ) * ((3 / 10 : ℝ) ^ 2 * Real.exp (-(49 / 10) * lamOf q z.2)) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (3 / 10 : ℝ) ^ 2 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
          ring
  -- step 4: the layer-cake bound
  have hm0 : ∀ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
      ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))), (0 : ℝ) ≤ (zeroMult z.1 z.2 : ℝ) :=
    fun z _ => Nat.cast_nonneg _
  have hlamΛ : ∀ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
      ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))), Λ ≤ lamOf q z.2 := by
    intro z hz
    obtain ⟨hzm, him, hexc⟩ := hgoodmem z hz
    exact hrep' z.1 z.2 hzm him hexc
  have hlamL : ∀ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
      ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))), lamOf q z.2 ≤ Real.log q := by
    intro z hz
    have hzm : zeroMult z.1 z.2 ≠ 0 := (hgoodmem z hz).1
    have hre : 0 < z.2.re := zeroMult_re_pos_aux z.1 hzm
    rw [lamOf]
    calc (1 - z.2.re) * Real.log q ≤ 1 * Real.log q :=
          mul_le_mul_of_nonneg_right (by linarith) hlogpos.le
      _ = Real.log q := one_mul _
  have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ Real.log q →
      (∑ z ∈ (S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
          ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))).filter (fun z => lamOf q z.2 ≤ t),
        (zeroMult z.1 z.2 : ℝ))
        ≤ Cd * lam * Real.exp (cs * t) := by
    intro t htΛ htL
    have htpos : 0 < t := lt_of_lt_of_le hΛpos htΛ
    have hpair : (∑ z ∈ (S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
          ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))).filter (fun z => lamOf q z.2 ≤ t),
          (zeroMult z.1 z.2 : ℝ)) ≤ Siegel.pairCount χ₁ (β₁ : ℂ) t := by
      refine pairCount_dom hq1 χ₁ (β₁ : ℂ) _ ?_ ?_ ?_ ?_
      · intro z hz
        exact (hgoodmem z (Finset.mem_filter.mp hz).1).1
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · intro z hz
        exact (hgoodmem z (Finset.mem_filter.mp hz).1).2.1
      · intro z hz
        exact (hgoodmem z (Finset.mem_filter.mp hz).1).2.2
    have hdenq : Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ Cd * lamOf q (β₁ : ℂ) * Real.exp (c * t) := hDen q hqD χ₁ β₁ hχ hsq hβ1 hz hle t htpos htL
    calc (∑ z ∈ (S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
            ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))).filter (fun z => lamOf q z.2 ≤ t),
          (zeroMult z.1 z.2 : ℝ))
        ≤ Siegel.pairCount χ₁ (β₁ : ℂ) t := hpair
      _ ≤ Cd * lamOf q (β₁ : ℂ) * Real.exp (c * t) := hdenq
      _ = Cd * lam * Real.exp (c * t) := by rw [hlamdef]
      _ ≤ Cd * lam * Real.exp (cs * t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcsc htpos.le)
  have hcake := sum_mul_exp_neg_le_of_count
      (S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))))
      (fun z => (zeroMult z.1 z.2 : ℝ)) (fun z => lamOf q z.2)
      (a₀ := 49 / 10) (Λ := Λ) (L := Real.log q) (D := Cd) (lam₁ := lam) (c := cs)
      (by norm_num) hcs0 hcslt hCdpos hΛpos hlampos hm0 hlamΛ hlamL hcount
  -- step 5: the closing arithmetic
  have hexpΛ : Real.exp ((cs - 49 / 10) * Λ) = lam ^ δ := by
    rw [Real.rpow_def_of_pos hlampos]
    congr 1
    rw [hδdef, hΛdef, one_div, Real.log_inv]
    ring
  have hbase : lam ^ (1 + δ) = lam * lam ^ δ := by
    rw [Real.rpow_add hlampos, Real.rpow_one]
  calc Siegel.restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      = ∑ z ∈ S, lowTerm χ₁ (β₁ : ℂ) z := hstep1
    _ = ∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
          ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
          (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := hstep2
    _ ≤ (3 / 10 : ℝ) ^ 2 * ∑ z ∈ S.filter (fun z => zeroMult z.1 z.2 ≠ 0 ∧ |z.2.im| ≤ 1 ∧
          ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2) := hker
    _ ≤ (3 / 10 : ℝ) ^ 2 * (Cd * lam * Real.exp cs
          * Real.exp ((cs - 49 / 10) * Λ) / (1 - Real.exp (cs - 49 / 10))) :=
        mul_le_mul_of_nonneg_left hcake (by norm_num)
    _ ≤ Cfin * lam ^ (1 + δ) := by
        rw [hexpΛ, hbase, hCfindef]
        have hb : (0 : ℝ) ≤ lam * lam ^ δ := by positivity
        have he : (3 / 10 : ℝ) ^ 2
              * (Cd * lam * Real.exp cs * lam ^ δ / (1 - Real.exp (cs - 49 / 10)))
            = ((3 / 10 : ℝ) ^ 2 * Cd * Real.exp cs / (1 - Real.exp (cs - 49 / 10)))
              * (lam * lam ^ δ) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hb

end

end Work.LinnikAreas
