import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

/-!
# `Work.LinnikAreas.boxMaxZero` — the maximal zero of `L(·, χ₀)` in the box `|Im| ≤ 10 log q`

Given a non-zero multiplicity zero `ρ` (`zeroMult χ₀ ρ ≠ 0`) of `χ₀` with `|Im ρ| ≤ 1` and
`ρ ≠ ρ₀`, we produce a zero `ρ₂ ≠ ρ₀` in the box `|Im| ≤ 10 log q` which minimises
`lamOf q = (1 - Re ·) log q`, i.e. maximises the real part, among *all* zeros of `χ₀` in that box
other than `ρ₀`.

Since `log q > 0`, minimising `lamOf q` is the same as maximising the real part; and every zero
counted by `zeroMult` has real part `< 1`, so the relevant zeros lie in the compact box
`ρ.re ≤ Re ≤ 1`, `|Im| ≤ 10 log q`.  The candidate set of such zeros with `Re ≥ ρ.re` is finite,
which is what makes the minimum exist:

* for `χ₀ ≠ 1`, the zeros of `zeroMult χ₀` are the zeros of the entire function
  `completedLFunction χ₀.primitiveCharacter` (the completed `L`-function of the primitive
  character inducing `χ₀`), and an entire function that is not identically zero has only
  finitely many zeros in a compact set;
* for the principal character `χ₀ = 1`, `zeroMult 1 ρ` is the multiplicity of `ρ` as a zero of
  the completed zeta function `Λ = completedRiemannZeta`; such a `ρ` is either `0`, `1` — and by
  `completedRiemannZeta_eq` both cases force `Ξ(ρ) = 0` for the entire completion
  `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)` — so again the candidate set is contained in the zero set of a
  fixed entire function (not identically zero: `Ξ(0) = 1/2`).

The general fact about entire functions used here is `boxMaxZeroAux.finite_entire_zeros_closedBall`;
the identification of `zeroMult` with the vanishing order of `Λ` for the principal character is
`boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta`, and the strip bound
`boxMaxZeroAux.zeroMult_re_lt_one` (for *every* character, principal or not) is what replaces the
missing real-part upper bound on the minimisation.
-/
set_option linter.style.haveILetI false

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

namespace boxMaxZeroAux

/-! ## Zeros of an entire function in a compact set -/

/-- **Finiteness of the zeros of a non-zero entire function in a closed ball.**
If `f` is analytic on all of `ℂ` and is not the zero function, then `{z | f z = 0}` is discrete:
an infinite set of zeros inside the compact ball `closedBall c r` would have an accumulation
point, and the identity theorem would force `f ≡ 0`. -/
theorem finite_entire_zeros_closedBall {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) {w : ℂ}
    (hw : f w ≠ 0) (c : ℂ) (r : ℝ) : ({z : ℂ | f z = 0} ∩ Metric.closedBall c r).Finite := by
  rw [← Set.not_infinite]
  intro hInf
  -- an infinite subset of a compact set has an accumulation point
  obtain ⟨x, -, hacc⟩ := hInf.exists_accPt_of_subset_isCompact
    (isCompact_closedBall c r) Set.inter_subset_right
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ y in 𝓝[≠] x, f y = 0 := hacc.mono fun y hy => hy.1
  -- by the identity theorem `f` vanishes identically
  have hzero : Set.EqOn f 0 Set.univ :=
    hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x) hfreq
  exact hw (by simpa using hzero (Set.mem_univ w))

/-! ## The completed `L`-function of the principal character -/

/-- At level `1` the completed `L`-function is the completed Riemann zeta function. -/
theorem completedLFunction_conductor_one {N : ℕ} [NeZero N] (hN : N = 1)
    (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.completedLFunction χ = completedRiemannZeta := by
  subst hN
  exact DirichletCharacter.completedLFunction_modOne_eq

/-- `zeroMult` of the principal character is the vanishing order of the completed Riemann zeta
function `Λ`: the primitive character inducing the principal character mod `q` is the trivial
character mod `1`, whose completed `L`-function is `Λ`. -/
theorem zeroMult_one_eq_completedRiemannZeta (q : ℕ) [NeZero q] (ρ : ℂ) :
    zeroMult (1 : DirichletCharacter ℂ q) ρ = analyticOrderNatAt completedRiemannZeta ρ := by
  haveI : NeZero ((1 : DirichletCharacter ℂ q).conductor) :=
    ⟨DirichletCharacter.conductor_ne_zero (1 : DirichletCharacter ℂ q)⟩
  unfold zeroMult
  congr 1
  exact completedLFunction_conductor_one DirichletCharacter.conductor_one _

/-! ## The entire completion of `Λ` -/

/-- The entire completion `Ξ(s) = 1/2 + (1/2)·s·(s - 1)·Λ₀(s)` of the Riemann zeta function.
Its zeros are the non-trivial zeros of `ζ`, and `Ξ(0) = 1/2 ≠ 0`. -/
def xiEntire (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

theorem xiEntire_diff : Differentiable ℂ xiEntire := by
  have h1 : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  unfold xiEntire
  exact (differentiable_const _).add (h1.mul differentiable_completedZeta₀)

theorem xiEntire_analytic : AnalyticOnNhd ℂ xiEntire Set.univ := fun z _ => xiEntire_diff.analyticAt z

theorem xiEntire_zero_ne : xiEntire 0 ≠ 0 := by
  unfold xiEntire
  norm_num

/-- A zero of the completed zeta function away from `0` and `1` is a zero of the entire
completion `Ξ`.  (`Ξ(s) = (1/2)s(s-1)Λ(s)` in the sense of `completedRiemannZeta_eq`, so that
away from the two poles of `Λ` the two vanishing conditions coincide.) -/
theorem xiEntire_eq_zero_of_completedRiemannZeta_eq_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1)
    (hΛ : completedRiemannZeta ρ = 0) : xiEntire ρ = 0 := by
  have hΛ₀ : completedRiemannZeta₀ ρ = completedRiemannZeta ρ + 1 / ρ + 1 / (1 - ρ) := by
    have h := completedRiemannZeta_eq ρ
    rw [h]; ring
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [xiEntire, hΛ₀, hΛ]
  field_simp
  ring

/-! ## Zeros of `zeroMult` lie to the left of `Re = 1` -/

/-- The primitive character inducing a non-trivial character is non-trivial. -/
theorem primitiveCharacter_ne_one_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
  exact hχ h2.symm

/-- **Zeros of the completed `L`-function lie to the left of `Re = 1`**, for every Dirichlet
character, principal or not.

For `χ ≠ 1` this is the upper half of `Commons…zerosInStrip`.  For the principal character,
`zeroMult 1 ρ ≠ 0` gives `Λ ρ = 0`; at `ρ ≠ 0` this reads `ζ ρ = Λ ρ / Γℝ ρ = 0`, and
`ζ` has no zeros with `Re ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`).  (Only the upper bound
is used in the application, so no zero-free region on the left is needed.) -/
theorem zeroMult_re_lt_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (h : zeroMult χ ρ ≠ 0) : ρ.re < 1 := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [zeroMult_one_eq_completedRiemannZeta q ρ] at h
    have hΛ : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero h
    rcases eq_or_ne ρ 0 with rfl | hρ0
    · simp
    · have hz : riemannZeta ρ = 0 := by
        rw [riemannZeta_def_of_ne_zero hρ0, hΛ]; simp
      by_contra hc
      push_neg at hc
      exact (riemannZeta_ne_zero_of_one_le_re hc) hz
  · haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ
        ≠ 0 := h
    have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero h2
    exact (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
      (primitiveCharacter_ne_one_of_ne_one χ hχ)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hz).2

/-! ## The zero set of `zeroMult` in a compact box is finite -/

/-- **Finiteness of the zeros of `zeroMult` in a compact horizontal box.**  For every Dirichlet
character `χ` (including the principal one), the set of `ρ` with `zeroMult χ ρ ≠ 0`,
`a ≤ Re ρ ≤ 1` and `|Im ρ| ≤ R` is finite. -/
theorem finite_zeroMult_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a R : ℝ) :
    ({ρ : ℂ | zeroMult χ ρ ≠ 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ R} : Set ℂ).Finite := by
  classical
  -- the box is contained in a closed ball, of radius `N`
  set N : ℝ := max |a| 1 + R + 1 with hN
  have hbdd : ∀ ρ : ℂ, a ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ R → ρ ∈ Metric.closedBall (0 : ℂ) N := by
    intro ρ ha hb hc
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    have h2 : |ρ.re| ≤ max |a| 1 := by
      rw [abs_le]
      refine ⟨?_, le_trans hb (le_max_right _ _)⟩
      have h3 : -|a| ≤ a := neg_abs_le a
      have h4 : |a| ≤ max |a| 1 := le_max_left _ _
      linarith
    have h5 : (max |a| 1 : ℝ) + R ≤ N := by rw [hN]; linarith
    linarith
  by_cases hχ : χ = 1
  · -- the principal character: everything is a zero of the entire completion `Ξ`, up to `0,1`
    subst hχ
    have hsub : {ρ : ℂ | zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im| ≤ R} ⊆
        ({ρ : ℂ | xiEntire ρ = 0} ∩ Metric.closedBall (0 : ℂ) N) ∪ ({0, 1} : Set ℂ) := by
      intro ρ hρ
      obtain ⟨hzm, ha, hb, hc⟩ := hρ
      by_cases h01 : ρ = 0 ∨ ρ = 1
      · refine Set.mem_union_right _ ?_
        rcases h01 with h | h <;> simp [h]
      · push_neg at h01
        refine Set.mem_union_left _ ⟨?_, hbdd ρ ha hb hc⟩
        have hΛ : completedRiemannZeta ρ = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero
            (by rw [← zeroMult_one_eq_completedRiemannZeta q ρ]; exact hzm)
        exact xiEntire_eq_zero_of_completedRiemannZeta_eq_zero h01.1 h01.2 hΛ
    exact (((finite_entire_zeros_closedBall xiEntire_analytic xiEntire_zero_ne 0 N).union
      ((Set.finite_singleton (1 : ℂ)).insert 0))).subset hsub
  · -- non-principal: the zeros are zeros of one fixed entire function
    haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
    have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one_of_ne_one χ hχ
    have hne : ∃ w : ℂ, DirichletCharacter.completedLFunction χ.primitiveCharacter w ≠ 0 := by
      refine ⟨2, fun hc => ?_⟩
      have hL : DirichletCharacter.LFunction χ.primitiveCharacter 2 ≠ 0 :=
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψ)
          (by norm_num)
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ 2 (Or.inl (by norm_num)),
        hc, zero_div] at hL
      exact hL rfl
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        Set.univ := fun z _ => (DirichletCharacter.differentiable_completedLFunction hψ).analyticAt z
    obtain ⟨w, hw⟩ := hne
    refine (finite_entire_zeros_closedBall han hw 0 N).subset ?_
    intro ρ hρ
    obtain ⟨hzm, ha, hb, hc⟩ := hρ
    refine ⟨?_, hbdd ρ ha hb hc⟩
    have h2 : analyticOrderNatAt
        (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ 0 := hzm
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h2

end boxMaxZeroAux

/-! ## The main theorem -/

/-- **The zero of maximal real part of `L(·,χ₀)` in the box `|Im| ≤ 10 log q`, other than `ρ₀`.**

For `2 ≤ q`, given a non-zero multiplicity zero `ρ ≠ ρ₀` of `χ₀` with `|Im ρ| ≤ 1`, there is a
zero `ρ₂ ≠ ρ₀` of `χ₀` in the box `|Im| ≤ 10 log q` which *minimises* `lamOf q` (equivalently
maximises the real part) among all zeros of `χ₀` in that box except `ρ₀`; in particular
`lamOf q ρ₂ ≤ lamOf q ρ`.  (Zeros of the completed `L`-function lie in the strip `0 < Re < 1`,
so the zero set in the compact box is finite.) -/
theorem boxMaxZero {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ₀ : DirichletCharacter ℂ q) (ρ₀ ρ : ℂ)
    (hρ : Work.LinnikContract.zeroMult χ₀ ρ ≠ 0) (him : |ρ.im| ≤ 1) (hne : ρ ≠ ρ₀) :
    ∃ ρ₂ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ 10 * Real.log q ∧ ρ₂ ≠ ρ₀ ∧
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₀ u ≠ 0 → |u.im| ≤ 10 * Real.log q → u ≠ ρ₀ →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
  classical
  -- `log q > 0` and the box `|Im| ≤ 10 log q` contains `|Im| ≤ 1`
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hR1 : 1 ≤ 10 * Real.log q := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h3 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) h2
    have h4 := Real.log_two_gt_d9
    linarith
  have him' : |ρ.im| ≤ 10 * Real.log q := him.trans hR1
  have hρre : ρ.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one χ₀ hρ
  -- the finite candidate set: zeros in the box with `Re ρ' ≥ Re ρ` (i.e. `lamOf q ρ' ≤ lamOf q ρ`)
  have hfin := boxMaxZeroAux.finite_zeroMult_box χ₀ ρ.re (10 * Real.log q)
  set S := hfin.toFinset with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      zeroMult χ₀ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 10 * Real.log q := by
    intro u
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hρS : ρ ∈ S := by
    rw [hmemS]
    exact ⟨hρ, le_rfl, le_of_lt hρre, him'⟩
  -- a minimiser of `lamOf q` over the candidate set with `ρ₀` removed
  have hne' : (S.filter (fun u => u ≠ ρ₀)).Nonempty :=
    ⟨ρ, Finset.mem_filter.mpr ⟨hρS, hne⟩⟩
  obtain ⟨ρ₂, hρ₂mem, hmin⟩ :=
    Finset.exists_min_image (S.filter (fun u => u ≠ ρ₀)) (fun u => lamOf q u) hne'
  have hρ₂S : ρ₂ ∈ S := (Finset.mem_filter.mp hρ₂mem).1
  have hρ₂ne : ρ₂ ≠ ρ₀ := (Finset.mem_filter.mp hρ₂mem).2
  obtain ⟨hzm₂, -, -, him₂⟩ := (hmemS ρ₂).mp hρ₂S
  refine ⟨ρ₂, hzm₂, him₂, hρ₂ne, hmin ρ (Finset.mem_filter.mpr ⟨hρS, hne⟩), ?_⟩
  -- minimality among *all* zeros of `χ₀` in the box, except `ρ₀`
  intro u hzu himu hune
  rcases lt_or_ge (lamOf q ρ) (lamOf q u) with hlt | hle
  · exact le_trans (hmin ρ (Finset.mem_filter.mpr ⟨hρS, hne⟩)) (le_of_lt hlt)
  · -- `lamOf q u ≤ lamOf q ρ` forces `Re u ≥ Re ρ`, so `u` is a candidate as well
    have hre_le : ρ.re ≤ u.re := by
      have h1 : (1 - u.re) * Real.log q ≤ (1 - ρ.re) * Real.log q := hle
      have h2 : 1 - u.re ≤ 1 - ρ.re := (mul_le_mul_iff_left₀ hlogpos).mp h1
      linarith
    have huS : u ∈ S := by
      rw [hmemS]
      exact ⟨hzu, hre_le, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one χ₀ hzu), himu⟩
    exact hmin u (Finset.mem_filter.mpr ⟨huS, hune⟩)

end Work.LinnikAreas
