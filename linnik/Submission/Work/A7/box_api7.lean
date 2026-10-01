import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.exists_isMin1
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.style.haveILetI false

/-- **API part 1.** Everything in HB's box `InBox q R` (`λ(ρ) ≤ R`, `|Im ρ| log q ≤ R`) with
`R ≤ log q` and `q ≥ 2` lies in the working region `IsZ` (`χ ≠ 1`, multiplicity nonzero,
`|Im ρ| ≤ 1`).  Indeed `log q > 0` and `|Im ρ| log q ≤ R ≤ log q`. -/
lemma box_api7_p1 {q : ℕ} [NeZero q] {R : ℝ} (hq : 2 ≤ q) (hR : R ≤ Real.log q)
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hχ : χ ≠ 1)
    (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) (hbox : Work.LinnikContract.InBox q R ρ) :
    Work.LinnikContract.IsZ χ ρ := by
  obtain ⟨-, him⟩ := hbox
  have hlogpos : 0 < Real.log q := by
    apply Real.log_pos
    exact_mod_cast (show 1 < q by omega)
  have hle : |ρ.im| * Real.log q ≤ Real.log q := le_trans him hR
  have him1 : |ρ.im| ≤ 1 :=
    le_of_mul_le_mul_right (by simpa using hle) hlogpos
  exact ⟨hχ, hzm, him1⟩

/-- **API part 2.** If no point of HB's box `InBox q R` is a zero of `χ` in the working region
`IsZ`, then the (finitely supported) box sum of `χ` vanishes: each summand carries the
multiplicity factor `zeroMult χ ρ`, which is `0` at every point of the box. -/
lemma box_api7_p2 {q : ℕ} [NeZero q] {R : ℝ} (hq : 2 ≤ q) (hR : R ≤ Real.log q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (h : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ ρ ≠ 0 →
        ¬ Work.LinnikContract.IsZ χ ρ) :
    Work.LinnikContract.boxSum q (11/2) (3/10) R χ = 0 := by
  classical
  rw [Work.LinnikContract.boxSum]
  refine finsum_eq_zero_of_forall_eq_zero (fun ρ => ?_)
  by_cases hb : Work.LinnikContract.InBox q R ρ
  · rw [if_pos hb]
    have hzm : Work.LinnikContract.zeroMult χ ρ = 0 := by
      by_contra hne
      exact h ρ hb hne (box_api7_p1 hq hR hχ hne hb)
    rw [hzm]
    simp
  · rw [if_neg hb]

/-- **API part 3.** If the box `InBox q R` contains no non-trivial zero of `χ` at all, the
absolute box sum of `χ` vanishes. -/
lemma box_api7_p3 {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q} (_hχ : χ ≠ 1)
    (h : ∀ ρ : ℂ, ¬ (Work.LinnikContract.InBox q R ρ ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0)) :
    Work.LinnikContract.boxAbs q (3/10) R χ = 0 := by
  classical
  rw [Work.LinnikContract.boxAbs]
  refine finsum_eq_zero_of_forall_eq_zero (fun ρ => ?_)
  by_cases hb : Work.LinnikContract.InBox q R ρ
  · rw [if_pos hb]
    have hzm : Work.LinnikContract.zeroMult χ ρ = 0 := by
      by_contra hne
      exact h ρ ⟨hb, hne⟩
    rw [hzm]
    simp
  · rw [if_neg hb]

/-- **API part 4** (HB §6, the exceptional zero).  Let `χ₁` be a real character (`χ₁² = 1`) with a
real zero `ρ₁` (`Im ρ₁ = 0`) of multiplicity exactly one, of parameter `λ(ρ₁) < 1`.  Then no
Siegel zero of parameter `≤ lamS` can have parameter `< λ(ρ₁)`: if `lamS > λ(ρ₁)`, then `β = Re ρ₁`
is a real zero of the real character `χ₁` with `β < 1` and `(1-β) log q = λ(ρ₁) ≤ lamS`, i.e. a
Siegel zero.  The bound `β < 1` comes from the location of the non-trivial zeros in the critical
strip (`Commons.NumberTheory.Linnik.completedL_zero_strip`). -/
lemma box_api7_p4 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hχ : χ₁ ≠ 1)
    (hsq : χ₁ ^ 2 = 1) (him : ρ₁.im = 0)
    (hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ = 1)
    {lamS : ℝ} (hS : ¬ Work.LinnikContract.SiegelZero q lamS) (_hq : 2 ≤ q)
    (_hlt : Work.LinnikContract.lamOf q ρ₁ < 1) :
    lamS ≤ Work.LinnikContract.lamOf q ρ₁ := by
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hzm_ne : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := by rw [hzm]; norm_num
  have hΛ : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₁ = 0 := by
    have h' := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm_ne
    simpa [Work.LinnikContract.zeroMult] using h'
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
    (Work.A7.primitiveCharacter_ne_one hχ)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hΛ
  have hρ : ρ₁ = (ρ₁.re : ℂ) := Complex.ext (Complex.ofReal_re ρ₁.re).symm (by simpa using him)
  exact hS ⟨χ₁, hχ, hsq, ρ₁.re, hstrip.2, by rw [← hρ]; exact hzm_ne, le_of_lt hcon⟩

end

/-- **The AREA 7 interface.**  The four box/Siegel API facts used by the assembly. -/
theorem box_api7 :
    (∀ {q : ℕ} [NeZero q] {R : ℝ}, 2 ≤ q → R ≤ Real.log q →
      ∀ {χ : DirichletCharacter ℂ q} {ρ : ℂ}, χ ≠ 1 → Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      Work.LinnikContract.InBox q R ρ → Work.LinnikContract.IsZ χ ρ) ∧
    (∀ {q : ℕ} [NeZero q] {R : ℝ}, 2 ≤ q → R ≤ Real.log q →
      ∀ {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      (∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ ρ ≠ 0 →
        ¬ Work.LinnikContract.IsZ χ ρ) →
      Work.LinnikContract.boxSum q (11/2) (3/10) R χ = 0) ∧
    (∀ {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q}, χ ≠ 1 →
      (∀ ρ : ℂ, ¬ (Work.LinnikContract.InBox q R ρ ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0)) →
      Work.LinnikContract.boxAbs q (3/10) R χ = 0) ∧
    (∀ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}, χ₁ ≠ 1 →
      χ₁ ^ 2 = 1 → ρ₁.im = 0 → Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 →
      ∀ {lamS : ℝ}, ¬ Work.LinnikContract.SiegelZero q lamS → 2 ≤ q →
      Work.LinnikContract.lamOf q ρ₁ < 1 → lamS ≤ Work.LinnikContract.lamOf q ρ₁) :=
  ⟨box_api7_p1, box_api7_p2, box_api7_p3, box_api7_p4⟩

end Work.A7
