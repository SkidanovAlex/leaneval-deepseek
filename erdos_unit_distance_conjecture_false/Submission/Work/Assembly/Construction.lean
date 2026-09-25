import Submission.Work.Interface.All
import Submission.Work.Assembly.log_one_sub_ge
import Submission.Work.Assembly.cDist_le_card_sq
import Submission.Work.Assembly.exp_halves_pow
import Submission.Work.Assembly.exp_neg_le_pow

/-!
# Assembly of the unit-distance construction (Section 2 of *Erdős's conjecture is false*)

This is the assembly of Section 2 of the paper: from

* `hclass`, a bound for the class number of a number field in terms of its root discriminant
  (Minkowski's bound, proved in `Work.ClassNumber`),
* `fam`, the arithmetic input of the tower of Golod–Shafarevich type: for every `N` a CM field
  `K` with `N ≤ [K : ℚ]`, bounded root discriminant, in which all the primes `q b` split,

and the five interface lemmas of `Submission/Work/Interface/All.lean` (`numeric_inequalities`,
`exists_prime_family`, `exists_unitary_elements`, `exists_lattice`, `geometric_core`), we derive
the geometric conclusion: a fixed `δ > 0` such that for every `N` there is a finite planar point
set `P` with `N ≤ |P|` and `|P| ^ (1 + δ) ≤ ν(P)`.

The proof follows the paper: pick the constants `Hc = C' * C * (1 + log C)`, `γ = t log 2 - 2 log Hc`,
`R = max 1 (4/γ)`, `D = Q²`; the numeric input then produces `δ`. For a given `N` choose a CM
field `K` of large degree, take the lattice `Q⁻²𝒪_K` and `≥ 2^(t f)/h(K)` norm-one elements, and
apply the geometric core.

## The supporting API of this area

The elementary estimates used by the assembly are exposed as standalone lemmas so that they can be
reused without importing this file:

* `Work.Assembly.log_one_sub_ge` (`Submission.Work.Assembly.log_one_sub_ge`):
  `0 < x → x ≤ 1/2 → -(2 * x) ≤ Real.log (1 - x)`;
* `Work.Assembly.cDist_le_card_sq` (`Submission.Work.Assembly.cDist_le_card_sq`):
  `(Work.Defs.cDist P : ℝ) ≤ (P.card : ℝ) ^ 2`;
* `Work.Assembly.exp_halves_pow` (`Submission.Work.Assembly.exp_halves_pow`):
  `(Real.exp γ)^f * (Real.exp (-(γ/2)))^f = (Real.exp (γ/2))^f`;
* `Work.Assembly.exp_neg_le_pow` (`Submission.Work.Assembly.exp_neg_le_pow`):
  `0 < ρ → -(γ/4) ≤ Real.log ρ → (Real.exp (-(γ/2)))^f ≤ ρ^(2*f)`.
-/

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors
open Work.Interface
open Work.Defs

-- The existential witnesses of `fam` must be registered as local instances (via `letI`)
-- for the interface lemmas to elaborate; the `haveI`/`letI` style linter would prefer a
-- plain `let`, which would break typeclass search, so it is disabled for this file.
set_option linter.style.haveILetI false

namespace Work
namespace Assembly

/-- **Assembly of Section 2.**  See the module docstring for the shape of the argument. -/
theorem Construction (C' : ℝ) (hC'pos : 0 < C')
    (hclass : ∀ (K : Type) [Field K] [NumberField K] (A : ℝ), 1 ≤ A →
      NumberField.rootDiscr K ≤ A →
      (NumberField.classNumber K : ℝ) ≤ (C' * A * (1 + Real.log A)) ^ (Module.finrank ℚ K))
    (t : ℕ) (q : Fin t → ℕ) (C : ℝ) (ht : 0 < t) (hq : ∀ b, Nat.Prime (q b))
    (hqi : Function.Injective q) (hq4 : ∀ b, q b % 4 = 1) (hC : 1 ≤ C)
    (hnum : (C' * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t)
    (fam : ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ P : Finset ℂ,
      N ≤ P.card ∧ (P.card : ℝ) ^ (1 + δ) ≤ (Work.Defs.cDist P : ℝ) := by
  -- ## 1. The constants
  set Hc : ℝ := C' * C * (1 + Real.log C) with hHc_def
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h1logC : 0 < 1 + Real.log C := by
    have := Real.log_nonneg hC
    linarith
  have hHcpos : 0 < Hc := by
    rw [hHc_def]
    exact mul_pos (mul_pos hC'pos hCpos) h1logC
  have hnumH : Hc ^ 2 < (2 : ℝ) ^ t := hnum
  set γ : ℝ := (t : ℝ) * Real.log 2 - 2 * Real.log Hc with hγ_def
  have hγpos : 0 < γ := by
    rw [hγ_def]
    have h1 : 2 * Real.log Hc = Real.log (Hc ^ 2) := by rw [Real.log_pow]; norm_num
    have h2 : Real.log (Hc ^ 2) < Real.log ((2:ℝ) ^ t) :=
      Real.log_lt_log (pow_pos hHcpos 2) hnumH
    have h3 : Real.log ((2:ℝ) ^ t) = (t:ℝ) * Real.log 2 := by rw [Real.log_pow]
    linarith
  -- ## 2. The modulus `Q` of the construction and the separation scale `D = Q²`
  set Q : ℕ := ∏ b, q b with hQ_def
  have hQpos : 0 < Q := by
    rw [hQ_def]
    exact Finset.prod_pos (fun b _ => (hq b).pos)
  set D : ℝ := (Q : ℝ) ^ 2 with hD_def
  have hDpos : 0 < D := by
    rw [hD_def]; exact pow_pos (Nat.cast_pos.mpr hQpos) 2
  have hD1 : 1 ≤ D := by
    rw [hD_def]
    have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQpos
    calc (1:ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (Q:ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hQ1 2
  -- ## 3. The window radius `R`, and the log estimate feeding the numeric input
  set R : ℝ := max 1 (4 / γ) with hR_def
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hR : 1 / 2 < R := by linarith
  have hRD : 1 ≤ R * D := one_le_mul_of_one_le_of_one_le hR1 hD1
  have hx1 : 1 / (2 * R) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * R)]
    linarith
  have hx0 : 0 < 1 / (2 * R) := by
    rw [one_div]; exact inv_pos.mpr (by linarith : (0:ℝ) < 2 * R)
  have h2R : 2 * (1 / (2 * R)) = 1 / R := by
    rw [mul_one_div, div_mul_eq_div_div]; norm_num
  have h1R : 1 / R ≤ γ / 4 := by
    have h4γ : 0 < 4 / γ := div_pos (by norm_num) hγpos
    have h := one_div_le_one_div_of_le h4γ (le_max_right (1:ℝ) (4/γ))
    rwa [one_div_div] at h
  have hlogx : -(2 * (1 / (2 * R))) ≤ Real.log (1 - 1 / (2 * R)) :=
    log_one_sub_ge (1/(2*R)) hx0 hx1
  have hρ0 : (-γ) / 4 ≤ Real.log (1 - 1 / (2 * R)) := by
    calc (-γ) / 4 = -(γ / 4) := neg_div 4 γ
      _ ≤ -(1 / R) := by linarith
      _ = -(2 * (1 / (2 * R))) := by rw [h2R]
      _ ≤ Real.log (1 - 1 / (2 * R)) := hlogx
  -- ## 4. The numeric input produces `δ`
  obtain ⟨δ, hδpos, hnumest⟩ :=
    Work.Interface.numeric_inequalities t Hc hHcpos (by omega : 1 ≤ t) hnumH D R hD1 hR hRD hρ0
  -- ## 5. For each `N`, choose a field of large degree
  refine ⟨δ, hδpos, fun N => ?_⟩
  set η : ℝ := γ / 4 with hη_def
  have hρη : -η ≤ Real.log (1 - 1 / (2 * R)) := by
    rw [hη_def, ← neg_div]
    exact hρ0
  have hlogpos : 0 < 1 - 1 / (2 * R) := by linarith
  set A : ℝ := Real.exp γ with hA_def
  set A₂ : ℝ := Real.exp (γ / 2) with hA₂_def
  have hA₂1 : 1 < A₂ := by
    rw [hA₂_def, Real.one_lt_exp_iff]; linarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 2 * max (N : ℝ) ((2:ℝ) ^ (1/δ)) ≤ A₂ ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hA₂1).eventually_ge_atTop _
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨K, hKF, hKNF, hKCM, hdeg, hrd, hsplit⟩ := fam (2 * F)
  letI : Field K := hKF
  letI : NumberField K := hKNF
  letI : IsCMField K := hKCM
  set f : ℕ := Module.finrank ℚ (maximalRealSubfield K) with hf_def
  have hfinrankK : Module.finrank ℚ K = 2 * f := by
    rw [hf_def]; exact Work.Arithmetic.finrank_eq_two_mul K
  have hdeg2 : 2 * F ≤ 2 * f := by rw [← hfinrankK]; exact hdeg
  have hFf : F ≤ f := Nat.le_of_mul_le_mul_left hdeg2 (by norm_num)
  have hf1 : 1 ≤ f := by
    rw [hf_def]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := maximalRealSubfield K))
  -- ## 6. primes above the `q b` and the unitary elements they produce
  obtain ⟨𝔓, h𝔓prime, h𝔓ne, h𝔓conj, h𝔓div⟩ :=
    Work.Interface.exists_prime_family K t q hq hqi hq4 hsplit
  have hQdiv : ∀ i, ∃ p : ℕ, p ∣ Q ∧ Nat.Prime p ∧ Ideal.span {(p : 𝓞 K)} ≤ 𝔓 i := h𝔓div
  obtain ⟨U, hU1, hUQ, hUcard⟩ :=
    Work.Interface.exists_unitary_elements K (t * f) 𝔓 h𝔓prime h𝔓ne h𝔓conj Q hQpos hQdiv
  -- ## 7. the class-number bound, and the resulting lower bound for `|U|`
  have hcl : (NumberField.classNumber K : ℝ) ≤ Hc ^ (2 * f) := by
    have h := hclass K C hC hrd
    rw [hfinrankK] at h
    exact h
  have hUlb : (2:ℝ) ^ (t * f) ≤ Hc ^ (2 * f) * (U.card : ℝ) := by
    have h1 : (2:ℝ) ^ (t * f) ≤ (U.card : ℝ) * (NumberField.classNumber K : ℝ) := by
      exact_mod_cast hUcard
    have h2 : (U.card : ℝ) * (NumberField.classNumber K : ℝ) ≤
        (U.card : ℝ) * Hc ^ (2 * f) :=
      mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg U.card)
    calc (2:ℝ) ^ (t * f) ≤ (U.card : ℝ) * (NumberField.classNumber K : ℝ) := h1
      _ ≤ (U.card : ℝ) * Hc ^ (2 * f) := h2
      _ = Hc ^ (2 * f) * (U.card : ℝ) := by ring
  have hUpos : 0 < (U.card : ℝ) := by
    have h : 0 < U.card := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hUcard
      exact absurd hUcard (not_le.mpr (by positivity))
    exact_mod_cast h
  -- ## 8. the lattice and the geometric core
  obtain ⟨I, hIU, hIsep⟩ := Work.Interface.exists_lattice K Q hQpos U hUQ
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨S, hS0, hSub, hSlb⟩ :=
    Work.Interface.geometric_core K I R D hR hDpos hRD U hIU hU1 hIsep w₀
  have hSub' : (S.card : ℝ) ≤ (4 * R * D) ^ (2 * f) := by
    rw [hfinrankK] at hSub; exact hSub
  have hSlb' : 2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) * (S.card : ℝ)
      ≤ (Work.Defs.cDist S : ℝ) := by
    rw [hfinrankK] at hSlb; exact hSlb
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS0
  -- ## 9. the lower bound for `S.card`
  have hstep : 2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) ≤ (S.card : ℝ) := by
    have hcd : (Work.Defs.cDist S : ℝ) ≤ (S.card : ℝ) ^ 2 := cDist_le_card_sq S
    have h : 2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) * (S.card : ℝ)
        ≤ (S.card : ℝ) * (S.card : ℝ) := by
      calc 2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) * (S.card : ℝ)
          ≤ (Work.Defs.cDist S : ℝ) := hSlb'
        _ ≤ (S.card : ℝ) ^ 2 := hcd
        _ = (S.card : ℝ) * (S.card : ℝ) := pow_two _
    exact le_of_mul_le_mul_right h hSpos
  have hAexp : A = (2:ℝ) ^ t / Hc ^ 2 := by
    have e1 : γ = Real.log ((2:ℝ) ^ t) - Real.log (Hc ^ 2) := by
      rw [hγ_def]
      have a : (t:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ t) := by rw [Real.log_pow]
      have b : (2:ℝ) * Real.log Hc = Real.log (Hc ^ 2) := by rw [Real.log_pow]; norm_num
      rw [a, b]
    rw [hA_def, e1, Real.exp_sub, Real.exp_log (by positivity),
      Real.exp_log (pow_pos hHcpos 2)]
  have hAf : A ^ f = (2:ℝ) ^ (t * f) / Hc ^ (2 * f) := by
    rw [hAexp, div_pow, ← pow_mul, ← pow_mul]
  have hUge : A ^ f ≤ (U.card : ℝ) := by
    have h1 : (2:ℝ) ^ (t * f) / Hc ^ (2 * f) ≤ (U.card : ℝ) := by
      rw [div_le_iff₀ (pow_pos hHcpos _)]
      calc (2:ℝ) ^ (t * f) ≤ Hc ^ (2 * f) * (U.card : ℝ) := hUlb
        _ = (U.card : ℝ) * Hc ^ (2 * f) := by ring
    rw [hAf]
    exact h1
  have hexpρ : (Real.exp (-(γ/2))) ^ f ≤ (1 - 1/(2*R)) ^ (2*f) :=
    exp_neg_le_pow (1 - 1/(2*R)) γ f hlogpos hρη
  have hkey : A₂ ^ f = A ^ f * (Real.exp (-(γ/2))) ^ f := by
    rw [hA₂_def, hA_def]
    exact (exp_halves_pow γ f).symm
  have hA₂le : A₂ ^ f ≤ (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) := by
    rw [hkey]
    exact mul_le_mul hUge hexpρ (pow_nonneg (le_of_lt (Real.exp_pos _)) f)
      (Nat.cast_nonneg U.card)
  have hA₂F : 2 * max (N : ℝ) ((2:ℝ) ^ (1/δ)) ≤ A₂ ^ F := hF F le_rfl
  have hSge : max (N : ℝ) ((2:ℝ) ^ (1/δ)) ≤ (S.card : ℝ) := by
    have h1 : 2⁻¹ * A₂ ^ F ≤ (S.card : ℝ) := by
      calc 2⁻¹ * A₂ ^ F ≤ 2⁻¹ * A₂ ^ f :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt hA₂1) hFf) (by norm_num)
        _ ≤ 2⁻¹ * ((U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f)) :=
            mul_le_mul_of_nonneg_left hA₂le (by norm_num)
        _ = 2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (2*f) := by ring
        _ ≤ (S.card : ℝ) := hstep
    calc max (N : ℝ) ((2:ℝ) ^ (1/δ)) = 2⁻¹ * (2 * max (N : ℝ) ((2:ℝ) ^ (1/δ))) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_mul]
      _ ≤ 2⁻¹ * A₂ ^ F := mul_le_mul_of_nonneg_left hA₂F (by norm_num)
      _ ≤ (S.card : ℝ) := h1
  -- ## 10. conclude with the numeric input
  refine ⟨S, ?_, ?_⟩
  · exact Nat.cast_le.mp (le_trans (le_max_left _ _) hSge)
  · refine le_trans (hnumest f (U.card : ℝ) (S.card : ℝ) hf1 hUpos hUlb hSub' ?_) hSlb'
    exact le_trans (le_max_right _ _) hSge

end Assembly
end Work
