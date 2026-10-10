import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.WtDefs
import Submission.Work.MotV5.WtAux
import Submission.Work.MotV5.dvd_kleinQ
import Submission.Work.MotV5.wt_argmax_unique
import Submission.Work.MotV5.topPart_kleinQPoly
import Submission.Work.MotV5.topPart_asPolyF_mul_gen
import Submission.Work.MotV5.natDegree_kleinQPoly_le

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

namespace Work.MotV5

open Polynomial

/-! ## Bookkeeping helpers for the assembly of `tp_as` -/

/-- The Artin–Schreier polynomial `T⁵ - T - g` of a field is nonzero. -/
theorem asPolyF_ne_zero' {F : Type*} [Field F] (g : F) : asPolyF g ≠ 0 := by
  intro h
  have h5 := asPolyF_natDegree (F := F) g
  rw [h] at h5
  exact absurd h5 (by simp)

/-- `natDegree (polyOf y) ≤ 4`. -/
theorem natDegree_polyOf_le' {F : Type*} [CommRing F] (y : Fin 5 → F) :
    (polyOf y).natDegree ≤ 4 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [polyOf_coeff, dite_eq_right (by omega)]

/-- If `f : ℕ → F` has a unique maximal weight at index `i₀` (in the sense of `wt`), then
`f i₀ ≠ 0`. -/
theorem wt_max_coeff_ne_zero {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {g : F} {f : ℕ → F} {i₀ : ℕ}
    (hmax : ∀ i, wt v g (f i) i ≤ wt v g (f i₀) i₀)
    (huniq : ∀ i, wt v g (f i) i = wt v g (f i₀) i₀ → i = i₀) :
    f i₀ ≠ 0 := by
  intro h0
  have hW0 : wt v g (f i₀) i₀ = 0 := by rw [h0]; simp [wt]
  have hall : ∀ i, wt v g (f i) i = 0 := fun i =>
    le_antisymm (by rw [← hW0]; exact hmax i) zero_le
  exact absurd (huniq (i₀ + 1) (by rw [hall (i₀ + 1), hall i₀])) (by omega)

/-! ## The theorem -/

theorem tp_as {F L Γ₀ : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (w : L) (g : F)
    (hw : w ^ 5 - w = algebraMap F L g) {a b : F} (ha : v a = 1) (hb : v b = 1)
    (hab : v (a ^ 2 - a * b - b ^ 2) = 1) {y : Fin 5 → F} (hy : y ≠ 0)
    (heq : ∀ k, Work.MotK.kleinP (algebraMap F L a) (algebraMap F L b)
      (Work.MotV.asCoord w (fun j => algebraMap F L (y j))) k = 0)
    (hg : 1 < v g) : ∃ u : F, v g = v u ^ 5 := by
  by_contra hcon
  have hg0 : v g ≠ 0 := ne_of_gt (lt_trans zero_lt_one hg)
  -- the unique heaviest monomial of `y`
  obtain ⟨l₀, hl₀max, hl₀uniq⟩ := wt_argmax_unique (v := v) hcon hy
  have huniq : ∀ l : Fin 5, wt v g (y l) l = wt v g (y l₀) l₀ → l = l₀ :=
    fun l hl => hl₀uniq l (fun l' => by rw [hl]; exact hl₀max l')
  have hy₀ : y l₀ ≠ 0 := y_l₀_ne_zero v hl₀max huniq
  have hM_ne : wt v g (y l₀) l₀ ≠ 0 :=
    fun h => hy₀ ((wt_eq_zero_iff v hg0 (y l₀) (l₀ : ℕ)).mp h)
  -- the divisibility coming from `heq`
  obtain ⟨A, hA⟩ := dvd_kleinQ w g hw a b y heq
  -- the top part of the Klein polynomial
  obtain ⟨htopQ, hwtQ⟩ := topPart_kleinQPoly (v := v) hg ha hb hab hl₀max huniq
  have hq_ne : (kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ)) ≠ 0 := by
    intro h
    have hmul : wt v g (y l₀) l₀ * wt v g (y l₀) l₀ ≠ 0 := mul_ne_zero hM_ne hM_ne
    apply hmul
    rw [← hwtQ, h, wt]
    simp
  have hQ_ne : kleinQPoly a b (polyOf y) ≠ 0 := by
    intro h
    exact hq_ne (by rw [h]; simp)
  have hA_ne : A ≠ 0 := by
    intro h0
    exact hQ_ne (by rw [hA, h0, mul_zero])
  -- degree bound on `A`
  have hdegA : A.natDegree ≤ 3 := by
    have h1 : (kleinQPoly a b (polyOf y)).natDegree ≤ 2 * (polyOf y).natDegree :=
      natDegree_kleinQPoly_le a b (polyOf y)
    have h2 : (polyOf y).natDegree ≤ 4 := natDegree_polyOf_le' y
    rw [hA] at h1
    rw [Polynomial.natDegree_mul (asPolyF_ne_zero' g) hA_ne, asPolyF_natDegree] at h1
    omega
  -- the unique heaviest monomial of `A`
  have hyA : (fun i : Fin 5 => A.coeff (i : ℕ)) ≠ 0 := by
    intro h
    apply hA_ne
    ext n
    rcases lt_or_ge n 5 with hn | hn
    · have h' := congrFun h ⟨n, hn⟩
      simpa using h'
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨i₀, hi₀max, hi₀uniq⟩ := wt_argmax_unique (v := v) hcon hyA
  have hi₁ : ∀ i : ℕ, wt v g (A.coeff i) i ≤ wt v g (A.coeff (i₀ : ℕ)) (i₀ : ℕ) := by
    intro i
    rcases lt_or_ge i 5 with hi | hi
    · exact hi₀max ⟨i, hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), wt]
      simp only [map_zero, zero_pow (by norm_num : (5 : ℕ) ≠ 0), mul_zero]
      exact zero_le
  have hi₁uniq : ∀ i : ℕ, wt v g (A.coeff i) i = wt v g (A.coeff (i₀ : ℕ)) (i₀ : ℕ) → i = i₀ := by
    intro i hi
    rcases lt_or_ge i 5 with hi5 | hi5
    · have key : ∀ l' : Fin 5, wt v g (A.coeff (l' : ℕ)) (l' : ℕ) ≤ wt v g (A.coeff i) i := by
        intro l'
        have hl' := hi₁ (l' : ℕ)
        rw [← hi] at hl'
        exact hl'
      exact congrArg Fin.val (hi₀uniq ⟨i, hi5⟩ key)
    · exfalso
      have hi0 : A.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hW0 : wt v g (A.coeff (i₀ : ℕ)) (i₀ : ℕ) = 0 := by
        rw [← hi, hi0, wt]; simp
      refine hyA (funext fun j => ?_)
      refine (wt_eq_zero_iff v hg0 (A.coeff (j : ℕ)) (j : ℕ)).mp ?_
      refine le_antisymm (by rw [← hW0]; exact hi₁ (j : ℕ)) zero_le
  -- the top part of `asPolyF g * A`
  obtain ⟨htopA, hneA, hwtA⟩ := topPart_asPolyF_mul_gen (v := v) (g := g) hg hi₁ hi₁uniq
  -- compare the two descriptions of `topPart Q`
  have hkey : C ((asPolyF g * A).coeff ((i₀ : ℕ) + 5)) * X ^ ((i₀ : ℕ) + 5)
        + C ((asPolyF g * A).coeff (i₀ : ℕ)) * X ^ (i₀ : ℕ)
      = C ((kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ))) * X ^ (2 * (l₀ : ℕ)) := by
    rw [← htopA, ← htopQ, hA]
  -- the coefficient of `X^(i₀+5)`
  have hβ : ((i₀ : ℕ) + 5 = 2 * (l₀ : ℕ)) := by
    have h1 := congrArg (fun p : Polynomial F => p.coeff ((i₀ : ℕ) + 5)) hkey
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, ite_true] at h1
    rw [ite_eq_right (by omega : ¬ ((i₀ : ℕ) + 5 = (i₀ : ℕ))), add_zero] at h1
    by_contra hne
    rw [ite_eq_right hne] at h1
    exact hneA h1
  -- the coefficient of `X^i₀`
  have hδ : (asPolyF g * A).coeff (i₀ : ℕ) = 0 := by
    have h1 := congrArg (fun p : Polynomial F => p.coeff (i₀ : ℕ)) hkey
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, ite_true] at h1
    rw [ite_eq_right (by omega : ¬ ((i₀ : ℕ) = (i₀ : ℕ) + 5)), zero_add] at h1
    rw [ite_eq_right (by omega : ¬ ((i₀ : ℕ) = 2 * (l₀ : ℕ)))] at h1
    exact h1
  -- but that coefficient is the heaviest one and nonzero
  have hAi0 : A.coeff (i₀ : ℕ) ≠ 0 := wt_max_coeff_ne_zero v hi₁ hi₁uniq
  have hwti₀ : wt v g (A.coeff (i₀ : ℕ)) (i₀ : ℕ) ≠ 0 :=
    fun h => hAi0 ((wt_eq_zero_iff v hg0 (A.coeff (i₀ : ℕ)) (i₀ : ℕ)).mp h)
  have hwtδ : wt v g ((asPolyF g * A).coeff (i₀ : ℕ)) (i₀ : ℕ) ≠ 0 := by
    intro hzero
    rw [hwtA] at hzero
    exact mul_ne_zero (pow_ne_zero 5 hg0) hwti₀ hzero
  exact hwtδ (by rw [hδ]; exact wt_zero v g 0 (i₀ : ℕ) rfl)

end Work.MotV5
