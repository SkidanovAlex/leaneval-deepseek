import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

/-! ### Auxiliary radial-integral facts on Euclidean annuli

The two lemmas below remove the hypothesis `a ≤ b` from
`Work.CR.Flat.Cauchy.eucShell_integral_le_neg` and
`Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell`: when `b ≤ a` the annulus
`a ≤ ‖x‖ < b` is empty, and the corresponding statements are trivial. -/

/-- The Euclidean annulus `a ≤ ‖x‖ < b` is empty when `b ≤ a`. -/
lemma eucShell_eq_empty_of_le {n : ℕ} {a b : ℝ} (h : b ≤ a) :
    Work.CR.Flat.Cauchy.eucShell (n := n) a b = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x
  rw [Work.CR.Flat.Cauchy.mem_eucShell]
  rintro ⟨h1, h2⟩
  linarith

/-- `x ↦ eucNorm x ^ s` is integrable on a Euclidean annulus with inner radius `a > 0`,
with no restriction on the outer radius. -/
lemma integrableOn_eucNorm_rpow_eucShell' {n : ℕ} {s a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.eucNorm x ^ s)
      (Work.CR.Flat.Cauchy.eucShell (n := n) a b) volume := by
  by_cases hab : a ≤ b
  · exact Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell ha hab
  · rw [eucShell_eq_empty_of_le (le_of_lt (not_le.mp hab))]
    exact integrableOn_empty

/-- For `s + 2n < 0` the integral of `eucNorm ^ s` over an annulus with inner radius `a > 0`
is bounded by `C * a ^ (s + 2n)`, with no restriction on the outer radius. -/
lemma eucShell_integral_le_neg' {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hs : s + 2 * (n : ℝ) < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b : ℝ}, 0 < a →
      ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) a b,
        (Work.CR.Flat.Cauchy.eucNorm x) ^ s ≤ C * a ^ (s + 2 * (n : ℝ)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.CR.Flat.Cauchy.eucShell_integral_le_neg hn hs
  refine ⟨C0, hC0pos, ?_⟩
  intro a b ha
  by_cases hab : a ≤ b
  · exact hC0 ha hab
  · rw [eucShell_eq_empty_of_le (le_of_lt (not_le.mp hab)), setIntegral_empty]
    exact le_of_lt (mul_pos hC0pos (Real.rpow_pos_of_pos ha _))

/-! ### The pointwise far-field bound -/

/-- Pointwise bound for the far-field integrand: on the annulus `2η ≤ ‖x‖` the difference
`Φ x - Φ (x - h)` is `O(η ‖x‖^{-2n-1})` and the Hölder difference of `g` is
`O(‖x‖^α)`, giving `O(η ‖x‖^{α-2n-1})`. -/
lemma czFar_pointwise {n : ℕ} {α : ℝ} (hα : 0 < α) {A : ℝ} (hA : 0 < A)
    {Φ : (Fin n → ℂ) → ℂ} {h z : Fin n → ℂ} {K η : ℝ} (hK : 0 ≤ K) (hη : 0 < η)
    (hh : Work.CR.Flat.Cauchy.eucNorm h = η)
    (hΦ : ∀ x h' : Fin n → ℂ,
      2 * Work.CR.Flat.Cauchy.eucNorm h' ≤ Work.CR.Flat.Cauchy.eucNorm x →
      ‖Φ (x - h') - Φ x‖ ≤ A * Work.CR.Flat.Cauchy.eucNorm h'
        / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1))
    {g : (Fin n → ℂ) → ℂ} (hg : ∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α)
    {x : Fin n → ℂ} (hx : 2 * η ≤ Work.CR.Flat.Cauchy.eucNorm x) :
    ‖(Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖
      ≤ 2 ^ α * A * K * η * (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1) := by
  have hNpos : 0 < Work.CR.Flat.Cauchy.eucNorm x := lt_of_lt_of_le (by linarith) hx
  have hNnn : 0 ≤ Work.CR.Flat.Cauchy.eucNorm x := le_of_lt hNpos
  have hΦb : ‖Φ x - Φ (x - h)‖
      ≤ A * η / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1) := by
    have hc := hΦ x h (by rw [hh]; exact hx)
    rwa [norm_sub_rev, hh] at hc
  have hΦnn : 0 ≤ A * η / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1) :=
    div_nonneg (mul_nonneg hA.le hη.le) (pow_nonneg hNnn _)
  have hgb : ‖g (z + x) - g (z + h)‖
      ≤ K * (2 ^ α * (Work.CR.Flat.Cauchy.eucNorm x) ^ α) := by
    have hc := hg (z + x) (z + h)
    have he : z + x - (z + h) = x - h := by abel
    rw [he] at hc
    have hxb : ‖x - h‖ ≤ 2 * Work.CR.Flat.Cauchy.eucNorm x := by
      calc ‖x - h‖ ≤ ‖x‖ + ‖h‖ := norm_sub_le x h
        _ ≤ Work.CR.Flat.Cauchy.eucNorm x + η :=
            add_le_add (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm x)
              (le_trans (Work.CR.Flat.Cauchy.pi_norm_le_eucNorm h) (le_of_eq hh))
        _ ≤ Work.CR.Flat.Cauchy.eucNorm x + Work.CR.Flat.Cauchy.eucNorm x := by linarith
        _ = 2 * Work.CR.Flat.Cauchy.eucNorm x := by ring
    calc ‖g (z + x) - g (z + h)‖ ≤ K * ‖x - h‖ ^ α := hc
      _ ≤ K * (2 * Work.CR.Flat.Cauchy.eucNorm x) ^ α :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg _) hxb (le_of_lt hα)) hK
      _ = K * (2 ^ α * (Work.CR.Flat.Cauchy.eucNorm x) ^ α) := by
            rw [Real.mul_rpow (x := (2 : ℝ)) (y := Work.CR.Flat.Cauchy.eucNorm x) (z := α) (by norm_num) hNnn]
  rw [norm_mul]
  refine (mul_le_mul hΦb hgb (norm_nonneg _) hΦnn).trans_eq ?_
  have hrw : (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1)
      = (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * (n : ℝ) + 1) := by
    rw [← Real.rpow_natCast (Work.CR.Flat.Cauchy.eucNorm x) (2 * n + 1)]
    congr 1
    push_cast
    ring
  have hsub : (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1)
      = (Work.CR.Flat.Cauchy.eucNorm x) ^ α
          / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * (n : ℝ) + 1) := by
    rw [show α - 2 * (n : ℝ) - 1 = α - (2 * (n : ℝ) + 1) from by ring]
    exact Real.rpow_sub hNpos α _
  rw [hrw, hsub]
  have hNne : (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * (n : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hNpos (2 * (n : ℝ) + 1))
  field_simp

/-! ### The far-field kernel difference estimate -/

theorem czFarKernelDiff {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : (Fin n → ℂ) → ℂ} {h z : Fin n → ℂ} {K η : ℝ}, 0 ≤ K → 0 < η →
      Work.CR.Flat.Cauchy.eucNorm h = η →
      (∀ x h' : Fin n → ℂ, 2 * Work.CR.Flat.Cauchy.eucNorm h' ≤ Work.CR.Flat.Cauchy.eucNorm x →
        ‖Φ (x - h') - Φ x‖
          ≤ A * Work.CR.Flat.Cauchy.eucNorm h'
              / (Work.CR.Flat.Cauchy.eucNorm x) ^ (2 * n + 1)) →
      ∀ {g : (Fin n → ℂ) → ℂ}, (∀ x y : Fin n → ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      ‖∫ x in Work.CR.Flat.Cauchy.eucShell (2 * η) (4 * R),
          (Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖ ≤ C * A * K * η ^ α := by
  have hneg : (α - 2 * (n : ℝ) - 1) + 2 * (n : ℝ) < 0 := by linarith
  obtain ⟨C0, hC0pos, hC0⟩ :=
    eucShell_integral_le_neg' (n := n) (s := α - 2 * (n : ℝ) - 1) hn hneg
  refine ⟨2 ^ α * C0 * 2 ^ (α - 1) + 1, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) α) hC0pos)
        (Real.rpow_pos_of_pos (by norm_num) (α - 1))) zero_le_one
  intro Φ h z K η hK hη hh hΦ g hg
  have h2η : 0 < 2 * η := by linarith
  have hInt : IntegrableOn
      (fun x : Fin n → ℂ =>
        2 ^ α * A * K * η * (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1))
      (Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R)) volume :=
    (integrableOn_eucNorm_rpow_eucShell' (n := n) (s := α - 2 * (n : ℝ) - 1)
      (a := 2 * η) (b := 4 * R) h2η).integrable.const_mul _
  have hcK : 0 ≤ 2 ^ α * A * K * η :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) α) hA.le) hK) hη.le
  have hpt : ∀ x ∈ Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
      ‖(Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖
        ≤ 2 ^ α * A * K * η * (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1) :=
    fun x hx => czFar_pointwise hα hA hK hη hh hΦ hg hx.1
  have hstep2 : (∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
        ‖(Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖)
      ≤ ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
        2 ^ α * A * K * η * (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1) :=
    setIntegral_mono_of_nonneg (fun x _ => norm_nonneg _) hpt hInt
  have hshell := hC0 (a := 2 * η) (b := 4 * R) h2η
  have hs_exp : (α - 2 * (n : ℝ) - 1) + 2 * (n : ℝ) = α - 1 := by ring
  have hmulval : (2 : ℝ) ^ α * A * K * η
        * (C0 * (2 * η) ^ ((α - 2 * (n : ℝ) - 1) + 2 * (n : ℝ)))
      = (2 ^ α * C0 * 2 ^ (α - 1)) * (A * K * η ^ α) := by
    rw [hs_exp, Real.mul_rpow (x := (2 : ℝ)) (y := η) (z := α - 1) (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hη)]
    have heta : η * η ^ (α - 1) = η ^ α := by
      rw [show η * η ^ (α - 1) = η ^ (1 : ℝ) * η ^ (α - 1) from by rw [Real.rpow_one],
          ← Real.rpow_add hη 1 (α - 1), show (1 : ℝ) + (α - 1) = α from by ring]
    have hstep : (2 : ℝ) ^ α * A * K * η * (C0 * ((2 : ℝ) ^ (α - 1) * η ^ (α - 1)))
        = (2 ^ α * C0 * 2 ^ (α - 1)) * (A * K * (η * η ^ (α - 1))) := by ring_nf
    rw [hstep, heta]
  calc ‖∫ x in Work.CR.Flat.Cauchy.eucShell (2 * η) (4 * R),
        (Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖
      ≤ ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
          ‖(Φ x - Φ (x - h)) * (g (z + x) - g (z + h))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
          2 ^ α * A * K * η * (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1) :=
        hstep2
    _ = (2 ^ α * A * K * η) * ∫ x in Work.CR.Flat.Cauchy.eucShell (n := n) (2 * η) (4 * R),
          (Work.CR.Flat.Cauchy.eucNorm x) ^ (α - 2 * (n : ℝ) - 1) := by
        rw [integral_const_mul]
    _ ≤ (2 ^ α * A * K * η)
          * (C0 * (2 * η) ^ ((α - 2 * (n : ℝ) - 1) + 2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hshell hcK
    _ = (2 ^ α * C0 * 2 ^ (α - 1)) * (A * K * η ^ α) := hmulval
    _ ≤ (2 ^ α * C0 * 2 ^ (α - 1) + 1) * A * K * η ^ α := by
        rw [show (2 ^ α * C0 * 2 ^ (α - 1) + 1) * A * K * η ^ α
              = (2 ^ α * C0 * 2 ^ (α - 1) + 1) * (A * K * η ^ α) from by ring]
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))
          (mul_nonneg (mul_nonneg hA.le hK) (Real.rpow_nonneg hη.le α))

end Work.CR.Flat.Cauchy.bmCz
