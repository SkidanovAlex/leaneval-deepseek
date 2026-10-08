import Mathlib
import Submission.Work.Coherence.Inner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The sum of squared norms of `cfInner` against a prescribed set

If `cfInner T (e y)` takes the value `c - a` at the single point `y₀` of a finite index set `S`
and the value `c` at every other point of `S`, then the sum over `S` of the squared norms is
`(c - a) ^ 2 + (|S| - 1) * c ^ 2`.  This is the elementary bookkeeping step behind the
two-block norm computations.
-/

namespace Work.FeitSibley.Coherence

/-- The squared norm of an integer, viewed in `ℂ`, is the square of that integer, viewed in `ℝ`. -/
private lemma normSq_intCast_sq (n : ℤ) : Complex.normSq (n : ℂ) = ((n ^ 2 : ℤ) : ℝ) := by
  rw [Complex.normSq_intCast]
  push_cast
  ring

/-- The squared norm of `c - a` for an integer `c` and a natural `a`. -/
private lemma normSq_sub_natCast_sq (c : ℤ) (a : ℕ) :
    Complex.normSq ((c : ℂ) - (a : ℂ)) = (((c - a) ^ 2 : ℤ) : ℝ) := by
  rw [show (c : ℂ) - (a : ℂ) = ((c - (a : ℤ) : ℤ) : ℂ) by push_cast; ring]
  exact normSq_intCast_sq (c - (a : ℤ))

theorem sum_normSq_cfInner_eq {G ι : Type*} [Fintype G] [DecidableEq ι]
    (S : Finset ι) (e : ι → G → ℂ) (T : G → ℂ) {y₀ : ι} (hy₀ : y₀ ∈ S)
    (c : ℤ) (a : ℕ)
    (hc : ∀ y ∈ S, Work.Coherence.cfInner T (e y) =
      if y = y₀ then (c : ℂ) - (a : ℂ) else (c : ℂ)) :
    ∑ y ∈ S, Complex.normSq (Work.Coherence.cfInner T (e y))
      = (((c - a) ^ 2 + ((S.card : ℤ) - 1) * c ^ 2 : ℤ) : ℝ) := by
  rw [← Finset.add_sum_erase S (fun y => Complex.normSq (Work.Coherence.cfInner T (e y))) hy₀]
  have h0 : Complex.normSq (Work.Coherence.cfInner T (e y₀)) = (((c - a) ^ 2 : ℤ) : ℝ) := by
    rw [hc y₀ hy₀, ite_eq_left rfl]
    exact normSq_sub_natCast_sq c a
  have h1 : ∑ y ∈ S.erase y₀, Complex.normSq (Work.Coherence.cfInner T (e y))
      = ∑ _y ∈ S.erase y₀, ((c ^ 2 : ℤ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
    rw [hc y hyS, ite_eq_right hne]
    exact normSq_intCast_sq c
  rw [h0, h1, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((S.erase y₀).card : ℝ) = (S.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hy₀]
    have h1le : 1 ≤ S.card := Finset.card_pos.mpr ⟨y₀, hy₀⟩
    rw [Nat.cast_sub h1le, Nat.cast_one]
  rw [hcard]
  push_cast
  ring

end Work.FeitSibley.Coherence
