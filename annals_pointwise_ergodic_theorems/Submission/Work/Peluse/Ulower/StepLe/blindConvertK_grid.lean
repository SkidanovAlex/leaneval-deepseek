/-
# Grid structure of the mixed phase, and the sign identity with the low-rank transform

Two elementary facts used by the assembly of `Work.Peluse.Ulower.StepLe.blindConvertK`:

* `weight_compl` and `gowersDiff_eq_sign_mixedPhase`: the Gowers transform
  `gowersDiff β h u v = ∑_ω (-1)^{|ω|} β u (mixv h v ω)` of `blindConvertK_lowrank` (the object
  whose *constancy* is what makes the phases blind, via `sum_blindPhase`) is, at
  `(h,u,v) = (k.2.1, k.1, k.2.2)`, exactly `(-1)^σ` times the mixed phase
  `mixedPhase β k = ∑_ω (-1)^{|ω|} β k.1 (ω ? k.2.1 : k.2.2)` of `blindInterchangeDefs` -- the two
  conventions differ by the complementation `ω ↦ ω̄` of the summation index.
* `mixedPhase_grid`: after rounding, `β' u v = round (T β u v) / T` with `0 ≤ β u v < 1`, every
  mixed phase is an integer multiple of `1/T` of modulus at most `2^σ`; hence its *fractional
  part* is `m/T` with `m ≤ T` (`mixedPhase_frac`), which is what `pinValues` consumes.
-/

import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindInterchangeDefs
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_lowrank

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- Complementation of the summation index, as an equivalence of `Fin σ → Bool`. -/
def complEquiv (σ : ℕ) : (Fin σ → Bool) ≃ (Fin σ → Bool) where
  toFun ω := fun i => !(ω i)
  invFun ω := fun i => !(ω i)
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

@[simp] lemma complEquiv_apply {σ : ℕ} (ω : Fin σ → Bool) (i : Fin σ) :
    complEquiv σ ω i = !(ω i) := rfl

@[simp] lemma complEquiv_compl {σ : ℕ} (ω : Fin σ → Bool) :
    complEquiv σ (complEquiv σ ω) = ω := (complEquiv σ).left_inv ω

/-- The complement of a Boolean pattern has complementary weight. -/
lemma weight_compl {σ : ℕ} (ω : Fin σ → Bool) :
    Work.Peluse.weight (complEquiv σ ω) + Work.Peluse.weight ω = σ := by
  have h1 : Work.Peluse.weight (complEquiv σ ω)
      = (Finset.univ.filter (fun i : Fin σ => ¬ ω i)).card := by
    rw [Work.Peluse.weight]
    congr 1
    try (ext i; simp [complEquiv_apply])
  rw [h1, Work.Peluse.weight]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin σ)))
    (p := fun i : Fin σ => ω i)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- The mixture of `(k.2.1,k.2.2)` in the convention of `mixv` at the *complemented* pattern is the
mixture in the convention of `cubeTerm`/`ThetaSet`/`mixedPhase`. -/
lemma mixv_compl_eq_mixed (σ : ℕ) (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (ω : Fin σ → Bool) :
    mixv k.2.1 k.2.2 (complEquiv σ ω)
      = fun i => if ω i = true then k.2.1 i else k.2.2 i := by
  funext i
  rw [mixv_apply, complEquiv_apply]
  rcases Bool.eq_false_or_eq_true (ω i) with h | h <;> simp [h]

/-- **The sign identity.**  At the triple `k = (u,h,v)` the low-rank transform
`gowersDiff β h u v` (the object pinned by `fibrePairs`, whose constancy makes the phases blind)
equals `(-1)^σ` times the mixed phase `mixedPhase β k` of the exchange lemma: the two conventions
differ by the complementation `ω ↦ ω̄` of the summation index. -/
theorem gowersDiff_eq_sign_mixedPhase {σ : ℕ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    gowersDiff β k.2.1 k.1 k.2.2 = (-1 : ℝ) ^ σ * mixedPhase β k := by
  have hcomp : (∑ ω : Fin σ → Bool, (-1 : ℝ) ^ Work.Peluse.weight ω *
        β k.1 (mixv k.2.1 k.2.2 ω))
      = ∑ ω : Fin σ → Bool, (-1 : ℝ) ^ Work.Peluse.weight (complEquiv σ ω) *
        β k.1 (mixv k.2.1 k.2.2 (complEquiv σ ω)) :=
    ((complEquiv σ).sum_comp
      (fun ω : Fin σ → Bool => (-1 : ℝ) ^ Work.Peluse.weight ω *
        β k.1 (mixv k.2.1 k.2.2 ω))).symm
  rw [gowersDiff, hcomp, mixedPhase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hβeq : β k.1 (mixv k.2.1 k.2.2 (complEquiv σ ω))
      = β k.1 (fun i => if ω i = true then k.2.1 i else k.2.2 i) := by
    congr 1
    exact mixv_compl_eq_mixed σ k ω
  have hsgn : (-1 : ℝ) ^ Work.Peluse.weight (complEquiv σ ω)
      = (-1 : ℝ) ^ σ * (-1 : ℝ) ^ Work.Peluse.weight ω := by
    have hw : Work.Peluse.weight (complEquiv σ ω) + Work.Peluse.weight ω = σ :=
      weight_compl ω
    have h2 : (-1 : ℝ) ^ (Work.Peluse.weight ω + Work.Peluse.weight ω) = 1 :=
      Even.neg_one_pow ⟨Work.Peluse.weight ω, by ring⟩
    have h3 : (-1 : ℝ) ^ σ * (-1 : ℝ) ^ Work.Peluse.weight ω
        = (-1 : ℝ) ^ (Work.Peluse.weight (complEquiv σ ω) + Work.Peluse.weight ω)
          * (-1 : ℝ) ^ Work.Peluse.weight ω := by rw [hw]
    rw [h3, pow_add, mul_assoc, ← pow_add, h2, mul_one]
  rw [hβeq, hsgn]
  ring

/-- The mixed phase is an integer multiple of `1/T` when the phases are. -/
lemma mixedPhase_grid {σ : ℕ} {T : ℕ} (hT : 1 ≤ T) {β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ}
    (hβ : ∀ u v, ∃ m : ℤ, β u v = (m : ℝ) / (T : ℝ))
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    ∃ m : ℤ, mixedPhase β k = (m : ℝ) / (T : ℝ) := by
  classical
  choose m hm using hβ
  set φ : (Fin σ → Bool) → (Fin σ → ℤ) :=
    fun ω => fun i => if ω i = true then k.2.1 i else k.2.2 i with hφ
  have hTne : (T : ℝ) ≠ 0 := by positivity
  refine ⟨∑ ω : Fin σ → Bool, (-1) ^ (Work.Peluse.weight ω) * m k.1 (φ ω), ?_⟩
  have key : mixedPhase β k * (T : ℝ)
      = ((∑ ω : Fin σ → Bool, (-1) ^ (Work.Peluse.weight ω) * m k.1 (φ ω) : ℤ) : ℝ) := by
    rw [mixedPhase, Finset.sum_mul, Int.cast_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hc : (((-1 : ℤ) ^ (Work.Peluse.weight ω) * m k.1 (φ ω) : ℤ) : ℝ)
        = (-1 : ℝ) ^ (Work.Peluse.weight ω) * ((m k.1 (φ ω) : ℤ) : ℝ) := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [hc, hm k.1 (φ ω)]
    field_simp
  field_simp at key ⊢
  exact key

/-- The mixed phase of a phase family with `|β| ≤ 1` stays in `[-2^σ, 2^σ]`. -/
lemma mixedPhase_abs_le {σ : ℕ} {β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ}
    (hβ : ∀ u v, |β u v| ≤ 1)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    |mixedPhase β k| ≤ ((2 : ℝ) ^ σ) := by
  have hunit : |(-1 : ℝ) ^ (Work.Peluse.weight (fun _ : Fin σ => true))| = 1 := by simp
  rw [mixedPhase]
  have hterm : ∀ ω ∈ (Finset.univ : Finset (Fin σ → Bool)),
      |(-1 : ℝ) ^ (Work.Peluse.weight ω) *
        β k.1 (fun i => if ω i = true then k.2.1 i else k.2.2 i)| ≤ 1 := by
    intro ω _
    have h1 : |(-1 : ℝ) ^ (Work.Peluse.weight ω)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_mul, h1, one_mul]
    exact hβ _ _
  have hcard : ((Finset.univ : Finset (Fin σ → Bool)).card : ℝ) = (2 : ℝ) ^ σ := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  have hsum : (∑ _ω : Fin σ → Bool, (1 : ℝ))
      = ((Finset.univ : Finset (Fin σ → Bool)).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum hterm) (le_of_eq (hsum.trans hcard)))

end

end Work.Peluse.Ulower.StepLe
