/-
  Work.WilE2 — area E2.  The Rolle counting step of the Khovanskii elimination.

  The elimination step replaces the last chain function by a new coordinate and adds the
  equation `M = δ`, where `M` is the Khovanskii–Rolle determinant.  The analytic content of
  the step is the following one-dimensional fact: along the compact curve `C` on which the
  lifted system lives, each root `z` (a point where the old system holds) has an "oriented
  crossing" whose sign is the sign of `M(z)`; consecutive crossings have opposite signs, and
  therefore the level set `{M = δ}` for any small `δ > 0` meets the curve in at least as many
  points as there are roots.

  This module isolates the *counting* part, which is pure one-variable calculus: it is stated
  for a continuous `T`-periodic function `w` (the transport of `M` along an oriented
  parametrization of the curve) whose values at the roots alternate in sign.  The geometric
  input — the existence of the oriented periodic parametrization — is the content of
  `Work.WilE2.CurveParam` (see `STATUS.md`).
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical Set
namespace Work.WilE2

/-! ## §1. The cyclic successor -/

/-- The cyclic successor on `Fin p` (`p ≥ 1`). -/
def cycSucc {p : ℕ} (hp : 0 < p) (i : Fin p) : Fin p :=
  if h : (i : ℕ) + 1 < p then ⟨(i : ℕ) + 1, h⟩ else ⟨0, hp⟩

theorem cycSucc_val {p : ℕ} (hp : 0 < p) (i : Fin p) :
    (cycSucc hp i : ℕ) = if (i : ℕ) + 1 < p then (i : ℕ) + 1 else 0 := by
  rw [cycSucc]; split_ifs <;> rfl

theorem cycSucc_of_lt {p : ℕ} (hp : 0 < p) (i : Fin p) (h : (i : ℕ) + 1 < p) :
    (cycSucc hp i).val = (i : ℕ) + 1 := by
  rw [cycSucc_val, if_pos h]

theorem cycSucc_of_not_lt {p : ℕ} (hp : 0 < p) (i : Fin p) (h : ¬ (i : ℕ) + 1 < p) :
    cycSucc hp i = ⟨0, hp⟩ := by
  rw [cycSucc, dif_neg h]

/-- The index `i` with `i.val + 1 = p`, i.e. the last index. -/
theorem eq_last_of_not_lt {p : ℕ} (hp : 0 < p) {i : Fin p} (h : ¬ (i : ℕ) + 1 < p) :
    (i : ℕ) = p - 1 := by
  have := i.isLt
  omega

/-! ## §2. The intermediate value theorem, in the form used below -/

variable {w : ℝ → ℝ}

/-- A continuous function on `[a,b]` whose endpoint values bracket `δ` strictly takes the value
`δ` at an interior point. -/
theorem exists_eq_Ioo_of_bracket {w : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn w (Set.Icc a b)) (ha : w a ≠ δ) (hb : w b ≠ δ)
    (h : δ ∈ Set.Icc (w a) (w b) ∪ Set.Icc (w b) (w a)) :
    ∃ c ∈ Set.Ioo a b, w c = δ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨c, hc, hwc⟩ := (intermediate_value_Icc hab hcont) ⟨h1, h2⟩
    refine ⟨c, ⟨?_, ?_⟩, hwc⟩
    · exact lt_of_le_of_ne hc.1 (fun hh => ha (by rw [← hh] at hwc; exact hwc))
    · exact lt_of_le_of_ne hc.2 (fun hh => hb (by rw [hh] at hwc; exact hwc))
  · obtain ⟨c, hc, hwc⟩ := (intermediate_value_Icc' hab hcont) ⟨h1, h2⟩
    refine ⟨c, ⟨?_, ?_⟩, hwc⟩
    · exact lt_of_le_of_ne hc.1 (fun hh => ha (by rw [← hh] at hwc; exact hwc))
    · exact lt_of_le_of_ne hc.2 (fun hh => hb (by rw [hh] at hwc; exact hwc))

/-! ## §3. The Rolle counting step -/

/-- Auxiliary: if `w a` and `w b` have opposite signs and both exceed `δ` in absolute value,
then `δ` is bracketed. -/
theorem bracket_of_mul_neg {a b δ : ℝ} (hδ : 0 < δ) (h : w a * w b < 0)
    (ha : δ < |w a|) (hb : δ < |w b|) :
    δ ∈ Set.Icc (w a) (w b) ∪ Set.Icc (w b) (w a) := by
  rcases lt_trichotomy (w a) 0 with h1 | h1 | h1
  · have h2 : 0 < w b := by nlinarith
    have hb' : δ < w b := by rwa [abs_of_pos h2] at hb
    exact Or.inl ⟨le_of_lt (by linarith), le_of_lt hb'⟩
  · rw [h1, zero_mul] at h; exact absurd h (lt_irrefl 0)
  · have h2 : w b < 0 := by nlinarith
    have ha' : δ < w a := by rwa [abs_of_pos h1] at ha
    exact Or.inr ⟨le_of_lt (by linarith), le_of_lt ha'⟩

/-- Auxiliary: the value of `w` at a root is not `δ`. -/
theorem ne_delta_of_lt_abs {t δ : ℝ} (hδ : 0 < δ) (h : δ < |w t|) : w t ≠ δ := by
  intro hh
  rw [hh, abs_of_pos hδ] at h
  exact lt_irrefl δ h

/-- **Rolle counting along a closed curve.**  Let `w` be continuous on `[t 0, t 0 + T]`.  Let
`t : ℤ → ℝ` enumerate the roots of the "old" system along an oriented parametrization of
the curve, increasingly and periodically (`t (i+p) = t i + T`).  Assume that the values of `w` at
consecutive roots have opposite signs and all exceed `δ` in absolute value.  Then there are at
least `p` distinct points at which `w = δ`.

This is the counting content of the Khovanskii–Rolle step: `w` is the transport of the Rolle
determinant `M` along the parametrization, and the roots of the old system are transported to
the points `t i`. -/
theorem rolle_count {p : ℕ} (hp : 0 < p) (T : ℝ) (hT : 0 < T)
    (t : ℤ → ℝ) (hshift : ∀ i : ℤ, t (i + p) = t i + T) (hmono : StrictMono t)
    (hcont : ContinuousOn w (Set.Icc (t 0) (t 0 + T)))
    (δ : ℝ) (hδ : 0 < δ) (hδlt : ∀ i : ℤ, δ < |w (t i)|)
    (halt : ∀ i : ℤ, w (t i) * w (t (i + 1)) < 0) :
    ∃ S : Finset ℝ, (∀ s ∈ S, w s = δ) ∧ p ≤ S.card := by
  classical
  have htp : t (0 + (p : ℤ)) = t 0 + T := hshift 0
  have hpt : ∀ i : Fin p, ∃ c ∈ Set.Ioo (t (i : ℤ)) (t ((i : ℤ) + 1)), w c = δ := by
    intro i
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
    have hip : ((i : ℤ) + 1) ≤ (p : ℤ) := by
      have := i.isLt
      omega
    have hab : t (i : ℤ) ≤ t ((i : ℤ) + 1) := hmono.monotone (by omega)
    have hsub : Set.Icc (t (i : ℤ)) (t ((i : ℤ) + 1)) ⊆ Set.Icc (t 0) (t 0 + T) := by
      intro x hx
      refine ⟨le_trans (hmono.monotone hi0) hx.1, ?_⟩
      have h1 : t ((i : ℤ) + 1) ≤ t (0 + (p : ℤ)) := hmono.monotone (by omega)
      rw [htp] at h1
      exact le_trans hx.2 h1
    exact exists_eq_Ioo_of_bracket hab (hcont.mono hsub)
      (ne_delta_of_lt_abs hδ (hδlt _)) (ne_delta_of_lt_abs hδ (hδlt _))
      (bracket_of_mul_neg hδ (halt _) (hδlt _) (hδlt _))
  choose c hc hcw using hpt
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun hh => hne (Fin.ext hh)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have hmono' : (i : ℤ) < (j : ℤ) := by exact_mod_cast hlt
      have h1 : t ((i : ℤ) + 1) ≤ t (j : ℤ) := hmono.monotone (by omega)
      have h2 : c i < t ((i : ℤ) + 1) := (hc i).2
      have h3 : t (j : ℤ) < c j := (hc j).1
      rw [← hij] at h3
      linarith
    · have hmono' : (j : ℤ) < (i : ℤ) := by exact_mod_cast hlt
      have h1 : t ((j : ℤ) + 1) ≤ t (i : ℤ) := hmono.monotone (by omega)
      have h2 : c j < t ((j : ℤ) + 1) := (hc j).2
      have h3 : t (i : ℤ) < c i := (hc i).1
      rw [hij] at h3
      linarith
  refine ⟨Finset.univ.image c, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact hcw i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

end Work.WilE2
