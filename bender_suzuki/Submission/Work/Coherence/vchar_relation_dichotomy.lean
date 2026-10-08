import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.NormIrr
import Submission.Work.Coherence.irr_cfInner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The relation `⟨v, e₂⟩ - k ⟨v, e₁⟩ = -k` for norm-one virtual characters

Let `v, e₁, e₂` be virtual characters of `G` with `⟨v,v⟩ = ⟨e₁,e₁⟩ = ⟨e₂,e₂⟩ = 1` and
`⟨e₁,e₂⟩ = 0`.  Since a virtual character of norm one is `±` an irreducible character
(`vchar_norm_one`), the pairings `⟨v,e₁⟩` and `⟨v,e₂⟩` take values in `{1, 0, -1}`
(`cfInner_mem_unit_int`).  The requested relation

  `⟨v,e₂⟩ - k ⟨v,e₁⟩ = -k`,  `k ≥ 1` integral,

therefore forces `⟨v,e₁⟩ = 1` (whence `v = e₁`) or else `k = 1` and `⟨v,e₂⟩ = -1`
(whence `v = -e₂`).  The two implications "`⟨f,g⟩ = 1` and both norms one imply `f = g`" and
"`⟨f,g⟩ = -1` and both norms one imply `f = -g`" come from the norm-zero classification
`vchar_norm_zero` applied to `f - g` resp. `f + g`.
-/

noncomputable section

open Classical

namespace Work.Coherence

variable {G : Type*} [Group G] [Fintype G]

/-- **The inner product of two virtual characters of norm one is `1`, `0` or `-1`.**
Both are `±` irreducible characters, and irreducible characters are orthonormal. -/
theorem cfInner_mem_unit_int {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g)
    (hf1 : cfInner f f = 1) (hg1 : cfInner g g = 1) :
    ∃ m : ℤ, cfInner f g = (m : ℂ) ∧ (m = 1 ∨ m = 0 ∨ m = -1) := by
  obtain ⟨χ, hχ, hfv⟩ := vchar_norm_one hf hf1
  obtain ⟨ψ, hψ, hgv⟩ := vchar_norm_one hg hg1
  have key : cfInner χ ψ = if χ = ψ then 1 else 0 := irr_cfInner hχ hψ
  rcases hfv with hfχ | hfχ <;> rcases hgv with hgψ | hgψ
  · rw [hfχ, hgψ]
    by_cases h : χ = ψ
    · exact ⟨1, by rw [key, if_pos h]; norm_num, Or.inl rfl⟩
    · exact ⟨0, by rw [key, if_neg h]; norm_num, Or.inr (Or.inl rfl)⟩
  · rw [hfχ, hgψ]
    by_cases h : χ = ψ
    · exact ⟨-1, by rw [cfInner_neg_right, key, if_pos h]; norm_num, Or.inr (Or.inr rfl)⟩
    · exact ⟨0, by rw [cfInner_neg_right, key, if_neg h]; norm_num, Or.inr (Or.inl rfl)⟩
  · rw [hfχ, hgψ]
    by_cases h : χ = ψ
    · exact ⟨-1, by rw [cfInner_neg_left, key, if_pos h]; norm_num, Or.inr (Or.inr rfl)⟩
    · exact ⟨0, by rw [cfInner_neg_left, key, if_neg h]; norm_num, Or.inr (Or.inl rfl)⟩
  · rw [hfχ, hgψ]
    by_cases h : χ = ψ
    · exact ⟨1, by rw [cfInner_neg_left, cfInner_neg_right, key, if_pos h]; norm_num,
        Or.inl rfl⟩
    · exact ⟨0, by rw [cfInner_neg_left, cfInner_neg_right, key, if_neg h]; norm_num,
        Or.inr (Or.inl rfl)⟩

/-- Two virtual characters of norm one whose inner product is `1` are equal. -/
theorem eq_of_cfInner_eq_one {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g)
    (hf1 : cfInner f f = 1) (hg1 : cfInner g g = 1) (h : cfInner f g = 1) : f = g := by
  have hsub : IsVChar (f - g) := hf.sub hg
  have hnorm : cfInner (f - g) (f - g) = 0 := by
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right]
    have hgf : cfInner g f = 1 := by rw [cfInner_conj_symm, h]; simp
    rw [hgf, h, hf1, hg1]
    norm_num
  exact sub_eq_zero.mp (vchar_norm_zero hsub hnorm)

/-- Two virtual characters of norm one whose inner product is `-1` are negatives of each
other. -/
theorem eq_neg_of_cfInner_eq_neg_one {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g)
    (hf1 : cfInner f f = 1) (hg1 : cfInner g g = 1) (h : cfInner f g = -1) : f = -g := by
  have hsum : IsVChar (f + g) := hf.add hg
  have hnorm : cfInner (f + g) (f + g) = 0 := by
    rw [cfInner_add_left, cfInner_add_right, cfInner_add_right]
    have hgf : cfInner g f = -1 := by rw [cfInner_conj_symm, h]; simp
    rw [hgf, h, hf1, hg1]
    norm_num
  exact eq_neg_of_add_eq_zero_left (vchar_norm_zero hsum hnorm)

/-- **The relation dichotomy for virtual characters.**  If `v, e₁` have norm one, `e₂` has
norm one, `e₁ ⊥ e₂`, and `⟨v,e₂⟩ - k ⟨v,e₁⟩ = -k` with `k ≥ 1`, then `v = e₁`, or else `k = 1`
and `v = -e₂`. -/
theorem vchar_relation_dichotomy {G : Type} [Group G] [Fintype G] {v e₁ e₂ : G → ℂ}
    (hv : Work.Coherence.IsVChar v) (hv1 : Work.Coherence.cfInner v v = 1)
    (he₁ : Work.Coherence.IsVChar e₁) (he₁1 : Work.Coherence.cfInner e₁ e₁ = 1)
    (he₂ : Work.Coherence.IsVChar e₂) (he₂1 : Work.Coherence.cfInner e₂ e₂ = 1)
    (h12 : Work.Coherence.cfInner e₁ e₂ = 0)
    {k : ℤ} (hk : 1 ≤ k)
    (hrel : Work.Coherence.cfInner v e₂ - (k : ℂ) * Work.Coherence.cfInner v e₁
      = -(k : ℂ)) :
    v = e₁ ∨ (k = 1 ∧ v = -e₂) := by
  obtain ⟨a, ha, haval⟩ := cfInner_mem_unit_int hv he₁ hv1 he₁1
  obtain ⟨b, hb, hbval⟩ := cfInner_mem_unit_int hv he₂ hv1 he₂1
  have hrel' : b - k * a = -k := by
    have hcast : ((b - k * a : ℤ) : ℂ) = ((-k : ℤ) : ℂ) := by
      push_cast
      rw [← hb, ← ha]
      exact hrel
    exact_mod_cast hcast
  rcases haval with ha1 | ha0 | ham1
  · left
    exact eq_of_cfInner_eq_one hv he₁ hv1 he₁1 (by rw [ha, ha1]; norm_num)
  · right
    rw [ha0] at hrel'
    simp only [mul_zero, sub_zero] at hrel'
    have hk1 : k = 1 := by rcases hbval with hb1 | hb0 | hbm1 <;> omega
    refine ⟨hk1, ?_⟩
    refine eq_neg_of_cfInner_eq_neg_one hv he₂ hv1 he₂1 ?_
    rw [hb, hrel', hk1]
    norm_num
  · exfalso
    rw [ham1] at hrel'
    have hbk : b = -2 * k := by omega
    rcases hbval with hb1 | hb0 | hbm1 <;> omega

end Work.Coherence
