import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The scalar action of `ℚ` on `ℂ` agrees with multiplication by the cast. -/
private lemma sum_smul_eq_sum_mul {m : ℕ} (f : Fin m → ℚ) (ℓ : Fin m → ℂ) :
    ∑ i, f i • ℓ i = ∑ i, (f i : ℂ) * ℓ i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def]
  simp

/-- If `ℓ : Fin m → ℂ` is a minimal dependent family over `ℚ` (dependent as a whole, but
every subfamily obtained by deleting one index is independent), then there is a rational
relation `r` on `ℓ` with some nonzero entry, and *every* rational relation on `ℓ` is a
scalar multiple of `r`. -/
theorem exists_relation_span {m : ℕ} (ℓ : Fin m → ℂ)
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j)) :
    ∃ r : Fin m → ℚ, (∃ i, r i ≠ 0) ∧ (∑ i, (r i : ℂ) * ℓ i) = 0 ∧
      ∀ v : Fin m → ℚ, (∑ i, (v i : ℂ) * ℓ i) = 0 → ∃ c : ℚ, v = c • r := by
  classical
  -- A nonzero rational relation `r` exists, since `ℓ` is linearly dependent over `ℚ`.
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨r, hr, j, hrj⟩ := hdep
  have hr0 : ∑ i, (r i : ℂ) * ℓ i = 0 := by
    rw [← sum_smul_eq_sum_mul r ℓ]; exact hr
  refine ⟨r, ⟨j, hrj⟩, hr0, ?_⟩
  -- Every relation `v` is proportional to `r`.
  intro v hv
  have hv0 : ∑ i, v i • ℓ i = 0 := by rw [sum_smul_eq_sum_mul v ℓ]; exact hv
  set c : ℚ := v j / r j with hc
  refine ⟨c, ?_⟩
  -- `w := v - c • r` is a relation vanishing at `j`; minimality forces `w = 0`.
  set w : Fin m → ℚ := fun i => v i - c * r i with hw
  have hwj : w j = 0 := by
    simp only [hw]
    rw [hc, div_mul_cancel₀ _ hrj, sub_self]
  have hsum_w : ∑ i, w i • ℓ i = 0 := by
    have hpt : ∀ i, w i • ℓ i = v i • ℓ i - c • (r i • ℓ i) := by
      intro i
      simp only [hw]
      rw [sub_smul, ← smul_smul]
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hv0, hr, smul_zero, sub_zero]
  have hsub : ∑ x : {x : Fin m // x ≠ j}, w x • ℓ x = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.erase j) (p := fun x => x ≠ j)
          (fun x => by simp [Finset.mem_erase]) (fun x => w x • ℓ x)]
    rw [Finset.sum_erase Finset.univ (f := fun x => w x • ℓ x) (by simp [hwj])]
    exact hsum_w
  have hind : ∀ x : {x : Fin m // x ≠ j}, w x = 0 :=
    Fintype.linearIndependent_iff.mp (hmin j) (fun x => w x) hsub
  have hw0 : w = 0 := by
    funext i
    by_cases hi : i = j
    · subst hi; exact hwj
    · exact hind ⟨i, hi⟩
  funext i
  have hwi : v i - c * r i = 0 := by
    have := congr_fun hw0 i
    simpa [hw] using this
  rw [show v i = c * r i by linarith]
  simp [Pi.smul_apply]

end Work.BW
