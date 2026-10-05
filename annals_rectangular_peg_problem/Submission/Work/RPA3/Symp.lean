import Submission.Work.RPA3.TubularDefs

/-!
# RPA3: elementary symplectic algebra of `PS`

`ω = dp₁∧dq₁ + dp₂∧dq₂` is bilinear and antisymmetric; the complex structure `J(q,p) = (p,-q)`
is `ω`-compatible: `ω(Ja,Jb) = ω(a,b)`, `ω a (J b) = ⟪a,b⟫` (the standard inner product) and
`ω(a,Ja) = ⟪a,a⟫ > 0` for `a ≠ 0`.  Hence `Λ ∩ JΛ = 0` for a Lagrangian plane `Λ`, so
`(∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ)` is a basis: the linear algebra behind the tubular map `theta`.
-/

open scoped ContDiff
open Real

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

theorem symp_antisymm (a b : PS) : symp a b = -symp b a := by
  simp only [symp]; ring

@[simp] theorem symp_self (a : PS) : symp a a = 0 := by
  simp only [symp]; ring

theorem symp_neg_left (a b : PS) : symp (-a) b = -symp a b := by
  simp only [symp, Prod.fst_neg, Prod.snd_neg]; ring

theorem symp_neg_right (a b : PS) : symp a (-b) = -symp a b := by
  simp only [symp, Prod.fst_neg, Prod.snd_neg]; ring

theorem symp_add_left (a a' b : PS) : symp (a + a') b = symp a b + symp a' b := by
  simp only [symp, Prod.fst_add, Prod.snd_add]; ring

theorem symp_add_right (a b b' : PS) : symp a (b + b') = symp a b + symp a b' := by
  simp only [symp, Prod.fst_add, Prod.snd_add]; ring

theorem symp_sub_left (a a' b : PS) : symp (a - a') b = symp a b - symp a' b := by
  simp only [symp, Prod.fst_sub, Prod.snd_sub]; ring

theorem symp_sub_right (a b b' : PS) : symp a (b - b') = symp a b - symp a b' := by
  simp only [symp, Prod.fst_sub, Prod.snd_sub]; ring

theorem symp_smul_left (c : ℝ) (a b : PS) : symp (c • a) b = c * symp a b := by
  simp only [symp, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem symp_smul_right (c : ℝ) (a b : PS) : symp a (c • b) = c * symp a b := by
  simp only [symp, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

@[simp] theorem symp_J_J (a b : PS) : symp (J a) (J b) = symp a b := by
  simp only [symp, J]; ring

@[simp] theorem symp_J_self (a : PS) :
    symp a (J a) = a.1.1 ^ 2 + a.1.2 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 := by
  simp only [symp, J]; ring

/-- `ω(a, Jb)` is the standard inner product of `a` and `b`. -/
theorem symp_J_apply (a b : PS) :
    symp a (J b) = a.1.1 * b.1.1 + a.1.2 * b.1.2 + a.2.1 * b.2.1 + a.2.2 * b.2.2 := by
  simp only [symp, J]; ring

theorem symp_J_apply' (a b : PS) : symp (J a) b = -symp a (J b) := by
  simp only [symp, J]; ring

/-- `ω(Ja, a) = -⟪a,a⟫`, so `ω(a, Ja) > 0` for `a ≠ 0`. -/
theorem symp_J_left_self (a : PS) :
    symp (J a) a = -(a.1.1 ^ 2 + a.1.2 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2) := by
  simp only [symp, J]; ring

theorem symp_J_self_eq_zero_iff (a : PS) :
    symp a (J a) = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 : a.1.1 ^ 2 + a.1.2 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 0 := by
      rw [← symp_J_self a, h]
    have h1 : a.1.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a.1.1, sq_nonneg a.1.2, sq_nonneg a.2.1, sq_nonneg a.2.2])
    have h2 : a.1.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a.1.1, sq_nonneg a.1.2, sq_nonneg a.2.1, sq_nonneg a.2.2])
    have h3 : a.2.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a.1.1, sq_nonneg a.1.2, sq_nonneg a.2.1, sq_nonneg a.2.2])
    have h4 : a.2.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a.1.1, sq_nonneg a.1.2, sq_nonneg a.2.1, sq_nonneg a.2.2])
    exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  · intro h; rw [h]; simp

@[simp] theorem J_involutive (a : PS) : J (J a) = -a := by
  ext <;> simp [J]

theorem J_add (a b : PS) : J (a + b) = J a + J b := by
  ext <;> simp [J] <;> ring

theorem J_smul (c : ℝ) (a : PS) : J (c • a) = c • J a := by
  ext <;> simp [J] <;> ring

theorem J_neg (a : PS) : J (-a) = -J a := by
  ext <;> simp [J] <;> ring

/-- For a Lagrangian plane `Λ = span{u,v}`, the four vectors `u, v, Ju, Jv` are linearly
independent: `u, v` are independent by hypothesis and `Λ ∩ JΛ = 0`. -/
theorem lagrangian_independent (u v : PS)
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0)
    (hlag : symp u v = 0) :
    ∀ a b c d : ℝ, a • u + b • v + c • J u + d • J v = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro a b c d h
  have huu : symp u u = 0 := symp_self u
  have hvv : symp v v = 0 := symp_self v
  have hvu : symp v u = 0 := by rw [symp_antisymm, hlag, neg_zero]
  set w' : PS := -(c • u + d • v) with hw'
  have hsplit : a • u + b • v = -(c • J u + d • J v) := by
    have h' : (a • u + b • v) + (c • J u + d • J v) = 0 := by
      simpa only [add_assoc] using h
    exact eq_neg_iff_add_eq_zero.mpr h'
  have hw : a • u + b • v = J w' := by
    rw [hsplit, hw']
    ext <;> simp [J] <;> ring
  have hzero : symp (a • u + b • v) w' = 0 := by
    rw [hw']
    simp only [symp_add_left, symp_add_right, symp_smul_left, symp_smul_right,
      symp_neg_right, huu, hvv, hvu, hlag]
    ring
  have hinner : symp (J w') w' = 0 := by rw [← hw]; exact hzero
  have hw'0 : w' = 0 := by
    rw [symp_J_left_self] at hinner
    have h1 : w'.1.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg w'.1.1, sq_nonneg w'.1.2, sq_nonneg w'.2.1, sq_nonneg w'.2.2, hinner])
    have h2 : w'.1.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg w'.1.1, sq_nonneg w'.1.2, sq_nonneg w'.2.1, sq_nonneg w'.2.2, hinner])
    have h3 : w'.2.1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg w'.1.1, sq_nonneg w'.1.2, sq_nonneg w'.2.1, sq_nonneg w'.2.2, hinner])
    have h4 : w'.2.2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg w'.1.1, sq_nonneg w'.1.2, sq_nonneg w'.2.1, sq_nonneg w'.2.2, hinner])
    exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  have hcd : c • u + d • v = 0 := by
    have hh := hw'
    rw [hw'0] at hh
    simpa using neg_eq_zero.mp hh.symm
  obtain ⟨hc, hd⟩ := huv c d hcd
  subst hc; subst hd
  obtain ⟨ha, hb⟩ := huv a b (by rw [hsplit]; simp)
  exact ⟨ha, hb, rfl, rfl⟩

end Work.RPA3
