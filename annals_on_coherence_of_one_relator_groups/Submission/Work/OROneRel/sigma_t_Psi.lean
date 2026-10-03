import Mathlib
import Submission.Work.OROneRel.psiSubstDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The `n`-th power map `y ↦ y ^ n` on `Multiplicative ℤ`, as a monoid homomorphism. -/
noncomputable def powIntHom (n : ℤ) : Multiplicative ℤ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun y => y ^ n) (fun y z => mul_zpow y z n)

@[simp] theorem powIntHom_apply (n : ℤ) (y : Multiplicative ℤ) :
    powIntHom n y = y ^ n := rfl

section Base

variable {t s : α}

@[simp] theorem sigma_of_of_eq : sigma t (FreeGroup.of t) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [Work.OROneRel.sigma, FreeGroup.lift_apply_of]
  simp

theorem sigma_of_of_ne (h : s ≠ t) : sigma t (FreeGroup.of s) = 1 := by
  rw [Work.OROneRel.sigma, FreeGroup.lift_apply_of, if_neg h]

@[simp] theorem ofAdd_one_zpow (n : ℤ) :
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ n) = Multiplicative.ofAdd n := by
  rw [← ofAdd_zsmul]
  simp

end Base

/-- For `u v : Multiplicative ℤ` one has `u ^ v.toAdd * v ^ (- u.toAdd) = 1`. -/
theorem mul_zpow_toAdd (u v : Multiplicative ℤ) :
    u ^ (Multiplicative.toAdd v) * v ^ (-(Multiplicative.toAdd u)) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_zpow, toAdd_zpow, toAdd_one, smul_eq_mul, smul_eq_mul]
  ring

/-- The generator map whose lift is `sigma t ∘ Psi r t x`: it sends `t` to `(sigma x r).toAdd`
and `x` to `-(sigma t r).toAdd`, and kills every other generator. -/
noncomputable def PsiWeight (r : FreeGroup α) (t x : α) : α → Multiplicative ℤ := by
  classical
  exact fun s =>
    if s = t then Multiplicative.ofAdd ((sigma x r).toAdd)
    else if s = x then Multiplicative.ofAdd (-(sigma t r).toAdd)
    else 1

@[simp] theorem PsiWeight_self (r : FreeGroup α) (t x : α) :
    PsiWeight r t x t = Multiplicative.ofAdd ((sigma x r).toAdd) := by
  classical
  simp [PsiWeight]

@[simp] theorem PsiWeight_eq_x (r : FreeGroup α) {t x : α} (htx : x ≠ t) :
    PsiWeight r t x x = Multiplicative.ofAdd (-(sigma t r).toAdd) := by
  classical
  simp [PsiWeight, htx]

@[simp] theorem PsiWeight_of_ne (r : FreeGroup α) {t x s : α} (hst : s ≠ t) (hsx : s ≠ x) :
    PsiWeight r t x s = 1 := by
  classical
  simp [PsiWeight, hst, hsx]

theorem sigma_t_Psi {α : Type*} (r : FreeGroup α) (t x : α) (htx : x ≠ t) :
    Work.OROneRel.sigma t (Work.OROneRel.Psi r t x r) = 1 := by
  classical
  have hgen : ∀ s : α, ((sigma t).comp (Psi r t x)) (FreeGroup.of s) = PsiWeight r t x s := by
    intro s
    rw [MonoidHom.comp_apply]
    by_cases hst : s = t
    · subst hst
      rw [Psi_of_eq_t, map_zpow, sigma_of_of_eq, ofAdd_one_zpow, PsiWeight_self]
    · by_cases hsx : s = x
      · subst hsx
        rw [Psi_of_eq_x htx, map_mul, map_zpow, sigma_of_of_eq, sigma_of_of_ne htx,
          ofAdd_one_zpow, PsiWeight_eq_x r htx, one_mul]
      · rw [Psi_of_ne hst hsx, sigma_of_of_ne hst, PsiWeight_of_ne r hst hsx]
  have hmain : sigma t (Psi r t x r) = FreeGroup.lift (PsiWeight r t x) r :=
    FreeGroup.lift_unique (f := PsiWeight r t x) ((sigma t).comp (Psi r t x)) hgen
  rw [hmain]
  have hgenZ : ∀ s : α,
      ((powIntHom ((sigma x r).toAdd)).comp (sigma t) *
        (powIntHom (-(sigma t r).toAdd)).comp (sigma x)) (FreeGroup.of s)
        = PsiWeight r t x s := by
    intro s
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, powIntHom_apply]
    by_cases hst : s = t
    · subst hst
      rw [sigma_of_of_eq, sigma_of_of_ne (Ne.symm htx), ofAdd_one_zpow, PsiWeight_self]
      simp
    · by_cases hsx : s = x
      · subst hsx
        rw [sigma_of_of_ne htx, sigma_of_of_eq, ofAdd_one_zpow, PsiWeight_eq_x r htx]
        simp
      · rw [sigma_of_of_ne hst, sigma_of_of_ne hsx, PsiWeight_of_ne r hst hsx]
        simp
  have hZr : FreeGroup.lift (PsiWeight r t x) r =
      ((powIntHom ((sigma x r).toAdd)).comp (sigma t) *
        (powIntHom (-(sigma t r).toAdd)).comp (sigma x)) r :=
    (FreeGroup.lift_unique (f := PsiWeight r t x) _ hgenZ).symm
  rw [hZr]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, powIntHom_apply]
  exact mul_zpow_toAdd (sigma t r) (sigma x r)

end Work.OROneRel
