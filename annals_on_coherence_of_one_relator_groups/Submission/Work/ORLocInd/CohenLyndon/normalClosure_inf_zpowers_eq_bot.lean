/-
# The normal closure of `r` meets a letter subgroup trivially

Let `r ∈ F(α)` be an element of the free group on `α` and let `t ≠ x` be two distinct generators,
with the exponent sum of `x` in `r` nonzero (`σ_x r ≠ 1`, the exponent sum living in the
multiplicative integers, so `1` is the exponent sum `0`).  Then the normal closure of `r` meets the
cyclic subgroup `⟨of t⟩` trivially:

`⟪r⟫ ⊓ ⟨of t⟩ = ⊥`.

## The argument

The whole content is the existence of a *single* homomorphism out of `F(α)` that kills `r` but not
`of t`.  Let

* `a := (σ_t r).toAdd` and `b := (σ_x r).toAdd` be the two exponent sums (as integers), and
* `Ψ := FreeGroup.lift (PsiWeight r t x) : F(α) →* Multiplicative ℤ` be the homomorphism sending
  the generator `t` to `σ_x r` (i.e. `ofAdd b`), the generator `x` to `(σ_t r)⁻¹ = ofAdd (-a)`, and
  every other generator to `1`.

Because `Multiplicative ℤ` is abelian, `Ψ r` depends only on the exponent sums of `r`, and
`Ψ r = (σ_t r)ᵇ · (σ_x r)^(-a) = ofAdd (b * a) * ofAdd (-a * b) = 1`.  On the other hand
`Ψ (of t) = (σ_t (of t))ᵇ · (σ_x (of t))^(-a) = (ofAdd 1)ᵇ = ofAdd b ≠ 1` because `σ_x r ≠ 1`.  Now
`ker Ψ` is a normal subgroup containing `r`, so it contains `⟪r⟫`; and an element of `ker Ψ` that is
a power `(of t)ⁿ` of `of t` satisfies `(ofAdd b)ⁿ = 1`, which forces `n = 0` since `b ≠ 0`.  Hence
`⟪r⟫ ⊓ ⟨of t⟩ = ⊥`.

The evaluation of `Ψ` at `r` is the content of `Work.OROneRel.sigma_t_Psi` (where `Ψ` is used to
make the `t`-exponent sum of the Magnus/Putman substitute `Psi r t x r` vanish); it is reproduced
here as `lift_PsiWeight_eq_one`.
-/
import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.weinbaum_at
import Submission.Work.OROneRel.sigma_t_Psi

namespace Work.ORLocInd.CohenLyndon

universe u

variable {α : Type u}

/-- **The weight homomorphism.**  For a relator `r` and two generators `t ≠ x`, the homomorphism
`F(α) →* Multiplicative ℤ` that sends `t` to the exponent sum `σ_x r` of `x` in `r`, sends `x` to
`(σ_t r)⁻¹`, and kills every other generator.  (In `Multiplicative ℤ` the element `σ_x r` is the
inverse of `σ_x (r⁻¹)`, and additions of exponent sums are products.) -/
noncomputable def ncWeightHom (r : FreeGroup α) (t x : α) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift (Work.OROneRel.PsiWeight r t x)

/-- The weight homomorphism kills the relator: its value at `r` is the `t`-weighted exponent sum,
which vanishes because the `x`-exponent of `r` sits in the exponent of the `t`-exponent and vice
versa. -/
theorem lift_PsiWeight_eq_one (r : FreeGroup α) {t x : α} (htx : x ≠ t) :
    FreeGroup.lift (Work.OROneRel.PsiWeight r t x) r = 1 := by
  classical
  -- `PsiWeight r t x` agrees on generators with `(powIntHom b) ∘ σ_t * (powIntHom (-a)) ∘ σ_x`,
  -- where `a = σ_t r` and `b = σ_x r`; hence the two homomorphisms agree everywhere, and the
  -- second one takes the value `aᵇ * b^(-a) = 1` at `r`.
  have hZr : FreeGroup.lift (Work.OROneRel.PsiWeight r t x) r =
      ((Work.OROneRel.powIntHom ((Work.OROneRel.sigma x r).toAdd)).comp
          (Work.OROneRel.sigma t) *
        (Work.OROneRel.powIntHom (-(Work.OROneRel.sigma t r).toAdd)).comp
          (Work.OROneRel.sigma x)) r := by
    have hgenZ : ∀ s : α,
        ((Work.OROneRel.powIntHom ((Work.OROneRel.sigma x r).toAdd)).comp
            (Work.OROneRel.sigma t) *
          (Work.OROneRel.powIntHom (-(Work.OROneRel.sigma t r).toAdd)).comp
            (Work.OROneRel.sigma x)) (FreeGroup.of s) = Work.OROneRel.PsiWeight r t x s := by
      intro s
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Work.OROneRel.powIntHom_apply]
      by_cases hst : s = t
      · subst hst
        rw [Work.OROneRel.sigma_of_of_eq, Work.OROneRel.sigma_of_of_ne (Ne.symm htx),
          Work.OROneRel.ofAdd_one_zpow, Work.OROneRel.PsiWeight_self]
        simp
      · by_cases hsx : s = x
        · subst hsx
          rw [Work.OROneRel.sigma_of_of_ne htx, Work.OROneRel.sigma_of_of_eq,
            Work.OROneRel.ofAdd_one_zpow, Work.OROneRel.PsiWeight_eq_x r htx]
          simp
        · rw [Work.OROneRel.sigma_of_of_ne hst, Work.OROneRel.sigma_of_of_ne hsx,
            Work.OROneRel.PsiWeight_of_ne r hst hsx]
          simp
    exact (FreeGroup.lift_unique (f := Work.OROneRel.PsiWeight r t x) _ hgenZ).symm
  rw [hZr]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Work.OROneRel.powIntHom_apply]
  exact Work.OROneRel.mul_zpow_toAdd (Work.OROneRel.sigma t r) (Work.OROneRel.sigma x r)

/-- The value of the weight homomorphism at the generator `t` is the exponent sum `σ_x r`, which is
nontrivial by hypothesis. -/
theorem ncWeightHom_of_t (r : FreeGroup α) (t x : α) :
    ncWeightHom r t x (FreeGroup.of t) = Multiplicative.ofAdd ((Work.OROneRel.sigma x r).toAdd) := by
  classical
  rw [ncWeightHom, FreeGroup.lift_apply_of, Work.OROneRel.PsiWeight_self]

/-- The weight homomorphism kills the relator. -/
theorem ncWeightHom_relator (r : FreeGroup α) {t x : α} (htx : x ≠ t) :
    ncWeightHom r t x r = 1 := by
  rw [ncWeightHom]
  exact lift_PsiWeight_eq_one r htx

/-- If `σ_x r ≠ 0` then the `x`-exponent of `r` is a nonzero integer. -/
theorem toAdd_sigma_ne_zero {r : FreeGroup α} {x : α}
    (hσx : Work.OROneRel.sigma x r ≠ 1) : (Work.OROneRel.sigma x r).toAdd ≠ 0 := by
  intro hzero
  refine hσx ?_
  have h1 : Multiplicative.ofAdd ((Work.OROneRel.sigma x r).toAdd) = (1 : Multiplicative ℤ) := by
    rw [hzero, ofAdd_zero]
  rwa [ofAdd_toAdd] at h1

/-- A nonzero integer has no nontrivial power equal to `1` in `Multiplicative ℤ`. -/
theorem zpow_ofAdd_eq_one {b n : ℤ} (hb : b ≠ 0)
    (h : (Multiplicative.ofAdd b) ^ n = 1) : n = 0 := by
  have h3 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow, toAdd_ofAdd, toAdd_one, smul_eq_mul] at h3
  exact (mul_eq_zero.mp h3).resolve_right hb

/-- **The normal closure of a relator meets a letter subgroup trivially.**  If the generator `x`
occurs in the relator `r` with nonzero exponent sum and `t ≠ x`, then the normal closure of `r` meets
the cyclic subgroup generated by the free generator `t` only in the identity. -/
theorem normalClosure_inf_zpowers_eq_bot {α : Type u} {r : FreeGroup α} {t x : α}
    (htx : t ≠ x) (hσx : Work.OROneRel.sigma x r ≠ 1) :
    Subgroup.normalClosure ({r} : Set (FreeGroup α)) ⊓ Subgroup.zpowers (FreeGroup.of t) = ⊥ := by
  classical
  have hxt : x ≠ t := htx.symm
  have hb : (Work.OROneRel.sigma x r).toAdd ≠ 0 := toAdd_sigma_ne_zero hσx
  -- `⟪r⟫` lies in the kernel of the weight homomorphism
  have hker : Subgroup.normalClosure ({r} : Set (FreeGroup α)) ≤ (ncWeightHom r t x).ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact MonoidHom.mem_ker.mpr (ncWeightHom_relator r hxt)
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgz⟩ := hg
  obtain ⟨n, hgn⟩ := Subgroup.mem_zpowers_iff.mp hgz
  rw [← hgn]
  -- `of t ^ n` is killed by the weight homomorphism, hence `(σ_x r)ⁿ = 1`
  have hker' : (ncWeightHom r t x) g = 1 := MonoidHom.mem_ker.mp (hker hgN)
  rw [← hgn] at hker'
  have h1 : ((ncWeightHom r t x) (FreeGroup.of t)) ^ n = 1 := by
    rw [← map_zpow]
    exact hker'
  rw [ncWeightHom_of_t] at h1
  rw [zpow_ofAdd_eq_one hb h1, zpow_zero]

end Work.ORLocInd.CohenLyndon
