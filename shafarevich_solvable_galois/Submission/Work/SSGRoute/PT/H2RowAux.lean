import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.h1loc_conjLinearMap
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.HS.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coordinates of `D_A = I ⋊ C` and their calculus

Auxiliary vocabulary for the Hochschild–Serre two-row decomposition of a decomposition group
`D = decomp k A = I ⋊ C`, `C = closure (zpowers σ)`.  `HS.Setup` provides the coordinates
`ip : ↥D → ↥I` and `proj : ↥D → ↥C` with `ip d * proj d = d`; here they are regarded as elements
of `Gal(Ω/k)` (`Q`, `PP`), and the elementary calculus of the factorisation is collected.

Nothing here depends on the arithmetic: it is the group theory of a semidirect product with a
chosen complement, in the Kronecker form used by the two-row decomposition.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.PT

noncomputable section

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
variable (hI : I ≤ SSGRoute.decomp k A)
variable (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
variable (hσ : σ ∈ SSGRoute.decomp k A)
variable (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
variable (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)

/-- The `I`-coordinate, as an element of `Gal(Ω/k)`. -/
noncomputable def Q (d : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω :=
  (Work.SSGRoute.HS.ip A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d :
    Ω ≃ₐ[k] Ω)

/-- The `C`-coordinate, as an element of `Gal(Ω/k)`. -/
noncomputable def PP (d : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω :=
  (Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d :
    Ω ≃ₐ[k] Ω)

@[simp] lemma Q_mem (d : ↥(SSGRoute.decomp k A)) : Q k Ω A I σ hI hnorm hσ hsup d ∈ I :=
  (Work.SSGRoute.HS.ip A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2

@[simp] lemma PP_mem (d : ↥(SSGRoute.decomp k A)) :
    PP k Ω A I σ hI hnorm hσ hsup d
      ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ) :=
  (Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2

lemma PP_mem_D (d : ↥(SSGRoute.decomp k A)) :
    PP k Ω A I σ hI hnorm hσ hsup d ∈ SSGRoute.decomp k A :=
  Work.SSGRoute.HS.CC_le_DD A σ hσ (PP_mem k Ω A I σ hI hnorm hσ hsup d)

/-- The factorisation `d = q d * p d`. -/
lemma Q_mul_PP (d : ↥(SSGRoute.decomp k A)) :
    Q k Ω A I σ hI hnorm hσ hsup d * PP k Ω A I σ hI hnorm hσ hsup d = (d : Ω ≃ₐ[k] Ω) :=
  Work.SSGRoute.HS.ip_mul_proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d

include hinf

/-- `q` of a coset `d * γ` for `γ ∈ C`. -/
lemma Q_mul_mem_C (d : ↥(SSGRoute.decomp k A)) {γ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ)) :
    Q k Ω A I σ hI hnorm hσ hsup
      ⟨(d : Ω ≃ₐ[k] Ω) * γ, (SSGRoute.decomp k A).mul_mem d.2
        (Work.SSGRoute.HS.CC_le_DD A σ hσ hγ)⟩
      = Q k Ω A I σ hI hnorm hσ hsup d := by
  set d' : ↥(SSGRoute.decomp k A) :=
    ⟨(d : Ω ≃ₐ[k] Ω) * γ, (SSGRoute.decomp k A).mul_mem d.2
      (Work.SSGRoute.HS.CC_le_DD A σ hσ hγ)⟩ with hd'
  have hd'v : (d' : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω) * γ := rfl
  have heq : Q k Ω A I σ hI hnorm hσ hsup d' * PP k Ω A I σ hI hnorm hσ hsup d'
      = Q k Ω A I σ hI hnorm hσ hsup d
        * (PP k Ω A I σ hI hnorm hσ hsup d * γ) := by
    have h1 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d'
    have h2 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d
    rw [h1, hd'v, ← h2]
    group
  exact (Work.SSGRoute.HS.factor_unique A I σ hinf
    (i₁ := Q k Ω A I σ hI hnorm hσ hsup d')
    (i₂ := Q k Ω A I σ hI hnorm hσ hsup d)
    (γ₁ := PP k Ω A I σ hI hnorm hσ hsup d')
    (γ₂ := PP k Ω A I σ hI hnorm hσ hsup d * γ)
    (Q_mem k Ω A I σ hI hnorm hσ hsup d')
    (Q_mem k Ω A I σ hI hnorm hσ hsup d)
    (PP_mem k Ω A I σ hI hnorm hσ hsup d')
    ((Subgroup.topologicalClosure (Subgroup.zpowers σ)).mul_mem
      (PP_mem k Ω A I σ hI hnorm hσ hsup d) hγ)
    heq).1

/-- `p` of a coset `d * γ` for `γ ∈ C`. -/
lemma PP_mul_mem_C (d : ↥(SSGRoute.decomp k A)) {γ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ)) :
    PP k Ω A I σ hI hnorm hσ hsup
      ⟨(d : Ω ≃ₐ[k] Ω) * γ, (SSGRoute.decomp k A).mul_mem d.2
        (Work.SSGRoute.HS.CC_le_DD A σ hσ hγ)⟩
      = PP k Ω A I σ hI hnorm hσ hsup d * γ := by
  set d' : ↥(SSGRoute.decomp k A) :=
    ⟨(d : Ω ≃ₐ[k] Ω) * γ, (SSGRoute.decomp k A).mul_mem d.2
      (Work.SSGRoute.HS.CC_le_DD A σ hσ hγ)⟩ with hd'
  have hd'v : (d' : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω) * γ := rfl
  have heq : Q k Ω A I σ hI hnorm hσ hsup d' * PP k Ω A I σ hI hnorm hσ hsup d'
      = Q k Ω A I σ hI hnorm hσ hsup d
        * (PP k Ω A I σ hI hnorm hσ hsup d * γ) := by
    have h1 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d'
    have h2 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d
    rw [h1, hd'v, ← h2]
    group
  exact (Work.SSGRoute.HS.factor_unique A I σ hinf
    (i₁ := Q k Ω A I σ hI hnorm hσ hsup d')
    (i₂ := Q k Ω A I σ hI hnorm hσ hsup d)
    (γ₁ := PP k Ω A I σ hI hnorm hσ hsup d')
    (γ₂ := PP k Ω A I σ hI hnorm hσ hsup d * γ)
    (Q_mem k Ω A I σ hI hnorm hσ hsup d')
    (Q_mem k Ω A I σ hI hnorm hσ hsup d)
    (PP_mem k Ω A I σ hI hnorm hσ hsup d')
    ((Subgroup.topologicalClosure (Subgroup.zpowers σ)).mul_mem
      (PP_mem k Ω A I σ hI hnorm hσ hsup d) hγ)
    heq).2

/-- `p` of a coset `d * n` for `n ∈ I`. -/
lemma PP_mul_mem_I (d : ↥(SSGRoute.decomp k A)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    PP k Ω A I σ hI hnorm hσ hsup
      ⟨(d : Ω ≃ₐ[k] Ω) * n, (SSGRoute.decomp k A).mul_mem d.2 (hI hn)⟩
      = PP k Ω A I σ hI hnorm hσ hsup d := by
  set d' : ↥(SSGRoute.decomp k A) :=
    ⟨(d : Ω ≃ₐ[k] Ω) * n, (SSGRoute.decomp k A).mul_mem d.2 (hI hn)⟩ with hd'
  have hd'v : (d' : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω) * n := rfl
  have heq : Q k Ω A I σ hI hnorm hσ hsup d' * PP k Ω A I σ hI hnorm hσ hsup d'
      = (Q k Ω A I σ hI hnorm hσ hsup d
          * (PP k Ω A I σ hI hnorm hσ hsup d * n
              * (PP k Ω A I σ hI hnorm hσ hsup d)⁻¹))
        * PP k Ω A I σ hI hnorm hσ hsup d := by
    have h1 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d'
    have h2 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d
    rw [h1, hd'v, ← h2]
    group
  exact (Work.SSGRoute.HS.factor_unique A I σ hinf
    (i₁ := Q k Ω A I σ hI hnorm hσ hsup d')
    (i₂ := Q k Ω A I σ hI hnorm hσ hsup d
        * (PP k Ω A I σ hI hnorm hσ hsup d * n * (PP k Ω A I σ hI hnorm hσ hsup d)⁻¹))
    (γ₁ := PP k Ω A I σ hI hnorm hσ hsup d')
    (γ₂ := PP k Ω A I σ hI hnorm hσ hsup d)
    (Q_mem k Ω A I σ hI hnorm hσ hsup d')
    (I.mul_mem (Q_mem k Ω A I σ hI hnorm hσ hsup d)
      (hnorm _ (PP_mem_D k Ω A I σ hI hnorm hσ hsup d) n hn))
    (PP_mem k Ω A I σ hI hnorm hσ hsup d') (PP_mem k Ω A I σ hI hnorm hσ hsup d)
    heq).2

/-- `q` of a coset `d * n` for `n ∈ I`. -/
lemma Q_mul_mem_I (d : ↥(SSGRoute.decomp k A)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Q k Ω A I σ hI hnorm hσ hsup
      ⟨(d : Ω ≃ₐ[k] Ω) * n, (SSGRoute.decomp k A).mul_mem d.2 (hI hn)⟩
      = Q k Ω A I σ hI hnorm hσ hsup d
        * (PP k Ω A I σ hI hnorm hσ hsup d * n * (PP k Ω A I σ hI hnorm hσ hsup d)⁻¹) := by
  set d' : ↥(SSGRoute.decomp k A) :=
    ⟨(d : Ω ≃ₐ[k] Ω) * n, (SSGRoute.decomp k A).mul_mem d.2 (hI hn)⟩ with hd'
  have hd'v : (d' : Ω ≃ₐ[k] Ω) = (d : Ω ≃ₐ[k] Ω) * n := rfl
  have heq : Q k Ω A I σ hI hnorm hσ hsup d' * PP k Ω A I σ hI hnorm hσ hsup d'
      = (Q k Ω A I σ hI hnorm hσ hsup d
          * (PP k Ω A I σ hI hnorm hσ hsup d * n
              * (PP k Ω A I σ hI hnorm hσ hsup d)⁻¹))
        * PP k Ω A I σ hI hnorm hσ hsup d := by
    have h1 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d'
    have h2 := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d
    rw [h1, hd'v, ← h2]
    group
  exact (Work.SSGRoute.HS.factor_unique A I σ hinf
    (i₁ := Q k Ω A I σ hI hnorm hσ hsup d')
    (i₂ := Q k Ω A I σ hI hnorm hσ hsup d
        * (PP k Ω A I σ hI hnorm hσ hsup d * n * (PP k Ω A I σ hI hnorm hσ hsup d)⁻¹))
    (γ₁ := PP k Ω A I σ hI hnorm hσ hsup d')
    (γ₂ := PP k Ω A I σ hI hnorm hσ hsup d)
    (Q_mem k Ω A I σ hI hnorm hσ hsup d')
    (I.mul_mem (Q_mem k Ω A I σ hI hnorm hσ hsup d)
      (hnorm _ (PP_mem_D k Ω A I σ hI hnorm hσ hsup d) n hn))
    (PP_mem k Ω A I σ hI hnorm hσ hsup d') (PP_mem k Ω A I σ hI hnorm hσ hsup d)
    heq).1

/-- If `d ∈ I` then its `C`-coordinate is `1`. -/
lemma PP_eq_one_of_mem_I {d : ↥(SSGRoute.decomp k A)} (hd : (d : Ω ≃ₐ[k] Ω) ∈ I) :
    Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d = 1 := by
  have h := Work.SSGRoute.HS.factor_unique A I σ hinf
    (Work.SSGRoute.HS.ip A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2 hd
    (Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2
    (Subgroup.one_mem (Subgroup.topologicalClosure (Subgroup.zpowers σ)))
    (by rw [Work.SSGRoute.HS.ip_mul_proj, mul_one])
  exact Subtype.ext (by simpa using h.2)

lemma PP_mem_I_coe {d : ↥(SSGRoute.decomp k A)} (hd : (d : Ω ≃ₐ[k] Ω) ∈ I) :
    PP k Ω A I σ hI hnorm hσ hsup d = 1 := by
  have h := PP_eq_one_of_mem_I k Ω A I σ hI hnorm hσ hsup hinf hd
  simpa [PP] using congrArg (fun x : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) =>
    (x : Ω ≃ₐ[k] Ω)) h

lemma Q_eq_of_mem_I {d : ↥(SSGRoute.decomp k A)} (hd : (d : Ω ≃ₐ[k] Ω) ∈ I) :
    Q k Ω A I σ hI hnorm hσ hsup d = (d : Ω ≃ₐ[k] Ω) := by
  have h := Q_mul_PP k Ω A I σ hI hnorm hσ hsup d
  rw [PP_mem_I_coe k Ω A I σ hI hnorm hσ hsup hinf hd, mul_one] at h
  exact h

lemma PP_eq_of_mem_C {d : ↥(SSGRoute.decomp k A)}
    (hd : (d : Ω ≃ₐ[k] Ω) ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ)) :
    PP k Ω A I σ hI hnorm hσ hsup d = (d : Ω ≃ₐ[k] Ω) := by
  have h := Work.SSGRoute.HS.factor_unique A I σ hinf
    (Work.SSGRoute.HS.ip A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2
    (I.one_mem)
    (Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2 hd
    (by rw [Work.SSGRoute.HS.ip_mul_proj, one_mul])
  exact h.2

lemma Q_eq_one_of_mem_C {d : ↥(SSGRoute.decomp k A)}
    (hd : (d : Ω ≃ₐ[k] Ω) ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ)) :
    Q k Ω A I σ hI hnorm hσ hsup d = 1 := by
  have h := Work.SSGRoute.HS.factor_unique A I σ hinf
    (Work.SSGRoute.HS.ip A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2
    (I.one_mem)
    (Work.SSGRoute.HS.proj A I σ hI hnorm (Work.SSGRoute.HS.CC_le_DD A σ hσ) hsup d).2 hd
    (by rw [Work.SSGRoute.HS.ip_mul_proj, one_mul])
  exact h.1

end

end Work.SSGRoute.PT
