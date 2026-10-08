import Mathlib
import Submission.Work.DSTR.M110.All

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.AUTL2

open Subgroup OnePoint

variable (F : Type*) [Field F] [DecidableEq F]

/-- Conjugation by an element `π` of `PΓL(2,F)` as an equivalence of `PSL(2,F)`. -/
noncomputable def conjEquiv (π : pgammaL F) : ↥(pslImage F) ≃ ↥(pslImage F) where
  toFun := fun g =>
    ⟨(π : Equiv.Perm (P1 F)) * (g : Equiv.Perm (P1 F)) * (π : Equiv.Perm (P1 F))⁻¹,
      Normalizer.conj_mem_pslImage F (Galois.pgammaL_le_normalizer_pslImage F π.2) g.2⟩
  invFun := fun g =>
    ⟨(π : Equiv.Perm (P1 F))⁻¹ * (g : Equiv.Perm (P1 F)) * (π : Equiv.Perm (P1 F)),
      Normalizer.conj_mem_pslImage F
        (Galois.pgammaL_le_normalizer_pslImage F (Subgroup.inv_mem _ π.2)) g.2⟩
  left_inv := by
    intro g; apply Subtype.ext
    simp only [Subtype.coe_mk, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv]
    group
  right_inv := by
    intro g; apply Subtype.ext
    simp only [Subtype.coe_mk, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv]
    group

/-- Conjugation by an element `π` of `PΓL(2,F)` as an automorphism of `PSL(2,F)`. -/
noncomputable def conjAut (π : pgammaL F) : MulAut ↥(pslImage F) :=
  { conjEquiv F π with
    map_mul' := by
      intro g h; apply Subtype.ext
      simp only [conjEquiv, Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Subgroup.coe_mul]
      group }

@[simp] lemma conjAut_apply (π : pgammaL F) (g : ↥(pslImage F)) :
    (conjAut F π g : Equiv.Perm (P1 F)) =
      (π : Equiv.Perm (P1 F)) * (g : Equiv.Perm (P1 F)) * (π : Equiv.Perm (P1 F))⁻¹ := rfl

/-- Conjugation by `PΓL(2,F)` on `PSL(2,F)`, as a homomorphism `PΓL(2,F) →* Aut(PSL(2,F))`. -/
noncomputable def conjHom : pgammaL F →* MulAut ↥(pslImage F) :=
  MonoidHom.mk' (conjAut F) (by
    intro π σ
    ext g : 1
    apply Subtype.ext
    simp only [MulAut.mul_apply, conjAut_apply, Subgroup.coe_mul, Subtype.coe_mk,
      Equiv.Perm.coe_mul]
    group)

@[simp] lemma conjHom_apply (π : pgammaL F) (g : ↥(pslImage F)) :
    conjHom F π g = conjAut F π g := rfl

/-- `conjHom` is injective: its kernel is the centralizer of `pslImage` in `Perm ℙ¹(F)`,
which is trivial. -/
theorem conjHom_injective (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)] :
    Function.Injective (conjHom (GaloisField p k)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro π hπ
  rw [MonoidHom.mem_ker] at hπ
  have hmem : (π : Equiv.Perm (P1 (GaloisField p k))) ∈
      Subgroup.centralizer (pslImage (GaloisField p k) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 : ((conjHom (GaloisField p k) π ⟨g, hg⟩ : ↥(pslImage (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) = g := by
      rw [hπ]; rfl
    have h3 : ((conjHom (GaloisField p k) π ⟨g, hg⟩ : ↥(pslImage (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) =
        (π : Equiv.Perm (P1 (GaloisField p k))) * g *
          (π : Equiv.Perm (P1 (GaloisField p k)))⁻¹ :=
      conjAut_apply _ _ _
    rw [h3] at h2
    have h2' : g * (π : Equiv.Perm (P1 (GaloisField p k))) =
        (π : Equiv.Perm (P1 (GaloisField p k))) * g := by
      conv_lhs => rw [← h2]
      group
    exact h2'
  have hbot := Work.AUTL2.Aut.centralizer p k hp hq
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

/-- Assembling the isomorphism `PΓL(2,F) ≃* Aut(PSL(2,F))` from injectivity and the
(surjectivity) spatiality statement A6. -/
noncomputable def conjHomEquiv (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)]
    (hsurj : Function.Surjective (conjHom (GaloisField p k))) :
    MulAut ↥(Work.AUTL2.pslImage (GaloisField p k)) ≃*
      Work.AUTL2.pgammaL (GaloisField p k) :=
  (MulEquiv.ofBijective (conjHom (GaloisField p k))
    ⟨conjHom_injective p k hp hq, hsurj⟩).symm

/-- `conjHomEquiv` is a two-sided inverse of `conjHom`. -/
@[simp] lemma conjHom_conjHomEquiv (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)]
    (hsurj : Function.Surjective (conjHom (GaloisField p k)))
    (α : MulAut ↥(Work.AUTL2.pslImage (GaloisField p k))) :
    conjHom (GaloisField p k) (conjHomEquiv p k hp hq hsurj α) = α := by
  have hEq : conjHomEquiv p k hp hq hsurj =
      (MulEquiv.ofBijective (conjHom (GaloisField p k))
        ⟨conjHom_injective p k hp hq, hsurj⟩).symm := rfl
  rw [hEq]
  show (MulEquiv.ofBijective (conjHom (GaloisField p k))
      ⟨conjHom_injective p k hp hq, hsurj⟩)
    ((MulEquiv.ofBijective (conjHom (GaloisField p k))
      ⟨conjHom_injective p k hp hq, hsurj⟩).symm α) = α
  exact MulEquiv.apply_symm_apply _ _

end Work.AUTL2
