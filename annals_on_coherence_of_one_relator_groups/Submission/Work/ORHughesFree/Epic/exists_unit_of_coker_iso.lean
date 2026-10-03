/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Malcolmson's strengthened Schanuel lemma, in matrix form

Given matrices `A : m × n` and `B : m' × n'` over a ring `R` whose cokernels `cokerMat A` and
`cokerMat B` are isomorphic, this file produces a unimodular matrix `U` of size `n + n'` (with
two-sided inverse `U'`) such that the row space of the block matrix `[[A, 0], [0, 1]] · U` equals
the row space of `blkB B = [[B, 0], [0, 1]]` (with its two column blocks exchanged).

The mathematical content is Schanuel's argument: if `K ≤ R^n` and `L ≤ R^{n'}` are the row spaces
of `A` and `B` and `e : R^n/K ≃ R^{n'}/L`, choose linear lifts `lam` and `mu` of `e ∘ mkQ` and
`e⁻¹ ∘ mkQ`; then

* `lam K ⊆ L`, `mu L ⊆ K`, `(1 - lam ∘ mu) R^{n'} ⊆ L` and `(1 - mu ∘ lam) R^n ⊆ K`;
* the block matrix `[[1, mu], [-lam, 1 - lam ∘ mu]]` is an automorphism of `R^n × R^{n'}` (with
  explicit inverse `[[1 - mu ∘ lam, -mu], [lam, 1]]`) that carries `K × ⊤` onto `⊤ × L`.

Transporting this automorphism across the identification `R^n × R^{n'} ≃ R^{n+n'}` gives the
required matrix `U`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.rk_blkM_defs
import Submission.Work.ORHughesFree.Epic.CokerIsoDefs
import Submission.Work.ORHughesFree.Epic.range_rowMulLin_blk_one
import Submission.Work.ORHughesFree.Epic.range_rowMulLin_blkB

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.Epic

open Matrix Work.ORHughesFree
open Work.ORHughesFree.Epic.CokerIso

/-! ## The automorphism of `R^n × R^{n'}` attached to an isomorphism of quotients

This is the general form of the strengthened Schanuel lemma: two submodules `K ≤ R^n`,
`L ≤ R^{n'}` whose quotients are isomorphic have `K × ⊤` and `⊤ × L` exchanged by an
automorphism of `R^n × R^{n'}`.  (The statement is the abstract version of
`exists_automorphism_prod_of_quotient_iso`; it is proved here from scratch so that this file does
not depend on the proof of that lemma.) -/

theorem exists_prodAutomorphism_of_quotient_iso {R : Type*} [Ring R] {n n' : ℕ}
    (K : Submodule R (Fin n → R)) (L : Submodule R (Fin n' → R))
    (e : ((Fin n → R) ⧸ K) ≃ₗ[R] ((Fin n' → R) ⧸ L)) :
    ∃ U : ((Fin n → R) × (Fin n' → R)) ≃ₗ[R] ((Fin n → R) × (Fin n' → R)),
      Submodule.map (U : ((Fin n → R) × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R)))
        (Submodule.prod K ⊤) = Submodule.prod ⊤ L := by
  obtain ⟨lam, hlam⟩ := Module.projective_lifting_property L.mkQ
    (e.toLinearMap.comp K.mkQ) (Submodule.mkQ_surjective L)
  obtain ⟨mu, hmu⟩ := Module.projective_lifting_property K.mkQ
    (e.symm.toLinearMap.comp L.mkQ) (Submodule.mkQ_surjective K)
  have hπ : ∀ x : Fin n → R, x ∈ K ↔ K.mkQ x = 0 := fun x => by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero K).symm
  have hρ : ∀ y : Fin n' → R, y ∈ L ↔ L.mkQ y = 0 := fun y => by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero L).symm
  have hlam_apply : ∀ x : Fin n → R, L.mkQ (lam x) = e (K.mkQ x) := fun x => by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hlam x
  have hmu_apply : ∀ y : Fin n' → R, K.mkQ (mu y) = e.symm (L.mkQ y) := fun y => by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hmu y
  have hlamK : ∀ x ∈ K, lam x ∈ L := by
    intro x hx
    rw [hρ, hlam_apply, (hπ x).mp hx, map_zero]
  have hmuL : ∀ y ∈ L, mu y ∈ K := by
    intro y hy
    rw [hπ, hmu_apply, (hρ y).mp hy, map_zero]
  have hlammu : ∀ y, (y - lam (mu y)) ∈ L := by
    intro y
    rw [hρ, map_sub, hlam_apply, hmu_apply, LinearEquiv.apply_symm_apply, sub_self]
  have hmulam : ∀ x, (x - mu (lam x)) ∈ K := by
    intro x
    rw [hπ, map_sub, hmu_apply, hlam_apply, LinearEquiv.symm_apply_apply, sub_self]
  let A : ((Fin n → R) × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R)) :=
    ((LinearMap.fst R _ _) + mu.comp (LinearMap.snd R _ _)).prod
      (((LinearMap.snd R _ _) - ((lam.comp mu).comp (LinearMap.snd R _ _)))
        - (lam.comp (LinearMap.fst R _ _)))
  let B : ((Fin n → R) × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R)) :=
    (((LinearMap.fst R _ _) - ((mu.comp lam).comp (LinearMap.fst R _ _)))
        - (mu.comp (LinearMap.snd R _ _))).prod
      ((lam.comp (LinearMap.fst R _ _)) + (LinearMap.snd R _ _))
  have hA : ∀ x y, A (x, y) = (x + mu y, (y - lam (mu y)) - lam x) := by
    intro x y
    simp [A]
  have hB : ∀ x y, B (x, y) = ((x - mu (lam x)) - mu y, lam x + y) := by
    intro x y
    simp [B]
  have hAB : A.comp B = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨u, v⟩ := p
    rw [LinearMap.comp_apply, hA, hB, LinearMap.id_apply]
    refine Prod.ext ?_ ?_ <;> simp only [map_add, map_sub] <;> abel
  have hBA : B.comp A = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨x, y⟩ := p
    rw [LinearMap.comp_apply, hB, hA, LinearMap.id_apply]
    refine Prod.ext ?_ ?_ <;> simp only [map_add, map_sub] <;> abel
  refine ⟨LinearEquiv.ofLinearMap A B hAB hBA, ?_⟩
  have hcoe : ((LinearEquiv.ofLinearMap A B hAB hBA :
      ((Fin n → R) × (Fin n' → R)) ≃ₗ[R] ((Fin n → R) × (Fin n' → R))) :
      ((Fin n → R) × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R))) = A :=
    LinearMap.ext (fun _ => rfl)
  rw [hcoe]
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [Submodule.mem_comap, Submodule.mem_prod]
    refine ⟨Submodule.mem_top, ?_⟩
    rw [hA]
    exact Submodule.sub_mem L (hlammu y) (hlamK x hx)
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    refine ⟨B (u, v), ?_, ?_⟩
    · show B (u, v) ∈ Submodule.prod K ⊤
      rw [Submodule.mem_prod, hB]
      exact ⟨Submodule.sub_mem K (hmulam u) (hmuL v hv), Submodule.mem_top⟩
    · rw [← LinearMap.comp_apply, hAB]
      rfl

/-- For a linear equivalence `e : M ≃ₗ N`, mapping a submodule of `M` up along `e` and back down
along `e.symm` returns it. -/
theorem map_symm_map {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : Submodule R M) :
    Submodule.map (e.symm : N →ₗ[R] M) (Submodule.map (e : M →ₗ[R] N) p) = p := by
  rw [← Submodule.comap_equiv_eq_map_symm e (Submodule.map (e : M →ₗ[R] N) p),
    Submodule.comap_map_eq, LinearMap.ker_eq_bot.mpr e.injective, sup_bot_eq]

/-! ## The main statement -/

theorem exists_unit_of_coker_iso {R : Type*} [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R)
    (h : Nonempty (Work.ORHughesFree.Epic.cokerMat A ≃ₗ[R] Work.ORHughesFree.Epic.cokerMat B)) :
    ∃ U U' : Matrix (Fin (n + n')) (Fin (n + n')) R, U * U' = 1 ∧ U' * U = 1 ∧
      LinearMap.range (Work.ORHughesFree.Epic.rowMulLin
          (Work.ORHughesFree.RankAPI.blk A 0 0 (1 : Matrix (Fin n') (Fin n') R) * U))
        = LinearMap.range (Work.ORHughesFree.Epic.rowMulLin
            (Work.ORHughesFree.Epic.blkB B)) := by
  obtain ⟨e⟩ := h
  obtain ⟨A₀, hA₀⟩ :=
    exists_prodAutomorphism_of_quotient_iso (LinearMap.range (rowMulLin A))
      (LinearMap.range (rowMulLin B)) e
  let E₁ : (Fin (n + n') → R) ≃ₗ[R] (Fin (n + n') → R) :=
    (sumProdEquiv R n n').symm.trans (A₀.trans (sumProdEquiv R n n'))
  let E₂ : (Fin (n + n') → R) ≃ₗ[R] (Fin (n + n') → R) :=
    (sumProdEquiv R n n').symm.trans (A₀.symm.trans (sumProdEquiv R n n'))
  have hE₁₂ : E₁.trans E₂ = LinearEquiv.refl R (Fin (n + n') → R) := by
    ext x; simp [E₁, E₂]
  have hE₂₁ : E₂.trans E₁ = LinearEquiv.refl R (Fin (n + n') → R) := by
    ext x; simp [E₁, E₂]
  refine ⟨rowMatrixOf E₁.toLinearMap, rowMatrixOf E₂.toLinearMap, ?_, ?_, ?_⟩
  · have hh : rowMulLin (rowMatrixOf E₁.toLinearMap * rowMatrixOf E₂.toLinearMap) =
        rowMulLin (1 : Matrix (Fin (n + n')) (Fin (n + n')) R) := by
      rw [rowMulLin_mul, rowMulLin_rowMatrixOf, rowMulLin_rowMatrixOf,
        ← rowMatrixOf_id (R := R) (n + n'), rowMulLin_rowMatrixOf,
        LinearEquiv.comp_coe E₁ E₂, hE₁₂]
      rfl
    rw [← rowMatrixOf_rowMulLin (rowMatrixOf E₁.toLinearMap * rowMatrixOf E₂.toLinearMap), hh,
      rowMatrixOf_rowMulLin]
  · have hh : rowMulLin (rowMatrixOf E₂.toLinearMap * rowMatrixOf E₁.toLinearMap) =
        rowMulLin (1 : Matrix (Fin (n + n')) (Fin (n + n')) R) := by
      rw [rowMulLin_mul, rowMulLin_rowMatrixOf, rowMulLin_rowMatrixOf,
        ← rowMatrixOf_id (R := R) (n + n'), rowMulLin_rowMatrixOf,
        LinearEquiv.comp_coe E₂ E₁, hE₂₁]
      rfl
    rw [← rowMatrixOf_rowMulLin (rowMatrixOf E₂.toLinearMap * rowMatrixOf E₁.toLinearMap), hh,
      rowMatrixOf_rowMulLin]
  · rw [rowMulLin_mul, LinearMap.range_comp, rowMulLin_rowMatrixOf, range_rowMulLin_blk_one A,
      range_rowMulLin_blkB B]
    have hcoe : (E₁ : (Fin (n + n') → R) →ₗ[R] (Fin (n + n') → R)) =
        ((sumProdEquiv R n n') : ((Fin n → R) × (Fin n' → R)) →ₗ[R] (Fin (n + n') → R)).comp
          ((A₀ : ((Fin n → R) × (Fin n' → R)) →ₗ[R] ((Fin n → R) × (Fin n' → R))).comp
            ((sumProdEquiv R n n').symm :
              (Fin (n + n') → R) →ₗ[R] ((Fin n → R) × (Fin n' → R)))) := rfl
    have hkey := map_symm_map (sumProdEquiv R n n')
      (Submodule.prod (LinearMap.range (rowMulLin A)) ⊤)
    rw [hcoe, Submodule.map_comp, Submodule.map_comp, hkey, hA₀]

end Work.ORHughesFree.Epic
