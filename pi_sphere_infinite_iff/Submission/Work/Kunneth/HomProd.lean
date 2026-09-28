import Mathlib
import Submission.Work.Kunneth.HomAux
import Submission.Work.Kunneth.flatKerQuotRange

/-!
# The homological Künneth computation

This file proves the remaining steps of

`H_n (tpC C (sumShift M)) ≅ ⨁_{p+q=n} H_p(C) ⊗_ℤ M q`   (`M q` flat):

* `homology_iso_hCycQuot` — `H_n` as cycles modulo boundaries;
* `hCycQuot_iso_prod` — the quotient of the product decomposes as the product of the quotients;
* `hQuot_iso_hHTens` — flat base change in each bidegree;
* `hHTensProd_iso_hQuotProd` and `hHTensProd_iso_X` — the product over the bidegrees is the
  degree-`n` part of the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct
open MonoidalCategory

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The `ℤ`-linear equivalence underlying an isomorphism of `ℤ`-modules. -/
def hIsoToLinearEquiv {X Y : ModuleCat ℤ} (e : X ≅ Y) : ↥X ≃ₗ[ℤ] ↥Y where
  toLinearMap := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x

/-- Membership in the kernel of `hIn`, componentwise. -/
theorem mem_hIn_ker_iff (n : ℕ) (x : tpX C (sumShift M) n) :
    x ∈ (hIn C M n).ker ↔ ∀ pq, x pq ∈ (hDIn C M pq.1.1 pq.1.2).ker := by
  rw [hIn_ker C M n, mem_hProdSub]

/-- The predecessor of `n` in the chain shape `ComplexShape.down ℕ` is `n + 1`. -/
theorem down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  ComplexShape.prev_eq' _ (ComplexShape.down_mk (n + 1) n rfl)

/-- The successor of `n` in the chain shape `ComplexShape.down ℕ` is `n - 1`. -/
theorem down_next (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | k
  · exact ComplexShape.next_eq_self' _ 0 (by intro i hi; simp [ComplexShape.down] at hi)
  · rw [ComplexShape.next_eq' _ (ComplexShape.down_mk (k + 1) k rfl)]
    omega

/-- `H_n (homTens C M)` is cycles modulo boundaries. -/
theorem homology_iso_hCycQuot (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((homTens C M).homology n) (hCycQuot C M n)) := by
  refine ⟨(homTens C M).homologyIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n) ≪≫
    ShortComplex.moduleCatHomologyIso ((homTens C M).sc' (n + 1) n (n - 1)) ≪≫ eqToIso ?_⟩
  rw [Work.Kunneth.moduleCatLeftHomologyData_H_eq]
  rw [show ((homTens C M).sc' (n + 1) n (n - 1)).g = ModuleCat.ofHom (hIn C M n) from
    homTens_d_in C M n]
  rw [show ((homTens C M).sc' (n + 1) n (n - 1)).f = ModuleCat.ofHom (hIn C M (n + 1)) from
    homTens_d C M n]
  unfold hCycQuot
  rfl

/-! ## The quotient of the cycles -/

/-- The submodule of the cycles in bidegree `pq` coming from the incoming differential. -/
def hCycBnd (n : ℕ) (pq : tpIdx n) :
    Submodule ℤ ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2)) :=
  (LinearMap.range (hDOut C M pq.1.1 pq.1.2)).comap
    (LinearMap.ker (hDIn C M pq.1.1 pq.1.2)).subtype

/-- The projection of the cycles of `homTens C M` onto the cycles of one summand. -/
def hCycProj (n : ℕ) (pq : tpIdx n) :
    ↥(LinearMap.ker (hIn C M n)) →ₗ[ℤ] ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2)) where
  toFun x := ⟨(x : tpX C (sumShift M) n) pq,
    (mem_hIn_ker_iff C M n (x : tpX C (sumShift M) n)).mp x.2 pq⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    exact DirectSum.smul_apply c (x : tpX C (sumShift M) n) pq

/-- The value of the projection, as an element of the ambient module. -/
theorem hCycProj_val (n : ℕ) (pq : tpIdx n) (x : ↥(LinearMap.ker (hIn C M n))) :
    ((hCycProj C M n pq x : ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2))) :
      tpSummand C (sumShift M) pq.1.1 pq.1.2) = (x : tpX C (sumShift M) n) pq := rfl

/-- The same statement with the canonical subtype inclusion written out. -/
theorem hCycProj_subtype (n : ℕ) (pq : tpIdx n) (x : ↥(LinearMap.ker (hIn C M n))) :
    (LinearMap.ker (hDIn C M pq.1.1 pq.1.2)).subtype (hCycProj C M n pq x)
      = (x : tpX C (sumShift M) n) pq := rfl

/-- The projection of the cycles onto the product of the quotients of the summands' cycles. -/
def hCycToProd (n : ℕ) :
    ↥(LinearMap.ker (hIn C M n)) →ₗ[ℤ]
      (∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2)) :=
  LinearMap.pi (fun pq => (Submodule.mkQ (hCycBnd C M n pq)).comp (hCycProj C M n pq))

theorem hCycToProd_apply (n : ℕ) (x : ↥(LinearMap.ker (hIn C M n))) (pq : tpIdx n) :
    hCycToProd C M n x pq
      = (Submodule.mkQ (hCycBnd C M n pq)) (hCycProj C M n pq x) := rfl

/-- The kernel of the projection is exactly the submodule of boundaries. -/
theorem ker_hCycToProd (n : ℕ) :
    (hCycToProd C M n).ker
      = (LinearMap.range (hIn C M (n + 1))).comap (LinearMap.ker (hIn C M n)).subtype := by
  ext x
  rw [LinearMap.mem_ker, funext_iff, Submodule.mem_comap, hIn_range_succ, mem_hProdSub]
  constructor
  · intro h pq
    have h' : hCycToProd C M n x pq = 0 := by simpa using h pq
    rw [hCycToProd_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hCycBnd,
      Submodule.mem_comap, hCycProj_subtype] at h'
    exact h'
  · intro hx pq
    show hCycToProd C M n x pq = 0
    rw [hCycToProd_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hCycBnd,
      Submodule.mem_comap, hCycProj_subtype]
    exact hx pq

/-- The projection is surjective. -/
theorem hCycToProd_surjective (n : ℕ) : Function.Surjective (hCycToProd C M n) := by
  intro f
  choose g hg using fun pq => Submodule.mkQ_surjective (hCycBnd C M n pq) (f pq)
  have hz : hMk C M n (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2))
      ∈ LinearMap.ker (hIn C M n) := by
    rw [mem_hIn_ker_iff]
    intro pq
    rw [hMk_apply]
    exact (g pq).2
  refine ⟨⟨hMk C M n (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2)), hz⟩, ?_⟩
  funext pq
  show hCycToProd C M n ⟨_, hz⟩ pq = f pq
  rw [hCycToProd_apply]
  have hsub : hCycProj C M n pq ⟨_, hz⟩ = g pq := by
    apply Subtype.ext
    rw [hCycProj_val, hMk_apply]
  rw [hsub]
  exact hg pq

/-- `hCycQuot C M n` is the product, over the bidegrees `p + q = n`, of the quotients of the
cycles of the summands. -/
theorem hCycQuot_iso_prod (n : ℕ) :
    Nonempty (CategoryTheory.Iso (hCycQuot C M n) (hQuotProd C M n)) := by
  refine ⟨Iso.trans (LinearEquiv.toModuleIso
      ((Submodule.quotEquivOfEq _ _ (ker_hCycToProd C M n).symm).trans
        (LinearMap.quotKerEquivOfSurjective (hCycToProd C M n) (hCycToProd_surjective C M n))))
    (LinearEquiv.toModuleIso (LinearEquiv.piCongrRight (fun pq => ?_)))⟩
  exact { toFun := id, invFun := id, left_inv := fun x => rfl, right_inv := fun x => rfl,
          map_add' := fun x y => rfl, map_smul' := fun c x => rfl }

/-! ## Flat base change in each bidegree -/

/-- **The flat Künneth summand**: `ker (∂_p ⊗ 1) ⧸ im (∂_{p+1} ⊗ 1) ≅ H_p(C) ⊗ M q`. -/
theorem hQuot_iso_hHTens (p q : ℕ) (hM : Module.Flat ℤ ↥(M q)) :
    Nonempty (CategoryTheory.Iso (hQuot C M p q) (hHTens C M p q)) := by
  haveI : Module.Flat ℤ ↥((sumShift M).X q) := hM
  have e1 : C.homology p ≅ ((C.sc' (p + 1) p (p - 1))).homology :=
    (homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ) (p + 1) p (p - 1)
      (down_prev p) (down_next p)).app C
  have e2 : hHTens C M p q
      ≅ ((C.sc' (p + 1) p (p - 1))).homology ⊗ (sumShift M).X q :=
    (tensorRight ((sumShift M).X q)).mapIso e1
  have e3 : ((C.sc' (p + 1) p (p - 1))).homology ⊗ (sumShift M).X q
      ≅ (((C.sc' (p + 1) p (p - 1))).map (tensorRight ((sumShift M).X q))).homology :=
    (ShortComplex.mapHomologyIso ((C.sc' (p + 1) p (p - 1)))
      (tensorRight ((sumShift M).X q))).symm
  have e4 : (((C.sc' (p + 1) p (p - 1))).map (tensorRight ((sumShift M).X q))).homology
      ≅ hQuot C M p q :=
    (FlatKerQuot.moduleCatHomologyIsoKerQuot _).some
  exact ⟨(e2.trans e3 |>.trans e4).symm⟩

/-- The product of the flat base change isomorphisms. -/
theorem hHTensProd_iso_hQuotProd (n : ℕ) (hM : ∀ q, Module.Flat ℤ ↥(M q)) :
    Nonempty (CategoryTheory.Iso (hQuotProd C M n) (hHTensProd C M n)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.piCongrRight (fun pq =>
    hIsoToLinearEquiv (hQuot_iso_hHTens C M pq.1.1 pq.1.2 (hM pq.1.2)).some))⟩

/-- The product over the bidegrees is the degree-`n` part of the target complex. -/
theorem hHTensProd_iso_X (n : ℕ) :
    Nonempty (CategoryTheory.Iso (hHTensProd C M n)
      ((tpC (sumShift (fun p => C.homology p)) (sumShift M)).X n)) :=
  ⟨LinearEquiv.toModuleIso (DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
    (fun pq => ↥(hHTens C M pq.1.1 pq.1.2))).symm⟩

end

end Work.Kunneth
