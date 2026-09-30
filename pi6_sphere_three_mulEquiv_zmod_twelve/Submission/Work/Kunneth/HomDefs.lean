import Mathlib
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.ctensAux
import Submission.Work.Kunneth.homologyIsoKerQuotRange

/-!
# The homological Künneth computation: vocabulary

This file sets up the homological companion of the cohomological Künneth machine in
`Submission/Work/Kunneth/`.  The object of study is the chain complex

`homTens C M = tpC C (sumShift M)`,

whose degree `n` part is `⨁_{p+q=n} C_p ⊗_ℤ M q` and whose differential is `d_C ⊗ 1` (the
Koszul sign and the second summand of `tpD` vanish because `sumShift M` has zero differential).

The target statement is

`H_n (homTens C M) ≅ ⨁_{p+q=n} H_p(C) ⊗_ℤ M q`   (`M q` flat),

proved by the same three steps as `Work.Kunneth.homology_ctens`:

* the kernel and the range of the differential of `homTens C M` are the products, over the
  bidegrees, of the kernels respectively the ranges of the coefficient differentials `hDIn`,
  `hDOut`;
* hence `H_n (homTens C M)` is the product, over `p + q = n`, of `ker (hDIn p q) ⧸ im (hDOut p q)`;
* and `ker (hDIn p q) ⧸ im (hDOut p q) ≅ H_p(C) ⊗ M q` because `M q` is flat.

This file contains the definitions and the elementary facts; the three steps are in the
companion files.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The homological Künneth complex** `C ⊗_ℤ (⊕_q M q [q])`. -/
abbrev homTens (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  tpC C (sumShift M)

@[simp]
theorem homTens_X (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (n : ℕ) :
    (homTens C M).X n = ModuleCat.of ℤ (tpX C (sumShift M) n) := rfl

@[simp]
theorem homTens_d (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ) (n : ℕ) :
    (homTens C M).d (n + 1) n = ModuleCat.ofHom (tpD C (sumShift M) n) :=
  tpC_d C (sumShift M) n

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-- The "incoming" coefficient differential `∂_p : C_p ⊗ M q ⟶ C_{p-1} ⊗ M q`.
It is zero for `p = 0`. -/
def hDIn (p q : ℕ) :
    tpSummand C (sumShift M) p q →ₗ[ℤ] tpSummand C (sumShift M) (p - 1) q :=
  LinearMap.rTensor ↥((sumShift M).X q) (C.d p (p - 1)).hom

/-- The "outgoing" coefficient differential `∂_{p+1} : C_{p+1} ⊗ M q ⟶ C_p ⊗ M q`. -/
def hDOut (p q : ℕ) :
    tpSummand C (sumShift M) (p + 1) q →ₗ[ℤ] tpSummand C (sumShift M) p q :=
  LinearMap.rTensor ↥((sumShift M).X q) (C.d (p + 1) p).hom

/-- `hDIn p q` is zero in degree `0`. -/
theorem hDIn_zero (q : ℕ) : hDIn C M 0 q = 0 := by
  have h : C.d 0 (0 - 1) = 0 :=
    HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down_Rel])
  rw [hDIn, h, ModuleCat.hom_zero]
  exact LinearMap.rTensor_zero (R := ℤ) (M := ↥((sumShift M).X q))
    (N := ↥(C.X 0)) (P := ↥(C.X (0 - 1)))

/-- The outgoing differential is the incoming differential shifted by one. -/
theorem hDIn_succ_eq_hDOut (p q : ℕ) : hDIn C M (p + 1) q = hDOut C M p q := rfl

/-- The composite of the two coefficient differentials is zero. -/
theorem hDIn_comp_hDOut (p q : ℕ) : (hDIn C M p q).comp (hDOut C M p q) = 0 := by
  have h : ((C.d p (p - 1)).hom).comp ((C.d (p + 1) p).hom) = 0 := by
    have h2 := congrArg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d C (p + 1) p (p - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact h2
  rw [hDIn, hDOut, ← LinearMap.rTensor_comp, h]
  exact LinearMap.rTensor_zero (R := ℤ) (M := ↥((sumShift M).X q))
    (N := ↥(C.X (p + 1))) (P := ↥(C.X (p - 1)))

/-- The incoming differential of `homTens C M` in degree `n`: `0` in degree `0`, and `tpD` in
positive degree. -/
def hIn : (n : ℕ) → tpX C (sumShift M) n →ₗ[ℤ] tpX C (sumShift M) (n - 1)
  | 0 => 0
  | (m + 1) => tpD C (sumShift M) m

@[simp]
theorem hIn_zero : hIn C M 0 = 0 := rfl

@[simp]
theorem hIn_succ (m : ℕ) : hIn C M (m + 1) = tpD C (sumShift M) m := rfl

/-- The incoming differential of `homTens C M` is Mathlib's differential `d n (n-1)`. -/
theorem homTens_d_in (n : ℕ) :
    (homTens C M).d n (n - 1) = ModuleCat.ofHom (hIn C M n) := by
  match n with
  | 0 =>
    rw [show (homTens C M).d (0 - 1) 0 = (homTens C M).d 0 0 from rfl]
    rw [show (homTens C M).d 0 0 = 0 from
      HomologicalComplex.shape (homTens C M) 0 0 (by simp [ComplexShape.down_Rel])]
    rfl
  | (m + 1) =>
    rw [show (homTens C M).d (m + 1) ((m + 1) - 1)
          = ModuleCat.ofHom (tpD C (sumShift M) m) from by
        simpa using homTens_d C M m]
    rfl

/-- The first component of `tpStep n j` minus one is that of `j`. -/
theorem tpStep_fst_sub_one (n : ℕ) (j : tpIdx n) : (tpStep n j).1.1 - 1 = j.1.1 := by
  simp [tpStep]

/-- The second component of `tpStep n j` is that of `j`. -/
theorem tpStep_snd' (n : ℕ) (j : tpIdx n) : (tpStep n j).1.2 = j.1.2 := rfl

/-- The element of `tpX C (sumShift M) n` with prescribed components. -/
def hMk (n : ℕ) (F : ∀ pq : tpIdx n, tpSummand C (sumShift M) pq.1.1 pq.1.2) :
    tpX C (sumShift M) n :=
  DFinsupp.mk (Finset.univ : Finset (tpIdx n)) (fun pq => F pq.1)

@[simp]
theorem hMk_apply (n : ℕ) (F : ∀ pq : tpIdx n, tpSummand C (sumShift M) pq.1.1 pq.1.2)
    (pq : tpIdx n) : hMk C M n F pq = F pq := by
  rw [hMk, DFinsupp.mk_apply, dif_pos (Finset.mem_univ pq)]

/-- Every element is the element with its own components. -/
theorem hMk_self (n : ℕ) (x : tpX C (sumShift M) n) : hMk C M n (fun pq => x pq) = x := by
  apply DirectSum.ext
  intro pq
  rw [hMk_apply]

/-- The submodule of `tpX C (sumShift M) n` whose `pq`-component lies in `P pq`. -/
def hProdSub (n : ℕ)
    (P : ∀ pq : tpIdx n, Submodule ℤ (tpSummand C (sumShift M) pq.1.1 pq.1.2)) :
    Submodule ℤ (tpX C (sumShift M) n) where
  carrier := {x | ∀ pq, x pq ∈ P pq}
  zero_mem' := by intro pq; simp
  add_mem' := by
    intro x y hx hy pq
    rw [DirectSum.add_apply]
    exact (P pq).add_mem (hx pq) (hy pq)
  smul_mem' := by
    intro c x hx pq
    rw [DirectSum.smul_apply]
    exact (P pq).smul_mem c (hx pq)

@[simp]
theorem mem_hProdSub {n : ℕ}
    {P : ∀ pq : tpIdx n, Submodule ℤ (tpSummand C (sumShift M) pq.1.1 pq.1.2)}
    {x : tpX C (sumShift M) n} : x ∈ hProdSub C M n P ↔ ∀ pq, x pq ∈ P pq := Iff.rfl

/-- The projection onto the `pq`-th summand. -/
def hProj (n : ℕ) (pq : tpIdx n) :
    tpX C (sumShift M) n →ₗ[ℤ] tpSummand C (sumShift M) pq.1.1 pq.1.2 where
  toFun x := x pq
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem hProj_apply (n : ℕ) (pq : tpIdx n) (x : tpX C (sumShift M) n) :
    hProj C M n pq x = x pq := rfl

/-- The concrete `H_p` of the coefficient complex `C ⊗ M q`: `ker ∂_p ⧸ im ∂_{p+1}`. -/
def hQuot (p q : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LinearMap.ker (hDIn C M p q) ⧸
    (LinearMap.range (hDOut C M p q)).comap (LinearMap.ker (hDIn C M p q)).subtype)

/-- The concrete `H_n` of `homTens C M`: cycles modulo boundaries, where the incoming
differential is `hIn`. -/
def hCycQuot (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LinearMap.ker (hIn C M n) ⧸
    (LinearMap.range (hIn C M (n + 1))).comap (LinearMap.ker (hIn C M n)).subtype)

/-- `H_p(C) ⊗_ℤ M q`, the `(p,q)`-summand of the Künneth target. -/
abbrev hHTens (p q : ℕ) : ModuleCat ℤ := C.homology p ⊗ (sumShift M).X q

/-- The product, over `p + q = n`, of the `(p,q)`-summands `ker ∂_p ⧸ im ∂_{p+1}`. -/
abbrev hQuotProd (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2))

/-- The product, over `p + q = n`, of the Künneth summands `H_p(C) ⊗ M q`. -/
abbrev hHTensProd (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(hHTens C M pq.1.1 pq.1.2))

end

end Work.Kunneth
