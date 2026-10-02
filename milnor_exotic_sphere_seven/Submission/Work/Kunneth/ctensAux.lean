import Mathlib
import Submission.Work.Kunneth.TensorCo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary vocabulary for the computation of `H^*(ctens A T)`

This file collects the small combinatorial and algebraic definitions that the proof of
`Work.Kunneth.homology_ctens` needs:

* `tpStep`, `tpZero` — the two classes of bidegrees in `tpIdx (n+1)`;
* `tpIdxEquivFin`, and consequently `Fintype (tpIdx n)`;
* `ctensProj` — the projection onto one bidegree summand of `ctensX A T n`;
* `dTensIn`, `dTensOut` — the "incoming" and "outgoing" differentials of `A`, tensored with `T q`;
* `ctensDIn` — the incoming differential of the complex `ctens A T` in degree `n`;
* `ctensMk` — the element of `ctensX A T n` with prescribed components;
* `ctensProdSub` — the submodule of `ctensX A T n` given by a family of submodules of the
  summands;
* the component formulas `ctensD_apply_step` and `ctensD_apply_zero` for `ctensD`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ)

/-! ## The bidegree index sets -/

/-- The "step" `(p,q) ↦ (p+1,q)` on bidegrees. -/
abbrev tpStep (n : ℕ) (pq : tpIdx n) : tpIdx (n + 1) := ⟨(pq.1.1 + 1, pq.1.2), by omega⟩

/-- The bidegree `(0,n+1)` of total degree `n+1`, the only one not hit by `tpStep`. -/
abbrev tpZero (n : ℕ) : tpIdx (n + 1) := ⟨(0, n + 1), by omega⟩

@[simp] theorem tpStep_fst (n : ℕ) (pq : tpIdx n) : (tpStep n pq).1.1 = pq.1.1 + 1 := rfl
@[simp] theorem tpStep_snd (n : ℕ) (pq : tpIdx n) : (tpStep n pq).1.2 = pq.1.2 := rfl
@[simp] theorem tpZero_fst (n : ℕ) : (tpZero n).1.1 = 0 := rfl
@[simp] theorem tpZero_snd (n : ℕ) : (tpZero n).1.2 = n + 1 := rfl

lemma tpStep_injective (n : ℕ) : Function.Injective (tpStep (n := n)) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · simpa using congrArg (fun i : tpIdx (n + 1) => i.1.1) h
  · simpa using congrArg (fun i : tpIdx (n + 1) => i.1.2) h

lemma tpStep_ne_tpZero (n : ℕ) (r : tpIdx n) : tpStep n r ≠ tpZero n := by
  intro h
  have := congrArg (fun i : tpIdx (n + 1) => i.1.1) h
  simp at this

lemma eq_tpZero_of_fst_eq_zero {n : ℕ} {j : tpIdx (n + 1)} (h : j.1.1 = 0) :
    j = tpZero n := by
  apply Subtype.ext
  apply Prod.ext
  · simpa using h
  · have hj := j.2
    simp only [tpZero_snd]
    omega

lemma eq_tpStep_of_pos {n : ℕ} {j : tpIdx (n + 1)} (h : 1 ≤ j.1.1) :
    j = tpStep n ⟨(j.1.1 - 1, j.1.2), by omega⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · have hj := j.2
    simp only [tpStep_fst]
    omega
  · simp only [tpStep_snd]

/-- The bidegrees of total degree `n` are the integers `0, …, n`. -/
def tpIdxEquivFin (n : ℕ) : tpIdx n ≃ Fin (n + 1) where
  toFun pq := ⟨pq.1.1, by have := pq.2; omega⟩
  invFun i := ⟨(i.1, n - i.1), by have := i.2; omega⟩
  left_inv pq := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show n - pq.1.1 = pq.1.2
      have := pq.2
      omega
  right_inv i := by
    apply Fin.ext
    rfl

instance (n : ℕ) : Fintype (tpIdx n) := Fintype.ofEquiv (Fin (n + 1)) (tpIdxEquivFin n).symm

/-! ## Projections and the tensor differentials -/

/-- The projection onto the `pq`-th summand of the degree-`n` part of `ctens A T`. -/
def ctensProj (n : ℕ) (pq : tpIdx n) : ctensX A T n →ₗ[ℤ] ctensSummand A T pq.1.1 pq.1.2 where
  toFun x := x pq
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem ctensProj_apply (n : ℕ) (pq : tpIdx n) (x : ctensX A T n) :
    ctensProj A T n pq x = x pq := rfl

/-- `A^{p-1} ⊗ T q → A^p ⊗ T q`, the incoming differential of `A`, tensored with `T q`. -/
def dTensIn (p q : ℕ) : ctensSummand A T (p - 1) q →ₗ[ℤ] ctensSummand A T p q :=
  LinearMap.rTensor (↥(T q)) (A.d (p - 1) p).hom

/-- `A^p ⊗ T q → A^{p+1} ⊗ T q`, the outgoing differential of `A`, tensored with `T q`. -/
def dTensOut (p q : ℕ) : ctensSummand A T p q →ₗ[ℤ] ctensSummand A T (p + 1) q :=
  LinearMap.rTensor (↥(T q)) (A.d p (p + 1)).hom

/-- The composite of the incoming and the outgoing differentials is zero. -/
theorem dTensIn_comp_dTensOut (p q : ℕ) : (dTensOut A T p q).comp (dTensIn A T p q) = 0 := by
  have h : ((A.d p (p + 1)).hom).comp ((A.d (p - 1) p).hom) = 0 := by
    have h2 := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d A (p - 1) p (p + 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact h2
  rw [dTensOut, dTensIn, ← LinearMap.rTensor_comp, h]
  ext x
  simp
  try rfl

/-- The incoming differential of the complex `ctens A T` in degree `n`; it is `0` for `n = 0`. -/
def ctensDIn : (n : ℕ) → ctensX A T (n - 1) →ₗ[ℤ] ctensX A T n
  | 0 => 0
  | (m + 1) => ctensD A T m

@[simp]
theorem ctensDIn_zero : ctensDIn A T 0 = 0 := rfl

@[simp]
theorem ctensDIn_succ (m : ℕ) : ctensDIn A T (m + 1) = ctensD A T m := rfl

/-- The incoming differential of `ctens A T` is Mathlib's differential `d (n-1) n`. -/
theorem ctens_d_in (n : ℕ) :
    (ctens A T).d (n - 1) n = ModuleCat.ofHom (ctensDIn A T n) := by
  match n with
  | 0 =>
    rw [show (ctens A T).d (0 - 1) 0 = 0 from by
      simpa using HomologicalComplex.shape (ctens A T) 0 0 (by simp [ComplexShape.up_Rel])]
    rfl
  | (m + 1) =>
    rw [show (ctens A T).d ((m + 1) - 1) (m + 1) = ModuleCat.ofHom (ctensD A T m) from by
      simpa using ctens_d A T m]
    rfl

/-! ## Concrete descriptions as `ModuleCat ℤ` objects

These definitions spell out the concrete "cycles modulo boundaries" descriptions as objects of
`ModuleCat ℤ`, so that statements about them can be quoted outside this file (where the
`AddCommGroup.toIntModule` instance has not been removed). -/

/-- The concrete `H^n` of a cochain complex of `ℤ`-modules: `ker d^n ⧸ im d^{n-1}`. -/
def homologyQuot (C : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((LinearMap.ker ((C.d n (n + 1)).hom)) ⧸
    (LinearMap.range ((C.d (n - 1) n).hom)).comap (LinearMap.ker ((C.d n (n + 1)).hom)).subtype)

/-- `ker (d ⊗ 1) ⧸ im (d ⊗ 1)` in degree `p` of the "coefficient" complex `A ⊗ T q`. -/
def kerQuotTens (p q : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LinearMap.ker (dTensOut A T p q) ⧸
    (LinearMap.range (dTensIn A T p q)).comap (LinearMap.ker (dTensOut A T p q)).subtype)

/-- `H^p(A) ⊗ T q`. -/
def homologyTensor (p q : ℕ) : ModuleCat ℤ := A.homology p ⊗ T q

/-! ## Components -/

/-- The element of `ctensX A T n` whose `pq`-component is `F pq`. -/
def ctensMk (n : ℕ) (F : ∀ pq : tpIdx n, ctensSummand A T pq.1.1 pq.1.2) : ctensX A T n :=
  DFinsupp.mk (Finset.univ : Finset (tpIdx n)) (fun pq => F pq.1)

@[simp]
theorem ctensMk_apply (n : ℕ) (F : ∀ pq : tpIdx n, ctensSummand A T pq.1.1 pq.1.2) (pq : tpIdx n) :
    ctensMk A T n F pq = F pq := by
  rw [ctensMk, DFinsupp.mk_apply, dif_pos (Finset.mem_univ pq)]

/-- Every element of `ctensX A T n` is the element with its own components. -/
theorem ctensMk_self (n : ℕ) (x : ctensX A T n) : ctensMk A T n (fun pq => x pq) = x := by
  apply DirectSum.ext
  intro pq
  rw [ctensMk_apply]

/-- The submodule of `ctensX A T n` of elements whose `pq`-component lies in `P pq`. -/
def ctensProdSub (n : ℕ) (P : ∀ pq : tpIdx n, Submodule ℤ (ctensSummand A T pq.1.1 pq.1.2)) :
    Submodule ℤ (ctensX A T n) where
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
theorem mem_ctensProdSub {n : ℕ} {P : ∀ pq : tpIdx n, Submodule ℤ (ctensSummand A T pq.1.1 pq.1.2)}
    {x : ctensX A T n} : x ∈ ctensProdSub A T n P ↔ ∀ pq, x pq ∈ P pq := Iff.rfl

theorem ctensProdSub_mono {n : ℕ} {P Q : ∀ pq : tpIdx n, Submodule ℤ (ctensSummand A T pq.1.1 pq.1.2)}
    (h : ∀ pq, P pq ≤ Q pq) : ctensProdSub A T n P ≤ ctensProdSub A T n Q :=
  fun _x hx pq => h pq (hx pq)

/-! ## The component formulas for `ctensD` -/

/-- `ctensD` on a generator `lof pq c`. -/
theorem ctensD_lof (n : ℕ) (pq : tpIdx n) (c : ctensSummand A T pq.1.1 pq.1.2) :
    ctensD A T n (ctensLof A T n pq c)
      = ctensLof A T (n + 1) (tpStep n pq) (dTensOut A T pq.1.1 pq.1.2 c) := by
  rw [ctensD, DirectSum.toModule_lof, ctensDpq]
  rfl

/-- The `pq`-component of `ctensD n x` is the outgoing differential of the `pq`-component of `x`. -/
theorem ctensD_apply_step (n : ℕ) (x : ctensX A T n) (pq : tpIdx n) :
    ctensD A T n x (tpStep n pq) = dTensOut A T pq.1.1 pq.1.2 (x pq) := by
  have h : (ctensProj A T (n + 1) (tpStep n pq)).comp (ctensD A T n)
      = (dTensOut A T pq.1.1 pq.1.2).comp (ctensProj A T n pq) := by
    apply DirectSum.linearMap_ext ℤ
    intro r
    apply LinearMap.ext
    intro c
    show ctensD A T n (ctensLof A T n r c) (tpStep n pq)
      = dTensOut A T pq.1.1 pq.1.2 ((ctensLof A T n r c) pq)
    rw [ctensD_lof]
    by_cases hrc : r = pq
    · subst hrc
      rw [DirectSum.lof_apply, DirectSum.lof_apply]
    · have h2 : tpStep n pq ≠ tpStep n r := fun hh => hrc (tpStep_injective n hh.symm)
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h2, DirectSum.lof_eq_of,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hrc)]
      simp
  have hx := LinearMap.congr_fun h x
  show (ctensProj A T (n + 1) (tpStep n pq)) (ctensD A T n x)
    = (dTensOut A T pq.1.1 pq.1.2) ((ctensProj A T n pq) x)
  exact hx

/-- The `(0,n+1)`-component of `ctensD n x` is zero. -/
theorem ctensD_apply_zero (n : ℕ) (x : ctensX A T n) : ctensD A T n x (tpZero n) = 0 := by
  have h : (ctensProj A T (n + 1) (tpZero n)).comp (ctensD A T n) = 0 := by
    apply DirectSum.linearMap_ext ℤ
    intro r
    apply LinearMap.ext
    intro c
    show ctensD A T n (ctensLof A T n r c) (tpZero n) = 0
    rw [ctensD_lof, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne (tpStep n r) (tpZero n) _
        (Ne.symm (tpStep_ne_tpZero n r))]
  have hx := LinearMap.congr_fun h x
  show (ctensProj A T (n + 1) (tpZero n)) (ctensD A T n x) = 0
  simpa using hx

end

end Work.Kunneth
