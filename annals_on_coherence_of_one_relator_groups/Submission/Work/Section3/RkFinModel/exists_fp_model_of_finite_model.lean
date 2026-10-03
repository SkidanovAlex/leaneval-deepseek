import Mathlib
import Submission.Work.Section3.RkFinModel.Defs
import Submission.Work.Section3.RkFinModel.BalCombos

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Work.Section3.RkFinModel

/-! ### Auxiliary lemmas

Every element of `S ⊗[ℤ] N` is a finite sum of elementary tensors, and the two directions of
`mk f L x = 0 ↔ x ∈ closure (balRelMod f L)`.
-/

/-- Every element of the `ℤ`-tensor product `S ⊗[ℤ] N` is a finite sum of elementary tensors. -/
private lemma tensor_decomp (S : Type u) [Ring S] (N : Type u) [AddCommGroup N] [Module ℤ N]
    (x : TensorProduct ℤ S N) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → S) (b : ι → N), x = ∑ i, a i ⊗ₜ[ℤ] b i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp⟩
  | tmul a b => exact ⟨PUnit, inferInstance, fun _ => a, fun _ => b, by simp⟩
  | add x y hx hy =>
      obtain ⟨ι₁, hι₁, a₁, b₁, rfl⟩ := hx
      obtain ⟨ι₂, hι₂, a₂, b₂, rfl⟩ := hy
      exact ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, by
        rw [Fintype.sum_sum_type]; simp [Sum.elim_inl, Sum.elim_inr]⟩

private theorem mem_closure_of_mk_eq_zero {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] {x : TensorProduct ℤ S L}
    (hx : BalancedTensorMod.mk f L x = 0) : x ∈ AddSubgroup.closure (balRelMod f L) := by
  rw [← AddMonoidHom.mem_ker, BalancedTensorMod.mk, QuotientAddGroup.ker_mk'] at hx
  exact hx

private theorem mk_eq_zero_of_mem_closure {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] {x : TensorProduct ℤ S L}
    (hx : x ∈ AddSubgroup.closure (balRelMod f L)) : BalancedTensorMod.mk f L x = 0 :=
  AddMonoidHom.mem_ker.mp (by
    rw [BalancedTensorMod.mk, QuotientAddGroup.ker_mk']
    exact hx)

/-- **Finite descent.**  If `z ⊗[R] r = 0` for an `R`-module `L` that is only assumed *finitely
generated* (equipped with a semilinear map `φ : L → S`), then the same vanishing can be witnessed
on a *finitely presented* `R`-module `L'`, with the value `φ r` preserved. -/
theorem exists_fp_model_of_finite_model {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] [Module.Finite R L]
    (φ : L →+ S) (hφ : ∀ (a : R) (l : L), φ (a • l) = f a * φ l) (z : S) (r : L)
    (h : Work.Section3.RkFinModel.BalancedTensorMod.tmulM f z r = 0) :
    ∃ (L' : Type u) (_ : AddCommGroup L') (_ : Module R L') (_ : Module.FinitePresentation R L')
      (φ' : L' →+ S) (_ : ∀ (a : R) (l : L'), φ' (a • l) = f a * φ' l) (r' : L'),
      φ' r' = φ r ∧ Work.Section3.RkFinModel.BalancedTensorMod.tmulM f z r' = 0 := by
  classical
  -- a finite free presentation `R^n ↠ L`, and a lift `vt` of `r`
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R L
  obtain ⟨vt, hvt⟩ := hp r
  let pz : (Fin n → R) →ₗ[ℤ] L := p.restrictScalars ℤ
  let K : Submodule ℤ (Fin n → R) := LinearMap.ker pz
  -- the vanishing `z ⊗ r = 0` is a finite `ℤ`-linear combination of balance relations
  have hmem : z ⊗ₜ[ℤ] r ∈ AddSubgroup.closure (balRelMod f L) :=
    mem_closure_of_mk_eq_zero f h
  obtain ⟨ι, hι, c, a, l, q, hcomb⟩ := exists_balRelMod_combo f hmem
  choose w hw using fun i => hp (l i)
  -- the correction term that makes `z ⊗ vt` land in the kernel of `1 ⊗ p`
  let B : TensorProduct ℤ S (Fin n → R) :=
    ∑ i, c i • ((a i * f (q i)) ⊗ₜ[ℤ] (w i) - (a i) ⊗ₜ[ℤ] (q i • w i))
  let δ : TensorProduct ℤ S (Fin n → R) := (z ⊗ₜ[ℤ] vt) - B
  have h0 : (LinearMap.lTensor S pz) (z ⊗ₜ[ℤ] vt) = z ⊗ₜ[ℤ] r := by
    rw [LinearMap.lTensor_tmul]
    show z ⊗ₜ[ℤ] (p vt) = z ⊗ₜ[ℤ] r
    rw [hvt]
  have hB : (LinearMap.lTensor S pz) B
      = ∑ i, c i • ((a i * f (q i)) ⊗ₜ[ℤ] (l i) - (a i) ⊗ₜ[ℤ] (q i • l i)) := by
    have hterm : ∀ i, (LinearMap.lTensor S pz)
        ((a i * f (q i)) ⊗ₜ[ℤ] (w i) - (a i) ⊗ₜ[ℤ] (q i • w i))
        = ((a i * f (q i)) ⊗ₜ[ℤ] (l i) - (a i) ⊗ₜ[ℤ] (q i • l i)) := by
      intro i
      rw [map_sub, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      congr 1
      · show (a i * f (q i)) ⊗ₜ[ℤ] (p (w i)) = (a i * f (q i)) ⊗ₜ[ℤ] (l i)
        rw [hw i]
      · show (a i) ⊗ₜ[ℤ] (p (q i • w i)) = (a i) ⊗ₜ[ℤ] (q i • l i)
        rw [map_smul, hw i]
    dsimp only [B]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hterm i]
  have hδker : (LinearMap.lTensor S pz) δ = 0 := by
    show (LinearMap.lTensor S pz) ((z ⊗ₜ[ℤ] vt) - B) = 0
    rw [map_sub, h0, hB, ← hcomb, sub_self]
  have hpz_surj : Function.Surjective pz := fun y => hp y
  have hex : Function.Exact ⇑K.subtype ⇑pz := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hker_eq : (LinearMap.lTensor S pz).ker = (LinearMap.lTensor S K.subtype).range :=
    Function.Exact.linearMap_ker_eq (lTensor_exact S hex hpz_surj)
  have hδmem : δ ∈ (LinearMap.lTensor S pz).ker := LinearMap.mem_ker.mpr hδker
  obtain ⟨ε, hε⟩ := LinearMap.mem_range.mp (hker_eq ▸ hδmem)
  obtain ⟨ι', hι', s', k', hεdecomp⟩ := tensor_decomp S K ε
  let gen : ι' → (Fin n → R) := fun i => (k' i : (Fin n → R))
  let KR : Submodule R (Fin n → R) := Submodule.span R (Set.range gen)
  have hKR_fg : KR.FG := Submodule.fg_span (Set.finite_range gen)
  have hgen_ker : ∀ i, p (gen i) = 0 := by
    intro i
    have h1 : pz (gen i) = 0 := LinearMap.mem_ker.mp (show gen i ∈ K from (k' i).2)
    show p (gen i) = 0
    exact h1
  have hKR_le : KR ≤ LinearMap.ker p := by
    dsimp only [KR]
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hgen_ker i)
  let g : (Fin n → R) →ₗ[ℤ] ((Fin n → R) ⧸ KR) := (KR.mkQ).restrictScalars ℤ
  have hδeq : δ = ∑ i, s' i ⊗ₜ[ℤ] gen i := by
    rw [← hε, hεdecomp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul]
    rfl
  have hgδ : (LinearMap.lTensor S g) δ = 0 := by
    rw [hδeq, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hgi : g (gen i) = 0 := by
      show KR.mkQ (gen i) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [LinearMap.lTensor_tmul, hgi, TensorProduct.tmul_zero]
  have hg_smul : ∀ i, g (q i • w i) = q i • g (w i) := by
    intro i
    show KR.mkQ (q i • w i) = q i • KR.mkQ (w i)
    rw [map_smul]
  have hB2 : (LinearMap.lTensor S g) B
      = ∑ i, c i • ((a i * f (q i)) ⊗ₜ[ℤ] (g (w i)) - (a i) ⊗ₜ[ℤ] (q i • g (w i))) := by
    have hterm : ∀ i, (LinearMap.lTensor S g)
        ((a i * f (q i)) ⊗ₜ[ℤ] (w i) - (a i) ⊗ₜ[ℤ] (q i • w i))
        = ((a i * f (q i)) ⊗ₜ[ℤ] (g (w i)) - (a i) ⊗ₜ[ℤ] (q i • g (w i))) := by
      intro i
      rw [map_sub, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hg_smul i]
    dsimp only [B]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hterm i]
  have hBal : (LinearMap.lTensor S g) B
      ∈ AddSubgroup.closure (balRelMod f ((Fin n → R) ⧸ KR)) := by
    rw [hB2]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    refine AddSubgroup.zsmul_mem _ ?_ (c i)
    exact AddSubgroup.subset_closure ⟨a i, g (w i), q i, rfl⟩
  -- the semilinear map out of the finite presentation
  let ψ : (Fin n → R) →+ S := φ.comp p.toAddMonoidHom
  let KRz : Submodule ℤ (Fin n → R) := KR.restrictScalars ℤ
  let ψz : (Fin n → R) →ₗ[ℤ] S := { ψ with map_smul' := fun m x => ψ.map_zsmul m x }
  have hz : KRz ≤ ψz.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    show φ (p x) = 0
    rw [LinearMap.mem_ker.mp (hKR_le (show x ∈ KR from hx)), map_zero]
  let φ' : ((Fin n → R) ⧸ KR) →+ S := (Submodule.liftQ KRz ψz hz).toAddMonoidHom
  let r' : (Fin n → R) ⧸ KR := KR.mkQ vt
  have hφ'φ : ∀ (x : Fin n → R), φ' (KR.mkQ x) = φ (p x) := by
    intro x
    rw [Submodule.mkQ_apply]
    change (Submodule.liftQ KRz ψz hz) (Submodule.Quotient.mk x) = φ (p x)
    rw [Submodule.liftQ_apply]
    rfl
  have hφ'r' : φ' r' = φ r := by
    show φ' (KR.mkQ vt) = φ r
    rw [hφ'φ vt, hvt]
  have hφ'sem : ∀ (a : R) (l : (Fin n → R) ⧸ KR), φ' (a • l) = f a * φ' l := by
    intro a l
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective KR l
    rw [← hx, ← map_smul KR.mkQ a x, hφ'φ (a • x), hφ'φ x, map_smul, hφ a (p x)]
  have hzr : z ⊗ₜ[ℤ] r' = (LinearMap.lTensor S g) (z ⊗ₜ[ℤ] vt) := by
    rw [LinearMap.lTensor_tmul]
    rfl
  have hsplit : z ⊗ₜ[ℤ] vt = δ + B := by
    rw [show δ = (z ⊗ₜ[ℤ] vt) - B from rfl, sub_add_cancel]
  have htmul : Work.Section3.RkFinModel.BalancedTensorMod.tmulM f z r' = 0 := by
    apply mk_eq_zero_of_mem_closure f
    rw [hzr, hsplit, map_add, hgδ, zero_add]
    exact hBal
  refine ⟨(Fin n → R) ⧸ KR, inferInstance, inferInstance,
    Module.finitePresentation_of_free_of_surjective KR.mkQ KR.mkQ_surjective
      (by rw [Submodule.ker_mkQ]; exact hKR_fg),
    φ', hφ'sem, r', hφ'r', htmul⟩

end Work.Section3.RkFinModel
