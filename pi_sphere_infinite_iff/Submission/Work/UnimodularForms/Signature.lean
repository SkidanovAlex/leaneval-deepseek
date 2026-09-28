/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.UnimodularForms.Basic
import Submission.Work.SignatureBordism.Signature
import Submission.Work.SignatureBordism.signature_prod
import Submission.Work.SignatureBordism.BilinearQuadratic

/-!
# The signature of an integral bilinear form

For an integral bilinear form `B` on a `ℤ`-module `M` the **signature** is defined by rationalising:

* `Work.UnimodularForms.ratBilin B` — `B ⊗ ℚ`, a `ℚ`-bilinear form on `ℚ ⊗[ℤ] M`
  (this is Mathlib's `LinearMap.BilinForm.baseChange`);
* `Work.UnimodularForms.ratForm B` — the associated quadratic form `x ↦ B x x` on `ℚ ⊗[ℤ] M`;
* `Work.UnimodularForms.sig B : ℤ` — its signature `sigPos - sigNeg`
  (`Work.SignatureBordism.signature`).

The rational model is forced: it is *canonical* in `M`, so that the signature cannot depend on the
choice of a lattice basis, and it is exactly the object that a manifold's middle intersection form
produces (`Work.SignatureBordism.sigma` is the signature of the rationalised middle intersection
form of a closed oriented `2k`-manifold; see `Submission/Work/UnimodularForms/Bridge.lean` for the
identification `Work.UnimodularForms.sig (interForm ...) = Work.SignatureBordism.sigma ...`).

## Conventions

* `rank M = Module.finrank ℤ M` is the rank of the underlying lattice (`0` if not finite free).
* Definiteness of `B` is the *integral* notion (`0 < B x x` for every nonzero lattice vector `x`,
  `Work.UnimodularForms.IsPosDef`); the signature is the rational one.  For a definite form the two
  interact as `|sig B| = rank M` (`Work.UnimodularForms.abs_sig_eq_rank_of_isDefinite`), the key
  input of the dimension-`4` and dimension-`8` applications.

## Main definitions and results

* `Work.UnimodularForms.rank`, `Work.UnimodularForms.ratBilin`, `Work.UnimodularForms.ratForm`,
  `Work.UnimodularForms.sig`
* `Work.UnimodularForms.ratBilin_tmul`, `Work.UnimodularForms.ratForm_tmul` — computation on pure
  tensors;
* `Work.UnimodularForms.sig_neg`, `Work.UnimodularForms.sig_eq_of_isIsometric`,
  `Work.UnimodularForms.sig_orthSum` — the signature is additive and an isometry invariant;
* `Work.UnimodularForms.sig_eq_rank_of_posDef`, `Work.UnimodularForms.sig_eq_neg_rank_of_negDef`,
  `Work.UnimodularForms.abs_sig_eq_rank_of_isDefinite` — **the signature of a definite form has
  absolute value the rank**;
* `Work.UnimodularForms.sigPos_add_sigNeg_eq_rank_of_isUnimodular` — for a unimodular form the
  rationalised form is nondegenerate, so `sigPos + sigNeg = rank`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

-- Make the product module structure resolve to `Prod.instModule` (the instance used by Mathlib's
-- `TensorProduct.prodRight`), avoiding the `AddCommGroup.toIntModule` diamond.
attribute [local instance 5000] Prod.instModule

namespace Work.UnimodularForms

noncomputable section

open LinearMap (BilinForm)
open scoped TensorProduct

variable {M : Type*} [AddCommGroup M] [Module ℤ M]
variable {M' : Type*} [AddCommGroup M'] [Module ℤ M']

/-- The **rank** of an integral form on `M`: the rank of the underlying `ℤ`-module (the number of
basis vectors of the lattice; `0` for a module that is not finite free). -/
def rank (M : Type*) [AddCommGroup M] [Module ℤ M] : ℕ := Module.finrank ℤ M

/-- The **rationalisation** of an integral bilinear form: the `ℚ`-bilinear form on `ℚ ⊗[ℤ] M`
with `(a ⊗ x, b ⊗ y) ↦ (a * b) • B x y`.  This is Mathlib's `LinearMap.BilinForm.baseChange`. -/
def ratBilin (B : ZForm M) : BilinForm ℚ (ℚ ⊗[ℤ] M) := B.baseChange ℚ

@[simp]
theorem ratBilin_apply (B : ZForm M) (x y : ℚ ⊗[ℤ] M) : ratBilin B x y = B.baseChange ℚ x y := rfl

/-- The **rationalised quadratic form** of an integral bilinear form, `x ↦ B x x`. -/
def ratForm (B : ZForm M) : QuadraticForm ℚ (ℚ ⊗[ℤ] M) :=
  Work.SignatureBordism.quadOfBilin (ratBilin B)

@[simp]
theorem ratForm_apply (B : ZForm M) (x : ℚ ⊗[ℤ] M) : ratForm B x = ratBilin B x x :=
  Work.SignatureBordism.quadOfBilin_apply _ x

/-- Two `ℚ`-bilinear forms on `ℚ ⊗[ℤ] M` agree if they agree on pure tensors. -/
theorem ratBilin_ext {F G : BilinForm ℚ (ℚ ⊗[ℤ] M)}
    (h : ∀ (a b : ℚ) (x y : M), F (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = G (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y)) :
    F = G := by
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul b y => exact h a b x y
      | add v w hv hw => simp [map_add, hv, hw]
  | add u w hu hw => simp [map_add, hu, hw]

theorem ratBilin_tmul (B : ZForm M) (a b : ℚ) (x y : M) :
    ratBilin B (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] y) = (B x y : ℚ) * (a * b) := by
  rw [ratBilin, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]

theorem ratForm_tmul (B : ZForm M) (a : ℚ) (x : M) :
    ratForm B (a ⊗ₜ[ℤ] x) = (B x x : ℚ) * (a * a) := by
  simp only [ratForm_apply, ratBilin_tmul]

/-- The **signature** of an integral bilinear form: the signature `sigPos - sigNeg` of its
rationalisation.  This is an integer of the same parity as `rank M`. -/
def sig (B : ZForm M) : ℤ := Work.SignatureBordism.signature (ratForm B)

@[simp]
theorem sig_def (B : ZForm M) : sig B = Work.SignatureBordism.signature (ratForm B) := rfl

/-- The rationalisation of the negation is the negation of the rationalisation. -/
@[simp]
theorem ratBilin_neg (B : ZForm M) : ratBilin (-B) = -ratBilin B := by
  refine ratBilin_ext fun a b x y => ?_
  simp [ratBilin_tmul]

@[simp]
theorem ratForm_neg (B : ZForm M) : ratForm (-B) = -ratForm B := by
  rw [ratForm, ratForm, ratBilin_neg, Work.SignatureBordism.quadOfBilin_neg]

/-! ## Clearing denominators in `ℚ ⊗[ℤ] M`

The tensor product `ℚ ⊗[ℤ] M` is the *canonical* rationalisation of the lattice `M`: it is the
source of all the signature statements below, and every element of it is a *pure* tensor.  This is
the technical heart of the two "definite" theorems (`Work.UnimodularForms.sig_eq_rank_of_posDef`):
on a definite lattice the rationalised form is definite, because a nonzero rational vector is
`n ⊗ x` with `n ≠ 0` and `x ≠ 0`.
-/

/-- Moving an integral scalar across a pure tensor (the first factor is `ℚ`). -/
theorem tmul_zsmul (a : ℚ) (c : ℤ) (x : M) :
    a ⊗ₜ[ℤ] (c • x) = (a * (c : ℚ)) ⊗ₜ[ℤ] x := by
  have h : a ⊗ₜ[ℤ] (c • x) = c • (a ⊗ₜ[ℤ] x) := by
    show ((TensorProduct.mk ℤ ℚ M a).toAddMonoidHom) (c • x)
        = c • (((TensorProduct.mk ℤ ℚ M a).toAddMonoidHom) x)
    exact map_zsmul _ c x
  rw [h, ← Int.cast_smul_eq_zsmul ℚ c (a ⊗ₜ[ℤ] x)]
  show ((c : ℚ) * a) ⊗ₜ[ℤ] x = (a * (c : ℚ)) ⊗ₜ[ℤ] x
  rw [mul_comm]

/-- A single rational can be cleared: `n ⊗ x = (1 / n.den) ⊗ (n.num • x)`. -/
theorem tmul_eq_inv_den (n : ℚ) (x : M) :
    n ⊗ₜ[ℤ] x = (1 / (n.den : ℚ)) ⊗ₜ[ℤ] (n.num • x) := by
  rw [tmul_zsmul, show (1 / (n.den : ℚ) * (n.num : ℚ)) = n by
    rw [one_div, inv_mul_eq_div]
    exact Rat.num_div_den n]

/-- Rescaling a pure tensor whose first factor is a unit fraction. -/
theorem tmul_inv_den_rescale (q : ℚ) (N : ℕ) (hN : (N : ℚ) ≠ 0) (p : ℤ) (x : M) :
    (1 / q) ⊗ₜ[ℤ] (p • x) = (1 / (q * (N : ℚ))) ⊗ₜ[ℤ] (((N : ℤ) * p) • x) := by
  rw [tmul_zsmul, tmul_zsmul]
  congr 1
  field_simp
  push_cast
  ring

/-- **Clearing denominators**: every element of `ℚ ⊗[ℤ] M` is a pure tensor. -/
theorem exists_tmul_eq (y : ℚ ⊗[ℤ] M) : ∃ (n : ℚ) (x : M), y = n ⊗ₜ[ℤ] x := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x => exact ⟨a, x, rfl⟩
  | add u v hu hv =>
      obtain ⟨n, x, rfl⟩ := hu
      obtain ⟨m, w, rfl⟩ := hv
      rcases eq_or_ne n 0 with rfl | hn
      · exact ⟨m, w, by simp⟩
      rcases eq_or_ne m 0 with rfl | hm
      · exact ⟨n, x, by simp⟩
      have hd : ((n.den : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.cast_ne_zero.mpr (Rat.den_nz n)
      have hd' : ((m.den : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.cast_ne_zero.mpr (Rat.den_nz m)
      refine ⟨1 / ((n.den : ℚ) * (m.den : ℚ)),
        (((m.den : ℤ) * n.num) • x + ((n.den : ℤ) * m.num) • w), ?_⟩
      rw [tmul_eq_inv_den n x, tmul_eq_inv_den m w,
        tmul_inv_den_rescale (n.den : ℚ) m.den hd' n.num x,
        tmul_inv_den_rescale (m.den : ℚ) n.den hd m.num w,
        show (1 : ℚ) / ((m.den : ℚ) * (n.den : ℚ)) = 1 / ((n.den : ℚ) * (m.den : ℚ)) by
          ring,
        TensorProduct.tmul_add]

/-- **The rationalisation of a positive definite form is positive definite.** -/
theorem ratForm_posDef_of_posDef (B : ZForm M) (h : IsPosDef B) : (ratForm B).PosDef := by
  intro y hy
  obtain ⟨n, x, rfl⟩ := exists_tmul_eq y
  rw [ratForm_tmul]
  have hn : n ≠ 0 := fun h0 => hy (by simp [h0])
  have hx : x ≠ 0 := fun h0 => hy (by simp [h0])
  have hpos : (0 : ℚ) < (B x x : ℚ) := by exact_mod_cast h x hx
  exact mul_pos hpos (mul_self_pos.mpr hn)

/-! ## The signature of a definite form -/

theorem sig_neg (B : ZForm M) : sig (-B) = -sig B := by
  simp [sig]

theorem sig_eq_of_isIsometric {B : ZForm M} {B' : ZForm M'} (h : IsIsometric B B') :
    sig B = sig B' := by
  obtain ⟨e, he⟩ := h
  let E := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ) e
  have hE : ∀ (a : ℚ) (x : M),
      (E : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] M') (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] e x := fun a x => by
    show (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ) e) (a ⊗ₜ[ℤ] x)
      = a ⊗ₜ[ℤ] e x
    rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have key : (ratBilin B').compl₁₂ (E : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] M')
      (E : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] M') = ratBilin B := by
    refine ratBilin_ext fun a b x y => ?_
    simp only [LinearMap.compl₁₂_apply, hE, ratBilin_tmul, he x y]
  have key2 : ∀ u : ℚ ⊗[ℤ] M, ratForm B' (E u) = ratForm B u := fun u => by
    rw [ratForm_apply, ratForm_apply, ← key, LinearMap.compl₁₂_apply]
    rfl
  have hEq : QuadraticMap.Equivalent (ratForm B) (ratForm B') :=
    ⟨QuadraticMap.IsometryEquiv.mk E key2⟩
  simpa only [sig] using Work.SignatureBordism.signature_eq_of_equiv hEq

theorem sig_orthSum [Module.Finite ℤ M] [Module.Finite ℤ M'] (B : ZForm M) (B' : ZForm M') :
    sig (orthSum B B') = sig B + sig B' := by
  let E := TensorProduct.prodRight ℤ ℚ ℚ M M'
  have hE : ∀ (a : ℚ) (x : M × M'),
      (E : ℚ ⊗[ℤ] (M × M') →ₗ[ℚ] ℚ ⊗[ℤ] M × ℚ ⊗[ℤ] M') (a ⊗ₜ[ℤ] x)
        = (a ⊗ₜ[ℤ] x.1, a ⊗ₜ[ℤ] x.2) :=
    fun a x => TensorProduct.prodRight_tmul ℤ ℚ ℚ M M' a x
  have key : ratBilin (orthSum B B')
      = ((ratBilin B).compl₁₂
          (LinearMap.fst ℚ (ℚ ⊗[ℤ] M) (ℚ ⊗[ℤ] M') ∘ₗ (E : ℚ ⊗[ℤ] (M × M') →ₗ[ℚ] _))
          (LinearMap.fst ℚ (ℚ ⊗[ℤ] M) (ℚ ⊗[ℤ] M') ∘ₗ (E : ℚ ⊗[ℤ] (M × M') →ₗ[ℚ] _)))
        + ((ratBilin B').compl₁₂
          (LinearMap.snd ℚ (ℚ ⊗[ℤ] M) (ℚ ⊗[ℤ] M') ∘ₗ (E : ℚ ⊗[ℤ] (M × M') →ₗ[ℚ] _))
          (LinearMap.snd ℚ (ℚ ⊗[ℤ] M) (ℚ ⊗[ℤ] M') ∘ₗ (E : ℚ ⊗[ℤ] (M × M') →ₗ[ℚ] _))) := by
    refine ratBilin_ext fun a b x y => ?_
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, hE, ratBilin_tmul, orthSum_apply]
    push_cast
    ring_nf
  have key2 : ∀ u : ℚ ⊗[ℤ] (M × M'),
      (ratForm B).prod (ratForm B') (E u) = ratForm (orthSum B B') u := by
    intro u
    rw [ratForm_apply, QuadraticMap.prod_apply, ratForm_apply, ratForm_apply]
    rw [key]
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    rfl
  have hEq : QuadraticMap.Equivalent (ratForm (orthSum B B'))
      ((ratForm B).prod (ratForm B')) :=
    ⟨QuadraticMap.IsometryEquiv.mk E key2⟩
  have h1 : sig (orthSum B B')
      = Work.SignatureBordism.signature ((ratForm B).prod (ratForm B')) := by
    simpa only [sig] using Work.SignatureBordism.signature_eq_of_equiv hEq
  rw [h1, sig, sig, Work.SignatureBordism.signature_prod]

theorem sig_eq_rank_of_posDef [Module.Free ℤ M] [Module.Finite ℤ M] (B : ZForm M)
    (h : IsPosDef B) : sig B = (rank M : ℤ) := by
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] M) := inferInstance
  have hpd : (ratForm B).PosDef := ratForm_posDef_of_posDef B h
  have htop : ((ratForm B).restrict (⊤ : Submodule ℚ (ℚ ⊗[ℤ] M))).PosDef := by
    intro x hx
    rw [QuadraticMap.restrict_apply]
    exact hpd x.1 fun h0 => hx (Subtype.ext h0)
  have hle := le_sigPos_of_posDef (ratForm B) htop
  rw [finrank_top ℚ (ℚ ⊗[ℤ] M)] at hle
  have hsigPos : sigPos (ratForm B) = Module.finrank ℚ (ℚ ⊗[ℤ] M) :=
    le_antisymm (sigPos_le_finrank _) hle
  have hsigNeg : sigNeg (ratForm B) = 0 := by
    have hrad := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := ratForm B)
    rw [hsigPos] at hrad
    omega
  rw [sig, Work.SignatureBordism.signature, hsigPos, hsigNeg, Nat.cast_zero, sub_zero,
    Module.finrank_baseChange]
  rfl

theorem sig_eq_neg_rank_of_negDef [Module.Free ℤ M] [Module.Finite ℤ M] (B : ZForm M)
    (h : IsNegDef B) : sig B = -(rank M : ℤ) := by
  have hpos : IsPosDef (-B) := fun x hx => by
    have := h x hx
    simpa using neg_pos.mpr this
  have hkey := sig_eq_rank_of_posDef (-B) hpos
  rw [sig_neg] at hkey
  linarith

theorem abs_sig_eq_rank_of_isDefinite [Module.Free ℤ M] [Module.Finite ℤ M] (B : ZForm M)
    (h : IsDefinite B) : (sig B).natAbs = rank M := by
  rcases h with h | h
  · rw [sig_eq_rank_of_posDef B h, Int.natAbs_natCast]
  · rw [sig_eq_neg_rank_of_negDef B h, Int.natAbs_neg, Int.natAbs_natCast]

/-- The rationalised bilinear form of a symmetric form is symmetric. -/
theorem ratBilin_symm {B : ZForm M} (hsymm : IsSymm B) :
    ∀ u v : ℚ ⊗[ℤ] M, ratBilin B u v = ratBilin B v u := by
  intro u v
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul b y => simp only [ratBilin_tmul, hsymm x y, mul_comm]
      | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]

/-- **A unimodular symmetric form has trivial radical after rationalisation**, so that
`sigPos + sigNeg = rank`. -/
theorem sigPos_add_sigNeg_eq_rank_of_isUnimodular [Module.Free ℤ M] [Module.Finite ℤ M]
    (B : ZForm M) (hsymm : IsSymm B) (h : IsUnimodular B) :
    sigPos (ratForm B) + sigNeg (ratForm B) = rank M := by
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] M) := inferInstance
  have hrad : QuadraticMap.radical (ratForm B) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem := (QuadraticMap.mem_radical_iff'.mp hu)
    have hzero : ∀ v, ratBilin B u v = 0 := by
      intro v
      have h1 := hmem.2 v
      have h2 : ratForm B (u + v)
          = ratForm B u + ratForm B v + (ratBilin B u v + ratBilin B v u) := by
        simp only [ratForm_apply, map_add, LinearMap.add_apply]
        ring
      rw [h2, hmem.1, zero_add] at h1
      have h3 : ratBilin B u v + ratBilin B v u = 0 := by linarith
      rw [ratBilin_symm hsymm u v] at h3
      linarith
    obtain ⟨n, x, rfl⟩ := exists_tmul_eq u
    rcases eq_or_ne n 0 with hn | hn
    · simp [hn]
    · have hx : x = 0 := by
        refine IsUnimodular.eq_zero_of h fun y => ?_
        have hy := hzero (1 ⊗ₜ[ℤ] y)
        rw [ratBilin_tmul] at hy
        have hn' : n * 1 ≠ 0 := by simpa using hn
        have : (B x y : ℚ) = 0 := by
          rcases mul_eq_zero.mp hy with h' | h'
          · exact h'
          · exact absurd h' hn'
        exact_mod_cast this
      simp [hx]
  have hrank := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := ratForm B)
  rw [hrad, finrank_bot, add_zero] at hrank
  rw [hrank, Module.finrank_baseChange]
  rfl

end

end Work.UnimodularForms
