import Mathlib

/-!
# The tensor square of a complex of modules, by hand

This file constructs, for a cochain complex `F` of `A`-modules, the tensor square `F ⊗ F`
as an explicit cochain complex: in degree `n` it is the direct sum of `F.X i ⊗ F.X j` over
all pairs `(i, j)` with `i + j = n`, with the Koszul differential

`d (x ⊗ y) = (dx) ⊗ y + (-1)^i x ⊗ (dy)`.

The point of the explicit construction (rather than Mathlib's monoidal structure on
`HomologicalComplex`) is that the terms of the complex are then *manifestly* free modules
(direct sums of tensor products of free modules), so that the complex is K-projective as
soon as it is bounded above.  We only ever use the following interface:

* `Work.DSEQ0.TensorCpx.T` : the tensor square complex;
* `Work.DSEQ0.TensorCpx.TIncl` : the inclusion of the summand `F.X i ⊗ F.X j` into `T`;
* `Work.DSEQ0.TensorCpx.T_d` : the differential of `T`;
* `Work.DSEQ0.TensorCpx.Td_lof` : the differential on a summand, i.e. the Leibniz rule
  for the "universal" product.

The notation `(-1)^i` is `Int.negOnePow i`; it agrees with `(-1 : A) ^ i.natAbs`
(see `negOnePow_eq_pow_natAbs`).
-/

namespace Work.DSEQ0.TensorCpx

universe a

open CategoryTheory Limits

/-- `eqToHom` of a self-equality is the identity. -/
lemma eqToHom_self {C : Type*} [Category C] {X : C} (h : X = X) : eqToHom h = 𝟙 X := by
  have hh : h = rfl := Subsingleton.elim h rfl
  rw [hh, eqToHom_refl]

variable {A : Type a} [CommRing A]

/-- The index type of the degree-`n` part of `F ⊗ F`: pairs `(i, j)` with `i + j = n`. -/
abbrev TIdx (n : ℤ) : Type := {p : ℤ × ℤ // p.1 + p.2 = n}

/-- The `(i, j)`-summand of the tensor square. -/
abbrev TFam (F : CochainComplex (ModuleCat.{a} A) ℤ) (i j : ℤ) : Type a :=
  TensorProduct A (↥(F.X i)) (↥(F.X j))

/-- The degree-`n` part of the tensor square `F ⊗ F`. -/
abbrev TX (F : CochainComplex (ModuleCat.{a} A) ℤ) (n : ℤ) : Type a :=
  DirectSum (TIdx n) (fun p => TFam F p.1.1 p.1.2)

variable (F : CochainComplex (ModuleCat.{a} A) ℤ)

/-- The inclusion of the `(i, j)`-summand into the degree-`n` part of `F ⊗ F`. -/
noncomputable def TIncl (i j : ℤ) {n : ℤ} (h : i + j = n) :
    TFam F i j →ₗ[A] TX F n :=
  DirectSum.lof A (TIdx n) (fun p => TFam F p.1.1 p.1.2) ⟨(i,j), h⟩

/-- The definition of `TIncl` does not depend on the proof of the degree identity. -/
lemma TIncl_apply_eq (i j : ℤ) {n : ℤ} (h1 h2 : i + j = n) (x : TFam F i j) :
    TIncl F i j h1 x = TIncl F i j h2 x := by
  unfold TIncl
  rfl

lemma TIncl_eq (i j : ℤ) {n : ℤ} (h1 h2 : i + j = n) :
    TIncl F i j h1 = TIncl F i j h2 :=
  LinearMap.ext (fun x => TIncl_apply_eq F i j h1 h2 x)

/-- The component of the differential of `F ⊗ F` on the `(i, j)`-summand. -/
noncomputable def TdComp (i j : ℤ) {n : ℤ} (h : i + j = n) :
    TFam F i j →ₗ[A] TX F (n+1) :=
  TIncl F (i+1) j (by omega) ∘ₗ
      TensorProduct.map (F.d i (i+1)).hom LinearMap.id
  + (Int.negOnePow i : A) • (TIncl F i (j+1) (by omega) ∘ₗ
      TensorProduct.map LinearMap.id (F.d j (j+1)).hom)

/-- The differential of the tensor square `F ⊗ F`, degree `n` to degree `n + 1`. -/
noncomputable def Td (n : ℤ) : TX F n →ₗ[A] TX F (n+1) :=
  DirectSum.toModule A (TIdx n) (TX F (n+1))
    (fun p => TdComp F p.1.1 p.1.2 p.2)

/-- The differential, restricted to a summand. -/
lemma Td_lof (i j : ℤ) {n : ℤ} (h : i + j = n) :
    Td F n ∘ₗ (TIncl F i j h) = TdComp F i j h := by
  refine LinearMap.ext (fun x => ?_)
  show (DirectSum.toModule A (TIdx n) (TX F (n+1))
      (fun p => TdComp F p.1.1 p.1.2 p.2))
    ((DirectSum.lof A (TIdx n) (fun p => TFam F p.1.1 p.1.2) ⟨(i,j),h⟩) x)
    = TdComp F i j h x
  rw [DirectSum.toModule_lof]

lemma Td_apply_incl (i j : ℤ) {n : ℤ} (h : i + j = n) (x : TFam F i j) :
    Td F n (TIncl F i j h x) = TdComp F i j h x :=
  congrFun (congrArg DFunLike.coe (Td_lof F i j h)) x

/-- The differential on a pure tensor. -/
lemma TdComp_tmul (i j : ℤ) {n : ℤ} (h : i + j = n)
    (y : ↥(F.X i)) (z : ↥(F.X j)) :
    TdComp F i j h (y ⊗ₜ[A] z) =
      TIncl F (i+1) j (by omega) (((F.d i (i+1)).hom y) ⊗ₜ[A] z)
      + (Int.negOnePow i : A) • TIncl F i (j+1) (by omega)
        (y ⊗ₜ[A] ((F.d j (j+1)).hom z)) := by
  simp only [TdComp, LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, LinearMap.smul_apply]

/-- `d ∘ d = 0` on `F`, pointwise. -/
lemma F_d_comp_d (i : ℤ) (y : ↥(F.X i)) :
    (F.d (i+1) ((i+1)+1)).hom ((F.d i (i+1)).hom y) = 0 := by
  have h2 : (F.d (i+1) ((i+1)+1)).hom ∘ₗ (F.d i (i+1)).hom = 0 := by
    have h3 := congrArg (fun (f : F.X i ⟶ F.X ((i+1)+1)) => f.hom)
      (HomologicalComplex.d_comp_d F i (i+1) ((i+1)+1))
    rwa [ModuleCat.hom_comp, ModuleCat.hom_zero] at h3
  exact congrFun (congrArg DFunLike.coe h2) y

/-- The signs satisfy `(-1)^{i+1} + (-1)^i = 0`. -/
lemma negOnePow_succ_add (i : ℤ) :
    (Int.negOnePow (i+1) : A) + (Int.negOnePow i : A) = 0 := by
  rw [Int.negOnePow_succ]
  simp

/-- The `(i,j)`-component of `d ∘ d`. -/
lemma Td_comp_tmul (i j : ℤ) {n : ℤ} (h : i + j = n)
    (y : ↥(F.X i)) (z : ↥(F.X j)) :
    Td F (n+1) (TdComp F i j h (y ⊗ₜ[A] z)) = 0 := by
  rw [TdComp_tmul F i j h y z, map_add, LinearMap.map_smul,
    Td_apply_incl, Td_apply_incl]
  rw [TdComp_tmul F (i+1) j (by omega) ((F.d i (i+1)).hom y) z,
    TdComp_tmul F i (j+1) (by omega) y ((F.d j (j+1)).hom z)]
  rw [F_d_comp_d, TensorProduct.zero_tmul, map_zero,
    F_d_comp_d, TensorProduct.tmul_zero, map_zero]
  simp only [smul_zero, add_zero, zero_add]
  rw [← TIncl_eq F (i+1) (j+1) (by omega) (by omega), ← add_smul,
    negOnePow_succ_add, zero_smul]

/-- `d ∘ d = 0` for the tensor square. -/
lemma Td_comp (n : ℤ) : Td F (n+1) ∘ₗ Td F n = 0 := by
  apply DirectSum.linearMap_ext A
  intro p
  obtain ⟨⟨i,j⟩, h⟩ := p
  change (Td F (n+1) ∘ₗ Td F n) ∘ₗ (TIncl F i j h)
      = 0 ∘ₗ (TIncl F i j h)
  rw [LinearMap.comp_assoc, Td_lof, LinearMap.zero_comp]
  refine LinearMap.ext (fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul y z => exact Td_comp_tmul F i j (by omega) y z

/-- **The tensor square complex** `F ⊗ F`. -/
noncomputable def T : CochainComplex (ModuleCat.{a} A) ℤ :=
  HomologicalComplex.mk (fun n => ModuleCat.of A (TX F n))
    (fun n m => if h : n + 1 = m then
        ModuleCat.ofHom (Td F n) ≫ eqToHom (by rw [h]) else 0)
    (by
      intro n m h
      rw [dite_eq_right]
      intro h'
      exact h (by rw [ComplexShape.up_Rel]; exact h'))
    (by
      intro n m k h1 h2
      rw [ComplexShape.up_Rel] at h1 h2
      subst h1 h2
      rw [dite_eq_left (hc := rfl), dite_eq_left (hc := rfl), eqToHom_self, eqToHom_self,
        Category.comp_id, Category.comp_id, ← ModuleCat.ofHom_comp, Td_comp,
        ModuleCat.ofHom_zero])

/-- The differential of `T` in the shape `d n (n+1)`. -/
lemma T_d (n : ℤ) : (T F).d n (n+1) = ModuleCat.ofHom (Td F n) := by
  show (if h : n + 1 = n + 1 then
      ModuleCat.ofHom (Td F n) ≫ eqToHom (by rw [h]) else 0) = ModuleCat.ofHom (Td F n)
  rw [dite_eq_left (hc := rfl), eqToHom_self, Category.comp_id]

end Work.DSEQ0.TensorCpx

namespace Work.DSEQ0.TensorCpx

universe a

open CategoryTheory Limits

variable {A : Type a} [CommRing A]

/-- `Int.negOnePow i` agrees with `(-1 : A) ^ i.natAbs`. -/
lemma negOnePow_eq_pow_natAbs (i : ℤ) :
    (Int.negOnePow i : A) = (-1 : A) ^ i.natAbs := by
  rw [← Int.cast_negOnePow_natCast A i.natAbs,
    show Int.negOnePow (i.natAbs) = Int.negOnePow i from by
      rw [Int.natCast_natAbs, Int.negOnePow_abs]]

/-- The transport `XIsoOfEq` of `T` is compatible with the summand inclusions. -/
lemma T_XIsoOfEq_TIncl (F : CochainComplex (ModuleCat.{a} A) ℤ) (i j : ℤ) {p q : ℤ}
    (h : p = q) (hp : i + j = p) (hq : i + j = q) (x : TFam F i j) :
    ((T F).XIsoOfEq h).hom (TIncl F i j hp x) = TIncl F i j hq x := by
  cases h
  rw [HomologicalComplex.XIsoOfEq_rfl]
  exact TIncl_apply_eq F i j hp hq x

end Work.DSEQ0.TensorCpx
