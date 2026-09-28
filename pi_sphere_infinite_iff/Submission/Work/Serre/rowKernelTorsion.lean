import Mathlib
import Submission.Work.Kunneth.Chapter

/-!
# The row-kernel torsion lemma for a tensor product of chain complexes

Let `C` and `K` be chain complexes of `ℤ`-modules.  Suppose that in degree `q` the homology of `K`
is torsion, in the explicit sense that every cycle `z` of `K` in degree `q` has a positive multiple
which is a boundary: there is `m > 0` and `y ∈ K_{q+1}` with `d y = m • z`.  Then the same holds for
the "row" complex `C_p ⊗ K_•`: every cycle `u ∈ C_p ⊗ K_q` of `1 ⊗ d_K` has a positive multiple `M • u`
which is a boundary of the row complex, i.e. `M • u = (1 ⊗ d_K) w` for some `w ∈ C_p ⊗ K_{q+1}`.

The only hypothesis on `C` is that `C_p` is a **free** `ℤ`-module.  Choosing a basis `b` of `C_p`,
the tensor product `C_p ⊗ K_q` is the direct sum `⨁_i K_q` (the free module on the basis index with
values in `K_q`), and `1 ⊗ d_K` acts componentwise.  The cycle `u` therefore has finitely many
coordinates `Z i ∈ K_q`, each of which is a cycle; multiplying the corresponding witnesses together
gives the common multiple `M`.

Everything here is standard Künneth-type linear algebra over a principal ideal domain; the substance
of the proof is the coordinate computation
`TensorProduct.equivFinsuppOfBasisLeft_lTensor` (which is what makes the tensor product of a free
module computable coordinatewise).

## Main results

* `Work.Serre.lid_lTensor` — naturality of `TensorProduct.lid` in the second variable;
* `Work.Serre.equivFinsuppOfBasisLeft_lTensor` — coordinatewise compatibility of the
  `Finsupp`-coordinates of a tensor product with `f ⊗ id` (`f.lTensor M`);
* `Work.Serre.tensor_kernel_torsion` — the general form of the lemma;
* `Work.Serre.rowKernelTorsion` — the requested statement.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

attribute [-instance] AddCommGroup.toIntModule

set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

/-- `TensorProduct.lid` is natural in the second variable: for `f : N →ₗ[ℤ] N'` and
`y : ℤ ⊗[ℤ] N`, one has `lid ℤ N' ((f.lTensor ℤ) y) = f (lid ℤ N y)`. -/
theorem lid_lTensor {N N' : Type*} [AddCommGroup N] [Module ℤ N] [AddCommGroup N']
    [Module ℤ N'] (f : N →ₗ[ℤ] N') (y : ℤ ⊗[ℤ] N) :
    TensorProduct.lid ℤ N' (f.lTensor ℤ y) = f (TensorProduct.lid ℤ N y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [TensorProduct.lid_tmul]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **The coordinates of a tensor product are compatible with `f.lTensor M`.**

For a basis `b` of `M`, the `i`-th coordinate of `f.lTensor M x` in `M ⊗ A ≅ ι →₀ A` is `f` applied
to the `i`-th coordinate of `x`. -/
theorem equivFinsuppOfBasisLeft_lTensor {M A B : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℤ M) (f : A →ₗ[ℤ] B) (x : M ⊗[ℤ] A)
    (i : ι) :
    (TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor M x)) i
      = f ((TensorProduct.equivFinsuppOfBasisLeft b x) i) := by
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor M (b.coord i) f]
  rw [← lid_lTensor f]
  congr 1
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor M (b.coord i) f]

/-- **The row-kernel torsion lemma.**  If `M` is a free `ℤ`-module and every cycle of
`f : A →ₗ[ℤ] B` is a boundary for `g : C →ₗ[ℤ] A` up to a positive multiple, then every element of
`M ⊗[ℤ] A` killed by `id ⊗ f` is killed by `id ⊗ g` up to a positive multiple.

Concretely, for a basis `b` of `M` the tensor product `M ⊗ A` is `ι →₀ A`, and `id ⊗ f` acts
componentwise.  The components `Z i` of `Z = Φ u` are cycles of `f`; choosing for each of them a
multiple `m i • Z i = g (yOf i)` and multiplying the `m i` over the finite support `s` of `Z` gives
a common multiple `M' = ∏ i ∈ s, mOf i`.  The witness is `w = Ψ.symm Y` where `Y i` carries the
coefficient `(∏ j ∈ s.erase i, mOf j) • yOf i` (no division is needed: the "division" is the
complementary product). -/
theorem tensor_kernel_torsion {M A B C : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C]
    (hM : Module.Free ℤ M) (f : A →ₗ[ℤ] B) (g : C →ₗ[ℤ] A)
    (hker : ∀ a : A, f a = 0 → ∃ m : ℕ, 0 < m ∧ ∃ c : C, g c = m • a)
    (u : M ⊗[ℤ] A) (hu : f.lTensor M u = 0) :
    ∃ M' : ℕ, 0 < M' ∧ ∃ w : M ⊗[ℤ] C, g.lTensor M w = M' • u := by
  classical
  haveI : Module.Free ℤ M := hM
  let b := Module.Free.chooseBasis ℤ M
  let Φ : M ⊗[ℤ] A ≃ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ A) :=
    TensorProduct.equivFinsuppOfBasisLeft b
  let Ψ : M ⊗[ℤ] C ≃ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ C) :=
    TensorProduct.equivFinsuppOfBasisLeft b
  let Z : Module.Free.ChooseBasisIndex ℤ M →₀ A := Φ u
  have hZcyc : ∀ i, f (Z i) = 0 := by
    intro i
    rw [show Z i = (Φ u) i from rfl, ← equivFinsuppOfBasisLeft_lTensor b f u i, hu, map_zero]
    rfl
  have hz : ∀ i, ∃ m : ℕ, 0 < m ∧ ∃ c : C, g c = m • Z i := fun i => hker (Z i) (hZcyc i)
  let mOf : Module.Free.ChooseBasisIndex ℤ M → ℕ := fun i => Classical.choose (hz i)
  have hmOf_pos : ∀ i, 0 < mOf i := fun i => (Classical.choose_spec (hz i)).1
  have hySpec : ∀ i, ∃ c : C, g c = mOf i • Z i := fun i => (Classical.choose_spec (hz i)).2
  let yOf : Module.Free.ChooseBasisIndex ℤ M → C := fun i => Classical.choose (hySpec i)
  have hyOf : ∀ i, g (yOf i) = mOf i • Z i := fun i => Classical.choose_spec (hySpec i)
  let s : Finset (Module.Free.ChooseBasisIndex ℤ M) := Z.support
  let M' : ℕ := ∏ i ∈ s, mOf i
  have hM'pos : 0 < M' := Finset.prod_pos (fun i _ => hmOf_pos i)
  let Y : Module.Free.ChooseBasisIndex ℤ M →₀ C :=
    ∑ i ∈ s, Finsupp.single i ((∏ j ∈ s.erase i, mOf j) • yOf i)
  have hY : Finsupp.mapRange g (map_zero g) Y = M' • Z := by
    ext i
    rw [Finsupp.mapRange_apply, Finsupp.smul_apply]
    by_cases hi : i ∈ s
    · have hYi : Y i = (∏ j ∈ s.erase i, mOf j) • yOf i := by
        rw [show Y i = (∑ k ∈ s, Finsupp.single k ((∏ j ∈ s.erase k, mOf j) • yOf k)) i from rfl,
          Finsupp.finsetSum_apply]
        rw [Finset.sum_eq_single i]
        · rw [Finsupp.single_eq_same]
        · intro j hj hji
          rw [Finsupp.single_eq_of_ne (Ne.symm hji)]
        · intro hnot
          exact absurd hi hnot
      rw [hYi, map_nsmul, hyOf i, smul_smul, Finset.prod_erase_mul s mOf hi]
    · have hZi : Z i = 0 := Finsupp.notMem_support_iff.mp hi
      have hYi : Y i = 0 := by
        rw [show Y i = (∑ k ∈ s, Finsupp.single k ((∏ j ∈ s.erase k, mOf j) • yOf k)) i from rfl,
          Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero (fun j hj => Finsupp.single_eq_of_ne (by rintro rfl; exact hi hj))
      rw [hYi, map_zero, hZi, smul_zero]
  refine ⟨M', hM'pos, Ψ.symm Y, ?_⟩
  have hkey : Φ ((g.lTensor M) (Ψ.symm Y)) = Finsupp.mapRange g (map_zero g) Y := by
    ext i
    rw [Finsupp.mapRange_apply, equivFinsuppOfBasisLeft_lTensor b g (Ψ.symm Y) i,
      LinearEquiv.apply_symm_apply]
  apply Φ.injective
  rw [hkey, hY]
  show M' • Z = Φ (M' • u)
  rw [map_nsmul]

/-- **The row-kernel torsion lemma, in the form needed for the Künneth spectral sequence.**

Let `C` and `K` be chain complexes of `ℤ`-modules with `C_p` free.  If every cycle of `K` in degree
`q` is a boundary up to a positive multiple, then every element `u ∈ C_p ⊗ K_q` killed by
`1 ⊗ d_K : C_p ⊗ K_q ⟶ C_p ⊗ K_{q-1}` has a positive multiple which is a boundary
`1 ⊗ d_K : C_p ⊗ K_{q+1} ⟶ C_p ⊗ K_q`. -/
theorem rowKernelTorsion (C K : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ)
    (hF : Module.Free ℤ ↥(C.X p))
    (hcyc : ∀ z : ↥(K.X q), (K.d q (q - 1)).hom z = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X (q + 1)), (K.d (q + 1) q).hom y = m • z)
    (u : Work.Kunneth.tpSummand C K p q)
    (hu : TensorProduct.map (LinearMap.id) ((K.d q (q - 1)).hom) u = 0) :
    ∃ M : ℕ, 0 < M ∧ ∃ w : Work.Kunneth.tpSummand C K p (q + 1),
      TensorProduct.map (LinearMap.id) ((K.d (q + 1) q).hom) w = M • u := by
  exact tensor_kernel_torsion (M := ↥(C.X p)) (A := ↥(K.X q)) (B := ↥(K.X (q - 1)))
    (C := ↥(K.X (q + 1))) hF (K.d q (q - 1)).hom (K.d (q + 1) q).hom hcyc u hu

end

end Work.Serre
