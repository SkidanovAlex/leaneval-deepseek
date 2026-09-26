/-
# Holomorphy of the cusp numerator in `z`

The cusp numerator `Ncusp ℓ d τ z` of `Work.Asymptotics.KMinusCuspBallDefs` is, for fixed
`ℓ, d, τ`, an explicit finite sum of products of the `z`-functions

* `z ↦ jInvariantFun z` (through the entries of the coefficient matrix `Mcusp d τ z`),
* `z ↦ fk (ulen d m) z` (`= E₄, E₆, E₈, E₁₀, E₁₄/Δ` in the two relevant cases `d = 8, 24`),
* `z ↦ Pcusp ℓ m z`, i.e. `ℓ.L_S`, `-V`, `U² - W²`,

with `z`-independent coefficients.  Each of these factors is holomorphic on `ℍ`:

* `j = E₄³/Δ` is holomorphic because `E₄` is and `Δ` is a nowhere vanishing holomorphic
  function (`CuspFormClass.holo`, `ClassicalFacts.DeltaFun_ne_zero`),
* `fk k` reduces to a monomial in `E₄, E₆` or to `E₁₀/Δ`, `E₁₄/Δ`,
* `ℓ.L_S` is holomorphic by the structure field `LogLambdaData.holo_S`,
* `V = θ₁₀⁴`, `U = θ₀₀⁴`, `W = θ₀₁⁴` are fourth powers of the Jacobi theta functions.

Hence `z ↦ Ncusp ℓ d τ z` is holomorphic, and so is `z ↦ Ecusp z * Ncusp ℓ d τ z`, since
`Ecusp z = exp (π i z)`.  Converting a holomorphic function `ℍ → ℂ` into a complex differentiable
function on `{w : ℂ | 0 < w.im}` via `UpperHalfPlane.mdifferentiable_iff` gives the stated
differentiability of `w ↦ Ecusp (ofComplex w) * Ncusp ℓ d τ (ofComplex w)`.

The file is deliberately organised as a small library of "holomorphy of the cusp atoms", so that
the same ingredients can be reused for the other analytic arguments on the `z`-side of the kernel.
-/
import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs

namespace Work.Asymptotics.MFix

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle Topology

noncomputable section

/-! ## Elementary closure properties of `MDiff` -/

/-- `MDiff` is invariant under pointwise equality of functions. -/
lemma MDiff_congr {f g : ℍ → ℂ} (h : f = g) (hf : MDiff f) : MDiff g := h ▸ hf

/-- `MDiff` of a finite sum of functions, in the "function of `z`" form. -/
lemma MDiff_sum_fun {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (h : ∀ i ∈ s, MDiff (F i)) :
    MDiff (fun z : ℍ => ∑ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))
  | insert i s hi ih =>
      have heq : (fun z : ℍ => ∑ j ∈ insert i s, F j z)
          = fun z : ℍ => F i z + ∑ j ∈ s, F j z := by
        funext z; rw [Finset.sum_insert hi]
      rw [heq]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## Holomorphy of the classical modular forms attached to the cusp -/

lemma mdiff_jInvariantFun : MDiff Work.Kernels.jInvariantFun :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (CuspFormClass.holo CuspForm.discriminant)
    (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

lemma mdiff_E4Fun : MDiff Work.Kernels.E4Fun := ModularFormClass.holo ModularForm.E₄

lemma mdiff_E6Fun : MDiff Work.Kernels.E6Fun := ModularFormClass.holo ModularForm.E₆

lemma mdiff_DeltaFun : MDiff Work.Kernels.DeltaFun := CuspFormClass.holo CuspForm.discriminant

lemma mdiff_E8Fun : MDiff Work.Kernels.E8Fun := mdiff_E4Fun.pow 2

lemma mdiff_E10Fun : MDiff Work.Kernels.E10Fun := mdiff_E4Fun.mul mdiff_E6Fun

lemma mdiff_E14Fun : MDiff Work.Kernels.E14Fun := (mdiff_E4Fun.pow 2).mul mdiff_E6Fun

lemma mdiff_E10_div_Delta :
    MDiff (fun z : ℍ => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z) :=
  mdiff_E10Fun.div mdiff_DeltaFun (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

lemma mdiff_E14_div_Delta :
    MDiff (fun z : ℍ => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) :=
  mdiff_E14Fun.div mdiff_DeltaFun (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-! ## Holomorphy of the Jacobi theta functions and of `U, W, V` -/

lemma mdiff_theta00Fun : MDiff Work.Kernels.theta00Fun := mdifferentiable_jacobiTheta

lemma mdiff_theta01Fun : MDiff Work.Kernels.theta01Fun :=
  Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1

lemma mdiff_theta10Fun : MDiff Work.Kernels.theta10Fun :=
  Work.Kernels.ClassicalFacts.mdifferentiable_theta10Fun

lemma mdiff_UFun : MDiff Work.Kernels.UFun := mdiff_theta00Fun.pow 4

lemma mdiff_WFun : MDiff Work.Kernels.WFun := mdiff_theta01Fun.pow 4

lemma mdiff_VFun : MDiff Work.Kernels.VFun := mdiff_theta10Fun.pow 4

/-! ## Holomorphy of the cusp atoms `fk k` -/

lemma mdiff_fk_ten : MDiff (fun z : ℍ => Work.Kernels.fk 10 z) := by
  have h : (fun z : ℍ => Work.Kernels.fk 10 z) = Work.Kernels.E10Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdiff_E10Fun

lemma mdiff_fk_eight : MDiff (fun z : ℍ => Work.Kernels.fk 8 z) := by
  have h : (fun z : ℍ => Work.Kernels.fk 8 z) = Work.Kernels.E8Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdiff_E8Fun

lemma mdiff_fk_six : MDiff (fun z : ℍ => Work.Kernels.fk 6 z) := by
  have h : (fun z : ℍ => Work.Kernels.fk 6 z) = Work.Kernels.E6Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdiff_E6Fun

lemma mdiff_fk_two : MDiff (fun z : ℍ => Work.Kernels.fk 2 z) := by
  have h : (fun z : ℍ => Work.Kernels.fk 2 z)
      = fun z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdiff_E14_div_Delta

lemma mdiff_fk_zero : MDiff (fun z : ℍ => Work.Kernels.fk 0 z) := by
  have h : (fun z : ℍ => Work.Kernels.fk 0 z) = fun _ : ℍ => (1 : ℂ) := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdifferentiable_const

lemma mdiff_fk_neg_two : MDiff (fun z : ℍ => Work.Kernels.fk (-2) z) := by
  have h : (fun z : ℍ => Work.Kernels.fk (-2) z)
      = fun z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact mdiff_E10_div_Delta

/-- The `z`-weights `ulen d m` only ever take the values `10, 8, 6` (for `d = 8`) and
`2, 0, -2` (otherwise), for which `fk` is holomorphic. -/
lemma mdiff_fk_ulen (d : ℕ) (m : Fin 3) :
    MDiff (fun z : ℍ => Work.Kernels.fk (ulen d m) z) := by
  rcases eq_or_ne d 8 with rfl | hd
  · fin_cases m
    · simpa [ulen] using mdiff_fk_ten
    · simpa [ulen] using mdiff_fk_eight
    · simpa [ulen] using mdiff_fk_six
  · fin_cases m
    · simpa [ulen, hd] using mdiff_fk_two
    · simpa [ulen, hd] using mdiff_fk_zero
    · simpa [ulen, hd] using mdiff_fk_neg_two

/-! ## Holomorphy of the entries of `Mcusp` -/

/-- Any affine function of `jInvariantFun` is holomorphic. -/
lemma mdiff_affine_j (a b : ℂ) : MDiff (fun z : ℍ => a + b * Work.Kernels.jInvariantFun z) :=
  mdifferentiable_const.add (mdifferentiable_const.mul mdiff_jInvariantFun)

/-- Every entry of the coefficient matrix `Mcusp d τ z` is a holomorphic function of `z`:
for `d = 8` the matrix is independent of `z`, while for `d ≠ 8` (the branch used for `d = 24`)
its entries are constants or affine functions of `jInvariantFun z`. -/
lemma mdiff_Mcusp_entry (d : ℕ) (τ : ℍ) (i m : Fin 3) :
    MDiff (fun z : ℍ => Mcusp d τ z i m) := by
  rcases eq_or_ne d 8 with rfl | hd
  · -- `d = 8`: all entries are independent of `z`
    fin_cases i <;> fin_cases m <;> exact mdifferentiable_const
  · have h24 : (fun z : ℍ => Mcusp d τ z i m) = fun z : ℍ => Mcusp 24 τ z i m := by
      funext z; simp [Mcusp, hd]
    rw [h24]
    fin_cases i <;> fin_cases m
    · exact mdifferentiable_const
    · exact mdifferentiable_const.mul (mdifferentiable_const.sub mdiff_jInvariantFun)
    · exact mdifferentiable_const
    · exact mdifferentiable_const
    · exact mdifferentiable_const.add (mdifferentiable_const.mul
        (mdifferentiable_const.sub mdiff_jInvariantFun))
    · exact mdifferentiable_const
    · exact mdifferentiable_const
    · exact (mdifferentiable_const.sub (mdifferentiable_const.mul
        (mdifferentiable_const.sub mdiff_jInvariantFun))).sub mdifferentiable_const
    · exact mdifferentiable_const

/-! ## Holomorphy of the cusp basis `Pcusp` -/

lemma mdiff_Pcusp (ℓ : Work.Kernels.LogLambdaData) (m : Fin 3) :
    MDiff (fun z : ℍ => Pcusp ℓ m z) := by
  fin_cases m
  · change MDiff (fun z : ℍ => Pcusp ℓ (0 : Fin 3) z)
    have h : (fun z : ℍ => Pcusp ℓ (0 : Fin 3) z) = ℓ.L_S := by funext z; simp [Pcusp]
    rw [h]; exact ℓ.holo_S
  · change MDiff (fun z : ℍ => Pcusp ℓ (1 : Fin 3) z)
    have h : (fun z : ℍ => Pcusp ℓ (1 : Fin 3) z) = fun z : ℍ => - Work.Kernels.VFun z := by
      funext z; simp [Pcusp]
    rw [h]; exact mdiff_VFun.neg
  · change MDiff (fun z : ℍ => Pcusp ℓ (2 : Fin 3) z)
    have h : (fun z : ℍ => Pcusp ℓ (2 : Fin 3) z)
        = fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2 := by
      funext z; simp [Pcusp]
    rw [h]; exact (mdiff_UFun.pow 2).sub (mdiff_WFun.pow 2)

/-! ## Assembly -/

/-- For fixed `ℓ, d, τ` the cusp numerator `z ↦ Ncusp ℓ d τ z` is holomorphic on `ℍ`. -/
lemma mdiff_Ncusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) :
    MDiff (fun z : ℍ => Ncusp ℓ d τ z) := by
  have hterm : ∀ m : Fin 3, MDiff (fun z : ℍ =>
      (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
        Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) * Pcusp ℓ m z) := by
    intro m
    have hsum : MDiff (fun z : ℍ => ∑ i : Fin 3,
        Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
          Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) :=
      MDiff_sum_fun Finset.univ (fun i _ =>
        ((mdifferentiable_const.mul mdifferentiable_const).mul
          (mdiff_Mcusp_entry d τ i m)).mul (mdiff_fk_ulen d m))
    exact hsum.mul (mdiff_Pcusp ℓ m)
  have hsum : MDiff (fun z : ℍ => ∑ m : Fin 3,
      (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
        Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) * Pcusp ℓ m z) :=
    MDiff_sum_fun Finset.univ (fun m _ => hterm m)
  have hfin : MDiff (fun z : ℍ => (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ *
      ∑ m : Fin 3, (∑ i : Fin 3, Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ *
        Mcusp d τ z i m * Work.Kernels.fk (ulen d m) z) * Pcusp ℓ m z) :=
    mdifferentiable_const.mul hsum
  exact hfin

/-- The cusp parameter `Ecusp z = e^{π i z}` is holomorphic on `ℍ`. -/
lemma mdiff_Ecusp : MDiff Ecusp := by
  have hcoe : MDiff (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.mdifferentiable_coe
  have hconst : MDiff (fun _ : ℍ => (Real.pi : ℂ) * Complex.I) := mdifferentiable_const
  have hlin : MDiff (fun z : ℍ => (Real.pi : ℂ) * Complex.I * (z : ℂ)) := hconst.mul hcoe
  exact Complex.differentiable_exp.comp_mdifferentiable hlin

theorem mdiff_eta (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (fun w : ℂ => Work.Asymptotics.Ecusp (UpperHalfPlane.ofComplex w) *
      Work.Asymptotics.Ncusp ℓ d τ (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} := by
  have h : MDiff (fun z : ℍ => Ecusp z * Ncusp ℓ d τ z) :=
    mdiff_Ecusp.mul (mdiff_Ncusp ℓ d τ)
  exact UpperHalfPlane.mdifferentiable_iff.mp h

end

end Work.Asymptotics.MFix
