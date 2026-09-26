import Mathlib
import Submission.Work.SG.SGsepDefs

/-!
# Shared vocabulary for the `sym` (symmorphy order) certificate lemmas

`Data.SymCert.chk k a` has two halves: the `yes` half (there is `σ` with
`n² ∣ (1 - g) σ - o·n·z_g` for every generator, i.e. `o · τ` is a coboundary) and the `no` half
(for every prime `p ∣ o` there is an integer left-kernel vector `u` of `(1 - g)_{g}`, with
`∑_g u_g · (o/p) · z_g ≢ 0 (mod n)`, which witnesses that `(o/p) · τ` is *not* a coboundary).

This file contains the definitions and the elementary dot-product calculus used by the two
halves, and the abstract argument `not_isCob_of_leftKernel` in which the second half is used.

All vectors are coordinate vectors `Fin 3 → ℤ` resp. `Fin 3 → ℝ`; `dotRZ` is the real pairing,
`dotZZ` the integral one.
-/

namespace Work.SGsep

open Work.SG
open scoped BigOperators

/-! ## The two dot products -/

/-- Real-valued dot product of an integer vector with a real vector. -/
noncomputable def dotRZ (u : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ℝ := ∑ i, (u i : ℝ) * x i

/-- Integer-valued dot product. -/
def dotZZ (u w : Fin 3 → ℤ) : ℤ := ∑ i, u i * w i

theorem dotRZ_toRVec (u w : Fin 3 → ℤ) :
    dotRZ u (toRVec w) = (dotZZ u w : ℝ) := by
  simp only [dotRZ, dotZZ, toRVec, Fin.sum_univ_three]
  push_cast
  ring

theorem dotRZ_add (u : Fin 3 → ℤ) (x y : Fin 3 → ℝ) :
    dotRZ u (x + y) = dotRZ u x + dotRZ u y := by
  simp only [dotRZ, Fin.sum_univ_three, Pi.add_apply]
  ring

theorem dotRZ_sub (u : Fin 3 → ℤ) (x y : Fin 3 → ℝ) :
    dotRZ u (x - y) = dotRZ u x - dotRZ u y := by
  simp only [dotRZ, Fin.sum_univ_three, Pi.sub_apply]
  ring

theorem dotRZ_smul (u : Fin 3 → ℤ) (a : ℝ) (x : Fin 3 → ℝ) :
    dotRZ u (a • x) = a * dotRZ u x := by
  simp only [dotRZ, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

/-- The integer matrix acts on the real vector; the adjoint action lands in integer vectors.
`∑ᵢ uᵢ (A x)ᵢ = ∑ₖ (∑ᵢ uᵢ Aᵢₖ) xₖ`. -/
theorem dotRZ_mulVec (u : Fin 3 → ℤ) (A : IMat) (x : Fin 3 → ℝ) :
    dotRZ u ((toRMat A).mulVec x) = dotRZ (fun k => ∑ i, u i * A i k) x := by
  simp only [dotRZ, Matrix.mulVec, dotProduct, toRMat, Matrix.map_apply, Fin.sum_univ_three]
  simp only [Int.coe_castRingHom]
  push_cast
  ring

/-- `dotRZ` of a vector whose coordinates are `wᵢ / n`. -/
theorem dotRZ_div (u w : Fin 3 → ℤ) (n : ℕ) :
    dotRZ u (fun i => (w i : ℝ) / n) = (dotZZ u w : ℝ) / n := by
  have h1 : ∀ i : Fin 3, (u i : ℝ) * ((w i : ℝ) / (n : ℝ)) = ((u i * w i : ℤ) : ℝ) / (n : ℝ) := by
    intro i
    push_cast
    ring
  simp only [dotRZ, dotZZ]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_div]
  push_cast
  rfl

/-- Scaling the right factor of the integer dot product. -/
theorem dotZZ_smul (u z : Fin 3 → ℤ) (c : ℤ) :
    dotZZ u (fun i => c * z i) = c * dotZZ u z := by
  simp only [dotZZ, Fin.sum_univ_three]
  ring

/-! ## The left-kernel data of a `SymCert` -/

/-- The `g`-th block of the certificate vector `u`, as a coordinate vector. -/
def ublk (u : List ℤ) (g : ℕ) : Fin 3 → ℤ := ((Data.blocks u).getD g Data.V3.zero).toFun

/-- Kernel condition of the certificate: `∑_g (u_g - A_gᵀ u_g) = 0` for the generators `A_g`. -/
def KernCond (D : Data.ArithData) (u : List ℤ) : Prop :=
  List.foldl (fun acc g => Data.V3.add acc (Data.V3.sub ((Data.blocks u).getD g Data.V3.zero)
      (Data.M3.tmulV (D.gens.getD g Data.M3.one) ((Data.blocks u).getD g Data.V3.zero))))
    Data.V3.zero (List.range D.gens.length) = Data.V3.zero

/-- Dot-product condition of the certificate: `n ∤ ∑_g u_g · (o/p) z_g`. -/
def DotCond (D : Data.ArithData) (o p : ℕ) (z : ℕ → Data.V3) (u : List ℤ) : Prop :=
  ¬ ((D.n : ℤ) ∣ List.foldl (fun acc g => acc + Data.V3.dot ((Data.blocks u).getD g Data.V3.zero)
      (Data.V3.smul ((o / p : ℕ) : ℤ) (z g))) 0 (List.range D.gens.length))

/-! ## The abstract argument -/

/-- **A left-kernel vector kills the coboundary equation.**
Let `P` be an integral point group, `τ` a cocycle on it, `c, n : ℕ`, and let `A g` (`g < G`) be
elements of `P` on which `τ` takes the values `z g / n`.  If the integer vectors `u g` satisfy

* `∑_g u_g · (x - A_g x) = 0` for every `x : ℝ³` (the "left kernel" of the stacked
  `(1 - A_g)`), and
* `n ∤ ∑_g u_g · (c · z_g)`,

then `c • τ` is not an integral coboundary on `P`.

Indeed a potential `σ` with `(c • τ)(A_g) - (σ - A_g σ) ∈ ℤ³` would give
`∑_g u_g·(c z_g) / n = ∑_g u_g · w_g ∈ ℤ` with `w_g ∈ ℤ³`, so `n` would divide
`∑_g u_g·(c z_g)`. -/
theorem not_isCob_of_leftKernel {P : Set IMat} {τ : IMat → Fin 3 → ℝ}
    (c n G : ℕ) (hn : 0 < n) (A : ℕ → IMat) (z u : ℕ → Fin 3 → ℤ)
    (hA : ∀ g, g < G → A g ∈ P)
    (hτ : ∀ g, g < G → τ (A g) = fun i => (z g i : ℝ) / n)
    (hker : ∀ x : Fin 3 → ℝ,
      ∑ g ∈ Finset.range G, dotRZ (u g) (x - (toRMat (A g)).mulVec x) = 0)
    (hndvd : ¬ (n : ℤ) ∣ ∑ g ∈ Finset.range G, dotZZ (u g) (fun i => (c : ℤ) * z g i)) :
    ¬ IsCob P (fun A => (c : ℝ) • τ A) := by
  rintro ⟨σ, hσ⟩
  have hw : ∀ g, g < G → ∃ w : Fin 3 → ℤ, ∀ i, (w i : ℝ) =
      ((c : ℝ) • τ (A g) - (σ - (toRMat (A g)).mulVec σ)) i := by
    intro g hg
    obtain ⟨w, hw⟩ := mem_zLat.mp (hσ (A g) (hA g hg))
    exact ⟨w, fun i => congrFun hw i⟩
  set w : ℕ → Fin 3 → ℤ := fun g => if h : g < G then (hw g h).choose else 0 with hwdef
  have hwspec : ∀ g (hg : g < G), ∀ i, (w g i : ℝ) =
      ((c : ℝ) • τ (A g) - (σ - (toRMat (A g)).mulVec σ)) i := by
    intro g hg i
    have h := (hw g hg).choose_spec
    simp only [hwdef]
    rw [dite_eq_left hg]
    exact h i
  have step1 : ∀ g, g < G → dotRZ (u g) ((c : ℝ) • τ (A g)) =
      (dotZZ (u g) (fun i => (c : ℤ) * z g i) : ℝ) / n := by
    intro g hg
    rw [hτ g hg, dotRZ_smul, dotRZ_div, dotZZ_smul]
    push_cast
    ring
  have step3 : ∀ g (hg : g < G), dotRZ (u g) ((c : ℝ) • τ (A g)) =
      dotRZ (u g) (σ - (toRMat (A g)).mulVec σ) + (dotZZ (u g) (w g) : ℝ) := by
    intro g hg
    have h : (c : ℝ) • τ (A g) = (σ - (toRMat (A g)).mulVec σ) + toRVec (w g) := by
      funext i
      have h1 := hwspec g hg i
      simp only [Pi.sub_apply] at h1
      simp only [Pi.add_apply, Pi.sub_apply, toRVec]
      linarith
    rw [h, dotRZ_add, dotRZ_toRVec]
  have hS : ((∑ g ∈ Finset.range G, dotZZ (u g) (fun i => (c : ℤ) * z g i) : ℤ) : ℝ)
      = ∑ g ∈ Finset.range G, (dotZZ (u g) (fun i => (c : ℤ) * z g i) : ℝ) := by
    push_cast
    rfl
  have hK : ((∑ g ∈ Finset.range G, dotZZ (u g) (w g) : ℤ) : ℝ)
      = ∑ g ∈ Finset.range G, (dotZZ (u g) (w g) : ℝ) := by
    push_cast
    rfl
  have key : ((∑ g ∈ Finset.range G, dotZZ (u g) (fun i => (c : ℤ) * z g i) : ℤ) : ℝ) / n
      = ((∑ g ∈ Finset.range G, dotZZ (u g) (w g) : ℤ) : ℝ) := by
    rw [hS, hK, Finset.sum_div]
    rw [Finset.sum_congr rfl (fun g hg => (step1 g (Finset.mem_range.mp hg)).symm)]
    rw [Finset.sum_congr rfl (fun g hg => step3 g (Finset.mem_range.mp hg))]
    rw [Finset.sum_add_distrib, hker σ, zero_add]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hInt : (∑ g ∈ Finset.range G, dotZZ (u g) (fun i => (c : ℤ) * z g i))
      = (∑ g ∈ Finset.range G, dotZZ (u g) (w g)) * (n : ℤ) := by
    have h := key
    rw [div_eq_iff hn'] at h
    push_cast at h
    exact_mod_cast h
  exact hndvd ⟨∑ g ∈ Finset.range G, dotZZ (u g) (w g), by rw [mul_comm]; exact hInt⟩

end Work.SGsep
