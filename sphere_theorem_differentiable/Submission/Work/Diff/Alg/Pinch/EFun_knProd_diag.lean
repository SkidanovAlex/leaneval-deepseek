import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The isotropic curvature form of `knProd` of two diagonal tensors

Let `da = diag a`, `db = diag b` be the diagonal `2`-tensors `daᵢₖ = δᵢₖ aᵢ`, `dbⱼₗ = δⱼₗ bⱼ`.
This file computes the quartic form `EFun` of the Kulkarni–Nomizu product `knProd da db` on the
decomposable complex `2`-form `(x + iy) ∧ (z + iw)`:

`EFun (knProd da db) x y z w = ∑ᵢⱼ aᵢ bⱼ · |ζᵢ ηⱼ − ζⱼ ηᵢ|²`,  `ζ = x + iy`, `η = z + iw`.

The right-hand side is a sum of squares, so this simultaneously identifies `knProd da db` with an
explicit tensor built from the unit sphere tensors `Iso n`,

`knProd da db = (aᵢbⱼ + aⱼbᵢ) · (δᵢₖδⱼₗ − δᵢₗδⱼₖ)`,

and gives the (frame-free) complex sectional curvature of such a tensor. It is the algebraic input
for the boundary analysis of the Böhm–Wilking cones: the tensors of the form `knProd da db` are
exactly the `Ric₀² ∧ id`-type corrections appearing in the `D_{a,b}(S)` decomposition, and the
formula exhibits their `EFun` as a sum of squares with weights `aᵢbⱼ`.

## Conventions

* `knProd A B i j k l = A i k B j l - A i l B j k - A j k B i l + A j l B i k` (no `1/2`),
* `R4 R a b c d = ∑ᵢⱼₖₗ R i j k l aᵢ bⱼ cₖ dₗ`,
* `EFun R x y z w = R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 R4 R x y z w`.

## Proof outline

1. `knProd_diag`: `knProd da db = ((aᵢbⱼ + aⱼbᵢ) · Iso n i j k l)` pointwise (via the Kronecker
   deltas `id2`).
2. `R4_iso_weight`: `R4 (cᵢⱼ · Iso n i j k l) p q r s = ∑ᵢⱼ cᵢⱼ pᵢqⱼ (rᵢsⱼ − rⱼsᵢ)`, from the
   contraction `∑ₖₗ Iso n i j k l rₖ sₗ = rᵢ sⱼ − rⱼ sᵢ` (`sum_iso_contract`, a Kronecker-delta
   computation).
3. `R4_knProd_diag`: combine the two and symmetrize `cᵢⱼ = aᵢbⱼ + aⱼbᵢ` against the antisymmetric
   `rᵢsⱼ − rⱼsᵢ`, using the reindexing `i ↔ j`, to get
   `R4 (knProd da db) p q r s = ∑ᵢⱼ aᵢbⱼ (pᵢqⱼ − pⱼqᵢ)(rᵢsⱼ − rⱼsᵢ)`.
4. `normSq_pair_eq`: the pointwise complex identity
   `|(xᵢ+iyᵢ)(zⱼ+iwⱼ) − (xⱼ+iyⱼ)(zᵢ+iwᵢ)|²`
   `= (xᵢzⱼ−xⱼzᵢ)² + (xᵢwⱼ−xⱼwᵢ)² + (yᵢzⱼ−yⱼzᵢ)² + (yᵢwⱼ−yⱼwᵢ)² − 2(xᵢyⱼ−xⱼyᵢ)(zᵢwⱼ−zⱼwᵢ)`
   (the Plücker relation `(xᵢzⱼ−xⱼzᵢ)(yᵢwⱼ−yⱼwᵢ) − (xᵢwⱼ−xⱼwᵢ)(yᵢzⱼ−yⱼzᵢ) = −(xᵢyⱼ−xⱼyᵢ)(zᵢwⱼ−zⱼwᵢ)`,
   discharged by `ring` after expanding `Complex.normSq`).
5. `sum_pair_combine` reassembles the four `R4` sums and the `-2 R4` term of `EFun` into one double
   sum, and the termwise identity of step 4 finishes.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-! ## Kronecker-delta contractions -/

/-- Summation against a Kronecker delta: `∑ k, (if i = k then 1 else 0) * g k = g i`. -/
private lemma ite_delta_mul_sum {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ k, (if i = k then (1 : ℝ) else 0) * g k) = g i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have h : ¬ (i = b) := fun hh => hb hh.symm
    simp [h]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Contraction of the round-sphere tensor against a decomposable pair:
`∑ k l, Iso n i j k l * (r k * s l) = r i * s j - r j * s i`. -/
private lemma sum_iso_contract {n : ℕ} (i j : Fin n) (r s : Fin n → ℝ) :
    (∑ k, ∑ l, Iso n i j k l * (r k * s l)) = r i * s j - r j * s i := by
  have hfirst :
      (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)) * (r k * s l))
        = r i * s j := by
    have step : ∀ k, (∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)) * (r k * s l))
        = (if i = k then (1:ℝ) else 0) * (r k * s j) := by
      intro k
      rw [show (∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)) * (r k * s l))
          = (if i = k then (1:ℝ) else 0) * (∑ l, (if j = l then (1:ℝ) else 0) * (r k * s l)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _; ring]
      rw [ite_delta_mul_sum j (fun l => r k * s l)]
    rw [Finset.sum_congr rfl (fun k _ => step k)]
    exact ite_delta_mul_sum i (fun k => r k * s j)
  have hsecond :
      (∑ k, ∑ l, ((if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l))
        = r j * s i := by
    rw [Finset.sum_comm]
    have step : ∀ l, (∑ k, ((if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l))
        = (if i = l then (1:ℝ) else 0) * (r j * s l) := by
      intro l
      rw [show (∑ k, ((if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l))
          = (if i = l then (1:ℝ) else 0) * (∑ k, (if j = k then (1:ℝ) else 0) * (r k * s l)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring]
      rw [ite_delta_mul_sum j (fun k => r k * s l)]
    rw [Finset.sum_congr rfl (fun l _ => step l)]
    exact ite_delta_mul_sum i (fun l => r j * s l)
  have hmain : (∑ k, ∑ l, Iso n i j k l * (r k * s l))
      = (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)) * (r k * s l))
        - (∑ k, ∑ l, ((if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l)) := by
    simp only [Iso]
    rw [show (∑ k, ∑ l, ((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)
            - (if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l))
        = ∑ k, ∑ l, (((if i = k then (1:ℝ) else 0) * (if j = l then (1:ℝ) else 0)) * (r k * s l)
            - ((if i = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) * (r k * s l)) from by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring]
    simp only [Finset.sum_sub_distrib]
  rw [hmain, hfirst, hsecond]

/-! ## `knProd` of diagonals and its `R4` -/

/-- `knProd` of two diagonal tensors is a multiple of the round-sphere tensor:
`knProd (diag a) (diag b) i j k l = (aᵢbⱼ + aⱼbᵢ) · Iso n i j k l`. -/
private lemma knProd_diag {n : ℕ} (a b : Fin n → ℝ) :
    knProd (fun i j => if i = j then a i else 0) (fun i j => if i = j then b i else 0)
      = fun i j k l => (a i * b j + a j * b i) * Iso n i j k l := by
  have hA : (fun i j : Fin n => if i = j then a i else 0) = fun i j => a i * id2 n i j := by
    funext i j; by_cases h : i = j <;> simp [id2, h]
  have hB : (fun i j : Fin n => if i = j then b i else 0) = fun i j => b i * id2 n i j := by
    funext i j; by_cases h : i = j <;> simp [id2, h]
  rw [hA, hB]
  funext i j k l
  simp only [knProd]
  rw [show Iso n i j k l = id2 n i k * id2 n j l - id2 n i l * id2 n j k from rfl]
  ring

/-- Evaluation of a tensor of the form `(i j k l) ↦ cᵢⱼ · Iso n i j k l`:
`R4 (cᵢⱼ Iso n i j k l) p q r s = ∑ᵢⱼ cᵢⱼ pᵢ qⱼ (rᵢ sⱼ − rⱼ sᵢ)`. -/
private lemma R4_iso_weight {n : ℕ} (c : Fin n → Fin n → ℝ) (p q r s : Fin n → ℝ) :
    R4 (fun i j k l => c i j * Iso n i j k l) p q r s
      = ∑ i, ∑ j, c i j * p i * q j * (r i * s j - r j * s i) := by
  have step : ∀ i j, (∑ k, ∑ l, c i j * Iso n i j k l * p i * q j * r k * s l)
      = c i j * p i * q j * (r i * s j - r j * s i) := by
    intro i j
    rw [show (∑ k, ∑ l, c i j * Iso n i j k l * p i * q j * r k * s l)
        = (c i j * p i * q j) * (∑ k, ∑ l, Iso n i j k l * (r k * s l)) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      ring]
    rw [sum_iso_contract]
  rw [show R4 (fun i j k l => c i j * Iso n i j k l) p q r s
      = ∑ i, ∑ j, ∑ k, ∑ l, c i j * Iso n i j k l * p i * q j * r k * s l from rfl]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step i j))]

/-- **Master evaluation.** `R4 (knProd da db) p q r s`
`= ∑ᵢⱼ aᵢ bⱼ (pᵢqⱼ − pⱼqᵢ)(rᵢsⱼ − rⱼsᵢ)`. -/
private lemma R4_knProd_diag {n : ℕ} (a b : Fin n → ℝ) (p q r s : Fin n → ℝ) :
    R4 (knProd (fun i j => if i = j then a i else 0) (fun i j => if i = j then b i else 0)) p q r s
      = ∑ i, ∑ j, a i * b j * ((p i * q j - p j * q i) * (r i * s j - r j * s i)) := by
  rw [knProd_diag a b, R4_iso_weight (fun i j => a i * b j + a j * b i) p q r s]
  have hsym : (∑ i, ∑ j, (a i * b j + a j * b i) * p i * q j * (r i * s j - r j * s i))
      = ∑ i, ∑ j, a i * b j * ((p i * q j - p j * q i) * (r i * s j - r j * s i)) := by
    have hsplit : (∑ i, ∑ j, (a i * b j + a j * b i) * p i * q j * (r i * s j - r j * s i))
        = (∑ i, ∑ j, a i * b j * (p i * q j * (r i * s j - r j * s i)))
          + (∑ i, ∑ j, a j * b i * (p i * q j * (r i * s j - r j * s i))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      ring
    have hsecond : (∑ i, ∑ j, a j * b i * (p i * q j * (r i * s j - r j * s i)))
        = - (∑ i, ∑ j, a i * b j * (p j * q i * (r i * s j - r j * s i))) := by
      conv_lhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    have hfinal : (∑ i, ∑ j, a i * b j * (p i * q j * (r i * s j - r j * s i)))
          - (∑ i, ∑ j, a i * b j * (p j * q i * (r i * s j - r j * s i)))
        = ∑ i, ∑ j, a i * b j * ((p i * q j - p j * q i) * (r i * s j - r j * s i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [hsplit, hsecond, ← sub_eq_add_neg, hfinal]
  exact hsym

/-! ## The pointwise complex identity -/

/-- The squared modulus of the decomposable complex `2`-form in real coordinates:
`|ζᵢηⱼ − ζⱼηᵢ|²` for `ζ = x + iy`, `η = z + iw` equals the real quartic combination appearing in
`EFun` of `knProd da db`. -/
private lemma normSq_pair_eq (xi yi zi wi xj yj zj wj : ℝ) :
    Complex.normSq (((xi : ℂ) + (yi : ℂ) * Complex.I) * ((zj : ℂ) + (wj : ℂ) * Complex.I)
        - ((xj : ℂ) + (yj : ℂ) * Complex.I) * ((zi : ℂ) + (wi : ℂ) * Complex.I))
      = (xi * zj - xj * zi) * (xi * zj - xj * zi) + (xi * wj - xj * wi) * (xi * wj - xj * wi)
        + (yi * zj - yj * zi) * (yi * zj - yj * zi) + (yi * wj - yj * wi) * (yi * wj - yj * wi)
        - 2 * ((xi * yj - xj * yi) * (zi * wj - zj * wi)) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Reassembly of the four quartic sums and the `-2 R4` term of `EFun` into a single double sum. -/
private lemma sum_pair_combine {n : ℕ} (f1 f2 f3 f4 f5 : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f1 i j) + (∑ i, ∑ j, f2 i j) + (∑ i, ∑ j, f3 i j) + (∑ i, ∑ j, f4 i j)
        - 2 * (∑ i, ∑ j, f5 i j)
      = ∑ i, ∑ j, (f1 i j + f2 i j + f3 i j + f4 i j - 2 * f5 i j) := by
  have hinner : ∀ i, (∑ j, f1 i j) + (∑ j, f2 i j) + (∑ j, f3 i j) + (∑ j, f4 i j)
        - 2 * (∑ j, f5 i j)
      = ∑ j, (f1 i j + f2 i j + f3 i j + f4 i j - 2 * f5 i j) := by
    intro i
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  calc (∑ i, ∑ j, f1 i j) + (∑ i, ∑ j, f2 i j) + (∑ i, ∑ j, f3 i j) + (∑ i, ∑ j, f4 i j)
        - 2 * (∑ i, ∑ j, f5 i j)
      = ∑ i, ((∑ j, f1 i j) + (∑ j, f2 i j) + (∑ j, f3 i j) + (∑ j, f4 i j)
          - 2 * (∑ j, f5 i j)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    _ = ∑ i, ∑ j, (f1 i j + f2 i j + f3 i j + f4 i j - 2 * f5 i j) :=
        Finset.sum_congr rfl (fun i _ => hinner i)

/-- **The isotropic curvature of the Kulkarni–Nomizu product of two diagonal tensors.**

For `da = diag a`, `db = diag b` and `ζ = x + iy`, `η = z + iw`,

`EFun (knProd da db) x y z w = ∑ᵢⱼ aᵢ bⱼ |ζᵢ ηⱼ − ζⱼ ηᵢ|²`.

Equivalently (via `knProd da db = (aᵢbⱼ + aⱼbᵢ) · Iso n`): the complex sectional curvature of a
weighted sum of "coordinate plane" unit-sphere tensors is the corresponding weighted sum of the
squared moduli of `ζᵢηⱼ − ζⱼηᵢ`. -/
theorem EFun_knProd_diag (n : ℕ) (a b : Fin n → ℝ) (x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun
        (Work.Diff.Alg.Pinch.knProd (fun i j => if i = j then a i else 0)
          (fun i j => if i = j then b i else 0)) x y z w
      = ∑ i, ∑ j, (a i * b j) *
          Complex.normSq (((x i : ℂ) + (y i : ℂ) * Complex.I) * ((z j : ℂ) + (w j : ℂ) * Complex.I)
            - ((x j : ℂ) + (y j : ℂ) * Complex.I) * ((z i : ℂ) + (w i : ℂ) * Complex.I)) := by
  have hL : Work.Diff.Alg.Q2P.EFun
        (Work.Diff.Alg.Pinch.knProd (fun i j => if i = j then a i else 0)
          (fun i j => if i = j then b i else 0)) x y z w
      = ∑ i, ∑ j, (a i * b j) *
          ((x i * z j - x j * z i) * (x i * z j - x j * z i)
           + (x i * w j - x j * w i) * (x i * w j - x j * w i)
           + (y i * z j - y j * z i) * (y i * z j - y j * z i)
           + (y i * w j - y j * w i) * (y i * w j - y j * w i)
           - 2 * ((x i * y j - x j * y i) * (z i * w j - z j * w i))) := by
    rw [Work.Diff.Alg.Q2P.EFun, R4_knProd_diag a b x z x z, R4_knProd_diag a b x w x w,
      R4_knProd_diag a b y z y z, R4_knProd_diag a b y w y w, R4_knProd_diag a b x y z w]
    rw [sum_pair_combine
      (fun i j => a i * b j * ((x i * z j - x j * z i) * (x i * z j - x j * z i)))
      (fun i j => a i * b j * ((x i * w j - x j * w i) * (x i * w j - x j * w i)))
      (fun i j => a i * b j * ((y i * z j - y j * z i) * (y i * z j - y j * z i)))
      (fun i j => a i * b j * ((y i * w j - y j * w i) * (y i * w j - y j * w i)))
      (fun i j => a i * b j * ((x i * y j - x j * y i) * (z i * w j - z j * w i)))]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hL]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [normSq_pair_eq (x i) (y i) (z i) (w i) (x j) (y j) (z j) (w j)]

end Work.Diff.Alg.Pinch
