import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EFun (knProd A B) ≥ 0` for positive semidefinite `A`, `B`

For a symmetric `4`-index array `R` the complex sectional curvature form is

`EFun R x y z w = R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 R4 R x y z w`,

and `InPIC2 R` is `∀ x y z w, 0 ≤ EFun R x y z w` (`Submission/Diff/Alg`).

The main theorem of this file, `EFun_knProd_psd`, says that for symmetric *positive semidefinite*
`2`-tensors `A`, `B` the Kulkarni–Nomizu product `A ∧ B` has nonnegative complex sectional
curvature.  (This generalises `inPIC2_knProd_gram`, which only treats `knProd (A Aᵀ) (A Aᵀ)`.)

## Proof

`A`, `B` positive semidefinite means, via `Matrix.posSemidef_iff_eq_sum_vecMulVec`, that they are
finite sums of rank-one forms `u ⊗ u`, resp. `v ⊗ v`.  `knProd` is bilinear and `EFun` is additive
in the tensor variable, so it suffices to treat the rank-one case.  There the tensor collapses to
`W ⊗ W` with `W = u ∧ v` the rank-one (decomposable) `2`-form, and

`EFun (W ⊗ W) x y z w = (W(x,z) - W(y,w))² + (W(x,w) + W(y,z))² ≥ 0`

by the Plücker relation.

## Conventions

`R4 R a b c d = ∑ᵢⱼₖₗ Rᵢⱼₖₗ aᵢbⱼcₖdₗ`,
`knProd A B i j k l = AᵢₖBⱼₗ - AᵢₗBⱼₖ - AⱼₖBᵢₗ + AⱼₗBᵢₖ` (no `1/2`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Additivity of `EFun` in the tensor variable -/

private lemma R4_add_tensor (R S : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 (R + S) a b c d = R4 R a b c d + R4 S a b c d := by
  simp only [R4, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma EFun_add (R S : Curv4 n) (x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun (R + S) x y z w
      = Work.Diff.Alg.Q2P.EFun R x y z w + Work.Diff.Alg.Q2P.EFun S x y z w := by
  simp only [Work.Diff.Alg.Q2P.EFun, R4_add_tensor]
  ring

private lemma EFun_sum_finset {ι : Type*} (F : ι → Curv4 n) (s : Finset ι)
    (x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun (∑ i ∈ s, F i) x y z w
      = ∑ i ∈ s, Work.Diff.Alg.Q2P.EFun (F i) x y z w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Work.Diff.Alg.Q2P.EFun, R4]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EFun_add, ih]

private lemma EFun_sum {ι : Type*} [Fintype ι] (F : ι → Curv4 n) (x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun (∑ i, F i) x y z w
      = ∑ i, Work.Diff.Alg.Q2P.EFun (F i) x y z w :=
  EFun_sum_finset F Finset.univ x y z w

/-! ## Evaluation of `R4` on `knProd` of rank-one tensors -/

/-- The bilinear evaluation `∑ᵢⱼ Aᵢⱼ pᵢ qⱼ`. -/
private noncomputable def A2 (A : Fin n → Fin n → ℝ) (p q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * p i * q j

/-- The antisymmetric pairing `W(p,q) = (u·p)(v·q) - (u·q)(v·p)`. -/
private noncomputable def Wv (u v p q : Fin n → ℝ) : ℝ :=
  (∑ i, u i * p i) * (∑ j, v j * q j) - (∑ i, u i * q i) * (∑ j, v j * p j)

/-- Factoring a four-fold sum whose summand is a product of an `(a,c)`-factor and a `(b,d)`-factor. -/
private lemma sum4_factor (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d) = (∑ a, ∑ c, f a c) * (∑ b, ∑ d, g b d) := by
  have hswap : (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d)
      = ∑ a, ∑ c, ∑ b, ∑ d, f a c * g b d := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum]

/-- Variant of `sum4_factor` with the two contraction patterns crossed. -/
private lemma sum4_factor' (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a d * g b c) = (∑ a, ∑ d, f a d) * (∑ b, ∑ c, g b c) := by
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, f a d * g b c)
      = (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d) from by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    exact Finset.sum_comm]
  exact sum4_factor f g

/-- Expansion of `R4 (knProd A B)` as a difference of four four-fold sums, with the summands
ordered so that each one factors against a `(a,c)`/`(b,d)` or a `(a,d)`/`(b,c)` pattern. -/
private lemma R4_knProd_expand (A B : Fin n → Fin n → ℝ) (p q r s : Fin n → ℝ) :
    R4 (knProd A B) p q r s
      = (∑ i, ∑ j, ∑ k, ∑ l, (A i k * p i * r k) * (B j l * q j * s l))
        - (∑ i, ∑ j, ∑ k, ∑ l, (A i l * p i * s l) * (B j k * q j * r k))
        - (∑ i, ∑ j, ∑ k, ∑ l, (B i l * p i * s l) * (A j k * q j * r k))
        + (∑ i, ∑ j, ∑ k, ∑ l, (B i k * p i * r k) * (A j l * q j * s l)) := by
  rw [R4]
  have key : ∀ i j k l : Fin n,
      knProd A B i j k l * p i * q j * r k * s l
        = (A i k * p i * r k) * (B j l * q j * s l) - (A i l * p i * s l) * (B j k * q j * r k)
          - (B i l * p i * s l) * (A j k * q j * r k) + (B i k * p i * r k) * (A j l * q j * s l) := by
    intro i j k l
    simp only [knProd]
    ring
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **Master evaluation.** For arbitrary `A`, `B`,
`R4 (knProd A B) p q r s = A2 A p r * A2 B q s - A2 A p s * A2 B q r - A2 B p s * A2 A q r
+ A2 B p r * A2 A q s`. -/
private lemma R4_knProd (A B : Fin n → Fin n → ℝ) (p q r s : Fin n → ℝ) :
    R4 (knProd A B) p q r s
      = A2 A p r * A2 B q s - A2 A p s * A2 B q r - A2 B p s * A2 A q r
        + A2 B p r * A2 A q s := by
  rw [R4_knProd_expand,
    sum4_factor (fun i k => A i k * p i * r k) (fun j l => B j l * q j * s l),
    sum4_factor' (fun i l => A i l * p i * s l) (fun j k => B j k * q j * r k),
    sum4_factor' (fun i l => B i l * p i * s l) (fun j k => A j k * q j * r k),
    sum4_factor (fun i k => B i k * p i * r k) (fun j l => A j l * q j * s l)]
  rfl

/-- `A2` of a rank-one tensor `u ⊗ u`. -/
private lemma A2_rankOne (u p r : Fin n → ℝ) :
    A2 (fun i j => u i * u j) p r = (∑ i, u i * p i) * (∑ j, u j * r j) := by
  simp only [A2]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  ring

/-- **Rank-one evaluation.** For `A = u ⊗ u`, `B = v ⊗ v` the tensor `knProd A B` collapses to
`W ⊗ W` with `W = u ∧ v`, so `R4` is the product of the two `W`-pairings. -/
private lemma R4_knProd_rankOne (u v p q r s : Fin n → ℝ) :
    R4 (knProd (fun i j => u i * u j) (fun i j => v i * v j)) p q r s
      = Wv u v p q * Wv u v r s := by
  rw [R4_knProd]
  rw [A2_rankOne u p r, A2_rankOne v q s, A2_rankOne u p s, A2_rankOne v q r,
    A2_rankOne v p s, A2_rankOne u q r, A2_rankOne v p r, A2_rankOne u q s]
  simp only [Wv]
  ring

/-! ## The rank-one `EFun` and its nonnegativity -/

/-- `EFun` of a rank-one Kulkarni–Nomizu product is a sum of two squares (Plücker relation). -/
private lemma EFun_knProd_rankOne (u v x y z w : Fin n → ℝ) :
    Work.Diff.Alg.Q2P.EFun (knProd (fun i j => u i * u j) (fun i j => v i * v j)) x y z w
      = (Wv u v x z - Wv u v y w) ^ 2 + (Wv u v x w + Wv u v y z) ^ 2 := by
  have e1 := R4_knProd_rankOne u v x z x z
  have e2 := R4_knProd_rankOne u v x w x w
  have e3 := R4_knProd_rankOne u v y z y z
  have e4 := R4_knProd_rankOne u v y w y w
  have e5 := R4_knProd_rankOne u v x y z w
  simp only [Work.Diff.Alg.Q2P.EFun, e1, e2, e3, e4, e5, Wv]
  ring

/-- `EFun` of a rank-one Kulkarni–Nomizu product is nonnegative. -/
private lemma EFun_knProd_rankOne_nonneg (u v x y z w : Fin n → ℝ) :
    0 ≤ Work.Diff.Alg.Q2P.EFun (knProd (fun i j => u i * u j) (fun i j => v i * v j)) x y z w := by
  rw [EFun_knProd_rankOne]
  positivity

/-! ## Bilinearity of `knProd` over finite sums -/

private lemma knProd_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Fin n → Fin n → ℝ) (g : κ → Fin n → Fin n → ℝ) :
    knProd (∑ i, f i) (∑ j, g j) = ∑ i, ∑ j, knProd (f i) (g j) := by
  funext a b c d
  have hR : (∑ i, ∑ j, knProd (f i) (g j)) a b c d
      = (∑ i, ∑ j, f i a c * g j b d) - (∑ i, ∑ j, f i a d * g j b c)
        - (∑ i, ∑ j, f i b c * g j a d) + (∑ i, ∑ j, f i b d * g j a c) := by
    simp only [Finset.sum_apply]
    have h1 : ∀ i, (∑ j, knProd (f i) (g j) a b c d)
        = ∑ j, (f i a c * g j b d - f i a d * g j b c - f i b c * g j a d
            + f i b d * g j a c) := by
      intro i
      apply Finset.sum_congr rfl; intro j _
      simp only [knProd]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hL : knProd (∑ i, f i) (∑ j, g j) a b c d
      = (∑ i, f i a c) * (∑ j, g j b d) - (∑ i, f i a d) * (∑ j, g j b c)
        - (∑ i, f i b c) * (∑ j, g j a d) + (∑ i, f i b d) * (∑ j, g j a c) := by
    simp only [knProd, Finset.sum_apply]
  rw [hL, hR]
  simp only [Finset.sum_mul_sum]

/-! ## The main theorem -/

theorem EFun_knProd_psd (n : ℕ) {A B : Fin n → Fin n → ℝ}
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, A i j * v i * v j)
    (hB : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, B i j * v i * v j)
    (x y z w : Fin n → ℝ) :
    0 ≤ Work.Diff.Alg.Q2P.EFun (Work.Diff.Alg.Pinch.knProd A B) x y z w := by
  have hApsd : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℝ) := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext (fun i j => by simp only [star_trivial]; exact hAsym j i)
    · intro v
      have hv := hA v
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hv
  have hBpsd : Matrix.PosSemidef (B : Matrix (Fin n) (Fin n) ℝ) := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext (fun i j => by simp only [star_trivial]; exact hBsym j i)
    · intro v
      have hv := hB v
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hv
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hApsd
  obtain ⟨m', v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hBpsd
  have hu' : A = ∑ k, fun i j => u k i * u k j := by
    rw [hu]
    apply Finset.sum_congr rfl; intro k _
    funext i j
    simp [Matrix.vecMulVec_apply]
  have hv' : B = ∑ l, fun i j => v l i * v l j := by
    rw [hv]
    apply Finset.sum_congr rfl; intro l _
    funext i j
    simp [Matrix.vecMulVec_apply]
  have hkn : knProd (∑ k, fun i j => u k i * u k j) (∑ l, fun i j => v l i * v l j)
      = ∑ k, ∑ l, knProd (fun i j => u k i * u k j) (fun i j => v l i * v l j) :=
    knProd_sum_sum (fun k => fun i j => u k i * u k j) (fun l => fun i j => v l i * v l j)
  have hsum : Work.Diff.Alg.Q2P.EFun
        (∑ k, ∑ l, knProd (fun i j => u k i * u k j) (fun i j => v l i * v l j)) x y z w
      = ∑ k, ∑ l, Work.Diff.Alg.Q2P.EFun
          (knProd (fun i j => u k i * u k j) (fun i j => v l i * v l j)) x y z w := by
    rw [EFun_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [EFun_sum]
  rw [hu', hv', hkn, hsum]
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro l _
  exact EFun_knProd_rankOne_nonneg (u k) (v l) x y z w

end Work.Diff.Alg.Pinch
