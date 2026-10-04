import Mathlib
import Submission.Work.Diff.STE.DeTurckJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-jet decomposition of the DeTurck operator `pPhi`: `pPhi = secOp + pN`

This file proves `Work.Diff.STE.deTurck.pPhi_decomp`: the dependence of the coordinate DeTurck
operator `pPhi = -2 Ric + L_W g` (see `Submission/Work/Diff/STE/DeTurckJet.lean`) on the *second*
spatial jet `B` of the chart matrix is exactly the scalar principal part

`secOp A B i j = Σ_{c,d} γ^{cd} B (bB c) (bB d) i j`,

equivalently `pPhi(A,L,B) = secOp A B + pPhi(A,L,0)`.

Writing `bet B m a i j` for `B (bB m) (bB a) i j` (so that `bet B m a i j = ∂_m∂_a g_{ij}`), the two
ingredients are

* the `B`-part of the Ricci tensor,
  `jRic(B) - jRic(0) = ½ (Σ_{kl} γ^{kl} bet B k j i l - Σ_{kl} γ^{kl} bet B k l i j
      - Σ_{kl} γ^{kl} bet B i j k l + Σ_{kl} γ^{kl} bet B i l k j)`   (`jRic_sub`),
* the `B`-part of `(L_W g)_{ij} = ∇_iW_j + ∇_jW_i`,
  `jnabW(B) - jnabW(0) = Σ_{ij} γ^{ij} ∂_i∂_j-`   (`jnabW_sub`),

and the combination uses only that the four "slot patterns" of a `γ`-contraction of the second jet
agree (`sum_bet_iklj`, `sum_bet_ilkj`, `sum_bet_jkil`, `sum_bet_jikl`) and the elementary identity
`Σ_c A_{bc} γ^{cp} = δ_b^p` (`Matrix.mul_nonsing_inv`).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT Work.Diff.STE.DeTurck

noncomputable section

/-! ## Elementary helpers -/

/-- The components of the second spatial jet of the chart matrix, as a function of the four
indices: `bet B m a i j = B (bB m) (bB a) i j = ∂_m∂_a g_{ij}`. -/
def bet (B : BilMat E) (m a i j : Idx E) : ℝ := B (bB m) (bB a) i j

/-- Exchange the two dummy variables of a double sum with a symmetric weight. -/
lemma sum_swap_symm {ι : Type*} [Fintype ι] (γ : ι → ι → ℝ) (hγ : ∀ a b, γ a b = γ b a)
    (f : ι → ι → ℝ) : (∑ k, ∑ l, γ k l * f k l) = ∑ k, ∑ l, γ k l * f l k := by
  have e : (∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1) = ∑ p : ι × ι, γ p.1 p.2 * f p.1 p.2 :=
    Equiv.sum_comp (Equiv.prodComm ι ι) (fun p : ι × ι => γ p.1 p.2 * f p.1 p.2)
  have e2 : (∑ p : ι × ι, γ p.1 p.2 * f p.2 p.1) = ∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1 :=
    Finset.sum_congr rfl (fun p _ => by rw [hγ p.1 p.2])
  calc ∑ k, ∑ l, γ k l * f k l
      = ∑ p : ι × ι, γ p.1 p.2 * f p.1 p.2 :=
        (Fintype.sum_prod_type (fun p : ι × ι => γ p.1 p.2 * f p.1 p.2)).symm
    _ = ∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1 := e.symm
    _ = ∑ p : ι × ι, γ p.1 p.2 * f p.2 p.1 := e2.symm
    _ = ∑ k, ∑ l, γ k l * f l k := Fintype.sum_prod_type (fun p : ι × ι => γ p.1 p.2 * f p.2 p.1)

/-- The inverse of a symmetric matrix is symmetric. -/
lemma jInv_symm (A : MatE (E := E)) (hA : ∀ i j, A i j = A j i) :
    ∀ r s : Idx E, jInv A r s = jInv A s r := by
  intro r s
  have htrans : (Matrix.of A).transpose = Matrix.of A := by
    ext i j
    simpa [Matrix.transpose_apply] using (hA i j).symm
  have h := Matrix.transpose_nonsing_inv (Matrix.of A)
  rw [htrans] at h
  have h2 := congrFun (congrFun h r) s
  rw [Matrix.transpose_apply] at h2
  exact h2.symm

/-- `A` contracted with `γ = A⁻¹` in one index: `Σ_c A y c γ^{c p} = δ_{yp}`. -/
lemma A_mul_jInv (A : MatE (E := E)) (hdet : (Matrix.of A).det ≠ 0) :
    ∀ y p : Idx E, ∑ c, A y c * jInv A c p = if y = p then 1 else 0 := by
  intro y p
  have h1 : (Matrix.of A) * (Matrix.of A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have h2 := congrFun (congrFun h1 y) p
  rwa [Matrix.mul_apply, Matrix.one_apply] at h2

/-- The `A`-`γ` contraction: `Σ_c A y c (Σ_p γ^{c p} g p) = g y`. -/
lemma sum_A_jInv_mul (A : MatE (E := E)) (hdet : (Matrix.of A).det ≠ 0)
    (y : Idx E) (g : Idx E → ℝ) :
    ∑ c, A y c * (∑ p, jInv A c p * g p) = g y := by
  have hdelta : ∀ y p : Idx E, ∑ c, A y c * jInv A c p = if y = p then 1 else 0 :=
    A_mul_jInv A hdet
  calc ∑ c, A y c * (∑ p, jInv A c p * g p)
      = ∑ c, ∑ p, A y c * jInv A c p * g p := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = ∑ p, ∑ c, A y c * jInv A c p * g p := Finset.sum_comm
    _ = ∑ p, (∑ c, A y c * jInv A c p) * g p := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ p, (if y = p then 1 else 0) * g p := by simp only [hdelta]
    _ = ∑ p, (if y = p then g p else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : y = p <;> simp [hp]
    _ = g y := by rw [Finset.sum_ite_eq]; simp

/-- Splitting a sum of a four-term linear combination. -/
lemma sum4 {ι : Type*} [Fintype ι] (f1 f2 f3 f4 : ι → ℝ) :
    (∑ x, (f1 x - f2 x - f3 x + f4 x))
      = (∑ x, f1 x) - (∑ x, f2 x) - (∑ x, f3 x) + (∑ x, f4 x) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Splitting a sum of a scaled four-term linear combination. -/
lemma sum4_scale {ι : Type*} [Fintype ι] (c : ℝ) (f1 f2 f3 f4 : ι → ℝ) :
    (∑ x, c * (f1 x - f2 x - f3 x + f4 x))
      = c * ((∑ x, f1 x) - (∑ x, f2 x) - (∑ x, f3 x) + (∑ x, f4 x)) := by
  rw [show (∑ x, c * (f1 x - f2 x - f3 x + f4 x))
      = ∑ x, (c * f1 x - c * f2 x - c * f3 x + c * f4 x) from
    Finset.sum_congr rfl (fun x _ => by ring)]
  rw [sum4]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The two-level version of `sum4_scale`. -/
lemma sum4_scale2 {ι : Type*} [Fintype ι] (c : ℝ) (f1 f2 f3 f4 : ι → ι → ℝ) :
    (∑ k, ∑ l, c * (f1 k l - f2 k l - f3 k l + f4 k l))
      = c * ((∑ k, ∑ l, f1 k l) - (∑ k, ∑ l, f2 k l) - (∑ k, ∑ l, f3 k l)
        + (∑ k, ∑ l, f4 k l)) := by
  calc ∑ k, ∑ l, c * (f1 k l - f2 k l - f3 k l + f4 k l)
      = ∑ k, c * ((∑ l, f1 k l) - (∑ l, f2 k l) - (∑ l, f3 k l) + (∑ l, f4 k l)) :=
        Finset.sum_congr rfl (fun k _ => sum4_scale c (f1 k) (f2 k) (f3 k) (f4 k))
    _ = c * ((∑ k, ∑ l, f1 k l) - (∑ k, ∑ l, f2 k l) - (∑ k, ∑ l, f3 k l)
          + (∑ k, ∑ l, f4 k l)) :=
        sum4_scale c (fun k => ∑ l, f1 k l) (fun k => ∑ l, f2 k l)
          (fun k => ∑ l, f3 k l) (fun k => ∑ l, f4 k l)

/-! ## Moving the second jet through the contractions

The four "slot patterns" of a contraction of the second jet with `γ` that occur below all reduce
to the same contracted tensor, by the two symmetry hypotheses `hB1` (in the first two slots) and
`hB2` (in the last two slots) and the symmetry of `γ`. -/

/-- `Σ_{kl} γ^{kl} T(j,k,l,i) = Σ_{kl} γ^{kl} T(k,j,i,l)`. -/
lemma sum_bet_jkil (A : MatE (E := E)) (_hA : ∀ i j, A i j = A j i)
    (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (i j : Idx E) :
    (∑ k, ∑ l, jInv A k l * bet B j k l i) = ∑ k, ∑ l, jInv A k l * bet B k j i l := by
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [bet]
  rw [hB1 j k l i, hB2 k j l i]

/-- `Σ_{kl} γ^{kl} T(j,i,k,l) = Σ_{kl} γ^{kl} T(i,j,k,l)`. -/
lemma sum_bet_jikl (A : MatE (E := E)) (_hA : ∀ i j, A i j = A j i)
    (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (i j : Idx E) :
    (∑ k, ∑ l, jInv A k l * bet B j i k l) = ∑ k, ∑ l, jInv A k l * bet B i j k l := by
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [bet]
  rw [hB1 j i k l]

/-- `Σ_{kl} γ^{kl} T(i,l,k,j) = Σ_{kl} γ^{kl} T(k,i,j,l)`. -/
lemma sum_bet_ilkj (A : MatE (E := E)) (hA : ∀ i j, A i j = A j i)
    (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (i j : Idx E) :
    (∑ k, ∑ l, jInv A k l * bet B i l k j) = ∑ k, ∑ l, jInv A k l * bet B k i j l := by
  have hγ : ∀ a b : Idx E, jInv A a b = jInv A b a := jInv_symm A hA
  have h1 : (∑ k, ∑ l, jInv A k l * bet B i l k j)
      = ∑ k, ∑ l, jInv A k l * bet B l i k j := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bet]
    rw [hB1 i l k j]
  have h2 : (∑ k, ∑ l, jInv A k l * bet B l i k j)
      = ∑ k, ∑ l, jInv A k l * bet B l i j k := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bet]
    rw [hB2 l i k j]
  rw [h1, h2]
  exact sum_swap_symm (jInv A) hγ (fun k l => bet B l i j k)

/-- `Σ_{kl} γ^{kl} T(i,k,l,j) = Σ_{kl} γ^{kl} T(k,i,j,l)`. -/
lemma sum_bet_iklj (A : MatE (E := E)) (hA : ∀ i j, A i j = A j i)
    (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (i j : Idx E) :
    (∑ k, ∑ l, jInv A k l * bet B i k l j) = ∑ k, ∑ l, jInv A k l * bet B k i j l := by
  have hγ : ∀ a b : Idx E, jInv A a b = jInv A b a := jInv_symm A hA
  rw [sum_swap_symm (jInv A) hγ (fun k l => bet B i k l j)]
  exact sum_bet_ilkj A hA B hB1 hB2 i j

/-- The expansion of the Koszul derivative `jKzD` of the second jet, summed against `γ`. -/
lemma sum_jKzD_expand (A : MatE (E := E)) (hA : ∀ i j, A i j = A j i)
    (B : BilMat E) (x y : Idx E) :
    (∑ i, ∑ j, jInv A i j * jKzD B x i j y)
      = (∑ i, ∑ j, jInv A i j * bet B x i j y)
        - (1/2) * ∑ i, ∑ j, jInv A i j * bet B x y i j := by
  have hγ : ∀ a b : Idx E, jInv A a b = jInv A b a := jInv_symm A hA
  have hsum2 : (∑ i, ∑ j, jInv A i j * bet B x j i y) = ∑ i, ∑ j, jInv A i j * bet B x i j y :=
    sum_swap_symm (jInv A) hγ (fun k l => bet B x l k y)
  have h1 : ∀ i j, jKzD B x i j y
      = (1/2) * (bet B x i j y + bet B x j i y - bet B x y i j) := by
    intro i j; simp only [jKzD, bet]
  have hinner : ∀ i, (∑ j, jInv A i j * (bet B x i j y + bet B x j i y - bet B x y i j))
      = (∑ j, jInv A i j * bet B x i j y) + (∑ j, jInv A i j * bet B x j i y)
        - (∑ j, jInv A i j * bet B x y i j) := by
    intro i
    calc ∑ j, jInv A i j * (bet B x i j y + bet B x j i y - bet B x y i j)
        = ∑ j, (jInv A i j * bet B x i j y + jInv A i j * bet B x j i y
              - jInv A i j * bet B x y i j) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = (∑ j, jInv A i j * bet B x i j y) + (∑ j, jInv A i j * bet B x j i y)
            - (∑ j, jInv A i j * bet B x y i j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit : (∑ i, ∑ j, jInv A i j * (bet B x i j y + bet B x j i y - bet B x y i j))
      = (∑ i, ∑ j, jInv A i j * bet B x i j y) + (∑ i, ∑ j, jInv A i j * bet B x j i y)
        - (∑ i, ∑ j, jInv A i j * bet B x y i j) := by
    calc ∑ i, ∑ j, jInv A i j * (bet B x i j y + bet B x j i y - bet B x y i j)
        = ∑ i, ((∑ j, jInv A i j * bet B x i j y) + (∑ j, jInv A i j * bet B x j i y)
              - (∑ j, jInv A i j * bet B x y i j)) := Finset.sum_congr rfl (fun i _ => hinner i)
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  calc ∑ i, ∑ j, jInv A i j * jKzD B x i j y
      = (1/2) * ∑ i, ∑ j, jInv A i j * (bet B x i j y + bet B x j i y - bet B x y i j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [h1 i j]; ring
    _ = (1/2) * ((∑ i, ∑ j, jInv A i j * bet B x i j y)
          + (∑ i, ∑ j, jInv A i j * bet B x j i y)
          - (∑ i, ∑ j, jInv A i j * bet B x y i j)) := by rw [hsplit]
    _ = (1/2) * ((∑ i, ∑ j, jInv A i j * bet B x i j y)
          + (∑ i, ∑ j, jInv A i j * bet B x i j y)
          - (∑ i, ∑ j, jInv A i j * bet B x y i j)) := by rw [hsum2]
    _ = (∑ i, ∑ j, jInv A i j * bet B x i j y)
          - (1/2) * ∑ i, ∑ j, jInv A i j * bet B x y i j := by ring

/-! ## The `B`-part of the Ricci tensor -/

/-- The `B`-dependence of a single curvature component. -/
lemma jRm_sub_B (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (k i l j : Idx E) :
    jRm A L B k i l j - jRm A L 0 k i l j
      = (1/2) * (bet B k j i l - bet B k l i j - bet B i j k l + bet B i l k j) := by
  have hz : ∀ u v w (s : Idx E), (0 : BilMat E) (bB u) (bB v) w s = 0 := by
    intro u v w s; simp
  simp only [jRm, jKzD, bet, hz]
  rw [hB1 k i j l, ← hB2 k l i j, ← hB2 i l k j]
  ring

/-- The `B`-part of the Ricci tensor, as a four-term contraction. -/
lemma jRic_sub (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (hB1 : ∀ m a b c, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (i j : Idx E) :
    jRic A L B i j - jRic A L 0 i j
      = (1/2) * ((∑ k, ∑ l, jInv A k l * bet B k j i l)
                - (∑ k, ∑ l, jInv A k l * bet B k l i j)
                - (∑ k, ∑ l, jInv A k l * bet B i j k l)
                + (∑ k, ∑ l, jInv A k l * bet B i l k j)) := by
  have hstep : jRic A L B i j - jRic A L 0 i j
      = ∑ k, ∑ l, jInv A k l * (jRm A L B k i l j - jRm A L 0 k i l j) := by
    simp only [jRic]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hstep]
  calc ∑ k, ∑ l, jInv A k l * (jRm A L B k i l j - jRm A L 0 k i l j)
      = ∑ k, ∑ l, jInv A k l * ((1/2) * (bet B k j i l - bet B k l i j - bet B i j k l
            + bet B i l k j)) :=
        Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun l _ => by rw [jRm_sub_B A L B hB1 hB2 k i l j]))
    _ = ∑ k, ∑ l, (1/2) * (jInv A k l * bet B k j i l - jInv A k l * bet B k l i j
            - jInv A k l * bet B i j k l + jInv A k l * bet B i l k j) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    _ = (1/2) * ((∑ k, ∑ l, jInv A k l * bet B k j i l)
                - (∑ k, ∑ l, jInv A k l * bet B k l i j)
                - (∑ k, ∑ l, jInv A k l * bet B i j k l)
                + (∑ k, ∑ l, jInv A k l * bet B i l k j)) :=
        sum4_scale2 (1/2) (fun k l => jInv A k l * bet B k j i l)
          (fun k l => jInv A k l * bet B k l i j) (fun k l => jInv A k l * bet B i j k l)
          (fun k l => jInv A k l * bet B i l k j)

/-! ## The `B`-part of `L_W g` -/

/-- The `B`-dependence of the coordinate derivative `∂_aΓ^r_{ij}` of the Christoffel symbol: only
the second derivatives of the metric contribute. -/
lemma jdGamU_sub (A : MatE (E := E)) (L : LinMat E) (B : BilMat E) (x c i j : Idx E) :
    jdGamU A L B x c i j - jdGamU A L 0 x c i j
      = ∑ p, jInv A c p * jKzD B x i j p := by
  have h0 : jdGamU A L 0 x c i j = ∑ p, jdInv A L x c p * jKz L i j p := by
    simp only [jdGamU, jKzD]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp
  have hB : jdGamU A L B x c i j
      = (∑ p, jdInv A L x c p * jKz L i j p) + ∑ p, jInv A c p * jKzD B x i j p := by
    simp only [jdGamU]
    rw [Finset.sum_add_distrib]
  rw [h0, hB, add_sub_cancel_left]

/-- The `B`-dependence of the coordinate derivative `∂_aW^c` of the DeTurck field. -/
lemma jdWU_sub (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (x c : Idx E) :
    jdWU A L B Abar Lbar Bbar x c - jdWU A L 0 Abar Lbar Bbar x c
      = ∑ i, ∑ j, jInv A i j * ∑ p, jInv A c p * jKzD B x i j p := by
  have h1 : jdWU A L B Abar Lbar Bbar x c - jdWU A L 0 Abar Lbar Bbar x c
      = ∑ i, ∑ j, jInv A i j * (jdGamU A L B x c i j - jdGamU A L 0 x c i j) := by
    simp only [jdWU]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [jdGamU_sub A L B x c i j]

/-- The `B`-dependence of the coordinate derivative `∂_aW_b` of the lowered DeTurck field. -/
lemma jdWb_sub (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (x y : Idx E) :
    jdWb A L B Abar Lbar Bbar x y - jdWb A L 0 Abar Lbar Bbar x y
      = ∑ c, A y c * (jdWU A L B Abar Lbar Bbar x c - jdWU A L 0 Abar Lbar Bbar x c) := by
  simp only [jdWb]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c _ => by ring)

/-- The `B`-dependence of `∇_aW_b`: the Christoffel and `W` terms do not see `B`. -/
lemma jnabW_sub_pre (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (x y : Idx E) :
    jnabW A L B Abar Lbar Bbar x y - jnabW A L 0 Abar Lbar Bbar x y
      = jdWb A L B Abar Lbar Bbar x y - jdWb A L 0 Abar Lbar Bbar x y := by
  simp only [jnabW]
  ring

/-- The `B`-part of `∇_aW_b`: it is the contraction of the second jet with `γ`. -/
lemma jnabW_sub (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E)
    (hdet : (Matrix.of A).det ≠ 0) (x y : Idx E) :
    jnabW A L B Abar Lbar Bbar x y - jnabW A L 0 Abar Lbar Bbar x y
      = ∑ i, ∑ j, jInv A i j * jKzD B x i j y := by
  rw [jnabW_sub_pre A L B Abar Lbar Bbar x y,
    jdWb_sub A L B Abar Lbar Bbar x y]
  rw [show (∑ c, A y c * (jdWU A L B Abar Lbar Bbar x c
        - jdWU A L 0 Abar Lbar Bbar x c))
      = ∑ c, A y c * (∑ i, ∑ j, jInv A i j * ∑ p, jInv A c p * jKzD B x i j p) from
    Finset.sum_congr rfl (fun c _ => by rw [jdWU_sub A L B Abar Lbar Bbar x c])]
  calc ∑ c, A y c * (∑ i, ∑ j, jInv A i j * ∑ p, jInv A c p * jKzD B x i j p)
      = ∑ c, ∑ i, ∑ j, A y c * (jInv A i j * ∑ p, jInv A c p * jKzD B x i j p) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        conv_lhs => rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        conv_lhs => rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ c, A y c * (jInv A i j * ∑ p, jInv A c p * jKzD B x i j p) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, jInv A i j * ∑ c, A y c * (∑ p, jInv A c p * jKzD B x i j p) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        calc ∑ c, A y c * (jInv A i j * (∑ p, jInv A c p * jKzD B x i j p))
            = ∑ c, jInv A i j * (A y c * (∑ p, jInv A c p * jKzD B x i j p)) :=
              Finset.sum_congr rfl (fun c _ => by ring)
          _ = jInv A i j * ∑ c, A y c * (∑ p, jInv A c p * jKzD B x i j p) :=
              (Finset.mul_sum Finset.univ
                (fun c => A y c * (∑ p, jInv A c p * jKzD B x i j p)) (jInv A i j)).symm
    _ = ∑ i, ∑ j, jInv A i j * jKzD B x i j y := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [sum_A_jInv_mul A hdet y (fun p => jKzD B x i j p)]

/-! ## The decomposition of the DeTurck operator -/

theorem pPhi_decomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (Abar : Work.Diff.EXT.MatE (E := E))
    (Lbar : Work.Diff.STE.DeTurck.LinMat E)
    (Bbar : Work.Diff.STE.DeTurck.BilMat E)
    (A : Work.Diff.EXT.MatE (E := E))
    (L : Work.Diff.STE.DeTurck.LinMat E)
    (B : Work.Diff.STE.DeTurck.BilMat E)
    (hA : ∀ i j, A i j = A j i)
    (hL : ∀ a i j, L (Work.Diff.EXT.bB (E := E) a) i j = L (Work.Diff.EXT.bB (E := E) a) j i)
    (hB1 : ∀ m a b c, B (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) b c
        = B (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) m) b c)
    (hB2 : ∀ m a b c, B (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) b c
        = B (Work.Diff.EXT.bB (E := E) m) (Work.Diff.EXT.bB (E := E) a) c b)
    (hdet : (Matrix.of A).det ≠ 0) :
    Work.Diff.STE.DeTurck.pPhi Abar Lbar Bbar A L B
      = Work.Diff.STE.DeTurck.secOp A B + Work.Diff.STE.DeTurck.pN Abar Lbar Bbar A L := by
  funext i j
  -- the four contracted pieces
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ∑ k, ∑ l, jInv A k l * bet B k j i l := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ k, ∑ l, jInv A k l * bet B k l i j := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ k, ∑ l, jInv A k l * bet B i j k l := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ k, ∑ l, jInv A k l * bet B k i j l := ⟨_, rfl⟩
  -- the `B`-part of the Ricci tensor
  have hRic : jRic A L B i j - jRic A L 0 i j = (1/2) * (U - V - W + P) := by
    rw [jRic_sub A L B hB1 hB2 i j, sum_bet_ilkj A hA B hB1 hB2 i j]
    rw [← hU, ← hV, ← hW, ← hP]
  -- the `B`-part of `L_W g`
  have h1 : jnabW A L B Abar Lbar Bbar i j - jnabW A L 0 Abar Lbar Bbar i j = P - (1/2) * W := by
    rw [jnabW_sub A L B Abar Lbar Bbar hdet i j, sum_jKzD_expand A hA B i j,
      sum_bet_iklj A hA B hB1 hB2 i j]
    rw [← hP, ← hW]
  have h2 : jnabW A L B Abar Lbar Bbar j i - jnabW A L 0 Abar Lbar Bbar j i = U - (1/2) * W := by
    rw [jnabW_sub A L B Abar Lbar Bbar hdet j i, sum_jKzD_expand A hA B j i,
      sum_bet_jkil A hA B hB1 hB2 i j, sum_bet_jikl A hA B hB1 i j]
    rw [← hU, ← hW]
  have hLW : jLW A L B Abar Lbar Bbar i j - jLW A L 0 Abar Lbar Bbar i j = P + U - W := by
    simp only [jLW]
    rw [show jnabW A L B Abar Lbar Bbar i j + jnabW A L B Abar Lbar Bbar j i
          - (jnabW A L 0 Abar Lbar Bbar i j + jnabW A L 0 Abar Lbar Bbar j i)
        = (jnabW A L B Abar Lbar Bbar i j - jnabW A L 0 Abar Lbar Bbar i j)
          + (jnabW A L B Abar Lbar Bbar j i - jnabW A L 0 Abar Lbar Bbar j i) from by ring]
    rw [h1, h2]
    ring
  -- the principal part is `V`
  have hsec : (∑ c, ∑ d, jInv A c d * B (bB c) (bB d) i j) = V := by
    rw [hV]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    simp only [bet]
  have hmain : -2 * (jRic A L B i j - jRic A L 0 i j)
      + (jLW A L B Abar Lbar Bbar i j - jLW A L 0 Abar Lbar Bbar i j) = V := by
    rw [hRic, hLW]
    ring
  simp only [pPhi, pN, secOp, Pi.add_apply]
  rw [hsec]
  linarith [hmain]

end

end Work.Diff.STE.deTurck
