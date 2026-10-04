import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A global smooth clamped inverse of a matrix family

The statement `Work.Diff.STE.B3.clampedInv_exists` asks for a globally smooth map `K` on
`Fin n → Fin n → ℝ` which

* agrees with matrix inversion on the pinched set
  `P = {G | G symmetric, a‖ξ‖² ≤ ⟨Gξ,ξ⟩ ≤ b‖ξ‖²}`,
* is *uniformly positive definite* everywhere (`lam' > 0`),
* is symmetric on the set where `G` is symmetric with `⟨Gξ,ξ⟩ ≥ a‖ξ‖²`,
* has bounded `iteratedFDeriv` of order `≤ k` on the box `{|G i j| ≤ B}`.

The construction is the natural one: a smooth bump `ψ` which is `1` on `P` and is supported in a
neighbourhood `V` of `P` on which the symmetric part of `G` is still wedged between `a/2` and
`2b + a`; the actual inverse is realised as `adj(S) · g(det S)` with `g` a smooth function equal
to `1/t` off a neighbourhood of `0` that is disjoint from the (compact) support of `ψ`; and the
global positive definiteness comes from mixing with `μ • 1`:

  `K G = ψ G • (adj (sym G) · g (det (sym G))) + (1 - ψ G) • μ • 1`.

Everything is formalised from scratch; the only inputs are Mathlib's `ContDiffBump`, the
adjugate/`Cramer` API and the elementary theory of the quadratic form `∑ i, ∑ j, A i j x i x j`.
-/


namespace Work.Diff.STE.B3

open scoped ContDiff BigOperators
open Matrix

variable {n : ℕ}

/-! ## I. Quadratic forms -/

noncomputable def blm0 (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ y)
noncomputable def qfm0 (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := blm0 A x x
noncomputable def qraw0 (G : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, G i j * x i * x j
noncomputable def symG0 (G : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (G i j + G j i) / 2

lemma qfm0_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfm0 A x = ∑ i, ∑ j, A i j * x i * x j := by
  unfold qfm0 blm0
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qraw0_sym (G : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ i, ∑ j, G j i * x i * x j) = ∑ i, ∑ j, G i j * x i * x j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qraw0_eq_qfm0 (G : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    qraw0 G x = qfm0 (symG0 G) x := by
  rw [qfm0_eq_sum]
  rw [qraw0]
  have h1 : (∑ i, ∑ j, symG0 G i j * x i * x j)
      = (1/2) * (∑ i, ∑ j, G i j * x i * x j) + (1/2) * (∑ i, ∑ j, G j i * x i * x j) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [symG0, Matrix.of_apply]
    ring
  rw [h1, qraw0_sym]
  ring

@[simp] lemma symG0_apply (G : Fin n → Fin n → ℝ) (i j : Fin n) :
    symG0 G i j = (G i j + G j i) / 2 := rfl

lemma symG0_transpose (G : Fin n → Fin n → ℝ) : (symG0 G)ᵀ = symG0 G := by
  ext i j
  simp only [Matrix.transpose_apply, symG0_apply]
  ring

/-! ## II. Bilinearity, expansion, evaluations on standard vectors -/

lemma blm0_add_right (A : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    blm0 A x (y + z) = blm0 A x y + blm0 A x z := by
  unfold blm0; rw [Matrix.mulVec_add, dotProduct_add]

lemma blm0_add_left (A : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    blm0 A (x + y) z = blm0 A x z + blm0 A y z := by
  unfold blm0; rw [add_dotProduct]

lemma blm0_smul_right (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) (t : ℝ) :
    blm0 A x (t • y) = t * blm0 A x y := by
  unfold blm0; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma blm0_smul_left (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) (t : ℝ) :
    blm0 A (t • x) y = t * blm0 A x y := by
  unfold blm0; rw [smul_dotProduct, smul_eq_mul]

lemma qfm0_smul (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (t : ℝ) :
    qfm0 A (t • y) = t ^ 2 * qfm0 A y := by
  unfold qfm0
  rw [blm0_smul_right, blm0_smul_left]
  ring

lemma qfm0_add (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    qfm0 A (x + y) = qfm0 A x + blm0 A y x + blm0 A x y + qfm0 A y := by
  unfold qfm0 blm0
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
  ring

lemma vecMul_of_transpose_eq_self {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    (x : Fin n → ℝ) : x ᵥ* A = A *ᵥ x := by
  conv_lhs => rw [← hA]
  exact Matrix.vecMul_transpose A x

lemma blm0_comm (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    blm0 A x y = blm0 A y x := by
  unfold blm0
  rw [Matrix.dotProduct_mulVec, vecMul_of_transpose_eq_self hA x, dotProduct_comm]

lemma qfm0_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x y : Fin n → ℝ) (t : ℝ) :
    qfm0 A (x + t • y) = qfm0 A x + 2 * t * blm0 A x y + t ^ 2 * qfm0 A y := by
  rw [qfm0_add, blm0_smul_right, blm0_smul_left, qfm0_smul, blm0_comm A hA y x]
  ring

lemma sq_sum_eq_dotProduct (v : Fin n → ℝ) : (∑ i, (v i) ^ 2) = v ⬝ᵥ v := by
  simp only [dotProduct, pow_two]

lemma qfm0_single (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    qfm0 A (Pi.single i (1:ℝ)) = A i i := by
  unfold qfm0 blm0
  rw [Matrix.mulVec_single_one, single_one_dotProduct]
  rfl

lemma blm0_single_single (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    blm0 A (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ)) = A i j := by
  unfold blm0
  rw [Matrix.mulVec_single_one, single_one_dotProduct]
  rfl

lemma transpose_apply_eq (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (i j : Fin n) :
    A j i = A i j := by
  have h := congrFun (congrFun hA j) i
  simp only [Matrix.transpose_apply] at h
  exact h.symm

lemma qfm0_single_add (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (i j : Fin n) :
    qfm0 A (Pi.single i (1:ℝ) + Pi.single j (1:ℝ)) = A i i + A j j + 2 * A i j := by
  rw [qfm0_add, qfm0_single, qfm0_single, blm0_single_single, blm0_single_single,
    transpose_apply_eq A hA i j]
  ring

lemma sq_sum_single (i : Fin n) :
    (∑ k, ((Pi.single i (1:ℝ) : Fin n → ℝ) k) ^ 2) = 1 := by
  rw [sq_sum_eq_dotProduct, dotProduct_single_one, Pi.single_eq_same]

lemma sq_sum_single_add {i j : Fin n} (hij : i ≠ j) :
    (∑ k, ((Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) k) ^ 2) = 2 := by
  rw [show (∑ k, ((Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) k) ^ 2)
      = (Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) ⬝ᵥ
        (Pi.single i (1:ℝ) + Pi.single j (1:ℝ) : Fin n → ℝ) from by
    rw [sq_sum_eq_dotProduct]]
  rw [dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_single_one, dotProduct_single_one, dotProduct_single_one, dotProduct_single_one]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]
  norm_num

/-! ## III. The pinched set, its compactness, and the sandwich neighbourhood -/

lemma continuous_apply_pair (i j : Fin n) :
    Continuous fun G : Fin n → Fin n → ℝ => G i j := by
  fun_prop

lemma continuous_qraw0 (ξ : Fin n → ℝ) :
    Continuous fun G : Fin n → Fin n → ℝ => qraw0 G ξ := by
  unfold qraw0
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_apply_pair i j |>.mul continuous_const).mul continuous_const

lemma qraw0_single (G : Fin n → Fin n → ℝ) (i : Fin n) :
    qraw0 G (Pi.single i (1:ℝ)) = G i i := by
  rw [qraw0_eq_qfm0, qfm0_single, symG0_apply]
  ring

lemma qraw0_single_add (G : Fin n → Fin n → ℝ) (hG : ∀ i j, G i j = G j i) (i j : Fin n) :
    qraw0 G (Pi.single i (1:ℝ) + Pi.single j (1:ℝ)) = G i i + G j j + 2 * G i j := by
  rw [qraw0_eq_qfm0, qfm0_single_add _ (symG0_transpose G), symG0_apply, symG0_apply, symG0_apply,
    hG i j]
  ring

def Pinch (a b : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {G | (∀ i j, G i j = G j i) ∧
       (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ) ∧
       (∀ ξ : Fin n → ℝ, qraw0 G ξ ≤ b * ∑ i, (ξ i) ^ 2)}

def Box (M : ℝ) : Set (Fin n → Fin n → ℝ) := {G | ∀ i j, |G i j| ≤ M}

def Sand (a b : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {G | ∀ ξ : Fin n → ℝ,
      (a/2) * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ ∧ qraw0 G ξ ≤ (2*b + a) * ∑ i, (ξ i) ^ 2}

lemma isClosed_Pinch (a b : ℝ) : IsClosed (Pinch (n := n) a b) := by
  have h1 : IsClosed {G : Fin n → Fin n → ℝ | ∀ i j, G i j = G j i} := by
    rw [show {G : Fin n → Fin n → ℝ | ∀ i j, G i j = G j i}
        = ⋂ (i : Fin n), ⋂ (j : Fin n), {G : Fin n → Fin n → ℝ | G i j = G j i} from by
      ext G; simp]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_apply_pair i j) (continuous_apply_pair j i)
  have h2 : IsClosed {G : Fin n → Fin n → ℝ |
      ∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ} := by
    rw [show {G : Fin n → Fin n → ℝ | ∀ ξ : Fin n → ℝ,
          a * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ}
        = ⋂ (ξ : Fin n → ℝ), {G : Fin n → Fin n → ℝ |
            a * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ} from by ext G; simp]
    exact isClosed_iInter fun ξ => isClosed_le continuous_const (continuous_qraw0 ξ)
  have h3 : IsClosed {G : Fin n → Fin n → ℝ |
      ∀ ξ : Fin n → ℝ, qraw0 G ξ ≤ b * ∑ i, (ξ i) ^ 2} := by
    rw [show {G : Fin n → Fin n → ℝ | ∀ ξ : Fin n → ℝ,
          qraw0 G ξ ≤ b * ∑ i, (ξ i) ^ 2}
        = ⋂ (ξ : Fin n → ℝ), {G : Fin n → Fin n → ℝ |
            qraw0 G ξ ≤ b * ∑ i, (ξ i) ^ 2} from by ext G; simp]
    exact isClosed_iInter fun ξ => isClosed_le (continuous_qraw0 ξ) continuous_const
  rw [show Pinch (n := n) a b
      = ({G : Fin n → Fin n → ℝ | ∀ i j, G i j = G j i}
         ∩ {G : Fin n → Fin n → ℝ | ∀ ξ : Fin n → ℝ,
              a * ∑ i, (ξ i) ^ 2 ≤ qraw0 G ξ})
        ∩ {G : Fin n → Fin n → ℝ | ∀ ξ : Fin n → ℝ,
              qraw0 G ξ ≤ b * ∑ i, (ξ i) ^ 2} from by
    ext G
    exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩]
  exact (h1.inter h2).inter h3

lemma isCompact_box (M : ℝ) : IsCompact (Box (n := n) M) := by
  have h : Box (n := n) M
      = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (-M) M := by
    ext G
    simp only [Box, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

lemma Pinch_subset_box {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Pinch (n := n) a b ⊆ Box (max a b) := by
  intro G hG
  obtain ⟨hsym, hlow, hup⟩ := hG
  have hdiag : ∀ i : Fin n, a ≤ G i i ∧ G i i ≤ b := by
    intro i
    constructor
    · have := hlow (Pi.single i (1:ℝ))
      rwa [qraw0_single, sq_sum_single, mul_one] at this
    · have := hup (Pi.single i (1:ℝ))
      rwa [qraw0_single, sq_sum_single, mul_one] at this
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [abs_le]
    exact ⟨by linarith [(hdiag i).1, ha, le_max_left a b, le_max_right a b],
      by linarith [(hdiag i).2, ha, le_max_left a b, le_max_right a b]⟩
  · have h5 : G i i + G j j + 2 * G i j ≤ b * 2 := by
      have := hup (Pi.single i (1:ℝ) + Pi.single j (1:ℝ))
      rwa [qraw0_single_add G hsym, sq_sum_single_add hij] at this
    have h6 : a * 2 ≤ G i i + G j j + 2 * G i j := by
      have := hlow (Pi.single i (1:ℝ) + Pi.single j (1:ℝ))
      rwa [qraw0_single_add G hsym, sq_sum_single_add hij] at this
    rw [abs_le]
    exact ⟨by linarith [(hdiag i).2, (hdiag j).2, h6, ha, hb, le_max_left a b, le_max_right a b],
      by linarith [(hdiag i).1, (hdiag j).1, h5, ha, hb, le_max_left a b, le_max_right a b]⟩

lemma isCompact_Pinch {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsCompact (Pinch (n := n) a b) :=
  (isCompact_box (max a b)).of_isClosed_subset (isClosed_Pinch a b) (Pinch_subset_box ha hb)

noncomputable def rho (a : ℝ) : ℝ := a / (4 * ((n : ℝ) + 1))

lemma rho_pos {a : ℝ} (ha : 0 < a) : 0 < rho (n := n) a := by
  unfold rho; positivity

lemma rho_mul_card_le {a : ℝ} (ha : 0 < a) : rho (n := n) a * (n : ℝ) ≤ a / 4 := by
  unfold rho
  have h4 : (0:ℝ) < 4 * ((n : ℝ) + 1) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h4]
  have hthis : (a / 4) * (4 * ((n : ℝ) + 1)) = a * ((n : ℝ) + 1) := by ring
  rw [hthis]
  nlinarith [ha, Nat.cast_nonneg (α := ℝ) n]

lemma Sand_of_ball {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : Fin n → Fin n → ℝ} (hx : x ∈ Pinch a b)
    {G : Fin n → Fin n → ℝ} (hG : ‖G - x‖ ≤ rho (n := n) a) : G ∈ Sand a b := by
  intro ξ
  have hcard : ((∑ i, |ξ i|) ^ 2) ≤ (n : ℝ) * ∑ i, (ξ i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |ξ i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at this
    simpa using this
  have hcardnn : (0:ℝ) ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdiff : |qraw0 G ξ - qraw0 x ξ| ≤ ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) := by
    have h1 : qraw0 G ξ - qraw0 x ξ
        = ∑ i, ∑ j, (G i j - x i j) * ξ i * ξ j := by
      have hA : qraw0 G ξ = ∑ i, ∑ j, G i j * ξ i * ξ j := rfl
      have hB : qraw0 x ξ = ∑ i, ∑ j, x i j * ξ i * ξ j := rfl
      rw [hA, hB, ← Finset.sum_sub_distrib]
      congr 1 with i
      rw [← Finset.sum_sub_distrib]
      congr 1 with j
      ring
    rw [h1]
    calc |∑ i, ∑ j, (G i j - x i j) * ξ i * ξ j|
        ≤ ∑ i, |∑ j, (G i j - x i j) * ξ i * ξ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(G i j - x i j) * ξ i * ξ j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ‖G - x‖ * (|ξ i| * |ξ j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have hle : |G i j - x i j| ≤ ‖G - x‖ := by
            have h1 : ‖(G - x) i j‖ ≤ ‖G - x‖ :=
              (norm_le_pi_norm ((G - x) i) j).trans (norm_le_pi_norm (G - x) i)
            simpa [Pi.sub_apply, Real.norm_eq_abs] using h1
          calc |G i j - x i j| * |ξ i| * |ξ j| ≤ ‖G - x‖ * |ξ i| * |ξ j| := by
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (abs_nonneg _))
                  (abs_nonneg _)
            _ = ‖G - x‖ * (|ξ i| * |ξ j|) := by ring
      _ = ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) := by
          have h1 : (∑ i, ∑ j, ‖G - x‖ * (|ξ i| * |ξ j|))
              = ‖G - x‖ * ∑ i, ∑ j, |ξ i| * |ξ j| := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
          have h2 : (∑ i, ∑ j, |ξ i| * |ξ j|) = (∑ i, |ξ i|) * (∑ j, |ξ j|) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
          rw [h1, h2]; ring
  have hpert : ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) ≤ (a/4) * (∑ i, (ξ i) ^ 2) := by
    have h3 : ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) ≤ rho (n := n) a * ((n:ℝ) * ∑ i, (ξ i) ^ 2) :=
      mul_le_mul hG hcard (by positivity) (le_of_lt (rho_pos (n := n) ha))
    have h4 : rho (n := n) a * ((n:ℝ) * ∑ i, (ξ i) ^ 2)
        ≤ (a/4) * ∑ i, (ξ i) ^ 2 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (rho_mul_card_le (n := n) ha) hcardnn
    linarith
  obtain ⟨hxlow, hxup⟩ := hx.2
  constructor
  · have h2 : qraw0 G ξ ≥ qraw0 x ξ - ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) := by
      have := neg_le_of_abs_le hdiff
      linarith
    have h3 : a * (∑ i, (ξ i) ^ 2) ≤ qraw0 x ξ := hxlow ξ
    nlinarith [h2, h3, hpert, hcardnn, ha]
  · have h2 : qraw0 G ξ ≤ qraw0 x ξ + ‖G - x‖ * ((∑ i, |ξ i|) ^ 2) := by
      have := le_of_abs_le hdiff
      linarith
    have h3 : qraw0 x ξ ≤ b * (∑ i, (ξ i) ^ 2) := hxup ξ
    nlinarith [h2, h3, hpert, hcardnn, ha, hb]


/-! ## IV. Cauchy--Schwarz and the lower bound for the inverse -/

lemma sq_le_mul_of_quad_nonneg {c b a : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hq : ∀ t : ℝ, 0 ≤ c + 2 * t * b + t ^ 2 * a) : b ^ 2 ≤ c * a := by
  rcases lt_or_eq_of_le ha with hapos | haz
  · have h := hq (-b / a)
    have hsimp : c + 2 * (-b / a) * b + (-b / a) ^ 2 * a = c - b ^ 2 / a := by
      field_simp
      ring
    rw [hsimp] at h
    have h2 : b ^ 2 / a ≤ c := by linarith
    rw [div_le_iff₀ hapos] at h2
    linarith
  · have hb0 : b = 0 := by
      by_contra hbne
      have h := hq (-(c + 1) / (2 * b))
      have hsimp : c + 2 * (-(c + 1) / (2 * b)) * b + (-(c + 1) / (2 * b)) ^ 2 * a = c - (c + 1) := by
        rw [← haz]
        field_simp
        ring
      rw [hsimp] at h
      linarith
    rw [hb0, ← haz]
    simp

lemma cs_qfm0 {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hpsd : ∀ z, 0 ≤ qfm0 A z)
    (x y : Fin n → ℝ) : (blm0 A x y) ^ 2 ≤ qfm0 A x * qfm0 A y := by
  have hq : ∀ t : ℝ, 0 ≤ qfm0 A x + 2 * t * blm0 A x y + t ^ 2 * qfm0 A y := by
    intro t
    have h := hpsd (x + t • y)
    rwa [qfm0_add_smul A hA x y t] at h
  exact sq_le_mul_of_quad_nonneg (hpsd y) (hpsd x) hq

lemma inv_qfm0_lower {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (hdet : A.det ≠ 0)
    {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hlow : ∀ x : Fin n → ℝ, c * ∑ i, (x i) ^ 2 ≤ qfm0 A x)
    (hup : ∀ x : Fin n → ℝ, qfm0 A x ≤ B * ∑ i, (x i) ^ 2) :
    ∀ ξ : Fin n → ℝ, (∑ i, (ξ i) ^ 2) ≤ B * qfm0 A⁻¹ ξ := by
  intro ξ
  have hpsd : ∀ z : Fin n → ℝ, 0 ≤ qfm0 A z := by
    intro z
    have h := hlow z
    have h0 : (0:ℝ) ≤ c * ∑ i, (z i) ^ 2 :=
      mul_nonneg (le_of_lt hc) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  set η : Fin n → ℝ := A⁻¹ *ᵥ ξ with hη
  have hAη : A *ᵥ η = ξ := by
    rw [hη, Matrix.mulVec_mulVec]
    have hunit : IsUnit A.det := by rwa [isUnit_iff_ne_zero]
    rw [Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
  have hqinv : qfm0 A⁻¹ ξ = qfm0 A η := by
    unfold qfm0 blm0
    rw [hAη]
    exact dotProduct_comm _ _
  have hcs := cs_qfm0 hA hpsd (A *ᵥ η) η
  have hX : (A *ᵥ η) ⬝ᵥ (A *ᵥ η) = ∑ i, (ξ i) ^ 2 := by
    rw [hAη, sq_sum_eq_dotProduct]
  have hup' : qfm0 A (A *ᵥ η) ≤ B * ((A *ᵥ η) ⬝ᵥ (A *ᵥ η)) := by
    have h := hup (A *ᵥ η)
    rwa [sq_sum_eq_dotProduct] at h
  have hkey : ((∑ i, (ξ i) ^ 2)) ^ 2 ≤ B * (∑ i, (ξ i) ^ 2) * qfm0 A⁻¹ ξ := by
    calc ((∑ i, (ξ i) ^ 2)) ^ 2
        = ((A *ᵥ η) ⬝ᵥ (A *ᵥ η)) ^ 2 := by rw [← hX]
      _ ≤ qfm0 A (A *ᵥ η) * qfm0 A η := hcs
      _ ≤ (B * ((A *ᵥ η) ⬝ᵥ (A *ᵥ η))) * qfm0 A η :=
          mul_le_mul_of_nonneg_right hup' (hpsd η)
      _ = B * (∑ i, (ξ i) ^ 2) * qfm0 A⁻¹ ξ := by rw [hX, ← hqinv]
  rcases lt_or_eq_of_le (show (0:ℝ) ≤ ∑ i, (ξ i) ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg _) with hpos | hz
  · rw [pow_two] at hkey
    have h3 : (∑ i, (ξ i) ^ 2) * (∑ i, (ξ i) ^ 2) ≤ (B * qfm0 A⁻¹ ξ) * (∑ i, (ξ i) ^ 2) := by
      nlinarith [hkey]
    exact le_of_mul_le_mul_right h3 hpos
  · rw [← hz, hqinv]
    exact mul_nonneg (le_of_lt hB) (hpsd η)

/-! ## V. The bump function -/

noncomputable def bumpAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    (x : E) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump x :=
  ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩

@[simp] lemma bumpAt_rIn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    (x : E) (ρ : ℝ) (hρ : 0 < ρ) : (bumpAt x ρ hρ).rIn = ρ / 2 := rfl

@[simp] lemma bumpAt_rOut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
    (x : E) (ρ : ℝ) (hρ : 0 < ρ) : (bumpAt x ρ hρ).rOut = ρ := rfl

noncomputable def psi (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ)
    (G : Fin n → Fin n → ℝ) : ℝ :=
  1 - ∏ x ∈ t, (1 - (bumpAt x ρ hρ) G)

lemma contDiff_psi (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (psi t ρ hρ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun G : Fin n → Fin n → ℝ => ∏ x ∈ t, (1 - (bumpAt x ρ hρ) G)) :=
    contDiff_prod fun x _ => contDiff_const.sub (bumpAt x ρ hρ).contDiff
  unfold psi
  exact contDiff_const.sub h

lemma psi_eq_one (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ)
    {G : Fin n → Fin n → ℝ} (hG : G ∈ ⋃ x ∈ t, Metric.closedBall x (ρ / 2)) :
    psi t ρ hρ G = 1 := by
  obtain ⟨x, hxt, hxG⟩ := Set.mem_iUnion₂.mp hG
  have hone : (bumpAt x ρ hρ) G = 1 := (bumpAt x ρ hρ).one_of_mem_closedBall (by simpa using hxG)
  unfold psi
  rw [Finset.prod_eq_zero hxt (by rw [hone]; ring)]
  ring

lemma psi_eq_zero (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ)
    {G : Fin n → Fin n → ℝ} (hG : G ∉ ⋃ x ∈ t, Metric.closedBall x ρ) :
    psi t ρ hρ G = 0 := by
  unfold psi
  have hprod : (∏ x ∈ t, (1 - (bumpAt x ρ hρ) G)) = 1 := by
    refine Finset.prod_eq_one fun x hxt => ?_
    have hnot : G ∉ Metric.closedBall x ρ := fun h => hG (Set.mem_iUnion₂.mpr ⟨x, hxt, h⟩)
    have hdist : ρ ≤ dist G x := by
      rw [Metric.mem_closedBall, not_le] at hnot
      exact le_of_lt hnot
    have hzero : (bumpAt x ρ hρ) G = 0 := (bumpAt x ρ hρ).zero_of_le_dist (by simpa using hdist)
    rw [hzero]; ring
  rw [hprod]; ring

lemma prod_le_one_of_Icc {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h0a : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have h1a : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have h0s : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      have his : ∏ i ∈ s, f i ≤ 1 :=
        ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      calc f a * ∏ i ∈ s, f i ≤ 1 * 1 := mul_le_mul h1a his h0s (by norm_num)
        _ = 1 := by ring

lemma psi_mem_Icc (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ)
    (G : Fin n → Fin n → ℝ) : 0 ≤ psi t ρ hρ G ∧ psi t ρ hρ G ≤ 1 := by
  unfold psi
  have h1 : 0 ≤ ∏ x ∈ t, (1 - (bumpAt x ρ hρ) G) :=
    Finset.prod_nonneg fun x _ => by
      have hb := (bumpAt x ρ hρ).le_one (x := G)
      have hb2 := (bumpAt x ρ hρ).nonneg (x := G)
      linarith
  have h2 : (∏ x ∈ t, (1 - (bumpAt x ρ hρ) G)) ≤ 1 :=
    prod_le_one_of_Icc t (fun x _ => by
      have hb2 := (bumpAt x ρ hρ).nonneg (x := G)
      have hb := (bumpAt x ρ hρ).le_one (x := G)
      linarith)
      (fun x _ => by
      have hb2 := (bumpAt x ρ hρ).nonneg (x := G)
      linarith)
  constructor <;> linarith

lemma psi_ne_zero_mem (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ)
    {G : Fin n → Fin n → ℝ} (hG : psi t ρ hρ G ≠ 0) :
    G ∈ ⋃ x ∈ t, Metric.closedBall x ρ := by
  by_contra hnot
  exact hG (psi_eq_zero t ρ hρ hnot)

/-! ## VI. The determinant does not vanish on the sandwich set -/

lemma det_symG0_ne_zero_of_Sand {a b : ℝ} (ha : 0 < a)
    {G : Fin n → Fin n → ℝ} (hG : G ∈ Sand a b) : (symG0 G).det ≠ 0 := by
  have hinj : Function.Injective (symG0 G).mulVec := by
    intro x y hxy
    have hq : qfm0 (symG0 G) (x - y) = 0 := by
      have hz : (symG0 G) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
      unfold qfm0 blm0
      rw [hz, dotProduct_zero]
    have hlow := (hG (x - y)).1
    rw [qraw0_eq_qfm0] at hlow
    have hsum : (∑ i, ((x - y) i) ^ 2) = 0 := by
      have hnn : 0 ≤ ∑ i, ((x - y) i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith [hlow, hq, ha]
    have h1 : ∀ i : Fin n, (x - y) i = 0 := by
      intro i
      have h2 : ((x - y) i) ^ 2 ≤ ∑ j, ((x - y) j) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => ((x - y) j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h3 : ((x - y) i) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      exact sq_eq_zero_iff.mp h3
    exact sub_eq_zero.mp (funext h1)
  have hunit : IsUnit (symG0 G).det :=
    (Matrix.isUnit_iff_isUnit_det (symG0 G)).mp ((Matrix.mulVec_injective_iff_isUnit).mp hinj)
  rwa [isUnit_iff_ne_zero] at hunit

/-! ## VII. Smoothness of the determinant and the adjugate of the symmetric part -/

lemma contDiff_det_of_components {Y : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hY : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun G => Y G p q)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun G => (Y G).det) := by
  classical
  rw [show (fun G : Fin n → Fin n → ℝ => (Y G).det)
      = fun G => ∑ σ : Equiv.Perm (Fin n),
          (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, Y G (σ k) k from by
    funext G; rw [Matrix.det_apply']]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => hY (σ k) k)

lemma contDiff_symG0_entry (p q : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => symG0 G p q) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => G p q) :=
    contDiff_apply_apply ℝ ℝ p q
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => G q p) :=
    contDiff_apply_apply ℝ ℝ q p
  simpa [symG0] using (h1.add h2).div_const 2

lemma contDiff_det_symG0 : ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => (symG0 G).det) :=
  contDiff_det_of_components contDiff_symG0_entry

lemma contDiff_updateRow_symG0 (q : Fin n) (b : Fin n → ℝ) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun G : Fin n → Fin n → ℝ => (symG0 G).updateRow q b k l) := by
  have h2 : (fun G : Fin n → Fin n → ℝ => (symG0 G).updateRow q b k l)
      = fun G => if k = q then b l else symG0 G k l := by
    funext G; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hk : k = q
  · simp only [hk, ite_true]; exact contDiff_const
  · simp only [hk, ite_false]; exact contDiff_symG0_entry k l

lemma contDiff_adjugate_symG0 (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => (symG0 G).adjugate i j) := by
  classical
  have hrw : (fun G : Fin n → Fin n → ℝ => (symG0 G).adjugate i j)
      = fun G => ((symG0 G).updateRow j (Pi.single i 1)).det := by
    funext G; rw [Matrix.adjugate_apply]
  rw [hrw]
  exact contDiff_det_of_components (contDiff_updateRow_symG0 j (Pi.single i 1))


/-! ## VIII. Sum lemmas for the raw quadratic form -/

lemma qraw0_add_fun (A B : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    qraw0 (fun i j => A i j + B i j) ξ = qraw0 A ξ + qraw0 B ξ := by
  unfold qraw0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qraw0_smul_fun (c : ℝ) (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    qraw0 (fun i j => c * A i j) ξ = c * qraw0 A ξ := by
  unfold qraw0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qraw0_ite_delta (c : ℝ) (ξ : Fin n → ℝ) :
    qraw0 (fun i j => c * (if i = j then (1:ℝ) else 0)) ξ = c * ∑ i, (ξ i) ^ 2 := by
  unfold qraw0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · beta_reduce; rw [if_pos rfl]; ring
  · intro j _ hj
    beta_reduce
    rw [if_neg (Ne.symm hj)]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma qraw0_of_apply (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    qraw0 (fun i j => A i j) ξ = qfm0 A ξ := by
  rw [qfm0_eq_sum]; rfl

lemma qfm0_smul_matrix (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    qfm0 (c • A) ξ = c * qfm0 A ξ := by
  rw [qfm0_eq_sum, qfm0_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

lemma symG0_of_symm {G : Fin n → Fin n → ℝ} (hG : ∀ i j, G i j = G j i) :
    symG0 G = Matrix.of G := by
  ext i j
  simp only [symG0_apply, Matrix.of_apply]
  rw [hG]; ring

lemma adjugate_symm_of_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (i j : Fin n) :
    A.adjugate i j = A.adjugate j i := by
  have h := Matrix.adjugate_transpose A
  have h1 : (A.adjugate)ᵀ i j = (Aᵀ).adjugate i j := by rw [h]
  rw [Matrix.transpose_apply, hA] at h1
  exact h1.symm

/-! ## IX. The finite cover of the pinched set -/

lemma exists_finite_cover {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ t : Finset (Fin n → Fin n → ℝ), (∀ x ∈ t, x ∈ Pinch (n := n) a b) ∧
      Pinch (n := n) a b ⊆ ⋃ x ∈ t, Metric.ball x (rho (n := n) a / 2) := by
  classical
  obtain ⟨t, ht⟩ := (isCompact_Pinch (n := n) ha hb).elim_finite_subcover
    (fun x : {G : Fin n → Fin n → ℝ // G ∈ Pinch (n := n) a b} =>
      Metric.ball (x : Fin n → Fin n → ℝ) (rho (n := n) a / 2))
    (fun x => Metric.isOpen_ball)
    (fun G hG => Set.mem_iUnion.mpr ⟨⟨G, hG⟩, by
      rw [Metric.mem_ball]
      simpa using half_pos (rho_pos (n := n) ha)⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  · intro G hG
    obtain ⟨x, hxt, hxG⟩ := Set.mem_iUnion₂.mp (ht hG)
    exact Set.mem_iUnion₂.mpr ⟨x.1, Finset.mem_image_of_mem _ hxt, hxG⟩

/-! ## X. The determinant bound on the support of the bump -/

lemma exists_eps_det {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (t : Finset (Fin n → Fin n → ℝ)) (htP : ∀ x ∈ t, x ∈ Pinch (n := n) a b)
    (htcv : Pinch (n := n) a b ⊆ ⋃ x ∈ t, Metric.ball x (rho (n := n) a / 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ G : Fin n → Fin n → ℝ,
      psi t (rho (n := n) a) (rho_pos (n := n) ha) G ≠ 0 → ε ≤ |(symG0 G).det| := by
  classical
  have hρ : 0 < rho (n := n) a := rho_pos (n := n) ha
  have hsub1 : ∀ G : Fin n → Fin n → ℝ,
      psi t (rho (n := n) a) hρ G ≠ 0 → G ∈ ⋃ x ∈ t, Metric.closedBall x (rho (n := n) a) :=
    fun G hG => psi_ne_zero_mem t (rho (n := n) a) hρ hG
  have hsub2 : (⋃ x ∈ t, Metric.closedBall x (rho (n := n) a)) ⊆ Sand (n := n) a b := by
    intro G hG
    obtain ⟨x, hxt, hxG⟩ := Set.mem_iUnion₂.mp hG
    refine Sand_of_ball (n := n) ha hb (htP x hxt) ?_
    rw [Metric.mem_closedBall] at hxG
    rwa [dist_eq_norm] at hxG
  have hcont : Continuous (fun G : Fin n → Fin n → ℝ => |(symG0 G).det|) :=
    contDiff_det_symG0.continuous.abs
  have hcomp : IsCompact (⋃ x ∈ t, Metric.closedBall x (rho (n := n) a)) :=
    t.finite_toSet.isCompact_biUnion fun x _ => isCompact_closedBall x (rho (n := n) a)
  by_cases hne : ∃ G : Fin n → Fin n → ℝ, psi t (rho (n := n) a) hρ G ≠ 0
  · obtain ⟨G₀, hG₀⟩ := hne
    obtain ⟨G₁, hG₁, hmin⟩ := hcomp.exists_isMinOn ⟨G₀, hsub1 G₀ hG₀⟩ hcont.continuousOn
    exact ⟨|(symG0 G₁).det|, abs_pos.mpr (det_symG0_ne_zero_of_Sand ha (hsub2 hG₁)),
      fun G hG => hmin (hsub1 G hG)⟩
  · push_neg at hne
    exact ⟨1, one_pos, fun G hG => absurd (hne G) hG⟩

/-! ## XI. The smooth function `1/z` off a neighbourhood of `0` -/

noncomputable def gFun (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ :=
  fun z => z / (z ^ 2 + (ε / 2) ^ 2 * ((bumpAt (0 : ℝ) ε hε) z))

lemma contDiff_gFun (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (gFun ε hε) := by
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => z) := contDiff_id
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ => z ^ 2 + (ε / 2) ^ 2 * ((bumpAt (0:ℝ) ε hε) z)) :=
    (contDiff_id.pow 2).add (contDiff_const.mul (bumpAt (0:ℝ) ε hε).contDiff)
  unfold gFun
  refine ContDiff.div hnum hden ?_
  · intro z
    by_cases hz : z = 0
    · subst hz
      have h1 : (bumpAt (0:ℝ) ε hε) 0 = 1 :=
        (bumpAt (0:ℝ) ε hε).one_of_mem_closedBall (by
          rw [Metric.mem_closedBall]
          simpa using le_of_lt (half_pos hε))
      rw [h1]
      have h2 : (0:ℝ) ^ 2 + (ε / 2) ^ 2 * 1 = (ε / 2) ^ 2 := by ring
      rw [h2]
      positivity
    · have h2 : 0 < z ^ 2 := by positivity
      have h3 : 0 ≤ (ε / 2) ^ 2 * ((bumpAt (0:ℝ) ε hε) z) :=
        mul_nonneg (by positivity) (bumpAt (0:ℝ) ε hε).nonneg
      linarith

lemma gFun_of_le_abs (ε : ℝ) (hε : 0 < ε) {z : ℝ} (hz : ε ≤ |z|) : gFun ε hε z = 1 / z := by
  have hdist : (bumpAt (0:ℝ) ε hε).rOut ≤ dist z 0 := by
    rw [Real.dist_eq]
    simpa using hz
  have hzero : (bumpAt (0:ℝ) ε hε) z = 0 :=
    (bumpAt (0:ℝ) ε hε).zero_of_le_dist hdist
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  rw [gFun, hzero, mul_zero, add_zero, div_eq_div_iff (pow_ne_zero 2 hz0) hz0]
  ring

/-! ## XII. The clamped inverse and its properties -/

noncomputable def Kinv (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ)
    (μ : ℝ) (G : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => (psi t ρ hρ G * g ((symG0 G).det)) * ((symG0 G).adjugate i j)
    + (1 - psi t ρ hρ G) * (μ * if i = j then (1 : ℝ) else 0)

lemma contDiff_Kinv_entry (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (μ : ℝ) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => Kinv t ρ hρ g μ G i j) := by
  unfold Kinv
  have hpsi : ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => psi t ρ hρ G) :=
    contDiff_psi t ρ hρ
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => g ((symG0 G).det)) :=
    hg.comp contDiff_det_symG0
  exact ((hpsi.mul hcomp).mul (contDiff_adjugate_symG0 i j)).add
    ((contDiff_const.sub hpsi).mul contDiff_const)

lemma Kinv_symm (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ) (μ : ℝ)
    {G : Fin n → Fin n → ℝ} (hG : ∀ i j, G i j = G j i) (i j : Fin n) :
    Kinv t ρ hρ g μ G i j = Kinv t ρ hρ g μ G j i := by
  unfold Kinv
  have h1 : (symG0 G).adjugate i j = (symG0 G).adjugate j i :=
    adjugate_symm_of_transpose (symG0_transpose G) i j
  have h2 : ((if i = j then (1:ℝ) else 0 : ℝ)) = (if j = i then (1:ℝ) else 0) := by
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [h1, h2]

lemma Kinv_exact (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ) (μ : ℝ)
    {G : Fin n → Fin n → ℝ} (hψ : psi t ρ hρ G = 1)
    (hgd : g ((symG0 G).det) = ((symG0 G).det)⁻¹)
    (hsym : symG0 G = Matrix.of G) :
    Kinv t ρ hρ g μ G = fun i j => (Matrix.of G)⁻¹ i j := by
  funext i j
  unfold Kinv
  rw [hψ, hgd, hsym]
  simp only [sub_self, zero_mul, one_mul, add_zero]
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  have h3 : Ring.inverse ((Matrix.of G).det) = ((Matrix.of G).det)⁻¹ :=
    congrFun (Ring.inverse_eq_inv' (G₀ := ℝ)) _
  rw [h3]

lemma Kinv_lower (t : Finset (Fin n → Fin n → ℝ)) (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ)
    (a b μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hμ : μ = 1 / (2 * b + a))
    (hSand : ∀ G : Fin n → Fin n → ℝ, psi t ρ hρ G ≠ 0 → G ∈ Sand (n := n) a b)
    (hgd : ∀ G : Fin n → Fin n → ℝ,
      psi t ρ hρ G ≠ 0 → g ((symG0 G).det) = ((symG0 G).det)⁻¹)
    (G : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    μ * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Kinv t ρ hρ g μ G i j * ξ i * ξ j := by
  have hK : Kinv t ρ hρ g μ G
      = fun i j => (psi t ρ hρ G * g ((symG0 G).det)) * ((symG0 G).adjugate i j)
        + (1 - psi t ρ hρ G) * (μ * (if i = j then (1:ℝ) else 0)) := rfl
  show μ * ∑ i, (ξ i) ^ 2 ≤ qraw0 (Kinv t ρ hρ g μ G) ξ
  have hsplit : qraw0 (Kinv t ρ hρ g μ G) ξ
      = qraw0 (fun i j => (psi t ρ hρ G * g ((symG0 G).det)) * ((symG0 G).adjugate i j)) ξ
        + qraw0 (fun i j => (1 - psi t ρ hρ G) * (μ * (if i = j then (1:ℝ) else 0))) ξ := by
    rw [hK]
    exact qraw0_add_fun _ _ _
  have hA : qraw0 (fun i j => (psi t ρ hρ G * g ((symG0 G).det)) * ((symG0 G).adjugate i j)) ξ
      = (psi t ρ hρ G * g ((symG0 G).det)) * qfm0 (symG0 G).adjugate ξ := by
    rw [show qraw0 (fun i j => (psi t ρ hρ G * g ((symG0 G).det)) * ((symG0 G).adjugate i j)) ξ
        = (psi t ρ hρ G * g ((symG0 G).det))
          * qraw0 (fun i j => (symG0 G).adjugate i j) ξ from
      qraw0_smul_fun (psi t ρ hρ G * g ((symG0 G).det)) (fun i j => (symG0 G).adjugate i j) ξ]
    rw [show qraw0 (fun i j => (symG0 G).adjugate i j) ξ
        = qfm0 (symG0 G).adjugate ξ from qraw0_of_apply _ _]
  have hB : qraw0 (fun i j => (1 - psi t ρ hρ G) * (μ * (if i = j then (1:ℝ) else 0))) ξ
      = (1 - psi t ρ hρ G) * (μ * ∑ i, (ξ i) ^ 2) := by
    rw [show qraw0 (fun i j => (1 - psi t ρ hρ G) * (μ * (if i = j then (1:ℝ) else 0))) ξ
        = (1 - psi t ρ hρ G) * qraw0 (fun i j => μ * (if i = j then (1:ℝ) else 0)) ξ from
      qraw0_smul_fun (1 - psi t ρ hρ G) (fun i j => μ * (if i = j then (1:ℝ) else 0)) ξ]
    rw [show qraw0 (fun i j => μ * (if i = j then (1:ℝ) else 0)) ξ = μ * ∑ i, (ξ i) ^ 2 from
      qraw0_ite_delta μ ξ]
  rw [hsplit, hA, hB]
  have hcardnn : (0:ℝ) ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hpsi : psi t ρ hρ G = 0
  · have h1 : (psi t ρ hρ G * g ((symG0 G).det)) * qfm0 (symG0 G).adjugate ξ = 0 := by
      rw [hpsi, zero_mul, zero_mul]
    have h2 : (1 - psi t ρ hρ G) * (μ * ∑ i, (ξ i) ^ 2) = μ * ∑ i, (ξ i) ^ 2 := by
      rw [hpsi]; ring
    rw [h1, h2, zero_add]
  · have hS := hSand G hpsi
    have hdet := det_symG0_ne_zero_of_Sand ha hS
    have hgd' := hgd G hpsi
    have hlowS : ∀ x : Fin n → ℝ, (a/2) * ∑ i, (x i) ^ 2 ≤ qfm0 (symG0 G) x := fun x => by
      have h := (hS x).1
      rwa [qraw0_eq_qfm0] at h
    have hupS : ∀ x : Fin n → ℝ, qfm0 (symG0 G) x ≤ (2*b + a) * ∑ i, (x i) ^ 2 := fun x => by
      have h := (hS x).2
      rwa [qraw0_eq_qfm0] at h
    have hBpos : 0 < 2 * b + a := by linarith
    have hinv : (∑ i, (ξ i) ^ 2) ≤ (2*b + a) * qfm0 (symG0 G)⁻¹ ξ :=
      inv_qfm0_lower (symG0_transpose G) hdet (by linarith) hBpos hlowS hupS ξ
    have hμS : μ * (∑ i, (ξ i) ^ 2) ≤ qfm0 (symG0 G)⁻¹ ξ := by
      have h1 : (1 / (2 * b + a)) * (∑ i, (ξ i) ^ 2) = (∑ i, (ξ i) ^ 2) / (2 * b + a) := by
        ring
      rw [hμ, h1, div_le_iff₀ hBpos]
      linarith
    have hqinv : qfm0 (symG0 G)⁻¹ ξ = ((symG0 G).det)⁻¹ * qfm0 (symG0 G).adjugate ξ := by
      have hSinv : (symG0 G)⁻¹ = ((symG0 G).det)⁻¹ • (symG0 G).adjugate := by
        rw [Matrix.inv_def, congrFun (Ring.inverse_eq_inv' (G₀ := ℝ)) (symG0 G).det]
      rw [hSinv, qfm0_smul_matrix]
    rw [hgd', mul_assoc, ← hqinv]
    have hψIcc := (psi_mem_Icc t ρ hρ G).1
    have hψIcc2 := (psi_mem_Icc t ρ hρ G).2
    have h2 : psi t ρ hρ G * (μ * (∑ i, (ξ i) ^ 2)) ≤ psi t ρ hρ G * qfm0 (symG0 G)⁻¹ ξ :=
      mul_le_mul_of_nonneg_left hμS hψIcc
    nlinarith [h2, hcardnn, hψIcc, hψIcc2]

/-! ## XIII. The main theorem -/

theorem clampedInv_exists (n k : ℕ) (a b B : ℝ) (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ (K : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)) (lam' CK : ℝ),
      0 < lam' ∧ 0 ≤ CK ∧
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => K G i j)) ∧
      (∀ (G : Fin n → Fin n → ℝ),
        (∀ i j, G i j = G j i) →
        (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
        (∀ ξ : Fin n → ℝ, ∑ i, ∑ j, G i j * ξ i * ξ j ≤ b * ∑ i, (ξ i) ^ 2) →
        K G = fun i j => (Matrix.of G)⁻¹ i j) ∧
      (∀ (G : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, K G i j * ξ i * ξ j) ∧
      (∀ (G : Fin n → Fin n → ℝ),
        (∀ i j, G i j = G j i) →
        (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
        (∀ i j, K G i j = K G j i)) ∧
      (∀ (G : Fin n → Fin n → ℝ), (∀ i j, |G i j| ≤ B) →
        ∀ (j : ℕ), j ≤ k → ∀ (p q : Fin n),
          ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K G' p q) G‖ ≤ CK) := by
  classical
  obtain ⟨t, htP, htcv⟩ := exists_finite_cover (n := n) ha hb
  obtain ⟨ε, hεpos, hεdet⟩ := exists_eps_det (n := n) ha hb t htP htcv
  have hρ : 0 < rho (n := n) a := rho_pos (n := n) ha
  set μ : ℝ := 1 / (2 * b + a) with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  set g : ℝ → ℝ := gFun ε hεpos with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by rw [hgdef]; exact contDiff_gFun ε hεpos
  set K : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) := Kinv t (rho (n := n) a) hρ g μ
    with hKdef
  have hsm : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => K G i j) := by
    intro i j
    rw [hKdef]
    exact contDiff_Kinv_entry t (rho (n := n) a) hρ g hg μ i j
  have hexact : ∀ (G : Fin n → Fin n → ℝ),
      (∀ i j, G i j = G j i) →
      (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
      (∀ ξ : Fin n → ℝ, ∑ i, ∑ j, G i j * ξ i * ξ j ≤ b * ∑ i, (ξ i) ^ 2) →
      K G = fun i j => (Matrix.of G)⁻¹ i j := by
    intro G hsym hlow hup
    have hGP : G ∈ Pinch (n := n) a b := ⟨hsym, hlow, hup⟩
    have hmem : G ∈ ⋃ x ∈ t, Metric.closedBall x (rho (n := n) a / 2) := by
      obtain ⟨x, hxt, hxG⟩ := Set.mem_iUnion₂.mp (htcv hGP)
      exact Set.mem_iUnion₂.mpr ⟨x, hxt, Metric.ball_subset_closedBall hxG⟩
    have hpsi : psi t (rho (n := n) a) hρ G = 1 := psi_eq_one t (rho (n := n) a) hρ hmem
    have hgd : g ((symG0 G).det) = ((symG0 G).det)⁻¹ := by
      rw [hgdef]
      simpa [one_div] using gFun_of_le_abs ε hεpos (hεdet G (by rw [hpsi]; exact one_ne_zero))
    rw [hKdef]
    exact Kinv_exact t (rho (n := n) a) hρ g μ hpsi hgd (symG0_of_symm hsym)
  have hlowq : ∀ (G : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ),
      μ * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, K G i j * ξ i * ξ j := by
    intro G ξ
    rw [hKdef]
    refine Kinv_lower t (rho (n := n) a) hρ g a b μ ha hb ?_ ?_ ?_ G ξ
    · rw [hμdef]
    · intro G' hG'
      obtain ⟨x, hxt, hxG⟩ :=
        Set.mem_iUnion₂.mp (psi_ne_zero_mem t (rho (n := n) a) hρ hG')
      refine Sand_of_ball (n := n) ha hb (htP x hxt) ?_
      rw [Metric.mem_closedBall] at hxG
      rwa [dist_eq_norm] at hxG
    · intro G' hG'
      rw [hgdef]
      simpa [one_div] using gFun_of_le_abs ε hεpos (hεdet G' hG')
  have hsymK : ∀ (G : Fin n → Fin n → ℝ), (∀ i j, G i j = G j i) →
      (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
      ∀ i j, K G i j = K G j i := by
    intro G hG _ i j
    rw [hKdef]
    exact Kinv_symm t (rho (n := n) a) hρ g μ hG i j
  have hboxne : (Box (n := n) B).Nonempty :=
    ⟨fun _ _ => 0, fun i j => by simpa using hB⟩
  have hjet : ∀ (j : ℕ) (p q : Fin n), ∃ M : ℝ, 0 ≤ M ∧ ∀ G ∈ Box (n := n) B,
      ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K G' p q) G‖ ≤ M := by
    intro j p q
    have hcont : Continuous (fun G : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K G' p q) G‖) :=
      ((hsm p q).continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
    obtain ⟨G₀, -, hmax⟩ :=
      (isCompact_box (n := n) B).exists_isMaxOn hboxne hcont.continuousOn
    exact ⟨_, norm_nonneg _, fun G hG => hmax hG⟩
  choose M hM using hjet
  refine ⟨K, μ, max 0 (∑ j ∈ Finset.range (k+1), ∑ p : Fin n, ∑ q : Fin n, M j p q),
    hμpos, le_max_left _ _, hsm, hexact, hlowq, hsymK, ?_⟩
  intro G hG j hj p q
  have hj' : j ∈ Finset.range (k+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsum_nn : ∀ j' ∈ Finset.range (k+1), 0 ≤ ∑ p : Fin n, ∑ q : Fin n, M j' p q :=
    fun j' _ => Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hM j' p q).1
  have h1 : M j p q ≤ max 0 (∑ j' ∈ Finset.range (k+1), ∑ p : Fin n, ∑ q : Fin n, M j' p q) := by
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (Finset.single_le_sum hsum_nn hj')
    refine le_trans ?_ (Finset.single_le_sum
      (fun p' (_ : p' ∈ Finset.univ) => Finset.sum_nonneg fun q' _ => (hM j p' q').1)
      (Finset.mem_univ p))
    exact Finset.single_le_sum (fun q' (_ : q' ∈ Finset.univ) => (hM j p q').1) (Finset.mem_univ q)
  exact le_trans ((hM j p q).2 G hG) h1

end Work.Diff.STE.B3
