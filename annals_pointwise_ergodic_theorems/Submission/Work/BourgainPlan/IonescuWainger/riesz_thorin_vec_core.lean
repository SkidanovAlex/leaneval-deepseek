import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vec_interp

/-!
# The core (Hadamard three-lines) estimate for vector-valued Riesz--Thorin

This file proves the bilinear core of the vector-valued Riesz--Thorin theorem: for a `ℂ`-linear
`T : (α → ℂ) → (β → ι → ℂ)` that is bounded from `ℓ²(α)` to `L²(β;ℓ²(ι))` with constant `A` and
from `ℓ^∞(α)` to `L^∞(β;ℓ²(ι))` with constant `B`, and for `2 < p`, the pairing of `T f` with
`g` is bounded by `A^{2/p} B^{1-2/p}` whenever `f` has `ℓ^p`-norm `≤ 1` and `g` has mixed
conjugate `ℓ^{p/(p-1)}`-norm `≤ 1`.

The proof interpolates with the affines `t(z) = p/2 - (p/2) z` (source exponent) and
`s(z) = Q/2 + (Q/2) z` with `Q = p/(p-1)` (target exponent) and applies Hadamard's three-lines
theorem to `F z = ∑ b ∑ i, (T (interpC f t z)) b i * (vinterp g s z) b i`.  Note that the target
interpolation uses the exponent `Q = (p/(p-1))`, the *conjugate* of `p`, so that the two boundary
conditions are `‖g_z‖_{L²(β;ℓ²)} ≤ 1` (at `Re z = 0`) and `‖g_z‖_{L¹(β;ℓ²)} ≤ 1` (at `Re z = 1`,
the dual of the `L^∞` endpoint of the operator hypothesis).
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-! ## Elementary pairing bounds -/

lemma holder_two_two {σ : Type*} [Fintype σ] (x y : σ → ℂ) :
    ‖∑ i, x i * y i‖ ≤ (∑ i, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2) * (∑ i, ‖y i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have h := Commons.Analysis.Integral.holder_complex_finset Finset.univ x y (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
  simpa using h

lemma norm_sum_mul_le_n2 {σ : Type*} [Fintype σ] (x y : σ → ℂ) :
    ‖∑ i, x i * y i‖ ≤ n2 x * n2 y := by
  rw [n2_eq_rpow, n2_eq_rpow]
  exact holder_two_two x y

lemma rpow_two_eq_sq (a : ℝ) : a ^ (2 : ℝ) = a ^ 2 := Real.rpow_two a

lemma sum_sq_n2_eq (x : β → ι → ℂ) :
    ∑ b, (n2 (x b)) ^ (2 : ℝ) = ∑ b, ∑ i, ‖x b i‖ ^ 2 := by
  rw [Finset.sum_congr rfl fun b _ => rpow_two_eq_sq (n2 (x b))]
  exact Finset.sum_congr rfl fun b _ => sq_n2 (x b)

lemma sum_sq_n2_eq' (x : β → ι → ℂ) :
    (∑ b, (n2 (x b)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = (∑ b, ∑ i, ‖x b i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [sum_sq_n2_eq]

lemma norm_pairing_le_L2 (x y : β → ι → ℂ) :
    ‖∑ b, ∑ i, x b i * y b i‖
      ≤ (∑ b, ∑ i, ‖x b i‖ ^ 2) ^ ((1 : ℝ) / 2)
        * (∑ b, ∑ i, ‖y b i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have h1 : ‖∑ b, ∑ i, x b i * y b i‖ ≤ ∑ b, n2 (x b) * n2 (y b) := by
    calc ‖∑ b, ∑ i, x b i * y b i‖ ≤ ∑ b, ‖∑ i, x b i * y b i‖ := norm_sum_le _ _
      _ ≤ ∑ b, n2 (x b) * n2 (y b) :=
          Finset.sum_le_sum fun b _ => norm_sum_mul_le_n2 (x b) (y b)
  have h2 : ∑ b, n2 (x b) * n2 (y b)
      ≤ (∑ b, (n2 (x b)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∑ b, (n2 (y b)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (fun b _ => n2_nonneg (x b)) (fun b _ => n2_nonneg (y b))
  calc ‖∑ b, ∑ i, x b i * y b i‖
      ≤ (∑ b, (n2 (x b)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∑ b, (n2 (y b)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := le_trans h1 h2
    _ = (∑ b, ∑ i, ‖x b i‖ ^ 2) ^ ((1 : ℝ) / 2)
        * (∑ b, ∑ i, ‖y b i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [sum_sq_n2_eq x, sum_sq_n2_eq y]

lemma norm_pairing_le_sup_l1 (x y : β → ι → ℂ) :
    ‖∑ b, ∑ i, x b i * y b i‖ ≤ (⨆ b, n2 (x b)) * (∑ b, n2 (y b)) := by
  have h1 : ‖∑ b, ∑ i, x b i * y b i‖ ≤ ∑ b, n2 (x b) * n2 (y b) := by
    calc ‖∑ b, ∑ i, x b i * y b i‖ ≤ ∑ b, ‖∑ i, x b i * y b i‖ := norm_sum_le _ _
      _ ≤ ∑ b, n2 (x b) * n2 (y b) :=
          Finset.sum_le_sum fun b _ => norm_sum_mul_le_n2 (x b) (y b)
  refine le_trans h1 ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right
    (le_ciSup (Set.finite_range (fun b => n2 (x b))).bddAbove b) (n2_nonneg (y b))

/-! ## Differentiability of the three-lines functional -/

lemma linearMap_apply_eq_sum [DecidableEq α] (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (v : α → ℂ)
    (b : β) (i : ι) :
    T v b i = ∑ a, v a * (T (Pi.single a 1)) b i := by
  classical
  have hv : v = ∑ a, Pi.single a (v a) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : Pi.single a (v a) = (v a) • Pi.single a (1 : ℂ) := by
    ext c
    rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hc : c = a <;> simp [hc]
  rw [hs, map_smul]
  simp [Pi.smul_apply, smul_eq_mul]

lemma differentiable_T_interpC (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (f : α → ℂ) {t : ℂ → ℂ}
    (ht : Differentiable ℂ t) (b : β) (i : ι) :
    Differentiable ℂ (fun z => T (interpC f t z) b i) := by
  classical
  have h : (fun z => T (interpC f t z) b i)
      = fun z => ∑ a, interpC f t z a * (T (Pi.single a 1)) b i := by
    funext z
    exact linearMap_apply_eq_sum T (interpC f t z) b i
  rw [h]
  exact Differentiable.fun_sum fun a _ => (differentiable_interpC f ht a).mul_const _

lemma ciSup_le_of_nonneg {σ : Type*} (f : σ → ℝ) {a : ℝ} (h : ∀ i, f i ≤ a) (ha : 0 ≤ a) :
    (⨆ i, f i) ≤ a := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · haveI : IsEmpty σ := hσ
    simpa using ha
  · haveI : Nonempty σ := hσ
    exact ciSup_le h

lemma sum_sq_norm_interpC {σ : Type*} [Fintype σ] (f : σ → ℂ) {t : ℂ → ℂ} {z : ℂ} {ρ : ℝ}
    (hz : 0 < (t z).re) (hρ : (t z).re = ρ) :
    ∑ a, ‖interpC f t z a‖ ^ 2 = ∑ a, ‖f a‖ ^ (2 * ρ) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_interpC f hz a, ← rpow_two_eq_sq, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  rw [hρ]; ring

/-- The three-lines generating function. -/
def threeLinesF (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (f : α → ℂ) (g : β → ι → ℂ) (t s : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  ∑ b, ∑ i, (T (interpC f t z)) b i * (vinterp g s z) b i

lemma differentiable_threeLinesF (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (f : α → ℂ) (g : β → ι → ℂ)
    {t s : ℂ → ℂ} (ht : Differentiable ℂ t) (hs : Differentiable ℂ s) :
    Differentiable ℂ (threeLinesF T f g t s) := by
  unfold threeLinesF
  exact Differentiable.fun_sum fun b _ => Differentiable.fun_sum fun i _ =>
    (differentiable_T_interpC T f ht b i).mul (differentiable_vinterp g hs b i)

lemma threeLinesF_apply (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (f : α → ℂ) (g : β → ι → ℂ)
    (t s : ℂ → ℂ) (z : ℂ) :
    threeLinesF T f g t s z
      = ∑ b, ∑ i, (T (interpC f t z)) b i * (vinterp g s z) b i := rfl

lemma threeLinesF_self (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (f : α → ℂ) (g : β → ι → ℂ)
    {t s : ℂ → ℂ} {θ : ℂ} (ht : t θ = 1) (hs : s θ = 1) :
    threeLinesF T f g t s θ = ∑ b, ∑ i, (T f) b i * g b i := by
  unfold threeLinesF
  rw [interpC_self f ht, vinterp_self g hs]

/-- **The core bilinear estimate.**  If `T` is bounded `ℓ²(α) → L²(β;ℓ²(ι))` with constant `A` and
`ℓ^∞(α) → L^∞(β;ℓ²(ι))` with constant `B`, then for `2 < p` and `f`, `g` of (mixed) norms
`≤ 1` in `ℓ^p(α)` and `ℓ^{p/(p-1)}(β;ℓ²(ι))` the pairing `⟨T f, g⟩` is bounded by
`A^{2/p} B^{1-2/p}`. -/
theorem riesz_thorin_vec_core (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) {p A B : ℝ}
    (hp : 2 < p) (hA : 0 < A) (hB : 0 < B)
    (hT0 : ∀ f : α → ℂ, (∑ b, ∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ A * (∑ a, ‖f a‖ ^ 2) ^ ((1 : ℝ) / 2))
    (hT1 : ∀ f : α → ℂ, (⨆ b, n2 (T f b)) ≤ B * (⨆ a, ‖f a‖))
    (f : α → ℂ) (g : β → ι → ℂ) (hf : (∑ a, ‖f a‖ ^ p) ≤ 1)
    (hg : (∑ b, (n2 (g b)) ^ (p / (p - 1))) ≤ 1) :
    ‖∑ b, ∑ i, (T f) b i * g b i‖ ≤ A ^ (2 / p) * B ^ (1 - 2 / p) := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : p ≠ 1 := by linarith
  have hpm1 : p - 1 ≠ 0 := by linarith
  set Q : ℝ := p / (p - 1) with hQdef
  set θ : ℝ := 1 - 2 / p with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef, sub_pos, div_lt_one hp0]; linarith
  have hθlt1 : θ < 1 := by
    rw [hθdef]; linarith [div_pos (by norm_num : (0:ℝ) < 2) hp0]
  have hQpos : 0 < Q := by rw [hQdef]; exact div_pos hp0 (by linarith)
  have hQ1 : 1 < Q := by
    rw [hQdef, one_lt_div (by linarith : (0:ℝ) < p - 1)]; linarith
  have hθp : p / 2 + (-(p / 2)) * θ = 1 := by rw [hθdef]; field_simp; ring
  have hθQ : Q / 2 + (Q / 2) * θ = 1 := by rw [hQdef, hθdef]; field_simp; ring
  have htθ : affine (p / 2) (-(p / 2)) (θ : ℂ) = 1 := by
    have h : affine (p / 2) (-(p / 2)) (θ : ℂ) = ((p / 2 + (-(p / 2)) * θ : ℝ) : ℂ) := by
      simp only [affine]; rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [h, hθp, Complex.ofReal_one]
  have hsθ : affine (Q / 2) (Q / 2) (θ : ℂ) = 1 := by
    have h : affine (Q / 2) (Q / 2) (θ : ℂ) = ((Q / 2 + (Q / 2) * θ : ℝ) : ℂ) := by
      simp only [affine]; rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [h, hθQ, Complex.ofReal_one]
  have htre : ∀ z : ℂ, (affine (p / 2) (-(p / 2)) z).re = p / 2 * (1 - z.re) := by
    intro z; rw [affine_re]; ring
  have hsre : ∀ z : ℂ, (affine (Q / 2) (Q / 2) z).re = Q / 2 * (1 + z.re) := by
    intro z; rw [affine_re]; ring
  set F : ℂ → ℂ := threeLinesF T f g (affine (p / 2) (-(p / 2))) (affine (Q / 2) (Q / 2)) with hFdef
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]; exact differentiable_threeLinesF T f g (differentiable_affine _ _)
      (differentiable_affine _ _)
  -- boundary at `Re z = 0`
  have hbound0 : ∀ y : ℝ, ‖F ((y : ℂ) * Complex.I)‖ ≤ A := by
    intro y
    set z : ℂ := (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 0 := by rw [hzdef]; simp
    have ht : (affine (p / 2) (-(p / 2)) z).re = p / 2 := by rw [htre z, hzre]; ring
    have hs : (affine (Q / 2) (Q / 2) z).re = Q / 2 := by rw [hsre z, hzre]; ring
    have htpos : 0 < (affine (p / 2) (-(p / 2)) z).re := by rw [ht]; linarith
    have hspos : 0 < (affine (Q / 2) (Q / 2) z).re := by rw [hs]; linarith
    have hfz : (∑ a, ‖interpC f (affine (p / 2) (-(p / 2))) z a‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 := by
      have hsum : (∑ a, ‖interpC f (affine (p / 2) (-(p / 2))) z a‖ ^ 2)
          = ∑ a, ‖f a‖ ^ p := by
        rw [sum_sq_norm_interpC f htpos ht]
        exact Finset.sum_congr rfl fun a _ => by congr 1; ring
      rw [hsum]
      exact Real.rpow_le_one (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) p)
        hf (by norm_num)
    have hfirst : (∑ b, ∑ i, ‖T (interpC f (affine (p / 2) (-(p / 2))) z) b i‖ ^ 2)
        ^ ((1 : ℝ) / 2) ≤ A := by
      refine le_trans (hT0 (interpC f (affine (p / 2) (-(p / 2))) z)) ?_
      calc A * (∑ a, ‖interpC f (affine (p / 2) (-(p / 2))) z a‖ ^ 2) ^ ((1 : ℝ) / 2)
          ≤ A * 1 := mul_le_mul_of_nonneg_left hfz hA.le
        _ = A := mul_one A
    have hsecond : (∑ b, ∑ i, ‖vinterp g (affine (Q / 2) (Q / 2)) z b i‖ ^ 2)
        ^ ((1 : ℝ) / 2) ≤ 1 := by
      rw [← sum_sq_n2_eq (vinterp g (affine (Q / 2) (Q / 2)) z)]
      have hsum : (∑ b, (n2 (vinterp g (affine (Q / 2) (Q / 2)) z b)) ^ (2 : ℝ))
          = ∑ b, (n2 (g b)) ^ Q := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [n2_vinterp g hspos b, ← Real.rpow_mul (n2_nonneg (g b))]
        congr 1
        rw [hs]; ring
      rw [hsum]
      exact Real.rpow_le_one (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (n2_nonneg _) Q)
        hg (by norm_num)
    calc ‖F z‖ = ‖∑ b, ∑ i, T (interpC f (affine (p / 2) (-(p / 2))) z) b i
            * vinterp g (affine (Q / 2) (Q / 2)) z b i‖ := rfl
      _ ≤ (∑ b, ∑ i, ‖T (interpC f (affine (p / 2) (-(p / 2))) z) b i‖ ^ 2) ^ ((1 : ℝ) / 2)
            * (∑ b, ∑ i, ‖vinterp g (affine (Q / 2) (Q / 2)) z b i‖ ^ 2) ^ ((1 : ℝ) / 2) :=
          norm_pairing_le_L2 _ _
      _ ≤ A * 1 := mul_le_mul hfirst hsecond
          (Real.rpow_nonneg (Finset.sum_nonneg fun b _ =>
            Finset.sum_nonneg fun i _ => sq_nonneg _) _) hA.le
      _ = A := mul_one A
  -- boundary at `Re z = 1`
  have hbound1 : ∀ y : ℝ, ‖F (1 + (y : ℂ) * Complex.I)‖ ≤ B := by
    intro y
    set z : ℂ := 1 + (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 1 := by rw [hzdef]; simp
    have ht : (affine (p / 2) (-(p / 2)) z).re = 0 := by rw [htre z, hzre]; ring
    have hs : (affine (Q / 2) (Q / 2) z).re = Q := by rw [hsre z, hzre]; ring
    have hspos : 0 < (affine (Q / 2) (Q / 2) z).re := by rw [hs]; linarith
    have hsupf : (⨆ a, ‖interpC f (affine (p / 2) (-(p / 2))) z a‖) ≤ 1 :=
      ciSup_le_of_nonneg _ (fun a => norm_interpC_le_one f ht a) (by norm_num)
    have hfirst : (⨆ b, n2 (T (interpC f (affine (p / 2) (-(p / 2))) z) b)) ≤ B := by
      refine le_trans (hT1 (interpC f (affine (p / 2) (-(p / 2))) z)) ?_
      calc B * (⨆ a, ‖interpC f (affine (p / 2) (-(p / 2))) z a‖) ≤ B * 1 :=
            mul_le_mul_of_nonneg_left hsupf hB.le
        _ = B := mul_one B
    have hsecond : (∑ b, n2 (vinterp g (affine (Q / 2) (Q / 2)) z b)) ≤ 1 := by
      have hsum : (∑ b, n2 (vinterp g (affine (Q / 2) (Q / 2)) z b)) = ∑ b, (n2 (g b)) ^ Q := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [n2_vinterp g hspos b, hs]
      rw [hsum]; exact hg
    calc ‖F z‖ = ‖∑ b, ∑ i, T (interpC f (affine (p / 2) (-(p / 2))) z) b i
            * vinterp g (affine (Q / 2) (Q / 2)) z b i‖ := rfl
      _ ≤ (⨆ b, n2 (T (interpC f (affine (p / 2) (-(p / 2))) z) b))
            * (∑ b, n2 (vinterp g (affine (Q / 2) (Q / 2)) z b)) := norm_pairing_le_sup_l1 _ _
      _ ≤ B * 1 := mul_le_mul hfirst hsecond (Finset.sum_nonneg fun b _ => n2_nonneg _) hB.le
      _ = B := mul_one B
  -- interior bound
  have hboundInt : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖F z‖ ≤ A * (∑ a, (max 1 (‖f a‖ ^ (p / 2))) ^ 2) ^ ((1 : ℝ) / 2)
        * (∑ b, (max 1 ((n2 (g b)) ^ Q)) ^ 2) ^ ((1 : ℝ) / 2) := by
    intro z hz0 hz1
    have ht0 : 0 ≤ (affine (p / 2) (-(p / 2)) z).re := by rw [htre z]; nlinarith
    have ht1 : (affine (p / 2) (-(p / 2)) z).re ≤ p / 2 := by rw [htre z]; nlinarith
    have hs0 : 0 ≤ (affine (Q / 2) (Q / 2) z).re := by rw [hsre z]; nlinarith
    have hs1 : (affine (Q / 2) (Q / 2) z).re ≤ Q := by rw [hsre z]; nlinarith
    have hfirst : (∑ b, ∑ i, ‖T (interpC f (affine (p / 2) (-(p / 2))) z) b i‖ ^ 2)
        ^ ((1 : ℝ) / 2)
        ≤ A * (∑ a, (max 1 (‖f a‖ ^ (p / 2))) ^ 2) ^ ((1 : ℝ) / 2) := by
      refine le_trans (hT0 (interpC f (affine (p / 2) (-(p / 2))) z))
        (mul_le_mul_of_nonneg_left ?_ hA.le)
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun a _ => sq_nonneg _)
        (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_interpC_le_max f (by positivity) ht0 ht1 a) 2
    have hsecond : (∑ b, ∑ i, ‖vinterp g (affine (Q / 2) (Q / 2)) z b i‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ (∑ b, (max 1 ((n2 (g b)) ^ Q)) ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← sum_sq_n2_eq (vinterp g (affine (Q / 2) (Q / 2)) z)]
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (n2_nonneg _) 2)
        (Finset.sum_le_sum fun b _ => ?_) (by norm_num)
      rw [rpow_two_eq_sq]
      exact pow_le_pow_left₀ (n2_nonneg _) (n2_vinterp_le_max g hQpos.le hs0 hs1 b) 2
    calc ‖F z‖ = ‖∑ b, ∑ i, T (interpC f (affine (p / 2) (-(p / 2))) z) b i
            * vinterp g (affine (Q / 2) (Q / 2)) z b i‖ := rfl
      _ ≤ (∑ b, ∑ i, ‖T (interpC f (affine (p / 2) (-(p / 2))) z) b i‖ ^ 2) ^ ((1 : ℝ) / 2)
            * (∑ b, ∑ i, ‖vinterp g (affine (Q / 2) (Q / 2)) z b i‖ ^ 2) ^ ((1 : ℝ) / 2) :=
          norm_pairing_le_L2 _ _
      _ ≤ (A * (∑ a, (max 1 (‖f a‖ ^ (p / 2))) ^ 2) ^ ((1 : ℝ) / 2))
            * (∑ b, (max 1 ((n2 (g b)) ^ Q)) ^ 2) ^ ((1 : ℝ) / 2) :=
          mul_le_mul hfirst hsecond (by positivity) (by positivity)
      _ = A * (∑ a, (max 1 (‖f a‖ ^ (p / 2))) ^ 2) ^ ((1 : ℝ) / 2)
            * (∑ b, (max 1 ((n2 (g b)) ^ Q)) ^ 2) ^ ((1 : ℝ) / 2) := by ring
  -- three lines
  have hthree := Commons.Analysis.Complex.hadamard_three_lines F hFdiff hA hB hboundInt hbound0 hbound1
  have hres := hthree (θ : ℂ) (by simp [Complex.ofReal_re, hθpos.le])
    (by simp [Complex.ofReal_re, hθlt1.le])
  rw [Complex.ofReal_re] at hres
  have hFθ : F (θ : ℂ) = ∑ b, ∑ i, (T f) b i * g b i := by
    rw [hFdef]
    exact threeLinesF_self T f g htθ hsθ
  rw [hFθ] at hres
  have hAexp : A ^ (1 - θ) = A ^ (2 / p) := by
    congr 1
    rw [hθdef]; ring
  have hBexp : B ^ θ = B ^ (1 - 2 / p) := by rw [hθdef]
  rwa [hAexp, hBexp] at hres

end

end Work.BourgainPlan.IonescuWainger
