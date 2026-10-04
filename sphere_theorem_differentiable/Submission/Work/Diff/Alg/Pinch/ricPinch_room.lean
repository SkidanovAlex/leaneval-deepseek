import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.exists_eps_margin_quad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Perturbation room for the Ricci pinching condition

This file proves `Work.Diff.Alg.Pinch.ricPinch_room`: the compactness/uniformity step which turns
the *pointwise strictness* statement `RicPinch_one_step_of_strict` into a statement with room for a
further algebraic perturbation.

The mathematical content.  Write `A R v = ∑ᵢⱼ (ric R i j) vᵢ vⱼ` and let

`M R = ric R - (p · scal R / n) · id`,   `q R v = ∑ᵢⱼ M R i j vᵢ vⱼ = A R v - (p·scal R/n)‖v‖²`

be the matrix of the pinching margin and its quadratic form.  `RicPinch p R` says exactly that
`q R ≥ 0` (positive semidefiniteness of `M R`).  The hypotheses are

* `q S ≥ 0` (`hric`), the pinching of `S` at `p`;
* `q W v > 0` for every `v ≠ 0` with `q S v = 0` (`hstrict`), strict improvement of the margin
  along `W` in the tight directions of `S`.

Since `q` is linear in the tensor, `q (S + τ • (W + Y)) v = q S v + τ (q W v + q Y v)`, so the
claim `RicPinch p (S + τ • (W + Y))` for small `τ > 0` and small perturbations `Y` reduces to

`q S v + τ q W v ≥ τ · c · ‖v‖²`  and  `|q Y v| ≤ C ‖Y‖ ‖v‖²`

for suitable constants `c, C > 0` (both independent of `τ` and `Y`).  The first is the *scaled*
margin lemma `exists_scaled_margin` below — a strengthening of
`Work.Diff.Alg.Pinch.exists_eps_margin_quad` in which the margin is proportional to `τ`, obtained
from the compactness of the intersection of the unit sphere with the kernel of `q S`; the second is
the elementary finite-dimensional estimate `abs_quad_mPinch_le`.  Taking `ρ = c / (2 C)` finishes.

The hypotheses `IsAlgCurv S`, `IsAlgCurv W`, `IsAlgCurv Y` are not used: the argument is purely
about the quadratic forms attached to `ric` and `scalAlg`, i.e. about the linear map `R ↦ M R`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The matrix of the pinching margin of a curvature tensor:
`M R i j = ric R i j - (p · scal R / n) · δᵢⱼ`.

`Work.Diff.Alg.Pinch.RicPinch p R` is exactly the positive semidefiniteness of the quadratic form of
this matrix. -/
noncomputable def mPinch (p : ℝ) (R : Curv4 n) : Fin n → Fin n → ℝ :=
  fun i j => ric R i j - (p * scalAlg R / (n : ℝ)) * id2 n i j

/-! ## Elementary algebra of the quadratic forms -/

/-- The quadratic form of the identity `2`-tensor is the squared Euclidean norm. -/
private lemma quad_id2_eq (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i := by
  apply Finset.sum_congr rfl
  intro i _
  simp [id2]

/-- The quadratic form of `M - c · id`. -/
private lemma quad_sub_id2 (n : ℕ) (M : Fin n → Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (M i j - c * id2 n i j) * v i * v j)
      = (∑ i, ∑ j, M i j * v i * v j) - c * (∑ i, v i * v i) := by
  have h1 : ∀ i j : Fin n, (M i j - c * id2 n i j) * v i * v j
      = M i j * v i * v j - c * (id2 n i j * v i * v j) := fun i j => by ring
  simp only [h1, Finset.sum_sub_distrib]
  have h2 : (∑ i, ∑ j, c * (id2 n i j * v i * v j))
      = c * (∑ i, ∑ j, id2 n i j * v i * v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  rw [h2, quad_id2_eq]

/-- The quadratic form of `M + s · N`. -/
private lemma quad_add_smul_id (n : ℕ) (M N : Fin n → Fin n → ℝ) (s : ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (M i j + s * N i j) * v i * v j)
      = (∑ i, ∑ j, M i j * v i * v j) + s * (∑ i, ∑ j, N i j * v i * v j) := by
  have h1 : ∀ i j : Fin n, (M i j + s * N i j) * v i * v j
      = M i j * v i * v j + s * (N i j * v i * v j) := fun i j => by ring
  simp only [h1, Finset.sum_add_distrib]
  have h2 : (∑ i, ∑ j, s * (N i j * v i * v j)) = s * (∑ i, ∑ j, N i j * v i * v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  rw [h2]

/-- A constant multiple of the rank-one matrix `|u i| |u j|`. -/
private lemma sum_sum_const_mul (n : ℕ) (K : ℝ) (u : Fin n → ℝ) :
    (∑ i, ∑ j, K * |u i| * |u j|) = K * (∑ i, |u i|) ^ 2 := by
  have h1 : (∑ i, ∑ j, |u i| * |u j|) = (∑ i, |u i|) * (∑ i, |u i|) := by
    rw [Finset.sum_mul_sum]
  have h2 : (∑ i, ∑ j, K * |u i| * |u j|) = K * (∑ i, ∑ j, |u i| * |u j|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [h2, h1, pow_two]

/-! ## Linearity of `ric` and `scalAlg` -/

private lemma ric_add_aux (n : ℕ) (A B : Curv4 n) (i j : Fin n) :
    ric (A + B) i j = ric A i j + ric B i j := by
  simp only [ric, Pi.add_apply, Finset.sum_add_distrib]

private lemma ric_smul_aux (n : ℕ) (c : ℝ) (A : Curv4 n) (i j : Fin n) :
    ric (c • A) i j = c * ric A i j := by
  simp only [ric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private lemma scalAlg_add_aux (n : ℕ) (A B : Curv4 n) :
    scalAlg (A + B) = scalAlg A + scalAlg B := by
  simp only [scalAlg, Pi.add_apply, Finset.sum_add_distrib]

private lemma scalAlg_smul_aux (n : ℕ) (c : ℝ) (A : Curv4 n) :
    scalAlg (c • A) = c * scalAlg A := by
  simp only [scalAlg, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private lemma ric_add_smul (n : ℕ) (A B : Curv4 n) (t : ℝ) (i j : Fin n) :
    ric (A + t • B) i j = ric A i j + t * ric B i j := by
  rw [ric_add_aux, ric_smul_aux]

private lemma scalAlg_add_smul (n : ℕ) (A B : Curv4 n) (t : ℝ) :
    scalAlg (A + t • B) = scalAlg A + t * scalAlg B := by
  rw [scalAlg_add_aux, scalAlg_smul_aux]

private lemma quad_ric_add_smul (n : ℕ) (A B : Curv4 n) (t : ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, ric (A + t • B) i j * v i * v j)
      = (∑ i, ∑ j, ric A i j * v i * v j) + t * (∑ i, ∑ j, ric B i j * v i * v j) := by
  rw [show (∑ i, ∑ j, ric (A + t • B) i j * v i * v j)
      = ∑ i, ∑ j, (ric A i j + t * ric B i j) * v i * v j from by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ric_add_smul]]
  exact quad_add_smul_id n (fun i j => ric A i j) (fun i j => ric B i j) t v

/-! ## A margin along the kernel, uniform on the unit sphere -/

private lemma ne_zero_of_normSq_eq_one {n : ℕ} {v : Fin n → ℝ} (h : normSq v = 1) : v ≠ 0 := by
  intro hv
  have h0 : normSq v = 0 := by rw [hv]; simp [normSq]
  rw [h0] at h
  exact zero_ne_one h

/-- If `q B > 0` on the nonzero kernel of the positive semidefinite form `q A`, then there is a
constant `c > 0` with `c ‖v‖² < q B v` on the whole (nonzero) kernel of `q A`. -/
lemma exists_margin_const_of_pos_on_kernel (n : ℕ) (hn : 1 ≤ n) (MA MB : Fin n → Fin n → ℝ)
    (hAB : ∀ v : Fin n → ℝ, v ≠ 0 → quad MA v = 0 → 0 < quad MB v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin n → ℝ, v ≠ 0 → quad MA v = 0 → c * normSq v < quad MB v := by
  have hclosed : IsClosed {v : Fin n → ℝ | normSq v = 1 ∧ quad MA v = 0} :=
    (isClosed_eq continuous_normSq continuous_const).inter
      (isClosed_eq (continuous_quad MA) continuous_const)
  have hsub : {v : Fin n → ℝ | normSq v = 1 ∧ quad MA v = 0} ⊆
      {v : Fin n → ℝ | normSq v = 1} := fun _ hv => hv.1
  have hK : IsCompact {v : Fin n → ℝ | normSq v = 1 ∧ quad MA v = 0} :=
    IsCompact.of_isClosed_subset (isCompact_normSq_eq_one n) hclosed hsub
  obtain ⟨c, hc0, hcle⟩ := IsCompact.exists_forall_le' (f := quad MB) hK
    (continuous_quad MB).continuousOn (a := 0)
    (fun b hb => hAB b (ne_zero_of_normSq_eq_one hb.1) hb.2)
  refine ⟨c / 2, by linarith, fun v hv h0 => ?_⟩
  set t : ℝ := Real.sqrt (normSq v) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (normSq_pos hv)
  have htne : t ≠ 0 := ne_of_gt htpos
  have ht2 : t ^ 2 = normSq v := Real.sq_sqrt (normSq_nonneg v)
  set w : Fin n → ℝ := t⁻¹ • v with hw
  have hwS : normSq w = 1 := by
    rw [hw, normSq_smul, ← ht2, ← mul_pow, inv_mul_cancel₀ htne, one_pow]
  have htw : t • w = v := by
    rw [hw, smul_smul, mul_inv_cancel₀ htne, one_smul]
  have hwA : quad MA w = 0 := by
    rw [hw, quad_smul, h0, mul_zero]
  have hle : c ≤ quad MB w := hcle w ⟨hwS, hwA⟩
  have hb : quad MB v = normSq v * quad MB w := by
    have h1 : quad MB v = quad MB (t • w) := by rw [htw]
    rw [h1, quad_smul, ht2]
  calc c / 2 * normSq v < quad MB w * normSq v :=
        mul_lt_mul_of_pos_right (by linarith) (normSq_pos hv)
    _ = quad MB v := by rw [hb]; ring

/-- **The scaled margin lemma.**  If `q A ≥ 0` and `q B > 0` on the nonzero kernel of `q A`, then
`q A + s q B` dominates `s · c · ‖v‖²` for all sufficiently small `s > 0`, with `c > 0` *not*
depending on `s`.  This is the strengthening of `Work.Diff.Alg.Pinch.exists_eps_margin_quad` that
survives an additional perturbation of `B` of size `O(s)`.

It is the reusable "pointwise strictness ⟹ one step" compactness input: applied to
`MA = mPinch p S`, `MB = mPinch p W` it yields, for all small `s > 0`,

`q S v + s · q W v ≥ s · c · ‖v‖²`  (`q R v = ∑ᵢⱼ mPinch p R i j vᵢ vⱼ`),

i.e. a *uniform* positive margin for `RicPinch p (S + s • W)` with room for a perturbation `s • Y`
with `‖Y‖ ≤ c / (2 C)` (`C` as in `abs_quad_mPinch_le` below). -/
lemma exists_scaled_margin_quad (n : ℕ) (hn : 1 ≤ n) (MA MB : Fin n → Fin n → ℝ)
    (hA : ∀ v : Fin n → ℝ, 0 ≤ quad MA v)
    (hAB : ∀ v : Fin n → ℝ, v ≠ 0 → quad MA v = 0 → 0 < quad MB v) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε → ∀ v : Fin n → ℝ,
      s * c * normSq v ≤ quad MA v + s * quad MB v := by
  obtain ⟨c, hcpos, hc⟩ := exists_margin_const_of_pos_on_kernel n hn MA MB hAB
  have hA' : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, MA i j * v i * v j := fun v => hA v
  have hAB' : ∀ v : Fin n → ℝ, v ≠ 0 → (∑ i, ∑ j, MA i j * v i * v j) = 0 →
      0 < ∑ i, ∑ j, (MB i j - c * id2 n i j) * v i * v j := by
    intro v hv h0
    have h1 : c * (∑ i, v i * v i) < ∑ i, ∑ j, MB i j * v i * v j := hc v hv h0
    have h3 := quad_sub_id2 n MB c v
    linarith
  obtain ⟨ε, hεpos, hε⟩ := exists_eps_margin_quad n hn MA
    (fun i j => MB i j - c * id2 n i j) hA' hAB'
  refine ⟨c, hcpos, ε, hεpos, fun s hs hse v => ?_⟩
  obtain ⟨m, hmpos, hmle⟩ := hε s hs hse
  have hmlev : m * (∑ i, v i * v i)
      ≤ (∑ i, ∑ j, MA i j * v i * v j)
        + s * (∑ i, ∑ j, (MB i j - c * id2 n i j) * v i * v j) := hmle v
  have h3 := quad_sub_id2 n MB c v
  rw [h3] at hmlev
  rcases eq_or_ne v 0 with rfl | hv
  · simp [normSq, quad]
  · have hN : 0 < ∑ i, v i * v i := normSq_pos hv
    have h1 : s * c * (∑ i, v i * v i)
        < m * (∑ i, v i * v i) + s * c * (∑ i, v i * v i) := by
      have := mul_pos hmpos hN
      linarith
    have h2 : m * (∑ i, v i * v i) + s * c * (∑ i, v i * v i)
        ≤ (∑ i, ∑ j, MA i j * v i * v j) + s * (∑ i, ∑ j, MB i j * v i * v j) := by
      linarith [hmlev]
    show s * c * (∑ i, v i * v i)
        ≤ (∑ i, ∑ j, MA i j * v i * v j) + s * (∑ i, ∑ j, MB i j * v i * v j)
    linarith [h1, h2]

/-! ## The size of the quadratic form of `mPinch` in terms of the sup norm -/

/-- The quadratic form of `mPinch p Y = ric Y - (p · scal Y / n)·id` is bounded by a constant times
`‖Y‖` times `‖v‖²`; an explicit constant is `n² (1 + |p|) + 1`. -/
lemma abs_quad_mPinch_le (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (Y : Curv4 n) (v : Fin n → ℝ) :
    |∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j|
      ≤ ((n : ℝ) ^ 2 * (1 + |p|) + 1) * ‖Y‖ * (∑ i, v i * v i) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hY : ∀ i j k l : Fin n, |Y i j k l| ≤ ‖Y‖ := by
    intro i j k l
    have h1 : |Y i j k l| ≤ ‖Y i j k‖ := by simpa using norm_le_pi_norm (Y i j k) l
    have h2 : ‖Y i j k‖ ≤ ‖Y i j‖ := norm_le_pi_norm (Y i j) k
    have h3 : ‖Y i j‖ ≤ ‖Y i‖ := norm_le_pi_norm (Y i) j
    have h4 : ‖Y i‖ ≤ ‖Y‖ := norm_le_pi_norm Y i
    linarith
  have hric : ∀ i j : Fin n, |ric Y i j| ≤ (n : ℝ) * ‖Y‖ := by
    intro i j
    calc |ric Y i j| = |∑ k, Y k i k j| := rfl
      _ ≤ ∑ k, |Y k i k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, ‖Y‖ := Finset.sum_le_sum (fun k _ => hY k i k j)
      _ = (n : ℝ) * ‖Y‖ := by simp
  have hscal : |scalAlg Y| ≤ (n : ℝ) * ((n : ℝ) * ‖Y‖) := by
    calc |scalAlg Y| = |∑ i, ∑ j, Y i j i j| := rfl
      _ ≤ ∑ i, |∑ j, Y i j i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |Y i j i j| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖Y‖ :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hY i j i j))
      _ = (n : ℝ) * ((n : ℝ) * ‖Y‖) := by simp
  have hcoef : |p * scalAlg Y / (n : ℝ)| ≤ |p| * (n : ℝ) * ‖Y‖ := by
    rw [abs_div, abs_mul, abs_of_pos hnpos]
    have h1 : |p| * |scalAlg Y| ≤ |p| * ((n : ℝ) * ((n : ℝ) * ‖Y‖)) :=
      mul_le_mul_of_nonneg_left hscal (abs_nonneg p)
    calc |p| * |scalAlg Y| / (n : ℝ) ≤ |p| * ((n : ℝ) * ((n : ℝ) * ‖Y‖)) / (n : ℝ) :=
          div_le_div_of_nonneg_right h1 hnpos.le
      _ = |p| * (n : ℝ) * ‖Y‖ := by
          rw [div_eq_iff (ne_of_gt hnpos)]
          ring
  have hM : ∀ i j : Fin n, |ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j|
      ≤ (n : ℝ) * (1 + |p|) * ‖Y‖ := by
    intro i j
    have hid : |id2 n i j| ≤ 1 := by
      simp only [id2]
      split_ifs <;> simp
    have h2 : |(p * scalAlg Y / (n : ℝ)) * id2 n i j| ≤ |p| * (n : ℝ) * ‖Y‖ := by
      calc |(p * scalAlg Y / (n : ℝ)) * id2 n i j|
          = |p * scalAlg Y / (n : ℝ)| * |id2 n i j| := abs_mul _ _
        _ ≤ (|p| * (n : ℝ) * ‖Y‖) * 1 :=
            mul_le_mul hcoef hid (abs_nonneg _) (by positivity)
        _ = |p| * (n : ℝ) * ‖Y‖ := by ring
    calc |ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j|
        ≤ |ric Y i j| + |(p * scalAlg Y / (n : ℝ)) * id2 n i j| := by
          have h := abs_add_le (ric Y i j) (-((p * scalAlg Y / (n : ℝ)) * id2 n i j))
          simpa [sub_eq_add_neg, abs_neg] using h
      _ ≤ (n : ℝ) * ‖Y‖ + |p| * (n : ℝ) * ‖Y‖ := add_le_add (hric i j) h2
      _ = (n : ℝ) * (1 + |p|) * ‖Y‖ := by ring
  have hK : (0 : ℝ) ≤ (n : ℝ) * (1 + |p|) * ‖Y‖ := by positivity
  have hcs : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * (∑ i, v i * v i) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |v i|)
    rw [Finset.card_univ, Fintype.card_fin] at h
    calc (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, |v i| ^ 2 := h
      _ = (n : ℝ) * ∑ i, v i * v i := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [sq_abs, pow_two]
  have hN : 0 ≤ ∑ i, v i * v i := normSq_nonneg v
  have hYn : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg Y
  calc |∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j|
      = |∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j| := rfl
    _ ≤ ∑ i, ∑ j,
          |(ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j| := by
        calc |∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j|
            = |∑ i, (∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j)
                * v i * v j)| := rfl
          _ ≤ ∑ i, |∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j,
                |(ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j| :=
              Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, ∑ j, |ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j| * |v i| * |v j| := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [abs_mul, abs_mul]
    _ ≤ ∑ i, ∑ j, ((n : ℝ) * (1 + |p|) * ‖Y‖) * |v i| * |v j| := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hM i j) (abs_nonneg _)) (abs_nonneg _)
    _ = (n : ℝ) * (1 + |p|) * ‖Y‖ * (∑ i, |v i|) ^ 2 := sum_sum_const_mul n _ v
    _ ≤ (n : ℝ) * (1 + |p|) * ‖Y‖ * ((n : ℝ) * (∑ i, v i * v i)) :=
        mul_le_mul_of_nonneg_left hcs hK
    _ ≤ ((n : ℝ) ^ 2 * (1 + |p|) + 1) * ‖Y‖ * (∑ i, v i * v i) := by
        have h1 : (n : ℝ) * (1 + |p|) * ‖Y‖ * ((n : ℝ) * (∑ i, v i * v i))
            = ((n : ℝ) * (n : ℝ)) * (1 + |p|) * ‖Y‖ * (∑ i, v i * v i) := by ring
        have h2 : ((n : ℝ) ^ 2 * (1 + |p|) + 1) * ‖Y‖ * (∑ i, v i * v i)
            = ((n : ℝ) ^ 2 * (1 + |p|)) * ‖Y‖ * (∑ i, v i * v i)
              + ‖Y‖ * (∑ i, v i * v i) := by ring
        have h3 : (0 : ℝ) ≤ ‖Y‖ * (∑ i, v i * v i) := mul_nonneg hYn hN
        nlinarith [hYn, hN, h3]

/-! ## The target -/

theorem ricPinch_room (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp1 : p < 1) {S W : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) (hW : Submission.Diff.Alg.IsAlgCurv W) (hric : Work.Diff.Alg.Pinch.RicPinch p S)
    (hstrict : ∀ v : Fin n → ℝ, v ≠ 0 →
      (p * Submission.Diff.Alg.scalAlg S / (n : ℝ)) * (∑ i, v i * v i) = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j →
      (p * Submission.Diff.Alg.scalAlg W / (n : ℝ)) * (∑ i, v i * v i) < ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric W i j * v i * v j) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      ∀ Y : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv Y → ‖Y‖ ≤ ρ → Work.Diff.Alg.Pinch.RicPinch p (S + τ • (W + Y)) := by
  have hMAeq : ∀ v : Fin n → ℝ, quad (mPinch p S) v
      = (∑ i, ∑ j, ric S i j * v i * v j) - (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i) := by
    intro v
    show (∑ i, ∑ j, (ric S i j - (p * scalAlg S / (n : ℝ)) * id2 n i j) * v i * v j) = _
    exact quad_sub_id2 n (fun i j => ric S i j) (p * scalAlg S / (n : ℝ)) v
  have hMBeq : ∀ v : Fin n → ℝ, quad (mPinch p W) v
      = (∑ i, ∑ j, ric W i j * v i * v j) - (p * scalAlg W / (n : ℝ)) * (∑ i, v i * v i) := by
    intro v
    show (∑ i, ∑ j, (ric W i j - (p * scalAlg W / (n : ℝ)) * id2 n i j) * v i * v j) = _
    exact quad_sub_id2 n (fun i j => ric W i j) (p * scalAlg W / (n : ℝ)) v
  have hA : ∀ v : Fin n → ℝ, 0 ≤ quad (mPinch p S) v := by
    intro v
    rw [hMAeq v]
    have h := hric v
    linarith
  have hAB : ∀ v : Fin n → ℝ, v ≠ 0 → quad (mPinch p S) v = 0 → 0 < quad (mPinch p W) v := by
    intro v hv h0
    rw [hMAeq v] at h0
    rw [hMBeq v]
    have h := hstrict v hv (by linarith)
    linarith
  obtain ⟨c, hcpos, ε, hεpos, hscale⟩ :=
    exists_scaled_margin_quad n hn (mPinch p S) (mPinch p W) hA hAB
  set C : ℝ := (n : ℝ) ^ 2 * (1 + |p|) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hbound : ∀ Y : Curv4 n, ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j|
        ≤ C * ‖Y‖ * (∑ i, v i * v i) := by
    intro Y v
    rw [hCdef]
    exact abs_quad_mPinch_le n hn p Y v
  refine ⟨ε, hεpos, c / (2 * C), by positivity, fun τ hτ0 hτε Y hYalg hYnorm v => ?_⟩
  have hs : τ * c * (∑ i, v i * v i)
      ≤ (∑ i, ∑ j, mPinch p S i j * v i * v j)
        + τ * (∑ i, ∑ j, mPinch p W i j * v i * v j) := hscale τ hτ0 hτε v
  have hN : 0 ≤ ∑ i, v i * v i := normSq_nonneg v
  have hYb : -(C * ‖Y‖ * (∑ i, v i * v i))
      ≤ ∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j := by
    have h := neg_abs_le (∑ i, ∑ j,
      (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j)
    linarith [hbound Y v]
  have hCρ : C * ‖Y‖ ≤ c / 2 := by
    have h1 : C * ‖Y‖ ≤ C * (c / (2 * C)) := mul_le_mul_of_nonneg_left hYnorm hCpos.le
    have h2 : C * (c / (2 * C)) = c / 2 := by
      field_simp
    linarith
  have hτY : -τ * (C * ‖Y‖) * (∑ i, v i * v i)
      ≤ τ * (∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j) := by
    have h := mul_le_mul_of_nonneg_left hYb hτ0.le
    linarith
  have hτC : τ * (C * ‖Y‖) * (∑ i, v i * v i) ≤ τ * (c / 2) * (∑ i, v i * v i) := by
    have h1 : τ * (C * ‖Y‖) ≤ τ * (c / 2) := mul_le_mul_of_nonneg_left hCρ hτ0.le
    exact mul_le_mul_of_nonneg_right h1 hN
  have hmain : 0 ≤ (∑ i, ∑ j, mPinch p S i j * v i * v j)
      + τ * ((∑ i, ∑ j, mPinch p W i j * v i * v j)
             + (∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j)) := by
    have h1 : τ * c * (∑ i, v i * v i) - τ * (C * ‖Y‖) * (∑ i, v i * v i)
        ≤ (∑ i, ∑ j, mPinch p S i j * v i * v j)
          + τ * ((∑ i, ∑ j, mPinch p W i j * v i * v j)
                 + (∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j)
                     * v i * v j)) := by
      linarith [hs, hτY]
    have h2 : τ * (c / 2) * (∑ i, v i * v i)
        ≤ τ * c * (∑ i, v i * v i) - τ * (C * ‖Y‖) * (∑ i, v i * v i) := by
      linarith [hτC]
    have h3 : 0 ≤ τ * (c / 2) * (∑ i, v i * v i) := by
      have hc2 : (0 : ℝ) ≤ c / 2 := by linarith
      exact mul_nonneg (mul_nonneg hτ0.le hc2) hN
    linarith [h1, h2, h3]
  have hricS : (∑ i, ∑ j, mPinch p S i j * v i * v j)
      = (∑ i, ∑ j, ric S i j * v i * v j) - (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i) := by
    rw [show (∑ i, ∑ j, mPinch p S i j * v i * v j) = quad (mPinch p S) v from rfl]
    exact hMAeq v
  have hricW : (∑ i, ∑ j, mPinch p W i j * v i * v j)
      = (∑ i, ∑ j, ric W i j * v i * v j) - (p * scalAlg W / (n : ℝ)) * (∑ i, v i * v i) := by
    rw [show (∑ i, ∑ j, mPinch p W i j * v i * v j) = quad (mPinch p W) v from rfl]
    exact hMBeq v
  have hricY : (∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j)
      = (∑ i, ∑ j, ric Y i j * v i * v j) - (p * scalAlg Y / (n : ℝ)) * (∑ i, v i * v i) :=
    quad_sub_id2 n (fun i j => ric Y i j) (p * scalAlg Y / (n : ℝ)) v
  have hscal : scalAlg (S + τ • (W + Y)) = scalAlg S + τ * (scalAlg W + scalAlg Y) := by
    have h1 : scalAlg (W + Y) = scalAlg W + scalAlg Y := by
      have h := scalAlg_add_smul n W Y 1
      simpa using h
    rw [scalAlg_add_smul n S (W + Y) τ, h1]
  have hricτ : (∑ i, ∑ j, ric (S + τ • (W + Y)) i j * v i * v j)
      = (∑ i, ∑ j, ric S i j * v i * v j)
        + τ * ((∑ i, ∑ j, ric W i j * v i * v j)
               + (∑ i, ∑ j, ric Y i j * v i * v j)) := by
    have h1 : (∑ i, ∑ j, ric (W + Y) i j * v i * v j)
        = (∑ i, ∑ j, ric W i j * v i * v j)
          + (∑ i, ∑ j, ric Y i j * v i * v j) := by
      have h := quad_ric_add_smul n W Y 1 v
      simpa using h
    rw [quad_ric_add_smul n S (W + Y) τ v, h1]
  have key : (∑ i, ∑ j, ric S i j * v i * v j)
        + τ * ((∑ i, ∑ j, ric W i j * v i * v j)
               + (∑ i, ∑ j, ric Y i j * v i * v j))
        - (p * (scalAlg S + τ * (scalAlg W + scalAlg Y)) / (n : ℝ)) * (∑ i, v i * v i)
      = (∑ i, ∑ j, mPinch p S i j * v i * v j)
        + τ * ((∑ i, ∑ j, mPinch p W i j * v i * v j)
               + (∑ i, ∑ j, (ric Y i j - (p * scalAlg Y / (n : ℝ)) * id2 n i j) * v i * v j)) := by
    rw [hricS, hricW, hricY]
    ring
  rw [hscal, hricτ]
  linarith [hmain, key]

end Work.Diff.Alg.Pinch
