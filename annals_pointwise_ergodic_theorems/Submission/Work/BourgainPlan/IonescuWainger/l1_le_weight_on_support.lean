import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.l1_combination_le_of_weight

open scoped BigOperators lp

namespace Work.BourgainPlan.IonescuWainger

/-- **Rerouting a kernel through a weight that inverts it only on the kernel's support.**  If `K`
vanishes off `S` and `W · v = 1` on `S`, then globally `W · (v · K) = K` (off `S` both sides
vanish because `K` does).  This is the single place where the support hypothesis `hKS` enters the
weighted `ℓ¹` bound. -/
theorem weight_mul_v_mul_eq_of_support {K : ℤ → ℂ} {v W : ℤ → ℂ} {S : Set ℤ}
    (hKS : ∀ n : ℤ, n ∉ S → K n = 0) (hvW : ∀ n : ℤ, n ∈ S → W n * v n = 1) (n : ℤ) :
    W n * (v n * K n) = K n := by
  by_cases hn : n ∈ S
  · rw [← mul_assoc, hvW n hn, one_mul]
  · rw [hKS n hn, mul_zero, mul_zero]

/-- **The weighted Cauchy–Schwarz/Pythagoras step of Tao's `p = ∞` argument, on the support.**  Same
as `tsum_norm_sum_le_weight` but with the weight `v` inverted by `W` only on the set `S` where the
kernels live: the Cauchy–Schwarz pairing only needs `Σ ‖W n‖²`, and the `ℓ²`-mass is measured with
the pieces `v · K i`. -/
theorem tsum_norm_sum_le_weight_on_support {ι : Type*} [Fintype ι] {K : ι → ℤ → ℂ} {v W : ℤ → ℂ}
    {S : Set ℤ} (hKS : ∀ (i : ι) (n : ℤ), n ∉ S → K i n = 0)
    (hvW : ∀ n : ℤ, n ∈ S → W n * v n = 1)
    (hKv : ∀ i, Memℓp (fun n : ℤ => v n * K i n) 2)
    (horth : ∀ i j, i ≠ j → ∑' n : ℤ, (v n * K i n) * star (v n * K j n) = 0)
    (hW : Memℓp W 2) (c : ι → ℂ) :
    ∑' n : ℤ, ‖∑ i, c i * K i n‖
      ≤ (∑' n : ℤ, ‖W n‖ ^ 2) ^ ((1 : ℝ) / 2)
          * (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  classical
  -- `W` and the weighted kernels `v · K i` as elements of `ℓ²(ℤ)`, and their combination.
  set Wl : lp (fun _ : ℤ => ℂ) 2 := ⟨W, hW⟩ with hWdef
  set F : ι → lp (fun _ : ℤ => ℂ) 2 := fun i => ⟨fun n => v n * K i n, hKv i⟩ with hFdef
  set G : lp (fun _ : ℤ => ℂ) 2 := ∑ i, c i • F i with hGdef
  have hW_apply : ∀ n : ℤ, Wl n = W n := fun n => rfl
  have hF_apply : ∀ i : ι, ∀ n : ℤ, F i n = v n * K i n := fun i n => rfl
  -- The coefficients of `G` are the rerouted combination.
  have hG_apply : ∀ n : ℤ, G n = ∑ i, c i * (v n * K i n) := by
    intro n
    rw [hGdef, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, hF_apply, smul_eq_mul]
  -- Rerouting the weight through the support: `∑ i, c i * K i n = W n * G n`.
  have hkey : ∀ n : ℤ, ∑ i, c i * K i n = Wl n * G n := by
    intro n
    rw [hW_apply, hG_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show W n * (c i * (v n * K i n)) = c i * (W n * (v n * K i n)) by ring,
      weight_mul_v_mul_eq_of_support (hKS i) hvW n]
  -- The rescaled pieces `c i · (v · K i)` are again pairwise orthogonal.
  have horth' : ∀ i j, i ≠ j →
      ∑' n : ℤ, (c i * (v n * K i n)) * star (c j * (v n * K j n)) = 0 := by
    intro i j hij
    rw [show (fun n : ℤ => (c i * (v n * K i n)) * star (c j * (v n * K j n)))
        = fun n => (c i * star (c j)) * ((v n * K i n) * star (v n * K j n)) from
      funext (fun n => by simp only [star_mul]; ring)]
    rw [tsum_mul_left, horth i j hij, mul_zero]
  have hgm : ∀ i, Memℓp (fun n : ℤ => c i * (v n * K i n)) 2 := fun i => (hKv i).const_mul (c i)
  -- Pythagoras: the squared `ℓ²`-norm of `G` splits over the orthogonal pieces.
  have hG_sq : ∑' n : ℤ, ‖G n‖ ^ 2 = ∑ i, ∑' n : ℤ, ‖c i * (v n * K i n)‖ ^ 2 := by
    rw [show (∑' n : ℤ, ‖G n‖ ^ 2) = ∑' n : ℤ, ‖∑ i, c i * (v n * K i n)‖ ^ 2 from
      tsum_congr (fun n => by rw [hG_apply n])]
    exact tsum_norm_sq_sum_of_orthogonal hgm horth'
  have hsplit : ∀ i, ∑' n : ℤ, ‖c i * (v n * K i n)‖ ^ 2
      = ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2 := by
    intro i
    rw [show (fun n : ℤ => ‖c i * (v n * K i n)‖ ^ 2)
        = fun n => ‖c i‖ ^ 2 * ‖v n * K i n‖ ^ 2 from funext (fun n => by rw [norm_mul]; ring)]
    rw [tsum_mul_left]
  have hG_sq' : ∑' n : ℤ, ‖G n‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2 := by
    rw [hG_sq]
    exact Finset.sum_congr rfl (fun i _ => hsplit i)
  -- The `ℓ²`-norms of `G` and `W` in the `tsum` shape of the statement.
  have hGnorm2 : ‖G‖ = (∑' n : ℤ, ‖G n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num) G]
    simp
  have hGnorm : ‖G‖ = (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [hGnorm2, hG_sq']
  have hWnorm : ‖Wl‖ = (∑' n : ℤ, ‖W n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num) Wl]
    simp [hW_apply]
  -- Hölder / Cauchy–Schwarz in `ℓ²(ℤ)`, from Mathlib's `lp`-space inequality.
  have hCS : ∑' n : ℤ, ‖Wl n‖ * ‖G n‖ ≤ ‖Wl‖ * ‖G‖ :=
    lp.tsum_mul_le_mul_norm' (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff]) Wl G
  calc ∑' n : ℤ, ‖∑ i, c i * K i n‖
      = ∑' n : ℤ, ‖Wl n * G n‖ := tsum_congr (fun n => by rw [hkey n])
    _ = ∑' n : ℤ, ‖Wl n‖ * ‖G n‖ := tsum_congr (fun n => by rw [norm_mul])
    _ ≤ ‖Wl‖ * ‖G‖ := hCS
    _ = _ := by rw [hWnorm, hGnorm]

/-- **The weighted `ℓ¹` bound with the Cauchy–Schwarz taken over the support.**  This is the form of
Tao's weighted step that is actually sharp: the kernels `K i` are supported in a set `S` (in the
application `S = Q_Aℤ`, and this is Tao's observation "the integrand is supported on `(Q_Aℤ)^d`"),
so the Cauchy–Schwarz with the inverse weight only needs `Σ_{n∈S}‖W n‖²`, where `W = w⁻¹` on `S`;
this is what makes the product of the two weight norms `O(1)` rather than `O(√Q)`. -/
theorem l1_le_weight_on_support {ι : Type*} [Fintype ι] {K : ι → ℤ → ℂ} {v W : ℤ → ℂ}
    {S : Set ℤ} (hKS : ∀ (i : ι) (n : ℤ), n ∉ S → K i n = 0)
    (hvW : ∀ n : ℤ, n ∈ S → W n * v n = 1)
    (hKv : ∀ i, Memℓp (fun n : ℤ => v n * K i n) 2)
    (horth : ∀ i j, i ≠ j → ∑' n : ℤ, (v n * K i n) * star (v n * K j n) = 0)
    (hW : Memℓp W 2) {C₁ C₂ : ℝ}
    (hC₁ : ∑' n : ℤ, ‖W n‖ ^ 2 ≤ C₁ ^ 2)
    (hC₂ : ∀ i, ∑' n : ℤ, ‖v n * K i n‖ ^ 2 ≤ C₂ ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (c : ι → ℂ) :
    ∑' n : ℤ, ‖∑ i, c i * K i n‖ ≤ C₁ * C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  classical
  have hmain := tsum_norm_sum_le_weight_on_support hKS hvW hKv horth hW c
  refine hmain.trans ?_
  -- Nonnegativity of the three quantities appearing in the bound.
  have hD_nn : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB_nn : 0 ≤ ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
      (tsum_nonneg (fun n => sq_nonneg _)))
  -- The `ℓ²`-mass of the weighted pieces is bounded by `C₂² ‖c‖²`.
  have hB_le : ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2
      ≤ C₂ ^ 2 * ∑ i, ‖c i‖ ^ 2 := by
    calc ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2
        ≤ ∑ i, ‖c i‖ ^ 2 * C₂ ^ 2 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hC₂ i) (sq_nonneg _))
      _ = (∑ i, ‖c i‖ ^ 2) * C₂ ^ 2 :=
          (Finset.sum_mul Finset.univ (fun i => ‖c i‖ ^ 2) (C₂ ^ 2)).symm
      _ = C₂ ^ 2 * ∑ i, ‖c i‖ ^ 2 := by ring
  -- Both square-root factors are bounded, and the product of the bounds is the claim.
  calc (∑' n : ℤ, ‖W n‖ ^ 2) ^ ((1 : ℝ) / 2)
        * (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖v n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ C₁ * (C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul (rpow_half_le_of_le_sq hC₁0 hC₁)
          (rpow_half_le_sq_mul hB_nn hC₂0 hD_nn hB_le)
          (Real.rpow_nonneg hB_nn _) hC₁0
    _ = C₁ * C₂ * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := (mul_assoc C₁ C₂ _).symm

end Work.BourgainPlan.IonescuWainger
