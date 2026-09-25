import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_sum_of_orthogonal

open scoped BigOperators lp

namespace Work.BourgainPlan.IonescuWainger

/-- **The weighted Cauchy–Schwarz/Pythagoras step of Tao's `p = ∞` argument.**  If `w` is a weight
which is never zero, the weighted kernels `w·K i` are square-summable and pairwise `ℓ²`-orthogonal,
then the `ℓ¹`-norm of any linear combination `Σ_i c_i K_i` is controlled by the `ℓ²`-norms of the
weighted pieces.  (In the application `w(n) = 1 + ε²n²` and the orthogonality comes from the
disjoint frequency supports of the `K i`, preserved by the polynomial weight.) -/
theorem tsum_norm_sum_le_weight {ι : Type*} [Fintype ι] {K : ι → ℤ → ℂ} {w : ℤ → ℂ}
    (hw : ∀ n : ℤ, w n ≠ 0) (hK : ∀ i, Memℓp (fun n : ℤ => w n * K i n) 2)
    (horth : ∀ i j, i ≠ j → ∑' n : ℤ, (w n * K i n) * star (w n * K j n) = 0)
    (hwinv : Memℓp (fun n : ℤ => (w n)⁻¹) 2) (c : ι → ℂ)
    (hsum : Summable fun n : ℤ => ∑ i, ‖c i * K i n‖) :
    ∑' n : ℤ, ‖∑ i, c i * K i n‖
      ≤ (∑' n : ℤ, ‖(w n)⁻¹‖ ^ 2) ^ ((1 : ℝ) / 2)
          * (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  classical
  -- The hypothesis `hsum` is not needed: the decay of the weight already bounds the whole sum.
  have _hsum := hsum
  -- `W` is the weighted reciprocal, `F i = w · K i`, and `G = Σ_i c_i · F i`, all in `ℓ²(ℤ)`.
  set W : lp (fun _ : ℤ => ℂ) 2 := ⟨fun n => (w n)⁻¹, hwinv⟩ with hWdef
  set F : ι → lp (fun _ : ℤ => ℂ) 2 := fun i => ⟨fun n => w n * K i n, hK i⟩ with hFdef
  set G : lp (fun _ : ℤ => ℂ) 2 := ∑ i, c i • F i with hGdef
  have hW_apply : ∀ n : ℤ, W n = (w n)⁻¹ := fun n => rfl
  have hF_apply : ∀ i : ι, ∀ n : ℤ, F i n = w n * K i n := fun i n => rfl
  -- The coefficients of `G` are the rerouted combination.
  have hG_apply : ∀ n : ℤ, G n = ∑ i, c i * (w n * K i n) := by
    intro n
    rw [hGdef, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, hF_apply, smul_eq_mul]
  -- Rerouting the weight: `∑ i, c i * K i n = W n * G n`.
  have hkey : ∀ n : ℤ, ∑ i, c i * K i n = W n * G n := by
    intro n
    rw [hW_apply, hG_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (w n)⁻¹ * (c i * (w n * K i n)) = c i * ((w n)⁻¹ * (w n * K i n)) by ring,
      inv_mul_cancel_left₀ (hw n)]
  -- The rescaled pieces `c i · (w · K i)` are again pairwise orthogonal.
  have horth' : ∀ i j, i ≠ j →
      ∑' n : ℤ, (c i * (w n * K i n)) * star (c j * (w n * K j n)) = 0 := by
    intro i j hij
    rw [show (fun n : ℤ => (c i * (w n * K i n)) * star (c j * (w n * K j n)))
        = fun n => (c i * star (c j)) * ((w n * K i n) * star (w n * K j n)) from
      funext (fun n => by simp only [star_mul]; ring)]
    rw [tsum_mul_left, horth i j hij, mul_zero]
  have hgm : ∀ i, Memℓp (fun n : ℤ => c i * (w n * K i n)) 2 := fun i => (hK i).const_mul (c i)
  have hsqF : ∀ i, Summable (fun n : ℤ => ‖w n * K i n‖ ^ 2) := fun i =>
    by simpa [Real.rpow_two] using (memℓp_gen_iff (p := 2) (by norm_num)).mp (hK i)
  -- Pythagoras: the squared `ℓ²`-norm of `G` splits over the orthogonal pieces.
  have hG_sq : ∑' n : ℤ, ‖G n‖ ^ 2 = ∑ i, ∑' n : ℤ, ‖c i * (w n * K i n)‖ ^ 2 := by
    rw [show (∑' n : ℤ, ‖G n‖ ^ 2) = ∑' n : ℤ, ‖∑ i, c i * (w n * K i n)‖ ^ 2 from
      tsum_congr (fun n => by rw [hG_apply n])]
    exact tsum_norm_sq_sum_of_orthogonal hgm horth'
  have hsplit : ∀ i, ∑' n : ℤ, ‖c i * (w n * K i n)‖ ^ 2
      = ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2 := by
    intro i
    rw [show (fun n : ℤ => ‖c i * (w n * K i n)‖ ^ 2)
        = fun n => ‖c i‖ ^ 2 * ‖w n * K i n‖ ^ 2 from funext (fun n => by rw [norm_mul]; ring)]
    rw [tsum_mul_left]
  have hG_sq' : ∑' n : ℤ, ‖G n‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2 := by
    rw [hG_sq]
    exact Finset.sum_congr rfl (fun i _ => hsplit i)
  -- The `ℓ²`-norms of `G` and `W` in the `tsum` shape of the statement.
  have hGnorm2 : ‖G‖ = (∑' n : ℤ, ‖G n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num) G]
    simp
  have hGnorm : ‖G‖ = (∑ i, ‖c i‖ ^ 2 * ∑' n : ℤ, ‖w n * K i n‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [hGnorm2, hG_sq']
  have hWnorm : ‖W‖ = (∑' n : ℤ, ‖(w n)⁻¹‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num) W]
    simp [hW_apply]
  -- Hölder / Cauchy–Schwarz in `ℓ²(ℤ)`, from Mathlib's `lp`-space inequality.
  have hCS : ∑' n : ℤ, ‖W n‖ * ‖G n‖ ≤ ‖W‖ * ‖G‖ :=
    lp.tsum_mul_le_mul_norm' (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff]) W G
  calc ∑' n : ℤ, ‖∑ i, c i * K i n‖
      = ∑' n : ℤ, ‖W n * G n‖ := tsum_congr (fun n => by rw [hkey n])
    _ = ∑' n : ℤ, ‖W n‖ * ‖G n‖ := tsum_congr (fun n => by rw [norm_mul])
    _ ≤ ‖W‖ * ‖G‖ := hCS
    _ = _ := by rw [hWnorm, hGnorm]

end Work.BourgainPlan.IonescuWainger
