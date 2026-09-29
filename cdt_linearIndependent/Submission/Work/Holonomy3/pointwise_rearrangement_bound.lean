import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.ArcCert.sum_mul_max_eq_sorted
import Submission.Work.Holonomy3.fstats

/-!
# The pointwise rearrangement bound (Area H, the fine holonomy bound)

Given `d` numbers `u j ∈ [0,1)` of box discrepancy `≤ ε` and `d` numbers `v j` bounded by `G₀`,
such that *some* rearrangement of `u` and some rearrangement of `v` are nondecreasing, the weighted
sum `Σ_j u_j v_j` is bounded by the value of the rearrangement integral of `v` (the comonotone
pairing of the increasing rearrangement of `v` with the uniform grid `i/d`, which is exactly
`(1/(2d))·(Σ_{a,b} max(v a, v b) − Σ_a v a)`) plus the error `(ε + 1/d)·d·G₀`.

The mathematics is the rearrangement inequality.  Write `a = u ∘ ρ` and `b = v ∘ σ` (both
nondecreasing), so that the pairing is `Σ_j u_j v_j = Σ_i a_i b(τ i)` for the permutation
`τ = ρ.trans σ.symm`, and write `a_i = i/d + e_i`.  Then

* `Σ_j u_j v_j = Σ_i (i/d)·b(τ i) + Σ_i e_i·b(τ i)`;
* the first sum is at most `Σ_i (i/d)·b i` by the rearrangement inequality (`Monovary` API), since
  both `i ↦ i/d` and `b` are nondecreasing;
* the second is at most `d·ε·G₀`, because `sorted_bounds` of `fstats` gives `|e_i| ≤ ε` and
  `|b| ≤ G₀` pointwise;
* and `(ε + 1/d)·d·G₀ = ε·d·G₀ + G₀ ≥ ε·d·G₀`.

The evaluation of the double sum `Σ_{a,b} max(v a, v b) = Σ_i (2i+1)·b_i` is
`Work.ArcCert.sum_mul_max_eq_sorted` specialised to the constant weight `μ ≡ 1`.
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open scoped BigOperators

/-- Sorted evaluation of the double sum of `max`: for a nondecreasing `b`,
`Σ_{a,b} max (b a) (b b) = Σ_i (2i + 1) * b i`. -/
private theorem sum_max_sorted_eq {d : ℕ} (b : Fin d → ℝ) (hmono : Monotone b) :
    (∑ a, ∑ b', max (b a) (b b')) = ∑ i : Fin d, (2 * (i : ℝ) + 1) * b i := by
  have h := Work.ArcCert.sum_mul_max_eq_sorted (M := d) b (fun _ => (1 : ℝ)) (Equiv.refl (Fin d))
    (by simpa using hmono)
  simp only [one_mul, Equiv.refl_apply] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (∑ j ∈ Finset.univ.filter (fun j : Fin d => j ≤ i), (1 : ℝ)) = ((i : ℝ) + 1) := by
    rw [show Finset.univ.filter (fun j : Fin d => j ≤ i) = Finset.Iic i from by ext j; simp]
    rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have h2 : (∑ j ∈ Finset.univ.filter (fun j : Fin d => j < i), (1 : ℝ)) = ((i : ℝ)) := by
    rw [show Finset.univ.filter (fun j : Fin d => j < i) = Finset.Iio i from by ext j; simp]
    rw [Finset.sum_const, Fin.card_Iio, nsmul_eq_mul, mul_one]
  rw [h1, h2]
  ring

/-- The rearrangement integral of `v` (with the uniform grid weights `i/d`) is
`(1/(2d))·(Σ_{a,b} max(v a, v b) − Σ_a v a)`, the comonotone pairing of the increasing
rearrangement of `v` with the grid `i/d`. -/
private theorem main_term {d : ℕ} (v : Fin d → ℝ) (σ : Equiv.Perm (Fin d))
    (hσ : Monotone (v ∘ σ)) :
    (1 / (2 * (d : ℝ))) * ((∑ a, ∑ b, max (v a) (v b)) - ∑ a, v a)
      = ∑ i : Fin d, ((i : ℝ) / (d : ℝ)) * v (σ i) := by
  have hds : (∑ a, ∑ b, max (v a) (v b)) = ∑ a, ∑ b, max ((v ∘ σ) a) ((v ∘ σ) b) := by
    simp only [Function.comp_apply]
    rw [← Equiv.sum_comp σ (fun a => ∑ b, max (v a) (v b))]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Equiv.sum_comp σ (fun b => max (v (σ a)) (v b))]
  have hsum : (∑ a, v a) = ∑ i : Fin d, v (σ i) := (Equiv.sum_comp σ v).symm
  rw [hds, hsum]
  simp only [Function.comp_apply]
  rw [sum_max_sorted_eq (fun i => v (σ i)) hσ]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

/-- The permutation (rearrangement) part of the bound: if `a` is `ε`-close to the uniform grid
`i/d` and `b` is bounded by `G₀`, then pairing `a` against any permutation of the nondecreasing
`b` costs at most the comonotone pairing plus `(ε + 1/d)·d·G₀`. -/
private theorem pairing_bound {d : ℕ} (hd : 0 < d) (a b : Fin d → ℝ)
    (τ : Equiv.Perm (Fin d)) (hmono_b : Monotone b) {ε G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (herr : ∀ i, |a i - (i : ℝ) / (d : ℝ)| ≤ ε) (hG : ∀ i, |b i| ≤ G₀) :
    ∑ i : Fin d, a i * b (τ i) ≤
      ∑ i : Fin d, ((i : ℝ) / (d : ℝ)) * b i + (ε + 1 / (d : ℝ)) * (d : ℝ) * G₀ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmono_c : Monotone (fun i : Fin d => (i : ℝ) / (d : ℝ)) := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hdR.le
    exact_mod_cast hij
  have hsplit : (∑ i : Fin d, a i * b (τ i))
      = (∑ i : Fin d, ((i : ℝ) / (d : ℝ)) * b (τ i))
        + (∑ i : Fin d, (a i - (i : ℝ) / (d : ℝ)) * b (τ i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrearr : (∑ i : Fin d, ((i : ℝ) / (d : ℝ)) * b (τ i))
      ≤ ∑ i : Fin d, ((i : ℝ) / (d : ℝ)) * b i :=
    (hmono_c.monovary hmono_b).sum_mul_comp_perm_le_sum_mul
  have herr' : (∑ i : Fin d, (a i - (i : ℝ) / (d : ℝ)) * b (τ i)) ≤ ε * (d : ℝ) * G₀ := by
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      calc (a i - (i : ℝ) / (d : ℝ)) * b (τ i)
          ≤ |(a i - (i : ℝ) / (d : ℝ)) * b (τ i)| := le_abs_self _
        _ = |a i - (i : ℝ) / (d : ℝ)| * |b (τ i)| := abs_mul _ _
        _ ≤ ε * G₀ :=
            mul_le_mul (herr i) (hG (τ i)) (abs_nonneg _) (le_trans (abs_nonneg _) (herr i)))
    calc (∑ i : Fin d, (a i - (i : ℝ) / (d : ℝ)) * b (τ i)) ≤ ∑ i : Fin d, ε * G₀ := h1
      _ = ε * (d : ℝ) * G₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hfinal : ε * (d : ℝ) * G₀ ≤ (ε + 1 / (d : ℝ)) * (d : ℝ) * G₀ := by
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hthis : (ε + 1 / (d : ℝ)) * (d : ℝ) * G₀ = ε * (d : ℝ) * G₀ + G₀ := by
      field_simp
    rw [hthis]; linarith
  linarith [hsplit, hrearr, herr', hfinal]

/-- **The pointwise rearrangement bound.**  For `d ≥ 1`, a configuration `u` with values in
`[0,1)` and box discrepancy `≤ ε`, and a vector `v` bounded by `G₀` whose increasing rearrangement
exists (`v ∘ σ` nondecreasing), the weighted sum `Σ_j u_j v_j` is bounded by the rearrangement
integral `(1/(2d))·(Σ_{a,b} max(v a, v b) − Σ_a v a)` plus the error `(ε + 1/d)·d·G₀`. -/
theorem pointwise_rearrangement_bound {d : ℕ} (hd : 0 < d) (u v : Fin d → ℝ)
    (ρ σ : Equiv.Perm (Fin d)) (hρ : Monotone (u ∘ ρ)) (hσ : Monotone (v ∘ σ))
    {ε G₀ : ℝ} (hε : 0 ≤ ε) (hG0 : 0 ≤ G₀)
    (hu : ∀ j, u j ∈ Set.Ico 0 1) (hdisc : Submission.CDT.Discrepancy.disc u ≤ ε)
    (hG : ∀ j, |v j| ≤ G₀) :
    ∑ j, u j * v j ≤
      (1 / (2 * (d : ℝ))) * ((∑ a, ∑ b, max (v a) (v b)) - ∑ a, v a)
        + (ε + 1 / (d : ℝ)) * (d : ℝ) * G₀ := by
  have hdisc' : Submission.CDT.Discrepancy.disc (fun i => u (ρ i)) ≤ ε := by
    rw [disc_comp_perm u ρ]; exact hdisc
  have herr : ∀ i : Fin d, |(fun i => u (ρ i)) i - (i : ℝ) / (d : ℝ)| ≤ ε := by
    intro i
    obtain ⟨h1, h2⟩ :=
      sorted_bounds (fun i => u (ρ i)) (fun j => hu (ρ j)) hρ hε hdisc' i
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpair := pairing_bound hd (fun i => u (ρ i)) (fun i => v (σ i)) (ρ.trans σ.symm) hσ
    hG0 herr (fun i => hG (σ i))
  have hLHS : (∑ j : Fin d, u j * v j)
      = ∑ i : Fin d, (u ∘ ρ) i * (v ∘ σ) ((ρ.trans σ.symm) i) := by
    rw [← Equiv.sum_comp ρ (fun j => u j * v j)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hLHS, main_term v σ hσ]
  exact hpair

end Work.Holonomy3
