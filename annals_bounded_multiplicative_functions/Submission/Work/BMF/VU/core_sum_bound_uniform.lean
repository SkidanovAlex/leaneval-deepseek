import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.holder_box
import Submission.Work.BMF.VU.arcind_box
import Submission.Work.BMF.VU.nu_integrals
import Submission.Work.BMF.VU.polysum_abel_compare_v2
import Submission.Work.BMF.VU.nset_count_bridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Heath-Brown's core mean-value bound, with an explicit constant `exp(k³)`

`core_sum_bound_uniform` is the `ν`/Hölder step of Heath-Brown's Lemma 1 (Vinogradov's reduction):
for `k ≥ 2`, `H ≥ 1`, `L = ⌊H⌋₊ < N`, `s ≥ 1` and `M` bounding the power means of the polynomial
exponential sums on the box, the sum `Σ_{n ≤ N-L} ‖polySum (k-1) a_n y‖` is at most
`exp(C₀k³) (N-L)^{1-1/s} 𝒩^{1/2s} H^{k(k-1)/(4s)} M^{1/2s}`, uniformly in `k`.
-/

namespace Work.BMF

open Finset MeasureTheory Set
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## Elementary complements -/

private lemma norm_eC_core (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

lemma arcInd_eq_zero_or_one (a δ t : ℝ) : arcInd a δ t = 0 ∨ arcInd a δ t = 1 := by
  unfold arcInd; split_ifs <;> simp

lemma arcInd_eq_one_iff (a δ t : ℝ) :
    arcInd a δ t = 1 ↔ ∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ := by
  unfold arcInd
  by_cases h : ∃ z : ℤ, |t - a - (z : ℝ)| ≤ δ
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun hh => absurd hh.symm one_ne_zero, fun hh => absurd hh h⟩

lemma prod_eq_zero_or_one_of_forall {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (h : ∀ i ∈ s, g i = 0 ∨ g i = 1) : ∏ i ∈ s, g i = 0 ∨ ∏ i ∈ s, g i = 1 := by
  induction s using Finset.induction with
  | empty => right; simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      rcases ih (fun x hx => h x (Finset.mem_insert_of_mem hx)) with h0 | h1
      · left; rw [h0, mul_zero]
      · rcases h i (Finset.mem_insert_self i s) with h0 | h1'
        · left; rw [h0, zero_mul]
        · right; rw [h1, h1', mul_one]

lemma prod_arcInd_eq_one_iff (m : ℕ) (a δ : Fin m → ℝ) (α : Fin m → ℝ) :
    (∏ j : Fin m, arcInd (a j) (δ j) (α j)) = 1 ↔ ∀ j : Fin m, arcInd (a j) (δ j) (α j) = 1 := by
  refine ⟨fun h j => ?_, fun h => by simp [h]⟩
  by_contra hj
  have hj0 : arcInd (a j) (δ j) (α j) = 0 := (arcInd_eq_zero_or_one _ _ _).resolve_right hj
  exact absurd (h ▸ Finset.prod_eq_zero (Finset.mem_univ j) hj0) one_ne_zero

lemma measurable_norm_polySum (m : ℕ) (x : ℝ) :
    Measurable fun α : Fin m → ℝ => ‖polySum m α x‖ := by
  have h : Continuous fun α : Fin m → ℝ => polySum m α x := by
    unfold polySum phase eC
    fun_prop
  exact h.norm.measurable

lemma norm_polySum_le (m : ℕ) (x : ℝ) (α : Fin m → ℝ) : ‖polySum m α x‖ ≤ ⌊x⌋₊ := by
  rw [polySum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun h _ => norm_eC_core (phase m α h)), Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul]
  simp

lemma integrable_of_bound_unitBox {m : ℕ} {G : (Fin m → ℝ) → ℝ} {C : ℝ}
    (hm : Measurable G) (hC : ∀ α, ‖G α‖ ≤ C) : Integrable G (volume.restrict (unitBox m)) := by
  haveI := isFiniteMeasure_restrict_unitBox m
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)

lemma sum_range_add_one_real (m : ℕ) :
    (∑ i ∈ Finset.range m, ((i:ℝ) + 1)) = (m:ℝ) * ((m:ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_fin_cast (k : ℕ) :
    (∑ j : Fin k, (((j:ℕ)+1 : ℕ) : ℝ)) = (k:ℝ) * ((k:ℝ) + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => (((n+1 : ℕ)) : ℝ)) k]
  have h : ∀ n : ℕ, (((n+1 : ℕ)) : ℝ) = (n:ℝ) + 1 := fun n => by push_cast; ring
  simp only [h]
  rw [sum_range_add_one_real]

/-- `H^{-k(k-1)/2}` is a lower bound for `V = ∏_j min (2 H^{-(j+1)}) 1`, for `H ≥ 1`. -/
lemma V_ge (k : ℕ) (hk : 2 ≤ k) {H : ℝ} (hH : 1 ≤ H) :
    H ^ (-((k:ℝ)*((k:ℝ)-1)/2)) ≤
      ∏ j : Fin (k-1), min (2 * (H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))) 1 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hpow : H ^ (-((k:ℝ)*((k:ℝ)-1)/2))
      = ∏ j : Fin (k-1), H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_sum_of_pos hHpos (fun j : Fin (k-1) => -(((j:ℕ)+1 : ℕ) : ℝ)) Finset.univ]
    congr 1
    rw [Finset.sum_neg_distrib, sum_fin_cast (k-1)]
    have hk1 : 1 ≤ k := by omega
    have hcast : ((k-1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk1]; norm_num
    rw [hcast]; ring
  rw [hpow]
  refine Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (le_of_lt hHpos) _) (fun j _ => ?_)
  have h1 : H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) := by
    have := Real.rpow_pos_of_pos hHpos (-(((j:ℕ)+1 : ℕ) : ℝ))
    linarith
  have h2 : H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) ≤ 1 := by
    have h1' : (1:ℝ) ≤ H ^ (((j:ℕ)+1 : ℕ) : ℝ) := Real.one_le_rpow hH (by positivity)
    rw [Real.rpow_neg (le_of_lt hHpos)]
    calc (H ^ (((j:ℕ)+1 : ℕ) : ℝ))⁻¹ ≤ (1:ℝ)⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hHpos _) zero_lt_one).mpr h1'
      _ = 1 := by rw [inv_one]
  exact le_min h1 h2

/-- `1 + 2πk² ≤ exp(k³)` for `k ≥ 2`. -/
lemma one_add_two_pi_mul_sq_le_exp_cube (k : ℕ) (hk : 2 ≤ k) :
    1 + 2 * Real.pi * (k:ℝ)^2 ≤ Real.exp ((k:ℝ)^3) := by
  have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hthree : 3 * k ≤ k^3 := by
    have h1 : 3 ≤ k^2 := by nlinarith
    calc 3 * k ≤ k^2 * k := Nat.mul_le_mul_right k h1
      _ = k^3 := by ring
  have h1 : (1:ℝ) + 2 * Real.pi * (k:ℝ)^2 ≤ 1 + 8 * (k:ℝ)^2 := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith [Real.pi_pos, sq_nonneg (k:ℝ)]
  have h2 : (1:ℝ) + 8 * (k:ℝ)^2 ≤ 8^k := by
    have hbase : (1:ℝ) + 8 * (2:ℝ)^2 ≤ 8^2 := by norm_num
    have key : ∀ m : ℕ, 2 ≤ m → (1:ℝ) + 8 * (m:ℝ)^2 ≤ 8^m := by
      intro m hm
      induction m with
      | zero => omega
      | succ j ih =>
          rcases le_or_gt 2 j with hj | hj
          · have ihj := ih hj
            have hj2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
            have haux : (16 * (j:ℝ) + 1) ≤ 56 * (j:ℝ)^2 := by
              nlinarith [sq_nonneg ((j:ℝ) - 1), hj2]
            have hgoal : (1:ℝ) + 8 * ((j:ℝ) + 1)^2 ≤ 8 * (1 + 8 * (j:ℝ)^2) := by
              nlinarith [haux]
            calc (1:ℝ) + 8 * (↑(j+1))^2 = 1 + 8 * ((↑j : ℝ) + 1)^2 := by push_cast; ring
              _ ≤ 8 * (1 + 8 * (↑j)^2) := hgoal
              _ ≤ 8 * (8:ℝ)^j := mul_le_mul_of_nonneg_left ihj (by norm_num)
              _ = (8:ℝ)^(j+1) := by rw [pow_succ]; ring
          · have hj1 : j = 1 := by omega
            subst hj1
            norm_num
    exact key k hk
  have h3 : (8:ℝ)^k = 2^(3*k) := by rw [show (8:ℝ) = 2^3 by norm_num, ← pow_mul]
  have h4 : (2:ℝ)^(3*k) ≤ 2^(k^3) :=
    pow_le_pow_right₀ (by norm_num) hthree
  have h5 : (2:ℝ)^(k^3) ≤ Real.exp 1 ^ (k^3) :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le (k^3)
  have h6 : Real.exp 1 ^ (k^3) = Real.exp ((k:ℝ)^3) := by
    rw [← Real.exp_nat_mul, mul_one, Nat.cast_pow]
  rw [← h6]
  calc 1 + 2 * Real.pi * (k:ℝ)^2 ≤ 1 + 8 * (k:ℝ)^2 := h1
    _ ≤ 8^k := h2
    _ = 2^(3*k) := h3
    _ ≤ 2^(k^3) := h4
    _ ≤ Real.exp 1 ^ (k^3) := h5

/-- `V⁻¹ (V 𝒩)^a ((P) V)^b = 𝒩^a P^b V^{-a}` for `a = 1/(2s)`, `b = 1 - 1/s`. -/
lemma rpow_combine {V Nn Pp : ℝ} (hV : 0 < V) (hNn : 0 ≤ Nn) (hPp : 0 ≤ Pp)
    {s : ℕ} (hs : 1 ≤ s) :
    V⁻¹ * ((V * Nn) ^ (1/(2*(s:ℝ))) * (Pp * V) ^ (1 - 1/(s:ℝ)))
      = Nn ^ (1/(2*(s:ℝ))) * Pp ^ (1 - 1/(s:ℝ)) * V ^ (-(1/(2*(s:ℝ)))) := by
  have hsR : (0:ℝ) < (s:ℝ) := by positivity
  have hVexp : V⁻¹ * (V ^ (1/(2*(s:ℝ))) * V ^ (1 - 1/(s:ℝ))) = V ^ (-(1/(2*(s:ℝ)))) := by
    rw [← Real.rpow_neg_one V, ← Real.rpow_add hV, ← Real.rpow_add hV]
    congr 1
    field_simp
    ring
  calc V⁻¹ * ((V * Nn) ^ (1/(2*(s:ℝ))) * (Pp * V) ^ (1 - 1/(s:ℝ)))
      = (Nn ^ (1/(2*(s:ℝ))) * Pp ^ (1 - 1/(s:ℝ))) *
          (V⁻¹ * (V ^ (1/(2*(s:ℝ))) * V ^ (1 - 1/(s:ℝ)))) := by
        rw [Real.mul_rpow (le_of_lt hV) hNn, Real.mul_rpow hPp (le_of_lt hV)]; ring
    _ = (Nn ^ (1/(2*(s:ℝ))) * Pp ^ (1 - 1/(s:ℝ))) * V ^ (-(1/(2*(s:ℝ)))) := by rw [hVexp]
    _ = Nn ^ (1/(2*(s:ℝ))) * Pp ^ (1 - 1/(s:ℝ)) * V ^ (-(1/(2*(s:ℝ)))) := by ring

/-- **Core Weyl-type mean-value bound with a `k`-explicit constant.** -/
theorem core_sum_bound_uniform :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (k : ℕ), 2 ≤ k → ∀ (N : ℕ) (f : ℝ → ℝ) (H M : ℝ) (s : ℕ),
      ⌊H⌋₊ < N → 1 ≤ s → 1 ≤ H →
      (∀ x : ℝ, 0 ≤ x → x ≤ H →
        (∫ α in unitBox (k-1), ‖polySum (k-1) α x‖ ^ (2*(s:ℝ))) ≤ M) →
      (∀ y : ℝ, 0 ≤ y → y ≤ ⌊H⌋₊ →
        (∑ n ∈ Finset.Icc 1 (N - ⌊H⌋₊),
          ‖polySum (k-1) (fun j : Fin (k-1) => iteratedDeriv ((j:ℕ)+1) f (n:ℝ)
            / (Nat.factorial ((j:ℕ)+1) : ℝ)) y‖)
          ≤ Real.exp (C₀ * (k:ℝ)^3) * (((N - ⌊H⌋₊ : ℕ) : ℝ) ^ (1 - 1/(s:ℝ)))
            * (((Nset k (N - ⌊H⌋₊) f H).ncard : ℝ) ^ (1/(2*(s:ℝ))))
            * H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) * M ^ (1/(2*(s:ℝ)))) := by
  refine ⟨1, le_refl 1, ?_⟩
  intro k hk N f H M s hLN hs hH1 hM
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hk1 : 1 ≤ k := by omega
  set L : ℕ := ⌊H⌋₊ with hLdef
  have hLle : L ≤ N := le_of_lt hLN
  set P : ℕ := N - L with hPdef
  set δ : Fin (k-1) → ℝ := fun j => H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) with hδdef
  have hδnn : ∀ j, 0 ≤ δ j := fun j => by rw [hδdef]; exact Real.rpow_nonneg (le_of_lt hHpos) _
  have hδpos : ∀ j, 0 < δ j := fun j => by rw [hδdef]; exact Real.rpow_pos_of_pos hHpos _
  set aa : Fin P → (Fin (k-1) → ℝ) := fun i j =>
      iteratedDeriv ((j:ℕ)+1) f ((((i:ℕ)+1 : ℕ)) : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
    with haadef
  set V : ℝ := ∏ j : Fin (k-1), min (2 * δ j) 1 with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    exact Finset.prod_pos fun j _ => lt_min (by linarith [hδpos j]) one_pos
  have hVnn : 0 ≤ V := le_of_lt hVpos
  set c : ℝ := 2 * Real.pi * (k:ℝ)^2 * H⁻¹ with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  set ν : (Fin (k-1) → ℝ) → ℝ :=
    fun α => ∑ i : Fin P, ∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j) with hνdef
  have hνm : Measurable ν := by
    rw [hνdef]
    exact Finset.measurable_sum Finset.univ fun i _ => measurable_prod_arcInd (k-1) (aa i) δ
  have hνnn : ∀ α, 0 ≤ ν α := fun α => by
    rw [hνdef]
    exact Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => arcInd_nonneg' _ _ _
  have hνle : ∀ α, ν α ≤ (P:ℝ) := fun α => by
    rw [hνdef]
    refine (Finset.sum_le_sum fun i _ => (prod_arcInd_mem_Icc (k-1) (aa i) δ α).2).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  intro y hy0 hyL
  rw [hLdef] at hyL
  have hyH : y ≤ H := le_trans hyL (Nat.floor_le (le_of_lt hHpos))
  have hyfloor : (⌊y⌋₊ : ℝ) ≤ H := by
    have h1 : ⌊y⌋₊ ≤ ⌊H⌋₊ := by
      have hh := Nat.floor_mono hyL
      rwa [Nat.floor_natCast] at hh
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (le_of_lt hHpos))
  have hMnn : 0 ≤ M := by
    have h0 := hM 0 le_rfl (by linarith)
    have hz : (0:ℝ) ≤ (∫ α in unitBox (k-1), ‖polySum (k-1) α 0‖ ^ (2*(s:ℝ))) :=
      integral_nonneg fun α => Real.rpow_nonneg (norm_nonneg _) _
    linarith
  -- abbreviations for the two sides of the Hölder bound
  set NN : ℝ := ((Nset k P f H).ncard : ℝ) with hNndef
  have hNNnn : 0 ≤ NN := by rw [hNndef]; exact Nat.cast_nonneg _
  set EE : ℝ := M ^ (1/(2*(s:ℝ))) * (V * NN) ^ (1/(2*(s:ℝ))) * ((P:ℝ) * V) ^ (1 - 1/(s:ℝ))
    with hEEdef
  have hEEnn : 0 ≤ EE := by
    rw [hEEdef]
    positivity
  set Gfun : (Fin (k-1) → ℝ) → ℝ :=
    fun α => ‖polySum (k-1) α y‖ + c * ∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖
    with hGdef
  -- reindex the sum over `Icc 1 P` as a sum over `Fin P`
  have hLHS : (∑ n ∈ Finset.Icc 1 P, ‖polySum (k-1)
        (fun j : Fin (k-1) => iteratedDeriv ((j:ℕ)+1) f (n:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)) y‖)
      = ∑ i : Fin P, ‖polySum (k-1) (aa i) y‖ := by
    have hIcc : Finset.Icc 1 P = (Finset.range P).image (fun n => n + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hn; exact ⟨n - 1, by omega, by omega⟩
      · rintro ⟨m, hm, rfl⟩; omega
    rw [hIcc, Finset.sum_image (fun x hx y hy hxy => by omega)]
    rw [sum_range (fun m => ‖polySum (k-1)
        (fun j : Fin (k-1) => iteratedDeriv ((j:ℕ)+1) f ((m+1 : ℕ):ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)) y‖)]
  rw [hLHS]
  -- ## Step 1: the pointwise Abel comparison, summed over `i`
  have hpoint : ∀ α : Fin (k-1) → ℝ,
      (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖ * ∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j))
        ≤ Gfun α * ν α := by
    intro α
    rw [hGdef, hνdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hQ : (∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j)) = 1
    · have hall := (prod_arcInd_eq_one_iff (k-1) (aa i) δ α).mp hQ
      have hclose : ∀ j : Fin (k-1), ∃ z : ℤ, |α j - aa i j - z| ≤ H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)) := by
        intro j
        have h1 := (arcInd_eq_one_iff (aa i j) (δ j) (α j)).mp (hall j)
        simpa [hδdef] using h1
      have hab := Work.BMF.VU.polysum_abel_compare_v2 k hk hHpos hyL hclose
      rw [hQ]
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hab (by norm_num : (0:ℝ) ≤ 1)
    · have hQ0 : (∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j)) = 0 :=
        (prod_eq_zero_or_one_of_forall Finset.univ _
          (fun j _ => arcInd_eq_zero_or_one _ _ _)).resolve_right hQ
      rw [hQ0, mul_zero, mul_zero]
  -- ## Step 2: integrate; `V * Σ_i ‖·‖` becomes an integral against `ν`
  have hint_poly : ∀ x : ℝ, Integrable (fun α : Fin (k-1) → ℝ => ‖polySum (k-1) α x‖ * ν α)
      (volume.restrict (unitBox (k-1))) := by
    intro x
    refine integrable_of_bound_unitBox (C := (⌊x⌋₊ : ℝ) * (P:ℝ)) ?_ ?_
    · exact (measurable_norm_polySum (k-1) x).mul hνm
    · intro α
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hνnn α))]
      exact mul_le_mul (norm_polySum_le (k-1) x α) (hνle α) (hνnn α) (Nat.cast_nonneg _)
  have hbox_i : ∀ i : Fin P, V = ∫ α in unitBox (k-1),
      ∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j) := by
    intro i
    rw [hVdef, box_product_arcInd_integral (k-1) (aa i) δ hδnn]
  have hVeq : V * (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖)
      = ∫ α in unitBox (k-1), ∑ i : Fin P, (‖polySum (k-1) (aa i) y‖ *
          ∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j)) := by
    rw [Finset.mul_sum]
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (f := fun i (α : Fin (k-1) → ℝ) => ‖polySum (k-1) (aa i) y‖ *
          ∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j))]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hbox_i i, MeasureTheory.integral_const_mul, mul_comm]
    · intro i _
      refine integrable_of_bound_unitBox (C := (⌊y⌋₊ : ℝ)) ?_ ?_
      · exact (measurable_prod_arcInd (k-1) (aa i) δ).const_mul _
      · intro α
        have hb := prod_arcInd_mem_Icc (k-1) (aa i) δ α
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hb.1)]
        exact le_trans (mul_le_mul_of_nonneg_left hb.2 (norm_nonneg _))
          (le_trans (le_of_eq (mul_one _)) (norm_polySum_le (k-1) y (aa i)))
  have hInt1 : V * (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖)
      ≤ ∫ α in unitBox (k-1), Gfun α * ν α := by
    rw [hVeq]
    refine integral_mono ?_ ?_ (fun α => hpoint α)
    · refine integrable_of_bound_unitBox (C := (P:ℝ) * (⌊y⌋₊ : ℝ)) ?_ ?_
      · exact Finset.measurable_sum Finset.univ fun i _ =>
          measurable_const.mul (measurable_prod_arcInd (k-1) (aa i) δ)
      · intro α
        have hb : ∀ i : Fin P, ‖polySum (k-1) (aa i) y‖ *
            (∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j)) ≤ (⌊y⌋₊ : ℝ) := by
          intro i
          have hb2 := prod_arcInd_mem_Icc (k-1) (aa i) δ α
          exact le_trans (mul_le_mul_of_nonneg_left hb2.2 (norm_nonneg _))
            (le_trans (le_of_eq (mul_one _)) (norm_polySum_le (k-1) y (aa i)))
        have hnn : ∀ i ∈ Finset.univ, (0:ℝ) ≤ ‖polySum (k-1) (aa i) y‖ *
            (∏ j : Fin (k-1), arcInd (aa i j) (δ j) (α j)) := fun i _ =>
          mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ => arcInd_nonneg' _ _ _)
        rw [Real.norm_of_nonneg (Finset.sum_nonneg hnn)]
        exact le_trans (Finset.sum_le_sum fun i _ => hb i)
          (le_of_eq (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
    · refine integrable_of_bound_unitBox
        (C := ((⌊y⌋₊ : ℝ) + c * ((⌊y⌋₊ : ℝ) * ⌊y⌋₊)) * (P:ℝ)) ?_ ?_
      · exact ((measurable_norm_polySum (k-1) y).add
          (measurable_const.mul (Finset.measurable_sum (Finset.range ⌊y⌋₊) fun h _ =>
            measurable_norm_polySum (k-1) (h:ℝ)))).mul hνm
      · intro α
        have h1 : ‖polySum (k-1) α y‖ ≤ (⌊y⌋₊ : ℝ) := norm_polySum_le (k-1) y α
        have h2 : (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖) ≤ (⌊y⌋₊:ℝ) * ⌊y⌋₊ := by
          refine le_trans (Finset.sum_le_sum fun h hh => ?_)
            (le_of_eq (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
          rw [Finset.mem_range] at hh
          have h3 : (⌊((h:ℕ):ℝ)⌋₊ : ℝ) = (h:ℝ) := by simp
          exact le_trans (norm_polySum_le (k-1) (h:ℝ) α)
            (le_trans (le_of_eq h3) (by exact_mod_cast (le_of_lt hh)))
        have hgnn : 0 ≤ Gfun α := by
          rw [hGdef]
          exact add_nonneg (norm_nonneg _) (mul_nonneg hcnn (Finset.sum_nonneg fun h _ => norm_nonneg _))
        rw [hGdef, Real.norm_of_nonneg (mul_nonneg hgnn (hνnn α))]
        exact mul_le_mul (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hcnn)) (hνle α) (hνnn α)
          (by positivity)
  -- ## Step 3: the Hölder bound
  have hIν : (∫ α in unitBox (k-1), ν α) = (P:ℝ) * V := by
    rw [hνdef, hVdef]
    exact integral_nu_eq_fin (k-1) P δ hδnn aa
  have hIν2 : (∫ α in unitBox (k-1), ν α ^ 2) ≤ V * NN := by
    rw [hNndef]
    have h := integral_nu_sq_le_fin (k-1) P δ hδnn aa
    rw [hνdef, hVdef]
    refine h.trans ?_
    have hfilter : (Finset.univ.filter (fun p : Fin P × Fin P => ∀ j : Fin (k-1), ∃ z : ℤ,
          |aa p.1 j - aa p.2 j - z| ≤ 2 * δ j))
        = (Finset.univ.filter (fun p : Fin P × Fin P => ∀ j : Fin (k-1), ∃ z : ℤ,
          |iteratedDeriv ((j:ℕ)+1) f ((p.1:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
           - iteratedDeriv ((j:ℕ)+1) f ((p.2:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
            ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))) := by
      apply Finset.filter_congr
      intro p _
      simp only [haadef, hδdef, Nat.cast_add, Nat.cast_one]
    have hcard : ((Finset.univ.filter (fun p : Fin P × Fin P => ∀ j : Fin (k-1), ∃ z : ℤ,
          |aa p.1 j - aa p.2 j - z| ≤ 2 * δ j)).card : ℝ)
        ≤ ((Nset k P f H).ncard : ℝ) := by
      rw [hfilter]
      exact Work.BMF.VU.nset_count_bridge k P hk f H
    exact mul_le_mul_of_nonneg_left hcard
      (Finset.prod_nonneg fun j _ => le_min (by linarith [hδnn j]) zero_le_one)
  have hholder : ∀ x : ℝ, 0 ≤ x → x ≤ H →
      (∫ α in unitBox (k-1), ‖polySum (k-1) α x‖ * ν α) ≤ EE := by
    intro x hx0 hxH
    have hbox := holder_box (k-1) s hs (U := fun α => ‖polySum (k-1) α x‖) (V := ν)
      (fun α => norm_nonneg _) hνnn (measurable_norm_polySum (k-1) x) hνm
      (fun α => norm_polySum_le (k-1) x α) hνle
    rw [hIν] at hbox
    rw [hEEdef]
    refine hbox.trans ?_
    have hA : (∫ α in unitBox (k-1), ‖polySum (k-1) α x‖ ^ (2 * (s:ℝ))) ^ (1/(2*(s:ℝ)))
        ≤ M ^ (1/(2*(s:ℝ))) :=
      Real.rpow_le_rpow (integral_nonneg fun α => Real.rpow_nonneg (norm_nonneg _) _)
        (hM x hx0 hxH) (by positivity : (0:ℝ) ≤ 1/(2*(s:ℝ)))
    have hB : (∫ α in unitBox (k-1), ν α ^ 2) ^ (1/(2*(s:ℝ)))
        ≤ (V * NN) ^ (1/(2*(s:ℝ))) :=
      Real.rpow_le_rpow (integral_nonneg fun α => pow_nonneg (hνnn α) 2) hIν2
        (by positivity : (0:ℝ) ≤ 1/(2*(s:ℝ)))
    have h1 := mul_le_mul hA hB
      (Real.rpow_nonneg (integral_nonneg fun α => pow_nonneg (hνnn α) 2) _)
      (Real.rpow_nonneg hMnn _)
    exact mul_le_mul_of_nonneg_right h1
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hVnn) _)
  -- ## Step 4: the linearity of the integral and the `⌊y⌋₊`-fold sum
  have hGm : Measurable Gfun := by
    rw [hGdef]
    exact (measurable_norm_polySum (k-1) y).add (measurable_const.mul
      (Finset.measurable_sum (Finset.range ⌊y⌋₊) fun h _ => measurable_norm_polySum (k-1) (h:ℝ)))
  have hsecond_int : Integrable (fun α : Fin (k-1) → ℝ => (c *
      (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖)) * ν α)
      (volume.restrict (unitBox (k-1))) := by
    refine integrable_of_bound_unitBox (C := c * ((⌊y⌋₊:ℝ) * ⌊y⌋₊) * (P:ℝ)) ?_ ?_
    · exact (measurable_const.mul (Finset.measurable_sum (Finset.range ⌊y⌋₊) fun h _ =>
        measurable_norm_polySum (k-1) (h:ℝ))).mul hνm
    · intro α
      have h2 : (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖) ≤ (⌊y⌋₊:ℝ) * ⌊y⌋₊ := by
        refine le_trans (Finset.sum_le_sum fun h hh => ?_)
          (le_of_eq (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
        rw [Finset.mem_range] at hh
        have h3 : (⌊((h:ℕ):ℝ)⌋₊ : ℝ) = (h:ℝ) := by simp
        exact le_trans (norm_polySum_le (k-1) (h:ℝ) α)
          (le_trans (le_of_eq h3) (by exact_mod_cast (le_of_lt hh)))
      have hnn : 0 ≤ (c * (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖)) * ν α :=
        mul_nonneg (mul_nonneg hcnn (Finset.sum_nonneg fun h _ => norm_nonneg _)) (hνnn α)
      rw [Real.norm_of_nonneg hnn]
      exact le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h2 hcnn) (hνle α) (hνnn α) (by positivity))
        (le_of_eq (by ring))
  have hstep : (∫ α in unitBox (k-1), (c * (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖)) * ν α)
      = c * ∑ h ∈ Finset.range ⌊y⌋₊, (∫ α in unitBox (k-1), ‖polySum (k-1) α (h:ℝ)‖ * ν α) := by
    rw [show (∫ α in unitBox (k-1), (c * (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖)) * ν α)
        = ∫ α in unitBox (k-1), c * ((∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖) * ν α) from
      setIntegral_congr_fun (measurableSet_unitBox (k-1)) (fun α _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ α in unitBox (k-1), (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖) * ν α)
        = ∫ α in unitBox (k-1), ∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖ * ν α from
      setIntegral_congr_fun (measurableSet_unitBox (k-1)) (fun α _ => by rw [Finset.sum_mul])]
    exact MeasureTheory.integral_finsetSum (s := Finset.range ⌊y⌋₊)
      (f := fun h (α : Fin (k-1) → ℝ) => ‖polySum (k-1) α (h:ℝ)‖ * ν α)
      (fun h _ => hint_poly (h:ℝ))
  have hlin : (∫ α in unitBox (k-1), Gfun α * ν α)
      = (∫ α in unitBox (k-1), ‖polySum (k-1) α y‖ * ν α)
        + c * ∑ h ∈ Finset.range ⌊y⌋₊, (∫ α in unitBox (k-1), ‖polySum (k-1) α (h:ℝ)‖ * ν α) := by
    rw [hGdef]
    rw [show (∫ α in unitBox (k-1), (‖polySum (k-1) α y‖ + c *
          ∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖) * ν α)
        = ∫ α in unitBox (k-1), (‖polySum (k-1) α y‖ * ν α +
            (c * (∑ h ∈ Finset.range ⌊y⌋₊, ‖polySum (k-1) α (h:ℝ)‖)) * ν α) from
      setIntegral_congr_fun (measurableSet_unitBox (k-1)) (fun α _ => by ring)]
    rw [MeasureTheory.integral_add (hint_poly y) hsecond_int, hstep]
  have hInt2 : (∫ α in unitBox (k-1), Gfun α * ν α) ≤ (1 + c * (⌊y⌋₊ : ℝ)) * EE := by
    rw [hlin]
    have h1 : (∫ α in unitBox (k-1), ‖polySum (k-1) α y‖ * ν α) ≤ EE := hholder y hy0 hyH
    have h2 : (∑ h ∈ Finset.range ⌊y⌋₊, (∫ α in unitBox (k-1), ‖polySum (k-1) α (h:ℝ)‖ * ν α))
        ≤ (⌊y⌋₊ : ℝ) * EE := by
      refine le_trans (Finset.sum_le_sum fun h hh => ?_)
        (le_of_eq (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
      rw [Finset.mem_range] at hh
      refine hholder (h:ℝ) (by positivity) ?_
      exact le_trans (by exact_mod_cast (le_of_lt hh) : ((h:ℕ):ℝ) ≤ (⌊y⌋₊:ℝ)) hyfloor
    exact le_trans (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hcnn))
      (le_of_eq (by ring))
  -- ## Step 5: divide by `V` and finish
  have hmain : V * (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖) ≤ (1 + c * (⌊y⌋₊ : ℝ)) * EE :=
    le_trans hInt1 hInt2
  have hbracket : V⁻¹ * ((1 + c * (⌊y⌋₊ : ℝ)) * EE)
      = (1 + c * (⌊y⌋₊ : ℝ)) * (V⁻¹ * EE) := by ring
  have hSumm : (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖) ≤ (1 + c * (⌊y⌋₊ : ℝ)) * (V⁻¹ * EE) := by
    have h1 : (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖) ≤
        V⁻¹ * ((1 + c * (⌊y⌋₊ : ℝ)) * EE) := by
      have heq : V⁻¹ * (V * (∑ i : Fin P, ‖polySum (k-1) (aa i) y‖))
          = ∑ i : Fin P, ‖polySum (k-1) (aa i) y‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hVpos), one_mul]
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hVnn)
    exact le_trans h1 (le_of_eq hbracket)
  refine hSumm.trans ?_
  have hEEsplit : V⁻¹ * EE = M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
        V ^ (-(1/(2*(s:ℝ)))) := by
    rw [hEEdef]
    calc V⁻¹ * (M ^ (1/(2*(s:ℝ))) * (V * NN) ^ (1/(2*(s:ℝ))) * ((P:ℝ) * V) ^ (1 - 1/(s:ℝ)))
        = M ^ (1/(2*(s:ℝ))) *
            (V⁻¹ * ((V * NN) ^ (1/(2*(s:ℝ))) * ((P:ℝ) * V) ^ (1 - 1/(s:ℝ)))) := by ring
      _ = M ^ (1/(2*(s:ℝ))) * (NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
            V ^ (-(1/(2*(s:ℝ))))) := by
          rw [rpow_combine hVpos hNNnn (Nat.cast_nonneg P) hs]
      _ = M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
            V ^ (-(1/(2*(s:ℝ)))) := by ring
  rw [hEEsplit]
  have hkey1 : 1 + c * (⌊y⌋₊ : ℝ) ≤ Real.exp ((k:ℝ)^3) := by
    have hcy : c * (⌊y⌋₊ : ℝ) ≤ 2 * Real.pi * (k:ℝ)^2 := by
      rw [hcdef]
      have h1 : (⌊y⌋₊ : ℝ) * H⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hHpos]; linarith [hyfloor]
      have h2 : (0:ℝ) ≤ 2 * Real.pi * (k:ℝ)^2 := by positivity
      calc 2 * Real.pi * (k:ℝ)^2 * H⁻¹ * (⌊y⌋₊ : ℝ)
            = 2 * Real.pi * (k:ℝ)^2 * ((⌊y⌋₊ : ℝ) * H⁻¹) := by ring
        _ ≤ 2 * Real.pi * (k:ℝ)^2 * 1 := mul_le_mul_of_nonneg_left h1 h2
        _ = 2 * Real.pi * (k:ℝ)^2 := by ring
    linarith [one_add_two_pi_mul_sq_le_exp_cube k hk]
  have hkey2 : V ^ (-(1/(2*(s:ℝ)))) ≤ H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) := by
    have hVH : H ^ (-((k:ℝ)*((k:ℝ)-1)/2)) ≤ V := by
      rw [hVdef, hδdef]
      exact V_ge k hk hH1
    have hpos : 0 < H ^ (-((k:ℝ)*((k:ℝ)-1)/2)) := Real.rpow_pos_of_pos hHpos _
    have hexp : -(1/(2*(s:ℝ))) ≤ 0 := by
      have : (0:ℝ) < 1/(2*(s:ℝ)) := by positivity
      linarith
    refine le_trans (Real.rpow_le_rpow_of_nonpos hpos hVH hexp) (le_of_eq ?_)
    rw [← Real.rpow_mul (le_of_lt hHpos)]
    congr 1
    field_simp
    ring
  have hrest_nn : 0 ≤ M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
        V ^ (-(1/(2*(s:ℝ)))) := by positivity
  have hinner_nn : 0 ≤ M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
        H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ))) := by positivity
  have hA : (1 + c * (⌊y⌋₊ : ℝ)) *
        (M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
          V ^ (-(1/(2*(s:ℝ)))))
      ≤ Real.exp ((k:ℝ)^3) *
        (M ^ (1/(2*(s:ℝ))) * NN ^ (1/(2*(s:ℝ))) * (P:ℝ) ^ (1 - 1/(s:ℝ)) *
          H ^ ((k:ℝ)*((k:ℝ)-1)/(4*(s:ℝ)))) :=
    mul_le_mul hkey1
      (mul_le_mul_of_nonneg_left hkey2
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hMnn _) (Real.rpow_nonneg hNNnn _))
          (Real.rpow_nonneg (Nat.cast_nonneg P) _)))
      hrest_nn (Real.exp_pos _).le
  refine le_trans hA (le_of_eq ?_)
  rw [one_mul]
  ring

end Work.BMF
