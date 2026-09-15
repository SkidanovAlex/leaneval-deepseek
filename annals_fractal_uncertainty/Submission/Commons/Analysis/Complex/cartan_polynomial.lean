import Mathlib
import Submission.Commons.Analysis.Complex.Cartan.monic_level_set_volume_le
import Submission.Commons.Analysis.Complex.Cartan.cartan_greedy
import Submission.Commons.Analysis.Complex.Cartan.prod_le_prod_of_card_filter_lt

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.Analysis.Complex

open Cartan

/-- **Cartan's lemma, disks form.** For `n` points `a : Fin n → ℂ` and a scale `ρ > 0`, there are
disks with total radius at most `2 ρ n` outside of which `∏ i, ‖z - a i‖ ≥ ρ^n · n!`. -/
theorem cartan_points (n : ℕ) (a : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (s : Finset ℂ) (r : ℂ → ℝ),
      (∀ z ∈ s, 0 < r z) ∧
      (∑ z ∈ s, r z ≤ 2 * ρ * n) ∧
      ∀ z : ℂ, (∀ w ∈ s, r w ≤ ‖z - w‖) →
        ρ ^ n * (Nat.factorial n : ℝ) ≤ ‖∏ i, (z - a i)‖ := by
  obtain ⟨J, c, lam, cl, hlam, hcl, hdist, hcard, hsum, hkey⟩ := cartan_greedy n a ρ hρ
  classical
  refine ⟨J.image c, fun w => ∑ j ∈ J.filter (fun j => c j = w), 2 * (lam j : ℝ) * ρ,
    ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨j0, hj0J, rfl⟩ := hw
    have hmem : j0 ∈ J.filter (fun j => c j = c j0) := Finset.mem_filter.mpr ⟨hj0J, rfl⟩
    have hnonneg : ∀ j ∈ J.filter (fun j => c j = c j0), 0 ≤ 2 * (lam j : ℝ) * ρ := by
      intro j hj
      have := hlam j (Finset.mem_filter.mp hj).1
      positivity
    have hpos : 0 < 2 * (lam j0 : ℝ) * ρ := by
      have := hlam j0 hj0J
      have : (1 : ℝ) ≤ (lam j0 : ℝ) := by exact_mod_cast this
      positivity
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hmem)
  · have hfib := Finset.sum_fiberwise_of_maps_to (s := J) (t := J.image c) (g := c)
        (fun j hj => Finset.mem_image_of_mem c hj) (fun j => 2 * (lam j : ℝ) * ρ)
    change (∑ w ∈ J.image c, ∑ j ∈ J with c j = w, 2 * (lam j : ℝ) * ρ) ≤ 2 * ρ * n
    rw [hfib]
    have h2 : ∑ j ∈ J, 2 * ((lam j : ℕ) : ℝ) * ρ = 2 * ρ * ∑ j ∈ J, ((lam j : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h2]
    have hcast : ((∑ j ∈ J, lam j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsum
    have hsumcast : (∑ j ∈ J, ((lam j : ℕ) : ℝ)) = ((∑ j ∈ J, lam j : ℕ) : ℝ) := by
      push_cast; rfl
    rw [hsumcast]
    nlinarith [hcast, hρ]
  · intro z hz
    have hcount : ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (Finset.univ.filter (fun i : Fin n => ‖z - a i‖ < (k : ℝ) * ρ)).card ≤ k - 1 := by
      intro k hk1 hkn
      by_contra hcon
      rw [not_le] at hcon
      have hkcard : k ≤ (Finset.univ.filter (fun i : Fin n => ‖z - a i‖ < (k : ℝ) * ρ)).card := by
        omega
      obtain ⟨i, hi, hlami⟩ := hkey k z hk1 hkn hkcard
      set j := cl i with hjdef
      have hjJ : j ∈ J := hcl i
      have hcw : c j ∈ J.image c := Finset.mem_image_of_mem c hjJ
      have hterm : 2 * (lam j : ℝ) * ρ ≤
          ∑ j' ∈ J.filter (fun j' => c j' = c j), 2 * (lam j' : ℝ) * ρ := by
        refine Finset.single_le_sum (f := fun j' => 2 * (lam j' : ℝ) * ρ) ?_ ?_
        · intro j' hj'
          have := hlam j' (Finset.mem_filter.mp hj').1
          positivity
        · exact Finset.mem_filter.mpr ⟨hjJ, rfl⟩
      have hrz : (∑ j' ∈ J.filter (fun j' => c j' = c j), 2 * (lam j' : ℝ) * ρ) ≤ ‖z - c j‖ :=
        hz (c j) hcw
      have hdisti : ‖c j - a i‖ < (lam j : ℝ) * ρ := by
        have := hdist i
        rw [← hjdef] at this
        exact this
      have htri : ‖z - c j‖ ≤ ‖z - a i‖ + ‖c j - a i‖ := by
        have h1 : ‖z - c j‖ ≤ ‖z - a i‖ + ‖a i - c j‖ := by
          have := norm_add_le (z - a i) (a i - c j)
          rwa [show (z - a i) + (a i - c j) = z - c j by ring] at this
        rwa [norm_sub_rev (a i) (c j)] at h1
      have hkR : ((k : ℕ) : ℝ) ≤ (lam j : ℝ) := by exact_mod_cast hlami
      have hkey2 : (2 : ℝ) * (lam j : ℝ) * ρ < ((k : ℝ) + (lam j : ℝ)) * ρ := by
        nlinarith [hterm, hrz, htri, hi, hdisti]
      have hlt : (lam j : ℝ) < (k : ℝ) := by nlinarith [hkey2, hρ]
      linarith [hkR, hlt]
    have hrearr := prod_le_prod_of_card_filter_lt (Finset.univ : Finset (Fin n))
        (fun i => ‖z - a i‖) (fun k => if k = 0 then 1 else (k : ℝ) * ρ)
        (fun i => norm_nonneg _)
        (fun k => by
          rcases eq_or_ne k 0 with hk | hk
          · subst hk; norm_num
          · rw [if_neg hk]; positivity)
        (fun k hk1 hkn => by
          rw [if_neg (by omega : k ≠ 0)]
          have hkn' : k ≤ n := by simpa [Finset.card_univ] using hkn
          exact hcount k hk1 hkn')
    have hL : ∏ k ∈ Finset.Icc 1 n, (if k = 0 then 1 else (k : ℝ) * ρ)
        = (Nat.factorial n : ℝ) * ρ ^ n := by
      have hcongr : ∀ k ∈ Finset.Icc 1 n, (if k = 0 then 1 else (k : ℝ) * ρ) = (k : ℝ) * ρ := by
        intro k hk
        rw [if_neg (by have := (Finset.mem_Icc.mp hk).1; omega)]
      rw [Finset.prod_congr rfl hcongr,
        Finset.prod_mul_distrib, Finset.prod_const]
      have hfac : ∏ k ∈ Finset.Icc 1 n, (k : ℝ) = (Nat.factorial n : ℝ) := by
        rw [← Nat.cast_prod]
        congr 1
        rw [← Finset.Ico_add_one_right_eq_Icc 1 n, Finset.prod_Ico_id_eq_factorial]
      rw [hfac]
      have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
      rw [hcard]
    rw [Finset.card_univ, Fintype.card_fin] at hrearr
    rw [hL] at hrearr
    have hR : ∏ i ∈ (Finset.univ : Finset (Fin n)), ‖z - a i‖ = ‖∏ i, (z - a i)‖ :=
      (norm_prod Finset.univ (fun i => z - a i)).symm
    rw [hR] at hrearr
    rw [mul_comm (ρ ^ n) (Nat.factorial n : ℝ)]
    exact hrearr

/-- For a monic complex polynomial, `p.eval z` is the product of `z - a` over the roots. -/
lemma prod_univ_eval (p : Polynomial ℂ) (hp : p.Monic) (z : ℂ) :
    ∏ i : Fin p.roots.toList.length, (z - p.roots.toList.get i) = p.eval z := by
  have hsplit : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hp_prod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hsplit
  have hstep : Multiset.map p.roots.toList.get
      (Finset.univ : Finset (Fin p.roots.toList.length)).val = p.roots := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h1 : ∏ i : Fin p.roots.toList.length, (z - p.roots.toList.get i)
      = (Multiset.map (fun a => z - a) p.roots).prod := by
    rw [Finset.prod_eq_multiset_prod]
    congr 1
    rw [show Multiset.map (fun i : Fin p.roots.toList.length => z - p.roots.toList.get i)
          Finset.univ.val
        = Multiset.map ((fun a => z - a) ∘ p.roots.toList.get) Finset.univ.val from rfl]
    rw [← Multiset.map_map (fun a => z - a) p.roots.toList.get Finset.univ.val, hstep]
  have hpe : p.eval z = (Multiset.map (fun a => z - a) p.roots).prod := by
    conv_lhs => rw [← hp_prod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [Polynomial.eval_sub]
  rw [h1, hpe]

theorem cartan_polynomial (p : Polynomial ℂ) (hp : p.Monic)
    (hroot : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    ∃ (s : Finset ℂ) (r : ℂ → ℝ), (∀ z ∈ s, 0 < r z) ∧ (∑ z ∈ s, r z ≤ 10 * H) ∧
      ∀ z : ℂ, (∀ w ∈ s, r w ≤ ‖z - w‖) →
        (H / Real.exp 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hsplit : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  rcases Nat.eq_zero_or_pos p.roots.toList.length with hlen | hlen
  · have hnd : p.natDegree = 0 := by
      rw [← hsplit, ← Multiset.length_toList]; exact hlen
    have hp1 : p = 1 := hp.natDegree_eq_zero.mp hnd
    refine ⟨∅, fun _ => 0, ?_, ?_, ?_⟩
    · intro z hz; exact absurd hz (Finset.notMem_empty z)
    · rw [Finset.sum_empty]; positivity
    · intro z _
      rw [hnd, hp1]; simp
  · set n : ℕ := p.roots.toList.length with hn_def
    have hnpd : n = p.natDegree := by rw [hn_def, Multiset.length_toList]; exact hsplit
    set ρ : ℝ := 4 * H / n with hρ_def
    have hρ : 0 < ρ := by rw [hρ_def]; positivity
    obtain ⟨s, r, hpos, hsum, hcov⟩ := cartan_points n p.roots.toList.get ρ hρ
    refine ⟨s, r, hpos, ?_, ?_⟩
    · have h3 : ρ * n = 4 * H := by rw [hρ_def]; field_simp
      nlinarith [hsum, h3, hH]
    · intro z hz
      have h1 := hcov z hz
      rw [prod_univ_eval p hp z] at h1
      have h2 : (H / Real.exp 1) ^ p.natDegree ≤ ρ ^ n * (Nat.factorial n : ℝ) := by
        rw [← hnpd]
        have hfac : ((n : ℝ) / 4) ^ n ≤ (Nat.factorial n : ℝ) := factorial_ge_div_pow n
        have hbase : ρ * ((n : ℝ) / 4) = H := by rw [hρ_def]; field_simp
        calc (H / Real.exp 1) ^ n ≤ H ^ n := by
              apply pow_le_pow_left₀ (by positivity)
              exact div_le_self hH.le (Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1))
          _ = (ρ * ((n : ℝ) / 4)) ^ n := by rw [hbase]
          _ = ρ ^ n * ((n : ℝ) / 4) ^ n := by rw [mul_pow]
          _ ≤ ρ ^ n * (Nat.factorial n : ℝ) :=
              mul_le_mul_of_nonneg_left hfac (by positivity)
      linarith [h1, h2]

end Commons.Analysis.Complex
