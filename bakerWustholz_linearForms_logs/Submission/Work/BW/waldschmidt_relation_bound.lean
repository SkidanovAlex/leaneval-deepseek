import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.wsb_helpers
import Submission.Work.BW.minkowski_relation_vector_le
import Submission.Work.BW.wsb_isOfFinOrder_prod_of_deviation
import Submission.Work.BW.orderOf_le_four_mul_finrank_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- Product monotonicity for nonnegative real functions on a finset. -/
theorem wsb_prod_le_prod_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
           (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact mul_le_mul h1 h2 hfs (le_trans hfa h1)

/-! ## The perturbation identity for the log-form -/

/-- If `∑ i, (t i : ℂ) * ℓ i = 0` then for every `s`
`t k * (∑ i, (s i : ℂ) * ℓ i) = ∑_{j ≠ k} ((t k * s j − s k * t j : ℤ) : ℂ) * ℓ j`. -/
theorem theta_perturbation {m : ℕ} (ℓ : Fin m → ℂ) (t s : Fin m → ℤ) (k : Fin m)
    (ht : ∑ i, (t i : ℂ) * ℓ i = 0) :
    (t k : ℂ) * (∑ i, (s i : ℂ) * ℓ i)
      = ∑ j ∈ Finset.univ.erase k, ((t k * s j - s k * t j : ℤ) : ℂ) * ℓ j := by
  have hA : (t k : ℂ) * (∑ i, (s i : ℂ) * ℓ i)
      = ∑ i, ((t k * s i : ℤ) : ℂ) * ℓ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hB : (s k : ℂ) * (∑ i, (t i : ℂ) * ℓ i)
      = ∑ i, ((s k * t i : ℤ) : ℂ) * ℓ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hC : (∑ i, ((t k * s i - s k * t i : ℤ) : ℂ) * ℓ i)
      = (∑ i, ((t k * s i : ℤ) : ℂ) * ℓ i)
        - (∑ i, ((s k * t i : ℤ) : ℂ) * ℓ i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hD : (∑ i, ((t k * s i - s k * t i : ℤ) : ℂ) * ℓ i)
      = ∑ i, ((t k * s i : ℤ) : ℂ) * ℓ i := by
    rw [hC, ← hB, ht, mul_zero, sub_zero]
  rw [hA, ← hD]
  rw [← Finset.sum_erase_add Finset.univ
        (fun i => ((t k * s i - s k * t i : ℤ) : ℂ) * ℓ i) (Finset.mem_univ k)]
  have hk : ((t k * s k - s k * t k : ℤ) : ℂ) * ℓ k = 0 := by
    have : t k * s k - s k * t k = (0:ℤ) := by ring
    rw [this]; simp
  rw [hk, add_zero]

/-- Norm form of `theta_perturbation`: the deviation bounds on `t k * s j - s k * t j` bound
`‖∑ i, (s i : ℂ) * ℓ i‖` by `∑_{j ≠ k} c j * ‖ℓ j‖`. -/
theorem norm_thetaC_le {m : ℕ} (ℓ : Fin m → ℂ) (t s : Fin m → ℤ) (k : Fin m) (c : Fin m → ℝ)
    (ht : ∑ i, (t i : ℂ) * ℓ i = 0) (htk : t k ≠ 0)
    (hdev : ∀ j : Fin m, j ≠ k →
      |((t k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((t j : ℤ) : ℝ)|
        ≤ |((t k : ℤ) : ℝ)| * c j) :
    ‖∑ i, (s i : ℂ) * ℓ i‖ ≤ ∑ j ∈ Finset.univ.erase k, c j * ‖ℓ j‖ := by
  have h1 := theta_perturbation ℓ t s k ht
  have htkn : (0:ℝ) < |((t k : ℤ) : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero]; exact htk
  have hstep : |((t k : ℤ) : ℝ)| * ‖∑ i, (s i : ℂ) * ℓ i‖
      = ‖((t k : ℤ) : ℂ) * (∑ i, (s i : ℂ) * ℓ i)‖ := by
    rw [norm_mul, Complex.norm_intCast]
  have hbound : |((t k : ℤ) : ℝ)| * ‖∑ i, (s i : ℂ) * ℓ i‖
      ≤ |((t k : ℤ) : ℝ)| * ∑ j ∈ Finset.univ.erase k, c j * ‖ℓ j‖ := by
    rw [hstep, h1]
    calc ‖∑ j ∈ Finset.univ.erase k, ((t k * s j - s k * t j : ℤ) : ℂ) * ℓ j‖
        ≤ ∑ j ∈ Finset.univ.erase k, ‖((t k * s j - s k * t j : ℤ) : ℂ) * ℓ j‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase k, |(((t k * s j - s k * t j : ℤ)) : ℝ)| * ‖ℓ j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_intCast]
      _ ≤ ∑ j ∈ Finset.univ.erase k, |((t k : ℤ) : ℝ)| * (c j * ‖ℓ j‖) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
          have hc_nn : 0 ≤ c j :=
            (mul_nonneg_iff_of_pos_left htkn).mp (le_trans (abs_nonneg _) (hdev j hjne))
          have h3 : |(((t k * s j - s k * t j : ℤ)) : ℝ)| ≤ |((t k : ℤ) : ℝ)| * c j := by
            have h := hdev j hjne
            push_cast
            exact h
          calc |(((t k * s j - s k * t j : ℤ)) : ℝ)| * ‖ℓ j‖
              ≤ (|((t k : ℤ) : ℝ)| * c j) * ‖ℓ j‖ :=
                mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
            _ = |((t k : ℤ) : ℝ)| * (c j * ‖ℓ j‖) := by ring
      _ = |((t k : ℤ) : ℝ)| * ∑ j ∈ Finset.univ.erase k, c j * ‖ℓ j‖ := by
          rw [Finset.mul_sum]
  exact le_of_mul_le_mul_left hbound htkn

/-! ## Waldschmidt, Acta Arith. 37 (1980), Lemma 4.1

**Setup.**  `d = [K : ℚ]`, `V j = hmod (α j) (ℓ j)`, `θ y = ∑ i, (y i : ℂ) * ℓ i`.
`hmin` makes `R := {y : Fin M → ℤ | θ y = 0}` free of rank one
(`Work.BW.exists_generator_ker_theta`); `hdep` makes it nonzero.

**Step 1 (Minkowski).**  Fix `k`.  With `c i := V`-dependent positive reals satisfying
`∏ i, c i ≥ 1`, `Work.BW.minkowski_relation_vector_le` produces `s ≠ 0` with
`|s k| ≤ c k` and `|t k * s j − s k * t j| ≤ |t k| * c j` (`j ≠ k`).

**Step 2 (p-adic) and Step 3 (archimedean).**  `∏ i, α i ^ (t i) = 1` (from `θ t = 0` and
injectivity of `φ`), so for every finite place `v`
`t k * log (v β) = ∑_{j ≠ k} (t k s j − s k t j) log (v α j)`, and similarly for every embedding;
with `∑_{j ≠ k} c j * logHeight₁ (α j) ≤ 1/(9 d²)` this makes `β := ∏ i, α i ^ (s i)` a unit of
`𝓞 K` (hence integral) whose conjugates all have `|log ‖·‖| ≤ 1/(9 d²)`, so `β` is a root of
unity (`Work.BW.isOfFinOrder_prod_of_deviation`).

**Step 4 (imaginary part).**  `β` has order `q ≤ 4 d²`; the same deviation bounds give
`‖θ s‖ ≤ π/(4 d²)`, so `‖θ s‖ * q ≤ π < 2π` while `q * θ s ∈ 2π i ℤ`; hence `θ s = 0`.

**Step 5.**  `s ∈ R = ℤ * t`, say `s = a * t` with `a ≠ 0`, so `|t k| ≤ |s k| ≤ c k`.
The arithmetical choice `c i := (9 (M-1) d³ V i)⁻¹` (`i ≠ k`) and
`c k := ∏_{j ≠ k} (c j)⁻¹` has `∏ i, c i = 1` and `c k ≤ (9 (M-1) d³)^(M-1) ∏_{j ≠ k} V j`.
-/

/-- **Waldschmidt, Acta Arith. 37 (1980), Lemma 4.1** (per-coordinate form, as printed: the
paper bounds each `|t_k|` separately — "the idea of bounding each `|t_k|` rather than `max |t_k|`
is due to Maurice Mignotte" — with the product `V_1…V_m/V_k` over the *other* logarithms), quoted
by Baker–Wüstholz (Crelle 442 (1993)) §6.  Here `V_j` is the modified height `hmod (α j) (ℓ j)`,
which keeps the `‖ℓ j‖/d` term: without it the statement fails for non-principal branches
(e.g. `K = ℚ`, `m = 2`, `α i = 1`, `ℓ = (2000πi, 1998πi)` has primitive relation `(999,-1000)`),
so the `‖ℓ‖/d` term is part of the statement.  Route: Minkowski's linear forms theorem
(`Work.BW.minkowski_linear_forms`), the ideal factorization `α 𝓞_K = ∏ 𝔭^{e_𝔭}` with
`|e_𝔭| ≤ log |N(α den α)| / log 2`, and the Lehmer/Blanksby–Montgomery bound
(`Work.BW.logHeight_one_gt_of_not_torsion`); see Waldschmidt's proof of Lemma 4.1. -/
theorem waldschmidt_relation_bound {K : Type*} [Field K] [NumberField K] {M : ℕ}
    (φ : K →+* ℂ) (α : Fin M → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin M → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin M // j ≠ i} => ℓ j)) :
    ∃ t : Fin M → ℤ, t ≠ 0 ∧ (∑ i, (t i : ℂ) * ℓ i) = 0 ∧
      ∀ k : Fin M, |((t k : ℤ) : ℝ)| ≤
        (9 * ((M : ℝ) - 1) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (M - 1) *
          ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j) := by
  classical
  rcases Nat.lt_or_ge M 2 with hM | hM
  · interval_cases M
    · -- `M = 0`: `hdep` is false
      exact absurd (by
        rw [linearIndependent_iff']
        intro s g hs i hi
        exact Fin.elim0 i) hdep
    · -- `M = 1`: a single dependent logarithm vanishes
      have hℓ0 : ℓ 0 = 0 := by
        by_contra hne
        apply hdep
        rw [Fintype.linearIndependent_iff]
        intro g hg
        rw [Fintype.sum_unique] at hg
        have hg0 : g 0 = 0 := by
          rcases smul_eq_zero.mp hg with h | h
          · exact h
          · exact absurd h hne
        intro i
        rw [Subsingleton.elim i 0]
        exact hg0
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · intro h
        exact one_ne_zero (congr_fun h 0)
      · rw [Fintype.sum_unique]
        simp [hℓ0]
      · intro k
        have hk : k = 0 := Subsingleton.elim k 0
        subst hk
        have hprod : ∏ j ∈ Finset.univ.erase (0 : Fin 1), hmod (α j) (ℓ j) = 1 :=
          Finset.prod_eq_one fun j hj => absurd (Subsingleton.elim j 0) (Finset.mem_erase.mp hj).1
        rw [hprod, mul_one]
        simp
  · -- main case `M ≥ 2`
    obtain ⟨tgen, htne, htθ, hgen⟩ := wsb_exists_generator_ker ℓ hmin hdep
    have htk : ∀ k : Fin M, tgen k ≠ 0 := fun k => wsb_coords_ne_zero hmin htne htθ k
    have htθ_sum : ∑ i, (tgen i : ℂ) * ℓ i = 0 := htθ
    have hexp_t : Complex.exp (∑ i, (tgen i : ℂ) * ℓ i) = φ (∏ i, α i ^ (tgen i : ℤ)) := by
      rw [Complex.exp_sum, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]
    have ht_one : ∏ i, α i ^ (tgen i : ℤ) = 1 := by
      apply φ.injective
      rw [map_one, ← hexp_t, htθ_sum, Complex.exp_zero]
    refine ⟨tgen, htne, htθ_sum, fun k => ?_⟩
    set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
    have hdpos : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
    have hd1 : (1:ℝ) ≤ d := by rw [hd]; exact_mod_cast Module.finrank_pos
    have hdne : d ≠ 0 := ne_of_gt hdpos
    have hm1R : (0:ℝ) < (M:ℝ) - 1 := by
      have h2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      linarith
    set qmax : ℝ := 4 * d ^ 2 with hqmax
    have hqmaxpos : 0 < qmax := by rw [hqmax]; positivity
    set cinv : Fin M → ℝ := fun j => ((M:ℝ) - 1) *
      max (max (9 * d ^ 2 * Height.logHeight₁ (α j)) (qmax * ‖ℓ j‖ / Real.pi)) 1 with hcinvdef
    set c : Fin M → ℝ := fun j => (cinv j)⁻¹ with hcdef
    set ck : ℝ := ∏ j ∈ Finset.univ.erase k, cinv j with hckdef
    set c' : Fin M → ℝ := Function.update c k ck with hc'def
    have hcinv_pos : ∀ j, 0 < cinv j := by
      intro j
      have h2 : (0:ℝ) < max (max (9 * d ^ 2 * Height.logHeight₁ (α j))
          (qmax * ‖ℓ j‖ / Real.pi)) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      simp only [hcinvdef]
      exact mul_pos hm1R h2
    have hc_pos : ∀ j, 0 < c j := fun j => by
      simp only [hcdef]; exact inv_pos.mpr (hcinv_pos j)
    have hc'_pos : ∀ i, 0 < c' i := by
      intro i
      rw [hc'def]
      by_cases hik : i = k
      · rw [hik, Function.update_self]
        exact Finset.prod_pos fun j _ => hcinv_pos j
      · rw [Function.update_of_ne hik]
        exact hc_pos i
    have hc'_prod : ∏ i, c' i = 1 := by
      rw [hc'def]
      rw [← Finset.prod_erase_mul Finset.univ (Function.update c k ck) (Finset.mem_univ k)]
      have h1 : ∀ i ∈ Finset.univ.erase k, Function.update c k ck i = (cinv i)⁻¹ := by
        intro i hi
        rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      have h2 : Function.update c k ck k = ck := Function.update_self ..
      rw [Finset.prod_congr rfl h1, h2, hckdef, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      exact inv_mul_cancel₀ (ne_of_gt (hcinv_pos j))
    obtain ⟨s, hsne, hsk, hdevraw⟩ :=
      minkowski_relation_vector_le tgen k (htk k) c' hc'_pos (le_of_eq hc'_prod.symm)
    have hdev : ∀ j : Fin M, j ≠ k →
        |((tgen k : ℤ) : ℝ) * (s j : ℝ) - (s k : ℝ) * ((tgen j : ℤ) : ℝ)|
          ≤ |((tgen k : ℤ) : ℝ)| * c j := by
      intro j hj
      have h := hdevraw j hj
      rwa [hc'def, Function.update_of_ne hj] at h
    -- the archimedean bound
    have hterm_arch : ∀ j ∈ Finset.univ.erase k,
        c j * Height.logHeight₁ (α j) ≤ 1 / (((M:ℝ) - 1) * 9 * d ^ 2) := by
      intro j _
      have hge : ((M:ℝ) - 1) * (9 * d ^ 2 * Height.logHeight₁ (α j)) ≤ cinv j := by
        have h := mul_le_mul_of_nonneg_left
          (le_trans (le_max_left (9 * d ^ 2 * Height.logHeight₁ (α j))
            (qmax * ‖ℓ j‖ / Real.pi)) (le_max_left _ 1)) (le_of_lt hm1R)
        simp only [hcinvdef]
        exact h
      have hge' : Height.logHeight₁ (α j) * (((M:ℝ) - 1) * 9 * d ^ 2)
          ≤ cinv j := by
        have heq : ((M:ℝ) - 1) * (9 * d ^ 2 * Height.logHeight₁ (α j))
            = Height.logHeight₁ (α j) * (((M:ℝ) - 1) * 9 * d ^ 2) := by ring
        rw [heq] at hge
        exact hge
      rcases eq_or_lt_of_le (Height.zero_le_logHeight₁ (α j)) with hzero | hpos
      · have : Height.logHeight₁ (α j) = 0 := hzero.symm
        rw [this, mul_zero]
        positivity
      · have hcq : c j * Height.logHeight₁ (α j)
            = Height.logHeight₁ (α j) / cinv j := by
          simp only [hcdef, div_eq_inv_mul]
        rw [hcq]
        rw [div_le_div_iff₀ (hcinv_pos j) (by positivity)]
        linarith [hge']
    have hcard : (Finset.univ.erase k).card = M - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    have hcast : (((M - 1 : ℕ)) : ℝ) = (M:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]
      norm_num
    have harch : (∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j))
        ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by
      calc ∑ j ∈ Finset.univ.erase k, c j * Height.logHeight₁ (α j)
          ≤ ∑ j ∈ Finset.univ.erase k, 1 / (((M:ℝ) - 1) * 9 * d ^ 2) :=
            Finset.sum_le_sum hterm_arch
        _ = ((Finset.univ.erase k).card : ℝ) * (1 / (((M:ℝ) - 1) * 9 * d ^ 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 / (9 * d ^ 2) := by
            rw [hcard, hcast]
            field_simp
        _ = 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by rw [hd]
    have hiso : IsOfFinOrder (∏ i, α i ^ (s i : ℤ)) :=
      wsb_isOfFinOrder_prod_of_deviation φ α hα ℓ hℓ tgen k (htk k) htθ_sum s c hdev harch
    set β : K := ∏ i, α i ^ (s i : ℤ) with hβdef
    have hβexp : Complex.exp (∑ i, (s i : ℂ) * ℓ i) = φ β := by
      rw [hβdef, Complex.exp_sum, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]
    have hqpos : 0 < orderOf β := hiso.orderOf_pos
    have hqle : (orderOf β : ℝ) ≤ qmax := by
      have h := orderOf_le_four_mul_finrank_sq β hiso
      have h' : (orderOf β : ℝ) ≤ 4 * (Module.finrank ℚ K : ℝ) ^ 2 := by
        exact_mod_cast h
      rw [hqmax, hd]
      exact h'
    -- the imaginary-part bound
    have hterm_imag : ∀ j ∈ Finset.univ.erase k,
        c j * ‖ℓ j‖ ≤ Real.pi / (((M:ℝ) - 1) * qmax) := by
      intro j _
      have hge : ((M:ℝ) - 1) * (qmax * ‖ℓ j‖) / Real.pi ≤ cinv j := by
        have h := mul_le_mul_of_nonneg_left
          (le_trans (le_max_right (9 * d ^ 2 * Height.logHeight₁ (α j))
            (qmax * ‖ℓ j‖ / Real.pi)) (le_max_left _ 1)) (le_of_lt hm1R)
        simp only [hcinvdef]
        have heq : ((M:ℝ) - 1) * (qmax * ‖ℓ j‖) / Real.pi
            = ((M:ℝ) - 1) * (qmax * ‖ℓ j‖ / Real.pi) := by ring
        rw [heq]
        exact h
      have hge' : ((M:ℝ) - 1) * (qmax * ‖ℓ j‖) ≤ Real.pi * cinv j := by
        rw [div_le_iff₀ Real.pi_pos] at hge
        linarith [hge]
      rcases eq_or_lt_of_le (norm_nonneg (ℓ j)) with hzero | hpos
      · have : c j * ‖ℓ j‖ = 0 := by
          have hcq : c j * ‖ℓ j‖ = ‖ℓ j‖ / cinv j := by
            simp only [hcdef, div_eq_inv_mul]
          rw [hcq, ← hzero]; simp
        rw [this]; positivity
      · have hcq : c j * ‖ℓ j‖ = ‖ℓ j‖ / cinv j := by
          simp only [hcdef, div_eq_inv_mul]
        rw [hcq]
        rw [div_le_div_iff₀ (hcinv_pos j) (by positivity)]
        linarith [hge']
    have hsum_imag : ∑ j ∈ Finset.univ.erase k, c j * ‖ℓ j‖ ≤ Real.pi / qmax := by
      calc ∑ j ∈ Finset.univ.erase k, c j * ‖ℓ j‖
          ≤ ∑ j ∈ Finset.univ.erase k, Real.pi / (((M:ℝ) - 1) * qmax) :=
            Finset.sum_le_sum hterm_imag
        _ = ((Finset.univ.erase k).card : ℝ) * (Real.pi / (((M:ℝ) - 1) * qmax)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = Real.pi / qmax := by
            rw [hcard, hcast]
            field_simp
    have himag : ‖∑ i, (s i : ℂ) * ℓ i‖ * (orderOf β : ℝ) < 2 * Real.pi := by
      have hnorm := norm_thetaC_le ℓ tgen s k c htθ_sum (htk k) hdev
      have h1 : ‖∑ i, (s i : ℂ) * ℓ i‖ ≤ Real.pi / qmax := le_trans hnorm hsum_imag
      have h3 : ‖∑ i, (s i : ℂ) * ℓ i‖ * (orderOf β : ℝ) ≤ (Real.pi / qmax) * qmax :=
        mul_le_mul h1 hqle (by positivity) (by positivity)
      rw [div_mul_cancel₀ Real.pi (ne_of_gt hqmaxpos)] at h3
      linarith [Real.pi_pos]
    have hexpq : Complex.exp ((orderOf β : ℂ) * (∑ i, (s i : ℂ) * ℓ i)) = 1 := by
      rw [Complex.exp_nat_mul, hβexp, ← map_pow, pow_orderOf_eq_one, map_one]
    have hnormq : (orderOf β : ℝ) * ‖∑ i, (s i : ℂ) * ℓ i‖ < 2 * Real.pi := by
      rw [mul_comm]
      exact himag
    have hθs : ∑ i, (s i : ℂ) * ℓ i = 0 :=
      smul_theta_eq_zero_of_exp_eq_one (orderOf β) (∑ i, (s i : ℂ) * ℓ i) hqpos hexpq hnormq
    obtain ⟨a, ha⟩ := hgen s hθs
    have ha_ne : a ≠ 0 := by
      rintro rfl
      exact hsne (by rw [ha]; simp)
    have hsk_le : |((tgen k : ℤ) : ℝ)| ≤ |(s k : ℝ)| := by
      have habs : (1:ℝ) ≤ |(a:ℝ)| := by
        have h2 : (1:ℤ) ≤ |a| := by
          have h3 : (0:ℤ) < |a| := abs_pos.mpr ha_ne
          omega
        calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
          _ ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast h2
          _ = |((a:ℤ):ℝ)| := by simp
      have hsk_eq : (s k : ℤ) = a * tgen k := by
        rw [ha, Pi.smul_apply, smul_eq_mul]
      rw [hsk_eq, Int.cast_mul, abs_mul]
      calc |((tgen k : ℤ) : ℝ)| = 1 * |((tgen k : ℤ) : ℝ)| := (one_mul _).symm
        _ ≤ |((a:ℤ):ℝ)| * |((tgen k : ℤ) : ℝ)| :=
            mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    -- the final arithmetic
    have hV1 : ∀ j, Height.logHeight₁ (α j) ≤ d * hmod (α j) (ℓ j) := by
      intro j
      have h := wsb_div_d_le_hmod (α j) (ℓ j)
      rw [div_le_iff₀ hdpos] at h
      linarith
    have hV3 : ∀ j, (1:ℝ) ≤ 9 * d ^ 3 * hmod (α j) (ℓ j) := by
      intro j
      have h1 : (1:ℝ) / d ≤ hmod (α j) (ℓ j) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h2 : 9 * d ^ 3 * ((1:ℝ) / d) = 9 * d ^ 2 := by field_simp
      have h3 : (1:ℝ) ≤ 9 * d ^ 2 := by nlinarith [hd1]
      calc (1:ℝ) ≤ 9 * d ^ 2 := h3
        _ = 9 * d ^ 3 * ((1:ℝ) / d) := h2.symm
        _ ≤ 9 * d ^ 3 * hmod (α j) (ℓ j) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hper : ∀ j ∈ Finset.univ.erase k,
        cinv j ≤ 9 * ((M:ℝ) - 1) * d ^ 3 * hmod (α j) (ℓ j) := by
      intro j _
      have hA : 9 * d ^ 2 * Height.logHeight₁ (α j) ≤ 9 * d ^ 3 * hmod (α j) (ℓ j) := by
        have h := hV1 j
        nlinarith [h, hdpos]
      have hB : qmax * ‖ℓ j‖ / Real.pi ≤ 9 * d ^ 3 * hmod (α j) (ℓ j) := by
        rw [hqmax]
        have hV2 : ‖ℓ j‖ ≤ d * hmod (α j) (ℓ j) := wsb_norm_le_d_mul_hmod (α j) (ℓ j)
        have hstep : 4 * d ^ 2 * ‖ℓ j‖ / Real.pi ≤ 4 * d ^ 2 * (d * hmod (α j) (ℓ j)) / Real.pi :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV2 (by positivity))
            (le_of_lt Real.pi_pos)
        have hfour : 4 / Real.pi ≤ 9 := by
          rw [div_le_iff₀ Real.pi_pos]
          nlinarith [Real.pi_gt_three]
        have hstep2 : 4 * d ^ 2 * (d * hmod (α j) (ℓ j)) / Real.pi
            ≤ 9 * d ^ 3 * hmod (α j) (ℓ j) := by
          have hVnn : 0 < hmod (α j) (ℓ j) := wsb_hmod_pos (α j) (ℓ j)
          calc 4 * d ^ 2 * (d * hmod (α j) (ℓ j)) / Real.pi
              = (4 / Real.pi) * (d ^ 3 * hmod (α j) (ℓ j)) := by field_simp
            _ ≤ 9 * (d ^ 3 * hmod (α j) (ℓ j)) :=
                mul_le_mul_of_nonneg_right hfour (by positivity)
            _ = 9 * d ^ 3 * hmod (α j) (ℓ j) := by ring
        linarith
      simp only [hcinvdef]
      have heq : ((M:ℝ) - 1) * (9 * d ^ 3 * hmod (α j) (ℓ j))
          = 9 * ((M:ℝ) - 1) * d ^ 3 * hmod (α j) (ℓ j) := by ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_left (max_le (max_le hA hB) (hV3 j)) (le_of_lt hm1R)
    have hsk_bound : |(s k : ℝ)|
        ≤ (9 * ((M:ℝ) - 1) * d ^ 3) ^ (M - 1) * ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j) := by
      have h1 : |(s k : ℝ)| ≤ ck := by
        have := hsk
        rw [hc'def, Function.update_self] at this
        exact this
      have h4 : ck ≤ ∏ j ∈ Finset.univ.erase k,
          (9 * ((M:ℝ) - 1) * d ^ 3 * hmod (α j) (ℓ j)) := by
        rw [hckdef]
        exact wsb_prod_le_prod_of_nonneg _ (fun j _ => le_of_lt (hcinv_pos j)) hper
      have h5 : ∏ j ∈ Finset.univ.erase k,
            (9 * ((M:ℝ) - 1) * d ^ 3 * hmod (α j) (ℓ j))
          = (9 * ((M:ℝ) - 1) * d ^ 3) ^ (M - 1)
            * ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
      linarith [h1, h4, le_of_eq h5]
    have hgoal : |((tgen k : ℤ) : ℝ)|
        ≤ (9 * ((M:ℝ) - 1) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (M - 1)
          * ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j) := by
      have h' := hsk_bound
      rw [hd] at h'
      exact le_trans hsk_le h'
    exact hgoal

end Work.BW
