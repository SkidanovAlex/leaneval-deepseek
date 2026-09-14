import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!
# The "small bad set of block-compositions" lemma, with the positivity hypothesis `1 ≤ d h`
-/

namespace Commons.Combinatorics

open Finset

section SymCount

/-- For a fixed box `k`, summed over all multisets of size `n` on `Fin N`, the total number of
occurrences of `k` equals `|Sym (Fin N) n| * n / N`. -/
theorem sum_sym_count {N : ℕ} (n : ℕ) (k : Fin N) :
    ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℕ) : ℝ)
      = (Fintype.card (Sym (Fin N) n) : ℝ) * n / N := by
  have hN : (N : ℝ) ≠ 0 := by
    have : (0 : ℕ) < N := k.pos
    exact_mod_cast this.ne'
  have hperm : ∀ k' : Fin N,
      (∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k' : ℕ) : ℝ))
        = ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℕ) : ℝ) := by
    intro k'
    have hstep : ∀ s : Sym (Fin N) n,
        ((((Sym.equivCongr (Equiv.swap k k')) s : Sym (Fin N) n) : Multiset (Fin N)).count k' : ℝ)
          = (((s : Multiset (Fin N)).count k : ℕ) : ℝ) := by
      intro s
      have hcount := Multiset.count_map_eq_count' (Equiv.swap k k') (s : Multiset (Fin N))
        (Equiv.swap k k').injective k
      rw [Equiv.swap_apply_left] at hcount
      rw [Sym.equivCongr_apply, Sym.coe_map, hcount]
    have h := Equiv.sum_comp (Sym.equivCongr (Equiv.swap k k'))
        (fun s : Sym (Fin N) n => (((s : Multiset (Fin N)).count k' : ℕ) : ℝ))
    rw [← h]
    exact Finset.sum_congr rfl fun s _ => hstep s
  rw [eq_div_iff hN]
  calc (∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℕ) : ℝ)) * (N : ℝ)
      = (N : ℝ) * ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℕ) : ℝ) := by ring
    _ = ∑ _k' : Fin N, ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ k' : Fin N, ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k' : ℕ) : ℝ) :=
          Finset.sum_congr rfl fun k' _ => (hperm k').symm
    _ = ∑ s : Sym (Fin N) n, ∑ k' : Fin N, (((s : Multiset (Fin N)).count k' : ℕ) : ℝ) :=
          Finset.sum_comm
    _ = ∑ _s : Sym (Fin N) n, (n : ℝ) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have hc : ∑ k' : Fin N, ((s : Multiset (Fin N)).count k' : ℕ) = n := by
            rw [Multiset.sum_count_eq_card (s := Finset.univ) (m := (s : Multiset (Fin N)))
              (fun a _ => Finset.mem_univ a)]
            exact Sym.card_coe
          exact_mod_cast hc
    _ = (Fintype.card (Sym (Fin N) n) : ℝ) * n := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SymCount

section PiSums

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {T : ι → Type*} [∀ i, Fintype (T i)]

/-- Sum over a product type of a function of a single coordinate. -/
theorem sum_pi_apply (i : ι) (g : T i → ℝ) :
    ∑ x : ∀ j, T j, g (x i)
      = (∏ j ∈ Finset.univ.erase i, (Fintype.card (T j) : ℝ)) * ∑ t : T i, g t := by
  set F : ∀ j, T j → ℝ := Function.update (fun j (_ : T j) => (1 : ℝ)) i g with hFdef
  have hprod := Finset.prod_univ_sum (t := fun _ : ι => (Finset.univ : Finset (T _)))
      (f := F)
  rw [Fintype.piFinset_univ] at hprod
  have hL : ∏ j, ∑ t : T j, F j t
      = (∑ t : T i, g t) * ∏ j ∈ Finset.univ.erase i, (Fintype.card (T j) : ℝ) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ t : T j, F j t) (Finset.mem_univ i)]
    congr 1
    · simp only [hFdef, Function.update_self]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hFdef, Function.update_of_ne hji]
  have hR : ∑ x : ∀ j, T j, ∏ j, F j (x j) = ∑ x : ∀ j, T j, g (x i) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (x j)) (Finset.mem_univ i)]
    have h1 : F i (x i) = g (x i) := by simp only [hFdef, Function.update_self]
    have h2 : (∏ j ∈ Finset.univ.erase i, F j (x j)) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hFdef, Function.update_of_ne hji]
    rw [h1, h2, mul_one]
  rw [hL] at hprod
  rw [hR] at hprod
  rw [mul_comm]
  exact hprod.symm

/-- Sum over a product type of a product of functions of two distinct coordinates. -/
theorem sum_pi_apply_mul_apply (i j : ι) (hij : i ≠ j) (f : T i → ℝ) (g : T j → ℝ) :
    ∑ x : ∀ k, T k, f (x i) * g (x j)
      = (∑ t : T i, f t) * (∑ t : T j, g t)
        * ∏ k ∈ (Finset.univ.erase i).erase j, (Fintype.card (T k) : ℝ) := by
  set F : ∀ k, T k → ℝ :=
    Function.update (Function.update (fun k (_ : T k) => (1 : ℝ)) i f) j g with hFdef
  have hprod := Finset.prod_univ_sum (t := fun _ : ι => (Finset.univ : Finset (T _)))
      (f := F)
  rw [Fintype.piFinset_univ] at hprod
  have hji : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hL : ∏ k, ∑ t : T k, F k t
      = (∑ t : T i, f t) * (∑ t : T j, g t)
        * ∏ k ∈ (Finset.univ.erase i).erase j, (Fintype.card (T k) : ℝ) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ t : T k, F k t) (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => ∑ t : T k, F k t) hji]
    have hFi : (∑ t : T i, F i t) = ∑ t : T i, f t := by
      simp [hFdef, Function.update_of_ne hij]
    have hFj : (∑ t : T j, F j t) = ∑ t : T j, g t := by
      simp [hFdef, Function.update_self]
    rw [hFi, hFj]
    have hP : (∏ k ∈ (Finset.univ.erase i).erase j, (∑ t : T k, F k t))
        = ∏ k ∈ (Finset.univ.erase i).erase j, (Fintype.card (T k) : ℝ) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      simp [hFdef, Function.update_of_ne hkj, Function.update_of_ne hki]
    rw [hP, mul_assoc]
  have hR : ∑ x : ∀ k, T k, ∏ k, F k (x k)
      = ∑ x : ∀ k, T k, f (x i) * g (x j) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ (fun k => F k (x k)) (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => F k (x k)) hji]
    have h1 : F i (x i) = f (x i) := by simp [hFdef, Function.update_of_ne hij]
    have h2 : F j (x j) = g (x j) := by simp [hFdef, Function.update_self]
    rw [h1, h2]
    have h3 : (∏ k ∈ (Finset.univ.erase i).erase j, F k (x k)) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      simp [hFdef, Function.update_of_ne hkj, Function.update_of_ne hki]
    rw [h3]; ring
  rw [hL] at hprod
  rw [hR] at hprod
  exact hprod.symm

/-- Variance bound on a product type: if each coordinate function has mean `0` and second moment
at most `|T i| * C`, then the square of the sum has mean at most `|∏ T| * |ι| * C`. -/
theorem sum_sq_sum_le {C : ℝ} (b : ∀ i, T i → ℝ)
    (hsum : ∀ i, ∑ t : T i, b i t = 0)
    (hsq : ∀ i, ∑ t : T i, (b i t)^2 ≤ (Fintype.card (T i) : ℝ) * C) :
    ∑ x : ∀ i, T i, (∑ i, b i (x i))^2
      ≤ (∏ i, (Fintype.card (T i) : ℝ)) * (Fintype.card ι : ℝ) * C := by
  have hcardi : ∀ i, (0 : ℝ) ≤ ∏ k ∈ Finset.univ.erase i, (Fintype.card (T k) : ℝ) :=
    fun i => Finset.prod_nonneg (fun k _ => by positivity)
  have hoff : ∀ i j, i ≠ j → (∑ x : ∀ k, T k, b i (x i) * b j (x j)) = 0 := by
    intro i j hij
    rw [sum_pi_apply_mul_apply i j hij (b i) (b j), hsum i, zero_mul, zero_mul]
  have hdiag : ∀ i, (∑ x : ∀ k, T k, b i (x i) * b i (x i))
      ≤ (∏ k, (Fintype.card (T k) : ℝ)) * C := by
    intro i
    rw [show (∑ x : ∀ k, T k, b i (x i) * b i (x i))
        = ∑ x : ∀ k, T k, (b i (x i))^2 by
      refine Finset.sum_congr rfl (fun x _ => by rw [sq])]
    rw [sum_pi_apply i (fun t => (b i t)^2)]
    calc (∏ k ∈ Finset.univ.erase i, (Fintype.card (T k) : ℝ)) * (∑ t : T i, (b i t)^2)
        ≤ (∏ k ∈ Finset.univ.erase i, (Fintype.card (T k) : ℝ))
            * ((Fintype.card (T i) : ℝ) * C) :=
          mul_le_mul_of_nonneg_left (hsq i) (hcardi i)
      _ = (∏ k, (Fintype.card (T k) : ℝ)) * C := by
          rw [← Finset.mul_prod_erase Finset.univ (fun k => (Fintype.card (T k) : ℝ))
            (Finset.mem_univ i)]
          ring
  have hexp : ∑ x : ∀ i, T i, (∑ i, b i (x i))^2
      = ∑ i, ∑ j, ∑ x : ∀ i, T i, b i (x i) * b j (x j) := by
    have h1 : ∀ x : ∀ i, T i, (∑ i, b i (x i)) * (∑ j, b j (x j))
        = ∑ i, ∑ j, b i (x i) * b j (x j) := by
      intro x
      rw [Finset.sum_mul_sum]
    rw [show (∑ x : ∀ i, T i, (∑ i, b i (x i))^2)
          = ∑ x : ∀ i, T i, (∑ i, b i (x i)) * (∑ j, b j (x j)) by
        refine Finset.sum_congr rfl (fun x _ => by rw [sq])]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [hexp]
  have hsplit : ∀ i, (∑ j, ∑ x : ∀ k, T k, b i (x i) * b j (x j))
      = (∑ x : ∀ k, T k, b i (x i) * b i (x i))
        + ∑ j ∈ Finset.univ.erase i, ∑ x : ∀ k, T k, b i (x i) * b j (x j) := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => ∑ x : ∀ k, T k, b i (x i) * b j (x j)) (Finset.mem_univ i)]
  calc ∑ i, ∑ j, ∑ x : ∀ k, T k, b i (x i) * b j (x j)
      = ∑ i, ((∑ x : ∀ k, T k, b i (x i) * b i (x i))
          + ∑ j ∈ Finset.univ.erase i, ∑ x : ∀ k, T k, b i (x i) * b j (x j)) :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, ∑ x : ∀ k, T k, b i (x i) * b i (x i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show (∑ j ∈ Finset.univ.erase i, ∑ x : ∀ k, T k, b i (x i) * b j (x j)) = 0 by
          refine Finset.sum_eq_zero (fun j hj => ?_)
          exact hoff i j (Finset.ne_of_mem_erase hj).symm]
        rw [add_zero]
    _ ≤ ∑ i, (∏ k, (Fintype.card (T k) : ℝ)) * C :=
        Finset.sum_le_sum (fun i _ => hdiag i)
    _ = (∏ k, (Fintype.card (T k) : ℝ)) * (Fintype.card ι : ℝ) * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end PiSums

section Chebyshev

/-- Chebyshev/Markov on a finset: the number of points above a positive threshold contributes at
most the sum of squares. -/
theorem card_filter_abs_mul_sq_le' {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ((s.filter (fun a => t < |g a|)).card : ℝ) * t ^ 2 ≤ ∑ a ∈ s, (g a) ^ 2 := by
  have h1 : ((s.filter (fun a => t < |g a|)).card : ℝ) * t^2
      = ∑ a ∈ s.filter (fun a => t < |g a|), t^2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  refine le_trans (Finset.sum_le_sum (fun a ha => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => sq_nonneg _))
  rw [Finset.mem_filter] at ha
  have h : t ≤ |g a| := le_of_lt ha.2
  rw [← sq_abs (g a)]
  nlinarith [ht, h, abs_nonneg (g a)]

end Chebyshev

section SymCentered

/-- Second moment of the centred box-counting statistic on `Sym (Fin N) n`. -/
theorem sum_sym_centered_sq_le {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) (k : Fin N) :
    ∑ s : Sym (Fin N) n, (((s : Multiset (Fin N)).count k : ℝ) / (n : ℝ) - 1 / (N : ℝ)) ^ 2
      ≤ (Fintype.card (Sym (Fin N) n) : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set a : Sym (Fin N) n → ℝ := fun s => ((s : Multiset (Fin N)).count k : ℝ) / (n : ℝ) with ha
  have ha_nonneg : ∀ s, 0 ≤ a s := fun s => by positivity
  have ha_le_one : ∀ s, a s ≤ 1 := by
    intro s
    rw [ha]
    rw [div_le_one (by positivity)]
    have := Multiset.count_le_card k (s : Multiset (Fin N))
    rw [Sym.card_coe] at this
    exact_mod_cast this
  have hsum_a : ∑ s, a s = (Fintype.card (Sym (Fin N) n) : ℝ) / N := by
    rw [ha]
    rw [← Finset.sum_div, sum_sym_count n k]
    field_simp
  have hexp : ∑ s, (a s - 1 / (N : ℝ))^2
      = ∑ s, (a s)^2 - (Fintype.card (Sym (Fin N) n) : ℝ) / (N : ℝ)^2 := by
    have hpt : ∀ s, (a s - 1 / (N : ℝ))^2
        = (a s)^2 - 2 * (1 / (N : ℝ)) * a s + (1 / (N : ℝ))^2 := by
      intro s; ring
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ s, 2 * (1 / (N : ℝ)) * a s)
        = 2 * (1 / (N : ℝ)) * ∑ s, a s by rw [Finset.mul_sum]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum_a]
    field_simp
    ring
  have hsq_le : ∑ s, (a s)^2 ≤ ∑ s, a s := by
    refine Finset.sum_le_sum (fun s _ => ?_)
    have h0 := ha_nonneg s
    have h1 := ha_le_one s
    nlinarith [sq_nonneg (a s)]
  rw [hexp]
  have hfin : (Fintype.card (Sym (Fin N) n) : ℝ) * (((N : ℝ) - 1) / (N : ℝ)^2)
      = (Fintype.card (Sym (Fin N) n) : ℝ) / N - (Fintype.card (Sym (Fin N) n) : ℝ) / (N : ℝ)^2 := by
    field_simp
  rw [hfin]
  linarith [hsq_le, hsum_a]

end SymCentered


section Main

theorem exists_bad_exponents_small_fn_pos {m N : ℕ} (hN : 2 ≤ N) (d : Fin m → ℕ)
    (hd : ∀ h, 1 ≤ d h)
    (W : ℝ) (hW : 0 < W) (r : ℕ) (hWm : 2 * r ≤ (m : ℝ) * W ^ 2) :
    ∃ bad : Finset (Fin m → Fin N → ℕ),
      (∀ j ∈ bad, ∀ h : Fin m, ∑ k : Fin N, j h k = d h) ∧
      (∀ j, (∀ h : Fin m, ∑ k : Fin N, j h k = d h) → j ∉ bad →
        ∀ k : Fin N,
          |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
            ≤ (m : ℝ) * W) ∧
      2 * r * bad.card < ∏ h : Fin m, (d h + N - 1).choose (N - 1) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine ⟨Finset.univ, ?_, ?_, ?_⟩
    · intro j hj h; exact (Fin.elim0 h)
    · intro j hj hnot; exact absurd (Finset.mem_univ j) hnot
    · have hr : r = 0 := by
        have h1 : ((2 * r : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) := by simpa using hWm
        have h2 : 2 * r ≤ 0 := Nat.cast_le.mp h1
        omega
      subst hr
      simp
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hNR : (0 : ℝ) < (N : ℝ) := by positivity
    have hOne : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans (by norm_num) hN)
    -- the map sending a tuple of multisets to its counting function
    let φ : (∀ h : Fin m, Sym (Fin N) (d h)) → (Fin m → Fin N → ℕ) :=
      fun x h k => (x h : Multiset (Fin N)).count k
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      funext h
      apply Sym.coe_injective
      apply Multiset.toFinsupp.injective
      ext k
      rw [Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
      exact congrFun (congrFun hxy h) k
    set S : Finset (Fin m → Fin N → ℕ) := Finset.univ.image φ with hSdef
    have hSp : ∀ j : Fin m → Fin N → ℕ, j ∈ S ↔ ∀ h : Fin m, ∑ k : Fin N, j h k = d h := by
      intro j
      constructor
      · intro hj
        rw [hSdef] at hj
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hj
        intro h
        have : (∑ k : Fin N, (x h : Multiset (Fin N)).count k) = (x h : Multiset (Fin N)).card :=
          Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
        rw [this, Sym.card_coe]
      · intro hj
        rw [hSdef]
        refine Finset.mem_image.mpr ⟨fun h : Fin m =>
          (Sym.equivNatSumOfFintype (Fin N) (d h)).symm ⟨j h, hj h⟩, Finset.mem_univ _, ?_⟩
        funext h k
        have key := Sym.coe_equivNatSumOfFintype_apply_apply (Fin N) (d h)
          ((Sym.equivNatSumOfFintype (Fin N) (d h)).symm ⟨j h, hj h⟩) k
        have key2 := congrFun (congrArg Subtype.val
          (Equiv.apply_symm_apply (Sym.equivNatSumOfFintype (Fin N) (d h)) ⟨j h, hj h⟩)) k
        rw [key] at key2
        exact key2
    have hSymCard : ∀ h : Fin m, Fintype.card (Sym (Fin N) (d h)) = (d h + N - 1).choose (N - 1) := by
      intro h
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have hEq : N + d h - 1 = d h + (N - 1) := by omega
      rw [Nat.choose_symm_of_eq_add hEq]
      congr 1
      omega
    have hS_card : S.card = ∏ h : Fin m, (d h + N - 1).choose (N - 1) := by
      rw [hSdef, Finset.card_image_of_injective Finset.univ hφ_inj, Finset.card_univ,
        Fintype.card_pi]
      exact Finset.prod_congr rfl (fun h _ => hSymCard h)
    have hSpos : 0 < S.card := by
      rw [hS_card]
      refine Finset.prod_pos (fun h _ => ?_)
      apply Nat.choose_pos
      omega
    have hSRpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
    have hprod : (∏ h : Fin m, (Fintype.card (Sym (Fin N) (d h)) : ℝ)) = (S.card : ℝ) := by
      have hcast : (∏ h : Fin m, (Fintype.card (Sym (Fin N) (d h)) : ℝ))
          = ((∏ h : Fin m, Fintype.card (Sym (Fin N) (d h)) : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, Finset.prod_congr rfl (fun h _ => hSymCard h), ← hS_card]
    have hratio_lt : ((N : ℝ) - 1) / (N : ℝ) < 1 := by
      rw [div_lt_one hNR]; linarith
    have hmain : ∀ k : Fin N,
        (((S.filter (fun j => (m : ℝ) * W <
            |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ)
          * ((m : ℝ) * W) ^ 2
          ≤ (S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2)) := by
      intro k
      set b : ∀ h : Fin m, Sym (Fin N) (d h) → ℝ :=
        fun h t => ((t : Multiset (Fin N)).count k : ℝ) / (d h : ℝ) - 1 / (N : ℝ) with hbdef
      have hsum_b : ∀ h : Fin m, ∑ t : Sym (Fin N) (d h), b h t = 0 := by
        intro h
        have hdh : (d h : ℝ) ≠ 0 := by
          have := hd h; positivity
        rw [hbdef]
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_sym_count (d h) k]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
        ring
      have hsq_b : ∀ h : Fin m, ∑ t : Sym (Fin N) (d h), (b h t) ^ 2
          ≤ (Fintype.card (Sym (Fin N) (d h)) : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2) := by
        intro h
        rw [hbdef]
        exact sum_sym_centered_sq_le hN (d h) (hd h) k
      have hvariance := sum_sq_sum_le b hsum_b hsq_b
      have hcheb := card_filter_abs_mul_sq_le' S
        (fun j => (∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ))
        (mul_nonneg (le_of_lt hmR) (le_of_lt hW))
      have htrans : ∑ j ∈ S,
            ((∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)) ^ 2
          = ∑ x : ∀ h : Fin m, Sym (Fin N) (d h), (∑ h, b h (x h)) ^ 2 := by
        rw [hSdef, Finset.sum_image (f := fun j : Fin m → Fin N → ℕ =>
            ((∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)) ^ 2)
          (g := φ) (fun x _ y _ hxy => hφ_inj hxy)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have hF : (∑ h : Fin m, ((φ x h k : ℕ) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)
            = ∑ h : Fin m, b h (x h) := by
          have hb : ∑ h : Fin m, b h (x h)
              = (∑ h : Fin m, (((x h : Multiset (Fin N)).count k : ℕ) : ℝ) / (d h : ℝ))
                - ∑ _h : Fin m, (1 : ℝ) / (N : ℝ) := by
            rw [hbdef, Finset.sum_sub_distrib]
          rw [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one_div]
        rw [hF]
      have h1 : ((S.filter (fun j => (m : ℝ) * W <
            |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ)
          * ((m : ℝ) * W) ^ 2
          ≤ ∑ x : ∀ h : Fin m, Sym (Fin N) (d h), (∑ h, b h (x h)) ^ 2 := by
        rw [← htrans]
        exact hcheb
      have h2 : ∑ x : ∀ h : Fin m, Sym (Fin N) (d h), (∑ h, b h (x h)) ^ 2
          ≤ (∏ h : Fin m, (Fintype.card (Sym (Fin N) (d h)) : ℝ)) * (m : ℝ)
              * (((N : ℝ) - 1) / (N : ℝ) ^ 2) := by
        simpa using hvariance
      calc ((S.filter (fun j => (m : ℝ) * W <
            |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ)
          * ((m : ℝ) * W) ^ 2
          ≤ ∑ x : ∀ h : Fin m, Sym (Fin N) (d h), (∑ h, b h (x h)) ^ 2 := h1
        _ ≤ (∏ h : Fin m, (Fintype.card (Sym (Fin N) (d h)) : ℝ)) * (m : ℝ)
              * (((N : ℝ) - 1) / (N : ℝ) ^ 2) := h2
        _ = (S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2) := by rw [hprod]
    set bad : Finset (Fin m → Fin N → ℕ) :=
      S.filter (fun j => ∃ k : Fin N, (m : ℝ) * W <
        |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|) with hbaddef
    have hbad_sub : bad ⊆ Finset.univ.biUnion (fun k : Fin N =>
        S.filter (fun j => (m : ℝ) * W <
          |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)) := by
      intro j hj
      rw [hbaddef, Finset.mem_filter] at hj
      obtain ⟨hjS, k, hk⟩ := hj
      rw [Finset.mem_biUnion]
      exact ⟨k, Finset.mem_univ k, by rw [Finset.mem_filter]; exact ⟨hjS, hk⟩⟩
    have hbad_card : (bad.card : ℝ) ≤ ∑ k : Fin N,
        ((S.filter (fun j => (m : ℝ) * W <
          |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ) := by
      have h1 : bad.card ≤ (Finset.univ.biUnion (fun k : Fin N =>
          S.filter (fun j => (m : ℝ) * W <
            |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|))).card :=
        Finset.card_le_card hbad_sub
      have h2 : (Finset.univ.biUnion (fun k : Fin N =>
          S.filter (fun j => (m : ℝ) * W <
            |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|))).card
          ≤ ∑ k : Fin N, (S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card :=
        Finset.card_biUnion_le
      calc (bad.card : ℝ)
          ≤ ((Finset.univ.biUnion (fun k : Fin N => S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|))).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ ((∑ k : Fin N, (S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℕ) : ℝ) := by
            exact_mod_cast h2
        _ = ∑ k : Fin N, ((S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ) := by
            push_cast; ring
    have hcheb_sum : (bad.card : ℝ) * ((m : ℝ) * W) ^ 2
        ≤ (N : ℝ) * ((S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2)) := by
      calc (bad.card : ℝ) * ((m : ℝ) * W) ^ 2
          ≤ (∑ k : Fin N, ((S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ))
            * ((m : ℝ) * W) ^ 2 :=
            mul_le_mul_of_nonneg_right hbad_card (sq_nonneg _)
        _ = ∑ k : Fin N, ((S.filter (fun j => (m : ℝ) * W <
              |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|)).card : ℝ)
            * ((m : ℝ) * W) ^ 2 := by rw [Finset.sum_mul]
        _ ≤ ∑ _k : Fin N, (S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2) :=
            Finset.sum_le_sum (fun k _ => hmain k)
        _ = (N : ℝ) * ((S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmain_bound : (bad.card : ℝ) * ((m : ℝ) * W) ^ 2
        ≤ (S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ)) := by
      have hsq : ((m : ℝ) * W) ^ 2 = (m : ℝ) * ((m : ℝ) * W ^ 2) := by ring
      have h' : (N : ℝ) * ((S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ) ^ 2))
          = (S.card : ℝ) * (m : ℝ) * (((N : ℝ) - 1) / (N : ℝ)) := by
        field_simp
      rw [hsq, h'] at hcheb_sum
      rw [hsq]
      exact hcheb_sum
    have hdiv : (bad.card : ℝ) * ((m : ℝ) * W ^ 2)
        ≤ (S.card : ℝ) * (((N : ℝ) - 1) / (N : ℝ)) := by
      have h : (m : ℝ) * ((bad.card : ℝ) * ((m : ℝ) * W ^ 2))
          ≤ (m : ℝ) * ((S.card : ℝ) * (((N : ℝ) - 1) / (N : ℝ))) := by
        nlinarith [hmain_bound]
      exact le_of_mul_le_mul_left h hmR
    have hlt : ((2 * r : ℕ) : ℝ) * (bad.card : ℝ) < (S.card : ℝ) := by
      have h2r : ((2 * r : ℕ) : ℝ) ≤ (m : ℝ) * W ^ 2 := by
        push_cast; exact hWm
      have h1 : ((2 * r : ℕ) : ℝ) * (bad.card : ℝ) ≤ ((m : ℝ) * W ^ 2) * (bad.card : ℝ) :=
        mul_le_mul_of_nonneg_right h2r (by positivity)
      calc ((2 * r : ℕ) : ℝ) * (bad.card : ℝ)
          ≤ ((m : ℝ) * W ^ 2) * (bad.card : ℝ) := h1
        _ = (bad.card : ℝ) * ((m : ℝ) * W ^ 2) := by ring
        _ ≤ (S.card : ℝ) * (((N : ℝ) - 1) / (N : ℝ)) := hdiv
        _ < (S.card : ℝ) * 1 := mul_lt_mul_of_pos_left hratio_lt hSRpos
        _ = (S.card : ℝ) := by ring
    refine ⟨bad, ?_, ?_, ?_⟩
    · intro j hj h
      rw [hbaddef, Finset.mem_filter] at hj
      exact (hSp j).mp hj.1 h
    · intro j hp hjnb k
      by_contra hcon
      have hlt' : (m : ℝ) * W < |(∑ h : Fin m, (j h k : ℝ) / (d h : ℝ))
          - (m : ℝ) / (N : ℝ)| := not_le.mp hcon
      have hjS : j ∈ S := (hSp j).mpr hp
      have hjb : j ∈ bad := by
        rw [hbaddef, Finset.mem_filter]
        exact ⟨hjS, k, hlt'⟩
      exact hjnb hjb
    · have hltN : 2 * r * bad.card < S.card := by exact_mod_cast hlt
      rw [← hS_card]
      exact hltN

end Main

end Commons.Combinatorics