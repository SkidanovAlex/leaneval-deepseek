import Mathlib
import Submission.Work.HP.badclass.BadDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- The exponent vector `(d-1)·e_i + e_j` for `i ≠ j`, an element of `Mon d n`. -/
def monE2 (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hij : i ≠ j) : Mon d n :=
  ⟨fun k => ⟨(if k = i then d - 1 else if k = j then 1 else 0 : ℕ), by
      by_cases hki : k = i
      · rw [if_pos hki]; omega
      · rw [if_neg hki]
        by_cases hkj : k = j
        · rw [if_pos hkj]; omega
        · rw [if_neg hkj]; omega⟩, by
    have h2 : ∀ k, (if k = i then d - 1 else if k = j then 1 else 0 : ℕ)
        = (if k = i then d - 1 else 0) + (if k = j then 1 else 0) := by
      intro k
      by_cases hki : k = i
      · simp [hki, hij]
      · by_cases hkj : k = j
        · simp [hki, hkj, show ¬ (j = i) from fun h => hij h.symm]
        · simp [hki, hkj]
    simp only [h2, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun _ => (d - 1 : ℕ)),
      Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℕ)), Finset.mem_univ, if_true]
    omega⟩

lemma monE2_self (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hij : i ≠ j) :
    ((monE2 d n hd i j hij).1 i : ℕ) = d - 1 := by
  simp only [monE2]
  simp

lemma monE2_right (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hij : i ≠ j) :
    ((monE2 d n hd i j hij).1 j : ℕ) = 1 := by
  simp only [monE2]
  rw [if_neg (show ¬ (j = i) from fun h => hij h.symm)]
  simp

lemma monE2_other (d n : ℕ) (hd : 1 ≤ d) (i j k : Fin (n + 1)) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : ((monE2 d n hd i j hij).1 k : ℕ) = 0 := by
  simp only [monE2]
  rw [if_neg hki, if_neg hkj]

lemma veronese_monE (d n p : ℕ) (x : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) :
    (∏ k, x k ^ ((Work.HP.monE d n j).1 k : ℕ)) = x j ^ d := by
  rw [Finset.prod_eq_single j (f := fun k : Fin (n + 1) => x k ^ ((Work.HP.monE d n j).1 k : ℕ))
    (fun k _ hkj => by rw [Work.HP.monE_ne d n j k hkj]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)]
  rw [Work.HP.monE_self]

lemma veronese_monE2 (d n p : ℕ) (hd : 1 ≤ d) (x : Fin (n + 1) → ZMod p)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    (∏ k, x k ^ ((monE2 d n hd i j hij).1 k : ℕ)) = x i ^ (d - 1) * x j := by
  rw [Finset.prod_eq_mul (s := Finset.univ) i j hij
    (f := fun k : Fin (n + 1) => x k ^ ((monE2 d n hd i j hij).1 k : ℕ))
    (fun k _ hk => by rw [monE2_other d n hd i j k hij hk.1 hk.2, pow_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)
    (fun hj => absurd (Finset.mem_univ j) hj)]
  rw [monE2_self, monE2_right, pow_one]

/-- If the Veronese vectors of `x` and `y` (both in the torus) are proportional then `x` and `y`
are collinear. -/
lemma eq_smul_of_veronese (d n p : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ZMod p) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (lam : ZMod p) (h : ∀ m : Work.HP.Mon d n,
      (∏ k, x k ^ ((m.1 k : ℕ))) = lam * ∏ k, y k ^ ((m.1 k : ℕ))) :
    ∃ t : ZMod p, x = t • y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey : ∀ i j : Fin (n + 1), i ≠ j → x i / y i = x j / y j := by
    intro i j hij
    have h1 := h (Work.HP.monE d n i)
    rw [veronese_monE d n p x i, veronese_monE d n p y i] at h1
    have h2 := h (monE2 d n hd i j hij)
    rw [veronese_monE2 d n p hd x i j hij, veronese_monE2 d n p hd y i j hij] at h2
    have ht : (x i / y i) ^ d = lam := by
      rw [div_pow, h1, mul_div_assoc, div_self (pow_ne_zero _ (hy i)), mul_one]
    have ht2 : (x i / y i) ^ (d - 1) * (x j / y j) = lam := by
      rw [div_pow]
      field_simp [hy i, hy j]
      linear_combination h2
    have hpow : (x i / y i) ^ d = (x i / y i) ^ (d - 1) * (x i / y i) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    have htne : (x i / y i) ^ (d - 1) ≠ 0 := pow_ne_zero _ (div_ne_zero (hx i) (hy i))
    have heq : (x i / y i) ^ (d - 1) * (x i / y i) = (x i / y i) ^ (d - 1) * (x j / y j) := by
      rw [← hpow, ht, ht2]
    exact mul_left_cancel₀ htne heq
  refine ⟨x 0 / y 0, funext (fun i => ?_)⟩
  have hti : x i / y i = x 0 / y 0 := by
    by_cases hi : i = 0
    · rw [hi]
    · exact hkey i 0 hi
  rw [Pi.smul_apply, smul_eq_mul, ← hti, div_mul_cancel₀ _ (hy i)]

/-- Two nonzero linear functionals given by Veronese evaluation, with nested kernels, force a
proportionality relation between the two points. -/
lemma prop_of_ker (d n p : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (u v : Fin (n + 1) → ZMod p) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (L₁ L₂ : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] ZMod p)
    (h₁ : ∀ m : Work.HP.Mon d n, L₁ (Pi.single m 1) = ∏ k, u k ^ (m.1 k : ℕ))
    (h₂ : ∀ m : Work.HP.Mon d n, L₂ (Pi.single m 1) = ∏ k, v k ^ (m.1 k : ℕ))
    (hker : ∀ a, L₂ a = 0 → L₁ a = 0) :
    ∃ t : ZMod p, v = t • u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hune0 : (∏ k, u k ^ (((Work.HP.monE d n 0).1 k : ℕ))) ≠ 0 := by
    rw [Finset.prod_eq_single 0
      (f := fun k : Fin (n + 1) => u k ^ (((Work.HP.monE d n 0).1 k : ℕ)))
      (fun b _ hb0 => by rw [Work.HP.monE_ne d n 0 b hb0, pow_zero])
      (fun h0 => absurd (Finset.mem_univ 0) h0)]
    rw [Work.HP.monE_self]
    exact pow_ne_zero _ (hu 0)
  have hrel : ∀ m : Work.HP.Mon d n,
      (∏ k, v k ^ (((Work.HP.monE d n 0).1 k : ℕ))) * (∏ k, u k ^ ((m.1 k : ℕ)))
        = (∏ k, v k ^ ((m.1 k : ℕ))) * (∏ k, u k ^ (((Work.HP.monE d n 0).1 k : ℕ))) := by
    intro m
    have hz : L₂ ((∏ k, v k ^ (((Work.HP.monE d n 0).1 k : ℕ))) • Pi.single m 1 -
        (∏ k, v k ^ ((m.1 k : ℕ))) • Pi.single (Work.HP.monE d n 0) 1) = 0 := by
      rw [map_sub, map_smul, map_smul, h₂, h₂]
      ring
    have hthis := hker _ hz
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h₁, h₁] at hthis
    rw [sub_eq_zero] at hthis
    exact hthis
  obtain ⟨t, ht⟩ := eq_smul_of_veronese d n p hp hd hn v u hv hu
    ((∏ k, v k ^ (((Work.HP.monE d n 0).1 k : ℕ))) *
      (∏ k, u k ^ (((Work.HP.monE d n 0).1 k : ℕ)))⁻¹)
    (fun m => by
      have h := hrel m
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, eq_div_iff hune0]
      exact h.symm)
  exact ⟨t, ht⟩

/-- For `x, y` in the torus which are not proportional, the two functionals `f_·(x)`, `f_·(y)`
are independent, so their joint kernel has `p^{N-2}` elements. -/
theorem pair_ker (d n p : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ZMod p) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hxy : ¬ ∃ z : ZMod p, y = z • x) :
    ({a : Work.HP.Mon d n → ZMod p |
        Work.HP.formEvalZMod d n p a x = 0 ∧ Work.HP.formEvalZMod d n p a y = 0} :
      Set (Work.HP.Mon d n → ZMod p)).ncard = p ^ (Work.HP.NN d n - 2) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set Lx : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] ZMod p :=
    Fintype.linearCombination (ZMod p)
      (fun m : Work.HP.Mon d n => ∏ j : Fin (n + 1), x j ^ (m.1 j : ℕ)) with hLx
  set Ly : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] ZMod p :=
    Fintype.linearCombination (ZMod p)
      (fun m : Work.HP.Mon d n => ∏ j : Fin (n + 1), y j ^ (m.1 j : ℕ)) with hLy
  have hLxapp : ∀ a, Lx a = Work.HP.formEvalZMod d n p a x := by
    intro a
    rw [hLx, Fintype.linearCombination_apply]
    simp only [smul_eq_mul, Work.HP.formEvalZMod]
  have hLyapp : ∀ a, Ly a = Work.HP.formEvalZMod d n p a y := by
    intro a
    rw [hLy, Fintype.linearCombination_apply]
    simp only [smul_eq_mul, Work.HP.formEvalZMod]
  have hLxdirac : ∀ m : Work.HP.Mon d n, Lx (Pi.single m 1) = ∏ k, x k ^ (m.1 k : ℕ) := by
    intro m
    rw [hLx, Fintype.linearCombination_apply,
      Finset.sum_eq_single m (f := fun b : Work.HP.Mon d n =>
        (Pi.single m 1 : Work.HP.Mon d n → ZMod p) b • (∏ j : Fin (n + 1), x j ^ (b.1 j : ℕ)))
        (fun b _ hbm => by rw [Pi.single_eq_of_ne (show b ≠ m from hbm), zero_smul])
        (fun hm => absurd (Finset.mem_univ m) hm)]
    rw [Pi.single_eq_same, one_smul]
  have hLydirac : ∀ m : Work.HP.Mon d n, Ly (Pi.single m 1) = ∏ k, y k ^ (m.1 k : ℕ) := by
    intro m
    rw [hLy, Fintype.linearCombination_apply,
      Finset.sum_eq_single m (f := fun b : Work.HP.Mon d n =>
        (Pi.single m 1 : Work.HP.Mon d n → ZMod p) b • (∏ j : Fin (n + 1), y j ^ (b.1 j : ℕ)))
        (fun b _ hbm => by rw [Pi.single_eq_of_ne (show b ≠ m from hbm), zero_smul])
        (fun hm => absurd (Finset.mem_univ m) hm)]
    rw [Pi.single_eq_same, one_smul]
  have hexa : ∃ a, Lx a ≠ 0 ∧ Ly a = 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    have hker : ∀ a, Ly a = 0 → Lx a = 0 := by
      intro a ha
      by_contra h2
      exact hcon a ⟨h2, ha⟩
    obtain ⟨t, ht⟩ := prop_of_ker d n p hp hd hn x y hx hy Lx Ly hLxdirac hLydirac hker
    exact hxy ⟨t, ht⟩
  have heya : ∃ a, Lx a = 0 ∧ Ly a ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    have hker : ∀ a, Lx a = 0 → Ly a = 0 := by
      intro a ha
      by_contra h2
      exact hcon a ⟨ha, h2⟩
    obtain ⟨t, ht⟩ := prop_of_ker d n p hp hd hn y x hy hx Ly Lx hLydirac hLxdirac hker
    have ht0 : t ≠ 0 := by
      intro h0
      have hc := congrFun ht 0
      simp only [Pi.smul_apply, smul_eq_mul, h0, zero_mul] at hc
      exact hx 0 hc
    refine hxy ⟨t⁻¹, ?_⟩
    rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  set φ : (Work.HP.Mon d n → ZMod p) →ₗ[ZMod p] (ZMod p × ZMod p) := Lx.prod Ly with hφ
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a₁, ha₁, hb₁⟩ := hexa
    obtain ⟨a₂, ha₂, hb₂⟩ := heya
    refine ⟨(w.1 * (Lx a₁)⁻¹) • a₁ + (w.2 * (Ly a₂)⁻¹) • a₂, ?_⟩
    have hc1 : Lx ((w.1 * (Lx a₁)⁻¹) • a₁ + (w.2 * (Ly a₂)⁻¹) • a₂) = w.1 := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ha₂, mul_zero, add_zero,
        mul_assoc, inv_mul_cancel₀ ha₁, mul_one]
    have hc2 : Ly ((w.1 * (Lx a₁)⁻¹) • a₁ + (w.2 * (Ly a₂)⁻¹) • a₂) = w.2 := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hb₁, mul_zero, zero_add,
        mul_assoc, inv_mul_cancel₀ hb₂, mul_one]
    exact Prod.ext hc1 hc2
  have hkerNat : Nat.card ↥(LinearMap.ker φ) = p ^ (Work.HP.NN d n - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker φ)), Nat.card_zmod]
    congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank (ZMod p) ↥(LinearMap.range φ) = 2 := by
      rw [LinearMap.range_eq_top.mpr hsurj]
      have h3 : Module.finrank (ZMod p) ↥(⊤ : Submodule (ZMod p) (ZMod p × ZMod p))
          = Module.finrank (ZMod p) (ZMod p × ZMod p) :=
        (Submodule.eq_top_iff_finrank_eq (W := ⊤)).mp rfl
      rw [h3, Module.finrank_prod, Module.finrank_self]
    have h4 : Module.finrank (ZMod p) (Work.HP.Mon d n → ZMod p) = Work.HP.NN d n :=
      Module.finrank_fintype_fun_eq_card (ZMod p)
    omega
  have hset : ({a : Work.HP.Mon d n → ZMod p |
      Work.HP.formEvalZMod d n p a x = 0 ∧ Work.HP.formEvalZMod d n p a y = 0} :
      Set (Work.HP.Mon d n → ZMod p)) = (φ.ker : Set (Work.HP.Mon d n → ZMod p)) := by
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hφ]
    rw [show (Lx.prod Ly) a = (Lx a, Ly a) from rfl,
      show (0 : ZMod p × ZMod p) = (0, 0) from rfl, Prod.mk.injEq, hLxapp, hLyapp]
  rw [hset, Work.HP.ncard_coe_submodule, hkerNat]

end Work.HP.badclass
