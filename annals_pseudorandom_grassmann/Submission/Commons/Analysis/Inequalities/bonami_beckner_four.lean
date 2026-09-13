import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Inequalities.two_point_four
import Submission.Commons.Analysis.Inequalities.finset_lp_minkowski

open Finset BigOperators

namespace Commons.Analysis.Inequalities

noncomputable section

private def kern (ρ : ℝ) (c d : ZMod 2) : ℝ := if d = c then (1 + ρ) / 2 else (1 - ρ) / 2

@[simp] private lemma kern_self (ρ : ℝ) (c : ZMod 2) : kern ρ c c = (1 + ρ) / 2 := by rw [kern, if_pos rfl]
private lemma kern_of_ne (ρ : ℝ) {c d : ZMod 2} (h : d ≠ c) : kern ρ c d = (1 - ρ) / 2 := by rw [kern, if_neg h]
private lemma kern_01 (ρ : ℝ) : kern ρ 0 1 = (1 - ρ) / 2 := by
  rw [kern_of_ne]; exact fun h => by norm_num at h
private lemma kern_10 (ρ : ℝ) : kern ρ 1 0 = (1 - ρ) / 2 := by
  rw [kern_of_ne]; exact fun h => by norm_num at h
private lemma kern_00 (ρ : ℝ) : kern ρ 0 0 = (1 + ρ) / 2 := kern_self ..
private lemma kern_11 (ρ : ℝ) : kern ρ 1 1 = (1 + ρ) / 2 := kern_self ..

private abbrev consv {n : ℕ} (c : ZMod 2) (x' : Fin n → ZMod 2) : Fin (n+1) → ZMod 2 := Fin.cons c x'

private def noise (n : ℕ) (ρ : ℝ) {ι : Type*} [Fintype ι] (f : (Fin n → ZMod 2) → ι → ℝ) :
    (Fin n → ZMod 2) → ι → ℝ :=
  fun x j => ∑ y : Fin n → ZMod 2, (∏ i : Fin n, kern ρ (x i) (y i)) * f y j

private def NSq {ι : Type*} [Fintype ι] (g : ι → ℝ) : ℝ := ∑ j, (g j) ^ 2

private lemma sum_zmod2 {M : Type*} [AddCommMonoid M] (G : ZMod 2 → M) :
    ∑ d : ZMod 2, G d = G 0 + G 1 := by
  have h := Equiv.sum_comp (ZMod.finEquiv 2).toEquiv G
  rw [← h, Fin.sum_univ_two]; simp

private lemma sum_cons (n : ℕ) (F : (Fin (n+1) → ZMod 2) → ℝ) :
    ∑ x : Fin (n+1) → ZMod 2, F x
      = ∑ c : ZMod 2, ∑ x' : Fin n → ZMod 2, F (consv c x') := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => ZMod 2)) F]
  rw [Fintype.sum_prod_type]
  rfl

private lemma prod_kern_cons (ρ : ℝ) {n : ℕ} (c d : ZMod 2) (x' y' : Fin n → ZMod 2) :
    (∏ i : Fin (n+1), kern ρ ((consv c x') i) ((consv d y') i))
      = kern ρ c d * ∏ i : Fin n, kern ρ (x' i) (y' i) := by
  rw [Fin.prod_univ_succ]; simp [consv]

private lemma noise_cons (n : ℕ) (ρ : ℝ) {ι : Type*} [Fintype ι]
    (f : (Fin (n+1) → ZMod 2) → ι → ℝ) (c : ZMod 2) (x' : Fin n → ZMod 2) (j : ι) :
    noise (n+1) ρ f (consv c x') j
      = kern ρ c 0 * noise n ρ (fun z j' => f (consv 0 z) j') x' j
        + kern ρ c 1 * noise n ρ (fun z j' => f (consv 1 z) j') x' j := by
  simp only [noise]
  rw [sum_cons (n := n) (F := fun y => (∏ i : Fin (n+1), kern ρ ((consv c x') i) (y i)) * f y j)]
  simp_rw [prod_kern_cons]
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [sum_zmod2]

private lemma noise_cons_fun (n : ℕ) (ρ : ℝ) {ι : Type*} [Fintype ι]
    (f : (Fin (n+1) → ZMod 2) → ι → ℝ) (c : ZMod 2) (z : Fin n → ZMod 2) :
    noise (n+1) ρ f (consv c z)
      = fun j => kern ρ c 0 * noise n ρ (fun z' j' => f (consv 0 z') j') z j
          + kern ρ c 1 * noise n ρ (fun z' j' => f (consv 1 z') j') z j := by
  funext j; exact noise_cons n ρ f c z j

private lemma noise_pair (n : ℕ) (ρ : ℝ) {ι : Type*} [Fintype ι]
    (f : (Fin (n+1) → ZMod 2) → ι → ℝ) (z : Fin n → ZMod 2) (j : ι) (c : ZMod 2) :
    noise n ρ (fun z' p => f (consv p.2 z') p.1) z (j, c)
      = noise n ρ (fun z' j' => f (consv c z') j') z j := by
  simp only [noise]

private lemma Ns_quad {ι : Type*} [Fintype ι] (a b : ℝ) (u v : ι → ℝ) :
    ∑ j, (a * u j + b * v j) ^ 2
      = a^2 * (∑ j, u j ^ 2) + (2 * (a*b)) * (∑ j, u j * v j) + b^2 * (∑ j, v j ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma arith (ρ α β γ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (hcs : β ^ 2 ≤ α * γ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    (α + 2*ρ*β + ρ^2*γ)^2 + (α - 2*ρ*β + ρ^2*γ)^2 ≤ (2*(α+γ))^2 / 2 := by
  have hρ4 : ρ^4 ≤ 1 := by nlinarith [sq_nonneg ρ, hρ]
  have hkey : (α+ρ^2*γ)^2 + 4*ρ^2*(α*γ) ≤ (α+γ)^2 := by
    have hid : (α+γ)^2 - ((α+ρ^2*γ)^2 + 4*ρ^2*(α*γ))
        = (2 - 6*ρ^2)*(α*γ) + (1-ρ^4)*γ^2 := by ring
    have hb1 : 0 ≤ 2 - 6*ρ^2 := by nlinarith
    have hb2 : 0 ≤ 1 - ρ^4 := by nlinarith
    have hnn : 0 ≤ (2-6*ρ^2)*(α*γ) + (1-ρ^4)*γ^2 := by
      apply add_nonneg
      · exact mul_nonneg hb1 (mul_nonneg hα hγ)
      · exact mul_nonneg hb2 (sq_nonneg γ)
    linarith [hid]
  have h1 : (α + 2*ρ*β + ρ^2*γ)^2 + (α - 2*ρ*β + ρ^2*γ)^2
      = 2*(α+ρ^2*γ)^2 + 8*ρ^2*β^2 := by ring
  have hstep : 8*ρ^2*β^2 ≤ 8*ρ^2*(α*γ) := by nlinarith [hcs, sq_nonneg ρ]
  calc (α + 2*ρ*β + ρ^2*γ)^2 + (α - 2*ρ*β + ρ^2*γ)^2
      = 2*(α+ρ^2*γ)^2 + 8*ρ^2*β^2 := h1
    _ ≤ 2*(α+ρ^2*γ)^2 + 8*ρ^2*(α*γ) := by linarith [hstep]
    _ = 2*((α+ρ^2*γ)^2 + 4*ρ^2*(α*γ)) := by ring
    _ ≤ 2*(α+γ)^2 := by linarith [hkey]
    _ = (2*(α+γ))^2/2 := by ring

private lemma vec_two_point {ι : Type*} [Fintype ι] (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3)
    (u v : ι → ℝ) :
    (∑ j, (((1 + ρ) / 2) * u j + ((1 - ρ) / 2) * v j) ^ 2) ^ 2
      + (∑ j, (((1 - ρ) / 2) * u j + ((1 + ρ) / 2) * v j) ^ 2) ^ 2
    ≤ (∑ j, u j ^ 2 + ∑ j, v j ^ 2) ^ 2 / 2 := by
  set mm : ι → ℝ := fun j => (u j + v j) / 2 with hmm
  set zz : ι → ℝ := fun j => (u j - v j) / 2 with hzz
  set α : ℝ := ∑ j, mm j ^ 2 with hα
  set β : ℝ := ∑ j, mm j * zz j with hβ
  set γ : ℝ := ∑ j, zz j ^ 2 with hγ
  have hAc : ∀ j, (((1 + ρ) / 2) * u j + ((1 - ρ) / 2) * v j) = mm j + ρ * zz j := by
    intro j; simp only [hmm, hzz]; ring
  have hBc : ∀ j, (((1 - ρ) / 2) * u j + ((1 + ρ) / 2) * v j) = mm j + (-ρ) * zz j := by
    intro j; simp only [hmm, hzz]; ring
  have hA : ∑ j, (((1 + ρ) / 2) * u j + ((1 - ρ) / 2) * v j) ^ 2 = α + 2*ρ*β + ρ^2*γ := by
    simp only [hAc]
    have hq := Ns_quad (1:ℝ) ρ mm zz
    simp only [one_mul, one_pow] at hq
    rw [hq, ← hα, ← hβ, ← hγ]; try ring
  have hB : ∑ j, (((1 - ρ) / 2) * u j + ((1 + ρ) / 2) * v j) ^ 2 = α - 2*ρ*β + ρ^2*γ := by
    simp only [hBc]
    have hq := Ns_quad (1:ℝ) (-ρ) mm zz
    simp only [one_mul, one_pow] at hq
    rw [hq, ← hα, ← hβ, ← hγ]; try ring
  have hu : ∑ j, u j ^ 2 = α + 2*β + γ := by
    have hc : ∀ j, u j = mm j + zz j := by intro j; simp only [hmm, hzz]; ring
    simp only [hc]
    have hq := Ns_quad (1:ℝ) 1 mm zz
    simp only [one_mul, one_pow] at hq
    rw [hq, ← hα, ← hβ, ← hγ]; try ring
  have hv : ∑ j, v j ^ 2 = α - 2*β + γ := by
    have hc : ∀ j, v j = mm j + (-1) * zz j := by intro j; simp only [hmm, hzz]; ring
    simp only [hc]
    have hq := Ns_quad (1:ℝ) (-1) mm zz
    simp only [one_mul, one_pow] at hq
    rw [hq, ← hα, ← hβ, ← hγ]; try ring
  have hcs : β ^ 2 ≤ α * γ := by
    rw [hβ, hα, hγ]
    simpa using sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) mm zz
  have hαnn : 0 ≤ α := by rw [hα]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hγnn : 0 ≤ γ := by rw [hγ]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [hA, hB, hu, hv]
  have hsum : α + 2*β + γ + (α - 2*β + γ) = 2*(α+γ) := by ring
  rw [hsum]
  exact arith ρ α β γ hρ hcs hαnn hγnn

private theorem bb_vec (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) : ∀ (n : ℕ) {ι : Type*} [Fintype ι]
    (f : (Fin n → ZMod 2) → ι → ℝ),
    (2 : ℝ) ^ n * (∑ x : Fin n → ZMod 2, (NSq (noise n ρ f x)) ^ 2)
      ≤ (∑ x : Fin n → ZMod 2, NSq (f x)) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro ι _ f
    have hnoise : noise 0 ρ f = f := by
      funext x j
      simp only [noise]
      rw [Fintype.sum_subsingleton (fun y => (∏ i : Fin 0, kern ρ (x i) (y i)) * f y j) x]
      simp
    rw [hnoise, pow_zero, one_mul]
    rw [Fintype.sum_subsingleton (fun x : Fin 0 → ZMod 2 => (NSq (f x)) ^ 2) default]
    rw [Fintype.sum_subsingleton (fun x : Fin 0 → ZMod 2 => NSq (f x)) default]
  | succ n ih =>
    intro ι _ f
    let a : (Fin n → ZMod 2) → ι → ℝ := fun z j => f (consv 0 z) j
    let b : (Fin n → ZMod 2) → ι → ℝ := fun z j => f (consv 1 z) j
    let w : (Fin n → ZMod 2) → (ι × ZMod 2) → ℝ := fun z p => f (consv p.2 z) p.1
    have hab : a = fun z j => w z (j, 0) := rfl
    have hbb : b = fun z j => w z (j, 1) := rfl
    have hAB : ∀ z : Fin n → ZMod 2,
        (NSq (noise (n+1) ρ f (consv 0 z)))^2 + (NSq (noise (n+1) ρ f (consv 1 z)))^2
          ≤ (NSq (noise n ρ a z) + NSq (noise n ρ b z))^2 / 2 := by
      intro z
      rw [noise_cons_fun n ρ f 0 z, noise_cons_fun n ρ f 1 z]
      simp only [kern_00, kern_01, kern_10, kern_11]
      exact vec_two_point ρ hρ (noise n ρ a z) (noise n ρ b z)
    have hC : ∀ z : Fin n → ZMod 2,
        NSq (noise n ρ a z) + NSq (noise n ρ b z) = NSq (noise n ρ w z) := by
      intro z
      simp only [NSq]
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_zmod2]
      rw [noise_pair n ρ f z j 0, noise_pair n ρ f z j 1]
    have hW : ∑ x : Fin (n+1) → ZMod 2, (NSq (noise (n+1) ρ f x))^2
        = ∑ z : Fin n → ZMod 2,
            ((NSq (noise (n+1) ρ f (consv 0 z)))^2 + (NSq (noise (n+1) ρ f (consv 1 z)))^2) := by
      rw [sum_cons (n := n) (F := fun x => (NSq (noise (n+1) ρ f x))^2)]
      rw [sum_zmod2]
      rw [← Finset.sum_add_distrib]
    have hstep : ∑ z : Fin n → ZMod 2,
            ((NSq (noise (n+1) ρ f (consv 0 z)))^2 + (NSq (noise (n+1) ρ f (consv 1 z)))^2)
        ≤ (1/2) * ∑ z : Fin n → ZMod 2, (NSq (noise n ρ w z))^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z _
      calc (NSq (noise (n+1) ρ f (consv 0 z)))^2 + (NSq (noise (n+1) ρ f (consv 1 z)))^2
          ≤ (NSq (noise n ρ a z) + NSq (noise n ρ b z))^2 / 2 := hAB z
        _ = (1/2) * (NSq (noise n ρ w z))^2 := by rw [hC z]; ring
    have hw : ∀ z : Fin n → ZMod 2,
        NSq (w z) = NSq (f (consv 0 z)) + NSq (f (consv 1 z)) := by
      intro z
      simp only [NSq]
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_zmod2]
    have hE : ∑ z : Fin n → ZMod 2, NSq (w z)
        = ∑ x : Fin (n+1) → ZMod 2, NSq (f x) := by
      simp_rw [hw]
      rw [Finset.sum_add_distrib]
      rw [sum_cons (n := n) (F := fun x => NSq (f x)), sum_zmod2]
    have hIH := ih (ι := ι × ZMod 2) w
    calc (2 : ℝ) ^ (n+1) * (∑ x : Fin (n+1) → ZMod 2, (NSq (noise (n+1) ρ f x))^2)
        = (2 : ℝ) ^ (n+1) * (∑ z : Fin n → ZMod 2,
            ((NSq (noise (n+1) ρ f (consv 0 z)))^2 + (NSq (noise (n+1) ρ f (consv 1 z)))^2)) := by
              rw [hW]
      _ ≤ (2 : ℝ) ^ (n+1) * ((1/2) * ∑ z : Fin n → ZMod 2, (NSq (noise n ρ w z))^2) := by
              exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (2 : ℝ) ^ n * ∑ z : Fin n → ZMod 2, (NSq (noise n ρ w z))^2 := by rw [pow_succ]; ring
      _ ≤ (∑ z : Fin n → ZMod 2, NSq (w z))^2 := hIH
      _ = (∑ x : Fin (n+1) → ZMod 2, NSq (f x))^2 := by rw [hE]


theorem bonami_beckner_four (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3)
    (f : (Fin n → ZMod 2) → ℝ) :
    (2 : ℝ) ^ n *
        (∑ x : Fin n → ZMod 2,
          ((∑ y : Fin n → ZMod 2,
            (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) * f y) ^ 4))
      ≤ (∑ x : Fin n → ZMod 2, f x ^ 2) ^ 2 := by
  have h := bb_vec ρ hρ n (ι := Fin 1) (fun x _ => f x)
  simp only [NSq, noise, kern, Fin.sum_univ_one, ← pow_mul, Nat.reduceMul] at h
  exact h

end
end Commons.Analysis.Inequalities