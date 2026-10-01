import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.weil_bound_poly
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_product_poly_weil
import Submission.Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow
import Submission.Commons.Combinatorics.Counting.card_fin_fun_sum_le

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

lemma sum_Ioc_eq_sum_fin (p H : ℕ) (f : ZMod p → ℂ) (m : ℕ) :
    ∑ h ∈ Finset.Ioc m (m + H), f (h : ZMod p)
      = ∑ j : Fin H, f ((m : ZMod p) + ((((j : ℕ) + 1 : ℕ)) : ZMod p)) := by
  have himg : Finset.Ioc m (m + H) = (Finset.range H).image (fun j => m + 1 + j) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨x - (m+1), by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
  have hinj : Set.InjOn (fun j => m + 1 + j) ↑(Finset.range H) := by
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  rw [himg, Finset.sum_image hinj]
  rw [Fin.sum_univ_eq_sum_range (fun j => f ((m : ZMod p) + (((j + 1 : ℕ)) : ZMod p))) H]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  ring

lemma zmod_sum_range_eq (p : ℕ) [NeZero p] (f : ZMod p → ℂ) :
    ∑ m ∈ Finset.range p, f (m : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij (fun m _ => (m : ZMod p)) ?_ ?_ ?_ ?_
  · intro m hm; exact Finset.mem_univ _
  · intro m1 hm1 m2 hm2 h
    rw [Finset.mem_range] at hm1 hm2
    have hmod : m1 % p = m2 % p := (ZMod.natCast_eq_natCast_iff m1 m2 p).mp h
    rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro m hm; rfl

lemma chi_pow_pred_eq_conj {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hm : 2 ≤ orderOf χ) (y : ZMod p) :
    χ y ^ (orderOf χ - 1) = (starRingEnd ℂ) (χ y) := by
  have hm1 : orderOf χ - 1 ≠ 0 := by omega
  rcases eq_or_ne y 0 with rfl | hy
  · rw [MulChar.map_zero, zero_pow hm1]
    exact (map_zero (starRingEnd ℂ)).symm
  · have hunit : IsUnit y := isUnit_iff_ne_zero.mpr hy
    have hpow1 : (χ y) ^ orderOf χ = 1 := by
      have hp : χ ^ orderOf χ = (1 : DirichletCharacter ℂ p) := pow_orderOf_eq_one χ
      have h2 : (χ ^ orderOf χ) y = 1 := by rw [hp, MulChar.one_apply hunit]
      rwa [MulChar.pow_apply' χ (by omega : orderOf χ ≠ 0) y] at h2
    have hconj : (starRingEnd ℂ) (χ y) = (χ y)⁻¹ := by
      rw [show (starRingEnd ℂ) (χ y) = star (χ y) from rfl, MulChar.star_apply' χ y,
        MulChar.inv_apply_eq_inv' χ y]
    have hpow : χ y ^ (orderOf χ - 1) = (χ y)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (orderOf_pos χ), hpow1]
    rw [hpow, hconj]

lemma chi_mul_conj_eq (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hm : 2 ≤ orderOf χ) (f g : Polynomial (ZMod p)) (x : ZMod p) :
    χ (f.eval x) * (starRingEnd ℂ) (χ (g.eval x))
      = χ ((f * g ^ (orderOf χ - 1)).eval x) := by
  rw [Polynomial.eval_mul, Polynomial.eval_pow, map_mul, map_pow]
  rw [chi_pow_pred_eq_conj χ hm (g.eval x)]

noncomputable def Pf (p H r : ℕ) (f : Fin r → Fin H) : Polynomial (ZMod p) :=
  ∏ i, (Polynomial.X + Polynomial.C ((((f i : ℕ) + 1 : ℕ)) : ZMod p))

lemma Pf_monic (p H r : ℕ) (f : Fin r → Fin H) : (Pf p H r f).Monic := by
  unfold Pf
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact Polynomial.monic_X_add_C _

lemma Pf_natDegree (p : ℕ) [Fact p.Prime] (H r : ℕ) (f : Fin r → Fin H) :
    (Pf p H r f).natDegree = r := by
  unfold Pf
  rw [Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_X_add_C]
    simp
  · intro i _
    exact (Polynomial.monic_X_add_C _).ne_zero

lemma Pf_ne_zero (p : ℕ) [Fact p.Prime] (H r : ℕ) (f : Fin r → Fin H) : Pf p H r f ≠ 0 :=
  (Pf_monic p H r f).ne_zero

lemma S_pow_eq (p H r : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (m : ℕ) :
    (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r
      = ∑ f : Fin r → Fin H, χ ((Pf p H r f).eval (m : ZMod p)) := by
  rw [sum_Ioc_eq_sum_fin]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  rw [← map_prod]
  congr 1
  unfold Pf
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

lemma S_conj_pow_eq (p H r : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (m : ℕ) :
    (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r)
      = ∑ g : Fin r → Fin H, (starRingEnd ℂ) (χ ((Pf p H r g).eval (m : ZMod p))) := by
  rw [S_pow_eq, map_sum]

lemma Smulconj_eq (p H r : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (m : ℕ) :
    (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r *
      (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r)
      = ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H,
          χ ((Pf p H r f).eval (m : ZMod p)) *
            (starRingEnd ℂ) (χ ((Pf p H r g).eval (m : ZMod p))) := by
  rw [S_conj_pow_eq, S_pow_eq, Finset.sum_mul_sum]

/-! ## Value map injectivity -/

lemma val_injective (p H : ℕ) [NeZero p] (hHp : H ≤ p) :
    Function.Injective (fun j : Fin H => ((((j : ℕ) + 1 : ℕ)) : ZMod p)) := by
  intro u v huv
  have hu : (u : ℕ) + 1 ≤ p := by have := u.isLt; omega
  have hv : (v : ℕ) + 1 ≤ p := by have := v.isLt; omega
  have hmod : ((u : ℕ) + 1) % p = ((v : ℕ) + 1) % p :=
    (ZMod.natCast_eq_natCast_iff ((u:ℕ)+1) ((v:ℕ)+1) p).mp huv
  have hkey : (u : ℕ) + 1 = (v : ℕ) + 1 := by
    rcases lt_or_eq_of_le hu with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hmod
      rcases lt_or_eq_of_le hv with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at hmod; omega
      · rw [h2, Nat.mod_self] at hmod; omega
    · rw [h1, Nat.mod_self] at hmod
      rcases lt_or_eq_of_le hv with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at hmod; omega
      · omega
  exact Fin.ext (by omega)

/-! ## The good and bad estimates -/

lemma norm_T_le_bad {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (H r : ℕ)
    (f g : Fin r → Fin H) :
    ‖∑ x : ZMod p, χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)‖ ≤ (p : ℝ) := by
  calc ‖∑ x : ZMod p, χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)‖
      ≤ ∑ x : ZMod p, ‖χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x : ZMod p, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => DirichletCharacter.norm_le_one χ _)
    _ = (p : ℝ) := by rw [Finset.sum_const, Finset.card_univ, ZMod.card]; simp

lemma norm_T_le_good {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (H r : ℕ) (hr : 1 ≤ r) (f g : Fin r → Fin H)
    (hgood : ¬ ∃ c : ZMod p, ∃ Q : Polynomial (ZMod p),
       Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1) = Polynomial.C c * Q ^ (orderOf χ)) :
    ‖∑ x : ZMod p, χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)‖
      ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hF0 : Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1) ≠ 0 :=
    mul_ne_zero (Pf_ne_zero p H r f) (pow_ne_zero _ (Pf_ne_zero p H r g))
  have hdeg : (Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).natDegree
      = r + (orderOf χ - 1) * r := by
    rw [Polynomial.natDegree_mul (Pf_ne_zero p H r f) (pow_ne_zero _ (Pf_ne_zero p H r g)),
      Polynomial.natDegree_pow, Pf_natDegree, Pf_natDegree]
  have hd : 1 ≤ (Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).natDegree := by
    rw [hdeg]; nlinarith [Nat.zero_le (orderOf χ - 1), hr]
  have hnd : ∀ (c : ZMod p) (Q : Polynomial (ZMod p)),
      Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1) ≠ Polynomial.C c * Q ^ (orderOf χ) :=
    fun c Q h => hgood ⟨c, Q, h⟩
  have hb := weil_bound_poly p χ hχ _ hF0 hd hnd
  have hcard : ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).rootSet
        (AlgebraicClosure (ZMod p))).ncard ≤ 2 * r := by
    have h := ncard_rootSet_mul_pow_le p (Pf p H r f) (Pf p H r g) (orderOf χ - 1) (by omega)
    rw [Pf_natDegree p H r f, Pf_natDegree p H r g] at h
    omega
  have hcardR : (((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).rootSet
        (AlgebraicClosure (ZMod p))).ncard : ℝ) ≤ (2 * r : ℝ) := by
    exact_mod_cast hcard
  calc ‖∑ x : ZMod p, χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)‖
      ≤ (((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).rootSet
          (AlgebraicClosure (ZMod p))).ncard : ℝ) * Real.sqrt (p : ℝ) := hb
    _ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) :=
        mul_le_mul_of_nonneg_right hcardR (Real.sqrt_nonneg _)

lemma congruent_of_bad {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (H r : ℕ) (hHp : H ≤ p) (f g : Fin r → Fin H)
    (hbad : ∃ c : ZMod p, ∃ Q : Polynomial (ZMod p),
       Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1) = Polynomial.C c * Q ^ (orderOf χ)) :
    ∀ j : Fin H, (Finset.univ.filter (fun i => f i = j)).card % orderOf χ
               = (Finset.univ.filter (fun i => g i = j)).card % orderOf χ := by
  obtain ⟨c, Q, hQ⟩ := hbad
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hmain := Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow (K := ZMod p) hm2
      (a := fun i : Fin r => ((((f i : ℕ) + 1 : ℕ)) : ZMod p))
      (b := fun i : Fin r => ((((g i : ℕ) + 1 : ℕ)) : ZMod p)) (c := c) (Q := Q)
      (by simpa only [Pf] using hQ)
  intro j
  have hj := hmain ((((j : ℕ) + 1 : ℕ)) : ZMod p)
  have e1 : (Finset.univ.filter (fun i : Fin r =>
        ((((f i : ℕ) + 1 : ℕ)) : ZMod p) = ((((j : ℕ) + 1 : ℕ)) : ZMod p)))
      = (Finset.univ.filter (fun i : Fin r => f i = j)) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h; exact val_injective p H hHp h
    · intro h; rw [h]
  have e2 : (Finset.univ.filter (fun i : Fin r =>
        ((((g i : ℕ) + 1 : ℕ)) : ZMod p) = ((((j : ℕ) + 1 : ℕ)) : ZMod p)))
      = (Finset.univ.filter (fun i : Fin r => g i = j)) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h; exact val_injective p H hHp h
    · intro h; rw [h]
  rw [e1, e2] at hj
  exact hj

/-! ## Assembly -/

lemma pow_mul_conj_pow (z : ℂ) (n : ℕ) :
    z ^ n * (starRingEnd ℂ) (z ^ n) = ((‖z‖ ^ (2 * n) : ℝ) : ℂ) := by
  have h : z ^ n * (starRingEnd ℂ) (z ^ n) = (z * (starRingEnd ℂ) z) ^ n := by
    rw [map_pow]; ring
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [pow_mul]

lemma norm_ofReal_complex (y : ℝ) : ‖((y : ℝ) : ℂ)‖ = |y| := by
  have h : ‖((y : ℝ) : ℂ)‖ ^ 2 = y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

lemma sum_norm_eq_norm_sum {p : ℕ} [NeZero p] (S : ℕ → ℂ) (r : ℕ) :
    (∑ m ∈ Finset.range p, ‖S m‖ ^ (2 * r))
      = ‖∑ m ∈ Finset.range p, S m ^ r * (starRingEnd ℂ) (S m ^ r)‖ := by
  have h : (∑ m ∈ Finset.range p, S m ^ r * (starRingEnd ℂ) (S m ^ r))
      = ((∑ m ∈ Finset.range p, ‖S m‖ ^ (2 * r) : ℝ) : ℂ) := by
    trans ∑ m ∈ Finset.range p, ((‖S m‖ ^ (2 * r) : ℝ) : ℂ)
    · apply Finset.sum_congr rfl; intro m _
      exact pow_mul_conj_pow (S m) r
    · exact (Complex.ofReal_sum (s := Finset.range p) (f := fun m => ‖S m‖ ^ (2 * r))).symm
  rw [h, norm_ofReal_complex]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun m _ => by positivity))]

noncomputable def Tg (p H r : ℕ) [NeZero p] (χ : DirichletCharacter ℂ p) (f g : Fin r → Fin H) : ℂ :=
  ∑ x : ZMod p, χ ((Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1)).eval x)

lemma Z_eq (p H r : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    (∑ m ∈ Finset.range p, (∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r *
        (starRingEnd ℂ) ((∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) ^ r))
      = ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tg p H r χ f g := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  simp_rw [Smulconj_eq p H r χ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro f _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro g _
  simp only [Tg]
  simp_rw [chi_mul_conj_eq p χ hm2 (Pf p H r f) (Pf p H r g)]
  exact zmod_sum_range_eq p (fun z : ZMod p =>
    χ (Polynomial.eval z (Pf p H r f * (Pf p H r g) ^ (orderOf χ - 1))))

def Good (p H r : ℕ) (χ : DirichletCharacter ℂ p) (fg : (Fin r → Fin H) × (Fin r → Fin H)) : Prop :=
  ¬ ∃ c : ZMod p, ∃ Q : Polynomial (ZMod p),
      Pf p H r fg.1 * (Pf p H r fg.2) ^ (orderOf χ - 1) = Polynomial.C c * Q ^ (orderOf χ)


namespace BurgessMoment


/-- multiplicity of the value `c` in `f`. -/
def Mf {r n : ℕ} (f : Fin r → Fin n) (c : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => f i = c)).card

lemma sum_Mf {r n : ℕ} (f : Fin r → Fin n) : ∑ c, Mf (f := f) c = r := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin r)))
      (t := (Finset.univ : Finset (Fin n))) (f := f) (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa only [Mf] using h.symm

/-- multiplicity vector of `f` reduced mod `m`. -/
def Sig {r n : ℕ} (m : ℕ) (f : Fin r → Fin n) (c : Fin n) : ℕ := Mf (f := f) c % m

lemma sum_Sig {r n m : ℕ} (f : Fin r → Fin n) : ∑ c, Sig m f c = r - m * ∑ c, Mf (f := f) c / m := by
  have h1 : ∑ c, Mf (f := f) c = r := sum_Mf f
  have h2 : ∀ c, Mf (f := f) c = m * (Mf (f := f) c / m) + Sig m f c := by
    intro c
    simp only [Sig]
    exact (Nat.div_add_mod (Mf (f := f) c) m).symm
  have h3 : ∑ c, Mf (f := f) c
      = m * (∑ c, Mf (f := f) c / m) + ∑ c, Sig m f c := by
    rw [Finset.sum_congr rfl (fun c _ => h2 c), Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1] at h3
  omega

/-- The number of functions `Fin r → Fin n` with a prescribed multiplicity vector `τ` is at
most `r ^ r` (the support of `τ` has at most `r` elements). -/
lemma fiber_le {r n : ℕ} (τ : Fin n → ℕ) (hτ : ∑ c, τ c ≤ r) :
    (Finset.univ.filter (fun f : Fin r → Fin n => ∀ c, Mf (f := f) c = τ c)).card ≤ r ^ r := by
  classical
  set s : Finset (Fin n) := Finset.univ.filter (fun c => τ c ≠ 0) with hs
  have hscard : s.card ≤ r := by
    have h1 : ∑ c ∈ s, τ c = ∑ c, τ c := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c _ hc
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact not_not.mp hc
    have h2 : s.card ≤ ∑ c ∈ s, τ c := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro c hc
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      omega
    omega
  have hinj : Function.Injective
      (fun f : {f : Fin r → Fin n // ∀ c, Mf (f := f) c = τ c} =>
        (fun i => (⟨f.1 i, by
          have h1 : 1 ≤ Mf (f := f.1) (f.1 i) := by
            rw [Mf]; exact Finset.card_pos.mpr ⟨i, by simp⟩
          have h2 : Mf (f := f.1) (f.1 i) = τ (f.1 i) := f.2 (f.1 i)
          simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
          omega⟩ : {c // c ∈ s}))) := by
    intro f g hfg
    apply Subtype.ext
    funext i
    exact Subtype.ext_iff.mp (congrFun hfg i)
  have hcardeq : (Finset.univ.filter (fun f : Fin r → Fin n => ∀ c, Mf (f := f) c = τ c)).card
      = Fintype.card {f : Fin r → Fin n // ∀ c, Mf (f := f) c = τ c} := by
    rw [Fintype.card_subtype]
  rw [hcardeq]
  calc Fintype.card {f : Fin r → Fin n // ∀ c, Mf (f := f) c = τ c}
      ≤ Fintype.card (Fin r → {c // c ∈ s}) := Fintype.card_le_of_injective _ hinj
    _ = s.card ^ r := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    _ ≤ r ^ r := Nat.pow_le_pow_left hscard r

lemma beta_card_le (n I : ℕ) :
    (Finset.univ.filter (fun β : Fin n → Fin (I+1) => ∑ i, (β i : ℕ) = I)).card ≤ n ^ I := by
  rw [← Fintype.card_subtype]
  exact Commons.Combinatorics.Counting.card_fin_fun_sum_le n I

/-- A bound for the cardinality of a set of functions `Fin n → Fin m` with prescribed sum. -/
lemma card_pattern_le (n A m : ℕ) :
    (Finset.univ.filter (fun S : Fin n → Fin m => ∑ c, (S c : ℕ) = A)).card ≤ n ^ A := by
  classical
  let φ : {S : Fin n → Fin m // ∑ c, (S c : ℕ) = A} →
      {β : Fin n → Fin (A+1) // ∑ c, (β c : ℕ) = A} :=
    fun S => ⟨fun c => ⟨(S.1 c : ℕ), by
        have h : (S.1 c : ℕ) ≤ ∑ c', (S.1 c' : ℕ) :=
          Finset.single_le_sum (f := fun c' => (S.1 c' : ℕ)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ c)
        omega⟩, by
      show ∑ c, (S.1 c : ℕ) = A
      exact S.2⟩
  have hinj : Function.Injective φ := by
    intro S T hST
    apply Subtype.ext
    funext c
    have h := congrFun (congrArg Subtype.val hST) c
    have h2 : (S.1 c : ℕ) = (T.1 c : ℕ) := by
      have := congrArg (fun x : Fin (A+1) => (x : ℕ)) h
      simpa using this
    exact Fin.ext h2
  have hcardeq : (Finset.univ.filter (fun S : Fin n → Fin m => ∑ c, (S c : ℕ) = A)).card
      = Fintype.card {S : Fin n → Fin m // ∑ c, (S c : ℕ) = A} := by
    rw [Fintype.card_subtype]
  rw [hcardeq]
  exact (Fintype.card_le_of_injective φ hinj).trans
    (Commons.Combinatorics.Counting.card_fin_fun_sum_le n A)

def Ac {r n : ℕ} (m : ℕ) (f : Fin r → Fin n) : ℕ := ∑ c, Mf (f := f) c % m

lemma Ac_le {r n m : ℕ} (f : Fin r → Fin n) : Ac m f ≤ r := by
  calc Ac m f = ∑ c, Mf (f := f) c % m := rfl
    _ ≤ ∑ c, Mf (f := f) c := Finset.sum_le_sum (fun c _ => Nat.mod_le _ _)
    _ = r := sum_Mf f

/-- The number of `f` realising a fixed residue pattern `S` is at most
`r ^ r` times the number of ways to distribute the `m`-blocks. -/
lemma fiber_res_le {r n m : ℕ} (hm : 2 ≤ m) (S : Fin n → Fin m) :
    (Finset.univ.filter (fun f : Fin r → Fin n => ∀ c, Mf (f := f) c % m = (S c : ℕ))).card
      ≤ r ^ r * n ^ ((r - ∑ c, (S c : ℕ)) / m) := by
  classical
  by_cases hAc : ∑ c, (S c : ℕ) ≤ r
  · set A : ℕ := ∑ c, (S c : ℕ) with hA
    set I : ℕ := (r - A) / m with hI
    set Fiber : Finset (Fin r → Fin n) :=
      Finset.univ.filter (fun f : Fin r → Fin n => ∀ c, Mf (f := f) c % m = (S c : ℕ)) with hFiber
    set Beta : Finset (Fin n → Fin (I+1)) :=
      Finset.univ.filter (fun β : Fin n → Fin (I+1) => ∑ c, (β c : ℕ) = I) with hBeta
    have hAle : A ≤ r := by omega
    have hsub : Fiber ⊆ Beta.biUnion (fun β => Finset.univ.filter (fun f : Fin r → Fin n =>
        ∀ c, Mf (f := f) c = (S c : ℕ) + m * (β c : ℕ))) := by
      intro f hf
      have hf' : ∀ c, Mf (f := f) c % m = (S c : ℕ) := (Finset.mem_filter.mp hf).2
      have hA' : ∑ c, Mf (f := f) c % m = A := by
        rw [hA]; exact Finset.sum_congr rfl (fun c _ => hf' c)
      have hdecomp : ∑ c, Mf (f := f) c = m * (∑ c, Mf (f := f) c / m) + A := by
        rw [Finset.sum_congr rfl (fun c _ => (Nat.div_add_mod (Mf (f := f) c) m).symm),
          Finset.sum_add_distrib, Finset.mul_sum, hA']
      have hsum : ∑ c, Mf (f := f) c = r := sum_Mf f
      have hdiv : ∑ c, Mf (f := f) c / m = I := by
        have hX : m * (∑ c, Mf (f := f) c / m) = r - A := by omega
        rw [hI]
        calc ∑ c, Mf (f := f) c / m
            = m * (∑ c, Mf (f := f) c / m) / m :=
              (Nat.mul_div_cancel_left _ (by omega : 0 < m)).symm
          _ = (r - A) / m := by rw [hX]
      let βf : Fin n → Fin (I+1) := fun c => ⟨Mf (f := f) c / m, by
        have h1 : Mf (f := f) c / m ≤ ∑ c', Mf (f := f) c' / m :=
          Finset.single_le_sum (f := fun c' => Mf (f := f) c' / m) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ c)
        omega⟩
      have hβmem : βf ∈ Beta := by
        rw [hBeta, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hdiv⟩
      rw [Finset.mem_biUnion]
      refine ⟨βf, hβmem, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro c
      have h3 : Mf (f := f) c = m * (Mf (f := f) c / m) + (S c : ℕ) := by
        rw [← hf' c]; exact (Nat.div_add_mod (Mf (f := f) c) m).symm
      show Mf (f := f) c = (S c : ℕ) + m * (βf c : ℕ)
      rw [h3, add_comm]
    have hstep1 : Fiber.card ≤ ∑ β ∈ Beta,
        (Finset.univ.filter (fun f : Fin r → Fin n =>
          ∀ c, Mf (f := f) c = (S c : ℕ) + m * (β c : ℕ))).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hstep2 : ∑ β ∈ Beta,
        (Finset.univ.filter (fun f : Fin r → Fin n =>
          ∀ c, Mf (f := f) c = (S c : ℕ) + m * (β c : ℕ))).card ≤ ∑ _β ∈ Beta, r ^ r := by
      apply Finset.sum_le_sum
      intro β hβ
      apply fiber_le
      have h2 : ∑ c, ((S c : ℕ) + m * (β c : ℕ)) = A + m * I := by
        have hSumS : ∑ c, (S c : ℕ) = A := hA.symm
        have hSumB : ∑ c, (β c : ℕ) = I := by
          rw [hBeta] at hβ
          exact (Finset.mem_filter.mp hβ).2
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hSumS, hSumB]
      rw [h2]
      have hmI : m * I ≤ r - A := by rw [hI]; exact Nat.mul_div_le _ _
      omega
    have hstep3 : ∑ _β ∈ Beta, r ^ r = Beta.card * r ^ r := by
      rw [Finset.sum_const, smul_eq_mul]
    have hBeta_le : Beta.card ≤ n ^ I := by
      rw [hBeta]; exact beta_card_le n I
    rw [hFiber]
    calc Fiber.card ≤ Beta.card * r ^ r := le_trans hstep1 (le_trans hstep2 hstep3.le)
      _ ≤ n ^ I * r ^ r := Nat.mul_le_mul_right _ hBeta_le
      _ = r ^ r * n ^ ((r - ∑ c, (S c : ℕ)) / m) := by rw [hI, mul_comm]
  · have hempty : (Finset.univ.filter (fun f : Fin r → Fin n =>
        ∀ c, Mf (f := f) c % m = (S c : ℕ))) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨f, hf⟩
      rw [Finset.mem_filter] at hf
      have hle : ∑ c, Mf (f := f) c % m ≤ r := Ac_le f
      have heq : ∑ c, Mf (f := f) c % m = ∑ c, (S c : ℕ) :=
        Finset.sum_congr rfl (fun c _ => hf.2 c)
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- The two orientations of the "congruent multiplicity" filter agree. -/
lemma filter_symm {r n m : ℕ} (f : Fin r → Fin n) :
    (Finset.univ.filter (fun g : Fin r → Fin n => ∀ c, Mf (f := f) c % m = Mf (f := g) c % m))
      = (Finset.univ.filter (fun g : Fin r → Fin n =>
          ∀ c, Mf (f := g) c % m = Mf (f := f) c % m)) := by
  apply Finset.filter_congr
  intro g _
  exact ⟨fun h c => (h c).symm, fun h c => (h c).symm⟩

/-- The number of `f` with a prescribed value `A` of `Ac` is at most
`n ^ A` (choices of the residue pattern) times the number of extensions. -/
lemma card_ac_le {r n m : ℕ} (hm : 2 ≤ m) (A : ℕ) :
    (Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A)).card
      ≤ n ^ A * (r ^ r * n ^ ((r - A) / m)) := by
  classical
  set PatSet : Finset (Fin n → Fin m) :=
    Finset.univ.filter (fun S : Fin n → Fin m => ∑ c, (S c : ℕ) = A) with hPat
  have hsub : (Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A))
      ⊆ PatSet.biUnion (fun S => Finset.univ.filter (fun f : Fin r → Fin n =>
          ∀ c, Mf (f := f) c % m = (S c : ℕ))) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_biUnion]
    refine ⟨fun c => ⟨Mf (f := f) c % m, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · rw [hPat, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hf.2⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun c => rfl⟩
  calc (Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A)).card
      ≤ ∑ S ∈ PatSet, (Finset.univ.filter (fun f : Fin r → Fin n =>
          ∀ c, Mf (f := f) c % m = (S c : ℕ))).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ PatSet, (r ^ r * n ^ ((r - A) / m)) := by
        apply Finset.sum_le_sum
        intro S hS
        rw [hPat] at hS
        have h := fiber_res_le (r := r) (n := n) (m := m) hm S
        rw [show ∑ c, (S c : ℕ) = A from (Finset.mem_filter.mp hS).2] at h
        exact h
    _ = PatSet.card * (r ^ r * n ^ ((r - A) / m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n ^ A * (r ^ r * n ^ ((r - A) / m)) :=
        Nat.mul_le_mul_right _ (by rw [hPat]; exact card_pattern_le n A m)

theorem card_bad_mult_pair_le' (r n m : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ((Finset.univ.filter (fun p : (Fin r → Fin n) × (Fin r → Fin n) =>
        ∀ c : Fin n, (Finset.univ.filter (fun i => p.1 i = c)).card % m
                   = (Finset.univ.filter (fun i => p.2 i = c)).card % m)).card)
      ≤ (r + 1) * r ^ (2 * r) * n ^ r := by
  classical
  have hsum : (Finset.univ.filter (fun p : (Fin r → Fin n) × (Fin r → Fin n) =>
        ∀ c : Fin n, Mf (f := p.1) c % m = Mf (f := p.2) c % m)).card
      = ∑ f : Fin r → Fin n,
        (Finset.univ.filter (fun g : Fin r → Fin n =>
          ∀ c, Mf (f := f) c % m = Mf (f := g) c % m)).card := by
    rw [Finset.card_filter]
    rw [Fintype.sum_prod_type (f := fun p : (Fin r → Fin n) × (Fin r → Fin n) =>
        if (∀ c, Mf (f := p.1) c % m = Mf (f := p.2) c % m) then (1 : ℕ) else 0)]
    simp only [Finset.card_filter, Prod.fst, Prod.snd]
  have hAc_le : ∀ f : Fin r → Fin n, Ac m f ≤ r := fun f => Ac_le f
  have hgroup := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin r → Fin n))) (t := Finset.range (r+1))
      (g := fun f : Fin r → Fin n => Ac m f)
      (fun f _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hAc_le f)))
      (fun f => n ^ ((r - Ac m f) / m))
  have hsum_bound : ∑ f : Fin r → Fin n, n ^ ((r - Ac m f) / m) ≤ (r + 1) * (r ^ r * n ^ r) := by
    rw [← hgroup]
    calc ∑ A ∈ Finset.range (r+1),
          (∑ f ∈ Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A),
              n ^ ((r - Ac m f) / m))
        ≤ ∑ _A ∈ Finset.range (r+1), r ^ r * n ^ r := by
          apply Finset.sum_le_sum
          intro A hA
          have hAr : A ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hA)
          have hinner : (∑ f ∈ Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A),
                n ^ ((r - Ac m f) / m))
              = (Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A)).card
                  * n ^ ((r - A) / m) := by
            rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2])]
            rw [Finset.sum_const, smul_eq_mul]
          rw [hinner]
          calc (Finset.univ.filter (fun f : Fin r → Fin n => Ac m f = A)).card
                * n ^ ((r - A) / m)
              ≤ (n ^ A * (r ^ r * n ^ ((r - A) / m))) * n ^ ((r - A) / m) :=
                Nat.mul_le_mul_right _ (card_ac_le (r := r) (n := n) (m := m) hm A)
            _ = r ^ r * (n ^ (2 * ((r - A) / m)) * n ^ A) := by ring
            _ = r ^ r * n ^ (A + 2 * ((r - A) / m)) := by
                rw [← pow_add]
                ring_nf
            _ ≤ r ^ r * n ^ r := by
                apply Nat.mul_le_mul_left
                apply Nat.pow_le_pow_right (by omega : 0 < n)
                have h1 : 2 * ((r - A) / m) ≤ m * ((r - A) / m) :=
                  Nat.mul_le_mul_right _ hm
                have h2 : m * ((r - A) / m) ≤ r - A := Nat.mul_div_le _ _
                omega
      _ = (r + 1) * (r ^ r * n ^ r) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (Finset.univ.filter (fun p : (Fin r → Fin n) × (Fin r → Fin n) =>
        ∀ c : Fin n, (Finset.univ.filter (fun i => p.1 i = c)).card % m
                   = (Finset.univ.filter (fun i => p.2 i = c)).card % m)).card
      = (Finset.univ.filter (fun p : (Fin r → Fin n) × (Fin r → Fin n) =>
          ∀ c : Fin n, Mf (f := p.1) c % m = Mf (f := p.2) c % m)).card := rfl
    _ = ∑ f : Fin r → Fin n,
        (Finset.univ.filter (fun g : Fin r → Fin n =>
          ∀ c, Mf (f := f) c % m = Mf (f := g) c % m)).card := hsum
    _ = ∑ f : Fin r → Fin n,
        (Finset.univ.filter (fun g : Fin r → Fin n =>
          ∀ c, Mf (f := g) c % m = Mf (f := f) c % m)).card :=
        Finset.sum_congr rfl (fun f _ => by rw [filter_symm (r := r) (n := n) (m := m) f])
    _ ≤ ∑ f : Fin r → Fin n, r ^ r * n ^ ((r - Ac m f) / m) := by
        apply Finset.sum_le_sum
        intro f _
        have h1 := fiber_res_le (r := r) (n := n) (m := m) hm
          (fun c => (⟨Mf (f := f) c % m, Nat.mod_lt _ (by omega)⟩ : Fin m))
        rw [show ∑ c, ((⟨Mf (f := f) c % m, Nat.mod_lt _ (by omega)⟩ : Fin m) : ℕ) = Ac m f
            from rfl] at h1
        exact h1
    _ = r ^ r * ∑ f : Fin r → Fin n, n ^ ((r - Ac m f) / m) := by
        rw [Finset.mul_sum]
    _ ≤ r ^ r * ((r + 1) * (r ^ r * n ^ r)) := Nat.mul_le_mul_left _ hsum_bound
    _ = (r + 1) * r ^ (2 * r) * n ^ r := by
        rw [show (2:ℕ) * r = r + r by ring, pow_add]
        ring


end BurgessMoment

lemma pair_sum_bound {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (H r : ℕ) (hr : 1 ≤ r) (hH1 : 1 ≤ H) (hHp : H ≤ p) :
    ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, ‖Tg p H r χ f g‖
      ≤ (2 * r : ℝ) * Real.sqrt p * (H : ℝ) ^ (2 * r)
        + ((((r + 1) * r ^ (2 * r) : ℕ)) : ℝ) * (p : ℝ) * (H : ℝ) ^ r := by
  classical
  set A : ℝ := (2 * r : ℝ) * Real.sqrt p with hA
  set B : ℝ := (p : ℝ) with hB
  set Cb : ℝ := ((((r + 1) * r ^ (2 * r) : ℕ)) : ℝ) with hCb
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  rw [← Fintype.sum_prod_type (f := fun fg : (Fin r → Fin H) × (Fin r → Fin H) => ‖Tg p H r χ fg.1 fg.2‖)]
  have hterm : ∀ fg : (Fin r → Fin H) × (Fin r → Fin H),
      ‖Tg p H r χ fg.1 fg.2‖ ≤ if Good p H r χ fg then A else B := by
    intro fg
    by_cases hg : Good p H r χ fg
    · rw [if_pos hg]
      exact norm_T_le_good χ hχ H r hr fg.1 fg.2 hg
    · rw [if_neg hg]
      exact norm_T_le_bad χ H r fg.1 fg.2
  have h1 : ∑ fg : (Fin r → Fin H) × (Fin r → Fin H), ‖Tg p H r χ fg.1 fg.2‖
      ≤ A * ((Finset.univ.filter (fun fg => Good p H r χ fg)).card : ℝ)
        + B * ((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℝ) := by
    calc ∑ fg : (Fin r → Fin H) × (Fin r → Fin H), ‖Tg p H r χ fg.1 fg.2‖
        ≤ ∑ fg : (Fin r → Fin H) × (Fin r → Fin H),
            (if Good p H r χ fg then A else B) :=
          Finset.sum_le_sum (fun fg _ => hterm fg)
      _ = A * ((Finset.univ.filter (fun fg => Good p H r χ fg)).card : ℝ)
            + B * ((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℝ) := by
          rw [Finset.sum_ite]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hGood : ((Finset.univ.filter (fun fg => Good p H r χ fg)).card : ℝ)
      ≤ (H : ℝ) ^ (2 * r) := by
    have hcard : Fintype.card ((Fin r → Fin H) × (Fin r → Fin H)) = H ^ r * H ^ r := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hle : (Finset.univ.filter (fun fg => Good p H r χ fg)).card ≤ H ^ r * H ^ r := by
      rw [← hcard, ← Finset.card_univ]
      exact Finset.card_filter_le _ _
    calc ((Finset.univ.filter (fun fg => Good p H r χ fg)).card : ℝ)
        ≤ ((H ^ r * H ^ r : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (H : ℝ) ^ (2 * r) := by push_cast; rw [← pow_add]; ring_nf
  have hBad : ((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℝ)
      ≤ Cb * (H : ℝ) ^ r := by
    have hsub : (Finset.univ.filter (fun fg => ¬ Good p H r χ fg))
        ⊆ (Finset.univ.filter (fun fg : (Fin r → Fin H) × (Fin r → Fin H) =>
            ∀ j : Fin H, (Finset.univ.filter (fun i => fg.1 i = j)).card % orderOf χ
                       = (Finset.univ.filter (fun i => fg.2 i = j)).card % orderOf χ)) := by
      intro fg hfg
      rw [Finset.mem_filter] at hfg ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hbad : ∃ c : ZMod p, ∃ Q : Polynomial (ZMod p),
          Pf p H r fg.1 * (Pf p H r fg.2) ^ (orderOf χ - 1)
            = Polynomial.C c * Q ^ (orderOf χ) := by
        by_contra hc
        exact hfg.2 hc
      exact congruent_of_bad χ hχ H r hHp fg.1 fg.2 hbad
    have hcard := le_trans (Finset.card_le_card hsub)
      (BurgessMoment.card_bad_mult_pair_le' r H (orderOf χ) hm2 hH1)
    have hcast : (((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℕ) : ℝ)
        ≤ (((r + 1) * r ^ (2 * r) * H ^ r : ℕ) : ℝ) := by exact_mod_cast hcard
    calc ((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℝ)
        ≤ (((r + 1) * r ^ (2 * r) * H ^ r : ℕ) : ℝ) := hcast
      _ = Cb * (H : ℝ) ^ r := by rw [hCb]; push_cast; ring
  calc ∑ fg : (Fin r → Fin H) × (Fin r → Fin H), ‖Tg p H r χ fg.1 fg.2‖
      ≤ A * ((Finset.univ.filter (fun fg => Good p H r χ fg)).card : ℝ)
        + B * ((Finset.univ.filter (fun fg => ¬ Good p H r χ fg)).card : ℝ) := h1
    _ ≤ A * (H : ℝ) ^ (2 * r) + B * (Cb * (H : ℝ) ^ r) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hGood hA0
        · exact mul_le_mul_of_nonneg_left hBad hB0
    _ = (2 * r : ℝ) * Real.sqrt p * (H : ℝ) ^ (2 * r)
        + ((((r + 1) * r ^ (2 * r) : ℕ)) : ℝ) * (p : ℝ) * (H : ℝ) ^ r := by
        rw [hA, hB, hCb]; ring

theorem burgess_moment_prime (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 →
      ∀ H : ℕ, H ≤ p →
        ∑ m ∈ Finset.range p, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)‖ ^ (2 * r)
          ≤ C * ((p : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (p : ℝ)) := by
  have hr1 : 1 ≤ r := hr
  set Cb : ℝ := ((((r + 1) * r ^ (2 * r) : ℕ)) : ℝ) with hCb
  refine ⟨max (2 * (r : ℝ)) Cb + 1, by positivity, ?_⟩
  intro p _inst χ hχ H hHp
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases Nat.eq_zero_or_pos H with hH0 | hHpos
  · subst hH0
    have hzero : (∑ m ∈ Finset.range p,
        ‖∑ h ∈ Finset.Ioc m (m + 0), χ (h : ZMod p)‖ ^ (2 * r)) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      have hempty : Finset.Ioc m (m + 0) = ∅ := by rw [add_zero, Finset.Ioc_self]
      rw [hempty, Finset.sum_empty, norm_zero, zero_pow (by omega : 2 * r ≠ 0)]
    rw [hzero]
    apply mul_nonneg
    · positivity
    · apply add_nonneg <;> positivity
  · have hH1 : 1 ≤ H := hHpos
    have hM := sum_norm_eq_norm_sum (p := p)
      (fun m => ∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)) r
    rw [hM, Z_eq p H r χ hχ]
    have h1 : ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tg p H r χ f g‖
        ≤ ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, ‖Tg p H r χ f g‖ := by
      calc ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tg p H r χ f g‖
          ≤ ∑ f : Fin r → Fin H, ‖∑ g : Fin r → Fin H, Tg p H r χ f g‖ :=
            norm_sum_le _ _
        _ ≤ ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, ‖Tg p H r χ f g‖ :=
            Finset.sum_le_sum (fun f _ => norm_sum_le _ _)
    have h2 := pair_sum_bound χ hχ H r hr1 hH1 hHp
    have hfinal : (2 * r : ℝ) * Real.sqrt (p : ℝ) * (H : ℝ) ^ (2 * r)
          + Cb * (p : ℝ) * (H : ℝ) ^ r
        ≤ (max (2 * (r : ℝ)) Cb + 1) *
          ((p : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (p : ℝ)) := by
      set C : ℝ := max (2 * (r : ℝ)) Cb + 1 with hCdef
      have hC1 : (2 * (r : ℝ)) ≤ C := by
        rw [hCdef]; linarith [le_max_left (2 * (r : ℝ)) Cb]
      have hC2 : Cb ≤ C := by
        rw [hCdef]; linarith [le_max_right (2 * (r : ℝ)) Cb]
      have hC0 : 0 ≤ C := by
        have : (0 : ℝ) ≤ 2 * (r : ℝ) := by positivity
        linarith
      have hp0 : 0 ≤ (p : ℝ) := by positivity
      have hHr0 : 0 ≤ (H : ℝ) ^ r := by positivity
      have hH2r0 : 0 ≤ (H : ℝ) ^ (2 * r) := by positivity
      have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
      have e1 : (2 * (r : ℝ)) * (Real.sqrt (p : ℝ) * (H : ℝ) ^ (2 * r))
          ≤ C * (Real.sqrt (p : ℝ) * (H : ℝ) ^ (2 * r)) :=
        mul_le_mul_of_nonneg_right hC1 (mul_nonneg hs0 hH2r0)
      have e2 : Cb * ((p : ℝ) * (H : ℝ) ^ r) ≤ C * ((p : ℝ) * (H : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_right hC2 (mul_nonneg hp0 hHr0)
      nlinarith [e1, e2]
    calc ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tg p H r χ f g‖
        ≤ ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, ‖Tg p H r χ f g‖ := h1
      _ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) * (H : ℝ) ^ (2 * r)
            + Cb * (p : ℝ) * (H : ℝ) ^ r := h2
      _ ≤ (max (2 * (r : ℝ)) Cb + 1) *
            ((p : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (p : ℝ)) := hfinal

end Commons.NumberTheory.DirichletCharacter
