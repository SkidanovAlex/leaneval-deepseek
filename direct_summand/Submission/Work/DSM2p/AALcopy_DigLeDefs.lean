-- Redirected copy of `Submission.Work.DSM2p.DigLeDefs` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_approx_defs
import Submission.Work.DSM2p.AALcopy_WittPolyWt

/-!
# The Gauss-norm ("digit bound") vocabulary on the tilt

Fix a perfectoid datum `QR : DSMap.PerfectoidData p R` (so `R` is `p`-adically complete and `p` is
not a unit), let `Λ = PreTilt R p` be the tilt and `𝕎 = WittVector p Λ`.

* `nv v x = v (x^♯)` is the value of `x ∈ Λ` under the multiplicative map `♯ = PreTilt.untilt`.
* `DigLe v z B` says that every tilt digit of `z` has `v`-value at most `B` — the sup-norm
  condition `|z|_sup ≤ B` of Česnavičius–Scholze.

The main content of the companion files is that `DigLe` behaves like a norm: it is monotone,
subadditive (`DigLe.add`) and submultiplicative (`DigLe.mul`), which is what turns the
Teichmüller recursion of `Work.DSM2p.witt_step_rec` into a numerical estimate.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.DSM2p

universe u v w

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]

/-! ## `nv`, the value of an element of the tilt -/

theorem untilt_zero : PreTilt.untilt (0 : PreTilt R p) = 0 := by
  rw [show PreTilt.untilt (0 : PreTilt R p)
      = (Perfection.teichmuller p (Ideal.span {(p : R)})) 0 from rfl,
    Perfection.teichmuller_zero]

/-- `nv v x = v (x^♯)`: the value of `x ∈ PreTilt R p` under the untilt map. -/
noncomputable def nv {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (x : PreTilt R p) : Γ₀ := v (PreTilt.untilt x)

@[simp]
theorem nv_one {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) :
    nv v (1 : PreTilt R p) = 1 := by
  simp [nv]

@[simp]
theorem nv_zero {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) :
    nv v (0 : PreTilt R p) = 0 := by
  simp only [nv, untilt_zero, map_zero]

theorem nv_mul {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (a b : PreTilt R p) : nv v (a * b) = nv v a * nv v b := by
  simp [nv]

theorem nv_pow {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (a : PreTilt R p) (n : ℕ) : nv v (a ^ n) = nv v a ^ n := by
  simp [nv]

theorem nv_le_one {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hball : IsUnitBall v Set.univ) (x : PreTilt R p) : nv v x ≤ 1 :=
  hball _ (Set.mem_univ _)

/-! ## The Frobenius-symm power acts as an iterate

`(frobeniusEquiv Λ p).symm ^ j` (the monoid power, i.e. composition) coincides with the `j`-fold
iterate of the function `(frobeniusEquiv Λ p).symm`.  This is the bridge that lets Mathlib's
`PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` be applied to `tiltDigit`. -/

theorem frobeniusEquiv_symm_pow_apply (j : ℕ) (y : PreTilt R p) :
    ((frobeniusEquiv (PreTilt R p) p).symm ^ j) y
      = ((⇑(frobeniusEquiv (PreTilt R p) p).symm)^[j]) y := by
  induction j generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    rw [show ((frobeniusEquiv (PreTilt R p) p).symm *
          ((frobeniusEquiv (PreTilt R p) p).symm ^ k)) y
        = (frobeniusEquiv (PreTilt R p) p).symm
            (((frobeniusEquiv (PreTilt R p) p).symm ^ k) y) from by simp]
    rw [ih, ← Function.iterate_succ_apply' (⇑(frobeniusEquiv (PreTilt R p) p).symm) k y]

theorem frobeniusEquiv_symm_apply_pow (y : PreTilt R p) :
    ((frobeniusEquiv (PreTilt R p) p).symm y) ^ p = y := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow y 1
  simpa using h

/-- **The `p ^ j`-th power of the untilt of the `j`-th tilt digit.**  This is the only place where
the perfectness of `Λ` enters the digit calculus. -/
theorem untilt_tiltDigit_pow (z : WittVector p (PreTilt R p)) (j : ℕ) :
    PreTilt.untilt (tiltDigit z j) ^ p ^ j = PreTilt.untilt (z.coeff j) := by
  rw [tiltDigit, frobeniusEquiv_symm_pow_apply]
  exact PreTilt.untilt_iterate_frobeniusEquiv_symm_pow (z.coeff j) j

theorem nv_tiltDigit_pow {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (z : WittVector p (PreTilt R p)) (j : ℕ) :
    nv v (tiltDigit z j) ^ p ^ j = nv v (z.coeff j) := by
  simp only [nv]
  rw [← map_pow, untilt_tiltDigit_pow]

/-- Multiplication by `p` shifts the tilt digits (up to the Frobenius twist, which is what makes
the *values* agree). -/
theorem tiltDigit_mul_p_succ (z : WittVector p (PreTilt R p)) (k : ℕ) :
    tiltDigit (z * (p : WittVector p (PreTilt R p))) (k + 1) = tiltDigit z k := by
  have hcoeff : (z * (p : WittVector p (PreTilt R p))).coeff (k + 1) = z.coeff k ^ p :=
    mul_charP_coeff_succ z k
  rw [tiltDigit, hcoeff, tiltDigit, pow_succ]
  rw [show ((frobeniusEquiv (PreTilt R p) p).symm ^ k *
        (frobeniusEquiv (PreTilt R p) p).symm) (z.coeff k ^ p)
      = ((frobeniusEquiv (PreTilt R p) p).symm ^ k)
          ((frobeniusEquiv (PreTilt R p) p).symm (z.coeff k ^ p)) from by simp]
  rw [show (frobeniusEquiv (PreTilt R p) p).symm (z.coeff k ^ p) = z.coeff k from by
    rw [map_pow, frobeniusEquiv_symm_apply_pow]]

/-! ## `DigLe` -/

/-- `DigLe v z B` : every tilt digit of `z` has `v`-value at most `B`. -/
def DigLe {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (z : WittVector p (PreTilt R p)) (B : Γ₀) : Prop :=
  ∀ j : ℕ, v (PreTilt.untilt (tiltDigit z j)) ≤ B

theorem DigLe.mono {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    {z : WittVector p (PreTilt R p)} {B B' : Γ₀} (h : B ≤ B') (hz : DigLe v z B) :
    DigLe v z B' := fun j => le_trans (hz j) h

theorem DigLe.zero {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (B : Γ₀) : DigLe v (0 : WittVector p (PreTilt R p)) B := by
  intro j
  have h : tiltDigit (0 : WittVector p (PreTilt R p)) j = 0 := by simp [tiltDigit]
  rw [h, untilt_zero, map_zero]
  exact zero_le

/-- The Teichmüller lift `[a]` has all digits bounded by `nv v a`. -/
theorem DigLe.teichmuller_self {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (a : PreTilt R p) :
    DigLe v (WittVector.teichmuller p a) (v (PreTilt.untilt a)) := by
  intro j
  rw [tiltDigit_teichmuller]
  by_cases h : j = 0
  · subst h; simp
  · rw [if_neg h, untilt_zero, map_zero]
    exact zero_le

theorem DigLe.to_coeff {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} {z : WittVector p (PreTilt R p)} {B : Γ₀} (hz : DigLe v z B) (j : ℕ) :
    nv v (z.coeff j) ≤ B ^ p ^ j := by
  rw [← nv_tiltDigit_pow v z j]
  exact pow_le_pow_left' (hz j) _

theorem DigLe.of_coeff {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} {z : WittVector p (PreTilt R p)} {B : Γ₀}
    (hz : ∀ j : ℕ, nv v (z.coeff j) ≤ B ^ p ^ j) : DigLe v z B := by
  intro j
  have h := hz j
  rw [← nv_tiltDigit_pow v z j] at h
  exact le_of_pow_le_pow_left₀ (pow_ne_zero j (Fact.out : p.Prime).ne_zero) (zero_le) h

/-- Multiplication by `p` does not change the digit bound. -/
theorem DigLe.mul_p {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} {z : WittVector p (PreTilt R p)} {B : Γ₀} (hz : DigLe v z B) :
    DigLe v (z * (p : WittVector p (PreTilt R p))) B := by
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h : tiltDigit (z * (p : WittVector p (PreTilt R p))) 0 = 0 := by
      rw [tiltDigit, mul_charP_coeff_zero]; simp
    rw [h, untilt_zero, map_zero]
    exact zero_le
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj)
    rw [tiltDigit_mul_p_succ]
    exact hz k

/-! ## The ℤ-forms of the polynomial weight statements -/

theorem WtLe.map_intCast {σ : Type*} {ρ : σ → ℕ} {N : ℕ} {P : MvPolynomial σ ℤ}
    (h : WtLe ρ P N) : WtLe ρ (MvPolynomial.map (Int.castRingHom ℚ) P) N := by
  intro m hm
  rw [MvPolynomial.coeff_map] at hm
  exact h m (fun h0 => hm (by rw [h0, map_zero]))

theorem WtLe.map_intCast_iff {σ : Type*} {ρ : σ → ℕ} {N : ℕ} {P : MvPolynomial σ ℤ} :
    WtLe ρ (MvPolynomial.map (Int.castRingHom ℚ) P) N ↔ WtLe ρ P N := by
  constructor
  · intro h m hm
    refine h m ?_
    rw [MvPolynomial.coeff_map]
    exact fun h0 => hm (Int.cast_eq_zero.mp h0)
  · exact WtLe.map_intCast

theorem wtLe_wittAdd (n : ℕ) :
    WtLe (rho2 (p := p)) (WittVector.wittAdd p n) (p ^ n) := by
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) (WittVector.wittAdd p n) = wittAddRat p n := by
    rw [WittVector.wittAdd, wittAddRat, map_wittStructureInt]
    congr 1
    simp
  rw [← WtLe.map_intCast_iff, hmap]
  exact wtLe_wittAddRat n

theorem wtLe_wittMul_row (i : Fin 2) (n : ℕ) :
    WtLe (rhoRow (p := p) i) (WittVector.wittMul p n) (p ^ n) := by
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) (WittVector.wittMul p n) = wittMulRat p n := by
    rw [WittVector.wittMul, wittMulRat, map_wittStructureInt]
    congr 1
    simp
  rw [← WtLe.map_intCast_iff, hmap]
  exact wtLe_wittMulRat_row i n

end Work.DSM2p
