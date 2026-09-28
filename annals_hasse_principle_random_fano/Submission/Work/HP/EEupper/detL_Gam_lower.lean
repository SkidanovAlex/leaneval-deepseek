import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.EE.wedgeNorm_veronese
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.GM.exists_not_dvd_mul_of_dvd_gcdMinors2_veronese

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Finset

namespace Work.HP.EEupper

/-! ## Two primitive vectors not equal up to sign are `ℤ`-linearly independent -/

/-- Two primitive integer vectors `x ≠ y`, `x ≠ -y` are `ℤ`-linearly independent: an integer
dependence `a • x + b • y = 0` with `a, b ≠ 0` forces `b ∣ a` and `a ∣ b` (via the gcd of the
coordinates), hence `a = ±b` and then `x = ±y`. -/
theorem linearIndependent_of_isPrim {ι : Type*} [Fintype ι] {x y : ι → ℤ}
    (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y) (h1 : x ≠ y) (h2 : x ≠ -y) :
    LinearIndependent ℤ ![x, y] := by
  classical
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hcomp : ∀ i, a * x i + b * y i = 0 := by
    intro i
    have := congrFun hab i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, zero_add] at hcomp
    refine ⟨rfl, ?_⟩
    by_contra hb
    exact Work.HP.isPrim_ne_zero hy (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left hb)
  · by_cases hb : b = 0
    · subst hb
      simp only [zero_mul, add_zero] at hcomp
      exact absurd (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left ha)
        (Work.HP.isPrim_ne_zero hx)
    · exfalso
      have hb_dvd : b ∣ normalize a := by
        have hd : b ∣ Finset.univ.gcd (fun i => a * x i) :=
          Finset.dvd_gcd (fun i _ => ⟨-y i, by have h := hcomp i; linear_combination h⟩)
        rw [Finset.gcd_mul_left, hx, mul_one] at hd
        exact hd
      have ha_dvd : a ∣ normalize b := by
        have hd : a ∣ Finset.univ.gcd (fun i => b * y i) :=
          Finset.dvd_gcd (fun i _ => ⟨-x i, by have h := hcomp i; linear_combination h⟩)
        rw [Finset.gcd_mul_left, hy, mul_one] at hd
        exact hd
      have h1n : b.natAbs ∣ a.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr hb_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have h2n : a.natAbs ∣ b.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr ha_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have heq : a.natAbs = b.natAbs := (Nat.dvd_antisymm h1n h2n).symm
      have hax : ∀ i, a * x i = -(b * y i) := by intro i; have h := hcomp i; linarith
      rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
      · exact h2 (funext fun i => by
          have hh := hax i
          rw [h] at hh
          have hb0 : b * (x i + y i) = 0 := by
            have h1' : b * (x i + y i) = b * x i + b * y i := by ring
            rw [h1']; linarith
          have hx0 : x i + y i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
          simp only [Pi.neg_apply]
          linarith)
      · exact h1 (funext fun i => by
          have hh := hax i
          rw [h] at hh
          have hb0 : b * (y i - x i) = 0 := by
            have h1' : b * (y i - x i) = b * y i - b * x i := by ring
            rw [h1']; linarith
          have hy0 : y i - x i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
          linarith)

/-! ## Lemma G, one direction: `𝒢(νx, νy) ∣ 𝒢(x, y)` -/

/-- Every `2 × 2` minor of the Veronese pair `(ν_{d,n}(x), ν_{d,n}(y))` is divisible by the gcd
`𝒢(x,y)` of the minors of `(x,y)`: for a prime `p` and a power `p^k` dividing all Veronese minors,
the monomials `X_j^{d-1}X_i`, `X_j^{d-1}X_l` exhibit `p^k ∣ (x_j y_j)^{d-1}(x_i y_l - x_l y_i)`;
choosing `j` with `p ∤ x_j y_j` (possible by
`GM.exists_not_dvd_mul_of_dvd_gcdMinors2_veronese`) cancels the unit factor. -/
theorem gcdMinors2_veronese_dvd (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y) :
    Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) ∣
      Work.HP.gcdMinors2 x y := by
  classical
  set H : ℤ := Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) with hHdef
  refine Int.natAbs_dvd_natAbs.mp ?_
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; simpa using hp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hpkZ : ((p : ℤ) ^ k) ∣ H := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Int.natAbs_pow] using hpk
  have hpH : (p : ℤ) ∣ H := by
    have h1 : ((p : ℤ) ^ 1) ∣ ((p : ℤ) ^ k) :=
      pow_dvd_pow (p : ℤ) (by omega : 1 ≤ k)
    simpa using dvd_trans h1 hpkZ
  obtain ⟨j, hj⟩ :=
    Work.HP.GM.exists_not_dvd_mul_of_dvd_gcdMinors2_veronese d n p hd hp x y hx hy hpH
  have hminor : ∀ i l : Fin (n + 1), ((p : ℤ) ^ k) ∣ (x i * y l - x l * y i) := by
    intro i l
    have h1 : H ∣ (Work.HP.veronese d n x (Work.HP.NA.monDij d n hd j i) *
          Work.HP.veronese d n y (Work.HP.NA.monDij d n hd j l) -
          Work.HP.veronese d n x (Work.HP.NA.monDij d n hd j l) *
          Work.HP.veronese d n y (Work.HP.NA.monDij d n hd j i)) :=
      (Work.HP.NA.gcdMinors2_dvd_iff H (Work.HP.veronese d n x) (Work.HP.veronese d n y)).mp
        dvd_rfl (Work.HP.NA.monDij d n hd j i) (Work.HP.NA.monDij d n hd j l)
    have h2 : ((p : ℤ) ^ k) ∣ (Work.HP.veronese d n x (Work.HP.NA.monDij d n hd j i) *
          Work.HP.veronese d n y (Work.HP.NA.monDij d n hd j l) -
          Work.HP.veronese d n x (Work.HP.NA.monDij d n hd j l) *
          Work.HP.veronese d n y (Work.HP.NA.monDij d n hd j i)) := dvd_trans hpkZ h1
    rw [Work.HP.NA.veronese_monDij d n hd x j i, Work.HP.NA.veronese_monDij d n hd y j l,
      Work.HP.NA.veronese_monDij d n hd x j l, Work.HP.NA.veronese_monDij d n hd y j i] at h2
    have ha : ¬ (p : ℤ) ∣ (x j * y j) ^ (d - 1) := fun hh => hj (hpz.dvd_of_dvd_pow hh)
    have h2' : ((p : ℤ) ^ k) ∣ (x j * y j) ^ (d - 1) * (x i * y l - x l * y i) := by
      convert h2 using 1
      ring
    exact Work.HP.NA.dvd_of_dvd_mul_of_not_dvd_pow hpz ha h2'
  have hpg : ((p : ℤ) ^ k) ∣ Work.HP.gcdMinors2 x y :=
    (Work.HP.NA.gcdMinors2_dvd_iff ((p : ℤ) ^ k) x y).mpr hminor
  have := Int.natAbs_dvd_natAbs.mpr hpg
  simpa [Int.natAbs_pow] using this

/-! ## The pointwise lower bound on `det Γ_{x,y}` -/

theorem detL_Gam_lower (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
      x ≠ y → x ≠ -y →
      C * (Work.HP.dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * Work.HP.eNorm x ^ (d - 1) *
        Work.HP.eNorm y ^ (d - 1)) ≤ Work.HP.detL (Work.HP.Gam d n x y) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := Work.HP.EE.wedgeNorm_veronese d n hd
  refine ⟨c₁, hc₁pos, ?_⟩
  intro x y hx hy h1 h2
  have hind : LinearIndependent ℤ ![x, y] := linearIndependent_of_isPrim hx hy h1 h2
  have hnu := Work.HP.Sig2.nu_indep d n hd x y hx hy h1 h2
  have hdet : Work.HP.detL (Work.HP.Gam d n x y) =
      Work.HP.wedgeNorm (Work.HP.veronese d n x) (Work.HP.veronese d n y) /
        (Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) : ℝ) := by
    rw [show Work.HP.Gam d n x y =
        Work.HP.latOrth (Work.HP.veronese d n x) ⊓ Work.HP.latOrth (Work.HP.veronese d n y)
        from rfl]
    exact (Work.HP.det_gam_gen (Work.HP.veronese d n x) (Work.HP.veronese d n y) hnu).1
  have hdmin : Work.HP.dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) =
      Work.HP.wedgeNorm x y / (Work.HP.gcdMinors2 x y : ℝ) := by
    rw [(Work.HP.det_gam_gen x y hind).2, (Work.HP.det_gam_gen x y hind).1]
  have hgpos : 0 < (Work.HP.gcdMinors2 x y : ℝ) := by
    exact_mod_cast Work.HP.DGG.gcdMinors2_pos x y hind
  have hGpos : 0 < (Work.HP.gcdMinors2 (Work.HP.veronese d n x)
      (Work.HP.veronese d n y) : ℝ) := by
    exact_mod_cast Work.HP.DGG.gcdMinors2_pos _ _ hnu
  have hGle : (Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) : ℝ)
      ≤ (Work.HP.gcdMinors2 x y : ℝ) := by
    have hdvd := gcdMinors2_veronese_dvd d n (by omega) x y hx hy
    have hle : Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y)
        ≤ Work.HP.gcdMinors2 x y := Int.le_of_dvd (by exact_mod_cast hgpos) hdvd
    exact_mod_cast hle
  have hWnn : 0 ≤ Work.HP.wedgeNorm (Work.HP.veronese d n x) (Work.HP.veronese d n y) :=
    Real.sqrt_nonneg _
  calc c₁ * (Work.HP.dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * Work.HP.eNorm x ^ (d - 1) *
        Work.HP.eNorm y ^ (d - 1))
      = c₁ * (Work.HP.eNorm x ^ (d - 1) * Work.HP.eNorm y ^ (d - 1) * Work.HP.wedgeNorm x y) /
          (Work.HP.gcdMinors2 x y : ℝ) := by
        rw [hdmin]; field_simp
    _ = c₁ * Work.HP.eNorm x ^ (d - 1) * Work.HP.eNorm y ^ (d - 1) * Work.HP.wedgeNorm x y /
          (Work.HP.gcdMinors2 x y : ℝ) := by ring
    _ ≤ Work.HP.wedgeNorm (Work.HP.veronese d n x) (Work.HP.veronese d n y) /
          (Work.HP.gcdMinors2 x y : ℝ) :=
        div_le_div_of_nonneg_right (hc₁ x y) (le_of_lt hgpos)
    _ ≤ Work.HP.wedgeNorm (Work.HP.veronese d n x) (Work.HP.veronese d n y) /
          (Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y) : ℝ) := by
        rw [div_le_div_iff₀ hgpos hGpos]
        exact mul_le_mul_of_nonneg_left hGle hWnn
    _ = Work.HP.detL (Work.HP.Gam d n x y) := hdet.symm

end Work.HP.EEupper
