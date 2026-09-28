import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Lat.span_pair_lattice
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.HPgram
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.EE.wedgeNorm_veronese
import Submission.Work.HP.EE.veronese_swap
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.sum_le_ceil_logb_of_prod
import Submission.Work.HP.EE.ellAux
import Submission.Work.HP.ball_prod_window_r2
import Submission.Work.HP.dyadic_sum_r2
import Submission.Work.HP.EEupper.Assembly
import Submission.Work.HP.EEupper.Count
import Submission.Work.EEupper.latCovolStep
import Submission.Work.HP.EEupper.Schmidt

/-!
# `Work.HP.EE.ellXY_two_pub`

The rank-`2` pair count `ℓ_{2,n}(X,Y;Δ) ≪ X²Y²Δ^{n-1}` (Browning--Le Boudec--Sawin §3.3),
exposed under the name `ellXY_two_pub`.  This is the `private lemma ellXY_two_final` of
`Work.HP.EE_upper_all` (which is `sorry`-free), re-exported so that other modules can use it.
-/


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP

/-! ## Elementary facts about primitive vectors -/

section PrimAux

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- `a • v = 0` with `a ≠ 0` forces `v = 0`. -/
private lemma smul_int_eq_zero_iff {v : ι → ℤ} {a : ℤ} (ha : a ≠ 0) : a • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  · rintro rfl; simp

/-- Two primitive vectors that are not equal up to sign are linearly independent over `ℤ`. -/
private lemma linearIndependent_of_isPrim {x y : ι → ℤ} (hx : IsPrim x) (hy : IsPrim y)
    (h1 : x ≠ y) (h2 : x ≠ -y) : LinearIndependent ℤ ![x, y] := by
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
    exact isPrim_ne_zero hy (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left hb)
  · by_cases hb : b = 0
    · subst hb
      simp only [zero_mul, add_zero] at hcomp
      exact absurd (funext fun i => (mul_eq_zero.mp (hcomp i)).resolve_left ha) (isPrim_ne_zero hx)
    · exfalso
      have hb_dvd : b ∣ normalize a := by
        have hd : b ∣ Finset.univ.gcd (fun i => a * x i) :=
          Finset.dvd_gcd (fun i _ => ⟨-y i, by
            have h := hcomp i
            linear_combination h⟩)
        rw [Finset.gcd_mul_left, hx, mul_one] at hd
        exact hd
      have ha_dvd : a ∣ normalize b := by
        have hd : a ∣ Finset.univ.gcd (fun i => b * y i) :=
          Finset.dvd_gcd (fun i _ => ⟨-x i, by
            have h := hcomp i
            linear_combination h⟩)
        rw [Finset.gcd_mul_left, hy, mul_one] at hd
        exact hd
      have h1n : b.natAbs ∣ a.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr hb_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have h2n : a.natAbs ∣ b.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr ha_dvd
        simpa [Int.abs_eq_normalize, Int.natAbs_abs] using h
      have heq : a.natAbs = b.natAbs := (Nat.dvd_antisymm h1n h2n).symm
      have hax : ∀ i, a * x i = -(b * y i) := by
        intro i
        have h := hcomp i
        linarith
      rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
      · -- `a = b`
        exact h2 (funext fun i => by
          have hh := hax i
          rw [h] at hh
          have hb0 : b * (x i + y i) = 0 := by
            have h1' : b * (x i + y i) = b * x i + b * y i := by ring
            rw [h1']; linarith
          have hx0 : x i + y i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
          simp only [Pi.neg_apply]
          linarith)
      · -- `a = -b`
        exact h1 (funext fun i => by
          have hh := hax i
          rw [h] at hh
          have hb0 : b * (y i - x i) = 0 := by
            have h1' : b * (y i - x i) = b * y i - b * x i := by ring
            rw [h1']; linarith
          have hy0 : y i - x i = 0 := (mul_eq_zero.mp hb0).resolve_left hb
          linarith)

end PrimAux

/-! ## The two bounds on `dmin 2 {x,y}` -/

section DminAux

variable {ι : Type*} [Fintype ι]

/-- `𝔡₂(x,y) ≥ 1`. -/
private lemma one_le_dmin_two {x y : ι → ℤ} (h : LinearIndependent ℤ ![x, y]) :
    1 ≤ dmin 2 ({x, y} : Set (ι → ℤ)) := by
  classical
  refine le_csInf ⟨detL (Submodule.span ℤ (Set.range ![x, y])),
    Submodule.span ℤ (Set.range ![x, y]), ?_, ?_, rfl⟩ ?_
  · rw [rk, Module.finrank_eq_card_basis (Module.Basis.span h)]; simp
  · intro z hz
    rcases hz with rfl | rfl
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  · rintro D ⟨L', -, -, rfl⟩
    exact MDEstimates.detL_one_le L'

/-- `𝔡₂(x,y) ≤ ‖x‖ ‖y‖`. -/
private lemma dmin_two_le_norm_mul {x y : ι → ℤ} (h : LinearIndependent ℤ ![x, y]) :
    dmin 2 ({x, y} : Set (ι → ℤ)) ≤ eNorm x * eNorm y := by
  classical
  obtain ⟨L, hL, hxL, hyL, hdet⟩ := Lat.span_pair_lattice x y h
  refine le_trans (csInf_le ?_ ?_) hdet
  · exact ⟨0, by rintro D ⟨L', -, -, rfl⟩; exact detL_nonneg_gram L'⟩
  · exact ⟨L, hL, (by
      intro z hz
      rcases hz with rfl | rfl
      · exact hxL
      · exact hyL), rfl⟩

end DminAux

/-! ## Dyadic shell index -/

/-- `shIdx s` is the exponent of the dyadic shell containing `s`: for `s ≥ 1` one has
`s ≤ 2^{shIdx s} ≤ 4 s`. -/
private def shIdx (s : ℝ) : ℕ := Nat.log 2 ⌈s⌉₊ + 1

private lemma le_two_pow_shIdx (s : ℝ) : s ≤ (2 : ℝ) ^ shIdx s := by
  have h1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have h2 : (⌈s⌉₊ : ℝ) < (2 : ℝ) ^ shIdx s := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) ⌈s⌉₊
    have hcast : (((2 : ℕ) ^ (Nat.log 2 ⌈s⌉₊ + 1) : ℕ) : ℝ) = (2 : ℝ) ^ shIdx s := by
      rw [shIdx]; push_cast; ring
    rw [← hcast]
    exact_mod_cast h
  linarith

private lemma two_pow_shIdx_le (s : ℝ) (hs : 1 ≤ s) : (2 : ℝ) ^ shIdx s ≤ 4 * s := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hcne : ⌈s⌉₊ ≠ 0 := by
    have : 1 ≤ ⌈s⌉₊ := Nat.one_le_ceil_iff.mpr hs0
    omega
  have h1 : (2 : ℕ) ^ Nat.log 2 ⌈s⌉₊ ≤ ⌈s⌉₊ := Nat.pow_log_le_self 2 hcne
  have h1r : (2 : ℝ) ^ Nat.log 2 ⌈s⌉₊ ≤ (⌈s⌉₊ : ℝ) := by exact_mod_cast h1
  have h2 : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one (le_of_lt hs0)
  have h3 : (2 : ℝ) ^ shIdx s = 2 * (2 : ℝ) ^ (Nat.log 2 ⌈s⌉₊) := by
    rw [shIdx, pow_succ]; ring
  rw [h3]
  linarith

/-- Dyadic shell bound. -/
private lemma inv_pow_le_shell (d : ℕ) (s : ℝ) (hs : 1 ≤ s) {I : ℕ} (hI : shIdx s ≤ I) :
    1 / s ^ (d - 1) ≤ (4 : ℝ) ^ (d - 1) *
      ∑ i ∈ Finset.range (I + 1),
        (if s ≤ (2 : ℝ) ^ i then (1 / (2 : ℝ) ^ i) ^ (d - 1) else 0) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hmem : shIdx s ∈ Finset.range (I + 1) := Finset.mem_range.mpr (by omega)
  have hcond : s ≤ (2 : ℝ) ^ shIdx s := le_two_pow_shIdx s
  have hle := Finset.single_le_sum
    (f := fun i => (if s ≤ (2 : ℝ) ^ i then (1 / (2 : ℝ) ^ i) ^ (d - 1) else 0))
    (fun i _ => by split <;> positivity) hmem
  rw [if_pos hcond] at hle
  have h4 : (2 : ℝ) ^ shIdx s ≤ 4 * s := two_pow_shIdx_le s hs
  have hkey : 1 / s ^ (d - 1) ≤ (4 : ℝ) ^ (d - 1) * (1 / (2 : ℝ) ^ shIdx s) ^ (d - 1) := by
    have h4' : (1 : ℝ) / (4 * s) ≤ 1 / (2 : ℝ) ^ shIdx s := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using h4
    have hpow : (1 / (4 * s)) ^ (d - 1) ≤ (1 / (2 : ℝ) ^ shIdx s) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) h4' (d - 1)
    have heq : (1 : ℝ) / s ^ (d - 1) = (4 : ℝ) ^ (d - 1) * (1 / (4 * s)) ^ (d - 1) := by
      rw [div_pow, one_pow, mul_pow]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc (1 : ℝ) / s ^ (d - 1)
      ≤ (4 : ℝ) ^ (d - 1) * (1 / (2 : ℝ) ^ shIdx s) ^ (d - 1) := hkey
    _ ≤ (4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1),
          (if s ≤ (2 : ℝ) ^ i then (1 / (2 : ℝ) ^ i) ^ (d - 1) else 0) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
section

open Work.HP.NA

/-- `gcdMinors2 x y ∣ gcdMinors2 (ν x) (ν y)`: every `2 × 2` minor of the Veronese pair
is a polynomial combination of the minors of `(x,y)`. -/
private lemma gcdMinors2_dvd_veronese (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) :
    gcdMinors2 x y ∣ gcdMinors2 (veronese d n x) (veronese d n y) := by
  classical
  set G : ℤ := gcdMinors2 x y with hG
  set q : ℕ := G.natAbs with hq
  have hqG : (q : ℤ) = G := by rw [hq]; exact Int.natAbs_of_nonneg (DGG.gcdMinors2_nonneg x y)
  have hmin : ∀ i j : Fin (n + 1),
      ((x i : ZMod q) * (y j : ZMod q)) = (x j : ZMod q) * (y i : ZMod q) := by
    intro i j
    have hdiv : (q : ℤ) ∣ (x i * y j - x j * y i) := by
      rw [hqG]
      exact (NA.gcdMinors2_dvd_iff G x y).mp dvd_rfl i j
    have hcast : (((x i * y j - x j * y i : ℤ)) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    push_cast at hcast
    linear_combination hcast
  rw [← hqG]
  refine (NA.gcdMinors2_dvd_iff ((q : ℤ)) (veronese d n x) (veronese d n y)).mpr ?_
  intro m m'
  have hswap := veronese_swap (R := ZMod q) (fun i => (x i : ZMod q)) (fun i => (y i : ZMod q))
    hmin d (fun i => (m.1 i : ℕ)) (fun i => (m'.1 i : ℕ)) m.2 m'.2
  have hxcast : ∀ m : Mon d n,
      ((veronese d n x m : ℤ) : ZMod q) = veronese d n (fun i => (x i : ZMod q)) m := by
    intro m
    simp only [veronese, Int.cast_prod, Int.cast_pow]
  have hycast : ∀ m : Mon d n,
      ((veronese d n y m : ℤ) : ZMod q) = veronese d n (fun i => (y i : ZMod q)) m := by
    intro m
    simp only [veronese, Int.cast_prod, Int.cast_pow]
  have h0 : (((veronese d n x m * veronese d n y m'
      - veronese d n x m' * veronese d n y m : ℤ)) : ZMod q) = 0 := by
    push_cast
    rw [hxcast m, hxcast m', hycast m, hycast m']
    simp only [veronese]
    linear_combination hswap
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

/-- `gcdMinors2 (ν x) (ν y) ∣ gcdMinors2 x y` for primitive `x, y`: a prime power dividing
the gcd of the Veronese minors divides every minor of `(x,y)` (paper's Lemma G). -/
private lemma veronese_dvd_gcdMinors2 (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) :
    gcdMinors2 (veronese d n x) (veronese d n y) ∣ gcdMinors2 x y := by
  classical
  set H : ℤ := gcdMinors2 (veronese d n x) (veronese d n y) with hH
  have hH0 : 0 ≤ H := DGG.gcdMinors2_nonneg _ _
  have hHnat : (H.natAbs : ℤ) = H := Int.natAbs_of_nonneg hH0
  -- the per-prime-power step
  have key : ∀ (p k : ℕ), p.Prime → ((p : ℤ) ^ k) ∣ H →
      ∀ i j : Fin (n + 1), ((p : ℤ) ^ k) ∣ (x i * y j - x j * y i) := by
    intro p k hp hpk i j
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    have hpH : (p : ℤ) ∣ H := by
      have h1 : (1 : ℕ) ≤ k := hkpos
      have h2 := dvd_trans (pow_dvd_pow (p : ℤ) h1) hpk
      rwa [pow_one] at h2
    -- step 1: for every `t`, `p^k ∣ (x t * y t)^{d-1} * (x i * y j - x j * y i)`
    have hstep : ∀ t : Fin (n + 1),
        ((p : ℤ) ^ k) ∣ (x t * y t) ^ (d - 1) * (x i * y j - x j * y i) := by
      intro t
      have h1 : H ∣ (veronese d n x (monDij d n hd t i) * veronese d n y (monDij d n hd t j)
          - veronese d n x (monDij d n hd t j) * veronese d n y (monDij d n hd t i)) :=
        (NA.gcdMinors2_dvd_iff H (veronese d n x) (veronese d n y)).mp dvd_rfl
          (monDij d n hd t i) (monDij d n hd t j)
      have h2 := dvd_trans hpk h1
      rw [NA.veronese_monDij d n hd x t i, NA.veronese_monDij d n hd y t j,
          NA.veronese_monDij d n hd x t j, NA.veronese_monDij d n hd y t i] at h2
      convert h2 using 1
      ring
    -- step 2: some `t` has `p ∤ x t * y t`
    have hex : ∃ t : Fin (n + 1), ¬ ((p : ℤ) ∣ x t * y t) := by
      by_contra hcon
      push_neg at hcon
      have hxex : ∃ t : Fin (n + 1), ¬ ((p : ℤ) ∣ x t) := by
        by_contra hcon2
        push_neg at hcon2
        have hgcd : (p : ℤ) ∣ Finset.univ.gcd x := Finset.dvd_gcd (fun t _ => hcon2 t)
        rw [hx] at hgcd
        exact hpz.not_dvd_one hgcd
      obtain ⟨t1, ht1⟩ := hxex
      have hy1 : (p : ℤ) ∣ y t1 := by
        rcases hpz.dvd_or_dvd (hcon t1) with h | h
        · exact absurd h ht1
        · exact h
      have hyex : ∃ t : Fin (n + 1), ¬ ((p : ℤ) ∣ y t) := by
        by_contra hcon3
        push_neg at hcon3
        have hgcd : (p : ℤ) ∣ Finset.univ.gcd y := Finset.dvd_gcd (fun t _ => hcon3 t)
        rw [hy] at hgcd
        exact hpz.not_dvd_one hgcd
      obtain ⟨t0, ht0⟩ := hyex
      have hx0 : (p : ℤ) ∣ x t0 := by
        rcases hpz.dvd_or_dvd (hcon t0) with h | h
        · exact h
        · exact absurd h ht0
      -- the minor of the pair `(νx, νy)` at `(ξ_{t0}^d, ξ_{t1}^d)`
      have h1 : H ∣ (veronese d n x (monDi d n t0) * veronese d n y (monDi d n t1)
          - veronese d n x (monDi d n t1) * veronese d n y (monDi d n t0)) :=
        (NA.gcdMinors2_dvd_iff H (veronese d n x) (veronese d n y)).mp dvd_rfl
          (monDi d n t0) (monDi d n t1)
      rw [NA.veronese_monDi, NA.veronese_monDi, NA.veronese_monDi, NA.veronese_monDi] at h1
      have hp1 : (p : ℤ) ∣ x t0 ^ d * y t1 ^ d :=
        dvd_mul_of_dvd_left (dvd_pow hx0 (by omega : d ≠ 0)) _
      have hp2 : ¬ ((p : ℤ) ∣ x t1 ^ d * y t0 ^ d) := by
        intro hcon4
        rcases hpz.dvd_or_dvd hcon4 with h | h
        · exact ht1 (hpz.dvd_of_dvd_pow h)
        · exact ht0 (hpz.dvd_of_dvd_pow h)
      have : (p : ℤ) ∣ x t0 ^ d * y t1 ^ d := hp1
      have hcon5 : ¬ ((p : ℤ) ∣ x t0 ^ d * y t1 ^ d - x t1 ^ d * y t0 ^ d) := by
        intro hcon6
        apply hp2
        have : x t1 ^ d * y t0 ^ d = x t0 ^ d * y t1 ^ d - (x t0 ^ d * y t1 ^ d - x t1 ^ d * y t0 ^ d) := by ring
        rw [this]
        exact dvd_sub hp1 hcon6
      exact hcon5 (dvd_trans hpH h1)
    obtain ⟨t, ht⟩ := hex
    have ha : ¬ ((p : ℤ) ∣ (x t * y t) ^ (d - 1)) :=
      fun hh => ht (hpz.dvd_of_dvd_pow hh)
    exact NA.dvd_of_dvd_mul_of_not_dvd_pow hpz ha (hstep t)
  -- assembly
  have hnat : H.natAbs ∣ (gcdMinors2 x y).natAbs := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hpkH : ((p : ℤ) ^ k) ∣ H := by
      obtain ⟨m, hm⟩ := hpk
      refine ⟨(m : ℤ), ?_⟩
      rw [← hHnat, hm]
      push_cast
      ring
    have hG : ((p : ℤ) ^ k) ∣ gcdMinors2 x y :=
      (NA.gcdMinors2_dvd_iff ((p : ℤ) ^ k) x y).mpr (key p k hp hpkH)
    have h2 : (((p : ℤ) ^ k).natAbs) ∣ (gcdMinors2 x y).natAbs := Int.natAbs_dvd_natAbs.mpr hG
    simpa using h2
  exact Int.natAbs_dvd_natAbs.mp hnat


/-- **Browning--Le Boudec--Sawin, Lemma G**: for primitive `x, y` the gcd of the `2 × 2` minors of
the Veronese pair `(ν_{d,n}(x), ν_{d,n}(y))` equals the gcd of the `2 × 2` minors of `(x, y)`. -/
private lemma gcdMinors2_veronese_eq (d n : ℕ) (hd : 1 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) :
    gcdMinors2 (veronese d n x) (veronese d n y) = gcdMinors2 x y := by
  have h1 := gcdMinors2_dvd_veronese d n hd x y hx hy
  have h2 := veronese_dvd_gcdMinors2 d n hd x y hx hy
  have hn : (gcdMinors2 (veronese d n x) (veronese d n y)).natAbs = (gcdMinors2 x y).natAbs :=
    Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr h2) (Int.natAbs_dvd_natAbs.mpr h1)
  have hnn1 : 0 ≤ gcdMinors2 (veronese d n x) (veronese d n y) := DGG.gcdMinors2_nonneg _ _
  have hnn2 : 0 ≤ gcdMinors2 x y := DGG.gcdMinors2_nonneg _ _
  calc gcdMinors2 (veronese d n x) (veronese d n y)
      = ((gcdMinors2 (veronese d n x) (veronese d n y)).natAbs : ℤ) := (Int.natAbs_of_nonneg hnn1).symm
    _ = ((gcdMinors2 x y).natAbs : ℤ) := by rw [hn]
    _ = gcdMinors2 x y := Int.natAbs_of_nonneg hnn2


end

/-! ## The pointwise bound `det Γ_{x,y} ≫ 𝔡₂(x,y) ‖x‖^{d-1} ‖y‖^{d-1}` -/

/-- The paper's "Lemma upper and lower bounds det": for primitive `x, y` with `x ≠ ±y`,
`det Γ_{x,y} ≫ 𝔡₂(x,y) ‖x‖^{d-1} ‖y‖^{d-1}`.

Combines the exact formulas `det Γ_{x,y} = ‖ν(x)∧ν(y)‖/𝓖(νx,νy)` and
`𝔡₂(x,y) = ‖x∧y‖/𝓖(x,y)` (`Work.HP.det_gam_gen`), the invariance `𝓖(νx,νy) = 𝓖(x,y)`
(`Work.HP.EE.gcdMinors_veronese`) and the Cauchy--Schwarz/Veronese angular bound
`‖ν(x)∧ν(y)‖ ≫ ‖x‖^{d-1}‖y‖^{d-1}‖x∧y‖` (`Work.HP.EE.wedgeNorm_veronese`). -/
private lemma detL_Gam_lower_aux (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      C * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1))
        ≤ detL (Gam d n x y) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := EE.wedgeNorm_veronese d n hd
  refine ⟨c₁, hc₁pos, ?_⟩
  intro x y hx hy h1 h2
  have hind := linearIndependent_of_isPrim hx hy h1 h2
  have hnu := Sig2.nu_indep d n hd x y hx hy h1 h2
  have hdet : detL (Gam d n x y) =
      wedgeNorm (veronese d n x) (veronese d n y) / (gcdMinors2 x y : ℝ) := by
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl,
      (det_gam_gen (veronese d n x) (veronese d n y) hnu).1,
      gcdMinors2_veronese_eq d n (by omega) x y hx hy]
  have hdmin : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) = wedgeNorm x y / (gcdMinors2 x y : ℝ) := by
    rw [(det_gam_gen x y hind).2, (det_gam_gen x y hind).1]
  have hgpos : 0 < (gcdMinors2 x y : ℝ) := by
    exact_mod_cast DGG.gcdMinors2_pos x y hind
  calc c₁ * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1))
      = c₁ * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y) /
          (gcdMinors2 x y : ℝ) := by
        rw [hdmin]
        field_simp
    _ = c₁ * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y / (gcdMinors2 x y : ℝ) := by
        ring
    _ ≤ wedgeNorm (veronese d n x) (veronese d n y) / (gcdMinors2 x y : ℝ) :=
        div_le_div_of_nonneg_right (hc₁ x y) (le_of_lt hgpos)
    _ = detL (Gam d n x y) := hdet.symm


/-- `1 ≤ λ_j` for a nonzero index. -/
private lemma lam_ge_one' {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℤ)) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ rk L) : 1 ≤ lam L j := by
  rw [lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L hjk) ?_
  rintro r ⟨hr0, f, hfL, hfLI, hfr⟩
  exact le_trans (one_le_eNorm_of_ne_zero (hfLI.ne_zero ⟨0, hj⟩)) (hfr ⟨0, hj⟩)

/-- A tuple of independent lattice vectors bounds the corresponding successive minimum. -/
private lemma lam_le_of_tuple' {n : ℕ} {M : Submodule ℤ (Fin (n + 1) → ℤ)} {j : ℕ}
    {f : Fin j → (Fin (n + 1) → ℤ)} (hf : ∀ k, f k ∈ M) (hind : LinearIndependent ℤ f)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : ∀ k, eNorm (f k) ≤ x) : lam M j ≤ x := by
  rw [lam]
  refine csInf_le ⟨0, fun r hr => hr.1⟩ ⟨hx0, f, hf, hind, hx⟩

/-- `r = 2` form of `Work.HP.win_membership`. -/
private lemma win_membership_two (n : ℕ)
    (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ)
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = 2) (hdet : detL L ≤ Δ + 1)
    (hmink : (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hwin : (∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j)) ∧
      (∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin 2 L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊)) :
    Monotone (kwin 2 L) ∧
      (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ ∧
      (∀ j : Fin 2, kwin 2 L j ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊) := by
  have hlam : ∏ j : Fin 2, lam L (j.1 + 1) ≤ Kmink * (Δ + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun j => lam L (j + 1)) 2, ← hrL]
    calc ∏ j ∈ Finset.range (rk L), lam L (j + 1)
        ≤ Kmink * detL L := hmink
      _ ≤ Kmink * (Δ + 1) := mul_le_mul_of_nonneg_left hdet (by linarith)
  have hprod : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have hstep1 : ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) := by
      apply Finset.prod_le_prod₀
      · intro j _; positivity
      · intro j _; exact hwin.2.1 j
    have hstep2 : ∏ j : Fin 2, (2 * lam L (j.1 + 1))
        = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)
        ≤ ∏ j : Fin 2, (2 * lam L (j.1 + 1)) := hstep1
      _ = (2 : ℝ) ^ 2 * ∏ j : Fin 2, lam L (j.1 + 1) := hstep2
      _ ≤ (2 : ℝ) ^ 2 * (Kmink * (Δ + 1)) :=
            mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by ring
  have hM : 1 ≤ (2 : ℝ) ^ 2 * Kmink * (Δ + 1) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 2 := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Δ + 1 := by linarith
    have ha : (1 : ℝ) ≤ (2 : ℝ) ^ 2 * Kmink := by nlinarith [h1, hKmink]
    have hb : (0 : ℝ) < (2 : ℝ) ^ 2 * Kmink := by positivity
    nlinarith [ha, h2, hb]
  refine ⟨hwin.2.2.1, hwin.2.2.2 _ hM hprod, ?_⟩
  intro j
  exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
    (hwin.2.2.2 _ hM hprod)

/-- The `r = 2` window exponents `kwin 2 L` have the expected properties. -/
private lemma kwin_specs_two (n : ℕ) (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = 2) :
    (∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j)) ∧
      (∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1)) ∧
      Monotone (kwin 2 L) ∧
      (∀ M : ℝ, 1 ≤ M → (∏ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j)) ≤ M →
        (∑ j : Fin 2, kwin 2 L j) ≤ ⌈Real.logb 2 M⌉₊) := by
  have h1 : ∀ j : Fin 2, 1 ≤ lam L (j.1 + 1) := by
    intro j
    refine lam_ge_one' L (by omega) ?_
    rw [hrL]; exact Nat.succ_le_of_lt j.2
  refine ⟨fun j => (ceil_logb_bounds (h1 j)).1, fun j => (ceil_logb_bounds (h1 j)).2, ?_, ?_⟩
  · intro i j hij
    have hle : lam L (i.1 + 1) ≤ lam L (j.1 + 1) :=
      lam_mono L (by omega) (by rw [hrL]; exact Nat.succ_le_of_lt j.2)
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (lt_of_lt_of_le one_pos (h1 i)) hle
    have h3 := Nat.ceil_mono h2
    simpa [kwin] using h3
  · intro M hM h
    exact sum_le_ceil_logb_of_prod hM h

/-- Per-window second-moment bound (`r = 2`). -/
private lemma fiber_bound_two (n : ℕ)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ j : Fin 2, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1))))
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin 2 → ℕ) (X Y : ℝ), rk L = 2 →
      (∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y → X ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ))) (k : Fin 2 → ℕ)
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y)
    (hwin1 : ∀ L ∈ T, ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j))
    (hwin2 : ∀ L ∈ T, ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1))
    (hk : ∀ L ∈ T, kwin 2 L = k) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
  set C : ℝ := Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))) with hC
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hper : ∀ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤ C := by
    intro L hL
    have hk2 : ∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1) :=
      fun j => by have := hwin2 L hL j; rwa [hk L hL] at this
    rw [hC]
    exact hbp L k X Y (hT L hL).2.1 hk2 hX hY hXY (hT L hL).2.2.2.1 (hT L hL).2.2.2.2
  have hcard : (T.card : ℝ) ≤
      Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) := by
    have hnum' := hnum (fun j => (2 : ℝ) ^ (k j)) T
      (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1,
        fun j => by have := hwin1 L hL j; rwa [hk L hL] at this⟩)
    have hprod : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)))
        = (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) := by
      have h1 : (∏ j : Fin 2, ((2 : ℝ) ^ (k j)) ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)))
          = ∏ j : Fin 2, (2 : ℝ) ^ (k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) :=
        Finset.prod_congr rfl (fun j _ => by rw [← pow_mul])
      rw [h1, Finset.prod_pow_eq_pow_sum]
    rwa [hprod] at hnum'
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ _L ∈ T, C := Finset.sum_le_sum hper
    _ = (T.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1)))) * C :=
        mul_le_mul_of_nonneg_right hcard hCnn
    _ = Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
        rw [hC]

/-- Clearing the window denominators, first term. -/
private lemma pow_exp1 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (2 * b))
      = (2 : ℝ) ^ (n * a + (n - 2) * b) := by
  have hexp : a * (n + 2) + b * n = 2 * a + 2 * b + (n * a + (n - 2) * b) := by
    have h2 : 2 ≤ n := hn
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((2 * a + 2 * b + (n * a + (n - 2) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring

/-- Clearing the window denominators, second term. -/
private lemma pow_exp2 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ b)
      = (2 : ℝ) ^ (n * a + (n - 1) * b) := by
  have hexp : a * (n + 2) + b * n = 2 * a + b + (n * a + (n - 1) * b) := by
    have h2 : 1 ≤ n := by omega
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((2 * a + b + (n * a + (n - 1) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring

/-- Clearing the window denominators, third term. -/
private lemma pow_exp3 (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    (2 : ℝ) ^ (a * (n + 2) + b * n) / ((2 : ℝ) ^ a * (2 : ℝ) ^ b)
      = (2 : ℝ) ^ ((n + 1) * a + (n - 1) * b) := by
  have hexp : a * (n + 2) + b * n = a + b + ((n + 1) * a + (n - 1) * b) := by
    have h2 : 1 ≤ n := by omega
    have hcast : ((a * (n + 2) + b * n : ℕ) : ℤ)
        = ((a + b + ((n + 1) * a + (n - 1) * b) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      ring
    exact_mod_cast hcast
  rw [div_eq_iff (by positivity), hexp, pow_add, pow_add]
  ring


/-- The window sum for `r = 2`. -/
private lemma windowSum_two (n : ℕ) (hn : 2 ≤ n)
    (Knum : ℝ) (hKnum : 0 < Knum)
    (hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ j : Fin 2, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      ((F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1))))
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin 2 → ℕ) (X Y : ℝ), rk L = 2 →
      (∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y → X ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
    (Karith : ℝ) (hKarith : 0 < Karith)
    (harith : ∀ (X Y Δ : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 =>
          Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊
            ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
        else 0))
      ≤ Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1))
    (X Y Δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ) (hXY : X ≤ Y)
    (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ)))
    (hT : ∀ L ∈ T, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) :
    (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
      (Knum * Ksmall ^ 2 * 16 * Karith) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  set N : ℕ := ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ with hN
  have hwin1 : ∀ L ∈ T, ∀ j : Fin 2, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j) :=
    fun L hL => (kwin_specs_two n L (hT L hL).2.1).1
  have hwin2 : ∀ L ∈ T, ∀ j : Fin 2, (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1) :=
    fun L hL => (kwin_specs_two n L (hT L hL).2.1).2.1
  have hwinL : ∀ L ∈ T, Monotone (kwin 2 L) ∧ (∑ j : Fin 2, kwin 2 L j) ≤ N ∧
      (∀ j : Fin 2, kwin 2 L j ≤ N) := by
    intro L hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT L hL
    rw [hN]
    exact win_membership_two n Kmink Δ hKmink hΔ L h2 h3 (hmink L h2) (kwin_specs_two n L h2)
  have hcond : ∀ k ∈ T.image (fun L => kwin 2 L), Monotone k ∧ (∑ j : Fin 2, k j) ≤ N := by
    intro k hk
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨(hwinL L hL).1, (hwinL L hL).2.1⟩
  have hcond4 : ∀ k ∈ T.image (fun L => kwin 2 L), Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧
      (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y := by
    intro k hk
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT L hL
    refine ⟨(hwinL L hL).1, (hwinL L hL).2.1, ?_, ?_⟩
    · have h := hwin2 L hL ⟨0, by omega⟩
      have h' : ((⟨0, by omega⟩ : Fin 2).1) + 1 = 1 := rfl
      rw [h'] at h
      exact le_trans h (by linarith [show lam L 1 ≤ X from h4])
    · have h := hwin2 L hL ⟨1, by omega⟩
      have h' : ((⟨1, by omega⟩ : Fin 2).1) + 1 = 2 := rfl
      rw [h'] at h
      exact le_trans h (by linarith [show lam L 2 ≤ Y from h5])
  have himg_sub : T.image (fun L => kwin 2 L) ⊆
      (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hwinL L hL).2.2 j)
  have hfib : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      = ∑ k ∈ T.image (fun L => kwin 2 L),
          ∑ L ∈ T.filter (fun L => kwin 2 L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image (fun L => kwin 2 L))
      (g := fun L => kwin 2 L) (fun i hi => Finset.mem_image_of_mem _ hi)
      (fun L => (ballCount L X : ℝ) * (ballCount L Y : ℝ))).symm
  have hinner : ∀ k ∈ T.image (fun L => kwin 2 L),
      (∑ L ∈ T.filter (fun L => kwin 2 L = k), (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
    intro k hk
    have hTf : ∀ L ∈ T.filter (fun L => kwin 2 L = k),
        IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y :=
      fun L hL => hT L (Finset.mem_of_mem_filter L hL)
    have hw1 : ∀ L ∈ T.filter (fun L => kwin 2 L = k), ∀ j : Fin 2,
        lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin 2 L j) :=
      fun L hL => hwin1 L (Finset.mem_of_mem_filter L hL)
    have hw2 : ∀ L ∈ T.filter (fun L => kwin 2 L = k), ∀ j : Fin 2,
        (2 : ℝ) ^ (kwin 2 L j) ≤ 2 * lam L (j.1 + 1) :=
      fun L hL => hwin2 L (Finset.mem_of_mem_filter L hL)
    have hkk : ∀ L ∈ T.filter (fun L => kwin 2 L = k), kwin 2 L = k :=
      fun L hL => (Finset.mem_filter.mp hL).2
    exact fiber_bound_two n Knum hKnum hnum Ksmall hKsmall hbp
      X Y Δ hX hY hXY (T.filter (fun L => kwin 2 L = k)) k hTf hw1 hw2 hkk
  have hterm : ∀ k : Fin 2 → ℕ,
      Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
        (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
      ≤ Knum * Ksmall ^ 2 * 16 *
        (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
          + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
          + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)) := by
    intro k
    have hexp : (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1)))
        = k 0 * (n + 2) + k 1 * n := by
      rw [Fin.sum_univ_two]
      norm_num
    have hn1 : (n + 1 - 1) = n := by omega
    have hn2 : (n + 1 - 3) = n - 2 := by omega
    have hn3 : (n + 1 - 2) = n - 1 := by omega
    rw [hn1, hn2, hn3, hexp]
    have hD1 : ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)) ≠ 0 := by positivity
    have hD2 : ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)) ≠ 0 := by positivity
    have hD3 : ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)) ≠ 0 := by positivity
    have e1 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
        = 16 * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 2) * k 1)) := by
      rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
          = 16 * (X ^ 2 * Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))) from by field_simp <;> ring]
      rw [pow_exp1 n hn (k 0) (k 1)]
      ring
    have e2 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
        ≤ 16 * (X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1)) := by
      rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
          = 8 * (X * Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))) from by field_simp <;> ring]
      rw [pow_exp2 n hn (k 0) (k 1)]
      have hx : 0 ≤ X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1) := by positivity
      nlinarith [hx]
    have e3 : (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
          * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
        ≤ 16 * (Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1)) := by
      rw [show (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))
          = 4 * (Y ^ 2) * ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
            / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))) from by field_simp <;> ring]
      rw [pow_exp3 n hn (k 0) (k 1)]
      have hy : 0 ≤ Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1) := by positivity
      nlinarith [hy]
    have hsplit : Knum * (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n) *
          (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
            + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
            + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))))
        = Knum * Ksmall ^ 2 *
          ((2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
              * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1)))
            + (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
              * (8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1)))
            + (2 : ℝ) ^ (k 0 * (n + 2) + k 1 * n)
              * (4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
      rw [mul_add, mul_add]
      ring
    rw [hsplit, e1]
    have hK0 : 0 ≤ Knum * Ksmall ^ 2 := mul_nonneg (le_of_lt hKnum) (sq_nonneg Ksmall)
    have h2e2 := mul_le_mul_of_nonneg_left e2 hK0
    have h2e3 := mul_le_mul_of_nonneg_left e3 hK0
    have h1 : 0 ≤ X ^ 2 * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 2) * k 1) := by positivity
    have h2' : 0 ≤ X * Y ^ 2 * (2 : ℝ) ^ (n * k 0 + (n - 1) * k 1) := by positivity
    have h3 : 0 ≤ Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n - 1) * k 1) := by positivity
    nlinarith [hK0, h2e2, h2e3, h1, h2', h3]
  have hstep2 : (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ ∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
            (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
              + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
              + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))) := by
    rw [hfib]
    exact Finset.sum_le_sum hinner
  have hstep3 : (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
            (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
              + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
              + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))))
      ≤ Knum * Ksmall ^ 2 * 16 *
        (∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0)) := by
    have hA : (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
            (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
              + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
              + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))))
        ≤ ∑ k ∈ T.image (fun L => kwin 2 L),
            Knum * Ksmall ^ 2 * 16 *
              (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
                + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
                + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    have hA2 : (∑ k ∈ T.image (fun L => kwin 2 L),
            Knum * Ksmall ^ 2 * 16 *
              (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
                + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
                + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)))
        = Knum * Ksmall ^ 2 * 16 *
          (∑ k ∈ T.image (fun L => kwin 2 L),
            (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1))) := by
      rw [Finset.mul_sum]
    have hA3 : (∑ k ∈ T.image (fun L => kwin 2 L),
            (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)))
        ≤ ∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) : Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0) := by
      rw [show (∑ k ∈ T.image (fun L => kwin 2 L),
            (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)))
          = ∑ k ∈ T.image (fun L => kwin 2 L),
            (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
                ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
              X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
                + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
                + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
            else 0) from
          Finset.sum_congr rfl (fun k hk => (if_pos (hcond4 k hk)).symm)]
      exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun k _ _ => by split <;> positivity)
    calc (∑ k ∈ T.image (fun L => kwin 2 L),
          Knum * (2 : ℝ) ^ (∑ j : Fin 2, k j * (n + 1 + 2 + 1 - 2 * (j.1 + 1))) *
            (Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
              + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
              + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))))
        ≤ _ := hA
      _ = _ := hA2
      _ ≤ Knum * Ksmall ^ 2 * 16 * _ := mul_le_mul_of_nonneg_left hA3 (by positivity)
  have hstep4 : (∑ k ∈ (Fintype.piFinset (fun _ : Fin 2 => Finset.range (N + 1)) :
          Finset (Fin 2 → ℕ)),
          (if Monotone k ∧ (∑ j : Fin 2, k j) ≤ N ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X
              ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0))
      = (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 =>
            Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊ + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊
              ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0)) := by
    rw [hN]
  calc (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ))
      ≤ _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ Knum * Ksmall ^ 2 * 16 * (Karith * X ^ 2 * Y ^ 2 * Δ ^ (n - 1)) := by
        rw [hstep4]
        exact mul_le_mul_of_nonneg_left (harith X Y Δ hX hY hΔ) (by positivity)
    _ = (Knum * Ksmall ^ 2 * 16 * Karith) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by ring


/-- The pair count is symmetric in the two height bounds. -/
private lemma ellXY_comm' (n : ℕ) (r : ℕ) (X Y Δ : ℝ) :
    ellXY n r X Y Δ = ellXY n r Y X Δ := by
  simp only [ellXY]
  apply Set.ncard_congr (fun p _ => (p.2, p.1))
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨?_, h3, h2, ?_⟩
    · rw [LinearIndependent.pair_iff] at h1 ⊢
      intro s t hst
      have h' := h1 t s (by simpa [add_comm] using hst)
      exact ⟨h'.2, h'.1⟩
    · simpa only [Set.pair_comm p.1 p.2] using h4
  · intro p q hp hq h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · intro q hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨?_, h3, h2, ?_⟩
    · rw [LinearIndependent.pair_iff] at h1 ⊢
      intro s t hst
      have h' := h1 t s (by simpa [add_comm] using hst)
      exact ⟨h'.2, h'.1⟩
    · simpa only [Set.pair_comm q.1 q.2] using h4

/-- Reduction of the pair count to a sum of `ballCount` products over a finite family of
primitive rank-`2` lattices. -/
private lemma ellXY_le_latSum_two (n : ℕ) (hn : 2 ≤ n) (X Y Δ : ℝ)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hΔ : 1 ≤ Δ) (hXY : X ≤ Y) :
    ∃ T : Finset (Submodule ℤ (Fin (n + 1) → ℤ)),
      (∀ L ∈ T, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) ∧
      (ellXY n 2 X Y Δ : ℝ) ≤ ∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ) := by
  classical
  set P : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧
      dmin 2 {p.1, p.2} ≤ Δ} with hP
  have hPfin : P.Finite :=
    (Set.Finite.prod (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X)
      (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) Y)).subset
      (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
  let Lat : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → Submodule ℤ (Fin (n + 1) → ℤ) := fun p =>
    if h : LinearIndependent ℤ ![p.1, p.2] ∧ dmin 2 {p.1, p.2} ≤ Δ then
      satLat (Submodule.span ℤ ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
    else ⊥
  have hLatspec : ∀ p ∈ P, IsPrimLat (Lat p) ∧ rk (Lat p) = 2 ∧ p.1 ∈ Lat p ∧ p.2 ∈ Lat p ∧
      detL (Lat p) ≤ Δ + 1 := by
    intro p hp
    have hp' : LinearIndependent ℤ ![p.1, p.2] ∧ dmin 2 {p.1, p.2} ≤ Δ := ⟨hp.1, hp.2.2.2⟩
    simp only [Lat, dif_pos hp']
    refine ⟨isPrimLat_satLat _, ?_, ?_, ?_, ?_⟩
    · rw [DGG.rk_sat_span_pair _ _ hp'.1]
    · exact le_satLat _ (Submodule.subset_span (by simp))
    · exact le_satLat _ (Submodule.subset_span (by simp))
    · rw [← DGG.dmin_pair_eq_detL_sat _ _ hp'.1]
      exact le_trans hp'.2 (by linarith)
  have hlam1 : ∀ p ∈ P, lam (Lat p) 1 ≤ X := by
    intro p hp
    obtain ⟨-, -, hmem, -, -⟩ := hLatspec p hp
    refine lam_le_of_tuple' (M := Lat p) (j := 1) (f := fun _ : Fin 1 => p.1)
      (fun k => hmem) ?_ (le_trans zero_le_one hX) (fun k => by simpa using hp.2.1)
    rw [linearIndependent_unique_iff]
    intro h
    exact (hp.1.ne_zero 0) (by simpa using h)
  have hlam2 : ∀ p ∈ P, lam (Lat p) 2 ≤ Y := by
    intro p hp
    obtain ⟨-, -, hmem1, hmem2, -⟩ := hLatspec p hp
    refine lam_le_of_tuple' (M := Lat p) (j := 2) (f := ![p.1, p.2])
      (fun k => by fin_cases k <;> assumption) hp.1 (le_trans zero_le_one hY) (fun k => ?_)
    fin_cases k
    · simpa using le_trans hp.2.1 hXY
    · simpa using hp.2.2.1
  refine ⟨(hPfin.toFinset).image Lat, ?_, ?_⟩
  · intro L hL
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL
    have hpP : p ∈ P := by rwa [Set.Finite.mem_toFinset] at hp
    exact ⟨(hLatspec p hpP).1, (hLatspec p hpP).2.1, (hLatspec p hpP).2.2.2.2,
      hlam1 p hpP, hlam2 p hpP⟩
  · have hcard : ((P.ncard : ℕ) : ℝ) =
        ∑ L ∈ (hPfin.toFinset).image Lat,
          (((hPfin.toFinset).filter (fun p => Lat p = L)).card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hPfin]
      rw [Finset.card_eq_sum_card_fiberwise (f := Lat) (s := hPfin.toFinset)
        (t := (hPfin.toFinset).image Lat) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
      push_cast
      rfl
    rw [ellXY, ← hP, hcard]
    refine Finset.sum_le_sum (fun L hL => ?_)
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hL
    have hp₀P : p₀ ∈ P := by rwa [Set.Finite.mem_toFinset] at hp₀
    obtain ⟨-, -, h1, h2, -⟩ := hLatspec p₀ hp₀P
    have hPLfin : ({v : Fin (n + 1) → ℤ | v ∈ Lat p₀ ∧ eNorm v ≤ X}).Finite :=
      (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).subset (fun v hv => hv.2)
    have hPMfin : ({v : Fin (n + 1) → ℤ | v ∈ Lat p₀ ∧ eNorm v ≤ Y}).Finite :=
      (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) Y).subset (fun v hv => hv.2)
    have hsub : ((hPfin.toFinset).filter (fun p => Lat p = Lat p₀)) ⊆
        (hPLfin.toFinset ×ˢ hPMfin.toFinset) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpT, hpg⟩ := hp
      have hpP : p ∈ P := by rwa [Set.Finite.mem_toFinset] at hpT
      obtain ⟨-, -, hmem1, hmem2, -⟩ := hLatspec p hpP
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨by rw [← hpg]; exact hmem1, hpP.2.1⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨by rw [← hpg]; exact hmem2, hpP.2.2.1⟩
    have hfib : (((hPfin.toFinset).filter (fun p => Lat p = Lat p₀)).card : ℝ) ≤
        ((hPLfin.toFinset ×ˢ hPMfin.toFinset).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine le_trans hfib ?_
    rw [Finset.card_product]
    push_cast
    have h1' : hPLfin.toFinset.card = ballCount (Lat p₀) X := by
      rw [← Set.ncard_eq_toFinset_card _ hPLfin]; rfl
    have h2' : hPMfin.toFinset.card = ballCount (Lat p₀) Y := by
      rw [← Set.ncard_eq_toFinset_card _ hPMfin]; rfl
    rw [h1', h2']

/-- The `r = 2` pair count, given the sharp rank-`2` lattice count and the rank-`2`
Minkowski product bound. -/
private lemma ellXY_two_of_two (n : ℕ) (hn : 2 ≤ n)
    (hnum0 : ∃ K : ℝ, 0 < K ∧ ∀ (s : Fin 2 → ℝ), (∀ j : Fin 2, 1 ≤ s j) →
      (({L : Submodule ℤ (Fin (n + 1) → ℤ) | IsPrimLat L ∧ rk L = 2 ∧
        (∀ j : Fin 2, lam L (j.1 + 1) ≤ s j)}.ncard : ℝ)
        ≤ K * ∏ j : Fin 2, s j ^ (Fintype.card (Fin (n + 1)) + 3 - 2 * (j.1 + 1))))
    (hmink0 : ∃ K : ℝ, 0 < K ∧ ∀ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = 2 →
      lam L 1 * lam L 2 ≤ K * detL L) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  classical
  obtain ⟨Knum, hKnumpos, hnum00⟩ := hnum0
  have hnumF := EE.numLattices_finset_of (ι := Fin (n + 1)) (K := Knum) hnum00
  have hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ j : Fin 2, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ (∀ j : Fin 2, lam L (j.1 + 1) ≤ s j)) →
      (F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)) := by
    intro s F hs hF
    refine (hnumF s hs F hF).trans (le_of_eq ?_)
    refine congrArg (fun x => Knum * x) ?_
    refine Finset.prod_congr rfl (fun j _ => ?_)
    first
      | rfl
      | (congr 1; simp only [Fintype.card_fin])
  obtain ⟨Km, hKmpos, hmink0'⟩ := hmink0
  have hKm1 : (1 : ℝ) ≤ max Km 1 := le_max_right _ _
  have hmink : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)), rk L = 2 →
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ (max Km 1) * detL L := by
    intro L hL
    have hprod2 : (∏ j ∈ Finset.range (rk L), lam L (j + 1)) = lam L 1 * lam L 2 := by
      rw [hL, Finset.prod_range_succ (f := fun j => lam L (j + 1)) 1, Finset.prod_range_one]
    rw [hprod2]
    exact (hmink0' L hL).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L))
  obtain ⟨K2, hK2pos, hK20⟩ := EEupper.ballCountRank2Mine (ι := Fin (n + 1))
  obtain ⟨KY, hKYpos, hKY0⟩ := EEupper.ballCountRankGe2Mine (ι := Fin (n + 1))
  have hKs : 0 < max K2 KY := lt_of_lt_of_le hK2pos (le_max_left _ _)
  have hsmall2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
      (ballCount L X : ℝ) ≤ (max K2 KY) * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := by
    intro L X h1 h2
    refine (hK20 L X h1 h2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have hX0 : 0 ≤ X := le_trans zero_le_one h2
    have h3 : 0 ≤ lam L 1 := lam_nonneg L 1
    have h4 : 0 ≤ lam L 2 := lam_nonneg L 2
    positivity
  have hsmallY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L →
      lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ (max K2 KY) * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    intro L Y h1 h2 h3
    refine (hKY0 L Y h1 h2 h3).trans (div_le_div_of_nonneg_right ?_ ?_)
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (le_trans zero_le_one h1) _)
    · exact mul_nonneg (lam_nonneg L 1) (pow_nonneg (lam_nonneg L 2) _)
  obtain ⟨Cdy, hCdypos, hdy0⟩ := dyadic_sum_r2 (n + 1) (by omega)
  have harith : ∀ (X Y Δ : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset
          (fun _ : Fin 2 => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ 2 * (max Km 1) * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ 2 * (max Km 1) * (Δ + 1))⌉₊
            ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
        else 0))
      ≤ (Cdy * (8 * (max Km 1)) ^ (n - 1)) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
    intro X Y Δ hX hY hΔ
    set V : ℝ := (2 : ℝ) ^ 2 * (max Km 1) * (Δ + 1) with hV
    have hVpos : 0 < V := by positivity
    have hV1 : 1 ≤ V := by
      rw [hV]
      nlinarith [hKm1, hΔ]
    have hlog : 0 ≤ Real.logb 2 V := Real.logb_nonneg (by norm_num) hV1
    have h := hdy0 X Y (Real.logb 2 V) hX hY hlog
    have hpow : (2 : ℝ) ^ ((↑(n + 1) - 2 : ℝ) * Real.logb 2 V) = V ^ (n - 1) := by
      have he : (↑(n + 1) - 2 : ℝ) = ↑(n - 1) := by
        have h1 : (↑(n + 1) : ℝ) - 2 = ↑((n + 1) - 2) :=
          (Nat.cast_sub (show 2 ≤ n + 1 by omega)).symm
        rw [h1, show n + 1 - 2 = n - 1 by omega]
      rw [he, mul_comm (↑(n - 1) : ℝ) (Real.logb 2 V),
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
        Real.rpow_logb (by norm_num) (by norm_num) hVpos]
    have hVle : V ≤ 8 * (max Km 1) * Δ := by
      have h1 : V = 4 * (max Km 1) * (Δ + 1) := by rw [hV]; ring
      rw [h1]
      nlinarith [hKm1, hΔ]
    calc (∑ k ∈ Fintype.piFinset
            (fun _ : Fin 2 => Finset.range (⌈Real.logb 2 V⌉₊ + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 V⌉₊
              ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
            X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
              + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
              + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
          else 0))
        ≤ Cdy * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((↑(n + 1) - 2 : ℝ) * Real.logb 2 V) := h
      _ = Cdy * X ^ 2 * Y ^ 2 * V ^ (n - 1) := by rw [hpow]
      _ ≤ Cdy * X ^ 2 * Y ^ 2 * (8 * (max Km 1) * Δ) ^ (n - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hVle _
      _ = (Cdy * (8 * (max Km 1)) ^ (n - 1)) * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
          rw [mul_pow]
          ring
  have hbp : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (k : Fin 2 → ℕ) (X Y : ℝ), rk L = 2 →
      (∀ j : Fin 2, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1)) → 1 ≤ X → 1 ≤ Y → X ≤ Y →
      lam L 1 ≤ X → lam L 2 ≤ Y →
      (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
        (max K2 KY) ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
          + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
          + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1))) :=
    fun L k X Y hrL hk2 hX hY hXY hlX hlY =>
      ball_prod_window_r2 n hn (max K2 KY) hKs hsmall2 hsmallY L hrL k hk2 X Y hX hY hXY hlX hlY
  have hW := windowSum_two n hn Knum hKnumpos hnum (max Km 1) hKm1 hmink (max K2 KY) hKs hbp
      (Cdy * (8 * (max Km 1)) ^ (n - 1)) (by positivity) harith
  refine ⟨Knum * (max K2 KY) ^ 2 * 16 * (Cdy * (8 * (max Km 1)) ^ (n - 1)), by positivity, ?_⟩
  intro X Y Δ hX hY hΔ
  rcases le_total X Y with hXY | hYX
  · obtain ⟨T, hT, hle⟩ := ellXY_le_latSum_two n hn X Y Δ hX hY hΔ hXY
    exact hle.trans (hW X Y Δ hX hY hΔ hXY T hT)
  · rw [ellXY_comm' n 2 X Y Δ]
    obtain ⟨T, hT, hle⟩ := ellXY_le_latSum_two n hn Y X Δ hY hX hΔ hYX
    refine hle.trans ?_
    refine (hW Y X Δ hY hX hΔ hYX T hT).trans (le_of_eq ?_)
    ring


/-- The `r = 2` pair count, from the sharp rank-`2` lattice count and the rank-`2`
Minkowski product bound. -/
theorem ellXY_two_pub (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  have hcov : EEupper.CovStep (ι := Fin (n + 1)) :=
    fun Φ u v hbij => Work.EEupper.latCovolStep Φ u v hbij
  obtain ⟨Kmk, hKmkpos, hKmk⟩ := EEupper.minkowskiProdMine n hcov
  have hKmk0 : 0 ≤ Kmk := le_of_lt hKmkpos
  have hmink0 : ∃ K : ℝ, 0 < K ∧ ∀ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = 2 →
      lam L 1 * lam L 2 ≤ K * detL L := by
    refine ⟨Kmk, hKmkpos, fun L hL => ?_⟩
    have h := hKmk L
    rw [hL] at h
    rwa [show (∏ j ∈ Finset.range 2, lam L (j + 1)) = lam L 1 * lam L 2 by
      simp [Finset.prod_range_succ]] at h
  exact ellXY_two_of_two n hn (EEupper.numLattices2Mine n Kmk hKmk0 hKmk) hmink0
end Work.HP

namespace Work.HP.EE

/-- Compatibility alias for `Work.HP.ellXY_two_pub`. -/
theorem ellXY_two_pub (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) :=
  Work.HP.ellXY_two_pub n hn

end Work.HP.EE
