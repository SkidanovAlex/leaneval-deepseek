import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Lat.span_pair_lattice
import Submission.Work.HP.HPgram
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.EE.wedgeNorm_veronese
import Submission.Work.HP.EEupper.detL_Gam_lower
import Submission.Work.HP.EE.ellXY_two_pub

/-!
# `Work.HP.EE_bound`

Browning--Le Boudec--Sawin, Lemma E (upper half): the average of `1 / det Γ_{x,y}` over the
pairs `(x,y) ∈ Ω_{d,n}(B)` of primitive vectors of norm at most `B^{1/(n+1-d)}` with `x ≠ ±y`
is `≪ B²`.
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
lemma smul_int_eq_zero_iff {v : ι → ℤ} {a : ℤ} (ha : a ≠ 0) : a • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  · rintro rfl; simp

/-- Two primitive vectors that are not equal up to sign are linearly independent over `ℤ`. -/
lemma linearIndependent_of_isPrim {x y : ι → ℤ} (hx : IsPrim x) (hy : IsPrim y)
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
lemma one_le_dmin_two {x y : ι → ℤ} (h : LinearIndependent ℤ ![x, y]) :
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
lemma dmin_two_le_norm_mul {x y : ι → ℤ} (h : LinearIndependent ℤ ![x, y]) :
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

/-! ## The pointwise bound and the weighted pair count -/

/-- The paper's "Lemma upper and lower bounds det": `det Γ_{x,y} ≫ 𝔡₂(x,y) ‖x‖^{d-1} ‖y‖^{d-1}`. -/
private lemma detL_Gam_lower (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      C * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1))
        ≤ detL (Gam d n x y) :=
  Work.HP.EEupper.detL_Gam_lower d n hd hn

/-- The `r = 2` case of the paper's Lemma `l_r(X,Y)`. -/
private lemma tmp_ellXY_two (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) :=
  Work.HP.ellXY_two_pub n hn

/-- The geometric bound `Σ_{i=0}^{N} r^i ≤ 2 r^N` for `r ≥ 2`. -/
private lemma geom_two (r : ℝ) (hr : 2 ≤ r) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), r ^ i ≤ 2 * r ^ N := by
  have hr1 : 0 < r := by linarith
  have hrne : r ≠ 1 := by linarith
  rw [geom_sum_eq hrne, div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)]
  have hpow : (0 : ℝ) < r ^ N := pow_pos hr1 N
  have h2 : 0 ≤ r ^ N * (r - 2) := mul_nonneg (le_of_lt hpow) (by linarith)
  rw [pow_succ]
  nlinarith [hpow, h2]

/-- Weighted pair count: `Σ 1/𝔡₂(x,y) ≪ X²Y²Δ^{n-2}` over pairs with `‖x‖ ≤ X`, `‖y‖ ≤ Y`,
`𝔡₂(x,y) ≤ Δ`. -/
private lemma weighted_count (n : ℕ) (hn : 3 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X Y Δ : ℝ) (F : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (∀ p ∈ F, LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧
        dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ) →
      (∑ p ∈ F, 1 / dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
        ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 2) := by
  obtain ⟨K₂, hK₂pos, hK₂⟩ := tmp_ellXY_two n (by omega)
  refine ⟨8 * 4 ^ (n - 2) * K₂, by positivity, ?_⟩
  intro X Y Δ F hX hY hΔ hF
  set M : ℕ := Nat.log 2 ⌈Δ⌉₊ + 1 with hM
  have hΔ0 : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have h2M : (2 : ℝ) ^ M ≤ 4 * Δ := by
    rw [hM]; exact two_pow_shIdx_le Δ hΔ
  -- pointwise layer cake
  have hpt : ∀ p ∈ F, 1 / dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤
      ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
        (if dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m then (1 : ℝ) else 0) := by
    intro p hp
    obtain ⟨hli, -, -, hdΔ⟩ := hF p hp
    set t := dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) with ht
    have ht1 : 1 ≤ t := one_le_dmin_two hli
    have hlim : shIdx t ≤ M := by
      rw [shIdx, hM]
      have hceil : ⌈t⌉₊ ≤ ⌈Δ⌉₊ := Nat.ceil_mono hdΔ
      have hlog : Nat.log 2 ⌈t⌉₊ ≤ Nat.log 2 ⌈Δ⌉₊ := Nat.log_mono_right hceil
      omega
    have hmem : shIdx t ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
    have hcond : t ≤ (2 : ℝ) ^ shIdx t := le_two_pow_shIdx t
    have hsingle := Finset.single_le_sum
      (f := fun m => 4 * (1 / (2 : ℝ) ^ m) *
        (if t ≤ (2 : ℝ) ^ m then (1 : ℝ) else 0))
      (fun m _ => by split <;> positivity) hmem
    rw [if_pos hcond, mul_one] at hsingle
    have h4 : (2 : ℝ) ^ shIdx t ≤ 4 * t := two_pow_shIdx_le t ht1
    have hval : 1 / t ≤ 4 * (1 / (2 : ℝ) ^ shIdx t) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using h4
    linarith
  -- swap the sums and bound each count
  have hcnt : ∀ m ∈ Finset.range (M + 1),
      ((F.filter (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m)).card : ℝ)
        ≤ K₂ * X ^ 2 * Y ^ 2 * ((2 : ℝ) ^ m) ^ (n - 1) := by
    intro m hm
    have h2m : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hsub : ((F.filter (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m) :
            Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))) : Set _)
        ⊆ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
            eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧
            dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m} := by
      intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      obtain ⟨hFp, hpm⟩ := hp
      obtain ⟨hli, h1, h2, -⟩ := hF p hFp
      exact ⟨hli, h1, h2, hpm⟩
    have hfin2 : ({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
            eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧
            dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m} : Set _).Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).prod
        (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) Y)).subset
        (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
    have h1' := Set.ncard_le_ncard hsub hfin2
    rw [Set.ncard_coe_finset] at h1'
    have h2' : ((ellXY n 2 X Y ((2 : ℝ) ^ m) : ℕ) : ℝ)
        ≤ K₂ * X ^ 2 * Y ^ 2 * ((2 : ℝ) ^ m) ^ (n - 1) := hK₂ X Y ((2 : ℝ) ^ m) hX hY h2m
    exact le_trans (by exact_mod_cast h1') h2'
  have hswap : ∑ p ∈ F, ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
        (if dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m then (1 : ℝ) else 0)
      = ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
        ((F.filter (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
  have hpow : ∀ m : ℕ, (1 / (2 : ℝ) ^ m) * ((2 : ℝ) ^ m) ^ (n - 1) = ((2 : ℝ) ^ m) ^ (n - 2) := by
    intro m
    have h2m0 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have h : ((2 : ℝ) ^ m) ^ (n - 1) = ((2 : ℝ) ^ m) ^ (n - 2) * (2 : ℝ) ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h, div_mul_eq_mul_div, one_mul]
    field_simp
  have hgeom : ∑ m ∈ Finset.range (M + 1), ((2 : ℝ) ^ m) ^ (n - 2) ≤ 2 * ((2 : ℝ) ^ M) ^ (n - 2) := by
    have h1 : 1 ≤ n - 2 := by omega
    have hr : (2 : ℝ) ≤ (2 : ℝ) ^ (n - 2) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (n - 2) := pow_le_pow_right₀ (by norm_num) h1
    calc ∑ m ∈ Finset.range (M + 1), ((2 : ℝ) ^ m) ^ (n - 2)
        = ∑ m ∈ Finset.range (M + 1), ((2 : ℝ) ^ (n - 2)) ^ m := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 2 * ((2 : ℝ) ^ (n - 2)) ^ M := geom_two _ hr M
      _ = 2 * ((2 : ℝ) ^ M) ^ (n - 2) := by
          rw [← pow_mul, ← pow_mul, mul_comm (n - 2) M]
  calc ∑ p ∈ F, 1 / dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
      ≤ ∑ p ∈ F, ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
          (if dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
          ((F.filter (fun p => dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ (2 : ℝ) ^ m)).card : ℝ) :=
        hswap
    _ ≤ ∑ m ∈ Finset.range (M + 1), 4 * (1 / (2 : ℝ) ^ m) *
          (K₂ * X ^ 2 * Y ^ 2 * ((2 : ℝ) ^ m) ^ (n - 1)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have h4 : (0:ℝ) ≤ 4 * (1 / (2 : ℝ) ^ m) := by positivity
        exact mul_le_mul_of_nonneg_left (hcnt m hm) h4
    _ = 4 * K₂ * X ^ 2 * Y ^ 2 * ∑ m ∈ Finset.range (M + 1), ((2 : ℝ) ^ m) ^ (n - 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hkey : 4 * (1 / (2 : ℝ) ^ m) * (K₂ * X ^ 2 * Y ^ 2 * ((2 : ℝ) ^ m) ^ (n - 1))
            = 4 * K₂ * X ^ 2 * Y ^ 2 * ((1 / (2 : ℝ) ^ m) * ((2 : ℝ) ^ m) ^ (n - 1)) := by
          ring
        rw [hkey, hpow m]
    _ ≤ 4 * K₂ * X ^ 2 * Y ^ 2 * (2 * ((2 : ℝ) ^ M) ^ (n - 2)) := by
        have h0 : (0:ℝ) ≤ 4 * K₂ * X ^ 2 * Y ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hgeom h0
    _ ≤ 4 * K₂ * X ^ 2 * Y ^ 2 * (2 * (4 * Δ) ^ (n - 2)) := by
        have h0 : (0:ℝ) ≤ 4 * K₂ * X ^ 2 * Y ^ 2 * 2 := by positivity
        have hmono : ((2 : ℝ) ^ M) ^ (n - 2) ≤ (4 * Δ) ^ (n - 2) :=
          pow_le_pow_left₀ (by positivity) h2M (n - 2)
        nlinarith [hmono, h0]
    _ = (8 * 4 ^ (n - 2) * K₂) * X ^ 2 * Y ^ 2 * Δ ^ (n - 2) := by
        rw [mul_pow]
        ring


/-- **Lemma E, upper half.** -/
theorem EE_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ B : ℝ, B₀ ≤ B → EE d n B ≤ K * B ^ 2 := by
  have hn3 : 3 ≤ n := by
    rcases eq_or_ne d 2 with h | h
    · subst h
      have h2 : n ≠ 2 := fun hn => h22 (by simp [hn])
      omega
    · omega
  obtain ⟨C, hCpos, hC⟩ := detL_Gam_lower d n hd hn3
  obtain ⟨K₃, hK₃pos, hK₃⟩ := weighted_count n hn3
  refine ⟨(1 / C) * 4 ^ (2 * (d - 1)) * K₃ * 2 ^ (2 * (n - 2)) * 4 * 4 ^ (2 * (n + 1 - d)), 1,
    by positivity, ?_⟩
  intro B hB
  have hB1 : 1 ≤ B := hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  set T : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hT
  have hden : (0 : ℝ) < (n : ℝ) + 1 - d := by
    have : (d : ℝ) ≤ n := by exact_mod_cast hdn
    linarith
  have hT1 : 1 ≤ T := Real.one_le_rpow hB1 (by positivity)
  set I : ℕ := Nat.log 2 ⌈T⌉₊ + 1 with hI
  have hIbound : (2 : ℝ) ^ I ≤ 4 * T := by
    rw [hI]; exact two_pow_shIdx_le T hT1
  have hfin : (Omega d n B).Finite := (MDBasic.finite_sets d n B B (fun _ => True)).2.2
  set G : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ := fun p => 1 / detL (Gam d n p.1 p.2) with hG
  have hsup : ((Omega d n B) ∩ Function.support G).Finite := hfin.subset Set.inter_subset_left
  have hEE : EE d n B = ∑ p ∈ hsup.toFinset, G p := by
    rw [EE, finsum_mem_eq_sum (fun p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) =>
      1 / detL (Gam d n p.1 p.2)) hsup]
  rw [hEE]
  have hsubO : hsup.toFinset ⊆ hfin.toFinset := by
    rw [Set.Finite.toFinset_subset, Set.Finite.coe_toFinset]
    exact Set.inter_subset_left
  have hmemO : ∀ p ∈ hsup.toFinset, p ∈ Omega d n B := fun p hp =>
    (Set.Finite.mem_toFinset hfin).mp (hsubO hp)
  -- abbreviations
  let AA : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
    fun p => 1 / dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
  let Phi : ℕ → (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
    fun i p => if eNorm p.1 ≤ (2 : ℝ) ^ i then (1 / (2 : ℝ) ^ i) ^ (d - 1) else 0
  let Psi : ℕ → (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
    fun j p => if eNorm p.2 ≤ (2 : ℝ) ^ j then (1 / (2 : ℝ) ^ j) ^ (d - 1) else 0
  -- Step 1: pointwise bound
  have hstep1 : ∑ p ∈ hsup.toFinset, G p ≤
      ∑ p ∈ hsup.toFinset, (1 / C) * AA p * ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) *
        ((4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hX1, hX2, hne1, hne2⟩ := hmemO p hp
    obtain ⟨hprim1, hle1⟩ := hX1
    obtain ⟨hprim2, hle2⟩ := hX2
    have hind := linearIndependent_of_isPrim hprim1 hprim2 hne1 hne2
    have hd1 : 1 ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := one_le_dmin_two hind
    have hge1 : 1 ≤ eNorm p.1 := one_le_eNorm_of_ne_zero (isPrim_ne_zero hprim1)
    have hge2 : 1 ≤ eNorm p.2 := one_le_eNorm_of_ne_zero (isPrim_ne_zero hprim2)
    have hI1 : shIdx (eNorm p.1) ≤ I := by
      rw [shIdx, hI]
      have hc : ⌈eNorm p.1⌉₊ ≤ ⌈T⌉₊ := Nat.ceil_mono hle1
      have hl : Nat.log 2 ⌈eNorm p.1⌉₊ ≤ Nat.log 2 ⌈T⌉₊ := Nat.log_mono_right hc
      omega
    have hI2 : shIdx (eNorm p.2) ≤ I := by
      rw [shIdx, hI]
      have hc : ⌈eNorm p.2⌉₊ ≤ ⌈T⌉₊ := Nat.ceil_mono hle2
      have hl : Nat.log 2 ⌈eNorm p.2⌉₊ ≤ Nat.log 2 ⌈T⌉₊ := Nat.log_mono_right hc
      omega
    have hs1 : 1 / eNorm p.1 ^ (d - 1) ≤ (4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p :=
      inv_pow_le_shell d (eNorm p.1) hge1 hI1
    have hs2 : 1 / eNorm p.2 ^ (d - 1) ≤ (4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p :=
      inv_pow_le_shell d (eNorm p.2) hge2 hI2
    have hCp := hC p.1 p.2 hprim1 hprim2 hne1 hne2
    have hpos : (0 : ℝ) < C * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
        eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1)) := by
      have h4 : (0 : ℝ) < C := hCpos
      have h1 : (0 : ℝ) < dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) :=
        lt_of_lt_of_le one_pos hd1
      have h2 : (0 : ℝ) < eNorm p.1 ^ (d - 1) := pow_pos (lt_of_lt_of_le one_pos hge1) _
      have h3 : (0 : ℝ) < eNorm p.2 ^ (d - 1) := pow_pos (lt_of_lt_of_le one_pos hge2) _
      positivity
    have hsum1 : 0 ≤ ∑ i ∈ Finset.range (I + 1), Phi i p :=
      Finset.sum_nonneg fun i _ => by dsimp only [Phi]; split <;> positivity
    have hsum2 : 0 ≤ ∑ j ∈ Finset.range (I + 1), Psi j p :=
      Finset.sum_nonneg fun j _ => by dsimp only [Psi]; split <;> positivity
    calc G p = 1 / detL (Gam d n p.1 p.2) := rfl
      _ ≤ 1 / (C * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
            eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) := one_div_le_one_div_of_le hpos hCp
      _ = (1 / C) * AA p * (eNorm p.1 ^ (d - 1))⁻¹ * (eNorm p.2 ^ (d - 1))⁻¹ := by
          rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
          ring
      _ ≤ (1 / C) * AA p * ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) *
            ((4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p) := by
          have h0 : 0 ≤ (1 / C) * AA p := by
            have hA0 : 0 ≤ AA p := by
              simp only [AA]
              exact div_nonneg zero_le_one (le_of_lt (lt_of_lt_of_le one_pos hd1))
            exact mul_nonneg (by positivity) hA0
          have hX1' : 0 ≤ (4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p := by positivity
          have hfirst : (1 / C) * AA p * (eNorm p.1 ^ (d - 1))⁻¹ ≤
              (1 / C) * AA p * ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) := by
            refine mul_le_mul_of_nonneg_left ?_ h0
            rw [← one_div]
            exact hs1
          refine mul_le_mul hfirst ?_ (by positivity) (mul_nonneg h0 hX1')
          rw [← one_div]
          exact hs2
  -- Step 2: expand the shells and swap the sums
  have hstep2 : ∑ p ∈ hsup.toFinset, (1 / C) * AA p *
        ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) *
        ((4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p)
      = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
        ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
          (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
            ∑ p ∈ (hsup.toFinset.filter
              (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j)), AA p := by
    calc ∑ p ∈ hsup.toFinset, (1 / C) * AA p *
          ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) *
          ((4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p)
        = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
            ∑ p ∈ hsup.toFinset, AA p * (∑ i ∈ Finset.range (I + 1), Phi i p) *
              (∑ j ∈ Finset.range (I + 1), Psi j p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [show 2 * (d - 1) = (d - 1) + (d - 1) by omega, pow_add]
          ring
      _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
            ∑ p ∈ hsup.toFinset, ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
              AA p * (Phi i p * Psi j p) := by
          congr 1
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mul_sum]
      _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
            ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
              ∑ p ∈ hsup.toFinset, AA p * (Phi i p * Psi j p) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_comm]
      _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
            ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
              (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
                ∑ p ∈ (hsup.toFinset.filter
                  (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j)), AA p := by
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [Phi, Psi]
          by_cases h1 : eNorm p.1 ≤ (2 : ℝ) ^ i <;> by_cases h2 : eNorm p.2 ≤ (2 : ℝ) ^ j <;>
            simp [h1, h2, mul_assoc, mul_comm]
  -- Step 3: apply the weighted pair count on each dyadic cell
  have hstep3 : ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
        (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
          ∑ p ∈ (hsup.toFinset.filter
            (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j)), AA p
      ≤ ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
          (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
            (K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2)) := by
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    have hcell := hK₃ ((2 : ℝ) ^ i) ((2 : ℝ) ^ j) ((2 : ℝ) ^ (i + j + 2))
      (hsup.toFinset.filter (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j))
      (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) ?_
    · have hcell' : ∑ p ∈ (hsup.toFinset.filter
          (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j)), AA p
          ≤ K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2) := hcell
      exact mul_le_mul_of_nonneg_left hcell' (by positivity)
    · intro p hp
      simp only [Finset.mem_filter] at hp
      obtain ⟨hpsf, h1, h2⟩ := hp
      obtain ⟨hX1, hX2, hne1, hne2⟩ := hmemO p hpsf
      have hli := linearIndependent_of_isPrim hX1.1 hX2.1 hne1 hne2
      have hdm := dmin_two_le_norm_mul hli
      have h12 : eNorm p.1 * eNorm p.2 ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j :=
        mul_le_mul h1 h2 (eNorm_nonneg p.2) (pow_nonneg (by norm_num) i)
      have h3 : (2 : ℝ) ^ i * (2 : ℝ) ^ j = (2 : ℝ) ^ (i + j) := (pow_add 2 i j).symm
      have h4 : (2 : ℝ) ^ (i + j) ≤ (2 : ℝ) ^ (i + j + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact ⟨hli, h1, h2, le_trans (le_trans hdm h12) (le_trans (le_of_eq h3) h4)⟩
  -- Step 4: evaluate the double sum
  have hpowe : ∀ i j : ℕ, ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2) =
      ((2 : ℝ) ^ i) ^ (n - 2) * ((2 : ℝ) ^ j) ^ (n - 2) * (2 : ℝ) ^ (2 * (n - 2)) := by
    intro i j
    have h1 : (2 : ℝ) ^ (i + j + 2) = (2 : ℝ) ^ i * (2 : ℝ) ^ j * 4 := by
      rw [pow_add, pow_add, pow_two]; norm_num
    have h4 : (4 : ℝ) ^ (n - 2) = (2 : ℝ) ^ (2 * (n - 2)) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_mul]
    rw [h1, mul_pow, mul_pow, h4]
  have hw : ∀ i : ℕ, (1 / (2 : ℝ) ^ i) ^ (d - 1) * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n - 2)
      = ((2 : ℝ) ^ (n + 1 - d)) ^ i := by
    intro i
    calc (1 / (2 : ℝ) ^ i) ^ (d - 1) * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n - 2)
        = ((2 : ℝ) ^ i) ^ n / ((2 : ℝ) ^ i) ^ (d - 1) := by
          rw [div_pow, one_pow, one_div, mul_assoc, ← pow_add,
            (show (2 : ℕ) + (n - 2) = n by omega), inv_mul_eq_div]
      _ = ((2 : ℝ) ^ i) ^ (n + 1 - d) := by
          rw [div_eq_iff (by positivity : ((2 : ℝ) ^ i) ^ (d - 1) ≠ 0), ← pow_add]
          congr 1
          omega
      _ = ((2 : ℝ) ^ (n + 1 - d)) ^ i := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hstep4 : ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
        (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
          (K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2))
      = K₃ * 2 ^ (2 * (n - 2)) *
        (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) ^ 2 := by
    have hterm : ∀ i j : ℕ,
        (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
          (K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2))
        = K₃ * 2 ^ (2 * (n - 2)) * ((((2 : ℝ) ^ (n + 1 - d)) ^ i) * (((2 : ℝ) ^ (n + 1 - d)) ^ j)) := by
      intro i j
      rw [hpowe i j, ← hw i, ← hw j]
      ring
    have hprod : (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) *
        (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ j)
        = ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
            ((((2 : ℝ) ^ (n + 1 - d)) ^ i) * (((2 : ℝ) ^ (n + 1 - d)) ^ j)) :=
      Finset.sum_mul_sum _ _ _ _
    calc ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
          (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
            (K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2))
        = ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
            K₃ * 2 ^ (2 * (n - 2)) *
              ((((2 : ℝ) ^ (n + 1 - d)) ^ i) * (((2 : ℝ) ^ (n + 1 - d)) ^ j)) := by
          refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i j
      _ = K₃ * 2 ^ (2 * (n - 2)) *
            ((∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) *
             (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ j)) := by
          rw [hprod, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mul_sum]
      _ = K₃ * 2 ^ (2 * (n - 2)) *
            (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) ^ 2 := by
          rw [pow_two]
  -- Step 5: the height bound
  have hTB : T ^ (n + 1 - d) = B := by
    have hB0' : (0 : ℝ) ≤ B := le_of_lt hB0
    have hee : (((n + 1 - d : ℕ)) : ℝ) = (n : ℝ) + 1 - d := by
      have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
      rw [Nat.cast_sub (by omega : d ≤ n + 1)]
      push_cast
      linarith
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hB0', hee]
    rw [show (1 : ℝ) / ((n : ℝ) + 1 - d) * ((n : ℝ) + 1 - d) = 1 by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hden)]]
    exact Real.rpow_one B
  have hstep5 : (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) ^ 2
      ≤ 4 * ((4 : ℝ) ^ (n + 1 - d) * B) ^ 2 := by
    have h1 : 1 ≤ n + 1 - d := by omega
    have hr : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1 - d) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (n + 1 - d) := pow_le_pow_right₀ (by norm_num) h1
    have hg := geom_two ((2 : ℝ) ^ (n + 1 - d)) hr I
    have hA : ((2 : ℝ) ^ (n + 1 - d)) ^ I ≤ (4 * T) ^ (n + 1 - d) := by
      rw [← pow_mul, Nat.mul_comm (n + 1 - d) I, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hIbound (n + 1 - d)
    have hB' : ((2 : ℝ) ^ (n + 1 - d)) ^ I ≤ (4 : ℝ) ^ (n + 1 - d) * B := by
      refine le_trans hA ?_
      rw [mul_pow, hTB]
    calc (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) ^ 2
        ≤ (2 * ((2 : ℝ) ^ (n + 1 - d)) ^ I) ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
      _ = 4 * (((2 : ℝ) ^ (n + 1 - d)) ^ I) ^ 2 := by ring
      _ ≤ 4 * ((4 : ℝ) ^ (n + 1 - d) * B) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact pow_le_pow_left₀ (by positivity) hB' 2
  calc ∑ p ∈ hsup.toFinset, G p
      ≤ ∑ p ∈ hsup.toFinset, (1 / C) * AA p *
          ((4 : ℝ) ^ (d - 1) * ∑ i ∈ Finset.range (I + 1), Phi i p) *
          ((4 : ℝ) ^ (d - 1) * ∑ j ∈ Finset.range (I + 1), Psi j p) := hstep1
    _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
          ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
            (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
              ∑ p ∈ (hsup.toFinset.filter
                (fun p => eNorm p.1 ≤ (2 : ℝ) ^ i ∧ eNorm p.2 ≤ (2 : ℝ) ^ j)), AA p := hstep2
    _ ≤ (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
          ∑ i ∈ Finset.range (I + 1), ∑ j ∈ Finset.range (I + 1),
            (1 / (2 : ℝ) ^ i) ^ (d - 1) * (1 / (2 : ℝ) ^ j) ^ (d - 1) *
              (K₃ * ((2 : ℝ) ^ i) ^ 2 * ((2 : ℝ) ^ j) ^ 2 *
                ((2 : ℝ) ^ (i + j + 2)) ^ (n - 2)) := by
          refine mul_le_mul_of_nonneg_left hstep3 ?_
          positivity
    _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
          (K₃ * 2 ^ (2 * (n - 2)) *
            (∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ (n + 1 - d)) ^ i) ^ 2) := by
          rw [hstep4]
    _ ≤ (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) *
          (K₃ * 2 ^ (2 * (n - 2)) * (4 * ((4 : ℝ) ^ (n + 1 - d) * B) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left hstep5 ?_
          positivity
    _ = (1 / C) * (4 : ℝ) ^ (2 * (d - 1)) * K₃ * 2 ^ (2 * (n - 2)) * 4 *
          4 ^ (2 * (n + 1 - d)) * B ^ 2 := by
          rw [mul_pow, ← pow_mul, show (n + 1 - d) * 2 = 2 * (n + 1 - d) by omega]
          ring

end Work.HP
