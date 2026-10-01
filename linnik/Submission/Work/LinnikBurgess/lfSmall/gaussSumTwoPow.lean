/-
The `2`-adic quadratic Gauss sum used in the "two-digit peel" for the cubic character
correlation modulo a power of two.

`G = ∑_{w : ZMod (2^K)} θ ^ ((α * w - 2^(m-1) * γ * w ^ 2).val)` for a primitive
`2^K`-th root of unity `θ`.  Writing `D = 2^m * γ` and `g = m + vcap 2 (K-m) γ.val` (so that
`g = vcap 2 K D.val`), the classical computation gives `G * conj G = 2^K * S` with
`S = ∑_{h : D h = 0} θ ^ ((α h - 2^(m-1) γ h²).val)`.  Then `‖S‖ ≤ 2^g`, and `S = 0` unless
`2^(g-1) ∣ α.val`; hence `‖G‖ ≤ 2^((K+g)/2) · [2^(g-1) ∣ α.val]`, the form consumed by the peel.
-/
import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq

namespace Work.LinnikBurgess.lfSmall

open scoped BigOperators
open Classical

/-! ### Elementary `theta`-power lemmas -/

/-- `θ ^ ((x + y).val) = θ ^ x.val * θ ^ y.val` for `θ ^ N = 1`. -/
lemma theta_pow_val_add {N : ℕ} [NeZero N] {θ : ℂ} (hN : θ ^ N = 1) (x y : ZMod N) :
    θ ^ ((x + y).val) = θ ^ x.val * θ ^ y.val := by
  rw [ZMod.val_add, pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hN, pow_add]

/-- Conjugation of `θ ^ x.val`, for a primitive `N`-th root of unity. -/
lemma conj_theta_pow_val {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (x : ZMod N) :
    (starRingEnd ℂ) (θ ^ x.val) = θ ^ (-x).val := by
  have hN : θ ^ N = 1 := hθ.pow_eq_one
  have hnorm : ‖θ‖ = 1 := hθ.norm'_eq_one (NeZero.ne N)
  have hnorm' : ‖θ ^ x.val‖ = 1 := by rw [norm_pow, hnorm, one_pow]
  have hmul : θ ^ x.val * θ ^ (-x).val = 1 := by
    rw [← theta_pow_val_add hN x (-x), add_neg_cancel, ZMod.val_zero, pow_zero]
  rw [← Complex.inv_eq_conj hnorm']
  exact (eq_inv_of_mul_eq_one_right hmul).symm

/-- Complete additive character sum over `ZMod N`. -/
lemma sum_theta_val_mul {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (D : ZMod N) :
    (∑ w : ZMod N, θ ^ ((D * w).val)) = if D = 0 then (N : ℂ) else 0 :=
  Work.LinnikAreas.LocalCorr.sum_zmod_val_pow_eq N hθ D

/-- The inner sum after peeling off the constant term. -/
lemma sum_theta_val_add_mul {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N)
    (c E : ZMod N) :
    (∑ w : ZMod N, θ ^ ((c + E * w).val)) = θ ^ c.val * (if E = 0 then (N : ℂ) else 0) := by
  have hterm : ∀ w : ZMod N, θ ^ ((c + E * w).val) = θ ^ c.val * θ ^ ((E * w).val) :=
    fun w => theta_pow_val_add hθ.pow_eq_one c (E * w)
  rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, sum_theta_val_mul hθ E]

/-- The shear `(a, b) ↦ (a + b, b)` of `ZMod N × ZMod N`. -/
def addSndEquiv (N : ℕ) : (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) where
  toFun := fun p => (p.1 + p.2, p.2)
  invFun := fun p => (p.1 - p.2, p.2)
  left_inv := fun p => by simp [sub_add_cancel]
  right_inv := fun p => by simp

/-- Reindexing a double sum over `ZMod N × ZMod N` by the shear. -/
lemma sum_prod_shift {N : ℕ} [NeZero N] (F : ZMod N × ZMod N → ℂ) :
    (∑ p : ZMod N × ZMod N, F p) = ∑ p : ZMod N × ZMod N, F (p.1 + p.2, p.2) :=
  (Equiv.sum_comp (addSndEquiv N) F).symm

/-! ### `2`-adic valuations -/

lemma vcap_eq_of_zero (K : ℕ) : vcap 2 K 0 = K := by simp [vcap]

lemma vcap_eq_of_ne_zero {K x : ℕ} (hx : x ≠ 0) :
    vcap 2 K x = min (padicValNat 2 x) K := by simp [vcap, hx]

lemma vcap_le (K x : ℕ) : vcap 2 K x ≤ K := by
  rw [vcap]; split
  · exact le_rfl
  · exact Nat.min_le_right _ _

lemma vcap_eq_right_of_dvd {K x : ℕ} (h : 2 ^ K ∣ x) : vcap 2 K x = K := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hx, vcap_eq_of_zero]
  · rw [vcap_eq_of_ne_zero hx, Nat.min_eq_right]
    exact (padicValNat_dvd_iff_le hx).mp h

lemma dvd_of_vcap_eq_right {K x : ℕ} (h : vcap 2 K x = K) : 2 ^ K ∣ x := by
  rw [vcap] at h
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  · rw [if_neg hx] at h
    exact (padicValNat_dvd_iff_le hx).mpr (h ▸ Nat.min_le_left (padicValNat 2 x) K)

/-- `padicValNat` of a reduction modulo a power of two. -/
lemma padicValNat_two_mod {M t : ℕ} (ht : t % 2 ^ M ≠ 0) :
    padicValNat 2 (t % 2 ^ M) = padicValNat 2 t := by
  have ht0 : t ≠ 0 := fun h => ht (by rw [h, Nat.zero_mod])
  have hdiv : ∀ n ≤ M, (2 ^ n ∣ t % 2 ^ M ↔ 2 ^ n ∣ t) := by
    intro n hn
    have hndvd : 2 ^ n ∣ 2 ^ M := pow_dvd_pow 2 hn
    have hsub : t - t / 2 ^ M * 2 ^ M = t % 2 ^ M := by
      refine Nat.sub_eq_of_eq_add ?_
      have h := (Nat.div_add_mod t (2 ^ M)).symm
      rw [mul_comm (2 ^ M) (t / 2 ^ M), add_comm] at h
      exact h
    constructor
    · intro h
      have hd := Nat.div_add_mod t (2 ^ M)
      rw [← hd]
      exact Nat.dvd_add (dvd_mul_of_dvd_left hndvd (t / 2 ^ M)) h
    · intro h
      have h2 : 2 ^ n ∣ t - t / 2 ^ M * 2 ^ M :=
        Nat.dvd_sub h (dvd_mul_of_dvd_right hndvd (t / 2 ^ M))
      rwa [hsub] at h2
  have hM1 : 1 ≤ M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0, pow_zero, Nat.mod_one] at ht
    exact ht rfl
  have hlt : padicValNat 2 t < M := by
    by_contra hcon
    push_neg at hcon
    exact ht (Nat.mod_eq_zero_of_dvd ((padicValNat_dvd_iff_le ht0).mpr hcon))
  refine le_antisymm ?_ ?_
  · by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ (padicValNat 2 t + 1) ∣ t % 2 ^ M :=
      (padicValNat_dvd_iff_le ht).mpr (by omega)
    have h2 : 2 ^ (padicValNat 2 t + 1) ∣ t := (hdiv (padicValNat 2 t + 1) (by omega)).mp h1
    exact pow_succ_padicValNat_not_dvd ht0 h2
  · have h1 : 2 ^ padicValNat 2 t ∣ t := (padicValNat_dvd_iff_le ht0).mpr le_rfl
    have h2 : 2 ^ padicValNat 2 t ∣ t % 2 ^ M := (hdiv _ hlt.le).mpr h1
    exact (padicValNat_dvd_iff_le ht).mp h2

/-- `padicValNat 2 (2 * x) = 1 + padicValNat 2 x`.  In particular `(2 * δ).val = 2 * δ.val % 2^K`. -/
lemma two_mul_val {K : ℕ} (δ : ZMod (2 ^ K)) : (2 * δ).val = 2 * δ.val % 2 ^ K := by
  have h : (2 : ZMod (2 ^ K)) * δ = ((2 * δ.val : ℕ) : ZMod (2 ^ K)) := by
    conv_lhs => rw [show δ = ((δ.val : ℕ) : ZMod (2 ^ K)) from (ZMod.natCast_zmod_val δ).symm]
    rw [show (2 : ZMod (2 ^ K)) = ((2 : ℕ) : ZMod (2 ^ K)) from rfl, ← Nat.cast_mul]
  rw [h, ZMod.val_natCast]

/-- **The key valuation identity.**  `vcap 2 K (2^m γ).val = m + vcap 2 (K-m) γ.val`. -/
lemma vcap_mul_twoPow {K m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K) (γ : ZMod (2 ^ K)) :
    vcap 2 K (((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ).val = m + vcap 2 (K - m) γ.val := by
  haveI : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num)⟩
  have hpow : 2 ^ m * 2 ^ (K - m) = 2 ^ K := by
    rw [← pow_add]; congr 1; omega
  have hval : (((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ).val = 2 ^ m * (γ.val % 2 ^ (K - m)) := by
    rw [ZMod.val_mul, ZMod.val_natCast]
    rcases eq_or_lt_of_le hmK with h | h
    · subst h
      rw [Nat.mod_self, zero_mul, Nat.zero_mod, Nat.sub_self, pow_zero, Nat.mod_one, mul_zero]
    · have hmod : 2 ^ m % 2 ^ K = 2 ^ m :=
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)
      rw [hmod]
      have h1 : 2 ^ m * γ.val % (2 ^ m * 2 ^ (K - m)) = 2 ^ m * (γ.val % 2 ^ (K - m)) :=
        Nat.mul_mod_mul_left (2 ^ m) γ.val (2 ^ (K - m))
      rwa [hpow] at h1
  rw [hval]
  rcases eq_or_ne (γ.val % 2 ^ (K - m)) 0 with hr | hr
  · rw [hr, mul_zero, vcap_eq_of_zero]
    have hd : 2 ^ (K - m) ∣ γ.val := Nat.dvd_of_mod_eq_zero hr
    rw [vcap_eq_right_of_dvd hd]
    omega
  · have h2r : 2 ^ m * (γ.val % 2 ^ (K - m)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero m (by norm_num : (2 : ℕ) ≠ 0)) hr
    have hgne : γ.val ≠ 0 := fun h0 => hr (by rw [h0, Nat.zero_mod])
    rw [vcap_eq_of_ne_zero h2r, vcap_eq_of_ne_zero hgne]
    have hv : padicValNat 2 (γ.val % 2 ^ (K - m)) = padicValNat 2 γ.val :=
      padicValNat_two_mod hr
    have hlt : padicValNat 2 γ.val < K - m := by
      rw [← hv]
      by_contra hc
      rw [Nat.not_lt] at hc
      exact hr (Nat.eq_zero_of_dvd_of_lt
        ((padicValNat_dvd_iff_le hr).mpr hc) (Nat.mod_lt _ (pow_pos (by norm_num) _)))
    rw [padicValNat.mul (pow_ne_zero m (by norm_num : (2 : ℕ) ≠ 0)) hr,
      padicValNat.prime_pow, hv]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

/-- `2 ^ vcap 2 K d` divides `d` (for `d` reduced mod `2^K`). -/
lemma pow_vcap_dvd {K d : ℕ} (hd : d < 2 ^ K) : 2 ^ vcap 2 K d ∣ d := by
  rw [vcap]
  by_cases h0 : d = 0
  · rw [if_pos h0, h0]; exact dvd_zero (2 ^ K)
  · rw [if_neg h0]
    have h1 : padicValNat 2 d < K := by
      by_contra hc
      rw [Nat.not_lt] at hc
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) ((padicValNat_dvd_iff_le h0).mpr hc))
        (by omega)
    rw [Nat.min_eq_left h1.le]
    exact (padicValNat_dvd_iff_le h0).mpr le_rfl

/-- If `vcap 2 K d < K` then it *is* the `2`-adic valuation. -/
lemma padicValNat_eq_vcap_of_lt {K d : ℕ} (h : vcap 2 K d < K) :
    padicValNat 2 d = vcap 2 K d := by
  rw [vcap] at h ⊢
  by_cases h0 : d = 0
  · rw [if_pos h0] at h; omega
  · rw [if_neg h0] at h ⊢
    have h1 : padicValNat 2 d < K := by
      by_contra hc
      rw [Nat.not_lt] at hc
      rw [Nat.min_eq_right hc] at h
      omega
    rw [Nat.min_eq_left h1.le]

/-- `a * (b % n) % n = a * b % n`. -/
lemma mul_mod_mod (a b n : ℕ) : a * (b % n) % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod]
  exact (Nat.mul_mod a b n).symm

/-- `2 ^ K = 2 * 2 ^ (K - 1)` for `K ≥ 1`. -/
lemma two_pow_eq_two_mul {K : ℕ} (hK : 1 ≤ K) : 2 ^ K = 2 * 2 ^ (K - 1) := by
  conv_rhs => rw [← pow_succ']
  congr 1
  omega

/-- From `2 ^ K ∣ 2 * d` deduce `2 ^ (K - 1) ∣ d` (for `K ≥ 1`). -/
lemma dvd_of_two_dvd {K d : ℕ} (hK : 1 ≤ K) (h : 2 ^ K ∣ 2 * d) : 2 ^ (K - 1) ∣ d := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have : 2 * d = 2 * (2 ^ (K - 1) * c) := by rw [hc, two_pow_eq_two_mul hK]; ring
  exact Nat.mul_left_cancel (by norm_num) this

/-! ### The Gauss sum -/

theorem gaussSumTwoPow {K m : ℕ} (hK : 1 ≤ K) (hm : 1 ≤ m) (hmK : m ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 ^ K)) (α γ : ZMod (2 ^ K)) :
    ‖∑ w : ZMod (2 ^ K), θ ^ ((α * w - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ * w ^ 2).val)‖
      ≤ (2 : ℝ) ^ (((K + (m + vcap 2 (K - m) γ.val) : ℕ) : ℝ) / 2)
        * (if 2 ^ (m + vcap 2 (K - m) γ.val - 1) ∣ α.val then 1 else 0) := by
  classical
  haveI hNe : NeZero (2 ^ K) := ⟨pow_ne_zero K (by norm_num)⟩
  have hθ1 : ‖θ‖ = 1 := hθ.norm'_eq_one (by positivity)
  set δ : ZMod (2 ^ K) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) * γ with hδ
  set D : ZMod (2 ^ K) := ((2 ^ m : ℕ) : ZMod (2 ^ K)) * γ with hD
  set g : ℕ := m + vcap 2 (K - m) γ.val with hg
  have h2m : (2 : ℕ) * 2 ^ (m - 1) = 2 ^ m := by rw [← pow_succ']; congr 1; omega
  have hthis : ((2 ^ m : ℕ) : ZMod (2 ^ K))
      = (2 : ZMod (2 ^ K)) * ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ K)) := by
    rw [show (2 : ZMod (2 ^ K)) = ((2 : ℕ) : ZMod (2 ^ K)) from rfl, ← Nat.cast_mul, h2m]
  have h2δ : (2 : ZMod (2 ^ K)) * δ = D := by
    rw [hδ, hD, hthis, mul_assoc]
  have hgvcap : g = vcap 2 K D.val := by rw [hg, hD, vcap_mul_twoPow hm hmK γ]
  have hgK : g ≤ K := by rw [hg]; have := vcap_le (K - m) γ.val; omega
  have hg1 : 1 ≤ g := by rw [hg]; have := vcap_le (K - m) γ.val; omega
  have hgdvd : 2 ^ g ∣ D.val := by rw [hgvcap]; exact pow_vcap_dvd (ZMod.val_lt D)
  have hgex : g < K → padicValNat 2 D.val = g := by
    intro hlt
    rw [hgvcap]
    exact padicValNat_eq_vcap_of_lt (hgvcap ▸ hlt)
  set G : ℂ := ∑ w : ZMod (2 ^ K), θ ^ ((α * w - δ * w ^ 2).val) with hG
  -- #### the computation of `G * conj G`
  have hmain : G * (starRingEnd ℂ) G
      = ((2 ^ K : ℕ) : ℂ) * ∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
          θ ^ ((α * h - δ * h ^ 2).val) := by
    have hconj : (starRingEnd ℂ) G
        = ∑ w : ZMod (2 ^ K), θ ^ ((-(α * w - δ * w ^ 2)).val) := by
      rw [hG, map_sum]
      exact Finset.sum_congr rfl (fun w _ => conj_theta_pow_val hθ (α * w - δ * w ^ 2))
    have h1 : G * (starRingEnd ℂ) G
        = ∑ w : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * w - δ * w ^ 2) - (α * w' - δ * w' ^ 2)).val) := by
      rw [hconj, hG, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
      rw [← theta_pow_val_add hθ.pow_eq_one (α * w - δ * w ^ 2) (-(α * w' - δ * w' ^ 2))]
      congr 1
      ring
    rw [h1]
    let F : ZMod (2 ^ K) × ZMod (2 ^ K) → ℂ := fun p =>
      θ ^ (((α * p.1 - δ * p.1 ^ 2) - (α * p.2 - δ * p.2 ^ 2)).val)
    have e1 : (∑ w : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
          θ ^ (((α * w - δ * w ^ 2) - (α * w' - δ * w' ^ 2)).val)) = ∑ p, F p := by
      rw [Fintype.sum_prod_type]
    have e2 : (∑ p : ZMod (2 ^ K) × ZMod (2 ^ K), F p)
        = ∑ p : ZMod (2 ^ K) × ZMod (2 ^ K), F (p.1 + p.2, p.2) := sum_prod_shift F
    have e3 : (∑ p : ZMod (2 ^ K) × ZMod (2 ^ K), F (p.1 + p.2, p.2))
        = ∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K), F (h + w', w') := by
      rw [Fintype.sum_prod_type]
    have e4 : (∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K), F (h + w', w'))
        = ∑ h : ZMod (2 ^ K), ∑ w' : ZMod (2 ^ K),
            θ ^ (((α * (h + w') - δ * (h + w') ^ 2) - (α * w' - δ * w' ^ 2)).val) := rfl
    rw [e1, e2, e3, e4]
    have h4 : ∀ h w' : ZMod (2 ^ K),
        (α * (h + w') - δ * (h + w') ^ 2) - (α * w' - δ * w' ^ 2)
          = (α * h - δ * h ^ 2) - D * h * w' := by
      intro h w'
      rw [← h2δ]
      ring
    simp_rw [h4]
    have h5 : ∀ h : ZMod (2 ^ K),
        (∑ w' : ZMod (2 ^ K), θ ^ (((α * h - δ * h ^ 2) - D * h * w').val))
          = θ ^ ((α * h - δ * h ^ 2).val) * (if D * h = 0 then ((2 ^ K : ℕ) : ℂ) else 0) := by
      intro h
      have key : (∑ w' : ZMod (2 ^ K), θ ^ (((α * h - δ * h ^ 2) - D * h * w').val))
          = ∑ w' : ZMod (2 ^ K), θ ^ (((α * h - δ * h ^ 2) + (-(D * h)) * w').val) := by
        refine Finset.sum_congr rfl (fun w' _ => ?_)
        congr 1
        ring
      rw [key, sum_theta_val_add_mul hθ (α * h - δ * h ^ 2) (-(D * h))]
      simp only [neg_eq_zero]
    simp_rw [h5]
    have h6 : ∀ h : ZMod (2 ^ K),
        θ ^ ((α * h - δ * h ^ 2).val) * (if D * h = 0 then ((2 ^ K : ℕ) : ℂ) else 0)
          = (if D * h = 0 then ((2 ^ K : ℕ) : ℂ) * θ ^ ((α * h - δ * h ^ 2).val) else 0) := by
      intro h
      by_cases hh : D * h = 0 <;> simp [hh, mul_comm]
    simp_rw [h6]
    rw [Finset.sum_filter]
    have h7 : ∀ h : ZMod (2 ^ K),
        (if D * h = 0 then ((2 ^ K : ℕ) : ℂ) * θ ^ ((α * h - δ * h ^ 2).val) else 0)
          = ((2 ^ K : ℕ) : ℂ) * (if D * h = 0 then θ ^ ((α * h - δ * h ^ 2).val) else 0) := by
      intro h
      by_cases hh : D * h = 0 <;> simp [hh]
    simp_rw [h7]
    rw [Finset.mul_sum]
  set S : ℂ := ∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
      θ ^ ((α * h - δ * h ^ 2).val) with hSdef
  have hmain' : G * (starRingEnd ℂ) G = ((2 ^ K : ℕ) : ℂ) * S := by
    rw [hSdef]; exact hmain
  have hsq : ‖G‖ ^ 2 = (2 : ℝ) ^ K * ‖S‖ := by
    have h1 : ‖G * (starRingEnd ℂ) G‖ = ‖G‖ * ‖G‖ := by
      rw [norm_mul, starRingEnd_apply, norm_star]
    have h2 : ‖G * (starRingEnd ℂ) G‖ = (2 : ℝ) ^ K * ‖S‖ := by
      rw [hmain', norm_mul, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_two, ← h1, h2]
  -- #### `S` vanishes off the critical congruence
  have hzero : ¬ (2 ^ (g - 1) ∣ α.val) → S = 0 := by
    intro hnd
    set h0 : ZMod (2 ^ K) := ((2 ^ (K - g) : ℕ) : ZMod (2 ^ K)) with hh0
    have hh0lt : 2 ^ (K - g) < 2 ^ K :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    -- `2^(g-1) ∣ δ.val`
    have hδdvd : 2 ^ (g - 1) ∣ δ.val := by
      have h1 : 2 ^ g ∣ (2 * δ).val := by rw [h2δ]; exact hgdvd
      have h2 : 2 ^ g ∣ 2 ^ K := pow_dvd_pow 2 hgK
      have hmod : (2 * δ).val = 2 * δ.val % 2 ^ K := two_mul_val δ
      have h3 : 2 ^ g ∣ 2 * δ.val := by
        rw [hmod] at h1
        have h4 : 2 ^ g ∣ 2 * δ.val % 2 ^ K + 2 ^ K * (2 * δ.val / 2 ^ K) :=
          Nat.dvd_add h1 (dvd_mul_of_dvd_left h2 (2 * δ.val / 2 ^ K))
        rwa [Nat.mod_add_div] at h4
      exact dvd_of_two_dvd hg1 h3
    -- `D * h0 = 0`
    have hDh0 : D * h0 = 0 := by
      obtain ⟨u, hu⟩ := hgdvd
      rw [← ZMod.val_eq_zero, ZMod.val_mul, hh0, ZMod.val_natCast,
        Nat.mod_eq_of_lt hh0lt, hu]
      have hsplit : 2 ^ g * u * 2 ^ (K - g) = u * 2 ^ K := by
        rw [show 2 ^ g * u * 2 ^ (K - g) = u * (2 ^ g * 2 ^ (K - g)) by ring,
          ← pow_add, Nat.add_sub_cancel' hgK]
      rw [hsplit]
      exact (Nat.dvd_iff_mod_eq_zero).mp (dvd_mul_of_dvd_right (dvd_refl _) u)
    -- the shift identity
    have hshift : ∀ h : ZMod (2 ^ K), D * h = 0 →
        θ ^ ((α * (h + h0) - δ * (h + h0) ^ 2).val)
          = θ ^ ((α * h - δ * h ^ 2).val) * θ ^ ((α * h0 - δ * h0 ^ 2).val) := by
      intro h hh
      have hz : D * h * h0 = 0 := by rw [hh, zero_mul]
      have hkey : (α * (h + h0) - δ * (h + h0) ^ 2)
          = (α * h - δ * h ^ 2) + (α * h0 - δ * h0 ^ 2) := by
        linear_combination (-(h * h0)) * h2δ - 1 * hz
      rw [hkey, theta_pow_val_add hθ.pow_eq_one]
    have htranslate : S = θ ^ ((α * h0 - δ * h0 ^ 2).val) * S := by
      have himg : (Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0)).image
            (fun h : ZMod (2 ^ K) => h + h0)
          = Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0) := by
        refine Finset.ext (fun h => ?_)
        rw [Finset.mem_image]
        constructor
        · rintro ⟨a, ha, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          rw [mul_add, ha, hDh0, add_zero]
        · intro hh
          refine ⟨h - h0, ?_, by rw [sub_add_cancel]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
          rw [mul_sub, hh, hDh0, sub_zero]
      have key : (∑ x ∈ (Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0)).image
              (fun h : ZMod (2 ^ K) => h + h0), θ ^ ((α * x - δ * x ^ 2).val))
          = ∑ x ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
              θ ^ ((α * (x + h0) - δ * (x + h0) ^ 2).val) :=
        Finset.sum_image (fun x _ y _ hxy => add_right_cancel hxy)
      rw [himg] at key
      have h2 : S = ∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
              θ ^ ((α * h - δ * h ^ 2).val) * θ ^ ((α * h0 - δ * h0 ^ 2).val) := by
        rw [hSdef, key]
        refine Finset.sum_congr rfl (fun h hh => ?_)
        exact hshift h (Finset.mem_filter.mp hh).2
      have h3 : (∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
              θ ^ ((α * h - δ * h ^ 2).val) * θ ^ ((α * h0 - δ * h0 ^ 2).val))
          = θ ^ ((α * h0 - δ * h0 ^ 2).val) * S := by
        rw [← Finset.sum_mul, hSdef]
        ring
      exact h2.trans h3
    have hκ0 : α * h0 - δ * h0 ^ 2 = 0 → 2 ^ (g - 1) ∣ α.val := by
      intro hk
      by_cases hgK' : g = K
      · have hh1 : h0 = 1 := by rw [hh0, hgK', Nat.sub_self, pow_zero, Nat.cast_one]
        rw [hh1, mul_one, one_pow, mul_one] at hk
        have hαδ : α = δ := sub_eq_zero.mp hk
        rw [hgK'] at hδdvd
        rw [hgK', hαδ]
        exact hδdvd
      · have hlt : g < K := lt_of_le_of_ne hgK hgK'
        have hδh0 : δ * h0 ^ 2 = 0 := by
          obtain ⟨w, hw⟩ := hδdvd
          rw [← ZMod.val_eq_zero]
          have h1 : (δ * h0 ^ 2).val = δ.val * (h0.val * h0.val) % 2 ^ K := by
            rw [pow_two, ZMod.val_mul]
            rw [show (h0 * h0).val = h0.val * h0.val % 2 ^ K from ZMod.val_mul h0 h0,
              mul_mod_mod]
          rw [h1, hh0, ZMod.val_natCast, Nat.mod_eq_of_lt hh0lt, hw]
          refine (Nat.dvd_iff_mod_eq_zero).mp ?_
          have hrw : 2 ^ (g - 1) * w * (2 ^ (K - g) * 2 ^ (K - g))
              = w * 2 ^ ((g - 1) + ((K - g) + (K - g))) := by
            rw [show 2 ^ (g - 1) * w * (2 ^ (K - g) * 2 ^ (K - g))
                = w * (2 ^ (g - 1) * (2 ^ (K - g) * 2 ^ (K - g))) by ring,
              ← pow_add, ← pow_add]
          rw [hrw]
          exact dvd_mul_of_dvd_right
            (pow_dvd_pow 2 (by omega : K ≤ (g - 1) + ((K - g) + (K - g)))) w
        have hαh0 : α * h0 = 0 := by
          have hsub : α * h0 - δ * h0 ^ 2 = α * h0 := by rw [hδh0, sub_zero]
          rwa [hsub] at hk
        have hv : 2 ^ K ∣ α.val * 2 ^ (K - g) := by
          have hval : (α * h0).val = 0 := by rw [hαh0, ZMod.val_zero]
          rw [ZMod.val_mul, hh0, ZMod.val_natCast, Nat.mod_eq_of_lt hh0lt] at hval
          exact (Nat.dvd_iff_mod_eq_zero).mpr hval
        have hv' : 2 ^ (K - g) * 2 ^ g ∣ 2 ^ (K - g) * α.val := by
          rw [show 2 ^ (K - g) * 2 ^ g = 2 ^ K by rw [← pow_add, Nat.sub_add_cancel hgK],
            mul_comm (2 ^ (K - g)) α.val]
          exact hv
        have hgdiv : 2 ^ g ∣ α.val :=
          (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ (K - g))).mp hv'
        exact dvd_trans (pow_dvd_pow 2 (Nat.sub_le g 1)) hgdiv
    have hκne : θ ^ ((α * h0 - δ * h0 ^ 2).val) ≠ 1 := by
      have hκ' : α * h0 - δ * h0 ^ 2 ≠ 0 := fun hk => hnd (hκ0 hk)
      have hvalne : (α * h0 - δ * h0 ^ 2).val ≠ 0 :=
        fun h => hκ' ((ZMod.val_eq_zero _).mp h)
      exact hθ.pow_ne_one_of_pos_of_lt hvalne (ZMod.val_lt _)
    have h3 : (θ ^ ((α * h0 - δ * h0 ^ 2).val) - 1) * S = 0 := by
      rw [sub_mul, one_mul, ← htranslate, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hκne
    · exact h
  -- #### the size bound for `S`
  have hcard : ‖S‖ ≤ (2 : ℝ) ^ g := by
    have hnorm1 : ∀ h : ZMod (2 ^ K), ‖θ ^ ((α * h - δ * h ^ 2).val)‖ = 1 := by
      intro h; rw [norm_pow, hθ1, one_pow]
    rw [hSdef]
    refine (norm_sum_le _ _).trans ?_
    have hsum : (∑ h ∈ Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0),
          ‖θ ^ ((α * h - δ * h ^ 2).val)‖)
        = ((Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0)).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun h _ => hnorm1 h), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    have hker : (Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0)).card ≤ 2 ^ g := by
      by_cases hgK' : g = K
      · rw [hgK']
        calc (Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0)).card
            ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 ^ K := by rw [Finset.card_univ, ZMod.card]
      · have hlt : g < K := lt_of_le_of_ne hgK hgK'
        set u : ℕ := D.val / 2 ^ g with hu
        have hu_eq : D.val = 2 ^ g * u := by
          rw [hu, mul_comm]
          exact (Nat.div_mul_cancel hgdvd).symm
        have hDne : D.val ≠ 0 := by
          intro hz
          have h := hgex hlt
          rw [hz] at h
          simp [padicValNat] at h
          omega
        have hu0 : u ≠ 0 := fun h0 => hDne (by rw [hu_eq, h0, mul_zero])
        have huodd : ¬ 2 ∣ u := by
          intro h2
          have hdvd' : 2 ^ (g + 1) ∣ D.val := by
            rw [hu_eq, pow_succ]
            exact mul_dvd_mul_left (2 ^ g) h2
          have hcontra := pow_succ_padicValNat_not_dvd (p := 2) hDne
          rw [hgex hlt] at hcontra
          exact hcontra hdvd'
        have hcop : Nat.Coprime u (2 ^ (K - g)) :=
          Nat.Coprime.pow_right (K - g)
            (Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp
              (fun hE => huodd (even_iff_two_dvd.mp hE))))
        have hdvdk : ∀ h : ZMod (2 ^ K), D * h = 0 → 2 ^ (K - g) ∣ h.val := by
          intro h hh
          have hv0 : 2 ^ K ∣ D.val * h.val := by
            have hval : (D * h).val = 0 := by rw [hh, ZMod.val_zero]
            rw [ZMod.val_mul] at hval
            exact (Nat.dvd_iff_mod_eq_zero).mpr hval
          have hv : 2 ^ K ∣ 2 ^ g * (u * h.val) := by
            rwa [hu_eq, mul_assoc] at hv0
          have hv' : 2 ^ (K - g) ∣ u * h.val := by
            have hv2 : 2 ^ g * 2 ^ (K - g) ∣ 2 ^ g * (u * h.val) := by
              rw [← pow_add, Nat.add_sub_cancel' hgK]
              exact hv
            exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ g)).mp hv2
          exact @Nat.Coprime.dvd_of_dvd_mul_left (2 ^ (K - g)) u h.val hcop.symm hv'
        have hinj := Finset.card_le_card_of_injOn
          (s := Finset.univ.filter (fun h : ZMod (2 ^ K) => D * h = 0))
          (t := Finset.range (2 ^ g)) (fun h => h.val / 2 ^ (K - g))
          (fun (h : ZMod (2 ^ K)) hh => by
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh
            rw [Finset.mem_coe, Finset.mem_range]
            rw [Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) (K - g))]
            calc h.val < 2 ^ K := ZMod.val_lt h
              _ = 2 ^ g * 2 ^ (K - g) := by rw [← pow_add, Nat.add_sub_cancel' hgK])
          (fun (h : ZMod (2 ^ K)) hh (h' : ZMod (2 ^ K)) hh' heq => by
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh hh'
            have h1 := hdvdk h hh
            have h2 := hdvdk h' hh'
            have heq' : h.val / 2 ^ (K - g) = h'.val / 2 ^ (K - g) := heq
            have : h.val = h'.val := by
              rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, heq']
            exact ZMod.val_injective _ this)
        simpa using hinj
    exact_mod_cast hker
  -- #### conclusion
  by_cases hind : 2 ^ (g - 1) ∣ α.val
  · rw [if_pos hind, mul_one]
    have hKG : ‖G‖ ^ 2 ≤ (2 : ℝ) ^ (K + g) := by
      rw [hsq]
      calc (2 ^ K : ℝ) * ‖S‖ ≤ (2 ^ K : ℝ) * (2 ^ g : ℝ) :=
            mul_le_mul_of_nonneg_left hcard (by positivity)
        _ = (2 : ℝ) ^ (K + g) := by rw [← pow_add]
    have h2split : ((K + g : ℕ) : ℝ) = ((K + g : ℕ) : ℝ) / 2 + ((K + g : ℕ) : ℝ) / 2 := by ring
    have hRHS : ((2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (K + g) := by
      rw [pow_two]
      conv_rhs => rw [← Real.rpow_natCast (2 : ℝ) (K + g)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← h2split]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2) := by positivity
    have hsq2 : ‖G‖ ^ 2 ≤ ((2 : ℝ) ^ (((K + g : ℕ) : ℝ) / 2)) ^ 2 := by rw [hRHS]; exact hKG
    have hfin := Real.sqrt_le_sqrt hsq2
    rwa [Real.sqrt_sq (norm_nonneg G), Real.sqrt_sq h2] at hfin
  · rw [if_neg hind, mul_zero]
    have hS0 : S = 0 := hzero hind
    rw [hS0, norm_zero, mul_zero] at hsq
    have hG0 : ‖G‖ = 0 := by
      have := norm_nonneg G
      nlinarith [hsq]
    rw [hG0]

end Work.LinnikBurgess.lfSmall
