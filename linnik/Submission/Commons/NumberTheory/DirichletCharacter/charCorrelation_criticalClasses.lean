import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
import Submission.Commons.NumberTheory.ZMod.digit_decomposition_bijective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

namespace CharCorr

variable {p e : ℕ}

lemma pow_one_add_eq_of_sq_eq_zero {R : Type*} [CommRing R] {a : R} (ha : a ^ 2 = 0) (n : ℕ) :
    (1 + a) ^ n = 1 + (n : R) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have h : (n : R) * a * a = 0 := by rw [mul_assoc, ← pow_two, ha, mul_zero]
    calc (1 + (n:R)*a) * (1+a) = 1 + (n:R)*a + a + (n:R)*a*a := by ring
      _ = 1 + (n:R)*a + a := by rw [h, add_zero]
      _ = 1 + ((n+1 : ℕ) : R)*a := by push_cast; ring

lemma digit_sq_eq_zero (he : 2 ≤ e) :
    (((p ^ (e - 1) : ℕ) : ZMod (p ^ e))) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  rw [show ((p ^ (e - 1)) ^ 2 : ℕ) = p ^ (2 * (e - 1)) by rw [pow_mul]; ring_nf]
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.pow_dvd_pow p (by omega)

lemma digit_pow_one_add (k : ℕ) (he : 2 ≤ e) :
    (((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e))) ^ k
      = 1 + (k : ZMod (p^e)) * ((p ^ (e-1) : ℕ) : ZMod (p^e)) := by
  have := pow_one_add_eq_of_sq_eq_zero (digit_sq_eq_zero (p := p) he) k
  simpa only [Nat.cast_add, Nat.cast_one] using this

lemma isUnit_iff_not_dvd_val [Fact p.Prime] (he : 0 < e) (z : ZMod (p^e)) :
    IsUnit z ↔ ¬ p ∣ z.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]

/-- The reduction map `ZMod (p^e) → ZMod p`. -/
noncomputable def red (p e : ℕ) (h : p ∣ p^e) : ZMod (p^e) →+* ZMod p :=
  ZMod.castHom h (ZMod p)

lemma red_apply_val [NeZero (p^e)] (h : p ∣ p^e) (z : ZMod (p^e)) :
    red p e h z = ((z.val : ℕ) : ZMod p) := by
  rw [red, ZMod.castHom_apply, ZMod.cast_eq_val]

lemma dvd_of_red_eq_zero [NeZero (p^e)] (h : p ∣ p^e) {z : ZMod (p^e)}
    (hz : red p e h z = 0) : p ∣ z.val := by
  rw [red_apply_val] at hz
  exact (ZMod.natCast_eq_zero_iff z.val p).mp hz

lemma red_eq_zero_of_dvd [NeZero (p^e)] (h : p ∣ p^e) {z : ZMod (p^e)}
    (hz : p ∣ z.val) : red p e h z = 0 := by
  rw [red_apply_val, ZMod.natCast_eq_zero_iff]
  exact hz

lemma digit_mul_eq_zero_of_dvd [NeZero (p^e)] (he : 1 ≤ e) {X : ZMod (p^e)}
    (hX : p ∣ X.val) : ((p^(e-1) : ℕ) : ZMod (p^e)) * X = 0 := by
  obtain ⟨c, hc⟩ := hX
  conv_lhs => rw [← ZMod.natCast_zmod_val X]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨c, ?_⟩
  rw [hc]
  have h1 : e - 1 + 1 = e := by omega
  calc p ^ (e - 1) * (p * c) = (p ^ (e - 1) * p) * c := by ring
    _ = p ^ (e - 1 + 1) * c := by rw [pow_succ]
    _ = p ^ e * c := by rw [h1]

lemma digit_mul_eq_zero_of_red_eq_zero [NeZero (p^e)] (hd : p ∣ p^e) (he : 1 ≤ e)
    {X : ZMod (p^e)} (hX : red p e hd X = 0) :
    ((p^(e-1) : ℕ) : ZMod (p^e)) * X = 0 :=
  digit_mul_eq_zero_of_dvd (p := p) (e := e) he (dvd_of_red_eq_zero hd hX)

lemma red_digit_eq_zero [NeZero (p^e)] (hd : p ∣ p^e) (he : 2 ≤ e) :
    red p e hd (((p^(e-1) : ℕ)) : ZMod (p^e)) = 0 := by
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  simpa using Nat.pow_dvd_pow p (show 1 ≤ e - 1 by omega)

/-- `(y,t) ↦ y + p^(e-1)·t` in `ZMod (p^e)`. -/
def digitPt (p e : ℕ) (y : ZMod (p ^ (e - 1))) (t : ZMod p) : ZMod (p ^ e) :=
  ((y.val : ℕ) : ZMod (p ^ e)) + ((p ^ (e - 1) * t.val : ℕ) : ZMod (p ^ e))

/-- The lift `y ↦ y` of `ZMod (p^(e-1))` into `ZMod (p^e)`. -/
def digitLift (p e : ℕ) (y : ZMod (p ^ (e - 1))) : ZMod (p ^ e) := ((y.val : ℕ) : ZMod (p ^ e))

theorem twist_chi [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (z : ZMod (p ^ e)) (t : ZMod p) :
    χ (z + ((p ^ (e - 1) * t.val : ℕ) : ZMod (p ^ e)))
      = χ z * (χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e))) ^
          ((t * ((red p e (by simpa using Nat.pow_dvd_pow p (show 1 ≤ e by omega))) z)⁻¹)).val := by
  have hnz : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  haveI := hnz
  have hdiv : p ∣ p ^ e := by simpa using Nat.pow_dvd_pow p (show 1 ≤ e by omega)
  have he1 : 1 ≤ e := by omega
  set M : ZMod (p^e) := ((p ^ (e-1) : ℕ) : ZMod (p^e)) with hM
  have honep : ((1 + p ^ (e-1) : ℕ) : ZMod (p^e)) = 1 + M := by
    rw [Nat.cast_add, Nat.cast_one, hM]
  have hMt : ((p ^ (e - 1) * t.val : ℕ) : ZMod (p ^ e)) = M * (t.val : ZMod (p^e)) := by
    rw [Nat.cast_mul, hM]
  rw [hMt]
  by_cases hred : red p e hdiv z = 0
  · have hdvd : p ∣ z.val := dvd_of_red_eq_zero hdiv hred
    have hnu : ¬ IsUnit z := fun h => ((isUnit_iff_not_dvd_val (p := p) (e := e) (by omega) z).mp h) hdvd
    have hz0 : χ z = 0 := MulChar.map_nonunit χ hnu
    have hred' : red p e hdiv (z + M * (t.val : ZMod (p^e))) = 0 := by
      rw [map_add, map_mul, hred, red_digit_eq_zero hdiv he, zero_mul, add_zero]
    have hnu' : ¬ IsUnit (z + M * (t.val : ZMod (p^e))) :=
      fun h => ((isUnit_iff_not_dvd_val (p := p) (e := e) (by omega) _).mp h)
        (dvd_of_red_eq_zero hdiv hred')
    have hz0' : χ (z + M * (t.val : ZMod (p^e))) = 0 := MulChar.map_nonunit χ hnu'
    rw [hz0', hz0, hred, inv_zero, mul_zero, ZMod.val_zero, pow_zero, mul_one]
  · have hnotdvd : ¬ p ∣ z.val := fun hd => hred (red_eq_zero_of_dvd hdiv hd)
    have hunit : IsUnit z := (isUnit_iff_not_dvd_val (p := p) (e := e) (by omega) z).mpr hnotdvd
    have hz_inv : z * z⁻¹ = 1 := ZMod.mul_inv_of_unit z hunit
    have hred_inv : red p e hdiv z⁻¹ = (red p e hdiv z)⁻¹ := by
      have h1 : red p e hdiv z * red p e hdiv z⁻¹ = 1 := by
        rw [← map_mul, hz_inv, map_one]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    set k : ℕ := (t * (red p e hdiv z)⁻¹).val with hk
    have hred_arg : red p e hdiv ((t.val : ZMod (p^e)) * z⁻¹) = (red p e hdiv z)⁻¹ * t := by
      rw [map_mul, map_natCast, ZMod.natCast_zmod_val, hred_inv]
      ring
    have hred_k : ((k : ℕ) : ZMod p) = (red p e hdiv z)⁻¹ * t := by
      rw [hk, ZMod.natCast_zmod_val, mul_comm]
    have hkey : 1 + M * ((t.val : ZMod (p^e)) * z⁻¹) = (1 + M) ^ k := by
      have hpoweq : (1 + M) ^ k = 1 + (k : ZMod (p^e)) * M := by
        rw [← honep]; exact digit_pow_one_add (p := p) (e := e) k he
      have hzero : M * ((t.val : ZMod (p^e)) * z⁻¹ - ((k : ℕ) : ZMod (p^e))) = 0 := by
        apply digit_mul_eq_zero_of_red_eq_zero hdiv he1
        rw [map_sub, hred_arg]
        show (red p e hdiv z)⁻¹ * t - red p e hdiv (((k : ℕ) : ZMod (p^e))) = 0
        rw [map_natCast, hred_k]
        ring
      have hmul : M * ((t.val : ZMod (p^e)) * z⁻¹) = M * ((k : ℕ) : ZMod (p^e)) := by
        rw [mul_sub] at hzero
        exact sub_eq_zero.mp hzero
      rw [hpoweq, hmul]
      ring
    calc χ (z + M * (t.val : ZMod (p^e)))
        = χ (z * (1 + M * ((t.val : ZMod (p^e)) * z⁻¹))) := by
          congr 1
          rw [mul_add, mul_one, show z * (M * ((t.val : ZMod (p^e)) * z⁻¹)) = M * t.val by
            rw [show z * (M * ((t.val : ZMod (p^e)) * z⁻¹)) = (z*z⁻¹) * (M * t.val) by ring,
              hz_inv, one_mul]]
      _ = χ z * χ (1 + M * ((t.val : ZMod (p^e)) * z⁻¹)) := map_mul χ _ _
      _ = χ z * χ ((1 + M) ^ k) := by rw [hkey]
      _ = χ z * (χ (1 + M)) ^ k := by rw [map_pow]
      _ = χ z * (χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e))) ^ k := by rw [honep]

theorem twist_pt [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (y : ZMod (p ^ (e - 1))) (u : ℕ) (t : ZMod p) :
    χ (digitPt p e y t + (u : ZMod (p^e)))
      = χ (digitLift p e y + (u : ZMod (p^e))) *
        (χ ((1 + p ^ (e - 1) : ℕ) : ZMod (p ^ e))) ^
          ((t * (((y.val : ℕ) : ZMod p) + (u : ZMod p))⁻¹)).val := by
  have hnz : NeZero (p^e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  haveI := hnz
  have hdiv : p ∣ p ^ e := by simpa using Nat.pow_dvd_pow p (show 1 ≤ e by omega)
  have h := twist_chi (p := p) (e := e) he χ (((y.val : ℕ) : ZMod (p^e)) + (u : ZMod (p^e))) t
  have harg : (((y.val : ℕ) : ZMod (p^e)) + (u : ZMod (p^e))) + ((p ^ (e - 1) * t.val : ℕ) : ZMod (p^e))
      = digitPt p e y t + (u : ZMod (p^e)) := by
    simp only [digitPt]; ring
  have hz : (((y.val : ℕ) : ZMod (p^e)) + (u : ZMod (p^e))) = ((y.val + u : ℕ) : ZMod (p^e)) := by
    push_cast; ring
  have hred : red p e hdiv (((y.val : ℕ) : ZMod (p^e)) + (u : ZMod (p^e)))
      = ((y.val : ℕ) : ZMod p) + (u : ZMod p) := by
    rw [hz, map_natCast, Nat.cast_add]
  rw [harg, hred] at h
  simpa only [digitLift] using h

lemma geom_sum_zmodChar [Fact p.Prime] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) (D : ZMod p) :
    ∑ t : ZMod p, ζ ^ ((t * D).val) = if D = 0 then (p : ℂ) else 0 := by
  have hnz : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := hnz
  have h1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p h1
  have hψ : AddChar.IsPrimitive ψ := AddChar.zmodChar_primitive_of_primitive_root p hζ
  have key := AddChar.sum_mulShift D hψ
  rw [ZMod.card] at key
  trans ∑ x : ZMod p, ψ (x * D)
  · exact Finset.sum_congr rfl (fun t _ => by rw [AddChar.zmodChar_apply])
  · rw [key]; split_ifs <;> simp

theorem coset_sum [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b c d : ℕ)
    (y : ZMod (p ^ (e - 1))) :
    (∑ t : ZMod p,
        χ ((digitPt p e y t + (a : ZMod (p^e))) * (digitPt p e y t + (b : ZMod (p^e)))) *
        star (χ ((digitPt p e y t + (c : ZMod (p^e))) * (digitPt p e y t + (d : ZMod (p^e))))))
      = (p : ℂ) * (if (((y.val : ℕ) : ZMod p) + (a : ZMod p))⁻¹ + (((y.val : ℕ) : ZMod p) + (b : ZMod p))⁻¹
                      - (((y.val : ℕ) : ZMod p) + (c : ZMod p))⁻¹ - (((y.val : ℕ) : ZMod p) + (d : ZMod p))⁻¹ = 0
                   then χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e)))) *
                        star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e)))))
                   else 0) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hnz : NeZero (p ^ e) := ⟨pow_ne_zero e hp_pos.ne'⟩
  haveI := hnz
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  set ζ : ℂ := χ ((1 + p ^ (e-1) : ℕ) : ZMod (p^e)) with hζdef
  have hζ : IsPrimitiveRoot ζ p := chi_one_add_primePow_isPrimitiveRoot p e hp2 he χ hχ
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζp
  have hψapply : ∀ s : ZMod p, ψ s = ζ ^ (s.val) := fun s => AddChar.zmodChar_apply hζp s
  have hringChar : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact hp_pos
  set w : ℕ → ZMod p := fun u => (((y.val : ℕ) : ZMod p) + (u : ZMod p))⁻¹ with hw
  set D : ZMod p := w a + w b - w c - w d with hD
  have htw : ∀ (u : ℕ) (t : ZMod p), χ (digitPt p e y t + (u : ZMod (p^e)))
      = χ (digitLift p e y + (u : ZMod (p^e))) * ψ (t * w u) := by
    intro u t
    rw [twist_pt (p := p) (e := e) he χ y u t, hψapply, ← hζdef]
  have htw' : ∀ (u : ℕ) (t : ZMod p), star (χ (digitPt p e y t + (u : ZMod (p^e))))
      = star (χ (digitLift p e y + (u : ZMod (p^e)))) * ψ (t * (-(w u))) := by
    intro u t
    rw [htw u t, star_mul']
    rw [show star (ψ (t * w u)) = ψ (-(t * w u)) from by
      rw [Complex.star_def]
      rw [show (starRingEnd ℂ) (ψ (t * w u)) = ψ⁻¹ (t * w u) from
        AddChar.starComp_apply (φ := ψ) hringChar (t * w u)]
      rw [AddChar.inv_apply]]
    congr 1
    ring_nf
  have hsplit : ∀ x y : ZMod (p^e), star (χ (x * y)) = star (χ x) * star (χ y) := by
    intro x y
    rw [MulChar.star_apply' χ (x * y), map_mul (χ⁻¹), ← MulChar.star_apply' χ x,
      ← MulChar.star_apply' χ y]
  have hψcomb : ∀ t : ZMod p,
      ψ (t * w a) * ψ (t * w b) * ψ (t * (-(w c))) * ψ (t * (-(w d))) = ψ (t * D) := by
    intro t
    have h1 : ψ (t * w a + t * w b + (t * (-(w c))) + (t * (-(w d)))) = ψ (t * D) := by
      congr 1
      rw [hD]; ring
    rw [← h1]
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  have hsummand : ∀ t : ZMod p,
      χ ((digitPt p e y t + (a : ZMod (p^e))) * (digitPt p e y t + (b : ZMod (p^e))))
        * star (χ ((digitPt p e y t + (c : ZMod (p^e))) * (digitPt p e y t + (d : ZMod (p^e)))))
      = (χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
          * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e))))))
        * ψ (t * D) := by
    intro t
    have hQ : χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
          * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e)))))
        = χ (digitLift p e y + (a : ZMod (p^e))) * χ (digitLift p e y + (b : ZMod (p^e)))
          * (star (χ (digitLift p e y + (c : ZMod (p^e))))
              * star (χ (digitLift p e y + (d : ZMod (p^e))))) := by
      rw [map_mul χ, hsplit]
    calc χ ((digitPt p e y t + (a : ZMod (p^e))) * (digitPt p e y t + (b : ZMod (p^e))))
        * star (χ ((digitPt p e y t + (c : ZMod (p^e))) * (digitPt p e y t + (d : ZMod (p^e)))))
        = χ (digitPt p e y t + (a : ZMod (p^e))) * χ (digitPt p e y t + (b : ZMod (p^e)))
          * (star (χ (digitPt p e y t + (c : ZMod (p^e))))
              * star (χ (digitPt p e y t + (d : ZMod (p^e))))) := by
          rw [map_mul χ, hsplit]
      _ = (χ (digitLift p e y + (a : ZMod (p^e))) * ψ (t * w a))
            * (χ (digitLift p e y + (b : ZMod (p^e))) * ψ (t * w b))
            * ((star (χ (digitLift p e y + (c : ZMod (p^e)))) * ψ (t * (-(w c))))
                * (star (χ (digitLift p e y + (d : ZMod (p^e)))) * ψ (t * (-(w d))))) := by
          rw [htw a t, htw b t, htw' c t, htw' d t]
      _ = (χ (digitLift p e y + (a : ZMod (p^e))) * χ (digitLift p e y + (b : ZMod (p^e)))
            * (star (χ (digitLift p e y + (c : ZMod (p^e))))
                * star (χ (digitLift p e y + (d : ZMod (p^e))))))
            * (ψ (t * w a) * ψ (t * w b) * ψ (t * (-(w c))) * ψ (t * (-(w d)))) := by
          ring
      _ = (χ (digitLift p e y + (a : ZMod (p^e))) * χ (digitLift p e y + (b : ZMod (p^e)))
            * (star (χ (digitLift p e y + (c : ZMod (p^e))))
                * star (χ (digitLift p e y + (d : ZMod (p^e))))))
            * ψ (t * D) := by
          rw [hψcomb t]
      _ = (χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
          * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e))))))
        * ψ (t * D) := by
          rw [hQ]
  calc (∑ t : ZMod p,
        χ ((digitPt p e y t + (a : ZMod (p^e))) * (digitPt p e y t + (b : ZMod (p^e)))) *
        star (χ ((digitPt p e y t + (c : ZMod (p^e))) * (digitPt p e y t + (d : ZMod (p^e))))))
      = ∑ t : ZMod p,
          (χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
            * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e))))))
          * ψ (t * D) := Finset.sum_congr rfl (fun t _ => hsummand t)
    _ = (χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
            * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e))))))
          * ∑ t : ZMod p, ψ (t * D) := by rw [Finset.mul_sum]
    _ = (χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
            * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e))))))
          * (if D = 0 then ((p : ℕ) : ℂ) else 0) := by
        rw [show (∑ t : ZMod p, ψ (t * D)) = ∑ t : ZMod p, ζ ^ ((t*D).val) from
          Finset.sum_congr rfl (fun t _ => hψapply (t*D))]
        rw [geom_sum_zmodChar hζ D]
    _ = (p : ℂ) * (if D = 0
          then χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e))))
            * star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e)))))
          else 0) := by
        split_ifs <;> ring
    _ = (p : ℂ) * (if (((y.val : ℕ) : ZMod p) + (a : ZMod p))⁻¹ + (((y.val : ℕ) : ZMod p) + (b : ZMod p))⁻¹
                      - (((y.val : ℕ) : ZMod p) + (c : ZMod p))⁻¹ - (((y.val : ℕ) : ZMod p) + (d : ZMod p))⁻¹ = 0
                   then χ ((digitLift p e y + (a : ZMod (p^e))) * (digitLift p e y + (b : ZMod (p^e)))) *
                        star (χ ((digitLift p e y + (c : ZMod (p^e))) * (digitLift p e y + (d : ZMod (p^e)))))
                   else 0) := by
        congr 1

lemma natCast_decomp_low (p k n : ℕ) :
    ((n : ℕ) : ZMod (p ^ (k + 1))) =
      ((n % p : ℕ) : ZMod (p ^ (k + 1))) +
        ((p : ℕ) : ZMod (p ^ (k + 1))) * ((n / p % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by
  have h1 : p * (n / p) + n % p = n := by rw [Nat.mul_comm p (n / p), Nat.div_add_mod']
  have h2 : p ^ k * (n / p / p ^ k) + n / p % p ^ k = n / p := Nat.div_add_mod (n / p) (p ^ k)
  have hpp : ((p : ℕ) : ZMod (p ^ (k + 1))) * ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) = 0 := by
    rw [← Nat.cast_mul, ← pow_succ', ZMod.natCast_self]
  calc ((n : ℕ) : ZMod (p ^ (k + 1)))
      = ((p * (n / p) + n % p : ℕ) : ZMod (p ^ (k + 1))) := by rw [h1]
    _ = ((p : ℕ) : ZMod (p ^ (k + 1))) * ((n / p : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p : ℕ) : ZMod (p ^ (k + 1))) := by push_cast; ring
    _ = ((p : ℕ) : ZMod (p ^ (k + 1)))
          * ((p ^ k * (n / p / p ^ k) + n / p % p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p : ℕ) : ZMod (p ^ (k + 1))) := by conv_lhs => rw [← h2]
    _ = ((p : ℕ) : ZMod (p ^ (k + 1))) * ((p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          * ((n / p / p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          + ((p : ℕ) : ZMod (p ^ (k + 1))) * ((n / p % p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p : ℕ) : ZMod (p ^ (k + 1))) := by push_cast; ring
    _ = ((n % p : ℕ) : ZMod (p ^ (k + 1)))
          + ((p : ℕ) : ZMod (p ^ (k + 1))) * ((n / p % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by
        rw [hpp]; ring

lemma lowDigit_decomposition_bijective (p k : ℕ) (hp : 0 < p) :
    Function.Bijective (fun rz : ZMod p × ZMod (p ^ k) =>
      ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (k + 1)))) := by
  have hpne : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  haveI : NeZero p := ⟨hpne⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hpne⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hpne⟩
  have hpk_pos : 0 < p ^ k := pow_pos hp k
  let f : ZMod p × ZMod (p ^ k) → ZMod (p ^ (k + 1)) := fun rz =>
    ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (k + 1)))
  let g : ZMod (p ^ (k + 1)) → ZMod p × ZMod (p ^ k) := fun a =>
    (((a.val % p : ℕ) : ZMod p), ((a.val / p % p ^ k : ℕ) : ZMod (p ^ k)))
  have hr : Function.RightInverse g f := by
    intro a
    have h1 : ((g a).1.val : ℕ) = a.val % p := by
      simp only [g, ZMod.val_natCast, Nat.mod_mod]
    have h2 : ((g a).2.val : ℕ) = a.val / p % p ^ k := by
      simp only [g, ZMod.val_natCast, Nat.mod_mod]
    show f (g a) = a
    rw [show f (g a) = ((a.val % p : ℕ) : ZMod (p ^ (k + 1))) +
        ((p : ℕ) : ZMod (p ^ (k + 1))) * ((a.val / p % p ^ k : ℕ) : ZMod (p ^ (k + 1))) from by
          simp only [f]; rw [h1, h2]; push_cast; ring]
    rw [← natCast_decomp_low p k a.val, ZMod.natCast_zmod_val]
  have hl : Function.LeftInverse g f := by
    intro rz
    obtain ⟨r, z⟩ := rz
    have hrv : r.val < p := ZMod.val_lt r
    have hzv : z.val < p ^ k := ZMod.val_lt z
    have hb : r.val + p * z.val < p ^ (k + 1) := by
      calc r.val + p * z.val < p + p * z.val := Nat.add_lt_add_right hrv _
        _ = p * (z.val + 1) := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hzv)
        _ = p ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    have hA : f (r, z) = ((r.val + p * z.val : ℕ) : ZMod (p ^ (k + 1))) := rfl
    have hAval : (f (r, z)).val = r.val + p * z.val := by
      rw [hA, ZMod.val_natCast, Nat.mod_eq_of_lt hb]
    have h1 : (f (r, z)).val % p = r.val := by
      rw [hAval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrv]
    have h2 : (f (r, z)).val / p % p ^ k = z.val := by
      rw [hAval, Nat.add_mul_div_left r.val z.val hp, Nat.div_eq_of_lt hrv, Nat.zero_add,
        Nat.mod_eq_of_lt hzv]
    have hg1 : (g (f (r, z))).1 = r := by
      show (((f (r, z)).val % p : ℕ) : ZMod p) = r
      rw [h1, ZMod.natCast_zmod_val]
    have hg2 : (g (f (r, z))).2 = z := by
      show (((f (r, z)).val / p % p ^ k : ℕ) : ZMod (p ^ k)) = z
      rw [h2, ZMod.natCast_zmod_val]
    exact Prod.ext hg1 hg2
  exact Function.bijective_iff_has_inverse.mpr ⟨g, hl, hr⟩

end CharCorr

open CharCorr

/-- **Coset (kernel) reduction of the prime-power character correlation.**

Let `p` be an odd prime, `e ≥ 2` and `χ` a primitive Dirichlet character modulo `p ^ e`.
Then the correlation `∑_x χ ((x+a)(x+b)) * conj (χ ((x+c)(x+d)))` over `x : ZMod (p^e)`
equals `p` times the sum over the *critical* residue classes `r : ZMod p` (those with
`∑ ± (r+u)⁻¹ = 0` in the field `ZMod p`) of the corresponding sum over the `p^(e-2)` lifts
`x = r + p*z`.

Proof idea: the bijection `ZMod (p^(e-1)) × ZMod p → ZMod (p^e)`, `(y,t) ↦ y + p^(e-1)*t`,
together with `χ (w + p^(e-1)*t) = χ w * ζ^t` for `ζ = χ (1 + p^(e-1))` a primitive `p`-th
root of unity, turns the sum over `t` into a geometric sum which vanishes unless the
"derivative" `∑ ± (y+u)⁻¹` is `0`; then `y` is decomposed as `r + p*z`. -/
theorem charCorrelation_criticalClasses (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b c d : ℕ) :
    (∑ x : ZMod (p^e), χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d))))
      = (p : ℂ) * ∑ r : ZMod p,
          (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                - (r + (d : ZMod p))⁻¹ = 0
           then ∑ z : ZMod (p ^ (e - 2)),
                  χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ)) *
                     (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ)))
                  * (starRingEnd ℂ) (χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ)) *
                     (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ))))
           else 0) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  haveI : NeZero (p^e) := ⟨pow_ne_zero e hp_pos.ne'⟩
  haveI : NeZero (p^(e-1)) := ⟨pow_ne_zero (e-1) hp_pos.ne'⟩
  haveI : NeZero (p^(e-2)) := ⟨pow_ne_zero (e-2) hp_pos.ne'⟩
  set F : ZMod (p^e) → ℂ := fun x => χ ((x + (a : ZMod (p^e))) * (x + (b : ZMod (p^e))))
      * star (χ ((x + (c : ZMod (p^e))) * (x + (d : ZMod (p^e))))) with hF
  set critY : ZMod (p^(e-1)) → Prop := fun y =>
      (((y.val : ℕ) : ZMod p) + (a : ZMod p))⁻¹ + (((y.val : ℕ) : ZMod p) + (b : ZMod p))⁻¹
        - (((y.val : ℕ) : ZMod p) + (c : ZMod p))⁻¹ - (((y.val : ℕ) : ZMod p) + (d : ZMod p))⁻¹ = 0
      with hcritY
  -- decomposition 1: ZMod (p^(e-1)) × ZMod p ≃ ZMod (p^e)
  have hB1 := Commons.NumberTheory.ZMod.digit_decomposition_bijective p (e - 1) hp_pos
  rw [show e - 1 + 1 = e by omega] at hB1
  let E1 : ZMod (p ^ (e - 1)) × ZMod p ≃ ZMod (p ^ e) :=
    Equiv.ofBijective (fun yt : ZMod (p ^ (e - 1)) × ZMod p =>
      ((yt.1.val : ℕ) : ZMod (p ^ e)) +
        ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * ((yt.2.val : ℕ) : ZMod (p ^ e))) hB1
  have hE1 : ∀ yt : ZMod (p^(e-1)) × ZMod p, E1 yt = digitPt p e yt.1 yt.2 := by
    intro yt
    show ((yt.1.val : ℕ) : ZMod (p ^ e)) +
        ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * ((yt.2.val : ℕ) : ZMod (p ^ e))
        = ((yt.1.val : ℕ) : ZMod (p ^ e)) + ((p ^ (e - 1) * yt.2.val : ℕ) : ZMod (p ^ e))
    rw [Nat.cast_mul]
  -- decomposition 2: ZMod p × ZMod (p^(e-2)) ≃ ZMod (p^(e-1))
  have hB2 := lowDigit_decomposition_bijective p (e - 2) hp_pos
  rw [show e - 2 + 1 = e - 1 by omega] at hB2
  let E2 : ZMod p × ZMod (p ^ (e - 2)) ≃ ZMod (p ^ (e - 1)) :=
    Equiv.ofBijective (fun rz : ZMod p × ZMod (p ^ (e - 2)) =>
      ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (e - 1)))) hB2
  have hE2apply : ∀ rz : ZMod p × ZMod (p ^ (e - 2)),
      E2 rz = ((rz.1.val + p * rz.2.val : ℕ) : ZMod (p ^ (e - 1))) := fun rz => rfl
  have hE2bound : ∀ rz : ZMod p × ZMod (p^(e-2)), rz.1.val + p * rz.2.val < p^(e-1) := by
    intro rz
    have h1 : rz.1.val < p := ZMod.val_lt rz.1
    have h2 : rz.2.val < p^(e-2) := ZMod.val_lt rz.2
    calc rz.1.val + p * rz.2.val < p + p * rz.2.val := Nat.add_lt_add_right h1 _
      _ = p * (rz.2.val + 1) := by ring
      _ ≤ p * p^(e-2) := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr h2)
      _ = p^(e-1) := by rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
  have hE2val : ∀ rz : ZMod p × ZMod (p ^ (e - 2)), (E2 rz).val = rz.1.val + p * rz.2.val := by
    intro rz
    rw [hE2apply, ZMod.val_natCast, Nat.mod_eq_of_lt (hE2bound rz)]
  have hE2red : ∀ rz : ZMod p × ZMod (p ^ (e - 2)), (((E2 rz).val : ℕ) : ZMod p) = rz.1 := by
    intro rz
    rw [hE2val, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hE2lift : ∀ rz : ZMod p × ZMod (p ^ (e - 2)),
      digitLift p e (E2 rz) =
        ((rz.1.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((rz.2.val : ℕ) : ZMod (p^e)) := by
    intro rz
    simp only [digitLift]
    rw [hE2val]
    push_cast
    ring
  have hcritYZ : ∀ rz : ZMod p × ZMod (p^(e-2)),
      (critY (E2 rz) ↔ (rz.1 + (a : ZMod p))⁻¹ + (rz.1 + (b : ZMod p))⁻¹
              - (rz.1 + (c : ZMod p))⁻¹ - (rz.1 + (d : ZMod p))⁻¹ = 0) := by
    intro rz
    show ((((E2 rz).val : ℕ) : ZMod p) + (a : ZMod p))⁻¹ + ((((E2 rz).val : ℕ) : ZMod p) + (b : ZMod p))⁻¹
        - ((((E2 rz).val : ℕ) : ZMod p) + (c : ZMod p))⁻¹ - ((((E2 rz).val : ℕ) : ZMod p) + (d : ZMod p))⁻¹ = 0
      ↔ (rz.1 + (a : ZMod p))⁻¹ + (rz.1 + (b : ZMod p))⁻¹
              - (rz.1 + (c : ZMod p))⁻¹ - (rz.1 + (d : ZMod p))⁻¹ = 0
    rw [hE2red rz]
  -- step 2: per-coset evaluation
  have hstep2 : ∀ y : ZMod (p^(e-1)), (∑ t : ZMod p, F (E1 (y, t))) =
      (p : ℂ) * (if critY y then F (digitLift p e y) else 0) := by
    intro y
    have h1 : (∑ t : ZMod p, F (E1 (y, t))) = ∑ t : ZMod p, F (digitPt p e y t) :=
      Finset.sum_congr rfl (fun t _ => by rw [hE1])
    rw [h1]
    have h2 := coset_sum (p := p) (e := e) hp2 he χ hχ a b c d y
    simp only [hF, hcritY, digitLift, digitPt]
    exact h2
  have key : (∑ x : ZMod (p^e), F x) = (p : ℂ) * ∑ r : ZMod p,
          (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                - (r + (d : ZMod p))⁻¹ = 0
           then ∑ z : ZMod (p ^ (e - 2)),
                  χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ)) *
                     (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ)))
                  * (starRingEnd ℂ) (χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ)) *
                     (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ))))
           else 0) := by
    calc (∑ x : ZMod (p^e), F x)
        = ∑ yt : ZMod (p^(e-1)) × ZMod p, F (E1 yt) :=
          (Fintype.sum_equiv E1 (fun yt => F (E1 yt)) F (fun yt => rfl)).symm
      _ = ∑ y : ZMod (p^(e-1)), ∑ t : ZMod p, F (E1 (y, t)) := Fintype.sum_prod_type _
      _ = ∑ y : ZMod (p^(e-1)), (p : ℂ) * (if critY y then F (digitLift p e y) else 0) :=
          Finset.sum_congr rfl (fun y _ => hstep2 y)
      _ = (p : ℂ) * ∑ y : ZMod (p^(e-1)), (if critY y then F (digitLift p e y) else 0) := by
          rw [Finset.mul_sum]
      _ = (p : ℂ) * ∑ rz : ZMod p × ZMod (p^(e-2)),
            (if critY (E2 rz) then F (digitLift p e (E2 rz)) else 0) := by
          congr 1
          exact (Fintype.sum_equiv E2
            (fun rz : ZMod p × ZMod (p^(e-2)) =>
              if critY (E2 rz) then F (digitLift p e (E2 rz)) else 0)
            (fun y => if critY y then F (digitLift p e y) else 0)
            (fun rz => rfl)).symm
      _ = (p : ℂ) * ∑ rz : ZMod p × ZMod (p^(e-2)),
            (if (rz.1 + (a : ZMod p))⁻¹ + (rz.1 + (b : ZMod p))⁻¹ - (rz.1 + (c : ZMod p))⁻¹
                  - (rz.1 + (d : ZMod p))⁻¹ = 0
             then F (digitLift p e (E2 rz)) else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun rz _ => ?_)
          by_cases h : (rz.1 + (a : ZMod p))⁻¹ + (rz.1 + (b : ZMod p))⁻¹ - (rz.1 + (c : ZMod p))⁻¹
                  - (rz.1 + (d : ZMod p))⁻¹ = 0
          · rw [if_pos ((hcritYZ rz).mpr h), if_pos h]
          · rw [if_neg (fun hh => h ((hcritYZ rz).mp hh)), if_neg h]
      _ = (p : ℂ) * ∑ r : ZMod p, ∑ z : ZMod (p^(e-2)),
            (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                  - (r + (d : ZMod p))⁻¹ = 0
             then F (digitLift p e (E2 (r, z))) else 0) := by
          rw [Fintype.sum_prod_type]
      _ = (p : ℂ) * ∑ r : ZMod p,
            (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                  - (r + (d : ZMod p))⁻¹ = 0
             then ∑ z : ZMod (p^(e-2)), F (digitLift p e (E2 (r, z))) else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          by_cases h : (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                  - (r + (d : ZMod p))⁻¹ = 0 <;> simp [h]
      _ = (p : ℂ) * ∑ r : ZMod p,
            (if (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                  - (r + (d : ZMod p))⁻¹ = 0
             then ∑ z : ZMod (p ^ (e - 2)),
                    χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ)) *
                       (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ)))
                    * (starRingEnd ℂ) (χ ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ)) *
                       (((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ))))
             else 0) := by
          congr 1
          refine Finset.sum_congr rfl (fun r _ => ?_)
          by_cases h : (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
                  - (r + (d : ZMod p))⁻¹ = 0
          · rw [if_pos h, if_pos h]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            rw [hE2lift]
            simp only [hF]
            rfl
          · rw [if_neg h, if_neg h]
  rw [show (∑ x : ZMod (p^e), χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d))))
      = ∑ x : ZMod (p^e), F x from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [hF]
    rfl]
  exact key

end Commons.NumberTheory.DirichletCharacter
