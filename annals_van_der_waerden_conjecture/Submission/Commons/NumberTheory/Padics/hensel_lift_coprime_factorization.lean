import Mathlib
import Submission.Commons.NumberTheory.Padics.hensel_lift_step

open Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Padics

/-! # Hensel lifting of a coprime monic factorization over the p-adic integers -/

-- =====================================================================
-- 1. A field-theoretic lemma: degree-bounded Bézout decomposition
-- =====================================================================

/-- Over a field, if `a b` are monic coprime polynomials and `e` has degree
bounded by `deg a + deg b`, then `e = u * b + v * a` for some `u v` whose
coefficients vanish above `deg a` and `deg b` respectively. -/
lemma exists_bezout_decomp {K : Type*} [Field K] {a b : K[X]}
    (ha : a.Monic) (hb : b.Monic) (hcop : IsCoprime a b) {e : K[X]}
    (he : e.degree < (a.natDegree + b.natDegree : WithBot ℕ)) :
    ∃ u v : K[X],
      (∀ i, a.natDegree ≤ i → u.coeff i = 0) ∧
      (∀ i, b.natDegree ≤ i → v.coeff i = 0) ∧ e = u * b + v * a := by
  classical
  by_cases he0 : e = 0
  · subst e; refine ⟨0, 0, ?_, ?_, ?_⟩ <;> simp
  · have he' : e.natDegree < a.natDegree + b.natDegree := by
      have hdeg : e.degree = (e.natDegree : WithBot ℕ) := degree_eq_natDegree he0
      rw [hdeg] at he
      exact WithBot.coe_lt_coe.mp he
    obtain ⟨s, t, hst⟩ := hcop  -- hst : s * a + t * b = 1
    let q : K[X] := (s * e) /ₘ b
    let v : K[X] := (s * e) %ₘ b
    let u : K[X] := a * q + t * e
    have hv : v = s * e - q * b := by
      dsimp [v, q]
      rw [modByMonic_eq_sub_mul_div]
      ring
    have hmain : e = u * b + v * a := by
      calc
        e = (a * q + t * e) * b + (s * e - q * b) * a := by
          calc
            e = e * (s * a + t * b) := by rw [hst]; ring
            _ = (a * q + t * e) * b + (s * e - q * b) * a := by ring
        _ = u * b + v * a := by
          dsimp [u]
          rw [hv]
    have hv_lt : v.natDegree < b.natDegree ∨ v = 0 := by
      by_cases hv0 : v = 0
      · exact Or.inr hv0
      · have hb1 : b ≠ 1 := by
          intro hb1
          apply hv0
          subst b
          simp [v]
        exact Or.inl (natDegree_modByMonic_lt (s * e) hb hb1)
    have hu_lt : u.natDegree < a.natDegree ∨ u = 0 := by
      by_cases hu0 : u = 0
      · exact Or.inr hu0
      · have h_eq : u * b = e - v * a := by
          rw [hmain]
          ring
        have hdeg_e : e.natDegree < a.natDegree + b.natDegree := he'
        have hdeg_va : (v * a).natDegree < a.natDegree + b.natDegree := by
          by_cases hv0 : v = 0
          · simp [hv0]
            omega
          · have hvd : v.natDegree < b.natDegree := hv_lt.resolve_right hv0
            rw [natDegree_mul hv0 ha.ne_zero]
            omega
        have hdeg : (e - v * a).natDegree < a.natDegree + b.natDegree := by
          have h1 : (e - v * a).natDegree ≤ max e.natDegree (v * a).natDegree := by
            simpa [sub_eq_add_neg] using natDegree_add_le e (-(v * a))
          exact lt_of_le_of_lt h1 (max_lt hdeg_e hdeg_va)
        have hdeg_ub : (u * b).natDegree < a.natDegree + b.natDegree := by
          rw [h_eq]
          exact hdeg
        have hdeg_u : u.natDegree < a.natDegree := by
          rw [natDegree_mul hu0 hb.ne_zero] at hdeg_ub
          omega
        exact Or.inl hdeg_u
    refine ⟨u, v, ?_, ?_, hmain⟩
    · intro i hi
      rcases hu_lt with hu_lt | hu0
      · exact coeff_eq_zero_of_natDegree_lt (p := u) (by omega)
      · simp [hu0]
    · intro i hi
      rcases hv_lt with hv_lt | hv0
      · exact coeff_eq_zero_of_natDegree_lt (p := v) (by omega)
      · simp [hv0]

-- =====================================================================
-- 2. ℤ_[p] and ZMod basics
-- =====================================================================

section PadicBasics

variable {p : ℕ} [Fact p.Prime]

/-- kernel of a composition with an injective ring hom is the kernel of the second map -/
lemma ker_comp_injective {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (e : S →+* T) (he : Function.Injective e) (φ : R →+* S) :
    RingHom.ker (e.comp φ) = RingHom.ker φ := by
  ext x
  simp [RingHom.mem_ker]
  constructor
  · intro h
    apply he
    simpa using h
  · intro h
    simp [h]

/-- The reduction `ℤ_[p] →+* ZMod p` factors through level-1 `ℤ_[p] →+* ZMod (p^1)`. -/
lemma toZMod_eq_congr_comp_toZModPow_one :
    (ZMod.ringEquivCongr (pow_one p)).toRingHom.comp (PadicInt.toZModPow (p := p) 1) =
      (PadicInt.toZMod (p := p)) := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [ker_comp_injective (ZMod.ringEquivCongr (pow_one p)).toRingHom
    (RingEquiv.injective (ZMod.ringEquivCongr (pow_one p))) (PadicInt.toZModPow (p := p) 1)]
  rw [PadicInt.ker_toZModPow, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  congr 1
  norm_num

/-- `p ∣ p^(k+1)` -/
lemma p_dvd_pow (k : ℕ) : p ∣ p ^ (k+1) := by
  refine ⟨p ^ k, ?_⟩
  rw [pow_succ', mul_comm]

/-- reduction `ZMod (p^(k+1)) →+* ZMod p` -/
def redMod (k : ℕ) : ZMod (p ^ (k+1)) →+* ZMod p :=
  ZMod.castHom (p_dvd_pow k) (ZMod p)

/-- reduction `ZMod (p^(k+1)) →+* ZMod (p^k)` -/
def castDown (k : ℕ) : ZMod (p ^ (k+1)) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))

/-- `x` reduces to zero at level `k` iff `p^k ∣ x.val` -/
lemma cast_eq_zero_iff_dvd_val (k : ℕ) (x : ZMod (p ^ (k+1))) :
    (castDown k x = 0) ↔ p ^ k ∣ x.val := by
  constructor
  · intro h
    change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))) x = 0 at h
    rw [ZMod.castHom_apply] at h
    rw [ZMod.cast_eq_val] at h
    exact (ZMod.natCast_eq_zero_iff x.val (p ^ k)).mp h
  · intro hd
    have h : (x.cast : ZMod (p ^ k)) = 0 := by
      rw [ZMod.cast_eq_val]
      exact (ZMod.natCast_eq_zero_iff x.val (p ^ k)).mpr hd
    change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))) x = 0
    rw [ZMod.castHom_apply]
    exact h

/-- decomposition of an element divisible by `p^k` -/
lemma eq_pow_mul_div_val (k : ℕ) (x : ZMod (p ^ (k+1))) (hx : p ^ k ∣ x.val) :
    x = ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * ((x.val / p ^ k : ℕ) : ZMod (p ^ (k+1))) := by
  calc
    x = ((x.val : ℕ) : ZMod (p ^ (k+1))) := (ZMod.natCast_zmod_val x).symm
    _ = (((p ^ k) * (x.val / p ^ k) : ℕ) : ZMod (p ^ (k+1))) := by
      congr 1
      rw [Nat.mul_comm, Nat.div_mul_cancel hx]
    _ = ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * ((x.val / p ^ k : ℕ) : ZMod (p ^ (k+1))) := by
      rw [Nat.cast_mul]

/-- multiplying by `p^k` kills anything divisible by `p` (in `ZMod (p^(k+1))`) -/
lemma pow_mul_eq_zero_of_cast_eq_zero (k : ℕ) (x : ZMod (p ^ (k+1)))
    (hx : (ZMod.castHom (p_dvd_pow k) (ZMod p)) x = 0) :
    ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * x = 0 := by
  have hz : p ∣ x.val := by
    rw [ZMod.castHom_apply] at hx
    rw [ZMod.cast_eq_val] at hx
    exact (ZMod.natCast_eq_zero_iff x.val p).mp hx
  have hx' : x = (p : ZMod (p ^ (k+1))) * ((x.val / p : ℕ) : ZMod (p ^ (k+1))) := by
    calc
      x = ((x.val : ℕ) : ZMod (p ^ (k+1))) := (ZMod.natCast_zmod_val x).symm
      _ = ((p * (x.val / p) : ℕ) : ZMod (p ^ (k+1))) := by
        congr 1
        rw [Nat.mul_comm, Nat.div_mul_cancel hz]
      _ = (p : ZMod (p ^ (k+1))) * ((x.val / p : ℕ) : ZMod (p ^ (k+1))) := by
        rw [Nat.cast_mul]
  rw [hx', ← mul_assoc]
  have hpown : (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (p : ZMod (p ^ (k+1)))) = 0 := by
    calc
      (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (p : ZMod (p ^ (k+1))))
          = ((p ^ k * p : ℕ) : ZMod (p ^ (k+1))) := by rw [Nat.cast_mul]
      _ = ((p ^ (k+1) : ℕ) : ZMod (p ^ (k+1))) := by
        rw [pow_succ]
      _ = 0 := ZMod.natCast_self (p ^ (k+1))
  rw [hpown]
  simp

/-- reduction of the canonical lift of `m < p` -/
lemma red_natCast_eq (k : ℕ) {m : ℕ} (hm : m < p) :
    (redMod k) ((m : ℕ) : ZMod (p ^ (k+1))) = (m : ZMod p) := by
  rw [map_natCast]

/-- casting the canonical lift of `m` to level `k` gives zero when `p^k ∣ m` -/
lemma castDown_natCast_eq_zero (k : ℕ) {m : ℕ} (hm : p ^ k ∣ m) :
    (castDown k) ((m : ℕ) : ZMod (p ^ (k+1))) = 0 := by
  change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))) ((m : ℕ) : ZMod (p ^ (k+1))) = 0
  rw [map_natCast]
  rw [ZMod.natCast_eq_zero_iff]
  exact hm

/-- p^k is sent to zero when cast down to level k -/
lemma castDown_pow_eq_zero (k : ℕ) :
    (castDown k) (((p ^ k : ℕ) : ZMod (p ^ (k+1)))) = 0 := by
  apply castDown_natCast_eq_zero
  exact dvd_rfl

/-- the cast down of `(p^k) * ↑c.val` is zero -/
lemma castDown_pow_mul_val (k : ℕ) (c : ZMod p) :
    (castDown k) (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (c.val : ZMod (p ^ (k+1)))) = 0 := by
  rw [show (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (c.val : ZMod (p ^ (k+1))))
        = ((p ^ k * c.val : ℕ) : ZMod (p ^ (k+1))) by
      rw [Nat.cast_mul]]
  rw [map_natCast]
  rw [ZMod.natCast_eq_zero_iff]
  exact ⟨c.val, by rw [mul_comm]⟩

/-- reduction of the canonical lift of a `ZMod p` element is itself -/
lemma red_val_cast (k : ℕ) (c : ZMod p) :
    (redMod k) ((c.val : ℕ) : ZMod (p ^ (k+1))) = c := by
  rw [map_natCast]
  exact ZMod.natCast_zmod_val c

/-- the value of `castDown k` at `x` -/
lemma castDown_val (k : ℕ) (x : ZMod (p ^ (k+1))) : (castDown k x).val = x.val % p ^ k := by
  rw [castDown, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [ZMod.val_natCast]

/-- if `x` casts down to `y`, the values differ by a multiple of `p^k` -/
lemma dvd_val_sub_of_castDown_eq (k : ℕ) (x : ZMod (p ^ (k+1))) (y : ZMod (p ^ k))
    (h : castDown k x = y) : (p : ℤ) ^ k ∣ (x.val : ℤ) - (y.val : ℤ) := by
  have hh := congrArg ZMod.val h
  have hval : x.val % p ^ k = y.val := by
    rw [castDown_val] at hh
    exact hh
  have hm := Nat.div_add_mod x.val (p ^ k)
  have hx : x.val = (x.val / p ^ k) * p ^ k + y.val := by
    rw [hval] at hm
    rw [mul_comm] at hm
    exact hm.symm
  refine ⟨((x.val / p ^ k : ℕ) : ℤ), ?_⟩
  have hx' : (x.val : ℤ) = ((x.val / p ^ k : ℕ) : ℤ) * ((p ^ k : ℕ) : ℤ) + (y.val : ℤ) := by
    exact_mod_cast hx
  rw [hx']
  have hp : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by norm_num
  rw [hp]
  ring

end PadicBasics


-- =====================================================================
-- 3. The recursive family of factorizations at all levels ZMod (p^k)
-- =====================================================================

section Recursion

variable {p : ℕ} [Fact p.Prime]

/-- level-1 ring: `ZMod (p ^ 1) ≃+* ZMod p` -/
def zmodOne (p : ℕ) : ZMod (p ^ 1) ≃+* ZMod p :=
  ZMod.ringEquivCongr (pow_one p)

/-- reduction `ZMod (p^k) →+* ZMod p` (requires `1 ≤ k`) -/
def redMap (k : ℕ) (hk : 1 ≤ k) : ZMod (p ^ k) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)

/-- canonical lift `ZMod p →+* ZMod (p ^ 1)` -/
def liftOne (p : ℕ) : ZMod p →+* ZMod (p ^ 1) :=
  (zmodOne p).symm.toRingHom

/-- reduction at level 1 agrees with the canonical identification with `ZMod p` -/
lemma redMap_one_eq :
    redMap (p := p) 1 (by omega : 1 ≤ 1) = (zmodOne p).toRingHom := by
  ext x
  apply ZMod.val_injective (p)
  change ((redMap (p := p) 1 (by omega : 1 ≤ 1)) x).val = ((zmodOne p) x).val
  rw [redMap, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [zmodOne]
  rw [ZMod.ringEquivCongr_val]
  exact Nat.mod_eq_of_lt (by simpa using (ZMod.val_lt x))

lemma redMap_comp_liftOne :
    (redMap (p := p) 1 (by omega : 1 ≤ 1)).comp (liftOne p) = RingHom.id (ZMod p) := by
  rw [redMap_one_eq]
  ext x
  exact (zmodOne p).right_inv x

/-- data of a monic factorization at level `k` (ring `ZMod (p ^ k)`) -/
structure LevelData (f : (PadicInt p)[X]) (a b : (ZMod p)[X]) (k : ℕ) where
  hk : 1 ≤ k
  α : (ZMod (p ^ k))[X]
  β : (ZMod (p ^ k))[X]
  monα : α.Monic
  monβ : β.Monic
  degα : α.natDegree = a.natDegree
  degβ : β.natDegree = b.natDegree
  fac : α * β = Polynomial.map (PadicInt.toZModPow k) f
  redα : Polynomial.map (redMap k hk) α = a
  redβ : Polynomial.map (redMap k hk) β = b

/-- output of one lifting step, together with the cast-down compatibility -/
structure SuccOut (f : (PadicInt p)[X]) (a b : (ZMod p)[X]) (m : ℕ)
    (D : LevelData f a b m) where
  D' : LevelData f a b (m + 1)
  compatA : Polynomial.map (castDown m) D'.α = D.α
  compatB : Polynomial.map (castDown m) D'.β = D.β

/-- one lifting step, packaged as `SuccOut` -/
noncomputable def levelSucc {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (m : ℕ) (D : LevelData f a b m) (hf : f.Monic) (ha : a.Monic)
    (hb : b.Monic) (hcop : IsCoprime a b) : SuccOut f a b m D := by
  classical
  let h := hensel_lift_step (m := m) D.hk hf ha hb hcop D.monα D.monβ D.degα D.degβ D.fac D.redα D.redβ
  let α' : (ZMod (p ^ (m+1)))[X] := Classical.choose h
  let hβ := Classical.choose_spec h
  let β' : (ZMod (p ^ (m+1)))[X] := Classical.choose hβ
  let P := Classical.choose_spec hβ
  -- P : α'.Monic ∧ β'.Monic ∧ ...
  let D' : LevelData f a b (m+1) := {
    hk := by omega, α := α', β := β',
    monα := P.1, monβ := P.2.1, degα := P.2.2.1, degβ := P.2.2.2.1,
    fac := P.2.2.2.2.1,
    redα := P.2.2.2.2.2.2.2.1, redβ := P.2.2.2.2.2.2.2.2 }
  exact {
    D' := D',
    compatA := P.2.2.2.2.2.1,
    compatB := P.2.2.2.2.2.2.1
  }

/-- level 1 is `toZModPow 1` followed by the canonical lift -/
lemma toZModPow_one_lift {x : ℤ_[p]} :
    (PadicInt.toZModPow (p := p) 1) x = liftOne p (PadicInt.toZMod (p := p) x) := by
  classical
  have hx : (zmodOne p) ((PadicInt.toZModPow (p := p) 1) x) = (PadicInt.toZMod (p := p) x) := by
    rw [zmodOne]
    simpa using (DFunLike.congr_fun (toZMod_eq_congr_comp_toZModPow_one (p := p)) x)
  have hs := congrArg (fun y : ZMod p => (zmodOne p).symm y) hx
  exact (((zmodOne p).symm_apply_apply ((PadicInt.toZModPow (p := p) 1) x)).symm).trans hs

/-- `toZModPow 1` is `toZMod` followed by the canonical lift -/
lemma liftOne_comp_toZMod :
    (liftOne p).comp (PadicInt.toZMod (p := p)) = (PadicInt.toZModPow (p := p) 1) := by
  ext x
  exact (toZModPow_one_lift (p := p)).symm

/-- data at level 1 obtained by transporting `a` and `b` -/
noncomputable def levelOne {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (hf : f.Monic) (ha : a.Monic) (hb : b.Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b) :
    LevelData f a b 1 := by
  classical
  refine ⟨by omega, Polynomial.map (liftOne p) a, Polynomial.map (liftOne p) b,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Polynomial.Monic.map (liftOne p) ha
  · exact Polynomial.Monic.map (liftOne p) hb
  · rw [Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective (zmodOne p).symm) a]
  · rw [Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective (zmodOne p).symm) b]
  · -- fac : α₁ * β₁ = map (toZModPow 1) f
    calc
      Polynomial.map (liftOne p) a * Polynomial.map (liftOne p) b
          = Polynomial.map (liftOne p) (a * b) := by rw [← Polynomial.map_mul]
      _ = Polynomial.map (liftOne p) (Polynomial.map (PadicInt.toZMod (p := p)) f) := by rw [hfac]
      _ = Polynomial.map ((liftOne p).comp (PadicInt.toZMod (p := p))) f := by rw [← Polynomial.map_map]
      _ = Polynomial.map (PadicInt.toZModPow (p := p) 1) f := by rw [liftOne_comp_toZMod]
  · -- redα
    calc
      Polynomial.map (redMap (p := p) 1 (by omega : 1 ≤ 1)) (Polynomial.map (liftOne p) a)
          = Polynomial.map ((redMap (p := p) 1 (by omega : 1 ≤ 1)).comp (liftOne p)) a := by
            rw [← Polynomial.map_map]
      _ = a := by
        rw [redMap_comp_liftOne]
        simp
  · -- redβ
    calc
      Polynomial.map (redMap (p := p) 1 (by omega : 1 ≤ 1)) (Polynomial.map (liftOne p) b)
          = Polynomial.map ((redMap (p := p) 1 (by omega : 1 ≤ 1)).comp (liftOne p)) b := by
            rw [← Polynomial.map_map]
      _ = b := by
        rw [redMap_comp_liftOne]
        simp

/-- the recursive family of factorizations at every level `n+1` -/
noncomputable def famAux {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (hf : f.Monic) (ha : a.Monic) (hb : b.Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b)
    (hcop : IsCoprime a b) : (n : ℕ) → LevelData f a b (n + 1)
  | 0 => levelOne hf ha hb hfac
  | n + 1 => (levelSucc (n + 1) (famAux hf ha hb hfac hcop n) hf ha hb hcop).D'

/-- compatibility of the family: level `n+2` casts down to level `n+1` -/
lemma famAux_cast {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (hf : f.Monic) (ha : a.Monic) (hb : b.Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b)
    (hcop : IsCoprime a b) (n : ℕ) :
    Polynomial.map (castDown (n+1)) ((famAux hf ha hb hfac hcop (n+1)).α) =
      (famAux hf ha hb hfac hcop n).α := by
  · -- level `n+2` from level `n+1`
    -- unfold the recursion
    simp [famAux]
    exact (levelSucc (n+1) (famAux hf ha hb hfac hcop n) hf ha hb hcop).compatA

/-- a coefficient of the family as a compatible integer sequence -/
noncomputable def levelCoeffSeq {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (F : (n : ℕ) → LevelData f a b (n+1)) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => ((F n).α.coeff i).val

/-- an element of `ℤ_[p]` with prescribed residues modulo each `p^k` -/
lemma exists_padic_of_seq (s : ℕ → ℕ)
    (hdiv : ∀ n, (p : ℤ) ^ n ∣ (s (n+1) : ℤ) - (s n : ℤ)) :
    ∃ x : ℤ_[p], ∀ n, (PadicInt.toZModPow n) x = (s n : ZMod (p ^ n)) := by
  use PadicInt.ofIntSeq (fun k => (s k : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (s k : ℤ)) p hdiv)
  intro n
  simpa using (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (s k : ℤ)) p hdiv n)


/-- compatibility of the family for the `β` component -/
lemma famAux_castβ {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (hf : f.Monic) (ha : a.Monic) (hb : b.Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b)
    (hcop : IsCoprime a b) (n : ℕ) :
    Polynomial.map (castDown (n+1)) ((famAux hf ha hb hfac hcop (n+1)).β) =
      (famAux hf ha hb hfac hcop n).β := by
  simp [famAux]
  exact (levelSucc (n+1) (famAux hf ha hb hfac hcop n) hf ha hb hcop).compatB

/-- a coefficient of the family (`β` component) as a compatible integer sequence -/
noncomputable def levelCoeffSeqβ {f : (PadicInt p)[X]} {a b : (ZMod p)[X]}
    (F : (n : ℕ) → LevelData f a b (n+1)) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => ((F n).β.coeff i).val

end Recursion


-- The main theorem (real proof to be completed).
-- The main theorem.
theorem hensel_lift_coprime_factorization {p : ℕ} [Fact p.Prime] {f : (PadicInt p)[X]}
    (hf : f.Monic) {a : (ZMod p)[X]} (ha : a.Monic) {b : (ZMod p)[X]} (hb : b.Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b)
    (hcop : IsCoprime a b) :
    ∃ A B : (PadicInt p)[X],
      A.Monic ∧ B.Monic ∧ A.natDegree = a.natDegree ∧ B.natDegree = b.natDegree ∧
        f = A * B ∧ A.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a ∧
        B.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = b := by
  classical
  let d₁ : ℕ := a.natDegree
  let d₂ : ℕ := b.natDegree
  let F : (n : ℕ) → LevelData f a b (n + 1) := famAux hf ha hb hfac hcop
  have Fcast : ∀ n, Polynomial.map (castDown (n+1)) (F (n+1)).α = (F n).α := by
    intro n
    exact famAux_cast hf ha hb hfac hcop n
  -- divisibility of the level-value sequences
  have hdivSeq : ∀ i n, (p : ℤ) ^ n ∣ ((levelCoeffSeq F i (n+1) : ℤ) - (levelCoeffSeq F i n : ℤ)) := by
    intro i n
    by_cases hn : n = 0
    · subst n
      simp [levelCoeffSeq]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hc := congrArg (fun P : (ZMod (p ^ (m + 1)))[X] => P.coeff i) (Fcast m)
      have hci : (castDown (m+1)) ((F (m+1)).α.coeff i) = ((F m).α.coeff i) := by
        simpa [Polynomial.coeff_map] using hc
      simpa [levelCoeffSeq] using
        (dvd_val_sub_of_castDown_eq (m+1) ((F (m+1)).α.coeff i) ((F m).α.coeff i) hci)
  -- assembled coefficients
  let coeffx (i : ℕ) : PadicInt p :=
    Classical.choose (exists_padic_of_seq (levelCoeffSeq F i) (hdivSeq i))
  have coeffx_spec (i n : ℕ) :
      (PadicInt.toZModPow n) (coeffx i) = ((levelCoeffSeq F i n : ℕ) : ZMod (p ^ n)) := by
    exact (Classical.choose_spec (exists_padic_of_seq (levelCoeffSeq F i) (hdivSeq i))) n
  -- the assembled polynomials
  have Fcastβ : ∀ n, Polynomial.map (castDown (n+1)) (F (n+1)).β = (F n).β := by
    intro n
    exact famAux_castβ hf ha hb hfac hcop n
  have hdivSeqβ : ∀ i n, (p : ℤ) ^ n ∣ ((levelCoeffSeqβ F i (n+1) : ℤ) - (levelCoeffSeqβ F i n : ℤ)) := by
    intro i n
    by_cases hn : n = 0
    · subst n
      simp [levelCoeffSeqβ]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hc := congrArg (fun P : (ZMod (p ^ (m + 1)))[X] => P.coeff i) (Fcastβ m)
      have hci : (castDown (m+1)) ((F (m+1)).β.coeff i) = ((F m).β.coeff i) := by
        simpa [Polynomial.coeff_map] using hc
      simpa [levelCoeffSeqβ] using
        (dvd_val_sub_of_castDown_eq (m+1) ((F (m+1)).β.coeff i) ((F m).β.coeff i) hci)
  let coeffy (i : ℕ) : PadicInt p :=
    Classical.choose (exists_padic_of_seq (levelCoeffSeqβ F i) (hdivSeqβ i))
  have coeffy_spec (i n : ℕ) :
      (PadicInt.toZModPow n) (coeffy i) = ((levelCoeffSeqβ F i n : ℕ) : ZMod (p ^ n)) := by
    exact (Classical.choose_spec (exists_padic_of_seq (levelCoeffSeqβ F i) (hdivSeqβ i))) n
  let A : (PadicInt p)[X] := ∑ i ∈ Finset.range (d₁ + 1), Polynomial.monomial i (coeffx i)
  let B : (PadicInt p)[X] := ∑ i ∈ Finset.range (d₂ + 1), Polynomial.monomial i (coeffy i)

  -- coefficient descriptions of A and B
  have A_coeff (j : ℕ) : A.coeff j = if j < d₁ + 1 then coeffx j else 0 := by
    by_cases hj : j < d₁ + 1
    · have hsum : (∑ i ∈ Finset.range (d₁ + 1), (Polynomial.monomial i (coeffx i)).coeff j)
          = coeffx j := by
        rw [Finset.sum_eq_single j]
        · simp [Polynomial.coeff_monomial]
        · intro b hb hbj
          simp [Polynomial.coeff_monomial, hbj]
        · intro hmem
          exact False.elim (hmem (Finset.mem_range.mpr hj))
      rw [show A.coeff j = (∑ i ∈ Finset.range (d₁ + 1), (Polynomial.monomial i (coeffx i)).coeff j) by
          simp [A]]
      rw [if_pos hj]
      exact hsum
    · have hzero : (∑ i ∈ Finset.range (d₁ + 1), (Polynomial.monomial i (coeffx i))).coeff j = 0 := by
        rw [finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i < d₁ + 1 := Finset.mem_range.mp hi
        have hij : i ≠ j := by omega
        simp [Polynomial.coeff_monomial, hij]
      rw [show A.coeff j = (∑ i ∈ Finset.range (d₁ + 1), (Polynomial.monomial i (coeffx i))).coeff j by
          simp [A]]
      rw [if_neg hj]
      exact hzero
  have B_coeff (j : ℕ) : B.coeff j = if j < d₂ + 1 then coeffy j else 0 := by
    by_cases hj : j < d₂ + 1
    · have hsum : (∑ i ∈ Finset.range (d₂ + 1), (Polynomial.monomial i (coeffy i)).coeff j)
          = coeffy j := by
        rw [Finset.sum_eq_single j]
        · simp [Polynomial.coeff_monomial]
        · intro b hb hbj
          simp [Polynomial.coeff_monomial, hbj]
        · intro hmem
          exact False.elim (hmem (Finset.mem_range.mpr hj))
      rw [show B.coeff j = (∑ i ∈ Finset.range (d₂ + 1), (Polynomial.monomial i (coeffy i)).coeff j) by
          simp [B]]
      rw [if_pos hj]
      exact hsum
    · have hzero : (∑ i ∈ Finset.range (d₂ + 1), (Polynomial.monomial i (coeffy i))).coeff j = 0 := by
        rw [finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i < d₂ + 1 := Finset.mem_range.mp hi
        have hij : i ≠ j := by omega
        simp [Polynomial.coeff_monomial, hij]
      rw [show B.coeff j = (∑ i ∈ Finset.range (d₂ + 1), (Polynomial.monomial i (coeffy i))).coeff j by
          simp [B]]
      rw [if_neg hj]
      exact hzero
  -- assembled polynomials reduce to the level data
  have A_level (n : ℕ) : Polynomial.map (PadicInt.toZModPow (n+1)) A = (F n).α := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map]
    by_cases hj : j < d₁ + 1
    · rw [A_coeff j, if_pos hj]
      have hs := coeffx_spec j (n+1)
      have hseq : levelCoeffSeq F j (n+1) = ((F n).α.coeff j).val := by
        simp [levelCoeffSeq]
      have hs' : (PadicInt.toZModPow (n+1)) (coeffx j) = (((F n).α.coeff j).val : ZMod (p ^ (n+1))) := by
        simpa [hseq] using hs
      rw [hs']
      exact ZMod.natCast_zmod_val ((F n).α.coeff j)
    · rw [A_coeff j, if_neg hj]
      simp
      exact (coeff_eq_zero_of_natDegree_lt (p := (F n).α) (by
        rw [(F n).degα]
        omega)).symm
  have B_level (n : ℕ) : Polynomial.map (PadicInt.toZModPow (n+1)) B = (F n).β := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map]
    by_cases hj : j < d₂ + 1
    · rw [B_coeff j, if_pos hj]
      have hs := coeffy_spec j (n+1)
      have hseq : levelCoeffSeqβ F j (n+1) = ((F n).β.coeff j).val := by
        simp [levelCoeffSeqβ]
      have hs' : (PadicInt.toZModPow (n+1)) (coeffy j) = (((F n).β.coeff j).val : ZMod (p ^ (n+1))) := by
        simpa [hseq] using hs
      rw [hs']
      exact ZMod.natCast_zmod_val ((F n).β.coeff j)
    · rw [B_coeff j, if_neg hj]
      simp
      exact (coeff_eq_zero_of_natDegree_lt (p := (F n).β) (by
        rw [(F n).degβ]
        omega)).symm
  -- the top coefficients are 1
  have coeffx_d₁ : coeffx d₁ = 1 := by
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    rw [coeffx_spec d₁ n]
    by_cases hn : n = 0
    · subst n
      haveI : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hc1 : (F m).α.coeff d₁ = 1 := by
        dsimp [d₁]
        rw [← (F m).degα]
        rw [Polynomial.coeff_natDegree]
        exact (F m).monα
      have hseq : levelCoeffSeq F d₁ (m+1) = ((F m).α.coeff d₁).val := by
        simp [levelCoeffSeq]
      rw [hseq, hc1]
      simp
  have coeffy_d₂ : coeffy d₂ = 1 := by
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    rw [coeffy_spec d₂ n]
    by_cases hn : n = 0
    · subst n
      haveI : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hc1 : (F m).β.coeff d₂ = 1 := by
        dsimp [d₂]
        rw [← (F m).degβ]
        rw [Polynomial.coeff_natDegree]
        exact (F m).monβ
      have hseq : levelCoeffSeqβ F d₂ (m+1) = ((F m).β.coeff d₂).val := by
        simp [levelCoeffSeqβ]
      rw [hseq, hc1]
      simp
  have A_coeff_d₁ : A.coeff d₁ = 1 := by
    rw [A_coeff d₁, if_pos (by omega : d₁ < d₁ + 1)]
    exact coeffx_d₁
  have B_coeff_d₂ : B.coeff d₂ = 1 := by
    rw [B_coeff d₂, if_pos (by omega : d₂ < d₂ + 1)]
    exact coeffy_d₂
  -- monicity and degrees
  have A_nat : A.natDegree = d₁ := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
        intro j hj
        rw [A_coeff j, if_neg (by omega : ¬ j < d₁ + 1)])
    · rw [A_coeff_d₁]
      simp
  have A_monic : A.Monic := by
    rw [Polynomial.Monic.def]
    rw [← Polynomial.coeff_natDegree (p := A), A_nat]
    exact A_coeff_d₁
  have B_nat : B.natDegree = d₂ := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
        intro j hj
        rw [B_coeff j, if_neg (by omega : ¬ j < d₂ + 1)])
    · rw [B_coeff_d₂]
      simp
  have B_monic : B.Monic := by
    rw [Polynomial.Monic.def]
    rw [← Polynomial.coeff_natDegree (p := B), B_nat]
    exact B_coeff_d₂
  -- product identity
  have hprod_level (n : ℕ) : Polynomial.map (PadicInt.toZModPow (n+1)) (A * B) =
      Polynomial.map (PadicInt.toZModPow (n+1)) f := by
    rw [Polynomial.map_mul, A_level n, B_level n]
    exact (F n).fac
  have hAB : A * B = f := by
    apply Polynomial.ext
    intro j
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    by_cases hn : n = 0
    · subst n
      haveI : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact Subsingleton.elim _ _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map]
      exact congrArg (fun P : (ZMod (p ^ (m + 1)))[X] => P.coeff j) (hprod_level m)
  -- reductions modulo p
  have hA_red : A.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a := by
    have h1 := A_level 0
    calc
      Polynomial.map (PadicInt.toZMod (p := p)) A
          = Polynomial.map (((zmodOne p).toRingHom).comp (PadicInt.toZModPow (p := p) 1)) A := by
            exact congrArg (fun φ : ℤ_[p] →+* ZMod p => Polynomial.map φ A)
              (toZMod_eq_congr_comp_toZModPow_one (p := p)).symm
      _ = Polynomial.map ((zmodOne p).toRingHom) (Polynomial.map (PadicInt.toZModPow (p := p) 1) A) := by
            rw [← Polynomial.map_map]
      _ = Polynomial.map ((zmodOne p).toRingHom) ((F 0).α) := by rw [h1]
      _ = Polynomial.map (redMap (p := p) 1 (by omega : 1 ≤ 1)) ((F 0).α) := by rw [← redMap_one_eq]
      _ = a := (F 0).redα
  have hB_red : B.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = b := by
    have h1 := B_level 0
    calc
      Polynomial.map (PadicInt.toZMod (p := p)) B
          = Polynomial.map (((zmodOne p).toRingHom).comp (PadicInt.toZModPow (p := p) 1)) B := by
            exact congrArg (fun φ : ℤ_[p] →+* ZMod p => Polynomial.map φ B)
              (toZMod_eq_congr_comp_toZModPow_one (p := p)).symm
      _ = Polynomial.map ((zmodOne p).toRingHom) (Polynomial.map (PadicInt.toZModPow (p := p) 1) B) := by
            rw [← Polynomial.map_map]
      _ = Polynomial.map ((zmodOne p).toRingHom) ((F 0).β) := by rw [h1]
      _ = Polynomial.map (redMap (p := p) 1 (by omega : 1 ≤ 1)) ((F 0).β) := by rw [← redMap_one_eq]
      _ = b := (F 0).redβ
  refine ⟨A, B, A_monic, B_monic, ?_, ?_, ?_, hA_red, hB_red⟩
  · simpa [d₁] using A_nat
  · simpa [d₂] using B_nat
  · exact hAB.symm

end Commons.NumberTheory.Padics
