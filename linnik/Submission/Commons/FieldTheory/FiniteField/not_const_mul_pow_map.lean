import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.FiniteField

open Polynomial

/-! ## Auxiliary lemmas about truncation of polynomials

`truncAux k P` keeps the coefficients of `P` of degree `< k`.  The main point is the
recursion identity `coeff_truncAux_succ_pow`, which lets one read off the coefficients of a
`p`-th power from the coefficients of the base polynomial one at a time (characteristic `≠ p`).
-/

section Aux

variable {E : Type*} [Field E]

/-- Truncation of a polynomial: keep the coefficients of degree `< k`. -/
noncomputable def truncAux (k : ℕ) (P : Polynomial E) : Polynomial E :=
  ∑ i ∈ Finset.range k, Polynomial.monomial i (P.coeff i)

theorem truncAux_coeff (k : ℕ) (P : Polynomial E) (j : ℕ) :
    (truncAux k P).coeff j = if j < k then P.coeff j else 0 := by
  rw [truncAux, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

theorem truncAux_succ (k : ℕ) (P : Polynomial E) :
    truncAux (k + 1) P = truncAux k P + Polynomial.C (P.coeff k) * Polynomial.X ^ k := by
  rw [truncAux, Finset.sum_range_succ, truncAux, Polynomial.C_mul_X_pow_eq_monomial]

theorem X_pow_dvd_sub_truncAux (k : ℕ) (P : Polynomial E) :
    Polynomial.X ^ k ∣ P - truncAux k P := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, truncAux_coeff, if_pos hd, sub_self]

theorem coeff_zero_mul' (P Q : Polynomial E) :
    (P * Q).coeff 0 = P.coeff 0 * Q.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
    ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]

theorem coeff_zero_pow' (P : Polynomial E) (n : ℕ) : (P ^ n).coeff 0 = (P.coeff 0) ^ n := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
    ← Polynomial.coeff_zero_eq_eval_zero]

/-- Congruent polynomials (mod `X ^ n`) have `p`-th powers with the same coefficient in
degree `k < n`. -/
theorem coeff_pow_congr (P Q : Polynomial E) (k p n : ℕ)
    (h : Polynomial.X ^ n ∣ P - Q) (hk : k < n) : (P ^ p).coeff k = (Q ^ p).coeff k := by
  have hdvd : Polynomial.X ^ n ∣ P ^ p - Q ^ p := by
    rw [← (Commute.all P Q).mul_geom_sum₂ p]
    exact h.mul_right _
  rw [Polynomial.X_pow_dvd_iff] at hdvd
  have h0 : (P ^ p - Q ^ p).coeff k = 0 := hdvd k hk
  rw [Polynomial.coeff_sub] at h0
  exact sub_eq_zero.mp h0

theorem coeff_pow_eq_truncAux (r : Polynomial E) (k p : ℕ) :
    (r ^ p).coeff k = ((truncAux (k + 1) r) ^ p).coeff k :=
  coeff_pow_congr r (truncAux (k + 1) r) k p (k + 1)
    (X_pow_dvd_sub_truncAux (k + 1) r) (Nat.lt_succ_self k)

/-- The recursion identity: extending a truncation whose constant coefficient is `1` by the
term of degree `k` (`k ≥ 1`) changes the `k`-th coefficient of the `p`-th power by `p`
times the new coefficient. -/
theorem coeff_truncAux_succ_pow (r : Polynomial E) (hr : r.coeff 0 = 1)
    (k p : ℕ) (hk : 1 ≤ k) :
    ((truncAux (k + 1) r) ^ p).coeff k
      = ((truncAux k r) ^ p).coeff k + (p : E) * r.coeff k := by
  set A := truncAux k r with hAdef
  set c := r.coeff k with hcdef
  set B := Polynomial.C c * Polynomial.X ^ k with hBdef
  have hAB : truncAux (k + 1) r = A + B := by
    rw [truncAux_succ, hAdef, hBdef, hcdef]
  have hA0 : A.coeff 0 = 1 := by
    rw [hAdef, truncAux_coeff, if_pos (by omega), hr]
  have hB0 : B.coeff 0 = 0 := by
    rw [hBdef, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  set S := ∑ i ∈ Finset.range p, (A + B) ^ i * A ^ (p - 1 - i) with hSdef
  have hgeom : (A + B) ^ p - A ^ p = B * S := by
    have h := (Commute.all (A + B) A).mul_geom_sum₂ p
    rw [add_sub_cancel_left] at h
    exact h.symm
  have hAB0 : (A + B).coeff 0 = 1 := by
    rw [Polynomial.coeff_add, hA0, hB0, add_zero]
  have hS0 : S.coeff 0 = (p : E) := by
    rw [hSdef, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    have hterm : ∀ i, ((A + B) ^ i * A ^ (p - 1 - i)).coeff 0 = 1 := by
      intro i
      rw [coeff_zero_mul', coeff_zero_pow', coeff_zero_pow', hAB0, hA0]
      simp
    simp_rw [hterm]
    simp
  have hBS : (B * S).coeff k = (p : E) * c := by
    rw [hBdef, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', if_pos le_rfl,
      tsub_self, hS0]
    ring
  have hmain : ((A + B) ^ p - A ^ p).coeff k = (p : E) * c := by
    rw [hgeom, hBS]
  rw [Polynomial.coeff_sub] at hmain
  rw [hAB]
  rw [sub_eq_iff_eq_add] at hmain
  rw [hmain]
  ring

theorem reverse_pow (P : Polynomial E) (n : ℕ) : (P ^ n).reverse = P.reverse ^ n := by
  induction n with
  | zero => simpa using Polynomial.reverse_C (1 : E)
  | succ n ih => rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]

theorem eq_sum_support_monomial (P : Polynomial E) :
    P = ∑ i ∈ P.support, Polynomial.monomial i (P.coeff i) := by
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq P]
  rw [Polynomial.sum]
  simp only [Polynomial.C_mul_X_pow_eq_monomial]

end Aux

/-- **Base change invariance of "not a constant times a `p`-th power".**

If a polynomial `f` over a field `F` is not of the form `C a * h ^ p`, then its image under a
field extension `F → E` (with `(p : E) ≠ 0`) is not of that form over `E` either. -/
theorem not_const_mul_pow_map {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [Algebra F E] (p : ℕ) (hp : p.Prime) (hchar : (p : E) ≠ 0) (f : Polynomial F)
    (hf : ∀ (a : F) (h : Polynomial F), f ≠ Polynomial.C a * h ^ p) :
    ∀ (a : E) (h : Polynomial E), f.map (algebraMap F E) ≠ Polynomial.C a * h ^ p := by
  intro a h hab
  have hinj : Function.Injective (algebraMap F E) := RingHom.injective _
  -- `f` and its image are nonzero
  have hf0 : f ≠ 0 := by
    intro h0
    exact hf 0 0 (by rw [h0, Polynomial.C_0, zero_mul])
  have hfm0 : f.map (algebraMap F E) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfm0 (by rw [hab, Polynomial.C_0, zero_mul])
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hfm0 (by rw [hab, zero_pow hp.ne_zero, mul_zero])
  -- normalise `h` to be monic
  set b : E := h.leadingCoeff with hb
  have hb0 : b ≠ 0 := by rw [hb]; exact Polynomial.leadingCoeff_ne_zero.mpr hh0
  set h₁ : Polynomial E := Polynomial.C b⁻¹ * h with hh1def
  have hh1monic : h₁.Monic := by
    rw [hh1def]
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [← hb, inv_mul_cancel₀ hb0]
  have hh_eq : Polynomial.C b * h₁ = h := by
    rw [hh1def, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hb0, Polynomial.C_1, one_mul]
  set a₁ : E := a * b ^ p with ha1def
  have hnew : f.map (algebraMap F E) = Polynomial.C a₁ * h₁ ^ p := by
    rw [hab, ← hh_eq, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      ← ha1def]
  -- `S` is the image of `F` in `E`, a subfield
  set S : Subfield E := (algebraMap F E).fieldRange with hSdef
  have memS : ∀ x : E, x ∈ S ↔ ∃ y : F, algebraMap F E y = x := by
    intro x; rw [hSdef]; exact RingHom.mem_fieldRange
  -- `a₁` is the leading coefficient of `f`, hence lies in `S`
  have ha₁eq : a₁ = algebraMap F E f.leadingCoeff := by
    have h1 : (Polynomial.C a₁ * h₁ ^ p).leadingCoeff = a₁ := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_pow,
        hh1monic.leadingCoeff, one_pow, mul_one]
    have h2 : (f.map (algebraMap F E)).leadingCoeff = algebraMap F E f.leadingCoeff :=
      Polynomial.leadingCoeff_map_of_injective hinj f
    rw [← h2, hnew, h1]
  have ha₁S : a₁ ∈ S := (memS a₁).mpr ⟨f.leadingCoeff, ha₁eq.symm⟩
  have hpS : (p : E) ∈ S := (memS (p : E)).mpr ⟨(p : F), map_natCast (algebraMap F E) p⟩
  have ha₁0 : a₁ ≠ 0 := by rw [ha1def]; exact mul_ne_zero ha0 (pow_ne_zero p hb0)
  -- reverse the polynomial to get an ascending recursion
  set r : Polynomial E := h₁.reverse with hrdef
  have hrev : Polynomial.C a₁ * r ^ p = (f.map (algebraMap F E)).reverse := by
    rw [hnew, Polynomial.reverse_mul_of_domain, Polynomial.reverse_C, reverse_pow, ← hrdef]
  have hr0 : r.coeff 0 = 1 := by
    rw [hrdef, Polynomial.coeff_zero_reverse, hh1monic.leadingCoeff]
  have hrevcoeff : ∀ k, (f.map (algebraMap F E)).reverse.coeff k ∈ S := by
    intro k
    rw [memS]
    refine ⟨f.coeff (Polynomial.revAt f.natDegree k), ?_⟩
    rw [Polynomial.coeff_reverse, Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.coeff_map]
  -- the recursive determination of the coefficients of `r`
  have hcoeff : ∀ k, r.coeff k ∈ S := fun k =>
    Nat.strongRecOn (motive := fun k => r.coeff k ∈ S) k (fun k ih => by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [memS]
        exact ⟨1, by rw [map_one, hr0]⟩
      · have hA_mem : truncAux k r ∈ (Polynomial.mapRingHom (algebraMap F E)).range := by
          rw [truncAux]
          apply Subring.sum_mem
          intro i hi
          rw [Finset.mem_range] at hi
          obtain ⟨c, hc⟩ := (memS (r.coeff i)).mp (ih i hi)
          refine ⟨Polynomial.C c * Polynomial.X ^ i, ?_⟩
          rw [show Polynomial.mapRingHom (algebraMap F E) (Polynomial.C c * Polynomial.X ^ i)
                = Polynomial.map (algebraMap F E) (Polynomial.C c * Polynomial.X ^ i) from rfl,
            Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hc,
            ← Polynomial.C_mul_X_pow_eq_monomial]
        have hAp_coeff : ((truncAux k r) ^ p).coeff k ∈ S := by
          obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp hA_mem
          rw [memS]
          refine ⟨(Q ^ p).coeff k, ?_⟩
          rw [← hQ,
            show Polynomial.mapRingHom (algebraMap F E) Q
              = Polynomial.map (algebraMap F E) Q from rfl,
            ← Polynomial.map_pow, Polynomial.coeff_map]
        have hmain : a₁ * (r ^ p).coeff k = (f.map (algebraMap F E)).reverse.coeff k := by
          rw [← hrev, Polynomial.coeff_C_mul]
        have h1 : a₁ * (r ^ p).coeff k ∈ S := by rw [hmain]; exact hrevcoeff k
        have h2 : a₁ * ((truncAux k r) ^ p).coeff k ∈ S := S.mul_mem ha₁S hAp_coeff
        have h3 : a₁ * ((p : E) * r.coeff k) ∈ S := by
          have hsub := S.sub_mem h1 h2
          convert hsub using 1
          rw [← mul_sub, coeff_pow_eq_truncAux r k p, coeff_truncAux_succ_pow r hr0 k p hk]
          ring
        have hxS : a₁ * (p : E) ∈ S := S.mul_mem ha₁S hpS
        have hxne : a₁ * (p : E) ≠ 0 := mul_ne_zero ha₁0 hchar
        obtain ⟨d, hd⟩ := (memS _).mp hxS
        obtain ⟨e, he⟩ := (memS _).mp h3
        have hd0 : d ≠ 0 := by
          rintro rfl
          rw [map_zero] at hd
          exact hxne hd.symm
        have hinvd : algebraMap F E d⁻¹ = (algebraMap F E d)⁻¹ := by
          refine eq_inv_of_mul_eq_one_right ?_
          rw [← map_mul, mul_inv_cancel₀ hd0, map_one]
        rw [memS]
        refine ⟨d⁻¹ * e, ?_⟩
        rw [map_mul, hinvd, hd, he,
          show a₁ * ((p : E) * r.coeff k) = (a₁ * (p : E)) * r.coeff k by ring,
          ← mul_assoc, inv_mul_cancel₀ hxne, one_mul])
  -- assemble: `h₁` has all coefficients in `S`
  have hh₁_coeff : ∀ j, h₁.coeff j ∈ S := by
    intro j
    rcases lt_or_ge h₁.natDegree j with hj | hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj]; exact S.zero_mem
    · have h := Polynomial.coeff_reverse h₁ (h₁.natDegree - j)
      rw [← hrdef] at h
      rw [Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hj] at h
      rw [← h]; exact hcoeff _
  -- so `h₁` is the image of a polynomial over `F`
  have hmem : h₁ ∈ (Polynomial.mapRingHom (algebraMap F E)).range := by
    rw [eq_sum_support_monomial h₁]
    apply Subring.sum_mem
    intro i hi
    obtain ⟨c, hc⟩ := (memS (h₁.coeff i)).mp (hh₁_coeff i)
    refine ⟨Polynomial.C c * Polynomial.X ^ i, ?_⟩
    rw [show Polynomial.mapRingHom (algebraMap F E) (Polynomial.C c * Polynomial.X ^ i)
          = Polynomial.map (algebraMap F E) (Polynomial.C c * Polynomial.X ^ i) from rfl,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hc,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  obtain ⟨h₀, hh₀⟩ := RingHom.mem_range.mp hmem
  -- contradict `hf`
  have hmap : f.map (algebraMap F E) = (Polynomial.C f.leadingCoeff * h₀ ^ p).map
      (algebraMap F E) := by
    rw [hnew, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, ← ha₁eq,
      show Polynomial.map (algebraMap F E) h₀ = h₁ from hh₀]
  exact hf f.leadingCoeff h₀ (Polynomial.map_injective (algebraMap F E) hinj hmap)

end Commons.FieldTheory.FiniteField