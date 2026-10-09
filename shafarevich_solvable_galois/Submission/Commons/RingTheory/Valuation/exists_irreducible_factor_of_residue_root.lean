import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open Polynomial

/-- A nonzero non-unit divisor of a monic polynomial over a domain has positive degree. -/
lemma natDegree_pos_of_dvd_monic {R : Type*} [CommRing R] [IsDomain R]
    {g p : Polynomial R} (hg : g.Monic) (hdvd : p ∣ g) (hpu : ¬ IsUnit p) :
    0 < p.natDegree := by
  obtain ⟨q, hq⟩ := hdvd
  have hg0 : g ≠ 0 := hg.ne_zero
  have hp0 : p ≠ 0 := by rintro rfl; simp at hq; exact hg0 hq
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hg0 hq
  by_contra h
  have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_not_pos h
  have hlc : p.leadingCoeff * q.leadingCoeff = 1 := by
    have h1 := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, hg.leadingCoeff] at h1
    exact h1.symm
  have hunit : IsUnit p.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨q.leadingCoeff, hlc⟩
  have hcoeff : p.coeff 0 = p.leadingCoeff := by
    rw [← hpdeg]
    exact Polynomial.coeff_natDegree
  have hp_eq : p = C p.leadingCoeff :=
    (Polynomial.eq_C_of_natDegree_eq_zero hpdeg).trans (by rw [hcoeff])
  rw [hp_eq] at hpu
  exact hpu (Polynomial.isUnit_C.mpr hunit)

theorem exists_irreducible_factor_of_residue_root {F : Type*} [Field F] (V : ValuationSubring F)
    (f : Polynomial V) (hf : f.Monic) (a : V)
    (h0 : f.eval a ∈ IsLocalRing.maximalIdeal V)
    (h1 : IsUnit (f.derivative.eval a)) :
    ∃ g : Polynomial V, g.Monic ∧ Irreducible (g.map (algebraMap V F)) ∧ g ∣ f ∧
      g.eval a ∈ IsLocalRing.maximalIdeal V ∧ IsUnit (g.derivative.eval a) := by
  classical
  have hmprime : (IsLocalRing.maximalIdeal V).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal V).isPrime
  have hm_unit : ∀ {x : V}, x ∈ IsLocalRing.maximalIdeal V → ¬ IsUnit x := by
    intro x hx
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  have hnonunit_mem : ∀ {x : V}, ¬ IsUnit x → x ∈ IsLocalRing.maximalIdeal V := by
    intro x hx
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  -- a monic divisor of `f` of minimal degree which has `a` as a root modulo the maximal ideal
  let P : ℕ → Prop := fun n => ∃ g : Polynomial V,
    g.Monic ∧ g ∣ f ∧ g.eval a ∈ IsLocalRing.maximalIdeal V ∧ g.natDegree = n
  have hP : ∃ n, P n := ⟨f.natDegree, f, hf, dvd_rfl, h0, rfl⟩
  obtain ⟨g, hgmonic, hgdvd, hgeval, hgdeg⟩ := Nat.find_spec hP
  have hmin : ∀ h : Polynomial V, h.Monic → h ∣ f → h.eval a ∈ IsLocalRing.maximalIdeal V →
      Nat.find hP ≤ h.natDegree := by
    intro h h1 h2 h3
    exact Nat.find_min' hP ⟨h, h1, h2, h3, rfl⟩
  have hg0 : g ≠ 0 := hgmonic.ne_zero
  have hnotunit : ¬ IsUnit g := fun hgu =>
    hm_unit hgeval (hgu.map (Polynomial.evalRingHom a))
  -- `g` is irreducible over `V`
  have hirr : Irreducible g := by
    rw [irreducible_iff]
    refine ⟨hnotunit, ?_⟩
    intro u w huw
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hu_nu, hw_nu⟩ := hc
    have hu0 : u ≠ 0 := by rintro rfl; simp at huw; exact hg0 huw
    have hw0 : w ≠ 0 := by rintro rfl; simp at huw; exact hg0 huw
    have hudvd : u ∣ g := ⟨w, huw⟩
    have hwdvd : w ∣ g := ⟨u, by rw [huw, mul_comm]⟩
    have hudeg : 0 < u.natDegree := natDegree_pos_of_dvd_monic hgmonic hudvd hu_nu
    have hwdeg : 0 < w.natDegree := natDegree_pos_of_dvd_monic hgmonic hwdvd hw_nu
    have hdegadd : g.natDegree = u.natDegree + w.natDegree := by
      rw [huw, Polynomial.natDegree_mul hu0 hw0]
    have hlcmul : u.leadingCoeff * w.leadingCoeff = 1 := by
      have h1 := congrArg Polynomial.leadingCoeff huw
      rw [Polynomial.leadingCoeff_mul, hgmonic.leadingCoeff] at h1
      exact h1.symm
    have hulc : u.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu0
    have hwlc : w.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hw0
    have hlcmul' : w.leadingCoeff * u.leadingCoeff = 1 := by rw [mul_comm, hlcmul]
    have hu'monic : (C w.leadingCoeff * u).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlcmul']
    have hw'monic : (C u.leadingCoeff * w).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlcmul]
    have hu'deg : (C w.leadingCoeff * u).natDegree = u.natDegree :=
      Polynomial.natDegree_C_mul hwlc
    have hw'deg : (C u.leadingCoeff * w).natDegree = w.natDegree :=
      Polynomial.natDegree_C_mul hulc
    have hnorm : (C w.leadingCoeff * u) * (C u.leadingCoeff * w) = g := by
      calc (C w.leadingCoeff * u) * (C u.leadingCoeff * w)
          = (C w.leadingCoeff * C u.leadingCoeff) * (u * w) := by ring
        _ = C (w.leadingCoeff * u.leadingCoeff) * (u * w) := by rw [C_mul]
        _ = C 1 * (u * w) := by rw [hlcmul']
        _ = g := by rw [C_1, one_mul, huw]
    have hmem : (C w.leadingCoeff * u).eval a ∈ IsLocalRing.maximalIdeal V ∨
        (C u.leadingCoeff * w).eval a ∈ IsLocalRing.maximalIdeal V := by
      have hmul : (C w.leadingCoeff * u).eval a * (C u.leadingCoeff * w).eval a =
          g.eval a := by
        rw [← Polynomial.eval_mul, hnorm]
      exact hmprime.mem_or_mem (by rw [hmul]; exact hgeval)
    rcases hmem with h | h
    · have hle := hmin (C w.leadingCoeff * u) hu'monic (dvd_trans ⟨C u.leadingCoeff * w, hnorm.symm⟩ hgdvd) h
      have hlt : (C w.leadingCoeff * u).natDegree < Nat.find hP := by
        rw [hu'deg, ← hgdeg, hdegadd]
        omega
      omega
    · have hle := hmin (C u.leadingCoeff * w) hw'monic
        (dvd_trans ⟨C w.leadingCoeff * u, by rw [← hnorm, mul_comm]⟩ hgdvd) h
      have hlt : (C u.leadingCoeff * w).natDegree < Nat.find hP := by
        rw [hw'deg, ← hgdeg, hdegadd]
        omega
      omega
  -- `g.derivative.eval a` is a unit
  have hderiv : IsUnit (g.derivative.eval a) := by
    by_contra hgd
    have hdmem : g.derivative.eval a ∈ IsLocalRing.maximalIdeal V := hnonunit_mem hgd
    obtain ⟨s, hs⟩ := hgdvd
    have hder : f.derivative.eval a =
        g.derivative.eval a * s.eval a + g.eval a * s.derivative.eval a := by
      rw [hs, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul]
    have hmemf : f.derivative.eval a ∈ IsLocalRing.maximalIdeal V := by
      rw [hder]
      exact Ideal.add_mem _
        (Ideal.mul_mem_right (s.eval a) (IsLocalRing.maximalIdeal V) hdmem)
        (Ideal.mul_mem_right (s.derivative.eval a) (IsLocalRing.maximalIdeal V) hgeval)
    exact hm_unit hmemf h1
  refine ⟨g, hgmonic, ?_, hgdvd, hgeval, hderiv⟩
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := F) hgmonic).mp hirr

end Commons.RingTheory.Valuation