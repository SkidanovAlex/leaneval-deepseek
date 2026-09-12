/-
Per-circle well-definedness (WD) for the family orbit: all coprime tangent
partners of one circle in the packing of famQuad t give one Kronecker symbol
value against the circle's curvature.  (Family analogue of WD.lean.)
-/
import Submission.Apollo.FamOrbit
import Submission.Apollo.FamQForms
import Submission.Apollo.SarnakParam
import Submission.Apollo.PropSingleton
import Submission.Apollo.ChiCross
import Submission.Apollo.Partner
import Submission.Apollo.KsymTool
import Submission.Apollo.WD
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped NumberTheorySymbols
open scoped Pointwise
open LocalGlobalApollonianCirclePackings
namespace Apollo

/-- odd coprime partners of a family-orbit circle are ≡ 5 mod 8. -/
lemma fam_copartner_odd_mod8 (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) {c : ℤ} (hc : RingCopartner w i c) (hodd : ¬ 2 ∣ c) : c % 8 = 5 := by
  rcases hc with ⟨u, hu, j, hji, huj, hg⟩
  have huorb : u ∈ orbitOf (famQuad t) := famOrbit_ringReach t w hw i u hu
  rw [← huj] at hodd
  have hjin : j = 0 ∨ j = 1 := (famOrbit_coord_odd_iff t u huorb j).1 hodd
  have h5 : u j % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t u huorb j hjin
  rwa [huj] at h5

/-- per-prime equality of Jacobi symbols for two coprime partners (family). -/
lemma fam_copartner_jacobi_eq (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) (c₁ c₂ : ℤ) (hc₁ : RingCopartner w i c₁) (hc₂ : RingCopartner w i c₂)
    (p : ℕ) (pp : p.Prime) (hpodd : p ≠ 2) (hpd : p ∣ (w i).natAbs) :
    jacobiSym c₁ p = jacobiSym c₂ p := by
  haveI : Fact p.Prime := ⟨pp⟩
  rcases hc₁ with ⟨u₁, hu₁, j₁, hj₁, huj₁, hg₁⟩
  rcases hc₂ with ⟨u₂, hu₂, j₂, hj₂, huj₂, hg₂⟩
  have hq₁ := sarnak_ring_partner w i u₁ hu₁ j₁ hj₁
  have hq₂ := sarnak_ring_partner w i u₂ hu₂ j₂ hj₂
  rcases hq₁ with ⟨x₁, y₁, hf₁⟩
  rcases hq₂ with ⟨x₂, y₂, hf₂⟩
  have hpa : (w i : ZMod p) = 0 := cast_zmod_eq_zero_of_natAbs_dvd hpd
  have hD := fam_qf_discriminant t w hw i
  have hnz₁ : (c₁ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₁ hpd pp
  have hnz₂ : (c₂ : ZMod p) ≠ 0 := zmod_ne_zero_of_gcd_one_of_dvd hg₂ hpd pp
  have hsq := form_pair_square_zmod (qfA w i) (qfB w i) (qfC w i) (w i) x₁ y₁ x₂ y₂ p pp hpodd hpa hD
  let R₁ : ℤ := qfA w i * x₁ ^ 2 + qfB w i * x₁ * y₁ + qfC w i * y₁ ^ 2
  let R₂ : ℤ := qfA w i * x₂ ^ 2 + qfB w i * x₂ * y₂ + qfC w i * y₂ ^ 2
  have hR₁ : qfEval w i x₁ y₁ = R₁ := by rfl
  have hR₂ : qfEval w i x₂ y₂ = R₂ := by rfl
  have hsub₁ : c₁ = qfEval w i x₁ y₁ - w i := by
    calc c₁ = u₁ j₁ := huj₁.symm
         _ = qfEval w i x₁ y₁ - w i := hf₁
  have hsub₂ : c₂ = qfEval w i x₂ y₂ - w i := by
    calc c₂ = u₂ j₂ := huj₂.symm
         _ = qfEval w i x₂ y₂ - w i := hf₂
  have hdif : (p : ℤ) ∣ c₁ * c₂ - R₁ * R₂ := by
    have hpz : (p : ℤ) ∣ w i := Int.natCast_dvd.mpr hpd
    rcases hpz with ⟨t', ht⟩
    refine ⟨t' * (-R₁ - R₂ + w i), ?_⟩
    rw [hsub₁, hsub₂]
    rw [hR₁, hR₂]
    rw [ht]
    ring
  have hEqCast : ((c₁ * c₂ : ℤ) : ZMod p) = ((R₁ * R₂ : ℤ) : ZMod p) := by
    have hz : ((c₁ * c₂ - R₁ * R₂ : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (c₁ * c₂ - R₁ * R₂) p).2 hdif
    calc
      ((c₁ * c₂ : ℤ) : ZMod p) = (((c₁ * c₂ - R₁ * R₂) + R₁ * R₂ : ℤ) : ZMod p) := by
        congr 1
        ring
      _ = ((R₁ * R₂ : ℤ) : ZMod p) := by
        rw [Int.cast_add]
        rw [hz]
        simp
  have hsq' : ∃ u : ZMod p, (c₁ * c₂ : ZMod p) = u ^ 2 := by
    rcases hsq with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    calc
      (c₁ * c₂ : ZMod p) = ((c₁ * c₂ : ℤ) : ZMod p) := (Int.cast_mul (α := ZMod p) c₁ c₂).symm
      _ = ((R₁ * R₂ : ℤ) : ZMod p) := hEqCast
      _ = u ^ 2 := hu
  have hnz : ((c₁ * c₂ : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_mul]
    exact mul_ne_zero hnz₁ hnz₂
  have hJ : jacobiSym (c₁ * c₂) p = 1 := by
    apply jacobiSym_eq_one_of_square (c₁ * c₂) p pp
    · exact hnz
    · simpa using hsq'
  have hg₁p : c₁.gcd p = 1 := gcd_of_natAbs_dvd hg₁ hpd
  have hg₂p : c₂.gcd p = 1 := gcd_of_natAbs_dvd hg₂ hpd
  have h1 : jacobiSym c₁ p = 1 ∨ jacobiSym c₁ p = -1 := jacobiSym.eq_one_or_neg_one hg₁p
  have h2 : jacobiSym c₂ p = 1 ∨ jacobiSym c₂ p = -1 := jacobiSym.eq_one_or_neg_one hg₂p
  have hmul := jacobiSym.mul_left c₁ c₂ p
  rw [hmul] at hJ
  rcases h1 with h1a | h1a <;> rcases h2 with h2a | h2a
  · rw [h1a, h2a]
  · exfalso
    rw [h1a, h2a] at hJ
    norm_num at hJ
  · exfalso
    rw [h1a, h2a] at hJ
    norm_num at hJ
  · rw [h1a, h2a]

/-- WD for any modulus n | |w i| (family). -/
theorem fam_wd_div (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) (n : ℕ) (hn : n ∣ (w i).natAbs) (c₁ c₂ : ℤ)
    (hc₁ : RingCopartner w i c₁) (hc₂ : RingCopartner w i c₂) :
    ksym c₁ n = ksym c₂ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [ksym]
    · by_cases hodd : Odd n
      · by_cases hn1 : n = 1
        · subst n
          simp [ksym]
        · have h₁ : ksym c₁ n = jacobiSym c₁ n := ksym_odd c₁ hodd
          have h₂ : ksym c₂ n = jacobiSym c₂ n := ksym_odd c₂ hodd
          rcases Nat.exists_prime_and_dvd hn1 with ⟨p, pp, hpn⟩
          rcases hpn with ⟨m, hm⟩
          have hpn' : p ∣ n := ⟨m, hm⟩
          have hpodd : p ≠ 2 := by
            intro hp2
            subst p
            exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn')
          have hmod : Odd m := by
            by_contra hme
            have hmev : Even m := Nat.not_odd_iff_even.mp hme
            rcases hmev with ⟨k, hk⟩
            have hnm : Even n := by
              refine ⟨p * k, ?_⟩
              rw [hm, hk]
              ring
            exact (Nat.not_even_iff_odd.mpr hodd) hnm
          have hpd_abs : p ∣ (w i).natAbs := dvd_trans hpn' hn
          have hp_eq := fam_copartner_jacobi_eq t w hw i c₁ c₂ hc₁ hc₂ p pp hpodd hpd_abs
          have hm0 : m ≠ 0 := by
            intro hmz
            subst m
            have : n = 0 := by rw [hm]; ring
            exact hn0 this
          have hmlt : m < n := by
            have h2m : m < 2 * m := by omega
            have h2mn : 2 * m ≤ p * m := Nat.mul_le_mul pp.two_le le_rfl
            calc m < 2 * m := h2m
                 _ ≤ p * m := h2mn
                 _ = n := by rw [hm]
          have hmdvd : m ∣ (w i).natAbs := by
            refine dvd_trans ⟨p, ?_⟩ hn
            calc
              n = p * m := hm
              _ = m * p := Nat.mul_comm p m
          have hIH := ih m hmlt hmdvd
          rw [h₁, h₂]
          calc
            jacobiSym c₁ n = jacobiSym c₁ (p * m) := by rw [hm]
            _ = jacobiSym c₁ p * jacobiSym c₁ m :=
              jacobiSym.mul_right' c₁ (Nat.Prime.ne_zero pp) hm0
            _ = jacobiSym c₂ p * jacobiSym c₂ m := by
              rw [hp_eq]
              rw [← ksym_odd c₁ hmod, hIH, ksym_odd c₂ hmod]
            _ = jacobiSym c₂ (p * m) :=
              (jacobiSym.mul_right' c₂ (Nat.Prime.ne_zero pp) hm0).symm
            _ = jacobiSym c₂ n := by rw [hm]
      · have hne : Even n := Nat.not_odd_iff_even.mp hodd
        have h₂n : 2 ∣ n := even_iff_two_dvd.mp hne
        have h2abs : 2 ∣ (w i).natAbs := dvd_trans h₂n hn
        have h2wi : (2 : ℤ) ∣ w i := Int.natCast_dvd.mpr h2abs
        have hc₁odd : c₁ % 2 = 1 := by
          rcases hc₁ with ⟨u₁, hu₁, j₁, hj₁, huj₁, hg₁⟩
          exact odd_mod_of_coprime_even h2wi hg₁
        have hc₂odd : c₂ % 2 = 1 := by
          rcases hc₂ with ⟨u₂, hu₂, j₂, hj₂, huj₂, hg₂⟩
          exact odd_mod_of_coprime_even h2wi hg₂
        have hnc₁ : ¬ 2 ∣ c₁ := not_even_of_emod_two hc₁odd
        have hnc₂ : ¬ 2 ∣ c₂ := not_even_of_emod_two hc₂odd
        have h8₁ : c₁ % 8 = 5 := fam_copartner_odd_mod8 t w hw i hc₁ hnc₁
        have h8₂ : c₂ % 8 = 5 := fam_copartner_odd_mod8 t w hw i hc₂ hnc₂
        have hk₁ : kronTwo c₁ = -1 := kronTwo_neg_of_mod8_five h8₁
        have hk₂ : kronTwo c₂ = -1 := kronTwo_neg_of_mod8_five h8₂
        have hkt : kronTwo c₁ = kronTwo c₂ := by rw [hk₁, hk₂]
        have hd₁ : ksym c₁ n = ksym c₁ (n / 2) * kronTwo c₁ := ksym_double c₁ hne hn0
        have hd₂ : ksym c₂ n = ksym c₂ (n / 2) * kronTwo c₂ := ksym_double c₂ hne hn0
        have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num : 1 < 2)
        have hn2eq : n = (n / 2) * 2 := by
          calc
            n = 2 * (n / 2) := two_mul_div_two n hne
            _ = (n / 2) * 2 := Nat.mul_comm 2 (n / 2)
        have hdiv : n / 2 ∣ (w i).natAbs := dvd_trans ⟨2, hn2eq⟩ hn
        have ih_eq := ih (n / 2) hlt hdiv
        calc
          ksym c₁ n = ksym c₁ (n / 2) * kronTwo c₁ := hd₁
          _ = ksym c₂ (n / 2) * kronTwo c₂ := by rw [ih_eq, hkt]
          _ = ksym c₂ n := hd₂.symm

/-- full well-definedness (family). -/
theorem fam_wd (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4)
    (c₁ c₂ : ℤ) (hc₁ : RingCopartner w i c₁) (hc₂ : RingCopartner w i c₂) :
    ksym c₁ (w i).natAbs = ksym c₂ (w i).natAbs :=
  fam_wd_div t w hw i (w i).natAbs (dvd_refl (w i).natAbs) c₁ c₂ hc₁ hc₂

/-- χ₂ well-definedness in pairChi form (family). -/
theorem fam_pairChi_wd (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4)
    (c₁ c₂ : ℤ) (hc₁ : RingCopartner w i c₁) (hc₂ : RingCopartner w i c₂) :
    pairChi (w i) c₁ = pairChi (w i) c₂ := by
  unfold pairChi
  exact fam_wd t w hw i c₁ c₂ hc₁ hc₂

end Apollo
