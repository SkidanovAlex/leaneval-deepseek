import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open scoped _root_.NumberField

/-- If `2 ∈ I` and `1 ∉ I` for an ideal `I ⊆ ℤ`, then the equation `c * (c + 1) = 1`
has no solution in `ℤ ⧸ I`. -/
private lemma no_root_mul_add_one {I : Ideal ℤ} (h2 : (2:ℤ) ∈ I) (h1 : (1:ℤ) ∉ I) :
    ∀ c : ℤ ⧸ I, c * (c + 1) ≠ 1 := by
  intro c
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective c
  intro h
  have hmem : n * (n + 1) - 1 ∈ I := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    show Ideal.Quotient.mk _ (n * (n + 1)) = Ideal.Quotient.mk _ 1
    simp only [map_mul, map_add, map_one]
    exact h
  have hnn : n * (n + 1) ∈ I := by
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    have : n * (n + 1) = 2 * k := by rw [hk]; ring
    rw [this]
    exact Ideal.mul_mem_right k _ h2
  exact h1 (by simpa using Ideal.sub_mem _ hnn hmem)

/-- Integrality of `(u + 1) / 2` when `u ^ 2 = D` with `D ≡ 1 (mod 4)`. -/
private lemma isIntegral_add_one_div_two {K : Type*} [Field K] [CharZero K]
    (u : K) (D m : ℤ) (hu : u ^ 2 = (D : K)) (hm : D = 1 + 4 * m) :
    IsIntegral ℤ ((u + 1) / 2) := by
  have h2 : (2:K) ≠ 0 := by norm_num
  have hx : (2:K) * ((u + 1) / 2) = u + 1 := by rw [mul_div_cancel₀ _ h2]
  have hux : u = 2 * ((u + 1) / 2) - 1 := by
    rw [eq_sub_iff_add_eq]; exact hx.symm
  have hsq : ((2:K) * ((u + 1) / 2) - 1)^2 = (D:K) := by rw [← hux]; exact hu
  have hrel : 4 * (((u + 1) / 2)^2 - ((u + 1) / 2)) = (D:K) - 1 := by
    have h1 : ((2:K) * ((u + 1) / 2) - 1)^2 =
        4*((u+1)/2)^2 - 4*((u+1)/2) + 1 := by ring
    rw [h1] at hsq
    linear_combination hsq
  have hmK : (D : K) = 1 + 4 * (m : K) := by rw [hm]; push_cast; ring
  have hrel2 : 4 * (((u + 1) / 2)^2 - ((u + 1) / 2)) = 4 * (m:K) := by
    rw [hrel, hmK]; ring
  have hfin : ((u + 1) / 2)^2 - ((u + 1) / 2) = (m:K) :=
    mul_left_cancel₀ (by norm_num : (4:K) ≠ 0) hrel2
  have hmonic : (Polynomial.X^2 - Polynomial.X - Polynomial.C m : Polynomial ℤ).Monic := by
    have hdeg : (Polynomial.X + Polynomial.C m : Polynomial ℤ).degree < (2:WithBot ℕ) := by
      rw [Polynomial.degree_X_add_C]; norm_num
    have h := Polynomial.monic_X_pow_sub
      (p := (Polynomial.X + Polynomial.C m : Polynomial ℤ)) hdeg
    have hpoly : (Polynomial.X^2 - (Polynomial.X + Polynomial.C m) : Polynomial ℤ)
        = Polynomial.X^2 - Polynomial.X - Polynomial.C m := by ring
    rw [hpoly] at h
    exact h
  have haev : Polynomial.aeval ((u + 1) / 2)
      (Polynomial.X^2 - Polynomial.X - Polynomial.C m) = 0 := by
    rw [Polynomial.aeval_def]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    rw [hfin]; simp
  refine ⟨Polynomial.X^2 - Polynomial.X - Polynomial.C m, hmonic, ?_⟩
  rw [← Polynomial.aeval_def]
  exact haev

theorem no_inertiaDeg_one_two_of_mod {K : Type*} [Field K] [NumberField K]
    (u : NumberField.RingOfIntegers K) (D : ℤ)
    (hu : ((u : K)) ^ 2 = algebraMap ℚ K (D : ℚ)) (hgen : Algebra.adjoin ℚ ({(u : K)} : Set K) = ⊤)
    (h4 : D % 4 = 1) (h8 : D % 8 = 5) :
    ∀ 𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(2 : ℤ)}) (NumberField.RingOfIntegers K),
      𝔭.inertiaDeg ℤ ≠ 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, D - 1 = 4 * m := (by omega : (4:ℤ) ∣ (D - 1))
  have hmD : D = 1 + 4 * m := by omega
  have hmodd : (2 : ℤ) ∣ (m - 1) := by omega
  have huK : ((u : K)) ^ 2 = (D : K) := by simpa using hu
  have hxint : IsIntegral ℤ (((u : K) + 1) / 2) :=
    isIntegral_add_one_div_two (u : K) D m huK hmD
  let b : 𝓞 K := ⟨((u : K) + 1) / 2, hxint⟩
  let a : 𝓞 K := b - 1
  have hb_coe : (b : K) = ((u : K) + 1) / 2 := rfl
  have ha_coe : (a : K) = ((u : K) + 1) / 2 - 1 := by
    simp only [a, b]; rfl
  have hfin_K : ((b : K)) ^ 2 - (b : K) = (m : K) := by
    have hfin : (((u : K) + 1) / 2)^2 - (((u : K) + 1) / 2) = (m : K) := by
      have h2 : (2:K) ≠ 0 := by norm_num
      have hx : (2:K) * (((u : K) + 1) / 2) = (u : K) + 1 := by
        rw [mul_div_cancel₀ _ h2]
      have hux : (u : K) = 2 * (((u : K) + 1) / 2) - 1 := by
        rw [eq_sub_iff_add_eq]; exact hx.symm
      have hsq : ((2:K) * (((u : K) + 1) / 2) - 1)^2 = (D:K) := by rw [← hux]; exact huK
      have hrel : 4 * ((((u : K) + 1) / 2)^2 - (((u : K) + 1) / 2)) = (D:K) - 1 := by
        have h1 : ((2:K) * (((u : K) + 1) / 2) - 1)^2 =
            4*(((u : K)+1)/2)^2 - 4*(((u : K)+1)/2) + 1 := by ring
        rw [h1] at hsq
        linear_combination hsq
      have hmK : (D : K) = 1 + 4 * (m : K) := by rw [hmD]; push_cast; ring
      have hrel2 : 4 * ((((u : K) + 1) / 2)^2 - (((u : K) + 1) / 2)) = 4 * (m:K) := by
        rw [hrel, hmK]; ring
      exact mul_left_cancel₀ (by norm_num : (4:K) ≠ 0) hrel2
    rw [hb_coe]; exact hfin
  have hab : a * b = (m : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    show ((a:K)) * ((b:K)) = (m:K)
    rw [← hfin_K, hb_coe, ha_coe]
    ring
  have hba : b = a + 1 := by
    simp only [a]; abel
  intro 𝔭 h𝔭 hf
  haveI h2max : (Ideal.span ({(2:ℤ)} : Set ℤ)).IsMaximal := by
    apply Ideal.IsPrime.isMaximal
    · exact (Ideal.span_singleton_prime (by norm_num : (2:ℤ) ≠ 0)).mpr Int.prime_two
    · intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact two_ne_zero h
  have h𝔭mem : 𝔭 ∈ (Ideal.span ({(2:ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (by
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact two_ne_zero h : (Ideal.span ({(2:ℤ)} : Set ℤ)) ≠ ⊥)
      (𝓞 K)).mp h𝔭
  have h𝔭prime : 𝔭.IsPrime := h𝔭mem.1
  have h𝔭lies : 𝔭.LiesOver (Ideal.span ({(2:ℤ)} : Set ℤ)) := h𝔭mem.2
  have h2mem : (2 : 𝓞 K) ∈ 𝔭 := by
    have h := (Ideal.mem_of_liesOver 𝔭 (Ideal.span ({(2:ℤ)} : Set ℤ)) (2 : ℤ)).mp
      (Ideal.subset_span (by simp))
    simpa using h
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    rw [hbot] at h2mem
    have h2z : (2 : 𝓞 K) = 0 := by simpa using h2mem
    exact (by norm_num : (2 : 𝓞 K) ≠ 0) h2z
  haveI : 𝔭.IsMaximal := h𝔭prime.isMaximal h𝔭ne
  -- Work over the residue field `ℤ ⧸ 𝔭.under ℤ`.
  have h2memI : (2:ℤ) ∈ 𝔭.under ℤ := by
    rw [Ideal.mem_under]; simpa using h2mem
  have h1memI : (1:ℤ) ∉ 𝔭.under ℤ := by
    intro h
    rw [Ideal.mem_under] at h
    refine h𝔭prime.ne_top ?_
    rw [Ideal.eq_top_iff_one]
    simpa using h
  haveI : (𝔭.under ℤ).IsMaximal :=
    (inferInstance : (𝔭.under ℤ).IsPrime).isMaximal (fun h => by
      rw [h] at h2memI; simp at h2memI)
  letI : Field (ℤ ⧸ 𝔭.under ℤ) := Ideal.Quotient.field _
  have hf' : Module.finrank (ℤ ⧸ 𝔭.under ℤ) (𝓞 K ⧸ 𝔭) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal (𝔭.under ℤ) 𝔭, hf]
  haveI : Module.Free (ℤ ⧸ 𝔭.under ℤ) (𝓞 K ⧸ 𝔭) :=
    Module.Free.of_divisionRing (ℤ ⧸ 𝔭.under ℤ) (𝓞 K ⧸ 𝔭)
  have hbij : Function.Bijective (algebraMap (ℤ ⧸ 𝔭.under ℤ) (𝓞 K ⧸ 𝔭)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hf'
  have hmk : Ideal.Quotient.mk 𝔭 (m : 𝓞 K) = 1 := by
    obtain ⟨k, hk⟩ := hmodd
    have hmk_int : m = 2 * k + 1 := by omega
    have hcast : (m : 𝓞 K) = 2 * (k : 𝓞 K) + 1 := by rw [hmk_int]; push_cast; ring
    rw [hcast, map_add, map_mul, map_one]
    have h2q : Ideal.Quotient.mk 𝔭 (2 : 𝓞 K) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h2mem
    rw [h2q, zero_mul, zero_add]
  have hab' : Ideal.Quotient.mk 𝔭 a * Ideal.Quotient.mk 𝔭 b = 1 := by
    rw [← map_mul, hab, hmk]
  have hb' : Ideal.Quotient.mk 𝔭 b = Ideal.Quotient.mk 𝔭 a + 1 := by
    rw [hba, map_add, map_one]
  have hroot : Ideal.Quotient.mk 𝔭 a * (Ideal.Quotient.mk 𝔭 a + 1) = 1 := by
    rw [← hb']; exact hab'
  obtain ⟨c, hc⟩ := hbij.surjective (Ideal.Quotient.mk 𝔭 a)
  have hc' : c * (c + 1) = 1 := by
    apply hbij.injective
    rw [map_mul, map_add, map_one, hc]
    exact hroot
  exact no_root_mul_add_one h2memI h1memI c hc'

end Commons.NumberTheory.NumberField