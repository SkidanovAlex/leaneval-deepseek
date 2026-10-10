import Mathlib
import Submission.Work.MotAS.ASRulV2M.sat_mem_gen
import Submission.Work.MotC5N3.SatCert2.hB1hB3
import Submission.Work.MotC5N3.SatCert2.K1_z
import Submission.Work.MotC5N3.SatCert2.K3_z
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotAS.ASZGC.clause1_mem
import Submission.Work.MotAS.satGraphIsPrimeGen
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZSatCertAll` — the full `D₀`-saturation certificate of the AS residual chart

The five generator memberships of the AS residual chart ideal `ZIAS a b g` in the `D₀`-saturation
`SatAS a b g = sat_{D₀}((P̃, G))` of its graph model.

* `k = 0, 2, 4` are `Work.MotAS.ASRulV2M.zcubAS_mem_sat_0/2/4` (proved from the certificates
  `Work.MotC5N3.hB0/2/4` and the `X 0`-decompositions `Work.MotC5N3.zdec0/2/4`).
* `k = 1, 3` are proved here, exactly as the others, from the now-proved certificates
  `Work.MotC5N3.hB1/hB3` (`Submission/Work/MotC5N3/SatCert2/{K1_h,K3_h}.lean`) and the
  decompositions `Work.MotC5N3.zdec1/3` together with the degree-three geometric-series identity
  `Work.MotAS.ASRulV2M.geom3`.
* `ASZSatCert` is the whole-ideal form `∀ F ∈ ZIAS, ∃ N, D₀^N F ∈ (P̃, G)`, and
  `ASZSatCert_ASZGC` its `rename Fin.succ`-translation, which is the `hcert` input of
  `Work.MotC5N3.isPrime_radical_ZIAS_of_cert`.
* `isPrime_radical_ZIAS_of_Dmin` assembles primality of `√(ZIAS a b g)` from the saturation
  certificate and the **`D₀`-avoidance** `hDmin` (the remaining input, supplied by the
  `D₀`-regularity of the plane model).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.MotC5N3

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

/-- **The generator `zcubAS a b g 1` lies in the saturation.** -/
theorem zcubAS_mem_sat_1 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∃ N : ℕ, (X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 1
      ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have hB : N1 a b g - X2AuxInputs.Pemb a b g * S1 a b g
      = (5 : MvPolynomial (Fin 3) K) * C1 a b g := (SatCert2.hB1hB3 K a b g).1
  have h1 : N1 a b g ∈ Ideal.span {X2AuxInputs.Pemb a b g} := by
    rw [h5, zero_mul, sub_eq_zero] at hB
    rw [hB]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have h2 : (X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 1 - N1 a b g
      ∈ Ideal.span {X2AuxInputs.G a b g} := by
    rw [zdec1 a b g]
    refine Ideal.mem_span_singleton.mpr ⟨W1 a b g, ?_⟩
    simp only [N1, W1, X2AuxInputs.G]
    rw [Work.MotAS.ASRulV2M.geom3 (X2AuxInputs.D a b g) (X2AuxInputs.R a b g) (X 0)
      (f10 a b g) (f11 a b g) (f12 a b g) (f13 a b g)]
    first | refl_ring1 | ring
  have hle1 : Ideal.span {X2AuxInputs.Pemb a b g}
      ≤ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hle2 : Ideal.span {X2AuxInputs.G a b g}
      ≤ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨3, ?_⟩
  rw [show (X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 1
      = N1 a b g + ((X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 1 - N1 a b g)
      by ring]
  exact Ideal.add_mem _ (hle1 h1) (hle2 h2)

/-- **The generator `zcubAS a b g 3` lies in the saturation.** -/
theorem zcubAS_mem_sat_3 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∃ N : ℕ, (X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 3
      ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have hB : N3 a b g - X2AuxInputs.Pemb a b g * S3 a b g
      = (5 : MvPolynomial (Fin 3) K) * C3 a b g := (SatCert2.hB1hB3 K a b g).2
  have h1 : N3 a b g ∈ Ideal.span {X2AuxInputs.Pemb a b g} := by
    rw [h5, zero_mul, sub_eq_zero] at hB
    rw [hB]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have h2 : (X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 3 - N3 a b g
      ∈ Ideal.span {X2AuxInputs.G a b g} := by
    rw [zdec3 a b g]
    refine Ideal.mem_span_singleton.mpr ⟨W3 a b g, ?_⟩
    simp only [N3, W3, X2AuxInputs.G]
    rw [Work.MotAS.ASRulV2M.geom3 (X2AuxInputs.D a b g) (X2AuxInputs.R a b g) (X 0)
      (f30 a b g) (f31 a b g) (f32 a b g) (f33 a b g)]
    first | refl_ring1 | ring
  have hle1 : Ideal.span {X2AuxInputs.Pemb a b g}
      ≤ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hle2 : Ideal.span {X2AuxInputs.G a b g}
      ≤ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨3, ?_⟩
  rw [show (X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 3
      = N3 a b g + ((X2AuxInputs.D a b g) ^ 3 * Work.MotAS.zcubAS a b g 3 - N3 a b g)
      by ring]
  exact Ideal.add_mem _ (hle1 h1) (hle2 h2)

/-- **The whole-ideal `D₀`-saturation certificate** of the AS residual chart (in the `X2AuxInputs`
normalisation).  Every element of `ZIAS a b g` reaches the two-generator ideal
`(Pemb, G) = (P̃, D·X₀ + R)` after multiplication by a power of `D`. -/
theorem ASZSatCert (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∀ F ∈ Work.MotAS.ZIAS a b g, ∃ N : ℕ,
      (X2AuxInputs.D a b g) ^ N * F ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
  intro F hF
  rw [Work.MotAS.ZIAS] at hF
  refine Submodule.span_induction (p := fun F _ => ∃ N : ℕ,
      (X2AuxInputs.D a b g) ^ N * F ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g})
    ?_ ?_ ?_ ?_ hF
  · rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Work.MotAS.ASRulV2M.zcubAS_mem_sat_0 K a b g
    · exact zcubAS_mem_sat_1 K a b g
    · exact Work.MotAS.ASRulV2M.zcubAS_mem_sat_2 K a b g
    · exact zcubAS_mem_sat_3 K a b g
    · exact Work.MotAS.ASRulV2M.zcubAS_mem_sat_4 K a b g
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    have h1 : (X2AuxInputs.D a b g) ^ max N M * x
        ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
      have hp : (X2AuxInputs.D a b g) ^ max N M
          = (X2AuxInputs.D a b g) ^ (max N M - N) * (X2AuxInputs.D a b g) ^ N := by
        conv_lhs => rw [show max N M = N + (max N M - N) from
          (Nat.add_sub_of_le (le_max_left N M)).symm]
        rw [pow_add]
        exact mul_comm _ _
      rw [hp, mul_assoc]
      exact Ideal.mul_mem_left _ _ hN
    have h2 : (X2AuxInputs.D a b g) ^ max N M * y
        ∈ Ideal.span {X2AuxInputs.Pemb a b g, X2AuxInputs.G a b g} := by
      have hp : (X2AuxInputs.D a b g) ^ max N M
          = (X2AuxInputs.D a b g) ^ (max N M - M) * (X2AuxInputs.D a b g) ^ M := by
        conv_lhs => rw [show max N M = M + (max N M - M) from
          (Nat.add_sub_of_le (le_max_right N M)).symm]
        rw [pow_add]
        exact mul_comm _ _
      rw [hp, mul_assoc]
      exact Ideal.mul_mem_left _ _ hM
    rw [mul_add]
    exact Ideal.add_mem _ h1 h2
  · rintro c x _ ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [smul_eq_mul]
    have hcomm : (X2AuxInputs.D a b g) ^ N * (c * x)
        = c * ((X2AuxInputs.D a b g) ^ N * x) := by ring
    rw [hcomm]
    exact Ideal.mul_mem_left _ _ hN

/-- **The whole-ideal `D₀`-saturation certificate**, in the `ASZGC` normalisation used by
`Work.MotC5N3.isPrime_radical_ZIAS_of_cert`. -/
theorem ASZSatCert_ASZGC (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∀ F ∈ Work.MotAS.ZIAS a b g, ∃ N : ℕ,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N * F
        ∈ Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
            MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
                * MvPolynomial.X 0
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} := by
  intro F hF
  obtain ⟨N, hN⟩ := ASZSatCert K a b g F hF
  exact ⟨N, by
    simpa only [Work.ASZF.D_eq_renameD0, Work.ASZF.R_eq_renameR0, X2AuxInputs.G,
      X2AuxInputs.Pemb] using hN⟩

/-! ## Part 2: primality of `√ZIAS` from the saturation certificate and the `D₀`-avoidance -/

/-- **`√(ZIAS a b g)` is prime**, from the `D₀`-saturation certificate `hcert` and the
`D₀`-avoidance `hDmin` for the minimal primes.

The graph saturation `S := sat_{D₀}((P̃, G)) = {F | ∃N, D₀^N F ∈ (P̃, G)}` is prime
(`Work.MotAS.satGraphIsPrimeGen`: `P̃` irreducible, `D₀` not a multiple of `P̃`), and `Z ≤ S` is
exactly `hcert`; conversely `F ∈ S` means `D₀^N F ∈ (P̃, G) ⊆ Z`, so for `𝔭 ∈ Z.minimalPrimes` the
assumption `D₀ ∉ 𝔭` gives `F ∈ 𝔭`.  Hence `√Z = S` is prime. -/
theorem isPrime_radical_ZIAS_of_cert (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hcert : ∀ F ∈ Work.MotAS.ZIAS a b g, ∃ N : ℕ,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N * F ∈
        Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
          MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
            * MvPolynomial.X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)})
    (hDmin : ∀ 𝔭 ∈ (Work.MotAS.ZIAS a b g).minimalPrimes,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) :
        MvPolynomial (Fin 3) K) ∉ 𝔭) :
    (Ideal.radical (Work.MotAS.ZIAS a b g)).IsPrime := by
  set Z : Ideal (MvPolynomial (Fin 3) K) := Work.MotAS.ZIAS a b g with hZ
  set D' : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) with hD'
  set J : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
      D' * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} with hJ
  set S : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {F : MvPolynomial (Fin 3) K | ∃ N : ℕ, D' ^ N * F ∈ J} with hS
  have hSprime : S.IsPrime := by
    rw [hS, hJ, hD']
    exact Work.MotAS.satGraphIsPrimeGen (Work.MotAS.ASZElim.P a b g)
      (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZGC.R0 a b g)
      (Work.MotAS.ASZElimP_irreducible K a b g ha hg)
      (Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg)
  have hZS : Z ≤ S := by
    rw [hZ, Work.MotAS.ZIAS, hS]
    refine Ideal.span_le.mpr ?_
    rintro F ⟨k, rfl⟩
    exact Ideal.subset_span (by
      rw [hJ, hD']
      exact hcert _ (Ideal.subset_span (Set.mem_range_self k)))
  have hle : Ideal.radical Z ≤ S := hSprime.radical_le_iff.mpr hZS
  have hSle : S ≤ Ideal.radical Z := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf ?_
    intro 𝔭 h𝔭
    haveI hp : 𝔭.IsPrime := h𝔭.isPrime
    have hZ𝔭 : Z ≤ 𝔭 := h𝔭.le
    have hmemE : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
        ∈ Z := by rw [hZ]; exact Work.MotAS.ASZElimMem K a b g ha hg
    have hmemG : D' * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) ∈ Z := by
      rw [hZ, hD']; exact Work.MotAS.ASZGC.clause1_mem K a b g
    have hJ𝔭 : J ≤ 𝔭 := by
      rw [hJ]
      refine Ideal.span_le.mpr ?_
      rintro y (rfl | rfl)
      · exact hZ𝔭 hmemE
      · exact hZ𝔭 hmemG
    have hDp : D' ∉ 𝔭 := by
      rw [hZ, hD'] at hDmin
      exact hDmin 𝔭 h𝔭
    rw [hS]
    refine Ideal.span_le.mpr ?_
    rintro y ⟨N, hN⟩
    rcases hp.mem_or_mem (hJ𝔭 hN) with h | h
    · exact absurd (hp.mem_of_pow_mem N h) hDp
    · exact h
  rw [le_antisymm hle hSle]
  exact hSprime

/-- **Irreducibility of the AS residual curve from the `D₀`-avoidance.**  The saturation
certificate is supplied by `ASZSatCert_ASZGC`, so the only input is
`hDmin : ∀ 𝔭 ∈ ZIAS.minimalPrimes, D₀ ∉ 𝔭` (equivalently: the residual chart is its own
`D₀`-saturation, i.e. `D₀` is a non-zero-divisor modulo `ZIAS a b g`). -/
theorem isPrime_radical_ZIAS_of_Dmin (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hDmin : ∀ 𝔭 ∈ (Work.MotAS.ZIAS a b g).minimalPrimes,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        : MvPolynomial (Fin 3) K) ∉ 𝔭) :
    (Ideal.radical (Work.MotAS.ZIAS a b g)).IsPrime :=
  isPrime_radical_ZIAS_of_cert K a b g ha hg (ASZSatCert_ASZGC K a b g) hDmin

/-- **The `D₀`-regularity implies the `D₀`-avoidance**: an element of a minimal prime of an ideal is
a zero divisor modulo that ideal (`Ideal.exists_mul_mem_of_mem_minimalPrimes`), so a
non-zero-divisor lies in no minimal prime. -/
theorem Dmin_of_Dregular (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hreg : ∀ y : MvPolynomial (Fin 3) K,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
          : MvPolynomial (Fin 3) K) * y ∈ Work.MotAS.ZIAS a b g →
        y ∈ Work.MotAS.ZIAS a b g) :
    ∀ 𝔭 ∈ (Work.MotAS.ZIAS a b g).minimalPrimes,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        : MvPolynomial (Fin 3) K) ∉ 𝔭 := by
  intro 𝔭 h𝔭 hx
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes h𝔭 hx
  exact hy (hreg y hxy)

/-- **Irreducibility of the AS residual curve from the `D₀`-regularity.**  With the saturation
certificate `ASZSatCert_ASZGC` and the `D₀`-avoidance derived from `hreg`, this gives the primality
of `√(ZIAS a b g)`; combined with `Work.MotC5N3.ASZTwistDivPlaneGeom_three_of_isPrime` it closes the
K6 leaf. -/
theorem isPrime_radical_ZIAS_of_Dregular (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hreg : ∀ y : MvPolynomial (Fin 3) K,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
          : MvPolynomial (Fin 3) K) * y ∈ Work.MotAS.ZIAS a b g →
        y ∈ Work.MotAS.ZIAS a b g) :
    (Ideal.radical (Work.MotAS.ZIAS a b g)).IsPrime :=
  isPrime_radical_ZIAS_of_Dmin K a b g ha hg (Dmin_of_Dregular K a b g hreg)

end Work.MotC5N3
