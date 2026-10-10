import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotAS.ASZGC.clause1_mem
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotAS.ZiasGraphData
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.satGraphIsPrimeGen
import Submission.Work.MotAS.ASRulV2M.ZiasLeSpanPQG
import Submission.Work.MotAS.ASRulV2M.ASZQuadDetGen
import Submission.Work.MotAS.ASRulV2M.D0_regular_gen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

/-- `ziasGraphD0` agrees with `ASZGC.D0` in characteristic `5`. -/
theorem ziasGraphD0_eq (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ziasGraphD0 a b g = Work.MotAS.ASZGC.D0 a b g := by
  rw [Work.MotAS.ziasGraphD0, Work.MotAS.ASZGC.D0]
  haveI hchar : CharP (MvPolynomial (Fin 2) K) 5 := inferInstance
  simp only [map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0]
  reduce_mod_char!

/-- `ziasGraphR` agrees with `ASZGC.R0` in characteristic `5`. -/
theorem ziasGraphR_eq (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ziasGraphR a b g = Work.MotAS.ASZGC.R0 a b g := by
  rw [Work.MotAS.ziasGraphR, Work.MotAS.ASZGC.R0]
  haveI hchar : CharP (MvPolynomial (Fin 2) K) 5 := inferInstance
  simp only [map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0]
  reduce_mod_char!

/-- **The monic AS-quadratic of the residual chart.**  `aszQ a b g` is the monic-in-`X 0`
quadratic `X 0 ^ 2 + (β²)⁻¹·Lt·X 0 + (β²)⁻¹·At` obtained from the two-generator certificate
`aszQu_ident` (`β · zcubAS 2 + 2α · zcubAS 4 = β² X 0 ^ 2 + Lt · X 0 + At`), divided by the
non-zero scalar `β² = (2(a+2b)⁴)²`; it lies in `ZIAS a b g` (`aszDpQuad`, `DpQuadNoHab`). -/
noncomputable def aszQ (K : Type) [Field K] [CharP K 5] (a b g : K) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) ^ 2
    + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
        * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
      * MvPolynomial.X 0
    + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
        * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g)

/-- **The AS-quadratic reaches the graph ideal.**  `D₀² · Q ∈ (P, D₀·X₀ + R₀)`.  This is the
elimination identity `R₀² − (β²)⁻¹Lt·R₀D₀ + (β²)⁻¹At·D₀² ∈ (P)` (`ASZQuadDetGen`, transported from
the `ziasGraphD0`/`ziasGraphR` normalisation by `ziasGraphD0_eq`/`ziasGraphR_eq`) together with the
graph relation `D₀·X₀ ≡ −R₀`:
`D₀²Q = (D₀X₀+R₀)(D₀X₀−R₀) + (D₀·(β²)⁻¹Lt)·(D₀X₀+R₀) + (R₀² − (β²)⁻¹Lt·R₀D₀ + (β²)⁻¹At·D₀²)`. -/
theorem aszQ_mem_sat (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 2
        * aszQ K a b g ∈
      Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
        MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
            * MvPolynomial.X 0
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} := by
  set D : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) with hD
  set R : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) with hR
  set P' : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g) with hP'
  set l' : MvPolynomial (Fin 3) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
      * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g) with hl
  set A' : MvPolynomial (Fin 3) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
      * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g) with hA
  -- the determinant identity, transported from the `ziasGraph` to the `ASZGC` normalisation
  have hdet : R ^ 2 - l' * R * D + A' * D ^ 2 ∈ Ideal.span {P'} := by
    have h := Work.MotAS.ASRulV2M.ASZQuadDetGen K a b g ha hg
    have h2 := Ideal.mem_map_of_mem (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)) h
    rw [Ideal.map_span, Set.image_singleton] at h2
    have heq : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        ((Work.MotAS.ziasGraphR a b g) ^ 2
          - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
              * (Work.MotAS.ziasGraphR a b g) * (Work.MotAS.ziasGraphD0 a b g)
          + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
              * (Work.MotAS.ziasGraphD0 a b g) ^ 2)
        = R ^ 2 - l' * R * D + A' * D ^ 2 := by
      simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.rename_C, hD, hR, hl, hA]
      rw [ziasGraphD0_eq K a b g, ziasGraphR_eq K a b g]
    rwa [heq] at h2
  have hdet' : R ^ 2 - l' * R * D + A' * D ^ 2 ∈ Ideal.span {P', D * MvPolynomial.X 0 + R} :=
    (Ideal.span_mono (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_insert _ _)) hdet
  have hgraph : (D * MvPolynomial.X 0 + R) ∈ Ideal.span {P', D * MvPolynomial.X 0 + R} :=
    Ideal.subset_span (by simp)
  have hkey : D ^ 2 * aszQ K a b g
      = (D * MvPolynomial.X 0 + R) * (D * MvPolynomial.X 0 - R)
        + (D * l') * (D * MvPolynomial.X 0 + R)
        + (R ^ 2 - l' * R * D + A' * D ^ 2) := by
    simp only [aszQ, hl, hA]
    first | refl_ring1 | ring
  rw [hkey]
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ hgraph)
    (Ideal.mul_mem_left _ _ hgraph)) hdet'

/-- **The `D₀`-saturation certificate, in the whole-ideal form.**  Every element of the AS residual
ideal `ZIAS a b g` is carried into the two-generator ideal
`(rename P, rename D₀ · X₀ + rename R₀)` by some power of `rename D₀`, where `P = ASZElim.P a b g`
and `D₀`, `R₀` are the graph data of `ASZGC`.

This is assembled from the presentation `ZIAS a b g = (P, Q, D₀·X₀ + R₀)` with the monic
AS-quadratic `Q` (`Work.MotAS.ASRulV2M.ZiasLeSpanPQG`) and the elimination identity
`D₀²·Q ∈ (P, D₀·X₀ + R₀)` (`aszQ_mem_sat`).  It avoids the large CAS modules that obstruct the
alternative per-generator form `Work.MotC5N3.ASZPrimeness.ASZFCert`. -/
theorem aszSatCert (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ F ∈ Work.MotAS.ZIAS a b g, ∃ N : ℕ,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N * F ∈
        Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
          MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
            * MvPolynomial.X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} := by
  set J : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
      MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} with hJ
  intro F hF
  have hFP : F ∈ Ideal.span
      {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g),
        aszQ K a b g,
        MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
            * MvPolynomial.X 0
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)} :=
    Work.MotAS.ASRulV2M.ZiasLeSpanPQG K a b g ha hg hF
  -- the three generators reach `J` after a power of `D₀`
  have hP : ∃ N : ℕ, (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      (Work.MotAS.ASZGC.D0 a b g)) ^ N
      * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g) ∈ J :=
    ⟨0, by rw [pow_zero, one_mul]; exact Ideal.subset_span (by simp [hJ])⟩
  have hG : ∃ N : ℕ, (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      (Work.MotAS.ASZGC.D0 a b g)) ^ N
      * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
          * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) ∈ J :=
    ⟨0, by rw [pow_zero, one_mul]; exact Ideal.subset_span (by simp [hJ])⟩
  have hQ : ∃ N : ℕ, (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      (Work.MotAS.ASZGC.D0 a b g)) ^ N * aszQ K a b g ∈ J :=
    ⟨2, by rw [hJ]; exact aszQ_mem_sat K a b g ha hg⟩
  refine Submodule.span_induction (p := fun F _ => ∃ N : ℕ,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N * F ∈ J)
    ?_ ?_ ?_ ?_ hFP
  · rintro x (rfl | rfl | rfl)
    · exact hP
    · exact hQ
    · exact hG
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    have h1 : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        ^ max N M * x ∈ J := by
      have hp : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          ^ max N M
          = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
              ^ (max N M - N)
            * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N := by
        conv_lhs => rw [show max N M = N + (max N M - N) from
          (Nat.add_sub_of_le (le_max_left N M)).symm]
        rw [pow_add]
        exact mul_comm _ _
      rw [hp, mul_assoc]
      exact Ideal.mul_mem_left _ _ hN
    have h2 : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
        ^ max N M * y ∈ J := by
      have hp : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          ^ max N M
          = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
              ^ (max N M - M)
            * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ M := by
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
    have hcomm : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N
        * (c * x) = c * ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
            (Work.MotAS.ASZGC.D0 a b g)) ^ N * x) := by ring
    rw [hcomm]
    exact Ideal.mul_mem_left _ _ hN

/-- **An element of a minimal prime is a zero divisor.**  Contrapositive form of
`Ideal.exists_mul_mem_of_mem_minimalPrimes`. -/
private theorem notMem_minimalPrimes_of_mul_mem {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (hx : ∀ y : R, x * y ∈ I → y ∈ I) : ∀ 𝔭 ∈ I.minimalPrimes, x ∉ 𝔭 := by
  intro 𝔭 h𝔭 hx𝔭
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes h𝔭 hx𝔭
  exact hy (hx y hxy)

/-- **The `D₀`-avoidance input.**  The graph coefficient `D₀ = ASZGC.D0 a b g` of the AS residual
curve lies in no minimal prime of `ZIAS a b g`.  Together with the saturation certificate
`aszSatCert` this says that `ZIAS a b g` is its own `D₀`-saturation, i.e. that the residual curve is
exactly the graph of the plane model `V(P)`; then `√(ZIAS a b g) = Sat` is prime.

This is the standard route to the `D₀`-avoidance: an element of a minimal prime of `ZIAS` is a
zero divisor modulo `ZIAS`, so it suffices that `rename D₀` is a non-zero-divisor modulo `ZIAS`
(the node `Work.MotAS.ASRulV2M.D0_regular_gen`, equivalently `Work.MotAS.ZiasGraphSat`). -/
theorem aszDMin (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ 𝔭 ∈ (Work.MotAS.ZIAS a b g).minimalPrimes,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        : MvPolynomial (Fin 3) K) ∉ 𝔭 :=
  notMem_minimalPrimes_of_mul_mem (Work.MotAS.ZIAS a b g)
    (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
    (fun y hy => Work.MotAS.ASRulV2M.D0_regular_gen K a b g ha hg y hy)

/-- **The assembly of the AS plane-model route, generic in `(K,a,b,g)`.**  Given the explicit
plane-model data `E`, `D₀`, `R` for `Z = ZIAS a b g` — witnesses `E`, `D₀ · X₀ + R` in `Z`,
irreducibility of `E`, `¬ E ∣ D₀`, the `D₀`-saturation certificate `Z ≤ S`, and `rename D₀`
avoiding the minimal primes of `Z` — the radical of `Z` is prime. -/
theorem isPrime_radical_zias_of_certificates {K : Type} [Field K] [CharP K 5] (a b g : K)
    (E D₀ R : MvPolynomial (Fin 2) K) (hE : Irreducible E) (hD₀ : ¬ E ∣ D₀)
    (hmemE : rename Fin.succ E ∈ Work.MotAS.ZIAS a b g)
    (hmemG : rename Fin.succ D₀ * X 0 + rename Fin.succ R ∈ Work.MotAS.ZIAS a b g)
    (hcert : ∀ F ∈ Work.MotAS.ZIAS a b g,
      ∃ N : ℕ, (rename Fin.succ D₀) ^ N * F ∈
        Ideal.span {rename Fin.succ E, rename Fin.succ D₀ * X 0 + rename Fin.succ R})
    (hDmin : ∀ 𝔭 ∈ (Work.MotAS.ZIAS a b g).minimalPrimes,
      (rename Fin.succ D₀ : MvPolynomial (Fin 3) K) ∉ 𝔭) :
    (Ideal.radical (Work.MotAS.ZIAS a b g)).IsPrime := by
  set Z : Ideal (MvPolynomial (Fin 3) K) := Work.MotAS.ZIAS a b g with hZ
  set D' : MvPolynomial (Fin 3) K := rename Fin.succ D₀ with hD'
  set J : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {rename Fin.succ E, D' * X 0 + rename Fin.succ R} with hJ
  set S : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {F : MvPolynomial (Fin 3) K | ∃ N : ℕ, D' ^ N * F ∈ J} with hS
  have hSprime : S.IsPrime := by
    rw [hS, hJ]
    exact Work.MotAS.satGraphIsPrimeGen E D₀ R hE hD₀
  have hZS : Z ≤ S := by
    rw [hZ, hS]
    refine Ideal.span_le.mpr ?_
    rintro F ⟨k, rfl⟩
    exact Ideal.subset_span (hcert _ (Ideal.subset_span (Set.mem_range_self k)))
  have hle : Ideal.radical Z ≤ S := hSprime.radical_le_iff.mpr hZS
  have hSle : S ≤ Ideal.radical Z := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf ?_
    intro 𝔭 h𝔭
    haveI hp : 𝔭.IsPrime := Ideal.IsMinimalPrime.isPrime h𝔭
    have hZ𝔭 : Z ≤ 𝔭 := Ideal.IsMinimalPrime.le h𝔭
    have hJ𝔭 : J ≤ 𝔭 := by
      rw [hJ]
      refine Ideal.span_le.mpr ?_
      rintro F (rfl | rfl)
      · exact hZ𝔭 hmemE
      · exact hZ𝔭 hmemG
    have hDp : D' ∉ 𝔭 := hDmin 𝔭 h𝔭
    rw [hS]
    refine Ideal.span_le.mpr ?_
    rintro F ⟨N, hN⟩
    rcases hp.mem_or_mem (hJ𝔭 hN) with h | h
    · exact absurd (hp.mem_of_pow_mem N h) hDp
    · exact h
  rw [le_antisymm hle hSle]
  exact hSprime

/-- **Irreducibility of the AS residual curve.**  For `K` a field of characteristic `5` and
`a b g : K` with `a² - ab - b² ≠ 0` and `g` not an Artin–Schreier value, the residual ideal
`ZIAS a b g` (the five cubics `kleinRAS a b g` at the chart vector `(1, X₀, X₁, X₂, 0)`) has prime
radical, i.e. `K[X₀,X₁,X₂] ⧸ √(ZIAS a b g)` is a domain.

All ingredients are in the workspace and are axiom-clean: `Work.MotAS.ASZElimP_irreducible`
(`E := ASZElim.P a b g` irreducible), `Work.MotAS.ASZElimMem` (`rename Fin.succ E ∈ ZIAS a b g`),
`Work.MotAS.ASZGC.clause1_mem` (`G := rename D₀ * X 0 + rename R₀ ∈ ZIAS a b g`),
`Work.MotAS.ASZGC.not_dvd_D0` (`¬ E ∣ D₀`, giving `rename E ∤ G` by the `X 0`-coefficient via
`MvPolynomial.finSuccEquiv K 2`), and `Work.MotAS.satGraphIsPrimeGen E D₀ R₀`
(the `D₀`-saturation `Sat` of `(rename E, G)` is prime).  What remains is to supply cleanly the
missing inputs of the existing route: `ZIAS ⊆ Sat` (the `D₀`-saturation certificate, a finite
`ring` identity — currently `Work.MotAS.ASZF.ASZFCert`, a `sorry`) and `Sat ⊆ √(ZIAS)` (the
`D₀`-avoidance for the minimal primes of `ZIAS` — cf. `Work.MotAS.ASZFFin`, `ASZFHeight`,
`Work.MotAS.notMem_minimalPrimes_of_quotient_finite`); then `√(ZIAS) = Sat` is prime.  Candidate
clean sources for those two inputs are `Work.MotAS.ASRulV2M.satIdentGen` (per-generator saturation
identities, assembled from `Submission/Work/MotC5N3/SatCert/K{k}_*`),
`Work.MotAS.ASRulV2M.DnotMemMinimalPrimes`, and `Work.MotV5.Contrib.le_two_height_radical_ZIAS`.
The statement is exactly `Work.MotC5N3.ASZRingIsDomainGen` in the `(a,b,g)` form. -/
theorem ASZRadicalIsPrime (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    IsDomain (MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotAS.ZIAS a b g)) := by
  haveI : (Ideal.radical (Work.MotAS.ZIAS a b g)).IsPrime :=
    isPrime_radical_zias_of_certificates (K := K) a b g (Work.MotAS.ASZElim.P a b g)
      (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZGC.R0 a b g)
      (Work.MotAS.ASZElimP_irreducible K a b g ha hg)
      (Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg) (Work.MotAS.ASZElimMem K a b g ha hg)
      (Work.MotAS.ASZGC.clause1_mem K a b g) (aszSatCert K a b g ha hg) (aszDMin K a b g ha hg)
  exact Ideal.Quotient.isDomain _

end Work.MotC5N3
