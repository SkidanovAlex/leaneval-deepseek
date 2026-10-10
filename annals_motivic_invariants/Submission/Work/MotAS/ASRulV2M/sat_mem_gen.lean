import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotC5N3.X2AuxInputs
import Submission.Work.MotC5N3.SatCert.K0_z
import Submission.Work.MotC5N3.SatCert.K0_h
import Submission.Work.MotC5N3.SatCert.K2_z
import Submission.Work.MotC5N3.SatCert.K2_h
import Submission.Work.MotC5N3.SatCert.K4_z
import Submission.Work.MotC5N3.SatCert.K4_h
import Submission.Work.ASZF.SPrimeGen
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.satGraphComapGen
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotAS.ASZGC.clause1_mem
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.Reflect.PolyId

/-!
# `Work.MotAS.ASRulV2M.sat_mem_gen`

The saturation / elimination machinery for `Work.MotAS.ASRulV2M.D0_regular_gen`.

* `SatAS` — the saturation `sat_{D₀}((P̃, G))` of the AS residual chart data.
* `zcubAS_mem_sat_0/2/4` — the generators `k = 0, 2, 4` lie in it, from the CAS certificates
  `Work.MotC5N3.zdec<k>` (the `X 0`-decomposition of `zcubAS a b g k`) and `Work.MotC5N3.hB<k>`
  (`N<k> - P̃ · S<k> = 5 · C<k>`, i.e. `N<k> ∈ (P̃)` in characteristic `5`), plus the
  geometric-series identity `geom2`.
* `zias_le_sat_of` — the assembly, given all five generators in `SatAS`.
* `aszElim_dvd_of_le_sat` — the elimination `Z ∩ K[X₁,X₂] = (P)` via `satGraphComapGen`.
* `aszQuad_mem`, `det_identity_of` — the AS quadratic `e = X 0^2 + l X 0 + A` lies in `Z` and the
  determinant identity `R₀² - l R₀ D₀ + A D₀² ∈ (P)`.

The two remaining generators (`k = 1, 3`) are *not* reachable through the files
`MotC5N3/SatCert/K1_h`, `K3_h`: `K1_C2` exceeds the heartbeat guard and the `K3_C*` chunks take
~20 minutes each.  They are reached instead through the `ASZGC` normalisation: the delegated
`Work.MotAS.ASRulV2M.Nn_dvd_gen` (`P ∣ Nn<k>`) plus the characteristic-`5` decomposition
`zcubAS a b g k = Σ_j rename (fk<k>_<j>) * X 0^j` (`ASZGC.SmallCorrId` is *broken*: keep its
statement in mind but reprove it) and the identity `geom3`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- The saturation ideal `sat_{D₀}((P̃, G))` of the AS residual chart data. -/
noncomputable def SatAS (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span {F : MvPolynomial (Fin 3) K | ∃ N : ℕ,
    (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * F ∈
      Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g}}

/-- The geometric-series identity for a degree-two polynomial. -/
lemma geom2 {A : Type*} [CommRing A] (d rr x f0 f1 f2 : A) :
    d ^ 2 * (f0 + f1 * x + f2 * x ^ 2)
      = (f0 * d ^ 2 + f1 * d * (-rr) + f2 * (-rr) ^ 2)
        + (f1 * d + f2 * (d * x + (-rr))) * (d * x + rr) := by
  first | refl_ring1 | ring

/-- The geometric-series identity for a degree-three polynomial. -/
lemma geom3 {A : Type*} [CommRing A] (d rr x f0 f1 f2 f3 : A) :
    d ^ 3 * (f0 + f1 * x + f2 * x ^ 2 + f3 * x ^ 3)
      = (f0 * d ^ 3 + f1 * d ^ 2 * (-rr) + f2 * d * (-rr) ^ 2 + f3 * (-rr) ^ 3)
        + (f1 * d ^ 2 + f2 * d * (d * x + (-rr))
            + f3 * ((d * x) ^ 2 + (d * x) * (-rr) + (-rr) ^ 2)) * (d * x + rr) := by
  first | refl_ring1 | ring

/-- **The generator `zcubAS a b g 0` lies in the saturation.** -/
theorem zcubAS_mem_sat_0 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 0
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have h1 : Work.MotC5N3.N0 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g} := by
    have h := Work.MotC5N3.hB0 a b g
    rw [h5, zero_mul, sub_eq_zero] at h
    rw [h]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have h2 : (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 0
      - Work.MotC5N3.N0 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g} := by
    rw [Work.MotC5N3.zdec0 a b g]
    refine Ideal.mem_span_singleton.mpr ⟨Work.MotC5N3.f01 a b g * Work.MotC5N3.X2AuxInputs.D a b g
      + Work.MotC5N3.f02 a b g * ((Work.MotC5N3.X2AuxInputs.D a b g) * X 0
          + (-(Work.MotC5N3.X2AuxInputs.R a b g))), ?_⟩
    simp only [Work.MotC5N3.N0, Work.MotC5N3.X2AuxInputs.G]
    rw [geom2 (Work.MotC5N3.X2AuxInputs.D a b g) (Work.MotC5N3.X2AuxInputs.R a b g) (X 0)
      (Work.MotC5N3.f00 a b g) (Work.MotC5N3.f01 a b g) (Work.MotC5N3.f02 a b g)]
    first | refl_ring1 | ring
  have hle1 : Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hle2 : Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨2, ?_⟩
  rw [show (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 0
      = Work.MotC5N3.N0 a b g + ((Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 0
        - Work.MotC5N3.N0 a b g) by ring]
  exact Ideal.add_mem _ (hle1 h1) (hle2 h2)

/-- **The generator `zcubAS a b g 2` lies in the saturation.** -/
theorem zcubAS_mem_sat_2 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 2
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have h1 : Work.MotC5N3.N2 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g} := by
    have h := Work.MotC5N3.hB2 a b g
    rw [h5, zero_mul, sub_eq_zero] at h
    rw [h]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have h2 : (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 2
      - Work.MotC5N3.N2 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g} := by
    rw [Work.MotC5N3.zdec2 a b g]
    refine Ideal.mem_span_singleton.mpr ⟨Work.MotC5N3.f21 a b g * Work.MotC5N3.X2AuxInputs.D a b g
      + Work.MotC5N3.f22 a b g * ((Work.MotC5N3.X2AuxInputs.D a b g) * X 0
          + (-(Work.MotC5N3.X2AuxInputs.R a b g))), ?_⟩
    simp only [Work.MotC5N3.N2, Work.MotC5N3.X2AuxInputs.G]
    rw [geom2 (Work.MotC5N3.X2AuxInputs.D a b g) (Work.MotC5N3.X2AuxInputs.R a b g) (X 0)
      (Work.MotC5N3.f20 a b g) (Work.MotC5N3.f21 a b g) (Work.MotC5N3.f22 a b g)]
    first | refl_ring1 | ring
  have hle1 : Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hle2 : Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨2, ?_⟩
  rw [show (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 2
      = Work.MotC5N3.N2 a b g + ((Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 2
        - Work.MotC5N3.N2 a b g) by ring]
  exact Ideal.add_mem _ (hle1 h1) (hle2 h2)

/-- **The generator `zcubAS a b g 4` lies in the saturation.** -/
theorem zcubAS_mem_sat_4 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 4
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have h1 : Work.MotC5N3.N4 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g} := by
    have h := Work.MotC5N3.hB4 a b g
    rw [h5, zero_mul, sub_eq_zero] at h
    rw [h]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have h2 : (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 4
      - Work.MotC5N3.N4 a b g ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g} := by
    rw [Work.MotC5N3.zdec4 a b g]
    refine Ideal.mem_span_singleton.mpr ⟨Work.MotC5N3.f41 a b g * Work.MotC5N3.X2AuxInputs.D a b g
      + Work.MotC5N3.f42 a b g * ((Work.MotC5N3.X2AuxInputs.D a b g) * X 0
          + (-(Work.MotC5N3.X2AuxInputs.R a b g))), ?_⟩
    simp only [Work.MotC5N3.N4, Work.MotC5N3.X2AuxInputs.G]
    rw [geom2 (Work.MotC5N3.X2AuxInputs.D a b g) (Work.MotC5N3.X2AuxInputs.R a b g) (X 0)
      (Work.MotC5N3.f40 a b g) (Work.MotC5N3.f41 a b g) (Work.MotC5N3.f42 a b g)]
    first | refl_ring1 | ring
  have hle1 : Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert _ _
  have hle2 : Ideal.span {Work.MotC5N3.X2AuxInputs.G a b g}
      ≤ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
    refine Ideal.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_insert_of_mem _ rfl
  refine ⟨2, ?_⟩
  rw [show (Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 4
      = Work.MotC5N3.N4 a b g + ((Work.MotC5N3.X2AuxInputs.D a b g) ^ 2 * Work.MotAS.zcubAS a b g 4
        - Work.MotC5N3.N4 a b g) by ring]
  exact Ideal.add_mem _ (hle1 h1) (hle2 h2)

/-- **The chart ideal is contained in the saturation**, given all five generators. -/
theorem zias_le_sat_of (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hgen : ∀ k : Fin 5, Work.MotAS.zcubAS a b g k ∈ SatAS K a b g) :
    Work.MotAS.ZIAS a b g ≤ SatAS K a b g := by
  rw [Work.MotAS.ZIAS]
  refine Ideal.span_le.mpr ?_
  rintro x ⟨k, rfl⟩
  exact hgen k

/-- **The elimination ideal of the AS residual chart.**  Every two-variable polynomial whose
`Fin.succ`-extension lies in `ZIAS a b g` is divisible by the eliminant `P`. -/
theorem aszElim_dvd_of_le_sat (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hZS : Work.MotAS.ZIAS a b g ≤ SatAS K a b g)
    (f : MvPolynomial (Fin 2) K)
    (hf : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) f ∈ Work.MotAS.ZIAS a b g) :
    Work.MotAS.ASZElim.P a b g ∣ f := by
  have hmem : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) f ∈ SatAS K a b g := hZS hf
  rw [SatAS] at hmem
  have h2 : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) f ∈
      Ideal.span {F : MvPolynomial (Fin 3) K | ∃ N : ℕ,
        (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ N * F ∈
          Ideal.span (insert (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g))
            (singleton (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
              * MvPolynomial.X 0
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g))))} := by
    simpa only [Work.ASZF.D_eq_renameD0, Work.ASZF.R_eq_renameR0, Work.MotC5N3.X2AuxInputs.G,
      Work.MotC5N3.X2AuxInputs.Pemb] using hmem
  exact (Work.MotAS.satGraphComapGen (K := K) (Work.MotAS.ASZElim.P a b g)
    (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZGC.R0 a b g)
    (Work.MotAS.ASZElimP_irreducible K a b g ha hg)
    (Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg) f).mp h2

/-- The graph element of the AS residual chart lies in `ZIAS a b g`. -/
theorem D0_graph_mem (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
    ∈ Work.MotAS.ZIAS a b g :=
  Work.MotAS.ASZGC.clause1_mem K a b g

/-- The graph element in the `X2AuxInputs` normalisation. -/
theorem D0_graph_mem' (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotC5N3.X2AuxInputs.G a b g ∈ Work.MotAS.ZIAS a b g := by
  rw [Work.MotC5N3.X2AuxInputs.G, Work.ASZF.D_eq_renameD0, Work.ASZF.R_eq_renameR0]
  exact D0_graph_mem K a b g

/-- **The AS quadratic lies in the chart ideal**: `e = X 0 ^ 2 + l·X 0 + A` with
`l = C (β²)⁻¹ · aszQuLt`, `A = C (β²)⁻¹ · aszQuAt`, monic in `X 0`. -/
theorem aszQuad_mem (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) :
    MvPolynomial.X 0 ^ 2
      + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g))
        * MvPolynomial.X 0
      + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g)
    ∈ Work.MotAS.ZIAS a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have hfac : a ^ 2 - a * b - b ^ 2 = (a + 2 * b) * (a - 3 * b) + 5 * b ^ 2 := by ring
    rw [h, zero_mul, zero_add] at hfac
    rw [hfac, h5, zero_mul]
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h32 : (3 : K) * 2 = 1 := by
      have h : (3 : K) * 2 - 1 = (5 : K) * 1 := by ring
      rwa [h5, mul_one, sub_eq_zero] at h
    rw [h2, mul_zero] at h32
    exact one_ne_zero h32.symm
  have hbeta : Work.MotAS.aszQuBeta a b ≠ 0 := by
    rw [Work.MotAS.aszQuBeta_eq a b]
    exact mul_ne_zero h2ne (pow_ne_zero 4 h2b)
  have hG : MvPolynomial.C (Work.MotAS.aszQuBeta a b) * Work.MotAS.zcubAS a b g 2
      + MvPolynomial.C (2 * Work.MotAS.aszQuAlpha a b) * Work.MotAS.zcubAS a b g 4
      ∈ Work.MotAS.ZIAS a b g :=
    Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨2, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))
  have hident := Work.MotAS.aszQu_ident (K := K) a b g
  have hc : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
      * MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2) = (1 : MvPolynomial (Fin 3) K) := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 hbeta), map_one]
  have key : MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
        * (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2) * (X 0 : MvPolynomial (Fin 3) K) ^ 2
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g) * X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g))
      = MvPolynomial.X 0 ^ 2
        + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g)) * X 0
        + MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g) := by
    rw [mul_add, mul_add, ← mul_assoc (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹)
      (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)) ((X 0 : MvPolynomial (Fin 3) K) ^ 2), hc,
      one_mul]
    first | refl_ring1 | ring
  rw [← key, ← hident]
  exact Ideal.mul_mem_left _ _ hG

/-- **The determinant identity**: `R₀² - l R₀ D₀ + A D₀² ∈ (P)` for the AS quadratic
`l = C (β²)⁻¹ aszQuLt`, `A = C (β²)⁻¹ aszQuAt`. -/
theorem det_identity_of (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hZS : Work.MotAS.ZIAS a b g ≤ SatAS K a b g) :
    Work.MotAS.ASZElim.P a b g ∣
      (Work.MotAS.ASZGC.R0 a b g) ^ 2
        - (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g)
            * Work.MotAS.ASZGC.R0 a b g * Work.MotAS.ASZGC.D0 a b g
        + (MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g)
            * (Work.MotAS.ASZGC.D0 a b g) ^ 2 := by
  set l : MvPolynomial (Fin 2) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g with hl
  set A : MvPolynomial (Fin 2) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g with hA
  have hmem : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      ((Work.MotAS.ASZGC.R0 a b g) ^ 2
        - l * Work.MotAS.ASZGC.R0 a b g * Work.MotAS.ASZGC.D0 a b g
        + A * (Work.MotAS.ASZGC.D0 a b g) ^ 2) ∈ Work.MotAS.ZIAS a b g := by
    have hl' : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l
        = MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g) := by
      rw [hl, map_mul, MvPolynomial.rename_C]
    have hA' : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A
        = MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g) := by
      rw [hA, map_mul, MvPolynomial.rename_C]
    have hQ : MvPolynomial.X 0 ^ 2
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A ∈ Work.MotAS.ZIAS a b g := by
      rw [hl', hA']
      exact aszQuad_mem K a b g ha
    have hG := D0_graph_mem K a b g
    have key : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        ((Work.MotAS.ASZGC.R0 a b g) ^ 2
          - l * Work.MotAS.ASZGC.R0 a b g * Work.MotAS.ASZGC.D0 a b g
          + A * (Work.MotAS.ASZGC.D0 a b g) ^ 2)
        = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 2
            * (MvPolynomial.X 0 ^ 2
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A)
          - (MvPolynomial.X 0
                * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
              - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l
                * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
            * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
                * MvPolynomial.X 0
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) := by
      simp only [map_add, map_sub, map_mul, map_pow]
      first | refl_ring1 | ring
    rw [key]
    exact Ideal.sub_mem (Work.MotAS.ZIAS a b g)
      (Ideal.mul_mem_left (Work.MotAS.ZIAS a b g)
        ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 2) hQ)
      (Ideal.mul_mem_left (Work.MotAS.ZIAS a b g)
        (MvPolynomial.X 0
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
          - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) hG)
  exact aszElim_dvd_of_le_sat K a b g ha hg hZS _ hmem

end Work.MotAS.ASRulV2M
