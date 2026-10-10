import Mathlib
import Submission.Work.MotK.TGen.ZpgPsiDefs
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZpgPsiKillAll
import Submission.Work.MotK.TGen.ZpgI4W4NonZeroDiv
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TGen.KerZpgPsiSat`

The kernel of the graph map `zpgPsi : K[y₁,y₂,y₃,y₄] → ZPF = Frac (K[y₁,y₃]/(zpgE))` is contained
in the saturation of the chart ideal `zpgI4` at the denominator `zpgW4`:
`zpgPsi f = 0 ⟹ ∃ n, zpgW4 ^ n * f ∈ zpgI4`.

The proof is an explicit "clearing of denominators", mirroring the graph formulas that define
`zpgPsi` (`y₂ ↦ (a²h²y₃y₄ − ab y₁²)/b²`, `y₄ ↦ c/(h²W)`):

* modulo the chart ideal one may substitute `b²y₂ ≡ a²h²y₃y₄ − ab y₁²` (the third chart quadric
  `zpgQ 3`) and `h²W y₄ ≡ c` (the chart relation `zpgG3`);
* consequently, for every `f` there are a constant `u ≠ 0`, an exponent `N` and a polynomial
  `Q ∈ K[y₁,y₃]` with `C u · zpgW4^N · f − Q(y₁,y₃) ∈ zpgI4` (an induction on `f`; the four
  coordinates are the base cases);
* `zpgPsi (Q(y₁,y₃)) = algebraMap (K[y₁,y₃]) ZPF Q`, and the kernel of that map is `(zpgE)`, because
  `ZP = K[y₁,y₃]/(zpgE)` is a domain (hypothesis) with fraction field `ZPF`; so `zpgPsi f = 0`
  forces `Q ∈ (zpgE)`, i.e. `Q(y₁,y₃) ∈ zpgI4` since `zpgE4 ∈ zpgI4`;
* hence `C u · zpgW4^N · f ∈ zpgI4`, and the non-zero scalar `u` is removed with
  `mem_of_C_mul_mem`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## The plane coordinates inside the four chart coordinates -/

/-- `y₁` and `y₃` as coordinates of the four-dimensional chart: `0 ↦ 0`, `1 ↦ 2`. -/
def zpgEmb24 : Fin 2 → Fin 4 := ![0, 2]

/-- The substitution `y₁ ↦ y₁`, `y₃ ↦ y₃` from `K[y₁,y₃]` into `K[y₁,y₂,y₃,y₄]`. -/
noncomputable def zpgRen (K : Type) [CommSemiring K] :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.rename zpgEmb24

@[simp] theorem zpgRen_X0 (K : Type) [CommSemiring K] :
    zpgRen K (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X (0 : Fin 4) := by
  rw [zpgRen, MvPolynomial.rename_X]
  rfl

@[simp] theorem zpgRen_X1 (K : Type) [CommSemiring K] :
    zpgRen K (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (2 : Fin 4) := by
  rw [zpgRen, MvPolynomial.rename_X]
  rfl

@[simp] theorem zpgRen_C (K : Type) [CommSemiring K] (r : K) :
    zpgRen K (MvPolynomial.C r : MvPolynomial (Fin 2) K) = MvPolynomial.C r := by
  rw [zpgRen, MvPolynomial.rename_C]

theorem zpgRen_zpgW (a b h : K) : zpgRen K (zpgW a b h) = zpgW4 a b h := by
  simp only [zpgW, zpgW4, map_sub, map_mul, map_pow, zpgRen_C, zpgRen_X0, zpgRen_X1]

theorem zpgRen_zpgC (a b h : K) : zpgRen K (zpgC a b h) = zpgC4 a b h := by
  simp only [zpgC, zpgC4, map_sub, map_mul, map_pow, zpgRen_C, zpgRen_X0, zpgRen_X1]

theorem zpgRen_zpgE (a b h : K) : zpgRen K (zpgE a b h) = zpgE4 a b h := by
  simp only [zpgE, zpgE4, map_add, map_sub, map_mul, map_pow, map_neg, zpgRen_C, zpgRen_X0,
    zpgRen_X1]

/-- **`zpgPsi` composed with the plane embedding is the structure map of the plane model.** -/
theorem zpgPsi_zpgRen (a b h : K) [IsDomain (ZP K a b h)] (Q : MvPolynomial (Fin 2) K) :
    zpgPsi K a b h (zpgRen K Q) = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) Q := by
  have hcomp : (zpgPsi K a b h).comp (zpgRen K) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin 2) K) (ZPF K a b h) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change zpgPsi K a b h (zpgRen K (MvPolynomial.X (0 : Fin 2)))
        = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (MvPolynomial.X (0 : Fin 2))
      rw [zpgRen_X0, zpgPsi_X0, zpg_alg_X0]
    · change zpgPsi K a b h (zpgRen K (MvPolynomial.X (1 : Fin 2)))
        = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (MvPolynomial.X (1 : Fin 2))
      rw [zpgRen_X1, zpgPsi_X2, zpg_alg_X1]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →ₐ[K] ZPF K a b h => g Q) hcomp

/-! ## The main theorem -/

theorem KerZpgPsiSat (K : Type) [Field K] (a b h : K) [IsDomain (Work.MotK.TGen.ZP K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (hw : Work.MotK.TGen.zpgWbar K a b h ≠ 0) (f : MvPolynomial (Fin 4) K) : Work.MotK.TGen.zpgPsi K a b h f = 0 → ∃ n : ℕ, (Work.MotK.TGen.zpgW4 a b h) ^ n * f ∈ Work.MotK.TGen.zpgI4 a b h := by
  intro hf
  have hW : algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h) ≠ 0 := by
    rw [← zpgWbar_eq_algebraMap]
    exact hw
  have hIle : zpgI4 a b h ≤ RingHom.ker (zpgPsi K a b h) := by
    rw [zpgI4, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact ZpgPsiKillAll K a b h ha hb hh hW k
  -- the two elimination certificates
  have hq3 : -zpgQ a b h 3 ∈ zpgI4 a b h :=
    neg_mem (Ideal.subset_span ⟨3, rfl⟩)
  have hg3 : zpgG3 a b h ∈ zpgI4 a b h := (ZTwistDivGeomCerts K a b h).2.2.1
  have hE4 : zpgE4 a b h ∈ zpgI4 a b h := (ZTwistDivGeomCerts K a b h).2.1
  -- the base cases of the induction
  have hX0 : ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
      C u * (zpgW4 a b h) ^ N * (X (0 : Fin 4)) - zpgRen K Q ∈ zpgI4 a b h :=
    ⟨1, one_ne_zero, 0, X (0 : Fin 2), by simp⟩
  have hX2 : ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
      C u * (zpgW4 a b h) ^ N * (X (2 : Fin 4)) - zpgRen K Q ∈ zpgI4 a b h :=
    ⟨1, one_ne_zero, 0, X (1 : Fin 2), by simp⟩
  have hX1 : ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
      C u * (zpgW4 a b h) ^ N * (X (1 : Fin 4)) - zpgRen K Q ∈ zpgI4 a b h := by
    refine ⟨b ^ 2 * h ^ 2, mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hh), 1,
      C (a ^ 2 * h ^ 2) * X 1 * zpgC a b h - C (a * b * h ^ 2) * zpgW a b h * (X 0) ^ 2, ?_⟩
    have hident : C (b ^ 2 * h ^ 2) * (zpgW4 a b h) ^ 1 * (X (1 : Fin 4))
        - zpgRen K (C (a ^ 2 * h ^ 2) * X 1 * zpgC a b h - C (a * b * h ^ 2) * zpgW a b h * (X 0) ^ 2)
        = C (h ^ 2) * zpgW4 a b h * (-zpgQ a b h 3) + C (a ^ 2 * h ^ 2) * X 2 * zpgG3 a b h := by
      simp only [zpgG3, zpgQ_three, zpgC4, zpgW4, zpgRen_zpgC, zpgRen_zpgW, zpgRen_X0,
        zpgRen_X1, zpgRen_C, map_sub, map_mul, map_pow, map_add, map_neg]
      first | refl_ring1 | ring
    rw [hident]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq3)
      (Ideal.mul_mem_left _ (C (a ^ 2 * h ^ 2) * X 2) hg3)
  have hX3 : ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
      C u * (zpgW4 a b h) ^ N * (X (3 : Fin 4)) - zpgRen K Q ∈ zpgI4 a b h := by
    refine ⟨h ^ 2, pow_ne_zero 2 hh, 1, zpgC a b h, ?_⟩
    have hident : C (h ^ 2) * (zpgW4 a b h) ^ 1 * (X (3 : Fin 4)) - zpgRen K (zpgC a b h)
        = zpgG3 a b h := by
      simp only [zpgG3, zpgRen_zpgC, map_one, mul_one, pow_one]
    rw [hident]
    exact hg3
  have hXn : ∀ n : Fin 4, ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
      C u * (zpgW4 a b h) ^ N * (X n) - zpgRen K Q ∈ zpgI4 a b h := by
    intro n
    fin_cases n
    · exact hX0
    · exact hX1
    · exact hX2
    · exact hX3
  -- the clearing-of-denominators induction
  have key : ∀ f : MvPolynomial (Fin 4) K,
      ∃ (u : K) (_ : u ≠ 0) (N : ℕ) (Q : MvPolynomial (Fin 2) K),
        C u * (zpgW4 a b h) ^ N * f - zpgRen K Q ∈ zpgI4 a b h := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => exact ⟨1, one_ne_zero, 0, C r, by simp⟩
    | add p q hp hq =>
      obtain ⟨u1, hu1, N1, Q1, h1⟩ := hp
      obtain ⟨u2, hu2, N2, Q2, h2⟩ := hq
      refine ⟨u1 * u2, mul_ne_zero hu1 hu2, N1 + N2,
        C u2 * (zpgW a b h) ^ N2 * Q1 + C u1 * (zpgW a b h) ^ N1 * Q2, ?_⟩
      have hmem : (C u2 * (zpgW4 a b h) ^ N2) * (C u1 * (zpgW4 a b h) ^ N1 * p - zpgRen K Q1)
          + (C u1 * (zpgW4 a b h) ^ N1) * (C u2 * (zpgW4 a b h) ^ N2 * q - zpgRen K Q2)
          ∈ zpgI4 a b h :=
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
      convert hmem using 1
      simp only [map_add, map_mul, map_pow, zpgRen_C, zpgRen_zpgW]
      first | refl_ring1 | ring
    | mul_X p n hp =>
      obtain ⟨u, hu, N, Q, hQ⟩ := hp
      obtain ⟨u', hu', N', Q', hQ'⟩ := hXn n
      refine ⟨u * u', mul_ne_zero hu hu', N + N', Q * Q', ?_⟩
      have hmem : (C u * (zpgW4 a b h) ^ N * p - zpgRen K Q)
            * (C u' * (zpgW4 a b h) ^ N' * X n)
          + zpgRen K Q * (C u' * (zpgW4 a b h) ^ N' * X n - zpgRen K Q') ∈ zpgI4 a b h :=
        Ideal.add_mem _ (Ideal.mul_mem_right _ _ hQ) (Ideal.mul_mem_left _ _ hQ')
      convert hmem using 1
      simp only [map_mul, map_pow, zpgRen_zpgW]
      first | refl_ring1 | ring
  obtain ⟨u, hu, N, Q, hQ⟩ := key f
  -- `zpgPsi` of the plane polynomial vanishes
  have hpsiQ : algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) Q = 0 := by
    have hmem := hIle hQ
    rw [RingHom.mem_ker, map_sub] at hmem
    have hz : zpgPsi K a b h (C u * (zpgW4 a b h) ^ N * f) = 0 := by
      simp only [map_mul, map_pow, zpgPsi_C, zpgPsi_zpgW4, hf, mul_zero, zero_mul]
    rw [zpgPsi_zpgRen, hz, zero_sub] at hmem
    exact neg_eq_zero.mp hmem
  -- hence `Q` is a multiple of the eliminant, so `Q(y₁,y₃) ∈ zpgI4`
  have hQmem : Q ∈ Ideal.span {zpgE a b h} := by
    have h2 : algebraMap (MvPolynomial (Fin 2) K) (ZP K a b h) Q = 0 :=
      IsFractionRing.injective (ZP K a b h) (ZPF K a b h) (by
        rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (ZP K a b h) (ZPF K a b h),
          hpsiQ, map_zero])
    have h3 : Ideal.Quotient.mk (Ideal.span {zpgE a b h}) Q = 0 := by
      rw [← Ideal.Quotient.algebraMap_eq]
      exact h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp hQmem
  have hrenQ : zpgRen K Q ∈ zpgI4 a b h := by
    rw [← hH, map_mul, zpgRen_zpgE]
    exact Ideal.mul_mem_left _ (zpgRen K H) hE4
  -- conclude
  have hfinal : C u * (zpgW4 a b h) ^ N * f ∈ zpgI4 a b h := by
    have := Ideal.add_mem _ hQ hrenQ
    simpa using this
  refine ⟨N, ?_⟩
  exact mem_of_C_mul_mem a b h u hu (f := (zpgW4 a b h) ^ N * f) (by simpa [mul_assoc] using hfinal)

end Work.MotK.TGen
