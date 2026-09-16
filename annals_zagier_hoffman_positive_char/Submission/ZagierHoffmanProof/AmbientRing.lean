import Submission.ZagierHoffmanProof.AmbientField
import Submission.Commons.Combinatorics.Polynomial.card_eval_image
import Submission.Commons.Combinatorics.Polynomial.card_eval_image_ringHom
import Submission.Commons.RingTheory.LaurentSeries.transcendental_single
import Submission.Commons.Combinatorics.Pigeonhole.exists_ne_of_card_lt_finite
import Submission.Commons.Algebra.Polynomial.coeff_sum_monomial
import Submission.Commons.Algebra.Polynomial.sum_monomial_eq_zero_iff
import Submission.Commons.Algebra.Matrix.mulVec_sum_monomial_coeff
import Submission.Commons.RingTheory.Valuation.v_eval2_eq

/-!
# The ring `O = A^{q^{-∞}}` inside the ambient field

Let `A = F[T]` and `A_ν = A^{q^{-ν}} ⊂ L` for the ambient field `L = Ambient F`.  This file
provides the arithmetic of `A_ν` (the "ring of integers" of `L`): the counting
`#{x ∈ A_ν : v x ≤ (v θ_ν)^n} = q ^ (n + 1)`, the integrality `1 ≤ v x` for `0 ≠ x ∈ A_ν`, and
the Thue–Siegel (pigeonhole) lemma used in the construction of the auxiliary function of the
Anderson–Brownawell–Papanikolas criterion.
-/

set_option autoImplicit false
open scoped WithZero Topology BigOperators
open Polynomial

namespace ZagierHoffmanPositiveChar

noncomputable section

attribute [local instance] Fintype.ofFinite

variable (F : Type*) [Field F] [Finite F]

/-- The coefficient map `F → L` of the ambient field. -/
noncomputable def ambCoeff : F →+* Ambient F :=
  (UniformSpace.Completion.coeRingHom : AmbientPerf F →+* Ambient F).comp
    ((PerfectClosure.of (LaurentSeries F) (ringChar F)).comp (algebraMap F (LaurentSeries F)))

-- The coefficient map is surjective onto the image of `F`, and we register the resulting
-- `Algebra` structure so that polynomial evaluation `eval₂` can be written with `algebraMap`.
noncomputable instance instAlgebraAmbient : Algebra F (Ambient F) :=
  (ambCoeff F).toAlgebra

lemma algebraMap_ambient_eq : (algebraMap F (Ambient F)) = ambCoeff F := rfl

/-- The valuation is trivial on the coefficient field. -/
lemma v_ambCoeff (c : F) (hc : c ≠ 0) : Valued.v (ambCoeff F c) = 1 := by
  have hpow : (ambCoeff F c) ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one]
  have hcar : Fintype.card F - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := F); omega
  have hv : (Valued.v (ambCoeff F c)) ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, hpow, map_one]
  rcases pow_eq_one_iff.mp hv with h | h
  · exact h
  · exact absurd h hcar

/-- The exponent `f` with `|F| = p ^ f`, `p = ringChar F`. -/
noncomputable def ambFrobIdx : ℕ :=
  ((Classical.choose (FiniteField.card F (ringChar F)) : ℕ+) : ℕ)

lemma ambCard_eq_pow : Nat.card F = ringChar F ^ ambFrobIdx F := by
  classical
  rw [Nat.card_eq_fintype_card, ambFrobIdx]
  exact (Classical.choose_spec (FiniteField.card F (ringChar F))).2

/-- `θ_ν = θ ^ (q ^ (-ν))`, the `q ^ ν`-th root of `θ` in the ambient field. -/
noncomputable def ambThetaNu (ν : ℕ) : Ambient F :=
  ((PerfectClosure.mk (LaurentSeries F) (ringChar F)
    (ambFrobIdx F * ν, kummerTheta F) : AmbientPerf F) : Ambient F)

lemma ambThetaNu_pow (ν : ℕ) :
    ambThetaNu F ν ^ (Nat.card F ^ ν) = ambTheta F := by
  have h : (PerfectClosure.mk (LaurentSeries F) (ringChar F)
      (ambFrobIdx F * ν, kummerTheta F) : AmbientPerf F) ^ (Nat.card F ^ ν)
      = PerfectClosure.of (LaurentSeries F) (ringChar F) (kummerTheta F) := by
    rw [ambCard_eq_pow F, ← pow_mul, ← iterate_frobenius (ringChar F) (ambFrobIdx F * ν)]
    exact PerfectClosure.iterate_frobenius_mk (LaurentSeries F) (ringChar F)
      (ambFrobIdx F * ν) (kummerTheta F)
  have hmap := map_pow (UniformSpace.Completion.coeRingHom : AmbientPerf F →+* Ambient F)
    (PerfectClosure.mk (LaurentSeries F) (ringChar F)
      (ambFrobIdx F * ν, kummerTheta F) : AmbientPerf F) (Nat.card F ^ ν)
  rw [h] at hmap
  rw [ambThetaNu, ambTheta]
  exact hmap.symm

/-- The role of `v (θ_ν)`: since `(v θ_ν) ^ (q ^ ν) = v θ`, it is `exp ((q - 1) / q ^ ν)`. -/
noncomputable def ambKappa (ν : ℕ) : ℚᵐ⁰ :=
  WithZero.exp (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)

lemma v_ambThetaNu (ν : ℕ) : Valued.v (ambThetaNu F ν) = ambKappa F ν := by
  have hperf : Valued.v (PerfectClosure.mk (LaurentSeries F) (ringChar F)
      (ambFrobIdx F * ν, kummerTheta F) : AmbientPerf F)
      = Commons.FieldTheory.PerfectClosureValuation.root (ringChar F) (ambFrobIdx F * ν)
          (valRatLaurent F (kummerTheta F)) :=
    Commons.FieldTheory.PerfectClosureValuation.wFun_mk (valRatLaurent F) _ _
  rw [ambThetaNu, valAmbient_coe, hperf, valRatLaurent_kummerTheta,
    Commons.FieldTheory.PerfectClosureValuation.root_of_ne_zero _ _ (WithZero.exp_ne_zero),
    ambKappa, WithZero.log_exp]
  congr 1
  have hcast : ((ringChar F : ℕ) : ℚ) ^ (ambFrobIdx F * ν) = ((Nat.card F : ℕ) : ℚ) ^ ν := by
    rw [ambCard_eq_pow F, Nat.cast_pow]
    exact pow_mul _ _ _
  rw [hcast]

lemma one_lt_ambKappa (ν : ℕ) : 1 < ambKappa F ν := by
  rw [ambKappa, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have hq : (2 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F
    exact_mod_cast this
  have hpos : (0 : ℚ) < (Nat.card F : ℚ) ^ ν := by positivity
  have : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
  exact div_pos this hpos

/-- The `q`-th power map is the identity on the coefficient field. -/
lemma ambCoeff_pow_card (a : F) : (ambCoeff F a) ^ (Nat.card F) = ambCoeff F a := by
  rw [Nat.card_eq_fintype_card, ← map_pow, FiniteField.pow_card a]

lemma pow_card_eq (a : F) : a ^ (Nat.card F) = a := by
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card a

lemma pow_card_pow (ν : ℕ) (a : F) : a ^ (Nat.card F ^ ν) = a := by
  induction ν with
  | zero => simp
  | succ ν ih =>
    rw [Nat.pow_succ, pow_mul, ih, Nat.card_eq_fintype_card, FiniteField.pow_card]

lemma ambCoeff_pow_pow (ν : ℕ) (a : F) :
    (ambCoeff F a) ^ (Nat.card F ^ ν) = ambCoeff F a := by
  induction ν with
  | zero => simp
  | succ ν ih =>
    rw [Nat.pow_succ, pow_mul, ih, ambCoeff_pow_card]

/-- `θ_ν ^ (q ^ ν) = θ`. -/
lemma ambThetaNu_pow_card (ν : ℕ) :
    (ambThetaNu F ν) ^ (Nat.card F ^ ν) = ambTheta F :=
  ambThetaNu_pow F ν

/-- Raising `θ_ν`-polynomials to the `q ^ ν`-th power gives `θ`-polynomials. -/
lemma ambThetaNu_eval_pow (ν : ℕ) (p : Polynomial F) :
    (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ (Nat.card F ^ ν)
      = p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
  haveI : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  haveI : FrobPow (Ambient F) (Nat.card F ^ ν) := FrobPow.pow (R := Ambient F) ν
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
    FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, show i * Nat.card F ^ ν = Nat.card F ^ ν * i by ring, pow_mul,
    ambThetaNu_pow F ν]
  congr 1
  change (ambCoeff F (p.coeff i)) ^ (Nat.card F ^ ν) = ambCoeff F (p.coeff i)
  exact ambCoeff_pow_pow F ν (p.coeff i)

/-- The composite map `F((y)) → L`. -/
noncomputable def ambLiftHom : LaurentSeries F →+* Ambient F :=
  (UniformSpace.Completion.coeRingHom : AmbientPerf F →+* Ambient F).comp
    (PerfectClosure.of (LaurentSeries F) (ringChar F))

lemma ambLiftHom_injective : Function.Injective (ambLiftHom F) := by
  intro a b h
  have h1 : PerfectClosure.of (LaurentSeries F) (ringChar F) a
      = PerfectClosure.of (LaurentSeries F) (ringChar F) b :=
    RingHom.injective (UniformSpace.Completion.coeRingHom : AmbientPerf F →+* Ambient F) h
  exact RingHom.injective (PerfectClosure.of (LaurentSeries F) (ringChar F)) h1

lemma ambCoeff_eq_comp :
    ambCoeff F = (ambLiftHom F).comp (algebraMap F (LaurentSeries F)) := rfl

lemma ambTheta_eq_lift : ambTheta F = ambLiftHom F (kummerTheta F) := rfl

/-- `θ` is transcendental over `F`. -/
lemma ambTheta_transcendental :
    ∀ p : Polynomial F, p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = 0 → p = 0 := by
  intro p hp
  have hq : 2 ≤ Nat.card F := two_le_card_field F
  have hd : ((-(((Nat.card F - 1 : ℕ)) : ℤ))) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
    omega
  have hc : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have htrans := Commons.RingTheory.LaurentSeries.transcendental_single (F := F) hd hc
  have hp' : Polynomial.eval₂ ((ambLiftHom F).comp (algebraMap F (LaurentSeries F)))
      (ambLiftHom F (kummerTheta F)) p = 0 := hp
  rw [← Polynomial.hom_eval₂] at hp'
  refine htrans p ?_
  rw [← kummerTheta]
  exact ambLiftHom_injective F (by rw [hp', map_zero])

/-- `θ_ν` is transcendental over `F`. -/
lemma ambThetaNu_transcendental (ν : ℕ) :
    ∀ p : Polynomial F, p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = 0 → p = 0 := by
  intro p hp
  haveI : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  have h := congrArg (· ^ (Nat.card F ^ ν)) hp
  rw [zero_pow (pow_ne_zero _ (FrobPow.ne_zero (Ambient F) (q := Nat.card F))),
    ambThetaNu_eval_pow] at h
  exact ambTheta_transcendental F p h

/-- The ring `A_ν` = image of `F[T]` under `T ↦ θ_ν`, as a subring of the ambient field. -/
noncomputable def ambASub (ν : ℕ) : Subring (Ambient F) :=
  (Polynomial.eval₂RingHom (algebraMap F (Ambient F)) (ambThetaNu F ν)).range

/-- The `ν`-th level of the ring of integers: the image of `F[T]` under `T ↦ θ_ν`. -/
noncomputable def ambA (ν : ℕ) : Set (Ambient F) := ambASub F ν

lemma mem_ambA_iff (ν : ℕ) (x : Ambient F) :
    x ∈ ambA F ν ↔
      ∃ p : Polynomial F, p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x := by
  simp only [ambA, ambASub, SetLike.mem_coe, RingHom.mem_range, Polynomial.coe_eval₂RingHom]

lemma ambA_add_mem {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν) :
    x + y ∈ ambA F ν := (ambASub F ν).add_mem hx hy

lemma ambA_mul_mem {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν) :
    x * y ∈ ambA F ν := (ambASub F ν).mul_mem hx hy

lemma ambA_sub_mem {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν) :
    x - y ∈ ambA F ν := (ambASub F ν).sub_mem hx hy

lemma ambA_one_mem (ν : ℕ) : (1 : Ambient F) ∈ ambA F ν := (ambASub F ν).one_mem

lemma ambA_sum_mem {ν : ℕ} {ι : Type*} {t : Finset ι} {f : ι → Ambient F}
    (h : ∀ i ∈ t, f i ∈ ambA F ν) : ∑ i ∈ t, f i ∈ ambA F ν :=
  (ambASub F ν).sum_mem h

lemma ambA_pow_mem (ν : ℕ) {x : Ambient F} (hx : x ∈ ambA F ν) (n : ℕ) :
    x ^ n ∈ ambA F ν := (ambASub F ν).pow_mem hx n

/-- `θ_ν ^ q = θ_ν ^ q` is again in `A_ν` (it is the image of `X ^ q`). -/
lemma ambThetaNu_pow_mem (ν : ℕ) (n : ℕ) :
    (ambThetaNu F ν) ^ n ∈ ambA F ν :=
  (mem_ambA_iff F ν _).mpr ⟨Polynomial.X ^ n, by rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]⟩

/-- `A_ν` is closed under the `q`-th power map (for `ν ≥ 1`): `(p(θ_ν))^q = p^{[q]}(θ_ν^q)`
and `θ_ν^q ∈ A_ν`.  Here `ν ≥ 1` is only needed because the statement uses the *same* level;
`θ_ν^q = θ_{ν-1}`. -/
lemma ambA_pow_card_mem {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    x ^ (Nat.card F) ∈ ambA F ν := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  haveI : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  have hpow : (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ (Nat.card F)
      = ∑ i ∈ Finset.range (p.natDegree + 1),
          (algebraMap F (Ambient F) (p.coeff i)) *
            ((ambThetaNu F ν) ^ (Nat.card F)) ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, FrobPow.sum_pow_finset]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, show i * Nat.card F = Nat.card F * i by ring, pow_mul,
      ← map_pow, pow_card_eq]
  rw [hpow]
  refine ambA_sum_mem F (fun i _ => ambA_mul_mem F ?_ ?_)
  · exact (mem_ambA_iff F ν _).mpr ⟨Polynomial.C (p.coeff i), by simp⟩
  · exact ambA_pow_mem F ν (ambThetaNu_pow_mem F ν (Nat.card F)) i

/-- `A_ν` is closed under `q ^ j`-th powers. -/
lemma ambA_pow_card_pow_mem {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) (j : ℕ) :
    x ^ (Nat.card F ^ j) ∈ ambA F ν := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [Nat.pow_succ, pow_mul]
    exact ambA_pow_card_mem F ih

/-- The valuation of a nonzero `θ_ν`-polynomial is `(v θ_ν) ^ deg`. -/
lemma v_eval₂_ambThetaNu (ν : ℕ) (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν))
      = (ambKappa F ν) ^ p.natDegree := by
  rw [Commons.RingTheory.Valuation.v_eval2_eq (Valued.v : Valuation (Ambient F) ℚᵐ⁰)
    (algebraMap F (Ambient F)) (θ := ambThetaNu F ν) (v_ambCoeff F)
    (by rw [v_ambThetaNu]; exact one_lt_ambKappa F ν) p hp, v_ambThetaNu]

/-- The counting: the number of elements of `A_ν` of valuation at most `(v θ_ν) ^ n` is
`q ^ (n + 1)`. -/
theorem card_ambA (ν n : ℕ) :
    Nat.card {x : Ambient F // x ∈ ambA F ν ∧ Valued.v x ≤ (ambKappa F ν) ^ n}
      = (Nat.card F) ^ (n + 1) := by
  have hiff : ∀ x : Ambient F,
      (x ∈ ambA F ν ∧ Valued.v x ≤ (ambKappa F ν) ^ n) ↔
        (∃ p : Polynomial F, p.natDegree ≤ n ∧
          p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x) := by
    intro x
    constructor
    · rintro ⟨hxA, hpv⟩
      obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hxA
      rcases eq_or_ne p 0 with rfl | hp
      · exact ⟨0, by simp, by simp⟩
      · refine ⟨p, ?_, rfl⟩
        by_contra hcon
        push Not at hcon
        have h1 : (ambKappa F ν) ^ n < (ambKappa F ν) ^ p.natDegree := by
          rw [pow_lt_pow_iff_right₀ (one_lt_ambKappa F ν)]
          omega
        rw [v_eval₂_ambThetaNu F ν p hp] at hpv
        exact absurd hpv (not_le.mpr h1)
    · rintro ⟨p, hpn, rfl⟩
      refine ⟨(mem_ambA_iff F ν _).mpr ⟨p, rfl⟩, ?_⟩
      rcases eq_or_ne p 0 with rfl | hp
      · simp
      · rw [v_eval₂_ambThetaNu F ν p hp]
        exact pow_le_pow_right₀ (le_of_lt (one_lt_ambKappa F ν)) hpn
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact Commons.Combinatorics.Polynomial.card_eval_image_ringHom (f := algebraMap F (Ambient F))
    (θ := ambThetaNu F ν) (ambThetaNu_transcendental F ν) n

/-- **Thue–Siegel / Siegel's lemma** over `A_ν`, for arbitrary finite index types. -/
theorem siegel_one {R S : Type*} [Fintype R] [Fintype S]
    (hcard : Fintype.card R < Fintype.card S) {ν μ m : ℕ}
    (hm : (m + μ + 1) * Fintype.card R < (m + 1) * Fintype.card S)
    (M : Matrix R S (Ambient F))
    (hM : ∀ i j, M i j ∈ ambA F ν ∧ Valued.v (M i j) ≤ (ambKappa F ν) ^ μ) :
    ∃ z : S → Ambient F,
      (∀ j, z j ∈ ambA F ν ∧ Valued.v (z j) ≤ (ambKappa F ν) ^ m) ∧
      z ≠ 0 ∧ M.mulVec z = 0 := by
  classical
  set T := {y : R → Ambient F // ∀ i, y i ∈ ambA F ν ∧
    Valued.v (y i) ≤ (ambKappa F ν) ^ (m + μ)} with hTdef
  have hcardS : Nat.card {z : S → Ambient F // ∀ j, z j ∈ ambA F ν ∧
      Valued.v (z j) ≤ (ambKappa F ν) ^ m} = (Nat.card F ^ (m + 1)) ^ Fintype.card S := by
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : S) (z : Ambient F) =>
      z ∈ ambA F ν ∧ Valued.v z ≤ (ambKappa F ν) ^ m))]
    rw [Nat.card_pi]
    have hprod : (∏ j : S, Nat.card {x : Ambient F // x ∈ ambA F ν ∧
        Valued.v x ≤ (ambKappa F ν) ^ m}) = ∏ _j : S, Nat.card F ^ (m + 1) :=
      Finset.prod_congr rfl fun j _ => card_ambA F ν m
    rw [hprod, Finset.prod_const, Finset.card_univ]
  have hcardT : Nat.card T = (Nat.card F ^ (m + μ + 1)) ^ Fintype.card R := by
    rw [hTdef, Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : R) (z : Ambient F) =>
      z ∈ ambA F ν ∧ Valued.v z ≤ (ambKappa F ν) ^ (m + μ)))]
    rw [Nat.card_pi]
    have hprod : (∏ i : R, Nat.card {x : Ambient F // x ∈ ambA F ν ∧
        Valued.v x ≤ (ambKappa F ν) ^ (m + μ)}) = ∏ _i : R, Nat.card F ^ (m + μ + 1) :=
      Finset.prod_congr rfl fun i _ => card_ambA F ν (m + μ)
    rw [hprod, Finset.prod_const, Finset.card_univ]
  have hlt : Nat.card T < Nat.card {z : S → Ambient F // ∀ j, z j ∈ ambA F ν ∧
      Valued.v (z j) ≤ (ambKappa F ν) ^ m} := by
    rw [hcardT, hcardS, ← pow_mul, ← pow_mul]
    exact pow_lt_pow_right₀ (by have := two_le_card_field F; omega) hm
  have hbound : ∀ (x : S → Ambient F), (∀ j, x j ∈ ambA F ν ∧
      Valued.v (x j) ≤ (ambKappa F ν) ^ m) →
      ∀ i, M.mulVec x i ∈ ambA F ν ∧
        Valued.v (M.mulVec x i) ≤ (ambKappa F ν) ^ (m + μ) := by
    intro x hx i
    have hmem : M.mulVec x i ∈ ambA F ν := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact (ambASub F ν).sum_mem (fun j _ => ambA_mul_mem F (hM i j).1 (hx j).1)
    refine ⟨hmem, ?_⟩
    rw [Matrix.mulVec_apply_eq_sum]
    refine Valuation.map_sum_le _ (fun j _ => ?_)
    rw [Valuation.map_mul]
    calc Valued.v (M i j) * Valued.v (x j)
        ≤ (ambKappa F ν) ^ μ * (ambKappa F ν) ^ m :=
          mul_le_mul' (hM i j).2 (hx j).2
      _ = (ambKappa F ν) ^ (m + μ) := by rw [← pow_add]; ring_nf
  let φ : {z : S → Ambient F // ∀ j, z j ∈ ambA F ν ∧
      Valued.v (z j) ≤ (ambKappa F ν) ^ m} → T :=
    fun x => ⟨M.mulVec x.1, hbound x.1 x.2⟩
  have hTne : Nat.card T ≠ 0 := by
    rw [hcardT]
    exact pow_ne_zero _ (pow_ne_zero _ (by have := two_le_card_field F; omega))
  haveI : Finite T := Nat.finite_of_card_ne_zero hTne
  obtain ⟨x₁, x₂, hne, heq⟩ :=
    Commons.Combinatorics.Pigeonhole.exists_ne_of_card_lt_finite φ hlt
  have hx1 : M.mulVec x₁.1 = M.mulVec x₂.1 := congrArg Subtype.val heq
  refine ⟨x₁.1 - x₂.1, fun j => ?_, ?_, ?_⟩
  · exact ⟨ambA_sub_mem F (x₁.2 j).1 (x₂.2 j).1,
      le_trans (Valuation.map_sub _ _ _) (max_le (x₁.2 j).2 (x₂.2 j).2)⟩
  · intro hz
    exact hne (Subtype.ext (sub_eq_zero.mp hz))
  · rw [Matrix.mulVec_sub, hx1, sub_self]

/-- **Siegel's lemma over `A_ν[T]`** (ABP's `Lemma:SiegelLemmaTwo`): a homogeneous linear system
over `A_ν[T]` of `R × S` shape (`|R| < |S|`) with entries of `T`-degree `≤ d` and coefficients in
`A_ν` of size `≤ (v θ_ν)^μ` has a nonzero solution vector of polynomials of `T`-degree `≤ e` and
coefficients in `A_ν` of size `≤ (v θ_ν)^m`. -/
theorem siegel_two {R S : Type*} [Fintype R] [Fintype S]
    (hcard : Fintype.card R < Fintype.card S) {ν d e μ m : ℕ}
    (hm : (m + μ + 1) * (Fintype.card R * (d + e + 1))
      < (m + 1) * (Fintype.card S * (e + 1)))
    (M : Matrix R S (Polynomial (Ambient F)))
    (hM : ∀ i j k, (M i j).coeff k ∈ ambA F ν ∧
      Valued.v ((M i j).coeff k) ≤ (ambKappa F ν) ^ μ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d) :
    ∃ x : S → Polynomial (Ambient F), x ≠ 0 ∧ M.mulVec x = 0 ∧
      (∀ j k, (x j).coeff k ∈ ambA F ν ∧
        Valued.v ((x j).coeff k) ≤ (ambKappa F ν) ^ m) ∧
      (∀ j, (x j).natDegree ≤ e) := by
  classical
  set M' : Matrix (R × Fin (d + e + 1)) (S × Fin (e + 1)) (Ambient F) :=
    fun p q => if (q.2 : ℕ) ≤ (p.2 : ℕ) then (M p.1 q.1).coeff ((p.2 : ℕ) - (q.2 : ℕ)) else 0
    with hM'def
  have hM'mem : ∀ p q, M' p q ∈ ambA F ν ∧ Valued.v (M' p q) ≤ (ambKappa F ν) ^ μ := by
    intro p q
    by_cases h : (q.2 : ℕ) ≤ (p.2 : ℕ)
    · rw [hM'def]; simp only [h, ↓reduceIte]
      exact hM p.1 q.1 _
    · rw [hM'def]; simp only [h, ↓reduceIte]
      exact ⟨(ambASub F ν).zero_mem, by rw [map_zero]; exact zero_le⟩
  have hcardR : Fintype.card R * (d + e + 1) < Fintype.card S * (e + 1) := by
    have h1 : (m + 1) * (Fintype.card R * (d + e + 1)) ≤
        (m + μ + 1) * (Fintype.card R * (d + e + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 hm)
  have hcard' : Fintype.card (R × Fin (d + e + 1)) < Fintype.card (S × Fin (e + 1)) := by
    simpa [Fintype.card_prod, Fintype.card_fin] using hcardR
  have hm' : (m + μ + 1) * Fintype.card (R × Fin (d + e + 1))
      < (m + 1) * Fintype.card (S × Fin (e + 1)) := by
    simpa [Fintype.card_prod, Fintype.card_fin, mul_assoc] using hm
  obtain ⟨z, hz, hz0, hzM⟩ := siegel_one F hcard' hm' M' hM'mem
  refine ⟨fun j => ∑ b : Fin (e + 1), Polynomial.monomial (b : ℕ) (z (j, b)),
    ?_, ?_, ?_, ?_⟩
  · intro hx
    refine hz0 (funext fun q => ?_)
    obtain ⟨j, b⟩ := q
    have := (Commons.Algebra.Polynomial.sum_monomial_eq_zero_iff
      (fun b' => z (j, b'))).mp (by simpa using congrFun hx j)
    exact this b
  · -- `M.mulVec x = 0`
    funext i
    apply Polynomial.ext
    intro k
    rw [Commons.Algebra.Matrix.mulVec_sum_monomial_coeff]
    by_cases hk : k < d + e + 1
    · have hkey : (∑ p : S × Fin (e + 1),
            (if (p.2 : ℕ) ≤ k then (M i p.1).coeff (k - (p.2 : ℕ)) else 0) * z p)
          = (M'.mulVec z) (i, ⟨k, hk⟩) := by
        rw [Matrix.mulVec_apply_eq_sum, hM'def]
      rw [hkey]
      exact congrFun hzM _
    · refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : (p.2 : ℕ) ≤ k
      · rw [if_pos hp]
        have hgt : d < k - (p.2 : ℕ) := by
          have h1 : (p.2 : ℕ) ≤ e := by have := (p.2).isLt; omega
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i p.1) hgt),
          zero_mul]
      · rw [if_neg hp, zero_mul]
  · -- the coefficients of `x j` are the `z (j, b)`
    intro j k
    rw [Commons.Algebra.Polynomial.coeff_sum_monomial]
    by_cases hk : k < e + 1
    · rw [dif_pos hk]
      exact hz _
    · rw [dif_neg hk]
      exact ⟨(ambASub F ν).zero_mem, by rw [map_zero]; exact zero_le⟩
  · -- the `T`-degree of `x j` is at most `e`
    intro j
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [Commons.Algebra.Polynomial.coeff_sum_monomial]
    exact dif_neg (by omega)

end

end ZagierHoffmanPositiveChar
