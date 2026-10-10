import Mathlib
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotC5N3.KleinPASNegApply
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Work.MotC5N3

/-! ## The sign involution `X i ↦ (-1)^i X i` of `K[X₀,…,X₄]`

The AS twisted Klein Pfaffians satisfy
`p^AS_k(a,b,-c)(z) = (-1)^k p^AS_k(a,b,c)(((-1)^i z_i))`
(`Work.MotC5N3.kleinPAS_neg_apply`).  Hence the sign involution `X i ↦ (-1)^i X i` of the polynomial
ring identifies the chart ideal of the AS twist of class `-c` with the chart ideal of the twist of
class `c`.  Since `K` has characteristic `5`, `3 * g = -(2 * g)`, which yields the asserted
isomorphism. -/

/-- The sign vector `i ↦ (-1)^i X_i`. -/
noncomputable def signFun (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 5) K :=
  fun i => (-1 : MvPolynomial (Fin 5) K) ^ (i : ℕ) * MvPolynomial.X i

/-- The `K`-algebra endomorphism `X i ↦ (-1)^i X i` of `K[X₀,…,X₄]`. -/
noncomputable def signHom (K : Type*) [CommRing K] :
    MvPolynomial (Fin 5) K →ₐ[K] MvPolynomial (Fin 5) K :=
  MvPolynomial.aeval (signFun K)

lemma signHom_X (K : Type*) [CommRing K] (i : Fin 5) :
    signHom K (MvPolynomial.X i) = signFun K i := by
  rw [signHom, MvPolynomial.aeval_X]

lemma signHom_C (K : Type*) [CommRing K] (r : K) :
    signHom K (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [signHom, MvPolynomial.aeval_C]
  rfl

/-- The ring-homomorphism form of `signHom` at the variables. -/
lemma signHom_coe_X (K : Type*) [CommRing K] (i : Fin 5) :
    (signHom K : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K) (MvPolynomial.X i)
      = signFun K i :=
  signHom_X K i

/-- The ring-homomorphism form of `signHom` at the scalars. -/
lemma signHom_coe_C (K : Type*) [CommRing K] (r : K) :
    (signHom K : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K) (MvPolynomial.C r)
      = MvPolynomial.C r :=
  signHom_C K r

lemma neg_one_pow_mul_self {R : Type*} [Ring R] (n : ℕ) :
    (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← pow_add]
  exact (Even.add_self n).neg_one_pow

/-- `signHom` is an involution. -/
lemma signHom_comp_self (K : Type*) [CommRing K] :
    (signHom K).comp (signHom K) = AlgHom.id K (MvPolynomial (Fin 5) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  show signHom K (signHom K (MvPolynomial.X i)) = MvPolynomial.X i
  rw [signHom_X]
  change signHom K ((-1 : MvPolynomial (Fin 5) K) ^ (i : ℕ) * MvPolynomial.X i)
    = MvPolynomial.X i
  rw [signHom, map_mul, map_pow, map_neg, map_one, MvPolynomial.aeval_X]
  change (-1 : MvPolynomial (Fin 5) K) ^ (i : ℕ) *
      ((-1 : MvPolynomial (Fin 5) K) ^ (i : ℕ) * MvPolynomial.X i) = MvPolynomial.X i
  rw [← mul_assoc, neg_one_pow_mul_self (R := MvPolynomial (Fin 5) K) (i : ℕ), one_mul]

/-- The sign involution as a `K`-algebra equivalence (its own inverse). -/
noncomputable def signEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  AlgEquiv.ofAlgHom (signHom K) (signHom K) (signHom_comp_self K) (signHom_comp_self K)

lemma signEquiv_apply (K : Type*) [CommRing K] (x : MvPolynomial (Fin 5) K) :
    signEquiv K x = signHom K x := rfl

/-- The ring-homomorphism coercion of `signEquiv` is `signHom`. -/
lemma signEquiv_coe (K : Type*) [CommRing K] :
    ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
      = (signHom K : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K) := by
  apply RingHom.ext
  intro x
  rfl

/-- The AS Pfaffians commute with every ring homomorphism. -/
lemma kleinPAS_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b g : R)
    (y : Fin 5 → R) (k : Fin 5) :
    f (Work.MotAS.kleinPAS a b g y k)
      = Work.MotAS.kleinPAS (f a) (f b) (f g) (fun i => f (y i)) k := by
  fin_cases k <;>
    simp only [Work.MotAS.kleinPAS, Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1,
      Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk,
      map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat] <;>
    first | refl_ring1 | ring

/-- The sign involution on the transported AS Pfaffians. -/
lemma signEquiv_coe_kleinPAS (K : Type*) [CommRing K] (a b c : K) (k : Fin 5) :
    ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
        (Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
          (fun i => MvPolynomial.X i) k)
      = Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
          (signFun K) k := by
  rw [signEquiv_coe]
  refine (kleinPAS_ringHom (signHom K : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
    (fun i => MvPolynomial.X i) k).trans ?_
  simp only [signHom_coe_C, signHom_coe_X]

/-- `kleinPAS_neg_apply`, phrased through the sign vector `signFun`. -/
lemma kleinPAS_neg_eq (K : Type*) [CommRing K] (a b c : K) (k : Fin 5) :
    Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C (-c))
        (fun i => MvPolynomial.X i) k
      = (-1 : MvPolynomial (Fin 5) K) ^ (k : ℕ) *
        Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
          (signFun K) k := by
  rw [MvPolynomial.C_neg]
  rw [Work.MotC5N3.kleinPAS_neg_apply (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
    (fun i => MvPolynomial.X i) k]
  rfl

/-- The span of the range of a family is unchanged by multiplying each member by a scalar `e i`
with `e i * e i = 1`. -/
lemma span_range_eq_of_eq_mul {ι R : Type*} [CommRing R] (u v e : ι → R)
    (h : ∀ i, v i = e i * u i) (he : ∀ i, e i * e i = 1) :
    Ideal.span (Set.range u) = Ideal.span (Set.range v) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hx : u i = e i * v i := by rw [h i, ← mul_assoc, he i, one_mul]
    rw [hx]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [h i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The sign involution carries the radical of the AS Pfaffian ideal of class `c` to the one of
class `-c`. -/
theorem map_signEquiv_asQideal (K : Type*) [CommRing K] (a b c : K) :
    Ideal.map ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
        (Work.MotAS.asQideal a b c) = Work.MotAS.asQideal a b (-c) := by
  have hsurj : Function.Surjective
      ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K) :=
    fun x => ⟨(signEquiv K).symm x, (signEquiv K).apply_symm_apply x⟩
  have hker : RingHom.ker ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
      ≤ Ideal.span (Set.range (fun k : Fin 5 => Work.MotAS.kleinPAS (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C c) (fun i => MvPolynomial.X i) k)) := by
    rw [AlgHom.ker_coe_equiv]
    exact bot_le
  rw [Work.MotAS.asQideal]
  rw [Ideal.map_radical_of_surjective hsurj hker]
  rw [Ideal.map_span]
  congr 1
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := hy
    beta_reduce
    rw [signEquiv_coe_kleinPAS K a b c k]
    have hP' : Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
          (signFun K) k
        = (-1 : MvPolynomial (Fin 5) K) ^ (k : ℕ) *
          Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C (-c))
            (fun i => MvPolynomial.X i) k := by
      rw [kleinPAS_neg_eq K a b c k, ← mul_assoc,
        neg_one_pow_mul_self (R := MvPolynomial (Fin 5) K) (k : ℕ), one_mul]
    rw [hP']
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    beta_reduce
    rw [kleinPAS_neg_eq K a b c k]
    have hP'' : (-1 : MvPolynomial (Fin 5) K) ^ (k : ℕ) *
          Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
            (signFun K) k
        = (-1 : MvPolynomial (Fin 5) K) ^ (k : ℕ) *
          ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
            (Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c)
              (fun i => MvPolynomial.X i) k) := by
      rw [signEquiv_coe_kleinPAS K a b c k]
    rw [hP'']
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)

/-- The sign involution carries the chart ideal of the AS twist of class `c` to the one of
class `-c`. -/
theorem map_signEquiv_asChartIdeal (K : Type*) [CommRing K] (a b c : K) :
    Ideal.map ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
        (Work.MotAS.asChartIdeal a b c) = Work.MotAS.asChartIdeal a b (-c) := by
  rw [Work.MotAS.asChartIdeal, Ideal.map_sup]
  congr 1
  · exact map_signEquiv_asQideal K a b c
  · have hsf : signFun K (0 : Fin 5) = MvPolynomial.X (0 : Fin 5) := by
      change (-1 : MvPolynomial (Fin 5) K) ^ (0 : ℕ) * MvPolynomial.X (0 : Fin 5)
        = MvPolynomial.X (0 : Fin 5)
      simp
    have h0 : ((signEquiv K) : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 5) K)
        (MvPolynomial.X (0 : Fin 5) - 1) = MvPolynomial.X (0 : Fin 5) - 1 := by
      rw [signEquiv_coe]
      rw [map_sub, signHom_coe_X, map_one]
      rw [hsf]
    rw [Ideal.map_span, Set.image_singleton, h0]

theorem ASZChartNegIso (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) K ⧸ Work.MotAS.asChartIdeal a b (3 * g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸ Work.MotAS.asChartIdeal a b (2 * g))) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h3g : (3 : K) * g = -(2 * g) := by
    rw [eq_neg_iff_add_eq_zero]
    have h : (3 : K) * g + 2 * g = (5 : K) * g := by ring
    rw [h, h5, zero_mul]
  rw [h3g]
  exact Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
    ((Ideal.quotientEquivAlg (Work.MotAS.asChartIdeal a b (2 * g))
        (Work.MotAS.asChartIdeal a b (-(2 * g))) (signEquiv K)
        (map_signEquiv_asChartIdeal K a b (2 * g)).symm).symm)

end Work.MotC5N3
