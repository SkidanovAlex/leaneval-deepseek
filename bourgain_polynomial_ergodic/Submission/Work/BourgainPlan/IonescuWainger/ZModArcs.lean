import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep

/-!
# The finite cyclic group form of the Ionescu–Wainger major arcs

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
§4 (Lemma `ortho`, Theorem `ortho-apply-arith`); see `REFS/Tao_2008.05066_IonescuWainger.tex` and
`Submission/Work/BourgainPlan/IonescuWainger/PLAN.md`.

The major arcs of `ArcDefs.lean` all consist of rational points `a/Q_A` with `Q_A = ∏_{q ∈ A} q`
dividing the common denominator `Q_S = ∏_{q ∈ S} q`.  Their *arithmetic* (Lemma `ortho`(i)(ii)(iii))
therefore lives on the finite cyclic group `ZMod Q_S`: the point `a/Q_A` is the image of the element
`a · (Q_S / Q_A) ∈ ZMod Q_S`, and the Fourier-theoretic orthogonality statements of Tao's §4 become
the *finite* character orthogonality `Σ_{y ∈ ZMod Q} e(α y / Q) = Q δ_{α,0}`.

This file records that dictionary:

* `iwChar α` — the character `y ↦ e(α y / Q)` of `ZMod Q`, with its algebra (multiplicativity,
  unit modulus, `star (iwChar α y) = iwChar (-α) y`) and the **orthogonality identity**
  `Σ_y iwChar α y * star (iwChar β y) = Q δ_{α,β}`;
* `arcLift Q A a` — the lift of the arc point `a/Q_A` to `ZMod Q` (when `Q_A ∣ Q`), and the
  bridge `arcLift_arcPt` identifying it with `a/Q_A` in `𝕋 = AddCircle 1`; consequently two lifts
  coincide in `ZMod Q` exactly when the corresponding arc points coincide in `𝕋`;
* `sigmaAQ`, `sigmaSubAQ`, `sigmaLeQ` — Tao's `Σ_A`, `Σ_{⊆ A}`, `Σ_{≤ k}` transported to `ZMod Q`;
* `expSum` — the exponential sum `y ↦ Σ_α c_α e(α y / Q)` with which the "arithmetic limit" form of
  `ortho-apply` is phrased.

Everything here is elementary finite-group Fourier analysis; the deep arithmetic (Tao's `ortho`) is
stated separately on top of this vocabulary.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

variable {Q : ℕ}

/-! ## The characters of `ZMod Q` -/

section Characters

variable [NeZero Q]

/-- The additive character `y ↦ e(α y / Q)` of the finite cyclic group `ZMod Q`. -/
noncomputable def iwChar (α : ZMod Q) : ZMod Q → ℂ := fun y => ZMod.stdAddChar (α * y)

@[simp]
lemma iwChar_apply (α y : ZMod Q) : iwChar α y = ZMod.stdAddChar (α * y) := rfl

/-- The explicit exponential form of `iwChar`. -/
lemma iwChar_eq_exp (α y : ZMod Q) :
    iwChar α y = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((α * y).val : ℂ) / (Q : ℂ)) := by
  rw [iwChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- `iwChar` is multiplicative in the frequency. -/
lemma iwChar_add_freq (α β y : ZMod Q) : iwChar (α + β) y = iwChar α y * iwChar β y := by
  rw [iwChar_apply, iwChar_apply, iwChar_apply, add_mul, AddChar.map_add_eq_mul]

/-- `iwChar` is multiplicative in the variable. -/
lemma iwChar_mul_add (α y z : ZMod Q) : iwChar α (y + z) = iwChar α y * iwChar α z := by
  rw [iwChar_apply, iwChar_apply, iwChar_apply, mul_add, AddChar.map_add_eq_mul]

/-- The character of frequency `0` is trivial. -/
lemma iwChar_zero_freq (y : ZMod Q) : iwChar 0 y = 1 := by
  rw [iwChar_apply, zero_mul, AddChar.map_zero_eq_one]

/-- Characters are unit modulus. -/
lemma norm_iwChar (α y : ZMod Q) : ‖iwChar α y‖ = 1 := by
  rw [iwChar_eq_exp]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((α * y).val : ℂ) / (Q : ℂ)
      = (((2 * Real.pi * ((α * y).val : ℝ)) / Q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma iwChar_ne_zero (α y : ZMod Q) : iwChar α y ≠ 0 := by
  intro h
  have := norm_iwChar α y
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

lemma iwChar_neg_freq (α y : ZMod Q) : iwChar (-α) y = (iwChar α y)⁻¹ := by
  rw [iwChar_apply, iwChar_apply, neg_mul, AddChar.map_neg_eq_inv]

/-- Complex conjugation of a character is the character of the opposite frequency. -/
lemma star_iwChar (α y : ZMod Q) : star (iwChar α y) = iwChar (-α) y :=
  (Complex.inv_eq_conj (norm_iwChar α y)).symm.trans (iwChar_neg_freq α y).symm

/-- The character of frequency `α ≠ 0` is non-trivial. -/
lemma iwChar_one_ne_one {α : ZMod Q} (hα : α ≠ 0) : iwChar α 1 ≠ 1 := by
  rw [iwChar_apply, mul_one, ZMod.stdAddChar_apply]
  intro h
  have hC : ZMod.toCircle α = 1 := Subtype.coe_injective h
  have h0 : ZMod.toCircle α = ZMod.toCircle (0 : ZMod Q) := by
    rw [hC, AddChar.map_zero_eq_one]
  have h1 : ZMod.toAddCircle α = ZMod.toAddCircle (0 : ZMod Q) := by
    apply AddCircle.injective_toCircle (T := (1:ℝ)) one_ne_zero
    exact h0
  exact hα (ZMod.toAddCircle_injective Q h1)

/-- **Character orthogonality on `ZMod Q`**: the mean of a character vanishes unless it is
trivial. -/
lemma sum_iwChar (α : ZMod Q) :
    ∑ y : ZMod Q, iwChar α y = if α = 0 then (Q : ℂ) else 0 := by
  classical
  by_cases hα : α = 0
  · subst hα
    simp [iwChar_apply, ZMod.card]
  · rw [if_neg hα]
    have hreindex : (∑ y : ZMod Q, iwChar α (y + 1)) = ∑ y : ZMod Q, iwChar α y :=
      Fintype.sum_equiv (Equiv.addRight (1 : ZMod Q)) _ _ (by intro y; simp)
    have hfix : (∑ y : ZMod Q, iwChar α y) = iwChar α 1 * ∑ y : ZMod Q, iwChar α y := by
      rw [Finset.mul_sum, ← hreindex]
      exact Finset.sum_congr rfl (fun y _ => (iwChar_mul_add α y 1).trans (mul_comm _ _))
    have h2 : (1 - iwChar α 1) * (∑ y : ZMod Q, iwChar α y) = 0 := by
      rw [show (1 - iwChar α 1) * (∑ y : ZMod Q, iwChar α y)
          = (∑ y : ZMod Q, iwChar α y) - iwChar α 1 * (∑ y : ZMod Q, iwChar α y) by
            rw [sub_mul, one_mul]]
      exact sub_eq_zero.mpr hfix
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm (iwChar_one_ne_one hα)
    · exact h

/-- **The orthogonality pairing of characters**: `Σ_y e(α y / Q) conj (e(β y / Q)) = Q δ_{α,β}`. -/
lemma sum_iwChar_mul_star (α β : ZMod Q) :
    ∑ y : ZMod Q, iwChar α y * star (iwChar β y) = if α = β then (Q : ℂ) else 0 := by
  have hpt : ∀ y : ZMod Q, iwChar α y * star (iwChar β y) = iwChar (α - β) y := by
    intro y
    rw [star_iwChar, ← iwChar_add_freq, sub_eq_add_neg]
  simp only [hpt]
  rw [sum_iwChar]
  by_cases h : α = β
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (sub_eq_zero.mp h'))]

end Characters

/-! ## The lift of the arc points to `ZMod Q` -/

/-- Two rational points with a common denominator agree in `𝕋` exactly when their numerators are
congruent modulo the denominator. -/
lemma arcPt_eq_arcPt_iff_dvd (hQ : Q ≠ 0) (x y : ℤ) :
    arcPt Q x = arcPt Q y ↔ (Q : ℤ) ∣ (x - y) := by
  have hsub : arcPt Q (x - y) = arcPt Q x - arcPt Q y := map_sub (arcPtHom Q) x y
  rw [← sub_eq_zero, ← hsub, arcPt_eq_zero_iff_dvd hQ]

/-- The integer points of `ZMod Q` and of `𝕋 = AddCircle 1` agree through `x ↦ x/Q`. -/
lemma intCast_zmod_eq_iff_arcPt (hQ : Q ≠ 0) (x y : ℤ) :
    ((x : ZMod Q) = (y : ZMod Q)) ↔ arcPt Q x = arcPt Q y := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd, arcPt_eq_arcPt_iff_dvd hQ,
    show y - x = -(x - y) by ring, dvd_neg]

/-- The lift of the arc point `a / Q_A` to `ZMod Q`, for `Q_A ∣ Q`: the element
`a · (Q / Q_A)`. -/
def arcLift (Q : ℕ) (A : Finset ℕ) (a : ℤ) : ZMod Q := (a * ((Q / QA A : ℕ) : ℤ) : ZMod Q)

/-- **The bridge between the lift and the arc point of `ArcDefs.lean`.**  When `Q_A ∣ Q`, the lift
`arcLift Q A a ∈ ZMod Q` and the arc point `a/Q_A ∈ 𝕋` correspond through `x ↦ x/Q`. -/
lemma arcLift_arcPt {A : Finset ℕ} (hQA : QA A ∣ Q) (hQ : Q ≠ 0) (a : ℤ) :
    arcPt Q (a * ((Q / QA A : ℕ) : ℤ)) = arcPt (QA A) a :=
  (arcPt_commonDenom (Nat.pos_of_dvd_of_pos hQA (Nat.pos_of_ne_zero hQ))
    (Nat.pos_of_ne_zero hQ) hQA a).symm

/-- The lift is injective precisely modulo the identification of the arc points. -/
lemma arcLift_eq_iff {A : Finset ℕ} (hQA : QA A ∣ Q) (hQ : Q ≠ 0) (a b : ℤ) :
    arcLift Q A a = arcLift Q A b ↔ arcPt (QA A) a = arcPt (QA A) b := by
  simp only [arcLift, ← Int.cast_mul]
  rw [intCast_zmod_eq_iff_arcPt hQ, arcLift_arcPt hQA hQ, arcLift_arcPt hQA hQ]

/-- Tao's `Σ_A` (the points of *exact* denominator `Q_A`), lifted to `ZMod Q`. -/
noncomputable def sigmaAQ (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  ((Finset.range (QA A)).filter (fun a => Nat.Coprime a (QA A))).image
    (fun a : ℕ => arcLift Q A (a : ℤ))

/-- Tao's `Σ_{⊆ A} = 𝕋[Q_A]`, lifted to `ZMod Q`. -/
noncomputable def sigmaSubAQ (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  (Finset.range (QA A)).image (fun a : ℕ => arcLift Q A (a : ℤ))

/-- **Tao's stratum `Σ_A`** (arXiv:2008.05066, Definition `major-arc`): the points of the
subgroup `𝕋[Q_A]` that do **not** lie in any strictly smaller subgroup `𝕋[Q_B]`, `B ⊊ A`.

This is the definition that makes the strata a *partition* of the major arc set,
`Σ_{≤ k} = ⨆_{A ∈ binom(S,≤k)} Σ_A`, which is what Tao's `ortho-apply`(i) uses (every frequency of
`Σ_{≤k}` must be seen by the cluster decomposition).  It is **strictly larger** than `sigmaAQ Q A`
(the points of *exact* denominator `Q_A`, i.e. `a/Q_A` with `gcd(a, Q_A) = 1`): whenever `Q_A` has a
divisor which is not of the form `Q_B` for a subset `B ⊆ A`, the corresponding torsion points
belong to `Σ_A` in Tao's sense but not to `sigmaAQ Q A`.  Example: `S = {4}`, `A = {4}` — then
`𝕋[Q_A] = ZMod 4` and the only proper subset is `∅` with `Q_∅ = 1`, so `Σ_{{4}} = {1/4, 1/2, 3/4}`
contains `1/2`, while `sigmaAQ 4 {4} = {1/4, 3/4}` misses it.  (A frequency such as `1/2` is
invisible to the clusters built from `sigmaAQ`, which is why the downstream statements must use the
strata below.) -/
noncomputable def sigmaStrataQ (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  (sigmaSubAQ Q A).filter (fun x => ∀ B ∈ A.powerset.erase A, x ∉ sigmaSubAQ Q B)

/-- Tao's `Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤k−|A₀|)} Σ_A`, lifted to `ZMod Q` (strata version). -/
noncomputable def sigmaStrataCompQ (Q : ℕ) (S : Finset ℕ) (k : ℕ) (A₀ : Finset ℕ) :
    Finset (ZMod Q) :=
  ((S \ A₀).powerset.filter (fun A => A.card ≤ k - A₀.card)).biUnion
    (fun A => sigmaStrataQ Q A)

/-- The finite set of `A₀ ⊆ S`, `A₀.card ≤ k`, for which `β` has a decomposition `β = α₀ + α` with
`α₀ ∈ Σ_{A₀}` and `α ∈ Σ_{(A₀)}` (strata version); Tao's counting bound is that this set has at
most `2 ^ k` elements. -/
noncomputable def sigmaStrataDecompSetQ (Q : ℕ) (S : Finset ℕ) (k : ℕ) (β : ZMod Q) :
    Finset (Finset ℕ) :=
  (S.powerset.filter (fun A₀ => A₀.card ≤ k)).filter
    (fun A₀ => ∃ α₀ ∈ sigmaStrataQ Q A₀, ∃ α ∈ sigmaStrataCompQ Q S k A₀, α₀ + α = β)

/-- Tao's `Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤k−|A₀|)} Σ_A`, lifted to `ZMod Q`. -/
noncomputable def sigmaCompQ (Q : ℕ) (S : Finset ℕ) (k : ℕ) (A₀ : Finset ℕ) :
    Finset (ZMod Q) :=
  ((S \ A₀).powerset.filter (fun A => A.card ≤ k - A₀.card)).biUnion (fun A => sigmaAQ Q A)

/-- Tao's `Σ_{≤ k}`, lifted to `ZMod Q`. -/
noncomputable def sigmaLeQ (Q : ℕ) (S : Finset ℕ) (k : ℕ) : Finset (ZMod Q) :=
  (S.powerset.filter (fun A => A.card ≤ k)).biUnion (fun A => sigmaSubAQ Q A)

/-- The finite set of `A₀ ⊆ S` with `A₀.card ≤ k` for which the point `β ∈ ZMod Q` has a
decomposition `β = α₀ + α` with `α₀ ∈ Σ_{A₀}` and `α ∈ Σ_{(A₀)}`; Tao's counting bound
(`ortho-apply`(i)) is that this set has at most `2 ^ k` elements. -/
noncomputable def sigmaCompDecompSetQ (Q : ℕ) (S : Finset ℕ) (k : ℕ) (β : ZMod Q) :
    Finset (Finset ℕ) :=
  (S.powerset.filter (fun A₀ => A₀.card ≤ k)).filter
    (fun A₀ => ∃ α₀ ∈ sigmaAQ Q A₀, ∃ α ∈ sigmaCompQ Q S k A₀, α₀ + α = β)

section ExponentialSums

variable [NeZero Q]

/-- The exponential sum `y ↦ Σ_α c_α e(α y / Q)` over `ZMod Q` with coefficient function `c`. -/
noncomputable def expSum (c : ZMod Q → ℂ) (y : ZMod Q) : ℂ := ∑ α, c α * iwChar α y

/-- The **cluster sum** `y ↦ Σ_γ c_γ e((α + γ) y / Q)`: the exponential sum whose frequencies lie
in the translate `α + supp c` of the frequency set of `c`.  In Tao's `ortho`(iii) and
`ortho-apply`, `α` runs over the petal set `Σ_{Aᵢ \ A₀}` and `c` has support in the core set
`Σ_{A₀}`. -/
noncomputable def clusterSum (c : ZMod Q → ℂ) (α : ZMod Q) (y : ZMod Q) : ℂ :=
  ∑ γ, c γ * iwChar (α + γ) y

/-- The **Fourier coefficient** of `F : ZMod Q → ℂ` at the frequency `β`:
`Q⁻¹ Σ_y F y · conj (e(β y / Q))`. -/
noncomputable def dftCoeff (F : ZMod Q → ℂ) (β : ZMod Q) : ℂ :=
  (1 / (Q : ℂ)) * ∑ y : ZMod Q, F y * star (iwChar β y)

/-- The **Fourier projection** of `F` onto a finite set `T` of frequencies:
`y ↦ Σ_{β ∈ T} ĉ_F(β) e(β y / Q)`.  This is Tao's `Op_{1_Σ}` on the compact group `Ẑ`
(equivalently on `ZMod Q`), and `proj (sigmaLeQ Q S k)` is the Ionescu–Wainger projection of
`ortho-apply`(arith) (x3). -/
noncomputable def proj (T : Finset (ZMod Q)) (F : ZMod Q → ℂ) (y : ZMod Q) : ℂ :=
  ∑ β ∈ T, dftCoeff F β * iwChar β y

/-- The projection is the exponential sum of the Fourier coefficients. -/
lemma proj_eq_sum (T : Finset (ZMod Q)) (F : ZMod Q → ℂ) (y : ZMod Q) :
    proj T F y = ∑ β ∈ T, dftCoeff F β * iwChar β y := rfl

/-- A Fourier coefficient of an exponential sum is the corresponding coefficient. -/
lemma dftCoeff_expSum (c : ZMod Q → ℂ) (β : ZMod Q) :
    dftCoeff (expSum c) β = c β := by
  classical
  have hQ : ((Q : ℂ)) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hexp : (∑ y : ZMod Q, expSum c y * star (iwChar β y))
      = ∑ α : ZMod Q, c α * (∑ y : ZMod Q, iwChar α y * star (iwChar β y)) := by
    simp only [expSum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [dftCoeff, hexp]
  have hinner : ∀ α : ZMod Q, (∑ y : ZMod Q, iwChar α y * star (iwChar β y))
      = if α = β then (Q : ℂ) else 0 := fun α => sum_iwChar_mul_star α β
  simp only [hinner]
  have hsingle : (∑ x : ZMod Q, c x * (if x = β then (Q : ℂ) else 0)) = c β * (Q : ℂ) := by
    rw [Finset.sum_eq_single β]
    · simp
    · intro x _ hx
      rw [if_neg hx, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ β) h
  rw [hsingle, mul_comm (c β), ← mul_assoc, one_div, inv_mul_cancel₀ hQ, one_mul]

/-- The projection onto `T` of an exponential sum with coefficients supported in `T` is that
exponential sum. -/
lemma proj_expSum (T : Finset (ZMod Q)) (c : ZMod Q → ℂ) (y : ZMod Q) :
    proj T (expSum c) y = ∑ β ∈ T, c β * iwChar β y := by
  simp only [proj_eq_sum, dftCoeff_expSum]

end ExponentialSums

end Work.BourgainPlan.IonescuWainger
