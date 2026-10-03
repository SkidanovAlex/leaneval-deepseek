/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twisted Laurent description of `⟨D N ∪ Γ⟩` for `Γ/N ≅ ℤ`

This file sets up the ring-theoretic machinery used in `oreFieldFrac_of_div.lean` to prove
Linnell's Ore field of fractions statement (I4′b) from the division-ring property (I4) alone.

Context: `E` is a `StarRegularEnvelope` for a group `G` (node N5's ambient ring `U(G)`), `φK` a
field embedding, `N ≤ Γ ≤ G` subgroups with `N` normal in `Γ`, `Γ/N ≅ ℤ`, and `s : Γ` an element
whose powers meet every coset of `N` in `Γ`.  Writing

* `R := ⟨D N ∪ gen Γ⟩ ⊆ U(G)` for the subring of the paper (`genSubring`),
* `(gen E s)^j` for the image of `s^j` in `U(G)`,

the file provides

* `laurentSum E φK s c = Σ_i d_i * (gen s)^i` for a finitely supported family `c` of elements of
  `D N` (the "twisted Laurent polynomial" presentation of `R`),
* the fact that the value of `laurentSum` always lies in `R` (`laurentSum_mem_genSubring`),
* the *surjectivity* of the twisted Laurent presentation: every element of `R` is a `laurentSum`
  (`exists_laurentSum_of_mem_genSubring`).

Surjectivity is where the ring structure of the twisted Laurent polynomial ring is genuinely used:
the image of the ring homomorphism `Φ : D N[ℤ] → U(G)`, `single i d ↦ d·(gen s)^i` (built from
Mathlib's `SkewMonoidAlgebra` with the conjugation action of `ℤ` on `D N`) is a subring of `U(G)`
containing `D N` and `gen γ` for every `γ ∈ Γ`; conversely every value of `Φ` lies in `R` because
the powers of `gen s` and the coefficients do.
-/
import Mathlib
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORLinnell.Main
import Submission.Work.ORLinnell.Laurent.existsUnique_laurent_rep
import Submission.Work.ORBridgeLinnell.Countable

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.OreField

open Work.ORVonNeumann Work.ORBridgeLinnell

universe u v

variable {K : Type*} [Field K] {G : Type*} [Group G]

/-- The image in `U(G)` of the `j`-th power of a group element `s`. -/
noncomputable def sPowU (E : StarRegularEnvelope G) (s : G) (j : ℤ) : E.U :=
  (((gen E s) ^ j : E.Uˣ) : E.U)

@[simp]
theorem sPowU_zero (E : StarRegularEnvelope G) (s : G) : sPowU E s 0 = 1 := by
  simp [sPowU]

@[simp]
theorem sPowU_add (E : StarRegularEnvelope G) (s : G) (j k : ℤ) :
    sPowU E s (j + k) = sPowU E s j * sPowU E s k := by
  simp [sPowU, zpow_add]

theorem sPowU_neg_mul (E : StarRegularEnvelope G) (s : G) (j : ℤ) :
    sPowU E s (-j) * sPowU E s j = 1 := by
  rw [← sPowU_add, neg_add_cancel, sPowU_zero]

/-- The monoid homomorphism `ℤ → U(G)ˣ`, `i ↦ (gen s)^i`. -/
noncomputable def unitPow (E : StarRegularEnvelope G) (s : G) : Multiplicative ℤ →* E.Uˣ where
  toFun i := (gen E s) ^ (Multiplicative.toAdd i)
  map_one' := by simp
  map_mul' i j := by
    have h : Multiplicative.toAdd (i * j) = Multiplicative.toAdd i + Multiplicative.toAdd j := rfl
    rw [h, zpow_add]

/-- The conjugation action of `ℤ` on `U(G)` through the powers of `gen s`; the action of
`i : Multiplicative ℤ` is `x ↦ (gen s)^i * x * (gen s)^{-i}`. -/
@[instance_reducible]
noncomputable def conjAction (E : StarRegularEnvelope G) (s : G) :
    MulSemiringAction (Multiplicative ℤ) E.U :=
  MulSemiringAction.compHom E.U
    ((ConjAct.toConjAct : E.Uˣ ≃* ConjAct E.Uˣ).toMonoidHom.comp (unitPow E s))

theorem conjAction_smul_apply (E : StarRegularEnvelope G) (s : G) (j : ℤ) (x : E.U) :
    (letI := conjAction E s; (Multiplicative.ofAdd j) • x)
      = sPowU E s j * x * sPowU E s (-j) := by
  show ConjAct.toConjAct ((gen E s) ^ j) • x = _
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  simp only [sPowU]
  rw [zpow_neg]

/-- Conjugation by an element of `Γ` preserves the division closure `D N` of `K[N]` when `N` is
normal in `Γ`. -/
theorem D_conj_mem_self (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (hN : N ≤ Γ) (hNn : (N.subgroupOf Γ).Normal) (γ : Γ) {x : E.U}
    (hx : x ∈ D E φK N) :
    (gen E (γ : G) : E.U) * x * ↑((gen E (γ : G))⁻¹) ∈ D E φK N := by
  have hmap : N.map (MulAut.conj (γ : G)) = N :=
    Work.ORLinnell.LinnellDatum.map_conj_eq_of_normal hN hNn γ
  rw [← hmap]
  exact D_conj_mem E φK (γ : G) N hx

/-! ## The twisted Laurent presentation of `R` -/

/-- The subring `R = ⟨D N ∪ gen Γ⟩ ≤ U(G)` of the Ore field of fractions statement. -/
noncomputable def genSubring (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (N Γ : Subgroup G) : Subring E.U :=
  Subring.closure (((D E φK N : Subring E.U) : Set E.U) ∪
    Set.range (fun γ : Γ => (gen E (γ : G) : E.U)))

/-- The twisted Laurent sum `Σ_i d_i * (gen s)^i`, for a finitely supported family `d` of elements
of `D N`. -/
noncomputable def laurentSum (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) (c : Multiplicative ℤ →₀ ↥(D E φK N)) : E.U :=
  c.sum (fun i d => (d : E.U) * sPowU E (s : G) (Multiplicative.toAdd i))

@[simp]
theorem laurentSum_single (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) (i : Multiplicative ℤ) (d : ↥(D E φK N)) :
    laurentSum E φK s (Finsupp.single i d)
      = (d : E.U) * sPowU E (s : G) (Multiplicative.toAdd i) := by
  rw [laurentSum, Finsupp.sum_single_index (by simp)]

@[simp]
theorem laurentSum_zero (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) :
    laurentSum E φK s (0 : Multiplicative ℤ →₀ ↥(D E φK N)) = 0 := by
  rw [laurentSum, Finsupp.sum_zero_index]

theorem laurentSum_add (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) (c c' : Multiplicative ℤ →₀ ↥(D E φK N)) :
    laurentSum E φK s (c + c') = laurentSum E φK s c + laurentSum E φK s c' := by
  rw [laurentSum, laurentSum, laurentSum,
    Finsupp.sum_add_index (by simp) (by intro a _ b₁ b₂; simp [add_mul])]

theorem laurentSum_neg (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) (c : Multiplicative ℤ →₀ ↥(D E φK N)) :
    laurentSum E φK s (-c) = -laurentSum E φK s c := by
  have h : (-c : Multiplicative ℤ →₀ ↥(D E φK N)) = 0 - c := by rw [zero_sub]
  rw [h, laurentSum, laurentSum,
    Finsupp.sum_sub_index (by intro a b₁ b₂; simp [sub_mul]), Finsupp.sum_zero_index, zero_sub]

/-- `(gen s)^k` is the image of `s^k`. -/
theorem sPowU_eq_gen (E : StarRegularEnvelope G) {Γ : Subgroup G} (s : Γ) (k : ℤ) :
    sPowU E (s : G) k = (gen E (((s ^ k : Γ)) : G) : E.U) := by
  rw [sPowU]
  have h : ((gen E (s : G)) ^ k : E.Uˣ) = gen E (((s ^ k : Γ)) : G) := by
    rw [← map_zpow]
    exact congrArg (fun z : G => gen E z) (map_zpow (Subgroup.subtype Γ) s k).symm
  rw [h]

/-- `(gen s)^{-k}` is the inverse of the image of `s^k`. -/
theorem sPowU_neg_eq_gen_inv (E : StarRegularEnvelope G) {Γ : Subgroup G} (s : Γ) (k : ℤ) :
    sPowU E (s : G) (-k) = ↑((gen E (((s ^ k : Γ)) : G))⁻¹) := by
  rw [sPowU, ← map_zpow]
  rw [show ((s : G) ^ (-k)) = (((s ^ k : Γ) : G))⁻¹ from by
    rw [← Subgroup.coe_zpow, zpow_neg, Subgroup.coe_inv]]
  rw [map_inv]

/-- Every value of `laurentSum` lies in `R = ⟨D N ∪ gen Γ⟩`. -/
theorem laurentSum_mem_genSubring (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    {N Γ : Subgroup G} (s : Γ) (c : Multiplicative ℤ →₀ ↥(D E φK N)) :
    laurentSum E φK s c ∈ genSubring E φK N Γ := by
  rw [laurentSum, Finsupp.sum]
  refine Subring.sum_mem _ fun i _ => ?_
  refine (genSubring E φK N Γ).mul_mem
    (Subring.subset_closure (Set.mem_union_left _ (c i).2)) ?_
  exact Subring.subset_closure (Set.mem_union_right _ ⟨s ^ (Multiplicative.toAdd i),
    (sPowU_eq_gen E s (Multiplicative.toAdd i)).symm⟩)

/-! ## Surjectivity of the twisted Laurent presentation -/

section Surjective

variable (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
variable {N Γ : Subgroup G}

theorem exists_laurentSum_of_mem_genSubring (hN : N ≤ Γ) (hNn : (N.subgroupOf Γ).Normal)
    (s : Γ) (hs : ∀ h : Γ, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf Γ)
    {x : E.U} (hx : x ∈ genSubring E φK N Γ) :
    ∃ c : Multiplicative ℤ →₀ ↥(D E φK N), laurentSum E φK s c = x := by
  letI : MulSemiringAction (Multiplicative ℤ) E.U := conjAction E (s : G)
  haveI hInv : IsInvariantSubring (Multiplicative ℤ) (D E φK N) := by
    refine ⟨fun i y hy => ?_⟩
    rw [show i = Multiplicative.ofAdd (Multiplicative.toAdd i) from ofAdd_toAdd i,
      conjAction_smul_apply, sPowU_eq_gen E s (Multiplicative.toAdd i),
      sPowU_neg_eq_gen_inv E s (Multiplicative.toAdd i)]
    exact D_conj_mem_self E φK hN hNn (s ^ (Multiplicative.toAdd i)) hy
  let Φ : SkewMonoidAlgebra ↥(D E φK N) (Multiplicative ℤ) →+* E.U :=
    SkewMonoidAlgebra.liftNCRingHom (Subring.subtype (D E φK N))
      ((Units.coeHom E.U).comp (unitPow E (s : G))) (fun {x y} => by
        have hcoe : ((y • x : ↥(D E φK N)) : E.U)
            = sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U)
              * sPowU E (s : G) (-(Multiplicative.toAdd y)) := by
          have h₁ : ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • x : ↥(D E φK N))
              = (y • x : ↥(D E φK N)) := by rw [ofAdd_toAdd]
          rw [← h₁]
          change ((Multiplicative.ofAdd (Multiplicative.toAdd y)) • (x : E.U)) = _
          rw [conjAction_smul_apply]
        show ((y • x : ↥(D E φK N)) : E.U) * sPowU E (s : G) (Multiplicative.toAdd y)
          = sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U)
        rw [hcoe, mul_assoc (sPowU E (s : G) (Multiplicative.toAdd y) * (x : E.U))
          (sPowU E (s : G) (-(Multiplicative.toAdd y))) (sPowU E (s : G) (Multiplicative.toAdd y)),
          sPowU_neg_mul, mul_one])
  have hΦsingle : ∀ (i : Multiplicative ℤ) (d : ↥(D E φK N)),
      Φ (SkewMonoidAlgebra.single i d)
        = (d : E.U) * sPowU E (s : G) (Multiplicative.toAdd i) := by
    intro i d
    exact SkewMonoidAlgebra.liftNC_single _ _ i d
  have hΦof : ∀ c : Multiplicative ℤ →₀ ↥(D E φK N),
      Φ (SkewMonoidAlgebra.ofCoeff c) = laurentSum E φK s c := by
    intro c
    rfl
  have hle : genSubring E φK N Γ ≤ Φ.range := by
    rw [genSubring, Subring.closure_le]
    rintro y (hy | hy)
    · refine ⟨SkewMonoidAlgebra.single 1 ⟨y, hy⟩, ?_⟩
      rw [hΦsingle]
      simp
    · obtain ⟨γ, rfl⟩ := hy
      obtain ⟨j, hj⟩ := hs γ
      set nn : Γ := γ * s ^ (-j) with hnn
      have hmem : (nn : G) ∈ N := by
        rw [hnn]
        exact Subgroup.mem_subgroupOf.mp hj
      have hγ : nn * s ^ j = γ := by
        rw [hnn]
        rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      have hval : (gen E (γ : G) : E.U)
          = (gen E (nn : G) : E.U) * sPowU E (s : G) j := by
        have hγ' : (γ : G) = (nn : G) * (s : G) ^ j := by
          rw [← hγ]; push_cast; rfl
        rw [hγ', map_mul, map_zpow]
        simp [sPowU]
      refine ⟨SkewMonoidAlgebra.single 1 ⟨(gen E (nn : G) : E.U), gen_mem_D' E φK hmem⟩
        * SkewMonoidAlgebra.single (Multiplicative.ofAdd j) 1, ?_⟩
      rw [map_mul, hΦsingle, hΦsingle]
      simpa using hval.symm
  have hge : Φ.range ≤ genSubring E φK N Γ := by
    rintro y ⟨z, rfl⟩
    rw [show Φ z = laurentSum E φK s z.coeff from rfl]
    exact laurentSum_mem_genSubring E φK s z.coeff
  have hrange : Φ.range = genSubring E φK N Γ := le_antisymm hge hle
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp (by rw [hrange]; exact hx)
  exact ⟨z.coeff, hz⟩

end Surjective

end Work.ORFinal.OreField
