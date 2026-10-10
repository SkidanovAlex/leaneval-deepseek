import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4MonoOrderU`

There is a monomial order (at an arbitrary universe for its `syn` type) on the four chart
coordinates `y₁,y₂,y₃,y₄` of the twisted Klein chart for which the five chart quadrics
`zpgQ a b h k` have leading coefficients which are units and prescribed leading monomials
`y₁y₂, y₂², y₁y₂, y₁², y₃²`.

The order is the weighted-lexicographic order with weights `(10,10,8,1)` (constructed from
scratch, since Mathlib only provides the pure lex and the degree-lex orders), lifted to an
arbitrary `syn`-universe via `ULift`.  All statements about `degree` and `leadingCoeff` are
proved for an arbitrary monomial order refining that weight order, so that the lifted order
inherits them.
-/

set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial Finsupp
open scoped MonomialOrder

universe u

/-! ## 1. The weighted-lexicographic order (syn at universe `0`) -/

/-- The weight vector `y₁ ↦ 10`, `y₂ ↦ 10`, `y₃ ↦ 8`, `y₄ ↦ 1`. -/
def zmuWt : Fin 4 → ℕ := ![10, 10, 8, 1]

/-- The exponent monoid `Fin 4 →₀ ℕ`, equipped with the weighted-lex order. -/
def Zmu := Fin 4 →₀ ℕ

def ofZmu : Zmu ≃ (Fin 4 →₀ ℕ) := Equiv.refl _
def toZmu : (Fin 4 →₀ ℕ) ≃ Zmu := Equiv.refl _

noncomputable instance : AddCommMonoid Zmu := ofZmu.addCommMonoid

theorem ofZmu_add (x y : Zmu) : ofZmu (x + y) = ofZmu x + ofZmu y := rfl

/-- Weighted lexicographic comparison: total `zmuWt`-weight first, then the lexicographic order. -/
noncomputable def zmuEmb (f : Fin 4 →₀ ℕ) : ℕ ×ₗ Lex (Fin 4 →₀ ℕ) :=
  toLex ((Finsupp.weight zmuWt f : ℕ), toLex f)

noncomputable def zmuLift (x : Zmu) : ℕ ×ₗ Lex (Fin 4 →₀ ℕ) := zmuEmb (ofZmu x)

theorem zmuEmb_injective : Function.Injective zmuEmb := by
  intro f g hh
  have h2 : ((Finsupp.weight zmuWt f : ℕ), toLex f) = ((Finsupp.weight zmuWt g : ℕ), toLex g) :=
    toLex_inj.mp hh
  exact toLex_inj.mp (congrArg Prod.snd h2)

theorem zmuLift_injective : Function.Injective zmuLift :=
  fun _ _ h => ofZmu.injective (zmuEmb_injective h)

noncomputable instance : LinearOrder Zmu := LinearOrder.lift' zmuLift zmuLift_injective

theorem zmuEmb_add (f g : Fin 4 →₀ ℕ) : zmuEmb (f + g) = zmuEmb f + zmuEmb g := by
  show toLex ((Finsupp.weight zmuWt (f + g) : ℕ), toLex (f + g))
      = toLex ((Finsupp.weight zmuWt f : ℕ), toLex f)
        + toLex ((Finsupp.weight zmuWt g : ℕ), toLex g)
  rw [map_add]
  rfl

theorem zmuLift_add (x y : Zmu) : zmuLift (x + y) = zmuLift x + zmuLift y := by
  unfold zmuLift
  rw [ofZmu_add, zmuEmb_add]

noncomputable instance : IsOrderedAddMonoid Zmu where
  add_le_add_left a b hab c := by
    show zmuLift (a + c) ≤ zmuLift (b + c)
    rw [zmuLift_add, zmuLift_add]
    exact add_le_add hab le_rfl
  add_le_add_right a b hab c := by
    show zmuLift (c + a) ≤ zmuLift (c + b)
    rw [zmuLift_add, zmuLift_add]
    exact add_le_add le_rfl hab

/-- The weighted-lexicographic monomial order on the four chart coordinates, `syn` at
universe `0`. -/
noncomputable def zmuMO0 : MonomialOrder.{0,0} (Fin 4) where
  syn := Zmu
  addCommMonoidSyn := inferInstance
  linearOrderSyn := inferInstance
  isOrderedAddMonoid_syn := inferInstance
  wellFoundedLT_syn := InvImage.wf zmuLift (inferInstance : WellFoundedLT (ℕ ×ₗ Lex (Fin 4 →₀ ℕ)))
  toSyn := AddEquiv.refl (Fin 4 →₀ ℕ)
  toSyn_monotone := by
    intro f g h
    have hw : Finsupp.weight zmuWt f ≤ Finsupp.weight zmuWt g := by
      have hfg : f + (g - f) = g := by
        ext i
        rw [Finsupp.add_apply, Finsupp.tsub_apply]
        exact Nat.add_sub_cancel' (h i)
      calc Finsupp.weight zmuWt f
            ≤ Finsupp.weight zmuWt f + Finsupp.weight zmuWt (g - f) := Nat.le_add_right _ _
        _ = Finsupp.weight zmuWt (f + (g - f)) := (map_add _ _ _).symm
        _ = Finsupp.weight zmuWt g := by rw [hfg]
    show zmuLift (AddEquiv.refl (Fin 4 →₀ ℕ) f) ≤ zmuLift (AddEquiv.refl (Fin 4 →₀ ℕ) g)
    unfold zmuLift zmuEmb
    rw [Prod.Lex.toLex_le_toLex]
    rcases lt_or_eq_of_le hw with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, Finsupp.toLex_monotone h⟩

/-- A monomial of strictly larger weight is strictly larger in `zmuMO0`. -/
theorem zmuMO0_lt_of_weight_lt {c d : Fin 4 →₀ ℕ}
    (h : Finsupp.weight zmuWt c < Finsupp.weight zmuWt d) : c ≺[zmuMO0] d := by
  show zmuLift (zmuMO0.toSyn c) < zmuLift (zmuMO0.toSyn d)
  unfold zmuLift zmuEmb
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-! ## 2. Lifting the `syn` universe -/

/-- The complement of `MonomialOrder`, with the `syn` type put in a higher universe. -/
noncomputable def zmuU (m : MonomialOrder.{0,0} (Fin 4)) : MonomialOrder.{0,u} (Fin 4) where
  syn := ULift.{u,0} m.syn
  addCommMonoidSyn := inferInstance
  linearOrderSyn := inferInstance
  isOrderedAddMonoid_syn :=
    { add_le_add_left := fun a b hab c => by
        change (a + c).down ≤ (b + c).down
        exact add_le_add_left (show a.down ≤ b.down from hab) c.down }
  toSyn := m.toSyn.trans AddEquiv.ulift.symm
  toSyn_monotone := fun a b h => ULift.up_le.mpr (m.toSyn_monotone h)
  wellFoundedLT_syn := inferInstance

theorem zmuU_lt_iff (m : MonomialOrder.{0,0} (Fin 4)) (c d : Fin 4 →₀ ℕ) :
    c ≺[zmuU m] d ↔ c ≺[m] d := by
  have h1 : (zmuU m).toSyn c = ULift.up (m.toSyn c) := rfl
  have h2 : (zmuU m).toSyn d = ULift.up (m.toSyn d) := rfl
  rw [h1, h2]
  exact ULift.up_lt

/-- The monomial order of the main theorem: the weighted-lex order, lifted to an arbitrary
`syn`-universe. -/
noncomputable def zmuMOU : MonomialOrder.{0,u} (Fin 4) := zmuU zmuMO0

theorem zmuMOU_lt_iff (c d : Fin 4 →₀ ℕ) : c ≺[zmuMOU.{u}] d ↔ c ≺[zmuMO0] d :=
  zmuU_lt_iff.{u} zmuMO0 c d

/-- A monomial of strictly larger weight is strictly larger in `zmuMOU`. -/
theorem zmuMOU_lt_of_weight_lt {c d : Fin 4 →₀ ℕ}
    (h : Finsupp.weight zmuWt c < Finsupp.weight zmuWt d) : c ≺[zmuMOU.{u}] d :=
  (zmuMOU_lt_iff.{u} c d).mpr (zmuMO0_lt_of_weight_lt h)

/-! ## 3. The auxiliary predicate `ZmuWtLt` -/

/-- Every monomial of `r` has `zmuWt`-weight strictly less than `W`. -/
def ZmuWtLt {K : Type} [CommSemiring K] (r : MvPolynomial (Fin 4) K) (W : ℕ) : Prop :=
  ∀ x ∈ r.support, Finsupp.weight zmuWt x < W

theorem ZmuWtLt.monomial {K : Type} [CommSemiring K] {m : Fin 4 →₀ ℕ} {x : K} {W : ℕ}
    (h : Finsupp.weight zmuWt m < W) : ZmuWtLt (monomial m x : MvPolynomial (Fin 4) K) W := by
  classical
  intro c hc
  by_cases hx : x = 0
  · rw [hx, MvPolynomial.monomial_zero] at hc
    simp at hc
  · rw [MvPolynomial.support_monomial, if_neg hx, Finset.mem_singleton] at hc
    rw [hc]; exact h

theorem ZmuWtLt.add {K : Type} [CommSemiring K] {p q : MvPolynomial (Fin 4) K} {W : ℕ}
    (hp : ZmuWtLt p W) (hq : ZmuWtLt q W) : ZmuWtLt (p + q) W := by
  classical
  intro c hc
  rcases Finset.mem_union.mp (MvPolynomial.support_add hc) with h | h
  · exact hp c h
  · exact hq c h

/-! ## 4. `degree` from a split off a strictly lighter remainder -/

/-- If `f = monomial d c + r` with `c ≠ 0` and all monomials of `r` strictly lighter than `d`,
then `d` is the `m`-degree of `f`, for any monomial order `m` refining the weight order. -/
theorem zmu_degree_eq_of_split {K : Type} [CommSemiring K] {m : MonomialOrder (Fin 4)}
    (hm : ∀ c d : Fin 4 →₀ ℕ, Finsupp.weight zmuWt c < Finsupp.weight zmuWt d → c ≺[m] d)
    {f r : MvPolynomial (Fin 4) K} {d : Fin 4 →₀ ℕ} (c : K) (W : ℕ)
    (hc : c ≠ 0) (hf : f = monomial d c + r) (hdW : Finsupp.weight zmuWt d = W)
    (hr : ZmuWtLt r W) : m.degree f = d := by
  classical
  have hr_d : r.coeff d = 0 := by
    by_contra h
    exact absurd (hr d (MvPolynomial.mem_support_iff.mpr h)) (by rw [hdW]; exact lt_irrefl _)
  have hcoeff : f.coeff d ≠ 0 := by
    rw [hf, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, if_pos rfl, hr_d, add_zero]
    exact hc
  have hmem : d ∈ f.support := MvPolynomial.mem_support_iff.mpr hcoeff
  apply m.toSyn.injective
  apply le_antisymm
  · refine MonomialOrder.degree_le_iff.mpr (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; exact le_refl _
    · have hxr : x ∈ r.support := by
        have h1 : x ∈ (monomial d c + r).support := by rw [← hf]; exact hx
        rcases Finset.mem_union.mp (MvPolynomial.support_add h1) with h2 | h2
        · rw [MvPolynomial.support_monomial, if_neg hc, Finset.mem_singleton] at h2
          exact absurd h2 hxd
        · exact h2
      exact (hm x d (by rw [hdW]; exact hr x hxr)).le
  · exact MonomialOrder.le_degree hmem

/-- The leading coefficient of a split `monomial d c + r` (with `c ≠ 0` and `r` strictly
lighter) is nonzero, hence a unit in a field. -/
theorem zmu_ne_zero_of_split {K : Type} [CommSemiring K]
    {f r : MvPolynomial (Fin 4) K} {d : Fin 4 →₀ ℕ} (c : K) (W : ℕ)
    (hc : c ≠ 0) (hf : f = monomial d c + r) (hdW : Finsupp.weight zmuWt d = W)
    (hr : ZmuWtLt r W) : f ≠ 0 := by
  classical
  have hr_d : r.coeff d = 0 := by
    by_contra h
    exact absurd (hr d (MvPolynomial.mem_support_iff.mpr h)) (by rw [hdW]; exact lt_irrefl _)
  have hcoeff : f.coeff d ≠ 0 := by
    rw [hf, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, if_pos rfl, hr_d, add_zero]
    exact hc
  intro h0
  exact hcoeff (by rw [h0]; simp)

/-! ## 5. Monomial conversions and the five splits -/

section Conversions

variable {K : Type} [CommSemiring K]

theorem zmuC_mul_X_mul_X (x : K) (i j : Fin 4) :
    (C x * X i * X j : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single i 1 + Finsupp.single j 1) x := by
  rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  simp

end Conversions

section ConversionsNeg

variable {K : Type} [CommRing K]

theorem zmu_neg_C_mul_X_pow (x : K) (i : Fin 4) (n : ℕ) :
    (-(C x) * X i ^ n : MvPolynomial (Fin 4) K) = monomial (Finsupp.single i n) (-x) := by
  have h : (-(C x) : MvPolynomial (Fin 4) K) = C (-x) := by simp
  rw [h, MvPolynomial.C_mul_X_pow_eq_monomial]

end ConversionsNeg

section Splits

variable {K : Type} [Field K] (a b h : K)

theorem zmuQ_split_0 :
    zpgQ a b h 0 = monomial (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1) (a^(2:ℕ)*h^(2:ℕ))
      + (monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))
          + C (-(a*b))) := by
  have h1 : zpgQ a b h 0
      = - C (a*b) + C (a^(2:ℕ)*h^(2:ℕ)) * X 1 * X 2 - C (b^(2:ℕ)*h^(2:ℕ)) * X 0 * X 3 := by
    simp only [zpgQ, Matrix.cons_val]
  have h2 : (C (a^(2:ℕ)*h^(2:ℕ)) * X 1 * X 2 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 1 1 + Finsupp.single 2 1) (a^(2:ℕ)*h^(2:ℕ)) :=
    zmuC_mul_X_mul_X _ 1 2
  have h3 : (C (b^(2:ℕ)*h^(2:ℕ)) * X 0 * X 3 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 0 1 + Finsupp.single 3 1) (b^(2:ℕ)*h^(2:ℕ)) :=
    zmuC_mul_X_mul_X _ 0 3
  rw [h1, h2, h3,
    show (monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))
        : MvPolynomial (Fin 4) K)
        = - monomial (Finsupp.single 0 1 + Finsupp.single 3 1) (b^(2:ℕ)*h^(2:ℕ)) from by simp,
    show (C (-(a*b)) : MvPolynomial (Fin 4) K) = - C (a*b) from by simp]
  first | refl_ring1 | ring

theorem zmuQ_split_1 :
    zpgQ a b h 1 = monomial (Finsupp.single (1 : Fin 4) 2) (-(a*b))
      + (monomial (Finsupp.single (3 : Fin 4) 1) (a^(2:ℕ))
          + monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1) (-(b^(2:ℕ)))) := by
  have h1 : zpgQ a b h 1
      = - C (a*b) * X 1 ^(2:ℕ) + C (a^(2:ℕ)) * X 3 - C (b^(2:ℕ)) * X 0 * X 2 := by
    simp only [zpgQ, Matrix.cons_val]
  have h2 : (-(C (a*b)) * X 1 ^(2:ℕ) : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 1 2) (-(a*b)) := zmu_neg_C_mul_X_pow (K := K) _ 1 2
  have h3 : (C (a^(2:ℕ)) * X 3 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 3 1) (a^(2:ℕ)) := MvPolynomial.C_mul_X_eq_monomial
  have h4 : (C (b^(2:ℕ)) * X 0 * X 2 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 0 1 + Finsupp.single 2 1) (b^(2:ℕ)) := zmuC_mul_X_mul_X _ 0 2
  rw [h1, h2, h3, h4,
    show (monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1) (-(b^(2:ℕ)))
        : MvPolynomial (Fin 4) K)
        = - monomial (Finsupp.single 0 1 + Finsupp.single 2 1) (b^(2:ℕ)) from by simp]
  first | refl_ring1 | ring

theorem zmuQ_split_2 :
    zpgQ a b h 2 = monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 1 1) (a^(2:ℕ))
      + (monomial (Finsupp.single (3 : Fin 4) 2) (-(a*b*h^(2:ℕ)))
          + monomial (Finsupp.single (2 : Fin 4) 1) (-(b^(2:ℕ)))) := by
  have h1 : zpgQ a b h 2
      = - C (a*b*h^(2:ℕ)) * X 3 ^(2:ℕ) + C (a^(2:ℕ)) * X 0 * X 1 - C (b^(2:ℕ)) * X 2 := by
    simp only [zpgQ, Matrix.cons_val]
  have h2 : (-(C (a*b*h^(2:ℕ))) * X 3 ^(2:ℕ) : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 3 2) (-(a*b*h^(2:ℕ))) := zmu_neg_C_mul_X_pow (K := K) _ 3 2
  have h3 : (C (a^(2:ℕ)) * X 0 * X 1 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (a^(2:ℕ)) := zmuC_mul_X_mul_X _ 0 1
  have h4 : (C (b^(2:ℕ)) * X 2 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 2 1) (b^(2:ℕ)) := MvPolynomial.C_mul_X_eq_monomial
  rw [h1, h2, h3, h4,
    show (monomial (Finsupp.single (2 : Fin 4) 1) (-(b^(2:ℕ))) : MvPolynomial (Fin 4) K)
        = - monomial (Finsupp.single 2 1) (b^(2:ℕ)) from by simp]
  first | refl_ring1 | ring

theorem zmuQ_split_3 :
    zpgQ a b h 3 = monomial (Finsupp.single (0 : Fin 4) 2) (-(a*b))
      + (monomial (Finsupp.single (2 : Fin 4) 1 + Finsupp.single 3 1) (a^(2:ℕ)*h^(2:ℕ))
          + monomial (Finsupp.single (1 : Fin 4) 1) (-(b^(2:ℕ)))) := by
  have h1 : zpgQ a b h 3
      = - C (a*b) * X 0 ^(2:ℕ) + C (a^(2:ℕ)*h^(2:ℕ)) * X 2 * X 3 - C (b^(2:ℕ)) * X 1 := by
    simp only [zpgQ, Matrix.cons_val]
  have h2 : (-(C (a*b)) * X 0 ^(2:ℕ) : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 0 2) (-(a*b)) := zmu_neg_C_mul_X_pow (K := K) _ 0 2
  have h3 : (C (a^(2:ℕ)*h^(2:ℕ)) * X 2 * X 3 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 2 1 + Finsupp.single 3 1) (a^(2:ℕ)*h^(2:ℕ)) := zmuC_mul_X_mul_X _ 2 3
  have h4 : (C (b^(2:ℕ)) * X 1 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 1 1) (b^(2:ℕ)) := MvPolynomial.C_mul_X_eq_monomial
  rw [h1, h2, h3, h4,
    show (monomial (Finsupp.single (1 : Fin 4) 1) (-(b^(2:ℕ))) : MvPolynomial (Fin 4) K)
        = - monomial (Finsupp.single 1 1) (b^(2:ℕ)) from by simp]
  first | refl_ring1 | ring

theorem zmuQ_split_4 :
    zpgQ a b h 4 = monomial (Finsupp.single (2 : Fin 4) 2) (-(a*b*h^(2:ℕ)))
      + (monomial (Finsupp.single (0 : Fin 4) 1) (a^(2:ℕ))
          + monomial (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))) := by
  have h1 : zpgQ a b h 4
      = - C (a*b*h^(2:ℕ)) * X 2 ^(2:ℕ) + C (a^(2:ℕ)) * X 0 - C (b^(2:ℕ)*h^(2:ℕ)) * X 1 * X 3 := by
    simp only [zpgQ, Matrix.cons_val]
  have h2 : (-(C (a*b*h^(2:ℕ))) * X 2 ^(2:ℕ) : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 2 2) (-(a*b*h^(2:ℕ))) := zmu_neg_C_mul_X_pow (K := K) _ 2 2
  have h3 : (C (a^(2:ℕ)) * X 0 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 0 1) (a^(2:ℕ)) := MvPolynomial.C_mul_X_eq_monomial
  have h4 : (C (b^(2:ℕ)*h^(2:ℕ)) * X 1 * X 3 : MvPolynomial (Fin 4) K)
      = monomial (Finsupp.single 1 1 + Finsupp.single 3 1) (b^(2:ℕ)*h^(2:ℕ)) := zmuC_mul_X_mul_X _ 1 3
  rw [h1, h2, h3, h4,
    show (monomial (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))
        : MvPolynomial (Fin 4) K)
        = - monomial (Finsupp.single 1 1 + Finsupp.single 3 1) (b^(2:ℕ)*h^(2:ℕ)) from by simp]
  first | refl_ring1 | ring

end Splits

/-! ## 6. The weight bounds for the five remainders -/

theorem ZmuWtLt_rest_0 {K : Type} [Field K] (a b h : K) :
    ZmuWtLt (monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))
      + (C (-(a*b)) : MvPolynomial (Fin 4) K)) 18 := by
  refine ZmuWtLt.add (ZmuWtLt.monomial ?_) (ZmuWtLt.monomial ?_)
  · rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]
  · simp

theorem ZmuWtLt_rest_1 {K : Type} [Field K] (a b : K) :
    ZmuWtLt (monomial (Finsupp.single (3 : Fin 4) 1) (a^(2:ℕ))
      + monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1) (-(b^(2:ℕ)))
        : MvPolynomial (Fin 4) K) 20 := by
  refine ZmuWtLt.add (ZmuWtLt.monomial ?_) (ZmuWtLt.monomial ?_)
  · rw [Finsupp.weight_single]; norm_num [zmuWt]
  · rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]

theorem ZmuWtLt_rest_2 {K : Type} [Field K] (a b h : K) :
    ZmuWtLt (monomial (Finsupp.single (3 : Fin 4) 2) (-(a*b*h^(2:ℕ)))
      + monomial (Finsupp.single (2 : Fin 4) 1) (-(b^(2:ℕ)))) 20 := by
  refine ZmuWtLt.add (ZmuWtLt.monomial ?_) (ZmuWtLt.monomial ?_)
  · rw [Finsupp.weight_single]; norm_num [zmuWt]
  · rw [Finsupp.weight_single]; norm_num [zmuWt]

theorem ZmuWtLt_rest_3 {K : Type} [Field K] (a b h : K) :
    ZmuWtLt (monomial (Finsupp.single (2 : Fin 4) 1 + Finsupp.single 3 1) (a^(2:ℕ)*h^(2:ℕ))
      + monomial (Finsupp.single (1 : Fin 4) 1) (-(b^(2:ℕ)))) 20 := by
  refine ZmuWtLt.add (ZmuWtLt.monomial ?_) (ZmuWtLt.monomial ?_)
  · rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]
  · rw [Finsupp.weight_single]; norm_num [zmuWt]

theorem ZmuWtLt_rest_4 {K : Type} [Field K] (a b h : K) :
    ZmuWtLt (monomial (Finsupp.single (0 : Fin 4) 1) (a^(2:ℕ))
      + monomial (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1) (-(b^(2:ℕ)*h^(2:ℕ)))) 16 := by
  refine ZmuWtLt.add (ZmuWtLt.monomial ?_) (ZmuWtLt.monomial ?_)
  · rw [Finsupp.weight_single]; norm_num [zmuWt]
  · rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]

/-! ## 7. Degrees and leading coefficients of the five quadrics -/

section Results

variable {K : Type} [Field K]

/-- The full degree statement, for any monomial order refining the weight order. -/
theorem zmuDegree (m : MonomialOrder (Fin 4))
    (hm : ∀ c d : Fin 4 →₀ ℕ, Finsupp.weight zmuWt c < Finsupp.weight zmuWt d → c ≺[m] d)
    (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    m.degree (zpgQ a b h 0)
        = (Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ∧
      m.degree (zpgQ a b h 1) = (Finsupp.single (1 : Fin 4) 2 : Fin 4 →₀ ℕ) ∧
      m.degree (zpgQ a b h 2)
        = (Finsupp.single (0 : Fin 4) 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ) ∧
      m.degree (zpgQ a b h 3) = (Finsupp.single (0 : Fin 4) 2 : Fin 4 →₀ ℕ) ∧
      m.degree (zpgQ a b h 4) = (Finsupp.single (2 : Fin 4) 2 : Fin 4 →₀ ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine zmu_degree_eq_of_split hm (a^(2:ℕ)*h^(2:ℕ)) 18
      (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hh)) (zmuQ_split_0 a b h) ?_
      (ZmuWtLt_rest_0 a b h)
    rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]
  · refine zmu_degree_eq_of_split hm (-(a*b)) 20 (neg_ne_zero.mpr (mul_ne_zero ha hb))
      (zmuQ_split_1 a b h) ?_ (ZmuWtLt_rest_1 a b)
    rw [Finsupp.weight_single]; norm_num [zmuWt]
  · refine zmu_degree_eq_of_split hm (a^(2:ℕ)) 20 (pow_ne_zero 2 ha) (zmuQ_split_2 a b h) ?_
      (ZmuWtLt_rest_2 a b h)
    rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt]
  · refine zmu_degree_eq_of_split hm (-(a*b)) 20 (neg_ne_zero.mpr (mul_ne_zero ha hb))
      (zmuQ_split_3 a b h) ?_ (ZmuWtLt_rest_3 a b h)
    rw [Finsupp.weight_single]; norm_num [zmuWt]
  · refine zmu_degree_eq_of_split hm (-(a*b*h^(2:ℕ))) 16
      (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero 2 hh)))
      (zmuQ_split_4 a b h) ?_ (ZmuWtLt_rest_4 a b h)
    rw [Finsupp.weight_single]; norm_num [zmuWt]

/-- The leading coefficients of the five quadrics are units. -/
theorem zmuLeadingCoeff_isUnit (m : MonomialOrder (Fin 4))
    (hm : ∀ c d : Fin 4 →₀ ℕ, Finsupp.weight zmuWt c < Finsupp.weight zmuWt d → c ≺[m] d)
    (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (k : Fin 5) :
    IsUnit (m.leadingCoeff (zpgQ a b h k)) := by
  rw [MonomialOrder.isUnit_leadingCoeff]
  fin_cases k
  · exact zmu_ne_zero_of_split (a^(2:ℕ)*h^(2:ℕ)) 18 (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hh))
      (zmuQ_split_0 a b h) (by rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt])
      (ZmuWtLt_rest_0 a b h)
  · exact zmu_ne_zero_of_split (-(a*b)) 20 (neg_ne_zero.mpr (mul_ne_zero ha hb))
      (zmuQ_split_1 a b h) (by rw [Finsupp.weight_single]; norm_num [zmuWt])
      (ZmuWtLt_rest_1 a b)
  · exact zmu_ne_zero_of_split (a^(2:ℕ)) 20 (pow_ne_zero 2 ha) (zmuQ_split_2 a b h)
      (by rw [map_add, Finsupp.weight_single, Finsupp.weight_single]; norm_num [zmuWt])
      (ZmuWtLt_rest_2 a b h)
  · exact zmu_ne_zero_of_split (-(a*b)) 20 (neg_ne_zero.mpr (mul_ne_zero ha hb))
      (zmuQ_split_3 a b h) (by rw [Finsupp.weight_single]; norm_num [zmuWt])
      (ZmuWtLt_rest_3 a b h)
  · exact zmu_ne_zero_of_split (-(a*b*h^(2:ℕ))) 16
      (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero 2 hh)))
      (zmuQ_split_4 a b h) (by rw [Finsupp.weight_single]; norm_num [zmuWt])
      (ZmuWtLt_rest_4 a b h)

end Results

/-! ## 8. The main theorem -/

theorem ZpgI4MonoOrderU (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∃ m : MonomialOrder.{0, u} (Fin 4),
      (∀ k : Fin 5, IsUnit (m.leadingCoeff (Work.MotK.TGen.zpgQ a b h k))) ∧
      m.degree (Work.MotK.TGen.zpgQ a b h 0)
        = (Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 4 →₀ ℕ) ∧
      m.degree (Work.MotK.TGen.zpgQ a b h 1) = (Finsupp.single 1 2 : Fin 4 →₀ ℕ) ∧
      m.degree (Work.MotK.TGen.zpgQ a b h 2)
        = (Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 4 →₀ ℕ) ∧
      m.degree (Work.MotK.TGen.zpgQ a b h 3) = (Finsupp.single 0 2 : Fin 4 →₀ ℕ) ∧
      m.degree (Work.MotK.TGen.zpgQ a b h 4) = (Finsupp.single 2 2 : Fin 4 →₀ ℕ) := by
  have hlt : ∀ c d : Fin 4 →₀ ℕ,
      Finsupp.weight zmuWt c < Finsupp.weight zmuWt d → c ≺[zmuMOU.{u}] d :=
    fun c d h => zmuMOU_lt_of_weight_lt h
  obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ := zmuDegree zmuMOU.{u} hlt a b h ha hb hh
  refine ⟨zmuMOU.{u}, fun k => zmuLeadingCoeff_isUnit zmuMOU.{u} hlt a b h ha hb hh k,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hd3
  · exact hd4

end Work.MotK.TGen
