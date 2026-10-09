import Mathlib
import Submission.Work.SSGRoute.prop5.adjacent_pSeries_inter_lcs_le
import Submission.Work.SSGRoute.gsFourDefs
import Submission.Work.SSGRoute.CC.FreeLieFourFixedGeneration
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mod-`2` Magnus layers of degree `2` and `4`

For a type `X` we let `A X = MonoidAlgebra (ZMod 2) (FreeMonoid X)` be the free associative
`𝔽₂`-algebra on `X` and `FreeAssoc X = MonoidAlgebra ℤ (FreeMonoid X)` its integral form.
`prop5.magnus X N : FreeGroup X →* (FreeAssoc X ⧸ fil X N)ˣ` is the truncated Magnus map, and
`prop5.magLead N z = (magnus X N z : _) - 1`.

This file sets up

* `red2` — the coefficientwise reduction `FreeAssoc X →+* A X`;
* `degq j` — the degree-`j` component of an element of the truncation `FreeAssoc X ⧸ fil X 5`,
  reduced mod `2` (a well-defined function for `j < 5`);
* `mag4`, `mag2` — the degree-`4` and degree-`2` components of the Magnus image at truncation `5`;
* `sigA` — the algebra endomorphism of `A X` induced by a map `σ` of letters.

The layer `E(4,4) = γ₄P₅/P₅` is the `𝔽₂`-vector space `mag4` maps onto; `Wsub X ⊆ A X` is spanned
by the degree-`4` left-nested brackets `brk4`.
-/

open scoped commutatorElement

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

noncomputable section

variable {X : Type}

/-! ## Reduction mod `2` and the degree components of the truncated Magnus image -/

/-- The coefficientwise reduction `FreeAssoc X →+* MonoidAlgebra (ZMod 2) (FreeMonoid X)`. -/
abbrev red2 (X : Type) : FreeAssoc X →+* MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  MonoidAlgebra.mapRingHom (FreeMonoid X) (Int.castRingHom (ZMod 2))

theorem red2_apply (X : Type) (a : FreeAssoc X) (w : FreeMonoid X) :
    (red2 X a).coeff w = (a.coeff w : ZMod 2) :=
  MonoidAlgebra.coeff_mapRingHom (Int.castRingHom (ZMod 2)) a w

theorem red2_single (X : Type) (w : FreeMonoid X) (r : ℤ) :
    red2 X (MonoidAlgebra.single w r) = MonoidAlgebra.single w (r : ZMod 2) := by
  classical
  ext v
  rw [red2_apply, MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply]
  by_cases h : w = v <;> simp [h]

/-- The degree-`j` component of an element of the truncation `FreeAssoc X ⧸ fil X 5`, reduced
mod `2`. -/
def degq (j : ℕ) (X : Type) (x : FreeAssoc X ⧸ fil X 5) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  red2 X (degPart (X := X) j (Quotient.out x))

theorem degq_apply (j : ℕ) (X : Type) (x : FreeAssoc X ⧸ fil X 5) :
    degq j X x = red2 X (degPart (X := X) j (Quotient.out x)) := rfl

theorem degq_mk {j : ℕ} (hj : j < 5) (X : Type) (a : FreeAssoc X) :
    degq j X (Ideal.Quotient.mk (fil X 5) a) = red2 X (degPart (X := X) j a) := by
  have h1 : Ideal.Quotient.mk (fil X 5) a
      = Ideal.Quotient.mk (fil X 5) (Quotient.out (Ideal.Quotient.mk (fil X 5) a)) :=
    (Ideal.Quotient.mk_out _).symm
  have hmem : a - Quotient.out (Ideal.Quotient.mk (fil X 5) a) ∈ fil X 5 :=
    (Ideal.Quotient.eq).mp h1
  have h0 : degPart (X := X) j (a - Quotient.out (Ideal.Quotient.mk (fil X 5) a)) = 0 :=
    degPart_eq_zero_of_mem_fil hmem hj
  rw [map_sub] at h0
  rw [sub_eq_zero] at h0
  rw [degq, h0]

theorem degq_add {j : ℕ} (hj : j < 5) (X : Type) (x y : FreeAssoc X ⧸ fil X 5) :
    degq j X (x + y) = degq j X x + degq j X y := by
  have hmem : Quotient.out (x + y) - (Quotient.out x + Quotient.out y) ∈ fil X 5 := by
    have h1 : Ideal.Quotient.mk (fil X 5) (Quotient.out (x + y))
        = Ideal.Quotient.mk (fil X 5) (Quotient.out x + Quotient.out y) := by
      rw [Ideal.Quotient.mk_out, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]
    exact (Ideal.Quotient.eq).mp h1
  have h0 : degPart (X := X) j (Quotient.out (x + y) - (Quotient.out x + Quotient.out y)) = 0 :=
    degPart_eq_zero_of_mem_fil hmem hj
  have h1 : degPart (X := X) j (Quotient.out (x + y))
      = degPart (X := X) j (Quotient.out x) + degPart (X := X) j (Quotient.out y) := by
    rw [map_sub] at h0
    have h2 : degPart (X := X) j (Quotient.out (x + y))
        = degPart (X := X) j (Quotient.out x + Quotient.out y) := sub_eq_zero.mp h0
    rw [h2, map_add]
  show red2 X (degPart (X := X) j (Quotient.out (x + y)))
      = red2 X (degPart (X := X) j (Quotient.out x))
        + red2 X (degPart (X := X) j (Quotient.out y))
  rw [h1, map_add]

theorem degq_neg {j : ℕ} (hj : j < 5) (X : Type) (x : FreeAssoc X ⧸ fil X 5) :
    degq j X (-x) = -degq j X x := by
  have hmem : Quotient.out (-x) + Quotient.out x ∈ fil X 5 := by
    have h1 : Ideal.Quotient.mk (fil X 5) (Quotient.out (-x) + Quotient.out x) = 0 := by
      rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, neg_add_cancel]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
  have h0 : degPart (X := X) j (Quotient.out (-x) + Quotient.out x) = 0 :=
    degPart_eq_zero_of_mem_fil hmem hj
  rw [map_add] at h0
  have h1 : degPart (X := X) j (Quotient.out (-x)) = -degPart (X := X) j (Quotient.out x) :=
    add_eq_zero_iff_eq_neg.mp h0
  show red2 X (degPart (X := X) j (Quotient.out (-x)))
      = -red2 X (degPart (X := X) j (Quotient.out x))
  rw [h1, map_neg]

/-- In characteristic `2`, `-a = a`. -/
theorem neg_eq_self_zmodTwo {M : Type*} (a : MonoidAlgebra (ZMod 2) M) : -a = a := by
  have h : a + a = 0 := by
    conv_lhs => rw [← one_smul (ZMod 2) a, ← one_smul (ZMod 2) a, ← add_smul]
    rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]
  calc -a = -a + (a + a) := by rw [h, add_zero]
    _ = a := by abel

/-! ## The degree-`4` and degree-`2` Magnus components -/

/-- The mod-`2` degree-`4` component of the Magnus image of `z` at truncation `5`. -/
def mag4 (X : Type) (z : FreeGroup X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  degq 4 X (magLead 5 z)

/-- The mod-`2` degree-`2` component of the Magnus image of `z` at truncation `5`. -/
def mag2 (X : Type) (z : FreeGroup X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  degq 2 X (magLead 5 z)

theorem mag4_eq_of_mk {a : FreeAssoc X} {z : FreeGroup X}
    (h : Ideal.Quotient.mk (fil X 5) a = magLead 5 z) :
    mag4 X z = red2 X (degPart (X := X) 4 a) := by
  rw [mag4, ← h, degq_mk (by norm_num) X]

theorem mag2_eq_of_mk {a : FreeAssoc X} {z : FreeGroup X}
    (h : Ideal.Quotient.mk (fil X 5) a = magLead 5 z) :
    mag2 X z = red2 X (degPart (X := X) 2 a) := by
  rw [mag2, ← h, degq_mk (by norm_num) X]

/-- `mag4` is additive on `γ₄`. -/
theorem mag4_mul {z z' : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3)
    (hz' : z' ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    mag4 X (z * z') = mag4 X z + mag4 X z' := by
  have h := magLead_mul (X := X) 5 4 (by norm_num) (by norm_num) (by norm_num) hz hz'
  simp only [mag4]
  rw [h, degq_add (by norm_num)]

/-- `mag4` of an inverse in `γ₄`. -/
theorem mag4_inv {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    mag4 X z⁻¹ = mag4 X z := by
  have h := magLead_inv (X := X) 5 4 (by norm_num) (by norm_num) (by norm_num) hz
  simp only [mag4]
  rw [h, degq_neg (by norm_num), neg_eq_self_zmodTwo]

/-- `mag4` is additive on products with an inverse, in the form used by the assembly. -/
theorem mag4_mul_neg {z z' : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3)
    (hz' : z' ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    mag4 X (z * z'⁻¹) = mag4 X z + mag4 X z' := by
  rw [mag4_mul hz (Subgroup.inv_mem _ hz'), mag4_inv hz']

/-! ## The algebra map induced by `σ` -/

/-- The algebra endomorphism of `A X` induced by a map `σ : X → X` of letters. -/
abbrev sigA (X : Type) (σ : X → X) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) →+* MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  MonoidAlgebra.mapDomainRingHom (ZMod 2) (FreeMonoid.map σ)

theorem sigA_mul (X : Type) (σ : X → X)
    (a b : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    sigA X σ (a * b) = sigA X σ a * sigA X σ b := map_mul _ a b

theorem sigA_one (X : Type) (σ : X → X) :
    sigA X σ (1 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = 1 := map_one _

theorem sigA_single (X : Type) (σ : X → X) (x : X) :
    sigA X σ (MonoidAlgebra.single (FreeMonoid.of x) (1 : ZMod 2))
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1 := by
  rw [sigA, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
    FreeMonoid.map_of]

theorem sigA_ltr (X : Type) (σ : X → X) (x : X) :
    sigA X σ (flg_ltr X x) = flg_ltr X (σ x) := sigA_single X σ x


/-! ## The quadratic form `φ` and its generators, and the two witness words -/

/-- `sigA X σ`, as a `ZMod 2`-linear map. -/
def sigAL (X : Type) (σ : X → X) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X) where
  toFun := sigA X σ
  map_add' a b := map_add _ a b
  map_smul' c a := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl <;> simp

/-- The quadratic form `φ(u) = u·σA u + σA u·u`. -/
def phi (X : Type) (σ : X → X) (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  u * sigA X σ u + sigA X σ u * u

/-- The span of `φ` at the squares of single letters. -/
def selfSpan (X : Type) (σ : X → X) :
    Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range fun x : X => phi X σ (flg_ltr X x * flg_ltr X x))

/-- The span of `φ` at the brackets of pairs of letters. -/
def brkSpan (X : Type) (σ : X → X) :
    Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range fun p : X × X =>
    phi X σ (brk X (flg_ltr X p.1) (flg_ltr X p.2)))

/-- The word `(x·σx)·⁅x⁻¹,σx⁆·(x·σx)` whose norm is `selfPairWord`. -/
def selfPairElt (X : Type) (σ : X ≃ X) (x : X) : FreeGroup X :=
  let A : FreeGroup X := FreeGroup.of x * FreeGroup.of (σ x)
  let D : FreeGroup X := ⁅(FreeGroup.of x)⁻¹, FreeGroup.of (σ x)⁆
  A * D * A

theorem selfPairWord_eq_selfPairElt (X : Type) (σ : X ≃ X) (x : X) :
    selfPairWord X σ x
      = (FreeGroup.freeGroupCongr σ (selfPairElt X σ x))⁻¹ * selfPairElt X σ x := rfl

end

end Work.SSGRoute.CC
