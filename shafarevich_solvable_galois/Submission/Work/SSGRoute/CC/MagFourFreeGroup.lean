import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.selfPair_witness_four
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm map `ν(z) = (σ z)⁻¹ z` and the two witness families for the `(4,4)` graded step

For an involution `σ` of the letters and `z : FreeGroup X`, `normG X σ z = (σ z)⁻¹ * z` is the
"norm" whose class in `F/P₅` is the `δ`-difference of the class of `z`.  The two families of
witnesses are

* the self-pair word `selfPairWord X σ x = ν((x·σx)·⁅x⁻¹,σx⁆·(x·σx))`, whose class is
  `φ(x * x) = x²σx² + σx²x²` (`mag4_selfPairWord`; this is the content of
  `Work.SSGRoute.selfPair_witness_four`, transported to the degree-`2` mod-`2` Magnus component);
* the double word `doubleWord X σ g = ν(g · σg)` for `g ∈ γ₂`.

The last three lemmas realise the three subspaces `flgDeltaW`, `selfSpan` and `brkSpan` of the
abstract degree-`4` statement `Work.SSGRoute.CC.freeLieFourFixedGeneration`.
-/

open scoped commutatorElement

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

noncomputable section

/-! ## The norm map -/

/-- The norm `ν(z) = (σ z)⁻¹ * z` of an element of a free group under an involution `σ`. -/
def normG (X : Type) (σ : X ≃ X) (z : FreeGroup X) : FreeGroup X :=
  (FreeGroup.freeGroupCongr σ z)⁻¹ * z

theorem doubleWord_eq_normG (X : Type) (σ : X ≃ X) (g : FreeGroup X) :
    doubleWord X σ g = normG X σ (g * FreeGroup.freeGroupCongr σ g) := rfl

theorem selfPairWord_eq_normG (X : Type) (σ : X ≃ X) (x : X) :
    selfPairWord X σ x = normG X σ (selfPairElt X σ x) := rfl

theorem normG_mul_generic {F : Type*} [Group F] (Φ : F ≃* F) (u v : F) :
    (Φ (u * v))⁻¹ * (u * v) = ((Φ v)⁻¹ * v) * (v⁻¹ * ((Φ u)⁻¹ * u) * v) := by
  rw [map_mul Φ u v]
  group

theorem normG_mul (X : Type) (σ : X ≃ X) (u v : FreeGroup X) :
    normG X σ (u * v) = normG X σ v * (v⁻¹ * normG X σ u * v) := by
  rw [normG, normG, normG]
  exact normG_mul_generic (FreeGroup.freeGroupCongr σ) u v

@[simp] theorem normG_one (X : Type) (σ : X ≃ X) : normG X σ 1 = 1 := by
  simp [normG]

/-! ## The involution and the `γ₂`-membership of its translates -/

/-- The involution `freeGroupCongr σ` is an involution when `σ` is. -/
theorem freeGroupCongr_freeGroupCongr (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (g : FreeGroup X) :
    FreeGroup.freeGroupCongr σ (FreeGroup.freeGroupCongr σ g) = g := by
  have hττ : ∀ y : FreeGroup X,
      FreeGroup.freeGroupCongr σ (FreeGroup.freeGroupCongr σ y) = y := by
    intro y
    induction y using FreeGroup.induction_on with
    | one => simp
    | of x => simp [FreeGroup.freeGroupCongr_apply, hσ x]
    | inv_of x hx => simpa using congrArg Inv.inv hx
    | mul a b ha hb => simp only [map_mul, ha, hb]
  exact hττ g

/-- `γ₂` is characteristic: `freeGroupCongr σ` preserves the commutator subgroup. -/
theorem freeGroupCongr_mem_lowerCentralSeries_one (X : Type) (σ : X ≃ X)
    {g : FreeGroup X} (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1) :
    FreeGroup.freeGroupCongr σ g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1 := by
  have hmono : Subgroup.map ((FreeGroup.freeGroupCongr σ : FreeGroup X ≃* FreeGroup X) :
        FreeGroup X →* FreeGroup X)
      ⁅(⊤ : Subgroup (FreeGroup X)), (⊤ : Subgroup (FreeGroup X))⁆
      = ⁅(⊤ : Subgroup (FreeGroup X)), (⊤ : Subgroup (FreeGroup X))⁆ := by
    rw [Subgroup.map_commutator]
    rw [Subgroup.map_top_of_surjective ((FreeGroup.freeGroupCongr σ : FreeGroup X ≃* FreeGroup X) :
        FreeGroup X →* FreeGroup X) (FreeGroup.freeGroupCongr σ).surjective]
  have hmem : FreeGroup.freeGroupCongr σ g
      ∈ Subgroup.map ((FreeGroup.freeGroupCongr σ : FreeGroup X ≃* FreeGroup X) :
          FreeGroup X →* FreeGroup X)
        ⁅(⊤ : Subgroup (FreeGroup X)), (⊤ : Subgroup (FreeGroup X))⁆ :=
    Subgroup.mem_map_of_mem _ hg
  rwa [hmono] at hmem

/-- **The double witness lies in `γ₄`.** -/
theorem double_witness_four (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) (g : FreeGroup X)
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1) :
    doubleWord X σ g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 := by
  have hword : doubleWord X σ g = ⁅g⁻¹, (FreeGroup.freeGroupCongr σ g)⁻¹⁆ := by
    unfold doubleWord
    rw [map_mul, freeGroupCongr_freeGroupCongr X σ hσ g, commutatorElement_def]
    group
  rw [hword]
  have hg' : g⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1 := Subgroup.inv_mem _ hg
  have hσg : FreeGroup.freeGroupCongr σ g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1 :=
    freeGroupCongr_mem_lowerCentralSeries_one X σ hg
  have hσg' : (FreeGroup.freeGroupCongr σ g)⁻¹
      ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1 := Subgroup.inv_mem _ hσg
  exact prop5.commutator_lowerCentralSeries_le (FreeGroup X) 1 1
    (Subgroup.commutator_mem_commutator hg' hσg')

/-- `freeGroupCongr σ` preserves every term of the lower central series. -/
theorem freeGroupCongr_map_lowerCentralSeries_le (X : Type) (σ : X ≃ X) (k : ℕ) :
    Subgroup.map ((FreeGroup.freeGroupCongr σ : FreeGroup X ≃* FreeGroup X) :
        FreeGroup X →* FreeGroup X)
      ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k)
      ≤ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k := by
  induction k with
  | zero => simp
  | succ n ih =>
      have htop : Subgroup.map ((FreeGroup.freeGroupCongr σ : FreeGroup X ≃* FreeGroup X) :
          FreeGroup X →* FreeGroup X) (⊤ : Subgroup (FreeGroup X)) = ⊤ :=
        Subgroup.map_top_of_surjective _ (FreeGroup.freeGroupCongr σ).surjective
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.map_commutator, htop]
      exact Subgroup.commutator_mono ih le_rfl

/-- `freeGroupCongr σ` preserves `γ₄`. -/
theorem freeGroupCongr_mem_lowerCentralSeries_three (X : Type) (σ : X ≃ X)
    {g : FreeGroup X} (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    FreeGroup.freeGroupCongr σ g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 :=
  freeGroupCongr_map_lowerCentralSeries_le X σ 3 (Subgroup.mem_map_of_mem _ hg)

theorem mff_mag4_one (X : Type) : mag4 X (1 : FreeGroup X) = 0 := by
  have h0 : (0 : FreeAssoc X ⧸ fil X 5)
      = Ideal.Quotient.mk (fil X 5) (0 : FreeAssoc X) :=
    (map_zero (Ideal.Quotient.mk (fil X 5))).symm
  rw [mag4, magLead_one, h0, degq_mk (by norm_num) X, map_zero, map_zero]

/-- `selfPairClass X σ x = φ(x*x)`. -/
theorem phi_self (X : Type) (σ : X ≃ X) (x : X) :
    phi X (σ : X → X) (flg_ltr X x * flg_ltr X x) = selfPairClass X σ x := by
  have hsig : sigA X σ (flg_ltr X x * flg_ltr X x)
      = flg_ltr X (σ x) * flg_ltr X (σ x) := by
    rw [map_mul, sigA_ltr]
  have h1 : (flg_ltr X x * flg_ltr X x)
      = MonoidAlgebra.single (FreeMonoid.of x * FreeMonoid.of x) (1 : ZMod 2) := by
    rw [flg_ltr, MonoidAlgebra.single_mul_single, mul_one]
  have h2 : (flg_ltr X (σ x) * flg_ltr X (σ x))
      = MonoidAlgebra.single (FreeMonoid.of (σ x) * FreeMonoid.of (σ x)) (1 : ZMod 2) := by
    rw [flg_ltr, MonoidAlgebra.single_mul_single, mul_one]
  rw [phi, hsig, h1, h2, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.single_mul_single, mul_one, selfPairClass]
  abel

/-- A sum of two `single`s supported on words of length `4` has no coefficient in length `≠ 4`. -/
theorem coeff_add_single_deg4 {X : Type} (u v w : FreeMonoid X)
    (hu : u.length = 4) (hv : v.length = 4) (hw : w.length ≠ 4) :
    (MonoidAlgebra.single u (1 : ZMod 2) + MonoidAlgebra.single v 1).coeff w = 0 := by
  classical
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single_apply,
    MonoidAlgebra.coeff_single_apply]
  have h1 : ¬ (u = w) := fun h => hw (h ▸ hu)
  have h2 : ¬ (v = w) := fun h => hw (h ▸ hv)
  rw [if_neg h1, if_neg h2, add_zero]

theorem deg4_selfPairClass {X : Type} (σ : X ≃ X) (x : X)
    (e : FreeAssoc X) (hclass : red2 X e = selfPairClass X σ x) :
    red2 X (degPart (X := X) 4 e) = red2 X e := by
  classical
  ext w
  rw [red2_apply, red2_apply, coeff_degPart]
  by_cases hw : w.length = 4
  · rw [if_pos hw]
  · rw [if_neg hw, ← red2_apply, hclass]
    exact (coeff_add_single_deg4
      (FreeMonoid.of (σ x) * FreeMonoid.of (σ x) * (FreeMonoid.of x * FreeMonoid.of x))
      (FreeMonoid.of x * FreeMonoid.of x * (FreeMonoid.of (σ x) * FreeMonoid.of (σ x)))
      w (by simp [FreeMonoid.length_mul, FreeMonoid.length_of])
      (by simp [FreeMonoid.length_mul, FreeMonoid.length_of]) hw).symm

/-- The self-pair word lies in `γ₄`. -/
theorem selfPairWord_mem (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (x : X) :
    selfPairWord X σ x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 :=
  (selfPair_witness_four X σ hσ x (hfree x)).1

/-- **The class of the self-pair witness.** -/
theorem mag4_selfPairWord (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (x : X) :
    mag4 X (selfPairWord X σ x) = phi X (σ : X → X) (flg_ltr X x * flg_ltr X x) := by
  obtain ⟨hz, e, he, hclass⟩ := selfPair_witness_four X σ hσ x (hfree x)
  have hmk : Ideal.Quotient.mk (fil X 5) e = magLead 5 (selfPairWord X σ x) := by
    rw [show magLead 5 (selfPairWord X σ x)
        = ((magnus X 5 (selfPairWord X σ x) : (FreeAssoc X ⧸ fil X 5)ˣ) :
            FreeAssoc X ⧸ fil X 5) - 1 from rfl, he, add_sub_cancel_left]
  rw [mag4_eq_of_mk hmk, deg4_selfPairClass σ x e hclass, hclass, phi_self]

end

end Work.SSGRoute.CC
