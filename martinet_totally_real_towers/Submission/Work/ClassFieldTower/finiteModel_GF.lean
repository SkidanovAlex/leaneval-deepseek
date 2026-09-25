import Mathlib
import Submission.Work.ClassFieldTower.FiniteModelDefs
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five

/-!
# `Work.ClassFieldTower.finiteModel_GF` -- the finite model `GF` is `(ℤ/2)^5`

`Work.ClassFieldTower.GF` is the group presented by five generators `x₀,…,x₄` subject to
the relations `xᵢ ^ 2 = 1` and `⁅xᵢ, xⱼ⁆ = 1` (`Work.ClassFieldTower.relF`), i.e. the
elementary abelian `2`-group of order `2 ^ 5`, written
`F2five = Fin 5 → Multiplicative (ZMod 2)`.  This module proves that identification and the
consequent minimal generator number `5`:

* `pi0` is the "exponent parity" homomorphism `FreeGroup (Fin 5) →* F2five` sending the `i`-th
  free generator to the `i`-th basis vector; all relators are killed by it, so it descends to
  `psiGF : GF →* F2five` (`psiGF_surjective`);
* conversely the images `gF i ∈ GF` of the free generators are involutions (`gF_sq`) which
  pairwise commute (`gF_mul_comm`) and generate `GF` (`gF_closure`); hence `GF` is commutative
  (`commute_gF_all`, via `Subgroup.centralizer_closure`) and every element of `GF` is a product
  `∏ i, gF i ^ ε (b i)` with `b : Fin 5 → Bool` (`exists_bool_prod`, by
  `Subgroup.closure_induction`), which gives `Nat.card GF ≤ 2 ^ 5` (`card_GF_le`);
* the surjection `psiGF` gives the reverse inequality (`card_GF_ge`), so `GF ≃* F2five`
  (`finiteModel_GF`);
* a generating finset of `F2five = (ℤ/2)^5` has at least `5` elements, being a spanning set of a
  `5`-dimensional `𝔽₂`-vector space (`card_le_card_of_closure_eq_top_pi`, adapted from
  `Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five`), whence every generating finset of
  `GF` has at least `5` elements.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped IsMulCommutative
open scoped commutatorElement

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The quotient `GF ↠ F2five` -/

/-- The `i`-th basis vector of `F2five = (ℤ/2)^5`: the function which is `1` away from `i` and
`Multiplicative.ofAdd 1` at `i`. -/
def basisF (i : Fin 5) : F2five := Function.update 1 i (Multiplicative.ofAdd (1 : ZMod 2))

theorem basisF_self (i : Fin 5) : basisF i i = Multiplicative.ofAdd (1 : ZMod 2) := by
  simp [basisF]

theorem basisF_of_ne {i j : Fin 5} (h : j ≠ i) : basisF i j = 1 := by
  simp [basisF, Function.update_of_ne h]

theorem basisF_mul_self (i : Fin 5) : basisF i * basisF i = 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [Pi.mul_apply, basisF_self, Pi.one_apply]
    decide
  · simp [Pi.mul_apply, basisF_of_ne h]

theorem basisF_sq (i : Fin 5) : basisF i ^ 2 = 1 := by
  rw [pow_two]
  exact basisF_mul_self i

/-- The power of a single basis vector `ofAdd 1` of `Multiplicative (ZMod 2)` only depends on the
exponent modulo `2`. -/
theorem ofAdd_one_pow (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ n = Multiplicative.ofAdd ((n : ZMod 2)) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]

theorem sq_mem_relF (i : Fin 5) : FreeGroup.of i ^ 2 ∈ relF := by
  simp [relF]

theorem comm_mem_relF (i j : Fin 5) :
    FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹ ∈ relF := by
  simp [relF]

/-- **The exponent-parity map** on the free group on five generators: the `i`-th generator is sent
to the `i`-th basis vector of `(ℤ/2)^5`. -/
def pi0 : FreeGroup (Fin 5) →* F2five := FreeGroup.lift basisF

theorem pi0_of (i : Fin 5) : pi0 (FreeGroup.of i) = basisF i := by
  rw [pi0, FreeGroup.lift_apply_of]

/-- Every relator of the model presentation is killed by `pi0`. -/
theorem pi0_eq_one_of_mem_relF (r : FreeGroup (Fin 5)) (hr : r ∈ relF) : pi0 r = 1 := by
  simp only [relF, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hr
  rcases hr with ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
  · rw [map_pow, pi0_of, basisF_sq]
  · simp only [map_mul, map_inv, pi0_of]
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

theorem relF_subset_ker : (relF : Set (FreeGroup (Fin 5))) ⊆ pi0.ker := by
  intro r hr
  simpa [MonoidHom.mem_ker] using pi0_eq_one_of_mem_relF r hr

/-- **The canonical surjection `GF ↠ (ℤ/2)^5`**, induced by the exponent-parity map. -/
def psiGF : GF →* F2five :=
  QuotientGroup.lift (Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5)))) pi0
    (Subgroup.normalClosure_le_normal relF_subset_ker)

theorem psiGF_mk (x : FreeGroup (Fin 5)) :
    psiGF (QuotientGroup.mk' (Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5)))) x)
      = pi0 x := by
  rw [psiGF, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

/-- The basis vectors generate `(ℤ/2)^5`. -/
theorem basisF_closure : Subgroup.closure (Set.range basisF) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y = ∏ i : Fin 5, basisF i ^ ((y i).toAdd).val := by
    funext j
    rw [Finset.prod_apply]
    rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [Pi.pow_apply, basisF_self, ofAdd_one_pow, ZMod.natCast_zmod_val, ofAdd_toAdd]
    · intro i _ hi
      rw [Pi.pow_apply, basisF_of_ne (Ne.symm hi), one_pow]
  rw [hy]
  exact Subgroup.prod_mem (Subgroup.closure (Set.range basisF))
    (fun i _ => Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_range_self i)) _)

theorem pi0_surjective : Function.Surjective pi0 := by
  rw [show pi0 = FreeGroup.lift basisF from rfl, ← MonoidHom.range_eq_top,
    FreeGroup.range_lift_eq_closure, basisF_closure]

theorem psiGF_surjective : Function.Surjective psiGF := by
  intro y
  obtain ⟨x, hx⟩ := pi0_surjective y
  exact ⟨QuotientGroup.mk' (Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5)))) x,
    by rw [psiGF_mk, hx]⟩

/-! ## 2. `GF` is generated by five commuting involutions -/

/-- The quotient map `FreeGroup (Fin 5) →* GF`. -/
def qGF : FreeGroup (Fin 5) →* GF :=
  QuotientGroup.mk' (Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5))))

/-- The images in `GF` of the five free generators. -/
def gF (i : Fin 5) : GF := qGF (FreeGroup.of i)

theorem gF_sq (i : Fin 5) : gF i ^ 2 = 1 := by
  have hmem : FreeGroup.of i ^ 2 ∈ Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5))) :=
    Subgroup.subset_normalClosure (sq_mem_relF i)
  have h1 : qGF (FreeGroup.of i ^ 2) = 1 := by
    rw [qGF, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  rw [map_pow] at h1
  simpa [gF] using h1

theorem gF_mul_comm (i j : Fin 5) : gF i * gF j = gF j * gF i := by
  have hmem : FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹ ∈
      Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5))) :=
    Subgroup.subset_normalClosure (comm_mem_relF i j)
  have h1 : qGF (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹
      * (FreeGroup.of j)⁻¹) = 1 := by
    rw [qGF, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  simp only [map_mul, map_inv] at h1
  have h2 : ⁅gF i, gF j⁆ = 1 := by
    rw [commutatorElement_def]
    exact h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

/-- The five elements `gF i` generate `GF`. -/
theorem gF_closure : Subgroup.closure (Set.range gF) = ⊤ := by
  have h2 : Set.range gF = qGF '' Set.range (FreeGroup.of : Fin 5 → FreeGroup (Fin 5)) := by
    rw [show gF = qGF ∘ (FreeGroup.of : Fin 5 → FreeGroup (Fin 5)) from rfl]
    exact Set.range_comp' ⇑qGF (FreeGroup.of : Fin 5 → FreeGroup (Fin 5))
  rw [h2, ← MonoidHom.map_closure qGF (Set.range (FreeGroup.of : Fin 5 → FreeGroup (Fin 5))),
    FreeGroup.closure_range_of (Fin 5)]
  exact Subgroup.map_top_of_surjective qGF (QuotientGroup.mk'_surjective _)

/-- `GF` is commutative: its generators commute and generate it. -/
theorem commute_gF_all (x y : GF) : x * y = y * x := by
  have hle : Subgroup.closure (Set.range gF) ≤ Subgroup.centralizer (Set.range gF) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro y ⟨j, rfl⟩
    exact (gF_mul_comm i j).symm
  rw [← Subgroup.centralizer_closure (Set.range gF), gF_closure] at hle
  have hmem : ∀ h ∈ (⊤ : Subgroup GF), h * x = x * h :=
    Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp (hle trivial))
  exact (hmem y trivial).symm

instance instIsMulCommutativeGF : IsMulCommutative GF := IsMulCommutative.of_comm commute_gF_all

/-- The exponent `0` or `1` attached to a bit. -/
def epsB (b : Bool) : ℕ := if b then 1 else 0

/-- The standard product `∏ i, gF i ^ ε (b i)` attached to a bit vector `b`.  Since `GF` is
commutative (`instIsMulCommutativeGF`), this is an ordinary `Finset.prod`. -/
def Pb (b : Fin 5 → Bool) : GF := ∏ i, gF i ^ epsB (b i)

theorem Pb_mul (b c : Fin 5 → Bool) : Pb b * Pb c = Pb (fun i => b i ^^ c i) := by
  simp only [Pb]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← pow_add]
  rcases hb : b i with _ | _ <;> rcases hc : c i with _ | _ <;> simp_all [epsB, gF_sq]

theorem Pb_one : Pb (fun _ => false) = 1 := by
  simp [Pb, epsB]

theorem Pb_inv (b : Fin 5 → Bool) : (Pb b)⁻¹ = Pb b := by
  simp only [Pb]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rcases hb : b i with _ | _
  · simp [epsB]
  · simp only [epsB, reduceIte, pow_one]
    exact mul_eq_one_iff_inv_eq.mp (by simpa [pow_two] using gF_sq i)

theorem Pb_single (i : Fin 5) : Pb (fun j => j == i) = gF i := by
  simp only [Pb]
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [epsB]
  · intro j _ hj
    have h : (j == i) = false := beq_eq_false_iff_ne.mpr hj
    simp [h, epsB]

/-- **Every element of `GF` is a subset product of the five generators.** -/
theorem exists_bool_prod (x : GF) : ∃ b : Fin 5 → Bool, x = Pb b := by
  have hx : x ∈ Subgroup.closure (Set.range gF) := by rw [gF_closure]; trivial
  refine Subgroup.closure_induction (k := Set.range gF)
    (p := fun y _ => ∃ b : Fin 5 → Bool, y = Pb b) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    exact ⟨fun j => j == i, (Pb_single i).symm⟩
  · exact ⟨fun _ => false, Pb_one.symm⟩
  · rintro y z hy hz ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨fun i => b i ^^ c i, Pb_mul b c⟩
  · rintro y hy ⟨b, rfl⟩
    exact ⟨b, Pb_inv b⟩

theorem Pb_surjective : Function.Surjective Pb := fun x => by
  obtain ⟨b, hb⟩ := exists_bool_prod x
  exact ⟨b, hb.symm⟩

theorem finite_GF : Finite GF := Finite.of_surjective Pb Pb_surjective

theorem card_GF_le : Nat.card GF ≤ 32 := by
  have h := Nat.card_le_card_of_surjective Pb Pb_surjective
  have h2 : Nat.card (Fin 5 → Bool) = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  rwa [h2] at h

theorem card_F2five : Nat.card F2five = 32 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp [Fintype.card_multiplicative]

theorem card_GF_ge : 32 ≤ Nat.card GF := by
  haveI : Finite GF := finite_GF
  have h := Nat.card_le_card_of_surjective psiGF psiGF_surjective
  rwa [card_F2five] at h

/-! ## 3. A generating finset of `(ℤ/2)^n` has at least `n` elements -/

/-- The additive group of `(ZMod 2)^n` written multiplicatively: a generating finset spans the
`ZMod 2`-vector space `(ZMod 2)^n`, so it has at least `n` elements. -/
private theorem card_le_card_of_closure_eq_top_multiplicative {n : ℕ}
    (A : Finset (Multiplicative (Fin n → ZMod 2)))
    (hA : Subgroup.closure (A : Set (Multiplicative (Fin n → ZMod 2))) = ⊤) : n ≤ A.card := by
  classical
  have htop : Subgroup.toAddSubgroup' (⊤ : Subgroup (Multiplicative (Fin n → ZMod 2))) = ⊤ :=
    OrderIso.map_top _
  have hclos : AddSubgroup.closure
      (Multiplicative.ofAdd ⁻¹' (A : Set (Multiplicative (Fin n → ZMod 2)))) = ⊤ := by
    rw [← Subgroup.toAddSubgroup'_closure (S := (A : Set (Multiplicative (Fin n → ZMod 2)))),
      hA, htop]
  set B : Finset (Fin n → ZMod 2) := A.image Multiplicative.toAdd with hBdef
  have hBcoe : (Multiplicative.ofAdd ⁻¹' (A : Set (Multiplicative (Fin n → ZMod 2))))
      = (B : Set (Fin n → ZMod 2)) := by
    ext y
    simp only [Set.mem_preimage, Finset.mem_coe, hBdef, Finset.mem_image]
    exact ⟨fun hy => ⟨Multiplicative.ofAdd y, hy, rfl⟩,
      by rintro ⟨a, ha, rfl⟩; simpa using ha⟩
  have hspan : Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ AddSubgroup.closure (B : Set (Fin n → ZMod 2)) := by
      rw [← hBcoe, hclos]; trivial
    have hle : AddSubgroup.closure (B : Set (Fin n → ZMod 2))
        ≤ (Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2))).toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr (fun y hy => Submodule.subset_span hy)
    exact hle hx
  have hfr : Module.finrank (ZMod 2) (Fin n → ZMod 2) ≤ B.card := by
    have h := finrank_span_le_card (R := ZMod 2) (M := Fin n → ZMod 2)
      (s := (B : Set (Fin n → ZMod 2)))
    rw [hspan, finrank_top, Finset.toFinset_coe] at h
    exact h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfr
  exact hfr.trans (by rw [hBdef]; exact Finset.card_image_le)

/-- A generating finset of `(ℤ/2)^n` written multiplicatively has at least `n` elements. -/
private theorem card_le_card_of_closure_eq_top_pi {n : ℕ}
    (A : Finset (Fin n → Multiplicative (ZMod 2)))
    (hA : Subgroup.closure (A : Set (Fin n → Multiplicative (ZMod 2))) = ⊤) : n ≤ A.card := by
  classical
  have hgen : Subgroup.closure
      ((A.image (piMulEquivZmodTwo n) : Finset (Multiplicative (Fin n → ZMod 2))) :
        Set (Multiplicative (Fin n → ZMod 2))) = ⊤ := by
    have h1 : Subgroup.map (piMulEquivZmodTwo n).toMonoidHom
        (Subgroup.closure (A : Set (Fin n → Multiplicative (ZMod 2))))
        = Subgroup.closure ((piMulEquivZmodTwo n).toMonoidHom ''
            (A : Set (Fin n → Multiplicative (ZMod 2)))) :=
      MonoidHom.map_closure _ _
    rw [hA, Subgroup.map_top_of_surjective _ (piMulEquivZmodTwo n).surjective] at h1
    rw [Finset.coe_image]
    exact h1.symm
  calc n ≤ (A.image (piMulEquivZmodTwo n)).card :=
        card_le_card_of_closure_eq_top_multiplicative _ hgen
    _ ≤ A.card := Finset.card_image_le

/-! ## 4. The statement -/

/-- **The explicit finite model `GF` is the elementary abelian `2`-group of order `32`**, with
minimal generating number `5`.

`GF = FreeGroup (Fin 5) ⧸ Subgroup.normalClosure relF` where `relF` consists of the squares
`xᵢ ^ 2` and all commutators `⁅xᵢ, xⱼ⁆` of the five free generators
(`Submission/Work/ClassFieldTower/FiniteModelDefs.lean`).  Consequently:

* `GF` is finite (it is generated by five commuting involutions, so it is a quotient of
  `(ℤ/2)^5`);
* `GF ≃* F2five` (`F2five = Fin 5 → Multiplicative (ZMod 2)`);
* every generating finset `S` of `GF` has at least `5` elements (`F2five` needs five generators).

Proof strategy: define `π : FreeGroup (Fin 5) →* F2five` by `FreeGroup.lift` sending `i` to the
`i`-th basis vector of `(ℤ/2)^5`; the elements of `relF` lie in `ker π`, so `π` descends to a
surjection `GF ↠ F2five` (`QuotientGroup.lift`).  Conversely the images `gᵢ` of the generators in
`GF` commute and satisfy `gᵢ ^ 2 = 1` (they are killed by the relators, via
`QuotientGroup.eq_one_iff` and `Subgroup.le_normalClosure`), so the map
`(Fin 5 → Bool) → GF`, `b ↦ ∏ i, gᵢ ^ (bᵢ : ℕ)`, is a surjection onto the subgroup generated by
the `gᵢ` (which is `⊤`, from `FreeGroup.closure_range_of` and
`Subgroup.map_top_of_surjective`), whence `Nat.card GF ≤ 2^5` by
`Nat.card_le_card_of_surjective`.  Thus `Nat.card GF = 32`, `GF ≃* F2five` (surjection between
finite groups of equal cardinality), and the minimality of `5` follows from the same
`(ℤ/2)^5`-vector-space argument (cf. `Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five`),
since `S ↦ its image in F2five` generates `(ℤ/2)^5 = F2five`, which needs at least `5`
generators. -/
theorem finiteModel_GF : Finite GF ∧ Nonempty (GF ≃* F2five) ∧
    (∀ S : Finset GF, Subgroup.closure (S : Set GF) = ⊤ → 5 ≤ S.card) := by
  haveI : Finite GF := finite_GF
  haveI : Fintype GF := Fintype.ofFinite GF
  have hcard : Fintype.card GF = 32 := by
    refine le_antisymm ?_ ?_
    · have h := Fintype.card_le_of_surjective Pb Pb_surjective
      have h2 : Fintype.card (Fin 5 → Bool) = 32 := by simp
      rwa [h2] at h
    · have h := Fintype.card_le_of_surjective psiGF psiGF_surjective
      have h2 : Fintype.card F2five = 32 := by
        simp [Fintype.card_multiplicative]
      rwa [h2] at h
  have hbij : Function.Bijective psiGF := by
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨psiGF_surjective, by rw [hcard, Fintype.card_fun]; simp [Fintype.card_multiplicative]⟩
  refine ⟨inferInstance, ⟨MulEquiv.ofBijective psiGF hbij⟩, ?_⟩
  intro S hS
  have hImg : Subgroup.closure ((S.image psiGF : Finset F2five) : Set F2five) = ⊤ := by
    rw [Finset.coe_image, ← MonoidHom.map_closure psiGF (S : Set GF), hS,
      Subgroup.map_top_of_surjective _ psiGF_surjective]
  calc 5 ≤ (S.image psiGF).card := card_le_card_of_closure_eq_top_pi _ hImg
    _ ≤ S.card := Finset.card_image_le

end Work.ClassFieldTower

end
