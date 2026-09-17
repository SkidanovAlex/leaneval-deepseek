import Submission.E8Decomp
import Submission.E8ConstChar
import Submission.E8WCFM
import Submission.E8Trunc
import Submission.E8MtabUnitri

/-!
# The forty isotypic components of the tensor square

The Klimyk value `(A_ρ · ch T)(Λ i + ρ) = KbZ (ord40get i) = ccv i ≥ 1` computed in
`Submission/E8Trunc`/`Submission/E8Num40` shows that every one of the forty dominant weights
`Λ i ⪯ 2λ` is the highest weight of a simple constituent of `T N = (V ⧸ N) ⊗ (V ⧸ N)`.

Two simple constituents with distinct highest weights are non-isomorphic (their isotypic components
differ), so `T N` has at least forty isotypic components; with
`Submission.E8TensorBound.ncard_tensor_le_forty` this gives exactly forty.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8Ncard

open Submission.WCFSetup
open Submission.E8Character
open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Weights (SerreE SerreF SerreH)
open Commons.LinearAlgebra.Matrix.Cartan
open UniversalEnvelopingAlgebra

variable {N : Submodule U V}

/-! ## The top weight of a simple constituent -/

/-- A primitive vector of a dominant weight in a simple submodule of the tensor square. -/
structure PrimD (N : Submodule U V) (S : Submodule U (T N)) where
  /-- the index of the dominant weight -/
  i : Fin 40
  /-- the primitive vector -/
  x : T N
  hxS : x ∈ S
  hx0 : x ≠ 0
  hE : ∀ j, deriv (N := N) (SerreE j) x = 0
  hH : ∀ j, deriv (N := N) (SerreH j) x = (((Submission.E8Extract.ord40get i j : ℤ)) : ℂ) • x

/-- `the40` and `ord40` list the same weights. -/
theorem the40_toFinset_eq :
    (Submission.E8Enum.the40.toFinset : Finset (Fin 8 → ℤ))
      = Submission.E8Extract.ord40.toFinset := by decide

/-- A weight of `the40` is `ord40get i` for a unique `i`. -/
lemma mem_ord40 {ν : Fin 8 → ℤ} (h : ν ∈ Submission.E8Enum.the40) :
    ∃ i : Fin 40, Submission.E8Extract.ord40get i = ν := by
  have h' : ν ∈ Submission.E8Extract.ord40 := by
    have h1 : ν ∈ (Submission.E8Enum.the40.toFinset : Finset (Fin 8 → ℤ)) :=
      List.mem_toFinset.mpr h
    rw [the40_toFinset_eq] at h1
    exact List.mem_toFinset.mp h1
  have hlt' : Submission.E8Extract.ord40.idxOf ν
      < Submission.E8Extract.ord40.length := List.idxOf_lt_length_iff.mpr h'
  refine ⟨⟨Submission.E8Extract.ord40.idxOf ν, by
      rw [← Submission.E8Extract.ord40_length]; exact hlt'⟩, ?_⟩
  exact List.idxOf_get hlt'

/-- Every simple submodule of the tensor square carries such a primitive vector. -/
lemma exists_PrimD (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) {S : Submodule U (T N)}
    (hS : IsSimpleModule U S) : Nonempty (PrimD N S) := by
  obtain ⟨x, ν, hxS, hx0, hH, hE, hdom, hmem⟩ := exists_prim_of_simple N hvN hmax S hS
  obtain ⟨i, hi⟩ := mem_ord40 hmem
  refine ⟨{ i := i, x := x, hxS := hxS, hx0 := hx0, hE := hE, hH := ?_ }⟩
  intro j
  rw [hi]
  exact hH j

/-- The index of the highest weight of a simple submodule of the tensor square. -/
noncomputable def topIdx (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (S : Submodule U (T N))
    (hS : IsSimpleModule U S) : Fin 40 :=
  (Classical.choice (exists_PrimD N hvN hmax hS)).i

lemma topIdx_spec (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (S : Submodule U (T N))
    (hS : IsSimpleModule U S) :
    ∃ x : T N, x ∈ S ∧ x ≠ 0 ∧
      (∀ j, deriv (N := N) (SerreE j) x = 0) ∧
      (∀ j, deriv (N := N) (SerreH j) x
        = (((Submission.E8Extract.ord40get (topIdx N hvN hmax S hS) j : ℤ)) : ℂ) • x) := by
  let d := Classical.choice (exists_PrimD N hvN hmax hS)
  exact ⟨d.x, d.hxS, d.hx0, d.hE, d.hH⟩

/-! ## The support bound for primitive vectors -/

/-- **The support bound.**  If `x` and `y` are non-zero vectors of the simple submodule `S`, `x`
primitive of weight `ν` and `y` of weight `μ`, then `μ ⪯ ν`. -/
lemma posCon_of_primitive {S : Submodule U (T N)} [IsSimpleModule U S]
    {ν μ : Fin 8 → ℤ} {x y : T N}
    (hxS : x ∈ S) (hx0 : x ≠ 0)
    (hxE : ∀ j, deriv (N := N) (SerreE j) x = 0)
    (hxH : ∀ j, deriv (N := N) (SerreH j) x = (((ν j : ℤ)) : ℂ) • x)
    (hyS : y ∈ S) (hy0 : y ≠ 0)
    (hyH : ∀ j, deriv (N := N) (SerreH j) y = (((μ j : ℤ)) : ℂ) • y) :
    posCon (ν - μ) := by
  have hE : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreE j) • (⟨x, hxS⟩ : ↥S) = 0 := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, iota_smul_eq_deriv]
    exact hxE j
  have hH : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreH j) • (⟨x, hxS⟩ : ↥S)
      = (((ν j : ℤ)) : ℂ) • (⟨x, hxS⟩ : ↥S) := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, Submission.E8ConstChar.coe_smul_C, iota_smul_eq_deriv]
    exact hxH j
  have hyw : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreH j) • (⟨y, hyS⟩ : ↥S)
      = (((μ j : ℤ)) : ℂ) • (⟨y, hyS⟩ : ↥S) := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, Submission.E8ConstChar.coe_smul_C, iota_smul_eq_deriv]
    exact hyH j
  have hsupp := Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
    (M := ↥S) (⟨x, hxS⟩ : ↥S) ν
    (Submission.E8ConstChar.exists_smul_eq_of_simple hxS hx0) hE hH
    (fun hh => hy0 (Subtype.ext_iff.mp hh)) hyw
  intro j
  rw [← Submission.E8ConstChar.coords_eq]
  exact hsupp j

/-- Negation of the coordinates. -/
lemma coords_neg (a : Fin 8 → ℤ) :
    Submission.E8Character.coords (-a) = -Submission.E8Character.coords a := by
  funext i
  simp only [Submission.E8Character.coords, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- A weight in the cone together with its negative is zero. -/
lemma eq_zero_of_posCon_neg {δ : Fin 8 → ℤ} (h : posCon δ) (h' : posCon (-δ)) : δ = 0 := by
  have hc : Submission.E8Character.coords δ = 0 := by
    funext i
    have h1 := h i
    have h2 : 0 ≤ -(Submission.E8Character.coords δ i) := by
      have hh := h' i
      rwa [coords_neg] at hh
    exact le_antisymm (neg_nonneg.mp h2) h1
  have hm := Submission.E8Character.mulVec_coords δ
  rw [hc, Matrix.mulVec_zero] at hm
  exact hm.symm

/-! ## Transferring primitive vectors along a linear equivalence -/

/-- A `U`-linear equivalence is `ℂ`-linear. -/
lemma map_smul_C {S S' : Submodule U (T N)} (e : ↥S ≃ₗ[U] ↥S') (c : ℂ) (z : ↥S) :
    e (c • z) = c • e z := by
  haveI : IsScalarTower ℂ U ↥S := instISTSub S
  haveI : IsScalarTower ℂ U ↥S' := instISTSub S'
  rw [← IsScalarTower.algebraMap_smul (R := ℂ) (A := U) c z, map_smul,
    IsScalarTower.algebraMap_smul (R := ℂ) (A := U) c (e z)]

/-- A `U`-linear equivalence transfers a primitive vector of a simple submodule. -/
lemma transfer_primitive {S S' : Submodule U (T N)} (e : ↥S ≃ₗ[U] ↥S') {i : Fin 40} {x : T N}
    (hxS : x ∈ S) (hx0 : x ≠ 0)
    (hxH : ∀ j, deriv (N := N) (SerreH j) x
      = (((Submission.E8Extract.ord40get i j : ℤ)) : ℂ) • x) :
    ∃ y : T N, y ∈ S' ∧ y ≠ 0 ∧
      (∀ j, deriv (N := N) (SerreH j) y
        = (((Submission.E8Extract.ord40get i j : ℤ)) : ℂ) • y) := by
  set m : ↥S := ⟨x, hxS⟩ with hm
  have hm0 : m ≠ 0 := fun h => hx0 (Subtype.ext_iff.mp h)
  set m' : ↥S' := e m with hm'
  refine ⟨(m' : T N), m'.2, ?_, ?_⟩
  · intro h0
    have h1 : m' = 0 := Subtype.ext h0
    have h2 : m = 0 := e.injective (by rw [← hm', h1, map_zero])
    exact hm0 h2
  · intro j
    have hH : (UniversalEnvelopingAlgebra.ι ℂ (SerreH j)) • m
        = (((Submission.E8Extract.ord40get i j : ℤ)) : ℂ) • m := by
      refine Subtype.ext ?_
      rw [Submodule.coe_smul, Submission.E8ConstChar.coe_smul_C, iota_smul_eq_deriv]
      exact hxH j
    have hmap : (UniversalEnvelopingAlgebra.ι ℂ (SerreH j)) • m'
        = (((Submission.E8Extract.ord40get i j : ℤ)) : ℂ) • m' := by
      rw [hm', ← map_smul e (UniversalEnvelopingAlgebra.ι ℂ (SerreH j)) m, hH]
      exact map_smul_C e _ m
    have hT := congrArg (fun z : ↥S' => (z : T N)) hmap
    simp only [Submodule.coe_smul, Submission.E8ConstChar.coe_smul_C] at hT
    rw [← iota_smul_eq_deriv (N := N) (SerreH j) (m' : T N)]
    exact hT

/-- **Two simple submodules with the same isotypic component have the same highest weight.** -/
lemma topIdx_eq_of_isotypicComponent_eq (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) {S S' : Submodule U (T N)}
    (hS : IsSimpleModule U S) (hS' : IsSimpleModule U S')
    (h : isotypicComponent U (T N) S = isotypicComponent U (T N) S') :
    topIdx N hvN hmax S hS = topIdx N hvN hmax S' hS' := by
  haveI := hS
  haveI := hS'
  obtain ⟨x, hxS, hx0, hxE, hxH⟩ := topIdx_spec N hvN hmax S hS
  obtain ⟨x', hx'S', hx'0, hx'E, hx'H⟩ := topIdx_spec N hvN hmax S' hS'
  have hle : S ≤ isotypicComponent U (T N) S' := by
    rw [← h]; exact Submodule.le_isotypicComponent S
  obtain ⟨e⟩ := (isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent U (T N) S')) S hle
  obtain ⟨y, hyS', hy0, hyH⟩ := transfer_primitive (S := S) (S' := S') e hxS hx0 hxH
  have hcon1 := posCon_of_primitive hx'S' hx'0 hx'E hx'H hyS' hy0 hyH
  have hle' : S' ≤ isotypicComponent U (T N) S := by
    rw [h]; exact Submodule.le_isotypicComponent S'
  obtain ⟨e'⟩ := (isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent U (T N) S)) S' hle'
  obtain ⟨y', hy'S, hy'0, hy'H⟩ := transfer_primitive (S := S') (S' := S) e' hx'S' hx'0 hx'H
  have hcon2 := posCon_of_primitive hxS hx0 hxE hxH hy'S hy'0 hy'H
  have h3 : Submission.E8Extract.ord40get (topIdx N hvN hmax S hS)
      = Submission.E8Extract.ord40get (topIdx N hvN hmax S' hS') := by
    have hz := eq_zero_of_posCon_neg (δ := Submission.E8Extract.ord40get (topIdx N hvN hmax S hS)
      - Submission.E8Extract.ord40get (topIdx N hvN hmax S' hS')) hcon2
      (by rw [neg_sub]; exact hcon1)
    exact sub_eq_zero.mp hz
  exact Submission.E8MtabUnitri.ord40get_inj _ _ h3

/-! ## The Weyl sum of a constituent -/

/-- `WSum` is linear in its argument. -/
lemma WSum_mul_const (c : ℚ) (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ) :
    WSum (fun ν => c * f ν) x = c * WSum f x := by
  rw [WSum, WSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  ring

/-- **The Weyl sum of the character of a simple constituent.** -/
lemma WSum_chFun (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) {S : Submodule U (T N)}
    (hS : IsSimpleModule U S) (y : Fin 8 → ℤ) :
    WSum (fun ν => Submission.E8ConstChar.chFun N S ν) y
      = Submission.E8ConstChar.chFun N S
          (Submission.E8Extract.ord40get (topIdx N hvN hmax S hS))
        * Submission.E8WCFC.alt
            (Submission.E8Extract.ord40get (topIdx N hvN hmax S hS) + rhoV) y := by
  obtain ⟨x, hxS, hx0, hE, hH⟩ := topIdx_spec N hvN hmax S hS
  have hfun : (fun ν => Submission.E8ConstChar.chFun N S ν)
      = fun ν => Submission.E8ConstChar.chFun N S
          (Submission.E8Extract.ord40get (topIdx N hvN hmax S hS))
          * Submission.E8ConstChar.MnuQ (topIdx N hvN hmax S hS) ν := by
    funext μ
    rw [Submission.E8ConstChar.chFun_eq_Mnu hvN hmax hxS hx0 hE hH μ]
    rfl
  rw [hfun, WSum_mul_const, Submission.E8WCFM.WCF_constituent]

/-! ## Generic list-sum interchanges -/

/-- Interchanging a list sum with a finset sum. -/
lemma list_sum_finset_sum {β γ δ : Type*} [AddCommMonoid β] (l : List γ) (s : Finset δ)
    (h : γ → δ → β) :
    (∑ d ∈ s, (l.map (fun c => h c d)).sum) = (l.map (fun c => ∑ d ∈ s, h c d)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The Weyl sum of a list sum of functions. -/
lemma WSum_list_sum (l : List (Submodule U (T N)))
    (g : Submodule U (T N) → (Fin 8 → ℤ) → ℚ) (y : Fin 8 → ℤ) :
    WSum (fun ν => (l.map (fun S => g S ν)).sum) y = (l.map (fun S => WSum (g S) y)).sum := by
  rw [WSum]
  rw [Finset.sum_congr rfl (fun M _ => (List.sum_map_mul_left (r := (M.det : ℚ))
    (f := fun S => g S (y - ap M rhoV)) (l := l)).symm)]
  rw [list_sum_finset_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro S _
  rfl

/-! ## The Klimyk argument: every one of the forty weights occurs -/

theorem exists_constituent (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N)
    (hK : ∀ i : Fin 40, Submission.E8Trunc.KbZ (Submission.E8Extract.ord40get i)
      = Submission.E8Extract.ccv i) (i : Fin 40) :
    ∃ S : Submodule U (T N), ∃ hS : IsSimpleModule U S, topIdx N hvN hmax S hS = i := by
  classical
  haveI hfin : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  obtain ⟨l, hsimp, hchT⟩ := Submission.E8Decomp.chT_eq_sum_chFun N hvN hmax
  let F : Submodule U (T N) → ℚ := fun S =>
    if hS : IsSimpleModule U S then
      Submission.E8ConstChar.chFun N S
          (Submission.E8Extract.ord40get (topIdx N hvN hmax S hS))
        * (if Submission.E8Extract.ord40get (topIdx N hvN hmax S hS)
            = Submission.E8Extract.ord40get i then 1 else 0)
    else 0
  have h1 : WSum (fun ν => (Module.finrank ℂ ↥(TLwt N ν) : ℚ))
      (Submission.E8Extract.ord40get i + rhoV) = (l.map F).sum := by
    have hfun : (fun ν => (Module.finrank ℂ ↥(TLwt N ν) : ℚ))
        = fun ν => (l.map (fun S => Submission.E8ConstChar.chFun N S ν)).sum := funext hchT
    rw [hfun, WSum_list_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro S hS
    have hSS : IsSimpleModule U S := hsimp S hS
    have hFS : F S = Submission.E8ConstChar.chFun N S
        (Submission.E8Extract.ord40get (topIdx N hvN hmax S hSS))
        * (if Submission.E8Extract.ord40get (topIdx N hvN hmax S hSS)
            = Submission.E8Extract.ord40get i then 1 else 0) := by
      dsimp only [F]
      rw [dif_pos hSS]
    rw [WSum_chFun N hvN hmax (S := S) hSS, hFS, Submission.E8WCFM.alt_dominant]
  have h2 : (l.map F).sum = (Submission.E8Extract.ccv i : ℚ) := by
    rw [← h1, Submission.E8Trunc.WSum_chT_at N hvN hmax i, hK i]
  by_contra hcon
  push_neg at hcon
  have hzero_aux : ∀ m : List (Submodule U (T N)),
      (∀ S ∈ m, IsSimpleModule U S) →
      (∀ S ∈ m, ∀ hSS : IsSimpleModule U S, topIdx N hvN hmax S hSS ≠ i) →
      (m.map F).sum = 0 := by
    intro m
    induction m with
    | nil => intro _ _; rfl
    | cons S t ih =>
        intro hm hm'
        rw [List.map_cons, List.sum_cons,
          ih (fun S' hS' => hm S' (List.mem_cons_of_mem S hS'))
             (fun S' hS' hSS => hm' S' (List.mem_cons_of_mem S hS') hSS)]
        have hSS : IsSimpleModule U S := hm S List.mem_cons_self
        have hFS : F S = Submission.E8ConstChar.chFun N S
            (Submission.E8Extract.ord40get (topIdx N hvN hmax S hSS))
            * (if Submission.E8Extract.ord40get (topIdx N hvN hmax S hSS)
                = Submission.E8Extract.ord40get i then 1 else 0) := by
          dsimp only [F]
          rw [dif_pos hSS]
        rw [hFS, if_neg]
        · ring
        · intro hh
          exact hm' S List.mem_cons_self hSS
            (Submission.E8MtabUnitri.ord40get_inj _ _ hh)
  have hzero : (l.map F).sum = 0 := hzero_aux l hsimp (fun S hS hSS => hcon S hSS)
  rw [h2] at hzero
  have hpos : (0 : ℚ) < (Submission.E8Extract.ccv i : ℚ) := by
    have h1 : (1 : ℤ) ≤ Submission.E8Extract.ccv i := Submission.E8Extract.ccv_pos i
    have h2 : (1 : ℚ) ≤ (Submission.E8Extract.ccv i : ℚ) := by exact_mod_cast h1
    linarith
  linarith

/-! ## The forty isotypic components -/

theorem ncard_ge_forty (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N)
    (hK : ∀ i : Fin 40, Submission.E8Trunc.KbZ (Submission.E8Extract.ord40get i)
      = Submission.E8Extract.ccv i) :
    40 ≤ (isotypicComponents U (T N)).ncard := by
  classical
  haveI hfin : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  haveI hnoeth : IsNoetherian U (T N) :=
    isNoetherian_of_tower ℂ (isNoetherian_of_isNoetherianRing_of_finite ℂ (T N))
  choose S hS using fun i : Fin 40 => exists_constituent N hvN hmax hK i
  set c : Fin 40 → isotypicComponents U (T N) := fun i =>
    ⟨isotypicComponent U (T N) (S i), ⟨S i, (hS i).1, rfl⟩⟩ with hc
  have hcinj : Function.Injective c := by
    intro i j hij
    have hval : isotypicComponent U (T N) (S i) = isotypicComponent U (T N) (S j) :=
      Subtype.ext_iff.mp hij
    have htop := topIdx_eq_of_isotypicComponent_eq N hvN hmax (hS i).1 (hS j).1 hval
    rw [(hS i).2, (hS j).2] at htop
    exact htop
  have h40 : (Set.range (fun i : Fin 40 => (c i : Submodule U (T N)))).ncard = 40 := by
    rw [Set.ncard_range_of_injective (f := fun i : Fin 40 => (c i : Submodule U (T N)))
      (fun i j hij => hcinj (Subtype.ext hij))]
    simp
  calc (40 : ℕ) = (Set.range (fun i : Fin 40 => (c i : Submodule U (T N)))).ncard := h40.symm
    _ ≤ (isotypicComponents U (T N)).ncard :=
        Set.ncard_le_ncard (Set.range_subset_iff.mpr (fun i => (c i).2))

/-! ## The final assembly -/

/-- **The main theorem**, given the numerical input `KbZ (ord40get i) = ccv i` for the forty
dominant weights (proved by `decide` in `Submission.E8Num40`). -/
theorem main_assembly (hK : ∀ i : Fin 40, Submission.E8Trunc.KbZ
      (Submission.E8Extract.ord40get i) = Submission.E8Extract.ccv i) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) W) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) W),
      Module.finrank ℂ W = 779247 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) W ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ))
        (W ⊗[ℂ] W)).ncard = 40 := by
  obtain ⟨N, hvN, hmax⟩ := Submission.VermaWeight.exists_max_submodule
  refine ⟨Submission.VermaWeight.V ⧸ N, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · exact Submission.E8Finrank.finrank_eq N hvN hmax
  · rw [Commons.RepresentationTheory.LieEnveloping.isIrreducible_iff_isSimpleModule
      (M := Submission.VermaWeight.V ⧸ N) (fun x m => rfl)]
    exact Submission.VermaWeight.quotient_isSimpleModule hvN hmax
  · exact le_antisymm (Submission.E8TensorBound.ncard_tensor_le_forty N hvN hmax)
      (ncard_ge_forty N hvN hmax hK)

end Submission.E8Ncard
