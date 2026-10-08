/-
Bender–Glauberman 1981, §4 (pp. 213–214): **CONG-CONTRA**, the congruence contradiction.

`Work.GW2.C23.CongContraProp D C` says that in the situation `|S| = 4` (`D.n = 2`, the
nontrivial `β₂ : H₀/U → ℂˣ`, `δ_ν = (ν - λ₂ν)^G`, `𝒮'(χ) = bset' C β₂ χ`) there is **no**
configuration of `χ₁, ψ₁, ψ₂, ψ₃ ∈ ±Irr(G)` and pairwise distinct `ν₁, ν₂, ν₃` with

  `𝒮'(χ₁) = {ν₁,ν₂,ν₃}`,  `𝒮'(ψ₁) = {ν₁}`,  `𝒮'(ψ₂) = {ν₂}`,  `𝒮'(ψ₃) = {ν₃}`.

The proof follows the paper.

* Fix a hat `ν̂ ∈ Irr(B)` for every `ν ∈ 𝒮₄` (`Hat`), unique (`Hat`), injective (`hatInj`).
* `L41 (iii)` (`l41iii`) gives `χ ≡ Σ_{ν∈𝒮'(χ)} ν̂` modulo `2` on `B`, and `L41 (iv)`
  (`lemma41`) gives that `χ(1)` is odd.  These are the two character-theoretic inputs.
* **(CC1)** For `χ ∈ ±Irr(G)` of odd degree and `g ∈ G`: `ω_χ(ĝ) ≡ χ(g)` if `|G : C_G(g)|` is
  odd and `≡ 0` otherwise, where `ω_χ(ĝ) = |G : C_G(g)|·χ(g)/χ(1)` is the central-character
  value at the class sum of `g`.  The parity input is the Sylow fact that `|G : C_G(g)|` is odd
  iff `g` is conjugate into `C_G(S)` (`congOddConj`), together with `C_G(S) = S·B` (`congCGS`)
  and Lemma 1.6 (`lemma16_mod_two`).
* **(CC2)** The central characters are multiplicative: `ω_χ(C_i)·ω_χ(C_j) = Σ_s a_{ijs}ω_χ(C_s)`
  with **natural number** structure constants (`centralCharacterOfRep_classSum_mul`,
  `classSum_mul_apply`).  Hence for `a, b ∈ B` the crossed congruence below holds.
* **(CC3)** `modTwoIndep` (Lemma 1.8) applied to the crossed difference gives
  `θ₁(a) + θ₃(a) ≡ 0` for all `a ∈ B`, and applied once more to the distinct irreducibles
  `θ₁ ≠ θ₃` gives `1 ≡ 0 (mod 2)`, a contradiction.
-/
import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.l41iii
import Submission.Work.BG.hatInj
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.lemma16_mod_two
import Submission.Work.BG.classMult
import Submission.Work.BG.kappaExists
import Submission.Work.BG.invJCard
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.congDeps
import Submission.Work.BG.splitglue.Split
import Submission.OddOrder.Algebra.AlgInt

set_option maxHeartbeats 1000000

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 Subgroup
open OddOrder.GroupTheory.CenterClassSum
open scoped MonoidAlgebra Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Elementary algebra of `≡ (mod 2)` -/

/-- The product rule for the congruence `≡ (mod 2)` of algebraic integers. -/
theorem algIntModTwo_mul {x y x' y' : ℂ} (hx : IsIntegral ℤ x) (hy' : IsIntegral ℤ y')
    (h : AlgIntModTwo x y) (h' : AlgIntModTwo x' y') : AlgIntModTwo (x * x') (y * y') := by
  obtain ⟨c, hc, hc'⟩ := h
  obtain ⟨d, hd, hd'⟩ := h'
  refine ⟨x * d + c * y', (hx.mul hd).add (hc.mul hy'), ?_⟩
  linear_combination x * hd' + hc' * y'

/-- `1 : ℂ` is not congruent to `0` modulo `2`. -/
theorem not_algIntModTwo_one_zero : ¬ AlgIntModTwo (1 : ℂ) 0 := by
  rintro ⟨c, hc, hc'⟩
  have hc'' : (1 : ℂ) = 2 * c := by simpa using hc'
  have h2 : ((1 / 2 : ℚ) : ℂ) = c := by
    rw [show ((1 / 2 : ℚ) : ℂ) = (1 : ℂ) / 2 by norm_num, hc'']
    field_simp
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int (q := (1 / 2 : ℚ))
    (by rw [h2]; exact hc)
  have h4 : ((1 / 2 : ℚ) : ℂ) = (n : ℂ) := hn
  have h5 : (1 / 2 : ℚ) = (n : ℚ) := by exact_mod_cast h4
  have h6 : (1 : ℚ) = 2 * ((n : ℤ) : ℚ) := by linarith
  have h7 : (1 : ℤ) = 2 * n := by exact_mod_cast h6
  omega

/-- An integer, cast to `ℂ`, is an algebraic integer. -/
theorem isIntegral_intCast_complex (n : ℤ) : IsIntegral ℤ ((n : ℂ)) := by
  have h : IsIntegral ℤ (algebraMap ℤ ℂ n) := isIntegral_algebraMap
  rw [algebraMap_int_eq] at h
  simpa using h

/-- A natural number, cast to `ℂ`, is an algebraic integer. -/
theorem isIntegral_natCast_complex (n : ℕ) : IsIntegral ℤ ((n : ℂ)) := by
  have h : IsIntegral ℤ (algebraMap ℤ ℂ (n : ℤ)) := isIntegral_algebraMap
  rw [algebraMap_int_eq] at h
  simpa using h

/-- `AlgIntModTwo` converted into the divisibility form `≡ (mod 2)` of `OddOrder.AlgInt`. -/
theorem algIntModTwo_to_cong {a b : ℂ} (h : AlgIntModTwo a b) : OddOrder.AlgInt.Cong 2 a b := by
  obtain ⟨c, hc, hcab⟩ := h
  exact show IsIntegral ℤ ((a - b) / (2 : ℂ)) from by
    rw [show (a - b) / (2 : ℂ) = c by rw [hcab]; ring]
    exact hc

/-- The degree of an irreducible character of a finite group of odd order is an odd natural. -/
theorem exists_odd_nat_degree {K : Type} [Group K] [Finite K] (hK : Odd (Nat.card K))
    {φ : ClassFunction K ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∃ n : ℕ, Odd n ∧ φ 1 = (n : ℂ) := by
  obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := hφ
  letI := hV1
  letI := hV2
  letI := hV3
  haveI : Representation.IsIrreducible ρ := hρ
  have hdvd : Module.finrank ℂ V ∣ Nat.card K := finrank_dvd_card ρ
  refine ⟨Module.finrank ℂ V, hK.of_dvd_nat hdvd, ?_⟩
  rw [congrFun hchar 1, ρ.char_one]

/-- The degree of a signed irreducible character of `G` is an integer. -/
theorem exists_int_degree {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ) :
    ∃ d : ℤ, φ 1 = (d : ℂ) := by
  rcases hφ with h | h
  · obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := h
    letI := hV1
    letI := hV2
    letI := hV3
    refine ⟨(Module.finrank ℂ V : ℤ), ?_⟩
    rw [congrFun hchar 1, ρ.char_one]
    push_cast
    rfl
  · obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := h
    letI := hV1
    letI := hV2
    letI := hV3
    refine ⟨-(Module.finrank ℂ V : ℤ), ?_⟩
    have hneg : (-φ) 1 = -(φ 1) := rfl
    have h1 : (-φ) 1 = ((Module.finrank ℂ V : ℕ) : ℂ) := by
      rw [congrFun hchar 1, ρ.char_one]
    rw [show φ 1 = -((-φ) 1) from by rw [hneg]; ring, h1]
    push_cast
    rfl

/-- An irreducible character has nonzero degree. -/
theorem isIrreducibleCharacter_one_ne_zero {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) : φ 1 ≠ 0 := by
  obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := hφ
  haveI : Representation.IsIrreducible ρ := hρ
  have := nontrivial_of_isIrreducible ρ
  rw [congrFun hchar 1, ρ.char_one]
  exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

/-- The class function of an irreducible representation. -/
theorem eq_repCharacterClassFunction {φ : ClassFunction G ℂ} {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (h : (φ : G → ℂ) = ρ.character) : φ = repCharacterClassFunction ρ :=
  ClassFunction.ext fun g => (congrFun h g).trans (repCharacterClassFunction_apply ρ g).symm

/-! ## 1. Group-theoretic facts in the case `|S| = 4` -/

/-- For `D.n = 2` the Sylow `2`-subgroup `S` is commutative. -/
theorem congS_comm (D : BGData G) (hn : D.n = 2) {x y : G}
    (hx : x ∈ (D.S : Subgroup G)) (hy : y ∈ (D.S : Subgroup G)) : x * y = y * x := by
  obtain ⟨e⟩ := D.dih
  have hcommd : IsMulCommutative (DihedralGroup D.n) :=
    DihedralGroup.commutative_iff.mpr (Or.inr hn)
  have hkey : e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul]
    exact hcommd.is_comm.comm _ _
  exact Subtype.ext_iff.mp (e.injective hkey)

/-- For `D.n = 2` every element of `S` is an involution. -/
theorem congS_sq (D : BGData G) (hn : D.n = 2) {v : G} (hv : v ∈ (D.S : Subgroup G)) :
    v * v = 1 := by
  obtain ⟨e⟩ := D.dih
  haveI : IsKleinFour (DihedralGroup D.n) := by rw [hn]; infer_instance
  have h2 : e (⟨v, hv⟩ * ⟨v, hv⟩) = e 1 := by
    rw [map_mul, map_one]
    exact IsKleinFour.mul_self _
  have h3 : (⟨v, hv⟩ : ↥(D.S : Subgroup G)) * ⟨v, hv⟩ = 1 := e.injective h2
  exact congrArg Subtype.val h3

/-- In the case `|S| = 4`, `D.B ≤ D.U`. -/
theorem congB_le_U (D : BGData G) : D.B ≤ D.U := inf_le_left.trans inf_le_left

/-- `b ∈ B` has odd centralizer index. -/
theorem congB_index_odd (D : BGData G) (hn : D.n = 2) {b : G} (hb : b ∈ D.B) :
    Odd (Subgroup.centralizer ({b} : Set G)).index := by
  have hS : (D.S : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hb)) x hx
  have hSodd : Odd (D.S : Subgroup G).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Sylow.not_dvd_index D.S
  refine hSodd.of_dvd_nat ?_
  refine ⟨(D.S : Subgroup G).relIndex (Subgroup.centralizer ({b} : Set G)), ?_⟩
  exact (relIndex_mul_index hS).symm.trans (mul_comm _ _)

/-- `Odd (Nat.card ↥D.B)`. -/
theorem congB_card_odd (D : BGData G) [Fintype G] : Odd (Nat.card ↥D.B) :=
  (odd_card_U D).of_dvd_nat (Subgroup.card_dvd_of_le (congB_le_U D))

/-- An element of `C_G(S)` is a product `s · b` with `s ∈ S`, `b ∈ B` (the case `D.n = 2`).

Since `H = U · S` and `S` is abelian, an element of `C_G(S) ⊆ C_G(t) = H` that centralizes `S`
has its `U`-part centralized by `t₁, t₂`, i.e. in `B`. -/
theorem congCGS' [Fintype G] (D : BGData G) (hn : D.n = 2) (h : G)
    (hh : ∀ x ∈ (D.S : Subgroup G), x * h = h * x) :
    ∃ s ∈ (D.S : Subgroup G), ∃ b ∈ D.B, h = s * b := by
  have hsplit : D.U ⊔ (D.S : Subgroup G) = D.H :=
    SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (S_le_H D hx))
  have ht : h * D.t = D.t * h := (hh D.t (D.S0_le D.t_mem)).symm
  have hhH : h ∈ D.H := by
    rw [show D.H = Subgroup.centralizer ({D.t} : Set G) from rfl,
      Subgroup.mem_centralizer_singleton_iff]
    exact ht
  have hmem : h ∈ (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) := by
    rw [← coe_U_sup_S D]
    exact hsplit.symm ▸ hhH
  obtain ⟨u, huU, v, hvS, huv⟩ := Set.mem_mul.mp hmem
  have hu1 : u * D.t1 = D.t1 * u := by
    have h1 : D.t1 * (u * v) = (u * v) * D.t1 := by
      have h0 : D.t1 * h = h * D.t1 := hh D.t1 D.t1_mem
      rwa [← huv] at h0
    have hv1 : v * D.t1 = D.t1 * v := congS_comm D hn hvS D.t1_mem
    have h2 : (D.t1 * u) * v = (u * D.t1) * v := by
      calc (D.t1 * u) * v = D.t1 * (u * v) := by rw [mul_assoc]
        _ = (u * v) * D.t1 := h1
        _ = u * (v * D.t1) := by rw [mul_assoc]
        _ = u * (D.t1 * v) := by rw [hv1]
        _ = (u * D.t1) * v := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  have hu2 : u * D.t2 = D.t2 * u := by
    have h1 : D.t2 * (u * v) = (u * v) * D.t2 := by
      have h0 : D.t2 * h = h * D.t2 := hh D.t2 D.t2_mem
      rwa [← huv] at h0
    have hv2 : v * D.t2 = D.t2 * v := congS_comm D hn hvS D.t2_mem
    have h2 : (D.t2 * u) * v = (u * D.t2) * v := by
      calc (D.t2 * u) * v = D.t2 * (u * v) := by rw [mul_assoc]
        _ = (u * v) * D.t2 := h1
        _ = u * (v * D.t2) := by rw [mul_assoc]
        _ = u * (D.t2 * v) := by rw [hv2]
        _ = (u * D.t2) * v := by rw [mul_assoc]
    exact (mul_right_cancel h2).symm
  have hU1 : u ∈ Subgroup.centralizer ({D.t1} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hu1.symm
  have hU2 : u ∈ Subgroup.centralizer ({D.t2} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hu2.symm
  have huB : u ∈ D.B := ⟨⟨huU, hU1⟩, huU, hU2⟩
  have huv' : u * v = v * u :=
    ((Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D huB)) v hvS).symm
  exact ⟨v, hvS, u, huB, by rw [← huv, huv']⟩

instance instMulActionConjClass (S : Subgroup G) (g : G) :
    MulAction S {x : G // IsConj g x} where
  smul s x := ⟨(s : G) * (x : G) * (s : G)⁻¹, by
    obtain ⟨c, hc⟩ := isConj_iff.mp x.2
    rw [isConj_iff]
    refine ⟨(s : G) * c, ?_⟩
    rw [mul_inv_rev]
    calc (s : G) * c * g * (c⁻¹ * (s : G)⁻¹)
        = (s : G) * (c * g * c⁻¹) * (s : G)⁻¹ := by group
      _ = (s : G) * (x : G) * (s : G)⁻¹ := by rw [hc]⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  mul_smul s t x := by
    apply Subtype.ext
    show ((s : G) * (t : G)) * (x : G) * ((s : G) * (t : G))⁻¹
      = (s : G) * ((t : G) * (x : G) * (t : G)⁻¹) * (s : G)⁻¹
    rw [mul_inv_rev]
    group

/-- If `|G : C_G(g)|` is odd then `g` is conjugate to an element centralized by the Sylow
`2`-subgroup `S` (a `2`-group acting on an odd-sized set has a fixed point). -/
theorem congOddConj' (S : Sylow 2 G) (g : G)
    (hg : Odd (Subgroup.centralizer ({g} : Set G)).index) :
    ∃ h : G, IsConj g h ∧ ∀ s ∈ (S : Set G), s * h = h * s := by
  classical
  haveI : Fintype {x : G // IsConj g x} := Fintype.ofFinite _
  have hcard : (Subgroup.centralizer ({g} : Set G)).index
      = Nat.card {x : G // IsConj g x} := by
    rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq]
    rfl
  have hne : ¬ 2 ∣ Nat.card {x : G // IsConj g x} := by
    rw [← hcard, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hg
  haveI hS2 : IsPGroup 2 ↥(S : Subgroup G) := S.isPGroup'
  obtain ⟨x, hx⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card (p := 2) hS2
    {x : G // IsConj g x} hne
  refine ⟨x.1, x.2, fun s hs => ?_⟩
  have hfix : (⟨s, hs⟩ : ↥(S : Subgroup G)) • x = x :=
    (MulAction.mem_fixedPoints.mp hx) ⟨s, hs⟩
  have hval : s * x.1 * s⁻¹ = x.1 := congrArg Subtype.val hfix
  calc s * x.1 = (s * x.1 * s⁻¹) * s := by group
    _ = x.1 * s := by rw [hval]

/-! ## 2. Central characters -/

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- `ω_φ(C) = |C|·φ(g_C)/φ(1)` for a conjugacy class `C` with representative `C.out`. -/
noncomputable def omegaClass (φ : ClassFunction G ℂ) (C : ConjClasses G) : ℂ :=
  (Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * φ C.out / φ 1

/-- `ω_φ(g) = |G : C_G(g)|·φ(g)/φ(1)`. -/
noncomputable def omegaVal (φ : ClassFunction G ℂ) (g : G) : ℂ :=
  ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * φ g / φ 1

theorem omegaVal_eq_omegaClass (φ : ClassFunction G ℂ) (g : G) :
    omegaVal φ g = omegaClass φ (ConjClasses.mk g) := by
  rw [omegaVal, omegaClass, Work.BG.centralizer_index_eq_natCard_conjClass g]
  rw [φ.of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp (conjClass_mk_out (ConjClasses.mk g)))]

theorem omegaVal_neg (φ : ClassFunction G ℂ) (g : G) : omegaVal (-φ) g = omegaVal φ g := by
  rw [omegaVal, omegaVal]
  simp only [ClassFunction.neg_apply]
  rw [mul_neg, neg_div_neg_eq]

theorem omegaClass_neg (φ : ClassFunction G ℂ) (C : ConjClasses G) :
    omegaClass (-φ) C = omegaClass φ C := by
  rw [omegaClass, omegaClass]
  simp only [ClassFunction.neg_apply]
  rw [mul_neg, neg_div_neg_eq]

/-- The central character `ω_ρ` of an irreducible representation, evaluated at a class sum,
agrees with `omegaClass` of its character. -/
theorem omegaClass_eq_centralCharacter {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (C : ConjClasses G) :
    omegaClass (repCharacterClassFunction ρ) C
      = centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ := by
  rw [omegaClass, centralCharacterOfRep_classSum,
    sum_character_eq_card_mul ρ C (conjClass_mk_out C)]
  simp only [repCharacterClassFunction_apply, ρ.char_one]

/-- **(CC2)**, representation form: the central-character product formula, with natural-number
structure constants. -/
theorem omegaClass_mul_rep {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (Ci Cj : ConjClasses G) :
    omegaClass (repCharacterClassFunction ρ) Ci * omegaClass (repCharacterClassFunction ρ) Cj =
      ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) *
        omegaClass (repCharacterClassFunction ρ) Cs := by
  rw [omegaClass_eq_centralCharacter ρ Ci, omegaClass_eq_centralCharacter ρ Cj,
    centralCharacterOfRep_classSum_mul]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  rw [omegaClass_eq_centralCharacter ρ Cs, smul_eq_mul]

/-- `omegaClass` of an irreducible character satisfies the product formula. -/
theorem omegaClass_mul_irr {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ)
    (Ci Cj : ConjClasses G) :
    omegaClass φ Ci * omegaClass φ Cj =
      ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass φ Cs := by
  obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := hφ
  letI := hV1
  letI := hV2
  letI := hV3
  haveI : Representation.IsIrreducible ρ := hρ
  rw [eq_repCharacterClassFunction hchar]
  exact omegaClass_mul_rep ρ Ci Cj

/-- `omegaClass` of a signed irreducible character satisfies the product formula. -/
theorem omegaClass_mul_pm {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ) (Ci Cj : ConjClasses G) :
    omegaClass φ Ci * omegaClass φ Cj =
      ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass φ Cs := by
  rcases hφ with h | h
  · exact omegaClass_mul_irr h Ci Cj
  · have h1 := omegaClass_mul_irr (φ := -φ) h Ci Cj
    have h2 : (∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass (-φ) Cs)
        = ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass φ Cs :=
      Finset.sum_congr rfl fun Cs _ => by rw [omegaClass_neg φ Cs]
    calc omegaClass φ Ci * omegaClass φ Cj
        = omegaClass (-φ) Ci * omegaClass (-φ) Cj := by
          rw [omegaClass_neg φ Ci, omegaClass_neg φ Cj]
      _ = ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass (-φ) Cs := h1
      _ = ∑ Cs, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * omegaClass φ Cs := h2

/-- The structure constants of the class algebra are algebraic integers. -/
theorem coeff_classSum_mul_isIntegral (Ci Cj : ConjClasses G) (g : G) :
    IsIntegral ℤ ((classSum Ci * classSum Cj : ℂ[G]).coeff g) := by
  classical
  rw [classSum_mul_apply]
  exact isIntegral_natCast_complex _

/-- `omegaClass` is integral on irreducible characters. -/
theorem omegaClass_isIntegral {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ)
    (C : ConjClasses G) : IsIntegral ℤ (omegaClass φ C) := by
  obtain ⟨V, hV1, hV2, hV3, ρ, hρ, hchar⟩ := hφ
  letI := hV1
  letI := hV2
  letI := hV3
  haveI : Representation.IsIrreducible ρ := hρ
  have h := isIntegral_card_mul_character_div ρ C (conjClass_mk_out C)
  rw [eq_repCharacterClassFunction hchar]
  simpa [omegaClass] using h

/-- `omegaVal` is integral on signed irreducible characters. -/
theorem omegaVal_isIntegral_pm {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ) (g : G) :
    IsIntegral ℤ (omegaVal φ g) := by
  rcases hφ with h | h
  · rw [omegaVal_eq_omegaClass]
    exact omegaClass_isIntegral h _
  · rw [← omegaVal_neg φ g, omegaVal_eq_omegaClass]
    exact omegaClass_isIntegral h _

/-! ## 3. The congruence `ω_φ(g) ≡ φ(g)` -/

/-- **(CC1), irreducible case, odd index**: `ω_φ(g) ≡ φ(g) (mod 2)`. -/
theorem omegaVal_cong_odd {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ)
    {d : ℤ} (hd : Odd d) (hdeg : φ 1 = (d : ℂ)) {g : G}
    (hg : Odd (Subgroup.centralizer ({g} : Set G)).index) :
    AlgIntModTwo (omegaVal φ g) (φ g) := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨m, hm⟩ := hd
  have hφint : IsIntegral ℤ (φ g) := isIntegral_apply_of_isIrreducibleCharacter hφ g
  have hΩ : IsIntegral ℤ (omegaVal φ g) := omegaVal_isIntegral_pm (Or.inl hφ) g
  refine ⟨(k : ℂ) * φ g - (m : ℂ) * omegaVal φ g, ?_, ?_⟩
  · exact ((isIntegral_intCast_complex (k : ℤ)).mul hφint).sub
      ((isIntegral_intCast_complex (m : ℤ)).mul hΩ)
  · have hdne : (d : ℂ) ≠ 0 := by rw [← hdeg]; exact isIrreducibleCharacter_one_ne_zero hφ
    have h1 : omegaVal φ g * (d : ℂ)
        = ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * φ g := by
      rw [omegaVal, hdeg]
      field_simp
    have hd' : (d : ℂ) = 2 * (m : ℂ) + 1 := by rw [hm]; push_cast; ring
    have hn : ((Subgroup.centralizer ({g} : Set G)).index : ℂ) = 2 * (k : ℂ) + 1 := by
      rw [hk]; push_cast; ring
    linear_combination h1 - omegaVal φ g * hd' + φ g * hn

/-- **(CC1), irreducible case, even index**: `ω_φ(g) ≡ 0 (mod 2)`. -/
theorem omegaVal_cong_even {φ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ)
    {d : ℤ} (hd : Odd d) (hdeg : φ 1 = (d : ℂ)) {g : G}
    (hg : ¬ Odd (Subgroup.centralizer ({g} : Set G)).index) :
    AlgIntModTwo (omegaVal φ g) 0 := by
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hg
  obtain ⟨m, hm⟩ := hd
  have hφint : IsIntegral ℤ (φ g) := isIntegral_apply_of_isIrreducibleCharacter hφ g
  have hΩ : IsIntegral ℤ (omegaVal φ g) := omegaVal_isIntegral_pm (Or.inl hφ) g
  refine ⟨(k : ℂ) * φ g - (m : ℂ) * omegaVal φ g, ?_, ?_⟩
  · exact ((isIntegral_intCast_complex (k : ℤ)).mul hφint).sub
      ((isIntegral_intCast_complex (m : ℤ)).mul hΩ)
  · have hdne : (d : ℂ) ≠ 0 := by rw [← hdeg]; exact isIrreducibleCharacter_one_ne_zero hφ
    have h1 : omegaVal φ g * (d : ℂ)
        = ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * φ g := by
      rw [omegaVal, hdeg]
      field_simp
    have hd' : (d : ℂ) = 2 * (m : ℂ) + 1 := by rw [hm]; push_cast; ring
    have hn : ((Subgroup.centralizer ({g} : Set G)).index : ℂ) = 2 * (k : ℂ) := by
      rw [hk]; push_cast; ring
    linear_combination h1 - omegaVal φ g * hd' + φ g * hn

/-- **(CC1)** for signed irreducible characters, odd index. -/
theorem omegaVal_cong_odd_pm {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ)
    {d : ℤ} (hd : Odd d) (hdeg : φ 1 = (d : ℂ)) {g : G}
    (hg : Odd (Subgroup.centralizer ({g} : Set G)).index) :
    AlgIntModTwo (omegaVal φ g) (φ g) := by
  rcases hφ with h | h
  · exact omegaVal_cong_odd h hd hdeg hg
  · have hdeg' : (-φ) 1 = ((-d : ℤ) : ℂ) := by
      simp only [ClassFunction.neg_apply]
      rw [hdeg]
      push_cast
      ring
    have h2 := omegaVal_cong_odd (φ := -φ) h hd.neg hdeg' hg
    rw [omegaVal_neg] at h2
    have hint : IsIntegral ℤ (φ g) := by
      simpa using (isIntegral_apply_of_isIrreducibleCharacter h g).neg
    exact h2.trans (AlgIntModTwo.neg_self hint)

/-- **(CC1)** for signed irreducible characters, even index. -/
theorem omegaVal_cong_even_pm {φ : ClassFunction G ℂ} (hφ : IsPmIrr φ)
    {d : ℤ} (hd : Odd d) (hdeg : φ 1 = (d : ℂ)) {g : G}
    (hg : ¬ Odd (Subgroup.centralizer ({g} : Set G)).index) :
    AlgIntModTwo (omegaVal φ g) 0 := by
  rcases hφ with h | h
  · exact omegaVal_cong_even h hd hdeg hg
  · have hdeg' : (-φ) 1 = ((-d : ℤ) : ℂ) := by
      simp only [ClassFunction.neg_apply]
      rw [hdeg]
      push_cast
      ring
    have h2 := omegaVal_cong_even (φ := -φ) h hd.neg hdeg' hg
    rw [omegaVal_neg] at h2
    exact h2

/-! ## 4. Vectors are injective, and finite sums over three-element sets -/

theorem fin_two_injective {α : Type*} {a b : α} (hab : a ≠ b) :
    Function.Injective (![a, b] : Fin 2 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one] at hij
  · rfl
  · exact absurd hij hab
  · exact absurd hij.symm hab
  · rfl

theorem fin_three_injective {α : Type*} {a b c : α} (h12 : a ≠ b) (h13 : a ≠ c)
    (h23 : b ≠ c) : Function.Injective (![a, b, c] : Fin 3 → α) := by
  have e0 : (![a, b, c] : Fin 3 → α) 0 = a := rfl
  have e1 : (![a, b, c] : Fin 3 → α) 1 = b := rfl
  have e2 : (![a, b, c] : Fin 3 → α) 2 = c := rfl
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [e0, e1, e2] at hij <;>
    first
      | rfl
      | exact absurd hij h12
      | exact absurd hij h13
      | exact absurd hij h23
      | exact absurd hij.symm h12
      | exact absurd hij.symm h13
      | exact absurd hij.symm h23

theorem finsum_mem_three {α M : Type*} [AddCommMonoid M] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (f : α → M) :
    (∑ᶠ x ∈ ({a, b, c} : Set α), f x) = f a + f b + f c := by
  rw [show ({a, b, c} : Set α) = insert a (insert b (insert c (∅ : Set α))) by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]]
  rw [finsum_mem_insert f (by simp [hab, hac]) ((Set.finite_empty.insert c).insert b),
    finsum_mem_insert f (by simp [hbc]) (Set.finite_empty.insert c),
    finsum_mem_insert f (by simp) Set.finite_empty, finsum_mem_empty]
  abel

/-! ## 5. CONG-CONTRA -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem congContra {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.CongContraProp D C := by
  classical
  intro hc hn β₂ hβ ν₁ ν₂ ν₃ h12 h13 h23 χ₁ ψ₁ ψ₂ ψ₃ hχ₁ hψ₁ hψ₂ hψ₃ hb1 hb2 hb3 hb4
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  haveI : Fintype ↥D.B := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥D.B : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- membership of the `νᵢ` in `𝒮'(χ)`
  have hm1 : ν₁ ∈ bset' C β₂ χ₁ := by rw [hb1]; simp
  have hm2 : ν₁ ∈ bset' C β₂ ψ₁ := by rw [hb2]; simp
  have hm3 : ν₂ ∈ bset' C β₂ ψ₂ := by rw [hb3]; simp
  have hm4 : ν₃ ∈ bset' C β₂ ψ₃ := by rw [hb4]; simp
  have hν1 : ν₁ ∈ S4Index C := hm1.1
  have hν2 : ν₂ ∈ S4Index C := hm3.1
  have hν3 : ν₃ ∈ S4Index C := hm4.1
  -- the hat map `ν ↦ ν̂`
  let Θ : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥D.B ℂ := fun ν =>
    if h : ν ∈ S4Index C then (Hat D C hc hn ν h).1.choose else 0
  have hΘ : ∀ ν (h : ν ∈ S4Index C), HatOf D C ν (Θ ν) := by
    intro ν h
    dsimp only [Θ]
    rw [dif_pos h]
    exact (Hat D C hc hn ν h).1.choose_spec
  have hΘint : ∀ ν (h : ν ∈ S4Index C), IsIrreducibleCharacter (Θ ν) := fun ν h => (hΘ ν h).1
  have hΘinj : ∀ ν μ (hν : ν ∈ S4Index C) (hμ : μ ∈ S4Index C), Θ ν = Θ μ → ν = μ := by
    intro ν μ hν hμ h
    exact hatInj D C hc hn ν hν μ hμ (Θ ν) (hΘ ν hν) (h ▸ hΘ μ hμ)
  -- Odd degrees (BG Lemma 4.1 (iv)).  `L41 (iii)` at the identity of `B` gives
  -- `χ(1) ≡ Σ_{ν∈𝒮'(χ)} ν̂(1) (mod 2)`; each `ν̂(1)` is an odd integer because `|B|` is odd.
  have hdegThree : ∀ {χ : ClassFunction G ℂ}, IsPmIrr χ →
      ∀ {α₁ α₂ α₃ : ClassFunction ↥C.P.H0 ℂ}, bset' C β₂ χ = {α₁, α₂, α₃} →
      α₁ ≠ α₂ → α₁ ≠ α₃ → α₂ ≠ α₃ → ∃ d : ℤ, Odd d ∧ χ 1 = (d : ℂ) := by
    intro χ hχ α₁ α₂ α₃ hbs h1 h2 h3
    have hm : α₁ ∈ bset' C β₂ χ := by rw [hbs]; simp
    have hI1 : α₁ ∈ S4Index C := hm.1
    have hm' : α₂ ∈ bset' C β₂ χ := by rw [hbs]; simp
    have hI2 : α₂ ∈ S4Index C := hm'.1
    have hm'' : α₃ ∈ bset' C β₂ χ := by rw [hbs]; simp
    have hI3 : α₃ ∈ S4Index C := hm''.1
    have h := (l41iii D C hc hn β₂ hβ χ hχ ⟨α₁, hm⟩).2 Θ (fun ν hν => hΘ ν hν.1) 1
    rw [hbs, finsum_mem_three h1 h2 h3] at h
    obtain ⟨n₁, hn₁, hdn₁⟩ := exists_odd_nat_degree (K := ↥D.B) (congB_card_odd D) (hΘint α₁ hI1)
    obtain ⟨n₂, hn₂, hdn₂⟩ := exists_odd_nat_degree (K := ↥D.B) (congB_card_odd D) (hΘint α₂ hI2)
    obtain ⟨n₃, hn₃, hdn₃⟩ := exists_odd_nat_degree (K := ↥D.B) (congB_card_odd D) (hΘint α₃ hI3)
    obtain ⟨dχ, hdχ⟩ := exists_int_degree hχ
    have hdχ' : χ ((1 : ↥D.B) : G) = (dχ : ℂ) := hdχ
    rw [hdχ'] at h
    have hsum : Θ α₁ 1 + Θ α₂ 1 + Θ α₃ 1 = ((n₁ + n₂ + n₃ : ℕ) : ℂ) := by
      rw [hdn₁, hdn₂, hdn₃]
      push_cast
      ring
    rw [hsum] at h
    have h' : AlgIntModTwo (dχ : ℂ) (((n₁ + n₂ + n₃ : ℕ) : ℤ) : ℂ) := by simpa using h
    have hdvd : (2 : ℤ) ∣ dχ - ((n₁ + n₂ + n₃ : ℕ) : ℤ) :=
      OddOrder.RepresentationTheory.int_dvd_of_cong_intCast (by norm_num) (algIntModTwo_to_cong h')
    refine ⟨dχ, ?_, hdχ⟩
    have hoddSumNat : Odd (n₁ + n₂ + n₃) := by
      obtain ⟨i₁, hi₁⟩ := hn₁
      obtain ⟨i₂, hi₂⟩ := hn₂
      obtain ⟨i₃, hi₃⟩ := hn₃
      refine ⟨i₁ + i₂ + i₃ + 1, ?_⟩
      rw [hi₁, hi₂, hi₃]
      ring_nf
    have hoddSum : Odd (((n₁ + n₂ + n₃ : ℕ) : ℤ)) := by
      obtain ⟨i, hi⟩ := hoddSumNat
      refine ⟨(i : ℤ), ?_⟩
      rw [hi]
      push_cast
      ring
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hoddSum
    exact ⟨k + m, by linear_combination hk + hm⟩
  have hdegOne : ∀ {χ : ClassFunction G ℂ}, IsPmIrr χ →
      ∀ {α : ClassFunction ↥C.P.H0 ℂ}, bset' C β₂ χ = {α} → ∃ d : ℤ, Odd d ∧ χ 1 = (d : ℂ) := by
    intro χ hχ α hbs
    have hm : α ∈ bset' C β₂ χ := by rw [hbs]; simp
    have hI : α ∈ S4Index C := hm.1
    have h := (l41iii D C hc hn β₂ hβ χ hχ ⟨α, hm⟩).2 Θ (fun ν hν => hΘ ν hν.1) 1
    rw [hbs, finsum_mem_singleton] at h
    obtain ⟨n, hn, hdn⟩ := exists_odd_nat_degree (K := ↥D.B) (congB_card_odd D) (hΘint α hI)
    obtain ⟨dχ, hdχ⟩ := exists_int_degree hχ
    have hdχ' : χ ((1 : ↥D.B) : G) = (dχ : ℂ) := hdχ
    rw [hdχ', hdn] at h
    have h' : AlgIntModTwo (dχ : ℂ) (((n : ℕ) : ℤ) : ℂ) := by simpa using h
    have hdvd : (2 : ℤ) ∣ dχ - ((n : ℕ) : ℤ) :=
      OddOrder.RepresentationTheory.int_dvd_of_cong_intCast (by norm_num) (algIntModTwo_to_cong h')
    refine ⟨dχ, ?_, hdχ⟩
    have hoddSumNat : Odd n := hn
    have hoddSum : Odd (((n : ℕ) : ℤ)) := by
      obtain ⟨i, hi⟩ := hoddSumNat
      refine ⟨(i : ℤ), ?_⟩
      rw [hi]
      push_cast
      ring_nf
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hoddSum
    exact ⟨k + m, by linear_combination hk + hm⟩
  obtain ⟨dχ, hdχ, hdegχ⟩ := hdegThree hχ₁ hb1 h12 h13 h23
  obtain ⟨d1, hd1, hdeg1⟩ := hdegOne hψ₁ hb2
  obtain ⟨d2, hd2, hdeg2⟩ := hdegOne hψ₂ hb3
  obtain ⟨d3, hd3, hdeg3⟩ := hdegOne hψ₃ hb4
  -- `L41 (iii)`: `χ ≡ Σ_{ν∈𝒮'(χ)} ν̂` on `B`
  have hΘsumχ : ∀ a : ↥D.B, AlgIntModTwo (χ₁ (a : G)) (Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) := by
    intro a
    have h := (l41iii D C hc hn β₂ hβ χ₁ hχ₁ ⟨ν₁, hm1⟩).2 Θ (fun ν hν => hΘ ν hν.1) a
    rw [hb1] at h
    rwa [finsum_mem_three h12 h13 h23] at h
  have hΘsum1 : ∀ a : ↥D.B, AlgIntModTwo (ψ₁ (a : G)) (Θ ν₁ a) := by
    intro a
    have h := (l41iii D C hc hn β₂ hβ ψ₁ hψ₁ ⟨ν₁, hm2⟩).2 Θ (fun ν hν => hΘ ν hν.1) a
    rw [hb2] at h
    rwa [finsum_mem_singleton] at h
  have hΘsum2 : ∀ a : ↥D.B, AlgIntModTwo (ψ₂ (a : G)) (Θ ν₂ a) := by
    intro a
    have h := (l41iii D C hc hn β₂ hβ ψ₂ hψ₂ ⟨ν₂, hm3⟩).2 Θ (fun ν hν => hΘ ν hν.1) a
    rw [hb3] at h
    rwa [finsum_mem_singleton] at h
  have hΘsum3 : ∀ a : ↥D.B, AlgIntModTwo (ψ₃ (a : G)) (Θ ν₃ a) := by
    intro a
    have h := (l41iii D C hc hn β₂ hβ ψ₃ hψ₃ ⟨ν₃, hm4⟩).2 Θ (fun ν hν => hΘ ν hν.1) a
    rw [hb4] at h
    rwa [finsum_mem_singleton] at h
  -- **(CC1)**: the pointwise congruence on group elements
  have hpointE : ∀ g : G, AlgIntModTwo (omegaVal χ₁ g)
      (omegaVal ψ₁ g + omegaVal ψ₂ g + omegaVal ψ₃ g) := by
    intro g
    by_cases hodd : Odd (Subgroup.centralizer ({g} : Set G)).index
    · obtain ⟨h, hconj, hcent⟩ := congOddConj' (D.S) g hodd
      obtain ⟨s, hsS, b, hbB, hsb⟩ := congCGS' D hn h hcent
      have hbodd : Odd (orderOf b) :=
        (odd_card_U D).of_dvd_nat (Subgroup.orderOf_dvd_natCard D.U (congB_le_U D hbB))
      have hsbs : s * b = b * s :=
        (Subgroup.mem_centralizer_iff.mp (B_le_centralizer_S D hbB)) s hsS
      have hs2 : s * s = 1 := congS_sq D hn hsS
      have hchi : AlgIntModTwo (omegaVal χ₁ g) (Θ ν₁ ⟨b, hbB⟩ + Θ ν₂ ⟨b, hbB⟩ + Θ ν₃ ⟨b, hbB⟩) := by
        have c1 : AlgIntModTwo (omegaVal χ₁ g) (χ₁ g) := omegaVal_cong_odd_pm hχ₁ hdχ hdegχ hodd
        have c2 : χ₁ g = χ₁ h := χ₁.of_isConj hconj
        have c3 : AlgIntModTwo (χ₁ h) (χ₁ b) := by
          have h16 := lemma16_mod_two s b hs2 hbodd hsbs χ₁ (mem_ZIrr_of_isPmIrr hχ₁)
          rwa [← hsb] at h16
        exact (c2 ▸ c1).trans (c3.trans (hΘsumχ ⟨b, hbB⟩))
      have hpsi1 : AlgIntModTwo (omegaVal ψ₁ g) (Θ ν₁ ⟨b, hbB⟩) := by
        have c1 : AlgIntModTwo (omegaVal ψ₁ g) (ψ₁ g) := omegaVal_cong_odd_pm hψ₁ hd1 hdeg1 hodd
        have c2 : ψ₁ g = ψ₁ h := ψ₁.of_isConj hconj
        have c3 : AlgIntModTwo (ψ₁ h) (ψ₁ b) := by
          have h16 := lemma16_mod_two s b hs2 hbodd hsbs ψ₁ (mem_ZIrr_of_isPmIrr hψ₁)
          rwa [← hsb] at h16
        exact (c2 ▸ c1).trans (c3.trans (hΘsum1 ⟨b, hbB⟩))
      have hpsi2 : AlgIntModTwo (omegaVal ψ₂ g) (Θ ν₂ ⟨b, hbB⟩) := by
        have c1 : AlgIntModTwo (omegaVal ψ₂ g) (ψ₂ g) := omegaVal_cong_odd_pm hψ₂ hd2 hdeg2 hodd
        have c2 : ψ₂ g = ψ₂ h := ψ₂.of_isConj hconj
        have c3 : AlgIntModTwo (ψ₂ h) (ψ₂ b) := by
          have h16 := lemma16_mod_two s b hs2 hbodd hsbs ψ₂ (mem_ZIrr_of_isPmIrr hψ₂)
          rwa [← hsb] at h16
        exact (c2 ▸ c1).trans (c3.trans (hΘsum2 ⟨b, hbB⟩))
      have hpsi3 : AlgIntModTwo (omegaVal ψ₃ g) (Θ ν₃ ⟨b, hbB⟩) := by
        have c1 : AlgIntModTwo (omegaVal ψ₃ g) (ψ₃ g) := omegaVal_cong_odd_pm hψ₃ hd3 hdeg3 hodd
        have c2 : ψ₃ g = ψ₃ h := ψ₃.of_isConj hconj
        have c3 : AlgIntModTwo (ψ₃ h) (ψ₃ b) := by
          have h16 := lemma16_mod_two s b hs2 hbodd hsbs ψ₃ (mem_ZIrr_of_isPmIrr hψ₃)
          rwa [← hsb] at h16
        exact (c2 ▸ c1).trans (c3.trans (hΘsum3 ⟨b, hbB⟩))
      refine hchi.trans ?_
      simpa using ((hpsi1.add hpsi2).add hpsi3).symm
    · have hχe : AlgIntModTwo (omegaVal χ₁ g) 0 := omegaVal_cong_even_pm hχ₁ hdχ hdegχ hodd
      have hψ1e : AlgIntModTwo (omegaVal ψ₁ g) 0 := omegaVal_cong_even_pm hψ₁ hd1 hdeg1 hodd
      have hψ2e : AlgIntModTwo (omegaVal ψ₂ g) 0 := omegaVal_cong_even_pm hψ₂ hd2 hdeg2 hodd
      have hψ3e : AlgIntModTwo (omegaVal ψ₃ g) 0 := omegaVal_cong_even_pm hψ₃ hd3 hdeg3 hodd
      refine hχe.trans ?_
      simpa using ((hψ1e.add hψ2e).add hψ3e).symm
  -- the same congruence, on conjugacy classes
  have hpointC : ∀ C' : ConjClasses G, AlgIntModTwo (omegaClass χ₁ C')
      (omegaClass ψ₁ C' + omegaClass ψ₂ C' + omegaClass ψ₃ C') := by
    intro C'
    have h := hpointE C'.out
    simpa only [omegaVal_eq_omegaClass, conjClass_mk_out] using h
  -- the congruence against the hats, for elements of `B`
  have hBχ : ∀ a : ↥D.B, AlgIntModTwo (omegaVal χ₁ (a : G))
      (Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) := by
    intro a
    exact (omegaVal_cong_odd_pm hχ₁ hdχ hdegχ (congB_index_odd D hn a.2)).trans (hΘsumχ a)
  have hBψ1 : ∀ a : ↥D.B, AlgIntModTwo (omegaVal ψ₁ (a : G)) (Θ ν₁ a) := by
    intro a
    exact (omegaVal_cong_odd_pm hψ₁ hd1 hdeg1 (congB_index_odd D hn a.2)).trans (hΘsum1 a)
  have hBψ2 : ∀ a : ↥D.B, AlgIntModTwo (omegaVal ψ₂ (a : G)) (Θ ν₂ a) := by
    intro a
    exact (omegaVal_cong_odd_pm hψ₂ hd2 hdeg2 (congB_index_odd D hn a.2)).trans (hΘsum2 a)
  have hBψ3 : ∀ a : ↥D.B, AlgIntModTwo (omegaVal ψ₃ (a : G)) (Θ ν₃ a) := by
    intro a
    exact (omegaVal_cong_odd_pm hψ₃ hd3 hdeg3 (congB_index_odd D hn a.2)).trans (hΘsum3 a)
  -- integrality of the hat values
  have hΘsumInt : ∀ a : ↥D.B, IsIntegral ℤ (Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) := by
    intro a
    exact ((isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) a).add
      (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) a)).add
      (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) a)
  -- **(CC2) + (CC3)**, step 1: the crossed congruence
  have hcross : ∀ a b : ↥D.B, AlgIntModTwo
      ((Θ ν₂ a + Θ ν₃ a) * Θ ν₁ b + (Θ ν₁ a + Θ ν₃ a) * Θ ν₂ b
        + (Θ ν₁ a + Θ ν₂ a) * Θ ν₃ b) 0 := by
    intro a b
    have hXA : AlgIntModTwo
        (omegaClass χ₁ (ConjClasses.mk (a : G)) * omegaClass χ₁ (ConjClasses.mk (b : G)))
        (∑ Cs, ((classSum (ConjClasses.mk (a : G)) * classSum (ConjClasses.mk (b : G)) : ℂ[G]).coeff
            Cs.out) * (omegaClass ψ₁ Cs + omegaClass ψ₂ Cs + omegaClass ψ₃ Cs)) := by
      rw [omegaClass_mul_pm hχ₁]
      exact AlgIntModTwo.sum _ fun Cs _ =>
        AlgIntModTwo.mul (coeff_classSum_mul_isIntegral _ _ _) (hpointC Cs)
    have hAV : (∑ Cs, ((classSum (ConjClasses.mk (a : G)) * classSum (ConjClasses.mk (b : G)) :
            ℂ[G]).coeff Cs.out) * (omegaClass ψ₁ Cs + omegaClass ψ₂ Cs + omegaClass ψ₃ Cs))
        = (omegaClass ψ₁ (ConjClasses.mk (a : G)) * omegaClass ψ₁ (ConjClasses.mk (b : G))
            + omegaClass ψ₂ (ConjClasses.mk (a : G)) * omegaClass ψ₂ (ConjClasses.mk (b : G))
            + omegaClass ψ₃ (ConjClasses.mk (a : G)) * omegaClass ψ₃ (ConjClasses.mk (b : G))) := by
      rw [omegaClass_mul_pm hψ₁ (ConjClasses.mk (a : G)) (ConjClasses.mk (b : G)),
        omegaClass_mul_pm hψ₂ (ConjClasses.mk (a : G)) (ConjClasses.mk (b : G)),
        omegaClass_mul_pm hψ₃ (ConjClasses.mk (a : G)) (ConjClasses.mk (b : G))]
      simp only [mul_add, Finset.sum_add_distrib]
    have hBAt : AlgIntModTwo
        (omegaClass χ₁ (ConjClasses.mk (a : G)) * omegaClass χ₁ (ConjClasses.mk (b : G)))
        ((Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) * (Θ ν₁ b + Θ ν₂ b + Θ ν₃ b)) := by
      have h1 : omegaClass χ₁ (ConjClasses.mk (a : G)) = omegaVal χ₁ (a : G) :=
        (omegaVal_eq_omegaClass χ₁ (a : G)).symm
      have h2 : omegaClass χ₁ (ConjClasses.mk (b : G)) = omegaVal χ₁ (b : G) :=
        (omegaVal_eq_omegaClass χ₁ (b : G)).symm
      rw [h1, h2]
      exact algIntModTwo_mul (omegaVal_isIntegral_pm hχ₁ (a : G)) (hΘsumInt b) (hBχ a) (hBχ b)
    have hVAt : AlgIntModTwo
        (omegaClass ψ₁ (ConjClasses.mk (a : G)) * omegaClass ψ₁ (ConjClasses.mk (b : G))
            + omegaClass ψ₂ (ConjClasses.mk (a : G)) * omegaClass ψ₂ (ConjClasses.mk (b : G))
            + omegaClass ψ₃ (ConjClasses.mk (a : G)) * omegaClass ψ₃ (ConjClasses.mk (b : G)))
        ((Θ ν₁ a) * (Θ ν₁ b) + (Θ ν₂ a) * (Θ ν₂ b) + (Θ ν₃ a) * (Θ ν₃ b)) := by
      have e1 : omegaClass ψ₁ (ConjClasses.mk (a : G)) = omegaVal ψ₁ (a : G) :=
        (omegaVal_eq_omegaClass ψ₁ (a : G)).symm
      have e2 : omegaClass ψ₁ (ConjClasses.mk (b : G)) = omegaVal ψ₁ (b : G) :=
        (omegaVal_eq_omegaClass ψ₁ (b : G)).symm
      have e3 : omegaClass ψ₂ (ConjClasses.mk (a : G)) = omegaVal ψ₂ (a : G) :=
        (omegaVal_eq_omegaClass ψ₂ (a : G)).symm
      have e4 : omegaClass ψ₂ (ConjClasses.mk (b : G)) = omegaVal ψ₂ (b : G) :=
        (omegaVal_eq_omegaClass ψ₂ (b : G)).symm
      have e5 : omegaClass ψ₃ (ConjClasses.mk (a : G)) = omegaVal ψ₃ (a : G) :=
        (omegaVal_eq_omegaClass ψ₃ (a : G)).symm
      have e6 : omegaClass ψ₃ (ConjClasses.mk (b : G)) = omegaVal ψ₃ (b : G) :=
        (omegaVal_eq_omegaClass ψ₃ (b : G)).symm
      rw [e1, e2, e3, e4, e5, e6]
      exact ((algIntModTwo_mul (omegaVal_isIntegral_pm hψ₁ (a : G))
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) b) (hBψ1 a) (hBψ1 b)).add
        (algIntModTwo_mul (omegaVal_isIntegral_pm hψ₂ (a : G))
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) b) (hBψ2 a) (hBψ2 b))).add
        (algIntModTwo_mul (omegaVal_isIntegral_pm hψ₃ (a : G))
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) b) (hBψ3 a) (hBψ3 b))
    have hYV : AlgIntModTwo
        ((Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) * (Θ ν₁ b + Θ ν₂ b + Θ ν₃ b))
        ((Θ ν₁ a) * (Θ ν₁ b) + (Θ ν₂ a) * (Θ ν₂ b) + (Θ ν₃ a) * (Θ ν₃ b)) :=
      hBAt.symm.trans (hXA.trans (hAV.symm ▸ hVAt))
    have hVint : IsIntegral ℤ
        ((Θ ν₁ a) * (Θ ν₁ b) + (Θ ν₂ a) * (Θ ν₂ b) + (Θ ν₃ a) * (Θ ν₃ b)) :=
      (((isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) a).mul
        (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) b)).add
      ((isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) a).mul
        (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) b))).add
      ((isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) a).mul
        (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) b))
    have hzero : AlgIntModTwo
        (((Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) * (Θ ν₁ b + Θ ν₂ b + Θ ν₃ b))
          - ((Θ ν₁ a) * (Θ ν₁ b) + (Θ ν₂ a) * (Θ ν₂ b) + (Θ ν₃ a) * (Θ ν₃ b))) 0 := by
      have h := (hYV.symm).sub (AlgIntModTwo.refl _ hVint)
      simpa using h.symm
    have hkey : ((Θ ν₁ a + Θ ν₂ a + Θ ν₃ a) * (Θ ν₁ b + Θ ν₂ b + Θ ν₃ b))
        - ((Θ ν₁ a) * (Θ ν₁ b) + (Θ ν₂ a) * (Θ ν₂ b) + (Θ ν₃ a) * (Θ ν₃ b))
        = ((Θ ν₂ a + Θ ν₃ a) * Θ ν₁ b + (Θ ν₁ a + Θ ν₃ a) * Θ ν₂ b
            + (Θ ν₁ a + Θ ν₂ a) * Θ ν₃ b) := by ring
    rw [← hkey]
    exact hzero
  -- **(CC3)**, step 1: `Θ ν₁(a) + Θ ν₃(a) ≡ 0`
  have hstep : ∀ a : ↥D.B, AlgIntModTwo (Θ ν₁ a + Θ ν₃ a) 0 := by
    intro a
    have hisIrr : ∀ i : Fin 3, IsIrreducibleCharacter
        ((![Θ ν₁, Θ ν₂, Θ ν₃] : Fin 3 → ClassFunction ↥D.B ℂ) i) := by
      intro i
      fin_cases i
      · exact hΘint ν₁ hν1
      · exact hΘint ν₂ hν2
      · exact hΘint ν₃ hν3
    have hinj : Function.Injective ((![Θ ν₁, Θ ν₂, Θ ν₃] : Fin 3 → ClassFunction ↥D.B ℂ)) :=
      fin_three_injective
        (by intro h; exact h12 (hΘinj ν₁ ν₂ hν1 hν2 h))
        (by intro h; exact h13 (hΘinj ν₁ ν₃ hν1 hν3 h))
        (by intro h; exact h23 (hΘinj ν₂ ν₃ hν2 hν3 h))
    have hint : ∀ i : Fin 3, IsIntegral ℤ (((![Θ ν₂ a + Θ ν₃ a, Θ ν₁ a + Θ ν₃ a,
        Θ ν₁ a + Θ ν₂ a] : Fin 3 → ℂ)) i) := by
      intro i
      fin_cases i
      · exact (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) a).add
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) a)
      · exact (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) a).add
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₃ hν3) a)
      · exact (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₁ hν1) a).add
          (isIntegral_apply_of_isIrreducibleCharacter (hΘint ν₂ hν2) a)
    have hhyp : ∀ b : ↥D.B,
        AlgIntModTwo (∑ i : Fin 3, ((![Θ ν₂ a + Θ ν₃ a, Θ ν₁ a + Θ ν₃ a,
          Θ ν₁ a + Θ ν₂ a] : Fin 3 → ℂ) i) * ((![Θ ν₁, Θ ν₂, Θ ν₃] : Fin 3 →
            ClassFunction ↥D.B ℂ) i) b) 0 := by
      intro b
      have h := hcross a b
      simpa [Fin.sum_univ_three] using h
    have hfin := modTwoIndep (K := ↥D.B) (congB_card_odd D)
      ((![Θ ν₁, Θ ν₂, Θ ν₃] : Fin 3 → ClassFunction ↥D.B ℂ)) hisIrr hinj
      ((![Θ ν₂ a + Θ ν₃ a, Θ ν₁ a + Θ ν₃ a, Θ ν₁ a + Θ ν₂ a] : Fin 3 → ℂ)) hint hhyp
    have h1 := hfin 1
    simpa using h1
  -- **(CC3)**, step 2: contradiction
  have hisIrr2 : ∀ i : Fin 2, IsIrreducibleCharacter
      ((![Θ ν₁, Θ ν₃] : Fin 2 → ClassFunction ↥D.B ℂ) i) := by
    intro i
    fin_cases i
    · exact hΘint ν₁ hν1
    · exact hΘint ν₃ hν3
  have hinj2 : Function.Injective ((![Θ ν₁, Θ ν₃] : Fin 2 → ClassFunction ↥D.B ℂ)) :=
    fin_two_injective (by intro h; exact h13 (hΘinj ν₁ ν₃ hν1 hν3 h))
  have hint2 : ∀ i : Fin 2, IsIntegral ℤ (((![(1 : ℂ), (1 : ℂ)] : Fin 2 → ℂ)) i) := by
    intro i
    fin_cases i <;> exact isIntegral_one
  have hhyp2 : ∀ a : ↥D.B, AlgIntModTwo (∑ i : Fin 2,
      ((![(1 : ℂ), (1 : ℂ)] : Fin 2 → ℂ) i) *
        ((![Θ ν₁, Θ ν₃] : Fin 2 → ClassFunction ↥D.B ℂ) i) a) 0 := by
    intro a
    have h := hstep a
    simpa [Fin.sum_univ_two] using h
  have hfin2 := modTwoIndep (K := ↥D.B) (congB_card_odd D)
    ((![Θ ν₁, Θ ν₃] : Fin 2 → ClassFunction ↥D.B ℂ)) hisIrr2 hinj2
    ((![(1 : ℂ), (1 : ℂ)] : Fin 2 → ℂ)) hint2 hhyp2
  exact not_algIntModTwo_one_zero (by simpa using hfin2 0)

end Work.BG
