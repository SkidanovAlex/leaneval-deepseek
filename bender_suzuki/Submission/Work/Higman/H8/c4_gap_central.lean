/-
Copyright (c) 2024. All rights reserved.

# The central gap case of the `C₄` exclusion of Higman's Lemma 8

`Work.Higman.H8.c4_gap_central` is the statement that the Gorenstein–Thompson case of the
`C₄`-shape of Higman's Lemma 8 is impossible: there is no Suzuki 2-group `P` with a
`ξ`-invariant abelian normal subgroup `A` such that `A² = Ω₁(P) ≠ 1`, `A⁴ = 1`, `[P,P] = A`,
all squares lie in `A`, and a `ξ`-invariant normal subgroup `A < C` with `[C,C] = A²`,
`C² ≤ A`, `A` centralising `C`, minimal over `A` among such subgroups.

The mathematics is Higman's Lemma 2 together with Gorenstein–Thompson's theorem on
alternating `ξ`-equivariant forms, and is carried out in full in `c4g_alt_pairing` below
(the fourth-power map `f : C → A²`, its kernel `S`, the dichotomy `S = A` / `S = C`, and in
the case `S = A` the induced alternating biadditive pairing `A² × A² → A²`).
-/

import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.false_of_sq_all_mem_powSub_two
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.OmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.H8

variable {P : Type} [Group P] [Finite P]

/-! ## The fourth-power map on `C` -/

theorem c4g_pow_four_hom {P : Type} [Group P] [Finite P] {A C : Subgroup P}
    (hAC : A ≤ C) (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    ∃ f : ↥C →* ↥(Work.Higman.powSub A 2),
      (∀ x : ↥C, (f x : P) = (x : P) ^ 4) ∧
      (∀ x y : ↥C, f x = f y ↔ (x : P) * (y : P)⁻¹ ∈ f.ker.map C.subtype) := by
  have hab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => (hZ v (hAC hv) u hu).symm
  -- every element of `A²` is an involution
  have hVsq : ∀ v ∈ powSub A 2, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hab).mp hv
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hexp a ha
  -- the fourth power is multiplicative on `C`
  have hpow4 : ∀ x y : P, x ∈ C → y ∈ C → (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
    intro x y hx hy
    have hcom : ⁅y, x⁆ ∈ A := by
      have h1 : ⁅y, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hy hx
      rw [hCd] at h1
      exact powSub_le (by norm_num) h1
    have hx2 : x ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hx)
    have hy2 : y ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hy)
    have hunfold : y * x = ⁅y, x⁆ * x * y := by
      rw [← mul_mul_inv_eq_commutator_mul y x]; group
    have hcx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := hZ x hx ⁅y, x⁆ hcom
    have hfinal : x * ⁅y, x⁆ * x * y * y = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      rw [hcx, pow_two, pow_two]
      group
    have hsq : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (⁅y, x⁆ * x * y) * y := by rw [hunfold]
        _ = x * ⁅y, x⁆ * x * y * y := by group
        _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := hfinal
    have hc2 : ⁅y, x⁆ ^ 2 = 1 :=
      hVsq _ (by rw [← hCd]; exact Subgroup.commutator_mem_commutator hy hx)
    calc (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (⁅y, x⁆ * (x ^ 2 * y ^ 2)) ^ 2 := by rw [hsq]
      _ = ⁅y, x⁆ ^ 2 * (x ^ 2 * y ^ 2) ^ 2 :=
            Commute.mul_pow (hab _ hcom _ (A.mul_mem hx2 hy2)) 2
      _ = x ^ 4 * y ^ 4 := by
            rw [hc2, one_mul, Commute.mul_pow (hab _ hx2 _ hy2) 2]
            simp only [← pow_mul, Nat.reduceMul]
  have hmem : ∀ x : P, x ∈ C → x ^ 4 ∈ powSub A 2 := by
    intro x hx
    have h1 : x ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) hx)
    have h2 : (x ^ 2) ^ 2 ∈ powSub A 2 := pow_mem_powSub (n := 2) h1
    simpa [← pow_mul] using h2
  let f : ↥C →* ↥(powSub A 2) :=
    { toFun := fun x => ⟨(x : P) ^ 4, hmem x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (hpow4 x y x.2 y.2) }
  refine ⟨f, fun x => rfl, ?_⟩
  intro x y
  constructor
  · intro hxy
    refine Subgroup.mem_map.mpr ⟨⟨(x : P) * (y : P)⁻¹, C.mul_mem x.2 (C.inv_mem y.2)⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hzeq : (⟨(x : P) * (y : P)⁻¹, C.mul_mem x.2 (C.inv_mem y.2)⟩ : ↥C) = x * y⁻¹ := by
      apply Subtype.ext
      simp
    rw [hzeq, map_mul, map_inv, hxy, mul_inv_cancel]
  · rintro ⟨z, hz, hzx⟩
    have hfz : f z = 1 := MonoidHom.mem_ker.mp hz
    have hzeq : z = x * y⁻¹ := by
      apply Subtype.ext
      simpa using hzx
    rw [hzeq, map_mul, map_inv] at hfz
    have h2 := congrArg (fun w => w * f y) hfz
    simpa using h2



/- ## The automorphism induced by `ξ` on an invariant subgroup -/

/-- The automorphism of `↥H` induced by `ξ` when `H` is `ξ`-invariant. -/
noncomputable def c4gXi (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) : MulAut ↥H where
  toFun x := ⟨h.xi (x : P), by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm (x : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem c4gXi_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    ((c4gXi h hinv x : ↥H) : P) = h.xi (x : P) := rfl

theorem c4gXi_symm_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    (((c4gXi h hinv).symm x : ↥H) : P) = (h.xi : MulAut P).symm (x : P) := rfl

theorem c4gXi_pow_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) (x : ↥H) :
    (((c4gXi h hinv) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (c4gXi h hinv x), c4gXi_apply, pow_succ,
        MulAut.mul_apply]

/- ## Commutator calculus in `C`, a group of class two

`A ≤ C` centralises `C` and contains `[C,C] = A²`, so `C` has class two: commutators of
elements of `C` are central in `C`, and the usual identities hold. -/

/-- `C` has class two: its commutator subgroup is central. -/
theorem c4g_commutator_le_center_subtype {A C : Subgroup P}
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2) :
    ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ Subgroup.center ↥C := by
  rw [Subgroup.commutator_le]
  intro u _ v _
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hmem : ((⁅u, v⁆ : ↥C) : P) ∈ A := by
    have hcoe : ((⁅u, v⁆ : ↥C) : P) = ⁅((u : ↥C) : P), ((v : ↥C) : P)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    have h1 : ⁅((u : ↥C) : P), ((v : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator u.2 v.2
    rw [hCd] at h1
    exact powSub_le (by norm_num) h1
  have h2 := hZ _ w.2 _ hmem
  simpa using h2

/-- A commutator of two elements of `C` lies in `A` (and hence in `A²`). -/
theorem c4g_commutator_mem_A {A C : Subgroup P} (hCd : ⁅C, C⁆ = powSub A 2) {x y : P}
    (hx : x ∈ C) (hy : y ∈ C) : ⁅x, y⁆ ∈ A := by
  have h1 : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hCd] at h1
  exact powSub_le (by norm_num) h1

/-- Commutators are unchanged by multiplying an argument by an element of `A` (left slot). -/
theorem c4g_commutator_mul_mem_left {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y a : P} (hx : x ∈ C) (hy : y ∈ C) (ha : a ∈ A) :
    ⁅x * a, y⁆ = ⁅x, y⁆ := by
  have hZ2 := c4g_commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have key : (⁅(⟨x, hx⟩ : ↥C) * (⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) =
      (⁅(⟨x, hx⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ * ⁅(⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) :=
    commutator_mul_left hZ2 _ _ _
  have hone : (⁅(⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hZ y hy a ha]
    group
  have h := congrArg (fun t : ↥C => (t : P)) key
  rw [hone, mul_one] at h
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  exact h

/-- Commutators are unchanged by multiplying an argument by an element of `A` (right slot). -/
theorem c4g_commutator_mul_mem_right {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y a : P} (hx : x ∈ C) (hy : y ∈ C) (ha : a ∈ A) :
    ⁅x, y * a⁆ = ⁅x, y⁆ := by
  have hZ2 := c4g_commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have h1 : ⁅y * a, x⁆ = ⁅y, x⁆ := by
    have key : (⁅(⟨y, hy⟩ : ↥C) * (⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) =
        (⁅(⟨y, hy⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ * ⁅(⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) :=
      commutator_mul_left hZ2 _ _ _
    have hone : (⁅(⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hZ x hx a ha]
      group
    have h := congrArg (fun t : ↥C => (t : P)) key
    rw [hone, mul_one] at h
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    exact h
  rw [show ⁅x, y * a⁆ = (⁅y * a, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group,
      show ⁅x, y⁆ = (⁅y, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group, h1]

/-- The commutator pairing is additive in the left slot (class two). -/
theorem c4g_commutator_mul_left' {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hZ2 := c4g_commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have key : (⁅(⟨x, hx⟩ : ↥C) * (⟨y, hy⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ : ↥C) =
      (⁅(⟨x, hx⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ * ⁅(⟨y, hy⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ : ↥C) :=
    commutator_mul_left hZ2 _ _ _
  have h := congrArg (fun t : ↥C => (t : P)) key
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  exact h

/-- The commutator pairing is additive in the right slot (class two). -/
theorem c4g_commutator_mul_right' {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    (hAab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hm : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := c4g_commutator_mul_left' hAC hZ hCd hy hz hx
  have hcxz : ⁅x, z⁆ ∈ A := by
    rw [show ⁅x, z⁆ = (⁅z, x⁆)⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
    exact A.inv_mem (c4g_commutator_mem_A hCd hz hx)
  have hcxy : ⁅x, y⁆ ∈ A := by
    rw [show ⁅x, y⁆ = (⁅y, x⁆)⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
    exact A.inv_mem (c4g_commutator_mem_A hCd hy hx)
  have hcomm' : ⁅x, z⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x, z⁆ := hAab _ hcxz _ hcxy
  rw [show ⁅x, y * z⁆ = (⁅y * z, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group,
      hm, mul_inv_rev,
      show (⁅y, x⁆)⁻¹ = ⁅x, y⁆ by rw [commutatorElement_def, commutatorElement_def]; group,
      show (⁅z, x⁆)⁻¹ = ⁅x, z⁆ by rw [commutatorElement_def, commutatorElement_def]; group]
  exact hcomm'

/-! ## The main theorem -/

/-- **The alternating-pairing contradiction of the central gap case.**

Let `P` be a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup with `A² = Ω₁(P) ≠ 1`
and `A⁴ = 1`, and `C` a `ξ`-invariant normal subgroup with `A < C`, centralising `A`, with
`C² ≤ A` and `[C,C] = A²`, and with no `ξ`-invariant normal subgroup strictly between `A` and
`C`.  Then we reach a contradiction.

Route: the fourth power map `f : x ↦ x⁴` is a homomorphism `↥C →* ↥Ω₁(P)` (class two: `C`
centralises `A` and `[C,C] = A² ⊆ A`), its kernel `S` is normal in `P` and `ξ`-invariant with
`A ≤ S ≤ C`, so `S = A` or `S = C`; `S = C` contradicts Higman's Lemma 2
(`false_of_sq_all_mem_powSub_two`); `S = A` makes `f` surjective onto `Ω₁(P)`, and choosing for
`v ∈ Ω₁(P)` an element `root v ∈ C` with `(root v)⁴ = v` gives a `ξ`-equivariant alternating
biadditive `c : Ω₁ × Ω₁ → Ω₁` with `ξ` transitive on `Ω₁ \ {1}`, hence `c ≡ 0` by
Gorenstein–Thompson (`equivariant_bihom_trivial`), contradicting `[C,C] = A² ≠ 1`. -/

theorem c4g_alt_pairing {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : C ≠ A)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hOmega : Work.Higman.omega1 P = Work.Higman.powSub A 2)
    (hA2ne : Work.Higman.powSub A 2 ≠ ⊥)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    False := by
  classical
  -- ## Elementary facts about `V = A² = Ω₁(P)`
  have hVle : powSub A 2 ≤ A := powSub_le (by norm_num)
  have hVinv : (powSub A 2).map (h.xi : MulAut P).toMonoidHom = powSub A 2 :=
    map_powSub (h.xi : MulAut P) hA.map_eq 2
  have hOmA : ∀ z ∈ A, z ^ 2 = 1 → z ∈ powSub A 2 := by
    intro z _ hz2
    rw [← hOmega]
    exact h.mem_omega1.mpr hz2
  have hVsq : ∀ v ∈ powSub A 2, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hA.abelian).mp hv
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hexp a ha
  -- ## The fourth power map and its kernel `S`
  obtain ⟨f, hf, hfker⟩ := c4g_pow_four_hom hAC hZ hC2 hCd hexp
  let S : Subgroup P := f.ker.map C.subtype
  have hSmem : ∀ x : P, x ∈ S ↔ x ∈ C ∧ x ^ 4 = 1 := by
    intro x
    constructor
    · intro hx
      change x ∈ Subgroup.map C.subtype f.ker at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hy1 : f y = 1 := MonoidHom.mem_ker.mp hy
      have h4 : (y : P) ^ 4 = 1 := by
        have hh := congrArg (fun t : ↥(powSub A 2) => (t : P)) hy1
        rw [Subgroup.coe_one, hf y] at hh
        exact hh
      exact ⟨by rw [← hyx]; exact y.2, by rw [← hyx]; exact h4⟩
    · intro hx
      obtain ⟨hxC, hx4⟩ := hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      change f ⟨x, hxC⟩ = 1
      apply Subtype.ext
      rw [Subgroup.coe_one, hf]
      exact hx4
  have hSC : S ≤ C := fun x hx => ((hSmem x).mp hx).1
  have hAS : A ≤ S := fun a ha => (hSmem a).mpr ⟨hAC ha, hexp a ha⟩
  have hSn : S.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    obtain ⟨hnC, hn4⟩ := (hSmem n).mp hn
    refine (hSmem (g * n * g⁻¹)).mpr ⟨hCn.conj_mem n hnC g, ?_⟩
    have hconj : g * n ^ 4 * g⁻¹ = (g * n * g⁻¹) ^ 4 := by
      have hh := map_pow (MulAut.conj g) n 4
      simpa [MulAut.conj_apply] using hh.symm
    rw [← hconj, hn4, mul_one, mul_inv_cancel]
  have hSinv : S.map (h.xi : MulAut P).toMonoidHom = S := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨hyC, hy4⟩ := (hSmem y).mp hy
      refine (hSmem (h.xi y)).mpr ⟨?_, ?_⟩
      · rw [← hCinv]; exact Subgroup.mem_map_of_mem _ hyC
      · rw [← map_pow, hy4, map_one]
    · intro x hx
      obtain ⟨hxC, hx4⟩ := (hSmem x).mp hx
      refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
      refine (hSmem ((h.xi : MulAut P).symm x)).mpr ⟨?_, ?_⟩
      · have h1 : x ∈ C.map (h.xi : MulAut P).toMonoidHom := by rw [hCinv]; exact hxC
        obtain ⟨y, hy, hyx⟩ := h1
        have h2 : (h.xi : MulAut P).symm x = y := by rw [← hyx]; simp
        rw [h2]; exact hy
      · have h4 := map_pow (h.xi : MulAut P).symm x 4
        rw [hx4, map_one] at h4
        exact h4.symm
  rcases hcover S hSn hSinv hAS hSC with hSA | hSCeq
  · -- ## Case `S = A`: the fourth power map is onto `V` and yields a `ξ`-form
    -- elements of `V` are fourth powers of elements of `C`
    have hcongA : ∀ x y : ↥C, f x = f y → ∃ a ∈ A, (x : P) = a * (y : P) := by
      intro x y hxy
      have h1 : (x : P) * (y : P)⁻¹ ∈ S := (hfker x y).mp hxy
      rw [hSA] at h1
      exact ⟨(x : P) * (y : P)⁻¹, h1, by group⟩
    have hfeq : ∀ x : ↥C, f (c4gXi h hCinv x) = c4gXi h hVinv (f x) := by
      intro x
      apply Subtype.ext
      have h1 : ((f (c4gXi h hCinv x) : ↥(powSub A 2)) : P) = (h.xi (x : P)) ^ 4 := by
        rw [hf, c4gXi_apply]
      have h2 : ((c4gXi h hVinv (f x) : ↥(powSub A 2)) : P) = (h.xi (x : P)) ^ 4 := by
        rw [c4gXi_apply, hf, map_pow]
      rw [h1, h2]
    -- `V` is an irreducible `⟨ξ⟩`-module
    have hVirr : ∀ T : Subgroup P, T ≤ powSub A 2 →
        T.map (h.xi : MulAut P).toMonoidHom = T → T = ⊥ ∨ T = powSub A 2 := by
      intro T hT hTinv
      have h1 : T ≤ A ⊓ omega1 P := le_inf (hT.trans hVle) (by rw [hOmega]; exact hT)
      rcases invariant_subgroup_inf_omega1 h A h1 hTinv with hb | htop
      · exact Or.inl hb
      · refine Or.inr ?_
        rw [htop, hOmega, inf_eq_right.mpr hVle]
    -- the range of the fourth power map is all of `V`
    let g : ↥C →* P := (powSub A 2).subtype.comp f
    have hg : ∀ x : ↥C, g x = (x : P) ^ 4 := by
      intro x
      show ((f x : ↥(powSub A 2)) : P) = (x : P) ^ 4
      rw [hf]
    have hgrange : ∀ y : P, y ∈ g.range ↔ ∃ x : ↥C, (x : P) ^ 4 = y := by
      intro y
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx, hg]⟩
      · rintro ⟨x, hx⟩; exact ⟨x, by rw [hg, hx]⟩
    have hgle : g.range ≤ powSub A 2 := by
      rintro y ⟨x, rfl⟩
      rw [hg]
      have hx2 : (x : P) ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) x.2)
      have h4 : ((x : P) ^ 2) ^ 2 ∈ powSub A 2 := pow_mem_powSub (n := 2) hx2
      simpa [← pow_mul] using h4
    have hgfor : ∀ y ∈ g.range, h.xi y ∈ g.range := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨c4gXi h hCinv x, ?_⟩
      rw [hg, c4gXi_apply, ← hx, hg]
      exact (map_pow (h.xi : MulAut P) (x : P) 4).symm
    have hgback : ∀ y ∈ g.range, (h.xi : MulAut P).symm y ∈ g.range := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨(c4gXi h hCinv).symm x, ?_⟩
      rw [hg, c4gXi_symm_apply, ← hx, hg, map_pow]
    have hginv : g.range.map (h.xi : MulAut P).toMonoidHom = g.range := by
      apply le_antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact hgfor z hz
      · intro y hy
        exact ⟨(h.xi : MulAut P).symm y, hgback y hy, by simp⟩
    have hgne : g.range ≠ ⊥ := by
      intro hbot
      refine hCA (le_antisymm ?_ hAC)
      intro u hu
      have h4 : u ^ 4 ∈ g.range := (hgrange _).mpr ⟨⟨u, hu⟩, rfl⟩
      rw [hbot] at h4
      have h4' : u ^ 4 = 1 := Subgroup.mem_bot.mp h4
      have huS : u ∈ S := (hSmem u).mpr ⟨hu, h4'⟩
      rwa [hSA] at huS
    have hgtop : g.range = powSub A 2 := by
      rcases hVirr _ hgle hginv with hb | htop
      · exact absurd hb hgne
      · exact htop
    have hsurj : ∀ v : ↥(powSub A 2), ∃ x : ↥C, f x = v := by
      intro v
      have hv : (v : P) ∈ g.range := by rw [hgtop]; exact v.2
      obtain ⟨x, hx⟩ := (hgrange _).mp hv
      exact ⟨x, Subtype.ext (by rw [hf]; exact hx)⟩
    -- ## The alternating form
    letI : CommGroup ↥(powSub A 2) :=
      { (inferInstance : Group ↥(powSub A 2)) with
        mul_comm := fun x y => Subtype.ext
          (hA.abelian x (powSub_le (by norm_num) x.2) y (powSub_le (by norm_num) y.2)) }
    let root : ↥(powSub A 2) → ↥C := fun v => Classical.choose (hsurj v)
    have hroot : ∀ v, f (root v) = v := fun v => Classical.choose_spec (hsurj v)
    have hmemV : ∀ u v : ↥(powSub A 2),
        ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ ∈ powSub A 2 := by
      intro u v
      have h1 : ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
        Subgroup.commutator_mem_commutator (root u).2 (root v).2
      rwa [hCd] at h1
    let c : ↥(powSub A 2) → ↥(powSub A 2) → ↥(powSub A 2) :=
      fun u v => ⟨⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆, hmemV u v⟩
    have hc : ∀ u v : ↥(powSub A 2),
        ((c u v : ↥(powSub A 2)) : P) = ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ :=
      fun _ _ => rfl
    have hswap : ∀ {e x : P}, e ∈ A → x ∈ C → e * x = x * e :=
      fun {e x} he hx => (hZ x hx e he).symm
    have hcong1 : ∀ a b : ↥(powSub A 2),
        ∃ e ∈ A, (root (a * b) : P) = e * ((root a : P) * (root b : P)) := by
      intro a b
      refine hcongA (root (a * b)) (root a * root b) ?_
      rw [hroot, map_mul, hroot, hroot]
    have hc_mul : ∀ a b d : ↥(powSub A 2), c (a * b) d = c a d * c b d := by
      intro a b d
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hc]
      obtain ⟨e, heA, heq⟩ := hcong1 a b
      have hra : (root a : P) ∈ C := (root a).2
      have hrb : (root b : P) ∈ C := (root b).2
      have hrd : (root d : P) ∈ C := (root d).2
      rw [heq, hswap heA (C.mul_mem hra hrb),
        c4g_commutator_mul_mem_left hAC hZ hCd (C.mul_mem hra hrb) hrd heA,
        c4g_commutator_mul_left' hAC hZ hCd hra hrb hrd]
    have hc_mul' : ∀ a b d : ↥(powSub A 2), c a (b * d) = c a b * c a d := by
      intro a b d
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hc]
      obtain ⟨e, heA, heq⟩ := hcong1 b d
      have hra : (root a : P) ∈ C := (root a).2
      have hrb : (root b : P) ∈ C := (root b).2
      have hrd : (root d : P) ∈ C := (root d).2
      rw [heq, hswap heA (C.mul_mem hrb hrd),
        c4g_commutator_mul_mem_right hAC hZ hCd hra (C.mul_mem hrb hrd) heA,
        c4g_commutator_mul_right' hAC hZ hCd hA.abelian hra hrb hrd]
    have hc_alt : ∀ a : ↥(powSub A 2), c a a = 1 := by
      intro a
      apply Subtype.ext
      simp only [hc, Subgroup.coe_one, commutatorElement_def]
      group
    have hc_eq : ∀ a b : ↥(powSub A 2), c4gXi h hVinv (c a b) = c (c4gXi h hVinv a) (c4gXi h hVinv b) := by
      intro a b
      apply Subtype.ext
      simp only [hc, c4gXi_apply]
      rw [show h.xi ⁅(root a : P), (root b : P)⁆ =
          ⁅h.xi (root a : P), h.xi (root b : P)⁆ from by
        rw [commutatorElement_def, commutatorElement_def]; simp [map_mul, map_inv]]
      have h1 : ∃ e ∈ A, h.xi (root a : P) = e * (root (c4gXi h hVinv a) : P) := by
        have hh : f (c4gXi h hCinv (root a)) = f (root (c4gXi h hVinv a)) := by
          rw [hfeq, hroot, hroot]
        obtain ⟨e, heA, heq⟩ := hcongA (c4gXi h hCinv (root a))
          (root (c4gXi h hVinv a)) hh
        exact ⟨e, heA, by rwa [c4gXi_apply] at heq⟩
      have h2 : ∃ e ∈ A, h.xi (root b : P) = e * (root (c4gXi h hVinv b) : P) := by
        have hh : f (c4gXi h hCinv (root b)) = f (root (c4gXi h hVinv b)) := by
          rw [hfeq, hroot, hroot]
        obtain ⟨e, heA, heq⟩ := hcongA (c4gXi h hCinv (root b))
          (root (c4gXi h hVinv b)) hh
        exact ⟨e, heA, by rwa [c4gXi_apply] at heq⟩
      obtain ⟨e, heA, heq⟩ := h1
      obtain ⟨e', he'A, he'q⟩ := h2
      have hra : (root (c4gXi h hVinv a) : P) ∈ C := (root (c4gXi h hVinv a)).2
      have hrb : (root (c4gXi h hVinv b) : P) ∈ C := (root (c4gXi h hVinv b)).2
      rw [heq, he'q, hswap heA hra, hswap he'A hrb]
      exact calc ⁅(root (c4gXi h hVinv a) : P) * e,
            (root (c4gXi h hVinv b) : P) * e'⁆
          = ⁅(root (c4gXi h hVinv a) : P),
              (root (c4gXi h hVinv b) : P) * e'⁆ :=
              c4g_commutator_mul_mem_left hAC hZ hCd hra (C.mul_mem hrb (hAC he'A)) heA
        _ = ⁅(root (c4gXi h hVinv a) : P), (root (c4gXi h hVinv b) : P)⁆ :=
              c4g_commutator_mul_mem_right hAC hZ hCd hra hrb he'A
    -- the `ξ`-action on `V` is transitive on the non-identity elements
    have hV2 : ∀ x : ↥(powSub A 2), x * x = 1 :=
      fun x => Subtype.ext (by simpa [pow_two] using hVsq x x.2)
    have hVtr : ∀ x y : ↥(powSub A 2), x ≠ 1 → y ≠ 1 →
        ∃ k : ℕ, ((c4gXi h hVinv) ^ k) x = y := by
      intro x y hx1 hy1
      have hx2 : orderOf ((x : ↥(powSub A 2)) : P) = 2 := by
        refine orderOf_eq_two_of_mem_omega1 h ?_ ?_
        · rw [hOmega]; exact x.2
        · intro hc; exact hx1 (Subtype.ext hc)
      have hy2 : orderOf ((y : ↥(powSub A 2)) : P) = 2 := by
        refine orderOf_eq_two_of_mem_omega1 h ?_ ?_
        · rw [hOmega]; exact y.2
        · intro hc; exact hy1 (Subtype.ext hc)
      obtain ⟨k, hk⟩ := h.trans _ _ hx2 hy2
      exact ⟨k, Subtype.ext (by rw [c4gXi_pow_apply]; exact hk)⟩
    -- Gorenstein--Thompson: the form is trivial
    have htriv := equivariant_bihom_trivial hV2 (c4gXi h hVinv) hVtr c hc_mul hc_mul' hc_alt hc_eq
    -- hence every commutator in `C` is trivial
    have hbot : ⁅C, C⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot]
      have h1 : ((c (f ⟨x, hx⟩) (f ⟨y, hy⟩) : ↥(powSub A 2)) : P) = 1 := by
        rw [htriv (f ⟨x, hx⟩) (f ⟨y, hy⟩)]; rfl
      rw [hc] at h1
      obtain ⟨a, haA, ha⟩ := hcongA (root (f ⟨x, hx⟩)) ⟨x, hx⟩ (hroot (f ⟨x, hx⟩))
      obtain ⟨b, hbA, hb⟩ := hcongA (root (f ⟨y, hy⟩)) ⟨y, hy⟩ (hroot (f ⟨y, hy⟩))
      rw [ha, hb, hswap haA hx, hswap hbA hy,
        c4g_commutator_mul_mem_left hAC hZ hCd hx (C.mul_mem hy (hAC hbA)) haA,
        c4g_commutator_mul_mem_right hAC hZ hCd hx hy hbA] at h1
      exact h1
    rw [hCd] at hbot
    exact hA2ne hbot
  · -- ## Case `S = C`: Higman's Lemma 2 gives a contradiction
    refine false_of_sq_all_mem_powSub_two h hA hAC hCA hOmega hA2ne hZ ?_
    intro x hx
    have hxS : x ∈ S := by rw [hSCeq]; exact hx
    obtain ⟨-, hx4⟩ := (hSmem x).mp hxS
    refine hOmA (x ^ 2) (hC2 (pow_mem_powSub (n := 2) hx)) ?_
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hx4

/-! ## The requested lemma -/

/-- **`ω₁(P) = A²` is not trivial**: `A² = Ω₁(P)` contains the involution supplied by
the Suzuki hypothesis together with its identity. -/
theorem c4g_powSub_two_ne_bot (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Work.Higman.powSub A 2 ≠ ⊥ := by
  intro hb
  rw [htop] at hb
  obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
  have hxmem : x ∈ Work.Higman.omega1 P :=
    h.mem_omega1.mpr (by rw [← hx2]; exact pow_orderOf_eq_one x)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  exact hx1 (Subgroup.mem_bot.mp (hb ▸ hxmem))

/-- `A ^ (4) = ⊥` says `A` has exponent dividing `4`. -/
theorem c4g_pow_four_eq_one {A : Subgroup P} (hA4 : Work.Higman.powSub A 4 = ⊥) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  intro a ha
  have h1 : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub (n := 4) ha
  rw [hA4] at h1
  exact Subgroup.mem_bot.mp h1

/-- **The central gap case of the `C₄` exclusion** (Gorenstein–Thompson): if `A` is a
`ξ`-invariant abelian normal subgroup of a Suzuki 2-group with `A² = Ω₁(P)`, `A⁴ = 1`,
`[P,P] = A` and all squares in `A`, and if `C` is a `ξ`-invariant normal subgroup minimal over
`A` with `[C,C] = A²`, `C² ≤ A` and `A` centralising `C`, then we get a contradiction. -/
theorem c4_gap_central {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) : False := by
  exact c4g_alt_pairing h hA hCn hCinv hAC (Ne.symm hCA) hcover hZ hC2 hCd
    htop.symm (c4g_powSub_two_ne_bot h htop) (c4g_pow_four_eq_one hA4)

end Work.Higman.H8

