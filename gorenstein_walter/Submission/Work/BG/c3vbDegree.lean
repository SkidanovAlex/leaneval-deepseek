import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lambda
import Submission.Work.BG.lemma24
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma33Leaf
import Submission.Work.BG.lemma34Leaf
import Submission.Work.BG.c3LamOrbitKappa
import Submission.Work.BG.c3vbOrbit
import Submission.Work.BG.c3vbBKData
import Submission.Work.BG.c3vbDefs
import Submission.Work.BG.c3vbDescendIrr
import Submission.Work.BG.c3vbDirectFactorRestrict
import Submission.Work.BG.c3vbConstituentFixed
import Submission.Work.BG.pieceAInv
import Submission.Work.BG.kInvNormal
import Submission.Work.BG.HatInjDefs

/-!
# Area BG: `Work.BG.c3vbDegree` (BG 1981, Theorem C(3), the degree of `ν ∈ 𝒮(χ₁)`)

**Statement.**  In the Theorem C configuration (`Compat`, `ThmCHyps`, `4 ≤ D.n`, `Sec3Hyp`,
coherent `f`, admissible `κ`), for `ν ∈ 𝒮(χ₁) = bset C f χ₁` with `ν ≠ κ` there is an
irreducible character `β` of `B = C_U(S) = D.B` with `ν(1) = β(1)` or `ν(1) = 2β(1)`.

**Route** (BG 1981, p. 210, the display after (2)):

1. `κ ∈ 𝒮(χ₁)` (from `hi`) is `s`-fixed with `|Λκ| = D.n` (`c3LamOrbitKappa`), so by
   `sconj_mem_lamOrbit_of_fixed` (`c3vbOrbit`) the `s`-conjugate of `ν` lies in `Λν`; hence
   `ν^s = λν` with `λ ∈ Λ`, and `restrictU C ν` is `σ`-invariant (`σ = sigmaU C`, conjugation
   by `t₁`).
2. `|Λν| ≠ D.n`: otherwise Lemma 3.3 (`lemma33Leaf`, applied to `ν` and `κ`) or Lemma 3.4
   (`lemma34Leaf`) gives `D.n = 2`, resp. `𝒮(χ₁) = {ν, ν^s} ∌ κ`.
3. By Remark 3.1 (`rem31Shape`) therefore `ν|_U = a + a₂` with `a₂ ≠ a`, `a₂(1) = a(1)` and
   `2|Λν| = D.n`; hence `ν(1) = 2 a(1)`.  Transported to `↥U`: `restrictU C ν = A + A₂` with
   `A(1) = a(1)`.
4. `A` is fixed by `σ` (conjugation by `t₁`) or by `τ` (conjugation by `t₂`):
   `Work.BG.c3vbConstituentFixed`, whose inputs are `c3vbDefs` (`tauU = sigmaU * yU`,
   `yU² = 1` from `Sec3Hyp`) and Clifford theory for `ν|_U`.
5. `K = K₁ ⊓ K₂` is normal in `U` and inverted by `t₁` and `t₂` (`kInvNormal`), so
   `pieceAInv` gives `K ≤ ker A`.
6. `U = (B₁ ⊓ K₂) × (B ⊔ (K₁ ⊓ K₂))` (`hThm`), with `B₁ ⊓ K₂ ≤ K₂` abelian (`t₂` inverts
   `K₂`), so `c3vbDirectFactorRestrict` gives `A|_C ∈ Irr(C)` for `C = B ⊔ (K₁ ⊓ K₂)` with
   `(A|_C)(1) = A(1)`; `K ≤ ker A` gives `K ≤ ker(A|_C)`, and `C ⧸ K ≅ B` (`c3vbBKData`)
   turns `A|_C` into `β ∈ Irr(D.B)` with `β(1) = A(1)` (`c3vbDescendIrr`).
7. `ν(1) = 2A(1) = 2β(1)` — the second disjunct of the conclusion.

Steps 1–7 are all implemented below; the auxiliary facts used are
`Work.BG.c3LamOrbitKappa`, `Work.BG.sconj_mem_lamOrbit_of_fixed`, `Work.BG.lemma33Leaf`,
`Work.BG.lemma34Leaf`, `Work.BG.rem31Shape`, `Work.BG.c3vbConstituentFixed`,
`Work.BG.kInvNormal`, `Work.BG.pieceAInv`, `Work.BG.c3vbDirectFactorRestrict`,
`Work.BG.c3vbBKData`, `Work.BG.c3vbDescendIrr`, and the local `commute_of_mulAut_inv`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `restrictU C ν` is the restriction `ν|_U` transported along `↥(U.subgroupOf H₀) ≃* ↥U`. -/
theorem restrictU_eq_compHom (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    restrictU C ν = ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).symm.toMonoidHom
      (ClassFunction.restrict (Uin C) ν) := by
  ext u
  rfl

/-- **A subgroup inverted by an automorphism is abelian.**  If `φ x = x⁻¹` for every `x ∈ K`,
then `φ` is an anti-automorphism whose square is the identity on `K`, so `K` is abelian:
`φ (a⁻¹b⁻¹) = a·b` while also `φ (a⁻¹b⁻¹) = (a⁻¹b⁻¹)⁻¹ = b·a`. -/
private theorem commute_of_mulAut_inv {X : Type*} [Group X] (K : Subgroup X) (φ : X ≃* X)
    (hφ : ∀ x ∈ K, φ x = x⁻¹) : ∀ a b : ↥K, a * b = b * a := by
  intro a b
  apply Subtype.ext
  have h4 : φ ((a : X)⁻¹ * (b : X)⁻¹) = (a : X) * (b : X) := by
    rw [map_mul, hφ (a : X)⁻¹ (K.inv_mem a.2), hφ (b : X)⁻¹ (K.inv_mem b.2),
      inv_inv, inv_inv]
  have h5 : φ ((a : X)⁻¹ * (b : X)⁻¹) = (b : X) * (a : X) := by
    rw [hφ ((a : X)⁻¹ * (b : X)⁻¹) (K.mul_mem (K.inv_mem a.2) (K.inv_mem b.2)),
      mul_inv_rev, inv_inv, inv_inv]
  exact h4.symm.trans h5

theorem c3vbDegree {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hThm : Work.GW2.C16.ThmCHyps D K1 K2) (hn : 4 ≤ D.n)
    (hSec3 : Work.GW2.C16.Sec3Hyp D)
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
         OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (κ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) (hκ : Work.GW2.C16.IsKappa D C κ)
    (χ₁ : OddOrder.RepresentationTheory.ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ₁)
    (hi : OddOrder.RepresentationTheory.ClassFunction.inner χ₁ (f κ) = 1)
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hν : ν ∈ Work.GW2.C16.bset C f χ₁) (hνκ : ν ≠ κ) :
    ∃ β : OddOrder.RepresentationTheory.ClassFunction ↥D.B ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter β ∧ (ν 1 = β 1 ∨ ν 1 = 2 * β 1) := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI hFintypeU : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI hInvU : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨hκirr, hκ1, hκsconj, hκS0, hκne⟩ := hκ
  have hκmem : κ ∈ bset C f χ₁ := ⟨hκirr, by rw [hi]; norm_num⟩
  have hκorb : (lamOrbit C κ).ncard = D.n := c3LamOrbitKappa D C hC κ hκS0
  have hνirr : IsIrreducibleCharacter ν := hν.1
  -- **(2)** the `s`-conjugate of `ν` lies in its own `Λ`-orbit
  have hsconjν : sconj C ν ∈ lamOrbit C ν :=
    sconj_mem_lamOrbit_of_fixed D C f χ₁ hC hSec3 hf hχ hκmem hκsconj hν
  -- **`|Λν| ≠ D.n`** (BG p. 210 (2))
  have hνorb : (lamOrbit C ν).ncard ≠ D.n := by
    intro hcard
    by_cases hfix : sconj C ν = ν
    · obtain ⟨h2, -, -⟩ :=
        lemma33Leaf D C hC hSec3 f hf χ₁ hχ ν hν κ hκmem hνκ hfix hκsconj hcard hκorb
      omega
    · obtain ⟨hset, -⟩ := lemma34Leaf D C hC hSec3 f hf χ₁ hχ ν hν hfix (Or.inr hcard)
      have hmem : κ = ν ∨ κ = sconj C ν := by
        have h := hκmem
        rw [hset] at h
        simpa using h
      rcases hmem with h | h
      · exact hνκ h.symm
      · have h2 : sconj C κ = ν := by rw [h, sconj_sconj]
        rw [hκsconj] at h2
        exact hνκ h2.symm
  -- **Remark 3.1**: the shape of `ν|_U`
  obtain ⟨a₀, ha₀, hshape⟩ := rem31Shape D C hC hSec3 ν hνirr
  obtain ⟨a₂₀, ha₂₀, hne₀, hdeg₀, hres₀, hcard₀⟩ :
      ∃ a₂ : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a₂ ∧ a₂ ≠ a₀ ∧ a₂ 1 = a₀ 1 ∧
        ClassFunction.restrict (Uin C) ν = a₀ + a₂ ∧ 2 * (lamOrbit C ν).ncard = D.n := by
    rcases hshape with ⟨-, hc⟩ | h2
    · exact absurd hc hνorb
    · exact h2
  -- transport the shape to `↥U` along `↥(U.subgroupOf H₀) ≃* ↥U`
  let e : ↥(Uin C) ≃* ↥C.P.U := Subgroup.subgroupOfEquivOfLe C.P.U_le_H0
  let A : ClassFunction ↥C.P.U ℂ := ClassFunction.compHom e.symm.toMonoidHom a₀
  let A₂ : ClassFunction ↥C.P.U ℂ := ClassFunction.compHom e.symm.toMonoidHom a₂₀
  have hA : IsIrreducibleCharacter A := ha₀.compHom_of_surjective e.symm.surjective
  have hA₂ : IsIrreducibleCharacter A₂ := ha₂₀.compHom_of_surjective e.symm.surjective
  have hAne : A₂ ≠ A := fun h => hne₀ (by
    ext x
    have h2 := congrArg (fun φ : ClassFunction ↥C.P.U ℂ => φ (e x)) h
    simpa [A, A₂] using h2)
  have hresU : restrictU C ν = A + A₂ := by
    rw [restrictU_eq_compHom C ν, hres₀]
    rfl
  have hA1 : A 1 = a₀ 1 := rfl
  have hν1 : ν 1 = 2 * A 1 := by
    have h := congrArg (fun φ : ClassFunction ↥(Uin C) ℂ => φ (1 : ↥(Uin C))) hres₀
    simp only [ClassFunction.add_apply] at h
    have h' : (ClassFunction.restrict (Uin C) ν) (1 : ↥(Uin C)) = ν 1 := rfl
    rw [h'] at h
    rw [h, hdeg₀, hA1]
    ring
  -- **`restrictU C ν` is `σ`-invariant** (`σ` = conjugation by `s = t₁`)
  have hσfix : ∀ u : ↥C.P.U, restrictU C ν (sigmaU C u) = restrictU C ν u := by
    obtain ⟨β, hβ⟩ := hsconjν
    intro u
    have hkey : conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
        = (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) :=
      Subtype.ext (by rw [conjMulEquiv_apply, sigmaU_apply_coe])
    have hlamU : lamCF C β (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0) = 1 := by
      have hq : quotMk C.P ⟨(u : G), C.P.U_le_H0 u.2⟩ = 1 :=
        (QuotientGroup.eq_one_iff (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)).mpr (by
          rw [Subgroup.mem_subgroupOf]; exact u.2)
      rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, hq, map_one]
      rfl
    calc restrictU C ν (sigmaU C u)
        = ν (⟨((sigmaU C u : ↥C.P.U) : G), C.P.U_le_H0 (sigmaU C u).2⟩ : ↥C.P.H0) := rfl
      _ = ν (conjMulEquiv C.P C.s (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)) := by rw [hkey]
      _ = conjByH C.P C.s ν ⟨(u : G), C.P.U_le_H0 u.2⟩ := rfl
      _ = sconj C ν ⟨(u : G), C.P.U_le_H0 u.2⟩ := rfl
      _ = (lamCF C β * ν) ⟨(u : G), C.P.U_le_H0 u.2⟩ := by rw [hβ]
      _ = lamCF C β ⟨(u : G), C.P.U_le_H0 u.2⟩ * ν ⟨(u : G), C.P.U_le_H0 u.2⟩ :=
          ClassFunction.mul_apply _ _ _
      _ = 1 * ν ⟨(u : G), C.P.U_le_H0 u.2⟩ := by rw [hlamU]
      _ = restrictU C ν u := by rw [restrictU_apply, one_mul]
  -- **the constituent `A` is fixed by `σ` or by `τ` (conjugation by `t₂`)**
  have hfixA_or : (∀ u : ↥C.P.U, A (sigmaU C u) = A u) ∨
      (∀ u : ↥C.P.U, A (tauU D C hC u) = A u) :=
    c3vbConstituentFixed D C hC hSec3 hνirr A A₂ hA hA₂ hAne hresU hσfix
  -- **`K = K₁ ⊓ K₂` is normal in `U`, inverted by `t₁` and by `t₂`** (`kInvNormal`)
  obtain ⟨hKleU, hKN, hKinv1, hKinv2⟩ := kInvNormal G D K1 K2 hThm
  haveI hKnorm : ((K1 ⊓ K2).subgroupOf C.P.U).Normal :=
    ⟨fun n hn g => by
      have h := hKN (g : G) (by rw [← hC.U_eq]; exact g.2) (n : G)
        (by rwa [Subgroup.mem_subgroupOf] at hn)
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  have hKodd : Odd (Nat.card ↥((K1 ⊓ K2).subgroupOf C.P.U)) :=
    Odd.of_dvd_nat (odd_card_U_of_compat hC) (Subgroup.card_subgroup_dvd_card _)
  -- **`K ≤ ker A`** (BG p. 210), from `pieceAInv`
  have hKA : ∀ u : ↥C.P.U, (u : G) ∈ K1 ⊓ K2 → A u = A 1 := by
    intro u hu
    have hmem : u ∈ (K1 ⊓ K2).subgroupOf C.P.U := by rwa [Subgroup.mem_subgroupOf]
    rcases hfixA_or with hfixA | hfixA
    · have hσinv : ∀ k ∈ (K1 ⊓ K2).subgroupOf C.P.U, sigmaU C k = k⁻¹ := by
        intro k hk
        apply Subtype.ext
        rw [sigmaU_apply_coe, Subgroup.coe_inv, hC.s_eq]
        exact hKinv1 (k : G) (by rwa [Subgroup.mem_subgroupOf] at hk)
      exact pieceAInv ((K1 ⊓ K2).subgroupOf C.P.U) (odd_card_U_of_compat hC) (sigmaU C) hσinv A hA hfixA u hmem
    · have hτinv : ∀ k ∈ (K1 ⊓ K2).subgroupOf C.P.U, tauU D C hC k = k⁻¹ := by
        intro k hk
        apply Subtype.ext
        rw [tauU_apply_coe, Subgroup.coe_inv]
        exact hKinv2 (k : G) (by rwa [Subgroup.mem_subgroupOf] at hk)
      exact pieceAInv ((K1 ⊓ K2).subgroupOf C.P.U) (odd_card_U_of_compat hC) (tauU D C hC) hτinv A hA hfixA u hmem
  -- **Step 6**: `U = (B₁ ⊓ K₂) × (B ⊔ (K₁ ⊓ K₂))` and the descent to `B = C_U(S)`
  obtain ⟨hdir_sup, hdir_inf, hdir_comm⟩ := hThm.2.2.1
  have hAleU : D.B1 ⊓ K2 ≤ C.P.U := by
    rw [hC.U_eq, ← hdir_sup]
    exact le_sup_left
  have hBleU : D.B ⊔ (K1 ⊓ K2) ≤ C.P.U := by
    rw [hC.U_eq, ← hdir_sup]
    exact le_sup_right
  -- the two complementary subgroups of `↥U`
  set Ap : Subgroup ↥C.P.U := (D.B1 ⊓ K2).subgroupOf C.P.U with hApdef
  set Cp : Subgroup ↥C.P.U := (D.B ⊔ (K1 ⊓ K2)).subgroupOf C.P.U with hCpdef
  have hsup : Ap ⊔ Cp = ⊤ := by
    have h : ((D.B1 ⊓ K2) ⊔ (D.B ⊔ (K1 ⊓ K2))).subgroupOf C.P.U
        = (D.B1 ⊓ K2).subgroupOf C.P.U ⊔ (D.B ⊔ (K1 ⊓ K2)).subgroupOf C.P.U :=
      Subgroup.subgroupOf_sup hAleU hBleU
    rw [hdir_sup, ← hC.U_eq, Subgroup.subgroupOf_self] at h
    rw [hApdef, hCpdef]
    exact h.symm
  have hinf : Ap ⊓ Cp = ⊥ := by
    have h : ((D.B1 ⊓ K2) ⊓ (D.B ⊔ (K1 ⊓ K2))).subgroupOf C.P.U
        = (D.B1 ⊓ K2).subgroupOf C.P.U ⊓ (D.B ⊔ (K1 ⊓ K2)).subgroupOf C.P.U :=
      Subgroup.comap_inf (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) C.P.U.subtype
    rw [hdir_inf, Subgroup.bot_subgroupOf] at h
    rw [hApdef, hCpdef]
    exact h.symm
  have hcommAp : ∀ a ∈ Ap, ∀ c ∈ Cp, a * c = c * a := by
    intro a ha c hc
    have ha' : (a : G) ∈ D.B1 ⊓ K2 := by
      rw [hApdef, Subgroup.mem_subgroupOf] at ha
      exact ha
    have hc' : (c : G) ∈ D.B ⊔ (K1 ⊓ K2) := by
      rw [hCpdef, Subgroup.mem_subgroupOf] at hc
      exact hc
    apply Subtype.ext
    show (a : G) * (c : G) = (c : G) * (a : G)
    exact hdir_comm (a : G) ha' (c : G) hc'
  have hApinv : ∀ x ∈ Ap, tauU D C hC x = x⁻¹ := by
    intro x hx
    have hx' : (x : G) ∈ K2 := by
      rw [hApdef, Subgroup.mem_subgroupOf] at hx
      exact hx.2
    apply Subtype.ext
    rw [tauU_apply_coe, Subgroup.coe_inv]
    exact hThm.2.1.2.2.1 (x : G) hx'
  have habelAp : ∀ a b : ↥Ap, a * b = b * a :=
    commute_of_mulAut_inv Ap (tauU D C hC) hApinv
  obtain ⟨hirrC, hdegC⟩ :=
    c3vbDirectFactorRestrict Ap Cp hsup hinf hcommAp habelAp A hA
  -- the quotient data on `X = B ⊔ (K₁ ⊓ K₂)`
  obtain ⟨hBinK, _hnU, hnX, _hidx⟩ := c3vbBKData D K1 K2 hThm.1 hThm.2.1 hThm.2.2.1
  haveI hKpN : ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))).Normal := hnX
  haveI hFintX : Fintype ↥(D.B ⊔ (K1 ⊓ K2)) := Fintype.ofFinite _
  haveI hInvX : Invertible (Nat.card ↥(D.B ⊔ (K1 ⊓ K2)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hBs : D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2)) ⊔ (K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))
      = ⊤ := by
    have h : D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2)) ⊔ (K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))
        = (D.B ⊔ (K1 ⊓ K2)).subgroupOf (D.B ⊔ (K1 ⊓ K2)) :=
      (Subgroup.subgroupOf_sup (le_sup_left : D.B ≤ D.B ⊔ (K1 ⊓ K2))
        (le_sup_right : K1 ⊓ K2 ≤ D.B ⊔ (K1 ⊓ K2))).symm
    rw [Subgroup.subgroupOf_self] at h
    exact h
  have hBi : D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2)) ⊓ (K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))
      = ⊥ := by
    have h : (D.B ⊓ (K1 ⊓ K2)).subgroupOf (D.B ⊔ (K1 ⊓ K2))
        = D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2)) ⊓ (K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2)) :=
      Subgroup.comap_inf D.B (K1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)).subtype
    rw [hBinK, Subgroup.bot_subgroupOf] at h
    exact h.symm
  -- the character `ψ` of `X` obtained from `A|_C`
  let e : ↥Cp ≃* ↥(D.B ⊔ (K1 ⊓ K2)) := Subgroup.subgroupOfEquivOfLe hBleU
  let ψ : ClassFunction ↥(D.B ⊔ (K1 ⊓ K2)) ℂ :=
    ClassFunction.compHom e.symm.toMonoidHom (ClassFunction.restrict Cp A)
  have hψirr : IsIrreducibleCharacter ψ :=
    IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective hirrC
  have hψ1 : ψ 1 = A 1 := by
    dsimp only [ψ]
    rw [ClassFunction.compHom_apply, map_one]
    exact hdegC
  have hcoee : ∀ x : ↥(D.B ⊔ (K1 ⊓ K2)),
      ((((e.symm.toMonoidHom x : ↥Cp) : ↥C.P.U) : G)) = (x : G) := by
    intro x
    have h := Subgroup.subgroupOfEquivOfLe_apply_coe hBleU (e.symm x)
    rw [show (Subgroup.subgroupOfEquivOfLe hBleU) (e.symm x) = x from
      MulEquiv.apply_symm_apply e x] at h
    exact h.symm
  have hker : ∀ k ∈ (K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2)), ψ k = ψ 1 := by
    intro k hk
    have hkG : (k : G) ∈ K1 ⊓ K2 := by rwa [Subgroup.mem_subgroupOf] at hk
    have h1 : ψ k = A (e.symm.toMonoidHom (k : ↥(D.B ⊔ (K1 ⊓ K2))) : ↥C.P.U) := by
      dsimp only [ψ]
      rw [ClassFunction.compHom_apply, ClassFunction.restrict_apply]
    rw [h1, hψ1]
    exact hKA _ (by rw [hcoee]; exact hkG)
  obtain ⟨β', hβ'irr, hβ'1⟩ :=
    c3vbDescendIrr (D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2)))
      ((K1 ⊓ K2).subgroupOf (D.B ⊔ (K1 ⊓ K2))) hBs hBi ψ hψirr hker
  -- **Step 7**: transport `β'` from `↥Bp` to `↥D.B` and read off the degree
  let f : ↥(D.B.subgroupOf (D.B ⊔ (K1 ⊓ K2))) ≃* ↥D.B :=
    Subgroup.subgroupOfEquivOfLe (le_sup_left : D.B ≤ D.B ⊔ (K1 ⊓ K2))
  refine ⟨ClassFunction.compHom f.symm.toMonoidHom β', ?_, Or.inr ?_⟩
  · exact hβ'irr.compHom_of_surjective f.symm.surjective
  · have hβ1 : (ClassFunction.compHom f.symm.toMonoidHom β') 1 = A 1 := by
      rw [ClassFunction.compHom_apply, map_one, hβ'1, hψ1]
    rw [hβ1]
    exact hν1

end Work.BG
