import Mathlib
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma24
import Submission.Work.BG.L41Aux
import Submission.Work.BG.deltaShape
import Submission.Work.BG.Hat
import Submission.Work.BG.centralValue
import Submission.Work.BG.sconjLam
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.H0Conj
import Submission.Work.BG.hatInj
import Submission.Work.BG.l41iiiInvSum
import Submission.Work.BG.l41iiiInvAlg
import Submission.Work.BG.l41iiiDelta
import Submission.Work.BG.l41iiiFinsum
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Area BG: Bender–Glauberman 1981, Lemma 4.1 (iii)

`Work.BG.l41iii` proves `Work.GW2.C23.L41iiiProp' D C` (BG 1981, Lemma 4.1 (iii), p. 212):

> for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`, `χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂` (mod 2) on `B`.

Here `𝒮'(χ) = {ν ∈ Irr(H₀) | ν^s = ν, ν(t) = ν(1), (χ, δ_ν) ≠ 0}` with `δ_ν = (ν - λ₂ν)^G`, and
`ν̂ ∈ Irr(B)` is any "hat" of `ν`: an irreducible character of `B` congruent to `ν` mod 2
(`HatOf D C ν ν̂`).

## The argument

Write `H₀ = U × ⟨t⟩`, so `Λ = H₀/U = {1, λ₂}` and the `Λ`-orbits on `Irr(H₀)` are the pairs
`{ν, λ₂ν}`.  Since `δ_ν = (ν - λ₂ν)^G`, Frobenius reciprocity gives (for *every* `ν`)

  `(χ, δ_ν)_G = (χ|_{H₀}, ν)_{H₀} - (χ|_{H₀}, λ₂ν)_{H₀}`.

Consequently, for `b ∈ B`, the Fourier expansion `χ(b) = Σ_{ν} (χ|_{H₀}, ν) ν(b)` of `χ|_{H₀}`
may be regrouped orbit by orbit, and each orbit with representative `ν(t) = ν(1)` contributes
`(χ|_{H₀},ν) ν(b) + (χ|_{H₀},λ₂ν) (λ₂ν)(b) ≡ (χ,δ_ν) ν(b) (mod 2)`, because `λ₂ = 1` on
`B ≤ U`.  The involution `ν ↦ λ₂ν` is fixed-point free on `Irr(H₀)`, so the pairing lemma
`l41iiiInvSum` turns this into

  `χ(b) ≡ Σ_{ν(t) = ν(1)} (χ, δ_ν) ν(b) (mod 2)`.

Inside that index set the `s`-conjugation `ν ↦ ν^s` is a second fixed-point-free involution
away from `𝒮₄(C)`; its two-element orbits contribute equal terms
(`δ_{ν^s} = δ_ν` since induction to `G` does not see `s`, and `ν^s(b) = ν(b)` for `b ∈ B`),
so by `l41iiiInvAlg` they drop out modulo `2`.  What is left is

  `χ(b) ≡ Σ_{ν ∈ 𝒮₄(C)} (χ, δ_ν) ν(b) (mod 2)`.

Finally `deltaShape` (`Work.GW2.C23.DeltaShapeProp`) says that `δ_ν`, for `ν ∈ 𝒮₄(C)`, is a sum
of four *distinct* `±Irr` characters of `G` with coefficients `±1`; hence `(χ, δ_ν) ∈ {0,±1}`
and may be replaced by the indicator of `𝒮'(χ)`.  The result is the congruence with the sum
running over `𝒮'(χ)`.

Finiteness of `𝒮'(χ)` is immediate: it is contained in the range of the coercion from the
finite type `IrreducibleCharacter ↥C.P.H0`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23

variable {G : Type} [Group G] [Finite G]

section Base

variable (C : Work.BG.Sec2Ctx G) [Fintype G] [Fintype ↥C.P.H0]
  [Invertible (Nat.card ↥C.P.H0 : ℂ)]

/-- **Frobenius reciprocity**, in the orientation used below: `(χ, θ^G)_G = (χ|_{H₀}, θ)_{H₀}`
(the defining adjunction of induction and restriction). -/
theorem l41iii_inner_ind [Fintype G] [Invertible (Nat.card G : ℂ)] (χ : ClassFunction G ℂ)
    (θ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.inner χ (ind C θ) = ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) θ := by
  rw [ClassFunction.inner_star_comm χ (ind C θ),
    ClassFunction.inner_induce_eq_inner_restrict (H := C.P.H0) θ χ,
    ClassFunction.inner_star_comm θ (ClassFunction.restrict C.P.H0 χ), star_star]

/-- **The Fourier coefficient of `χ` at `δ_ν`** is the difference of the `H₀`-multiplicities of
`ν` and `λ₂ν`. -/
theorem l41iii_inner_delta [Fintype G] [Invertible (Nat.card G : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (χ : ClassFunction G ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.inner χ (delta C β₂ ν) =
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν -
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (lamCF C β₂ * ν) := by
  rw [delta, l41iii_inner_ind C χ (ν - lamCF C β₂ * ν), ClassFunction.inner_sub_right]

/-- The involution `ν ↦ λ₂ν` on `Irr(H₀)`. -/
noncomputable def l41iii_lamTwo (β₂ : quotGroup C.P →* ℂˣ) (a : IrreducibleCharacter ↥C.P.H0) :
    IrreducibleCharacter ↥C.P.H0 :=
  ⟨lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ), lam_two_mul_irr C a.2⟩

theorem l41iii_lamTwo_coe {β₂ : quotGroup C.P →* ℂˣ} (a : IrreducibleCharacter ↥C.P.H0) :
    ((l41iii_lamTwo C β₂ a : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ) =
      lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ) := rfl

/-- `λ₂` is an involution on `Irr(H₀)`. -/
theorem l41iii_lamTwo_involutive {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (a : IrreducibleCharacter ↥C.P.H0) : l41iii_lamTwo C β₂ (l41iii_lamTwo C β₂ a) = a := by
  refine Subtype.ext ?_
  show lamCF C β₂ * (lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ)) =
    (a : ClassFunction ↥C.P.H0 ℂ)
  ext g
  have hsq : lamCF C β₂ g * lamCF C β₂ g = 1 := by
    have h := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ g)
      (lamCF_two_mul_self C (β₂ := β₂) h2)
    simpa [ClassFunction.mul_apply, linearClassFunction_apply] using h
  rw [ClassFunction.mul_apply, ClassFunction.mul_apply, ← mul_assoc, hsq, one_mul]

/-- `λ₂ν ≠ ν`: `λ₂` has no fixed points on `Irr(H₀)`. -/
theorem l41iii_lamTwo_ne_self {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ₂ : β₂ ≠ 1) (a : IrreducibleCharacter ↥C.P.H0) : l41iii_lamTwo C β₂ a ≠ a := by
  intro h
  have h' : (l41iii_lamTwo C β₂ a : ClassFunction ↥C.P.H0 ℂ) =
      (a : ClassFunction ↥C.P.H0 ℂ) := congrArg Subtype.val h
  exact lam_two_mul_ne_self C (β₂ := β₂) h2 hβ₂ a.2
    ((l41iii_lamTwo_coe C (β₂ := β₂) a).symm.trans h')

/-- The value of `λ₂ν` at `t` is the negative of the value of `ν`. -/
theorem l41iii_lamTwo_apply_t {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ₂ : β₂ ≠ 1) (a : IrreducibleCharacter ↥C.P.H0) :
    (l41iii_lamTwo C β₂ a : ClassFunction ↥C.P.H0 ℂ) C.t = -(a : ClassFunction ↥C.P.H0 ℂ) C.t := by
  rw [l41iii_lamTwo_coe, ClassFunction.mul_apply, lamCF_two_apply_t C (β₂ := β₂) h2 hβ₂]
  ring

/-- The value of `λ₂ν` at `1`. -/
theorem l41iii_lamTwo_apply_one {β₂ : quotGroup C.P →* ℂˣ} (a : IrreducibleCharacter ↥C.P.H0) :
    (l41iii_lamTwo C β₂ a : ClassFunction ↥C.P.H0 ℂ) 1 = (a : ClassFunction ↥C.P.H0 ℂ) 1 := by
  show (lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ)) 1 = (a : ClassFunction ↥C.P.H0 ℂ) 1
  rw [ClassFunction.mul_apply]
  have h1 : lamCF C β₂ (1 : ↥C.P.H0) = 1 := by
    show (ClassFunction.compHom (quotMk C.P) (linearClassFunction β₂)) (1 : ↥C.P.H0) = 1
    rw [ClassFunction.compHom_apply, linearClassFunction_apply, map_one (quotMk C.P),
      map_one β₂, Units.val_one]
  rw [h1, one_mul]

/-- `λ₂` maps each `Λ`-orbit onto the other half of the "`t`-sign" partition. -/
theorem l41iii_lamTwo_t_iff {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2)
    (hβ₂ : β₂ ≠ 1) (a : IrreducibleCharacter ↥C.P.H0) :
    ((l41iii_lamTwo C β₂ a : ClassFunction ↥C.P.H0 ℂ) C.t = (l41iii_lamTwo C β₂ a : ClassFunction ↥C.P.H0 ℂ) 1) ↔
      ¬ ((a : ClassFunction ↥C.P.H0 ℂ) C.t = (a : ClassFunction ↥C.P.H0 ℂ) 1) := by
  have ht := l41iii_lamTwo_apply_t C (β₂ := β₂) h2 hβ₂ a
  have h1 := l41iii_lamTwo_apply_one C (β₂ := β₂) a
  have h0 := irr_apply_one_ne_zero C a.2
  rw [ht, h1]
  constructor
  · intro h ht1
    rw [ht1] at h
    have hsum : (a : ClassFunction ↥C.P.H0 ℂ) 1 + (a : ClassFunction ↥C.P.H0 ℂ) 1 = 0 :=
      neg_eq_iff_add_eq_zero.mp h
    have hzero : (a : ClassFunction ↥C.P.H0 ℂ) 1 = 0 := by
      have h2 : (2 : ℂ) * (a : ClassFunction ↥C.P.H0 ℂ) 1 = 0 := by
        rw [two_mul]; exact hsum
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact absurd hzero h0
  · intro h
    rcases t_val_or C a.2 with h' | h'
    · exact absurd h' h
    · rw [h']; ring

/-- **The `s`-conjugate has the same `δ`**: `δ_{ν^s} = δ_ν`, since induction to `G` does not see
`s`. -/
theorem l41iii_delta_sconj {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ₂ : β₂ ≠ 1) (ν : ClassFunction ↥C.P.H0 ℂ) :
    delta C β₂ (sconj C ν) = delta C β₂ ν := by
  have hlam : lamCF C β₂ * sconj C ν = sconj C (lamCF C β₂ * ν) := by
    rw [sconjLam C β₂ ν, lamCF_two_inv_eq C h2 hβ₂]
  change ind C (sconj C ν - lamCF C β₂ * sconj C ν) = ind C (ν - lamCF C β₂ * ν)
  rw [hlam, l41_ind_sconj_sub C ν (lamCF C β₂ * ν)]

/-- The value of `sconj C ν` at `t`. -/
theorem l41iii_sconj_apply_t (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ν C.t = ν C.t := by
  rw [sconj, conjByH_apply]
  have h : conjMulEquiv C.P C.s C.t = C.t := by
    refine Subtype.ext ?_
    rw [conjMulEquiv_apply]
    have hcomm : (C.s : G) * (C.t : G) = (C.t : G) * (C.s : G) := C.t_comm_H C.s C.s.2
    rw [hcomm, mul_inv_cancel_right]
  rw [h]

end Base

section Mid

variable (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype G] [Fintype ↥C.P.H0]
  [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥C.P.H0 : ℂ)]

open scoped Classical in
/-- `𝒮'(χ)` as a `Finset` of `Irr(H₀)`: the preimage of `bset' C β₂ χ` under the coercion. -/
noncomputable def l41iii_bsetFin (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ) :
    Finset (IrreducibleCharacter ↥C.P.H0) :=
  Finset.univ.filter (fun a => (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ)

theorem l41iii_bsetFin_mem {β₂ : quotGroup C.P →* ℂˣ} {χ : ClassFunction G ℂ}
    (a : IrreducibleCharacter ↥C.P.H0) :
    a ∈ l41iii_bsetFin C β₂ χ ↔ (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ := by
  classical
  simp [l41iii_bsetFin]

open scoped Classical in
/-- The "`t`-sign" half of `Irr(H₀)`: the irreducibles with `ν(t) = ν(1)`. -/
noncomputable def l41iii_Sp : Finset (IrreducibleCharacter ↥C.P.H0) :=
  Finset.univ.filter (fun a =>
    (a : ClassFunction ↥C.P.H0 ℂ) C.t = (a : ClassFunction ↥C.P.H0 ℂ) 1)

theorem l41iii_Sp_mem (a : IrreducibleCharacter ↥C.P.H0) :
    a ∈ l41iii_Sp C ↔ (a : ClassFunction ↥C.P.H0 ℂ) C.t = (a : ClassFunction ↥C.P.H0 ℂ) 1 := by
  classical
  simp [l41iii_Sp]

open scoped Classical in
/-- `𝒮₄(C)`, as the `s`-fixed part of the `t`-sign half. -/
noncomputable def l41iii_S4 : Finset (IrreducibleCharacter ↥C.P.H0) :=
  (l41iii_Sp C).filter (fun a =>
    sconj C (a : ClassFunction ↥C.P.H0 ℂ) = (a : ClassFunction ↥C.P.H0 ℂ))

theorem l41iii_S4_mem (a : IrreducibleCharacter ↥C.P.H0) :
    a ∈ l41iii_S4 C ↔ (a : ClassFunction ↥C.P.H0 ℂ) C.t = (a : ClassFunction ↥C.P.H0 ℂ) 1 ∧
      sconj C (a : ClassFunction ↥C.P.H0 ℂ) = (a : ClassFunction ↥C.P.H0 ℂ) := by
  classical
  simp [l41iii_S4, l41iii_Sp]

/-- The summand `(χ, δ_a)·a(b)` of the middle sum of the proof of Lemma 4.1 (iii). -/
noncomputable def l41iii_W (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ) (b : ↥C.P.H0)
    (a : IrreducibleCharacter ↥C.P.H0) : ℂ :=
  ClassFunction.inner χ (delta C β₂ (a : ClassFunction ↥C.P.H0 ℂ)) *
    ((a : ClassFunction ↥C.P.H0 ℂ) b)

/-- **The heart of Lemma 4.1 (iii)** (BG 1981, p. 212): on `B`, `χ` is congruent mod 2 to the
sum of the `H₀`-irreducibles lying in `𝒮'(χ)`.

The Fourier expansion `χ|_{H₀} = Σ_{a} (χ|_{H₀}, a) a` is first regrouped along the
fixed-point-free involution `a ↦ λ₂a`, using that `(χ|_{H₀}, a) - (χ|_{H₀}, λ₂a) = (χ, δ_a)`
and that `λ₂ = 1` on `B`; inside the resulting index set the fixed-point-free involution
`a ↦ a^s` pairs the terms outside `𝒮₄(C)` (they are equal, since `δ_{a^s} = δ_a` and
`(a^s)(b) = a(b)`), so they drop out modulo 2; and on `𝒮₄(C)` the `deltaShape` structure
theorem turns the coefficient `(χ, δ_a) ∈ {0,±1}` into the indicator of `𝒮'(χ)`. -/
theorem l41iii_mid (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : quotGroup C.P →* ℂˣ} (hβ₂ : β₂ ≠ 1) {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ) :
    ∀ b : ↥C.P.H0, (b : G) ∈ D.B →
      AlgIntModTwo (χ (b : G))
        (∑ a ∈ l41iii_bsetFin C β₂ χ, (a : ClassFunction ↥C.P.H0 ℂ) b) := by
  classical
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hφZ : ClassFunction.restrict C.P.H0 χ ∈ ZIrr ↥C.P.H0 :=
    ClassFunction.restrict_mem_ZIrr C.P.H0 (mem_ZIrr_of_isPmIrr hχ)
  -- ## the values of `λ₂` and of `s`-conjugation on `B`
  have hB_U : ∀ {x : G}, x ∈ D.B → x ∈ C.P.U := by
    intro x hx; rw [hc.U_eq]; exact mem_DU_of_mem_B D hx
  have hlamB : ∀ (β : quotGroup C.P →* ℂˣ) (b : ↥C.P.H0), (b : G) ∈ D.B →
      lamCF C β b = 1 := by
    intro β b hb
    exact Lambda.apply_eq_one_of_mem_U (P := C.P) (δ := lamCF C β) ⟨β, rfl⟩ (hB_U hb)
  have hconjB : ∀ (ν : ClassFunction ↥C.P.H0 ℂ) (b : ↥C.P.H0), (b : G) ∈ D.B →
      sconj C ν b = ν b := by
    intro ν b hb
    have hfix : conjMulEquiv C.P C.s b = b := by
      refine Subtype.ext ?_
      rw [conjMulEquiv_apply]
      have h2' := le_C_t1_of_mem_B D hb
      rw [Subgroup.mem_centralizer_singleton_iff] at h2'
      rw [hc.s_eq, ← h2', mul_assoc, mul_inv_cancel, mul_one]
    rw [sconj, conjByH_apply, hfix]
  have hmulB : ∀ (β : quotGroup C.P →* ℂˣ) (ν : ClassFunction ↥C.P.H0 ℂ) (b : ↥C.P.H0),
      (b : G) ∈ D.B → (lamCF C β * ν) b = ν b := by
    intro β ν b hb
    rw [ClassFunction.mul_apply, hlamB β b hb, one_mul]
  -- ## the Fourier expansion of `χ|_{H₀}`
  have hexp : ∀ b : ↥C.P.H0, χ (b : G) =
      ∑ a : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (a : ClassFunction ↥C.P.H0 ℂ) *
          ((a : ClassFunction ↥C.P.H0 ℂ) b) := by
    intro b
    have h := sum_inner_irreducibleCharacter_smul (ClassFunction.restrict C.P.H0 χ)
    calc χ (b : G) = (ClassFunction.restrict C.P.H0 χ) b := rfl
      _ = (∑ a : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
                (a : ClassFunction ↥C.P.H0 ℂ) • (a : ClassFunction ↥C.P.H0 ℂ)) b := by rw [h]
      _ = ∑ a : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
                (a : ClassFunction ↥C.P.H0 ℂ) * ((a : ClassFunction ↥C.P.H0 ℂ) b) := by
          rw [ClassFunction.sum_apply]
          exact Finset.sum_congr rfl fun a _ => by rw [ClassFunction.smul_apply]
  -- ## integrality of the coefficients of the `λ₂`-partner
  have hcint : ∀ a : IrreducibleCharacter ↥C.P.H0,
      IsIntegral ℤ (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
        (lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ))) := by
    intro a
    obtain ⟨m, hm⟩ := mem_ZIrr_inner_int
      (⟨lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ), lam_two_mul_irr C a.2⟩ :
        IrreducibleCharacter ↥C.P.H0) hφZ
    rw [hm]; exact isIntegral_intCast m
  intro b hb
  -- ## the `s`-involution on `Irr(H₀)`
  let sj : IrreducibleCharacter ↥C.P.H0 → IrreducibleCharacter ↥C.P.H0 := fun a =>
    ⟨sconj C (a : ClassFunction ↥C.P.H0 ℂ),
      IsIrreducibleCharacter.conjByH C.P C.s a.2⟩
  have hsj_coe : ∀ a : IrreducibleCharacter ↥C.P.H0,
      ((sj a : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ) =
        sconj C (a : ClassFunction ↥C.P.H0 ℂ) := fun a => rfl
  have hsj_invol : ∀ a, sj (sj a) = a := by
    intro a
    refine Subtype.ext ?_
    show sconj C (sconj C (a : ClassFunction ↥C.P.H0 ℂ)) = (a : ClassFunction ↥C.P.H0 ℂ)
    exact s02c_sconj_involutive C _
  have hone_sj : ∀ a, ((sj a : IrreducibleCharacter ↥C.P.H0) :
      ClassFunction ↥C.P.H0 ℂ) 1 = (a : ClassFunction ↥C.P.H0 ℂ) 1 := by
    intro a
    show sconj C (a : ClassFunction ↥C.P.H0 ℂ) 1 = (a : ClassFunction ↥C.P.H0 ℂ) 1
    rw [sconj, conjByH_apply, map_one]
  have hsj_Sp : ∀ a, sj a ∈ l41iii_Sp C ↔ a ∈ l41iii_Sp C := by
    intro a
    rw [l41iii_Sp_mem, l41iii_Sp_mem, hsj_coe a, l41iii_sconj_apply_t C
      (a : ClassFunction ↥C.P.H0 ℂ), hone_sj a]
  have hsj_S4 : ∀ a, sj a ∈ l41iii_S4 C ↔ a ∈ l41iii_S4 C := by
    intro a
    rw [l41iii_S4_mem, l41iii_S4_mem, hsj_coe a, l41iii_sconj_apply_t C
      (a : ClassFunction ↥C.P.H0 ℂ), hone_sj a, s02c_sconj_involutive C
      (a : ClassFunction ↥C.P.H0 ℂ)]
    exact and_congr_right fun _ => eq_comm
  have hsj_ne : ∀ a, a ∈ (l41iii_Sp C) \ (l41iii_S4 C) → sj a ≠ a := by
    intro a ha h
    have hSp : a ∈ l41iii_Sp C := (Finset.mem_sdiff.mp ha).1
    have hS4 : a ∉ l41iii_S4 C := (Finset.mem_sdiff.mp ha).2
    refine hS4 ?_
    have hval : (sj a : ClassFunction ↥C.P.H0 ℂ) = (a : ClassFunction ↥C.P.H0 ℂ) :=
      congrArg Subtype.val h
    rw [l41iii_S4_mem]
    exact ⟨(l41iii_Sp_mem C a).mp hSp, by rw [← hsj_coe a]; exact hval⟩
  -- ## Step 1: the `λ₂`-pairing
  have hpair : (∑ a : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (a : ClassFunction ↥C.P.H0 ℂ) *
        ((a : ClassFunction ↥C.P.H0 ℂ) b)) =
      ∑ a ∈ l41iii_Sp C,
        (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (a : ClassFunction ↥C.P.H0 ℂ) *
            ((a : ClassFunction ↥C.P.H0 ℂ) b) +
          ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
              ((l41iii_lamTwo C β₂ a : IrreducibleCharacter ↥C.P.H0) :
                ClassFunction ↥C.P.H0 ℂ) *
            (((l41iii_lamTwo C β₂ a : IrreducibleCharacter ↥C.P.H0) :
                ClassFunction ↥C.P.H0 ℂ) b)) := by
    have h := l41iiiInvSum Finset.univ (l41iii_lamTwo C β₂)
      (fun a : IrreducibleCharacter ↥C.P.H0 =>
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (a : ClassFunction ↥C.P.H0 ℂ) *
          ((a : ClassFunction ↥C.P.H0 ℂ) b))
      (fun a : IrreducibleCharacter ↥C.P.H0 =>
        (a : ClassFunction ↥C.P.H0 ℂ) C.t = (a : ClassFunction ↥C.P.H0 ℂ) 1)
      (fun a _ => Finset.mem_univ (l41iii_lamTwo C β₂ a))
      (fun a _ => l41iii_lamTwo_involutive C (β₂ := β₂) h2 a)
      (fun a _ => l41iii_lamTwo_t_iff C (β₂ := β₂) h2 hβ₂ a)
    simpa [l41iii_Sp] using h
  have hstep1 : AlgIntModTwo
      (∑ a : IrreducibleCharacter ↥C.P.H0,
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (a : ClassFunction ↥C.P.H0 ℂ) *
          ((a : ClassFunction ↥C.P.H0 ℂ) b))
      (∑ a ∈ l41iii_Sp C, l41iii_W (C := C) β₂ χ b a) := by
    rw [hpair]
    refine AlgIntModTwo.sum _ fun a _ => ?_
    have hXint : IsIntegral ℤ ((a : ClassFunction ↥C.P.H0 ℂ) b) :=
      OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr (IsIrreducibleCharacter.mem_ZIrr a.2) b
    have hdelta_a := l41iii_inner_delta C (β₂ := β₂) χ (a : ClassFunction ↥C.P.H0 ℂ)
    rw [l41iii_lamTwo_coe C (β₂ := β₂) a, l41iii_W,
      hmulB β₂ (a : ClassFunction ↥C.P.H0 ℂ) b hb]
    exact ⟨ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
        (lamCF C β₂ * (a : ClassFunction ↥C.P.H0 ℂ)) * ((a : ClassFunction ↥C.P.H0 ℂ) b),
      (hcint a).mul hXint, by rw [hdelta_a]; ring⟩
  -- ## integrality of the middle summand
  have hWint : ∀ a : IrreducibleCharacter ↥C.P.H0, IsIntegral ℤ (l41iii_W (C := C) β₂ χ b a) := by
    intro a
    show IsIntegral ℤ (ClassFunction.inner χ (delta C β₂ (a : ClassFunction ↥C.P.H0 ℂ)) *
      ((a : ClassFunction ↥C.P.H0 ℂ) b))
    obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int (mem_ZIrr_of_isPmIrr hχ)
      (l41_delta_mem_ZIrr C (β₂ := β₂) a.2)
    rw [hm]
    exact (isIntegral_intCast m).mul (OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr
      (IsIrreducibleCharacter.mem_ZIrr a.2) b)
  -- ## Step 2: the `s`-pairing removes the terms outside `𝒮₄`
  have hrest : AlgIntModTwo (∑ a ∈ (l41iii_Sp C) \ (l41iii_S4 C),
      l41iii_W (C := C) β₂ χ b a) 0 := by
    have hmemT : ∀ a, a ∈ (l41iii_Sp C) \ (l41iii_S4 C) ↔
        a ∈ l41iii_Sp C ∧ a ∉ l41iii_S4 C := fun a => Finset.mem_sdiff
    have he_inj : Function.Injective (fun a : IrreducibleCharacter ↥C.P.H0 =>
        ((Fintype.equivFin _) a : ℕ)) :=
      fun a b hab => (Fintype.equivFin _).injective (Fin.ext hab)
    have hmem_sj : ∀ a ∈ (l41iii_Sp C) \ (l41iii_S4 C),
        sj a ∈ (l41iii_Sp C) \ (l41iii_S4 C) := by
      intro a ha
      exact (hmemT (sj a)).mpr ⟨(hsj_Sp a).mpr ((hmemT a).mp ha).1,
        fun hc => (hmemT a).mp ha |>.2 ((hsj_S4 a).mp hc)⟩
    have hfW : ∀ a ∈ (l41iii_Sp C) \ (l41iii_S4 C),
        l41iii_W (C := C) β₂ χ b (sj a) = l41iii_W (C := C) β₂ χ b a := by
      intro a _
      show ClassFunction.inner χ (delta C β₂ ((sj a : IrreducibleCharacter ↥C.P.H0) :
            ClassFunction ↥C.P.H0 ℂ)) *
          (((sj a : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ) b)
        = ClassFunction.inner χ (delta C β₂ (a : ClassFunction ↥C.P.H0 ℂ)) *
          ((a : ClassFunction ↥C.P.H0 ℂ) b)
      rw [hsj_coe a, l41iii_delta_sconj C h2 hβ₂ (a : ClassFunction ↥C.P.H0 ℂ)]
      congr 1
      exact hconjB (a : ClassFunction ↥C.P.H0 ℂ) b hb
    have hp_flip : ∀ a ∈ (l41iii_Sp C) \ (l41iii_S4 C),
        (sj a ∈ (l41iii_Sp C) \ (l41iii_S4 C) ∧ ((Fintype.equivFin _) (sj a) : ℕ) <
            ((Fintype.equivFin _) (sj (sj a)) : ℕ)) ↔
          ¬ (a ∈ (l41iii_Sp C) \ (l41iii_S4 C) ∧
            ((Fintype.equivFin _) a : ℕ) < ((Fintype.equivFin _) (sj a) : ℕ)) := by
      intro a ha
      have hmem' := hmem_sj a ha
      have hne : ((Fintype.equivFin _) a : ℕ) ≠ ((Fintype.equivFin _) (sj a) : ℕ) :=
        fun heq => hsj_ne a ha (he_inj heq.symm)
      rw [hsj_invol a]
      constructor
      · rintro ⟨-, hlt⟩
        exact fun h => absurd h.2 (not_lt.mpr (le_of_lt hlt))
      · intro h
        refine ⟨hmem', ?_⟩
        have hle : ((Fintype.equivFin _) (sj a) : ℕ) ≤ ((Fintype.equivFin _) a : ℕ) :=
          le_of_not_gt fun hlt => h ⟨ha, hlt⟩
        exact lt_of_le_of_ne hle (Ne.symm hne)
    exact l41iiiInvAlg ((l41iii_Sp C) \ (l41iii_S4 C)) sj
      (fun a => l41iii_W (C := C) β₂ χ b a)
      (fun a => a ∈ (l41iii_Sp C) \ (l41iii_S4 C) ∧
        ((Fintype.equivFin _) a : ℕ) < ((Fintype.equivFin _) (sj a) : ℕ))
      hmem_sj (fun a _ => hsj_invol a) hp_flip hfW (fun a _ => hWint a)
  -- ## Step 2': splitting off `𝒮₄`
  have hstep2a : AlgIntModTwo (∑ a ∈ l41iii_Sp C, l41iii_W (C := C) β₂ χ b a)
      (∑ a ∈ l41iii_S4 C, l41iii_W (C := C) β₂ χ b a) := by
    have hsub : l41iii_S4 C ⊆ l41iii_Sp C := fun a ha =>
      (l41iii_Sp_mem C a).mpr ((l41iii_S4_mem C a).mp ha).1
    have hS4int : IsIntegral ℤ (∑ a ∈ l41iii_S4 C, l41iii_W (C := C) β₂ χ b a) :=
      IsIntegral.sum _ fun a _ => hWint a
    have hsplit : (∑ a ∈ l41iii_Sp C, l41iii_W (C := C) β₂ χ b a) =
        (∑ a ∈ (l41iii_Sp C) \ (l41iii_S4 C), l41iii_W (C := C) β₂ χ b a) +
          (∑ a ∈ l41iii_S4 C, l41iii_W (C := C) β₂ χ b a) :=
      (Finset.sum_sdiff hsub).symm
    rw [hsplit]
    rw [add_comm]
    refine (AlgIntModTwo.add (AlgIntModTwo.refl _ hS4int) hrest).trans ?_
    exact ⟨0, isIntegral_zero, by ring⟩
  -- ## Step 3: `deltaShape` turns the coefficient into an indicator
  have hstep2b : AlgIntModTwo (∑ a ∈ l41iii_S4 C, l41iii_W (C := C) β₂ χ b a)
      (∑ a ∈ l41iii_bsetFin C β₂ χ, (a : ClassFunction ↥C.P.H0 ℂ) b) := by
    have hS4sub : ∀ a, a ∈ l41iii_S4 C → (a : ClassFunction ↥C.P.H0 ℂ) ∈ S4Index C := by
      intro a ha
      obtain ⟨hsign, hconj⟩ := (l41iii_S4_mem C a).mp ha
      exact ⟨a.2, hconj, hsign⟩
    have hterm : ∀ a ∈ l41iii_S4 C, AlgIntModTwo (l41iii_W (C := C) β₂ χ b a)
        (if (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ then
          (a : ClassFunction ↥C.P.H0 ℂ) b else 0) := by
      intro a ha
      obtain ⟨m, hm, hEq⟩ := l41iiiDelta D C hc hn hβ₂ hχ (hS4sub a ha)
      have hXint : IsIntegral ℤ ((a : ClassFunction ↥C.P.H0 ℂ) b) :=
        OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr (IsIrreducibleCharacter.mem_ZIrr a.2) b
      have hind : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ ↔ (m : ℂ) ≠ 0 := by
        rw [bset']
        constructor
        · rintro ⟨-, hne⟩
          rw [hEq] at hne
          exact hne
        · intro hne
          exact ⟨hS4sub a ha, by rw [hEq]; exact hne⟩
      rw [l41iii_W, hEq]
      by_cases h0 : m = 0
      · have hnot : ¬ ((a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ) := by
          rw [hind, h0, Int.cast_zero]
          exact not_not_intro rfl
        rw [if_neg hnot, h0, Int.cast_zero, zero_mul]
        exact ⟨0, isIntegral_zero, by ring⟩
      · have hmem : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ := by
          rw [hind]
          exact fun h => h0 (by exact_mod_cast h)
        rw [if_pos hmem]
        rcases hm with h | h | h
        · exact absurd h h0
        · rw [h, Int.cast_one, one_mul]
          exact ⟨0, isIntegral_zero, by ring⟩
        · rw [h, Int.cast_neg, Int.cast_one]
          exact ⟨-((a : ClassFunction ↥C.P.H0 ℂ) b), hXint.neg, by ring⟩
    have hsum := AlgIntModTwo.sum (l41iii_S4 C) hterm
    have hext : (∑ a ∈ l41iii_S4 C, (if (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ then
          (a : ClassFunction ↥C.P.H0 ℂ) b else 0))
        = ∑ a : IrreducibleCharacter ↥C.P.H0,
            (if (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ then
              (a : ClassFunction ↥C.P.H0 ℂ) b else 0) := by
      refine Finset.sum_subset (fun a _ => Finset.mem_univ a) ?_
      intro a _ ha
      by_cases hmem : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ
      · exact absurd ((l41iii_S4_mem C a).mpr ⟨hmem.1.2.2, hmem.1.2.1⟩) ha
      · rw [if_neg hmem]
    have hconv : (∑ a : IrreducibleCharacter ↥C.P.H0,
            (if (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ then
              (a : ClassFunction ↥C.P.H0 ℂ) b else 0))
        = ∑ a ∈ l41iii_bsetFin C β₂ χ, (a : ClassFunction ↥C.P.H0 ℂ) b := by
      rw [l41iii_bsetFin, Finset.sum_filter]
    rw [hext, hconv] at hsum
    exact hsum
  rw [hexp b]
  exact (hstep1.trans hstep2a).trans hstep2b

end Mid




end Work.BG

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
/-- **Bender–Glauberman 1981, Lemma 4.1 (iii)** (p. 212): for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`
and every family of "hats" `ν ↦ ν̂` (`ν̂ ∈ Irr(B)` congruent to `ν` modulo `2` on `B`),
`χ ≡ Σ_{ν ∈ 𝒮'(χ)} ν̂ (mod 2)` on `B`. -/
theorem l41iii {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.L41iiiProp' D C := by
  classical
  intro hc hn β₂ hβ₂ χ hχ _hne
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have hinj : Function.Injective (fun a : IrreducibleCharacter ↥C.P.H0 =>
      (a : ClassFunction ↥C.P.H0 ℂ)) := fun a c h => Subtype.ext h
  have hrange : bset' C β₂ χ ⊆ Set.range (fun a : IrreducibleCharacter ↥C.P.H0 =>
      (a : ClassFunction ↥C.P.H0 ℂ)) := fun ν hν => ⟨⟨ν, hν.1.1⟩, rfl⟩
  have hfin : (bset' C β₂ χ).Finite := Set.Finite.subset (Set.finite_range _) hrange
  refine ⟨hfin, ?_⟩
  intro θ hθ b
  -- `b` viewed as an element of `H₀`
  have hbH0 : (b : G) ∈ C.P.H0 := by
    rw [hc.H0_eq, Work.BG.H1]
    exact Subgroup.mem_sup_left (mem_DU_of_mem_B D b.2)
  let bH : ↥C.P.H0 := ⟨(b : G), hbH0⟩
  have hb_eq : (⟨bH, b.2⟩ : ↥D.B) = b := Subtype.ext rfl
  -- the `finsum` over `𝒮'(χ)` as a sum over the finite type `Irr(H₀)`
  have hconv := l41iiiFinsum (fun a : IrreducibleCharacter ↥C.P.H0 =>
      (a : ClassFunction ↥C.P.H0 ℂ)) hinj (bset' C β₂ χ) hrange (fun ν => θ ν b)
  refine (l41iii_mid D C hc hn hβ₂ hχ bH b.2).trans ?_
  rw [hconv]
  refine AlgIntModTwo.sum _ fun a ha => ?_
  have ha' : (a : ClassFunction ↥C.P.H0 ℂ) ∈ bset' C β₂ χ := (l41iii_bsetFin_mem C a).mp ha
  have h1 := (hθ (a : ClassFunction ↥C.P.H0 ℂ) ha').2 bH b.2
  rwa [hb_eq] at h1

end Work.BG
