import Mathlib
import Submission.Work.Higman.RedAux.subgroup_transfer
import Submission.Work.Higman.RedAux.crux_helpers
import Submission.Work.Higman.reducible_aux
import Submission.Work.Higman.MSA.centralizer_eq_self
import Submission.Work.Higman.H8.c4_sq_a2_card_quot
import Submission.Work.Higman.HS.case_deriv_sq_A2_false
import Submission.Work.Higman.Q3.crux_case_large_hard
import Submission.Work.Higman.RedAux.setup
import Submission.Work.Higman.RedAux.two_cover_algebraic_core
import Submission.Work.Higman.H8.c4_irred_module_iso

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement IsMulCommutative

namespace Work.Higman.RedAux

/-!
# The two-cover endgame: the `ξ`-action on `D / A`

This is the shared "stage" of the two-cover endgame: the automorphism `ξ` of a Suzuki 2-group
`P`, restricted to a `ξ`-invariant subgroup `D` and descended to the quotient `D / A`.

Everything here is proved and axiom-clean; the companion module
`Submission.Work.Higman.RedAux.two_cover_endgame` uses these definitions for the actual
endgame.
-/

variable {P : Type} [Group P] [Finite P]

/-- `ξ` as an automorphism of a `ξ`-invariant subgroup. -/
noncomputable def xiSub (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) : ↥D ≃* ↥D where
  toFun d := ⟨(h.xi : MulAut P) (d : P), by
    have := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) d.2
    rwa [hDinv] at this⟩
  invFun d := ⟨(h.xi : MulAut P).symm (d : P),
    Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hDinv d.2⟩
  left_inv d := Subtype.ext (by simp)
  right_inv d := Subtype.ext (by simp)
  map_mul' d e := Subtype.ext (by simp [map_mul])

theorem xiSub_coe (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    ((xiSub h hDinv d : ↥D) : P) = (h.xi : MulAut P) (d : P) := rfl

theorem xiSub_symm_coe (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    (((xiSub h hDinv)⁻¹ d : ↥D) : P) = (h.xi : MulAut P).symm (d : P) := rfl

@[simp] theorem xiSub_apply_symm (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    xiSub h hDinv ((xiSub h hDinv)⁻¹ d) = d := by simp

@[simp] theorem xiSub_symm_apply (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    (xiSub h hDinv)⁻¹ (xiSub h hDinv d) = d := by simp

/-- The underlying group homomorphism of `ξ` acting on `D / A`. -/
noncomputable def xiQuotHom (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    (↥D ⧸ (A.subgroupOf D)) →* (↥D ⧸ (A.subgroupOf D)) :=
  letI : (A.subgroupOf D).Normal := hAn.subgroupOf D
  QuotientGroup.lift (A.subgroupOf D)
    ((QuotientGroup.mk' (A.subgroupOf D)).comp (xiSub h hDinv))
    (by
      intro d hd
      show QuotientGroup.mk (xiSub h hDinv d) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show (h.xi : MulAut P) ((d : ↥D) : P) ∈ A
      have hm := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom)
        (Subgroup.mem_subgroupOf.mp hd)
      rwa [hAinv] at hm)

theorem xiQuotHom_mk (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    xiQuotHom h hAinv hDinv (QuotientGroup.mk d) = QuotientGroup.mk (xiSub h hDinv d) := by
  rw [xiQuotHom, QuotientGroup.lift_mk]
  rfl

/-- `ξ` as an automorphism of the quotient `D / A`. -/
noncomputable def xiQuot (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    (↥D ⧸ (A.subgroupOf D)) ≃* (↥D ⧸ (A.subgroupOf D)) := by
  haveI : (A.subgroupOf D).Normal := hAn.subgroupOf D
  refine MulEquiv.ofBijective (xiQuotHom h hAinv hDinv) ⟨?_, ?_⟩
  · intro x y hxy
    induction x using QuotientGroup.induction_on with
    | _ x =>
      induction y using QuotientGroup.induction_on with
      | _ y =>
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h2 : xiQuotHom h hAinv hDinv (QuotientGroup.mk x)
            = xiQuotHom h hAinv hDinv (QuotientGroup.mk y) := hxy
        rw [xiQuotHom_mk, xiQuotHom_mk] at h2
        have h2' : (xiSub h hDinv x)⁻¹ * (xiSub h hDinv y) ∈ A.subgroupOf D :=
          QuotientGroup.eq.mp h2
        rw [Subgroup.mem_subgroupOf] at h2'
        have h4 : (xiSub h hDinv x)⁻¹ * (xiSub h hDinv y) = xiSub h hDinv (x⁻¹ * y) := by
          rw [map_mul, map_inv]
        rw [h4] at h2'
        have h3 : (h.xi : MulAut P) (((x⁻¹ * y : ↥D) : P)) ∈ A := h2'
        have h5 : ((x⁻¹ * y : ↥D) : P) ∈ A := by
          simpa using Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hAinv h3
        exact h5
  · intro z
    induction z using QuotientGroup.induction_on with
    | _ z =>
      refine ⟨QuotientGroup.mk ⟨(h.xi : MulAut P).symm (z : P),
        Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hDinv z.2⟩, ?_⟩
      rw [xiQuotHom_mk]
      show QuotientGroup.mk (xiSub h hDinv _) = QuotientGroup.mk z
      congr 1
      apply Subtype.ext
      show (h.xi : MulAut P) ((h.xi : MulAut P).symm (z : P)) = (z : P)
      simp

theorem xiQuot_mk (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    xiQuot h hAinv hDinv (QuotientGroup.mk d) = QuotientGroup.mk (xiSub h hDinv d) := by
  haveI : (A.subgroupOf D).Normal := hAn.subgroupOf D
  change xiQuotHom h hAinv hDinv (QuotientGroup.mk d) = _
  rw [xiQuotHom_mk]

/-- The inverse of `xiQuot` on representatives. -/
theorem xiQuot_symm_mk (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (d : ↥D) :
    (xiQuot h hAinv hDinv)⁻¹ (QuotientGroup.mk d) = QuotientGroup.mk ((xiSub h hDinv)⁻¹ d) := by
  have h1 : xiQuot h hAinv hDinv
      (QuotientGroup.mk ((xiSub h hDinv)⁻¹ d)) = QuotientGroup.mk d := by
    rw [xiQuot_mk]
    congr 1
    exact MulEquiv.apply_symm_apply _ _
  exact (Equiv.symm_apply_eq _).mpr h1.symm

/-- `ξ` as an automorphism of `A ^ (2)`. -/
noncomputable def xiPow (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) : ↥(Work.Higman.powSub A 2) ≃* ↥(Work.Higman.powSub A 2) :=
  xiSub h (Work.Higman.map_powSub (h.xi : MulAut P) hAinv 2)

theorem xiPow_coe (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (z : ↥(Work.Higman.powSub A 2)) :
    ((xiPow h hAinv z : ↥(Work.Higman.powSub A 2)) : P) = (h.xi : MulAut P) (z : P) := rfl

variable {P : Type} [Group P] [Finite P]

section EZ

variable {A : Subgroup P} (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
variable {F : Type} [Field F] (ζ : F ≃ ↥(Work.Higman.omega1 P))

/-- The element of `Ω₁(P)` underlying an element of `A ^ (2)`. -/
noncomputable def tceZel (z : ↥(Work.Higman.powSub A 2)) : ↥(Work.Higman.omega1 P) :=
  ⟨(z : P), htop ▸ z.2⟩

theorem tceZel_coe (z : ↥(Work.Higman.powSub A 2)) :
    ((tceZel htop z : ↥(Work.Higman.omega1 P)) : P) = (z : P) := rfl

/-- `eZ : A ^ (2) → F`, the inverse of `ζ` transported along `A ^ (2) = Ω₁(P)`. -/
noncomputable def tceEZ : ↥(Work.Higman.powSub A 2) ≃ F where
  toFun z := ζ.symm (tceZel htop z)
  invFun x := ⟨(ζ x : P), htop.symm ▸ (ζ x).2⟩
  left_inv z := by
    apply Subtype.ext
    show ((ζ (ζ.symm (tceZel htop z)) : ↥(Work.Higman.omega1 P)) : P) = (z : P)
    rw [ζ.apply_symm_apply]
    rfl
  right_inv x := by
    show ζ.symm (tceZel htop ⟨(ζ x : P), htop.symm ▸ (ζ x).2⟩) = x
    rw [show tceZel htop (⟨(ζ x : P), htop.symm ▸ (ζ x).2⟩ : ↥(Work.Higman.powSub A 2)) = ζ x
      from Subtype.ext rfl]
    exact ζ.symm_apply_apply x

theorem tceEZ_apply (z : ↥(Work.Higman.powSub A 2)) :
    tceEZ htop ζ z = ζ.symm (tceZel htop z) := rfl

theorem tceEZ_symm_apply (x : F) :
    (tceEZ htop ζ).symm x = ⟨(ζ x : P), htop.symm ▸ (ζ x).2⟩ := rfl

theorem tceEZ_add (hζadd : ∀ x y : F, ζ (x + y) = ζ x * ζ y)
    (z w : ↥(Work.Higman.powSub A 2)) : tceEZ htop ζ (z * w) = tceEZ htop ζ z + tceEZ htop ζ w := by
  rw [tceEZ_apply, tceEZ_apply, tceEZ_apply]
  have h : tceZel htop (z * w) = tceZel htop z * tceZel htop w := Subtype.ext rfl
  rw [h]
  have key : tceZel htop z * tceZel htop w
      = ζ (ζ.symm (tceZel htop z) + ζ.symm (tceZel htop w)) := by
    rw [hζadd, ζ.apply_symm_apply, ζ.apply_symm_apply]
  rw [key, ζ.symm_apply_apply]

theorem tceEZ_twist (h : Work.Higman.IsSuzuki2Grp P) {hAinv : A.map (h.xi : MulAut P).toMonoidHom = A}
    {mu : F} (hζξ : ∀ x : F, ((ζ (mu * x) : ↥(Work.Higman.omega1 P)) : P)
      = (h.xi : MulAut P) ((ζ x : ↥(Work.Higman.omega1 P)) : P))
    (z : ↥(Work.Higman.powSub A 2)) :
    tceEZ htop ζ (xiPow h hAinv z) = mu * tceEZ htop ζ z := by
  rw [tceEZ_apply, tceEZ_apply]
  have h : tceZel htop (xiPow h hAinv z)
      = xiSub h (Work.Higman.map_xi_omega1 h) (tceZel htop z) := Subtype.ext rfl
  rw [h]
  apply ζ.injective
  rw [ζ.apply_symm_apply]
  apply Subtype.ext
  rw [hζξ, ζ.apply_symm_apply]
  rfl

end EZ

/-! ## Irreducibility -/

theorem xiQuot_irreducible {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hGs : Bracket.bracket (⊤ : Subgroup P) (⊤ : Subgroup P) = A)
    (hAD : A ≤ D)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D) :
    ∀ W : Subgroup (↥D ⧸ (A.subgroupOf D)),
      (∀ v ∈ W, xiQuot h hAinv hDinv v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  haveI : (A.subgroupOf D).Normal := hAn.subgroupOf D
  let E : Subgroup P := (W.comap (QuotientGroup.mk' (A.subgroupOf D))).map (Subgroup.subtype D)
  have hmkW : ∀ x : ↥D, (x : P) ∈ E ↔ QuotientGroup.mk x ∈ W := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hAE : A ≤ E := by
    intro a ha
    rw [show a = ((⟨a, hAD ha⟩ : ↥D) : P) from rfl, hmkW]
    rw [show QuotientGroup.mk (⟨a, hAD ha⟩ : ↥D) = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)]
    exact W.one_mem
  have hED : E ≤ D := by
    rintro y ⟨x, -, rfl⟩
    exact x.2
  have hEn : E.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
    show g * (y : P) * g⁻¹ ∈ E
    have h1 : ⁅g, (y : P)⁆ ∈ A := by
      have hh := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top (y : P))
      rwa [hGs] at hh
    have h2 : ⁅g, (y : P)⁆ ∈ E := hAE h1
    have h3 : g * (y : P) * g⁻¹ = ⁅g, (y : P)⁆ * (y : P) := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact E.mul_mem h2 (Subgroup.mem_map_of_mem (Subgroup.subtype D) hy)
  have hEinv : E.map (h.xi : MulAut P).toMonoidHom = E := by
    have hstep : ∀ x : ↥D, (x : P) ∈ E → ((xiSub h hDinv x : ↥D) : P) ∈ E := by
      intro x hx
      rw [hmkW] at hx ⊢
      rw [← xiQuot_mk h hAinv hDinv x]
      exact hW _ hx
    have hle : E.map (h.xi : MulAut P).toMonoidHom ≤ E := by
      rintro y ⟨e, he, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
      exact hstep x ((hmkW x).mpr hx)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (h.xi : MulAut P).toMonoidHom)
      (h.xi : MulAut P).injective]
  rcases hcover E hEn hEinv hAE hED with hEA | hED'
  · left
    ext v
    constructor
    · intro hv
      rw [Subgroup.mem_bot]
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      have hxE : (x : P) ∈ E := (hmkW x).mpr hv
      rw [hEA] at hxE
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxE)
    · intro hv
      rw [Subgroup.mem_bot] at hv
      rw [hv]
      exact W.one_mem
  · right
    ext v
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      exact (hmkW x).mp (le_of_eq hED'.symm x.2)

/-! ## The scalar identification of `D / A` -/

theorem xiQuot_scalar_iso {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} [hAn : A.Normal] [hDn : D.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hcomm : Bracket.bracket D D ≤ A)
    {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hDcard : Nat.card (↥D ⧸ (A.subgroupOf D)) = 2 ^ n)
    (hexp2 : ∀ v : ↥D ⧸ (A.subgroupOf D), v * v = 1)
    (hirr : ∀ W : Subgroup (↥D ⧸ (A.subgroupOf D)),
      (∀ v ∈ W, xiQuot h hAinv hDinv v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (sig : F) (e : (↥D ⧸ (A.subgroupOf D)) ≃ F),
      sig ≠ 1 ∧ (∀ k : ℕ, 1 ≤ k → k < n → sig ^ (2 ^ k) ≠ sig) ∧
      (∀ v w : ↥D ⧸ (A.subgroupOf D), e (v * w) = e v + e w) ∧
      (∀ v : ↥D ⧸ (A.subgroupOf D), e (xiQuot h hAinv hDinv v) = sig * e v) := by
  classical
  haveI hQ : IsMulCommutative (↥D ⧸ (A.subgroupOf D)) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    show ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ ≤ A.subgroupOf D
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact Subgroup.mem_subgroupOf.mpr (hcomm (Subgroup.commutator_mem_commutator x.2 y.2))
  let S := Additive (↥D ⧸ (A.subgroupOf D))
  haveI hSmod : Module (ZMod 2) S := AddCommGroup.zmodModule (n := 2) (fun (y : S) => by
    show (2 : ℕ) • y = 0
    induction y using Additive.rec with
    | _ a => rw [two_nsmul, ← ofMul_mul]; exact ofMul_eq_zero.mpr (hexp2 a))
  have hcardS : Nat.card S = 2 ^ n := by
    rw [← Nat.card_congr Additive.ofMul]; exact hDcard
  let ξS : S ≃+ S := (xiQuot h hAinv hDinv).toAdditive
  have hξS : ∀ v : ↥D ⧸ (A.subgroupOf D),
      ξS (Additive.ofMul v) = Additive.ofMul (xiQuot h hAinv hDinv v) := fun v => rfl
  let xS : S ≃ₗ[ZMod 2] S := AddEquiv.toLinearEquiv ξS (fun c y => by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with hc | hc <;> subst hc <;> simp)
  have hxS : ∀ y : S, xS y = ξS y := fun y => rfl
  have hirr' : ∀ U : Submodule (ZMod 2) S, (∀ y ∈ U, xS y ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let W : Subgroup (↥D ⧸ (A.subgroupOf D)) :=
      { carrier := {v | Additive.ofMul v ∈ U}
        one_mem' := by
          show Additive.ofMul (1 : ↥D ⧸ (A.subgroupOf D)) ∈ U
          rw [ofMul_one]
          exact U.zero_mem
        mul_mem' := fun {a b} ha hb => by
          show Additive.ofMul (a * b) ∈ U
          rw [ofMul_mul]
          exact U.add_mem ha hb
        inv_mem' := fun {a} ha => by
          show Additive.ofMul a⁻¹ ∈ U
          have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_left (hexp2 a)
          rw [h1]
          exact ha }
    have hstable : ∀ v ∈ W, xiQuot h hAinv hDinv v ∈ W := by
      intro v hv
      show Additive.ofMul (xiQuot h hAinv hDinv v) ∈ U
      rw [← hξS v, ← hxS (Additive.ofMul v)]
      exact hU _ hv
    rcases hirr W hstable with hW | hW
    · left
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hyW : y.toMul ∈ W := by
        show Additive.ofMul y.toMul ∈ U
        rwa [ofMul_toMul]
      rw [hW] at hyW
      have hy1 : y.toMul = 1 := Subgroup.mem_bot.mp hyW
      rw [← ofMul_toMul y, hy1, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro y
      have hyW : y.toMul ∈ W := by rw [hW]; exact Subgroup.mem_top _
      have hyU : Additive.ofMul y.toMul ∈ U := hyW
      rwa [ofMul_toMul] at hyU
  obtain ⟨sig, e0, hsig1, hpow, he0⟩ :=
    Work.Higman.H8.c4_irred_module_iso hn hcard hcardS xS hirr'
  refine ⟨sig, (Additive.ofMul).trans e0.toEquiv, hsig1, hpow, ?_, ?_⟩
  · intro v w
    show e0 (Additive.ofMul (v * w)) = e0 (Additive.ofMul v) + e0 (Additive.ofMul w)
    rw [ofMul_mul]
    exact e0.map_add _ _
  · intro v
    show e0 (Additive.ofMul (xiQuot h hAinv hDinv v)) = sig * e0 (Additive.ofMul v)
    have hh := he0 (Additive.ofMul v)
    rw [hxS, hξS] at hh
    exact hh

/-! ## Reduction lemmas (moved here from `two_cover_endgame`) -/

/-- In the `C₄` setting, `A ≤ Z(P)` is impossible: it would force `[P,P] ≤ Ω₁(P) = A²`. -/
theorem c4_A_not_le_center (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    ¬ A ≤ Subgroup.center P := by
  intro hAZ
  have hsq_center : ∀ x : P, x ^ 2 ∈ Subgroup.center P := fun x => hAZ (hsq x)
  have hle : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [h.mem_omega1]
    have h2 : ⁅x, y⁆ ∈ Subgroup.center P :=
      hAZ (by rw [← hGs]
              exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
    have h3 : ⁅x, ⁅x, y⁆⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp h2 x)
    have h1 : ⁅x ^ 2, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hsq_center x) y).symm
    have h4 : ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 = 1 := by
      rw [← Work.Higman.commutatorElement_sq_self x y]; exact h1
    rw [h3, one_mul] at h4
    exact h4
  have hAle : A ≤ Work.Higman.powSub A 2 := by
    calc A = ⁅(⊤ : Subgroup P), ⊤⁆ := hGs.symm
      _ ≤ Work.Higman.omega1 P := hle
      _ = Work.Higman.powSub A 2 := htop.symm
  have hAe : A = Work.Higman.powSub A 2 := le_antisymm hAle (Work.Higman.powSub_le (by norm_num))
  have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
    congrArg (fun X : Subgroup P => Nat.card ↥X) hAe
  rw [htop] at hc
  have hq : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    rw [← hcard, hc]
  have h4 := h.omega1_card_ge_four
  have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
  nlinarith [hq, h4, hpos]

/-- In the `C₄` setting, `A` is maximal among the `ξ`-invariant abelian normal subgroups. -/
theorem c4_maximal (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A :=
  Work.Higman.maximal_of_c4_data h hA hsq hA4 htop hcard

/-- In the `C₄` setting, `C_P(A) = A`. -/
theorem c4_centralizer (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    Subgroup.centralizer (A : Set P) = A :=
  Work.Higman.MSA.centralizer_eq_self h hA
    (c4_maximal h hA hsq hA4 htop hcard) hNA hGs hsq hA4 htop hcard
    (c4_A_not_le_center h hGs hsq htop hcard)

/-- **`⁅A,D⁆ = A²`** for a `ξ`-invariant normal `D ≥ A` with `⁅D,D⁆ = A²`, `A ≠ D` and
`C_P(A) = A`. -/
theorem c4_comm_A_D (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hA4 : Work.Higman.powSub A 4 = ⊥) (hAD : A ≤ D) (hADne : A ≠ D)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A) :
    ⁅A, D⁆ = Work.Higman.powSub A 2 := by
  have hle : ⁅A, D⁆ ≤ Work.Higman.powSub A 2 := by
    calc ⁅A, D⁆ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hAD le_rfl
      _ = Work.Higman.powSub A 2 := hDd
  have hinv : (⁅A, D⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅A, D⁆ := by
    rw [Subgroup.map_commutator, hA.map_eq, hDinv]
  rcases red_trichotomy h A ⁅A, D⁆ hA hA4
      (hle.trans (Work.Higman.powSub_le (by norm_num))) hinv with hb | hm | htop'
  · exfalso
    have h1 : (⁅D, A⁆ : Subgroup P) = ⊥ := by rw [Subgroup.commutator_comm]; exact hb
    have h2 : D ≤ Subgroup.centralizer (A : Set P) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    rw [hcent] at h2
    exact hADne (le_antisymm hAD h2)
  · exact hm
  · exfalso
    rw [htop'] at hle
    exact ne_powSub_two_of_card h htop hcard
      (le_antisymm hle (Work.Higman.powSub_le (by norm_num)))

/-- **`D ^ (2) = A ^ (2)`** for a `ξ`-invariant normal `D ≥ A` with `⁅D,D⁆ = A²`, `D ≠ A`. -/
theorem c4_D_sq (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hAD : A ≤ D) (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcent : Subgroup.centralizer (A : Set P) = A) (hADne : A ≠ D)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    Work.Higman.powSub D 2 = Work.Higman.powSub A 2 := by
  have hD2leA : Work.Higman.powSub D 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hCAd : ⁅A, D⁆ = Work.Higman.powSub A 2 :=
    c4_comm_A_D h hA hDinv hA4 hAD hADne hDd htop hcard hcent
  have hCAd' : ⁅D, A⁆ = Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_comm]; exact hCAd
  exact Work.Higman.HS.c4_C_sq_eq hA.abelian hA.map_eq htop hA4 hD2leA hDinv hDd hCAd'

/-- **`|D / A| = |Ω₁(P)|`** for a minimal `ξ`-invariant normal cover `D > A` with `⁅D,D⁆ = A²`. -/
theorem c4_card_quot (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : A ≠ D)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ F : Subgroup P, F.Normal → F.map (h.xi : MulAut P).toMonoidHom = F →
      A ≤ F → F ≤ D → F = A ∨ F = D) :
    Nat.card (↥D ⧸ (A.subgroupOf D)) = Nat.card ↥(Work.Higman.omega1 P) := by
  have hD2 : Work.Higman.powSub D 2 = Work.Higman.powSub A 2 :=
    c4_D_sq h hA hDinv htop hA4 hsq hAD hDd hcent hADne hcard
  have hAD2 : ⁅A, D⁆ = Work.Higman.powSub A 2 :=
    c4_comm_A_D h hA hDinv hA4 hAD hADne hDd htop hcard hcent
  refine Work.Higman.H8.c4_sq_a2_card_quot h hA hGs hNA htop hcent hDn hDinv hAD
    (fun hcon => hADne hcon.symm) hDd ?_ hcover hAD2
  rw [hD2, hDd, sup_idem]

/-- **The diagonal commutator relation.**  In any group, if `x ^ 2` is central and `⁅x,y⁆ ^ 4 = 1`
then `⁅x, ⁅x,y⁆⁆ = ⁅x,y⁆ ^ 2`.  (For `x` with `x ^ 2 ∈ Ω₁(P)` this is the relation
`Φ (β s t) s = β s t` of the two-cover endgame.) -/
theorem commutator_diag_eq {G : Type} [Group G] {x y : G}
    (hx2 : x ^ 2 ∈ Subgroup.center G) (h4 : ⁅x, y⁆ ^ 4 = 1) :
    ⁅x, ⁅x, y⁆⁆ = ⁅x, y⁆ ^ 2 := by
  have h1 : ⁅x ^ 2, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hx2 y).symm
  have h2 : ⁅x ^ 2, y⁆ = ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 :=
    Work.Higman.commutatorElement_sq_self x y
  rw [h2] at h1
  have hv : (⁅x, y⁆ ^ 2)⁻¹ = ⁅x, y⁆ ^ 2 := by
    have h5 : (⁅x, y⁆ ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * 2 = 4 from rfl, h4]
    exact inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using h5)
  have h3 : ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 = 1 := h1
  -- from `u * v = 1` and `v = v⁻¹` conclude `u = v`
  have h6 : ⁅x, ⁅x, y⁆⁆ = (⁅x, y⁆ ^ 2)⁻¹ := (inv_eq_of_mul_eq_one_left h3).symm
  rw [h6, hv]

end Work.Higman.RedAux
