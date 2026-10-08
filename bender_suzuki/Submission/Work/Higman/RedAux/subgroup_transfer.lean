import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open scoped commutatorElement

namespace Work.Higman.RedAux

variable {P : Type} [Group P] [Finite P]

/-! ## Transport of the Suzuki structure to a `ξ`-invariant subgroup

A copy (so that nothing from the `sorry`-carrying module `NSM/redcase.lean` is imported) of the
transport lemmas `xiSub`, `xiSub_apply`, `xiSub_pow_apply` and `isSuzuki2Grp_subgroup`. -/

/-- The automorphism of `↥C` induced by `ξ`, when `C` is `ξ`-invariant. -/
noncomputable def xiSubRG (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) : MulAut ↥C where
  toFun x := ⟨h.xi x, by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hCinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm x, symm_mem_of_map_eq (h.xi : MulAut P) hCinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem xiSubRG_apply (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (x : ↥C) :
    ((xiSubRG h hCinv x : ↥C) : P) = h.xi (x : P) := rfl

theorem xiSubRG_pow_apply (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (k : ℕ) (x : ↥C) :
    (((xiSubRG h hCinv : MulAut ↥C) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply]
      show h.xi ((((xiSubRG h hCinv : MulAut ↥C) ^ k) x : ↥C) : P) = _
      rw [ih, pow_succ', MulAut.mul_apply]

/-- **A `ξ`-invariant subgroup containing `Ω₁(P)` and two non-commuting elements is again a
Suzuki 2-group** (with the restricted automorphism). -/
noncomputable def isSuzuki2Grp_subgroupRG (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (hOm : omega1 P ≤ C)
    (hni : ∃ x y : ↥C, x * y ≠ y * x) : IsSuzuki2Grp ↥C where
  isPGroup := h.isPGroup.to_subgroup C
  noncomm := hni
  manyInvol := by
    obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
    have hxC : x ∈ C := hOm (h.mem_omega1.mpr (by
      rw [← orderOf_dvd_iff_pow_eq_one, hx2]))
    have hyC : y ∈ C := hOm (h.mem_omega1.mpr (by
      rw [← orderOf_dvd_iff_pow_eq_one, hy2]))
    refine ⟨⟨x, hxC⟩, ⟨y, hyC⟩, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe, hx2]
    · rw [← Subgroup.orderOf_coe, hy2]
    · intro hcon
      exact hxy (congrArg Subtype.val hcon)
  xi := xiSubRG h hCinv
  trans := by
    intro x y hx2 hy2
    have hxP : orderOf (x : P) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
    have hyP : orderOf (y : P) = 2 := by rw [Subgroup.orderOf_coe]; exact hy2
    obtain ⟨k, hk⟩ := h.trans (x : P) (y : P) hxP hyP
    exact ⟨k, Subtype.ext (by rw [xiSubRG_pow_apply, hk])⟩

/-! ## Transfers of `Ω₁`, `powSub`, `card` and `ξ`-invariance -/

/-- **`Ω₁` transfers to a Suzuki subgroup.** -/
theorem omega1_subgroupOf (h : IsSuzuki2Grp P) {D : Subgroup P} (hD : IsSuzuki2Grp ↥D) :
    omega1 ↥D = (omega1 P).subgroupOf D := by
  ext x
  rw [hD.mem_omega1, Subgroup.mem_subgroupOf, h.mem_omega1]
  constructor
  · intro hx
    have h1 := congrArg (fun y : ↥D => (y : P)) hx
    simpa using h1
  · intro hx
    exact Subtype.ext (by simpa using hx)

/-- **`|↥(A.subgroupOf D)| = |↥A|`.** -/
theorem card_subgroupOf {A D : Subgroup P} (hAD : A ≤ D) :
    Nat.card ↥(A.subgroupOf D) = Nat.card ↥A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv

/-- **The restricted automorphism acts as `ξ` on an invariant subgroup.** -/
theorem map_xiSubRG_subgroupOf (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) {hAD : A ≤ D} :
    (A.subgroupOf D).map (xiSubRG h hDinv).toMonoidHom = A.subgroupOf D := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    show h.xi ((x : ↥D) : P) ∈ A
    have hm := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom)
      (Subgroup.mem_subgroupOf.mp hx)
    rwa [hAinv] at hm
  · intro y hy
    have hyA : (y : P) ∈ A := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_map.mpr ⟨⟨(h.xi : MulAut P).symm (y : P), ?_⟩, ?_, ?_⟩
    · exact hAD (symm_mem_of_map_eq (h.xi : MulAut P) hAinv hyA)
    · exact Subgroup.mem_subgroupOf.mpr (symm_mem_of_map_eq (h.xi : MulAut P) hAinv hyA)
    · exact Subtype.ext (by show h.xi ((h.xi : MulAut P).symm (y : P)) = (y : P); simp)

/-- **`powSub` transfers to subgroups** (`n ≥ 1`). -/
theorem powSub_subgroupOf {A D : Subgroup P} (hAD : A ≤ D) {n : ℕ} (hn : 0 < n) :
    powSub (A.subgroupOf D) n = (powSub A n).subgroupOf D := by
  have hA : powSub A n ≤ A := powSub_le hn
  refine le_antisymm ?_ ?_
  · intro w hw
    show ((w : ↥D) : P) ∈ powSub A n
    induction hw using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨b, hb, rfl⟩ := hz
        rw [Subgroup.coe_pow]
        exact pow_mem_powSub (Subgroup.mem_subgroupOf.mp hb)
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [Subgroup.coe_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
        rw [Subgroup.coe_inv]
        exact Subgroup.inv_mem _ ihx
  · intro w hw
    suffices key : ∀ u : P, u ∈ powSub A n → ∀ v : ↥D, (v : P) = u →
        v ∈ powSub (A.subgroupOf D) n from key (w : P) hw w rfl
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
        rintro v hv
        obtain ⟨a, ha, rfl⟩ := hx
        have hv' : v = (⟨a, hAD ha⟩ : ↥D) ^ n := Subtype.ext (by rw [hv]; rfl)
        rw [hv']
        exact Subgroup.subset_closure ⟨⟨a, hAD ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    | one =>
        rintro v hv
        have hv' : v = 1 := Subtype.ext (by rw [hv]; rfl)
        rw [hv']
        exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        rintro v hv
        have hxD : x ∈ D := hAD (hA hx)
        have hyD : y ∈ D := hAD (hA hy)
        have hv' : v = (⟨x, hxD⟩ : ↥D) * ⟨y, hyD⟩ := Subtype.ext (by rw [hv]; rfl)
        rw [hv']
        exact Subgroup.mul_mem _ (ihx _ rfl) (ihy _ rfl)
    | inv x hx ihx =>
        rintro v hv
        have hxD : x ∈ D := hAD (hA hx)
        have hv' : v = (⟨x, hxD⟩ : ↥D)⁻¹ := Subtype.ext (by rw [hv]; rfl)
        rw [hv']
        exact Subgroup.inv_mem _ (ihx _ rfl)

/-- **The commutator transfers to a subgroup:** if `⁅D,D⁆ = A ≤ D` then `⁅⊤,⊤⁆` computed in
`↥D` is `A.subgroupOf D`. -/
theorem commutator_top_subgroupOf {A D : Subgroup P} (hAD : A ≤ D) (hDA : ⁅D, D⁆ = A) :
    ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ = A.subgroupOf D := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x _ y _
    show ((⁅x, y⁆ : ↥D) : P) ∈ A
    have h2 : ((⁅x, y⁆ : ↥D) : P) = ⁅(x : P), (y : P)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      simp
    rw [h2]
    have h1 : ⁅(x : P), (y : P)⁆ ∈ ⁅D, D⁆ :=
      Subgroup.commutator_mem_commutator x.2 y.2
    rwa [hDA] at h1
  · intro z hz
    have hzA : (z : P) ∈ A := hz
    have hle : ⁅D, D⁆ ≤ (⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆).map D.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx' : (⟨x, hx⟩ : ↥D) ∈ (⊤ : Subgroup ↥D) := Subgroup.mem_top _
      have hy' : (⟨y, hy⟩ : ↥D) ∈ (⊤ : Subgroup ↥D) := Subgroup.mem_top _
      have h1 : ⁅(⟨x, hx⟩ : ↥D), ⟨y, hy⟩⁆ ∈ ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ :=
        Subgroup.commutator_mem_commutator hx' hy'
      have h2 : ((⁅(⟨x, hx⟩ : ↥D), ⟨y, hy⟩⁆ : ↥D) : P) = ⁅x, y⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp
      exact ⟨_, h1, h2⟩
    have h1 : (z : P) ∈ (⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆).map D.subtype :=
      hle (by rw [hDA]; exact hzA)
    obtain ⟨w, hw, hwz⟩ := h1
    have hwz' : w = z := Subtype.ext hwz
    rwa [hwz'] at hw

/-! ## Structural transfers: maximality of `A`, and `hcover` -/

/-- **Maximality of `A` transfers to a `ξ`-invariant normal subgroup `D ≥ A`.** -/
theorem hmax_subgroupOf (h : IsSuzuki2Grp P) {A D : Subgroup P} (hD : IsSuzuki2Grp ↥D)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hDxi : (hD.xi : MulAut ↥D) = xiSubRG h hDinv)
    (hDn : D.Normal) (hAD : A ≤ D)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    ∀ B : Subgroup ↥D, IsXiAbelNormal hD B → A.subgroupOf D ≤ B → B = A.subgroupOf D := by
  intro B hB hAB
  have hAB' : A ≤ B.map D.subtype := by
    intro a ha
    exact ⟨⟨a, hAD ha⟩, hAB (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hB'n : (B.map D.subtype).Normal := by
    refine Subgroup.Normal.mk fun b hb g => ?_
    have h1 : ⁅g, b⁆ ∈ A :=
      hGs (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top b))
    rw [show g * b * g⁻¹ = ⁅g, b⁆ * b from by rw [commutatorElement_def]; group]
    exact (B.map D.subtype).mul_mem (hAB' h1) hb
  have hB'xi : (B.map D.subtype).map (h.xi : MulAut P).toMonoidHom = B.map D.subtype := by
    have hBinv : B.map (xiSubRG h hDinv).toMonoidHom = B := by rw [← hDxi]; exact hB.2.1
    calc (B.map D.subtype).map (h.xi : MulAut P).toMonoidHom
        = B.map ((h.xi : MulAut P).toMonoidHom.comp D.subtype) := Subgroup.map_map B _ _
      _ = B.map (D.subtype.comp (xiSubRG h hDinv).toMonoidHom) := by
          rfl
      _ = (B.map (xiSubRG h hDinv).toMonoidHom).map D.subtype := (Subgroup.map_map B _ _).symm
      _ = B.map D.subtype := by rw [hBinv]
  have hB'ab : ∀ x ∈ B.map D.subtype, ∀ y ∈ B.map D.subtype, x * y = y * x := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
    exact congrArg Subtype.val (hB.2.2 x' hx' y' hy')
  have hB'eq : B.map D.subtype = A := hmax _ ⟨hB'n, hB'xi, hB'ab⟩ hAB'
  refine le_antisymm ?_ hAB
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  exact hB'eq ▸ ⟨y, hy, rfl⟩

/-- **`hcover` transfers to a `ξ`-invariant normal subgroup `D ≥ C ≥ A`.** -/
theorem hcover_subgroupOf (h : IsSuzuki2Grp P) {A C D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (hAD : A ≤ D) (hCD : C ≤ D)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C) :
    ∀ E : Subgroup ↥D, E.Normal → E.map (xiSubRG h hDinv).toMonoidHom = E →
      A.subgroupOf D ≤ E → E ≤ C.subgroupOf D →
        E = A.subgroupOf D ∨ E = C.subgroupOf D := by
  intro E hEn hExi hAE hEC
  have hAE' : A ≤ E.map D.subtype := by
    intro a ha
    exact ⟨⟨a, hAD ha⟩, hAE (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hEC' : E.map D.subtype ≤ C := by
    rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hEC hy)
  have hE'n : (E.map D.subtype).Normal := by
    refine Subgroup.Normal.mk fun b hb g => ?_
    have h1 : ⁅g, b⁆ ∈ A :=
      hGs (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top b))
    rw [show g * b * g⁻¹ = ⁅g, b⁆ * b from by rw [commutatorElement_def]; group]
    exact (E.map D.subtype).mul_mem (hAE' h1) hb
  have hE'xi : (E.map D.subtype).map (h.xi : MulAut P).toMonoidHom = E.map D.subtype := by
    have hEinv : E.map (xiSubRG h hDinv).toMonoidHom = E := hExi
    calc (E.map D.subtype).map (h.xi : MulAut P).toMonoidHom
        = E.map ((h.xi : MulAut P).toMonoidHom.comp D.subtype) := Subgroup.map_map E _ _
      _ = E.map (D.subtype.comp (xiSubRG h hDinv).toMonoidHom) := by
          rfl
      _ = (E.map (xiSubRG h hDinv).toMonoidHom).map D.subtype := (Subgroup.map_map E _ _).symm
      _ = E.map D.subtype := by rw [hEinv]
  rcases hcover (E.map D.subtype) hE'n hE'xi hAE' hEC' with h1 | h1
  · left
    refine le_antisymm ?_ hAE
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact h1 ▸ ⟨y, hy, rfl⟩
  · right
    refine le_antisymm hEC ?_
    intro y hy
    have h2 : (y : P) ∈ E.map D.subtype := by
      rw [h1]; exact Subgroup.mem_subgroupOf.mp hy
    obtain ⟨w, hw, hwy⟩ := h2
    have hwy' : w = y := Subtype.ext hwy
    rwa [hwy'] at hw

/-- **Commutators transfer to subgroups:** for `C ≤ D`, `⁅C,C⁆` computed in `↥D` is the
corresponding subgroup of `⁅C,C⁆`. -/
theorem commutator_subgroupOf (C D : Subgroup P) (hCD : C ≤ D) :
    ⁅C.subgroupOf D, C.subgroupOf D⁆ = (⁅C, C⁆).subgroupOf D := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    have h2 : ((⁅x, y⁆ : ↥D) : P) = ⁅((x : ↥D) : P), ((y : ↥D) : P)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      simp
    rw [h2]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy)
  · intro z hz
    have hzA : (z : P) ∈ ⁅C, C⁆ := Subgroup.mem_subgroupOf.mp hz
    have hle : ⁅C, C⁆ ≤ (⁅C.subgroupOf D, C.subgroupOf D⁆).map D.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx' : (⟨x, hCD hx⟩ : ↥D) ∈ C.subgroupOf D := Subgroup.mem_subgroupOf.mpr hx
      have hy' : (⟨y, hCD hy⟩ : ↥D) ∈ C.subgroupOf D := Subgroup.mem_subgroupOf.mpr hy
      have h1 : ⁅(⟨x, hCD hx⟩ : ↥D), ⟨y, hCD hy⟩⁆ ∈ ⁅C.subgroupOf D, C.subgroupOf D⁆ :=
        Subgroup.commutator_mem_commutator hx' hy'
      have h2 : ((⁅(⟨x, hCD hx⟩ : ↥D), ⟨y, hCD hy⟩⁆ : ↥D) : P) = ⁅x, y⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp
      exact ⟨_, h1, h2⟩
    have h3 : (z : P) ∈ (⁅C.subgroupOf D, C.subgroupOf D⁆).map D.subtype := hle hzA
    obtain ⟨w, hw, hwz⟩ := h3
    have hwz' : w = z := Subtype.ext hwz
    rwa [hwz'] at hw

end Work.Higman.RedAux
