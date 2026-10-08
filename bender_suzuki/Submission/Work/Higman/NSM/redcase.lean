import Mathlib
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.l8_defs
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.NSM.irreducible
import Submission.Work.Higman.no_square_derived
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.higman_lemma7
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.nsd_powSub_top_eq
import Submission.Work.Higman.C4Cover.c4_cover_card_eq_cube
import Submission.Work.Higman.NSM.c4sqAMaximal
import Submission.Work.Higman.NSM.c4gapCentralises

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.Higman.NSM

open Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## The `C₄` setting: auxiliary facts -/

/-- If `A` contains the commutator subgroup then `P ⧸ A` is abelian. -/
theorem quot_mul_comm {A : Subgroup P} [A.Normal]
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A) (a b : P ⧸ A) : a * b = b * a := by
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have key : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  rw [key]
  exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top y⁻¹) (Subgroup.mem_top x⁻¹))

/-- In the `C₄` setting `⁅A, ⊤⁆ = A ^ (2) = Ω₁(P)`. -/
theorem commA_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (htop : powSub A 2 = omega1 P) :
    ⁅A, (⊤ : Subgroup P)⁆ = powSub A 2 := by
  rcases nsd_comm_eq_bot_or_omega1 h hAxi hAab hGs htop with hb | hT
  · exact absurd hb (nsd_comm_eq_bot_false h hAab hNA hGs hsq htop)
  · rw [hT, ← htop]

/-- A `ξ`-invariant normal subgroup of `A` in the `C₄` setting is `⊥`, `A ^ (2)` or `A`. -/
theorem trich (h : IsSuzuki2Grp P) {A S : Subgroup P}
    (hA : IsXiAbelNormal h A) (hA4 : powSub A 4 = ⊥)
    (hSA : S ≤ A) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S) :
    S = ⊥ ∨ S = powSub A 2 ∨ S = A := by
  obtain ⟨e, -, -, -, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  obtain ⟨i, hi⟩ := hsub S hSA hSinv
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inr (Or.inr (by rw [hi, h0, pow_zero, powSub_one_eq]))
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · exact Or.inr (Or.inl (by rw [hi, show i = 1 by omega]; norm_num))
  · exact Or.inl (by
      rw [hi]
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
      exact le_bot_iff.mp (hA4 ▸ powSub_le_of_dvd hA.abelian hdvd))

/-- For any `z` with `z ^ 2` central and any `d`: `⁅z, ⁅d, z⁆⁆ = ⁅d, z⁆ ^ (-2)`, i.e. `z` inverts
the commutator `⁅d, z⁆`.  Obtained from `⁅d, z * z⁆ = ⁅d, z⁆ * (z * ⁅d, z⁆ * z⁻¹)` (which is `1`
because `z * z` is central) and `z * u * z⁻¹ = ⁅z, u⁆ * u`. -/
theorem commutator_self_inv_sq {G : Type} [Group G] {z d : G}
    (hz : z ^ 2 ∈ Subgroup.center G) : ⁅z, ⁅d, z⁆⁆ = (⁅d, z⁆ * ⁅d, z⁆)⁻¹ := by
  have hc : z * z ∈ Subgroup.center G := by simpa [pow_two] using hz
  have h1 : ⁅d, z * z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hc d)
  have h2 : ⁅d, z * z⁆ = ⁅d, z⁆ * (z * ⁅d, z⁆ * z⁻¹) := by
    simp only [commutatorElement_def]; group
  have h3 : z * ⁅d, z⁆ * z⁻¹ = ⁅z, ⁅d, z⁆⁆ * ⁅d, z⁆ := by
    simp only [commutatorElement_def]; group
  have h4 : ⁅d, z⁆ * (⁅z, ⁅d, z⁆⁆ * ⁅d, z⁆) = 1 := by
    have hp : ⁅d, z⁆ * (z * ⁅d, z⁆ * z⁻¹) = 1 := h2.symm.trans h1
    rwa [h3] at hp
  have h5 : (⁅d, z⁆ * ⁅z, ⁅d, z⁆⁆) * ⁅d, z⁆ = 1 := by
    rw [mul_assoc]; exact h4
  have key : ⁅d, z⁆ * ⁅z, ⁅d, z⁆⁆ = (⁅d, z⁆)⁻¹ := mul_eq_one_iff_eq_inv.mp h5
  have h6 : ⁅z, ⁅d, z⁆⁆ = (⁅d, z⁆)⁻¹ * (⁅d, z⁆)⁻¹ := by
    calc ⁅z, ⁅d, z⁆⁆ = (⁅d, z⁆)⁻¹ * (⁅d, z⁆ * ⁅z, ⁅d, z⁆⁆) := by group
      _ = (⁅d, z⁆)⁻¹ * (⁅d, z⁆)⁻¹ := by rw [key]
  calc ⁅z, ⁅d, z⁆⁆ = (⁅d, z⁆)⁻¹ * (⁅d, z⁆)⁻¹ := h6
    _ = (⁅d, z⁆ * ⁅d, z⁆)⁻¹ := (mul_inv_rev _ _).symm

/-- **The `P/A`-normality of intermediate subgroups.**  In the `C₄` setting (`P/A` abelian),
every subgroup between `A` and a normal `C ≥ A` is normal in `P`.  Consequently the minimality
hypothesis about *normal* subgroups between `A` and `C` controls *all* `ξ`-invariant subgroups
there; this is what makes the reducible case accessible. -/
theorem normal_of_le_of_le {A C D : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hCn : C.Normal) (hAD : A ≤ D) (hDC : D ≤ C) : D.Normal := by
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  have hcommA : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A := le_of_eq hGs
  refine ⟨fun y hy g => ?_⟩
  have hyC : y ∈ C := hDC hy
  have hgyC : g * y * g⁻¹ ∈ C := hCn.conj_mem y hyC g
  -- the two elements have the same image in the abelian quotient `P ⧸ A`
  have hcos : ((g * y * g⁻¹ : P) : P ⧸ A) = ((y : P) : P ⧸ A) := by
    have h1 : ((g * y * g⁻¹ : P) : P ⧸ A)
        = (g : P ⧸ A) * (y : P ⧸ A) * (g : P ⧸ A)⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, quot_mul_comm hcommA g y, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : y⁻¹ * (g * y * g⁻¹) ∈ A := by
    rw [← QuotientGroup.eq, hcos]
  have h1 : y⁻¹ * (g * y * g⁻¹) ∈ D := hAD hmem
  have h2 : g * y * g⁻¹ = y * (y⁻¹ * (g * y * g⁻¹)) := by group
  rw [h2]
  exact D.mul_mem hy h1

/-! ## The Suzuki structure on a `ξ`-invariant subgroup -/

/-- The automorphism of `↥C` induced by `ξ`, when `C` is `ξ`-invariant. -/
noncomputable def xiSub (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) : MulAut ↥C where
  toFun x := ⟨h.xi x, by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hCinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm x,
    symm_mem_of_map_eq (h.xi : MulAut P) hCinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem xiSub_apply (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (x : ↥C) :
    ((xiSub h hCinv x : ↥C) : P) = h.xi (x : P) := rfl

theorem xiSub_pow_apply (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (k : ℕ) (x : ↥C) :
    (((xiSub h hCinv : MulAut ↥C) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply]
      show h.xi ((((xiSub h hCinv : MulAut ↥C) ^ k) x : ↥C) : P) = _
      rw [ih, pow_succ', MulAut.mul_apply]

/-- **A `ξ`-invariant subgroup containing `Ω₁(P)` and containing two non-commuting elements is
again a Suzuki 2-group** (with the restricted automorphism). -/
noncomputable def isSuzuki2Grp_subgroup (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hOm : omega1 P ≤ C)
    (hni : ∃ x y : ↥C, x * y ≠ y * x) :
    IsSuzuki2Grp ↥C where
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
  xi := xiSub h hCinv
  trans := by
    intro x y hx2 hy2
    have hxP : orderOf (x : P) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
    have hyP : orderOf (y : P) = 2 := by rw [Subgroup.orderOf_coe]; exact hy2
    obtain ⟨k, hk⟩ := h.trans (x : P) (y : P) hxP hyP
    exact ⟨k, Subtype.ext (by rw [xiSub_pow_apply, hk])⟩

/-! ## Compatibility lemmas for passing to a subgroup

These are used to transport the `C₄` hypotheses from `P` to a `ξ`-invariant Suzuki subgroup
`↥C` (see the notes in `NOTES_redcase.md`). -/

/-- `powSub` commutes with passing to a subgroup. -/
theorem powSub_subgroupOf {H C : Subgroup P} (hHC : H ≤ C)
    (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (n : ℕ) :
    powSub (H.subgroupOf C) n = (powSub H n).subgroupOf C := by
  have hab' : ∀ x ∈ H.subgroupOf C, ∀ y ∈ H.subgroupOf C, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hab x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, hax⟩ := (Work.Higman.mem_powSub_iff hab').mp hx
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Work.Higman.mem_powSub_iff hab).mpr ⟨a, ha, by
      have := congrArg (fun t : ↥C => (t : P)) hax
      simpa [Subgroup.coe_pow] using this⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨a, ha, hax⟩ := (Work.Higman.mem_powSub_iff hab).mp hx
    refine (Work.Higman.mem_powSub_iff hab').mpr ⟨⟨a, hHC ha⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ha
    · exact Subtype.ext (by simpa [Subgroup.coe_pow] using hax)

/-- `Ω₁` commutes with passing to a Suzuki subgroup. -/
theorem omega1_subgroupOf (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCSz : IsSuzuki2Grp ↥C) : omega1 ↥C = (omega1 P).subgroupOf C := by
  ext x
  rw [Subgroup.mem_subgroupOf, hCSz.mem_omega1]
  constructor
  · intro hx
    exact h.mem_omega1.mpr (by
      have := congrArg (fun t : ↥C => (t : P)) hx
      simpa [Subgroup.coe_pow] using this)
  · intro hx
    exact Subtype.ext (by
      have := h.mem_omega1.mp hx
      simpa [Subgroup.coe_pow] using this)

/-- The commutator subgroup commutes with passing to a subgroup. -/
theorem commutator_subgroupOf (C : Subgroup P) :
    ⁅(⊤ : Subgroup ↥C), ⊤⁆ = (⁅C, C⁆).subgroupOf C := by
  have htopmap : Subgroup.map C.subtype (⊤ : Subgroup ↥C) = C := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have h1 : Subgroup.map C.subtype ⁅(⊤ : Subgroup ↥C), ⊤⁆ = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, htopmap]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : P) ∈ Subgroup.map C.subtype ⁅(⊤ : Subgroup ↥C), ⊤⁆ := ⟨x, hx, rfl⟩
    rwa [h1] at hx'
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : (x : P) ∈ Subgroup.map C.subtype ⁅(⊤ : Subgroup ↥C), ⊤⁆ := by
      rwa [h1]
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']

/-- `map subtype` followed by `subgroupOf` is the identity. -/
theorem subgroupOf_map_subtype {C : Subgroup P} (D : Subgroup ↥C) :
    (D.map C.subtype).subgroupOf C = D := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  · intro hx
    exact ⟨x, hx, rfl⟩

/-! ## The two remaining open sub-lemmas of the reducible case

* `sharp8` is Higman's auxiliary result 8 (Higman 1963, p. 87): for a minimal cover `C > A` with
  `C ^ (2) ≤ A` and `⁅C,C⁆ = A`, the subgroup `A` has exponent `2`.  Its proof uses Higman §4
  Lemma 6 in the (now proved) module form `Work.Higman.higman_lemma6_core`.
* `c4ReducibleHyp` is the case `D ^ (2) ≤ A ^ (2)` and `⁅D,D⁆ ≤ A ^ (2)` of the reducible
  exclusion. -/

/-- **Higman 1963, auxiliary result 8 (`C₄`-specialised form).**

For a minimal `ξ`-invariant normal cover `C > A` of `A` in the `C₄` setting with `C ^ (2) ≤ A`
and `⁅C,C⁆ = A`, we reach a contradiction.

Route: by `normal_of_le_of_le` the hypothesis `hcover` also excludes every `ξ`-invariant subgroup
strictly between `A` and `C`; `↥C` is a Suzuki 2-group (`isSuzuki2Grp_subgroup`); hence the
already proved `Work.Higman.NSM.irreducible` applies to `↥C` with the subgroup
`A.subgroupOf C`.  The transport of the `C₄` hypotheses to `↥C` uses `powSub_subgroupOf`,
`omega1_subgroupOf`, `commutator_subgroupOf` and `MSA.map_xi_subgroupOf`. -/
theorem sharp8 (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) :
    False := by
  classical
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  have hAne : A ≠ ⊥ := by
    intro hb
    have h2 : powSub A 2 = ⊥ := by
      rw [hb, powSub]
      exact Subgroup.closure_eq_bot_iff.mpr (by
        rintro x ⟨y, hy, rfl⟩
        simp at hy
        rw [hy]
        simp)
    have h4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    rw [htop] at h2
    rw [h2] at h4
    simp at h4
  -- `C` is not abelian (`⁅C,C⁆ = A ≠ ⊥`)
  have hni : ∃ x y : ↥C, x * y ≠ y * x := by
    by_contra hcon
    push_neg at hcon
    have hbot : ⁅C, C⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcon ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hCd] at hbot
    exact hAne hbot
  set hCSz : IsSuzuki2Grp ↥C := isSuzuki2Grp_subgroup h hCinv (hNA.trans hAC) hni with hCSzdef
  have hxi : hCSz.xi = (xiSub h hCinv : MulAut ↥C) := by rw [hCSzdef]; rfl
  -- ## transport of the `C₄` hypotheses to `↥C`
  have hNA' : omega1 ↥C ≤ A.subgroupOf C := by
    rw [omega1_subgroupOf h hCSz]
    exact Subgroup.subgroupOf_mono C hNA
  have hGs' : ⁅(⊤ : Subgroup ↥C), ⊤⁆ = A.subgroupOf C := by
    rw [commutator_subgroupOf C, hCd]
  have hAxi' : Subgroup.map (hCSz.xi : MulAut ↥C).toMonoidHom (A.subgroupOf C)
      = A.subgroupOf C := by
    rw [hxi]
    exact MSA.map_xi_subgroupOf h hAxi hCinv
  have hAab' : ∀ x ∈ A.subgroupOf C, ∀ y ∈ A.subgroupOf C, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hAab x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hsq' : ∀ x : ↥C, x ^ 2 ∈ A.subgroupOf C := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    simpa using hsq (x : P)
  have hA4' : powSub (A.subgroupOf C) 4 = ⊥ := by
    rw [powSub_subgroupOf hAC hAab 4, hA4]
    simp
  have htop' : powSub (A.subgroupOf C) 2 = omega1 ↥C := by
    rw [powSub_subgroupOf hAC hAab 2, omega1_subgroupOf h hCSz, htop]
  have hcard' : Nat.card ↥(A.subgroupOf C) = (Nat.card ↥(omega1 ↥C)) ^ 2 := by
    rw [omega1_subgroupOf h hCSz]
    have h1 : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC)
    have h2 : Nat.card ↥((omega1 P).subgroupOf C) = Nat.card ↥(omega1 P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNA.trans hAC))
    rw [h1, h2]
    exact hcard
  -- ## the pair `(A.subgroupOf C, ↥C)` is irreducible
  have hirr : ∀ D : Subgroup ↥C, D.Normal → D.map (hCSz.xi : MulAut ↥C).toMonoidHom = D →
      A.subgroupOf C ≤ D → D = A.subgroupOf C ∨ D = ⊤ := by
    intro D hDn hDinv hA₀D
    have hADmap : A ≤ D.map C.subtype := by
      intro a ha
      exact ⟨⟨a, hAC ha⟩, hA₀D (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hDPn : (D.map C.subtype).Normal :=
      normal_of_le_of_le hGs hCn hADmap (Subgroup.map_subtype_le D)
    have hDPinv : (D.map C.subtype).map (h.xi : MulAut P).toMonoidHom = D.map C.subtype := by
      have hcomp : C.subtype.comp (xiSub h hCinv : MulAut ↥C).toMonoidHom
          = (h.xi : MulAut P).toMonoidHom.comp C.subtype := by
        ext x
        rfl
      have hDinv' : D.map (xiSub h hCinv : MulAut ↥C).toMonoidHom = D := by
        rw [← hxi]
        exact hDinv
      calc (D.map C.subtype).map (h.xi : MulAut P).toMonoidHom
          = D.map ((h.xi : MulAut P).toMonoidHom.comp C.subtype) :=
            Subgroup.map_map D (h.xi : MulAut P).toMonoidHom C.subtype
        _ = D.map (C.subtype.comp (xiSub h hCinv : MulAut ↥C).toMonoidHom) := by rw [hcomp]
        _ = (D.map (xiSub h hCinv : MulAut ↥C).toMonoidHom).map C.subtype :=
            (Subgroup.map_map D C.subtype (xiSub h hCinv : MulAut ↥C).toMonoidHom).symm
        _ = D.map C.subtype := by rw [hDinv']
    rcases hcover (D.map C.subtype) hDPn hDPinv hADmap (Subgroup.map_subtype_le D) with h1 | h1
    · left
      rw [← subgroupOf_map_subtype D, h1]
    · right
      rw [← subgroupOf_map_subtype D, h1, Subgroup.subgroupOf_self]
  exact irreducible hCSz hAxi' hAab' hNA' hGs' hsq' hA4' htop' hcard' hirr

/-- **The abelian sub-case `⁅D,D⁆ = ⊥`.**  With `D ^ (2) = A ^ (2)`, the squaring map
`D/A → A/A²` is zero, and it is injective because `D` is abelian with `Ω₁(D) = A²`; hence
`D = A`, contradicting `A < D`. -/
theorem c4DerivBotCase (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADlt : A < D)
    (hD2 : powSub D 2 = powSub A 2) (hDd : ⁅D, D⁆ = ⊥) : False := by
  classical
  have hD'ab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
      rw [← hDd]
      exact Subgroup.commutator_mem_commutator hx hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using h1)
  have hADle : A ≤ D := le_of_lt hADlt
  haveI : CommGroup ↥D := { mul_comm := fun a b => Subtype.ext (hD'ab a a.2 b b.2) }
  have hinj : ∀ x ∈ D, x ^ 2 ∈ powSub A 2 → x ∈ A := by
    intro x hx hx2
    obtain ⟨a, ha, ha2⟩ := (Work.Higman.mem_powSub_iff hAab).mp hx2
    have hsub : (x * a⁻¹) * (x * a⁻¹) = 1 := by
      have hcomm : x * a⁻¹ = a⁻¹ * x := hD'ab x hx a⁻¹ (D.inv_mem (hADle ha))
      calc (x * a⁻¹) * (x * a⁻¹) = a⁻¹ * x * (x * a⁻¹) := by rw [hcomm]
        _ = a⁻¹ * (x * x) * a⁻¹ := by group
        _ = a⁻¹ * (a * a) * a⁻¹ := by
              rw [show x * x = a * a by rw [← pow_two, ← pow_two]; exact ha2.symm]
        _ = 1 := by group
    have h2 : x * a⁻¹ ∈ powSub A 2 := by
      have hmem : x * a⁻¹ ∈ omega1 P := h.mem_omega1.mpr (by rw [pow_two]; exact hsub)
      exact htop.symm ▸ hmem
    have h3 : x = (x * a⁻¹) * a := by group
    rw [h3]
    exact A.mul_mem (powSub_le (by norm_num) h2) ha
  have hDA : D ≤ A := by
    intro x hx
    refine hinj x hx ?_
    have h : x ^ 2 ∈ powSub D 2 := Work.Higman.pow_mem_powSub hx
    rwa [hD2] at h
  exact absurd (le_antisymm hDA hADle) (Ne.symm (ne_of_lt hADlt))

/-- **The sub-case `⁅D,D⁆ = A`.**  Then the pair `(A, D)` has the full `C₄` shape inside the
Suzuki 2-group `↥D` (which is non-abelian), and minimality of `D` upgrades to irreducibility for
that pair; the irreducible case `Work.Higman.NSM.irreducible` applied to `↥D` gives the
contradiction. -/
theorem c4DerivACase (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hD2 : powSub D 2 = powSub A 2) (hDd : ⁅D, D⁆ = A)
    (hmin : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      powSub E 2 ≤ powSub A 2 → ⁅E,E⁆ ≤ A → A ≤ E → E ≤ D →
      E = A ∨ E = D) : False := by
  classical
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  have hni : ∃ x y : ↥D, x * y ≠ y * x := by
    by_contra hcon
    push_neg at hcon
    have hbot : ⁅D, D⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcon ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hDd] at hbot
    have h2 : A ≠ ⊥ := by
      intro hb
      have h4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
      rw [hb] at hcard
      simp at hcard
      nlinarith [hcard, h4]
    exact h2 hbot
  set hDSz : IsSuzuki2Grp ↥D := isSuzuki2Grp_subgroup h hDinv (hNA.trans hAD) hni with hDSzdef
  have hxiD : hDSz.xi = (xiSub h hDinv : MulAut ↥D) := by rw [hDSzdef]; rfl
  have hNA'' : omega1 ↥D ≤ A.subgroupOf D := by
    rw [omega1_subgroupOf h hDSz]
    exact Subgroup.subgroupOf_mono D hNA
  have hGs'' : ⁅(⊤ : Subgroup ↥D), ⊤⁆ = A.subgroupOf D := by
    rw [commutator_subgroupOf D, hDd]
  have hAxi'' : Subgroup.map (hDSz.xi : MulAut ↥D).toMonoidHom (A.subgroupOf D)
      = A.subgroupOf D := by
    rw [hxiD]
    exact MSA.map_xi_subgroupOf h hAxi hDinv
  have hAab'' : ∀ x ∈ A.subgroupOf D, ∀ y ∈ A.subgroupOf D, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hAab x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hsq'' : ∀ x : ↥D, x ^ 2 ∈ A.subgroupOf D := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    simpa using hsq (x : P)
  have hA4'' : powSub (A.subgroupOf D) 4 = ⊥ := by
    rw [powSub_subgroupOf hAD hAab 4, hA4]
    simp
  have htop'' : powSub (A.subgroupOf D) 2 = omega1 ↥D := by
    rw [powSub_subgroupOf hAD hAab 2, omega1_subgroupOf h hDSz, htop]
  have hcard'' : Nat.card ↥(A.subgroupOf D) = (Nat.card ↥(omega1 ↥D)) ^ 2 := by
    rw [omega1_subgroupOf h hDSz]
    have h1 : Nat.card ↥(A.subgroupOf D) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD)
    have h2 : Nat.card ↥((omega1 P).subgroupOf D) = Nat.card ↥(omega1 P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNA.trans hAD))
    rw [h1, h2]
    exact hcard
  have hirr : ∀ E : Subgroup ↥D, E.Normal → E.map (hDSz.xi : MulAut ↥D).toMonoidHom = E →
      A.subgroupOf D ≤ E → E = A.subgroupOf D ∨ E = ⊤ := by
    intro E hEn hEinv hA₀E
    have hAEmap : A ≤ E.map D.subtype := by
      intro a ha
      exact ⟨⟨a, hAD ha⟩, hA₀E (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have hEmn : (E.map D.subtype).Normal :=
      normal_of_le_of_le hGs hDn hAEmap (Subgroup.map_subtype_le E)
    have hEminv : (E.map D.subtype).map (h.xi : MulAut P).toMonoidHom = E.map D.subtype := by
      have hcomp : D.subtype.comp (xiSub h hDinv : MulAut ↥D).toMonoidHom
          = (h.xi : MulAut P).toMonoidHom.comp D.subtype := by
        ext x
        rfl
      have hEinv' : E.map (xiSub h hDinv : MulAut ↥D).toMonoidHom = E := by
        rw [← hxiD]
        exact hEinv
      calc (E.map D.subtype).map (h.xi : MulAut P).toMonoidHom
          = E.map ((h.xi : MulAut P).toMonoidHom.comp D.subtype) :=
            Subgroup.map_map E (h.xi : MulAut P).toMonoidHom D.subtype
        _ = E.map (D.subtype.comp (xiSub h hDinv : MulAut ↥D).toMonoidHom) := by rw [hcomp]
        _ = (E.map (xiSub h hDinv : MulAut ↥D).toMonoidHom).map D.subtype :=
            (Subgroup.map_map E D.subtype (xiSub h hDinv : MulAut ↥D).toMonoidHom).symm
        _ = E.map D.subtype := by rw [hEinv']
    -- `E.map D.subtype` is again an admissible subgroup; minimality forces `E = A` or `E = D`
    have hE2 : powSub (E.map D.subtype) 2 ≤ powSub A 2 := by
      rw [← hD2]
      exact powSub_mono (Subgroup.map_subtype_le E)
    have hEd : ⁅(E.map D.subtype), (E.map D.subtype)⁆ ≤ A :=
      (Subgroup.commutator_mono (Subgroup.map_subtype_le E)
        (Subgroup.map_subtype_le E)).trans (le_of_eq hDd)
    rcases hmin (E.map D.subtype) hEmn hEminv hE2 hEd hAEmap (Subgroup.map_subtype_le E) with h1 | h1
    · left
      rw [← subgroupOf_map_subtype E, h1]
    · right
      rw [← subgroupOf_map_subtype E, h1, Subgroup.subgroupOf_self]
  exact irreducible hDSz hAxi'' hAab'' hNA'' hGs'' hsq'' hA4'' htop'' hcard'' hirr

/-- **A cycle-free copy of `MSA.centralizer_eq_self`** (Higman's Lemma 9, endgame): the
centralizer of a maximal `ξ`-invariant abelian normal subgroup is itself.  (The module
`MSA.centralizer_eq_self` is downstream of this file, so the statement is re-proved here, using
the Gorenstein–Thompson piece `NSM.c4gapCentralises` for the `⁅D,D⁆ = A²` case.) -/
theorem c4_centralizer_eq_self (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set P) = A := by
  classical
  haveI : A.Normal := hA.normal
  set M : Subgroup P := Subgroup.centralizer (A : Set P) with hM
  have hAM : A ≤ M := by
    intro a ha
    rw [hM, Subgroup.mem_centralizer_iff]
    intro x hx
    exact hAab x hx a ha
  by_cases hMA : M ≤ A
  · exact le_antisymm hMA hAM
  · exfalso
    have hMne : M ≠ A := fun hEq => hMA (le_of_eq hEq)
    have hMn : M.Normal := by rw [hM]; infer_instance
    have hMinv : M.map (h.xi : MulAut P).toMonoidHom = M := by
      rw [hM]
      have hmem : ∀ g : P, (∀ a ∈ A, a * g = g * a) ↔ g ∈ Subgroup.centralizer (A : Set P) :=
        fun g => Subgroup.mem_centralizer_iff
      refine le_antisymm ?_ ?_
      · rintro y ⟨x, hx, rfl⟩
        refine (hmem (h.xi x)).mpr ?_
        intro a ha
        have hx' := (hmem x).mp hx
        have h1 := hx' ((h.xi : MulAut P).symm a) (symm_mem_of_map_eq (h.xi : MulAut P) hAxi ha)
        calc a * h.xi x = h.xi ((h.xi : MulAut P).symm a) * h.xi x := by simp
          _ = h.xi ((h.xi : MulAut P).symm a * x) := by rw [map_mul]
          _ = h.xi (x * (h.xi : MulAut P).symm a) := by rw [h1]
          _ = h.xi x * a := by rw [map_mul]; simp
      · intro y hy
        refine ⟨(h.xi : MulAut P).symm y, ?_, by simp⟩
        refine (hmem ((h.xi : MulAut P).symm y)).mpr ?_
        intro a ha
        have hy' := (hmem y).mp hy
        have h2 : h.xi a ∈ A := by
          have h3 := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom ha
          rwa [hAxi] at h3
        have h1 := hy' (h.xi a) h2
        have h4 : a * (h.xi : MulAut P).symm y = (h.xi : MulAut P).symm y * a := by
          have := congrArg (h.xi : MulAut P).symm h1
          simpa using this
        exact h4
    obtain ⟨D, hDn, hDinv, hAD, hDM, hDA, hcover⟩ :=
      MSA.exists_minimal_covering h (A := A) (M := M) hMn hMinv hAM hMne
    have hZ : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := by
      intro d hd a ha
      have hdM : d ∈ M := hDM hd
      rw [hM, Subgroup.mem_centralizer_iff] at hdM
      exact (hdM a ha).symm
    have hDdle : ⁅D, D⁆ ≤ A := by
      calc ⁅D, D⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = A := hGs
    have hDdxi : (⁅D, D⁆).map (h.xi : MulAut P).toMonoidHom = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, hDinv]
    rcases trich h hA hA4 hDdle hDdxi with hDbot | hDsq | hDself
    · -- `D` abelian, contradicting maximality of `A`
      exact hDA (hmax D ⟨hDn, hDinv, fun x hx y hy =>
        commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp
          (by rw [← hDbot]; exact Subgroup.commutator_mem_commutator hx hy))⟩ hAD)
    · -- `⁅D,D⁆ = A²`: `D` centralises `A`, Gorenstein–Thompson
      exact c4gapCentralises h hAxi hAab hNA hGs hsq hA4 htop hcard hA hmax hDn hDinv
        hAD (Ne.symm hDA) hcover hDsq hZ
    · -- `⁅D,D⁆ = A`: then `⁅x,y⁆² = ⁅x²,y⁆ = 1`, so `D' ≤ A² < A`
      have hA2lt : powSub A 2 < A := by
        refine lt_of_le_of_ne (powSub_le (n := 2) (by norm_num)) (Ne.symm ?_)
        intro heq
        have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [heq, htop]
        rw [h1] at hcard
        have h4 := h.omega1_card_ge_four
        nlinarith [hcard, h4]
      have hsq_le : ⁅D, D⁆ ≤ powSub A 2 := by
        refine Subgroup.commutator_le.mpr ?_
        intro x hx y hy
        rw [htop]
        refine h.mem_omega1.mpr ?_
        -- `⁅x,y⁆² = ⁅x²,y⁆ = 1`
        have h1 : ⁅x * x, y⁆ = x * ⁅x, y⁆ * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]; group
        have h2 : ⁅x * x, y⁆ = 1 := by
          have hx2 : x * x ∈ A := by simpa [pow_two] using hsq x
          exact commutatorElement_eq_one_iff_mul_comm.mpr (hZ y hy (x * x) hx2).symm
        have h3 : x * ⁅x, y⁆ * x⁻¹ = ⁅x, y⁆ := by
          have hmem : ⁅x, y⁆ ∈ A := hDself ▸ Subgroup.commutator_mem_commutator hx hy
          rw [hZ x hx ⁅x, y⁆ hmem]
          group
        rw [h1, h3, ← pow_two] at h2
        exact h2
      exact not_le_of_gt hA2lt (hDself ▸ hsq_le)

/-- **The isolated hard core of the residual** (delegated as
`Submission.Work.Higman.NSM.c4gapHard`): the `L₁ × L₂ → L₃` configuration of Higman's §4 Lemma 6:
`C` does *not* centralise `A` and `⁅⊤,C⁆ = A`. -/
theorem c4gapHard (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = powSub A 2)
    (hC2 : powSub C 2 = powSub A 2)
    (hCcard : Nat.card ↥C = (Nat.card ↥(omega1 P)) ^ 3)
    (hACd : ⁅A, C⁆ = powSub A 2)
    (hCP : ⁅(⊤ : Subgroup P), C⁆ = A) :
    False := by
  sorry

/-- **The residual of the `C₄` exclusion**, reduced to `c4gapHard`:
`⁅A,C⁆ = ⊥` is `c4gapCentralises` (Gorenstein–Thompson), and for `⁅A,C⁆ = A²` the sub-cases
`C² = ⊥`, `C² = A`, `⁅⊤,C⁆ = A²` are discarded (the last one forces `⁅A,C⁆ = ⊥`). -/
theorem c4gap (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : powSub A 4 = ⊥)
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = powSub A 2) :
    False := by
  classical
  have hA2ne : powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(omega1 P) = 1 := by rw [← htop, hb]; simp
    have h2 := h.omega1_card_ge_four
    omega
  have hACxi : (⁅A, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅A, C⁆ := by
    rw [Subgroup.map_commutator, hAxi, hCinv]
  have hACle : ⁅A, C⁆ ≤ A := by
    calc ⁅A, C⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC le_rfl
      _ = powSub A 2 := hCd
      _ ≤ A := powSub_le (n := 2) (by norm_num)
  have hC2le : powSub C 2 ≤ A := by
    rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hC2xi : (powSub C 2).map (h.xi : MulAut P).toMonoidHom = powSub C 2 :=
    map_powSub (h.xi : MulAut P) hCinv 2
  have hCPle : ⁅(⊤ : Subgroup P), C⁆ ≤ A := by
    rw [← hGs]
    exact Subgroup.commutator_mono le_rfl le_top
  have hCPxi : (⁅(⊤ : Subgroup P), C⁆).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), C⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective, hCinv]
  have hA2leCP : powSub A 2 ≤ ⁅(⊤ : Subgroup P), C⁆ := by
    rw [← hCd]
    exact Subgroup.commutator_mono le_top le_rfl
  rcases trich h hA hA4 hACle hACxi with hACbot | hACsq | hACself
  · -- `⁅A,C⁆ = ⊥`: Gorenstein–Thompson
    refine c4gapCentralises h hAxi hAab hNA hGs hsq hA4 htop hcard hA hmax hCn hCinv
      hAC hCA hcover hCd ?_
    intro c hc a ha
    have hmem : ⁅a, c⁆ ∈ ⁅A, C⁆ := Subgroup.commutator_mem_commutator ha hc
    rw [hACbot] at hmem
    have h1 : ⁅a, c⁆ = 1 := by simpa using hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · -- `⁅A,C⁆ = A²`
    rcases trich h hA hA4 hC2le hC2xi with hC2bot | hC2sq | hC2self
    · -- `C² = ⊥`: then `C ≤ Ω₁(P) ≤ A`
      have hCle : C ≤ omega1 P := by
        intro x hx
        rw [h.mem_omega1]
        have hxm : x ^ 2 ∈ powSub C 2 := pow_mem_powSub hx
        rw [hC2bot] at hxm
        simpa using hxm
      exact hCA (le_antisymm hAC (hCle.trans hNA))
    · -- `C² = A²`
      have hCcard : Nat.card ↥C = (Nat.card ↥(omega1 P)) ^ 3 :=
        C4Cover.c4_cover_card_eq_cube h hAab hNA hGs hsq htop hcard hCn hCinv hAC hCA
          hcover hCd
      rcases trich h hA hA4 hCPle hCPxi with hCPbot | hCPsq | hCPeq
      · exact hA2ne (le_bot_iff.mp (hCPbot ▸ hA2leCP))
      · -- `⁅⊤,C⁆ = A²` forces `⁅A,C⁆ = ⊥`
        have hsq_cent : ∀ u : P, ∀ d ∈ C, u ^ 2 * d = d * u ^ 2 := by
          intro u d hd
          have hud : ⁅u, d⁆ ∈ powSub A 2 := by
            rw [← hCPsq]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hd
          have hcent : ⁅u, d⁆ ∈ Subgroup.center P := h.omega1_le_center (htop ▸ hud)
          have hinv : ⁅u, d⁆ ^ 2 = 1 := h.mem_omega1.mp (htop ▸ hud)
          have h2 : ⁅u, ⁅u, d⁆⁆ = 1 :=
            commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hcent u)
          have h4 : ⁅u ^ 2, d⁆ = 1 := by
            rw [Work.Higman.commutatorElement_sq_self u d, h2, hinv, one_mul]
          exact commutatorElement_eq_one_iff_mul_comm.mp h4
        have h1 : A ≤ Subgroup.centralizer (C : Set P) := by
          rw [← nsd_powSub_top_eq h hAxi hAab hGs hsq htop hcard, powSub,
            Subgroup.closure_le]
          rintro y ⟨u, -, rfl⟩
          exact Subgroup.mem_centralizer_iff.mpr (fun d hd => (hsq_cent u d hd).symm)
        have h2 : ⁅A, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
        rw [hACsq] at h2
        exact hA2ne h2
      · exact c4gapHard h hAxi hAab hNA hGs hsq hA4 htop hcard hA hmax hCn hCinv
          hAC hCA hcover hCd hC2sq hCcard hACsq hCPeq
    · -- `C² = A`: Higman's Lemma 7
      have hPhi : powSub C 2 ⊔ ⁅C, C⁆ = A := by
        rw [hC2self, hCd]
        exact sup_eq_left.mpr (powSub_le (n := 2) (by norm_num))
      have hab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        MSA.higman_lemma7_msa h hA hCn hCinv hAC hCA hcover hPhi (le_of_eq hCd)
      have hCbot : ⁅C, C⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hab x hx y hy).symm
      rw [hCbot] at hCd
      exact hA2ne hCd.symm
  · -- `⁅A,C⁆ = A`: then `A ≤ A²`
    have hAle : A ≤ powSub A 2 := by
      calc A = ⁅A, C⁆ := hACself.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC le_rfl
        _ = powSub A 2 := hCd
    have hAeq : A = powSub A 2 := le_antisymm hAle (powSub_le (n := 2) (by norm_num))
    have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [hAeq, htop]
    rw [h1] at hcard
    have h4 := h.omega1_card_ge_four
    nlinarith [hcard, h4]

/-- **The genuinely hard configuration.**  A `ξ`-invariant normal `D > A` in the `C₄` setting with
`D ^ (2) = A ^ (2)` and `⁅D,D⁆ = A ^ (2)`: `D` is a Suzuki 2-group with
`D' = Ω₁(D) = Z(D) = A²` and `A ⊴ D` abelian with `A² = Ω₁(D)`, `|A| = |Ω₁(D)|²`; this is the
`L₁ × L₂ → L₃` pattern of Higman's §4 Lemma 6 (whose module form,
`Work.Higman.higman_lemma6_core`, is already proved and axiom-clean in this workspace). -/
theorem c4DerivSqCase (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hD2 : powSub D 2 = powSub A 2) (hDd : ⁅D, D⁆ = powSub A 2) : False := by
  classical
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  have hA : IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  have hmax := c4sqAMaximal h hAxi hAab hNA hGs hsq hA4 htop hcard
  -- a minimal `ξ`-invariant normal cover `C ≤ D` of `A`
  obtain ⟨C, hCn, hCinv, hAC, hCD, hCA, hcover⟩ :=
    MSA.exists_minimal_covering h (A := A) (M := D) hDn hDinv hAD hADne
  have hCA' : A ≠ C := Ne.symm hCA
  have hClt : A < C := lt_of_le_of_ne hAC hCA'
  -- the dichotomy for `⁅C,C⁆`
  have hDxi : (⁅C, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, hCinv]
  have hDle : ⁅C, C⁆ ≤ A := by
    rw [← hGs]
    exact Subgroup.commutator_mono le_top le_top
  rcases trich h hA hA4 hDle hDxi with hCbot | hCsq | hCder
  · -- `⁅C,C⁆ = ⊥`: `C` abelian, contradicting maximality of `A`
    exact hCA' (hmax C ⟨hCn, hCinv, fun x hx y hy =>
      commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp
        (by rw [← hCbot]; exact Subgroup.commutator_mem_commutator hx hy))⟩ hAC).symm
  · -- `⁅C,C⁆ = A²`: the residual
    exact c4gap h hAxi hAab hNA hGs hsq hA4 htop hcard hA hmax hCn hCinv hAC hCA' hcover hCsq
  · -- `⁅C,C⁆ = A`: Higman's Lemma 8 forces `exp A ∣ 2`
    have hC2le : powSub C 2 ≤ A := by
      rw [powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    have hexp : ∀ a ∈ A, a * a = 1 :=
      MSA.lemma8_clean h hA hCn hCinv hAC hCA' hcover hC2le hCder
    have hAle : A ≤ omega1 P := by
      intro a ha
      rw [h.mem_omega1]
      simpa [pow_two] using hexp a ha
    have hAeq : A = powSub A 2 :=
      le_antisymm (by rw [htop]; exact hAle) (powSub_le (n := 2) (by norm_num))
    have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [hAeq, htop]
    rw [h1] at hcard
    have h4 := h.omega1_card_ge_four
    nlinarith [hcard, h4]

end Work.Higman.NSM
