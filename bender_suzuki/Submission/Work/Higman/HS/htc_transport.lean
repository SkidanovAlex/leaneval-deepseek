import Mathlib
import Submission.Work.Higman.Defs
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
set_option maxHeartbeats 800000

open scoped commutatorElement

namespace Work.Higman.HS

variable {P : Type} [Group P] [Finite P]

/-- The full hypothesis package of `Work.Higman.HS.hard_two_cover`. -/
def HardTwoCoverData {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    (A C M : Subgroup P) [hAn : A.Normal] : Prop :=
  (A.map (h.xi : MulAut P).toMonoidHom = A) ∧
  (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
  (∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A) ∧
  Work.Higman.omega1 P ≤ A ∧
  ⁅(⊤ : Subgroup P), ⊤⁆ = A ∧
  (∀ x : P, x ^ 2 ∈ A) ∧
  Work.Higman.powSub A 4 = ⊥ ∧
  Work.Higman.powSub A 2 = Work.Higman.omega1 P ∧
  Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 ∧
  C.Normal ∧
  C.map (h.xi : MulAut P).toMonoidHom = C ∧
  A ≤ C ∧
  A ≠ C ∧
  (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C) ∧
  Work.Higman.powSub C 2 ≤ A ∧
  ⁅C, A⁆ = Work.Higman.powSub A 2 ∧
  ⁅C, C⁆ = Work.Higman.powSub A 2 ∧
  M.Normal ∧
  M.map (h.xi : MulAut P).toMonoidHom = M ∧
  C ≤ M ∧
  C ≠ M ∧
  (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D ≤ M → D = C ∨ D = M) ∧
  ⁅M, M⁆ = A




/-! ## The automorphism induced on a `ξ`-invariant subgroup

If `φ` is an automorphism of `P` preserving a subgroup `N`, we record the induced
automorphism `htc_restrictAut φ hN` of `↥N`, together with the two basic facts used below:
its value on an element (and on powers), and its interaction with `Subgroup.map`. -/

/-- The automorphism of `↥N` induced by an automorphism `φ` of `P` preserving `N`. -/
noncomputable def htc_restrictAut (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) : MulAut ↥N where
  toFun x := ⟨φ x, by
    have hx : φ (x : P) ∈ N.map (φ : MulAut P).toMonoidHom := Subgroup.mem_map_of_mem _ x.2
    rwa [hN] at hx⟩
  invFun x := ⟨φ⁻¹ x, by
    have hx : (x : P) ∈ N.map (φ : MulAut P).toMonoidHom := by rw [hN]; exact x.2
    obtain ⟨m, hm, hmx⟩ := hx
    rw [← hmx]
    simpa using hm⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem htc_restrictAut_coe (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) (x : ↥N) :
    (((htc_restrictAut φ hN) x : ↥N) : P) = φ (x : P) := rfl

theorem htc_restrictAut_inv_coe (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) (x : ↥N) :
    (((htc_restrictAut φ hN)⁻¹ x : ↥N) : P) = φ⁻¹ (x : P) := rfl

/-- Restated value of `htc_restrictAut` in the form that matches `Subgroup.map` goals. -/
theorem htc_subtype_restrictAut_eq (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) (x : ↥N) :
    (MulEquiv.toMonoidHom φ) (x : P) = (MulEquiv.toMonoidHom (htc_restrictAut φ hN)) x := rfl

theorem htc_restrictAut_pow_coe (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) (k : ℕ) (x : ↥N) :
    (((htc_restrictAut φ hN) ^ k) x : P) = (φ ^ k) (x : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, htc_restrictAut_coe, ih, ← MulAut.mul_apply, ← pow_succ']

/-- The inclusion of `N` intertwines `htc_restrictAut φ hN` with `φ`. -/
theorem htc_comp_subtype_restrictAut (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) :
    (φ : P →* P).comp N.subtype
      = N.subtype.comp (htc_restrictAut φ hN : MulAut ↥N).toMonoidHom := by
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (htc_restrictAut_coe φ hN x).symm

/-- `htc_restrictAut` commutes with `Subgroup.subgroupOf` and `Subgroup.map`. -/
theorem htc_map_subgroupOf_restrictAut (φ : MulAut P) {N : Subgroup P}
    (hN : N.map (φ : MulAut P).toMonoidHom = N) {K : Subgroup P} :
    (K.subgroupOf N).map (htc_restrictAut φ hN : MulAut ↥N).toMonoidHom
      = (K.map (φ : MulAut P).toMonoidHom).subgroupOf N := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [show (y : P) = φ (x : P) from by rw [← hxy]; exact htc_restrictAut_coe φ hN x]
    exact Subgroup.mem_map_of_mem _ hx
  · intro hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hy
    obtain ⟨k, hk, hkφ⟩ := hy
    rw [Subgroup.mem_map]
    refine ⟨(htc_restrictAut φ hN)⁻¹ y, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf, htc_restrictAut_inv_coe]
    rw [show (φ⁻¹) (y : P) = k from by rw [← hkφ]; simp]
    exact hk

/-- Push-forward of `ξ`-invariance along `N.subtype`. -/
theorem htc_map_xi_map_subtype (h : IsSuzuki2Grp P) {M : Subgroup P}
    (hMinv : M.map (h.xi : MulAut P).toMonoidHom = M) (D : Subgroup ↥M) :
    (D.map M.subtype).map (h.xi : MulAut P).toMonoidHom
      = (D.map (htc_restrictAut h.xi hMinv : MulAut ↥M).toMonoidHom).map M.subtype := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [Subgroup.mem_map] at hz
    obtain ⟨d, hd, hdz⟩ := hz
    rw [Subgroup.mem_map]
    refine ⟨(htc_restrictAut h.xi hMinv) d, ⟨d, hd, rfl⟩, ?_⟩
    change (MulEquiv.toMonoidHom h.xi) (d : P) = y
    rw [show (d : P) = z from hdz]
    exact hzy
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨d, hd, hdy⟩ := hy
    rw [Subgroup.mem_map] at hd
    obtain ⟨d₀, hd₀, hd₀d⟩ := hd
    rw [Subgroup.mem_map]
    refine ⟨(d₀ : P), ⟨d₀, hd₀, rfl⟩, ?_⟩
    rw [htc_subtype_restrictAut_eq h.xi hMinv d₀, hd₀d]
    exact hdy

/-! ## Elementary subgroup lemmas -/

/-- A subgroup containing the commutator subgroup has abelian quotient, hence is normal. -/
theorem htc_normal_of_commutator_le {D : Subgroup P} (hD : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ D) :
    D.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  refine le_antisymm le_top ?_
  rw [Subgroup.le_normalizer_iff]
  intro g _ d hd
  have hgd : ⁅g, d⁆ ∈ D :=
    hD (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top d))
  have hkey : g * d * g⁻¹ = ⁅g, d⁆ * d := by rw [commutatorElement_def]; group
  rw [hkey]
  exact D.mul_mem hgd hd

theorem htc_map_subtype_top (M : Subgroup P) :
    Subgroup.map (Subgroup.subtype M) (⊤ : Subgroup ↥M) = M := by
  rw [Subgroup.map_top, Subgroup.range_subtype]

theorem htc_map_subtype_subgroupOf_eq {B M : Subgroup P} (hBM : B ≤ M) :
    (B.subgroupOf M).map (Subgroup.subtype M) = B := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBM]

theorem htc_subgroupOf_map_subtype_eq {M : Subgroup P} (D : Subgroup ↥M) :
    (Subgroup.map (Subgroup.subtype M) D).subgroupOf M = D := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, hdx⟩
    exact Subtype.ext hdx ▸ hd
  · intro hx; exact ⟨x, hx, rfl⟩

theorem htc_card_subgroupOf_eq_card {B M : Subgroup P} (hBM : B ≤ M) :
    Nat.card ↥(B.subgroupOf M) = Nat.card ↥B := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective M) (K := B.subgroupOf M),
    htc_map_subtype_subgroupOf_eq hBM]

/-! ## `Ω₁` and `powSub` of a subgroup -/

/-- A subgroup `M` of a Suzuki 2-group, containing `Ω₁(P)`, invariant under `ξ` and with
`⁅M,M⁆ ≠ ⊥`, is again a Suzuki 2-group. -/
noncomputable def htc_isSuzuki2Grp_subgroup (h : IsSuzuki2Grp P) {M : Subgroup P}
    (hMinv : M.map (h.xi : MulAut P).toMonoidHom = M) (hNA : omega1 P ≤ M)
    (hne : ⁅M, M⁆ ≠ ⊥) : IsSuzuki2Grp ↥M where
  isPGroup := h.isPGroup.to_subgroup M
  noncomm := by
    by_contra hc
    push_neg at hc
    apply hne
    have hbot : ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (hc x y).symm
    have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥M) (⊤ : Subgroup ↥M)
      (Subgroup.subtype M)
    rw [hbot, Subgroup.map_bot, htc_map_subtype_top] at hmap
    exact hmap.symm
  manyInvol := by
    obtain ⟨x, y, hx2, hy2, hxy⟩ := h.manyInvol
    have hxM : x ∈ M := hNA (h.mem_omega1.mpr (by rw [← orderOf_dvd_iff_pow_eq_one, hx2]))
    have hyM : y ∈ M := hNA (h.mem_omega1.mpr (by rw [← orderOf_dvd_iff_pow_eq_one, hy2]))
    refine ⟨⟨x, hxM⟩, ⟨y, hyM⟩, ?_, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe (H := M)]; exact hx2
    · rw [← Subgroup.orderOf_coe (H := M)]; exact hy2
    · intro hh; exact hxy (Subtype.ext_iff.mp hh)
  xi := htc_restrictAut h.xi hMinv
  trans := by
    intro x y hx hy
    have hxP : orderOf (x : P) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hyP : orderOf (y : P) = 2 := (Subgroup.orderOf_coe y).trans hy
    obtain ⟨k, hk⟩ := h.trans (x : P) (y : P) hxP hyP
    exact ⟨k, Subtype.ext (by rw [htc_restrictAut_pow_coe, hk])⟩

/-- `Ω₁` of a subgroup, as a subgroup of the ambient group. -/
theorem htc_omega1_subgroupOf_eq {M : Subgroup P} (h : IsSuzuki2Grp P) (hM : IsSuzuki2Grp ↥M) :
    omega1 ↥M = (omega1 P).subgroupOf M := by
  ext x
  rw [Subgroup.mem_subgroupOf, hM.mem_omega1, h.mem_omega1]
  constructor
  · intro hh
    have := congrArg (Subtype.val) hh
    simpa [Subgroup.coe_pow] using this
  · intro hh
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hh

/-- `powSub` of a subgroup, as a subgroup of the ambient group (abelian case). -/
theorem htc_powSub_subgroupOf_eq {A M : Subgroup P} (hAM : A ≤ M)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (n : ℕ) :
    powSub (A.subgroupOf M) n = (powSub A n).subgroupOf M := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  rw [Work.Higman.mem_powSub_iff (A := A.subgroupOf M) (n := n) (fun x hx y hy =>
        Subtype.ext (hAab (x : P) (Subgroup.mem_subgroupOf.mp hx) (y : P)
          (Subgroup.mem_subgroupOf.mp hy))),
      Work.Higman.mem_powSub_iff (A := A) (n := n) hAab]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨(a : P), ha, by rw [← hax]; simp⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨⟨a, hAM ha⟩, ha, Subtype.ext hax⟩

/-- `powSub` of a subgroup is contained in the `subgroupOf` of the `powSub` (general case). -/
theorem htc_powSub_subgroupOf_le {A M : Subgroup P} (hAM : A ≤ M) (n : ℕ) :
    powSub (A.subgroupOf M) n ≤ (powSub A n).subgroupOf M := by
  rw [Work.Higman.powSub, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (by
    rw [Subgroup.coe_pow]
    exact Work.Higman.pow_mem_powSub (Subgroup.mem_subgroupOf.mp hx))

/-- **Descent step for `hard_two_cover`.**  If the `C₄`-configuration exists in a Suzuki
2-group `P` and the last subgroup `M` is proper, then `↥M` inherits the whole configuration
(`Ω₁(P) = A² ≤ A ≤ C ≤ M` forces `Ω₁(↥M) = Ω₁(P)`, `P/A` abelian makes every subgroup
between `A` and `M` normal in `P`, and `⁅M,M⁆ = A` gives `hGs`/`hmax`; the remaining
`M`-parameter of the data is replaced by `⊤`, whose cover condition only ranges over
`C ≤ D ≤ M`).  Since `|↥M| < |P|`, the induction hypothesis `hsmall` yields `False`. -/
theorem htc_hard_two_cover_descent {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C M : Subgroup P} [hAn : A.Normal]
    (hd : Work.Higman.HS.HardTwoCoverData h A C M)
    (hMlt : M < ⊤)
    (hsmall : ∀ (Q : Type) [Group Q] [Finite Q] (hQ : Work.Higman.IsSuzuki2Grp Q)
      {A' C' M' : Subgroup Q} [A'.Normal],
      Nat.card Q < Nat.card P → Work.Higman.HS.HardTwoCoverData hQ A' C' M' → False) :
    False := by
  obtain ⟨hAxi, hAab, hmax, hNA, hGs, hsq, hA4, htop, hcard, hCn, hCinv, hAC, hCA, hcover,
    hC2, hCAd, hCd, hMn, hMinv, hCM, hCMne, hMcover, hMd⟩ := hd
  have hAM : A ≤ M := hAC.trans hCM
  have hAne : A ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥A = 1 := by rw [hb, Subgroup.card_bot]
    rw [h1] at hcard
    have h4 := h.omega1_card_ge_four
    nlinarith
  have hne : ⁅M, M⁆ ≠ ⊥ := by rw [hMd]; exact hAne
  let hM : IsSuzuki2Grp ↥M := htc_isSuzuki2Grp_subgroup h hMinv (hNA.trans hAM) hne
  have hxi : (hM.xi : MulAut ↥M) = htc_restrictAut h.xi hMinv := rfl
  haveI : (A.subgroupOf M).Normal := hAn.subgroupOf M
  -- field 1: `A'` is `ξ`-invariant
  have hAxi' : (A.subgroupOf M).map (hM.xi : MulAut ↥M).toMonoidHom = A.subgroupOf M := by
    rw [hxi, htc_map_subgroupOf_restrictAut, hAxi]
  -- field 2: `A'` is abelian
  have hAab' : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hAab (x : P) (Subgroup.mem_subgroupOf.mp hx) (y : P)
      (Subgroup.mem_subgroupOf.mp hy))
  -- field 3: maximality of `A'`
  have hmax' : ∀ B : Subgroup ↥M, IsXiAbelNormal hM B → A.subgroupOf M ≤ B →
      B = A.subgroupOf M := by
    intro B hB hAB
    set Bbar : Subgroup P := B.map M.subtype with hBbar
    have hBxi : B.map (htc_restrictAut h.xi hMinv : MulAut ↥M).toMonoidHom = B := hB.2.1
    have hBbar_xi : Bbar.map (h.xi : MulAut P).toMonoidHom = Bbar := by
      rw [hBbar, htc_map_xi_map_subtype h hMinv, hBxi]
    have hBbar_n : Bbar.Normal := by
      apply htc_normal_of_commutator_le
      rw [hGs, hBbar, ← htc_map_subtype_subgroupOf_eq hAM]
      exact Subgroup.map_mono hAB
    have hBbar_ab : ∀ x ∈ Bbar, ∀ y ∈ Bbar, x * y = y * x := by
      intro x hx y hy
      rw [hBbar, Subgroup.mem_map] at hx hy
      obtain ⟨b, hb, hbx⟩ := hx
      obtain ⟨c, hc, hcy⟩ := hy
      rw [← hbx, ← hcy]
      simpa [Subgroup.coe_mul] using congrArg Subtype.val (hB.2.2 b hb c hc)
    have hABbar : A ≤ Bbar := by
      rw [hBbar, ← htc_map_subtype_subgroupOf_eq hAM]
      exact Subgroup.map_mono hAB
    have hBeq : Bbar = A := hmax Bbar ⟨hBbar_n, hBbar_xi, hBbar_ab⟩ hABbar
    rw [← htc_subgroupOf_map_subtype_eq B, ← hBbar, hBeq]
  -- field 4: `Ω₁(↥M) ≤ A'`
  have hNA' : omega1 ↥M ≤ A.subgroupOf M := by
    rw [htc_omega1_subgroupOf_eq h hM]
    exact Subgroup.comap_mono hNA
  -- fields 5 and 23: `⁅⊤,⊤⁆ = A'`
  have hGs' : ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ = A.subgroupOf M := by
    apply Subgroup.map_injective (Subgroup.subtype_injective M)
    rw [Subgroup.map_commutator, htc_map_subtype_top, hMd, htc_map_subtype_subgroupOf_eq hAM]
  -- field 6: squares lie in `A'`
  have hsq' : ∀ x : ↥M, x ^ 2 ∈ A.subgroupOf M := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hsq (x : P)
  -- field 7: `A'⁴ = ⊥`
  have hA4' : powSub (A.subgroupOf M) 4 = ⊥ := by
    rw [htc_powSub_subgroupOf_eq hAM hAab 4, hA4, Subgroup.bot_subgroupOf]
  -- field 8: `A'² = Ω₁(↥M)`
  have htop' : powSub (A.subgroupOf M) 2 = omega1 ↥M := by
    rw [htc_powSub_subgroupOf_eq hAM hAab 2, htop, htc_omega1_subgroupOf_eq h hM]
  -- field 9: `|A'| = |Ω₁(↥M)|²`
  have hcard' : Nat.card ↥(A.subgroupOf M) = (Nat.card ↥(omega1 ↥M)) ^ 2 := by
    rw [htc_card_subgroupOf_eq_card hAM, htc_omega1_subgroupOf_eq h hM,
      htc_card_subgroupOf_eq_card (hNA.trans hAM), hcard]
  -- field 10: `C'` is normal
  have hCn' : (C.subgroupOf M).Normal := hCn.subgroupOf M
  -- field 11: `C'` is `ξ`-invariant
  have hCinv' : (C.subgroupOf M).map (hM.xi : MulAut ↥M).toMonoidHom = C.subgroupOf M := by
    rw [hxi, htc_map_subgroupOf_restrictAut, hCinv]
  -- field 12: `A' ≤ C'`
  have hAC' : A.subgroupOf M ≤ C.subgroupOf M := Subgroup.comap_mono hAC
  -- field 13: `A' ≠ C'`
  have hCA' : A.subgroupOf M ≠ C.subgroupOf M := by
    intro hh
    apply hCA
    have hc := congrArg (Subgroup.map (Subgroup.subtype M)) hh
    rwa [htc_map_subtype_subgroupOf_eq hAM, htc_map_subtype_subgroupOf_eq hCM] at hc
  -- field 14: maximality of `A'` below `C'`
  have hcover' : ∀ D : Subgroup ↥M, D.Normal →
      D.map (hM.xi : MulAut ↥M).toMonoidHom = D → A.subgroupOf M ≤ D →
      D ≤ C.subgroupOf M → D = A.subgroupOf M ∨ D = C.subgroupOf M := by
    intro D hDn hDxi hAD hDC
    set Dbar : Subgroup P := D.map M.subtype with hDbar
    have hDxi' : D.map (htc_restrictAut h.xi hMinv : MulAut ↥M).toMonoidHom = D := by
      rw [← hxi]; exact hDxi
    have hDbar_xi : Dbar.map (h.xi : MulAut P).toMonoidHom = Dbar := by
      rw [hDbar, htc_map_xi_map_subtype h hMinv, hDxi']
    have hDbar_n : Dbar.Normal := by
      apply htc_normal_of_commutator_le
      rw [hGs, hDbar, ← htc_map_subtype_subgroupOf_eq hAM]
      exact Subgroup.map_mono hAD
    have hADbar : A ≤ Dbar := by
      rw [hDbar, ← htc_map_subtype_subgroupOf_eq hAM]
      exact Subgroup.map_mono hAD
    have hDCbar : Dbar ≤ C := by
      rw [hDbar, ← htc_map_subtype_subgroupOf_eq hCM]
      exact Subgroup.map_mono hDC
    rcases hcover Dbar hDbar_n hDbar_xi hADbar hDCbar with hh | hh
    · left; rw [← htc_subgroupOf_map_subtype_eq D, ← hDbar, hh]
    · right; rw [← htc_subgroupOf_map_subtype_eq D, ← hDbar, hh]
  -- field 15: `C'² ≤ A'`
  have hC2' : powSub (C.subgroupOf M) 2 ≤ A.subgroupOf M :=
    (htc_powSub_subgroupOf_le hCM 2).trans (Subgroup.comap_mono hC2)
  -- field 16: `⁅C', A'⁆ = A'²`
  have hCAd' : ⁅C.subgroupOf M, A.subgroupOf M⁆ = powSub (A.subgroupOf M) 2 := by
    apply Subgroup.map_injective (Subgroup.subtype_injective M)
    rw [Subgroup.map_commutator, htc_map_subtype_subgroupOf_eq hCM, htc_map_subtype_subgroupOf_eq hAM,
      hCAd, htc_powSub_subgroupOf_eq hAM hAab 2, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((Work.Higman.powSub_le (by norm_num : 0 < 2)).trans hAM)]
  -- field 17: `⁅C', C'⁆ = A'²`
  have hCd' : ⁅C.subgroupOf M, C.subgroupOf M⁆ = powSub (A.subgroupOf M) 2 := by
    apply Subgroup.map_injective (Subgroup.subtype_injective M)
    rw [Subgroup.map_commutator, htc_map_subtype_subgroupOf_eq hCM, hCd,
      htc_powSub_subgroupOf_eq hAM hAab 2, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr ((Work.Higman.powSub_le (by norm_num : 0 < 2)).trans hAM)]
  -- field 18: `⊤` is normal in `↥M`
  have htop_n : (⊤ : Subgroup ↥M).Normal := inferInstance
  -- field 19: `⊤` is `ξ`-invariant
  have htop_map : (⊤ : Subgroup ↥M).map (hM.xi : MulAut ↥M).toMonoidHom = ⊤ := by
    rw [Subgroup.map_top_of_surjective _ (hM.xi).surjective]
  -- field 20: `C' ≤ ⊤`
  have hCM' : C.subgroupOf M ≤ ⊤ := le_top
  -- field 21: `C' ≠ ⊤`
  have hCMne' : C.subgroupOf M ≠ ⊤ := by
    intro hh
    apply hCMne
    have hc := congrArg (Subgroup.map (Subgroup.subtype M)) hh
    rwa [htc_map_subtype_subgroupOf_eq hCM, htc_map_subtype_top] at hc
  -- field 22: maximality of `C'` below `⊤`
  have hMcover' : ∀ D : Subgroup ↥M, D.Normal →
      D.map (hM.xi : MulAut ↥M).toMonoidHom = D → C.subgroupOf M ≤ D → D ≤ ⊤ →
      D = C.subgroupOf M ∨ D = ⊤ := by
    intro D hDn hDxi hCD hDtop
    set Dbar : Subgroup P := D.map M.subtype with hDbar
    have hDxi' : D.map (htc_restrictAut h.xi hMinv : MulAut ↥M).toMonoidHom = D := by
      rw [← hxi]; exact hDxi
    have hDbar_xi : Dbar.map (h.xi : MulAut P).toMonoidHom = Dbar := by
      rw [hDbar, htc_map_xi_map_subtype h hMinv, hDxi']
    have hDbar_n : Dbar.Normal := by
      apply htc_normal_of_commutator_le
      rw [hGs, hDbar, ← htc_map_subtype_subgroupOf_eq hAM]
      exact (Subgroup.map_mono (Subgroup.comap_mono hAC)).trans (Subgroup.map_mono hCD)
    have hCDbar : C ≤ Dbar := by
      rw [hDbar, ← htc_map_subtype_subgroupOf_eq hCM]
      exact Subgroup.map_mono hCD
    have hDbarM : Dbar ≤ M := Subgroup.map_subtype_le D
    rcases hMcover Dbar hDbar_n hDbar_xi hCDbar hDbarM with hh | hh
    · left; rw [← htc_subgroupOf_map_subtype_eq D, ← hDbar, hh]
    · right; rw [← htc_subgroupOf_map_subtype_eq D, ← hDbar, hh, Subgroup.subgroupOf_self]
  have hdata : HardTwoCoverData hM (A.subgroupOf M) (C.subgroupOf M) ⊤ :=
    ⟨hAxi', hAab', hmax', hNA', hGs', hsq', hA4', htop', hcard', hCn', hCinv', hAC', hCA',
      hcover', hC2', hCAd', hCd', htop_n, htop_map, hCM', hCMne', hMcover', hGs'⟩
  have hcard_lt : Nat.card ↥M < Nat.card P := by
    have hlt := Subgroup.card_lt_of_lt hMlt
    rwa [Subgroup.card_top] at hlt
  exact hsmall ↥M hM hcard_lt hdata


end Work.Higman.HS
