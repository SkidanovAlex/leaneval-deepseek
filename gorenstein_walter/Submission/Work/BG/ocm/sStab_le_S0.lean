import Mathlib
import Submission.Work.BG.orbitCardAux
import Submission.Work.BG.kerLeOfMulAutInv
import Submission.Work.BG.L36SconjNotInOrbit
import Submission.Work.BG.pieceAInv
import Submission.Work.BG.mul_mem_of_notMem_of_notMem_of_relIndex_eq_two

/-!
# `Work.BG.ocm.sStab_le_S0` — the `S`-stabilizer of a `K`-nontrivial `a ∈ Irr(U)` lies in `S₀`

Let `D` be Bender–Glauberman data (`D.S` a dihedral Sylow `2`-subgroup, `D.S₀` its cyclic
maximal subgroup, `t₁, t₂ ∈ S ∖ S₀` the two involutions, so that `S₀ = ⟨t₁ t₂⟩`), `C` a §2
context compatible with `D`, `U = ↥(Uin C) = O(H)` of odd order, and `K ≤ D.U` a subgroup
normalized by `U` and inverted elementwise by both `t₁` and `t₂`.

Since `S₀ = ⟨t₁ t₂⟩` and conjugation by `t₁ t₂` is inversion followed by inversion, `S₀`
centralizes `K`; consequently **every** element of `S ∖ S₀` inverts `K` elementwise
(`inverts_K_of_notMem_S0`).  Hence, if `s ∈ S ∖ S₀` stabilized `a`, the irreducible character
`a` would be invariant under an automorphism of the odd-order group `U` inverting the normal
subgroup `KuSub C K`, and

`Work.BG.pieceAInv`

says exactly that such an `a` is trivial on `K` — contradicting `nontrivialOn C K a`.  So no
element outside `S₀` stabilizes `a`, i.e. `sStab D C hDC a ≤ S0sub D`.

## Main result

* `Work.BG.ocm.sStab_le_S0`
-/

namespace Work.BG.ocm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-- **Every element of `S ∖ S₀` inverts `K`.**  `t₁ t₂` generates `S₀` and conjugation by it is
inversion followed by inversion, hence the identity on `K`; thus `S₀` centralizes `K`.  As
`S₀` has index two in `S` and `t₁ ∉ S₀`, an element `s ∈ S ∖ S₀` is of the form `r t₁` with
`r ∈ S₀`, and `t₁` inverts `K`. -/
theorem inverts_K_of_notMem_S0 (D : BGData G) (K : Subgroup G)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    {s : ↥(D.S : Subgroup G)} (hs0 : (s : G) ∉ D.S0) :
    ∀ x ∈ K, (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
  -- `t₁` is an involution
  have ht1sq : D.t1 * D.t1 = 1 := by
    have h := pow_orderOf_eq_one D.t1
    rw [D.t1_order] at h
    simpa [pow_two] using h
  -- `s t₁ ∈ S₀`
  have hr : (s : G) * D.t1 ∈ D.S0 :=
    Work.BG.mul_mem_of_notMem_of_notMem_of_relIndex_eq_two D.S0_index s.2 hs0
      D.t1_mem D.t1_nmem
  -- `S₀` centralizes `K`
  have hcent := Work.BG.S0_centralizes_K D K h1 h2 ((s : G) * D.t1) hr
  intro x hx
  have hdecomp : (s : G) = ((s : G) * D.t1) * D.t1 := by
    rw [mul_assoc, ht1sq, mul_one]
  rw [hdecomp]
  have hstep : (((s : G) * D.t1) * D.t1) * x * (((s : G) * D.t1) * D.t1)⁻¹
      = ((s : G) * D.t1) * (D.t1 * x * D.t1⁻¹) * ((s : G) * D.t1)⁻¹ := by
    group
  rw [hstep, h1 x hx, hcent x⁻¹ (K.inv_mem hx)]

/-- The image `KuSub C K` of `K` in `U = ↥(Uin C)` is inverted by `φS s` for every
`s ∈ S ∖ S₀`. -/
theorem phiS_inverts_KuSub (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (K : Subgroup G)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    (s : ↥(D.S : Subgroup G)) (hs0 : (s : G) ∉ D.S0) :
    ∀ k ∈ Work.BG.KuSub C K, L33D.phiS D C hDC s k = k⁻¹ := by
  intro k hk
  have hkK : ((k : ↥(Uin C)) : G) ∈ K := by
    have h := hk
    rw [Work.BG.KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  rw [L33D.phiS_apply D C hDC s k]
  show (s : G) * ((k : ↥(Uin C)) : G) * (s : G)⁻¹ = ((k⁻¹ : ↥(Uin C)) : G)
  rw [inverts_K_of_notMem_S0 D K h1 h2 hs0 _ hkK]
  rfl

theorem sStab_le_S0 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Work.GW2.C16.Uin C)]
    (hDC : Work.GW2.C16.Compat D C) (K : Subgroup G)
    (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    {a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C)}
    (ha : Work.BG.nontrivialOn C K a) :
    Work.BG.sStab D C hDC (a : OddOrder.RepresentationTheory.ClassFunction
        ↥(Work.GW2.C16.Uin C) ℂ) ≤ Work.BG.S0sub D := by
  classical
  intro s hs
  rw [Work.BG.mem_S0sub]
  by_contra hs0
  -- `hs` says that `a` is invariant under `φS s`
  have hfix : ∀ u : ↥(Uin C),
      (a : ClassFunction ↥(Uin C) ℂ) (L33D.phiS D C hDC s u)
        = (a : ClassFunction ↥(Uin C) ℂ) u := by
    intro u
    have h := (Work.BG.mem_sStab D C hDC (a : ClassFunction ↥(Uin C) ℂ) s).mp hs
    have h2' := congrArg (fun φ : ClassFunction ↥(Uin C) ℂ => φ u) h
    rw [ClassFunction.compHom_apply] at h2'
    exact h2'
  -- `K` is normalized by `U`
  have hKnorm : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K := by
    intro u hu x hx
    exact Knorm u (by rwa [hDC.U_eq] at hu) x hx
  haveI hKunorm : (Work.BG.KuSub C K).Normal := Work.BG.KuSub_normal D C K hKnorm
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `s` inverts `K`, so the "Piece A" lemma makes `a` trivial on `K`
  have htriv := Work.BG.pieceAInv (Work.BG.KuSub C K) (L33D.odd_card_Uin D C hDC)
    (L33D.phiS D C hDC s) (phiS_inverts_KuSub D C hDC K h1 h2 s hs0)
    (a : ClassFunction ↥(Uin C) ℂ) a.isIrreducible hfix
  obtain ⟨u, huK, hune⟩ := ha
  refine hune (htriv u ?_)
  rw [Work.BG.KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact huK

end Work.BG.ocm
