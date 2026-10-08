import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.TitsCoordAux
import Submission.Work.ZassenhausSuzuki.TitsTerminal
import Submission.Work.ZassenhausSuzuki.SzASymmIso
import Submission.Work.ZassenhausSuzuki.SzA.orbit_covering
import Submission.Work.ZassenhausSuzuki.frel_generic_value_eps
import Submission.Work.ZassenhausSuzuki.frel_spread
import Submission.Work.ZassenhausSuzuki.frel_product
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.structPair_sq_fix
import Submission.Work.ZassenhausSuzuki.structure_value_of_fix

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `suzukiTitsOfFix`: the target statement

This file holds the requested statement

`Work.ZassenhausSuzuki.suzukiTitsOfFix (hsplit) (hzass) (hG) (hθ1) (hθodd) (e) (htorus) (hfix) :
    IsTitsTheta θ ∨ IsTitsTheta θ.symm`

and its proof, reduced to the pieces the area supplies:

* `Work.ZassenhausSuzuki.structPair_sq_fix` — the structure element `ρ` of the structure
  identity `t s t = ρ t ρ⁻¹` (Peterfalvi II Ch. V §2 Lemma 1 b)) satisfies `ρ² = s`; so `ρ` is a
  *structure element* in the sense of HB III 10.6: `t·ρ²·t = ρ·t·ρ⁻¹`;
* `Work.ZassenhausSuzuki.structure_value_of_fix` (**HB III XI 11.12**; its crux, HB XI 11.11 (b),
  is `Work.ZassenhausSuzuki.crux_structure_value`): in the coordinates `e : Q ≃* A(K,θ)`, `ρ` lies
  in the torus orbit of `⟨1,0⟩` or of `⟨1,1⟩`;
* `Work.ZassenhausSuzuki.tits_of_normalised` (**HB III XI 11.13–11.14 / Suzuki 1962 §5**: the
  terminal computation, in `TitsTerminal.lean`), applied to the torus twist `h_{μ⁻¹} ∘ e` in the
  `⟨1,1⟩` case and to the `A(K,θ) ≅ A(K,θ⁻¹)` transport (`SzASymmIso.lean`) followed by a twist in
  the `⟨1,0⟩` case — which is exactly the `θ ↔ θ⁻¹` freedom of the conclusion.

The auxiliary material (field kernel, coordinate computations, the σ-lemma) lives in
`Submission/Work/ZassenhausSuzuki/TitsAux.lean`; the design notes are in
`NOTES_suzukiTitsOfFix.md` and `NOTES_TERMINAL_suzukiTitsOfFix.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem suzukiTitsOfFix {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m) (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ)) (e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
    (htorus : ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
      ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
        e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1) :
    Work.ZassenhausSuzuki.IsTitsTheta θ ∨ Work.ZassenhausSuzuki.IsTitsTheta θ.symm := by
  classical
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have htc : TorusCoords (GaloisField 2 m) θ H Q t e := htorus
  -- ## the structure element `ρ` with `t·ρ²·t = ρ·t·ρ⁻¹` (Suzuki's structure equation)
  obtain ⟨hsQ, hs2, hρQ, hstructId⟩ := structPair_spec hsplit
  have hsq : (structPair hsplit).2 * (structPair hsplit).2 = (structPair hsplit).1 :=
    structPair_sq_fix hsplit hzass hθ1 hθodd hfix e htc h2
  set g : Q := ⟨(structPair hsplit).2, hρQ⟩ with hgdef
  have hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G) := by
    have ht2 : t * t = 1 := t_mul_self hsplit
    have hgsq : (((g ^ 2 : Q)) : G) = (structPair hsplit).1 := by
      rw [Subgroup.coe_pow, pow_two]
      exact hsq
    rw [hgsq]
    calc t * (structPair hsplit).1 * t
        = ((structPair hsplit).2 * t * (structPair hsplit).2⁻¹) * (t * t) := by
          rw [← hstructId]; group
      _ = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹ := by rw [ht2, mul_one]
      _ = (g : G) * t * (((g⁻¹ : Q)) : G) := rfl
  -- ## the normalisation of the structure element (HB III XI 11.12)
  obtain ⟨μ, b, hb, hvalg⟩ :=
    structure_value_of_fix hsplit hzass h2 hθ1 hθodd hfix htc
  have hval : e g = Work.ZassenhausSuzuki.SzA.hLam θ (μ : GaloisField 2 m)
      (⟨1, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    have hg_eq : g = (⟨(structPair hsplit).2, (structPair_spec hsplit).2.2.1⟩ : Q) :=
      Subtype.ext rfl
    rw [hg_eq]
    exact hvalg
  rcases hb with hb0 | hb1
  · -- ## the case `⟨1,0⟩`: transport to the `θ⁻¹` coordinates, where it is `⟨1,1⟩`
    have htor2 : TorusCoords (GaloisField 2 m) θ.symm H Q t (e.trans (szASymm θ)) := by
      intro d hd
      obtain ⟨lam, hlam⟩ := htc d hd
      refine ⟨Units.map θ.toMonoidHom lam, fun x => ?_⟩
      obtain ⟨y, hy, hye⟩ := hlam x
      refine ⟨y, hy, ?_⟩
      simp only [MulEquiv.trans_apply]
      rw [hye]
      exact szASymm_hLam θ (lam : GaloisField 2 m) (e x)
    have heg2 : szASymm θ (e g) = Work.ZassenhausSuzuki.SzA.hLam θ.symm
        (↑(Units.map θ.toMonoidHom μ) : GaloisField 2 m)
        (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ.symm) := by
      rw [hval, hb0, szASymm_hLam, szASymm_one_zero]
      rfl
    -- the residual twist `(θμ)⁻¹` in the `θ⁻¹`-picture
    let νu : (GaloisField 2 m)ˣ := (Units.map θ.toMonoidHom μ)⁻¹
    have htor3 : TorusCoords (GaloisField 2 m) θ.symm H Q t
        ((e.trans (szASymm θ)).trans (Work.ZassenhausSuzuki.SzA.hLamHom θ.symm νu)) :=
      torusCoords_twist htor2 νu
    have hg3 : ((e.trans (szASymm θ)).trans
          (Work.ZassenhausSuzuki.SzA.hLamHom θ.symm νu)) g
        = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ.symm) := by
      simp only [MulEquiv.trans_apply, Work.ZassenhausSuzuki.SzA.hLamHom_apply]
      rw [heg2, ← Work.ZassenhausSuzuki.SzA.hLam_mul]
      have hνu : (↑νu : GaloisField 2 m)
          * (↑(Units.map θ.toMonoidHom μ) : GaloisField 2 m) = 1 := by
        rw [← Units.val_mul,
          show νu * Units.map θ.toMonoidHom μ = 1 from inv_mul_cancel _, Units.val_one]
      rw [hνu, Work.ZassenhausSuzuki.SzA.hLam_one]
    have hsymm1 : θ.symm ≠ 1 := fun h => hθ1 (by
      have h' := congrArg (fun φ : GaloisField 2 m ≃+* GaloisField 2 m => φ.symm) h
      have h'' : (1 : GaloisField 2 m ≃+* GaloisField 2 m).symm = 1 := by ext x; rfl
      rw [h''] at h'
      simpa using h')
    have hsymmodd : Odd (orderOf θ.symm) := by
      rw [show θ.symm = θ⁻¹ from rfl, orderOf_inv]
      exact hθodd
    exact Or.inr (tits_of_normalised hsymm1 hsymmodd hsplit hzass h2 htor3 hg3 hstruct)
  · -- ## the case `⟨1,1⟩`: the twisted coordinates are those of `tits_of_normalised`
    have htor1 : TorusCoords (GaloisField 2 m) θ H Q t
        (e.trans (Work.ZassenhausSuzuki.SzA.hLamHom θ (μ⁻¹))) :=
      torusCoords_twist htc μ⁻¹
    have hg1 : (e.trans (Work.ZassenhausSuzuki.SzA.hLamHom θ (μ⁻¹))) g
        = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
      simp only [MulEquiv.trans_apply, Work.ZassenhausSuzuki.SzA.hLamHom_apply]
      rw [hval, hb1, ← Work.ZassenhausSuzuki.SzA.hLam_mul]
      have hμ : (↑(μ⁻¹) : GaloisField 2 m) * (↑μ : GaloisField 2 m) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hμ, Work.ZassenhausSuzuki.SzA.hLam_one]
    exact Or.inl (tits_of_normalised hθ1 hθodd hsplit hzass h2 htor1 hg1 hstruct)

end Work.ZassenhausSuzuki
