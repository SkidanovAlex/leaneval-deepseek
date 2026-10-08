import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.R_commutator_mem_P

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.ZRS_eq_P` — §3 leaf: `Z(RΣ) = P`

Peterfalvi II Ch. V §3 (the `Z(RC_W(P)) = Z(R) = P` of step (11)): in case (10-2)
(`|P| = 3`, `|C_Q(P)| = 8`, `Z(R) = P`, and `Σ` acting faithfully on `R/P`), the centre of
`RΣ` is exactly `P`.

The hypotheses of the standing context give `|R| = 3 · |C_Q(P) + 1| = 27`, so `R/P = R/Z(R)`
has order `9 = 3²` and is abelian: every commutator of two elements of `R` lies in `P`
(`Prove/R_commutator_mem_P`).  Now `Σ` normalises `R` (since `Σ ≤ C_G(P) ≤ N_G(R)`), so
`RΣ = R ⊔ Σ` is the set product `R · Σ` and `R ⊴ RΣ`.  An element `z` of the centre of `RΣ`
centralises `R`, so writing `z = rσ` one gets `σ x σ⁻¹ = r⁻¹ x r` for all `x ∈ R`, whence
`σ x σ⁻¹ x⁻¹ = r⁻¹ x r x⁻¹ ∈ [R,R] ≤ P`: `σ` acts trivially on `R/P`, so `σ = 1` by the
faithfulness `hSig`, and `z = r ∈ C_G(R) ⊓ R = P`.  Conversely `P` is central in `RΣ` because
`R ≤ C_G(P)` and `Σ ≤ C_G(P)`.  Hence `Z(RΣ) = P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

theorem ZRS_eq_P {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    (hp3 : Nat.card P = 3) (hA8 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8)
    (hZR : Subgroup.centralizer (h15.R : Set G) ⊓ h15.R = P)
    (hSig : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 →
      ∃ x ∈ h15.R, σ * x * σ⁻¹ * x⁻¹ ∉ P) :
    Subgroup.centralizer ((h15.R ⊔ Work.ThmF.ChV3.Sig H t P : Subgroup G) : Set G) ⊓
      (h15.R ⊔ Work.ThmF.ChV3.Sig H t P) = P := by
  -- `P ≤ R` and `Σ ≤ N_G(R)`
  have hPR : P ≤ h15.R := (le_of_eq hZR.symm).trans inf_le_right
  have hSC : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hSnorm : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) :=
    hSC.trans h15.hRn
  -- `|R| = 3 * 9 = 27`, hence `R/P` (order `9`) is abelian: commutators lie in `P`.
  have hcardR27 : Nat.card h15.R = 27 := by
    have hm9 : orderOf (s * t) ^ h15.m = 9 := by rw [← h15.hcq, hA8]
    rw [h15.hcardR, h7, hp3, hm9]
  have hcommR : ∀ a ∈ h15.R, ∀ b ∈ h15.R, a * b * a⁻¹ * b⁻¹ ∈ P :=
    R_commutator_mem_P hcardR27 hp3 hZR
  apply le_antisymm
  · -- `Z(RΣ) ≤ P`
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzC, hzS⟩ := hz
    -- `z` centralises `R`
    have hzCR : z ∈ Subgroup.centralizer (h15.R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hzC) x (Subgroup.mem_sup_left hx)
    -- decompose `z = rr * σ` with `rr ∈ R`, `σ ∈ Σ` (as `Σ` normalises `R`)
    have hcoe : ((h15.R ⊔ Work.ThmF.ChV3.Sig H t P : Subgroup G) : Set G) =
        (h15.R : Set G) * (Work.ThmF.ChV3.Sig H t P : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSnorm
    have hzS' : z ∈ (h15.R : Set G) * (Work.ThmF.ChV3.Sig H t P : Set G) := by
      rw [← hcoe]; exact hzS
    obtain ⟨rr, hrr, σ, hσ, hrσ⟩ := Set.mem_mul.mp hzS'
    -- `σ x σ⁻¹ = rr⁻¹ x rr` for all `x ∈ R`
    have hconj : ∀ x ∈ h15.R, σ * x * σ⁻¹ = rr⁻¹ * x * rr := by
      intro x hx
      have hcx : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hzCR) x hx
      rw [← hrσ] at hcx
      rw [show σ * x * σ⁻¹ = rr⁻¹ * ((rr * σ) * x) * σ⁻¹ by group, ← hcx]
      group
    -- faithfulness of `Σ` on `R/P` forces `σ = 1`
    have hσ1 : σ = 1 := by
      by_contra hne
      obtain ⟨x, hx, hxP⟩ := hSig σ hσ hne
      apply hxP
      rw [hconj x hx]
      simpa using hcommR rr⁻¹ (h15.R.inv_mem hrr) x hx
    have hzR : z ∈ h15.R := by
      rw [← hrσ, hσ1, mul_one]; exact hrr
    exact hZR ▸ (⟨hzCR, hzR⟩ : z ∈ Subgroup.centralizer (h15.R : Set G) ⊓ h15.R)
  · -- `P ≤ Z(RΣ)`
    refine le_inf ?_ ?_
    · -- `P` centralises `R` and `Σ`, hence `R ⊔ Σ`
      have hPcenR : P ≤ Subgroup.centralizer (h15.R : Set G) :=
        Subgroup.le_centralizer_iff.mpr h15.hRc
      have hPcenS : P ≤ Subgroup.centralizer (Work.ThmF.ChV3.Sig H t P : Set G) :=
        Subgroup.le_centralizer_iff.mpr hSC
      refine (le_inf hPcenR hPcenS).trans ?_
      intro g hg
      rw [Subgroup.mem_inf] at hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro x hx
      have h1 : h15.R ≤ Subgroup.centralizer ({g} : Set G) :=
        fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hg.1 y hy)
      have h2 : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer ({g} : Set G) :=
        fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hg.2 y hy)
      exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le h1 h2) hx)
    · exact hPR.trans le_sup_left

end Work.ThmF.ChV3.Prove
