import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.clo_sM_aux
import Submission.Work.Higman.h8_struct
import Submission.Work.Higman.h8_pairing_props
import Submission.Work.Higman.HS.core_mul
import Submission.Work.Higman.MSA.l8_exp_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The hard case of Higman's Lemma 8, assembled from the algebraic core

`Work.Higman.HS.core_mul` is Higman's §4 Lemma 6 in multiplicative form.  Here we check that the
objects of `CloH8Data` (`V = C/A`, `W = Ω₁(P)`, the power map `cloSM`, the commutator pairing
`cloBPair` and the bracket `cloBetaV`) satisfy its hypotheses; the structural facts (cardinality,
transitivity, anisotropy) and the algebraic properties of the pairings are the two lemmas
`Work.Higman.h8_struct` and `Work.Higman.h8_pairing_props`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- The commutator group `C/A` with its commutative group structure (`⁅C,C⁆ = A`). -/
@[instance_reducible]
noncomputable def h8CommGroupQ {A C : Subgroup P} [A.Normal] (hCd : ⁅C, C⁆ = A) :
    CommGroup (↥C ⧸ (A.subgroupOf C)) :=
  { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := cloQuot_comm hCd }

/-- `Ω₁(P)` with its commutative group structure. -/
@[instance_reducible]
noncomputable def h8CommGroupW (h : IsSuzuki2Grp P) : CommGroup ↥(omega1 P) :=
  { (inferInstance : Group ↥(omega1 P)) with
    mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }

/-- **The hard case of Higman's Lemma 8, given the structural and pairing data.**  This is
`Work.Higman.HS.core_mul` applied to `V = C/A` and `W = Ω₁(P)`. -/
theorem h8_hard_of_data (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A)
    (S : CloH8Data h A C) {n : ℕ} (hn2 : 2 ≤ n)
    (hWcard : Nat.card ↥(omega1 P) = 2 ^ n)
    (hVcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = 2 ^ n)
    (hVtrans : ∀ a b : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, ((cloXiQuot h S.hA.map_eq S.hCinv) ^ k) a = b)
    (hWtrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((cloXiOm h) ^ k) a = b)
    (hsne : ∀ x : ↥C ⧸ (A.subgroupOf C), cloSM S x = 1 → x = 1)
    (hpolar : ∀ x y : ↥C ⧸ (A.subgroupOf C),
      cloSM S (x * y) = cloSM S x * cloSM S y * cloBPair S x y)
    (hB1 : ∀ a b c : ↥C ⧸ (A.subgroupOf C),
      cloBPair S (a * b) c = cloBPair S a c * cloBPair S b c)
    (hB2 : ∀ a b c : ↥C ⧸ (A.subgroupOf C),
      cloBPair S a (b * c) = cloBPair S a b * cloBPair S a c)
    (hBdiag : ∀ a : ↥C ⧸ (A.subgroupOf C), cloBPair S a a = 1)
    (hBeq : ∀ a b : ↥C ⧸ (A.subgroupOf C),
      cloXiOm h (cloBPair S a b) =
        cloBPair S (cloXiQuot h S.hA.map_eq S.hCinv a) (cloXiQuot h S.hA.map_eq S.hCinv b))
    (hBne : ∃ a b : ↥C ⧸ (A.subgroupOf C), cloBPair S a b ≠ 1)
    (hβ1 : ∀ a a' : ↥C ⧸ (A.subgroupOf C), ∀ b : ↥(omega1 P),
      cloBetaV S (a * a') b = cloBetaV S a b * cloBetaV S a' b)
    (hβ2 : ∀ a : ↥C ⧸ (A.subgroupOf C), ∀ b b' : ↥(omega1 P),
      cloBetaV S a (b * b') = cloBetaV S a b * cloBetaV S a b')
    (hβeq : ∀ a : ↥C ⧸ (A.subgroupOf C), ∀ b : ↥(omega1 P),
      cloXiOm h (cloBetaV S a b) =
        cloBetaV S (cloXiQuot h S.hA.map_eq S.hCinv a) (cloXiOm h b))
    (hβrel : ∀ a : ↥C ⧸ (A.subgroupOf C), cloBetaV S a (cloSM S a) = 1)
    (hβne : ∃ a : ↥C ⧸ (A.subgroupOf C), ∃ b : ↥(omega1 P), cloBetaV S a b ≠ 1) : False := by
  letI hQc : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := cloQuot_comm hCd }
  letI hWc : CommGroup ↥(omega1 P) :=
    { (inferInstance : Group ↥(omega1 P)) with
      mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  refine HS.core_mul (fun x => cloQuot_sq_one hC2 x)
    (fun w => Subtype.ext (by have := h.mem_omega1.mp w.2; simpa [pow_two] using this))
    hn2 hVcard hWcard (cloXiQuot h S.hA.map_eq S.hCinv) (cloXiOm h) hVtrans hWtrans
    (cloBPair S) hB1 hB2 hBdiag hBeq hBne (cloSM S) (cloSM_one S) (cloSM_xi S) hpolar (fun a ha h => ha (hsne a h))
    (cloBetaV S) hβ1 hβ2 hβeq hβrel hβne

/-- **The hard case of Higman's Lemma 8.**  With `A ≠ ⊥` and `A ^ (2) ≠ ⊥` in the situation of
`higman_lemma8` there is a contradiction. -/
theorem h8_hard (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A)
    (hA0 : A ≠ ⊥) (hA2 : powSub A 2 ≠ ⊥) : False := by
  haveI hAn : A.Normal := hA.normal
  obtain ⟨e, he2, hOm, he1, htop, hkey⟩ := MSA.l8_exp_data h hA hA0 hA2
  let S : CloH8Data h A C :=
    { hA := hA, hCn := hCn, hCinv := hCinv, hAC := hAC, hCA := hCA, hcover := hcover,
      hC2 := hC2, hCd := hCd, hAne := hA0, hOmega := hOm, e := e, he := by omega, he2 := he2,
      he1 := he1, htopA := htop, hkey := hkey }
  obtain ⟨n, hn2, hWcard, hVcard, hVtrans, hWtrans, hsne⟩ := h8_struct h S
  obtain ⟨hpolar, hB1, hB2, hBdiag, hBeq, hBne, hβ1, hβ2, hβeq, hβrel, hβne⟩ :=
    h8_pairing_props h S
  exact h8_hard_of_data h hA hC2 hCd S hn2 hWcard hVcard hVtrans hWtrans hsne hpolar
    hB1 hB2 hBdiag hBeq hBne hβ1 hβ2 hβeq hβrel hβne

end Work.Higman
