import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.clo_sM_aux
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.squaring_layer
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.MSA.l8_card
import Submission.Work.Higman.MSA.l8_sV

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The properties of the power map `cloSM : C/A → Ω₁(P)`

Higman, *Suzuki 2-groups* (1963), §5.  In the situation of Higman's auxiliary result 8 — `A` a
`ξ`-invariant abelian normal subgroup, `C` a `ξ`-invariant normal subgroup covering `A`, with
`C ^ (2) ≤ A = ⁅C,C⁆` and `A ≠ ⊥` — the power map

`cloSM S : C/A → Ω₁(P)`,  `uA ↦ u ^ 2 ^ e`

(where `2 ^ e` is the exponent of the homocyclic group `A`) is a `ξ`-equivariant bijection, and it
is *quadratic* with polar form the commutator pairing `cloBPair`:
`cloSM (x * y) = cloSM x * cloSM y * cloBPair x y`.

The work is done in two layers:
* `Submission/Work/Higman/clo_sM_aux.lean` — the elementary facts about `cloSM` (`1 ↦ 1`,
  `ξ`-equivariance, transitivity of `ξ` on `Ω₁(P) ∖ {1}`, non-vanishing);
* `Submission/Work/Higman/MSA/l8_sV.lean` and `MSA/l8_card.lean` — the same statement for the
  parallel copy `MSA.L8.sV` of the power map, *together* with the `m = n` count
  `|C/A| = |Ω₁(P)|` (`MSA.L8.l8_quot_card`) that makes it a bijection.

Here we bridge the two copies: the structures `CloH8Data` and `MSA.L8.D` have the same fields, and
the maps `cloSM`, `cloBPair`, `cloXiOm`, `cloXiQuot` agree with `MSA.L8.sV`, `MSA.L8.BV`,
`MSA.L8.xiZ`, `MSA.L8.xiQuot`; the statement is then transported.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]
variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-! ## Bridging the two copies of the data -/

/-- The `MSA.L8` hypothesis package associated with a `CloH8Data` (the two structures have the
same fields, in the same order). -/
def cloD (S : CloH8Data h A C) : MSA.L8.D h A C where
  hA := S.hA
  hCn := S.hCn
  hCinv := S.hCinv
  hAC := S.hAC
  hCA := S.hCA
  hcover := S.hcover
  hC2 := S.hC2
  hCd := S.hCd
  hAne := S.hAne
  hOmega := S.hOmega
  e := S.e
  he := S.he
  he2 := S.he2
  he1 := S.he1
  htopA := S.htopA
  hkey := S.hkey

theorem cloD_e (S : CloH8Data h A C) : (cloD S).e = S.e := rfl

/-- The representatives chosen by `cloRepC` and `MSA.L8.repC` agree. -/
theorem cloRepC_eq_repC :
    (cloRepC : (↥C ⧸ (A.subgroupOf C)) → ↥C) = MSA.L8.repC := rfl

/-- The power maps `cloSM` and `MSA.L8.sV` agree. -/
theorem cloSM_eq_sV (S : CloH8Data h A C) : cloSM S = MSA.L8.sV (cloD S) := by
  funext x
  apply Subtype.ext
  induction x using QuotientGroup.induction_on with
  | _ u => rw [cloSM_mk, MSA.L8.sV_mk, cloD_e]

/-- The commutator pairings `cloBPair` and `MSA.L8.BV` agree. -/
theorem cloBPair_eq_BV (S : CloH8Data h A C) : cloBPair S = MSA.L8.BV (cloD S) := by
  funext x y
  apply Subtype.ext
  rw [cloBPair_apply, MSA.L8.BV_apply, cloRepC_eq_repC, cloD_e]

/-- The induced automorphisms of `Ω₁(P)` agree. -/
theorem cloXiOm_eq_xiZ (h : IsSuzuki2Grp P) : cloXiOm h = xiZ h := by
  ext z
  rw [cloXiOm_apply, xiZ_apply]

/-- The automorphisms of `↥C` induced by `ξ` agree. -/
theorem cloXiC_eq_xiSubAut (h : IsSuzuki2Grp P)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (cloXiC h hCinv : MulAut ↥C) = MSA.L8.xiSubAut h hCinv := by
  ext x
  show (((cloXiSub h hCinv) x : ↥C) : P) = ((MSA.L8.xiSubAut h hCinv x : ↥C) : P)
  rw [cloXiSub_apply, MSA.L8.xiSubAut_apply]

/-- The induced automorphisms of `C/A` agree. -/
theorem cloXiQuot_eq_xiQuot (h : IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    cloXiQuot h hAinv hCinv = MSA.L8.xiQuot h hAinv hCinv := by
  ext x
  induction x using QuotientGroup.induction_on with
  | _ u => rw [cloXiQuot_mk, MSA.L8.xiQuot_mk, cloXiC_eq_xiSubAut]

/-! ## The properties of `cloSM` -/

theorem clo_sM_props {P : Type} [Group P] [Finite P] {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [A.Normal] (S : CloH8Data h A C) :
    Function.Injective (cloSM S) ∧ Function.Surjective (cloSM S) ∧ (cloSM S 1 = 1) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C),
      cloXiOm h (cloSM S x) = cloSM S (cloXiQuot h S.hA.map_eq S.hCinv x)) ∧
    (∀ x y : ↥C ⧸ (A.subgroupOf C),
      cloSM S (x * y) = cloSM S x * cloSM S y * cloBPair S x y) := by
  -- `|Ω₁(P)| = 2 ^ n` with `2 ≤ n`
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    have h4 := h.omega1_card_ge_four
    rw [hn] at h4
    by_contra hcon
    push Not at hcon
    interval_cases n <;> norm_num at h4
  -- the `m = n` count `|C/A| = |Ω₁(P)|` and the properties of `MSA.L8.sV`
  have htriv : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A :=
    MSA.L8.l8_xi_pow_card_sub_one_triv_quot (cloD S)
  have hcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(omega1 P) :=
    MSA.L8.l8_quot_card (cloD S) hn hn2 htriv
  obtain ⟨hinj, hsurj, h1, hxi, hpol⟩ := MSA.L8.l8_sV (cloD S) hcard
  have hSM := cloSM_eq_sV S
  have hBP := cloBPair_eq_BV S
  have hZ := cloXiOm_eq_xiZ h
  have hQ := cloXiQuot_eq_xiQuot h S.hA.map_eq S.hCinv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSM]; exact hinj
  · rw [hSM]; exact hsurj
  · rw [hSM]; exact h1
  · intro x
    rw [hSM, hZ, hQ]
    exact hxi x
  · intro x y
    rw [hSM, hBP]
    exact hpol x y

end Work.Higman
