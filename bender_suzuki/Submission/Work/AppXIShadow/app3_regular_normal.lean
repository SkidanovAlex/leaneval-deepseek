import Mathlib
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.ThreePoints.ThmC.exists_normal_commutator_le
import Submission.Work.ThreePoints.ThmC.app3_1_defs
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.NormalComplement.appIII
import Submission.Work.AppXIShadow.app3A_exists
import Submission.Work.AppXIShadow.app3B_inf_normal
import Submission.Work.AppXIShadow.app3C_commutator_fixes
import Submission.Work.AppXIShadow.app3D_stabilizer
import Submission.Work.AppXIShadow.app3E_transitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

/-- **A3** (Peterfalvi I Appendix III (2), *non-faithful* form).  Let the finite group `F` act
transitively on `Ω`, let `M = Stab_F a` be a **maximal** strongly embedded (Bender) subgroup of
`F`, and let `F` have 2-rank `1` (`¬ HasFourGroup F`).  Then there is a normal subgroup `R ⊴ F`
which contains the kernel `K` of the action, is transitive on `Ω`, is abelian modulo `K`
(`[R,R] ≤ K`) and meets `M` only in `K` (`R ⊓ M ≤ K`).

Fatihfulness is *not* assumed.  Two routes are available.

(1) Quotient route.  `K := Work.ThreePoints.ThmC.actKer F Ω` is normal, `K ≤ M`, and `K` is odd
    (`K ≤ M ⊓ M^g` for `g ∉ M`, by normality and `M ≠ ⊤`, and that intersection is odd).  Put
    `F̄ = F ⧸ K` (build the action of `F ⧸ K` on `Ω` from `MulAction.toPermHom` and
    `QuotientGroup.lift`).  Then `F̄` acts faithfully, `M̄ = M.map (mk' K)` is strongly embedded
    and a coatom, `¬ HasFourGroup F̄` (an odd normal subgroup meets a Sylow 2-subgroup trivially,
    so the Sylow 2-subgroups of `F̄` are those of `F`), so `Work.NormalComplement.appIII hBrSz hFT`
    applies and gives `Q̄ ≤ F̄` abelian, `Q̄ ⊓ M̄ = ⊥`, `Q̄ ⊔ M̄ = ⊤`; take `R = Q̄.comap (mk' K)`.

(2) Direct route (no quotients).  BrSz applied to an involution `u ∈ M` with `C_F(u) ≤ M` gives
    `O_{2'}(F) ⊔ M = F`; as `M ≠ F`, `O_{2'}(F) ≄ M`; Feit–Thompson makes `O_{2'}(F)` solvable of
    odd order, so `Work.ThreePoints.ThmC.exists_normal_commutator_le` gives
    `A ⊴ F`, `A ≤ O_{2'}(F)`, `A ≄ M`, `[A,A] ≤ M`.  Take `A` minimal by cardinality among such
    subgroups: then `A ⊓ M ≤ K` (otherwise `A ⊓ M` is normal in `F` — because `A M = F` by
    maximality — with the same properties and strictly smaller), so `R := A` works:
    `R ⊴ F`, `K ≤ R`, `[R,R] ≤ K` (as `[A,A] ⊴ F` and `≤ M`, so `≤ core M = K`),
    `R ⊓ M ≤ K`, and `R M = F` gives transitivity.

See `Work.ThreePoints.ThmC.app3_1_thm` and `Work.NormalComplement.appIII` for the faithful case. -/
theorem app3_regular_normal {F Ω : Type} [Group F] [Finite F] [MulAction F Ω] (a : Ω)
    (htrans : MulAction.IsPretransitive F Ω)
    (hstrong : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (MulAction.stabilizer F a))
    (hmax : IsCoatom (MulAction.stabilizer F a))
    (hrank : ¬ Submission.Blueprint.HasFourGroup F)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp) :
    ∃ R : Subgroup F, R.Normal ∧
      (∀ g : F, (∀ ω : Ω, g • ω = ω) → g ∈ R) ∧
      (∀ x ∈ R, ∀ y ∈ R, ∀ ω : Ω, (x * y * x⁻¹ * y⁻¹) • ω = ω) ∧
      (∀ x ∈ R, x • a = a → ∀ ω : Ω, x • ω = ω) ∧
      (∀ ω : Ω, ∃ x ∈ R, x • a = ω) := by
  classical
  -- Implementation of route (2), with one simplification: no minimality choice is needed, since
  -- `A ⊓ M` is normal in `F` as soon as `⁅A,A⁆ ≤ M` and `A ⊔ M = ⊤` (`app3B_inf_normal`), and
  -- then lies in the kernel `K = actKer F Ω` of the action outright
  -- (`le_actKer_of_normal_le_stabilizer`, the kernel being the core of the point stabiliser).
  -- The required `A` is provided by `app3A_exists`.
  obtain ⟨A, hAn, hAle, hAnle, hAder⟩ := app3A_exists (F := F) (Ω := Ω) a hstrong hrank hBrSz hFT
  -- maximality of `M = Stab_F a` turns `A ≰ M` into `A ⊔ M = ⊤`
  have hAsup : A ⊔ MulAction.stabilizer F a = ⊤ := by
    obtain ⟨q, hqA, hqM⟩ := SetLike.not_le_iff_exists.mp hAnle
    exact (SetLike.isCoatom_iff.mp hmax).2 (A ⊔ MulAction.stabilizer F a) q le_sup_right hqM
      (Subgroup.mem_sup_left hqA)
  -- `A ⊓ M` is normal in `F`, hence inside the kernel `K` of the action
  have hXn : (A ⊓ MulAction.stabilizer F a).Normal := app3B_inf_normal hAn hAder hAsup
  have hXK : A ⊓ MulAction.stabilizer F a ≤ Work.ThreePoints.ThmC.actKer F Ω :=
    Work.ThreePoints.ThmC.le_actKer_of_normal_le_stabilizer a htrans hXn inf_le_right
  -- consequently `⁅A,A⁆ ≤ A ⊓ M ≤ K`
  have hAAleK : ⁅A, A⁆ ≤ Work.ThreePoints.ThmC.actKer F Ω := by
    haveI : A.Normal := hAn
    exact le_trans (le_inf (Subgroup.commutator_le_left A A) hAder) hXK
  -- the candidate is `R = A · K`
  refine ⟨A ⊔ Work.ThreePoints.ThmC.actKer F Ω, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R ⊴ F`
    haveI : A.Normal := hAn
    haveI : (Work.ThreePoints.ThmC.actKer F Ω).Normal := Work.ThreePoints.ThmC.actKer_normal
    exact inferInstance
  · -- `R` contains the kernel of the action
    intro g hg
    exact Subgroup.mem_sup_right (Work.ThreePoints.ThmC.mem_actKer.mpr hg)
  · -- `R` is abelian modulo the kernel
    exact app3C_commutator_fixes (K := Work.ThreePoints.ThmC.actKer F Ω) (A := A)
      Work.ThreePoints.ThmC.actKer_normal hAn hAAleK le_rfl
  · -- `R ⊓ M ≤ K`
    exact app3D_stabilizer a (K := Work.ThreePoints.ThmC.actKer F Ω) (A := A)
      Work.ThreePoints.ThmC.actKer_normal hAn le_rfl hXK
  · -- `R` is transitive on `Ω`
    exact app3E_transitive a htrans hAn hAsup

end Work.AppXIShadow
