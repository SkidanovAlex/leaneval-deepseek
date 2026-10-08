import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.theorem4_3
import Submission.Work.GlaubermanZJ.ZJ_le_pCore
import Submission.Work.GlaubermanZJ.PStableAux
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.ZJ_map_of_ker_inf_eq_bot
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Fitting.subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot
import Submission.Work.Fitting.isPSolvable_of_solvable
import Submission.Work.LocalPrelim.ft7_2_psolvable_bridge

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

/-! ## Two auxiliary facts about `Z(J(·))`

The main theorem below is Glauberman's Theorem A in the `O_{p'} = 1` case, assembled from the
pieces already proved in this area:

* `p`-stability of `X`
  (`Work.GlaubermanZJ.PStableAux.isPStable_of_isPSolvable_of_abelianSylowTwo`,
  Glauberman §6 via the quadratic Hall–Higman result),
* `Z(J(S)) ≤ O_p(X)` (`Work.GlaubermanZJ.ZJ_le_pCore`),
* Theorem 4.3 (`Work.GlaubermanZJ.theorem4_3`), which turns these into `Z(J(S)) ⊴ X`,

and the final step "normal + `Z(J(S))` of a Sylow `S` ⟹ characteristic": an automorphism `φ`
sends `S` to a Sylow `T = φ(S)`, which is conjugate to `S`, and `Z(J(·))` is natural under
automorphisms and under conjugation. -/

/-- `Z(J(·))` is natural under automorphisms: `Z(J(φ S)) = φ (Z(J(S)))`. -/
theorem ZJ_map_of_mulEquiv {X : Type*} [Group X] [Finite X] (φ : X ≃* X) (S : Subgroup X) :
    Submission.Blueprint.ZJ (S.map φ.toMonoidHom) =
      (Submission.Blueprint.ZJ S).map φ.toMonoidHom := by
  have hker : S ⊓ φ.toMonoidHom.ker = ⊥ := by
    rw [(MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective, inf_bot_eq]
  rw [ZJ_eq (S.map φ.toMonoidHom), ZJ_eq S,
    Work.PGroup.ZJ_map_of_ker_inf_eq_bot φ.toMonoidHom S hker]

-- The reduced form of the area's theorem: for `X` finite solvable with abelian Sylow
-- 2-subgroups (or `5 ≤ p`), `p` an odd prime and `O_{p'}(X) = ⊥`, `Z(J(S))` is characteristic
-- in `X` for every Sylow `p`-subgroup `S`.  (`C(O_p(X)) ⊆ O_p(X)` comes from Hall–Higman 1.2.3,
-- `Work.Fitting.centralizer_pPrimePCore_le`; p-stability from `pstable_of_abelianSylowTwo`;
-- then Theorem A.  If `O_p(X) = ⊥` then `X = 1` by Hall–Higman and the claim is trivial.)
theorem GlaubermanZJ_reduced {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpne : p ≠ 2) (hsol : Group.IsSolvable X)
    (h2 : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo X)
    (hcore : Work.Fitting.pPrimeCore p X = ⊥) (P : Sylow p X) :
    (Submission.Blueprint.ZJ (P : Subgroup X)).Characteristic := by
  haveI : Group.IsSolvable X := hsol
  haveI hFps : Work.Fitting.IsPSolvable p X := Work.Fitting.isPSolvable_of_solvable p X
  have hps : Work.HallHigman.IsPSolvable p X :=
    Work.LocalPrelim.ft7_2_psolvable_bridge hp hFps
  by_cases hOp : Work.Fitting.pCore p X = ⊥
  · -- `O_p(X) = 1` and `O_{p'}(X) = 1`, so `X` is trivial and every subgroup is characteristic
    haveI : Subsingleton X :=
      Work.Fitting.subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot p X hOp hcore
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    have hbot : Submission.Blueprint.ZJ (P : Subgroup X) = ⊥ :=
      le_bot_iff.mp fun x _ => Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
    rw [hbot, Subgroup.map_bot]
  · -- main case: `O_p(X) ≠ 1`
    haveI : Fact p.Prime := ⟨hp⟩
    -- `p`-stability of `X` (Glauberman §6)
    have hstab : IsPStable p X :=
      Work.GlaubermanZJ.PStableAux.isPStable_of_isPSolvable_of_abelianSylowTwo p hp hpne
        (Nat.card X) X le_rfl hps h2
    -- `Z(J(P)) ≤ O_p(X)` (the first half of Theorem A)
    have hZle : Submission.Blueprint.ZJ (P : Subgroup X) ≤ Work.Fitting.pCore p X :=
      ZJ_le_pCore hp hpne hps h2 hcore P
    -- Theorem 4.3 with `B = O_p(X)`: `Z(J(P)) ⊓ O_p(X) = Z(J(P))` is normal in `X`
    have hnorm : (Submission.Blueprint.ZJ (P : Subgroup X)).Normal := by
      have h := theorem4_3 hp hpne hps h2 hstab P (Work.Fitting.pCore p X)
        (Work.Fitting.isPGroup_pCore hp)
      rwa [inf_eq_left.mpr hZle] at h
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    -- `φ` maps the Sylow `P` to a Sylow `T`, which is a conjugate of `P`
    let T : Sylow p X := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective P
    haveI hpre : MulAction.IsPretransitive X (Sylow p X) :=
      Sylow.isPretransitive_of_finite (p := p) (G := X)
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := X) (α := Sylow p X) P T
    have hg' : (P : Subgroup X).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup X).map φ.toMonoidHom := by
      have h1 : ((g • P : Sylow p X) : Subgroup X) =
          (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.pointwise_smul_def _
      have h2 : (T : Subgroup X) = (P : Subgroup X).map φ.toMonoidHom :=
        Sylow.coe_mapSurjective φ.surjective P
      rw [← h1, hg, h2]
    -- conjugating back: `Z(J(P))` is normal in `X`
    have hconj : (Submission.Blueprint.ZJ (P : Subgroup X)).map
        (MulAut.conj g).toMonoidHom = Submission.Blueprint.ZJ (P : Subgroup X) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; exact Subgroup.mem_top g)
    calc (Submission.Blueprint.ZJ (P : Subgroup X)).map φ.toMonoidHom
        = Submission.Blueprint.ZJ ((P : Subgroup X).map φ.toMonoidHom) :=
          (ZJ_map_of_mulEquiv φ (P : Subgroup X)).symm
      _ = Submission.Blueprint.ZJ ((P : Subgroup X).map (MulAut.conj g).toMonoidHom) := by
          rw [← hg']
      _ = (Submission.Blueprint.ZJ (P : Subgroup X)).map (MulAut.conj g).toMonoidHom :=
          ZJ_map_of_mulEquiv (MulAut.conj g) (P : Subgroup X)
      _ = Submission.Blueprint.ZJ (P : Subgroup X) := hconj

end Work.GlaubermanZJ
