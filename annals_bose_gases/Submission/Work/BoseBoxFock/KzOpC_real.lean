import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.CFockReal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option linter.unusedVariables false

/-- `KzOpC` is a *real* operator: all of its matrix entries in the Fock basis
`β ↦ e_β = toCFock (Excited m) (Finsupp.single β 1)` are real numbers, i.e. it maps the
real locus `Work.BoseBoxFock.IsRealC` into itself.  This holds because every coefficient in
the definition of `KzOpC` is a real number cast to `ℂ` and every spectator operator
(`annC`, `creC`, `annOfE`, `creOfE`, `nOpC`, `nPlusC`, and the rows `KzBogC`, `linOpTC`,
`Q2exC`, `Q3TC`) is `IsRealMap` (`Work.BoseBoxFock.IsRealMap`, proved in
`Submission/Work/BoseBoxFock/CFockReal.lean`), while `BNH` is real by hypothesis.

Proof plan: `unfold KzOpC`, then discharge the eight rows with
`IsRealMap.add`, `IsRealMap.smul_real` (side goals `c.im = 0` closed by `simp`),
`IsRealMap.comp`, `IsRealMap.sum` (rows are sums over `Finset.univ`) and the atoms
`IsRealMap.annC`, `IsRealMap.creC`, `isRealMap_annOfE`, `isRealMap_creOfE`,
`isRealMap_nOpC`, `isRealMap_nPlusC`, `IsRealMap.id`, `hBNH`; the four named rows
`KzBogC`, `linOpTC`, `Q2exC`, `Q3TC` can be handled by the same means after
`unfold`ing them (`linOpTC`, `Q2exC`, `Q3TC` use `Work.BoseFixR.KzEnvAt E ρ`).

Note on the implementation: the scalar side goals `((r : ℝ) : ℂ).im = 0` are closed by the
dedicated closure lemma `IsRealMap.ofReal_smul` of `CFockReal.lean` (which packages
`IsRealMap.smul_real` together with `Complex.ofReal_im`); plain `simp` does not see through
the coercions in the compound real coefficients (`Complex.ofReal_div` leaves a complex
division, and `Complex.div_im` is not a simp lemma). -/
theorem KzOpC_real {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ)
    (hBNH : Work.BoseBoxFock.IsRealMap BNH) :
    Work.BoseBoxFock.IsRealMap (Work.BoseBoxFock.KzOpC f g BNH F E gHat0 ρ) := by
  -- FS `eq:BogHamPositive-1` (the Bogoliubov row): a sum over `Mode` whose summand is a
  -- real multiple of a sum of `IsRealMap` operators.
  have hKzBogC : IsRealMap (KzBogC f E ρ) := by
    unfold KzBogC
    refine IsRealMap.sum _ _ (fun k _ => ?_)
    refine IsRealMap.ofReal_smul ?_
    refine IsRealMap.add (IsRealMap.add ?_ ?_) ?_
    · exact IsRealMap.ofReal_smul (IsRealMap.add (isRealMap_nOpC (f k)) (isRealMap_nOpC (f (-k))))
    · exact IsRealMap.ofReal_smul (IsRealMap.add
        (IsRealMap.comp (isRealMap_annOfE (f k)) (isRealMap_annOfE (f (-k))))
        (IsRealMap.comp (isRealMap_creOfE (f k)) (isRealMap_creOfE (f (-k)))))
    · exact IsRealMap.ofReal_smul (IsRealMap.add (IsRealMap.add (IsRealMap.add
        (isRealMap_annOfE (f k)) (isRealMap_creOfE (f k))) (isRealMap_annOfE (f (-k))))
        (isRealMap_creOfE (f (-k))))
  -- FS's linear term `TildeData.linOpT` on the spectator space.
  have hLin : IsRealMap (linOpTC g (Work.BoseFixR.KzEnvAt E ρ)) := by
    unfold linOpTC
    refine IsRealMap.ofReal_smul ?_
    refine IsRealMap.sum _ _ (fun s _ => ?_)
    exact IsRealMap.ofReal_smul (IsRealMap.add (isRealMap_creOfE (g s)) (isRealMap_annOfE (g s)))
  -- FS's `𝒬₂^{ex}` on the spectator space.
  have hQ2 : IsRealMap (Q2exC f (Work.BoseFixR.KzEnvAt E ρ)) := by
    unfold Q2exC
    refine IsRealMap.sum _ _ (fun k _ => ?_)
    exact IsRealMap.ofReal_smul (isRealMap_nOpC (f k))
  -- FS `eq:kroelleQ3z` (`TildeData.Q3T`) on the spectator space.
  have hQ3 : IsRealMap (Q3TC f g F (Work.BoseFixR.KzEnvAt E ρ)) := by
    unfold Q3TC
    refine IsRealMap.ofReal_smul ?_
    refine IsRealMap.sum _ _ (fun s _ => ?_)
    refine IsRealMap.sum _ _ (fun k _ => ?_)
    exact IsRealMap.ofReal_smul (IsRealMap.add
      (IsRealMap.comp (isRealMap_creOfE (g s))
        (IsRealMap.comp (isRealMap_annOfE (f (s - k))) (isRealMap_annOfE (f k))))
      (IsRealMap.comp (isRealMap_creOfE (f k))
        (IsRealMap.comp (isRealMap_creOfE (f (s - k))) (isRealMap_annOfE (g s)))))
  -- The eight rows of `KzOpC`, assembled left to right.
  unfold KzOpC
  refine IsRealMap.add (IsRealMap.add (IsRealMap.add (IsRealMap.add (IsRealMap.add (IsRealMap.add
    (IsRealMap.add ?_ ?_) ?_) hKzBogC) ?_) ?_) ?_) ?_
  · exact IsRealMap.ofReal_smul isRealMap_nPlusC
  · exact IsRealMap.ofReal_smul hBNH
  · exact IsRealMap.ofReal_smul IsRealMap.id
  · exact IsRealMap.ofReal_smul (IsRealMap.sum _ _ (fun k _ => isRealMap_nOpC (f k)))
  · exact hLin
  · exact hQ2
  · exact hQ3

end Work.BoseBoxFock
