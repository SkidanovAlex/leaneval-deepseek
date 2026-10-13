import Mathlib
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.ReductEmb

namespace Work.WilC5.S4ExpF

theorem logFun_eq_zero_of_not_pos {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (x : K) (hx : ¬ 0 < x) :
    Work.WilC5.logFun x = 0 := by
  -- In field terms `¬ 0 < x` says the *definable* positivity predicate fails at `x`.
  have hx' : ¬ (Work.WilC5.leE (Work.WilC5.zeroE : K) x ∧
      ¬ Work.WilC5.leE x Work.WilC5.zeroE) :=
    fun h => hx ((Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg x).mp h)
  -- `logDefSet x ·` has a unique solution in a model of `TE`.
  obtain ⟨y, _hy, huniq⟩ := Work.WilC5.LogDefSetModel hTE x
  -- `exp 0 = 1`, so the second clause of `logDefSet` is satisfied at `y = 0`.
  have h0 : Work.WilC5.expE (Work.WilC5.zeroE : K) = Work.WilC5.oneE :=
    Work.WilC5.S4ExpF.expE_zeroE_of_model hTE
  have hz : Work.WilC5.logDefSet x (Work.WilC5.zeroE : K) := Or.inr ⟨hx', h0⟩
  have hex : ∃ y, Work.WilC5.logDefSet x y := ⟨_, hz⟩
  -- `logFun` selects the unique solution, which is `zeroE`, and `zeroE = 0`.
  unfold Work.WilC5.logFun
  rw [dite_eq_left hex]
  have h1 : Classical.choose hex = y := huniq _ (Classical.choose_spec hex)
  have h2 : (Work.WilC5.zeroE : K) = y := huniq _ hz
  rw [h1, ← h2, Work.WilC5.S4ExpF.zeroE_eq_zero hTE hadd]

end Work.WilC5.S4ExpF
