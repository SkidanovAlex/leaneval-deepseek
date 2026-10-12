import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.K2ndEval` — evaluation lemmas for the `c`-number dictionary

Small, mechanical facts about the data of `Work.BoseB4.K2ndDefs` that make the
final assembly of FS `thm:Kafz` for `eq:HLambdaSecond` a rewrite:

* the nine slots of `Kexp` evaluated at the `Fin 9` numerals (so that
  `monoOp (Kpvec i) (Kqvec i) (Kvec D i)` unfolds in a sum over `Fin 9`);
* `K2ndC` presented in the exact `Finset` form consumed by
  `Work.BoseB4.Kafz_sum` / `Work.BoseB4.Kafz_lattice`
  (`s = Finset.univ`, `p = Kpvec`, `q = Kqvec`, `B = Kvec D`);
* `K2ndSym` in *pointwise* form, by `Work.BoseB4.sum_symbol_apply`;
* `H2nd` split into its ten named pieces pointwise.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The exponent vector -/

@[simp] lemma Kpvec_0 : Kpvec 0 = 0 := by decide
@[simp] lemma Kqvec_0 : Kqvec 0 = 0 := by decide
@[simp] lemma Kpvec_1 : Kpvec 1 = 1 := by decide
@[simp] lemma Kqvec_1 : Kqvec 1 = 1 := by decide
@[simp] lemma Kpvec_2 : Kpvec 2 = 2 := by decide
@[simp] lemma Kqvec_2 : Kqvec 2 = 2 := by decide
@[simp] lemma Kpvec_3 : Kpvec 3 = 2 := by decide
@[simp] lemma Kqvec_3 : Kqvec 3 = 0 := by decide
@[simp] lemma Kpvec_4 : Kpvec 4 = 0 := by decide
@[simp] lemma Kqvec_4 : Kqvec 4 = 2 := by decide
@[simp] lemma Kpvec_5 : Kpvec 5 = 2 := by decide
@[simp] lemma Kqvec_5 : Kqvec 5 = 1 := by decide
@[simp] lemma Kpvec_6 : Kpvec 6 = 1 := by decide
@[simp] lemma Kqvec_6 : Kqvec 6 = 0 := by decide
@[simp] lemma Kpvec_7 : Kpvec 7 = 1 := by decide
@[simp] lemma Kqvec_7 : Kqvec 7 = 2 := by decide
@[simp] lemma Kpvec_8 : Kpvec 8 = 0 := by decide
@[simp] lemma Kqvec_8 : Kqvec 8 = 1 := by decide

/-! ## The slot operators -/

@[simp] lemma Kvec_0 (D : H2ndData m) : Kvec D 0 = K00 D := by simp [Kvec]
@[simp] lemma Kvec_1 (D : H2ndData m) : Kvec D 1 = K11 D := by simp [Kvec]
@[simp] lemma Kvec_2 (D : H2ndData m) : Kvec D 2 = K22 D := by simp [Kvec]
@[simp] lemma Kvec_3 (D : H2ndData m) : Kvec D 3 = K20 D := by simp [Kvec]
@[simp] lemma Kvec_4 (D : H2ndData m) : Kvec D 4 = K02 D := by simp [Kvec]
@[simp] lemma Kvec_5 (D : H2ndData m) : Kvec D 5 = K21 D := by simp [Kvec]
@[simp] lemma Kvec_6 (D : H2ndData m) : Kvec D 6 = K10 D := by simp [Kvec]
@[simp] lemma Kvec_7 (D : H2ndData m) : Kvec D 7 = K12 D := by simp [Kvec]
@[simp] lemma Kvec_8 (D : H2ndData m) : Kvec D 8 = K01 D := by simp [Kvec]

/-- The condensate mode is not an excited mode. -/
@[simp] lemma exc_zero_notMem : (0 : Fin m) ∉ exc m := by simp [exc]

/-! ## The two packaged forms -/

/-- `K2ndC` in the `Finset` form consumed by the `c`-number substitution
(`s = Finset.univ`, `p = Kpvec`, `q = Kqvec`, `B = Kvec D`). -/
theorem K2ndC_eq_sum (D : H2ndData m) :
    K2ndC D = ∑ i ∈ (Finset.univ : Finset (Fin 9)),
        monoOp (Kpvec i) (Kqvec i) (Kvec D i) :=
  rfl

/-- Pointwise form of the symbol `𝓚(z)` of `eq:HLambdaSecond`. -/
theorem K2ndSym_apply (D : H2ndData m) (z : ℂ) (v : cfock (Excited m)) :
    K2ndSym D z v
      = ∑ i : Fin 9, (z ^ (Kpvec i) * (starRingEnd ℂ z) ^ (Kqvec i)) • (Kvec D i v) := by
  rw [K2ndSym]
  exact sum_symbol_apply Finset.univ _ _ _ z v

/-! ## The ten pieces of `eq:HLambdaSecond`, pointwise -/

/-- `H2nd` split into its ten named pieces, pointwise. -/
theorem H2nd_apply (D : H2ndData m) (x : RealFock m) :
    H2nd D x = Hkin D x + Hgap D x + HgapH D x + Hcontact D x + Hmu D x + HW D x
      + Hbog D x + Hchi D x + HchiOm D x + Hnn D x := by
  simp only [H2nd, LinearMap.add_apply]

end Work.BoseB4
