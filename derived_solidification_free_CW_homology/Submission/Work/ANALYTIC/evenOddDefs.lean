import Mathlib
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.ZS.Unred.LCZ

/-!
# The even/odd test element of `∏^bnd ℤ` over `ℕ∪{∞}`, and the map `σ`

The goal `Work.ANALYTIC.evenOdd_mem_range` asks whether the element
`y_m(s) = [m even]·[s = m]` of `∏^bnd ℤ(ℕ∪{∞})` lies in the image of
`cBounded(ℕ∪{∞}) : P(ℕ∪{∞}) ⟶ ∏^bnd ℤ(ℕ∪{∞})`.

The witness is the class of `[id] − [σ]`, where `σ : ℕ∪{∞} ⟶ ℕ∪{∞}` fixes the odd points and sends
the even points (and `∞`) to `∞`.  Indeed `cBounded` sends the class of a map `g : S ⟶ ℕ∪{∞}` to
the family `m ↦ 1_{g⁻¹(m)}`, so the `m`-th component of `cBounded([id] − [σ])` is
`s ↦ [s = m] − [σ s = m] = [s = m]·[m even]`, which is `y_m`.

This file provides

* the map `σ` (`evenOddSigma`), its continuity, and its values;
* the pointwise identity `deltaFun m s - deltaFun m (σ s) = [m even]·deltaFun m s`;
* the general computation `cBounded(S)(P_proj(S)([g])) = E_g` for `g : S ⟶ ℕ∪{∞}`, i.e. that
  `cBounded` sends the class of `g` to the family `m ↦ 1_{g⁻¹(m)}`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- The map `σ : ℕ∪{∞} ⟶ ℕ∪{∞}` fixing the odd points (`σ(2k+1) = 2k+1`) and sending the even
points and `∞` to `∞`. -/
def evenOddSigmaFun (s : OnePoint ℕ) : OnePoint ℕ :=
  match s with
  | ∞ => ∞
  | OnePoint.some n => if n % 2 = 0 then ∞ else OnePoint.some n

@[simp] theorem evenOddSigmaFun_infty : evenOddSigmaFun ∞ = ∞ := rfl

@[simp] theorem evenOddSigmaFun_some (n : ℕ) :
    evenOddSigmaFun (OnePoint.some n) =
      if n % 2 = 0 then ∞ else OnePoint.some n := rfl

/-- The fibre of `σ` over a finite point: `{2k+1}` for `n = 2k+1` odd and empty for `n` even. -/
theorem evenOddSigmaFun_preimage (n : ℕ) :
    evenOddSigmaFun ⁻¹' {OnePoint.some n} =
      if n % 2 = 0 then ∅ else {OnePoint.some n} := by
  refine Set.ext ?_
  rw [OnePoint.forall]
  constructor
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, evenOddSigmaFun_infty]
    by_cases hn : n % 2 = 0
    · rw [if_pos hn, Set.mem_empty_iff_false]
      exact ⟨fun h => absurd h.symm (OnePoint.coe_ne_infty n), False.elim⟩
    · rw [if_neg hn, Set.mem_singleton_iff]
  · intro k
    simp only [Set.mem_preimage, Set.mem_singleton_iff, evenOddSigmaFun_some]
    by_cases hk : k % 2 = 0
    · rw [if_pos hk]
      by_cases hn : n % 2 = 0
      · rw [if_pos hn, Set.mem_empty_iff_false]
        exact ⟨fun h => absurd h.symm (OnePoint.coe_ne_infty n), False.elim⟩
      · rw [if_neg hn, Set.mem_singleton_iff]
        refine ⟨fun h => absurd h.symm (OnePoint.coe_ne_infty n), fun h => ?_⟩
        exact absurd (show n % 2 = 0 from OnePoint.coe_eq_coe.mp h ▸ hk) hn
    · rw [if_neg hk]
      by_cases hn : n % 2 = 0
      · rw [if_pos hn, Set.mem_empty_iff_false]
        refine ⟨fun h => ?_, False.elim⟩
        exact hk (show k % 2 = 0 from OnePoint.coe_eq_coe.mp h ▸ hn)
      · rw [if_neg hn, Set.mem_singleton_iff, OnePoint.coe_eq_coe]

/-- The map `σ : ℕ∪{∞} ⟶ ℕ∪{∞}` is continuous: its fibres over finite points are `{2k+1}` or
empty, and both are clopen. -/
theorem continuous_evenOddSigmaFun : Continuous evenOddSigmaFun := by
  rw [Work.ATOM.continuous_onePoint_iff_isClopen]
  intro n
  rw [evenOddSigmaFun_preimage n]
  split_ifs
  · exact isClopen_empty
  · exact Work.ATOM.isClopen_singleton_some n

/-- The morphism `σ : ℕ∪{∞} ⟶ ℕ∪{∞}` of light profinite sets. -/
def evenOddSigma :
    LightProfinite.NatUnionInfty ⟶ LightProfinite.NatUnionInfty :=
  ConcreteCategory.ofHom ⟨evenOddSigmaFun, continuous_evenOddSigmaFun⟩

@[simp] theorem evenOddSigma_apply (s : ↥(LightProfinite.NatUnionInfty).toTop) :
    (ConcreteCategory.hom evenOddSigma) s = evenOddSigmaFun s := rfl

@[simp] theorem evenOddSigma_apply_some (n : ℕ) :
    (ConcreteCategory.hom evenOddSigma) (OnePoint.some n) =
      if n % 2 = 0 then ∞ else OnePoint.some n := rfl

/-- **The pointwise identity behind the even/odd construction.**  Since `σ` fixes the odd points and
sends the even points to `∞`, the difference of the corresponding two basis elements is the even
part: `δ_m(s) − δ_m(σ s) = [m even]·δ_m(s)`. -/
theorem deltaFun_sub_evenOddSigma (m : ℕ) (s : OnePoint ℕ) :
    deltaFun m s - deltaFun m (evenOddSigmaFun s) =
      (if m % 2 = 0 then (1 : ℤ) else 0) * deltaFun m s := by
  refine OnePoint.rec ?_ (fun k => ?_) s
  · rw [evenOddSigmaFun_infty, sub_self, deltaFun_infty, mul_zero]
  · rw [evenOddSigmaFun_some]
    by_cases hk : k % 2 = 0
    · rw [if_pos hk, deltaFun_infty, sub_zero]
      by_cases hm : m % 2 = 0
      · rw [if_pos hm, one_mul]
      · rw [if_neg hm, zero_mul]
        rw [deltaFun_eq, if_neg]
        intro h
        exact hm (OnePoint.coe_eq_coe.mp h.symm ▸ hk)
    · rw [if_neg hk, sub_self]
      by_cases hm : m % 2 = 0
      · rw [if_pos hm, one_mul, deltaFun_eq, if_neg]
        intro h
        exact hk (OnePoint.coe_eq_coe.mp h.symm ▸ hm)
      · rw [if_neg hm, zero_mul]

/-! ## `cBounded` on the class of a single map -/

/-- **`cBounded` sends the class of `g : S ⟶ ℕ∪{∞}` to the family `m ↦ 1_{g⁻¹(m)}`.**
Here `[g] = homFreeEquiv S ℤ[ℕ∪{∞}] (ℤ[g])` is the image of `g` in `ℤ[ℕ∪{∞}](S)`. -/
theorem cBounded_homFreeEquiv_zmap (T : LightProfinite.{0})
    (g : T ⟶ LightProfinite.NatUnionInfty) :
    cBounded.hom.app (op T)
        (P_proj.hom.app (op T)
          (freeHomEquiv T (Work.ATOM.zfree LightProfinite.NatUnionInfty) (Work.ATOM.zmap g))) =
      boundedSeq.obj.map g.op deltaElem := by
  rw [← freeHomEquiv_naturality_target T P_proj (Work.ATOM.zmap g)]
  rw [← freeHomEquiv_naturality_target T cBounded (Work.ATOM.zmap g ≫ P_proj)]
  rw [Category.assoc, P_proj_cBounded]
  rw [freeHomEquiv_naturality g boundedSeq ((freeHomEquiv LightProfinite.NatUnionInfty boundedSeq).symm deltaElem)]
  rw [Equiv.apply_symm_apply]

end Work.ANALYTIC

end
