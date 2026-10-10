import Mathlib
import Submission.Work.MotK.TwRuling.ParamVec
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRuling.SdThetaFracTopAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotK.TwRuling

/-!
# The characteristic-two ruling algebra generates the whole function field

`paramR K D h = K[t, z₂, z₃] ⊆ sdA K D h` where `t = RatFunc.X` and `z₂, z₃` are the last two
coordinates of the characteristic-two parametrisation.  This file proves that the fraction field of
`paramR K D h` is all of `sdA K D h = RatFunc ↥(twistFieldTG K D h)`, i.e.

  `Subfield.closure (Set.range (algebraMap ↥(paramR K D h) (sdA K D h))) = ⊤`.

The proof is the same in shape as the characteristic `≠ 2` statement
`Work.MotK.TwRuling.SdThetaFracTop_charNeTwo` (there for `sdR`), but the input is different: in
characteristic `2` the ruling degenerates and the membership `sdY i ∈ T` is deduced from the
*parametrisation identity* `kleinTwR (paramVec) i = sdY i * kleinTwR (paramVec) 0` together with
`kleinTwR (paramVec) 0 ≠ 0`: both `kleinTwR (paramVec) j` are values of a polynomial map at the
point `paramVec`, hence lie in `paramR`, and `sdY i` is their quotient.

The polynomial bookkeeping is done with the algebra map `paramPsi : Fin 3 → sdA K D h` (so that
`(aeval (paramPsi)) (pzVec K j) = paramVec K D h j` for the obvious `pzVec`), which identifies
`paramR` with the range of `MvPolynomial.aeval (paramPsi K D h)`.
-/

/-- The three generators `paramVec 1, paramVec 2, paramVec 3` of `paramR`, as a map out of `Fin 3`
(so that `paramR K D h = (MvPolynomial.aeval (paramPsi K D h)).range`). -/
private noncomputable def paramPsi (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Fin 3 → Work.MotK.TGen.sdA K D h :=
  fun j => ![paramVec K D h 1, paramVec K D h 2, paramVec K D h 3] j

/-- The polynomial point `![0, X₀, X₁, X₂, 1]` whose `aeval (paramPsi K D h)`-image is
`paramVec K D h`. -/
private noncomputable def pzVec (K : Type) [Field K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![(0 : MvPolynomial (Fin 3) K), MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1]

theorem frac_closure_paramR (K : Type) [Field K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hparam : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TwRuling.paramVec K D h) i
        = Work.MotK.TGen.sdY K D h i *
          Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (Work.MotK.TwRuling.paramVec K D h) 0)
    (hne : Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TwRuling.paramVec K D h) 0 ≠ 0) :
    Subfield.closure (Set.range (algebraMap ↥(Work.MotK.TwRuling.paramR K D h)
      (Work.MotK.TGen.sdA K D h))) = ⊤ := by
  set A := Work.MotK.TGen.sdA K D h with hA
  set R := Work.MotK.TwRuling.paramR K D h with hR
  set T : Subfield A := Subfield.closure (Set.range (algebraMap ↥R A)) with hT
  -- `paramR` is the range of `aeval (paramPsi K D h)`
  have hrange :
      (MvPolynomial.aeval (paramPsi K D h) : MvPolynomial (Fin 3) K →ₐ[K] A).range = R := by
    show (MvPolynomial.aeval (paramPsi K D h)).range = _
    rw [MvPolynomial.aeval_range]
    rfl
  have hθ : ∀ p : MvPolynomial (Fin 3) K,
      (MvPolynomial.aeval (paramPsi K D h)) p ∈ R := by
    intro p
    rw [← hrange]
    exact ⟨p, rfl⟩
  -- the parametrisation point is the `aeval`-image of the polynomial point `pzVec K`
  have hQ : ∀ i : Fin 5,
      (MvPolynomial.aeval (paramPsi K D h))
          (Work.MotK.kleinTwR (MvPolynomial.C D.a) (MvPolynomial.C D.b) (MvPolynomial.C h)
            (pzVec K) i)
        = Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (Work.MotK.TwRuling.paramVec K D h) i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
    rcases hi with h | h | h | h | h <;> subst h <;>
      simp only [Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
        Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_add, map_mul, map_pow, map_sub,
        map_neg, map_ofNat, map_zero, map_one, pzVec, paramPsi,
        Work.MotK.TwRuling.paramVec]
  have hmemR : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TwRuling.paramVec K D h) i ∈ R := by
    intro i
    rw [← hQ i]
    exact hθ _
  have hkleinT : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TwRuling.paramVec K D h) i ∈ T := by
    intro i
    rw [hT]
    exact Subfield.subset_closure ⟨⟨_, hmemR i⟩, rfl⟩
  -- the twisted coordinates are quotients of two polynomial values
  have hYmem : ∀ i : Fin 5, Work.MotK.TGen.sdY K D h i ∈ T := by
    intro i
    have heq : Work.MotK.TGen.sdY K D h i
        = Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (Work.MotK.TwRuling.paramVec K D h) i
          / Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (Work.MotK.TwRuling.paramVec K D h) 0 := by
      rw [eq_div_iff hne, hparam i]
    rw [heq]
    exact T.div_mem (hkleinT i) (hkleinT 0)
  -- `RatFunc.X` is one of the generators of `paramR`
  have hXR : (RatFunc.X : A) ∈ R := by
    rw [hR]
    refine Algebra.subset_adjoin ?_
    refine ⟨0, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Work.MotK.TwRuling.paramVec]
  have hXT : (RatFunc.X : A) ∈ T := by
    rw [hT]
    exact Subfield.subset_closure ⟨⟨_, hXR⟩, rfl⟩
  have hKm : ∀ k : K, algebraMap K A k ∈ T := by
    intro k
    rw [hT]
    exact Subfield.subset_closure ⟨⟨algebraMap K A k, R.algebraMap_mem k⟩, rfl⟩
  -- the subfield generated by the constants and the twisted coordinates is contained in `T`
  have hSle : Subfield.closure (Set.range (algebraMap K A)
      ∪ Set.range (Work.MotK.TGen.sdY K D h)) ≤ T := by
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, rfl⟩ := hx
      exact hKm k
    · obtain ⟨i, rfl⟩ := hx
      exact hYmem i
  have hFmem : ∀ a : ↥(Work.MotK.twistFieldTG K D h),
      algebraMap ↥(Work.MotK.twistFieldTG K D h) A a ∈ T := by
    intro a
    exact hSle (range_algebraMap_subset K D h ⟨a, rfl⟩)
  have hle : IntermediateField.adjoin ↥(Work.MotK.twistFieldTG K D h)
      ({(RatFunc.X : A)} : Set A) ≤ T.toIntermediateField hFmem := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hXT
  have htop : T.toIntermediateField hFmem = ⊤ :=
    le_antisymm le_top (by
      rw [← RatFunc.adjoin_X (K := ↥(Work.MotK.twistFieldTG K D h))]
      exact hle)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (T.toIntermediateField hFmem) := by
    rw [htop]
    simp
  exact hx

end Work.MotK.TwRuling
