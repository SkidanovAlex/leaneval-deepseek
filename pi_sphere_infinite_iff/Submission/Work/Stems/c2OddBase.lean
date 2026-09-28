import Mathlib
import Submission.Work.Stems.c2FreeClauses
import Submission.Work.Serre.C1SphOneMap
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.Serre.attachIncl_const_piMapN_bijective
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Serre.Models
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

/-!
# The base level of the free-top `C2` odd interface

*(Area STEMS.  See `Submission/Work/Stems/c2FreeClauses.lean`, `C2ODD_STEP_STATE.md` §4.3.)*

`Work.Stems.OddClause c 1 N` is the level-`1` clause of `Work.Stems.Engine.C2oddFree c`: a range
model of `K(ℤ,1)` through degree `N` has `H_1(−;ℚ) ≅ ℚ` and vanishing rational homology in the
other degrees `0 < d < N - c`.

* `Work.Stems.bottomCellOne` is the `n = 1` case of
  `Work.RatHurewicz.exists_bijective_piMapN_rangeModel`: a range model of `K(ℤ,1)` through `N` has a
  based map `S¹ → X` inducing a *bijection* on `π₁`.  It is an immediate consequence of
  `Work.Serre.exists_sphOne_map_piMap_bijective` (`Serre/C1SphOneMap.lean`), because the homotopy
  groups of the sphere are cyclic by definition: `π₁(X,pt) ≅* ℤ` is exactly the hypothesis there.
* `Work.Stems.oddClauseOne` turns that map into the level-`1` clause: with a `π₁`-bijection
  `f : S¹ → X` in hand, the `π`-isomorphism theorem in range form
  (`Work.StemsB.comparisons_ratH_iso`, the sharp Whitehead theorem `serreK2IntSharp`) gives
  `H_i(X;ℚ) ≅ H_i(S¹;ℚ)` for `i ≤ N`, and the rational homology of the circle is
  `Work.StemsB.sphRatHomology`.  No degree is lost, so the clause holds with the sharp bound
  `d ≤ N`.

The two statements are unconditional in the parameter `c` of the interface: the level-`1` clause is
*independent of `c`* except through the trivial comparison `d < N - c ⟹ d ≤ N`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The bottom cell of a range model of `K(ℤ,1)`**: a based map `S¹ → X` inducing a bijection on
`π₁`.  The `n = 1` case of `Work.RatHurewicz.exists_bijective_piMapN_rangeModel`; it is *not* a
consequence of that theorem (`2 ≤ n` there), but it follows directly from
`Work.Serre.exists_sphOne_map_piMap_bijective`, whose hypothesis `π₁(X,pt) ≅* ℤ` is exactly the first
conjunct of the range-model hypothesis. -/
theorem bottomCellOne (X : Type) [TopologicalSpace X] (pt : X) (N : ℕ)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N X pt) :
    ∃ (s₀ : Work.Serre.Sph 1) (f : C(Work.Serre.Sph 1, X)),
      f s₀ = pt ∧ Function.Bijective (Work.Serre.piMapN f 1 s₀) := by
  obtain ⟨φ, hφ, hbij⟩ := Work.Serre.exists_sphOne_map_piMap_bijective X pt hX.1.some
  exact ⟨Work.Serre.sphOneBase, φ, hφ,
    (Work.Serre.piMapN_eq_pimap_succ φ 0 Work.Serre.sphOneBase).symm ▸ hbij⟩

/-- **The level-`1` clause of the odd interface.**  For a range model of `K(ℤ,1)` through `N`, and
any based map `S¹ → X` which is a bijection on `π₁`, the rational homology of `X` is that of `S¹`
in all degrees `≤ N`: `H_1(−;ℚ) ≅ ℚ` and `H_d(−;ℚ) = 0` for `0 < d ≤ N`, `d ≠ 1`. -/
theorem oddClauseOne (X : Type) [TopologicalSpace X] (pt : X) (N : ℕ)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N X pt)
    (hcell : ∃ (s₀ : Work.Serre.Sph 1) (f : C(Work.Serre.Sph 1, X)),
      f s₀ = pt ∧ Function.Bijective (Work.Serre.piMapN f 1 s₀)) :
    Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ) ∧
    (∀ d : ℕ, 0 < d → d ≤ N → d ≠ 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) d)) := by
  obtain ⟨s₀, f, -, hbij⟩ := hcell
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inl (by omega)))
  haveI hpcS : PathConnectedSpace (Work.Serre.Sph 1) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero s₀
      (Work.Stems.sphereConnectivity 1 0 (by omega) s₀)
  haveI hZerothX : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp hpcX |>.2
  haveI hZerothS : Subsingleton (ZerothHomotopy (Work.Serre.Sph 1)) :=
    (pathConnectedSpace_iff_zerothHomotopy (X := Work.Serre.Sph 1)).mp hpcS |>.2
  have hpi0X : ∀ y : X, Subsingleton (HomotopyGroup (Fin 0) X y) := fun y =>
    ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := y)).injective
      (Subsingleton.elim _ _)⟩
  have hpi0S : ∀ y : Work.Serre.Sph 1,
      Subsingleton (HomotopyGroup (Fin 0) (Work.Serre.Sph 1) y) := fun y =>
    ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Work.Serre.Sph 1)
      (x := y)).injective (Subsingleton.elim _ _)⟩
  -- the map `f` is a `π`-isomorphism in every degree `≤ max N 1`
  have hg : ∀ i : ℕ, i ≤ max N 1 → ∀ y : Work.Serre.Sph 1,
      Function.Bijective (Work.Serre.piMapN f i y) := by
    intro i hi y
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · haveI := hpi0S y
      haveI := hpi0X (f y)
      exact ⟨fun a b _ => Subsingleton.elim a b, fun z => ⟨default, Subsingleton.elim _ _⟩⟩
    · rcases eq_or_lt_of_le (show 1 ≤ i from hipos) with h1 | h2
      · subst h1
        exact Work.Serre.bijective_piMapN_of_joined f (hpcS.joined s₀ y) 1 hbij
      · haveI := Work.Serre.sphOneAspherical i h2 y
        haveI : Subsingleton (HomotopyGroup (Fin i) X (f y)) :=
          Work.Stems.subsingleton_homotopyGroup_change_basepoint
            (PathConnectedSpace.joined pt (f y)).some
            (hX.2 i (by omega) (Or.inr (by omega)))
        exact ⟨fun a b _ => Subsingleton.elim a b,
          fun z => ⟨default, Subsingleton.elim _ _⟩⟩
  have hcid : ∀ i : ℕ, i ≤ max N 1 → ∀ y : Work.Serre.Sph 1,
      Function.Bijective (Work.Serre.piMapN (ContinuousMap.id (Work.Serre.Sph 1)) i y) := by
    intro i hi y
    have hfun : Work.Serre.piMapN (ContinuousMap.id (Work.Serre.Sph 1)) i y
        = id := by
      funext a
      exact Work.Serre.piMapN_id i y a
    rw [hfun]
    exact Function.bijective_id
  obtain ⟨hcomp, -⟩ := Work.StemsB.comparisons_ratH_iso (N := max N 1) (Z := X)
    (P := Work.Serre.Sph 1) s₀ f (ContinuousMap.id (Work.Serre.Sph 1)) hg hcid
  constructor
  · obtain ⟨e⟩ := hcomp 1 (by omega)
    exact ⟨e.symm ≪≫ (Work.StemsB.sphRatHomology 1 (by norm_num)).1.some⟩
  · intro d hd0 hdN hdn
    obtain ⟨e⟩ := hcomp d (by omega)
    exact IsZero.of_iso ((Work.StemsB.sphRatHomology 1 (by norm_num)).2 d (by omega) (by omega))
      e.symm

end

end Work.Stems
