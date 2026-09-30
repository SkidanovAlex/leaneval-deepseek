import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Serre.serreK2Int
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.Serre.C1SphOne
import Submission.Work.Serre.C1SphOneMap
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.EMFG.defs
import Submission.Work.EMFG.basic
import Submission.Work.EMFG.torusFGandEM
import Submission.Work.EMFG.torusProdFG
import Submission.Work.EMFG.finiteAbelianModelFG
import Submission.Work.EMFG.kOneComparison
import Submission.Work.StemsB.fg_abelian_decomposition

/-!
# EMFG — the integral homology of range models of `K(A,m)` is finitely generated

Target: `Work.EMFG.emHomologyFG`, i.e. `Work.PiS.EMHomologyFG` from `Work.PiS.SerreFGThreeForTwo`:
every range model `X` of `K(A,m)` (`A` finitely generated, `m ≥ 2`) through degree `N+1` has
`H_i(X;ℤ)` finitely generated for `i ≤ N`.

## Architecture of the proof

* `EMOne A` — the `m = 1` case: every range model of `K(A,1)` through `N` (with `A` f.g.) has
  f.g. integral homology in the range.
* `P m` — the `m`-th case (range form).
* `P m` from `EMOne` (for `m = 2`) and `P (m-1)` from `P m` (for `m ≥ 3`): the **path–loop
  fibration** `ΩX → PX → X` (Serre fibration with contractible total space), the loop shift of
  `Work.Stems.isEMSpaceUpTo_loop'`, and direction 2 of the Serre spectral sequence
  (`SerreFGThreeForTwo`: base from total and fibre).

The mathematical substance that is *not* in the seed is the `m = 1` case `EMOne`, i.e. the integral
homology of range models of `K(A,1)` for f.g. `A`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The `m = 1` case, and the induction predicate

`EMOne A` is the `m = 1` case of the target: every range model of `K(A,1)` through `N` has f.g.
integral homology in the range.  `P m` is the `m`-th case (all range models, arbitrary range).

The whole target reduces to `∀ A (f.g.), EMOne A`:
* `P 2` from `EMOne` (the path–loop fibration of a range model of `K(A,2)` has as fibre a range
  model of `K(A,1)`), and
* `P (m+1)` from `P m` (same argument, with `Work.Stems.isEMSpaceUpTo_loop'`).

The `m = 1` case is where the mathematical substance lies: nothing in the workspace compares two
range models of `K(A,1)` (the comparison `Work.StemsB.rangeModel_ratH_iso` needs `2 ≤ k`, since the
CW model tower `Work.Serre.CWModel.towerA` needs a *simply connected* target).
-/

namespace Work.EMFG

/-- `H_*(S¹;ℤ)` is finitely generated in every degree. -/
theorem fgUpTo_sphOne (N : ℕ) : Work.PiS.FGUpTo (Work.Serre.Sph 1) N := by
  intro i _
  haveI : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact h0 ▸ fgUpTo_zero_of_pathConnected _ 0 le_rfl
  · rcases Nat.eq_or_lt_of_le (show 1 ≤ i from hpos) with h1 | h2
    · subst h1
      obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop 1 (by norm_num)
      exact Module.Finite.equiv e.symm.toLinearEquiv
    · have hz : CategoryTheory.Limits.IsZero (Work.PiS.HZ (Work.Serre.Sph 1) i) :=
        Work.Cohomology.sphereHomologyZero 1 i (by norm_num) (by omega) (by omega)
      exact Work.ThomBordism.fgch_moduleFinite_of_isZero
        (M := Work.PiS.HZ (Work.Serre.Sph 1) i) hz

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The `m = 2` case of `K(ℤ,1)`: the circle comparison

For `A = ℤ` the `m = 1` case is easy: a range model `X` of `K(ℤ,1)` through `N` receives a map
from the circle inducing an isomorphism on `π₁` (`Work.Serre.exists_sphOne_map_piMap_bijective`),
the circle is aspherical (`Work.Serre.sphOneAspherical`), so the map is a `π`-isomorphism in
degrees `≤ N-1` and `serreK2IntSharp` transfers the (finitely generated) homology of `S¹`. -/

theorem emOne_int : EMOne ℤ := by
  intro N X _ x hX
  have hsub0 : Subsingleton (HomotopyGroup (Fin 0) X x) :=
    hX.2 0 (by norm_num) (Or.inl (by norm_num))
  haveI hXc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hsub0
  haveI hS1c : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
  obtain ⟨e⟩ := hX.1
  obtain ⟨φ, hφ, hφbij⟩ := Work.Serre.exists_sphOne_map_piMap_bijective X x e
  -- the induced map on `πᵢ` is bijective at the base point, for `i < N`
  have hpi0 : ∀ i : ℕ, i < N →
      Function.Bijective (Work.Serre.piMapN φ i (Work.Serre.sphOneBase)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have h1 : Subsingleton
          (HomotopyGroup (Fin 0) (Work.Serre.Sph 1) (Work.Serre.sphOneBase)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Work.Serre.Sph 1)
          (x := Work.Serre.sphOneBase)).injective.subsingleton
      have h2 : Subsingleton (HomotopyGroup (Fin 0) X (φ Work.Serre.sphOneBase)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := X)
          (x := φ Work.Serre.sphOneBase)).injective.subsingleton
      exact ⟨fun a b _ => h1.elim a b, fun b => ⟨default, h2.elim _ _⟩⟩
    · rcases Nat.eq_or_lt_of_le (show 1 ≤ i from hpos) with h1 | h2
      · subst h1
        exact hφbij
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have h1 : Subsingleton
            (HomotopyGroup (Fin (k + 1)) (Work.Serre.Sph 1) (Work.Serre.sphOneBase)) :=
          Work.Serre.sphOneAspherical (k + 1) (by omega) _
        have h2 : Subsingleton (HomotopyGroup (Fin (k + 1)) X (φ Work.Serre.sphOneBase)) :=
          Work.Serre.subsingleton_homotopyGroup_of_joined
            (PathConnectedSpace.joined x (φ Work.Serre.sphOneBase)) k
            (by
              have hne : k + 1 ≠ 1 := by omega
              have := hX.2 (k + 1) hne (Or.inr (by omega))
              exact this)
        exact ⟨fun a b _ => h1.elim a b, fun b => ⟨default, h2.elim _ _⟩⟩
  have hpi : ∀ i : ℕ, i < N → ∀ y : Work.Serre.Sph 1,
      Function.Bijective (Work.Serre.piMapN φ i y) := fun i hi y =>
    Work.Serre.bijective_piMapN_of_joined φ (PathConnectedSpace.joined _ y) i (hpi0 i hi)
  -- the homology transfer
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact h0 ▸ fgUpTo_zero_of_pathConnected X 0 le_rfl
  · have hir : i < N := by omega
    have hiso : IsIso (Work.Serre.intHomologyMap φ i) :=
      Work.Serre.Assembly.serreK2IntSharp φ N hpi i hpos hir
    exact fg_of_homology_iso (asIso (Work.Serre.intHomologyMap φ i))
      (fgUpTo_sphOne (N - 1) i hi)

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The path–loop induction

The path–loop fibration `ΩX → PX → X` (total space contractible, fibre `ΩX` the loop space) with
direction 2 of the Serre spectral sequence (`SerreFGThreeForTwo`) upgrades "the homology of the
loop space is f.g." to "the homology of `X` is f.g.":

* `Work.Stems.isEMSpaceUpTo_loop'` says that the loop space of a range model of `K(A,m)` through
  `N` is a range model of `K(A,m-1)` through `N-1`;
* `Work.StemsB.fibreEvalOneHomeo` identifies the strict fibre of `Work.StemsB.evalOne` with the
  loop space `Path x x`, and `Work.StemsB.contractible_pathSpace` makes the total space's homology
  finitely generated in every degree (`fgUpTo_of_contractible`). -/

/-- **The path–loop step.**  `P m` follows from the `(m-1)`-st case (for all range models). -/
theorem P_of_loop (hSSS : Work.PiS.SerreFGThreeForTwo) (m : ℕ) (hm : 2 ≤ m)
    (h : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (N : ℕ) (Y : Type) [TopologicalSpace Y]
      (y : Y), Work.Serre.IsEMSpaceUpTo A (m - 1) (by omega) N Y y →
        Work.PiS.FGUpTo Y (N - 1)) :
    P m hm := by
  intro A _ _ N X _ x hX
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- the range is too small to use the fibration: `X` is path connected, so `H₀` is f.g.
    have hsub0 : Subsingleton (HomotopyGroup (Fin 0) X x) :=
      hX.2 0 (by omega) (Or.inr (by omega))
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hsub0
    exact FGUpTo.mono (fgUpTo_zero_of_pathConnected X) (by omega)
  · -- the loop space `ΩX` is a range model of `K(A,m-1)` through `N-1`
    have hΩ : Work.Serre.IsEMSpaceUpTo A (m - 1) (by omega) (N - 1) (Path x x)
        (Path.refl x) :=
      Work.Stems.isEMSpaceUpTo_loop' (A := A) (m := m) (M := N) hm x hX
    have hloop : Work.PiS.FGUpTo (Path x x) (N - 2) := by
      have h' := h (A := A) (N := N - 1) (Y := Path x x) (y := Path.refl x) hΩ
      simpa [Nat.sub_sub] using h'
    -- transport to the strict fibre of the path–loop fibration
    have hfib : Work.PiS.FGUpTo (Work.StemsB.fibre (Work.StemsB.evalOne X x) x) (N - 2) :=
      fgUpTo_of_homeomorph (Work.StemsB.fibreEvalOneHomeo X x).symm hloop
    -- the total space is contractible
    have hE : Work.PiS.FGUpTo (Work.StemsB.PathSpace X x) (N - 2 + 1) := by
      haveI : ContractibleSpace (Work.StemsB.PathSpace X x) :=
        Work.StemsB.contractible_pathSpace X x
      exact fgUpTo_of_contractible _ _
    have hsc : Work.PiS.SimplyConn X x :=
      ⟨hX.2 0 (by omega) (Or.inr (by omega)), hX.2 1 (by omega) (Or.inr (by omega))⟩
    have hbase := (hSSS (Work.StemsB.PathSpace X x) X (Work.StemsB.evalOne X x)
      (Work.StemsB.constPath X x) (Work.StemsB.isSerreFibration_evalOne X x) hsc).2.1
    have hres := hbase (N - 2) hE hfib
    simpa [show N - 2 + 1 = N - 1 by omega] using hres

/-- **`P 2` from the `m = 1` case.** -/
theorem P_two_of_EMOne (hSSS : Work.PiS.SerreFGThreeForTwo)
    (h1 : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A) :
    P 2 (by norm_num) := by
  intro A _ _ N X _ x hX
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hsub0 : Subsingleton (HomotopyGroup (Fin 0) X x) :=
      hX.2 0 (by norm_num) (Or.inr (by omega))
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hsub0
    exact FGUpTo.mono (fgUpTo_zero_of_pathConnected X) (by omega)
  · have hΩ : Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) (N - 1) (Path x x) (Path.refl x) := by
      have h' := Work.Stems.isEMSpaceUpTo_loop' (A := A) (m := 2) (M := N) (by norm_num) x hX
      simpa using h'
    have hloop : Work.PiS.FGUpTo (Path x x) (N - 2) := by
      have h' := h1 A (N - 1) (Path x x) (Path.refl x) hΩ
      simpa [Nat.sub_sub] using h'
    have hfib : Work.PiS.FGUpTo (Work.StemsB.fibre (Work.StemsB.evalOne X x) x) (N - 2) :=
      fgUpTo_of_homeomorph (Work.StemsB.fibreEvalOneHomeo X x).symm hloop
    have hE : Work.PiS.FGUpTo (Work.StemsB.PathSpace X x) (N - 2 + 1) := by
      haveI : ContractibleSpace (Work.StemsB.PathSpace X x) :=
        Work.StemsB.contractible_pathSpace X x
      exact fgUpTo_of_contractible _ _
    have hsc : Work.PiS.SimplyConn X x :=
      ⟨hX.2 0 (by norm_num) (Or.inr (by omega)), hX.2 1 (by norm_num) (Or.inr (by omega))⟩
    have hbase := (hSSS (Work.StemsB.PathSpace X x) X (Work.StemsB.evalOne X x)
      (Work.StemsB.constPath X x) (Work.StemsB.isSerreFibration_evalOne X x) hsc).2.1
    have hres := hbase (N - 2) hE hfib
    simpa [show N - 2 + 1 = N - 1 by omega] using hres

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Assembly: `EMHomologyFG` from the `m = 1` case -/

/-- `P m` holds for every `m ≥ 2` as soon as the `m = 1` case holds for every finitely generated
`A`. -/
theorem P_all (hSSS : Work.PiS.SerreFGThreeForTwo)
    (h1 : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A) :
    ∀ (m : ℕ) (hm : 2 ≤ m), P m hm := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ k ih =>
    intro hm
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · exact P_two_of_EMOne hSSS h1
    · exact P_of_loop hSSS (k + 1) (by omega) (ih (by omega))

/-- **The target, from the `m = 1` case.** -/
theorem emHomologyFG_of_emOne (hSSS : Work.PiS.SerreFGThreeForTwo)
    (h1 : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A) :
    Work.PiS.EMHomologyFG := by
  intro A _ _ m hm N X _ x hX
  have hP : P m hm := P_all hSSS h1 m hm
  have h' := hP A (N + 1) X x hX
  simpa using h'

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The target, from the `m = 1` case for finitely generated `A`.**

The `m = 1` case (`∀ A [Module.Finite ℤ A], EMOne A`) is the mathematical substance of the chapter:
the homology of range models of `K(A,1)`.  It is delegated to
`Submission/Work/EMFG/emOne.lean` (`Work.EMFG.emOne`). -/
theorem emHomologyFG_of_emOne' (hSSS : Work.PiS.SerreFGThreeForTwo)
    (hemOne : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A) :
    Work.PiS.EMHomologyFG :=
  emHomologyFG_of_emOne hSSS hemOne

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## A model of `K(A,1)` for a finite abelian `A` with finitely generated homology in *all*
degrees

`Work.EMFG.finiteAbelianModelFG` gives, for a finite abelian `A`, a range model of `K(A,1)` through
`N` whose integral homology is finitely generated through degree `N-1`.  For the Künneth theorem
`Work.EMFG.fgUpTo_prod_torus` (`H_*(T^r × Y)` is finitely generated whenever `H_*(Y)` is, in every
degree) we need the stronger statement that the finite model has finitely generated homology in
*every* degree; that is what this section adds.

The model is again the product of the lens spaces `∏ᵢ S^{2N+3}/μ_{nᵢ}` (`A ≃+ ∏ᵢ ZMod nᵢ`):

* it is a range model of `K(A,1)` through `N` by `Work.EMFG.isEMSpaceUpTo_pi` applied to
  `Work.EMFG.lensSpaceEMUpTo`;
* its homology is finitely generated in every degree by the product-of-good-covers lemma
  `Work.EMFG.piGoodFamFG` applied to the good families `Work.EMFG.lens_goodFam` of the lens spaces.

Both halves are proved in `Work.EMFG.finiteAbelianModelFG` for the same space (with `k` fixed); here
the finiteness conclusion is strengthened to all degrees, which `piGoodFamFG` gives directly. -/

/-- **A range model of `K(A,1)` through `N` with finitely generated integral homology in every
degree**, for `A` a finite abelian group. -/
theorem finiteAbelianModelAllDeg (A : Type) [AddCommGroup A] [Fintype A] (N : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (x : X),
      Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N X x ∧
        (∀ k : ℕ, Module.Finite ℤ (Work.PiS.HZ X k)) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨eA⟩⟩ := Work.EMFG.finiteAbelianEqProdZMod A
  letI : Fintype ι := hι
  haveI hnz : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  refine ⟨(i : ι) → Work.RatHurewicz.lensSpace (n i) N, inferInstance,
    fun i => Work.RatHurewicz.lensProj (n i) N (Work.EMFG.lensBasePt N), ?_, ?_⟩
  · have h1 : Work.Serre.IsEMSpaceUpTo ((i : ι) → ZMod (n i)) 1 (by norm_num) N
        ((i : ι) → Work.RatHurewicz.lensSpace (n i) N)
        (fun i => Work.RatHurewicz.lensProj (n i) N (Work.EMFG.lensBasePt N)) :=
      Work.EMFG.isEMSpaceUpTo_pi (by norm_num)
        (fun i => Work.RatHurewicz.lensProj (n i) N (Work.EMFG.lensBasePt N))
        (fun i => Work.EMFG.lensSpaceEMUpTo (n i) N (Work.EMFG.lensBasePt N))
    exact Work.EMFG.isEMSpaceUpTo_congr (Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv
      (by norm_num) _ h1 eA.symm)
  · intro k
    have hL : ∀ i : ι, ∃ (m : ℕ) (x : Fin m → Work.RatHurewicz.lensTotal N) (ε : ℝ),
        0 < ε ∧
        (⋃ j, Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x j) ε) = Set.univ ∧
        Work.ThomBordism.IsGoodFam
          (fun j : Fin m => Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x j) ε) :=
      fun i => Work.EMFG.lens_goodFam (n i) N
    choose m x ε _ hcov hgood using hL
    exact Work.EMFG.piGoodFamFG (fun i (j : Fin (m i)) =>
      Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x i j) (ε i)) hgood hcov k

/-! ## A good range model of `K(A,1)` for finitely generated `A`

For `A` finitely generated abelian write `A ≃+ (Fin r → ℤ) × F` with `F` finite
(`Work.StemsB.fg_abelian_decomposition`).  A range model of `K(A,1)` through `N` is the product

`X = (S¹)^r × Y`,   `Y` a range model of `K(F,1)` through `N`,

which is a range model by `Work.RatHurewicz.isEMSpaceUpTo_prod` (the torus factor is a range model
of `K(ℤ^r,1)` by `Work.EMFG.torusFGandEM`).  For the finiteness of its integral homology we take
for `Y` the product of lens spaces of `Work.EMFG.finiteAbelianModelAllDeg` — whose homology is
finitely generated in *every* degree — and apply the Künneth theorem for the torus factor,
`Work.EMFG.fgUpTo_prod_torus`. -/

/-- **A range model of `K(A,1)` through `N` with finitely generated integral homology through
`N-1`, for `A` finitely generated abelian.** -/
theorem exists_fgRangeModel_one_via (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (N : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (x : X),
      Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N X x ∧ Work.PiS.FGUpTo X (N - 1) := by
  classical
  obtain ⟨r, F, instF, hFin, ⟨eA⟩⟩ := Work.StemsB.fg_abelian_decomposition A
  letI := instF
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨Y, tY, y, hY, hYfg⟩ := finiteAbelianModelAllDeg F N
  letI : TopologicalSpace Y := tY
  refine ⟨(Fin r → Work.Serre.Sph 1) × Y, inferInstance,
    ((fun _ => Work.Serre.sphOneBase), y), ?_, ?_⟩
  · have hT : Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) 1 (by norm_num) N
        (Fin r → Work.Serre.Sph 1) (fun _ => Work.Serre.sphOneBase) :=
      (Work.EMFG.torusFGandEM r).2 N
    have hprod : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) 1 (by norm_num) N
        ((Fin r → Work.Serre.Sph 1) × Y) ((fun _ => Work.Serre.sphOneBase), y) :=
      Work.RatHurewicz.isEMSpaceUpTo_prod (by norm_num : (0 : ℕ) < 1)
        (fun _ => Work.Serre.sphOneBase) y hT hY
    exact Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv (by norm_num : (0 : ℕ) < 1)
      ((fun _ => Work.Serre.sphOneBase), y) hprod eA.symm
  · exact Work.EMFG.fgUpTo_prod_torus hYfg r (N - 1)

/-- **The `m = 1` case of `Work.PiS.EMHomologyFG`.**  Every range model of `K(A,1)` through degree
`N`, with `A` finitely generated abelian, has finitely generated integral homology through degree
`N - 1`.

This is `Work.EMFG.emOne_of_comparison_and_model` applied to the range-model comparison
`Work.EMFG.kOneComparison` and to the model `Work.EMFG.exists_fgRangeModel_one_via`. -/
theorem emOne_via (A : Type) [AddCommGroup A] [Module.Finite ℤ A] : EMOne A := by
  intro N X _ x hX i hi
  obtain ⟨W, tW, w, hW, hWfin⟩ := exists_fgRangeModel_one_via A N
  letI : TopologicalSpace W := tW
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hsub : Subsingleton (HomotopyGroup (Fin 0) X x) :=
      hX.2 0 (by norm_num) (Or.inl (by norm_num))
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hsub
    exact fgUpTo_zero_of_pathConnected X 0 le_rfl
  · obtain ⟨e⟩ := Work.EMFG.kOneComparison A N X x hX W w hW i (by omega)
    exact fg_of_homology_iso e.symm (hWfin i hi)

/-- **The `m = 1` case for finitely generated `A`** — the mathematical substance of the chapter:
the integral homology of range models of `K(A,1)`.  The proof is in
`Submission/Work/EMFG/emOne.lean` (`Work.EMFG.emOne`); here it is used through the reduction
`emHomologyFG_of_emOne`. -/
theorem emHomologyFG_of_emOne'' (hSSS : Work.PiS.SerreFGThreeForTwo)
    (hemOne : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A) :
    Work.PiS.EMHomologyFG :=
  emHomologyFG_of_emOne hSSS hemOne

/-- **EMFG.**  Every range model `X` of `K(A,m)` (`A` finitely generated, `m ≥ 2`) through degree
`N+1` has finitely generated integral homology through degree `N`.

This is `emHomologyFG_of_emOne` applied to the `m = 1` case `Work.EMFG.emOne`. -/
theorem emHomologyFG (hSSS : Work.PiS.SerreFGThreeForTwo) : Work.PiS.EMHomologyFG :=
  emHomologyFG_of_emOne hSSS (fun A _ _ => emOne_via A)

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Assembling the `m = 1` case from the comparison and a good model

The `m = 1` case `EMOne A` for finitely generated `A` follows from two independent inputs:

* `Work.EMFG.kOneComparison` — any two range models of `K(A,1)` through `N` have isomorphic
  integral homology in degrees `≤ N` (range-model uniqueness);
* `Work.EMFG.exists_fgRangeModel_one` — some range model of `K(A,1)` through `N` has f.g. integral
  homology through `N-1` (a model; for `A ≅ ℤ^r ⊕ F` one takes `T^r × (a lens-space-like model)`).

This file records the assembly, so that the target only depends on those two lemmas. -/

/-- **`EMOne` from the range-model comparison and a good model.** -/
theorem emOne_of_comparison_and_model
    (hcmp : ∀ (A : Type) [AddCommGroup A] (N : ℕ) (Z : Type) [TopologicalSpace Z] (z₀ : Z),
      Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N Z z₀ →
      ∀ (P : Type) [TopologicalSpace P] (p₀ : P),
        Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N P p₀ →
        ∀ i : ℕ, i ≤ N → Nonempty (Work.PiS.HZ Z i ≅ Work.PiS.HZ P i))
    (hmodel : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (N : ℕ),
      ∃ (X : Type) (_ : TopologicalSpace X) (x : X),
        Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N X x ∧ Work.PiS.FGUpTo X (N - 1)) :
    ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], EMOne A := by
  intro A _ _ N X _ x hX
  obtain ⟨W, tW, w, hW, hWfin⟩ := hmodel A N
  letI : TopologicalSpace W := tW
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hsub : Subsingleton (HomotopyGroup (Fin 0) X x) :=
      hX.2 0 (by norm_num) (Or.inl (by norm_num))
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hsub
    exact fgUpTo_zero_of_pathConnected X 0 le_rfl
  · obtain ⟨e⟩ := hcmp A N X x hX W w hW i (by omega)
    exact fg_of_homology_iso e.symm (hWfin i hi)

end

end Work.EMFG

namespace Work.EMFG

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The free case of `Work.EMFG.exists_fgRangeModel_one`**: the torus `(S¹)^r` is a range model of
`K(ℤ^r,1)` through every degree, with finitely generated integral homology. -/
theorem exists_fgRangeModel_one_free (r N : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (x : X),
      Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) 1 (by norm_num) N X x ∧ Work.PiS.FGUpTo X (N - 1) :=
  ⟨Fin r → Work.Serre.Sph 1, inferInstance, fun _ => Work.Serre.sphOneBase,
    (torusFGandEM r).2 N, (torusFGandEM r).1 (N - 1)⟩

end

end Work.EMFG
