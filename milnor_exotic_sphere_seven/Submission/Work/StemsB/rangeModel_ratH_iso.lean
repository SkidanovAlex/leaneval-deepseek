import Mathlib
import Submission.Work.StemsB.rangeModelDefs
import Submission.Work.StemsB.secondMap_firstGenStep
import Submission.Work.StemsB.secondMap_genStep
import Submission.Work.StemsB.secondMap_killStep
import Submission.Work.StemsB.rmTower_pi_bijective
import Submission.Work.StemsB.wedgeCellDefs
import Submission.Work.Serre.Models
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.bijective_piMapN_of_joined

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison of two range models of `K(A,k)`

`Work.StemsB.rangeModel_ratH_iso`: two range models `Z`, `P` of `K(A,k)` through degree `N`
(`Work.Serre.IsEMSpaceUpTo A k _ N _`) have isomorphic rational homology in degrees `≤ N`.

The proof compares both with a common cell complex:

* the CW model tower `Work.Serre.CWModel.towerA Z z₀ (m+1) …` (`rmTower`) maps a cell complex `Y`
  into `Z` and is a `π`-isomorphism in degrees `≤ N`;
* a second map `c : Y → P` is built along the same tower (`Work.StemsB.SecondMapInv`), and
  `Work.StemsB.rmTower_pi_bijective` shows it is a `π`-isomorphism in degrees `≤ N` as well;
* the sharp range Whitehead theorem `Work.Serre.Assembly.serreK2IntSharp` turns each of the two maps
  into an isomorphism on rational homology in degrees `≤ N`.

The three steps of the construction of `c` are
`Work.StemsB.secondMap_firstGenStep` (a wedge of spheres), `Work.StemsB.secondMap_genStep` and
`Work.StemsB.secondMap_killStep`; the cell-class generation input is
`Work.StemsB.wedge_cellClass_generate`.
-/

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

variable {A : Type} [AddCommGroup A] {m N : ℕ} {Z : Type} [TopologicalSpace Z] {z₀ : Z}
  {P : Type} [TopologicalSpace P] {p₀ : P}

/-! ## The final step: a common source with `π`-isomorphisms in the range -/

/-- **Comparison of the rational homologies from a common source.**  If `g : Y → Z` and `c : Y → P`
are `π`-isomorphisms in degrees `≤ N` (at every base point) and `Y`, `Z`, `P` are path connected,
then `H_i(Z;ℚ) ≅ H_i(P;ℚ)` for `i ≤ N`. -/
theorem comparisons_ratH_iso {Y : Type} [TopologicalSpace Y] (y₀ : Y) [PathConnectedSpace Y]
    [PathConnectedSpace Z] [PathConnectedSpace P]
    (g : C(Y, Z)) (c : C(Y, P))
    (hg : ∀ i : ℕ, i ≤ N → ∀ y : Y, Function.Bijective (Work.Serre.piMapN g i y))
    (hc : ∀ i : ℕ, i ≤ N → ∀ y : Y, Function.Bijective (Work.Serre.piMapN c i y)) :
    (∀ i : ℕ, i ≤ N → Nonempty (Work.Serre.ratH (TopCat.of Y) i ≅
      Work.Serre.ratH (TopCat.of Z) i)) ∧
    (∀ i : ℕ, i ≤ N → Nonempty (Work.Serre.ratH (TopCat.of Y) i ≅
      Work.Serre.ratH (TopCat.of P) i)) := by
  constructor
  · intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      obtain ⟨e1⟩ := Work.Serre.ratH_zero_of_pathConnected Y
      obtain ⟨e2⟩ := Work.Serre.ratH_zero_of_pathConnected Z
      exact ⟨e1 ≪≫ e2.symm⟩
    · have hint : IsIso (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)) i) :=
        Work.Serre.Assembly.serreK2IntSharp g (N + 1) (fun j hj y => hg j (by omega) y) i hpos
          (by omega)
      have hrat : IsIso (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)) i) :=
        Work.Serre.isIso_homologyMap_rat_of_isIso_int (TopCat.of Y) (TopCat.of Z)
          (TopCat.ofHom g) i hint
      exact ⟨asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g)) i)⟩
  · intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      obtain ⟨e1⟩ := Work.Serre.ratH_zero_of_pathConnected Y
      obtain ⟨e2⟩ := Work.Serre.ratH_zero_of_pathConnected P
      exact ⟨e1 ≪≫ e2.symm⟩
    · have hint : IsIso (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of P) (TopCat.ofHom c)) i) :=
        Work.Serre.Assembly.serreK2IntSharp c (N + 1) (fun j hj y => hc j (by omega) y) i hpos
          (by omega)
      have hrat : IsIso (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of P) (TopCat.ofHom c)) i) :=
        Work.Serre.isIso_homologyMap_rat_of_isIso_int (TopCat.of Y) (TopCat.of P)
          (TopCat.ofHom c) i hint
      exact ⟨asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of P) (TopCat.ofHom c)) i)⟩

/-! ## The trivial case: the range is below the first non-trivial degree -/

/-- **The small case.**  If `N ≤ m` then both `Z` and `P` are `(m+1-1)`-connected, so their
rational homology vanishes in degrees `1, …, N` (and is `ℚ` in degree `0`). -/
theorem small_case (hm : 1 ≤ m) (hN : N ≤ m)
    (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀)
    (hP : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N P p₀) :
    ∀ i : ℕ, i ≤ N →
      Nonempty (Work.Serre.ratH (TopCat.of Z) i ≅ Work.Serre.ratH (TopCat.of P) i) := by
  haveI hpcZ : PathConnectedSpace Z := pathConnected_Z hm hZ
  haveI hpcP : PathConnectedSpace P := pathConnected_P hm hP
  have hsubZ : ∀ j : ℕ, j ≤ N → Subsingleton (HomotopyGroup (Fin j) Z z₀) := by
    intro j hj
    exact hZ.2 j (by omega) (Or.inl (by omega))
  have hsubP : ∀ j : ℕ, j ≤ N → Subsingleton (HomotopyGroup (Fin j) P p₀) := by
    intro j hj
    exact hP.2 j (by omega) (Or.inl (by omega))
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    obtain ⟨e1⟩ := Work.Serre.ratH_zero_of_pathConnected Z
    obtain ⟨e2⟩ := Work.Serre.ratH_zero_of_pathConnected P
    exact ⟨e1 ≪≫ e2.symm⟩
  · have hZ0 : IsZero (Work.Serre.ratH (TopCat.of Z) i) :=
      Work.Serre.serreE0Range Z z₀ N hsubZ i hpos (by omega)
    have hP0 : IsZero (Work.Serre.ratH (TopCat.of P) i) :=
      Work.Serre.serreE0Range P p₀ N hsubP i hpos (by omega)
    exact ⟨IsZero.iso hZ0 hP0⟩

/-! ## The main case: the tower construction -/

/-- **The invariant survives the tower.**  Given the three steps of the construction as hypotheses
(they are the delegated lemmas), every level `1 ≤ t ≤ N - m` of the tower carries a second structure
map satisfying `Work.StemsB.SecondMapInv`. -/
theorem inv_tower (hm : 1 ≤ m) (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀)
    (hP : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N P p₀)
    (hfirst : ∃ c : C((Work.Serre.CWModel.genStep
        (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega)
          (fun i hi => hZ.2 i (by omega) (Or.inl hi)))).Y, P),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀)
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega)
            (fun i hi => hZ.2 i (by omega) (Or.inl hi)))).y₀
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.baseState Z z₀ (m + 1) (by omega)
            (fun i hi => hZ.2 i (by omega) (Or.inl hi)))).g c)
    (hgen : ∀ {n : ℕ} (hdeg : m + 1 < n + 2) (s : Work.Serre.CWModel.StA Z z₀ n)
      (c : C(s.Y, P)),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) s.y₀ s.g c →
      ∃ c' : C((Work.Serre.CWModel.genStep s).Y, P),
        SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀)
          (Work.Serre.CWModel.genStep s).y₀ (Work.Serre.CWModel.genStep s).g c')
    (hkill : ∀ {n : ℕ} (hdeg : m + 1 ≤ n + 2) (s : Work.Serre.CWModel.StG Z z₀ n)
      (c : C(s.Y, P)),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) s.y₀ s.g c →
      (m + 1 < n + 2 → ∀ y : P, Subsingleton (HomotopyGroup (Fin (n + 2)) P y)) →
      ∃ c' : C((Work.Serre.CWModel.killStep s).Y, P),
        SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀)
          (Work.Serre.CWModel.killStep s).y₀ (Work.Serre.CWModel.killStep s).g c') :
    ∀ t : ℕ, 1 ≤ t → t ≤ N - m →
      ∃ c : C((rmTower hm hZ t).Y, P),
        SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) (rmTower hm hZ t).y₀
          (rmTower hm hZ t).g c := by
  intro t
  induction t with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ t ih =>
    rcases t with _ | t'
    · -- the first two steps of the tower
      intro _ _
      rw [rmTower_succ]
      obtain ⟨c, hc⟩ := hfirst
      refine hkill (n := m - 1) (by omega) (Work.Serre.CWModel.genStep (rmTower hm hZ 0)) c ?_ ?_
      · exact hc
      · intro hcon; exact absurd hcon (by omega)
    · -- the generic steps
      intro ht htN
      rw [rmTower_succ]
      obtain ⟨c, hc⟩ := ih (by omega) (by omega)
      obtain ⟨c', hc'⟩ := hgen (n := m - 1 + (t' + 1)) (by omega) (rmTower hm hZ (t' + 1)) c hc
      refine hkill (n := m - 1 + (t' + 1)) (by omega)
        (Work.Serre.CWModel.genStep (rmTower hm hZ (t' + 1))) c' hc' ?_
      · intro _
        intro y
        haveI : PathConnectedSpace P := pathConnected_P hm hP
        have hsub := Work.Serre.subsingleton_homotopyGroup_of_joined
          (PathConnectedSpace.joined p₀ y) (m + t' + 1)
          (hP.2 (m + t' + 2) (by omega) (Or.inr (by omega)))
        simpa [show m - 1 + (t' + 1) + 2 = m + t' + 2 from by omega] using hsub

/-- **The main case.** -/
theorem main_case (hm : 1 ≤ m) (hN : m + 1 ≤ N)
    (hZ : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N Z z₀)
    (hP : Work.Serre.IsEMSpaceUpTo A (m + 1) (by omega) N P p₀) :
    ∀ i : ℕ, i ≤ N →
      Nonempty (Work.Serre.ratH (TopCat.of Z) i ≅ Work.Serre.ratH (TopCat.of P) i) := by
  haveI hpcY : PathConnectedSpace (rmTower hm hZ (N - m)).Y := (rmTower hm hZ (N - m)).conn
  haveI hpcZ : PathConnectedSpace Z := pathConnected_Z hm hZ
  haveI hpcP : PathConnectedSpace P := pathConnected_P hm hP
  -- the comparison isomorphism
  have Λ := hZ.1.some.trans hP.1.some.symm
  -- the invariant at the last level
  obtain ⟨c, hc⟩ := inv_tower hm hZ hP
    (secondMap_firstGenStep (A := A) (m := m) hm (Z := Z) (z₀ := z₀) (P := P) (p₀ := p₀)
      (fun i hi => hZ.2 i (by omega) (Or.inl hi)) Λ)
    (fun {n} hdeg s c hc => secondMap_genStep (A := A) (m := m) (Z := Z) (z₀ := z₀) (P := P)
      (p₀ := p₀) hdeg s c hc)
    (fun {n} hdeg s c hc htriv => secondMap_killStep (A := A) (m := m) (Z := Z) (z₀ := z₀)
      (P := P) (p₀ := p₀) hdeg s c hc htriv)
    (N - m) (by omega) (by omega)
  -- both maps are π-isomorphisms in the range
  obtain ⟨hg, hcbi⟩ := rmTower_pi_bijective hm hZ hP hN c hc
  -- compose the two comparisons with the common source
  intro i hi
  obtain ⟨e1⟩ := (comparisons_ratH_iso (rmTower hm hZ (N - m)).y₀ (rmTower hm hZ (N - m)).g c
    hg hcbi).1 i hi
  obtain ⟨e2⟩ := (comparisons_ratH_iso (rmTower hm hZ (N - m)).y₀ (rmTower hm hZ (N - m)).g c
    hg hcbi).2 i hi
  exact ⟨e1.symm ≪≫ e2⟩

/-- **The comparison of two range models of `K(A,k)`**: their rational homology agrees in degrees
`≤ N`. -/
theorem rangeModel_ratH_iso (A : Type) [AddCommGroup A] (k N : ℕ) (hk : 2 ≤ k)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : Work.Serre.IsEMSpaceUpTo A k (by omega) N Z z₀)
    (P : Type) [TopologicalSpace P] (p₀ : P)
    (hP : Work.Serre.IsEMSpaceUpTo A k (by omega) N P p₀) :
    ∀ i : ℕ, i ≤ N →
      Nonempty (Work.Serre.ratH (TopCat.of Z) i ≅ Work.Serre.ratH (TopCat.of P) i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hm : 1 ≤ m := by omega
  by_cases hle : N ≤ m
  · exact small_case (A := A) (m := m) (N := N) (Z := Z) (z₀ := z₀) (P := P) (p₀ := p₀)
      hm hle hZ hP
  · exact main_case (A := A) (m := m) (N := N) (Z := Z) (z₀ := z₀) (P := P) (p₀ := p₀)
      hm (by omega) hZ hP

end

end Work.StemsB
