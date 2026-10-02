import Mathlib
import Submission.Work.Serre.ratPairInputs
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.OneCell.RatMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational Serre pair comparison in the stable range: assembly

The stable-range comparison of the pair `(E, p⁻¹{b₀})` with `(B, {b₀})` over `ℚ` is assembled from
the sharp rational cell step (`Work.Serre.RatCellStepSharp`), the pullback comparison
(`Work.Serre.RatPullbackComparison`) and the cellular induction over the CW model
(`Work.Serre.RatTowerComparison`): the fibre hypotheses are transported along paths in `B`, the two
comparison theorems are applied to the `(f+3)`-rd stage of `Work.Serre.CWModel.towerA`, and the
resulting isomorphisms are glued with the long exact sequences of the pairs.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 800000

namespace Work.Serre

noncomputable section

/-- **The fibre data of a Serre fibration at every point of a path connected base**, from the data
at one point: the vanishing of the rational homology below `f` and `H₀ ≅ ℚ`. -/
theorem fibreData_all {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (f : ℕ) (hB : PathConnectedSpace B)
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    (∀ b' : B, ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b')) j)) ∧
    (∀ b' : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b')) 0
      ≅ ModuleCat.of ℚ ℚ)) := by
  have h0 : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0
      ≅ ModuleCat.of ℚ ℚ) := ratH_zero_of_pathConnected (Work.StemsB.fibre p b₀)
  refine ⟨fun b' j hj hjf => ?_, fun b' => ?_⟩
  · obtain ⟨P⟩ := hB.joined b₀ b'
    exact isZero_ratH_fibre_of_path p hp b₀ b' P.toContinuousMap P.source P.target f hfib j hj hjf
  · obtain ⟨P⟩ := hB.joined b₀ b'
    obtain ⟨e⟩ := ratH_fibre_iso_of_path p hp P.toContinuousMap 0
    have h0e : Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p (P.toContinuousMap 0))) 0
        = Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) 0 := by
      rw [show P.toContinuousMap 0 = b₀ from P.source]
    have h1e : Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p (P.toContinuousMap 1))) 0
        = Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b')) 0 := by
      rw [show P.toContinuousMap 1 = b' from P.target]
    exact ⟨(eqToIso h1e).symm ≪≫ e.symm ≪≫ eqToIso h0e ≪≫ h0.some⟩

/-- `Work.Serre.relChainsRPairMap` and `Work.Serre.relChainsRMapOf` are the same map of relative
chain complexes (both are the `cokernel.map` of the inducing maps). -/
theorem relChainsRPairMap_eq_relChainsRMapOf {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    relChainsRPairMap A B g hg
      = relChainsRMapOf (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom g)
          (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl) := rfl

/-- **The range five lemma for the "subtype form" of a map of pairs over `ℚ`**
(`Work.Serre.relChainsRPairMap`), the form in which the comparison maps of the Serre exactness
assembly are written. -/
theorem isIso_homologyMap_relChainsRPairMap_range {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (A : Set X) (Bm : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A Bm) (n : ℕ)
    (hf : ∀ k : ℕ, k ≤ n → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)) k))
    (hA : ∀ k : ℕ, k ≤ n → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of Bm)
        (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩)) k)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (relChainsRPairMap A Bm g hg) n) := by
  rw [relChainsRPairMap_eq_relChainsRMapOf A Bm g hg]
  exact Work.Serre.OneCell.isIso_homologyMap_relChainsRMapOf_range A Bm (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x => ⟨g x.1, hg x.2⟩, by fun_prop⟩) (by ext x; rfl) n hf hA

/-- **The comparison `(Γ, {γ₀}) → (B, {b₀})` of a stage of the CW model is an isomorphism on
rational homology in the range of the model.** -/
theorem isIso_pairMapOfRat {B : Type} [TopologicalSpace B] (b₀ : B) {n N : ℕ}
    (st : Work.Serre.CWModel.StA B b₀ n)
    (hbij : ∀ i : ℕ, i ≤ N → ∀ x : st.Y, Function.Bijective (Work.Serre.piMapN st.g i x)) :
    ∀ i : ℕ, i < N → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (pairMapOfRat st.g st.y₀ b₀ st.gbase) i) := by
  haveI : Nonempty st.Y := ⟨st.y₀⟩
  intro i hi
  refine isIso_homologyMap_relChainsRPairMap_range ({st.y₀} : Set st.Y) ({b₀} : Set B) st.g
    (fun x hx => by simpa [show x = st.y₀ from hx] using st.gbase) i ?_ ?_
  · intro k hk
    exact Work.Serre.serreK2 st.Y B st.g N (fun k hk x => hbij k (le_of_lt hk) x) k (by omega)
  · intro k hk
    let ρ : TopCat.of ({st.y₀} : Set st.Y) ⟶ TopCat.of ({b₀} : Set B) :=
      TopCat.ofHom ⟨fun x => ⟨st.g x.1, by
        rw [show x.1 = st.y₀ from x.2]; exact st.gbase⟩, by fun_prop⟩
    haveI : IsIso ρ :=
      ⟨⟨TopCat.ofHom ⟨fun _ => ⟨st.y₀, by simp⟩, continuous_const⟩, by
          ext x
          exact x.2.symm, by
          ext y
          show st.g st.y₀ = (y : B)
          rw [st.gbase]
          exact y.2.symm⟩⟩
    exact Work.Serre.OneCell.isIso_homologyMap_chainMap_of_isIso ρ k

/-- **The stable-range Serre pair comparison over `ℚ`**, assembled from the sharp cell step, the
pullback comparison and the cellular induction over the CW model. -/
theorem ratSerrePairComparison_of_inputs (hcell : RatCellStepSharp) (hpb : RatPullbackComparison)
    (htow : RatTowerComparison)
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b f : ℕ) (hb : 2 ≤ b) (hf : 1 ≤ f)
    (hE : PathConnectedSpace E) (hB : PathConnectedSpace B)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    (∀ i : ℕ, i < b + f → Nonempty
      (((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology i) ≅
        ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology i))) ∧
      (CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology (b + f)) →
        CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology (b + f))) := by
  obtain ⟨hfiball, h0all⟩ := fibreData_all p hp b₀ f hB hfib0 hfib
  let st : Work.Serre.CWModel.StA B b₀ (b - 2 + (f + 3)) :=
    Work.Serre.CWModel.towerA B b₀ b hb hconn (f + 3)
  haveI hstconn : PathConnectedSpace st.Y := st.conn
  have hbij : ∀ i : ℕ, i ≤ b + f + 1 → ∀ x : st.Y, Function.Bijective (Work.Serre.piMapN st.g i x) := by
    intro i hi x
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) st.Y x) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := x)).injective.subsingleton
      haveI : Subsingleton (HomotopyGroup (Fin 0) B (st.g x)) :=
        (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := st.g x)).injective.subsingleton
      exact ⟨fun a _ _ => Subsingleton.elim a _, fun y => ⟨default, Subsingleton.elim _ _⟩⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.bijective_piMapN_of_joined st.g (PathConnectedSpace.joined st.y₀ x) (j + 1)
        (st.bij j (by omega))
  obtain ⟨htowIso, htowSurj⟩ := htow hcell E B p hp b₀ b f hb hconn hfiball h0all (f + 3)
  have hpbIso : ∀ i : ℕ, i < b + f + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (pullbackPairMapRat st.g p st.y₀ b₀ st.gbase) i) :=
    fun i hi => hpb st.g p st.y₀ b₀ st.gbase hp (b + f + 1) (fun k hk x => hbij k hk x) i hi
  have hpairIso : ∀ i : ℕ, i < b + f + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (pairMapOfRat st.g st.y₀ b₀ st.gbase) i) :=
    fun i hi => isIso_pairMapOfRat b₀ st hbij i hi
  refine ⟨fun i hi => ?_, fun hz => ?_⟩
  · haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pullbackPairMapRat st.g p st.y₀ b₀ st.gbase) i) := hpbIso i (by omega)
    haveI h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (stagePairMapRat st.g p st.y₀) i) := htowIso i hi
    haveI h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pairMapOfRat st.g st.y₀ b₀ st.gbase) i) := hpairIso i (by omega)
    exact ⟨(asIso (HomologicalComplex.homologyMap (pullbackPairMapRat st.g p st.y₀ b₀ st.gbase) i)).symm
      ≪≫ asIso (HomologicalComplex.homologyMap (stagePairMapRat st.g p st.y₀) i)
      ≪≫ asIso (HomologicalComplex.homologyMap (pairMapOfRat st.g st.y₀ b₀ st.gbase) i)⟩
  · haveI h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pullbackPairMapRat st.g p st.y₀ b₀ st.gbase) (b + f)) := hpbIso (b + f) (by omega)
    have hX : CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.StemsB.Pullback st.g p))
        ((Work.StemsB.pullbackFst st.g p) ⁻¹' ({st.y₀} : Set st.Y))).homology (b + f)) :=
      CategoryTheory.Limits.IsZero.of_iso hz (asIso (HomologicalComplex.homologyMap
        (pullbackPairMapRat st.g p st.y₀ b₀ st.gbase) (b + f)))
    have hsub : Subsingleton ((Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.StemsB.Pullback st.g p))
        ((Work.StemsB.pullbackFst st.g p) ⁻¹' ({st.y₀} : Set st.Y))).homology (b + f)) :=
      ModuleCat.isZero_iff_subsingleton.mp hX
    haveI hsub' : Subsingleton ((Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.StemsB.Pullback st.g p))
        ((Work.StemsB.pullbackFst st.g p) ⁻¹' ({st.y₀} : Set st.Y))).homology (b + f)) := hsub
    have hsubG : Subsingleton ((Work.StemsB.relChainsR ℚ
        (TopCat.of st.Y) ({st.y₀} : Set st.Y)).homology (b + f)) :=
      htowSurj.subsingleton
    have hG : CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ
        (TopCat.of st.Y) ({st.y₀} : Set st.Y)).homology (b + f)) :=
      ModuleCat.isZero_iff_subsingleton.mpr hsubG
    haveI h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (pairMapOfRat st.g st.y₀ b₀ st.gbase) (b + f)) := hpairIso (b + f) (by omega)
    exact CategoryTheory.Limits.IsZero.of_iso hG (asIso (HomologicalComplex.homologyMap
      (pairMapOfRat st.g st.y₀ b₀ st.gbase) (b + f))).symm

end

end Work.Serre