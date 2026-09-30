import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.singularCohomology_zero_Hom
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.RatHurewicz.ConnectivityBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA EMZ — the loop shift `H_{i+1}(X;ℤ) ≅ H_i(ΩX;ℤ)`

For a range model `X` of `K(ℤ/2,n)` (`n ≥ 3`) and `1 ≤ i`, `i + 1 < 2n - 1`, the integral homology
of `X` in degree `i+1` is the integral homology of the loop space `ΩX = Path x₀ x₀` in degree `i`.

This is the stable-range consequence of the Serre exact sequence of the path–loop fibration
`ΩX → PX → X` (`Work.Pi6.SerreRangeLES`, taken as a hypothesis `hR`): `X` is `(n-1)`-connected, the
loop space is `(n-2)`-connected, and the path space `PX` is contractible, so the connecting map
`H_{i+1}(X;ℤ) → H_i(F;ℤ)` of the fibration is an isomorphism for `i + 1 < n + (n-1) = 2n-1`
(the range in which `SerreRangeLES` is exact), with `F = ΩX` written as the strict fibre of the
fibration and identified with `Path x₀ x₀` by `Work.StemsB.fibreEvalOneHomeo`.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMZ

noncomputable section

/-! ## Two generalities -/

/-- **A homotopy equivalence induces a linear equivalence on integral singular homology.** -/
theorem homologyLinearEquivOfHomotopyEquiv {X Y : TopCat}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ X).homology n ≃ₗ[ℤ]
      (Work.Cohomology.singularChains ℤ Y).homology n) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n) :=
    Work.Cohomology.homologyEquiv ℤ X Y f g h1 h2 n
  exact ⟨Work.Cohomology.moduleIsoToLinearEquiv
    (CategoryTheory.asIso
      (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n))⟩

/-- **An exact sequence `M →f→ N →g→ P →h→ Q` with `M` and `Q` zero exhibits `g` as an
isomorphism.**  (This is the "connecting map of the Serre sequence is an isomorphism in the stable
range" step, in the abstract form in which the total space is acyclic above degree `0`.) -/
theorem nonempty_linearEquiv_of_exact_zero {M N P Q : ModuleCat ℤ}
    (f : M ⟶ N) (g : N ⟶ P) (h : P ⟶ Q)
    (h1 : Function.Exact f.hom g.hom) (h2 : Function.Exact g.hom h.hom)
    (hM : IsZero M) (hQ : IsZero Q) : Nonempty (N ≃ₗ[ℤ] P) := by
  have hf : f = 0 := IsZero.eq_zero_of_src hM f
  have hh : h = 0 := IsZero.eq_zero_of_tgt hQ h
  have hf' : f.hom = 0 := by rw [hf]; simp
  have hh' : h.hom = 0 := by rw [hh]; simp
  have hker : LinearMap.ker g.hom = ⊥ := by
    rw [h1.linearMap_ker_eq, hf']
    exact LinearMap.range_zero
  have hran : LinearMap.range g.hom = ⊤ := by
    rw [← h2.linearMap_ker_eq, hh']
    exact LinearMap.ker_zero
  exact ⟨LinearEquiv.ofBijective g.hom
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩⟩

/-! ## The loop shift -/

theorem loopShift (hR : Work.Pi6.SerreRangeLES) (X : Type) [TopologicalSpace X] (x₀ : X)
    (n N i : ℕ) (hpos : 0 < n) (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) n hpos N X x₀)
    (hn : 3 ≤ n) (hi : 1 ≤ i) (hir : i + 1 < 2 * n - 1) :
    Nonempty (Work.Pi6.HR ℤ X (i + 1) ≃ₗ[ℤ] Work.Pi6.HR ℤ (Path x₀ x₀) i) := by
  classical
  -- the path space is contractible, hence path connected
  haveI hcontrP : ContractibleSpace (Work.StemsB.PathSpace X x₀) :=
    Work.StemsB.contractible_pathSpace X x₀
  haveI hpcP : PathConnectedSpace (Work.StemsB.PathSpace X x₀) := inferInstance
  -- connectivity of `X` and of the fibre
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀
      (hX.2 0 (by omega) (Or.inl (by omega)))
  have h1X : Subsingleton (HomotopyGroup (Fin 1) X x₀) :=
    hX.2 1 (by omega) (Or.inl (by omega))
  have hfib : Work.StemsB.IsSerreFibration (Work.StemsB.evalOne X x₀) :=
    Work.StemsB.isSerreFibration_evalOne X x₀
  have hpcF : PathConnectedSpace
      (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne X x₀) hfib x₀
      hpcP hpcX h1X
  have hpi0F : Subsingleton (HomotopyGroup (Fin 0)
      (Work.StemsB.fibre (Work.StemsB.evalOne X x₀)
        (Work.StemsB.evalOne X x₀ (Work.StemsB.constPath X x₀)))
      ⟨Work.StemsB.constPath X x₀, rfl⟩) :=
    Work.Serre.subsingleton_pi0_of_pathConnectedSpace
      (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀) ⟨Work.StemsB.constPath X x₀, rfl⟩
  -- `π_j(X) = 0` for `j < n`
  have hB : ∀ j : ℕ, j < n → Subsingleton
      (HomotopyGroup (Fin j) X (Work.StemsB.evalOne X x₀ (Work.StemsB.constPath X x₀))) := by
    intro j hj
    exact hX.2 j (by omega) (Or.inl hj)
  -- the loop space is a range model of `K(ℤ/2, n-1)`
  have hloop : Work.Serre.IsEMSpaceUpTo (ZMod 2) (n - 1) (by omega) (N - 1)
      (Path x₀ x₀) (Path.refl x₀) :=
    Work.Stems.isEMSpaceUpTo_loop' (A := ZMod 2) (m := n) (M := N) (by omega) x₀ hX
  -- connectivity of the loops implies vanishing of their homology below degree `n-1`
  have hloopVan : ∀ j : ℕ, 0 < j → j < n - 1 → IsZero (Work.Pi6.HR ℤ (Path x₀ x₀) j) := by
    intro j hj hjn
    refine Work.Pi6.SQASM.connHomology (Path.refl x₀) (n - 2) j ?_ hj (by omega)
    intro k hk
    exact hloop.2 k (by omega) (Or.inl (by omega))
  -- and the vanishing transfers to the strict fibre of the path–loop fibration
  have hfibVan : ∀ j : ℕ, 0 < j → j < n - 1 → IsZero (Work.Pi6.HR ℤ
      (Work.StemsB.fibre (Work.StemsB.evalOne X x₀)
        (Work.StemsB.evalOne X x₀ (Work.StemsB.constPath X x₀))) j) := by
    intro j hj hjn
    obtain ⟨e⟩ := homologyLinearEquivOfHomotopyEquiv
      (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀))
      (Y := TopCat.of (Path x₀ x₀)) (Work.StemsB.fibreEvalOneHomeo X x₀).toHomotopyEquiv j
    exact IsZero.of_iso (hloopVan j hj hjn) e.toModuleIso
  -- the total space of the fibration is acyclic in positive degrees
  have hE : IsZero (Work.Pi6.HR ℤ (Work.StemsB.PathSpace X x₀) (i + 1)) :=
    Work.Cohomology.homologyContractible (X := TopCat.of (Work.StemsB.PathSpace X x₀))
      (i + 1) (by omega)
  have hE' : IsZero (Work.Pi6.HR ℤ (Work.StemsB.PathSpace X x₀) i) :=
    Work.Cohomology.homologyContractible (X := TopCat.of (Work.StemsB.PathSpace X x₀))
      i (by omega)
  -- the Serre exact sequence in the stable range
  obtain ⟨bd, hbd⟩ := hR ℤ (Work.StemsB.PathSpace X x₀) X (Work.StemsB.evalOne X x₀)
    (Work.StemsB.constPath X x₀) n (n - 1) hfib (by omega) hB hpi0F hfibVan
  obtain ⟨-, hex2, hex3⟩ := hbd i (by omega : i + 1 < n + (n - 1))
  -- the connecting map is an isomorphism
  obtain ⟨e₁⟩ := nonempty_linearEquiv_of_exact_zero
    (Work.Pi6.hmap ℤ (Work.StemsB.evalOne X x₀) (i + 1)) (bd i)
    (Work.Pi6.hmap ℤ
      (Work.StemsB.fibreIncl (Work.StemsB.evalOne X x₀)
        (Work.StemsB.evalOne X x₀ (Work.StemsB.constPath X x₀))) i)
    hex2 hex3 hE hE'
  -- and the strict fibre is the loop space
  obtain ⟨e₂⟩ := homologyLinearEquivOfHomotopyEquiv
    (X := TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀))
    (Y := TopCat.of (Path x₀ x₀)) (Work.StemsB.fibreEvalOneHomeo X x₀).toHomotopyEquiv i
  exact ⟨e₁.trans e₂⟩

end

end Work.Pi6.EMZ
