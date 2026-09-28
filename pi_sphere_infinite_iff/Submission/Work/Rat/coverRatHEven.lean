import Mathlib
import Submission.Work.Rat.hopfInterfaces
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.StemsB.WangSphereHomology
import Submission.Work.Rat.c2FreeMain
import Submission.Work.Stems.Engine.C2FreeTop
import Submission.Work.Rat.coverFibreDataSerre
import Submission.Work.Rat.wangTopRatH
import Submission.Work.Stems.isEMSpace_loop
import Submission.Work.Stems.homotopyFibre_conn
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Stems.wangOddStep
import Submission.Work.Stems.wangOddStepSphere
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Engine
import Submission.Work.Stems.isEMSpace_change_basepoint
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Serre.Models
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Serre.EulerFibreRoot

namespace Work.Rat

set_option maxHeartbeats 1600000

/-- **The rational homology of the cover of an even sphere in every degree up to `M`.**

For `n ≥ 2` even, a range model `X` of `K(ℤ,n)` through degree `N ≥ M + 4n + 8`, a point `s₀` of
`Sⁿ` and a map `f : Sⁿ → X` inducing a bijection on `πₙ`, the `n`-connected cover
`E = hofib f s₀` of `Sⁿ` is rationally `S^{2n-1}` through degree `M`: `H_j(E;ℚ) = 0` for
`0 < j ≤ M`, `j ≠ 2n-1`, and `H_{2n-1}(E;ℚ) ≅ ℚ`.

The cover is the total space of the fibration `coverProj e f s₀ : E → Sᵐᵒᵈᵉˡ` (over the one-point
model of the sphere) whose fibre is the loop space `ΩX`, a range model of `K(ℤ,n-1)` with `n-1`
odd; the odd clause of the `C2` layer computes the rational homology of that range model through
degree `N - n ≫ M`.  The two halves are then

* `j ≤ n`: `E` is `n`-connected, so Serre's `E0` gives the vanishing (no computation needed);
* `n < j ≤ M`, `j ≠ 2n-1`: the exactness spot `H^{j-n}(ΩX) → H^j(E) → H^j(ΩX)` of the Wang
  sequence of the fibration over the sphere has both outer terms vanishing (this is where `j ≠ 2n-1`
  and the range hypothesis on `ΩX` are used);
* `j = 2n-1`: `Work.Rat.wangTopRatH` computes the top degree from the fibre data alone. -/
theorem coverRatHEven {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hE3b : Work.Serre.SerreE3b)
    {X : Type} [TopologicalSpace X] (pt : X) (N M : ℕ) (hN : M + 4 * n + 8 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt)
    (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X))
    (hbij : Function.Bijective (Work.Serre.piMapN f n s₀)) :
    (∀ j : ℕ, 0 < j → j ≤ M → j ≠ 2 * n - 1 →
        CategoryTheory.Limits.IsZero
          (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) j)) ∧
      Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) (2 * n - 1)
        ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- ## The one-point model of the sphere and the projection of the cover
  set e : Work.StemsB.SphModel n ≃ₜ Work.Serre.Sph n := Work.Stems.onePointSphereHomeo n with he
  let E : Type := Work.RatHurewicz.homotopyFibre f s₀
  let e₀ : E := Work.RatHurewicz.homotopyFibreBasepoint f s₀
  let p : C(E, Work.StemsB.SphModel n) := Work.Rat.coverProj e f s₀
  -- ## The fibre data of the cover, up to degree `2n` (Serre route, `hE3b`)
  obtain ⟨hHur, hFib2nVan, hFib2nGen⟩ :=
    Work.Rat.coverFibreDataSerre hn heven hE3b pt N (by omega) hX s₀ f hbij e
  -- ## `X` is path connected, and a range model at the base point `f s₀`
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inl (by omega)))
  obtain ⟨γ₀⟩ := hpcX.joined pt (f s₀)
  have hXs : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X (f s₀) :=
    Work.Stems.isEMSpaceUpTo_change_basepoint (by omega) γ₀ hX
  -- ## The cover is `n`-connected
  have hconnE : ∀ k : ℕ, k ≤ n → Subsingleton (HomotopyGroup (Fin k) E e₀) := by
    refine Work.Stems.subsingleton_homotopyFibre_of_inj_surj f n (by omega) s₀ ?_ ?_
    · intro i hi
      by_cases hin : i = n
      · subst hin; exact hbij.1
      · haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph n) s₀) :=
          Work.Stems.sphereConnectivity n i (by omega) s₀
        exact fun a b _ => Subsingleton.elim a b
    · intro i hi
      by_cases hin : i = n
      · subst hin; exact hbij.2
      · haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) :=
          hXs.2 i hin (by
            rcases lt_or_ge i n with hlt | hge
            · exact Or.inl hlt
            · exact Or.inr (by omega))
        exact fun y => ⟨Classical.choice
          (inferInstance : Nonempty (HomotopyGroup (Fin i) (Work.Serre.Sph n) s₀)),
          Subsingleton.elim _ y⟩
  -- ## The loop space `ΩX` has the rational homology of `S^{n-1}` through degree `M`
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  have hloopEM : Work.Serre.IsEMSpaceUpTo ℤ (n - 1) (by omega) (N - 1)
      (Path (f s₀) (f s₀)) (Path.refl (f s₀)) :=
    Work.Stems.isEMSpaceUpTo_loop' hn (f s₀) hXs
  obtain ⟨hloopGen, hloopVan⟩ :=
    (Work.Rat.c2Free hE3b).2 (n - 1) (by omega) hodd (N - 1)
      (Path (f s₀) (f s₀)) (Path.refl (f s₀)) hloopEM
  -- the range `M` sits inside the range `(N-1) - (n-1) = N - n` of the loop space
  have hrange : ∀ t : ℕ, t ≤ M → t < (N - 1) - 1 * (n - 1) := by
    intro t ht
    simp only [one_mul]
    omega
  -- ## Vanishing of the cohomology of the fibre of `coverProj` in the range `M`
  have hfibCohVan : ∀ t : ℕ, 0 < t → t ≤ M → t ≠ n - 1 →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp n p)) := by
    intro t ht0 htM htn
    obtain ⟨e'⟩ := Work.Rat.coverFibreRatH_iso_path (by omega : 1 ≤ n) s₀ f e t
    have hzL : CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Path (f s₀) (f s₀))) t) :=
      hloopVan t ht0 (hrange t htM) htn
    have hz : CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.Rat.coverFibre e f s₀)) t) :=
      CategoryTheory.Limits.IsZero.of_iso hzL e'
    exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup hz)
  -- ## The Wang data of the fibration over the sphere
  have hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter n)
      (Work.StemsB.dOuter n) :=
    Work.Stems.fibrewiseTrivial_sphLoopOuter E p hHur
  obtain ⟨d_G, hT_G⟩ := Work.Stems.fibrewiseTrivial_sphLoopBig (by omega : 1 ≤ n) E p hHur
  obtain ⟨γ, τS, -, -⟩ := Work.StemsB.wangSphereE4Rat n hn E p hHur hT_O d_G hT_G
  -- ## Vanishing of the cohomology of the cover in degrees `≤ M` other than `2n-1`
  have hvanCoh : ∀ t : ℕ, 0 < t → t ≤ M → t ≠ 2 * n - 1 →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) := by
    intro t ht0 htM htn
    by_cases htn' : t ≤ n
    · -- below the connectivity of the cover: nothing to compute
      exact ModuleCat.isZero_iff_subsingleton.mp
        (Work.Serre.isZero_ratCoh_of_isZero_ratH_dup
          ((Work.Serre.serreE0Range E e₀ n (fun i hi => hconnE i hi)) t ht0 (by omega)))
    · -- above it: the two outer terms of the Wang sequence vanish
      have hnt : n < t := by omega
      have hαβ := Work.Stems.wangCohShiftExactTotal (TopCat.of E)
        (p ⁻¹' Work.StemsB.sphLoopOuter n) (Work.StemsB.wangCohFsp n p) n γ τS (t - n - 1)
      have hsrc : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ ((t - n - 1) + 1)
          (Work.StemsB.wangCohFsp n p)) := by
        rw [show (t - n - 1) + 1 = t - n from by omega]
        exact hfibCohVan (t - n) (by omega) (by omega) (by omega)
      have htgt : Subsingleton ↥(Work.Cohomology.singularCohomology ℚ ((t - n - 1) + n + 1)
          (Work.StemsB.wangCohFsp n p)) := by
        rw [show (t - n - 1) + n + 1 = t from by omega]
        exact hfibCohVan t ht0 htM (by omega)
      have hmid := Work.Stems.subsingleton_of_exact_of_range _ _ hαβ
        (Work.Stems.subsingleton_range _ hsrc) (fun x => Subsingleton.elim _ _)
      rwa [show (t - n - 1) + n + 1 = t from by omega] at hmid
  -- ## The top degree
  have htop : Nonempty (Work.Serre.ratH (TopCat.of E) (2 * n - 1) ≅ ModuleCat.of ℚ ℚ) :=
    Work.Rat.wangTopRatH hn E p hHur hFib2nVan hFib2nGen
  refine ⟨fun j hj0 hjM hjne => ?_, htop⟩
  exact Work.Stems.isZero_ratH_of_isZero_ratCoh
    (ModuleCat.isZero_iff_subsingleton.mpr (hvanCoh j hj0 hjM hjne))

end Work.Rat
