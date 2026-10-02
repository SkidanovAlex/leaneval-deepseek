import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2b
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.subsingleton_relPiVanishing_of_path
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.homotopyFibre_pathConnected
import Submission.Work.Serre.relPi_one_subsingleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# C1: the pair lemma — `A ↪ Y` a `π₁`-iso with both spaces aspherical above degree 1

Let `Y` be a path connected topological space, `A ⊆ Y` a path connected subspace such that

* the inclusion `A ↪ Y` induces a bijection on `π₁` (`hpi1`),
* `π_j(A) = 0` and `π_j(Y) = 0` for `j ≥ 2`.

Then the inclusion induces an isomorphism on integral singular homology in every degree.  The proof
is the compression argument: the relative homotopy groups `π_k` (of the homotopy fibre of the
inclusion) vanish — in degrees `k ≥ 2` from the vanishing of the absolute groups, in degrees `0`
and `1` by the geometric argument of `homotopyFibre_pathConnected` / `relPi_one_subsingleton` —
hence (tom Dieck) every map of pairs `(I^d, ∂I^d) → (Y,A)` compresses into `A` in every dimension,
hence (`Work.Serre.serreE2b`) the relative homology vanishes, and the long exact sequence of the
pair gives the isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The relative groups in degrees `≥ 2` -/

/-- **`Rel(k) = 0` for `k ≥ 2`** for the pair `(Y, A)`: if `π_k(A) = 0` and `π_{k+1}(Y) = 0` then
the `k`-th homotopy group of the homotopy fibre of the inclusion vanishes.

Proof: the pair sequence (at the parameter `k - 2 ≥ 0` for `k ≥ 2`) is exact at `Rel(k)`, and the
map `π_{k+1}(Y) → Rel(k)` is trivial because `π_{k+1}(Y) = 0`; hence `Rel(k)` injects into
`π_k(A) = 0`. -/
theorem relPi_subsingleton_of_two_le {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (k : ℕ) (hk : 2 ≤ k)
    (hA : Subsingleton (HomotopyGroup (Fin k) ↥A a₀))
    (hY : Subsingleton (HomotopyGroup (Fin (k + 1)) Y (Work.RatHurewicz.setIncl A a₀))) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ k) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  subst hm
  obtain ⟨del, d, -, -, -, h4⟩ :=
    Work.RatHurewicz.pair_les (Work.RatHurewicz.setIncl A) a₀ (m + 1) (by omega)
  have hd : ∀ z : HomotopyGroup (Fin ((m + 1) + 2)) Y (Work.RatHurewicz.setIncl A a₀),
      d z = 1 := fun z => by rw [@Subsingleton.elim _ hY z 1, map_one]
  have hAt : Subsingleton (HomotopyGroup (Fin ((m + 1) + 1)) ↥A
      ((Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))) := hA
  have hinj : Function.Injective
      (⇑(Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)
        (m + 1) (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))) := by
    intro x y hxy
    have h1 : x * y⁻¹ = 1 := by
      have hg : (⇑(Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst
            (Work.RatHurewicz.setIncl A) a₀) (m + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀)))
          (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      obtain ⟨z, hz⟩ := (h4 (x * y⁻¹)).mp hg
      rw [← hz, hd z]
    rwa [mul_inv_eq_one] at h1
  exact ⟨fun p q => hinj (@Subsingleton.elim _ hAt _ _)⟩

/-! ## Relative vanishing implies the homology isomorphism -/

/-- **The long exact sequence of the pair, read as an isomorphism.**  If the relative homology
`H_n(Y,A;ℤ)` vanishes in every degree, then the inclusion `A ↪ Y` induces an isomorphism on
integral singular homology in every degree. -/
theorem isIso_inclChains_of_relVanishing {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (hrel : ∀ n : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of Y) A).homology n)) :
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) := by
  intro n
  have hmono : Mono (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) := by
    rw [(Work.Cohomology.hPair_exact₁ (TopCat.of Y) A n).mono_g_iff]
    exact IsZero.eq_of_src (hrel (n + 1)) _ _
  have hepi : Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) := by
    rw [(Work.Cohomology.hPair_exact₂ (TopCat.of Y) A n).epi_f_iff]
    exact IsZero.eq_of_tgt (hrel n) _ _
  haveI := hmono
  haveI := hepi
  exact isIso_of_mono_of_epi _

/-- **Compression in every dimension gives the homology isomorphism**: by the relative cone
construction (`Work.Serre.serreE2b`). -/
theorem isIso_inclChains_of_compress {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (hcomp : ∀ d : ℕ, Work.RatHurewicz.CompressRel Y A d) :
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) := by
  apply isIso_inclChains_of_relVanishing
  intro n
  obtain ⟨H⟩ := Work.Serre.simpHom_of_compress n (fun d _ => hcomp d)
  exact Work.Serre.simpHomVanishing H n le_rfl


end

end Work.Serre

namespace Work.Serre

noncomputable section

/-- **`PathConnectedSpace` of the homotopy fibre gives the vanishing of the relative `π₀`.** -/
theorem relPi_zero_subsingleton {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (h : PathConnectedSpace (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ 0) := by
  have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre
      (Work.RatHurewicz.setIncl A) a₀)) := (pathConnectedSpace_iff_zerothHomotopy.mp h).2
  have e := HomotopyGroup.pi0EquivZerothHomotopy
    (X := Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀)
    (x := Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀)
  exact ⟨fun p q => e.injective (@Subsingleton.elim _ hZ (e p) (e q))⟩

/-- **The pair lemma.**  For a path connected subspace `A ⊆ Y` such that the inclusion induces a
bijection on `π₁`, with `π_j(A) = π_j(Y) = 0` for `j ≥ 2`, and with the relative groups in degrees
`0` and `1` trivial (which hold by the geometric lemmas `homotopyFibre_pathConnected` and
`relPi_one_subsingleton`), the inclusion induces an isomorphism on integral singular homology in
every degree. -/
theorem pairHomologyIsoOfPiIso {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (hYc : PathConnectedSpace Y)
    (hpi1 : Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀))
    (hA2 : ∀ j : ℕ, 2 ≤ j → Subsingleton (HomotopyGroup (Fin j) ↥A a₀))
    (hY2 : ∀ j : ℕ, 2 ≤ j → Subsingleton (HomotopyGroup (Fin j) Y (Work.RatHurewicz.setIncl A a₀)))
    (hA : ∀ a : ↥A, Nonempty (Path a a₀))
    (hrel0 : Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ 0))
    (hrel1 : Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ 1)) :
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) := by
  apply isIso_inclChains_of_compress
  intro d
  have hconn : ∀ y : Y, ∃ a : ↥A, Nonempty (Path y a) :=
    fun y => ⟨a₀, PathConnectedSpace.joined y a₀⟩
  refine Work.RatHurewicz.compression_of_relPiVanishing (d - 1) hconn ?_ d (by omega)
  intro a k hk
  have h0 : Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ k) := by
    rcases lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact hrel0
      · exact hrel1
    · exact relPi_subsingleton_of_two_le a₀ k hk2 (hA2 k hk2) (hY2 (k + 1) (by omega))
  exact Work.RatHurewicz.subsingleton_relPiVanishing_of_path a₀ a (hA a).some.symm k h0


/-- **The pair lemma, with the low-degree hypotheses discharged** — the geometric lemmas
`homotopyFibre_pathConnected` and `relPi_one_subsingleton` provide the vanishing of the relative
groups in degrees `0` and `1`. -/
theorem pairHomologyIsoOfPiIso' {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (hYc : PathConnectedSpace Y)
    (hpi1 : Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀))
    (hA2 : ∀ j : ℕ, 2 ≤ j → Subsingleton (HomotopyGroup (Fin j) ↥A a₀))
    (hY2 : ∀ j : ℕ, 2 ≤ j → Subsingleton (HomotopyGroup (Fin j) Y (Work.RatHurewicz.setIncl A a₀)))
    (hA : ∀ a : ↥A, Nonempty (Path a a₀)) :
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of Y) A) n) :=
  pairHomologyIsoOfPiIso a₀ hYc hpi1 hA2 hY2 hA
    (relPi_zero_subsingleton a₀ (homotopyFibre_pathConnected a₀ hA hpi1.2))
    (relPi_one_subsingleton a₀ hpi1.1 (hY2 2 (by norm_num)))

end

end Work.Serre
