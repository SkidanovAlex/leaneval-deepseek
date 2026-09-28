import Mathlib
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh

/-!
# The rational homology of a Serre fibration over a weakly contractible base

Let `q : X → B` be a Serre fibration whose base `B` is path connected and *weakly* contractible
(all its homotopy groups vanish, `hBc`), and whose fibre `F = q⁻¹{b₀}` is path connected, with
rational homology concentrated in degree `r` and equal to `ℚ` there.  Then the same is true of the
total space `X`.

The proof has three steps, all of which are already available in the workspace:

* **the base is rationally acyclic.**  `Work.Serre.serreE0Range` (Serre's `E0` in range form)
  applied to the weak contractibility of `B` gives `H_j(B;ℚ) = 0` for `0 < j ≤ N+1`.
* **the pair `(B, {b₀})` and the pair `(X, F)` have the same relative homology.**  This is the
  stable-range Serre pair comparison `Work.Serre.ratSerrePairComparison` with connectivity
  parameters `b = N+1` (the base) and `f = r` (the fibre): it identifies `H_i(X, F;ℚ)` with
  `H_i(B, {b₀};ℚ)` for every `i < (N+1) + r`, and the relative homology of `(B, {b₀})` vanishes in
  degrees `1 ≤ i ≤ N+1` because `B` is path connected and rationally acyclic
  (`Work.Serre.DiscPair.isZero_relChainsR_point_of_isZero_ratH`).  Hence `H_i(X, F;ℚ) = 0` for
  `1 ≤ i ≤ N+1`.
* **the long exact sequence of the pair `(X, F)`** (the rational pair sequence
  `Work.StemsB.relChainsR_exact₁/₂/₃`) then identifies `H_t(X;ℚ)` with `H_t(F;ℚ)` in the range
  `1 ≤ t ≤ N`: `H_t(X,F) = 0` gives surjectivity of the inclusion-induced map (exactness at
  `H_t(X)`) and `H_{t+1}(X,F) = 0` gives its injectivity (exactness at `H_t(F)`).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option linter.style.haveILetI false

/-- **The inclusion of a subspace is an isomorphism on rational homology in degree `t` as soon as
the relative rational homology of the pair vanishes in degrees `t` and `t+1`.**

Exactness of the pair sequence at `H_t(X)` and at `H_t(A)`
(`Work.StemsB.relChainsR_exact₁/₂`) makes the map `H_t(A;ℚ) → H_t(X;ℚ)` monomorphic (the connecting
map `H_{t+1}(X,A;ℚ) → H_t(A;ℚ)` is zero) and epimorphic (the map `H_t(X;ℚ) → H_t(X,A;ℚ)` is
zero). -/
theorem nonempty_ratH_iso_of_isZero_rel (X : Type) [TopologicalSpace X] (A : Set X) (t : ℕ)
    (h1 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology (t + 1)))
    (h2 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology t)) :
    Nonempty ((Work.Cohomology.singularChains ℚ (TopCat.of A)).homology t ≅
      (Work.Cohomology.singularChains ℚ (TopCat.of X)).homology t) := by
  have hS1 := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of X) A t
  have hS2 := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) A t
  have hmono : Mono
      (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) t) :=
    hS1.mono_g_iff.mpr (IsZero.eq_zero_of_src h1 _)
  have hepi : Epi
      (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) t) :=
    hS2.epi_f_iff.mpr (IsZero.eq_zero_of_tgt h2 _)
  haveI := hmono
  haveI := hepi
  haveI : IsIso
      (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) t) :=
    isIso_of_mono_of_epi _
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) t)⟩

theorem ratH_of_contractible_base {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q)
    (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) r ≅ ModuleCat.of ℚ ℚ)) :
    (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) t)) ∧
    Nonempty (Work.Serre.ratH (TopCat.of X) r ≅ ModuleCat.of ℚ ℚ) := by
  classical
  haveI : PathConnectedSpace B := hB
  haveI : PathConnectedSpace X := hX
  haveI hFpc : PathConnectedSpace ↥(q ⁻¹' ({b₀} : Set B)) := hpc
  -- (1) `B` is rationally acyclic: `H_j(B;ℚ) = 0` for `0 < j ≤ N+1`.
  have hE0B : ∀ j : ℕ, 0 < j → j < N + 2 →
      IsZero (Work.Serre.ratH (TopCat.of B) j) :=
    Work.Serre.serreE0Range B b₀ (N + 1) (fun i _ => hBc i)
  -- (2) the relative rational homology of `(B, {b₀})` vanishes in degrees `1, …, N+1`.
  have hBrel : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology k) :=
    fun k hk1 hkN => isZero_relChainsR_point_of_isZero_ratH B b₀ k (by omega)
      (hE0B k (by omega) (by omega))
  -- (3) the Serre pair comparison: `H_i(X, q⁻¹{b₀};ℚ) ≅ H_i(B, {b₀};ℚ)` for `i < (N+1) + r`.
  have hcmp := (Work.Serre.ratSerrePairComparison q hq b₀ (N + 1) r (by omega) hr hX hB
    (fun i _ => hBc i) hpc (fun j hj hjr => hvan j hj (by omega) (by omega))).1
  have hXrel : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 →
      IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))).homology k) :=
    fun k hk1 hkN =>
      IsZero.of_iso (hBrel k hk1 hkN) (Classical.choice (hcmp k (by omega)))
  refine ⟨?_, ?_⟩
  · -- the absolute homology of `X` in degree `t ≠ r` vanishes
    intro t ht htr htN
    have hrel : IsZero
        ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B))).homology t) :=
      hXrel t (by omega) (by omega)
    have hF := hvan t ht htr htN
    exact (Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) (q ⁻¹' ({b₀} : Set B)) t).isZero_X₂
      (IsZero.eq_zero_of_src hF _) (IsZero.eq_zero_of_tgt hrel _)
  · -- in degree `r` the inclusion of the fibre is an isomorphism
    obtain ⟨e⟩ := nonempty_ratH_iso_of_isZero_rel X (q ⁻¹' ({b₀} : Set B)) r
      (hXrel (r + 1) (by omega) (by omega)) (hXrel r (by omega) (by omega))
    exact ⟨e.symm ≪≫ (Classical.choice hgen)⟩

end

end Work.Serre.DiscPair
