import Mathlib
import Submission.Work.Rat.s1Sphere
import Submission.Work.RatHurewicz.fibreRangeVanishing
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.RatHurewicz.isHurewiczFibration_trackMap
import Submission.Work.RatHurewicz.injective_homologyMap_trackProj
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.Serre.serreE0Range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Rat

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

/-! ## The mapping track of a map out of a path-connected space

The mapping track `Work.RatHurewicz.Track inc` of a continuous map `inc : X → Z` is the space of
pairs `(x, γ)` with `γ` a path in `Z` ending at `inc x`, and the projection
`trackProj inc : Track inc → X`, `(x,γ) ↦ x`, is a homotopy equivalence (with homotopy inverse the
constant-path section `trackSec inc`).  It is then path connected as soon as `X` is. -/

/-- **The mapping track of a map out of a path-connected space is path connected.** -/
private theorem track_pathConnected {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    [PathConnectedSpace X] (inc : C(X, Z)) :
    PathConnectedSpace (Work.RatHurewicz.Track inc) := by
  have H := Work.RatHurewicz.trackProj_trackSec_homotopy inc
  have hpath : ∀ z : Work.RatHurewicz.Track inc,
      Joined (Work.RatHurewicz.trackSec inc (Work.RatHurewicz.trackProj inc z)) z :=
    fun z => ⟨{ toFun := fun s => H (s, z)
                continuous_toFun := H.continuous_toFun.comp (continuous_id.prodMk continuous_const)
                source' := H.map_zero_left z
                target' := H.map_one_left z }⟩
  have hne : Nonempty X := (inferInstance : PathConnectedSpace X).nonempty
  refine ⟨⟨Work.RatHurewicz.trackSec inc hne.some⟩, fun x y => ?_⟩
  exact (hpath x).symm.trans
    (((PathConnectedSpace.joined (Work.RatHurewicz.trackProj inc x)
        (Work.RatHurewicz.trackProj inc y)).map
      (Work.RatHurewicz.trackSec inc).continuous_toFun).trans (hpath y))

/-- The homotopy equivalence `Track inc ≃ X` given by the projection of the mapping track. -/
private def trackHomotopyEquiv {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) : ContinuousMap.HomotopyEquiv (Work.RatHurewicz.Track inc) X where
  toFun := Work.RatHurewicz.trackProj inc
  invFun := Work.RatHurewicz.trackSec inc
  left_inv := ⟨Work.RatHurewicz.trackProj_trackSec_homotopy inc⟩
  right_inv := ⟨Work.RatHurewicz.trackSec_trackProj_homotopy inc⟩

/-! ## One step of the fibre-acyclicity bootstrap -/

/-- **One step of the fibre-acyclicity bootstrap from the rational pair comparison.**

Let `p : E → B` be a Serre fibration with `B` `(b-1)`-connected (`b ≥ 2`), `E`, `B` and the strict
fibre `F = p⁻¹{b₀}` path connected, and the fibre rationally acyclic below `n` (`n ≥ 1`).
If `H_n(E;ℚ) = 0` and the *relative* rational homology of the pair `(B,{b₀})` vanishes in degree
`n+1`, then `H_n(F;ℚ) = 0`.

Proof: the pair comparison `Work.RatHurewicz.ratPairComparison_proof` at `(b, f) = (b, n)` (its
range `b + n` contains `n + 1` since `b ≥ 2`) identifies `H_{n+1}(E,F;ℚ) ≅ H_{n+1}(B,{b₀};ℚ)`,
which vanishes; in the long exact sequence of the pair `(E,F)`
(`Work.StemsB.relChainsR_exact₁`) both the connecting map `H_{n+1}(E,F) → H_n(F)` and the map
`H_n(F) → H_n(E)` are then zero (the latter since `H_n(E) = 0`), forcing `H_n(F) = 0`. -/
private theorem fibreIsZero_step {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b n : ℕ)
    (hb : 2 ≤ b) (hn : 1 ≤ n)
    (hE : PathConnectedSpace E) (hB : PathConnectedSpace B)
    (hconn : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < n →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j))
    (hEvan : CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of E) n))
    (hBrel : CategoryTheory.Limits.IsZero
      (Work.RatHurewicz.relHRat (TopCat.of B) ({b₀} : Set B) (n + 1))) :
    CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) n) := by
  obtain ⟨hpair, -⟩ :=
    Work.RatHurewicz.ratPairComparison_proof p hp b₀ b n hb hn hE hB hconn hfib0 hfib
  have hrel : CategoryTheory.Limits.IsZero
      (Work.RatHurewicz.relHRat (TopCat.of E) (p ⁻¹' {b₀}) (n + 1)) :=
    IsZero.of_iso hBrel (hpair (n + 1) (by omega)).some
  have hS := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of E) (p ⁻¹' {b₀}) n
  exact hS.isZero_X₂ (IsZero.eq_zero_of_src hrel _) (IsZero.eq_zero_of_tgt hEvan _)

/-! ## The main theorem -/

/-- **Fibre acyclicity from two-column base and total rational homology.**

Let `g : X → P` be a based map of path-connected spaces, `x₀ ∈ X`, `p₀ = g x₀`, and let
`F := homotopyFibre g x₀` be its homotopy fibre.  Suppose

* `P` is `(d-1)`-connected (`d ≥ 2`) and `F` is `d`-connected;
* the rational homology of the *base* `P` is "two-column" in the range: `H_i(P;ℚ) = 0` for
  `0 < i ≤ M+1`, `i ≠ d`, and `H_d(P;ℚ) ≅ ℚ`;
* the rational homology of the *total space* `X` has the same two-column shape: `H_i(X;ℚ) = 0` for
  `0 < i ≤ M`, `i ≠ d`, and `H_d(X;ℚ) ≅ ℚ`.

Then `H_i(F;ℚ) = 0` for `d < i ≤ M`.

Intended proof (no spectral sequence needed): replace `g` by its mapping track
(`Work.RatHurewicz.trackSetup` / `trackFibreHomeo`, `isHurewiczFibration_trackMap`), a Serre
fibration over `P` with the same `X` up to homotopy equivalence and strict fibre `≅ F`.  Then argue
by strong induction on `i` with the rational pair comparison
(`Work.RatHurewicz.ratPairComparison_proof`) applied at base-connectivity `b = d` and
fibre-acyclicity parameter `f = i` — legitimate, because the induction hypothesis gives the fibre's
rational vanishing for `0 < j < i`, and the fibre's `d`-connectivity (`hconnF`) gives it for
`j ≤ d`.  The comparison (valid for `i+1 < b+f = d+i`, i.e. for all `i ≥ 2` when `d ≥ 2`)
identifies `H_{i+1}(E,A;ℚ) ≅ H_{i+1}(P,{p₀};ℚ)` and `H_i(E,A;ℚ) ≅ H_i(P,{p₀};ℚ)`, which vanish for
degrees `≠ d`; the long exact sequence of the pair `(E,A)` (`Work.StemsB.relChainsR_exact₁/₂/₃`)
then gives `H_i(F;ℚ) ≅ H_i(X;ℚ) = 0`.  (The conclusion range starts at `i = d+1`, so no exceptional
degree `i = d` occurs.)  `hPgen`/`hXgen` are not needed by this route. -/
theorem fibreAcyclicOfTwoColumn {X P : Type} [TopologicalSpace X] [TopologicalSpace P]
    (g : C(X, P)) (x₀ : X) (p₀ : P) (hgp : g x₀ = p₀)
    [PathConnectedSpace X] [PathConnectedSpace P]
    (d M : ℕ) (hd : 2 ≤ d)
    (hconnP : ∀ i : ℕ, i < d → Subsingleton (HomotopyGroup (Fin i) P p₀))
    (hconnF : ∀ i : ℕ, i ≤ d → Subsingleton (HomotopyGroup (Fin i)
        (Work.RatHurewicz.homotopyFibre g x₀) (Work.RatHurewicz.homotopyFibreBasepoint g x₀)))
    (hPvan : ∀ i : ℕ, 0 < i → i ≤ M + 1 → i ≠ d →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of P) i))
    (hPgen : Nonempty (Work.Serre.ratH (TopCat.of P) d ≅ ModuleCat.of ℚ ℚ))
    (hXvan : ∀ i : ℕ, 0 < i → i ≤ M → i ≠ d →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i))
    (hXgen : Nonempty (Work.Serre.ratH (TopCat.of X) d ≅ ModuleCat.of ℚ ℚ)) :
    ∀ i : ℕ, d < i → i ≤ M →
      CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre g x₀)) i) := by
  -- the mapping track of `g` is a Serre fibration over `P` with total space `≃ X`
  have hpcTrack : PathConnectedSpace (Work.RatHurewicz.Track g) := track_pathConnected g
  have hserre : Work.StemsB.IsSerreFibration (Work.RatHurewicz.trackMap g) :=
    Work.StemsB.IsHurewiczFibration.isSerreFibration
      (Work.RatHurewicz.isHurewiczFibration_trackMap g)
  -- connectivity of `P` at the base point `g x₀`
  have hconnG : ∀ k : ℕ, k < d → Subsingleton (HomotopyGroup (Fin k) P (g x₀)) :=
    fun k hk => hgp.symm ▸ hconnP k hk
  have h1P : Subsingleton (HomotopyGroup (Fin 1) P (g x₀)) := hconnG 1 (by omega)
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.RatHurewicz.trackMap g) (g x₀)) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.RatHurewicz.trackMap g) hserre
      (g x₀) hpcTrack (inferInstance : PathConnectedSpace P) h1P
  -- the strict fibre of the track fibration is the homotopy fibre of `g`
  have eHomeo : Work.RatHurewicz.homotopyFibre g x₀ ≃ₜ
      ↥(Work.RatHurewicz.trackFibre g (g x₀)) :=
    Classical.choose (Work.RatHurewicz.trackFibreHomeo g x₀)
  -- the fibre is rationally acyclic below `d + 1` (it is `d`-connected)
  have hFbelow : ∀ j : ℕ, 0 < j → j ≤ d →
      IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre g x₀)) j) := by
    intro j hj hjd
    exact Work.Serre.serreE0Range (Work.RatHurewicz.homotopyFibre g x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint g x₀) d hconnF j hj (by omega)
  -- the relative rational homology of `(P, {g x₀})` vanishes above `d` (up to `M + 1`)
  have hBrel : ∀ k : ℕ, d < k → k ≤ M + 1 →
      IsZero (Work.RatHurewicz.relHRat (TopCat.of P) ({g x₀} : Set P) k) := by
    intro k hdk hkM
    have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
    obtain ⟨e⟩ := Work.RatHurewicz.nonempty_iso_of_eq
      (congrArg (fun t => Work.Serre.ratH (TopCat.of P) t) hk1)
      (congrArg (fun t => Work.RatHurewicz.relHRat (TopCat.of P) ({g x₀} : Set P) t) hk1)
      (Work.RatHurewicz.nonempty_iso_cokernelπ_of_isZero (TopCat.of P) ({g x₀} : Set P) (k - 1)
        (Work.RatHurewicz.isZero_ratH_singleton (g x₀) (by omega))
        (Work.RatHurewicz.isZero_ratH_singleton (g x₀) (by omega)))
    exact IsZero.of_iso (hPvan k (by omega) hkM (by omega)) e.symm
  -- strong induction on the degree
  intro i
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hle
    -- the strict fibre is rationally acyclic below `n`
    have hfib : ∀ j : ℕ, 0 < j → j < n →
        IsZero (Work.Serre.ratH
          (TopCat.of (Work.StemsB.fibre (Work.RatHurewicz.trackMap g) (g x₀))) j) := by
      intro j hj hjn
      by_cases hjd : j ≤ d
      · exact Work.Stems.isZero_ratH_of_homotopyEquiv (eHomeo.symm.toHomotopyEquiv) j
          (hFbelow j hj hjd)
      · have hjd' : d < j := Nat.lt_of_not_le hjd
        exact Work.Stems.isZero_ratH_of_homotopyEquiv (eHomeo.symm.toHomotopyEquiv) j
          (ih j hjn hjd' (by omega))
    -- the total space of the track fibration is rationally acyclic in degree `n`
    have hEvan : IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.Track g)) n) :=
      Work.Stems.isZero_ratH_of_homotopyEquiv (trackHomotopyEquiv g) n
        (hXvan n (by omega) hle (by omega))
    -- one step of the bootstrap
    have hstep := fibreIsZero_step (Work.RatHurewicz.trackMap g) hserre (g x₀) d n hd (by omega)
      hpcTrack (inferInstance : PathConnectedSpace P) hconnG hfib0 hfib hEvan
      (hBrel (n + 1) (by omega) (by omega))
    -- transfer back to the homotopy fibre
    exact Work.Stems.isZero_ratH_of_homotopyEquiv eHomeo.toHomotopyEquiv n hstep

end

end Work.Rat
