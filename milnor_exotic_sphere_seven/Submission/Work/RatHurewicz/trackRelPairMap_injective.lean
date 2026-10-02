import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.isHurewiczFibration_trackMap
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.RatHurewicz.trackCompressRel
import Submission.Work.RatHurewicz.trackRelPairMapDefs
import Submission.Work.RatHurewicz.truncationHomologyTransfer_of_serre
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreK2
import Submission.Work.RatHurewicz.fibrationPairMap_injective_stableRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The level-wise compression lemma

`Work.RatHurewicz.compression_of_relPiVanishing` derives the compression property
`CompressRel Y A d` for all `d ≤ n+1` from the vanishing of the relative homotopy groups *in all
indices* `k ≤ n`.  Its proof, however, uses the hypothesis only at the single index `d - 1`
(the "pinched model" reduction of tom Dieck (6.7.3) turns a map of pairs into a *pinched* map —
i.e. a based map of the `k`-sphere — using only `π_{d-1}(Y,A) = 0`).

We record that level-wise form: the compression property in dimension `d` already follows from the
vanishing of the relative homotopy group in the *single* dimension `d - 1`.  This is what makes the
compression available in a range with one exceptional degree. -/
theorem compressRel_of_relPiVanishing_index {Y : Type} [TopologicalSpace Y] {A : Set Y} (d : ℕ)
    (hconn : ∀ y : Y, ∃ a : ↥A, Nonempty (Path y a))
    (hvan : ∀ a : ↥A, Subsingleton (RelHomotopyGroup (setIncl A) a (d - 1))) :
    CompressRel Y A d := by
  classical
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · -- the zero-dimensional case is exactly the `0`-connectivity hypothesis
    subst h0
    intro f hf
    obtain ⟨a, ⟨γ⟩⟩ := hconn (f (fun i : Fin 0 => i.elim0))
    refine ⟨⟨fun p : ICube 0 × I => γ p.2, γ.continuous.comp continuous_snd⟩, ?_, ?_, ?_⟩
    · intro x
      show γ (0 : I) = f x
      rw [show x = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
      exact γ.source'
    · intro x hx t
      obtain ⟨i, -⟩ := hx
      exact i.elim0
    · intro x
      show γ.toFun (1 : I) ∈ A
      rw [γ.target']
      exact a.2
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hvan' : ∀ a : ↥A, Subsingleton (RelHomotopyGroup (setIncl A) a e) := by
      intro a
      have h := hvan a
      simpa using h
    intro f hf
    obtain ⟨H1, hH10, hH1A, hH1pinch⟩ := exists_pinch e f hf
    have hvan'' : Subsingleton (RelHomotopyGroup (setIncl A)
        ⟨f (pinchBase e), hf _ (pinchBase_mem_boundary e)⟩ e) :=
      hvan' _
    obtain ⟨L, hL0, hLA, hL1⟩ := pinchedMap_nullHomotopic e
      ⟨f (pinchBase e), hf _ (pinchBase_mem_boundary e)⟩ hvan''
      ⟨fun x => H1 (x, 1), by fun_prop⟩ hH1pinch (fun x hx => hH1A x hx 1)
    set Gfun : ICube (e + 1) × I → Y := fun p =>
      if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then H1 (p.1, clampI (2 * (p.2 : ℝ)))
      else L (p.1, clampI (2 * (p.2 : ℝ) - 1)) with Gfun_def
    have hGcont : Continuous Gfun := by
      rw [Gfun_def]
      refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
      · exact H1.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
      · exact L.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
      · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
      · exact continuous_const
      · intro p hp
        have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
        have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
          have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
          rw [h2', clampI_zero']
        rw [h1, h2]
        exact (hL0 p.1).symm
    have hGle : ∀ p : ICube (e + 1) × I, (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
        Gfun p = H1 (p.1, clampI (2 * (p.2 : ℝ))) := by
      intro p h
      rw [Gfun_def]
      exact if_pos h
    have hGgt : ∀ p : ICube (e + 1) × I, ¬ (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
        Gfun p = L (p.1, clampI (2 * (p.2 : ℝ) - 1)) := by
      intro p h
      rw [Gfun_def]
      exact if_neg h
    have hG0 : ∀ x : ICube (e + 1), Gfun (x, 0) = f x := by
      intro x
      rw [hGle (x, 0) (by norm_num),
        show (2 : ℝ) * (((0 : I) : ℝ)) = 0 by norm_num, clampI_zero']
      exact hH10 x
    have hGbd : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → ∀ t : I, Gfun (x, t) ∈ A := by
      intro x hx t
      by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
      · rw [hGle (x, t) h]
        exact hH1A x hx _
      · rw [hGgt (x, t) h]
        exact hLA x hx _
    have hG1 : ∀ x : ICube (e + 1), Gfun (x, 1) ∈ A := by
      intro x
      rw [hGgt (x, 1) (by norm_num),
        show (2 : ℝ) * (((1 : I) : ℝ)) - 1 = 1 by norm_num, clampI_one']
      rw [hL1 x]
      exact hf _ (pinchBase_mem_boundary e)
    exact Triad.compressRel_of_homotopyPairs f ⟨Gfun, hGcont⟩ hG0 hGbd hG1

/-! ## The target in the range `n + 2 ≤ k - 1` -/

/-- **The vanishing of the relative homology of the track pair in the range `n+2 ≤ k-1`**, from
the compression property of the track pair in the dimensions `d ≤ k-1` (the dimensions where the
range model `Z` has vanishing `π_d`). -/
theorem trackRelPair_relChains_isZero {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hkn : n + 2 ≤ k - 1) :
    IsZero ((Work.Cohomology.relChains (TopCat.of (Work.RatHurewicz.Track inc))
      (Work.RatHurewicz.trackFibre inc (inc x₀))).homology (n + 2)) := by
  have hcomp : Work.Serre.CompressHyp (Work.RatHurewicz.Track inc)
      (Work.RatHurewicz.trackFibre inc (inc x₀)) (k - 1) := by
    intro d hd
    exact Work.RatHurewicz.trackCompressRel inc x₀ k d hmodel (by omega) (by omega)
  obtain ⟨H⟩ := Work.Serre.simpHom_of_compress (X := Work.RatHurewicz.Track inc)
    (A := Work.RatHurewicz.trackFibre inc (inc x₀)) (k - 1) hcomp
  exact Work.Serre.simpHomVanishing H (n + 2) (by omega)

/-- **The target in the range `n + 2 ≤ k - 1`.** -/
theorem trackRelPairMap_injective_of_le {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hkn : n + 2 ≤ k - 1) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap inc) (inc x₀)) (n + 2)).hom := by
  haveI : Subsingleton (↥((Work.Cohomology.relChains (TopCat.of (Work.RatHurewicz.Track inc))
      (Work.RatHurewicz.trackFibre inc (inc x₀))).homology (n + 2))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (trackRelPair_relChains_isZero inc x₀ k n hk hmodel hkn)
  intro x y _
  exact Subsingleton.elim x y

/-! ## Reduction of the target to the general stable-range statement for fibrations -/

/-- **The target reduces to the general injectivity statement for Hurewicz fibrations**: applied to
the track fibration `trackMap inc : Track inc → Z` (a Hurewicz fibration with fibre
`trackFibre inc (inc x₀)`), whose base is a range model by `hmodel` and whose fibre is `k`-connected
by `hconn` (transported along `trackFibreHomeo`). -/
theorem trackRelPairMap_injective_of_fibrationPairMap
    (hG : ∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)),
      Work.StemsB.IsHurewiczFibration p → ∀ (e₀ : E) (k : ℕ), 2 ≤ k →
      (∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k → Subsingleton (HomotopyGroup (Fin j) B (p e₀))) →
      (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩)) →
      ∀ i : ℕ, i ≤ 2 * k - 1 →
        Function.Injective
          (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i).hom)
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (Work.RatHurewicz.homotopyFibre inc x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 2) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap inc) (inc x₀)) (n + 2)).hom := by
  have hconn' : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (↥((Work.RatHurewicz.trackMap inc) ⁻¹'
        {Work.RatHurewicz.trackMap inc (Work.RatHurewicz.trackBase inc x₀)}))
      ⟨Work.RatHurewicz.trackBase inc x₀, rfl⟩) := by
    intro j hj
    have h := Work.RatHurewicz.subsingleton_homotopyGroup_trackFibre inc x₀
      (f := k + 1) (fun i hi => hconn i (by omega)) j (by omega)
    exact h
  exact hG (Work.RatHurewicz.trackMap inc) (Work.RatHurewicz.isHurewiczFibration_trackMap inc)
    (Work.RatHurewicz.trackBase inc x₀) k hk hmodel hconn' (n + 2) (by omega)

/-! ## The target -/

/-- The stable-range Serre comparison for the mapping track, in the injectivity form that the truncation transfer consumes: for the track fibration of an arbitrary continuous map whose homotopy fibre is `k`-connected and whose target is a range model of `K(π_k X,k)` up to `2k-1`, the comparison map of pairs `(Track, fibre) → (Z, {z₀})` is injective on homology in degree `n+2` whenever `n+1 ≤ 2k-2`. This is the injectivity half of Serre's exact sequence in the stable range (K5 of `Submission/Work/Drive/SERRE_BLUEPRINT.md`) for the mapping track. -/
theorem trackRelPairMap_injective {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k n : ℕ) (hk : 2 ≤ k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (Work.RatHurewicz.homotopyFibre inc x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint inc x₀)))
    (hrange : n + 1 ≤ 2 * k - 2) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (Work.RatHurewicz.trackMap inc) (inc x₀)) (n + 2)).hom :=
  trackRelPairMap_injective_of_fibrationPairMap
    (fun p hp e₀ k hk hmodel hconn i hi =>
      fibrationPairMap_injective_stableRange p hp e₀ k hk hmodel hconn i hi)
    inc x₀ k n hk hmodel hconn hrange

end

end Work.RatHurewicz
