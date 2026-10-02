import Mathlib
import Submission.Work.PTGeometric.ContinuousToPreData
import Submission.Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close
import Submission.Work.PTGeometric.exists_Rmap_lipschitz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: from the raw ambient data of the source construction to `ContinuousAmbientData`

The source construction produces the *raw* ambient data of the null-homotopy on a compact source `M`:
a continuous `P : M → End (ℝⁿ)` with values in the Grassmannian, a continuous `v : M → ℝⁿ` with
`P x (v x) = v x`, and — this is the shape of the flat source homotopy — the data are `C^∞` only on a
**collar `V` of the collapse end** `S` (the null-homotopy of the collapse class is the explicit
concatenation of the pieces' collapse maps on the collar, and only continuous in the working zone).

`Work.PTGeometric.ContinuousAmbientData` asks for something stronger: the data must be `C^∞` on a
closed set `Sh` whose interior contains the *whole* boundary `∂M` (because the downstream smoothing
step `Work.PTGeometric.smoothMap_into_tautTotal_eqOn` keeps the values there, and the boundary
transversality is transferred by eventual equality).  The raw data do not have that property: the
source region's *cap* `{Φ = 0}` reaches into the working zone.

This file closes the gap in the standard way (`NOTE_REGION_OBSTRUCTION.md` §4.3): **pre-smooth
globally**, prescribing the values only on the closed collar `S0 ⊆ V` where they are already smooth,
and control the resulting vector part by **closeness** — `Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close`
returns `‖v' - v‖ < ε` for any `ε > 0`, and one takes `ε` below half the (positive) minimum of `‖v‖`
on `∂M ∖ S0`, which exists because the boundary zeros of `v` all lie in the interior of `S0`.  After
that the data are globally `C^∞`, so `Sh := univ` and `V := univ` fill every smoothness field.

## Main results

* `Work.PTGeometric.continuousAmbientData_of_rawData`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **From the raw ambient data of the source construction to `ContinuousAmbientData`.**

The hypotheses are exactly what the flat source homotopy and TUBULAR's tube data provide:

* `M` a compact `T2` smooth `(9+k)`-manifold with boundary, `P`, `v` the ambient coordinates
  (continuous, `P` Grassmannian-valued, `P v = v`), `C^∞` on the open collar `V`;
* `S0` a closed collar of the collapse end inside `V` (the set on which the raw data are already
  smooth and whose values are *kept* by the smoothing);
* `S` the collapse end: closed, inside `∂M` and inside `S0`, with
  `S ∩ {v = 0} ≃ Σ i, (Fam i).pt`; every boundary zero of `v` lies in `S0`;
* `δ > 0` below `‖v‖` on `∂M ∖ S0` (it exists since the boundary zeros of `v` are inside `S0`);
* the prescribed boundary charts at the pieces (`ellE j`, `UE j ⊆ interior S0`), on which `ℓ` is
  injective on the planes of `P` (even over `closure (UE j)`), they cover the boundary zeros of `v`,
  and `ℓ ∘ v` is a submersion at *every* boundary zero they cover.

The conclusion is the `ContinuousAmbientData` of `ContinuousToPreData.lean`, whose downstream
processing (`Work.PTGeometric.ambientPreData_of_continuous`) is already proved. -/
noncomputable def continuousAmbientData_of_rawData
    (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    (P : M → EndOp n) (v : M → Amb n)
    (hPc : Continuous P) (hvc : Continuous v)
    (hProj : ∀ x : M, P x ∈ Gr n k)
    (hMem : ∀ x : M, P x (v x) = v x)
    (V : Set M) (hVopen : IsOpen V)
    (S0 : Set M) (hS0cl : IsClosed S0) (hS0V : S0 ⊆ V)
    (hPsmV : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EndOp n)) ((⊤ : ℕ∞) : WithTop ℕ∞) P V)
    (hvsmV : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (Amb n)) ((⊤ : ℕ∞) : WithTop ℕ∞) v V)
    (S : Set M) (hScl : IsClosed S)
    (hSsub : S ⊆ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    (hSS0 : S ⊆ S0)
    (hend : ↥(S ∩ {x : M | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt))
    (hzero_sub : ∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M,
      v x = 0 → x ∈ S)
    (δ : ℝ) (hδpos : 0 < δ)
    (hδ : ∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M,
      x ∉ S0 → δ ≤ ‖v x‖)
    (mE : ℕ)
    (ellE : Fin mE → Amb n →L[ℝ] Amb k)
    (UE : Fin mE → Set M)
    (isOpen_UE : ∀ j, IsOpen (UE j))
    (UE_int : ∀ j, UE j ⊆ interior S0)
    (ellE_inj : ∀ j y, y ∈ UE j → ∀ z : Amb n, P y z = z → ellE j z = 0 → z = 0)
    (ellE_inj_cl : ∀ j, closure (UE j) ⊆
      {y : M | ∀ z : Amb n, P y z = z → ellE j z = 0 → z = 0})
    (bndZero_cov : ∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M,
      v x = 0 → ∃ j, x ∈ UE j)
    (bndZero_trans : ∀ j, ∀ x ∈ UE j,
      ∀ (hx : x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M), v x = 0 →
      IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => ellE j (v y)) x ∧
      IsSubmersionAt (modelWithCornersSelf ℝ (Amb (8 + k)))
        (modelWithCornersSelf ℝ (Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : ↥((modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) =>
          ellE j (v y)) ⟨x, hx⟩)
    (hk : k ≤ n) (hk0 : 0 < k) :
    ContinuousAmbientData n k ι Fam := by
  classical
  haveI : NeZero (8 + k + 1) := ⟨by omega⟩
  -- the boundary of `∂M` in the model is the hyperplane `x 0 = 0`
  have hbdry : (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M
      = (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M := rfl
  -- Lipschitz constant of the Grassmannian retraction, and the smoothing threshold
  let L : NNReal := Classical.choose (exists_Rmap_lipschitz n k hk)
  have hL : ∀ A Q : Work.PTGeometric.EndOp n, Q ∈ Work.PTGeometric.Gr n k →
      ‖A - Q‖ ≤ 1 / 8 → ‖Work.PTGeometric.Rmap A - Q‖ ≤ (L : ℝ) * ‖A - Q‖ :=
    Classical.choose_spec (exists_Rmap_lipschitz n k hk)
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hex := smoothMap_into_tautTotal_eqOn_close n k hk hk0 M P v hPc hvc S0 hS0cl V hVopen
    hS0V hPsmV hvsmV hProj hMem L hL ε hε
  let P' : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := Classical.choose hex
  let v' : M → EuclideanSpace ℝ (Fin n) := Classical.choose (Classical.choose_spec hex)
  have h1 := Classical.choose_spec (Classical.choose_spec hex)
  have hP'sm := h1.1
  have h2 := h1.2
  have hv'sm := h2.1
  have h3 := h2.2
  have hproj' := h3.1
  have h4 := h3.2
  have heqS0 := h4.1
  have hclose := h4.2
  -- the smoothed data are continuous
  have hP'c : Continuous P' := hP'sm.continuous
  have hv'c : Continuous v' := hv'sm.continuous
  have hmem' : ∀ x : M, P' x (v' x) = v' x := fun x => (hproj' x).2
  -- on the collar `S0` the smoothed data agree with the raw ones
  have heqP' : ∀ x ∈ S0, P' x = P x := fun x hx => (heqS0 x hx).1
  have heqv' : ∀ x ∈ S0, v' x = v x := fun x hx => (heqS0 x hx).2
  -- `v'` does not vanish on `∂M ∖ S0`
  have hne_off : ∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M,
      x ∉ S0 → v' x ≠ 0 := by
    intro x hx hxS0 hv'x
    have hδx : δ ≤ ‖v x‖ := hδ x hx hxS0
    have hcl : ‖v' x - v x‖ < δ / 2 := by
      have h := hclose x
      linarith [hεdef]
    have htri : ‖v x‖ ≤ ‖v' x‖ + ‖v' x - v x‖ := by
      have h1 := norm_sub_le (v' x) (v' x - v x)
      have hvv : v' x - (v' x - v x) = v x := by abel
      rw [hvv] at h1
      exact h1
    have h0 : ‖v' x‖ = 0 := by rw [hv'x, norm_zero]
    linarith
  -- the end identification for the smoothed data
  have hsetEnd : S ∩ {x : M | v' x = 0} = S ∩ {x : M | v x = 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxS, hx0⟩
      exact ⟨hxS, by rw [← heqv' x (hSS0 hxS)]; exact hx0⟩
    · rintro ⟨hxS, hx0⟩
      exact ⟨hxS, by rw [heqv' x (hSS0 hxS)]; exact hx0⟩
  -- the prescribed-chart transfer: `v' = v` on each `UE j`
  have hev_eq : ∀ j, ∀ y ∈ UE j, ellE j (v y) = ellE j (v' y) := fun j y hy =>
    congrArg (ellE j) (heqv' y (interior_subset (UE_int j hy))).symm ▸ rfl
  have hinj' : ∀ j y, y ∈ UE j → ∀ z : Amb n, P' y z = z → ellE j z = 0 → z = 0 := by
    intro j y hy z hz h0
    exact ellE_inj j y hy z (by rw [← heqP' y (interior_subset (UE_int j hy))]; exact hz) h0
  have hcl' : ∀ j, closure (UE j) ⊆
      {y : M | ∀ z : Amb n, P' y z = z → ellE j z = 0 → z = 0} := by
    intro j y hy z hz h0
    have hyS0 : y ∈ S0 := closure_minimal (fun w hw => interior_subset (UE_int j hw)) hS0cl hy
    rw [heqP' y hyS0] at hz
    exact ellE_inj_cl j hy z hz h0
  refine (⟨M, P', hP'c, fun x => (hproj' x).1, v', hv'c, hmem',
    Set.univ, isClosed_univ, (fun x _ => by rw [interior_univ]; exact Set.mem_univ x),
    Set.univ, isOpen_univ, Set.subset_univ _,
    hP'sm.contMDiffOn, hv'sm.contMDiffOn,
    S, hScl, hSsub,
    (Homeomorph.setCongr hsetEnd).trans hend,
    ?_, mE, ellE, UE, isOpen_UE,
    (fun j => Set.subset_univ _), hinj', hcl', ?_, ?_⟩ : ContinuousAmbientData n k ι Fam)
  · -- `avoid`
    intro x hx hxS
    by_cases hxS0 : x ∈ S0
    · intro hv'x
      have hx0 : v x = 0 := by rw [← heqv' x hxS0]; exact hv'x
      exact hxS (hzero_sub x hx hx0)
    · exact hne_off x hx hxS0
  · -- `bndZero_cov`
    intro x hx hv'x
    by_cases hxS0 : x ∈ S0
    · exact bndZero_cov x hx (by rw [← heqv' x hxS0]; exact hv'x)
    · exact absurd hv'x (hne_off x hx hxS0)
  · -- `bndZero_trans`
    intro j x hxUE hx hv'x
    have hvx : v x = 0 := by
      rw [← heqv' x (interior_subset (UE_int j hxUE))]
      exact hv'x
    obtain ⟨h1, h2⟩ := bndZero_trans j x hxUE hx hvx
    refine ⟨h1.congr_of_eventuallyEq ?_, h2.congr_of_eventuallyEq ?_⟩
    · rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨UE j, (isOpen_UE j).mem_nhds hxUE, fun y hy => by
        simp only; rw [← hev_eq j y hy]⟩
    · rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Subtype.val ⁻¹' UE j,
        (((isOpen_UE j).preimage continuous_subtype_val).mem_nhds ?_), fun y hy => ?_⟩
      · exact hxUE
      · simp only at hy ⊢
        rw [← hev_eq j y.val hy]

end

end Work.PTGeometric
