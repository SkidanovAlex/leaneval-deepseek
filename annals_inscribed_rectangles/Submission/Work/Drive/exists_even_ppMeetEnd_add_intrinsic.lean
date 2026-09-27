import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.ppMeetEnd_even
import Submission.Work.Drive.ppIntrinsic.Defs
import Submission.Work.Drive.ppIntrinsic.FlowGen
import Submission.Work.Drive.ppIntrinsic.Smooth
import Submission.Work.Drive.ppIntrinsic.ppMeet_localGraph_Zpp
import Submission.Work.Drive.ppIntrinsic.flowGen_mapsTo_of_localGraph
import Submission.Work.Drive.ppIntrinsic.finite_and_even_ncard_bdry_of_localGraph
import Submission.Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Euclidean.TangentField.exists_smooth_tangent_field

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The chart-free pair equation set is closed** (for continuous chains). -/
theorem isClosed_Zpp_of_contMDiff
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    IsClosed (Zpp E E' V W) :=
  isClosed_Zpp E E' V W hE.continuous hE'.continuous hV.continuous hW.continuous

/-- **The pair meet set is compact.** -/
theorem isCompact_ppMeet
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    IsCompact (ppMeet E E' V W) := by
  rw [ppMeet_eq_Zpp_inter]
  exact (isCompact_unitBox 8).of_isClosed_subset
    ((isClosed_Zpp_of_contMDiff E E' V W hE hE' hV hW).inter (isClosed_unitBox 8))
    (fun x hx => hx.2)

/-- **The local graph data of the pair meet set** (the hypothesis `hgra` of the generic parity
engine), obtained from `PPRegAt` by choosing the coordinate with `exists_domRestrict_surjective`. -/
theorem exists_localGraph_Zpp
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ ppMeet E E' V W, PPRegAt E E' V W x) :
    ∀ x ∈ ppMeet E E' V W, ∃ (i : Fin 9) (U : Set (EuclideanSpace ℝ (Fin 9)))
        (η : ℝ → EuclideanSpace ℝ (Fin 9)),
      IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
      ∀ y ∈ U, (y ∈ Zpp E E' V W ↔
        y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)) := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_domRestrict_surjective (hreg x hx).1
  obtain ⟨U, η, hU, hxU, hη, hηi, hgr⟩ :=
    ppIntrinsic.ppMeet_localGraph_Zpp E E' V W hE hE' hV hW hx (hreg x hx) i hi
  exact ⟨i, U, η, hU, hxU, hη, hηi, hgr⟩

/-- **The face data** (the hypothesis `hface` of the generic parity engine): at a boundary meet the
face coordinate of `PPRegAt` is the coordinate in which the tangent field does not vanish, because
the field is parallel to the graph tangent `eᵢ + η'`. -/
theorem ppMeet_faceData
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ ppMeet E E' V W, PPRegAt E E' V W x)
    (Vf : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9))
    (hVfpar : ∀ x ∈ ppMeet E E' V W, ∀ (i : Fin 9) (U : Set (EuclideanSpace ℝ (Fin 9)))
        (η : ℝ → EuclideanSpace ℝ (Fin 9)),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ U, (y ∈ Zpp E E' V W ↔
          y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ Vf x = c • (EuclideanSpace.single i (1 : ℝ) +
          (fderiv ℝ η (x i)) (1 : ℝ))) :
    ∀ b ∈ ppMeet E E' V W ∩ Submission.Drive.unitBoxBdry 8,
      ∃ i : Fin 9, (b i = 0 ∨ b i = 1) ∧
        (∀ j : Fin 9, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧ Vf b i ≠ 0 := by
  intro b hb
  obtain ⟨hbK, hbB⟩ := hb
  obtain ⟨i, hi, hoth, hsurj_i⟩ := (hreg b hbK).2 hbB
  obtain ⟨U, η, hU, hbU, hη, hηi, hgr⟩ :=
    ppIntrinsic.ppMeet_localGraph_Zpp E E' V W hE hE' hV hW hbK (hreg b hbK) i hsurj_i
  obtain ⟨c, hc, hcx⟩ := hVfpar b hbK i U η hU hbU hη hηi hgr
  refine ⟨i, hi, hoth, ?_⟩
  have hsingle : (EuclideanSpace.single (i : Fin 9) (1 : ℝ) :
      EuclideanSpace ℝ (Fin 9)) i = 1 := by simp
  have hderiv_i : ((fderiv ℝ η (b i)) (1 : ℝ)) i = 0 := by
    set ℓ : ℝ → ℝ := fun t => (η t) i with hℓ
    have hproj_eq : (fun v : EuclideanSpace ℝ (Fin 9) => v i)
        = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) i) := by
      funext v
      rw [PiLp.proj_apply]
    have h2 : fderiv ℝ ℓ (b i)
        = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) i).comp (fderiv ℝ η (b i)) := by
      rw [hℓ, show (fun t : ℝ => (η t) i)
        = (fun v : EuclideanSpace ℝ (Fin 9) => v i) ∘ η from rfl, hproj_eq]
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) i).hasFDerivAt.comp (b i)
        (hη.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
    have h3 : (fderiv ℝ η (b i) (1 : ℝ)) i = fderiv ℝ ℓ (b i) 1 := by
      rw [h2, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    have hℓid : ℓ = fun _ : ℝ => (0 : ℝ) := by
      funext t
      simp [hℓ, hηi t]
    rw [h3, hℓid]
    simp
  rw [hcx, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply, hsingle, hderiv_i, add_zero, mul_one]
  exact hc

/-- **The box parity for the intrinsic pair meet** (S2 in the field-based form): if the pair meet set
carries a smooth compactly supported field `Vf` which is nowhere zero on it, parallel to every local
graph tangent, and whose flow preserves the meet set while it stays in the box, then the boundary
meets are finite and even in number. -/
theorem ppMeetBdry_even_intrinsic
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ ppMeet E E' V W, PPRegAt E E' V W x)
    (Vf : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 9))
    (hVf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Vf) (hVfs : HasCompactSupport Vf)
    (hVfne : ∀ x ∈ ppMeet E E' V W, Vf x ≠ 0)
    (hVfpar : ∀ x ∈ ppMeet E E' V W, ∀ (i : Fin 9) (U : Set (EuclideanSpace ℝ (Fin 9)))
        (η : ℝ → EuclideanSpace ℝ (Fin 9)),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ U, (y ∈ Zpp E E' V W ↔
          y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ Vf x = c • (EuclideanSpace.single i (1 : ℝ) +
          (fderiv ℝ η (x i)) (1 : ℝ)))
    (hmapsTo : ∀ x ∈ ppMeet E E' V W, ∀ t : ℝ,
        (∀ u ∈ Set.uIcc (0 : ℝ) t, flowGen Vf hVf hVfs u x ∈ Submission.Drive.unitBox 8) →
        flowGen Vf hVf hVfs t x ∈ ppMeet E E' V W) :
    (ppMeetBdry E E' V W).Finite ∧ Even ((ppMeetBdry E E' V W).ncard) := by
  have h := ppIntrinsic.finite_and_even_ncard_bdry_of_localGraph
    (Z := Zpp E E' V W) (K := ppMeet E E' V W)
    (isCompact_ppMeet E E' V W hE hE' hV hW)
    (isClosed_Zpp_of_contMDiff E E' V W hE hE' hV hW)
    (fun x hx => by
      rw [ppMeet_eq_Zpp_inter] at hx
      exact hx.1)
    (exists_localGraph_Zpp E E' V W hE hE' hV hW hreg)
    Vf hVf hVfs hVfne hVfpar
    (ppMeet_faceData E E' V W hE hE' hV hW hreg Vf hVfpar) hmapsTo
  have hset : ppMeetBdry E E' V W =
      ppMeet E E' V W ∩ Submission.Drive.unitBoxBdry 8 := by
    ext x
    simp [ppMeetBdry, Set.mem_inter_iff]
  rw [hset]
  exact h

end

theorem exists_even_ppMeetEnd_add_intrinsic
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (Work.Drive.ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ < Work.Drive.ftS x →
      Work.Drive.ftS x < 1 - δ → x ∈ K)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Work.Drive.ppMeet E E' V W,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) →
      Work.Drive.PPRegAt E E' V W x)
    (ε : ℝ) (hε : 0 < ε)
    (htube : ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε' ∧
      (∀ x ∈ Work.Drive.ppMeet (fun s u => Ξ (w s • Work.Drive.unpackFst t) (E s u))
        (fun s u => Ξ (w s • Work.Drive.unpackSnd t) (E' s u)) V W,
        x ∈ K → Work.Drive.PPRegAt (fun s u => Ξ (w s • Work.Drive.unpackFst t) (E s u))
          (fun s u => Ξ (w s • Work.Drive.unpackSnd t) (E' s u)) V W x) ∧
      (∀ x ∈ Work.Drive.ppMeet (fun s u => Ξ (w s • Work.Drive.unpackFst t) (E s u))
        (fun s u => Ξ (w s • Work.Drive.unpackSnd t) (E' s u)) V W,
        Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1 ∧
          Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 u →
      E s (Work.Drive.seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 u →
      E' s (Work.Drive.seamInv2 u) = E' s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam y →
      V (Work.Drive.seamInv y) = V y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam z →
      W (Work.Drive.seamInv z) = W z) :
    ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε ∧
      Even ((Work.Drive.ppMeetEnd (fun s u => Ξ (w s • Work.Drive.unpackFst t) (E s u))
              (fun s u => Ξ (w s • Work.Drive.unpackSnd t) (E' s u)) V W 0).ncard +
        (Work.Drive.ppMeetEnd (fun s u => Ξ (w s • Work.Drive.unpackFst t) (E s u))
              (fun s u => Ξ (w s • Work.Drive.unpackSnd t) (E' s u)) V W 1).ncard) := by
  -- the base regularity transfers to the open collars (germ equality)
  have hregBaseOpen : ∀ x ∈ Submission.Drive.unitBox 8,
      (Work.Drive.ftS x < δ ∨ 1 - δ < Work.Drive.ftS x) →
      Work.Drive.ppMeet E E' V W x → Work.Drive.PPRegAt E E' V W x := by
    intro x hxbox hxc hm
    exact hregBase x hm (hxc.elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
  have hwleft' : ∀ s : ℝ, s < δ → w s = 0 := fun s hs => hwleft s (le_of_lt hs)
  have hwright' : ∀ s : ℝ, 1 - δ < s → w s = 0 := fun s hs => hwright s (le_of_lt hs)
  -- the collar-boundary transfer, and a parameter in its range
  obtain ⟨ηc, hηc, hcol⟩ :=
    ppIntrinsic.PPRegAt_ppShift_of_collarBoundary Ξ hΞ0 hΞsm E E' V W hE hE' hV hW
      hw hwleft hwright hregBase
  obtain ⟨t, ht, hregK, hAv⟩ := htube (min ε ηc / 2) (by positivity)
  have htε : ‖t‖ < ε := by
    have h1 : (0:ℝ) < min ε ηc / 2 := by positivity
    have h2 : min ε ηc / 2 ≤ min ε ηc := by linarith
    have h3 : min ε ηc ≤ ε := min_le_left _ _
    linarith
  have htη : ‖t‖ < ηc := by
    have h1 : (0:ℝ) < min ε ηc / 2 := by positivity
    have h2 : min ε ηc / 2 ≤ min ε ηc := by linarith
    have h3 : min ε ηc ≤ ηc := min_le_right _ _
    linarith
  refine ⟨t, htε, ?_⟩
  -- every meet of the perturbed family is regular
  have hregAll : ∀ x ∈ Work.Drive.ppMeet
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
      Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W x := by
    intro x hx
    by_cases hmid : δ < Work.Drive.ftS x ∧ Work.Drive.ftS x < 1 - δ
    · exact hregK x hx (hKcover x hx.1 hmid.1 hmid.2)
    · have hout : Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x := by
        by_contra hcon
        push Not at hcon
        exact hmid hcon
      rcases hout with hle | hge
      · by_cases hlt : Work.Drive.ftS x < δ
        · exact PPRegAt_ppShift_of_collar hΞ0 hwleft' hwright'
            t E E' V W hregBaseOpen x hx.1 (Or.inl hlt) hx
        · have heq : Work.Drive.ftS x = δ := le_antisymm hle (not_lt.mp hlt)
          exact hcol t htη x hx (Or.inl heq)
      · by_cases hgt : 1 - δ < Work.Drive.ftS x
        · exact PPRegAt_ppShift_of_collar hΞ0 hwleft' hwright'
            t E E' V W hregBaseOpen x hx.1 (Or.inr hgt) hx
        · have heq : Work.Drive.ftS x = 1 - δ := le_antisymm (not_lt.mp hgt) hge
          exact hcol t htη x hx (Or.inr heq)
  -- the perturbed chains are smooth, and their meets avoid the level faces
  have hEt : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)) :=
    contMDiff_ppShift Ξ hΞsm hw (Work.Drive.unpackFst t) E hE
  have hEt' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E')) :=
    contMDiff_ppShift Ξ hΞsm hw (Work.Drive.unpackSnd t) E' hE'
  have havY : ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
      Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1 := by
    intro x hx
    obtain ⟨h1, h2, -, -⟩ := hAv x hx
    exact ⟨h1, h2⟩
  have havZ : ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
      Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1 := by
    intro x hx
    obtain ⟨-, -, h3, h4⟩ := hAv x hx
    exact ⟨h3, h4⟩
  -- the local graph data of the perturbed equation set
  have hgraK : ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
      ∃ (i : Fin 9) (U : Set (EuclideanSpace ℝ (Fin 9))) (η : ℝ → EuclideanSpace ℝ (Fin 9)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ s : ℝ, η s i = 0) ∧
        ∀ y ∈ U, (y ∈ Work.Drive.Zpp (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W ↔
          y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)) :=
    exists_localGraph_Zpp (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W hEt hEt' hV hW hregAll
  -- the smooth tangential field of the perturbed meet set
  obtain ⟨Vf, hVf, hVfs, hVfne, hVfpar⟩ :=
    Work.Euclidean.TangentField.exists_smooth_tangent_field (n := 9)
      (P := fun x : EuclideanSpace ℝ (Fin 9) =>
        x ∈ Work.Drive.Zpp (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W)
      (K := Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W)
      (isCompact_ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W hEt hEt' hV hW)
      (fun x hx => by rw [Work.Drive.ppMeet_eq_Zpp_inter] at hx; exact hx.1)
      hgraK
  -- the flow of that field preserves the perturbed meet set while in the box
  have hmapsTo : ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W, ∀ t' : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t',
        Work.Drive.flowGen Vf hVf hVfs u x ∈ Submission.Drive.unitBox 8) →
      Work.Drive.flowGen Vf hVf hVfs t' x ∈ Work.Drive.ppMeet
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W := by
    intro x hx t' hbox
    have hxZ : x ∈ Work.Drive.Zpp (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W ∩
        Submission.Drive.unitBox 8 := by
      rw [← Work.Drive.ppMeet_eq_Zpp_inter]
      exact hx
    have hmem := ppIntrinsic.flowGen_mapsTo_of_localGraph
      (Z := Work.Drive.Zpp (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W)
      (isClosed_Zpp_of_contMDiff (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W hEt hEt' hV hW)
      (fun y hy => by
        rw [← Work.Drive.ppMeet_eq_Zpp_inter] at hy
        exact hgraK y hy)
      Vf hVf hVfs
      (fun y hy => by
        rw [← Work.Drive.ppMeet_eq_Zpp_inter] at hy
        exact hVfpar y hy)
      (fun b hb => ppMeet_faceData (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W hEt hEt' hV hW hregAll Vf
        hVfpar b ⟨by rw [Work.Drive.ppMeet_eq_Zpp_inter]; exact ⟨hb.1, hb.2.1⟩, hb.2⟩)
      x hxZ t' hbox
    rw [Work.Drive.ppMeet_eq_Zpp_inter]
    exact ⟨hmem, hbox t' Set.right_mem_uIcc⟩
  -- the box parity of the perturbed meet set
  obtain ⟨hfin, heven⟩ := ppMeetBdry_even_intrinsic
    (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
    (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W
    hEt hEt' hV hW hregAll Vf hVf hVfs hVfne hVfpar hmapsTo
  -- the face clause and the split of the boundary count
  have hface : ∀ x ∈ Work.Drive.ppMeetBdry (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
      (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    obtain ⟨i, hi, hoth, -⟩ := (hregAll x hx.1).2 hx.2
    exact ⟨i, hi, hoth⟩
  exact ppMeetEnd_even (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
    (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W hface
    (fun s u hu => by simp only [Work.Drive.ppShift]; rw [hseamU s u hu])
    (fun s u hu => by simp only [Work.Drive.ppShift]; rw [hseamU' s u hu])
    hseamV hseamW
    havY havZ hfin heven


end Work.Drive
