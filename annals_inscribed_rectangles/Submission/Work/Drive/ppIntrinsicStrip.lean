import Mathlib
import Submission.Work.Drive.exists_even_ppMeetEnd_add_intrinsic
import Submission.Work.Drive.ppParity.IntrinsicT6

/-!
# The **collar-defect-free** versions of S4 and S5 (the intrinsic box parity and the transport `T6`)

`Submission/Work/Drive/PPPARITY_COLLAR_DEFECT.md` §0–§3bis: the three collar binders of S3/S4
(`hwne : ∀ x ∈ K, w (ftS x) ≠ 0`, the closed-slab cover `hKcover`, and the closed collar
`hwleft : s ≤ δ → w s = 0`) are **jointly unsatisfiable** for `δ ∈ [0, 1/2]`, so
`Work.Drive.exists_even_ppMeetEnd_add_intrinsic` (S4) and
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic` (S5) — although *proved* —
can never be instantiated by the design.  The defect is *only* in the hypothesis list: `hwne` occurs
exactly once in each file, in its own binder, and is **never used** in either proof.

This module therefore contains the two statements with `hwne` **deleted** (nothing else changed), and
their proofs are verbatim the proofs on disk.  The remaining binders — the strict-slab cover
`hKcover`, the closed collars `hwleft`/`hwright`, the collar-honesty hypothesis `hregBase` and the
Sard package `htube` — are consistent (they are satisfied by, e.g., the design's
"bump supported on the open strip" weight), and the collar *lines* are handled by the already proved
`ppIntrinsic.PPRegAt_ppShift_of_collarBoundary`, exactly as in the original proof.

**Consumers**: instantiate these instead of the `…_add_intrinsic` / `…_of_design_intrinsic` pair.  The
`T6` of `Submission/Work/Drive/ppParity/IntrinsicT6.lean` in the form the reference-triple assembly can
actually feed.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem exists_even_ppMeetEnd_add_intrinsic_strip
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

theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_strip
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hw : ContDiff ℝ Ctop w)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ < ftS x → ftS x < 1 - δ → x ∈ K)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0)
    (hE : ContMDiff 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (Function.uncurry (colPlane β Q)))
    (hE' : ContMDiff 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (Function.uncurry (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)))
    (hV : ContMDiff (𝓡 3) (𝓡 4) Ctop (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hW : ContMDiff (𝓡 3) (𝓡 4) Ctop (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      colPlane β Q s (seamInv2 u) = colPlane β Q s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      diskPlane Q (seamInv2 u) = diskPlane Q u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y →
      clampedSweep c₁ (fun t => 1 - t) P₁ (seamInv y) = clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z →
      clampedSweep c₂ (fun t => 1 - t) P₂ (seamInv z) = clampedSweep c₂ (fun t => 1 - t) P₂ z)
    (hregBase : ∀ x ∈ Work.Drive.ppMeet (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
      Work.Drive.PPRegAt (colPlane β Q) (fun _ u => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x)
    (ε : ℝ) (hε : 0 < ε)
    (htube : ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε' ∧
      (∀ x ∈ Work.Drive.ppMeet (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
        x ∈ K → Work.Drive.PPRegAt (ppShift Ξ w (unpackFst t) (colPlane β Q))
          (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
          (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x) ∧
      (∀ x ∈ Work.Drive.ppMeet (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) (fun _ u => diskPlane Q u))
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
        ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 ∧ ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1))
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    {δc : ℝ} (hδ : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ p ∈ coreMeet Q c₁ P₁, (diamMeet Q p.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
      Odd (coreSideCount Q c₂ P₂)) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  set V : EuclideanSpace ℝ (Fin 3) → CappingSpace := clampedSweep c₁ (fun t => 1 - t) P₁ with hVdef
  set W : EuclideanSpace ℝ (Fin 3) → CappingSpace := clampedSweep c₂ (fun t => 1 - t) P₂ with hWdef
  set E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u with hE'def
  obtain ⟨t, ht, heven⟩ :=
    exists_even_ppMeetEnd_add_intrinsic_strip (M := CappingSpace)
      Ξ hΞ.1 hΞ.2.1 (colPlane β Q) E' V W w K hK hE hE' hV hW hw hKcover hwleft hwright
      hregBase ε hε htube hseamU hseamU' hseamV hseamW
  have h0 : (ppMeetEnd (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) E') V W 0).ncard = colCount β Q V W 0 := by
    rw [ppMeetEnd_zero_eq β Q Ξ w hΞ hw0 t V W,
      ncard_ppMeetEnd_eq_colCount β Q V W (Set.left_mem_Icc.mpr zero_le_one)]
  have h1 : (ppMeetEnd (ppShift Ξ w (unpackFst t) (colPlane β Q))
        (ppShift Ξ w (unpackSnd t) E') V W 1).ncard = colCount β Q V W 1 := by
    rw [ppMeetEnd_one_eq β Q Ξ w hΞ hw1 t V W,
      ncard_ppMeetEnd_eq_colCount β Q V W (Set.right_mem_Icc.mpr zero_le_one)]
  have heven' : Even (colCount β Q V W 0 + colCount β Q V W 1) := by
    rw [← h0, ← h1]
    exact heven
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_even β Q P₁ P₂ c₀ c₁ c₂ heven' hfibV hfibW
    hQseam hδ hβδ hδcut hfin hfind hbase ht5

end

end Work.Drive
