/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (node P7 of the Følner/Lück argument for JZLA20 Proposition 3.11)

# The two-term operator `D + C·λ(t)` is injective

Let `N ⊴ G` (a normal subgroup), `t ∈ G` with `G = N ⋊ ⟨t⟩` (`Work.ORP311.IsExtensionByZ G N t`)
and `D C : HSum n →L[ℂ] HSum n` two operators on `ℓ²(G)ⁿ` which are **block diagonal** over the
`N`-cosets `N t^j` (`Work.ORP311.IsBlockDiag`) and commute with the right regular action of `N`
and `t` (i.e. lie in the image of the von Neumann algebra `N(G)`, `Work.ORP311.Equivariant`), with
`D` injective.  Then

  `D + C · λ(t)`

is injective.  This is the analytic core (node P7 of the lead design, §2/§4 of
`Submission/Work/ORP311/P311_DESIGN_LEAD.md`) of [JZLA20, Proposition 3.11].

## Proof

* `D` and `C` are equivariant, hence so is `Z := D + C·λ(t)`; the kernel `K = ker Z` is
  invariant under the right regular action of `G`, so its projection `P_K` is equivariant
  and `hdim K = tDim n (sWin t p) K / (2p+1)` (`Work.ORP311.tDim_eq_card_mul_hdim`,
  `Work.ORP311.card_sWin`).
* For `v ∈ ℓ²(X_p)ⁿ` (the window), `‖P_K v‖ ≤ ‖P_{Ewin} v‖` where
  `Ewin = ℓ²(X_p)ⁿ ⊓ ⋂_{-p<j≤p} ker (blk_j ∘ Z)` is the window kernel
  (`Work.ORP311.window_proj_mem_Ewin` + `Work.ORP311.norm_starProjection_le_of_proj_le`).
* Summing over the transversal `sWin t p` gives `tDim K ≤ tDim (Ewin)`, and the transport to `N`
  (node P5, `Work.ORP311.tDim_le_of_bottom_injective`) bounds `tDim (Ewin) ≤ n`.
* Hence `(2p+1) · hdim K ≤ n` for every `p`, so `hdim K = 0`, and `K = ⊥` by faithfulness of the
  von Neumann dimension (`Work.ORP311.eq_bot_of_hdim_eq_zero`).

## The self-contained block-diagonal lemmas

The module `Work.ORP311.isBlockDiag_adjoint_of_isBlockDiag` (adjoint of a block diagonal operator
is block diagonal) imports `Work.ORP311.UpWindowDefs`, and `Work.ORP311.Ewin_invariant` imports
`Work.ORP311.mul_mem_coset`; those two modules define declarations (`Work.ORP311.coset_disjoint`
resp. `Work.ORP311.zpow_conj_mem`) which are also defined, under the same names, in
`Work.ORP311.coset_disjoint` resp. `Work.ORP311.tDim_le_of_bottom_injective`.  Since this file must
import `Work.ORP311.tDim_le_of_bottom_injective`, the two replacements are proved here (under
distinct names) so that the import closure of this file is consistent.
-/
import Mathlib
import Submission.Work.ORP311.BlockShift
import Submission.Work.ORP311.HdimInject
import Submission.Work.ORP311.tDim_mono
import Submission.Work.ORP311.tDim_ell2Sub_compl_of_subset
import Submission.Work.ORP311.ell2Sub_inf
import Submission.Work.ORP311.ell2Sub_mono
import Submission.Work.ORP311.ell2Sub_orthogonal
import Submission.Work.ORP311.ell2Sub_map_diagOp_of_right_invariant
import Submission.Work.ORP311.Ell2SubAux
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.Ewin_hasOrthogonalProjection
import Submission.Work.ORP311.window_proj_mem_Ewin
import Submission.Work.ORP311.Ewin_bottom_injective
import Submission.Work.ORP311.tDim_le_of_bottom_injective
import Submission.Work.ORP311.eq_bot_of_hdim_eq_zero
import Submission.Work.ORP311.card_sWin
import Submission.Work.ORP311.tDim_eq_card_mul_hdim
import Submission.Work.ORP311.blk_comp_of_isBlockDiag
import Submission.Work.ORP311.norm_starProjection_le_of_proj_le
import Submission.Work.ORP311.coset_subset_window
import Submission.Work.ORP311.regBlk_equivariant
import Submission.Work.ORP311.equivariant_of_commutes_N_t
import Submission.Work.ORP311.mem_ell2Sub_iff
import Submission.Work.ORP311.hdim_translate
import Submission.Work.ORVonNeumann.Rep.vnDiagOpAdjoint

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### Instances -/

/-- The kernel of an operator on `HSum n` is closed, hence carries an orthogonal projection. -/
instance instKerHasOrthogonalProjection {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (T : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) :
    T.ker.HasOrthogonalProjection := by
  haveI : CompleteSpace ↥T.ker := (ContinuousLinearMap.isClosed_ker T).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The window kernel `Ewin` is closed, hence carries an orthogonal projection. -/
instance instEwinHasOrthogonalProjection {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (N : Subgroup G) (t : G) (m : ℕ)
    (Z : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) :
    (Work.ORP311.P311.Ewin n N t m Z).HasOrthogonalProjection :=
  Ewin_hasOrthogonalProjection n N t m Z

/-! ### `TwistData` from the extension hypotheses -/

/-- `TwistData N t` from `N.Normal` and `IsExtensionByZ G N t`. -/
theorem twistData_of_normal {N : Subgroup G} {t : G} (hN : N.Normal)
    (hext : IsExtensionByZ G N t) : P311.TwistData N t where
  conj x hx := hN.conj_mem x hx t
  conj_inv x hx := by
    have h := hN.conj_mem x hx t⁻¹
    simpa using h
  inf k hk := hext.2 k hk

/-! ### Coset bookkeeping -/

/-- Conjugation by any integer power of `t` preserves `N` (the `ℤ`-indexed form of the
`TwistData.conj`/`TwistData.conj_inv` fields). -/
theorem zpowConj_mem {N : Subgroup G} {t : G} (h : P311.TwistData N t) (j : ℤ) {x : G}
    (hx : x ∈ N) : t ^ j * x * t ^ (-j) ∈ N := by
  have ht : t ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact h.conj y
    · intro hy
      have h1 := h.conj_inv (t * y * t⁻¹) hy
      have heq : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rwa [heq] at h1
  have htj : t ^ j ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normalizer (N : Set G)).zpow_mem ht j
  have h2 := (Subgroup.mem_normalizer_iff.mp htj x).mp hx
  simpa only [zpow_neg] using h2

/-- Distinct cosets `N t ^ i`, `N t ^ j` are disjoint when `t` has infinite order modulo `N`. -/
theorem coset_disjoint_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) {i j : ℤ}
    (hij : i ≠ j) : Disjoint (coset N t i) (coset N t j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rw [mem_coset_iff] at hx hy
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  rw [hn] at hm
  have h2 : t ^ (i - j) = (n : G)⁻¹ * (m : G) := by
    have h3 : t ^ i = (n : G)⁻¹ * (m : G) * t ^ j := by
      have hh := congrArg (fun x : G => (n : G)⁻¹ * x) hm
      simpa [mul_assoc] using hh
    have h4 : t ^ i * (t ^ j)⁻¹ = (n : G)⁻¹ * (m : G) := by
      rw [h3, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [zpow_sub, zpow_neg] using h4
  have hmem : t ^ (i - j) ∈ N := h2 ▸ N.mul_mem (N.inv_mem n.2) m.2
  exact absurd (sub_eq_zero.mp (h.inf (i - j) hmem)) hij

/-- A coset is contained in the complement of any other coset. -/
theorem coset_subset_compl_coset_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t)
    {k j : ℤ} (hkj : k ≠ j) : coset N t k ⊆ (coset N t j)ᶜ := by
  intro a ha haj
  exact (Set.disjoint_left.mp (coset_disjoint_twist h hkj)) ha haj

/-- The `δ`-generator `e_i ⊗ δ_g` of `ell2Sub n Z`, for `g ∈ Z`. -/
theorem hinclude_deltaG_mem_ell2Sub_twist (n : ℕ) {Z : Set G} {g : G} (hg : g ∈ Z) (i : Fin n) :
    Rep.hinclude (G := G) n i (Rep.deltaG g) ∈ ell2Sub (G := G) n Z :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨g, hg, i, rfl⟩)

/-! ### Block diagonality of the adjoint and of `diagOp` -/

/-- A block diagonal operator preserves the complement of a single `N`-coset (proved from the
generators, using that every element outside `N t^j` lies in some other coset `N t^k`). -/
theorem isBlockDiag_map_compl_coset_subset_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t)
    (hext : IsExtensionByZ G N t) {m : ℕ} (D : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m)
    (hD : IsBlockDiag N t m D) (j : ℤ) :
    D '' (ell2Sub (G := G) m ((coset N t j)ᶜ) : Set (Rep.HSum (G := G) m))
      ⊆ ell2Sub (G := G) m ((coset N t j)ᶜ) := by
  rintro y ⟨x, hx, rfl⟩
  refine ell2Sub_map_subset_of_generators (G := G) m D ((coset N t j)ᶜ)
    (ell2Sub (G := G) m ((coset N t j)ᶜ)) ?_ ?_ x hx
  · unfold ell2Sub
    exact Submodule.isClosed_topologicalClosure _
  · intro g hg i
    obtain ⟨n, k, hk⟩ := hext.1 g
    have hkj : k ≠ j := by
      rintro rfl
      exact hg ⟨n, hk⟩
    refine ell2Sub_mono (coset_subset_compl_coset_twist h hkj) ?_
    have hgen : Rep.hinclude (G := G) m i (Rep.deltaG g) ∈ ell2Sub (G := G) m (coset N t k) :=
      hinclude_deltaG_mem_ell2Sub_twist (G := G) (Z := coset N t k) (g := g) m ⟨n, hk⟩ i
    exact hD k _ hgen

/-- **The adjoint of a block diagonal operator is block diagonal** over the `N`-cosets. -/
theorem isBlockDiag_adjoint_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t)
    (hext : IsExtensionByZ G N t) {m : ℕ}
    {D : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m} (hD : IsBlockDiag N t m D) :
    IsBlockDiag N t m (ContinuousLinearMap.adjoint D) := by
  intro j x hx
  rw [ell2Sub_orthogonal (G := G) m (coset N t j)]
  rw [Submodule.mem_orthogonal']
  intro u hu
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hx' : x ∈ (ell2Sub (G := G) m ((coset N t j)ᶜ))ᗮ := by
    rw [← ell2Sub_orthogonal (G := G) m (coset N t j)]
    exact hx
  exact (Submodule.mem_orthogonal' _ x).mp hx' (D u)
    (isBlockDiag_map_compl_coset_subset_twist h hext D hD j ⟨u, hu, rfl⟩)

/-- **The right regular action of an element of `N` is block diagonal** over the `N`-cosets. -/
theorem isBlockDiag_diagOp_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) (n : ℕ)
    {k : G} (hk : k ∈ N) : IsBlockDiag N t n (Rep.diagOp (G := G) n k) := by
  intro j x hx
  refine ell2Sub_map_subset_of_generators (G := G) n (Rep.diagOp (G := G) n k)
    (coset N t j) (ell2Sub (G := G) n (coset N t j)) ?_ ?_ x hx
  · unfold ell2Sub
    exact Submodule.isClosed_topologicalClosure _
  · intro g hg i
    have h1 : Rep.diagOp (G := G) n k (Rep.hinclude (G := G) n i (Rep.deltaG g))
        = Rep.hinclude (G := G) n i (Rep.rightRegOp k (Rep.deltaG g)) := by
      have hh := congrArg
        (fun f : Work.ORVonNeumann.l2 G →L[ℂ] Rep.HSum (G := G) n => f (Rep.deltaG g))
        (Rep.diagOp_hinclude (G := G) n k i)
      simpa only [ContinuousLinearMap.comp_apply] using hh
    rw [h1, Rep.rightRegOp_deltaG]
    obtain ⟨a, ha⟩ := hg
    have hc : t ^ j * k⁻¹ * t ^ (-j) ∈ N := zpowConj_mem h j (N.inv_mem hk)
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g * k⁻¹, ?_, i, rfl⟩)
    exact ⟨⟨(a : G) * (t ^ j * k⁻¹ * t ^ (-j)), N.mul_mem a.2 hc⟩, by rw [ha]; group⟩

/-- The adjoint of the right regular action of an element of `N` is again block diagonal. -/
theorem isBlockDiag_adjoint_diagOp_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) (n : ℕ)
    {k : G} (hk : k ∈ N) :
    IsBlockDiag N t n (ContinuousLinearMap.adjoint (Rep.diagOp (G := G) n k)) := by
  rw [Rep.vnDiagOpAdjoint]
  exact isBlockDiag_diagOp_twist h n (N.inv_mem hk)

/-- **`diagOp` of an element of `N` commutes with the block projections `blk`.** -/
theorem diagOp_comp_blk_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) (n : ℕ) (j : ℤ)
    {k : G} (hk : k ∈ N) :
    Rep.diagOp (G := G) n k ∘L P311.blk n N t j
      = P311.blk n N t j ∘L Rep.diagOp (G := G) n k :=
  (blk_comp_of_isBlockDiag (G := G) (N := N) (t := t) n j (Rep.diagOp (G := G) n k)
    (isBlockDiag_diagOp_twist h n hk) (isBlockDiag_adjoint_diagOp_twist h n hk)).symm

/-- The window is stable under right multiplication by `N`. -/
theorem mul_mem_window_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) (m : ℕ) {g : G}
    (hg : g ∈ window N t m) {k : G} (hk : k ∈ N) : g * k⁻¹ ∈ window N t m := by
  obtain ⟨n, j, hj1, hj2, rfl⟩ := hg
  have hc : t ^ j * k⁻¹ * t ^ (-j) ∈ N := zpowConj_mem h j (N.inv_mem hk)
  refine ⟨⟨(n : G) * (t ^ j * k⁻¹ * t ^ (-j)), N.mul_mem n.2 hc⟩, j, hj1, hj2, ?_⟩
  show (n : G) * t ^ j * k⁻¹ = (n : G) * (t ^ j * k⁻¹ * t ^ (-j)) * t ^ j
  group

/-- **The window kernel `Ewin` is invariant under the right regular action of `N`.** -/
theorem Ewin_invariant_twist {N : Subgroup G} {t : G} (h : P311.TwistData N t) (n m : ℕ)
    (Z : Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n)
    (hZ : Rep.Equivariant (G := G) Z) {k : G} (hk : k ∈ N)
    {x : Rep.HSum (G := G) n} (hx : x ∈ P311.Ewin n N t m Z) :
    Rep.diagOp (G := G) n k x ∈ P311.Ewin n N t m Z := by
  simp only [P311.Ewin, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact ell2Sub_map_diagOp_of_right_invariant (Z := window N t m) (k := k)
      (fun g hg => mul_mem_window_twist h m hg hk) x hx.1
  · intro j hj
    have hzero : (P311.blk n N t j ∘L Z) x = 0 := hx.2 j hj
    have hzero' : P311.blk n N t j (Z x) = 0 := hzero
    have hZapp : Z (Rep.diagOp (G := G) n k x) = Rep.diagOp (G := G) n k (Z x) := by
      have h1 := congrArg (fun f => f x) (hZ k)
      simpa only [ContinuousLinearMap.comp_apply] using h1
    have hblk : P311.blk n N t j (Rep.diagOp (G := G) n k (Z x))
        = Rep.diagOp (G := G) n k (P311.blk n N t j (Z x)) := by
      have h1 := congrArg (fun f => f (Z x)) (diagOp_comp_blk_twist h n j hk)
      simpa only [ContinuousLinearMap.comp_apply] using h1.symm
    change (P311.blk n N t j ∘L Z) (Rep.diagOp (G := G) n k x) = 0
    rw [ContinuousLinearMap.comp_apply, hZapp, hblk, hzero']
    simp

/-! ### The window argument -/

/-- The two-term operator `D + C∘regBlk t` is equivariant as soon as `D` and `C` are. -/
theorem equivariant_twoTerm {m : ℕ} {t : G} {D C : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m}
    (hD : Rep.Equivariant (G := G) D) (hC : Rep.Equivariant (G := G) C) :
    Rep.Equivariant (G := G) (twoTerm (G := G) m t D C) := by
  have h : twoTerm (G := G) m t D C = D + C.comp (regBlk (G := G) m t) := rfl
  rw [h]
  exact Rep.Equivariant.add hD (Rep.Equivariant.comp (regBlk_equivariant m t) hC)

/-- The per-vector inequality of the window argument: for `v` in the window, the projection
of `v` onto `ker Z` is dominated in norm by the projection onto `Ewin`. -/
theorem norm_starProjection_ker_le_Ewin {N : Subgroup G} {t : G} (h : P311.TwistData N t)
    {m p : ℕ} {D C : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m}
    (hSb : ∀ j : ℤ, P311.blk m N t j ∘L D = D ∘L P311.blk m N t j)
    (hCb : ∀ j : ℤ, P311.blk m N t j ∘L C = C ∘L P311.blk m N t j)
    {v : Rep.HSum (G := G) m} (hv : v ∈ ell2Sub (G := G) m (window N t p)) :
    ‖(twoTerm (G := G) m t D C).ker.starProjection v‖
      ≤ ‖(P311.Ewin m N t p (twoTerm (G := G) m t D C)).starProjection v‖ := by
  classical
  haveI : (ell2Sub (G := G) m (window N t p)).HasOrthogonalProjection := by
    haveI : CompleteSpace ↥(ell2Sub (G := G) m (window N t p)) :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    infer_instance
  have hsub : P311.Ewin m N t p (twoTerm (G := G) m t D C)
      ≤ ell2Sub (G := G) m (window N t p) := inf_le_left
  exact norm_starProjection_le_of_proj_le _ _ _ hsub
    (fun ξ hξ => window_proj_mem_Ewin h m p D C hSb hCb (by simpa using hξ)) hv

/-- Summing the per-vector inequality over the transversal `sWin t p`. -/
theorem tDim_ker_le_tDim_Ewin {N : Subgroup G} {t : G} (h : P311.TwistData N t) {m p : ℕ}
    {D C : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m}
    (hSb : ∀ j : ℤ, P311.blk m N t j ∘L D = D ∘L P311.blk m N t j)
    (hCb : ∀ j : ℤ, P311.blk m N t j ∘L C = C ∘L P311.blk m N t j) :
    tDim (G := G) m (P311.sWin t p) (twoTerm (G := G) m t D C).ker
      ≤ tDim (G := G) m (P311.sWin t p) (P311.Ewin m N t p (twoTerm (G := G) m t D C)) := by
  classical
  haveI : (ell2Sub (G := G) m (window N t p)).HasOrthogonalProjection := by
    haveI : CompleteSpace ↥(ell2Sub (G := G) m (window N t p)) :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    infer_instance
  rw [tDim_apply, tDim_apply]
  refine Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun i _ => ?_
  have hg' : g ∈ (Finset.Icc (-(p : ℤ)) p).image (fun j : ℤ => t ^ j) := hg
  rw [Finset.mem_image] at hg'
  obtain ⟨j, hj, rfl⟩ := hg'
  have hj1 : -(p : ℤ) ≤ j := (Finset.mem_Icc.mp hj).1
  have hj2 : j ≤ (p : ℤ) := (Finset.mem_Icc.mp hj).2
  have hv : Rep.hinclude (G := G) m i (Rep.deltaG (t ^ j))
      ∈ ell2Sub (G := G) m (window N t p) := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨t ^ j, coset_subset_window hj1 hj2 ⟨1, by simp⟩, i, rfl⟩
  have hle := norm_starProjection_ker_le_Ewin h hSb hCb hv
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- The `Ewin` subspace has transversal dimension at most `m`. -/
theorem tDim_Ewin_le {N : Subgroup G} {t : G} (h : P311.TwistData N t) {m p : ℕ}
    {D C : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m}
    (hSb : ∀ j : ℤ, P311.blk m N t j ∘L D = D ∘L P311.blk m N t j)
    (hCb : ∀ j : ℤ, P311.blk m N t j ∘L C = C ∘L P311.blk m N t j)
    (hZe : Rep.Equivariant (G := G) (twoTerm (G := G) m t D C))
    (hinj : Function.Injective D) :
    tDim (G := G) m (P311.sWin t p) (P311.Ewin m N t p (twoTerm (G := G) m t D C))
      ≤ (m : ℝ) := by
  have hsub : P311.Ewin m N t p (twoTerm (G := G) m t D C)
      ≤ ell2Sub (G := G) m (window N t p) := inf_le_left
  exact tDim_le_of_bottom_injective (h := h) (n := m) (m := p)
    (V := P311.Ewin m N t p (twoTerm (G := G) m t D C)) hsub
    (fun k hk x hx => Ewin_invariant_twist h m p (twoTerm (G := G) m t D C) hZe hk hx)
    (fun x hx h0 => Ewin_bottom_injective h m p D C hSb hCb hinj hx h0)

theorem twoTerm_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) (hN : N.Normal) (t : G) (hext : Work.ORP311.IsExtensionByZ G N t) (m : ℕ) (D C : Work.ORVonNeumann.Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) m) (hD : Work.ORP311.IsBlockDiag (G := G) N t m D) (hC : Work.ORP311.IsBlockDiag (G := G) N t m C) (hDn : ∀ n : ↥N, D.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)) = (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)).comp D) (hCn : ∀ n : ↥N, C.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)) = (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)).comp C) (hDt : D.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m t) = (Work.ORVonNeumann.Rep.diagOp (G := G) m t).comp D) (hCt : C.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m t) = (Work.ORVonNeumann.Rep.diagOp (G := G) m t).comp C) (hinj : Function.Injective D) : Function.Injective (Work.ORP311.twoTerm (G := G) m t D C) := by
  classical
  have hTw : P311.TwistData N t := twistData_of_normal hN hext
  have hDe : Rep.Equivariant (G := G) D := equivariant_of_commutes_N_t hext hDn hDt
  have hCe : Rep.Equivariant (G := G) C := equivariant_of_commutes_N_t hext hCn hCt
  have hZe : Rep.Equivariant (G := G) (twoTerm (G := G) m t D C) :=
    equivariant_twoTerm hDe hCe
  have hD' : IsBlockDiag (G := G) N t m (ContinuousLinearMap.adjoint D) :=
    isBlockDiag_adjoint_twist hTw hext hD
  have hC' : IsBlockDiag (G := G) N t m (ContinuousLinearMap.adjoint C) :=
    isBlockDiag_adjoint_twist hTw hext hC
  have hSb : ∀ j : ℤ, P311.blk m N t j ∘L D = D ∘L P311.blk m N t j :=
    fun j => blk_comp_of_isBlockDiag m j D hD hD'
  have hCb : ∀ j : ℤ, P311.blk m N t j ∘L C = C ∘L P311.blk m N t j :=
    fun j => blk_comp_of_isBlockDiag m j C hC hC'
  have hKinv : ∀ g : G, ∀ x ∈ (twoTerm (G := G) m t D C).ker,
      Rep.diagOp (G := G) m g x ∈ (twoTerm (G := G) m t D C).ker := by
    intro g x hx
    have h1 : (twoTerm (G := G) m t D C) (Rep.diagOp (G := G) m g x)
        = Rep.diagOp (G := G) m g ((twoTerm (G := G) m t D C) x) := by
      have h2 := congrArg (fun f : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m => f x)
        (hZe g)
      simpa [ContinuousLinearMap.comp_apply] using h2
    have hx0 : (twoTerm (G := G) m t D C) x = 0 := hx
    have h2 : (twoTerm (G := G) m t D C) (Rep.diagOp (G := G) m g x) = 0 := by
      rw [h1, hx0, map_zero]
    simpa using h2
  have hPK : Rep.Equivariant (G := G) (twoTerm (G := G) m t D C).ker.starProjection :=
    Rep.equivariant_starProjection hKinv
  have hbound : ∀ p : ℕ,
      ((2 * p + 1 : ℕ) : ℝ) * Rep.hdim (G := G) (twoTerm (G := G) m t D C).ker ≤ (m : ℝ) := by
    intro p
    have h1 : tDim (G := G) m (P311.sWin t p) (twoTerm (G := G) m t D C).ker
        = ((P311.sWin t p).card : ℝ) * Rep.hdim (G := G) (twoTerm (G := G) m t D C).ker :=
      tDim_eq_card_mul_hdim _ hPK _
    have h2 : (P311.sWin t p).card = 2 * p + 1 := card_sWin hTw p
    have h3 := tDim_ker_le_tDim_Ewin (h := hTw) (p := p) hSb hCb
    have h4 := tDim_Ewin_le (h := hTw) (p := p) hSb hCb hZe hinj
    rw [h1, h2] at h3
    nlinarith [h3, h4]
  have hd0 : Rep.hdim (G := G) (twoTerm (G := G) m t D C).ker = 0 := by
    have hnn : 0 ≤ Rep.hdim (G := G) (twoTerm (G := G) m t D C).ker := by
      rw [Rep.hdim]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases eq_or_lt_of_le hnn with hh | hh
    · exact hh.symm
    · exfalso
      set d := Rep.hdim (G := G) (twoTerm (G := G) m t D C).ker with hd
      obtain ⟨p, hp⟩ := exists_nat_gt ((m : ℝ) / d)
      have h1 := hbound p
      have h2 : ((2 * p + 1 : ℕ) : ℝ) > (m : ℝ) / d := by
        have h3 : (p : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := by push_cast; nlinarith
        linarith
      have h4 : ((2 * p + 1 : ℕ) : ℝ) * d > (m : ℝ) := by
        have h5 : (m : ℝ) / d < ((2 * p + 1 : ℕ) : ℝ) := h2
        have h6 := (div_lt_iff₀ hh).mp h5
        linarith
      linarith [h1, h4]
  have hKbot : (twoTerm (G := G) m t D C).ker = ⊥ :=
    eq_bot_of_hdim_eq_zero _ hKinv hd0
  intro x y hxy
  have hsub : x - y ∈ (twoTerm (G := G) m t D C).ker := by
    have h2 : (twoTerm (G := G) m t D C) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    simpa using h2
  rw [hKbot] at hsub
  have h0 : x - y = 0 := by simpa using hsub
  exact sub_eq_zero.mp h0

end Work.ORP311
