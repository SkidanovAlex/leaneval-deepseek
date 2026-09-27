import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union

/-!
# `Work.Engulf.E4S.Basic` — support lemmas for `pushShellG` and `stepG`

Area E4S of the Poincare project (`Submission/Work/NOTES_LEAD_poincare_E4c.md` §A): the *moving map*
step of Newman's Lemma 7 Case 1, i.e. `AltInnerG`-preservation.

This file contains the two pieces of the step that are independent of the push and of the piece
loop:

* `eq_g₁_of_mem_closedCube` — the **transfer lemma** of §A.5(2).  `ND.mesh` says that a fine face
  is either core (`f`-image in the `5/8` cube) or has its `g₁`-image outside the `9/16` cube; the
  margin `μ` of `exists_core_margin` upgrades that to *any* map `G` which is `μ`-close to `g₁`.
  Hence a point of `K ∪ Q` whose `G`-image lands in `ψ (closedCube 9/16)` is frozen, and
  `G = g₁` there.  This is what lets the `E4b` bad-set analysis (proved for `g₁`) be applied to the
  moving map `g′`.
* `card_le_of_simp_subset_K_union_Q` — the dimension bound `hGdim` of §A.5(3) for the subcomplex
  `G = K ∪ Q` of the shelling loop: every fine face inside `K ∪ Q` has at most `p + 1` vertices.
-/

open Set Metric PL
open Work.Engulf.Alt

universe u

namespace Work.Engulf.E4S

/-- **The transfer lemma** (`NOTES_LEAD_poincare_E4c.md` §A.5(2)).  Let `Cr` be a set of points
that is `μ`-separated from the `9/16` cube in the following sense: no point `x ∈ Γ₁.space`
*outside* `Cr` has a `μ`-neighbourhood of `g₁ x` which meets `ψ (closedCube 9/16)`
(`exists_core_margin` with `Cr = coreSet`).  If `G` agrees with `g₁` on `L ∪ Cr` and its value at
`y ∈ Γ₁.space` is within `μ` of `g₁ y`, then `G y ∈ ψ (closedCube 9/16)` forces `y ∈ Cr`, hence
`G y = g₁ y`. -/
theorem eq_g₁_of_mem_closedCube {N n : ℕ} {M : Type*} [MetricSpace M]
    {Γ₁ : Cx N} {L Cr : Set (E N)} {g₁ G : E N → M} {ψ : CubeChart n M} {μ : ℝ}
    (hmarg : ∀ x ∈ Γ₁.space, x ∉ Cr → ∀ z : M, dist z (g₁ x) < μ →
      z ∉ ψ.toFun '' closedCube (9 / 16 : ℝ))
    (hfrz : EqOn G g₁ (L ∪ Cr)) {y : E N} (hy : y ∈ Γ₁.space)
    (himg : G y ∈ ψ.toFun '' closedCube (9 / 16 : ℝ))
    (hdist : dist (G y) (g₁ y) < μ) : G y = g₁ y := by
  by_cases hyc : y ∈ Cr
  · exact hfrz (Or.inr hyc)
  · exact absurd himg (hmarg y hy hyc (G y) hdist)

/-- `eq_g₁_of_mem_closedCube` in the `near`-form in which the invariant carries the distance: the
hypothesis is `dist (G y) (g₁ y) ≤ i * β` with `i * β < μ`. -/
theorem eq_g₁_of_near {N n : ℕ} {M : Type*} [MetricSpace M]
    {Γ₁ : Cx N} {L Cr : Set (E N)} {g₁ G : E N → M} {ψ : CubeChart n M} {μ β : ℝ} {i : ℕ}
    (hmarg : ∀ x ∈ Γ₁.space, x ∉ Cr → ∀ z : M, dist z (g₁ x) < μ →
      z ∉ ψ.toFun '' closedCube (9 / 16 : ℝ))
    (hfrz : EqOn G g₁ (L ∪ Cr)) (hnear : ∀ x ∈ Γ₁.space, dist (G x) (g₁ x) ≤ (i : ℝ) * β)
    (hβμ : (i : ℝ) * β < μ) {y : E N} (hy : y ∈ Γ₁.space)
    (himg : G y ∈ ψ.toFun '' closedCube (9 / 16 : ℝ)) : G y = g₁ y :=
  eq_g₁_of_mem_closedCube hmarg hfrz hy himg (lt_of_le_of_lt (hnear y hy) hβμ)

/-- **The dimension bound `hGdim` for `G = K ∪ Q`** (`NOTES_LEAD_poincare_E4c.md` §A.5(3)).

`Q` is the `q`-skeleton of the first `i` members of the shelling order.  A fine face `s` with
`simp s ⊆ K ∪ Q` lies in `K` or in `Q` (`face_subset_of_subset_union`, `Q` being a subcomplex of
`Γ₁` by `isSubSp_iUnion_simp_erase`).  In the first case `CarrierS` produces a *coarse* face `t`
with `simp s ⊆ simp t ⊆ K`, whose card is `≤ p + 1` by `L7Hyp.cfg.dimH`, and affine independence
gives `s.card ≤ t.card`.  In the second case `simp_cover` puts `simp s` inside the simplex of a
single erased face `σ.erase w` with `σ ∈ ND.ord` (`σ.card = q + 2`), so `s.card ≤ q + 1 ≤ p + 1`. -/
theorem card_le_of_simp_subset_K_union_Q {n p q N : ℕ} {M : Type*} [MetricSpace M]
    {V X : Set M} {Γ : Cx N} {K L : Set (E N)} {f : E N → M}
    {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : L7Hyp n p q V X Γ K L f τ₀ τ₁) (hcS : CarrierS ND)
    {i : ℕ} {s : Finset (E N)} (hs : s ∈ ND.Γ₁.faces)
    (hsub : simp s ⊆ K ∪ ⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], simp (ND.ord[j].erase w)) : s.card ≤ p + 1 := by
  classical
  let Q : Set (E N) := (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], simp (ND.ord[j].erase w))
  have hQdef : Q = (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], simp (ND.ord[j].erase w)) := rfl
  have hKsub : IsSubSp ND.Γ₁ K := ND.subsp K H7.subK
  have hQsub : IsSubSp ND.Γ₁ Q := by
    constructor
    · intro x hx
      rw [hQdef] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨j, -, hj', w, -, hx⟩ := hx
      exact Geometry.SimplicialComplex.convexHull_subset_space
        (ND.ord_mem _ (List.getElem_mem hj')) (simp_mono (Finset.erase_subset w _) hx)
    · intro x hx
      rw [hQdef] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨j, hjmem, hj', w, hw, hx⟩ := hx
      have hjface : ND.ord[j] ∈ ND.Γ₁.faces := ND.ord_mem _ (List.getElem_mem hj')
      have hne : (ND.ord[j].erase w).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hw,
          ND.ord_card _ (List.getElem_mem hj'), H7.card]
        omega
      refine ⟨ND.ord[j].erase w, ND.Γ₁.down_closed hjface (Finset.erase_subset w _) hne,
        hx, fun y hy => ?_⟩
      rw [hQdef]
      exact Set.mem_iUnion₂.mpr ⟨j, hjmem, Set.mem_iUnion.mpr ⟨hj',
        Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩⟩⟩
  rcases Work.Engulf.Aux.face_subset_of_subset_union ND.hΓ₁ hKsub hQsub hs hsub with hK | hQ
  · obtain ⟨t, htf, hst, htK⟩ := hcS K H7.subK s hs hK
    have hdimt : t.card ≤ p + 1 :=
      H7.cfg.dimH t htf (fun y hy => Or.inl (htK hy))
    have hcard := card_le_of_simp_subset hs htf hst
    omega
  · set T : Finset (Finset (E N)) :=
      ND.ord.toFinset.biUnion (fun σ => σ.image (fun w => σ.erase w)) with hTdef
    have hTcov : Q ⊆ ⋃ t ∈ T, simp t := by
      intro x hx
      rw [hQdef] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨j, -, hj', w, hw, hx⟩ := hx
      have hσ : ND.ord[j] ∈ ND.ord.toFinset := List.mem_toFinset.mpr (List.getElem_mem hj')
      have herase : ND.ord[j].erase w ∈ T := by
        rw [hTdef, Finset.mem_biUnion]
        exact ⟨ND.ord[j], hσ, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨ND.ord[j].erase w, herase, hx⟩
    have hTface : ∀ t ∈ T, t ∈ ND.Γ₁.faces := by
      intro t ht
      rw [hTdef, Finset.mem_biUnion] at ht
      obtain ⟨σ, hσ, ht⟩ := ht
      rw [Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hσord : σ ∈ ND.ord := List.mem_toFinset.mp hσ
      have hne : (σ.erase w).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hw, ND.ord_card σ hσord, H7.card]
        omega
      exact ND.Γ₁.down_closed (ND.ord_mem σ hσord) (Finset.erase_subset w σ) hne
    obtain ⟨t, htT, hst⟩ := Work.Engulf.simp_cover hTface hs (hQ.trans hTcov)
    have htcard : t.card ≤ q + 1 := by
      rw [hTdef, Finset.mem_biUnion] at htT
      obtain ⟨σ, hσ, htT⟩ := htT
      rw [Finset.mem_image] at htT
      obtain ⟨w, hw, rfl⟩ := htT
      rw [Finset.card_erase_of_mem hw, ND.ord_card σ (List.mem_toFinset.mp hσ), H7.card]
      omega
    have hcard := card_le_of_simp_subset hs (hTface t htT) hst
    have hqp : q ≤ p := H7.hq
    omega

/-! ### Two elementary helpers of the `E4d` push (vendored from `Work.Engulf.E4alt.step`)

They are re-stated here under area `E4S`'s own namespace so that `Work.Engulf.E4S.Step` does not
depend on the (fixed-map) module `Work.Engulf.E4alt.step`. -/

/-- The open cube is convex. -/
lemma convex_openCube' {n : ℕ} (r : ℝ) : Convex ℝ (PL.openCube (n := n) r) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [PL.openCube, Set.mem_setOf_eq] at hx hy ⊢
  intro i
  have hxi := hx i
  have hyi := hy i
  rw [abs_lt] at hxi hyi ⊢
  have hcoord : (a • x + b • y) i = a * x i + b * y i := by
    simp [PiLp.add_apply, PiLp.smul_apply]
  rw [hcoord]
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The projection of the prism `Pr a b = E a × E b × ℝ` onto its middle factor. -/
noncomputable def prProj (a b : ℕ) : Work.Engulf.Pr a b →ₗ[ℝ] PL.E b :=
  (LinearMap.fst ℝ (PL.E b) ℝ).comp (LinearMap.snd ℝ (PL.E a) (PL.E b × ℝ))

@[simp] lemma prProj_apply (a b : ℕ) (x : PL.E a) (y : PL.E b) (t : ℝ) :
    prProj a b (x, y, t) = y := rfl

/-- **The base case of the shelling loop**: `g := ND.g₁` and `h := Homeomorph.refl M` satisfy
`AltInnerG` at `i = 0`, with `eng` from `NormData.g₁_eng` (`X ∪ g₁ '' K ⊆ V`). -/
theorem altInnerG_zero {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε) (Cr : Set (E N)) {β : ℝ} :
    AltInnerG V X K L Cr ND.Γ₁ ND.g₁ ND.ord β 0 ND.g₁ (Homeomorph.refl M) := by
  have h0 : (⋃ j ∈ Finset.range 0, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) = (∅ : Set (E N)) := by
    simp
  refine ⟨Nat.zero_le _, ?_, ND.g₁cont, fun x _ => rfl, ?_, ?_⟩
  · exact ⟨∅, isCompact_empty, Set.empty_subset _, fun x _ => rfl⟩
  · intro x hx
    simp
  · intro y hy
    have hy' : y ∈ X ∪ ND.g₁ '' K := by
      rcases hy with hX | hy
      · exact Or.inl hX
      · right
        obtain ⟨x, hx, rfl⟩ := hy
        have hxK : x ∈ K := by
          rcases hx with hx | hx
          · exact hx
          · rw [h0] at hx; exact absurd hx (Set.notMem_empty x)
        exact ⟨x, hxK, rfl⟩
    exact ⟨y, ND.g₁_eng hy', rfl⟩

/-- **`Q` is a subcomplex of `Γ₁`.**  `Q = ⋃_{j < i} ⋃_{w ∈ ord[j]} simp (ord[j].erase w)` is the
`q`-skeleton contributed by the first `i` members of the shelling order.  Each `ord[j]` is a
`(q+2)`-face of `Γ₁` (`ord_card`, `H7.card`), so every `ord[j].erase w` is a nonempty proper face. -/
theorem isSubSp_skeleton {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : L7Hyp n p q V X Γ K L f τ₀ τ₁) (i : ℕ) :
    IsSubSp ND.Γ₁ (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], simp (ND.ord[j].erase w)) := by
  constructor
  · intro x hx
    rw [Set.mem_iUnion] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨j, -, hj', w, -, hx⟩ := hx
    exact Geometry.SimplicialComplex.convexHull_subset_space
      (ND.ord_mem _ (List.getElem_mem hj')) (simp_mono (Finset.erase_subset w _) hx)
  · intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨j, hjmem, hj', w, hw, hx⟩ := hx
    have hjface : ND.ord[j] ∈ ND.Γ₁.faces := ND.ord_mem _ (List.getElem_mem hj')
    have hne : (ND.ord[j].erase w).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hw,
        ND.ord_card _ (List.getElem_mem hj'), H7.card]
      omega
    refine ⟨ND.ord[j].erase w, ND.Γ₁.down_closed hjface (Finset.erase_subset w _) hne,
      hx, fun y hy => ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hjmem, Set.mem_iUnion.mpr ⟨hj',
      Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩⟩⟩

/-- `K ∪ Q` is a subcomplex of `Γ₁` (`K` is one by hypothesis, `Q` by `isSubSp_skeleton`). -/
theorem isSubSp_K_union_Q {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : L7Hyp n p q V X Γ K L f τ₀ τ₁) (i : ℕ) :
    IsSubSp ND.Γ₁ (K ∪ ⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], simp (ND.ord[j].erase w)) :=
  isSubSp_union (ND.subsp K H7.subK) (isSubSp_skeleton ND H7 i)

end Work.Engulf.E4S
