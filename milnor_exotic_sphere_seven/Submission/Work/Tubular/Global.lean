import Mathlib
import Submission.Work.Tubular.Small
import Submission.Work.Tubular.TubeBasic
import Submission.Work.Tubular.Collapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

/-!
# The tubular neighbourhood theorem

This file assembles the tubular neighbourhood theorem `Work.Tubular.HasTubularNeighbourhood` for a
compact smooth `8`-manifold `V` embedded in `ℝ^{8+k}` (the model of
`Work.ThomBordism.PontryaginThom.EmbeddingData`), out of

* the **local** tube charts `Work.Tubular.LocalTube` and the chosen family
  `Work.Tubular.localTube` (`Work.Tubular.nonempty_localTube`),
* the **injectivity at small scale** `Work.Tubular.exists_injOn_tubeMap_small`, and
* the compactness of the closed disc bundle `Work.Tubular.compactSpace_normalDiscSub`.

The radius used is `eps = min eps₀ (η/2)`, where `eps₀` is the injectivity radius and `η > 0` is a
uniform lower bound for the radii `η_x` of the local tube charts over a finite cover of `V`.  The two
extra facts of `TubeChart` (that the open tube is open, and that the inverse is `C^∞` there) come
from the local tube charts, patched along the cover: this is where `η` is used, to guarantee that a
point of the `eps`-disc bundle over `S x` really lies in the local tube `W x`.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **A finite cover of `V` by local tube charts with a uniform radius.**  The local tube charts
`Work.Tubular.localTube` cover `V` by their neighbourhoods `S`, and because `V` is compact there is a
finite subcover; since a finite set of positive numbers has a positive minimum, the radii `η` can be
taken uniform over that subcover. -/
theorem finite_localTubeCover (E : EmbeddingData V (8 + k)) [Nonempty V.pt] :
    ∃ (t : Finset V.pt) (η : ℝ), 0 < η ∧ (∀ x ∈ t, η ≤ (localTube E x).η) ∧
      ∀ y : V.pt, ∃ x ∈ t, y ∈ (localTube E x).S := by
  classical
  obtain ⟨t, ht⟩ := (isCompact_univ (X := V.pt)).elim_finite_subcover
    (fun x : V.pt => (localTube E x).S) (fun x => (localTube E x).hS)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, (localTube E x).mem_S⟩)
  have htne : t.Nonempty := by
    obtain ⟨x₀⟩ := ‹Nonempty V.pt›
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x₀))
    exact ⟨y, hy⟩
  refine ⟨t, t.inf' htne (fun x => (localTube E x).η), ?_, fun x hx => Finset.inf'_le _ hx, ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun x _ => (localTube E x).η_pos
  · intro y
    obtain ⟨x, hx, hyS⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact ⟨x, hx, hyS⟩

/-- **The open tube is open**, from a cover of `V` by local tube charts of radius at least `eta`.
For a point `y = tubeMap p` of the open `eps`-tube with `eps < eta`, the base point `p.proj` lies in
some `S x`, and then `p ∈ W x` (because `‖p.vec‖ < eps < eta ≤ η x`); the image of
`W x ∩ {‖·‖ < eps}` is open by `Work.Tubular.LocalTube.isOpen_image_inter`. -/
theorem isOpen_openTube_of_cover (E : EmbeddingData V (8 + k)) {eps eta : ℝ} (heta : eps < eta)
    (hcov : ∀ y : V.pt, ∃ x : V.pt, y ∈ (localTube E x).S ∧ eta ≤ (localTube E x).η) :
    IsOpen (openTubeSet E eps) := by
  classical
  rw [openTubeSet, isOpen_iff_mem_nhds]
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨x, hxS, hxη⟩ := hcov p.1.1
  have hpW : p ∈ (localTube E x).W :=
    (localTube E x).nbd p.1.1 hxS p.1.2 p.2 (by
      have := lt_of_lt_of_le hp (le_of_lt (lt_of_lt_of_le heta hxη))
      simpa [normalNorm] using this)
  have hopenL : IsOpen (tubeMap E '' ((localTube E x).W ∩ {q | normalNorm E q < eps})) :=
    (localTube E x).isOpen_image_inter (isOpen_lt (continuous_normalNorm E) continuous_const)
  refine mem_of_superset (hopenL.mem_nhds ⟨p, ⟨hpW, hp⟩, rfl⟩) ?_
  rintro z ⟨q, ⟨-, hq⟩, rfl⟩
  exact ⟨q, hq, rfl⟩

/-- **The tube from injectivity at small scale.**  From the injectivity of the tubular map on the
closed `eps`-disc bundle one gets the closed tube `U = tubeMap '' {‖·‖ ≤ eps}`, a total "normal foot"
map `inv`, the two inverse identities and the continuity of `inv` on `U`: the tubular map is a
continuous bijection from the compact disc bundle onto the Hausdorff `U`, hence a homeomorphism. -/
theorem tubeChartOfInjOn (E : EmbeddingData V (8 + k)) [Nonempty V.pt] {eps : ℝ} (heps : 0 < eps)
    (hinj : Set.InjOn (tubeMap E) {p : NormalTotal E | normalNorm E p ≤ eps}) :
    ∃ (U : Set (Euc (8 + k))) (inv : Euc (8 + k) → NormalTotal E),
      IsClosed U ∧
      U = tubeMap E '' {p : NormalTotal E | normalNorm E p ≤ eps} ∧
      (∀ y ∈ U, normalNorm E (inv y) ≤ eps) ∧
      (∀ y ∈ U, tubeMap E (inv y) = y) ∧
      (∀ p : NormalTotal E, normalNorm E p ≤ eps → tubeMap E p ∈ U) ∧
      (∀ p : NormalTotal E, normalNorm E p ≤ eps → inv (tubeMap E p) = p) ∧
      ContinuousOn inv U := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty V.pt›
  haveI : CompactSpace (NormalDiscSub E eps) := compactSpace_normalDiscSub E eps
  let D : Set (NormalTotal E) := {p | normalNorm E p ≤ eps}
  have hDc : IsCompact D := isCompact_normalClosedDiscSet E eps
  let U : Set (Euc (8 + k)) := tubeMap E '' D
  have hUc : IsClosed U := (hDc.image (continuous_tubeMap E)).isClosed
  let Ψ : NormalDiscSub E eps → U := fun q => ⟨tubeMap E q.1, ⟨q.1, q.2, rfl⟩⟩
  have hΨcont : Continuous Ψ :=
    Continuous.subtype_mk ((continuous_tubeMap E).comp continuous_subtype_val)
      (fun q => ⟨q.1, q.2, rfl⟩)
  have hΨbij : Function.Bijective Ψ := by
    constructor
    · intro q q' h
      exact Subtype.ext (hinj q.2 q'.2 (congrArg Subtype.val h))
    · rintro ⟨y, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  let H : NormalDiscSub E eps ≃ₜ U :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Ψ hΨbij) hΨcont
  let inv : Euc (8 + k) → NormalTotal E :=
    fun y => if h : y ∈ U then (H.symm ⟨y, h⟩).1 else ⟨(x₀, 0), by simp⟩
  have hinv_eq : ∀ (y : Euc (8 + k)) (h : y ∈ U), inv y = (H.symm ⟨y, h⟩).1 := by
    intro y h
    show (if h' : y ∈ U then (H.symm ⟨y, h'⟩).1 else _) = _
    rw [dif_pos h]
  have hHapply : ∀ q : NormalDiscSub E eps, H q = Ψ q := fun q => rfl
  refine ⟨U, inv, hUc, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hinv_eq y hy]
    exact (H.symm ⟨y, hy⟩).2
  · intro y hy
    rw [hinv_eq y hy]
    have h := congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩)
    simpa [hHapply, Ψ] using h
  · intro p hp
    exact ⟨p, hp, rfl⟩
  · intro p hp
    have hmem : tubeMap E p ∈ U := ⟨p, hp, rfl⟩
    rw [hinv_eq (tubeMap E p) hmem]
    have h3 : H.symm ⟨tubeMap E p, hmem⟩ = (⟨p, hp⟩ : NormalDiscSub E eps) := by
      have h4 : (⟨tubeMap E p, hmem⟩ : U) = H (⟨p, hp⟩ : NormalDiscSub E eps) :=
        Subtype.ext rfl
      rw [h4, H.symm_apply_apply]
    exact congrArg Subtype.val h3
  · have hcont_restrict : Continuous
        ((Subtype.val : NormalDiscSub E eps → NormalTotal E) ∘
          (H.symm : U → NormalDiscSub E eps)) :=
      (continuous_subtype_val : Continuous
        (Subtype.val : NormalDiscSub E eps → NormalTotal E)).comp H.symm.continuous
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : U.domRestrict inv = (Subtype.val : NormalDiscSub E eps → NormalTotal E) ∘
        (H.symm : U → NormalDiscSub E eps) := by
      funext y
      simp only [Set.domRestrict_apply, Function.comp_apply]
      exact hinv_eq y.1 y.2
    rw [hfun]
    exact hcont_restrict

/-- **The tubular neighbourhood theorem** for a compact smooth `8`-manifold embedded in
`ℝ^{8+k}`: there is `ε > 0` such that the tubular map `(x,w) ↦ e x + w` is a homeomorphism of the
closed `ε`-disc bundle of the normal bundle onto a closed neighbourhood `U` of `e(V)`, and a
diffeomorphism of the open `ε`-disc bundle onto the open tube, which is open.

The hypothesis `[Nonempty V.pt]` is needed only to define the total inverse (`TubeChart.inv` is a
function `ℝ^{8+k} → ν`); for empty `V` the closed disc bundle is empty and the homeomorphism
statement is vacuous. -/
theorem hasTubularNeighbourhood (E : EmbeddingData V (8 + k)) [Nonempty V.pt] :
    HasTubularNeighbourhood E := by
  classical
  obtain ⟨t, η, hηpos, hηle, hcov⟩ := finite_localTubeCover E
  have hcov' : ∀ y : V.pt, ∃ x : V.pt, y ∈ (localTube E x).S ∧ η ≤ (localTube E x).η := by
    intro y
    obtain ⟨x, hx, hyS⟩ := hcov y
    exact ⟨x, hyS, hηle x hx⟩
  obtain ⟨ε₀, hε₀pos, hε₀inj⟩ := exists_injOn_tubeMap_small E
  set eps := min ε₀ (η / 2) with hepsdef
  have hepspos : 0 < eps := lt_min hε₀pos (by linarith)
  have hepsη : eps < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hepsε₀ : eps ≤ ε₀ := min_le_left _ _
  have hinj : Set.InjOn (tubeMap E) {p : NormalTotal E | normalNorm E p ≤ eps} :=
    hε₀inj.mono (fun p hp => le_trans hp hepsε₀)
  obtain ⟨U, inv, hUc, hUeq, hinv_mem, htubeMap_inv, hmem_U, hinv_tubeMap, hcontU⟩ :=
    tubeChartOfInjOn E hepspos hinj
  have hopen : IsOpen (openTubeSet E eps) := isOpen_openTube_of_cover E hepsη hcov'
  have hsub : openTubeSet E eps ⊆ U := by
    rintro y ⟨p, hp, rfl⟩
    exact hmem_U p (le_of_lt hp)
  have hcontOpen : ContinuousOn inv (openTubeSet E eps) := hcontU.mono hsub
  have hsmooth : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) ((𝓡 8).prod 𝓘(ℝ, Euc (8 + k))) ∞
      (fun y => ((inv y).1.1, (inv y).1.2)) (openTubeSet E eps) := by
    refine contMDiffOn_of_locally_contMDiffOn fun y hy => ?_
    have hyop : y ∈ openTubeSet E eps := hy
    obtain ⟨p, hp, hpy⟩ := hy
    have hpU : normalNorm E p ≤ eps := le_of_lt hp
    have hinvy : inv y = p := by
      rw [← hpy]
      exact hinv_tubeMap p hpU
    obtain ⟨x, hxS, hxη⟩ := hcov' p.1.1
    have hproj : ContinuousOn (fun y' : Euc (8 + k) => (inv y').1.1) (openTubeSet E eps) :=
      (NormalTotal.continuous_proj E).comp_continuousOn hcontOpen
    set u : Set (Euc (8 + k)) :=
      openTubeSet E eps ∩ {y' | (inv y').1.1 ∈ (localTube E x).S} with hudef
    have huopen : IsOpen u := hproj.isOpen_inter_preimage hopen (localTube E x).hS
    have hyu : y ∈ u := by
      refine ⟨hyop, ?_⟩
      show (inv y).1.1 ∈ (localTube E x).S
      rw [hinvy]
      exact hxS
    refine ⟨u, huopen, hyu, ?_⟩
    have hkey : ∀ y' ∈ openTubeSet E eps ∩ u,
        (‖(inv y').1.2‖ < (localTube E x).η) ∧ inv y' ∈ (localTube E x).W := by
      intro y' hy'
      obtain ⟨hy'op, hy'u⟩ := hy'
      rw [hudef] at hy'u
      have hy'S : (inv y').1.1 ∈ (localTube E x).S := hy'u.2
      have hy'U : y' ∈ U := hsub hy'op
      have hylt : ‖(inv y').1.2‖ < (localTube E x).η := by
        have h1 : normalNorm E (inv y') ≤ eps := hinv_mem y' hy'U
        have h2 : normalNorm E (inv y') < (localTube E x).η :=
          lt_of_le_of_lt h1 (lt_of_lt_of_le hepsη hxη)
        simpa [normalNorm] using h2
      exact ⟨hylt, (localTube E x).nbd (inv y').1.1 hy'S (inv y').1.2 (inv y').2 hylt⟩
    have hinv_eq : ∀ y' ∈ openTubeSet E eps ∩ u,
        inv y' = (localTube E x).invLoc y' := by
      intro y' hy'
      obtain ⟨hy'op, hy'u⟩ := hy'
      have hy'U : y' ∈ U := hsub hy'op
      have hWy : inv y' ∈ (localTube E x).W := (hkey y' ⟨hy'op, hy'u⟩).2
      have hmem : tubeMap E (inv y') ∈ (localTube E x).U :=
        (localTube E x).image_eq ▸ ⟨inv y', hWy, rfl⟩
      have hWyU : y' ∈ (localTube E x).U := by
        rwa [htubeMap_inv y' hy'U] at hmem
      have hWi : (localTube E x).invLoc y' ∈ (localTube E x).W :=
        (localTube E x).invLoc_mem y' hWyU
      have heq : tubeMap E ((localTube E x).invLoc y') = tubeMap E (inv y') := by
        rw [(localTube E x).tubeMap_invLoc y' hWyU, htubeMap_inv y' hy'U]
      exact ((localTube E x).injOn hWi hWy heq).symm
    refine ((localTube E x).contMDiffOn_invLoc.mono ?_).congr ?_
    · intro y' hy'
      have hy'U : y' ∈ U := hsub hy'.1
      exact (localTube E x).image_eq ▸ ⟨inv y', (hkey y' hy').2, htubeMap_inv y' hy'U⟩
    · intro y' hy'
      exact congrArg (fun z : NormalTotal E => (z.1.1, z.1.2)) (hinv_eq y' hy')
  refine ⟨eps, hepspos, ⟨?_⟩⟩
  exact ⟨hepspos, U, hUc, inv, hinv_mem, htubeMap_inv, hmem_U, hinv_tubeMap, hcontU, hopen,
    hsmooth⟩

end

end Work.Tubular
