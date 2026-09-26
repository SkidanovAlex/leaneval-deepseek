import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.Drive.Mono.cylRegion_e_mem_interior
import Submission.Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc
import Submission.Work.Drive.Mono.WindowCase.exists_cupParam

namespace Work.Drive.Mono.FiberModel

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

/-! ## The hypoRegion under the graph, and its three pieces -/

/-- The hypoRegion under the graph of the height `g` over the plane set `K`. -/
def hypoRegion (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | cproj P ∈ K ∧ 0 ≤ clast P ∧ clast P ≤ g (cproj P)}

/-- The bottom disc of the hypoRegion. -/
def hypoBot (K : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | cproj P ∈ K ∧ clast P = 0}

/-- The top graph of the hypoRegion. -/
def hypoTop (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | cproj P ∈ K ∧ clast P = g (cproj P)}

/-- The side wall of the hypoRegion, over the frontier of `K`. -/
def hypoWall (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | cproj P ∈ frontier K ∧ 0 ≤ clast P ∧ clast P ≤ g (cproj P)}

/-- The open intermediate region: the interior of the hypoRegion, in coordinates. -/
def hypoInt (K : Set (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {P | cproj P ∈ interior K ∧ 0 < clast P ∧ clast P < g (cproj P)}

/-! ## Metric normal forms for `cmk` -/

theorem norm_cmk_zero_fn (y : ℝ) : ‖cmk (0 : EuclideanSpace ℝ (Fin 2)) y‖ = |y| := by
  have h2 : ‖cmk (0 : EuclideanSpace ℝ (Fin 2)) y‖ ^ 2 = y ^ 2 := by
    rw [norm_sq_cmk]; simp
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq_eq_abs]

theorem norm_cmk_zero_left (x : EuclideanSpace ℝ (Fin 2)) : ‖cmk x 0‖ = ‖x‖ := by
  have h2 : ‖cmk x 0‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_cmk]; simp
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg x)]

theorem dist_cmk_same_proj (x : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    dist (cmk x y) (cmk x y') = |y - y'| := by
  rw [dist_eq_norm]
  have h : cmk x y - cmk x y' = cmk 0 (y - y') := by rw [cmk_sub, sub_self]
  rw [h, norm_cmk_zero_fn]

theorem dist_cmk_same_last (x x' : EuclideanSpace ℝ (Fin 2)) (y : ℝ) :
    dist (cmk x y) (cmk x' y) = dist x x' := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : cmk x y - cmk x' y = cmk (x - x') 0 := by rw [cmk_sub, sub_self]
  rw [h, norm_cmk_zero_left]

/-! ## The interior of the hypoRegion -/

theorem solidInt_subset (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) : hypoInt K g ⊆ hypoRegion K g :=
  fun _ hP => ⟨interior_subset hP.1, le_of_lt hP.2.1, le_of_lt hP.2.2⟩

theorem isOpen_solidInt {K : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K) : IsOpen (hypoInt K g) := by
  rw [isOpen_iff_mem_nhds]
  intro P hP
  rw [hypoInt] at hP
  obtain ⟨hX, h0, hlt⟩ := hP
  have hXK : cproj P ∈ K := interior_subset hX
  have hgap : 0 < g (cproj P) - clast P := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hX)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousWithinAt_iff.mp (hgc _ hXK)
    ((g (cproj P) - clast P) / 2) (by linarith)
  set δ : ℝ := min δ₁ (min δ₂ (min (clast P / 2) ((g (cproj P) - clast P) / 2))) with hδ
  have hδpos : 0 < δ := lt_min hδ₁pos (lt_min hδ₂pos (lt_min (by linarith) (by linarith)))
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδpos, fun Q hQ => ?_⟩
  rw [Metric.mem_ball] at hQ
  have hδ₁le : δ ≤ δ₁ := by rw [hδ]; exact min_le_left _ _
  have hδ₂le : δ ≤ δ₂ := by rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδs : δ ≤ clast P / 2 := by
    rw [hδ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδg : δ ≤ (g (cproj P) - clast P) / 2 := by
    rw [hδ]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hproj : dist (cproj Q) (cproj P) ≤ dist Q P := by
    rw [dist_eq_norm, dist_eq_norm, ← cproj_sub]
    exact norm_cproj_le (Q - P)
  have hlast : |clast Q - clast P| ≤ dist Q P := by
    rw [dist_eq_norm, ← clast_sub]
    exact abs_clast_le (Q - P)
  have hQint : cproj Q ∈ interior K :=
    hδ₁ (lt_of_le_of_lt hproj (lt_of_lt_of_le hQ hδ₁le))
  have hQK : cproj Q ∈ K := interior_subset hQint
  have hgQ : dist (g (cproj Q)) (g (cproj P)) < (g (cproj P) - clast P) / 2 :=
    hδ₂ hQK (lt_of_le_of_lt hproj (lt_of_lt_of_le hQ hδ₂le))
  have hQ0 : 0 < clast Q := by
    have := neg_abs_le (clast Q - clast P)
    linarith [lt_of_le_of_lt hlast (lt_of_lt_of_le hQ hδs)]
  have hQlt : clast Q < g (cproj Q) := by
    have h1 : clast Q < clast P + (g (cproj P) - clast P) / 2 := by
      have := le_abs_self (clast Q - clast P)
      linarith [lt_of_le_of_lt hlast (lt_of_lt_of_le hQ hδg)]
    have h2 : (g (cproj P) + clast P) / 2 < g (cproj Q) := by
      have := abs_lt.mp (by rw [Real.dist_eq] at hgQ; exact hgQ)
      linarith [this.1]
    linarith
  rw [hypoInt]
  exact ⟨hQint, hQ0, hQlt⟩

theorem interior_solid_eq {K : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K) :
    interior (hypoRegion K g) = hypoInt K g := by
  refine Subset.antisymm ?_ (interior_maximal (solidInt_subset K g) (isOpen_solidInt hgc))
  intro P hP
  rw [mem_interior_iff_mem_nhds] at hP
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hP
  have hPH : P ∈ hypoRegion K g := hδsub (Metric.mem_ball_self hδpos)
  rw [hypoRegion] at hPH
  obtain ⟨hXK, h0, hle⟩ := hPH
  have hPmk : P = cmk (cproj P) (clast P) := (cmk_cproj_clast P).symm
  rw [hypoInt]
  refine ⟨?_, ?_, ?_⟩
  · by_contra hX
    have hcl : cproj P ∈ closure (Kᶜ) := by rw [closure_compl]; exact hX
    obtain ⟨x, hxK, hxd⟩ := Metric.mem_closure_iff.mp hcl δ hδpos
    have hdist : dist (cmk x (clast P)) P < δ := by
      rw [hPmk]
      simp only [clast_cmk, cproj_cmk]
      rw [dist_cmk_same_last, dist_comm]
      exact hxd
    have hmem := hδsub (Metric.mem_ball.mpr hdist)
    rw [hypoRegion] at hmem
    simp only [Set.mem_ofPred_eq, cproj_cmk] at hmem
    exact hxK hmem.1
  · by_contra h
    rw [not_lt] at h
    have hc0 : clast P = 0 := le_antisymm h h0
    have hdist : dist (cmk (cproj P) (-(δ / 2))) P < δ := by
      rw [hPmk]
      simp only [clast_cmk, cproj_cmk]
      rw [dist_cmk_same_proj, hc0, sub_zero, abs_neg, abs_of_pos (by linarith)]
      linarith
    have hmem := hδsub (Metric.mem_ball.mpr hdist)
    rw [hypoRegion] at hmem
    simp only [Set.mem_ofPred_eq, clast_cmk] at hmem
    linarith [hmem.2.1]
  · by_contra h
    rw [not_lt] at h
    have heq : clast P = g (cproj P) := le_antisymm hle h
    have hdist : dist (cmk (cproj P) (clast P + δ / 2)) P < δ := by
      rw [hPmk]
      simp only [clast_cmk, cproj_cmk]
      rw [dist_cmk_same_proj, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    have hmem := hδsub (Metric.mem_ball.mpr hdist)
    rw [hypoRegion] at hmem
    simp only [Set.mem_ofPred_eq, clast_cmk, cproj_cmk] at hmem
    linarith [hmem.2.2, heq]

/-! ## The hypoRegion is closed, and its frontier is the union of the three pieces -/

theorem isClosed_solid {K : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hKcomp : IsCompact K) (hgc : ContinuousOn g K) :
    IsClosed (hypoRegion K g) := by
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hT : IsClosed ((K ×ˢ Set.Ici (0 : ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - g q.1) ⁻¹' Set.Iic (0 : ℝ)) := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hKclosed.prod isClosed_Ici) isClosed_Iic
    exact continuous_snd.continuousOn.sub
      (hgc.comp continuous_fst.continuousOn (fun q hq => hq.1))
  have hmap : Continuous fun P : EuclideanSpace ℝ (Fin 3) => (cproj P, clast P) :=
    continuous_cproj.prodMk continuous_clast
  have heq : hypoRegion K g = (fun P : EuclideanSpace ℝ (Fin 3) => (cproj P, clast P)) ⁻¹'
      ((K ×ˢ Set.Ici (0 : ℝ)) ∩
        (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - g q.1) ⁻¹' Set.Iic (0 : ℝ)) := by
    ext P
    rw [hypoRegion]
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ici, Set.mem_Iic,
      Set.mem_ofPred_eq, sub_nonpos]
    exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  rw [heq]
  exact hT.preimage hmap

theorem frontier_solid_eq {K : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hKcomp : IsCompact K) (hgc : ContinuousOn g K)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    frontier (hypoRegion K g) = hypoBot K ∪ hypoTop K g ∪ hypoWall K g := by
  have hclosed : IsClosed (hypoRegion K g) := isClosed_solid hKcomp hgc
  have hfront : frontier (hypoRegion K g) = hypoRegion K g \ hypoInt K g := by
    rw [frontier, hclosed.closure_eq, interior_solid_eq hgc]
  rw [hfront]
  ext P
  constructor
  · intro hP
    rw [mem_sdiff, hypoRegion] at hP
    obtain ⟨⟨hXK, h0, hle⟩, hPni⟩ := hP
    rw [hypoInt] at hPni
    by_cases hXi : cproj P ∈ interior K
    · have hnot : ¬ (0 < clast P ∧ clast P < g (cproj P)) :=
        fun h => hPni ⟨hXi, h.1, h.2⟩
      rw [not_and_or, not_lt, not_lt] at hnot
      rcases hnot with h | h
      · left; left
        rw [hypoBot]
        exact ⟨interior_subset hXi, le_antisymm h h0⟩
      · left; right
        rw [hypoTop]
        exact ⟨hXK, le_antisymm hle h⟩
    · right
      refine ⟨?_, h0, hle⟩
      show cproj P ∈ frontier K
      rw [frontier, hKcomp.isClosed.closure_eq]
      exact ⟨hXK, hXi⟩
  · intro hP
    rw [mem_sdiff, hypoRegion]
    rcases hP with (hb | ht) | hw
    · rw [hypoBot] at hb
      obtain ⟨hXK, hc0⟩ := hb
      refine ⟨⟨hXK, by rw [hc0], by rw [hc0]; exact hg0 _ hXK⟩, ?_⟩
      rw [hypoInt]
      exact fun h => by simp only [Set.mem_ofPred_eq] at h; linarith [h.2.1, hc0]
    · rw [hypoTop] at ht
      obtain ⟨hXK, hceq⟩ := ht
      refine ⟨⟨hXK, by rw [hceq]; exact hg0 _ hXK, by rw [hceq]⟩, ?_⟩
      rw [hypoInt]
      exact fun h => by simp only [Set.mem_ofPred_eq] at h; linarith [h.2.2, hceq]
    · rw [hypoWall] at hw
      obtain ⟨hXf, h0, hle⟩ := hw
      have hXfn : cproj P ∈ K ∧ cproj P ∉ interior K := by
        rw [frontier, hKcomp.isClosed.closure_eq] at hXf
        exact ⟨hXf.1, hXf.2⟩
      refine ⟨⟨hXfn.1, h0, hle⟩, ?_⟩
      rw [hypoInt]
      exact fun h => by simp only [Set.mem_ofPred_eq] at h; exact hXfn.2 h.1

/-! ## The disc parametrisation of the cup, and the assembly -/

theorem isEmbeddedSphere_frontier_of_cup
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (he_inj : Function.Injective e)
    (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x)
    (E : C(𝔻, EuclideanSpace ℝ (Fin 3))) (hE_inj : Function.Injective E)
    (hE_range : Set.range E =
      {P : EuclideanSpace ℝ (Fin 3) | cproj P ∈ K ∧ clast P = 0} ∪
      {P : EuclideanSpace ℝ (Fin 3) | cproj P ∈ frontier K ∧
        0 ≤ clast P ∧ clast P ≤ g (cproj P)})
    (hE_bdry : ∀ θ : ℝ, E (Work.CoreTopology.circlePoint θ) =
      cmk (e (Work.CoreTopology.circlePoint θ)) (g (e (Work.CoreTopology.circlePoint θ)))) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier (hypoRegion K g)) := by
  have hKcomp : IsCompact K := by rw [← he_range]; exact isCompact_range e.continuous
  have hKclosed : IsClosed K := hKcomp.isClosed
  -- the graph disc
  have hge : Continuous fun z : 𝔻 => g (e z) :=
    hgc.comp_continuous e.continuous (fun z => by rw [← he_range]; exact Set.mem_range_self z)
  let eA : C(𝔻, EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun z => cmk (e z) (g (e z)),
      Work.Drive.Mono.continuous_cmk.comp (e.continuous.prodMk hge)⟩
  have heA : ∀ z : 𝔻, eA z = cmk (e z) (g (e z)) := fun z => rfl
  have hAinj : Function.Injective eA := by
    intro z w hzw
    rw [heA z, heA w] at hzw
    exact he_inj ((cmk_eq_cmk_iff _ _ _ _).mp hzw).1
  have hArange : Set.range eA = hypoTop K g := by
    rw [hypoTop]
    ext P
    constructor
    · rintro ⟨z, rfl⟩
      rw [heA z]
      exact ⟨by rw [cproj_cmk]; exact he_range ▸ Set.mem_range_self z,
        by rw [clast_cmk, cproj_cmk]⟩
    · rintro ⟨hPK, hceq⟩
      obtain ⟨z, hz⟩ := show cproj P ∈ Set.range e from he_range ▸ hPK
      exact ⟨z, by rw [heA z, ← cmk_cproj_clast P, hz, hceq]⟩
  have hbd : ∀ θ : ℝ, eA (Work.CoreTopology.circlePoint θ) =
      E (Work.CoreTopology.circlePoint θ) := by
    intro θ
    rw [heA, hE_bdry]
  have hint : ∀ z w : 𝔻, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 → eA z = E w → False := by
    intro z w hz _ heq
    have hzK : e z ∈ interior K :=
      (Work.Drive.Mono.cylRegion_e_mem_interior he_inj he_range he_bdry z).mpr hz
    have hproj : e z = cproj (E w) := by
      have h := congrArg cproj heq
      rw [heA z, cproj_cmk] at h
      exact h
    have hmw : E w ∈ Set.range E := Set.mem_range_self w
    rw [hE_range] at hmw
    rcases hmw with hb | hw
    · rw [Set.mem_ofPred_eq] at hb
      have hcl : clast (eA z) = clast (E w) := congrArg clast heq
      rw [heA z, clast_cmk, hb.2] at hcl
      have : 0 < g (e z) := hgpos _ hzK
      linarith
    · rw [Set.mem_ofPred_eq] at hw
      have hfr : e z ∈ frontier K := by rw [hproj]; exact hw.1
      have hni : e z ∉ interior K := by
        rw [frontier, hKclosed.closure_eq] at hfr
        exact hfr.2
      exact hni hzK
  have hsphere := Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc eA E hAinj hE_inj hbd hint
  have hE_range' : Set.range E = hypoBot K ∪ hypoWall K g := by
    rw [hypoBot, hypoWall]
    exact hE_range
  have hfront := frontier_solid_eq hKcomp hgc hg0
  have hunion : Set.range eA ∪ Set.range E = hypoBot K ∪ hypoTop K g ∪ hypoWall K g := by
    rw [hArange, hE_range']
    ext P
    simp only [Set.mem_union]
    tauto
  rw [hfront, ← hunion]
  exact hsphere

/-- **The frontier of the region under a nonnegative concave graph over a plane disc cut out of a
convex body by a slab and a half-plane is an embedded `2`-sphere.**

`K = closure (interior W ∩ {h' < |x₀ - a'| ∨ lam ≤ x₁})` is the plane disc of the fibre model, `g` is
the height `fMax - fMin` of the box fibres, and the solid is the region `0 ≤ x₃ ≤ g x` over `K`.
Two proofs are available:

1. the three pieces `p⁺ = closure (interior W ∩ {x₀ > a' + h'})`, `p⁻ = closure (interior W ∩
   {x₀ < a' - h'})`, `p⁰ = closure (interior W ∩ {lam < x₁})` are convex compact, `K` is their union
   and `interior K` the union of their interiors; each `Hⁱ` (the region under `g` over `pⁱ`) is
   convex, and when two pieces have intersecting interiors the union-convex tool
   `Work.Drive.Mono.isEmbeddedSphere_frontier_union_convex` applies directly;
2. `Work.Drive.Mono.isEmbeddedSphere_of_twoDiscs` with the two discs "graph of `g` over `K`" (image
   of the given disc parametrisation of `K`) and the "cup" (bottom over `K` glued to the wall over
   `frontier K`); the cup is a disc, but the natural collar parametrisation collapses over the set
   where `g = 0` on `frontier K`, which is exactly the pinch that the cylindrical-region tool
   (`Work.Drive.Mono.isEmbeddedSphere_frontier_of_cylindricalRegion`, needing `α < β` on all of `S`)
   cannot handle; the collapse is harmless because at a degenerate `X₀` the local model of the solid
   is a wedge `{(x,s) : 0 ≤ s ≤ c x², x ≤ 0}`, locally homeomorphic to a half-space via
   `(x,s) ↦ (x,√s)`. -/
theorem hypograph_sphere
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hWc : Convex ℝ W) (hWk : IsCompact W)
    (hWi : (interior W).Nonempty)
    {a' h' lam : ℝ} (hh' : 0 < h')
    {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hKdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hKcl : K = closure (interior W ∩
      {X : EuclideanSpace ℝ (Fin 2) | h' < |X 0 - a'| ∨ lam ≤ X 1}))
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hgc : ContinuousOn g K) (hg : ConcaveOn ℝ K g)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hgpos : ∀ x ∈ interior K, 0 < g x) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier {P : LeanEval.KnotTheory.PardonDistortion.R3 |
        Work.Drive.Mono.cproj P ∈ K ∧ 0 ≤ Work.Drive.Mono.clast P ∧
        Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)}) := by
  obtain ⟨e, he_inj, he_range, he_bdry⟩ := hKdisc
  obtain ⟨E, hE_inj, hE_range, hE_bdry⟩ :=
    Work.Drive.Mono.WindowCase.exists_cupParam e he_inj he_range he_bdry hgc hg0
  exact isEmbeddedSphere_frontier_of_cup e he_inj he_range he_bdry hgc hg0 hgpos E hE_inj
    hE_range hE_bdry

end

end Work.Drive.Mono.FiberModel
