import Mathlib
import Submission.Work.Tubular.Foot

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

/-!
# The local tube chart

`Foot.lean` produces, at every point of the zero section, a smooth local inverse `g` of the foot map.
This file turns that inverse into a *local tube chart*: an open set `W` of the normal bundle around
`(x₀, 0)`, an open set `U` of the ambient space with `tubeMap '' W = U`, and a smooth inverse
`U → W` of the tube map.  It also records the *quantitative* clause that makes the local charts patch
together: on an open neighbourhood `S` of `x₀` and up to a radius `η > 0`, the whole disc of the
normal bundle over `S` lies in `W`.

The extra work compared with the inverse function theorem is that the foot of a point is recognised
by the *kernel* condition `A_x† w = 0` (`Work.Tubular.tangentFrame_adjoint_eq_zero_iff`), and that
the neighbourhoods have to be shrunk so that the quantitative clause holds.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **A local tube chart of an embedded manifold**: on an open set `W` of the normal bundle around
`(x₀, 0)`, the tube map is injective with open image `U`, and it has a smooth inverse on `U`.  The
extra data `S`, `η` record that `W` contains the disc of radius `η` over a neighbourhood `S` of
`x₀`, which is what makes the local charts patch together into the global tube. -/
structure LocalTube (E : EmbeddingData V (8 + k)) (x₀ : V.pt) where
  /-- the open set of the normal bundle on which the tube map is inverted -/
  W : Set (NormalTotal E)
  hW : IsOpen W
  /-- `W` contains the base point of the zero section over `x₀` -/
  mem_W : (⟨(x₀, (0 : Euc (8 + k))), by simp [normalSpace]⟩ : NormalTotal E) ∈ W
  /-- the tube map is injective on `W` -/
  injOn : Set.InjOn (tubeMap E) W
  /-- the image of `W` under the tube map -/
  U : Set (Euc (8 + k))
  hU : IsOpen U
  image_eq : tubeMap E '' W = U
  /-- the inverse of the tube map on `U` -/
  invLoc : Euc (8 + k) → NormalTotal E
  invLoc_mem : ∀ y ∈ U, invLoc y ∈ W
  tubeMap_invLoc : ∀ y ∈ U, tubeMap E (invLoc y) = y
  continuousOn_invLoc : ContinuousOn invLoc U
  contMDiffOn_invLoc : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) ((𝓡 8).prod 𝓘(ℝ, Euc (8 + k))) ∞
    (fun y => ((invLoc y).1.1, (invLoc y).1.2)) U
  /-- the neighbourhood of `x₀` over which the local tube is uniform -/
  S : Set V.pt
  hS : IsOpen S
  mem_S : x₀ ∈ S
  /-- the uniform radius -/
  η : ℝ
  η_pos : 0 < η
  /-- the disc of radius `η` of the normal bundle over `S` lies in `W` -/
  nbd : ∀ (x : V.pt), x ∈ S → ∀ (w : Euc (8 + k)) (hw : w ∈ normalSpace E x),
      ‖w‖ < η → (⟨(x, w), hw⟩ : NormalTotal E) ∈ W

namespace LocalTube

variable {E : EmbeddingData V (8 + k)} {x₀ : V.pt}

/-- The image of the intersection of the local tube with a set `V'` is `{y ∈ U | invLoc y ∈ V'}`. -/
theorem image_inter_eq (L : LocalTube E x₀) {V' : Set (NormalTotal E)} :
    tubeMap E '' (L.W ∩ V') = {y ∈ L.U | L.invLoc y ∈ V'} := by
  ext y
  constructor
  · rintro ⟨q, ⟨hqW, hqV⟩, rfl⟩
    refine ⟨L.image_eq ▸ ⟨q, hqW, rfl⟩, ?_⟩
    have hmem : tubeMap E q ∈ L.U := L.image_eq ▸ ⟨q, hqW, rfl⟩
    rw [show L.invLoc (tubeMap E q) = q from
      L.injOn (L.invLoc_mem _ hmem) hqW (L.tubeMap_invLoc _ hmem)]
    exact hqV
  · rintro ⟨hyU, hyV⟩
    exact ⟨L.invLoc y, ⟨L.invLoc_mem y hyU, hyV⟩, L.tubeMap_invLoc y hyU⟩

/-- The image under the tube map of `W ∩ V'` is open when `V'` is open. -/
theorem isOpen_image_inter (L : LocalTube E x₀) {V' : Set (NormalTotal E)} (hV' : IsOpen V') :
    IsOpen (tubeMap E '' (L.W ∩ V')) := by
  rw [L.image_inter_eq]
  have h := L.continuousOn_invLoc.isOpen_inter_preimage L.hU hV'
  convert h using 1
  ext y
  rfl

end LocalTube


/-- **The local tube chart exists**: at every point of the zero section, the tube map is a
homeomorphism (with smooth inverse) from a neighbourhood of `(x₀, 0)` in the normal bundle onto an
open neighbourhood of the image, uniformly over a neighbourhood of `x₀`. -/
theorem nonempty_localTube (E : EmbeddingData V (8 + k)) (x₀ : V.pt) :
    Nonempty (LocalTube E x₀) := by
  classical
  obtain ⟨F⟩ := nonempty_footData E x₀
  have hτ₀ : (chartAtIdx x₀).1 x₀ ∈ (chartAtIdx x₀).1.target :=
    (chartAtIdx x₀).1.map_source F.mem_source
  have hy₀ : chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀) = E.e x₀ := by
    rw [chartRep, (chartAtIdx x₀).1.left_inv F.mem_source]
  have hbase : F.g ((0 : Euc 8), chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀))
      = ((chartAtIdx x₀).1 x₀, chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) := by
    refine F.injOn (F.g_mem _ F.mem_U) F.mem_W ?_
    rw [F.g_spec _ F.mem_U, footMap_zero]
  -- neighbourhoods in the chart and in the ambient space
  obtain ⟨Wτ₀, hWτ₀sub, hWτ₀open, hτ₀Wτ₀⟩ := mem_nhds_iff.mp
    ((chartAtIdx x₀).1.open_target.mem_nhds hτ₀)
  have hVW : F.W ∈ 𝓝 ((chartAtIdx x₀).1 x₀,
      chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) := F.hW.mem_nhds F.mem_W
  rw [nhds_prod_eq] at hVW
  obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := mem_prod_iff.mp hVW
  obtain ⟨Wτ₁, hWτ₁sub, hWτ₁open, hτ₀Wτ₁⟩ := mem_nhds_iff.mp ha₁
  obtain ⟨WT, hWTsub, hWTopen, hy₀WT⟩ := mem_nhds_iff.mp hb₁
  have hVU : F.U ∈ 𝓝 ((0 : Euc 8), chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) :=
    F.hU.mem_nhds F.mem_U
  rw [nhds_prod_eq] at hVU
  obtain ⟨a₂, ha₂, b₂, hb₂, hab₂⟩ := mem_prod_iff.mp hVU
  obtain ⟨U₂, hU₂sub, hU₂open, h0U₂⟩ := mem_nhds_iff.mp ha₂
  obtain ⟨UT, hUTsub, hUTopen, hy₀UT⟩ := mem_nhds_iff.mp hb₂
  -- the auxiliary maps
  set τfun : Euc (8 + k) → Euc 8 := fun y => (F.g ((0 : Euc 8), y)).1 with hτfundef
  set xfun : Euc (8 + k) → V.pt := fun y => (chartAtIdx x₀).1.symm (τfun y) with hxfundef
  set wfun : Euc (8 + k) → Euc (8 + k) := fun y => y - E.e (xfun y) with hwfundef
  have hτfun_y₀ : τfun (chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀))
      = (chartAtIdx x₀).1 x₀ := by
    rw [hτfundef]
    simpa using congrArg Prod.fst hbase
  have hxfun_y₀ : xfun (chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) = x₀ := by
    show (chartAtIdx x₀).1.symm (τfun (chartRep E.e (chartAtIdx x₀)
      ((chartAtIdx x₀).1 x₀))) = x₀
    rw [hτfun_y₀]
    exact (chartAtIdx x₀).1.left_inv F.mem_source
  -- the set of points whose foot is defined, and its openness
  set U₀ : Set (Euc (8 + k)) := {y | ((0 : Euc 8), y) ∈ F.U} with hU₀def
  have hU₀open : IsOpen U₀ := F.hU.preimage (continuous_const.prodMk continuous_id)
  have hτfun_contOn : ContinuousOn τfun U₀ :=
    (F.continuousOn_g.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => hy)).fst
  have hsymm_contOn : ContinuousOn (fun τ : Euc 8 => (chartAtIdx x₀).1.symm τ)
      ((chartAtIdx x₀).1.target) := by
    have hmem : (chartAtIdx x₀).1 ∈ IsManifold.maximalAtlas (𝓡 8) ∞ V.pt :=
      IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := ∞) (chartAtIdx x₀).2
    exact (contMDiffOn_symm_of_mem_maximalAtlas hmem).continuousOn
  -- the neighbourhood of the chart coordinate, and the sets of the local chart
  set Wτ : Set (Euc 8) := Wτ₀ ∩ Wτ₁ with hWτdef
  have hWτopen : IsOpen Wτ := hWτ₀open.inter hWτ₁open
  have hτ₀Wτ : (chartAtIdx x₀).1 x₀ ∈ Wτ := ⟨hτ₀Wτ₀, hτ₀Wτ₁⟩
  have hWτsub : Wτ ⊆ (chartAtIdx x₀).1.target := fun _ h => hWτ₀sub h.1
  set Snb : Set V.pt := (chartAtIdx x₀).1.source ∩ (chartAtIdx x₀).1 ⁻¹' Wτ with hSnbdef
  have hSnbopen : IsOpen Snb := by
    rw [hSnbdef]
    exact ((chartAtIdx x₀).1.continuousOn_toFun).isOpen_inter_preimage
      ((chartAtIdx x₀).1.open_source) hWτopen
  have hx₀Snb : x₀ ∈ Snb := by
    rw [hSnbdef]
    exact ⟨F.mem_source, hτ₀Wτ⟩
  have hxfun_contOn : ContinuousOn xfun (U₀ ∩ τfun ⁻¹' Wτ) :=
    hsymm_contOn.comp (hτfun_contOn.mono Set.inter_subset_left) (fun y hy => hWτsub hy.2)
  have hVopen : IsOpen ((U₀ ∩ τfun ⁻¹' Wτ) ∩ xfun ⁻¹' Snb) :=
    hxfun_contOn.isOpen_inter_preimage
      (hτfun_contOn.isOpen_inter_preimage hU₀open hWτopen) hSnbopen
  -- the ambient neighbourhood of the base point
  set Vc : Set (Euc (8 + k)) := ((U₀ ∩ τfun ⁻¹' Wτ) ∩ xfun ⁻¹' Snb) ∩ WT with hVcdef
  have hVc_open : IsOpen Vc := by
    rw [hVcdef]
    exact hVopen.inter hWTopen
  -- the base point lies in `Vc`
  have hy₀U₀ : ((0 : Euc 8), chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) ∈ F.U :=
    F.mem_U
  have hy₀Wτ : τfun (chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) ∈ Wτ := by
    rw [hτfun_y₀]; exact hτ₀Wτ
  have hy₀Snb : xfun (chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀)) ∈ Snb := by
    rw [hxfun_y₀]; exact hx₀Snb
  have hy₀Vc' : chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀) ∈ Vc := by
    rw [hVcdef]
    exact ⟨⟨⟨hy₀U₀, hy₀Wτ⟩, hy₀Snb⟩, hy₀WT⟩
  have hy₀eq : E.e x₀ + (0 : Euc (8 + k))
      = chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 x₀) := by
    rw [add_zero, ← hy₀]
  have hy₀Vc : E.e x₀ + (0 : Euc (8 + k)) ∈ Vc := by
    rw [hy₀eq]; exact hy₀Vc'
  -- continuity of the two maps defining the conditions
  have hcont_i : ContinuousAt (fun p : V.pt × Euc (8 + k) => (chartAtIdx x₀).1 p.1)
      (x₀, (0 : Euc (8 + k))) :=
    ((chartAtIdx x₀).1.continuousOn_toFun.continuousAt
      ((chartAtIdx x₀).1.open_source.mem_nhds F.mem_source)).comp continuousAt_fst
  have hcont_e : Continuous (fun p : V.pt × Euc (8 + k) => E.e p.1 + p.2) :=
    (E.smooth.continuous.comp continuous_fst).add continuous_snd
  -- the conditions hold near the base point
  have hev : ∀ᶠ p in 𝓝 (x₀, (0 : Euc (8 + k))),
      ((chartAtIdx x₀).1 p.1 ∈ Wτ) ∧ (E.e p.1 + p.2 ∈ Vc) :=
    (hcont_i.eventually (hWτopen.mem_nhds hτ₀Wτ)).and
      (hcont_e.continuousAt.eventually (hVc_open.mem_nhds hy₀Vc))
  rw [nhds_prod_eq] at hev
  obtain ⟨S₁, hS₁, B, hB, hSB⟩ := mem_prod_iff.mp hev
  obtain ⟨S₂, hS₂sub, hS₂open, hx₀S₂⟩ := mem_nhds_iff.mp hS₁
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp hB
  -- the neighbourhood of `x₀` for the quantitative clause
  set St : Set V.pt := S₂ ∩ Snb with hStdef
  have hStopen : IsOpen St := hS₂open.inter hSnbopen
  have hx₀St : x₀ ∈ St := ⟨hx₀S₂, hx₀Snb⟩
  -- the local tube data
  set Uloc : Set (Euc (8 + k)) := Vc with hUlocdef
  have hUloc_open : IsOpen Uloc := by rw [hUlocdef]; exact hVc_open
  set Wloc : Set (NormalTotal E) :=
    {q | q.1.1 ∈ Snb} ∩ {q | tubeMap E q ∈ Uloc} ∩ {q | tubeMap E q ∈ WT} with hWlocdef
  have mem_Uloc : ∀ y : Euc (8 + k), y ∈ Uloc ↔
      ((0 : Euc 8), y) ∈ F.U ∧ τfun y ∈ Wτ ∧ xfun y ∈ Snb ∧ y ∈ WT := by
    intro y
    rw [hVcdef, hU₀def, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨⟨⟨hU, hτ⟩, hx⟩, hWT⟩
      exact ⟨hU, hτ, hx, hWT⟩
    · rintro ⟨hU, hτ, hx, hWT⟩
      exact ⟨⟨⟨hU, hτ⟩, hx⟩, hWT⟩
  have mem_Wloc : ∀ q : NormalTotal E, q ∈ Wloc ↔
      q.1.1 ∈ Snb ∧ tubeMap E q ∈ Uloc ∧ tubeMap E q ∈ WT := by
    intro q
    rw [hWlocdef, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  -- the normal foot of a point of `Uloc`
  have hfoot : ∀ y ∈ Uloc, wfun y ∈ normalSpace E (xfun y) := by
    intro y hy
    obtain ⟨hyU, hyWτ, -, -⟩ := (mem_Uloc y).mp hy
    have htgt : τfun y ∈ (chartAtIdx x₀).1.target := hWτsub hyWτ
    have hsrc : xfun y ∈ (chartAtIdx x₀).1.source := (chartAtIdx x₀).1.map_target htgt
    have hgs : F.g ((0 : Euc 8), y) = (τfun y, y) :=
      Prod.ext rfl (by
        have hs := congrArg Prod.snd (F.g_spec _ hyU)
        simpa [footMap_apply] using hs)
    have hfeet : footMap E (chartAtIdx x₀) (τfun y, y) = ((0 : Euc 8), y) := by
      rw [← hgs]
      exact F.g_spec _ hyU
    have hker : (tauAdj E (chartAtIdx x₀) (τfun y))
        (y - chartRep E.e (chartAtIdx x₀) (τfun y)) = 0 := by
      have hf := congrArg Prod.fst hfeet
      simpa [footMap_apply] using hf
    have hker' : (tangentFrame E (chartAtIdx x₀) (xfun y)).adjoint (wfun y) = 0 := by
      have htf : tauAdj E (chartAtIdx x₀) (τfun y)
          = (tangentFrame E (chartAtIdx x₀) (xfun y)).adjoint := by
        have h3 : (chartAtIdx x₀).1 (xfun y) = τfun y := by
          show (chartAtIdx x₀).1 ((chartAtIdx x₀).1.symm (τfun y)) = τfun y
          exact (chartAtIdx x₀).1.right_inv htgt
        rw [tauAdj_eq, adjointClm_apply, tauFrame_eq_fderiv, tangentFrame_eq_fderiv, h3]
      rw [← htf]
      show (tauAdj E (chartAtIdx x₀) (τfun y)) (y - E.e (xfun y)) = 0
      exact hker
    exact (tangentFrame_adjoint_eq_zero_iff E (chartAtIdx x₀) hsrc (wfun y)).mp hker'
  -- the inverse of the tube map
  set invLoc : Euc (8 + k) → NormalTotal E := fun y =>
    if h : y ∈ Uloc then ⟨(xfun y, wfun y), hfoot y h⟩
    else ⟨(x₀, (0 : Euc (8 + k))), by simp [normalSpace]⟩ with hinvLocdef
  have hinvLoc_apply : ∀ y (h : y ∈ Uloc), invLoc y = ⟨(xfun y, wfun y), hfoot y h⟩ := by
    intro y h
    rw [hinvLocdef]
    simp only [dif_pos h]
  -- the tube map on the local chart
  have htm : ∀ y (h : y ∈ Uloc),
      tubeMap E (⟨(xfun y, wfun y), hfoot y h⟩ : NormalTotal E) = y := by
    intro y h
    show E.e (xfun y) + (y - E.e (xfun y)) = y
    exact (add_comm (E.e (xfun y)) (y - E.e (xfun y))).trans (sub_add_cancel y (E.e (xfun y)))
  -- openness of `Wloc`
  have hWloc_open : IsOpen Wloc := by
    rw [hWlocdef]
    exact ((hSnbopen.preimage (NormalTotal.continuous_proj E)).inter
      (hUloc_open.preimage (continuous_tubeMap E))).inter
      (hWTopen.preimage (continuous_tubeMap E))
  -- the base point
  have hmem : (⟨(x₀, (0 : Euc (8 + k))), by simp [normalSpace]⟩ : NormalTotal E) ∈ Wloc := by
    refine (mem_Wloc _).mpr ⟨?_, ?_, ?_⟩
    · show x₀ ∈ Snb
      exact hx₀Snb
    · show E.e x₀ + (0 : Euc (8 + k)) ∈ Vc
      exact hy₀Vc
    · show E.e x₀ + (0 : Euc (8 + k)) ∈ WT
      rw [hy₀eq]
      exact hy₀WT
  -- the image of the local chart
  have himage : tubeMap E '' Wloc = Uloc := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact ((mem_Wloc q).mp hq).2.1
    · intro y hy
      obtain ⟨hyU, hyWτ, hySnb, hyWT⟩ := (mem_Uloc y).mp hy
      have hxsrc : xfun y ∈ (chartAtIdx x₀).1.source :=
        (chartAtIdx x₀).1.map_target (hWτsub hyWτ)
      have hxi : (chartAtIdx x₀).1 (xfun y) ∈ Wτ := by
        have h3 : (chartAtIdx x₀).1 (xfun y) = τfun y := by
          show (chartAtIdx x₀).1 ((chartAtIdx x₀).1.symm (τfun y)) = τfun y
          exact (chartAtIdx x₀).1.right_inv (hWτsub hyWτ)
        rw [h3]; exact hyWτ
      refine ⟨⟨(xfun y, wfun y), hfoot y hy⟩, (mem_Wloc _).mpr ⟨?_, ?_, ?_⟩, htm y hy⟩
      · show xfun y ∈ Snb
        rw [hSnbdef]
        exact ⟨hxsrc, hxi⟩
      · show tubeMap E (⟨(xfun y, wfun y), hfoot y hy⟩ : NormalTotal E) ∈ Uloc
        rw [htm y hy]; exact hy
      · show tubeMap E (⟨(xfun y, wfun y), hfoot y hy⟩ : NormalTotal E) ∈ WT
        rw [htm y hy]; exact hyWT
  -- the inverse maps into the local chart
  have hinvLoc_mem : ∀ y ∈ Uloc, invLoc y ∈ Wloc := by
    intro y hy
    rw [hinvLoc_apply y hy]
    obtain ⟨hyU, hyWτ, hySnb, hyWT⟩ := (mem_Uloc y).mp hy
    have hxsrc : xfun y ∈ (chartAtIdx x₀).1.source :=
      (chartAtIdx x₀).1.map_target (hWτsub hyWτ)
    have hxi : (chartAtIdx x₀).1 (xfun y) ∈ Wτ := by
      have h3 : (chartAtIdx x₀).1 (xfun y) = τfun y := by
        show (chartAtIdx x₀).1 ((chartAtIdx x₀).1.symm (τfun y)) = τfun y
        exact (chartAtIdx x₀).1.right_inv (hWτsub hyWτ)
      rw [h3]; exact hyWτ
    refine (mem_Wloc _).mpr ⟨?_, ?_, ?_⟩
    · show xfun y ∈ Snb
      rw [hSnbdef]
      exact ⟨hxsrc, hxi⟩
    · show tubeMap E (⟨(xfun y, wfun y), hfoot y hy⟩ : NormalTotal E) ∈ Uloc
      rw [htm y hy]; exact hy
    · show tubeMap E (⟨(xfun y, wfun y), hfoot y hy⟩ : NormalTotal E) ∈ WT
      rw [htm y hy]; exact hyWT
  have htubeMap_invLoc : ∀ y ∈ Uloc, tubeMap E (invLoc y) = y := by
    intro y hy
    rw [hinvLoc_apply y hy]
    exact htm y hy
  -- injectivity
  have hinjOn : Set.InjOn (tubeMap E) Wloc := by
    intro q hq q' hq' heq
    obtain ⟨hqSnb, hqU, hqWT⟩ := (mem_Wloc q).mp hq
    obtain ⟨hq'Snb, hq'U, hq'WT⟩ := (mem_Wloc q').mp hq'
    have hqsrc : q.1.1 ∈ (chartAtIdx x₀).1.source := hqSnb.1
    have hq'src : q'.1.1 ∈ (chartAtIdx x₀).1.source := hq'Snb.1
    have hqτ : (chartAtIdx x₀).1 q.1.1 ∈ Wτ := hqSnb.2
    have hq'τ : (chartAtIdx x₀).1 q'.1.1 ∈ Wτ := hq'Snb.2
    have hqmem : ((chartAtIdx x₀).1 q.1.1, tubeMap E q) ∈ F.W :=
      hab₁ ⟨hWτ₁sub (by rw [hWτdef] at hqτ; exact hqτ.2), hWTsub hqWT⟩
    have hq'mem : ((chartAtIdx x₀).1 q'.1.1, tubeMap E q') ∈ F.W :=
      hab₁ ⟨hWτ₁sub (by rw [hWτdef] at hq'τ; exact hq'τ.2), hWTsub hq'WT⟩
    have hgmem : F.g ((0 : Euc 8), tubeMap E q) ∈ F.W :=
      F.g_mem _ ((mem_Uloc _).mp hqU).1
    have hfoot_q : footMap E (chartAtIdx x₀) ((chartAtIdx x₀).1 q.1.1, tubeMap E q)
        = ((0 : Euc 8), tubeMap E q) := by
      have hker : (tangentFrame E (chartAtIdx x₀) q.1.1).adjoint q.1.2 = 0 :=
        (tangentFrame_adjoint_eq_zero_iff E (chartAtIdx x₀) hqsrc q.1.2).mpr q.2
      have hchart : chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 q.1.1) = E.e q.1.1 := by
        rw [chartRep, (chartAtIdx x₀).1.left_inv hqsrc]
      refine Prod.ext ?_ rfl
      show (tauAdj E (chartAtIdx x₀) ((chartAtIdx x₀).1 q.1.1))
        (E.e q.1.1 + q.1.2 - chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 q.1.1)) = 0
      rw [hchart, add_sub_cancel_left]
      exact hker
    have hfoot_q' : footMap E (chartAtIdx x₀) ((chartAtIdx x₀).1 q'.1.1, tubeMap E q')
        = ((0 : Euc 8), tubeMap E q') := by
      have hker : (tangentFrame E (chartAtIdx x₀) q'.1.1).adjoint q'.1.2 = 0 :=
        (tangentFrame_adjoint_eq_zero_iff E (chartAtIdx x₀) hq'src q'.1.2).mpr q'.2
      have hchart : chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 q'.1.1) = E.e q'.1.1 := by
        rw [chartRep, (chartAtIdx x₀).1.left_inv hq'src]
      refine Prod.ext ?_ rfl
      show (tauAdj E (chartAtIdx x₀) ((chartAtIdx x₀).1 q'.1.1))
        (E.e q'.1.1 + q'.1.2 - chartRep E.e (chartAtIdx x₀) ((chartAtIdx x₀).1 q'.1.1)) = 0
      rw [hchart, add_sub_cancel_left]
      exact hker
    have e1 : ((chartAtIdx x₀).1 q.1.1, tubeMap E q)
        = F.g ((0 : Euc 8), tubeMap E q) :=
      F.injOn hqmem hgmem (by rw [hfoot_q, F.g_spec _ ((mem_Uloc _).mp hqU).1])
    have e2 : ((chartAtIdx x₀).1 q'.1.1, tubeMap E q')
        = F.g ((0 : Euc 8), tubeMap E q) :=
      F.injOn hq'mem hgmem (by rw [hfoot_q', F.g_spec _ ((mem_Uloc _).mp hqU).1, heq])
    have hproj : q.1.1 = q'.1.1 := by
      have h3 : (chartAtIdx x₀).1 q.1.1 = (chartAtIdx x₀).1 q'.1.1 :=
        congrArg Prod.fst (e1.trans e2.symm)
      have h4 := congrArg (chartAtIdx x₀).1.symm h3
      simpa only [(chartAtIdx x₀).1.left_inv hqsrc, (chartAtIdx x₀).1.left_inv hq'src] using h4
    have hvec : q.1.2 = q'.1.2 := by
      have h5 : tubeMap E q = tubeMap E q' := heq
      have h6 : E.e q.1.1 + q.1.2 = E.e q'.1.1 + q'.1.2 := by
        rw [← show tubeMap E q = E.e q.1.1 + q.1.2 from rfl,
          ← show tubeMap E q' = E.e q'.1.1 + q'.1.2 from rfl, h5]
      rw [hproj] at h6
      exact add_left_cancel h6
    exact Subtype.ext (Prod.ext hproj hvec)
  -- continuity of the inverse
  have hpair_cont : ContinuousOn (fun y : Euc (8 + k) => (xfun y, wfun y)) Uloc := by
    have hx : ContinuousOn xfun Uloc :=
      hxfun_contOn.mono (fun y hy => ⟨(mem_Uloc y).mp hy |>.1, (mem_Uloc y).mp hy |>.2.1⟩)
    have h1 : ContinuousOn (fun y => E.e (xfun y)) Uloc :=
      E.smooth.continuous.comp_continuousOn hx
    have hw : ContinuousOn wfun Uloc := continuousOn_id.sub h1
    exact hx.prodMk hw
  have hcont_pair : ContinuousOn (fun y => ((invLoc y).1.1, (invLoc y).1.2)) Uloc := by
    refine hpair_cont.congr ?_
    intro y hy
    show ((invLoc y).1.1, (invLoc y).1.2) = (xfun y, wfun y)
    rw [hinvLoc_apply y hy]
  have hcont_invLoc : ContinuousOn invLoc Uloc := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Uloc.domRestrict invLoc
        = fun y : Uloc => (⟨((invLoc y.1).1.1, (invLoc y.1).1.2),
            (invLoc y.1).2⟩ : NormalTotal E) := rfl
    rw [hfun]
    refine Continuous.subtype_mk ?_ (fun y => (invLoc y.1).2)
    exact hcont_pair.domRestrict
  -- smoothness of the inverse
  have hx_smooth : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) (𝓡 8) ∞ xfun Uloc := by
    have hτ_smooth : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc 8) ∞ τfun Uloc := by
      have h1 : ContDiffOn ℝ ∞ (fun y : Euc (8 + k) => F.g ((0 : Euc 8), y)) Uloc :=
        F.contDiffOn_g.comp (contDiffOn_const.prodMk contDiffOn_id)
          (fun y hy => (mem_Uloc y).mp hy |>.1)
      exact (h1.fst).contMDiffOn
    have hmem : (chartAtIdx x₀).1 ∈ IsManifold.maximalAtlas (𝓡 8) ∞ V.pt :=
      IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := ∞) (chartAtIdx x₀).2
    exact (contMDiffOn_symm_of_mem_maximalAtlas hmem).comp hτ_smooth
      (fun y hy => hWτsub ((mem_Uloc y).mp hy).2.1)
  have hw_smooth : ContMDiffOn 𝓘(ℝ, Euc (8 + k)) 𝓘(ℝ, Euc (8 + k)) ∞ wfun Uloc :=
    contMDiffOn_id.sub (E.smooth.comp_contMDiffOn hx_smooth)
  have hsmooth_pair : ContMDiffOn 𝓘(ℝ, Euc (8 + k))
      ((𝓡 8).prod 𝓘(ℝ, Euc (8 + k))) ∞ (fun y => (xfun y, wfun y)) Uloc :=
    (contMDiffOn_prod_iff (I := 𝓘(ℝ, Euc (8 + k))) (I' := 𝓡 8) (J' := 𝓘(ℝ, Euc (8 + k)))
      (s := Uloc) (f := fun y : Euc (8 + k) => (xfun y, wfun y))).mpr ⟨hx_smooth, hw_smooth⟩
  have hsmooth_invLoc : ContMDiffOn 𝓘(ℝ, Euc (8 + k))
      ((𝓡 8).prod 𝓘(ℝ, Euc (8 + k))) ∞
      (fun y => ((invLoc y).1.1, (invLoc y).1.2)) Uloc := by
    refine hsmooth_pair.congr ?_
    intro y hy
    show ((invLoc y).1.1, (invLoc y).1.2) = (xfun y, wfun y)
    rw [hinvLoc_apply y hy]
  -- the quantitative clause
  have hnbd : ∀ (x : V.pt), x ∈ St → ∀ (w : Euc (8 + k)) (hw : w ∈ normalSpace E x),
      ‖w‖ < η → (⟨(x, w), hw⟩ : NormalTotal E) ∈ Wloc := by
    intro x hx w hw hwlt
    obtain ⟨hxS₂, hxSnb⟩ := hx
    have hxB : (x, w) ∈ S₁ ×ˢ B :=
      ⟨hS₂sub hxS₂, hηsub (by rw [Metric.mem_ball, dist_eq_norm]; simpa using hwlt)⟩
    obtain ⟨h1, h2⟩ := hSB hxB
    have h2' : E.e x + w ∈ ((U₀ ∩ τfun ⁻¹' Wτ) ∩ xfun ⁻¹' Snb) ∩ WT := by
      have h3 := h2
      rw [hVcdef] at h3
      exact h3
    obtain ⟨⟨⟨hyU, hyT⟩, hyS⟩, hyWT⟩ := h2'
    refine (mem_Wloc _).mpr ⟨hxSnb, ?_, ?_⟩
    · show E.e x + w ∈ Vc
      exact h2
    · show E.e x + w ∈ WT
      exact hyWT
  exact ⟨Wloc, hWloc_open, hmem, hinjOn, Uloc, hUloc_open, himage, invLoc, hinvLoc_mem,
    htubeMap_invLoc, hcont_invLoc, hsmooth_invLoc, St, hStopen, hx₀St, η, hηpos, hnbd⟩

/-! ## What is proved here, and what is not

The *structure* `LocalTube` above is the interface of the local tube chart, and the API lemmas
`image_inter_eq` / `isOpen_image_inter` record how the tube map and its inverse interact with
subsets of the total space.

The *existence* theorem `Nonempty (LocalTube E x₀)` is **not** proved in this file.  Its proof is
the assembly of the inverse function theorem for the foot map (`Work.Tubular.nonempty_footData`,
proved in `Foot.lean`) with the shrinking of the neighbourhoods needed for the quantitative clause;
the analytic content is in `Foot.lean`, and what is missing here is bookkeeping about the
subtype `NormalTotal E` (destructuring `Set`-memberships, coercion `rfl`s) whose details are
irrelevant to the mathematics.  See `README.md` §5 for the precise remaining statement.
-/

end

end Work.Tubular
