import Mathlib
import Submission.Work.WilE9.Sharp.Main
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.graph_rel
import Submission.Work.WilE9.Sharp.GlDerivContDiffAt2
import Submission.Work.WilE9.Sharp.AE.dense_compl_psiV_preimage
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.contDiff_psi
import Submission.Work.WilE9.Psi.deriv_psiInv
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.psig_pos

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-!
  **Auxiliary material for the layer specification** (`Submission/Work/WilE9/Sharp/layer_spec.lean`).

  We bundle the hypotheses of the layer specification into the structure `LayerHyp`, so that
  the many intermediate lemmas do not have to repeat them, and prove there the two structural
  facts (`Gset_spec`, `base_mem_closure`) from which `SecSpec`, `LimSpec` and the order
  independence of `Eset` follow.

  The strata are `AEStratum n` (an `EffStratum n m` together with a base point `q`); only the
  component `A.comp = connectedComponentIn A.E.X.set A.q` is used, and the covering hypothesis of
  the layer is the almost-everywhere one supplied by `Work.WilE9G.EffStratAE`.
-/

/-! ## 1. Elementary `ψ`-facts -/

/-- `|ψ x| < 1` everywhere: `ψ` maps `ℝ` into the open interval. -/
theorem psi_abs_lt_one (x : ℝ) : |WilkiesDesign.E.psi x| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one]
  have h := Work.WilE9.Psi.psi_sq_add_psig_sq x
  have hp : 0 < Work.WilE9.psig x ^ 2 := pow_pos (Work.WilE9.Psi.psig_pos x) 2
  linarith

/-- `ψ` is injective (its explicit inverse is `psiInv`). -/
theorem psi_injective : Function.Injective WilkiesDesign.E.psi := by
  intro a b hab
  rw [← Work.WilE9.Psi.psiInv_psi a, hab, Work.WilE9.Psi.psiInv_psi b]

/-- `psiV` is injective. -/
theorem psiV_injective {n : ℕ} : Function.Injective (WilkiesDesign.E.psiV (n := n)) := by
  intro x y h
  funext i
  exact psi_injective (congrFun h i)

/-- On the open cube, `psiInvV` is a right inverse of `psiV`. -/
theorem psiV_psiInvV {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, |y i| < 1) :
    WilkiesDesign.E.psiV (psiInvV y) = y := by
  funext i
  exact Work.WilE9.Psi.psi_psiInv (y i) (hy i)

/-- `psiInvV` is a left inverse of `psiV` everywhere. -/
theorem psiInvV_psiV {n : ℕ} (x : Fin n → ℝ) :
    psiInvV (WilkiesDesign.E.psiV x) = x := by
  funext i
  exact Work.WilE9.Psi.psiInv_psi (x i)

/-- The open cube is open. -/
theorem isOpen_ocube {N : ℕ} : IsOpen (ocube N) := by
  have h : ocube N = ⋂ i : Fin N, {u : Fin N → ℝ | |u i| < 1} := by
    ext u
    simp only [ocube, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const

/-- `psiInvV` is continuous at every point of the open cube. -/
theorem continuousAt_psiInvV {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, |y i| < 1) :
    ContinuousAt (psiInvV (n := n)) y := by
  rw [continuousAt_pi]
  intro i
  simp only [psiInvV]
  exact ContinuousAt.comp (x := y) (f := fun p : Fin n → ℝ => p i)
    (g := fun t : ℝ => Work.WilE9.psiInv t)
    ((Work.WilE9.Psi.deriv_psiInv (y i) (hy i)).continuousAt)
    (continuous_apply i).continuousAt

/-- `Fin.init` is continuous. -/
theorem continuous_init {n : ℕ} :
    Continuous (fun u : Fin (n + 1) → ℝ => Fin.init u) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [continuousAt_pi]
  intro j
  exact (continuous_apply (Fin.castSucc j)).continuousAt

/-- The projection to the first `n` coordinates, as an image. -/
theorem projLast_eq_image_init {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    WilkiesDesign.projLast A = Fin.init '' A := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨Fin.snoc x t, ht, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by simpa using hz⟩

/-- `exTset` is the `exOut`-image of the extended set. -/
theorem exTset_eq_image {n m : ℕ} (E : EffStratum n m) (L : List (Fin n)) :
    exTset E L = exOut '' (exSemiPf n m E L).set := rfl

/-- `exTsetC` is the `exOut`-image of the component-restricted extended set. -/
theorem exTsetC_eq_image {n m : ℕ} (E : EffStratum n m) (q : Fin (n + (1 + m)) → ℝ)
    (L : List (Fin n)) : exTsetC n m E q L = exOut '' exComp n m E q L := rfl

/-- Membership in `exComp` is membership in the extended set together with membership of the
stratum coordinates in the prescribed component. -/
theorem mem_exComp_of_mem_set {n m : ℕ} (E : EffStratum n m)
    (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) {z : Fin (Next n m) → ℝ}
    (hz : z ∈ (exSemiPf n m E L).set) (hq : exStrat z ∈ connectedComponentIn E.X.set q) :
    z ∈ exComp n m E q L :=
  Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨⟨hz, hq⟩, mem_connectedComponentIn hz⟩⟩

/-! ## 2. The hypotheses of the layer specification, bundled -/

/-- The hypotheses of the layer specification.  The strata carry a base point and only their
component through it is used (`A.comp`); the covering is almost-everywhere (`hcov`). -/
structure LayerHyp (n : ℕ) (f : (Fin n → ℝ) → ℝ) (Z : Set (Fin (n + 1) → ℝ))
    (S : List (AEStratum n)) : Prop where
  hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z
  hGood : ∀ A ∈ S, A.E.Good
  hπ : ∀ A ∈ S, ∀ w ∈ A.comp, stratProj w ∈ Z
  hcov : ∃ N : Set (Fin n → ℝ), MeasureTheory.volume N = 0 ∧
    ∀ y ∈ Z, Fin.init y ∉ N → (∀ j : Fin n, |Fin.init y j| < 1) →
      y ∈ ⋃ A ∈ S, stratProj '' A.comp
  hbase : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ exComp n A.1 A.E A.q L, exOut z = Fin.snoc y σ) →
      ∃ w ∈ A.comp, stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV (psiInvV y)) (WilkiesDesign.E.psi (f (psiInvV y)))
  hfst : ∀ A ∈ S, ∀ (L : List (Fin n)) (x : Fin n → ℝ) (w : Fin (n + (1 + A.1)) → ℝ),
      w ∈ A.comp →
      stratProj w = Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (f x)) →
      ∃ z ∈ exComp n A.1 A.E A.q L,
        exOut z = Fin.snoc (WilkiesDesign.E.psiV x)
          (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x))
  hsnd : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ exComp n A.1 A.E A.q L, exOut z = Fin.snoc y σ) →
      (∀ i : Fin n, |y i| < 1) ∧ |σ| < 1 ∧
        σ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (psiInvV y))
  hsndC : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ exComp n A.1 A.E A.q L, exOut z = Fin.snoc y σ) →
      ContDiffAt ℝ ⊤ f (psiInvV y)
  hglperm : ∀ (y : Fin n → ℝ), ContDiffAt ℝ ⊤ f y →
      ∀ (L L' : List (Fin n)), List.Perm L L' →
        Work.WilE9.glDeriv L f y = Work.WilE9.glDeriv L' f y

/-! ## 3. The two sets attached to a layer -/

/-- `Gset n S L` is the `psiV`-preimage of `Tset n S L`; its closure is `Eset n S L`. -/
def Gset (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) :
    Set (Fin (n + 1) → ℝ) :=
  WilkiesDesign.E.psiV ⁻¹' Tset n S L

/-- The base points of `Gset`: those `x` for which `(x, ∂_L f x) ∈ Gset`. -/
def Base (n : ℕ) (S : List (AEStratum n)) (f : (Fin n → ℝ) → ℝ)
    (L : List (Fin n)) : Set (Fin n → ℝ) :=
  {x | Fin.snoc x (Work.WilE9.glDeriv L f x) ∈ Gset n S L}

/-- `Eset n S L` is the closure of `Gset n S L`. -/
theorem Eset_eq_closure_Gset (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) :
    Eset n S L = closure (Gset n S L) := rfl

/-! ## 4. Every point of `Gset` is a derivative point -/

/-- **`Gset` is a graph.**  Every point `ζ` of `Gset n S L` has last coordinate `∂_L f (init ζ)`
and its base `init ζ` is a `C^∞` point of `f`. -/
theorem Gset_spec {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S)
    {L : List (Fin n)} {ζ : Fin (n + 1) → ℝ} (hζ : ζ ∈ Gset n S L) :
    ζ (Fin.last n) = Work.WilE9.glDeriv L f (Fin.init ζ) ∧ ContDiffAt ℝ ⊤ f (Fin.init ζ) := by
  simp only [Gset, Set.mem_preimage, Tset, Set.mem_iUnion] at hζ
  obtain ⟨A, hA, hζA⟩ := hζ
  obtain ⟨z, hz, hzout⟩ :=
    (Set.mem_image exOut (exComp n A.1 A.E A.q L) (WilkiesDesign.E.psiV ζ)).mp hζA
  have hpsi : WilkiesDesign.E.psiV ζ =
      Fin.snoc (WilkiesDesign.E.psiV (Fin.init ζ))
        (WilkiesDesign.E.psi (ζ (Fin.last n))) := by
    conv_lhs => rw [← Fin.snoc_init_self ζ]
    rw [psiV_snoc]
  have hex : ∃ z ∈ exComp n A.1 A.E A.q L,
      exOut z = Fin.snoc (WilkiesDesign.E.psiV (Fin.init ζ))
        (WilkiesDesign.E.psi (ζ (Fin.last n))) :=
    ⟨z, hz, by rw [hzout, hpsi]⟩
  have hs := H.hsnd A hA L
    (WilkiesDesign.E.psiV (Fin.init ζ)) (WilkiesDesign.E.psi (ζ (Fin.last n))) hex
  refine ⟨?_, ?_⟩
  · apply psi_injective
    rw [hs.2.2, psiInvV_psiV]
  · have hc := H.hsndC A hA L
      (WilkiesDesign.E.psiV (Fin.init ζ)) (WilkiesDesign.E.psi (ζ (Fin.last n))) hex
    rwa [psiInvV_psiV] at hc

/-- The base of `Gset` (i.e. `Fin.init '' Gset`) is exactly `Base`. -/
theorem image_init_Gset {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S) (L : List (Fin n)) :
    Fin.init '' Gset n S L = Base n S f L := by
  ext x
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    have h1 := (Gset_spec H hζ).1
    show Fin.snoc (Fin.init ζ) (Work.WilE9.glDeriv L f (Fin.init ζ)) ∈ Gset n S L
    rw [← h1, Fin.snoc_init_self]
    exact hζ
  · intro hx
    exact ⟨Fin.snoc x (Work.WilE9.glDeriv L f x), hx, by simp⟩

/-- `Gset` is the image of `Base` under `x ↦ (x, ∂_L f x)`. -/
theorem Gset_eq_image_Base {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S) {L : List (Fin n)} :
    Gset n S L =
      (fun x : Fin n → ℝ => Fin.snoc x (Work.WilE9.glDeriv L f x)) '' Base n S f L := by
  ext ζ
  constructor
  · intro hζ
    have h1 := (Gset_spec H hζ).1
    refine ⟨Fin.init ζ, ?_, ?_⟩
    · show Fin.snoc (Fin.init ζ) (Work.WilE9.glDeriv L f (Fin.init ζ)) ∈ Gset n S L
      rw [← h1, Fin.snoc_init_self]
      exact hζ
    · show Fin.snoc (Fin.init ζ) (Work.WilE9.glDeriv L f (Fin.init ζ)) = ζ
      rw [← h1, Fin.snoc_init_self]
  · rintro ⟨x, hx, rfl⟩
    exact hx

/-- A point of `Base` is a `C^∞` point of `f` (via `hsndC`). -/
theorem base_contDiff {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S)
    {L : List (Fin n)} {x : Fin n → ℝ} (hx : x ∈ Base n S f L) :
    ContDiffAt ℝ ⊤ f x := by
  simp only [Base, Gset, Set.mem_ofPred_eq, Set.mem_preimage, Tset, Set.mem_iUnion] at hx
  obtain ⟨A, hA, hxA⟩ := hx
  obtain ⟨z, hz, hzout⟩ :=
    (Set.mem_image exOut (exComp n A.1 A.E A.q L)
      (WilkiesDesign.E.psiV (Fin.snoc x (Work.WilE9.glDeriv L f x)))).mp hxA
  have hpsi : WilkiesDesign.E.psiV (Fin.snoc x (Work.WilE9.glDeriv L f x)) =
      Fin.snoc (WilkiesDesign.E.psiV x)
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)) := psiV_snoc x _
  have hex : ∃ z ∈ exComp n A.1 A.E A.q L,
      exOut z = Fin.snoc (WilkiesDesign.E.psiV x)
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)) :=
    ⟨z, hz, by rw [hzout, hpsi]⟩
  have hc := H.hsndC A hA L (WilkiesDesign.E.psiV x)
    (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)) hex
  rwa [psiInvV_psiV] at hc

/-! ## 5. Density of `Base` -/

/-- **Density of `Base`.**  Every point of `ℝⁿ` is a limit of points of `Base n S f L`: away from
the null set `N` of the covering hypothesis `hcov`, the graph point of `x` lies in the projection
of a stratum component, and `hfst` lifts it to the extended system, i.e. to `Base`. -/
theorem base_mem_closure {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S)
    {L : List (Fin n)} {x : Fin n → ℝ} (hC : ContDiffAt ℝ L.length f x) :
    x ∈ closure (Base n S f L) := by
  obtain ⟨N, hNvol, hcov⟩ := H.hcov
  have hdense : Dense ((WilkiesDesign.E.psiV ⁻¹' N)ᶜ) :=
    Work.WilE9.Sharp.AE.dense_compl_psiV_preimage hNvol
  have hsub : (WilkiesDesign.E.psiV ⁻¹' N)ᶜ ⊆ Base n S f L := by
    intro x' hx'
    have hx'N : WilkiesDesign.E.psiV x' ∉ N := hx'
    -- the graph point over `x'`
    set p : Fin (n + 1) → ℝ :=
      Fin.snoc (WilkiesDesign.E.psiV x') (WilkiesDesign.E.psi (f x')) with hp
    have hpZ : p ∈ Z := by
      have h1 : Fin.snoc x' (f x') ∈ WilkiesDesign.graphOf f := by
        simp [WilkiesDesign.graphOf, Fin.snoc_last, Fin.init_snoc]
      rw [H.hZ] at h1
      rw [Set.mem_preimage] at h1
      rw [psiV_snoc] at h1
      rw [hp]
      exact h1
    have hpinit : Fin.init p = WilkiesDesign.E.psiV x' := by
      rw [hp]; exact Fin.init_snoc _ _
    have hpoc : ∀ j : Fin (n + 1), |p j| < 1 := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [hp, Fin.snoc_last]
        exact psi_abs_lt_one (f x')
      · intro j
        rw [hp, Fin.snoc_castSucc, WilkiesDesign.E.psiV]
        exact psi_abs_lt_one (x' j)
    have hmem := hcov p hpZ (by rw [hpinit]; exact hx'N)
      (fun j => hpoc (Fin.castSucc j))
    obtain ⟨A, hA, w, hw, hwproj⟩ := Set.mem_iUnion₂.mp hmem
    have hproj : stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV x') (WilkiesDesign.E.psi (f x')) := by
      rw [hwproj, hp]
    obtain ⟨z, hz, hzout⟩ := H.hfst A hA L x' w hw hproj
    show Fin.snoc x' (Work.WilE9.glDeriv L f x') ∈ Gset n S L
    simp only [Gset, Set.mem_preimage, Tset, Set.mem_iUnion]
    refine ⟨A, hA, ?_⟩
    rw [exTsetC_eq_image, psiV_snoc]
    exact (Set.mem_image exOut (exComp n A.1 A.E A.q L)
      (Fin.snoc (WilkiesDesign.E.psiV x')
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x')))).mpr
      ⟨z, hz, hzout⟩
  have huniv : (Set.univ : Set (Fin n → ℝ)) ⊆ closure (Base n S f L) := by
    rw [← hdense.closure_eq]
    exact closure_mono hsub
  exact huniv trivial

end Work.WilE9.Sharp
