import Mathlib
import Submission.Work.Horn.spreadChain_spec
import Submission.Work.Horn.spread_chain_covering_off_critval
import Submission.Work.Horn.pushdown_covering
import Submission.Work.Horn.germF0_base

set_option linter.ambiguousOpen false
set_option linter.style.haveILetI false

namespace Work.Horn

open Set Filter Topology
open scoped Topology

/-! ## Helper 1: a covering map with path-connected total space over a simply connected base

The total space `E` of a covering `p : E → X` over a simply connected, locally path connected base
`X` is a *single* sheet: `p` is bijective and, being an open continuous bijection, a homeomorphism,
so preimages of compacta are compact. -/

theorem bijective_and_isCompact_preimage_of_isCoveringMap {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] {p : E → X} (hp : IsCoveringMap p) [PathConnectedSpace E]
    [SimplyConnectedSpace X] :
    Function.Bijective p ∧ ∀ L : Set X, IsCompact L → IsCompact (p ⁻¹' L) := by
  have hsurj : Function.Surjective p := by
    intro y
    obtain ⟨e₀⟩ : Nonempty E := inferInstance
    let γ : Path (p e₀) y := PathConnectedSpace.somePath (p e₀) y
    have hγ : (γ : C(unitInterval, X)) 0 = p e₀ := γ.source
    obtain ⟨Γ, hΓ1, _hΓ0⟩ := hp.exists_path_lifts (γ : C(unitInterval, X)) e₀ hγ
    refine ⟨Γ 1, ?_⟩
    have h1 : p (Γ 1) = (γ : C(unitInterval, X)) 1 := congr_fun hΓ1 1
    rw [h1]
    exact γ.target
  have hinj : Function.Injective p := by
    intro e₁ e₂ he
    let γ : Path e₁ e₂ := PathConnectedSpace.somePath e₁ e₂
    let loop : Path (p e₁) (p e₁) :=
      { toFun := fun t => p (γ t)
        continuous_toFun := hp.continuous.comp γ.continuous
        source' := by rw [γ.source]
        target' := by rw [γ.target, he] }
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic loop (Path.refl (p e₁))
    have key := hp.liftPath_apply_one_eq_of_homotopicRel (γ₀ := (loop : C(unitInterval, X)))
      (γ₁ := ((Path.refl (p e₁) : Path (p e₁) (p e₁)) : C(unitInterval, X))) ⟨H⟩ e₁
      (by simp [loop]) (by simp)
    have hlift : ((γ : C(unitInterval, E)) : unitInterval → E) =
        (hp.liftPath (loop : C(unitInterval, X)) e₁ (by simp [loop]) : unitInterval → E) := by
      rw [hp.eq_liftPath_iff]
      exact ⟨γ.continuous, by funext t; rfl, γ.source⟩
    have hconst : (fun _ : unitInterval => e₁) =
        (hp.liftPath ((Path.refl (p e₁) : Path (p e₁) (p e₁)) : C(unitInterval, X)) e₁
          (by simp) : unitInterval → E) := by
      rw [hp.eq_liftPath_iff]
      exact ⟨continuous_const, by funext t; rfl, rfl⟩
    have h1 : ((γ : C(unitInterval, E)) : unitInterval → E) 1 = e₁ := by
      rw [hlift, key, ← hconst]
    have h2 : ((γ : C(unitInterval, E)) : unitInterval → E) 1 = e₂ := γ.target
    rw [h2] at h1
    exact h1.symm
  refine ⟨⟨hinj, hsurj⟩, ?_⟩
  intro L hL
  set q := Function.invFun p with _hqdef
  have hleft : Function.LeftInverse q p := Function.leftInverse_invFun hinj
  have hright : Function.RightInverse q p := Function.rightInverse_invFun hsurj
  have hcont : Continuous q := by
    rw [continuous_def]
    intro U hU
    have hpre : q ⁻¹' U = p '' U := by
      ext x
      constructor
      · intro hx
        exact ⟨q x, hx, hright x⟩
      · rintro ⟨y, hy, rfl⟩
        show q (p y) ∈ U
        rw [hleft y]
        exact hy
    rw [hpre]
    exact hp.isOpenMap U hU
  have himg : q '' L = p ⁻¹' L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show p (q x) ∈ L
      rw [hright x]
      exact hx
    · intro hy
      exact ⟨p y, hy, hleft y⟩
  rw [← himg]
  exact hL.image hcont

/-! ## Helper 2: the level map of a covering of a plane domain

If `G : ℂ → ℂ` maps an open connected `C` into `V`, and the restriction `↥C → ℂ`, `z ↦ G z`, is a
covering map over the simply connected `V`, then `G` maps `C` bijectively onto `V` and the preimages
of compact subsets of `V` (intersected with `C`) are compact.  This is the general fact behind
Shishikura's Lemma 5.4: a covering of a simply connected base is trivial, so the *connected* level
`C` is a single sheet. -/

theorem bijOn_and_isCompact_of_isCoveringMapOn {G : ℂ → ℂ} {C V : Set ℂ}
    (hCopen : IsOpen C) (hCconn : IsConnected C) (hVC : G '' C ⊆ V)
    (hVsc : SimplyConnectedSpace V) (hcov : IsCoveringMapOn (fun z : ↥C => G z) V) :
    Set.BijOn G C V ∧
      ∀ L : Set ℂ, L ⊆ V → IsCompact L → IsCompact (C ∩ G ⁻¹' L) := by
  haveI : ConnectedSpace ↥C := isConnected_iff_connectedSpace.mp hCconn
  haveI : LocallyPathConnectedSpace ↥C := hCopen.locallyPathConnectedSpace
  haveI : PathConnectedSpace ↥C := PathConnectedSpace.of_locallyPathConnectedSpace
  haveI : SimplyConnectedSpace ↥V := hVsc
  set f : ↥C → ℂ := fun z => G z with hf
  have hpre : f ⁻¹' V = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun z => hVC ⟨z, z.2, rfl⟩
  -- the domain of the restricted covering is all of `↥C`, up to the canonical homeomorphism
  let e : ↥C ≃ₜ ↥(f ⁻¹' V) :=
    (Homeomorph.Set.univ ↥C).symm.trans (Homeomorph.setCongr hpre.symm)
  haveI : PathConnectedSpace ↥(f ⁻¹' V) := e.pathConnectedSpace
  have hcovsub : IsCoveringMap (V.restrictPreimage f) :=
    IsCoveringMapOn.isCoveringMap_restrictPreimage V hcov
  set q : ↥C → ↥V := fun z => ⟨G z, hVC ⟨z, z.2, rfl⟩⟩ with hq
  have hcomp : V.restrictPreimage f ∘ e = q := by
    funext z
    exact Subtype.ext rfl
  have hqcov : IsCoveringMap q := by
    rw [← hcomp]
    exact hcovsub.comp_homeomorph e
  obtain ⟨hbijq, hcompq⟩ := bijective_and_isCompact_preimage_of_isCoveringMap hqcov
  have hbij : Set.BijOn G C V := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact hVC ⟨z, hz, rfl⟩
    · intro z₁ h₁ z₂ h₂ he
      have : (⟨z₁, h₁⟩ : ↥C) = ⟨z₂, h₂⟩ := hbijq.1 (Subtype.ext he)
      exact congrArg Subtype.val this
    · intro y hy
      obtain ⟨z, hz⟩ := hbijq.2 ⟨y, hy⟩
      exact ⟨z.1, z.2, congrArg Subtype.val hz⟩
  refine ⟨hbij, ?_⟩
  intro L hLV hLc
  have hL' : IsCompact ((Subtype.val : ↥V → ℂ) ⁻¹' L) := by
    rw [_root_.Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe]
    rw [Set.inter_eq_right.mpr hLV]
    exact hLc
  have hK : IsCompact (q ⁻¹' ((Subtype.val : ↥V → ℂ) ⁻¹' L)) := hcompq _ hL'
  have himg : (Subtype.val '' (q ⁻¹' ((Subtype.val : ↥V → ℂ) ⁻¹' L))) = C ∩ G ⁻¹' L := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
  rw [← himg]
  exact hK.image continuous_subtype_val

/-! ## Helper 3: the levels of the spread chain against the definition

`spreadChain G D V (n+1)` is, by definition, the union of the connected components of the open set
`D ∩ G ⁻¹' (spreadChain G D V n i)` that meet `spreadChain G D V n i`; hence every level of the
chain is contained in the preimage of the previous one (no additive `{0}`), and in particular
`G` maps level `n + 1` into level `n` outright. -/

theorem spreadChain_succ_subset_preimage {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (n : ℕ) (i : Fin q) :
    spreadChain G D V (n + 1) i ⊆ D ∩ G ⁻¹' (spreadChain G D V n i) := by
  intro z hz
  have hz' : z ∈ spreadStep G D (spreadChain G D V n) i := hz
  rw [spreadStep] at hz'
  obtain ⟨x, _hx, hzc⟩ := Set.mem_iUnion₂.mp hz'
  exact connectedComponentIn_subset _ _ hzc

theorem spreadChain_image_succ_subset {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (n : ℕ) (i : Fin q) :
    G '' spreadChain G D V (n + 1) i ⊆ spreadChain G D V n i := by
  rintro y ⟨z, hz, rfl⟩
  exact (spreadChain_succ_subset_preimage n i hz).2

/-! ## The target: Shishikura's Lemma 5.4 for the levels of the spread chain

The level `W (n+1) i` of the spread chain is a connected component of `D ∩ g⁻¹(W n i)`, so it maps
into `W n i`; the level map `g : W (n+1) i → W n i` is a covering map away from `{0, π (Φ₀ c)}`
(`Work.Horn.spread_chain_covering_off_critval`).  Away from the critical value the base `W n i` is
simply connected, and `0` is never in a level, so the covering is a covering of a simply connected
base by a connected total space: it is a homeomorphism (`Work.Horn.bijOn_and_isCompact_of_isCoveringMapOn`).
-/

theorem level_bijOn_of_ne_critval {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (c : ℂ) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {q : ℕ} {V : Fin q → Set ℂ} (hVopen : ∀ (i : Fin q), IsOpen (V i))
    (hVconn : ∀ (i : Fin q), IsConnected (V i))
    (hVsub : ∀ (i : Fin q), V i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))
    (hVmap : ∀ (i : Fin q), ∀ z ∈ V i, MandelDim.pushdown d.E z ∈ V i ∪ {0})
    (hVne : ∀ (i : Fin q), (0 : ℂ) ∉ V i)
    (hVdisj : ∀ (i j : Fin q), i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ (i : Fin q), (0 : ℂ) ∈ closure (V i))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      ∃ n : ℕ, (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      (∃ n : ℕ, (∀ k < n, (MandelDim.pushdown d.E)^[k] z ∈
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
        (MandelDim.pushdown d.E)^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :
    let W : ℕ → Fin q → Set ℂ := Work.Horn.spreadChain (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) V
    ∀ (n : ℕ) (i : Fin q), MandelDim.piExp (d.Φ c) ∉ W n i → SimplyConnectedSpace (W n i) →
      Set.BijOn (MandelDim.pushdown d.E) (W (n + 1) i) (W n i) ∧
      (∀ L : Set ℂ, L ⊆ W n i → IsCompact L →
        IsCompact (W (n + 1) i ∩ (MandelDim.pushdown d.E) ⁻¹' L)) := by
  dsimp only
  intro n i hv hsc
  obtain ⟨hBuO, hBlO, _hBuT, _hBlT, hup₀, hlo₀, _hDE⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  set G : ℂ → ℂ := MandelDim.pushdown d.E with hGdef
  set D : Set ℂ := insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) with hDdef
  set v : ℂ := MandelDim.piExp (d.Φ c) with hvdef
  have hDopen : IsOpen D := isOpen_insert_piExp hBuO hBlO hup hlo
  have hGdiff : DifferentiableOn ℂ G D := pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D :=
    zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  have hG0 : G 0 = 0 := by simp [G, MandelDim.pushdown]
  have hz0 : ∀ z : ℂ, G z = 0 → z = 0 := by
    intro z hz
    by_contra hzne
    have h1 : G z = MandelDim.piExp (d.E (Complex.log z / (2 * Real.pi * Complex.I))) := by
      simp [G, MandelDim.pushdown, hzne]
    rw [h1] at hz
    exact MandelDim.piExp_ne_zero _ hz
  -- ### the structural facts about the spread chain
  obtain ⟨hWopen, hWconn, hWsub, hW0, hWmono, hWmap, hWsat, _hWmax, _hWdisj⟩ :=
    spreadChain_props (G := G) (D := D) (V := V) hDopen hGdiff hVopen hVconn hVsub hVmap hVne
      hVdisj hVcl h0out hVreach
  -- ### `0` is never in a level, and each level is mapped into itself
  have h0W : ∀ k : ℕ, (0 : ℂ) ∉ Work.Horn.spreadChain G D V k i := by
    intro k
    induction k with
    | zero => rw [hW0 i]; exact hVne i
    | succ k ih =>
      intro h0
      exact ih (spreadChain_image_succ_subset (G := G) (D := D) (V := V) k i ⟨0, h0, hG0⟩)
  have hGW : ∀ k : ℕ, G '' Work.Horn.spreadChain G D V k i ⊆ Work.Horn.spreadChain G D V k i := by
    intro k
    cases k with
    | zero =>
      rintro y ⟨z, hz, rfl⟩
      have hzV : z ∈ V i := by rwa [hW0 i] at hz
      rcases hVmap i z hzV with h | h
      · exact h
      · have hz_eq : z = 0 := hz0 z (by simpa using h)
        exact absurd (hz_eq ▸ hzV) (hVne i)
    | succ k =>
      exact fun y hy =>
        hWmono k i (spreadChain_image_succ_subset (G := G) (D := D) (V := V) k i hy)
  -- ### the covering of the horn domain and the covering of the level map
  have hcovE := cov_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi Work.HornVarphi.horn_varphi
    Work.Horn.hornSC f₀ D₀ B c d hsetup
  have hBuOf : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBlOf : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hcov : IsCoveringMapOn (fun z : ↥D => G z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} := by
    have hDeq : D = insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
      rw [hDdef, hBuOf, hBlOf]
    rw [hDeq]
    exact pushdown_covering Work.HornTopo.horn_topo d hsetup hcovE
  have hcrit : ∀ z ∈ D, deriv G z = 0 → G z = v :=
    pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo
  have hlev : IsCoveringMapOn (fun z : ↥(Work.Horn.spreadChain G D V (n + 1) i) => G z)
      (Work.Horn.spreadChain G D V n i \ {0, v}) :=
    spread_chain_covering_off_critval hDopen hGdiff hcov hcrit hWopen hWsub hWmono hWmap hWsat
      (n := n) (i := i)
  have hlev' : IsCoveringMapOn (fun z : ↥(Work.Horn.spreadChain G D V (n + 1) i) => G z)
      (Work.Horn.spreadChain G D V n i) :=
    hlev.mono (fun z hz => by
      rw [Set.mem_sdiff]
      refine ⟨hz, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h0W n (h ▸ hz), fun h => hv (h ▸ hz)⟩)
  -- ### a connected covering of the simply connected level `W n i` is a homeomorphism
  exact bijOn_and_isCompact_of_isCoveringMapOn (G := G)
    (C := Work.Horn.spreadChain G D V (n + 1) i) (V := Work.Horn.spreadChain G D V n i)
    (hWopen (n + 1) i) (hWconn (n + 1) i)
    (spreadChain_image_succ_subset (G := G) (D := D) (V := V) n i) hsc hlev'

end Work.Horn
