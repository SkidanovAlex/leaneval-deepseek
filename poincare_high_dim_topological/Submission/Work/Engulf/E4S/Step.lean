import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.shellPrism
import Submission.Work.Engulf.E4alt.badset
import Submission.Work.Engulf.E4alt.ShellPrep
import Submission.Work.Engulf.E4Aux.prism_push_step
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.PL.Subdiv.DomDim
import Submission.Work.PL.Generic.Basic
import Submission.Work.Engulf.E4Aux.ordGeom
import Submission.Work.Engulf.E4S.Basic
import Submission.Work.Engulf.E4S.PushShellG

/-!
# `Work.Engulf.E4S.Step` — one step of the `E4alt` shelling loop with a *moving* map

Newman's (13.2)–(13.4) as the invariant `Work.Engulf.Alt.AltInnerG` (`NOTES_LEAD_poincare_E4c.md`
§A.5): the `i`-th step of the shelling loop carries a map `g` frozen on `L ∪ coreSet` and
`i·β`-close to `g₁`, and produces `g′`, `h′` with `g′` frozen on `L ∪ coreSet`, `(i+1)·β`-close to
`g₁`, and the enlarged region engulfed.

The geometry of a single member of the shelling order is the one already used by
`Work.Engulf.E4alt.step` (`shell_wit`, `hA17`, `prism_of_shell`, `badset`, `Jq`, `hsmall`), reused
verbatim.  What is new (and is why the old fixed-map `AltInner` had to be replaced) is:

* `simp (ord[i]) ⊆ coreSet` (`shell_core`), so the input map `g` agrees with `g₁ = ψ ∘ A_τ` on the
  member; this gives `hAeq` and `hbase` for `g` and for `g′`;
* the **transfer lemma** `Work.Engulf.E4S.eq_g₁_of_mem_closedCube`: a point of `K ∪ Q` whose
  `g′`-image lands in `ψ (closedCube 9/16)` is `μ`-close to `g₁`, hence frozen, hence
  `g′ y = g₁ y`.  This transports the bad-set bound `hAs₁` (proved for `g₁`) to `g′`;
* the dimension bound `Work.Engulf.E4S.card_le_of_simp_subset_K_union_Q` for `G = K ∪ Q`.

The piece loop `E4c` enters as the hypothesis `hpieces` (instantiated at
`Work.Engulf.E4Aux.piecesEngulfG` in `Work.Engulf.E4S.StepG`), so that this file is independent of
the piece loop's proof.
-/

open Set Metric PL
open Work.Engulf.Alt

namespace Work.Engulf.E4S

/-- **`E4e` with a moving map** (`NOTES_LEAD_poincare_E4c.md` §A.5): one step of the shelling loop
preserves `AltInnerG`.

`hpieces` is the piece loop `E4c` (`Work.Engulf.E4Aux.piecesEngulfG`) in the exact form in which it
is consumed here: given a `Γ₁`-subcomplex `G` all of whose faces have `≤ p+1` vertices, a map `g̃`
continuous on `Γ₁.space` and frozen on `L ∪ coreSet`, the invariant `X ∪ g̃ '' G ⊆ h̃ '' V` and the
prism data of the member, it returns `g′, h′` with `g′` frozen on `L ∪ coreSet`, `dist (g′, g̃) < β₀`
and the region over `J` engulfed. -/
theorem stepG_of_pieces {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (T : Work.Engulf.ToolsAllM M n) (hB : Work.Engulf.BM M n p q)
    (hq : q + 1 ≤ p + 1) (A : Work.Engulf.Amb n p M V)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (SCh : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ)) (hε : 0 < ε)
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) (hcS : Work.Engulf.Alt.CarrierS ND)
    {μ : ℝ} (hmarg : ∀ x ∈ ND.Γ₁.space, x ∉ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ →
      ∀ z : M, dist z (ND.g₁ x) < μ → z ∉ ψ.toFun '' PL.closedCube (9 / 16 : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβμ : (ND.ord.length : ℝ) * β < μ)
    {i : ℕ} (hi : i < ND.ord.length) {g : PL.E N → M} {h : M ≃ₜ M}
    (inv : Work.Engulf.Alt.AltInnerG V X K L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.Γ₁ ND.g₁
      ND.ord β i g h)
    (hpieces : ∀ {G : Set (PL.E N)} (hGsub : Work.Engulf.IsSubSp ND.Γ₁ G)
      (hGdim : ∀ s ∈ ND.Γ₁.faces, PL.simp s ⊆ G → s.card ≤ p + 1)
      {g : PL.E N → M} (hgc : ContinuousOn g ND.Γ₁.space)
      (hgfrz : Set.EqOn g ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ))
      {h : M ≃ₜ M} (hsupp : PL.CSupp h (Set.univ : Set M)) (heng : X ∪ g '' G ⊆ h '' V)
      {Φ : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q} {F : Set (PL.E q)} {γ₀ γ₁ : PL.E q → ℝ}
      (hFc : IsCompact F) (hFconv : Convex ℝ F) (hγ₀c : Continuous γ₀) (hγ₁c : Continuous γ₁)
      (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z)
      {J : Set (PL.E q)} (hJF : J ⊆ F) (hJd : PL.DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
      (hsmall : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        Φ.symm ((0 : PL.E (n - q - 1)), z, t) ∈ PL.openCube (n := n) (9 / 16 : ℝ))
      {β₀ : ℝ} (hβ₀ : 0 < β₀),
      ∃ (g' : PL.E N → M) (h' : M ≃ₜ M), ContinuousOn g' ND.Γ₁.space ∧
        Set.EqOn g' g (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ∧
        (∀ x ∈ ND.Γ₁.space, dist (g' x) (g x) < β₀) ∧
        PL.CSupp h' (Set.univ : Set M) ∧ X ∪ g' '' G ⊆ h' '' V ∧
        ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
          ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, t)) ∈ h' '' V) :
    ∃ (g' : PL.E N → M) (h' : M ≃ₜ M),
      Work.Engulf.Alt.AltInnerG V X K L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.Γ₁ ND.g₁
        ND.ord β (i + 1) g' h' := by
  classical
  let Q : Set (PL.E N) := (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w))
  have hQdef : Q = (⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) := rfl
  have hinv : X ∪ g '' (K ∪ Q) ⊆ h '' V := inv.eng
  -- ## the witness of the shelled simplex
  obtain ⟨A_τ, hAeq₁, hAopen, hAvv⟩ := Work.Engulf.Alt.shell_wit ND hch hi
  have hσmem : ND.ord[i] ∈ ND.ord := List.getElem_mem hi
  have hσface : ND.ord[i] ∈ ND.Γ₁.faces := ND.ord_mem _ hσmem
  have hσΔ : PL.simp (ND.ord[i]) ⊆ PL.simp (τ₀ ∪ τ₁) := ND.ord_sub _ hσmem
  have hτcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) :=
    Work.Engulf.Alt.shell_core ND hch hi
  -- ## the member is core, so the moving map `g` agrees with `ψ ∘ A_τ` there
  have hσcore : PL.simp (ND.ord[i]) ⊆ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨ND.ord[i], hσface,
      Set.mem_iUnion.mpr ⟨hτcore, hx⟩⟩
  have hAeq' : ∀ x ∈ PL.simp (ND.ord[i]), g x = ψ.toFun (A_τ x) := by
    intro x hx
    rw [inv.frz (Or.inr (hσcore hx))]
    exact hAeq₁ x hx
  have hτinj : Set.InjOn A_τ (PL.simp (ND.ord[i])) :=
    Work.Engulf.Alt.shell_injOn ND A H7 hq hch hi A_τ hAvv
  have hindτ : AffineIndependent ℝ (fun v : ↥(ND.ord[i]) => A_τ v) :=
    Work.Engulf.E4Aux.affineIndependent_image_of_injOn (ND.Γ₁.indep hσface) hτinj
  have hcardτ : (ND.ord[i]).card = q + 2 := by rw [ND.ord_card _ hσmem, H7.card]
  -- ## the chart coordinates of the witness
  have hA17 : A_τ '' PL.simp (ND.ord[i]) ⊆ PL.openCube (17 / 32 : ℝ) := by
    have himg : A_τ '' PL.simp (ND.ord[i]) =
        convexHull ℝ (ND.vv '' (ND.ord[i] : Set (PL.E N))) := by
      change A_τ '' convexHull ℝ ((ND.ord[i] : Set (PL.E N))) =
        convexHull ℝ (ND.vv '' (ND.ord[i] : Set (PL.E N)))
      rw [AffineMap.image_convexHull]
      congr 1
      ext z
      simp only [Set.mem_image, Finset.mem_coe]
      exact ⟨fun ⟨v, hv, hz⟩ => ⟨v, hv, (hAvv v hv).symm.trans hz⟩,
        fun ⟨v, hv, hz⟩ => ⟨v, hv, (hAvv v hv).trans hz⟩⟩
    rw [himg]
    refine convexHull_min ?_ (convex_openCube' (17 / 32 : ℝ))
    rintro z ⟨v, hv, rfl⟩
    exact ND.shell17 v ((ND.Vt_mem v).mpr ⟨ND.ord[i], hσface, hv⟩) (hσΔ (subset_simp hv))
  have hcube : ∀ x ∈ PL.simp (ND.ord[i]),
      ψ.toFun (A_τ x) ∈ ψ.toFun '' PL.closedCube (9 / 16 : ℝ) := by
    intro x hx
    exact ⟨A_τ x, closedCube_mono (by norm_num)
      (openCube_subset_closedCube (17 / 32) (hA17 ⟨x, hx, rfl⟩)), rfl⟩
  -- ## the attaching facets of the shelled simplex
  obtain ⟨fl, hflne, hflsub, hflsplit⟩ := ND.ord_split i hi
  have hQss : Q ⊆ ⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length), PL.simp (ND.ord[j]) := by
    intro z hz
    rw [hQdef] at hz
    simp only [Set.mem_iUnion, exists_prop] at hz ⊢
    obtain ⟨j, hj, hj', w, -, hz⟩ := hz
    exact ⟨j, hj, hj', simp_mono (Finset.erase_subset w _) hz⟩
  have hflfacets : ∀ w ∈ fl, PL.simp (ND.ord[i].erase w) ⊆ K ∪ Q := by
    intro w hw x hx
    have hwi : w ∈ ND.ord[i] := hflsub.1 hw
    have hxmem : x ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
        ⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length), PL.simp (ND.ord[j])) := by
      rw [hflsplit]
      exact Set.mem_iUnion₂.mpr ⟨w, hw, hx⟩
    rcases hxmem.2 with hxfl | hxW
    · left
      rw [← H7.meetK] at hxfl
      exact hxfl.1
    · right
      rw [hQdef]
      obtain ⟨j, hjmem, hxW'⟩ := Set.mem_iUnion₂.mp hxW
      have hjlti : j < i := Finset.mem_range.mp hjmem
      obtain ⟨hjlen, hxj⟩ := Set.mem_iUnion.mp hxW'
      have hjface : ND.ord[j] ∈ ND.Γ₁.faces := ND.ord_mem _ (List.getElem_mem hjlen)
      have hneerase : (ND.ord[i].erase w).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hwi, hcardτ]; omega
      have hfaceerase : ND.ord[i].erase w ∈ ND.Γ₁.faces :=
        ND.Γ₁.down_closed hσface (Finset.erase_subset w _) hneerase
      have hxinter : x ∈ PL.simp ((ND.ord[i].erase w) ∩ ND.ord[j]) := by
        rw [← Work.Engulf.simp_inter hfaceerase hjface]
        exact ⟨hx, hxj⟩
      have hρne : (ND.ord[i].erase w) ∩ ND.ord[j] ≠ ND.ord[j] := by
        intro hcontra
        have hsub : ND.ord[j] ⊆ ND.ord[i].erase w := by
          rw [← hcontra]; exact Finset.inter_subset_left
        have hcardle : ND.ord[j].card ≤ (ND.ord[i].erase w).card := Finset.card_le_card hsub
        rw [ND.ord_card _ (List.getElem_mem hjlen), Finset.card_erase_of_mem hwi, H7.card,
          hcardτ] at hcardle
        omega
      have hssub : (ND.ord[i].erase w) ∩ ND.ord[j] ⊂ ND.ord[j] :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, hρne⟩
      obtain ⟨v, hvj, hvρ⟩ := Finset.exists_of_ssubset hssub
      have hsubev : (ND.ord[i].erase w) ∩ ND.ord[j] ⊆ ND.ord[j].erase v :=
        Finset.subset_erase.mpr ⟨Finset.inter_subset_right, hvρ⟩
      exact Set.mem_biUnion hjmem (Set.mem_iUnion.mpr ⟨hjlen,
        Set.mem_biUnion hvj (simp_mono hsubev hxinter)⟩)
  -- ## the prism decomposition of the shelled simplex
  have hflnes : fl ≠ ND.ord[i] := (Finset.ssubset_iff_subset_ne.mp hflsub).2
  have htopne : (ND.ord[i] \ fl).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    have hsub : ND.ord[i] ⊆ fl := by
      intro x hx
      by_contra hxf
      have hmem : x ∈ ND.ord[i] \ fl := Finset.mem_sdiff.mpr ⟨hx, hxf⟩
      rw [hc] at hmem
      exact Finset.notMem_empty x hmem
    exact hflnes (Finset.Subset.antisymm hflsub.1 hsub)
  have hdisjfl : Disjoint (ND.ord[i] \ fl) fl := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_sdiff] at ha
    exact ha.2 ha'
  have hunionfl : (ND.ord[i] \ fl) ∪ fl = ND.ord[i] := Finset.sdiff_union_of_subset hflsub.1
  obtain ⟨Φ, F, γ₀, γ₁, hFc, hFconv, hγ₀c, hγ₁c, hle, hfr, hprism0, hfloor0, _htop0⟩ :=
    Work.Engulf.E4alt.prism_of_shell (n := n) (q := q)
      (by have h1 := A.hp; have h2 := H7.hq; omega) ((T n).joinPrism)
      (y := A_τ) (τ := ND.ord[i]) (top := ND.ord[i] \ fl) (fl := fl)
      htopne hflne hdisjfl hunionfl hcardτ hindτ
  have himgσ : A_τ '' PL.simp (ND.ord[i]) =
      convexHull ℝ (A_τ '' (ND.ord[i] : Set (PL.E N))) := by
    change A_τ '' convexHull ℝ ((ND.ord[i] : Set (PL.E N))) = _
    rw [AffineMap.image_convexHull]
  have hprism : Φ '' (A_τ '' PL.simp (ND.ord[i])) =
      {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧
        γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} := by
    rw [himgσ]; exact hprism0
  have himgfl : A_τ '' (⋃ w ∈ fl, PL.simp (ND.ord[i].erase w)) =
      ⋃ w ∈ fl, convexHull ℝ (A_τ '' ((ND.ord[i].erase w) : Set (PL.E N))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨w, hw, by
        rw [← AffineMap.image_convexHull]
        exact ⟨x, hxw, rfl⟩⟩
    · intro hz
      obtain ⟨w, hw, hz⟩ := Set.mem_iUnion₂.mp hz
      rw [← AffineMap.image_convexHull] at hz
      obtain ⟨x, hxw, rfl⟩ := hz
      exact ⟨x, Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩, rfl⟩
  -- ## the exceptional set of `E4b`
  have hA9 : A_τ '' PL.simp (ND.ord[i]) ⊆ PL.openCube (9 / 16 : ℝ) :=
    hA17.trans (openCube_mono (by norm_num))
  have hτhnd : AffineIndependent ℝ (fun v : ↥(ND.ord[i] ∩ ND.Fzv) => ND.vv v) :=
    Work.Engulf.Alt.shell_hnd ND H7 hch hi
  have hτcard : (ND.ord[i]).card ≤ n + 1 := Work.Engulf.Alt.shell_card ND A H7 hq hi
  obtain ⟨Tex, hTexdim, hTexbad⟩ :=
    Work.Engulf.E4alt.badset ND H7 A hq hi hτcore A_τ hAeq₁ hAvv hτinj hτhnd hτcard
  -- ## `Jq`, the projection of the exceptional set to the base of the prism
  let ρ : PL.E n →ᵃ[ℝ] PL.E q := (prProj (n - q - 1) q).toAffineMap.comp Φ.toAffineMap
  have hρ : ∀ ξ : PL.E n, ρ ξ = (Φ ξ).2.1 := by
    intro ξ
    show prProj (n - q - 1) q (Φ ξ) = (Φ ξ).2.1
    obtain ⟨a, b, c⟩ := Φ ξ
    rfl
  have hTex' : PL.DomDim (closure Tex) ((q : ℤ) - 2) := by
    obtain ⟨S, hScard, hScov⟩ := hTexdim
    exact ⟨S, hScard, closure_minimal hScov (S.finite_toSet.isClosed_biUnion
      fun s _ => isClosed_simp s)⟩
  have hTexcomp : IsCompact (closure Tex) := by
    obtain ⟨S, hScard, hScov⟩ := hTex'
    exact IsCompact.of_isClosed_subset
      (S.finite_toSet.isCompact_biUnion fun s _ => isCompact_simp s) isClosed_closure hScov
  let Jq : Set (PL.E q) := ρ '' closure Tex ∩ F
  have hJd : PL.DomDim Jq ((q : ℤ) - 2) :=
    Work.PL.Subdiv.domDim_mono (Work.Engulf.E4Aux.DomDim.affine_image' ρ hTex')
      Set.inter_subset_left
  have hJF : Jq ⊆ F := Set.inter_subset_right
  have hJc : IsClosed Jq :=
    (hTexcomp.image ρ.continuous_of_finiteDimensional).isClosed.inter hFc.isClosed
  have hsmall : ∀ z ∈ Jq, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      Φ.symm ((0 : PL.E (n - q - 1)), z, t) ∈ PL.openCube (n := n) (9 / 16 : ℝ) := by
    intro z hz t ht
    have hzF : z ∈ F := hJF hz
    have hmem : ((0 : PL.E (n - q - 1)), z, t) ∈ Φ '' (A_τ '' PL.simp (ND.ord[i])) := by
      rw [hprism]; exact ⟨rfl, hzF, ht.1, ht.2⟩
    obtain ⟨y, hy, hyΦ⟩ := hmem
    have hsym : Φ.symm ((0 : PL.E (n - q - 1)), z, t) = y := by
      rw [← hyΦ, AffineEquiv.symm_apply_apply]
    rw [hsym]
    exact hA9 hy
  -- ## the bad-set statement in the form the push consumes, for the *frozen* map `g₁`
  have hAs₁ : ∀ x ∈ PL.simp (ND.ord[i]), ψ.toFun (A_τ x) ∈ X ∪ ND.g₁ '' (K ∪ Q) →
      ∃ z ∈ F, ∃ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        Φ (A_τ x) = ((0 : PL.E (n - q - 1)), z, t) ∧ (t = γ₀ z ∨ z ∈ Jq) := by
    intro x hx hmem
    have hprismx : Φ (A_τ x) ∈ {x : Work.Engulf.Pr (n - q - 1) q |
        x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} := by
      rw [← hprism]
      exact ⟨A_τ x, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨h10, h2F, h2le, h2ge⟩ := hprismx
    have hbad := hTexbad x hx (hcube x hx) (by
      rcases hmem with hmem | hmem
      · exact Or.inl hmem
      · exact Or.inr hmem)
    refine ⟨(Φ (A_τ x)).2.1, h2F, (Φ (A_τ x)).2.2, ⟨h2le, h2ge⟩, Prod.ext h10 rfl, ?_⟩
    rcases hbad with hxfloor | hxTex
    · left
      have hxfl : x ∈ ⋃ w ∈ fl, PL.simp (ND.ord[i].erase w) := by
        have h1 : x ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
            ⋃ j ∈ Finset.range i, ⋃ (_ : j < ND.ord.length), PL.simp (ND.ord[j])) := by
          refine ⟨hx, ?_⟩
          rcases hxfloor.2 with hxfloor | hxfloor
          · exact Or.inl hxfloor
          · exact Or.inr (hQss hxfloor)
        rwa [hflsplit] at h1
      have hflimg : Φ (A_τ x) ∈ {x : Work.Engulf.Pr (n - q - 1) q |
          x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} := by
        rw [← hfloor0]
        refine ⟨A_τ x, ?_, rfl⟩
        rw [← himgfl]
        exact ⟨x, hxfl, rfl⟩
      exact hflimg.2.2
    · right
      have hρmem : ρ (A_τ x) ∈ ρ '' closure Tex := ⟨A_τ x, subset_closure hxTex, rfl⟩
      rw [hρ] at hρmem
      exact ⟨hρmem, h2F⟩
  -- ## `G := K ∪ Q` is a subcomplex of `Γ₁` and `hGdim` holds for it
  have hQsub : Work.Engulf.IsSubSp ND.Γ₁ Q := by
    rw [hQdef]
    exact isSubSp_skeleton ND H7 i
  have hGsub : Work.Engulf.IsSubSp ND.Γ₁ (K ∪ Q) :=
    isSubSp_union (ND.subsp K H7.subK) hQsub
  have hGdim : ∀ s ∈ ND.Γ₁.faces, PL.simp s ⊆ K ∪ Q → s.card ≤ p + 1 := by
    intro s hs hsub
    rw [hQdef] at hsub
    exact card_le_of_simp_subset_K_union_Q ND H7 hcS hs hsub
  -- ## the piece loop (`E4c`), with the moving map
  obtain ⟨g', h_c, hg'c, hg'frz, hg'near, h_csupp, h_ceng, h_coverJ⟩ :=
    hpieces hGsub hGdim inv.cont inv.frz inv.supp hinv
      hFc hFconv hγ₀c hγ₁c hle hJF hJd hJc hsmall hβ
  -- ## the map `g'` agrees with `g₁` on `L ∪ coreSet`
  have hg'frz₁ : Set.EqOn g' ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) :=
    fun x hx => (hg'frz hx).trans (inv.frz hx)
  -- ## and `g'` still agrees with the witness `ψ ∘ A_τ` on the member
  have hAeq'g : ∀ x ∈ PL.simp (ND.ord[i]), g' x = ψ.toFun (A_τ x) := by
    intro x hx
    rw [hg'frz (Or.inr (hσcore hx))]
    exact hAeq' x hx
  -- ## the old engulfed set is closed
  have hsub2 : K ∪ Q ⊆ ND.Γ₁.space := Set.union_subset (ND.subsp K H7.subK).1 hQsub.1
  have hEc : IsClosed (X ∪ g' '' (K ∪ Q)) :=
    H7.cfg.Xc.union (((isCompact_of_isSubSp ND.hΓ₁ hGsub).image_of_continuousOn
      (hg'c.mono hsub2)).isClosed)
  -- ## the floor of the prism is engulfed
  have hbase' : ∀ z ∈ F,
      ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z)) ∈ X ∪ g' '' (K ∪ Q) := by
    intro z hz
    have hmem : ((0 : PL.E (n - q - 1)), z, γ₀ z) ∈
        Φ '' (A_τ '' (⋃ w ∈ fl, PL.simp (ND.ord[i].erase w))) := by
      rw [himgfl, hfloor0]
      exact ⟨rfl, hz, rfl⟩
    obtain ⟨y, hy, hyΦ⟩ := hmem
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    have hxσ : x ∈ PL.simp (ND.ord[i]) := simp_mono (Finset.erase_subset w _) hxw
    have hsym : Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z) = A_τ x := by
      rw [← hyΦ, AffineEquiv.symm_apply_apply, ← hxy]
    rw [hsym, (hAeq'g x hxσ).symm]
    exact Or.inr ⟨x, hflfacets w hw hxw, rfl⟩
  -- ## the bad-set bound for the moving map `g'`, via the transfer lemma
  have hAs' : ∀ x ∈ PL.simp (ND.ord[i]), ψ.toFun (A_τ x) ∈ X ∪ g' '' (K ∪ Q) →
      ∃ z ∈ F, ∃ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        Φ (A_τ x) = ((0 : PL.E (n - q - 1)), z, t) ∧ (t = γ₀ z ∨ z ∈ Jq) := by
    intro x hx hmem
    rcases hmem with hX | hcoll
    · exact hAs₁ x hx (Or.inl hX)
    · obtain ⟨y, hy, hyeq⟩ := hcoll
      have hyG : y ∈ ND.Γ₁.space := hsub2 hy
      have hycore : y ∈ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ := by
        by_contra hyc
        have himg : g' y ∈ ψ.toFun '' PL.closedCube (9 / 16 : ℝ) := by
          rw [hyeq]; exact hcube x hx
        have h1 : dist (g' y) (g y) < β := hg'near y hyG
        have h2 : dist (g y) (ND.g₁ y) ≤ (i : ℝ) * β := inv.near y hyG
        have hle' : (i : ℝ) + 1 ≤ (ND.ord.length : ℝ) := by
          have : i + 1 ≤ ND.ord.length := Nat.succ_le_of_lt hi
          exact_mod_cast this
        have hlt : ((i : ℝ) + 1) * β ≤ (ND.ord.length : ℝ) * β :=
          mul_le_mul_of_nonneg_right hle' (le_of_lt hβ)
        have hsum : dist (g' y) (ND.g₁ y) < ((i : ℝ) + 1) * β := by
          have ht := dist_triangle (g' y) (g y) (ND.g₁ y)
          have hb := add_lt_add_of_lt_of_le h1 h2
          have : ((i : ℝ) + 1) * β = β + (i : ℝ) * β := by ring
          rw [this]; linarith
        exact hmarg y hyG hyc (g' y) (lt_trans (lt_of_lt_of_le hsum hlt) hβμ) himg
      have hgy : g' y = ND.g₁ y :=
        eq_g₁_of_mem_closedCube hmarg hg'frz₁ hyG (by rw [hyeq]; exact hcube x hx)
          (by
            have h1 : dist (g' y) (g y) < β := hg'near y hyG
            have h2 : dist (g y) (ND.g₁ y) ≤ (i : ℝ) * β := inv.near y hyG
            have hle' : (i : ℝ) + 1 ≤ (ND.ord.length : ℝ) := by
              have : i + 1 ≤ ND.ord.length := Nat.succ_le_of_lt hi
              exact_mod_cast this
            have hlt : ((i : ℝ) + 1) * β ≤ (ND.ord.length : ℝ) * β :=
              mul_le_mul_of_nonneg_right hle' (le_of_lt hβ)
            have hsum : dist (g' y) (ND.g₁ y) < ((i : ℝ) + 1) * β := by
              have ht := dist_triangle (g' y) (g y) (ND.g₁ y)
              have hb := add_lt_add_of_lt_of_le h1 h2
              have : ((i : ℝ) + 1) * β = β + (i : ℝ) * β := by ring
              rw [this]; linarith
            exact lt_trans (lt_of_lt_of_le hsum hlt) hβμ)
      exact hAs₁ x hx (Or.inr ⟨y, hy, hgy ▸ hyeq⟩)
  -- ## the push (`E4d`)
  obtain ⟨h', h'supp, h'eng⟩ :=
    pushShellG ND T A.Vo hi hAeq'g hAopen hFc hFconv hγ₀c hγ₁c hle hfr hprism
      hEc h_csupp h_ceng hbase' hJF hJd hJc h_coverJ hAs'
  -- ## the invariant at `i + 1`
  have hsucc : (⋃ j ∈ Finset.range (i + 1), ⋃ (_ : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) = Q ∪ (⋃ w ∈ ND.ord[i],
        PL.simp (ND.ord[i].erase w)) := by
    rw [hQdef]
    ext y
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, Set.mem_union]
    constructor
    · rintro ⟨j, hj, hj', w, hw, hy⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact Or.inl ⟨j, hlt, hj', w, hw, hy⟩
      · exact Or.inr ⟨w, hw, hy⟩
    · rintro (⟨j, hj, hj', w, hw, hy⟩ | ⟨w, hw, hy⟩)
      · exact ⟨j, Nat.lt_succ_of_lt hj, hj', w, hw, hy⟩
      · exact ⟨i, Nat.lt_succ_self i, hi, w, hw, hy⟩
  refine ⟨g', h', Nat.succ_le_of_lt hi, h'supp, hg'c, ?_, ?_, ?_⟩
  · intro x hx
    exact (hg'frz hx).trans (inv.frz hx)
  · intro x hxspace
    have h1 : dist (g' x) (g x) ≤ β := le_of_lt (hg'near x hxspace)
    have h2 : dist (g x) (ND.g₁ x) ≤ (i : ℝ) * β := inv.near x hxspace
    have ht := dist_triangle (g' x) (g x) (ND.g₁ x)
    have hcast : ((i + 1 : ℕ) : ℝ) * β = (i : ℝ) * β + β := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rw [hcast]
    linarith
  · rw [hsucc]
    intro z hz
    refine h'eng ?_
    simpa only [Set.union_assoc] using hz

end Work.Engulf.E4S
