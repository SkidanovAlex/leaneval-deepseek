import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4Aux.prism_push_step
import Submission.Work.Engulf.E4Aux.collisionOfPair
import Submission.Work.Engulf.E4Aux.xCaseOfXcov
import Submission.Work.Engulf.E4alt.conjChart
import Submission.Work.Engulf.E4Aux.compact_subset_openCube
import Submission.Work.Engulf.E4Aux.le_of_affineEquiv_prism

namespace Work.Engulf.E4S

open Work.Engulf.E4Aux



private lemma isOpen_preimage_inter_openCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (ψ : PL.CubeChart n M) {T : Set M} (hT : IsOpen T) :
    IsOpen (ψ.toFun ⁻¹' T ∩ PL.openCube (n := n) 1) := by
  rw [Set.inter_comm]
  exact ψ.cont.isOpen_inter_preimage (Work.Engulf.isOpen_openCube 1) hT

private lemma isClosed_preimage_inter_closedCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (ψ : PL.CubeChart n M) {S : Set M} (hS : IsClosed S) {β : ℝ} (hβ : β < 1) :
    IsClosed (ψ.toFun ⁻¹' S ∩ PL.closedCube (n := n) β) := by
  have hcc : PL.closedCube (n := n) β ⊆ PL.openCube (n := n) 1 :=
    Work.Engulf.closedCube_subset_openCube hβ
  have hcont : ContinuousOn ψ.toFun (PL.closedCube (n := n) β) := ψ.cont.mono hcc
  have h := hcont.preimage_isClosed_of_isClosed (Work.Engulf.isClosed_closedCube β) hS
  rwa [Set.inter_comm] at h

/-- **`E4d` with a moving map: `pushStep2` with `ND.g₁ ↦ g`** (`NOTES_LEAD_poincare_E4c.md` §A.4).

This is the statement of §A.4: `Work.Engulf.E4Aux.pushStep2` with `ND.g₁` replaced by an arbitrary
`g` in `hAeq`, `hEc`, `heng`, `hbase`, `hAs` and in the conclusion, and with the two unused
hypotheses `hG` (containment of the old `q`-skeleton in `G`) and `hcore` (`f`-image in the `5/8`
cube) **dropped**.  It supersedes `Work.Engulf.E4Aux.pushShellG` (which keeps both unused
hypotheses).  See `Work.Engulf.E4S.pushStep2_of_pushShellG` for the converse derivation.

The push of one shelled simplex (Newman §14).  With the `E4a` normalisation `ND` and an arbitrary
map `g` (the loop's moving map; only `g = ψ ∘ A` on the member is used),
the `i`-th simplex `σ = ND.ord[i]` of the shelling order carried into the prism
`Φ '' (A '' simp σ) = {(0,z,t) | z ∈ F, γ₀ z ≤ t ≤ γ₁ z}` by its affine witness `A`, an open `V`,
the closed `(q-2)`-dominated exceptional set `J ⊆ F` of the bad-set analysis `E4b`, one obtains a
compactly supported homeomorphism `h'` engulfing the new part as well:

    X ∪ g '' (G ∪ ∂ σ) ⊆ h' '' V,     ∂ σ = ⋃_{w ∈ σ} simp (σ.erase w),

from four hypotheses, each of which is supplied by the loop:

* `hbase` — the *floor* of the prism (the `t = γ₀` slice) is already engulfed.  In the loop this is
  `floorOf τ₀ τ₁ ⊆ K ⊆ G` (`L7Hyp.meetK`) transported by the floor identification
  `Φ '' (A '' ⋃_{w ∈ fl} simp (σ.erase w)) = {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1}` of the
  `G2`/`joinPrism` datum (`Alt.prism_of_shell`) — it is `prism_push_step`'s `hb`;
* `hoverJ` — the region over `J` is already engulfed (the output of the piece loop `E4c`) — it is
  `prism_push_step`'s `hJ`;
* `heng` (+ closure `hEc`) — the old engulfed set `X ∪ g '' G` is inside `h '' V` and closed, so
  it can be put into the closed fix set of the push;
* `hAs` — the bad-set bound `E4b` (`xCaseOfXcov` + `collisionOfPair`): every prism point of
  `A '' simp σ` over the old engulfed set lies on the floor or over `J`.

The proof builds `U := ψ⁻¹ (h '' V) ∩ openCube 1` (open, since `hV : IsOpen V` and `h` is a
homeomorphism) and `W` an open neighbourhood of the compact prism with `closure W ⊆ openCube 1`,
and applies `prism_push_step` (via `T.prismPushRel`) with the closed fix set
`A₀ := Φ '' (ψ⁻¹ (X ∪ g₁ '' G) ∩ closure W) ∪ (prism over J)`; conjugating the resulting
homeomorphism of `E n` by `ψ` and extending by `T.extHomeo` gives `h'`.  The *new* part `∂ σ` is
automatic (the push presents every prism point as the image of a point of `U`, i.e. of a chart point
of `h '' V`); the old part needs `hAs`. -/
theorem pushShellG {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (T : Work.Engulf.ToolsAllM M n)
    (hV : IsOpen V)
    {i : ℕ} (hi : i < ND.ord.length)
    {g : PL.E N → M}
    {A : PL.E N →ᵃ[ℝ] PL.E n}
    (hAeq : ∀ x ∈ PL.simp (ND.ord[i]), g x = ψ.toFun (A x))
    (hAopen : ∀ x ∈ PL.simp (ND.ord[i]), A x ∈ PL.openCube (1 : ℝ))
    {Φ : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q} {F : Set (PL.E q)}
    {γ₀ γ₁ : PL.E q → ℝ}
    (hFc : IsCompact F) (hFconv : Convex ℝ F) (hγ₀c : Continuous γ₀) (hγ₁c : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z) (hfr : ∀ z ∈ frontier F, γ₀ z = γ₁ z)
    (hprism : Φ '' (A '' PL.simp (ND.ord[i])) =
      {x : Work.Engulf.Pr (n - q - 1) q |
        x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1})
    {G : Set (PL.E N)} (hEc : IsClosed (X ∪ g '' G))
    {h : M ≃ₜ M} (hsupp : PL.CSupp h (Set.univ : Set M))
    (heng : X ∪ g '' G ⊆ h '' V)
    (hbase : ∀ z ∈ F,
      ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z)) ∈ X ∪ g '' G)
    {J : Set (PL.E q)} (hJF : J ⊆ F) (hJd : PL.DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
    (hoverJ : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, t)) ∈ h '' V)
    (hAs : ∀ x ∈ PL.simp (ND.ord[i]), ψ.toFun (A x) ∈ X ∪ g '' G →
      ∃ z ∈ F, ∃ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        Φ (A x) = ((0 : PL.E (n - q - 1)), z, t) ∧ (t = γ₀ z ∨ z ∈ J)) :
    ∃ h' : M ≃ₜ M, PL.CSupp h' (Set.univ : Set M) ∧
      X ∪ g '' (G ∪ ⋃ w ∈ ND.ord[i], PL.simp (ND.ord[i].erase w)) ⊆ h' '' V := by
  classical
  -- ## the geometric dimension bound (needed to instantiate the prism push)
  have hq : q + 1 ≤ n := le_of_affineEquiv_prism Φ
  -- ## the shelled simplex lies in a strictly smaller open cube
  have hσsub : A '' PL.simp (ND.ord[i]) ⊆ PL.openCube (n := n) 1 := by
    rintro z ⟨x, hx, rfl⟩
    exact hAopen x hx
  have hσc : IsCompact (A '' PL.simp (ND.ord[i])) :=
    (Work.Engulf.isCompact_simp (ND.ord[i])).image A.continuous_of_finiteDimensional
  obtain ⟨β, hβ0, hβ1, hKβ⟩ := compact_subset_openCube hσc hσsub
  -- ## the chartwise sets
  set S : Set M := X ∪ g '' G with hSdef
  set U : Set (PL.E n) := ψ.toFun ⁻¹' (h '' V) ∩ PL.openCube (n := n) 1 with hUdef
  set A₀ : Set (PL.E n) := ψ.toFun ⁻¹' S ∩ PL.closedCube (n := n) β with hAdef
  have hSV : S ⊆ h '' V := by rw [hSdef]; exact heng
  have hSc : IsClosed S := by rw [hSdef]; exact hEc
  have hOpenV : IsOpen (h '' V) := h.isOpen_image.mpr hV
  have hUopen : IsOpen U := isOpen_preimage_inter_openCube ψ hOpenV
  have hAcl : IsClosed A₀ := isClosed_preimage_inter_closedCube ψ hSc hβ1
  have hPclβ : PL.closedCube (n := n) β ⊆ PL.openCube (n := n) 1 :=
    Work.Engulf.closedCube_subset_openCube hβ1
  have hKβ1 : A '' PL.simp (ND.ord[i]) ⊆ PL.openCube (n := n) 1 :=
    fun z hz => hPclβ (Work.Engulf.openCube_subset_closedCube β (hKβ hz))
  have hAU : A₀ ⊆ U := by
    intro z hz
    rw [hAdef] at hz
    rw [hUdef]
    exact ⟨hSV hz.1, hPclβ hz.2⟩
  -- ## the prism as the image of the shelled simplex
  have hprism_symm : Φ.symm '' {x : Work.Engulf.Pr (n - q - 1) q |
      x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1}
      = A '' PL.simp (ND.ord[i]) := by
    rw [← hprism]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, haw⟩ := hw
      rw [← haw, AffineEquiv.symm_apply_apply]
      exact ha
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Φ (A y), ⟨A y, ⟨y, hy, rfl⟩, rfl⟩, AffineEquiv.symm_apply_apply Φ (A y)⟩
  -- ## the hypotheses of the push
  have hb : ∀ z ∈ F, ((0 : PL.E (n - q - 1)), z, γ₀ z) ∈ Φ '' U := by
    intro z hz
    refine ⟨Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z), ?_, ?_⟩
    · rw [hUdef]
      refine ⟨?_, ?_⟩
      · exact hSV (by rw [hSdef]; exact hbase z hz)
      · have hm : Φ.symm ((0 : PL.E (n - q - 1)), z, γ₀ z) ∈ A '' PL.simp (ND.ord[i]) := by
          rw [← hprism_symm]
          exact ⟨((0 : PL.E (n - q - 1)), z, γ₀ z), ⟨rfl, hz, le_rfl, hle z hz⟩, rfl⟩
        exact hKβ1 hm
    · rw [AffineEquiv.apply_symm_apply]
  have hJ' : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E (n - q - 1)), z, t) ∈ Φ '' U := by
    intro z hz t ht
    refine ⟨Φ.symm ((0 : PL.E (n - q - 1)), z, t), ?_, ?_⟩
    · rw [hUdef]
      refine ⟨hoverJ z hz t ht, ?_⟩
      have hm : Φ.symm ((0 : PL.E (n - q - 1)), z, t) ∈ A '' PL.simp (ND.ord[i]) := by
        rw [← hprism_symm]
        exact ⟨((0 : PL.E (n - q - 1)), z, t), ⟨rfl, hJF hz, ht.1, ht.2⟩, rfl⟩
      exact hKβ1 hm
    · rw [AffineEquiv.apply_symm_apply]
  have hW' : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E (n - q - 1)), z, t) ∈ Φ '' PL.openCube (n := n) β := by
    intro z hz t ht
    refine ⟨Φ.symm ((0 : PL.E (n - q - 1)), z, t), ?_, ?_⟩
    · have hm : Φ.symm ((0 : PL.E (n - q - 1)), z, t) ∈ A '' PL.simp (ND.ord[i]) := by
        rw [← hprism_symm]
        exact ⟨((0 : PL.E (n - q - 1)), z, t), ⟨rfl, hz, ht.1, ht.2⟩, rfl⟩
      exact hKβ hm
    · rw [AffineEquiv.apply_symm_apply]
  have hAs' : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E (n - q - 1)), z, t) ∈ Φ '' A₀ → t = γ₀ z ∨ z ∈ J := by
    intro z hz t ht hmem
    obtain ⟨a, ha, haeq⟩ := hmem
    have haσ : a ∈ A '' PL.simp (ND.ord[i]) := by
      rw [← hprism_symm]
      refine ⟨((0 : PL.E (n - q - 1)), z, t), ⟨rfl, hz, ht.1, ht.2⟩, ?_⟩
      rw [← haeq, AffineEquiv.symm_apply_apply]
    obtain ⟨x, hx, rfl⟩ := haσ
    rw [hAdef] at ha
    have hψx : ψ.toFun (A x) ∈ X ∪ g '' G := by rw [hSdef] at ha; exact ha.1
    obtain ⟨z', hz'F, t', ht', heq, hcase⟩ := hAs x hx hψx
    have hzt : ((0 : PL.E (n - q - 1)), z, t) = ((0 : PL.E (n - q - 1)), z', t') :=
      haeq.symm.trans heq
    have hz_eq : z = z' :=
      congrArg (fun p : Work.Engulf.Pr (n - q - 1) q => p.2.1) hzt
    have ht_eq : t = t' :=
      congrArg (fun p : Work.Engulf.Pr (n - q - 1) q => p.2.2) hzt
    rcases hcase with h | h
    · left; rw [ht_eq, h, hz_eq]
    · right; rwa [hz_eq]
  -- ## the prism push
  obtain ⟨h_push, h_push_supp, h_push_fix, h_push_img⟩ :=
    prism_push_step hq Φ F J hFc hJc hJF γ₀ γ₁ hγ₀c hγ₁c hle hfr U
      (PL.openCube (n := n) β) A₀ hUopen (Work.Engulf.isOpen_openCube β) hAcl hAU
      hb hJ' hW' hAs' ((T N).prismPushRel)
  have h_push_out : ∀ x, x ∉ PL.openCube (n := n) β → h_push x = x := by
    intro x hx
    obtain ⟨C, hC, hCW, hCid⟩ := h_push_supp
    exact hCid x (fun hxC => hx (hCW hxC))
  -- ## conjugating the push through the chart
  obtain ⟨Hc, hHc_supp, hHc_on, hHc_off⟩ :=
    Work.Engulf.E4alt.conjChart T ψ hβ0 hβ1 h_push h_push_out
  have hHcsuppU : PL.CSupp Hc (Set.univ : Set M) := by
    obtain ⟨C, hC, -, hCid⟩ := hHc_supp
    exact ⟨C, hC, Set.subset_univ _, hCid⟩
  -- ## the chart image of the old engulfed set is fixed
  have hHcfixS : ∀ y ∈ S, Hc y = y := by
    intro y hy
    by_cases hyc : y ∈ ψ.toFun '' PL.openCube (n := n) 1
    · obtain ⟨u, hu, rfl⟩ := hyc
      have h1 : h_push u = u := by
        by_cases huW : u ∈ PL.openCube (n := n) β
        · exact h_push_fix u ⟨hy, Work.Engulf.openCube_subset_closedCube β huW⟩
        · exact h_push_out u huW
      rw [hHc_on u hu, h1]
    · exact hHc_off y hyc
  -- ## the new part: the push presents its chart image as an image of `h '' V`
  have hnew : ∀ x ∈ (⋃ w ∈ ND.ord[i], PL.simp (ND.ord[i].erase w)),
      g x ∈ Hc '' (h '' V) := by
    intro x hx
    have hxσ : x ∈ PL.simp (ND.ord[i]) := by
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact Work.Engulf.simp_mono (Finset.erase_subset w (ND.ord[i])) hxw
    have hp : Φ (A x) ∈ {x : Work.Engulf.Pr (n - q - 1) q |
        x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} := by
      rw [← hprism]; exact ⟨A x, ⟨x, hxσ, rfl⟩, rfl⟩
    obtain ⟨hp1, hp2F, hp2le, hp2ge⟩ := hp
    have hAx : A x ∈ h_push '' U := by
      have h := h_push_img (Φ (A x)).2.1 hp2F (Φ (A x)).2.2 ⟨hp2le, hp2ge⟩
      have he : ((0 : PL.E (n - q - 1)), (Φ (A x)).2.1, (Φ (A x)).2.2) = Φ (A x) := by
        rw [← hp1]
      rw [he, AffineEquiv.symm_apply_apply] at h
      exact h
    obtain ⟨u, hu, hu'⟩ := hAx
    refine ⟨ψ.toFun u, hu.1, ?_⟩
    rw [hHc_on u hu.2, hu', hAeq x hxσ]
  -- ## the new homeomorphism
  refine ⟨h.trans Hc, ?_, ?_⟩
  · obtain ⟨C₁, hC₁, -, hC₁id⟩ := hsupp
    obtain ⟨C₂, hC₂, -, hC₂id⟩ := hHcsuppU
    refine ⟨C₁ ∪ h.symm '' C₂, hC₁.union (hC₂.image h.symm.continuous),
      Set.subset_univ _, ?_⟩
    intro x hx
    rw [Homeomorph.trans_apply]
    have hx1 : x ∉ C₁ := fun hh => hx (Or.inl hh)
    have hx2 : h x ∉ C₂ := fun hh => hx (Or.inr ⟨h x, hh, h.symm_apply_apply x⟩)
    rw [hC₂id (h x) hx2, hC₁id x hx1]
  · have himgV : (h.trans Hc) '' V = Hc '' (h '' V) := by
      ext y; constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨h v, ⟨v, hv, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, by rw [Homeomorph.trans_apply]⟩
    rw [himgV]
    intro y hy
    rcases hy with hyX | hyG
    · exact ⟨y, hSV (by rw [hSdef]; exact Or.inl hyX),
        hHcfixS y (by rw [hSdef]; exact Or.inl hyX)⟩
    · obtain ⟨x, hx, rfl⟩ := hyG
      rcases hx with hxG | hxnew
      · refine ⟨g x, hSV (by rw [hSdef]; exact Or.inr ⟨x, hxG, rfl⟩), ?_⟩
        exact hHcfixS (g x) (by rw [hSdef]; exact Or.inr ⟨x, hxG, rfl⟩)
      · exact hnew x hxnew

end Work.Engulf.E4S
