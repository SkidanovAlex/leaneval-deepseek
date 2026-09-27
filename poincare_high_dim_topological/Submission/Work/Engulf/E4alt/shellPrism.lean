import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.ShellPrep
import Submission.Work.Engulf.E4alt.attaching
import Submission.Work.Engulf.E4alt.prism_of_shell
import Submission.Work.Engulf.E4Aux.affineIndependent_image_of_injOn

/-!
# `Work.Engulf.E4alt.shellPrism`

The prism decomposition of one member `ND.ord[i]` of the shelling order of the `E4alt`
normalisation (`Submission/Work/Engulf/E4alt/NOTES_step_recipe.md` §2), in the exact form the
per-simplex step `E4b`–`E4d` consumes:

* `fl` are the *attaching* vertices of `ND.ord[i]` — those facets of `ND.ord[i]` that lie in the
  already engulfed region `K ∪ Q^i` (`Work.Engulf.E4alt.attaching`); `top := ND.ord[i] \ fl` is
  the complementary ("new") vertex set;
* `A_τ` is the affine witness of `ND.g₁` on `simp (ND.ord[i])` with vertex values `ND.vv`
  (`Work.Engulf.Alt.shell_wit`) — so `A_τ v = ND.vv v` on the vertices, `ND.g₁ = ψ ∘ A_τ` on the
  simplex, and the whole simplex is sent into the open unit cube;
* `Tp` is the prism chart with base `F`, heights `γ₀ ≤ γ₁` (`Work.Engulf.E4alt.prism_of_shell`,
  i.e. `G2`/`JoinPrismForm` applied to the vertex images `A_τ v`), the `γ₀`-graph being the image
  of the `fl`-side (the floor) and the `γ₁`-graph that of the `top`-side.

The only genuinely new work here is the bookkeeping: the vertices of `ND.ord[i]` are affinely
independent as points of `E N` (`NormData.Γ₁.indep`), `A_τ` is injective on the simplex by general
position (`Work.Engulf.Alt.shell_injOn`), so the images `A_τ v` are affinely independent
(`Work.Engulf.E4Aux.affineIndependent_image_of_injOn`), and the affine image of a simplex is the
convex hull of the images of its vertices (`AffineMap.image_convexHull`), which is the form
`prism_of_shell` is stated in.
-/

namespace Work.Engulf.E4alt

open Set Metric

/-- The affine image of the simplex on a vertex set `t` is the convex hull of the images of the
vertices of `t` (the form in which `Work.Engulf.E4alt.prism_of_shell` states its conclusions). -/
lemma shellPrism_image_simp {N n : ℕ} (A : PL.E N →ᵃ[ℝ] PL.E n) (t : Finset (PL.E N)) :
    A '' PL.simp t = convexHull ℝ (A '' (t : Set (PL.E N))) := by
  rw [PL.simp]
  exact AffineMap.image_convexHull A (t : Set (PL.E N))

/-- The same for a union of facets over a vertex set `s`: the image of
`⋃ w ∈ s, simp (τ.erase w)` is the union of the convex hulls of the vertex images. -/
lemma shellPrism_image_iUnion_simp {N n : ℕ} (A : PL.E N →ᵃ[ℝ] PL.E n)
    (τ s : Finset (PL.E N)) :
    A '' (⋃ w ∈ s, PL.simp (τ.erase w)) =
      ⋃ w ∈ s, convexHull ℝ (A '' ((τ.erase w) : Set (PL.E N))) := by
  rw [Set.image_iUnion₂]
  simp_rw [shellPrism_image_simp A]

theorem shellPrism {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (T : Work.Engulf.ToolsAll n) (hq : q + 1 ≤ p + 1)
    (A : Work.Engulf.Amb n p M V)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    ∃ (fl top : Finset (PL.E N)) (A_τ : PL.E N →ᵃ[ℝ] PL.E n)
      (Tp : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q) (F : Set (PL.E q)) (γ₀ γ₁ : PL.E q → ℝ),
      fl.Nonempty ∧ top.Nonempty ∧ Disjoint top fl ∧ top ∪ fl = ND.ord[i] ∧
      (∀ w ∈ fl, PL.simp (ND.ord[i].erase w) ⊆ K ∪ ⋃ j ∈ Finset.range i,
        ⋃ (hj : j < ND.ord.length), ⋃ w' ∈ ND.ord[j], PL.simp (ND.ord[j].erase w')) ∧
      (∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A_τ x)) ∧
      (∀ x ∈ PL.simp (ND.ord[i]), A_τ x ∈ PL.openCube (1 : ℝ)) ∧
      (∀ v ∈ ND.ord[i], A_τ v = ND.vv v) ∧
      IsCompact F ∧ Convex ℝ F ∧ Continuous γ₀ ∧ Continuous γ₁ ∧
      (∀ z ∈ F, γ₀ z ≤ γ₁ z) ∧ (∀ z ∈ frontier F, γ₀ z = γ₁ z) ∧
      Tp '' (A_τ '' PL.simp (ND.ord[i])) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧
          γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} ∧
      Tp '' (A_τ '' (⋃ w ∈ fl, PL.simp (ND.ord[i].erase w))) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} ∧
      Tp '' (A_τ '' (⋃ w ∈ top, PL.simp (ND.ord[i].erase w))) =
        {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1} := by
  classical
  -- ## the attaching facets of the shelled simplex
  obtain ⟨fl, hflne, hflsub, hflfacets⟩ :=
    attaching ND H7 ND.ord ND.ord_mem ND.ord_card ND.ord_split (i := i) hi
  -- ## the affine witness of `g₁` on the simplex, with the vertex values `vv`
  obtain ⟨A_τ, hAeq, hAopen, hAvv⟩ := Work.Engulf.Alt.shell_wit ND hch hi
  -- ## the vertex images are affinely independent
  have hσmem : ND.ord[i] ∈ ND.ord := List.getElem_mem hi
  have hσface : ND.ord[i] ∈ ND.Γ₁.faces := ND.ord_mem _ hσmem
  have hτinj : Set.InjOn A_τ (PL.simp (ND.ord[i])) :=
    Work.Engulf.Alt.shell_injOn ND A H7 hq hch hi A_τ hAvv
  have hindτ : AffineIndependent ℝ (fun v : ↥(ND.ord[i]) => A_τ v) :=
    Work.Engulf.E4Aux.affineIndependent_image_of_injOn (ND.Γ₁.indep hσface) hτinj
  have hcardτ : (ND.ord[i]).card = q + 2 := by rw [ND.ord_card _ hσmem, H7.card]
  -- ## the join decomposition `ord[i] = top ∪ fl` into the new and the attached vertices
  have htopne : (ND.ord[i] \ fl).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    refine hflsub.2 fun x hx => ?_
    by_contra hxf
    have hx' : x ∈ ND.ord[i] \ fl := Finset.mem_sdiff.mpr ⟨hx, hxf⟩
    rw [hc] at hx'
    exact Finset.notMem_empty x hx'
  have hdisjfl : Disjoint (ND.ord[i] \ fl) fl :=
    Finset.disjoint_left.mpr (fun a ha ha' => (Finset.mem_sdiff.mp ha).2 ha')
  have hunionfl : (ND.ord[i] \ fl) ∪ fl = ND.ord[i] := Finset.sdiff_union_of_subset hflsub.1
  -- ## the prism decomposition (`G2`, `JoinPrismForm`)
  have hqn : q + 1 ≤ n := by have := A.hp; omega
  obtain ⟨Tp, F, γ₀, γ₁, hFc, hFconv, hγ₀c, hγ₁c, hle, hfr, hprism0, hfloor0, htop0⟩ :=
    prism_of_shell (n := n) (q := q) hqn ((T n).joinPrism)
      (y := A_τ) (τ := ND.ord[i]) (top := ND.ord[i] \ fl) (fl := fl)
      htopne hflne hdisjfl hunionfl hcardτ hindτ
  -- ## rewrite the three conclusions in the form of the statement
  have hprism : Tp '' (A_τ '' PL.simp (ND.ord[i])) =
      {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧
        γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} := by
    rw [shellPrism_image_simp A_τ (ND.ord[i])]
    exact hprism0
  have hfl' : Tp '' (A_τ '' (⋃ w ∈ fl, PL.simp (ND.ord[i].erase w))) =
      {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} := by
    rw [shellPrism_image_iUnion_simp A_τ (ND.ord[i]) fl]
    exact hfloor0
  have htop' : Tp '' (A_τ '' (⋃ w ∈ ND.ord[i] \ fl, PL.simp (ND.ord[i].erase w))) =
      {x : Work.Engulf.Pr (n - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1} := by
    rw [shellPrism_image_iUnion_simp A_τ (ND.ord[i]) (ND.ord[i] \ fl)]
    exact htop0
  exact ⟨fl, ND.ord[i] \ fl, A_τ, Tp, F, γ₀, γ₁, hflne, htopne, hdisjfl, hunionfl, hflfacets,
    hAeq, hAopen, hAvv, hFc, hFconv, hγ₀c, hγ₁c, hle, hfr, hprism, hfl', htop'⟩

end Work.Engulf.E4alt
