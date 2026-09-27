import Mathlib
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E1Inv
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.TameTransfer
import Submission.Work.Engulf.E1B.group

open Set Metric PL

universe u

namespace Work.Engulf.Chain

/-- Faces of a complex contained in the faces of another give an inclusion of spaces. -/
theorem faces_space_mono {N : ℕ} {Γ Γ' : PL.Cx N} (h : Γ.faces ⊆ Γ'.faces) :
    Γ.space ⊆ Γ'.space := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, h hs, hsx⟩

/-- `Tame` is monotone in the dominated set `X`. -/
theorem tame_of_subset {n p : ℕ} {M : Type*} [MetricSpace M] {X X' : Set M} {N : ℕ}
    {Γ : PL.Cx N} {L : Set (PL.E N)} {f : PL.E N → M} (hXX : X' ⊆ X)
    (ht : Work.Engulf.Tame n p X Γ L f) : Work.Engulf.Tame n p X' Γ L f := by
  intro x
  obtain ⟨ψ, hx, hdom, hlin⟩ := ht x
  obtain ⟨P, hPdim, hPmem⟩ := hdom
  exact ⟨ψ, hx, ⟨P, hPdim, fun y hy hyX => hPmem y hy (hXX hyX)⟩, hlin⟩

/-- `OvCtl` is monotone in the engulfed set `X`. -/
theorem ovCtl_of_subset_X {M : Type*} [MetricSpace M] {V X X' : Set M} {N : ℕ}
    {H L : Set (PL.E N)} {f : PL.E N → M}
    (hXX : X' ⊆ X) (h : Work.Engulf.OvCtl V X H L f) : Work.Engulf.OvCtl V X' H L f := by
  obtain ⟨C, hC, hCV, h1, h2⟩ := h
  exact ⟨C, hC, hCV, h1, fun x hx hxX => h2 x hx (hXX hxX)⟩

/-- A compact set is covered by the open `1/2`-cubes of finitely many `Tame` charts, each of
which is a smoothing chart. -/
theorem exists_chart_list_cover {n p : ℕ} {M : Type*} [MetricSpace M] {X : Set M} {N : ℕ}
    {Γ : PL.Cx N} {L : Set (PL.E N)} {f : PL.E N → M} {S : Set M}
    (hS : IsCompact S) (htame : Work.Engulf.Tame n p X Γ L f) :
    ∃ ψs : List (PL.CubeChart n M),
      (∀ i (hi : i < ψs.length), Work.Engulf.SmoothChart p X Γ L f ψs[i]) ∧
      S ⊆ ⋃ i ∈ Finset.range ψs.length, ⋃ (_ : i < ψs.length),
        ψs[i].toFun '' PL.openCube (1 / 2 : ℝ) := by
  classical
  choose ψ hmem hsm using htame
  have hopen : ∀ x : M, IsOpen ((ψ x).toFun '' PL.openCube (n := n) (1 / 2 : ℝ)) := fun x =>
    Work.Cells.Connell.cubeChart_isOpen_image_openCube (ψ x) (by norm_num) (by norm_num)
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun x : M => (ψ x).toFun '' PL.openCube (n := n) (1 / 2 : ℝ)) hopen
    (fun a _ => mem_iUnion.2 ⟨a, hmem a⟩)
  refine ⟨List.ofFn (fun j : Fin t.card => ψ ((t.equivFin.symm j : ↥t) : M)), ?_, ?_⟩
  · intro i hi
    rw [List.getElem_ofFn]
    exact hsm _
  · intro a ha
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (ht ha)
    refine mem_iUnion₂.2 ⟨(t.equivFin ⟨x, hx⟩).val, ?_, ?_⟩
    · rw [Finset.mem_range, List.length_ofFn]
      exact (t.equivFin ⟨x, hx⟩).isLt
    · refine mem_iUnion.2 ⟨?_, ?_⟩
      · rw [List.length_ofFn]
        exact (t.equivFin ⟨x, hx⟩).isLt
      · rw [List.getElem_ofFn]
        have hfix : ((t.equivFin.symm (t.equivFin ⟨x, hx⟩) : ↥t) : M) = x := by simp
        rw [hfix]
        exact hax

/-- **`E1` = Newman's Lemma 5** (repaired route: `Submission/Work/NOTES_LEAD_poincare_E1fix.md`; statement unchanged from the skeleton, universes made explicit).  Reduce a general configuration to one with `X ⊆ V`: cover `X ∖ V` by finitely many `Tame` charts `ψs` (each a `SmoothChart` for `(Γ,L,f)`), engulf the closed complement `X₀ = X ∖ ⋃ψs[i](openCube ½)` with `B (p+1)` (budget `ε/2`), then run the chart groups sequentially with `Engulf/E1B/group` (`E1_group`) (each group avoiding the *current* frozen image), and finish with `X ⊆ Xk ∪ g''F ⊆ h''V`.  `T` bundles the other areas' lemmas; see `Submission/Work/Engulf/Tools.lean` and the contract §7. -/
theorem E1 (n p : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (hB : Work.Engulf.B.{u} n p (p + 1))
    {M : Type u} [MetricSpace M] {V X : Set M} {N : ℕ} {Γ : PL.Cx N} {H L : Set (PL.E N)}
    {f : PL.E N → M} (A : Work.Engulf.Amb n p M V) (c : Work.Engulf.Cfg n p V X Γ H L f)
    (ε : ℝ) (hε : 0 < ε) : Work.Engulf.Engulfs V X Γ H L f ε := by
  classical
  -- `X ∖ V` is compact.
  have hXVclosed : IsClosed (X \ V) := c.Xc.sdiff A.Vo
  have hXV : IsCompact (X \ V) :=
    c.cpt.of_isClosed_subset hXVclosed (Set.diff_subset_diff Set.subset_union_left subset_rfl)
  -- finitely many smoothing charts covering `X ∖ V`
  obtain ⟨ψs, hψs, hcover⟩ := exists_chart_list_cover hXV c.tame
  -- the open chart cover `U` and the closed complement `X₀`
  set U : Set M := ⋃ i ∈ Finset.range ψs.length, ⋃ (_ : i < ψs.length),
    ψs[i].toFun '' PL.openCube (1 / 2 : ℝ) with hU
  set X₀ : Set M := X \ U with hX₀
  have hUopen : IsOpen U := by
    rw [hU]
    refine isOpen_biUnion fun i hi => ?_
    refine isOpen_iUnion fun hi' => ?_
    exact Work.Cells.Connell.cubeChart_isOpen_image_openCube
      (ψs[i]'(Finset.mem_range.mp hi)) (by norm_num) (by norm_num)
  have hX₀closed : IsClosed X₀ := by
    rw [hX₀]; exact c.Xc.sdiff hUopen
  have hX₀X : X₀ ⊆ X := by rw [hX₀]; exact Set.sdiff_subset
  have hX₀V : X₀ ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx.2 (hcover ⟨hx.1, hxV⟩)
  -- `f '' H` is compact and closed
  have hHc : IsCompact H := isCompact_of_isSubSp c.fin c.subH
  have hfHc : IsCompact (f '' H) := hHc.image_of_continuousOn (c.cont.mono c.subH.1)
  have hfHclosed : IsClosed (f '' H) := hfHc.isClosed
  have hcpt₀ : IsCompact ((X₀ ∪ f '' H) \ V) := by
    refine c.cpt.of_isClosed_subset ((hX₀closed.union hfHclosed).sdiff A.Vo) ?_
    rintro x ⟨hx1 | hx2, hxV⟩
    · exact ⟨Or.inl (hX₀X hx1), hxV⟩
    · exact ⟨Or.inr hx2, hxV⟩
  -- the configuration at `X₀`
  have hc₀ : Work.Engulf.Cfg n p V X₀ Γ H L f :=
    { fin := c.fin
      dimΓ := c.dimΓ
      room := c.room
      subH := c.subH
      subL := c.subL
      dimH := c.dimH
      cont := c.cont
      Xc := hX₀closed
      cpt := hcpt₀
      tame := tame_of_subset hX₀X c.tame
      ov := ovCtl_of_subset_X hX₀X c.ov }
  have hbad : Work.Engulf.BadCard Γ H f V (p + 1) := fun s hs hsH _ => c.dimH s hs hsH
  obtain ⟨g₀, hg₀cont, hg₀frz, hg₀near, h₀, h₀supp, h₀eng⟩ :=
    hB M V X₀ N Γ H L f A hc₀ hX₀V hbad (ε / 2) (by linarith)
  -- the invariant at `k = 0`
  have hdimF : ∀ s ∈ Γ.faces, PL.simp s ⊆ (∅ : Set (PL.E N)) → s.card ≤ p + 1 := by
    intro s _ hsF
    have hs : s = ∅ := simp_eq_empty_iff.mp (Set.subset_empty_iff.mp hsF)
    simp [hs]
  have hnear₀ : ∀ x ∈ Γ.space, dist (g₀ x) (f x) < ε * (1 - (1 / 2 : ℝ) ^ (0 + 1)) := by
    intro x hx
    have h1 : (1 : ℝ) - (1 / 2) ^ (0 + 1) = 1 / 2 := by norm_num
    have h2 : ε * (1 / 2 : ℝ) = ε / 2 := by ring
    rw [h1, h2]
    exact hg₀near x hx
  have htame₀ : Work.Engulf.Tame n p X Γ (L ∪ (∅ : Set (PL.E N))) g₀ := by
    have h := Work.Engulf.Tame.congr (p := p) hg₀frz c.tame
    simpa using h
  have hcover₀ : X ⊆ X₀ ∪ g₀ '' (∅ : Set (PL.E N)) ∪
      ⋃ i ∈ Finset.Ico 0 ψs.length, ⋃ (_ : i < ψs.length),
        ψs[i].toFun '' PL.closedCube (1 / 2 : ℝ) := by
    intro x hx
    by_cases hx₀ : x ∈ X₀
    · exact Or.inl (Or.inl hx₀)
    · refine Or.inr ?_
      have hxU : x ∈ U := by
        by_contra hxU
        exact hx₀ ⟨hx, hxU⟩
      rw [hU] at hxU
      obtain ⟨i, hi, hmem⟩ := mem_iUnion₂.1 hxU
      obtain ⟨hi', hf⟩ := mem_iUnion.1 hmem
      obtain ⟨y, hy, hyx⟩ := hf
      refine mem_iUnion₂.2 ⟨i, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        exact ⟨Nat.zero_le _, Finset.mem_range.mp hi⟩
      · exact mem_iUnion.2 ⟨Finset.mem_range.mp hi,
          ⟨y, openCube_subset_closedCube _ hy, hyx⟩⟩
  have hbase : Work.Engulf.E1GInv n p V X Γ H L f ψs ε 0 Γ (∅ : Set (PL.E N)) X₀ g₀ h₀ :=
    { le := Nat.zero_le _
      sub := subset_rfl
      fin := c.fin
      dim := c.dimΓ
      newF := fun s hs => Or.inl hs
      subF := isSubSp_empty Γ
      disjF := by simp
      dimF := hdimF
      cont := hg₀cont
      frz := hg₀frz
      near := hnear₀
      tame := htame₀
      supp := h₀supp
      Xkc := hX₀closed
      XkX := hX₀X
      eng := by simpa using h₀eng
      cover := hcover₀ }
  -- the loop over the chart groups
  have hloop : ∀ k ≤ ψs.length, ∃ (Γk : PL.Cx N) (F : Set (PL.E N)) (Xk : Set M)
      (g : PL.E N → M) (h : M ≃ₜ M),
      Work.Engulf.E1GInv n p V X Γ H L f ψs ε k Γk F Xk g h := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Γ, ∅, X₀, g₀, h₀, hbase⟩
    | succ k ih =>
      intro hk
      have hk' : k < ψs.length := by omega
      obtain ⟨Γk, F, Xk, g, h, I⟩ := ih (by omega)
      obtain ⟨Γk', F', Xk', g', h', I'⟩ := Work.Engulf.E1B.group T hB A c hψs hε hk' I
      exact ⟨Γk', F', Xk', g', h', I'⟩
  obtain ⟨Γk, F, Xk, g, h, I⟩ := hloop ψs.length le_rfl
  have hsub_space : Γ.space ⊆ Γk.space := faces_space_mono I.sub
  refine ⟨g, I.cont.mono hsub_space, I.frz, ?_, h, I.supp, ?_⟩
  · intro x hx
    have hfac : ε * (1 - (1 / 2 : ℝ) ^ (ψs.length + 1)) < ε := by
      have hp : (0 : ℝ) < (1 / 2) ^ (ψs.length + 1) := pow_pos (by norm_num) _
      nlinarith
    exact lt_trans (I.near x hx) hfac
  · rw [Set.union_subset_iff]
    constructor
    · intro x hx
      have hx' := I.cover hx
      rcases hx' with (hx1 | hx2) | hx3
      · exact I.eng (Or.inl hx1)
      · exact I.eng (Or.inr (Set.image_mono Set.subset_union_right hx2))
      · rw [Finset.Ico_self] at hx3
        simp at hx3
    · intro x hx
      exact I.eng (Or.inr (Set.image_mono Set.subset_union_left hx))

end Work.Engulf.Chain
