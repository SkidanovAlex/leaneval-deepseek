import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E1Inv
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Chain.E1gAux
import Submission.Work.Engulf.Auxi.exists_group_pieces
import Submission.Work.Engulf.Auxi.exists_thickening_subset
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.Engulf.Auxi.TameTransfer
import Submission.Work.Engulf.E1B.step

open Set Metric PL
universe u
namespace Work.Engulf.E1B

theorem group {n p N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {H L : Set (PL.E N)} {f : PL.E N → M}
    (T : Work.Engulf.ToolsAll.{u} n) (hB : Work.Engulf.B.{u} n p (p + 1))
    (A : Work.Engulf.Amb n p M V) (c : Work.Engulf.Cfg n p V X Γ H L f)
    {ψs : List (PL.CubeChart n M)} (hψs : ∀ i (hi : i < ψs.length),
      Work.Engulf.SmoothChart p X Γ L f ψs[i])
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : k < ψs.length)
    {Γk : PL.Cx N} {F : Set (PL.E N)} {Xk : Set M} {g : PL.E N → M} {h : M ≃ₜ M}
    (I : Work.Engulf.E1GInv n p V X Γ H L f ψs ε k Γk F Xk g h) :
    ∃ (Γk' : PL.Cx N) (F' : Set (PL.E N)) (Xk' : Set M) (g' : PL.E N → M) (h' : M ≃ₜ M),
      Work.Engulf.E1GInv n p V X Γ H L f ψs ε (k + 1) Γk' F' Xk' g' h' := by
  classical
  set ψ : PL.CubeChart n M := ψs[k] with hψdef
  have hψk : Work.Engulf.SmoothChart p X Γ L f ψ := by rw [hψdef]; exact hψs k hk
  -- ## the frozen image `g '' F` and a thickening of it inside `h '' V`
  have hFc : IsCompact F := isCompact_of_isSubSp I.fin I.subF
  have hgFc : IsCompact (g '' F) := hFc.image_of_continuousOn (I.cont.mono I.subF.1)
  have hgFV : g '' F ⊆ h '' V := fun y hy =>
    I.eng (Or.inr (Set.image_mono Set.subset_union_right hy))
  obtain ⟨δ, hδ, hδV⟩ :=
    Work.Engulf.Aux.exists_thickening_subset hgFc
      ((h.isOpen_image (s := V)).mpr A.Vo) hgFV
  -- ## the enlarged kept set `X₁` and the remaining pieces `R`
  set X₁ : Set M := Xk ∪ (X ∩ Metric.cthickening (δ / 2) (g '' F)) with hX₁def
  have hX₁closed : IsClosed X₁ := by
    rw [hX₁def]
    exact I.Xkc.union (c.Xc.inter Metric.isClosed_cthickening)
  have hX₁X : X₁ ⊆ X := by
    rw [hX₁def]
    exact Set.union_subset I.XkX Set.inter_subset_left
  have hX₁V : X₁ ⊆ h '' V := by
    rw [hX₁def]
    refine Set.union_subset (fun y hy => I.eng (Or.inl hy)) ?_
    rintro y ⟨-, hyc⟩
    have hlt : ((⟨δ / 2, by positivity⟩ : NNReal) : ℝ) < δ := by
      simp only [NNReal.coe_mk]; linarith
    exact hδV (Metric.cthickening_subset_thickening (δ₁ := ⟨δ / 2, by positivity⟩) hlt (g '' F) hyc)
  set R : Set M := (X ∩ ψ.toFun '' PL.closedCube (1 / 2 : ℝ)) \
    Metric.thickening (δ / 2) (g '' F) with hRdef
  have hψcl : IsCompact (ψ.toFun '' PL.closedCube (1 / 2 : ℝ)) :=
    (isCompact_closedCube (1 / 2 : ℝ)).image_of_continuousOn
      (ψ.cont.mono fun x hx => closedCube_subset_openCube (by norm_num) hx)
  have hXRc : IsCompact (X ∩ ψ.toFun '' PL.closedCube (1 / 2 : ℝ)) :=
    hψcl.of_isClosed_subset (c.Xc.inter hψcl.isClosed) Set.inter_subset_right
  have hRc : IsCompact R :=
    hXRc.of_isClosed_subset (hXRc.isClosed.sdiff Metric.isOpen_thickening) Set.sdiff_subset
  obtain ⟨pieces, hpieces_all, hRcov⟩ :=
    Work.Engulf.Aux.exists_group_pieces (T n).subdiv ψ hψk.1
      (R := R) (by rw [hRdef]; exact Set.sdiff_subset) (δ := δ / 4) (by linarith)
  -- ## the budget of one piece
  set η : ℝ := ε * (1 / 2 : ℝ) ^ (k + 2) / ((pieces.length : ℝ) + 1) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  -- ## the properties of the pieces, in particular the disjointness from `g '' F`
  have hpieces : ∀ j (hj : j < pieces.length),
      (pieces[j]).Nonempty ∧
      AffineIndependent ℝ (fun v : ↥(pieces[j]) => (v : PL.E n)) ∧
      (pieces[j]).card ≤ p + 1 ∧ PL.simp (pieces[j]) ⊆ PL.closedCube (5 / 8 : ℝ) ∧
      Disjoint (ψ.toFun '' PL.simp (pieces[j])) (g '' F) := by
    intro j hj
    obtain ⟨hne, haff, hcard, hcube, hnear⟩ := hpieces_all (pieces[j]) (List.get_mem _ _)
    refine ⟨hne, haff, hcard, hcube, ?_⟩
    rw [Set.disjoint_left]
    intro z hzψ hzg
    obtain ⟨y, hy, hyz⟩ := hzψ
    obtain ⟨z', hz'R, hdz'⟩ := hnear y hy
    have hdz' : dist z z' < δ / 4 := by rw [← hyz]; exact hdz'
    have hge : δ / 2 ≤ dist z z' := by
      by_contra hlt
      rw [not_le] at hlt
      exact hz'R.2 (Metric.mem_thickening_iff.mpr ⟨z, hzg, by simpa [dist_comm] using hlt⟩)
    linarith
  -- ## the state at `r = 0`
  have hnew_chart : ∀ s ∈ Γk.faces, PL.simp s ⊆ L → s ∈ Γ.faces := by
    intro s hs hsL
    rcases I.newF s hs with h | h
    · exact h
    · exfalso
      obtain ⟨v, hv⟩ := Γk.nonempty_of_mem_faces hs
      exact Set.disjoint_left.mp I.disjF (h (subset_simp hv)) (c.subL.1 (hsL (subset_simp hv)))
  have hS₀ : Work.Engulf.Chain.E1GSt (n := n) (p := p) V X Γk H L F ψ X₁ g pieces η 0 Γk ∅ g h :=
    { le := Nat.zero_le _
      sub := subset_rfl
      fin := I.fin
      dim := I.dim
      newG := fun s hs => Or.inl hs
      subG := isSubSp_empty Γk
      disjG := by simp
      dimG := fun s _ hsF => by
        have hs : s = ∅ := Work.Engulf.simp_eq_empty_iff.mp (Set.subset_empty_iff.mp hsF)
        simp [hs]
      cont := I.cont
      frz := fun x _ => rfl
      gaff := fun j hj _ => absurd hj (Nat.not_lt_zero j)
      near := fun x _ => by simp
      tame := by simpa [Set.union_empty] using I.tame
      chart := by
        have h := Work.Engulf.Chain.smoothChart_mono (p := p)
          (X := X) (X' := X) (Γ := Γ) (Γ' := Γk) (L := L) (f := f) (f' := g) (ψ := ψ)
          subset_rfl I.sub hnew_chart I.frz hψk
        simpa [Set.union_empty] using h
      eng := by
        refine Set.union_subset hX₁V ?_
        exact fun y hy => I.eng (Or.inr (by simpa [Set.union_empty] using hy))
      supp := I.supp }
  -- ## the loop over the pieces
  have hiter : ∀ r ≤ pieces.length, ∃ (Γr : PL.Cx N) (G : Set (PL.E N))
      (gr : PL.E N → M) (hr : M ≃ₜ M),
      Work.Engulf.Chain.E1GSt (n := n) (p := p) V X Γk H L F ψ X₁ g pieces η r Γr G gr hr := by
    intro r
    induction r with
    | zero => intro _; exact ⟨Γk, ∅, g, h, hS₀⟩
    | succ r ih =>
      intro hr
      have hrl : r < pieces.length := by omega
      obtain ⟨Γr, G, gr, hr', S⟩ := ih (by omega)
      obtain ⟨Γ', G', g', h', S'⟩ := step hB A c I hηpos hX₁closed hX₁X hpieces hrl S
      exact ⟨Γ', G', g', h', S'⟩
  obtain ⟨ΓF, G, gF, hF, SF⟩ := hiter pieces.length le_rfl
  -- ## the part of `X` covered by this chart
  have hXkcover : X ∩ ψ.toFun '' PL.closedCube (1 / 2 : ℝ) ⊆ X₁ ∪ gF '' G := by
    intro x hx
    by_cases hth : x ∈ Metric.thickening (δ / 2) (g '' F)
    · exact Or.inl (Or.inr ⟨hx.1, Metric.thickening_subset_cthickening _ _ hth⟩)
    · refine Or.inr ?_
      obtain ⟨Δ, hΔmem, hΔx⟩ := mem_iUnion₂.1 (hRcov ⟨hx, hth⟩)
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hΔmem
      have hgaff := SF.gaff j (by omega) (by omega)
      rw [hjeq] at hgaff
      exact hgaff hΔx
  -- ## the invariant at `k + 1`
  refine ⟨ΓF, F ∪ G, X₁, gF, hF, ?_⟩
  refine
    { le := hk
      sub := fun s hs => SF.sub (I.sub hs)
      fin := SF.fin
      dim := SF.dim
      newF := ?_
      subF := Work.Engulf.isSubSp_union (Work.Engulf.Chain.isSubSp_mono SF.sub I.subF) SF.subG
      disjF := ?_
      dimF := ?_
      cont := SF.cont
      frz := fun x hx => (SF.frz (Or.inl hx)).trans (I.frz hx)
      near := ?_
      tame := by simpa [Set.union_assoc] using SF.tame
      supp := SF.supp
      Xkc := hX₁closed
      XkX := hX₁X
      eng := by simpa [Set.union_assoc] using SF.eng
      cover := ?_ }
  · intro s hs
    rcases SF.newG s hs with h1 | h2
    · rcases I.newF s h1 with h3 | h4
      · exact Or.inl h3
      · exact Or.inr (Subset.trans h4 Set.subset_union_left)
    · exact Or.inr (Subset.trans h2 Set.subset_union_right)
  · have hGempty : G ∩ Γ.space = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxG, hxΓ⟩
      exact Set.disjoint_left.mp SF.disjG hxG (Work.Engulf.Chain.space_mono I.sub hxΓ)
    have hFd := I.disjF
    rw [Set.disjoint_iff_inter_eq_empty] at hFd ⊢
    rw [Set.union_inter_distrib_right, hFd, hGempty, Set.union_empty]
  · intro s hs hsFG
    rcases SF.newG s hs with h1 | h2
    · have hsub : PL.simp s ⊆ F := by
        intro y hy
        rcases hsFG hy with h | h
        · exact h
        · have hmem : y ∈ G ∩ Γk.space :=
            ⟨h, Geometry.SimplicialComplex.convexHull_subset_space h1 hy⟩
          exact absurd hmem (fun hc => Set.disjoint_left.mp SF.disjG hc.1 hc.2)
      exact I.dimF s h1 hsub
    · exact SF.dimG s hs h2
  · intro x hx
    have hxΓk : x ∈ Γk.space := Work.Engulf.Chain.space_mono I.sub hx
    have hmain : dist (gF x) (f x) < (pieces.length : ℝ) * η + ε * (1 - (1 / 2 : ℝ) ^ (k + 1)) := by
      have h2 := SF.near x hxΓk
      have h3 := I.near x hx
      have h4 := dist_triangle (gF x) (g x) (f x)
      linarith
    have hlen : (pieces.length : ℝ) * η + ε * (1 - (1 / 2 : ℝ) ^ (k + 1))
        ≤ ε * (1 - (1 / 2 : ℝ) ^ (k + 2)) := by
      have hηval : ((pieces.length : ℝ) + 1) * η = ε * (1 / 2 : ℝ) ^ (k + 2) := by
        rw [hηdef]
        field_simp
      have hle : (pieces.length : ℝ) * η ≤ ((pieces.length : ℝ) + 1) * η := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hηpos)
        linarith
      have hfac : (1 : ℝ) - (1 / 2 : ℝ) ^ (k + 2)
          = (1 - (1 / 2 : ℝ) ^ (k + 1)) + (1 / 2 : ℝ) ^ (k + 2) := by
        have : (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) := by
          rw [pow_succ]
        rw [this]; ring
      rw [hfac]
      linarith [hηval, hle]
    exact lt_of_lt_of_le hmain hlen
  · intro x hx
    rcases I.cover hx with (h1 | h2) | h3
    · exact Or.inl (Or.inl (Or.inl h1))
    · obtain ⟨y, hyF, hyx⟩ := h2
      exact Or.inl (Or.inr ⟨y, Or.inl hyF, by rw [SF.frz (Or.inr hyF)]; exact hyx⟩)
    · obtain ⟨i, hiIco, hmem⟩ := mem_iUnion₂.1 h3
      obtain ⟨hi', hxcl⟩ := mem_iUnion.1 hmem
      rw [Finset.mem_Ico] at hiIco
      by_cases hik : i = k
      · subst hik
        have hxψ : x ∈ ψ.toFun '' PL.closedCube (1 / 2 : ℝ) := by rw [hψdef]; exact hxcl
        rcases hXkcover ⟨hx, hxψ⟩ with h1 | h2
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Set.image_mono Set.subset_union_right h2))
      · refine Or.inr (mem_iUnion₂.2 ⟨i, ?_, ?_⟩)
        · rw [Finset.mem_Ico]
          exact ⟨by omega, hiIco.2⟩
        · exact mem_iUnion.2 ⟨hi', hxcl⟩

end Work.Engulf.E1B
