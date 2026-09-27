import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Engulf.Chain.Sub.Basic
import Submission.Work.Engulf.Chain.Sub.RelInt
import Submission.Work.Engulf.Chain.Sub.Skel
import Submission.Work.Engulf.Chain.Sub.Help
import Submission.Work.Engulf.Chain.Sub.Transfer
import Submission.Work.Engulf.Chain.Sub.Transfer2
import Submission.Work.Engulf.Chain.Sub.exists_coarse_face_superset
import Submission.Work.Engulf.Chain.Sub.exists_chart_cover_margin
import Submission.Work.Engulf.Chain.Sub.boundary_subset_skel

/-!
# `Work.Engulf.Chain.E5` (Newman §15)

`L7c q ⇒ L7 q`: the join simplex of Lemma 7 need not lie in a single smoothing chart.  The
simplex is shelled by the fine top faces `ord` of `SubdivTools.shell`, each lying in one smoothing
chart, and `L7c` is applied once per shelling step, pushing `V` along by the homeomorphisms
produced.  See `Submission/Work/NOTES_LEAD_poincare_engulf.md` §15.

**Universes.**  `Work.Engulf.ToolsAll`, `Work.Engulf.L7c` and `Work.Engulf.L7` each carry a
universe parameter.  Written without explicit universes, Lean elaborates them with three
independent universe metavariables, which are then generalised into three independent universe
*parameters* of the declaration; the resulting statement is not provable from its hypothesis,
since the goal `L7.{u₃} n p q` quantifies over `M : Type u₃` whereas `hc : L7c.{u₂} n p q` can
only be applied to an `M : Type u₂`, and there is no relation between `u₂` and `u₃` (Lean
reports `Application type mismatch: The argument M has type Type u_3 … but is expected to have
type Type u_2`).  The universes are therefore identified, exactly as in the lead's design file
`Submission/Work/Engulf/Skeleton.lean` (`theorem E5 (n p q : ℕ) (hc : L7c.{u} n p q) :
L7.{u} n p q`); this is the same correction the workspace applies to `E1`, `E2` and `E3` (see
`Submission/Work/Engulf/Chain/C1_of_L7.lean` and `NOTES_LEAD_poincare_E1fix.md`).  Nothing else
about the statement is changed.
-/

open Set Metric PL

set_option maxHeartbeats 1000000

namespace Work.Engulf.Chain

universe u

/-- Invariant of the outer shelling loop of `E5`. -/
structure Outer {M : Type*} [MetricSpace M] (N : ℕ) (Γ₁ : Cx N) (K : Set (E N))
    (L : Set (E N)) (f : E N → M) (ord : List (Finset (E N))) (η : ℝ)
    (V X : Set M) (i : ℕ) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le : i ≤ ord.length
  cont : ContinuousOn g Γ₁.space
  frz : EqOn g f L
  near : ∀ x ∈ Γ₁.space, dist (g x) (f x) < (i + 1) * η
  supp : PL.CSupp h univ
  eng : X ∪ g '' (K ∪ skel ord i) ⊆ h '' V

/-- **`E5` = Newman §15** (general case): `L7c q ⇒ L7 q`, removing the hypothesis that the join simplex lies in a single smoothing chart.  Cover the compact set `f '' simp (τ₀ ∪ τ₁)` by finitely many smoothing charts `ψ_j`; pick a Lebesgue number `λ > 0`; subdivide `Γ` so finely that every shelled `(q+1)`-face has `f`-image of diameter `< λ` (so it lies in one chart); let `ord` be the shelling order of `SubdivTools.shell` for the join `τ₀ ∪ τ₁` with floor `floorOf τ₀ τ₁`, and run the outer loop over `ord`, each step an instance of `L7c q` on `ord[i]` with `K' := K ∪ (q-skeleton so far)`.  Invariant: `Work.Engulf.InnerInv` with `Rc = ∅`, plus a chart-membership clause.  Note: `Cfg.tame`/`SmoothChart` transfer to the finely subdivided complex (aux `smoothChart_subdiv`), which is what makes the chart hypothesis of `L7c` available at each step. -/
theorem E5 (n p q : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (hc : Work.Engulf.L7c.{u} n p q) :
    Work.Engulf.L7.{u} n p q := by
  intro M _ V X N Γ K L f τ₀ τ₁ A hL7 ε hε
  classical
  set Δ := τ₀ ∪ τ₁ with hΔ
  have hmem : Δ ∈ Γ.faces := hΔ ▸ hL7.mem
  have hcardΔ : Δ.card = q + 2 := hΔ ▸ hL7.card
  have hneΔ : Δ.Nonempty := Finset.Nonempty.mono Finset.subset_union_left hL7.ne₀
  have hsimpΔ : PL.simp Δ ⊆ Γ.space :=
    Geometry.SimplicialComplex.convexHull_subset_space hmem
  -- ## 1. the finite chart cover and the Lebesgue number
  obtain ⟨m, hm, ψ, y, ρ, hρ, hsmooth, hcover, hball⟩ :=
    Work.Engulf.Chain.Sub.exists_chart_cover_margin (S := f '' PL.simp Δ)
      ((isCompact_simp Δ).image_of_continuousOn (hL7.cfg.cont.mono hsimpΔ))
      ((simp_nonempty hneΔ).image f) hL7.cfg.tame
  set lam := (Finset.univ : Finset (Fin m)).inf' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ ρ with hlamdef
  have hlamp : 0 < lam := by
    rw [hlamdef]
    exact (Finset.lt_inf'_iff _).2 fun j _ => hρ j
  have hlamle : ∀ j, lam ≤ ρ j := by
    intro j
    rw [hlamdef]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  -- ## 2. uniform continuity and the fine subdivision
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_radius hL7.cfg.fin hL7.cfg.cont (by linarith : (0:ℝ) < lam / 4)
  obtain ⟨r, hr⟩ := (T N).subdiv.fine Γ hL7.cfg.fin (δ / 2) (by linarith)
  set Γ₁ := (T N).subdiv.sdIter r Γ hL7.cfg.fin with hΓ₁def
  have hfin₁ : Γ₁.faces.Finite := by rw [hΓ₁def]; exact (T N).subdiv.fin r Γ hL7.cfg.fin
  have hsubΓ₁ : PL.Subdivides Γ₁ Γ := by rw [hΓ₁def]; exact (T N).subdiv.subdiv r Γ hL7.cfg.fin
  have hspace : Γ₁.space = Γ.space := hsubΓ₁.1
  have hmesh : PL.MeshLT Γ₁ (δ / 2) := by rw [hΓ₁def]; exact hr r le_rfl
  -- ## 3. the shelling
  have hτ₁sub : τ₁ ⊂ Δ := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_right, ?_⟩
    intro heq
    obtain ⟨a, ha⟩ := hL7.ne₀
    have : a ∈ τ₁ := by rw [heq]; exact Finset.mem_union_left _ ha
    exact (Finset.disjoint_left.1 hL7.disj) ha this
  obtain ⟨ord, hnodup, hfaces, hcov, hshell⟩ :=
    (T N).subdiv.shell r Γ hL7.cfg.fin Δ τ₁ hmem hL7.ne₁ hτ₁sub
  have hordfaces : ∀ j (hj : j < ord.length), ord.get ⟨j, hj⟩ ∈ Γ₁.faces :=
    fun j hj => (hfaces _ (List.get_mem ord ⟨j, hj⟩)).1
  have hordcards : ∀ j (hj : j < ord.length), (ord.get ⟨j, hj⟩).card = Δ.card :=
    fun j hj => (hfaces _ (List.get_mem ord ⟨j, hj⟩)).2.1
  -- the split of each shelling simplex into the floor side and the top side
  have hsplit : ∀ i : Fin ord.length, ∃ τ₁' : Finset (E N), τ₁'.Nonempty ∧ τ₁' ⊂ ord.get i ∧
      PL.simp (ord.get i) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪ covOrd ord i.1)
        = ⋃ w ∈ τ₁', PL.simp ((ord.get i).erase w) := by
    intro i
    obtain ⟨τ₁', hne, hsub, heq⟩ := hshell i.1 i.2
    rw [shellUnion_eq_covOrd] at heq
    exact ⟨τ₁', hne, hsub, heq⟩
  choose τ₁s hne_s hsub_s heq_s using hsplit
  -- ## 4. the budget
  set η := min ε (lam / 4) / (2 * ((ord.length : ℝ) + 1)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    apply div_pos (lt_min hε (by linarith))
    positivity
  have hden : (0:ℝ) < 2 * ((ord.length : ℝ) + 1) := by positivity
  have hratio : (ord.length : ℝ) * η
      = ((ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1))) * min ε (lam / 4) := by
    rw [hηdef, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hhalf : (ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1)) < 1 := by
    rw [div_lt_one hden]
    linarith
  have hηε : (ord.length : ℝ) * η < ε := by
    rw [hratio]
    calc ((ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1))) * min ε (lam / 4)
        ≤ ((ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1))) * ε := by
          exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ < 1 * ε := mul_lt_mul_of_pos_right hhalf hε
      _ = ε := one_mul _
  have hηlam : (ord.length : ℝ) * η < lam / 4 := by
    rw [hratio]
    calc ((ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1))) * min ε (lam / 4)
        ≤ ((ord.length : ℝ) / (2 * ((ord.length : ℝ) + 1))) * (lam / 4) := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ < 1 * (lam / 4) := mul_lt_mul_of_pos_right hhalf (by linarith)
      _ = lam / 4 := one_mul _
  have hbudget : ((ord.length : ℝ) + 1) * η = min ε (lam / 4) / 2 := by
    rw [hηdef]
    field_simp
  have hbudgetε : ((ord.length : ℝ) + 1) * η < ε := by
    rw [hbudget]; linarith [min_le_left ε (lam / 4), hε]
  have hbudgetlam : ((ord.length : ℝ) + 1) * η < lam / 4 := by
    rw [hbudget]; linarith [min_le_right ε (lam / 4), hlamp]
  -- ## 5. the outer loop
  have key : ∀ i (hi : i < ord.length),
      (∃ g : E N → M, ∃ h : M ≃ₜ M, Outer N Γ₁ K L f ord η V X i g h) →
      ∃ g : E N → M, ∃ h : M ≃ₜ M, Outer N Γ₁ K L f ord η V X (i + 1) g h := by
    intro i hi prev
    obtain ⟨g, h, hg⟩ := prev
    set σ := ord.get ⟨i, hi⟩ with hσdef
    set τ₁' := τ₁s ⟨i, hi⟩ with hτ₁'def
    set τ₀' := σ \ τ₁' with hτ₀'def
    set K' := K ∪ skel ord i with hK'def
    set V' := h '' V with hV'def
    have hget : ord.getD i ∅ = σ := by
      rw [hσdef]
      exact List.getD_eq_get ord ∅ ⟨i, hi⟩
    have hσface : σ ∈ Γ₁.faces := hordfaces i hi
    have hσcard : σ.card = Δ.card := hordcards i hi
    have hsimpσ : PL.simp σ ⊆ PL.simp Δ := (hfaces _ (List.get_mem ord ⟨i, hi⟩)).2.2
    have hsimpσΓ : PL.simp σ ⊆ Γ.space := hsimpσ.trans hsimpΔ
    have hne' : τ₁'.Nonempty := hne_s ⟨i, hi⟩
    have hsub' : τ₁' ⊂ σ := by rw [hσdef]; exact hsub_s ⟨i, hi⟩
    have hshell' : PL.simp σ ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪ covOrd ord i)
        = ⋃ w ∈ τ₁', PL.simp (σ.erase w) := by
      rw [hσdef]; exact heq_s ⟨i, hi⟩
    have hτ_union : τ₀' ∪ τ₁' = σ := by
      rw [hτ₀'def]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨hx, -⟩ | hx)
        · exact hx
        · exact hsub'.1 hx
      · intro hx
        by_cases hxt : x ∈ τ₁'
        · exact Or.inr hxt
        · exact Or.inl ⟨hx, hxt⟩
    have hne₀' : τ₀'.Nonempty := by
      rw [hτ₀'def]
      obtain ⟨a, ha, ha'⟩ := Finset.exists_of_ssubset hsub'
      exact ⟨a, Finset.mem_sdiff.mpr ⟨ha, ha'⟩⟩
    have hσq : σ.card = q + 2 := by rw [hσcard, hcardΔ]
    have htop_eq' : Work.Engulf.topOf τ₀' τ₁' = ⋃ w ∈ τ₀', PL.simp (σ.erase w) := by
      rw [Work.Engulf.topOf, hτ_union]
    have htopIsSub : Work.Engulf.IsSubSp Γ₁ (Work.Engulf.topOf τ₀' τ₁') := by
      have h2 : 2 ≤ σ.card := by omega
      rw [htop_eq']
      exact isSubSp_iUnion_erase_of_subset hσface
        (Finset.subset_union_left.trans hτ_union.le) h2
    have hsubK' : Work.Engulf.IsSubSp Γ₁ K' := by
      rw [hK'def]
      exact isSubSp_union (by rw [hΓ₁def]; exact (T N).subdiv.subsp r Γ hL7.cfg.fin K hL7.subK)
        (isSubSp_skel hordfaces i)
    have hK'compact : IsCompact K' := isCompact_of_isSubSp hfin₁ hsubK'
    have htop_compact : IsCompact (Work.Engulf.topOf τ₀' τ₁') := by
      rw [Work.Engulf.topOf]
      exact Finset.isCompact_biUnion τ₀' fun w _ => isCompact_simp ((τ₀' ∪ τ₁').erase w)
    have htop_space : (Work.Engulf.topOf τ₀' τ₁') ⊆ Γ₁.space := by
      rw [Work.Engulf.topOf]
      intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨w, hw, hzw⟩ := hz
      have hzw' : z ∈ PL.simp (σ.erase w) := by rw [← hτ_union]; exact hzw
      have hwσ : w ∈ σ := by rw [← hτ_union]; exact Finset.mem_union_left _ hw
      have hne : (σ.erase w).Nonempty := by
        rw [← Finset.card_pos]
        have h1 := Finset.card_erase_of_mem hwσ
        omega
      exact Geometry.SimplicialComplex.convexHull_subset_space
        (Γ₁.down_closed hσface (Finset.erase_subset w σ) hne) hzw'
    have hskelΔ : skel ord i ⊆ PL.simp Δ := by
      refine (skel_subset_covOrd ord i).trans ?_
      intro z hz
      obtain ⟨j, hj, hzj⟩ := mem_covOrd hz
      have hjl : j < ord.length := by omega
      rw [List.getD_eq_get ord ∅ ⟨j, hjl⟩] at hzj
      exact (hfaces _ (List.get_mem ord ⟨j, hjl⟩)).2.2 hzj
    have hmeetK' : K' ∩ PL.simp σ = Work.Engulf.floorOf τ₀' τ₁' := by
      rw [hK'def]
      rw [meet_skel (Γ₁ := Γ₁) (K := K) (Δ := Δ) (σ := σ) (τ₁' := τ₁') (ord := ord) (i := i)
        (τ₀ := τ₀) (τ₁ := τ₁) hget hnodup hi hordfaces hordcards hσcard hsimpσ hL7.meetK hshell']
      rw [Work.Engulf.floorOf, hτ_union]
    have hKeng : K ∪ skel ord (i + 1) ⊆ K' ∪ Work.Engulf.topOf τ₀' τ₁' := by
      rw [hK'def, skel_succ, hget]
      intro x hx
      rw [Set.mem_union] at hx
      rcases hx with hxK | hx
      · exact Or.inl (Or.inl hxK)
      · rw [Set.mem_union] at hx
        rcases hx with hxSkel | hxTop
        · exact Or.inl (Or.inr hxSkel)
        · rw [mem_iUnion₂_erase] at hxTop
          obtain ⟨w, hw, hxw⟩ := hxTop
          have hw' : w ∈ τ₀' ∪ τ₁' := by rw [hτ_union]; exact hw
          rcases Finset.mem_union.1 hw' with hw₀ | hw₁
          · refine Or.inr ?_
            rw [htop_eq']
            exact Set.mem_iUnion₂.2 ⟨w, hw₀, hxw⟩
          · refine Or.inl ?_
            have hfloor : x ∈ Work.Engulf.floorOf τ₀' τ₁' := by
              rw [Work.Engulf.floorOf, hτ_union]
              exact Set.mem_iUnion₂.2 ⟨w, hw₁, hxw⟩
            rw [← hmeetK'] at hfloor
            exact hfloor.1
    -- the chart containing the image of the shelled simplex
    have hchart : ∃ j : Fin m, g '' PL.simp σ ⊆ (ψ j).toFun '' PL.openCube (1 / 2) := by
      obtain ⟨v₀, hv₀⟩ := Γ₁.nonempty_of_mem_faces hσface
      have hv₀Δ : v₀ ∈ PL.simp Δ := hsimpσ (subset_simp hv₀)
      have hv₀S : f v₀ ∈ f '' PL.simp Δ := ⟨v₀, hv₀Δ, rfl⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover hv₀S)
      refine ⟨j, ?_⟩
      rintro z ⟨x, hx, rfl⟩
      refine hball j ?_
      have hxΓ : x ∈ Γ₁.space := (Geometry.SimplicialComplex.convexHull_subset_space hσface) hx
      have h1 : dist (g x) (f x) < lam / 4 := by
        have h2 := hg.near x hxΓ
        have h3 : ((i : ℝ) + 1) * η < lam / 4 := by
          have his : (i : ℝ) + 1 ≤ (ord.length : ℝ) + 1 := by
            have h4 : (i : ℝ) ≤ (ord.length : ℝ) := by exact_mod_cast Nat.le_of_lt hi
            linarith
          linarith [mul_le_mul_of_nonneg_right his (le_of_lt hηpos), hbudgetlam]
        linarith
      have h2 : dist (f x) (f v₀) < lam / 4 := by
        have hmeshσ : ∀ v ∈ σ, ∀ w ∈ σ, dist v w ≤ δ / 2 :=
          fun v hv w hw => le_of_lt (hmesh σ hσface v hv w hw)
        have hdx : dist x v₀ ≤ δ / 2 := dist_le_of_mem_simp hv₀ hmeshσ hx
        exact hδ x (hspace ▸ hxΓ) v₀
          (hspace ▸ (Geometry.SimplicialComplex.convexHull_subset_space hσface) (subset_simp hv₀))
          (by linarith)
      have h3 : dist (f v₀) (y j) < ρ j := hj
      have h4 : lam ≤ ρ j := hlamle j
      calc dist (g x) (y j) ≤ dist (g x) (f x) + dist (f x) (y j) := dist_triangle _ _ _
        _ ≤ dist (g x) (f x) + (dist (f x) (f v₀) + dist (f v₀) (y j)) := by
            linarith [dist_triangle (f x) (f v₀) (y j)]
        _ < lam / 4 + (lam / 4 + ρ j) := by linarith
        _ < 2 * ρ j := by linarith
    obtain ⟨j, hjchart⟩ := hchart
    -- the pushed configuration
    have hEngK' : X ∪ g '' K' ⊆ V' := by rw [hV'def]; exact hg.eng
    have hL7' : Work.Engulf.L7Hyp n p q V' X Γ₁ K' L g τ₀' τ₁' := {
      cfg := {
        fin := hfin₁
        dimΓ := by rw [hΓ₁def]; exact (T N).subdiv.dimle r Γ hL7.cfg.fin (p + 1) hL7.cfg.dimΓ
        room := hL7.cfg.room
        subH := isSubSp_union hsubK' htopIsSub
        subL := by rw [hΓ₁def]; exact (T N).subdiv.subsp r Γ hL7.cfg.fin L hL7.cfg.subL
        dimH := by
          intro s hs hsub
          have hsub1 : PL.simp s ⊆ K ∪ skel ord i ∪ ⋃ w ∈ τ₀', PL.simp (σ.erase w) := by
            rw [hK'def, htop_eq'] at hsub
            exact hsub
          have hbound : ∀ t ∈ Γ.faces, PL.simp t ⊆ K → t.card ≤ p + 1 := by
            intro t ht htK
            exact hL7.cfg.dimH t ht fun x hx => Or.inl (htK hx)
          exact card_le_of_simp_subset_loop (Γ := Γ) (Γ₁ := Γ₁) (K := K) (p := p) (q := q)
            (ord := ord) (i := i) (σ := σ) (τ := τ₀') (s := s) hsubΓ₁ hL7.subK hbound
            (Nat.succ_le_succ hL7.hq) (le_of_lt hi) hordfaces
            (fun j hj => by rw [hordcards j hj, hcardΔ])
            (Finset.subset_union_left.trans hτ_union.le) hσq hσface hs hsub1
        cont := hg.cont
        Xc := hL7.cfg.Xc
        cpt := isCompact_sdiff_of_engulfs hfin₁ hL7.cfg.Xc hg.cont hsubK' htop_compact
          htop_space (h.isOpenMap V A.Vo) hEngK'
        tame := by
          refine tame_of_eqOn ?_ hg.frz
          intro x
          obtain ⟨ψx, hx, hscx⟩ := hL7.cfg.tame x
          exact ⟨ψx, hx, smoothChart_subdiv hsubΓ₁ hL7.cfg.subL hscx⟩
        ov := by
          refine ⟨K' ∩ L, ?_, ?_, ?_, ?_⟩
          · have hLfine : Work.Engulf.IsSubSp Γ₁ L := by
              rw [hΓ₁def]
              exact (T N).subdiv.subsp r Γ hL7.cfg.fin L hL7.cfg.subL
            exact hK'compact.of_isClosed_subset
               ((isClosed_of_isSubSp hfin₁ hsubK').inter (isClosed_of_isSubSp hfin₁ hLfine))
               Set.inter_subset_left
          · exact ((Set.image_mono (Set.inter_subset_left : K' ∩ L ⊆ K')).trans
              Set.subset_union_right).trans hg.eng
          · rintro x hxmem y hymem heq hne
            obtain ⟨hx_or, hxL⟩ := hxmem
            obtain ⟨hy_or, hyL⟩ := hymem
            rw [hg.frz hxL, hg.frz hyL] at heq
            rcases hx_or with hxK' | hxTop
            · exact ⟨hxK', hxL⟩
            · exfalso
              have hxσ : x ∈ PL.simp σ := by
                rw [htop_eq'] at hxTop
                obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hxTop
                exact simp_mono (Finset.erase_subset w σ) hxw
              have hyΔ : y ∈ (K ∪ PL.simp Δ) ∩ L := by
                refine ⟨?_, hyL⟩
                rcases hy_or with hyK' | hyTop
                · rcases hyK' with hyK | hySkel
                  · exact Or.inl hyK
                  · exact Or.inr (hskelΔ hySkel)
                · rw [htop_eq'] at hyTop
                  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.1 hyTop
                  exact Or.inr (hsimpσ (simp_mono (Finset.erase_subset w σ) hyw))
              exact hne (hL7.clean x ⟨hsimpσ hxσ, hxL⟩ y hyΔ heq)
          · rintro x hxmem hxX
            obtain ⟨hx_or, hxL⟩ := hxmem
            rcases hx_or with hxK' | hxTop
            · exact ⟨hxK', hxL⟩
            · exfalso
              rw [htop_eq'] at hxTop
              obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hxTop
              have hxσ : x ∈ PL.simp σ := simp_mono (Finset.erase_subset w σ) hxw
              have hmem : f x ∈ f '' (L ∩ PL.simp (τ₀ ∪ τ₁)) :=
                ⟨x, ⟨hxL, by rw [← hΔ]; exact hsimpσ hxσ⟩, rfl⟩
              have hX : f x ∈ X := by rw [← hg.frz hxL]; exact hxX
              exact (Set.disjoint_left.1 hL7.offX) hmem hX
      }
      hq := hL7.hq
      mem := by rw [hτ_union]; exact hσface
      ne₀ := hne₀'
      ne₁ := hne'
      disj := by
        rw [Finset.disjoint_left]
        intro a ha ha'
        exact (Finset.mem_sdiff.1 ha).2 ha'
      card := by rw [hτ_union, hσq]
      subK := hsubK'
      meetK := by rw [hτ_union]; exact hmeetK'
      engK := hEngK'
      offX := by
        refine Disjoint.mono_left ?_ hL7.offX
        rintro y ⟨x, hx, rfl⟩
        have hxσ : x ∈ PL.simp σ := by rw [← hτ_union]; exact hx.2
        exact ⟨x, ⟨hx.1, hsimpσ hxσ⟩, by rw [hg.frz hx.1]⟩
      free := by
        obtain ⟨A, hA1, hA2⟩ := hL7.free
        refine ⟨A, hA1, fun x hx => hA2 ⟨hx.1, hsimpσ ?_⟩⟩
        rw [← hτ_union]; exact hx.2
      clean := by
        intro x hx y hy hxy
        have hxσ : x ∈ PL.simp σ := by rw [← hτ_union]; exact hx.1
        have hxΔ : x ∈ PL.simp Δ ∩ L := ⟨hsimpσ hxσ, hx.2⟩
        have hyΔ : y ∈ (K ∪ PL.simp Δ) ∩ L := by
          refine ⟨?_, hy.2⟩
          rcases hy.1 with hyK' | hyTop
          · rcases hyK' with hyK | hySkel
            · exact Or.inl hyK
            · exact Or.inr (hskelΔ hySkel)
          · have hyσ : y ∈ PL.simp σ := by rw [← hτ_union]; exact hyTop
            exact Or.inr (hsimpσ hyσ)
        exact hL7.clean x hxΔ y hyΔ (by rw [← hg.frz hx.2, ← hg.frz hy.2]; exact hxy)
    }
    have hSmoothC : Work.Engulf.SmoothChart p X Γ₁ L g (ψ j) :=
      smoothChart_of_eqOn (smoothChart_subdiv hsubΓ₁ hL7.cfg.subL (hsmooth j)) hg.frz
    obtain ⟨g', hg'cont, hg'frz, hg'near, h', h'supp, h'eng⟩ :=
      hc (M := M) (V := V') (X := X) (N := N) (Γ := Γ₁) (K := K') (L := L) (f := g)
        (τ₀ := τ₀') (τ₁ := τ₁') (ψ := ψ j) (amb_image A h) hL7' hSmoothC
        (by rw [hτ_union]; exact hjchart) η hηpos
    refine ⟨g', h.trans h', Nat.succ_le_of_lt hi, hg'cont, hg'frz.trans hg.frz, ?_,
      CSupp.trans hg.supp h'supp, ?_⟩
    · intro x hx
      have h1 := hg'near x hx
      have h2 := hg.near x hx
      calc dist (g' x) (f x) ≤ dist (g' x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
        _ < η + (↑i + 1) * η := add_lt_add h1 h2
        _ = (↑(i + 1) + 1) * η := by push_cast; ring
    · have himg : h' '' V' = (h.trans h') '' V := by
        rw [hV'def, Set.image_image]
        rfl
      rw [← himg]
      have hsub1 : X ∪ g' '' (K ∪ skel ord (i + 1))
          ⊆ X ∪ g' '' (K' ∪ Work.Engulf.topOf τ₀' τ₁') :=
        Set.union_subset Set.subset_union_left
          ((Set.image_mono hKeng).trans Set.subset_union_right)
      exact hsub1.trans h'eng
  -- ## 6. the loop and the conclusion
  have base : ∃ g : E N → M, ∃ h : M ≃ₜ M, Outer N Γ₁ K L f ord η V X 0 g h := by
    refine ⟨f, Homeomorph.refl M, ?_⟩
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hspace]; exact hL7.cfg.cont
    · intro x hx; rfl
    · intro x hx
      simp only [dist_self, Nat.cast_zero, zero_add, one_mul]
      exact hηpos
    · exact ⟨∅, isCompact_empty, subset_univ _, fun x _ => rfl⟩
    · intro x hx
      rw [skel_zero] at hx
      refine ⟨x, ?_, rfl⟩
      refine hL7.engK ?_
      rcases hx with h | ⟨y, hy, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, by simpa using hy, rfl⟩
  have loop : ∀ i, i ≤ ord.length →
      ∃ g : E N → M, ∃ h : M ≃ₜ M, Outer N Γ₁ K L f ord η V X i g h := by
    intro i
    induction i with
    | zero => intro _; exact base
    | succ i ih =>
      intro hi
      exact key i (Nat.lt_of_succ_le hi) (ih (Nat.le_of_succ_le hi))
  obtain ⟨g, h, hg⟩ := loop ord.length le_rfl
  have htopSkel : Work.Engulf.topOf τ₀ τ₁ ⊆ skel ord ord.length := by
    have h1 : Work.Engulf.topOf τ₀ τ₁ ⊆ ⋃ w ∈ Δ, PL.simp (Δ.erase w) := by
      rw [Work.Engulf.topOf]
      intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨w, hw, hxw⟩ := hx
      exact ⟨w, by rw [hΔ]; exact Finset.mem_union_left _ hw, by rw [hΔ]; exact hxw⟩
    refine h1.trans ?_
    refine (Work.Engulf.Chain.Sub.boundary_subset_skel hsubΓ₁ hmem hfaces hcov).trans ?_
    rw [iUnion_erase_eq_range]
    exact range_erase_subset_skel ord le_rfl
  refine ⟨g, hspace ▸ hg.cont, hg.frz, ?_, h, hg.supp, ?_⟩
  · intro x hx
    have h1 := hg.near x (hspace.symm ▸ hx)
    calc dist (g x) (f x) < ((ord.length : ℝ) + 1) * η := h1
      _ < ε := hbudgetε
  · have hsub : K ∪ Work.Engulf.topOf τ₀ τ₁ ⊆ K ∪ skel ord ord.length := by
      refine Set.union_subset Set.subset_union_left ?_
      exact htopSkel.trans Set.subset_union_right
    refine Set.union_subset ?_ ?_
    · exact (Set.subset_union_left : X ⊆ X ∪ g '' (K ∪ skel ord ord.length)).trans hg.eng
    · exact ((Set.image_mono hsub).trans Set.subset_union_right).trans hg.eng

end Work.Engulf.Chain
