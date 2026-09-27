import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Chain.exists_generic_apex
import Submission.Work.Engulf.Chain.exists_affineMap_fixing
import Submission.Work.Engulf.Chain.coneCx_exists
import Submission.Work.Engulf.Chain.exists_cone_extension_fin
import Submission.Work.Engulf.Chain.cone_l7hyp

/-!
# Newman §12: `L7 q ⇒ C1 (q+1)` with the universes identified

The cone step of Newman's Lemma 7 (see `Submission/Work/NOTES_LEAD_poincare_engulf.md` §12),
stated with a *single* universe parameter, exactly as in the lead's design file
`Submission/Work/Engulf/Skeleton.lean` (`theorem E3 (n p q : ℕ) (h7 : L7.{u} n p q) :
C1.{u} n p (q + 1)`).

**Why the universes must be identified.**  `PL.Cx`, `Work.Engulf.Cfg`, … are universe free, but
`Work.Engulf.ToolsAll n`, `Work.Engulf.L7 n p q` and `Work.Engulf.C1 n p k` each carry a universe
parameter (the universe of the auxiliary types `ι`/`M` that the other areas' forms and the
statement quantify over).  Writing the three occurrences without an explicit universe makes Lean
elaborate them with three *independent* universe metavariables, which are then generalised into
three independent universe *parameters* `u₁`, `u₂`, `u₃` of the declaration; the resulting
statement is not provable from its hypothesis, since the goal `C1.{u₃} n p (q+1)` quantifies over
`M : Type u₃` whereas `h7 : L7.{u₂} n p q` can only be applied to an `M : Type u₂` (Lean reports
`Application type mismatch: The argument M has type Type u_3 … but is expected to have type
Type u_2`), and there is no relation between `u₂` and `u₃`.  This is precisely the defect the lead
records for `E1` in `Submission/Work/NOTES_LEAD_poincare_E1fix.md`: "statement unchanged. NB:
universes must match: `{M : Type u}` and `B.{u}` (the draft in `_o/stmts.lean` has `M : Type*` and
an unannotated `B`, so `hB` cannot be applied at `M`)."

The corrected statement is `Work.Engulf.Chain.C1_of_L7` below; `Work.Engulf.Chain.E3`, stated in
`Submission/Work/Engulf/Chain/E3.lean`, is *that* result (the requested statement with the universes
identified).

Built on five auxiliary lemmas proved in this directory:

* `Work.Engulf.Chain.exists_generic_apex`       — a generic apex `a` for the cone;
* `Work.Engulf.Chain.coneCx_exists`             — the cone complex `Γ' = Γ ∪ a ∗ σ`;
* `Work.Engulf.Chain.exists_affineMap_fixing`   — the affine retraction `coneBd a σ → simp σ`;
* `Work.Engulf.Chain.exists_cone_extension_fin` — extending `f` over the cone;
* `Work.Engulf.Chain.cone_l7hyp`                — the `L7Hyp` verification for the cone data.

The definitions `coneFaces`, `coneBd`, `coneK` live in
`Submission/Work/Engulf/Chain/ConeDefs.lean`.
-/

open Set Metric PL

namespace Work.Engulf.Chain

universe u

/-- helper: the space of the cone complex -/
theorem E3_coneCx_space {N : ℕ} {Γ : Cx N} {σ : Finset (E N)} {a : E N} {Γ' : Cx N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (hσ : σ ∈ Γ.faces) :
    Γ'.space = Γ.space ∪ simp (insert a σ) := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun t ht => ?_
    rw [hΓ'] at ht
    rcases ht with ht | ⟨s, hs_or, hsub, rfl⟩
    · exact Set.subset_union_of_subset_left
        (Geometry.SimplicialComplex.convexHull_subset_space ht) _
    · rcases hs_or with hs | hemp
      · refine Set.subset_union_of_subset_right (convexHull_mono ?_) _
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsub hy)
      · subst hemp
        refine Set.subset_union_of_subset_right (fun x hx => ?_) _
        have hx' : x = a := by simpa using hx
        rw [hx']
        exact subset_convexHull ℝ _ (Finset.mem_insert_self a σ)
  · refine Set.union_subset ?_ ?_
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨s, by rw [hΓ']; exact Or.inl hs, hsx⟩
    · intro x hx
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨insert a σ, by rw [hΓ']; exact Or.inr ⟨σ, Or.inl hσ, Subset.rfl, rfl⟩, hx⟩

/-- **`C1 (q+1)` from `L7 q` (Newman §12, the cone step)**: if the join lemma `L7` holds for `q`
(at the universe `u`), then `C1` holds with `σ.card = q + 1`.

Choose a generic apex `a` outside `⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)` (using `Cfg.room : 2p+4 ≤ N`
and `Cfg.dimΓ`, via `Work.Engulf.Chain.exists_generic_apex`), form the cone complex
`Γ' = Γ ∪ {insert a s | s ∈ Γ.faces, s ⊆ σ}` (`coneCx_exists`), extend `f` first over `aσ̇` into `V`
and then over `aσ` into `M` (`exists_cone_extension_fin`, using `Amb.connV`, `Amb.connM` and
`Tools.simplexBall`), and apply `L7 q` with `τ₀ = {a}`, `τ₁ = σ` and
`K := ⋃{simp s | s ∈ Γ.faces, simp s ⊆ H, s ≠ σ} ∪ aσ̇` (`cone_l7hyp` supplies the `L7Hyp`
verification). -/
theorem C1_of_L7 (n p q : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (h7 : Work.Engulf.L7.{u} n p q) :
    Work.Engulf.C1.{u} n p (q + 1) := by
  intro M _ V X N Γ H L f σ hAmb hCfg hX hσ hcard hσH hprinc hoth hdisj hclean ε hε
  have hfin : Γ.faces.Finite := hCfg.fin
  have hdimΓ : DimLE Γ (p + 1) := hCfg.dimΓ
  have hσcard : σ.card ≤ p + 1 := hCfg.dimH σ hσ hσH
  have hq : q ≤ p := by omega
  obtain ⟨a, ha⟩ := exists_generic_apex Γ σ hσ hfin hσcard hCfg.room hdimΓ
  have hσsub : (σ : Set (E N)) ⊆ Γ.space := by
    intro v hv
    rw [Geometry.SimplicialComplex.mem_space_iff]
    exact ⟨σ, hσ, subset_convexHull ℝ _ hv⟩
  have ha_space : a ∉ Γ.space := by
    intro h
    obtain ⟨s, hs, hsx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp h
    have h1 : a ∈ (affineSpan ℝ (s : Set (E N)) : Set (E N)) := PL.simp_subset_affineSpan s hsx
    have h2 : (affineSpan ℝ (s : Set (E N)) : Set (E N)) ⊆
        (affineSpan ℝ (((σ ∪ s : Finset (E N)) : Set (E N))) : Set (E N)) :=
      affineSpan_mono ℝ (by intro y hy; exact Finset.mem_union_right σ hy)
    exact ha s hs (h2 h1)
  have ha_σ : a ∉ σ := fun h => ha_space (hσsub h)
  obtain ⟨Γ', hΓ'⟩ := coneCx_exists Γ σ a hσ ha
  have hsub : Γ.faces ⊆ Γ'.faces := by rw [hΓ']; exact Set.subset_union_left
  have hspace_sub : Γ.space ⊆ Γ'.space := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hsub hs, hsx⟩
  have hσne : σ.Nonempty := Γ.nonempty_of_mem_faces hσ
  have hind : AffineIndependent ℝ ((↑) : σ → E N) := Γ.indep hσ
  have ha_span : a ∉ (affineSpan ℝ (σ : Set (E N)) : Set (E N)) := by
    have h := ha σ hσ
    rwa [Finset.union_self] at h
  obtain ⟨A, hAfix, hAa⟩ := exists_affineMap_fixing σ a hσne hind ha_span
  have hbd : f '' (⋃ v ∈ σ, simp (σ.erase v)) ⊆ V := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
    rcases Finset.eq_empty_or_nonempty (σ.erase v) with hemp | hne
    · rw [hemp, simp_empty] at hyv; exact absurd hyv (Set.notMem_empty y)
    · exact hoth (σ.erase v) (Γ.down_closed hσ (Finset.erase_subset _ _) hne)
        ((simp_mono (Finset.erase_subset _ _)).trans hσH)
        (fun heq => Finset.notMem_erase v σ (heq.symm ▸ hv)) ⟨y, hyv, rfl⟩
  have hMconn : ∀ j, j + 2 ≤ σ.card + 1 → ExtOverDisc M j := by
    intro j hj
    exact hAmb.connM j (by omega)
  have hVconn : ∀ j, j + 2 ≤ σ.card → ExtOverDisc V j := by
    intro j hj
    exact hAmb.connV j (by omega)
  obtain ⟨f₁, hf₁c, hf₁f, hf₁V⟩ := exists_cone_extension_fin (T N).simplexBall V Γ σ a f A hfin hσ ha
    hCfg.cont hbd hAfix hAa hAmb.Vne hMconn hVconn
  have hf₁c' : ContinuousOn f₁ Γ'.space := by
    rw [E3_coneCx_space hΓ' hσ]; exact hf₁c
  have hL7 := cone_l7hyp hAmb hCfg hX hσ hcard hq hσH hprinc hoth hdisj hclean ha_space hΓ'
    hf₁c' hf₁f hf₁V
  obtain ⟨g, hgc, hgf, hgd, h, hh, hheng⟩ :=
    h7 M V X N Γ' (coneK Γ H σ a) L f₁ {a} σ hAmb hL7 ε hε
  have htop_le : simp σ ⊆ topOf ({a} : Finset (E N)) σ := by
    intro x hx
    refine mem_iUnion₂.mpr ⟨a, Finset.mem_singleton_self a, ?_⟩
    rwa [Finset.singleton_union, Finset.erase_insert ha_σ]
  have hHK : H ⊆ coneK Γ H σ a ∪ topOf ({a} : Finset (E N)) σ := by
    intro x hx
    obtain ⟨s, hs, hxs, hsub⟩ := hCfg.subH.2 x hx
    by_cases hseq : s = σ
    · exact Or.inr (htop_le (hseq ▸ hxs))
    · refine Or.inl (Or.inl ?_)
      refine mem_iUnion₂.mpr ⟨s, ?_, hxs⟩
      exact ⟨hs, hsub, hseq⟩
  refine ⟨g, hgc.mono hspace_sub, ?_, ?_, h, hh, ?_⟩
  · intro x hx
    rw [hgf hx, hf₁f (hCfg.subL.subset_space hx)]
  · intro x hx
    have h1 := hgd x (hspace_sub hx)
    rwa [hf₁f hx] at h1
  · rintro x (hx | hx)
    · exact hheng (Or.inl hx)
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hheng (Or.inr ⟨y, hHK hy, rfl⟩)

end Work.Engulf.Chain
