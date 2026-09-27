import Mathlib
import Submission.Work.Cells.Connell.Defs

/-!
# Separating a compact set from a point by an open cell

Let `M` be a compact metric space covered by two open `n`-cells `W₀`, `W₁`, let `q ∉ W₀`
(so `q ∈ W₁`, as `W₀ ∪ W₁ = M`), and let `K ⊆ M` be compact with `q ∉ K`.  Then `K` is
contained in an open `n`-cell `U` with `q ∉ U`.

This is the two-cell step (blueprint `C4`; Newman §16 / Connell) which feeds Brown's
criterion: applied with `K` ranging over the compacts of `M ∖ {q}`, it exhibits a basis of
open cells of `M ∖ {q}`.

## The proof

Choose a homeomorphism `ē : W₁ ≃ₜ ℝⁿ` with `ē q = 0` (compose the given cell homeomorphism
with the translation taking `q` to the origin).  Then

* `W₀ᶜ ⊆ W₁` is compact (as `W₀` is open in the compact `M`), so its `ē`-image is bounded:
  there is `C₀` with `‖y‖ ≤ C₀` whenever `ē.symm y ∈ W₀ᶜ`;
* `K ∩ W₁` is closed in the open cell `W₁` (compactness of `M` and `q ∉ K` are used here),
  so its `ē`-image is a closed subset of `ℝⁿ` avoiding the origin: there is `ε > 0` with
  `ε ≤ ‖y‖` for all `y ∈ ē '' (K ∩ W₁)`.

With `R := max (C₀ + 1) (ε + 1)` (so `0 < ε < R`), radial expansion `hrad ε R` supplies a
homeomorphism `g` of `ℝⁿ` fixing the origin, fixing the complement of the ball of radius
`R + 1`, and pushing everything outside the ball of radius `ε` outside the ball of radius
`R`.  Conjugating `g` by `ē` yields a self-homeomorphism `h` of `W₁` with compact support,
which extends by the identity to a homeomorphism `H` of the whole space (the extension
lemma `exists_homeomorph_extend_of_isCompact` proved below — this is the content of the
hypothesis `PL.ExtHomeoForm`).

Finally `U := H ⁻¹' W₀` is an open cell (a homeomorphic image of `W₀`):

* `q ∉ U`, because `H q = q`;
* `K ⊆ U`: for `x ∈ K ∩ W₁`, if `ē.symm (g (ē x)) ∈ W₀ᶜ` then `g (ē x)` lies in the bounded
  set `ē '' W₀ᶜ`, so `‖ē x‖ < ε`, contradicting `ε ≤ ‖ē x‖`; hence `H x ∈ W₀`.  Points of
  `K ∖ W₁` are already in `W₀` and are fixed by `H`.
-/

open Set Metric

namespace Work.Cells.Connell

/-- Extension of a self-homeomorphism of an open set that is the identity off a compact
subset of it: a homeomorphism of `X` equal to `h` on `O` and to the identity outside `O`. -/
theorem exists_homeomorph_extend_of_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {O : Set X} (hO : IsOpen O) (h : ↥O ≃ₜ ↥O) {C : Set ↥O} (hC : IsCompact C)
    (hid : ∀ x, x ∉ C → h x = x) :
    ∃ H : X ≃ₜ X, (∀ x : ↥O, H (x : X) = (h x : X)) ∧ ∀ x, x ∉ O → H x = x := by
  classical
  have hC'comp : IsCompact (Subtype.val '' C : Set X) := hC.image continuous_subtype_val
  have hC'closed : IsClosed (Subtype.val '' C : Set X) := hC'comp.isClosed
  have hC'sub : (Subtype.val '' C : Set X) ⊆ O := by rintro x ⟨y, -, rfl⟩; exact y.2
  have hidS : ∀ x : ↥O, x ∉ C → h.symm x = x := by
    intro x hx
    rw [h.symm_apply_eq]
    exact (hid x hx).symm
  let F : X → X := fun x => if hx : x ∈ O then (h ⟨x, hx⟩ : X) else x
  let G : X → X := fun x => if hx : x ∈ O then (h.symm ⟨x, hx⟩ : X) else x
  have hFof : ∀ (x : X) (hx : x ∈ O), F x = (h ⟨x, hx⟩ : X) := by
    intro x hx; simp only [F]; exact dite_eq_left hx
  have hFoff : ∀ (x : X), x ∉ O → F x = x := by
    intro x hx; simp only [F]; exact dite_eq_right hx
  have hGof : ∀ (x : X) (hx : x ∈ O), G x = (h.symm ⟨x, hx⟩ : X) := by
    intro x hx; simp only [G]; exact dite_eq_left hx
  have hGoff : ∀ (x : X), x ∉ O → G x = x := by
    intro x hx; simp only [G]; exact dite_eq_right hx
  have hFO : ContinuousOn F O := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : O.domRestrict F = fun y : ↥O => (h y : X) := by
      funext y
      rw [Set.domRestrict_apply, hFof _ y.2]
    rw [heq]
    exact continuous_subtype_val.comp h.continuous
  have hFc : ContinuousOn F (Subtype.val '' C : Set X)ᶜ := by
    apply ContinuousOn.congr continuousOn_id
    intro x hx
    by_cases hxO : x ∈ O
    · rw [hFof x hxO]
      have hxC : (⟨x, hxO⟩ : ↥O) ∉ C := by
        intro hmem; exact hx ⟨⟨x, hxO⟩, hmem, rfl⟩
      rw [show (h ⟨x, hxO⟩ : X) = ((⟨x, hxO⟩ : ↥O) : X) from
        congrArg Subtype.val (hid ⟨x, hxO⟩ hxC)]
      rfl
    · exact hFoff x hxO
  have hGO : ContinuousOn G O := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : O.domRestrict G = fun y : ↥O => (h.symm y : X) := by
      funext y
      rw [Set.domRestrict_apply, hGof _ y.2]
    rw [heq]
    exact continuous_subtype_val.comp h.symm.continuous
  have hGc : ContinuousOn G (Subtype.val '' C : Set X)ᶜ := by
    apply ContinuousOn.congr continuousOn_id
    intro x hx
    by_cases hxO : x ∈ O
    · rw [hGof x hxO]
      have hxC : (⟨x, hxO⟩ : ↥O) ∉ C := by
        intro hmem; exact hx ⟨⟨x, hxO⟩, hmem, rfl⟩
      rw [show (h.symm ⟨x, hxO⟩ : X) = ((⟨x, hxO⟩ : ↥O) : X) from
        congrArg Subtype.val (hidS ⟨x, hxO⟩ hxC)]
      rfl
    · exact hGoff x hxO
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxO : x ∈ O
    · exact (hFO.continuousWithinAt hxO).continuousAt (hO.mem_nhds hxO)
    · have hx' : x ∉ (Subtype.val '' C : Set X) := fun h => hxO (hC'sub h)
      exact (hFc.continuousWithinAt hx').continuousAt (hC'closed.isOpen_compl.mem_nhds hx')
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxO : x ∈ O
    · exact (hGO.continuousWithinAt hxO).continuousAt (hO.mem_nhds hxO)
    · have hx' : x ∉ (Subtype.val '' C : Set X) := fun h => hxO (hC'sub h)
      exact (hGc.continuousWithinAt hx').continuousAt (hC'closed.isOpen_compl.mem_nhds hx')
  have hleft : Function.LeftInverse G F := by
    intro x
    by_cases hxO : x ∈ O
    · rw [hFof x hxO, hGof _ (h ⟨x, hxO⟩).2]
      rw [show (⟨((h ⟨x, hxO⟩ : ↥O) : X), (h ⟨x, hxO⟩).2⟩ : ↥O) = h ⟨x, hxO⟩
        from Subtype.ext rfl]
      rw [h.symm_apply_apply]
    · rw [hFoff x hxO, hGoff x hxO]
  have hright : Function.RightInverse G F := by
    intro x
    by_cases hxO : x ∈ O
    · rw [hGof x hxO, hFof _ (h.symm ⟨x, hxO⟩).2]
      rw [show (⟨((h.symm ⟨x, hxO⟩ : ↥O) : X), (h.symm ⟨x, hxO⟩).2⟩ : ↥O) = h.symm ⟨x, hxO⟩
        from Subtype.ext rfl]
      rw [h.apply_symm_apply]
    · rw [hGoff x hxO, hFoff x hxO]
  refine ⟨{ toFun := F, invFun := G, left_inv := hleft, right_inv := hright,
            continuous_toFun := hFcont, continuous_invFun := hGcont }, ?_, ?_⟩
  · intro x
    change F (x : X) = (h x : X)
    rw [hFof _ x.2]
  · intro x hxO
    change F x = x
    exact hFoff x hxO

/-- The extension hypothesis `PL.ExtHomeoForm` (`C0`) holds. -/
theorem extHomeoForm (n : ℕ) : ExtHomeoForm n :=
  fun _M _ _ _O hO h _C hC hid => exists_homeomorph_extend_of_isCompact hO h hC hid

set_option linter.style.haveILetI false in
theorem exists_openCell_of_compact_subset_compl_point {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] {W₀ W₁ : Set M} (h₀ : PL.IsOpenCell n W₀)
    (h₁ : PL.IsOpenCell n W₁) (hcov : W₀ ∪ W₁ = Set.univ) (q : M) (hq : q ∉ W₀)
    (hrad : RadialExpandForm n) (hext : ExtHomeoForm n) :
    ∀ K : Set M, IsCompact K → q ∉ K →
      ∃ U : Set M, PL.IsOpenCell n U ∧ K ⊆ U ∧ q ∉ U := by
  intro K hKcomp hqK
  classical
  have _hn := hn
  have _hext := hext
  obtain ⟨hW₀open, ⟨e₀⟩⟩ := h₀
  obtain ⟨hW₁open, ⟨e₁⟩⟩ := h₁
  -- `q ∈ W₁`
  have hqW₁ : q ∈ W₁ := by
    have h : q ∈ W₀ ∪ W₁ := by rw [hcov]; exact Set.mem_univ q
    rcases h with h | h
    · exact absurd h hq
    · exact h
  -- `W₀ᶜ ⊆ W₁`
  have hsub : (W₀ᶜ : Set M) ⊆ W₁ := by
    intro x hx
    have h : x ∈ W₀ ∪ W₁ := by rw [hcov]; exact Set.mem_univ x
    rcases h with h | h
    · exact absurd h hx
    · exact h
  let q₁ : ↥W₁ := ⟨q, hqW₁⟩
  let p : PL.E n := e₁ q₁
  -- a chart of `W₁` centred at `q`
  let ē : ↥W₁ ≃ₜ PL.E n := e₁.trans (Homeomorph.subRight p)
  have hēq : ē q₁ = 0 := by
    show e₁ q₁ - p = 0
    rw [show e₁ q₁ = p from rfl, sub_self]
  -- ## Step 1: the `ē`-image of `W₀ᶜ` is bounded
  have hWccompact : IsCompact (W₀ᶜ : Set M) := hW₀open.isClosed_compl.isCompact
  haveI : CompactSpace ↥(W₀ᶜ : Set M) := isCompact_iff_compactSpace.mp hWccompact
  let ψ : ↥(W₀ᶜ : Set M) → PL.E n := fun x => ē (Set.inclusion hsub x)
  have hψcont : Continuous ψ := ē.continuous.comp (continuous_inclusion hsub)
  obtain ⟨C₀, hC₀⟩ :=
    ((isCompact_univ (X := ↥(W₀ᶜ : Set M))).image hψcont).isBounded.exists_norm_le
  have hSbound : ∀ y : PL.E n, ((ē.symm y : ↥W₁) : M) ∈ (W₀ᶜ : Set M) → ‖y‖ ≤ C₀ := by
    intro y hy
    apply hC₀
    refine ⟨⟨((ē.symm y : ↥W₁) : M), hy⟩, Set.mem_univ _, ?_⟩
    show ē (Set.inclusion hsub ⟨((ē.symm y : ↥W₁) : M), hy⟩) = y
    rw [show Set.inclusion hsub
        (⟨((ē.symm y : ↥W₁) : M), hy⟩ : ↥(W₀ᶜ : Set M)) = ē.symm y from Subtype.ext rfl]
    simp
  -- ## Step 2: `ē '' (K ∩ W₁)` is bounded away from the origin
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hK'closed : IsClosed {x : ↥W₁ | (x : M) ∈ K} := hKclosed.preimage continuous_subtype_val
  have hTclosed : IsClosed (ē '' {x : ↥W₁ | (x : M) ∈ K}) := (ē.isClosed_image).mpr hK'closed
  have h0T : (0 : PL.E n) ∉ ē '' {x : ↥W₁ | (x : M) ∈ K} := by
    rintro ⟨x, hxK, hx0⟩
    have hxq : x = q₁ := by
      apply ē.injective
      rw [hx0, hēq]
    have hqK' : q ∈ K := by
      have hx : (x : M) = q := by rw [hxq]
      rw [Set.mem_ofPred_eq, hx] at hxK
      exact hxK
    exact hqK hqK'
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε > 0, ∀ y ∈ ē '' {x : ↥W₁ | (x : M) ∈ K}, ε ≤ ‖y‖ := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hTclosed.isOpen_compl 0 h0T
    refine ⟨ε, hεpos, fun y hy => ?_⟩
    by_contra hc
    have hc' : ‖y‖ < ε := not_le.mp hc
    exact hεsub (by simpa using hc') hy
  -- ## Step 3: radial expansion and its extension to `M`
  let R : ℝ := max (C₀ + 1) (ε + 1)
  have hεR : ε < R := by
    have h : ε + 1 ≤ R := le_max_right _ _
    linarith
  obtain ⟨g, hg0, hgfix, hgexp⟩ := hrad ε R hεpos hεR
  let h : ↥W₁ ≃ₜ ↥W₁ := (ē.trans g).trans ē.symm
  have hh : ∀ x : ↥W₁, h x = ē.symm (g (ē x)) := by
    intro x
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  let C : Set ↥W₁ := ē.symm '' Metric.closedBall (0 : PL.E n) (R + 1)
  have hCcompact : IsCompact C :=
    (isCompact_closedBall (0 : PL.E n) (R + 1)).image ē.symm.continuous
  have hCsupp : ∀ x : ↥W₁, x ∉ C → h x = x := by
    intro x hx
    have hge : R + 1 ≤ ‖ē x‖ := by
      by_contra hlt
      have hlt' : ‖ē x‖ < R + 1 := not_le.mp hlt
      exact hx ⟨ē x, by simpa using hlt'.le, by simp⟩
    rw [hh x, hgfix (ē x) hge]
    simp
  obtain ⟨H, hHon, hHoff⟩ :=
    exists_homeomorph_extend_of_isCompact (hO := hW₁open) (h := h) (hC := hCcompact) (hid := hCsupp)
  -- ## Step 4: `U := H ⁻¹' W₀`
  have hUeq : H ⁻¹' W₀ = H.symm '' W₀ := (congrFun (Homeomorph.image_symm H) W₀).symm
  refine ⟨H ⁻¹' W₀, ⟨hW₀open.preimage H.continuous, ?_⟩, ?_, ?_⟩
  · rw [hUeq]
    exact ⟨((Homeomorph.image H.symm W₀).symm).trans e₀⟩
  · intro x hxK
    show H x ∈ W₀
    by_cases hxW₁ : x ∈ W₁
    · have hHx : H x = (h ⟨x, hxW₁⟩ : M) := by simpa using hHon ⟨x, hxW₁⟩
      rw [hHx, hh ⟨x, hxW₁⟩]
      by_contra hcon
      have hb := hSbound (g (ē ⟨x, hxW₁⟩)) hcon
      have hexp : ε ≤ ‖ē ⟨x, hxW₁⟩‖ :=
        hε (ē ⟨x, hxW₁⟩) ⟨⟨x, hxW₁⟩, hxK, rfl⟩
      have hR : R ≤ ‖g (ē ⟨x, hxW₁⟩)‖ := hgexp _ hexp
      have hC₀R : C₀ + 1 ≤ R := le_max_left _ _
      linarith
    · have hxW₀ : x ∈ W₀ := by
        have h : x ∈ W₀ ∪ W₁ := by rw [hcov]; exact Set.mem_univ x
        rcases h with h | h
        · exact h
        · exact absurd h hxW₁
      rw [hHoff x hxW₁]
      exact hxW₀
  · intro hqU
    have hHq : H q = q := by
      have h1 : H q = (h ⟨q, hqW₁⟩ : M) := by simpa using hHon ⟨q, hqW₁⟩
      rw [h1, hh ⟨q, hqW₁⟩]
      have h3 : ē ⟨q, hqW₁⟩ = 0 := hēq
      rw [h3, hg0]
      show ((ē.symm 0 : ↥W₁) : M) = q
      have h4 : ē.symm 0 = q₁ := by
        apply ē.injective
        rw [hēq]
        simp
      rw [h4]
    have hqU' : H q ∈ W₀ := hqU
    rw [hHq] at hqU'
    exact hq hqU'

end Work.Cells.Connell
