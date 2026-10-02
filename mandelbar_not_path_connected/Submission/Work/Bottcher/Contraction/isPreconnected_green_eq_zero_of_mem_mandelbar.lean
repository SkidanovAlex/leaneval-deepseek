import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zero locus of the Green function of the tricorn is preconnected on the mandelbar

For a parameter `c` of the mandelbar `M*` (the critical orbit of `T_c(z) = z̄² + c` is
bounded) the filled tricorn `K_c = {z | G_c z = 0}` is connected.

The proof is the classical "nested compact continua" argument.  Choosing a radius `R`
which is at once an escape radius and larger than the critical orbit, the sets
`A n = {z | ‖T_c^[n] z‖ ≤ R}` form a decreasing sequence of compact preconnected sets whose
intersection is exactly `K_c`.

* `preimage_sq_preconnected` : the preimage of a preconnected set containing `0` under
  `z ↦ z²` is preconnected (a *branched* double cover over `0` is connected over a
  connected base);
* `iInter_preconnected` : a decreasing intersection of compact preconnected sets is
  preconnected (Cantor's intersection argument applied to a separation).

Both are proved from scratch here.
-/

namespace Work.Bottcher.Contraction

open Set Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Squaring as an open map -/

private lemma isOpenMap_sq : IsOpenMap (fun z : ℂ => z ^ 2) := by
  rcases AnalyticOnNhd.is_constant_or_isOpenMap
    (AnalyticOnNhd.eval_polynomial (Polynomial.X ^ 2 : Polynomial ℂ)) with h | h
  · exfalso
    obtain ⟨w, hw⟩ := h
    have h1 := hw 1
    have h0 := hw 0
    simp [Polynomial.eval_pow, Polynomial.eval_X] at h1 h0
    rw [← h0] at h1
    norm_num at h1
  · simpa [Polynomial.eval_pow, Polynomial.eval_X] using h

/-- `f '' (f⁻¹' S ∩ W) = S ∩ f '' W`. -/
private lemma image_preimage_inter_sq (S W : Set ℂ) :
    (fun z : ℂ => z ^ 2) '' ((fun z : ℂ => z ^ 2) ⁻¹' S ∩ W) =
      S ∩ (fun z : ℂ => z ^ 2) '' W := by
  ext w
  constructor
  · rintro ⟨z, ⟨hzS, hzW⟩, rfl⟩
    refine ⟨?_, z, hzW, rfl⟩
    rwa [Set.mem_preimage] at hzS
  · rintro ⟨hwS, z, hzW, hzw⟩
    refine ⟨z, ⟨?_, hzW⟩, hzw⟩
    have hzw' : z ^ 2 = w := hzw
    rw [Set.mem_preimage, hzw']
    exact hwS

/-- **The preimage of a preconnected set containing `0` under squaring is preconnected.**

This is the "branched double cover" statement: away from `0` the map `z ↦ z²` is a covering
map, and the two sheets are glued over `0`.  The condition `0 ∈ S` is essential. -/
private lemma preimage_sq_preconnected {S : Set ℂ} (hS : IsPreconnected S) (h0 : (0 : ℂ) ∈ S) :
    IsPreconnected ((fun z : ℂ => z ^ 2) ⁻¹' S) := by
  have hsq : IsOpenMap (fun z : ℂ => z ^ 2) := isOpenMap_sq
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hXuv hXdisj
  -- `P` consists of the points whose two square roots lie on the same side (`u` or `v`),
  -- `Q` of those with one root on each side.
  let P : Set ℂ := (u ∩ Neg.neg ⁻¹' u) ∪ (v ∩ Neg.neg ⁻¹' v)
  let Q : Set ℂ := (u ∩ Neg.neg ⁻¹' v) ∪ (v ∩ Neg.neg ⁻¹' u)
  have hPmem : ∀ z : ℂ, z ∈ P ↔ (z ∈ u ∧ -z ∈ u) ∨ (z ∈ v ∧ -z ∈ v) := by
    intro z
    simp [P, Set.mem_union, Set.mem_inter_iff]
  have hQmem : ∀ z : ℂ, z ∈ Q ↔ (z ∈ u ∧ -z ∈ v) ∨ (z ∈ v ∧ -z ∈ u) := by
    intro z
    simp [Q, Set.mem_union, Set.mem_inter_iff]
  have hPsymm : ∀ z : ℂ, z ∈ P → -z ∈ P := by
    intro z hz
    rw [hPmem] at hz ⊢
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, by simpa using h1⟩
    · exact Or.inr ⟨h2, by simpa using h1⟩
  have hPopen : IsOpen P :=
    (hu.inter (hu.preimage continuous_neg)).union (hv.inter (hv.preimage continuous_neg))
  have hQopen : IsOpen Q :=
    (hu.inter (hv.preimage continuous_neg)).union (hv.inter (hu.preimage continuous_neg))
  have hno : ∀ z : ℂ, z ∈ (fun z : ℂ => z ^ 2) ⁻¹' S → ¬(z ∈ u ∧ z ∈ v) := by
    intro z hz h
    have hmem : z ∈ ((fun z : ℂ => z ^ 2) ⁻¹' S) ∩ (u ∩ v) := ⟨hz, h.1, h.2⟩
    rw [hXdisj] at hmem
    exact (Set.notMem_empty z) hmem
  -- every point of `S` has a square root in `P ∪ Q`
  have hScov : S ⊆ (fun z : ℂ => z ^ 2) '' P ∪ (fun z : ℂ => z ^ 2) '' Q := by
    intro w hw
    obtain ⟨z, hz⟩ := Complex.isSquare w
    have hz2 : z ^ 2 = w := by rw [pow_two]; exact hz.symm
    have hzX : z ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, hz2]; exact hw
    have hnzX : -z ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by
      rw [Set.mem_preimage, show (-z) ^ 2 = z ^ 2 by ring, hz2]; exact hw
    rcases hXuv hzX with hzu | hzu <;> rcases hXuv hnzX with hnzu | hnzu
    · exact Or.inl ⟨z, (hPmem z).mpr (Or.inl ⟨hzu, hnzu⟩), hz2⟩
    · exact Or.inr ⟨z, (hQmem z).mpr (Or.inl ⟨hzu, hnzu⟩), hz2⟩
    · exact Or.inr ⟨z, (hQmem z).mpr (Or.inr ⟨hzu, hnzu⟩), hz2⟩
    · exact Or.inl ⟨z, (hPmem z).mpr (Or.inr ⟨hzu, hnzu⟩), hz2⟩
  have h0P : (0 : ℂ) ∈ (fun z : ℂ => z ^ 2) '' P := by
    refine ⟨0, ?_, by ring⟩
    rw [hPmem]
    have h0X : (0 : ℂ) ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage]; simpa using h0
    rcases hXuv h0X with h0u | h0v
    · exact Or.inl ⟨h0u, by simpa using h0u⟩
    · exact Or.inr ⟨h0v, by simpa using h0v⟩
  -- the images of `P` and `Q` are disjoint over `S`
  have hdisjS : S ∩ ((fun z : ℂ => z ^ 2) '' P ∩ (fun z : ℂ => z ^ 2) '' Q) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwS, ⟨a, haP, hwa⟩, b, hbQ, hwb⟩
    have hwa2 : a ^ 2 = w := hwa
    have hwb2 : b ^ 2 = w := hwb
    have haX : a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, hwa2]; exact hwS
    have hnaX : -a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by
      rw [Set.mem_preimage, show (-a) ^ 2 = a ^ 2 by ring, hwa2]; exact hwS
    have hab : b = a ∨ b = -a := by
      have h : b ^ 2 = a ^ 2 := by rw [hwb2, ← hwa2]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases (hPmem a).mp haP with ⟨hau, hnu⟩ | ⟨hav, hnv⟩
    · rcases (hQmem b).mp hbQ with ⟨hbu, hnbv⟩ | ⟨hbv, hnbu⟩
      · rcases hab with hba | hba
        · subst b
          exact hno (-a) hnaX ⟨hnu, hnbv⟩
        · subst b
          have h1 : a ∈ v := by simpa using hnbv
          exact hno a haX ⟨hau, h1⟩
      · rcases hab with hba | hba
        · subst b
          exact hno a haX ⟨hau, hbv⟩
        · subst b
          exact hno (-a) hnaX ⟨hnu, hbv⟩
    · rcases (hQmem b).mp hbQ with ⟨hbu, hnbv⟩ | ⟨hbv, hnbu⟩
      · rcases hab with hba | hba
        · subst b
          exact hno a haX ⟨hbu, hav⟩
        · subst b
          exact hno (-a) hnaX ⟨hbu, hnv⟩
      · rcases hab with hba | hba
        · subst b
          exact hno (-a) hnaX ⟨hnbu, hnv⟩
        · subst b
          have h1 : a ∈ u := by simpa using hnbu
          exact hno a haX ⟨h1, hav⟩
  -- so `S` is covered by the single open set `p '' P`
  have hSP : S ⊆ (fun z : ℂ => z ^ 2) '' P := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hS) ((fun z : ℂ => z ^ 2) '' P)
        ((fun z : ℂ => z ^ 2) '' Q) (hsq P hPopen) (hsq Q hQopen) hScov hdisjS with h | h
    · exact h
    · exfalso
      have h0Q : (0 : ℂ) ∈ (fun z : ℂ => z ^ 2) '' Q := h h0
      have hmem : (0 : ℂ) ∈ S ∩ ((fun z : ℂ => z ^ 2) '' P ∩ (fun z : ℂ => z ^ 2) '' Q) :=
        ⟨h0, h0P, h0Q⟩
      rw [hdisjS] at hmem
      exact (Set.notMem_empty (0 : ℂ)) hmem
  -- hence every point of `X` is "unmixed"
  have hXP : (fun z : ℂ => z ^ 2) ⁻¹' S ⊆ P := by
    intro z hz
    have hzS : z ^ 2 ∈ S := hz
    obtain ⟨a, haP, ha⟩ := hSP hzS
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp ha) with h' | h'
    · rw [← h']; exact haP
    · have hza : z = -a := by rw [h']; ring
      rw [hza]; exact hPsymm a haP
  -- and now the dichotomy: the two sheets lie on the same side
  have hSuv : S ⊆ (fun z : ℂ => z ^ 2) '' u ∪ (fun z : ℂ => z ^ 2) '' v := by
    intro w hw
    obtain ⟨z, hz⟩ := Complex.isSquare w
    have hz2 : z ^ 2 = w := by rw [pow_two]; exact hz.symm
    have hzX : z ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, hz2]; exact hw
    rcases hXuv hzX with h | h
    · exact Or.inl ⟨z, h, hz2⟩
    · exact Or.inr ⟨z, h, hz2⟩
  have hSdisj2 : S ∩ ((fun z : ℂ => z ^ 2) '' u ∩ (fun z : ℂ => z ^ 2) '' v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwS, ⟨a, hau, ha⟩, b, hbv, hb⟩
    have ha2 : a ^ 2 = w := ha
    have hb2 : b ^ 2 = w := hb
    have haX : a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, ha2]; exact hwS
    have hnaX : -a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by
      rw [Set.mem_preimage, show (-a) ^ 2 = a ^ 2 by ring, ha2]; exact hwS
    have hab : b = a ∨ b = -a := by
      have h : b ^ 2 = a ^ 2 := by rw [hb2, ← ha2]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases (hPmem a).mp (hXP haX) with ⟨hau', hnu'⟩ | ⟨hav', hnv'⟩
    · rcases hab with hba | hba
      · subst b
        exact hno a haX ⟨hau, hbv⟩
      · subst b
        exact hno (-a) hnaX ⟨hnu', hbv⟩
    · exact hno a haX ⟨hau, hav'⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hS) ((fun z : ℂ => z ^ 2) '' u)
      ((fun z : ℂ => z ^ 2) '' v) (hsq u hu) (hsq v hv) hSuv hSdisj2 with h | h
  · left
    intro z hzX
    have hzS : z ^ 2 ∈ S := hzX
    obtain ⟨a, hau, ha⟩ := h hzS
    have ha2 : a ^ 2 = z ^ 2 := ha
    have haX : a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, ha2]; exact hzS
    have hnau : -a ∈ u := by
      rcases (hPmem a).mp (hXP haX) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact (hno a haX ⟨hau, h1⟩).elim
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp ha2) with h' | h'
    · rw [← h']; exact hau
    · have hza : z = -a := by rw [h']; ring
      rw [hza]; exact hnau
  · right
    intro z hzX
    have hzS : z ^ 2 ∈ S := hzX
    obtain ⟨a, hav, ha⟩ := h hzS
    have ha2 : a ^ 2 = z ^ 2 := ha
    have haX : a ∈ (fun z : ℂ => z ^ 2) ⁻¹' S := by rw [Set.mem_preimage, ha2]; exact hzS
    have hnav : -a ∈ v := by
      rcases (hPmem a).mp (hXP haX) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (hno a haX ⟨h1, hav⟩).elim
      · exact h2
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp ha2) with h' | h'
    · rw [← h']; exact hav
    · have hza : z = -a := by rw [h']; ring
      rw [hza]; exact hnav

/-! ## The preimage under the tricorn map -/

private lemma preimage_Tantibar_preconnected {c : ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hc : c ∈ S) : IsPreconnected ((Tantibar c) ⁻¹' S) := by
  have hSc : IsPreconnected ((fun s : ℂ => s - c) '' S) :=
    hS.image _ (continuous_id.sub continuous_const).continuousOn
  have h0c : (0 : ℂ) ∈ (fun s : ℂ => s - c) '' S := ⟨c, hc, by ring⟩
  have hpre : IsPreconnected ((fun w : ℂ => w ^ 2) ⁻¹' ((fun s : ℂ => s - c) '' S)) :=
    preimage_sq_preconnected hSc h0c
  have himg : (Tantibar c) ⁻¹' S =
      (starRingEnd ℂ) '' ((fun w : ℂ => w ^ 2) ⁻¹' ((fun s : ℂ => s - c) '' S)) := by
    ext z
    constructor
    · intro hz
      refine ⟨starRingEnd ℂ z, ?_, by simp⟩
      rw [Set.mem_preimage]
      refine ⟨(starRingEnd ℂ z) ^ 2 + c, ?_, by ring⟩
      simpa only [Set.mem_preimage, LeanEval.ComplexAnalysis.Tantibar] using hz
    · rintro ⟨w, hw, rfl⟩
      rw [Set.mem_preimage] at hw
      obtain ⟨s, hsS, hs⟩ := hw
      show LeanEval.ComplexAnalysis.Tantibar c (starRingEnd ℂ w) ∈ S
      simp only [LeanEval.ComplexAnalysis.Tantibar]
      rw [show starRingEnd ℂ (starRingEnd ℂ w) = w by simp]
      rw [show w ^ 2 + c = s by rw [← hs]; ring]
      exact hsS
  rw [himg]
  exact hpre.image _ continuous_star.continuousOn

/-! ## Intersection of a decreasing sequence of compact continua -/

/-- **A decreasing intersection of compact preconnected sets is preconnected.**

If `⋂ A n` met two disjoint closed sets `u`, `v`, the compact sets `K ∩ u`, `K ∩ v` could be
separated by disjoint open sets `P`, `Q`; some `A N` is then contained in `P ∪ Q` (Cantor's
intersection theorem applied to `A n \ (P ∪ Q)`), which separates `A N`. -/
private lemma iInter_preconnected {A : ℕ → Set ℂ} (hcpt : ∀ n, IsCompact (A n))
    (hpre : ∀ n, IsPreconnected (A n)) (hanti : ∀ n, A (n + 1) ⊆ A n) :
    IsPreconnected (⋂ n, A n) := by
  classical
  have hKcpt : IsCompact (⋂ n, A n) :=
    (hcpt 0).of_isClosed_subset (isClosed_iInter fun n => (hcpt n).isClosed)
      (Set.iInter_subset _ 0)
  have hFIP : ∀ W : Set ℂ, IsOpen W → (⋂ n, A n) ⊆ W → ∃ N, A N ⊆ W := by
    intro W hW hKW
    by_contra h
    have hnsub : ∀ n, ¬ A n ⊆ W := fun n hsub => h ⟨n, hsub⟩
    have hne : ∀ n, ∃ x, x ∈ A n ∧ x ∉ W := fun n => Set.not_subset.mp (hnsub n)
    set B : ℕ → Set ℂ := fun n => A n ∩ Wᶜ with hB
    have hBanti : ∀ i, B (i + 1) ⊆ B i := fun i x hx => ⟨hanti i hx.1, hx.2⟩
    have hBne : ∀ i, (B i).Nonempty := by
      intro i
      obtain ⟨x, hxA, hxW⟩ := hne i
      exact ⟨x, hxA, hxW⟩
    have hB0 : IsCompact (B 0) := (hcpt 0).inter_right hW.isClosed_compl
    have hBcl : ∀ i, IsClosed (B i) := fun i => (hcpt i).isClosed.inter hW.isClosed_compl
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hBanti hBne hB0 hBcl
    rw [Set.mem_iInter] at hx
    have hxK : x ∈ ⋂ n, A n := by
      rw [Set.mem_iInter]
      exact fun n => (hx n).1
    have hxW : x ∉ W := (hx 0).2
    exact hxW (hKW hxK)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hKuv hKdisj
  by_cases hKu : ((⋂ n, A n) ∩ u).Nonempty
  · by_cases hKv : ((⋂ n, A n) ∩ v).Nonempty
    · exfalso
      have hcptu : IsCompact ((⋂ n, A n) ∩ u) := hKcpt.inter_right hu
      have hcptv : IsCompact ((⋂ n, A n) ∩ v) := hKcpt.inter_right hv
      have hdisjuv : Disjoint ((⋂ n, A n) ∩ u) ((⋂ n, A n) ∩ v) := by
        rw [Set.disjoint_left]
        rintro x ⟨hxK, hxu⟩ ⟨-, hxv⟩
        have hmem : x ∈ (⋂ n, A n) ∩ (u ∩ v) := ⟨hxK, hxu, hxv⟩
        rw [hKdisj] at hmem
        exact (Set.notMem_empty x) hmem
      obtain ⟨P, Q, hPopen, hQopen, hKuP, hKvQ, hPQdisj⟩ :=
        SeparatedNhds.of_isCompact_isCompact hcptu hcptv hdisjuv
      have hKsub : (⋂ n, A n) ⊆ P ∪ Q := by
        intro x hx
        rcases hKuv hx with hxu | hxv
        · exact Or.inl (hKuP ⟨hx, hxu⟩)
        · exact Or.inr (hKvQ ⟨hx, hxv⟩)
      obtain ⟨N, hN⟩ := hFIP (P ∪ Q) (hPopen.union hQopen) hKsub
      obtain ⟨x, hxu⟩ := hKu
      have hANP : (A N ∩ P).Nonempty := ⟨x, Set.iInter_subset A N hxu.1, hKuP hxu⟩
      obtain ⟨y, hyv⟩ := hKv
      have hANQ : (A N ∩ Q).Nonempty := ⟨y, Set.iInter_subset A N hyv.1, hKvQ hyv⟩
      have hdisjPQ' : A N ∩ (P ∩ Q) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        exact (Set.disjoint_left.mp hPQdisj) hz.2.1 hz.2.2
      rcases (isPreconnected_iff_subset_of_disjoint.mp (hpre N)) P Q hPopen hQopen hN
        hdisjPQ' with hANP' | hANQ'
      · obtain ⟨z, hz⟩ := hANQ
        exact (Set.disjoint_left.mp hPQdisj) (hANP' hz.1) hz.2
      · obtain ⟨z, hz⟩ := hANP
        exact (Set.disjoint_left.mp hPQdisj) hz.2 (hANQ' hz.1)
    · left
      intro x hx
      rcases hKuv hx with hxu | hxv
      · exact hxu
      · exact absurd ⟨x, hx, hxv⟩ hKv
  · right
    intro x hx
    rcases hKuv hx with hxu | hxv
    · exact absurd ⟨x, hx, hxu⟩ hKu
    · exact hxv

/-! ## The main theorem -/

theorem isPreconnected_green_eq_zero_of_mem_mandelbar (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    IsPreconnected {z : ℂ | Work.Bottcher.green c z = 0} := by
  obtain ⟨M, hM⟩ := hc
  set R : ℝ := max (2 * (1 + ‖c‖)) (M + 1) with hR
  have hRge : 2 * (1 + ‖c‖) ≤ R := le_max_left _ _
  have hRM : M + 1 ≤ R := le_max_right _ _
  have hMR : M < R := by linarith
  -- escape step: a point of norm `> R` keeps growing in norm
  have hesc : ∀ z : ℂ, R < ‖z‖ → ‖z‖ < ‖Tantibar c z‖ := by
    intro z hz
    have hge : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
      have h := Work.Escape.norm_Td_ge 2 c z
      rwa [Work.Escape.Td_two_eq] at h
    have h2 : 2 * (1 + ‖c‖) < ‖z‖ := lt_of_le_of_lt hRge hz
    nlinarith [norm_nonneg c]
  have hesc' : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → R < ‖(Tantibar c)^[n] z‖ := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
        intro z hz
        rw [Function.iterate_succ_apply']
        exact lt_trans (ih z hz) (hesc _ (ih z hz))
  -- the nested compact sets
  let A : ℕ → Set ℂ := fun n => {z : ℂ | ‖(Tantibar c)^[n] z‖ ≤ R}
  have hAc : ∀ n, c ∈ A n := by
    intro n
    have hconv : (Tantibar c)^[n] c = (Tantibar c)^[n + 1] 0 := by
      have hT0 : (Tantibar c) 0 = c := by simp [LeanEval.ComplexAnalysis.Tantibar]
      rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply, hT0]
    show ‖(Tantibar c)^[n] c‖ ≤ R
    rw [hconv]
    exact le_trans (hM (n + 1)) (le_of_lt hMR)
  have hA0 : IsPreconnected (A 0) := by
    have h : A 0 = Metric.closedBall 0 R := by
      ext z
      simp [A, Metric.mem_closedBall, dist_zero_right]
    rw [h]
    exact Metric.isPreconnected_closedBall
  have hApre : ∀ n, IsPreconnected (A n) := by
    intro n
    induction n with
    | zero => exact hA0
    | succ k ih =>
        have hstep : A (k + 1) = (Tantibar c) ⁻¹' (A k) := by
          ext z
          show ‖(Tantibar c)^[k + 1] z‖ ≤ R ↔ ‖(Tantibar c)^[k] ((Tantibar c) z)‖ ≤ R
          rw [show k + 1 = k.succ from rfl, Function.iterate_succ_apply]
        rw [hstep]
        exact preimage_Tantibar_preconnected ih (hAc k)
  have hAcpt : ∀ n, IsCompact (A n) := by
    intro n
    have hcont : Continuous (fun z : ℂ => (Tantibar c)^[n] z) :=
      (Work.Escape.monicGrowth_Tantibar c).continuous.iterate n
    have hclosed : IsClosed (A n) := by
      change IsClosed {z : ℂ | ‖(Tantibar c)^[n] z‖ ≤ R}
      exact isClosed_le hcont.norm continuous_const
    have hsub : A n ⊆ Metric.closedBall 0 R := by
      intro z hz
      change ‖(Tantibar c)^[n] z‖ ≤ R at hz
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      rw [not_le] at h
      exact absurd hz (not_le.mpr (hesc' n z h))
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsub
  have hAanti : ∀ n, A (n + 1) ⊆ A n := by
    intro n z hz
    change ‖(Tantibar c)^[n + 1] z‖ ≤ R at hz
    change ‖(Tantibar c)^[n] z‖ ≤ R
    by_contra h
    rw [not_le] at h
    have h2 : R < ‖(Tantibar c)^[n + 1] z‖ := by
      rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply']
      exact lt_trans h (hesc ((Tantibar c)^[n] z) h)
    linarith
  have hInter : IsPreconnected (⋂ n, A n) := iInter_preconnected hAcpt hApre hAanti
  have hKeq : {z : ℂ | Work.Bottcher.green c z = 0} = ⋂ n, A n := by
    ext z
    rw [Set.mem_iInter]
    constructor
    · intro hz n
      change ‖(Tantibar c)^[n] z‖ ≤ R
      by_contra h
      rw [not_le] at h
      have hmax : max 2 ‖c‖ ≤ 2 * (1 + ‖c‖) := by
        rw [max_le_iff]
        exact ⟨by linarith [norm_nonneg c], by linarith [norm_nonneg c]⟩
      have hWmem : (Tantibar c)^[n] z ∈ Work.Escape.escapeRegion ‖c‖ :=
        lt_of_le_of_lt (le_trans hmax hRge) h
      have hten := Work.Escape.tendsto_norm_iterate_atTop (Tantibar c) 2 ‖c‖
        (Work.Escape.monicGrowth_Tantibar c) le_rfl hWmem
      obtain ⟨M', hM'⟩ := (Work.Bottcher.Green.green_eq_zero_iff_bounded c z).mp hz
      rw [Filter.tendsto_atTop_atTop] at hten
      obtain ⟨i, hi⟩ := hten (M' + 1)
      have h1 : M' + 1 ≤ ‖(Tantibar c)^[i] ((Tantibar c)^[n] z)‖ := hi i le_rfl
      have h2 : ‖(Tantibar c)^[i] ((Tantibar c)^[n] z)‖ ≤ M' := by
        rw [← Function.iterate_add_apply]
        exact hM' (i + n)
      linarith
    · intro hz
      change Work.Bottcher.green c z = 0
      rw [Work.Bottcher.Green.green_eq_zero_iff_bounded]
      exact ⟨R, fun n => hz n⟩
  rw [hKeq]
  exact hInter

end Work.Bottcher.Contraction
