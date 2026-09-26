import Mathlib
import Submission.Work.Smooth.JordanSeparation.exists_continuum_separating
import Submission.Work.Spike.janiszewski_pointInter
import Submission.Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn

/-!
# Reusable lemmas towards the two-point Janiszewski theorem

Sorry-free module collecting the pieces of `Work.Spike.janiszewski_twoPoints_compact`:

* the one-point Janiszewski thickening `preconnected_union_ball_inter`;
* the interior case `preconnected_compl_of_mem_interior` (and its four-flavour corollary
  `preconnected_compl_of_mem_interior_pair`, and `janiszewski_twoPoints_compact_of_interior`);
* Step 1 `sep_continuum_contains_pair` (a continuum `C ⊆ A ∪ B` separating two points of `(A∪B)ᶜ`
  in different components of `Cᶜ` contains both `p` and `q`);
* Step 2 `exists_sep_continuum_pair` (Wilder's irreducible-cut theorem plus Step 1);
* the frontier mechanism `frontier_component_contains_pair` (the frontier of a component of `Cᶜ`
  meeting `(A∪B)ᶜ` is a continuum through `p` and `q`).

The only ingredient of the two-point theorem that is *not* here is the pigeonhole crux
`Work.Spike.janiszewski_twoPoints_key`.
-/

namespace Work.Spike

open Set

noncomputable section

/-- `{p,q}` is not preconnected when `p ≠ q`. -/
theorem not_isPreconnected_pair {p q : ℂ} (hpq : p ≠ q) :
    ¬ IsPreconnected ({p, q} : Set ℂ) := by
  intro h
  have h2 : ({p, q} : Set ℂ) ⊆ ({p} : Set ℂ) ∪ {q} := by
    intro z hz; rcases hz with rfl | rfl <;> simp
  have hd : ({p, q} : Set ℂ) ∩ (({p} : Set ℂ) ∩ {q}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzp, hzq⟩
    exact hpq (hzp.symm.trans hzq)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp h) ({p} : Set ℂ) ({q} : Set ℂ)
    isClosed_singleton isClosed_singleton h2 hd with h3 | h3
  · have hq' : q = p := by simpa using h3 (by simp : q ∈ ({p, q} : Set ℂ))
    exact hpq hq'.symm
  · have hp' : p = q := by simpa using h3 (by simp : p ∈ ({p, q} : Set ℂ))
    exact hpq hp'

/-- `B ≠ {p,q}` for a preconnected `B` containing `p ≠ q`. -/
theorem preconnected_ne_pair {B : Set ℂ} (hBp : IsPreconnected B) {p q : ℂ} (hpq : p ≠ q)
    (hp : p ∈ B) (hq : q ∈ B) : B ≠ ({p, q} : Set ℂ) := by
  intro h
  exact not_isPreconnected_pair hpq (h ▸ hBp)

/-- Any two points of a preconnected set lie in the same component. -/
theorem connectedComponentIn_eq_of_isPreconnected {X : Set ℂ} (h : IsPreconnected X) {x y : ℂ}
    (hx : x ∈ X) (hy : y ∈ X) : connectedComponentIn X x = connectedComponentIn X y :=
  connectedComponentIn_eq (h.subset_connectedComponentIn hx subset_rfl hy)

/-- **Interior case.**  If `p ∈ interior A`, then `(A ∪ B)ᶜ` is preconnected, so the theorem is
immediate.

Take a small ball `D ∋ p` with `q ∉ D` and `D ⊆ A`.  Then `B ∩ D = {p}` (because `B ∩ A = {p,q}`),
so `p` is isolated in `B`; hence `B \ {p}` is closed and compact.  Moreover
`(B \ {p})ᶜ = Bᶜ ∪ {p}` and `A ∪ (B \ {p}) = A ∪ B` (as `p ∈ A`).  The one-point Janiszewski
theorem (`janiszewski_pointInter`) applied to `(A, B \ {p})`, whose intersection is `{q}`, says that
any two points `x, y ∉ A ∪ B` lying in the same component of `Aᶜ` and of `(B \ {p})ᶜ` lie in the
same component of `(A ∪ B)ᶜ`; both conditions hold as `Aᶜ` and `Bᶜ` are preconnected and contain
`x, y`.  So any two points of `(A ∪ B)ᶜ` are connected there. -/
theorem preconnected_compl_of_mem_interior {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q}) (hp : p ∈ interior A) :
    IsPreconnected ((A ∪ B)ᶜ : Set ℂ) := by
  obtain ⟨ε₀, hε₀, hballA⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  set ε : ℝ := min ε₀ (dist p q) / 2 with hεdef
  have hmin : 0 < min ε₀ (dist p q) := lt_min hε₀ (dist_pos.mpr hpq)
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεle₀ : ε ≤ ε₀ := le_trans (le_of_lt (half_lt_self hmin)) (min_le_left _ _)
  have hεle : ε ≤ dist p q := le_trans (le_of_lt (half_lt_self hmin)) (min_le_right _ _)
  have hball : Metric.ball p ε ⊆ A :=
    fun z hz => interior_subset (hballA (Metric.ball_subset_ball hεle₀ hz))
  have hqnot : q ∉ Metric.ball p ε := by
    intro h; rw [Metric.mem_ball, dist_comm] at h; linarith
  have hBinter : B ∩ Metric.ball p ε = {p} := by
    apply Subset.antisymm
    · rintro z ⟨hzB, hzball⟩
      have hzpq : z ∈ ({p, q} : Set ℂ) := by rw [← hint]; exact ⟨hball hzball, hzB⟩
      rcases (by simpa using hzpq : z = p ∨ z = q) with hzp' | hzq'
      · rw [hzp']; simp
      · exfalso
        exact hqnot (hzq' ▸ hzball)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨(by rw [hint]; exact Or.inl rfl : p ∈ A ∩ B).2, Metric.mem_ball_self hε⟩
  have hBclosed : IsClosed (B \ ({p} : Set ℂ)) := by
    have hset : B \ ({p} : Set ℂ) = B ∩ (Metric.ball p ε)ᶜ := by
      ext z; constructor
      · rintro ⟨hzB, hzp⟩
        refine ⟨hzB, fun hzball => hzp ?_⟩
        have hz : z ∈ ({p} : Set ℂ) := by
          rw [← hBinter]; exact ⟨hzB, hzball⟩
        simpa using hz
      · rintro ⟨hzB, hzball⟩
        refine ⟨hzB, ?_⟩
        intro hzp
        rw [hzp] at hzball
        exact hzball (Metric.mem_ball_self hε)
    rw [hset]
    exact hB.isClosed.inter Metric.isOpen_ball.isClosed_compl
  have hB'cpt : IsCompact (B \ ({p} : Set ℂ)) := hB.of_isClosed_subset hBclosed Set.sdiff_subset
  have hpair : A ∩ (B \ ({p} : Set ℂ)) = {q} := by
    ext z; constructor
    · rintro ⟨hzA, hzB, hzp⟩
      have hzpq : z ∈ ({p, q} : Set ℂ) := by rw [← hint]; exact ⟨hzA, hzB⟩
      rcases (by simpa using hzpq : z = p ∨ z = q) with hzp' | hzq'
      · exfalso
        exact hzp (by rw [hzp']; simp)
      · rw [hzq']; simp
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hqAB : q ∈ A ∩ B := by rw [hint]; exact Or.inr rfl
      exact ⟨hqAB.1, hqAB.2, fun h => hpq h.symm⟩
  have hcomp : (B \ ({p} : Set ℂ))ᶜ = Bᶜ ∪ ({p} : Set ℂ) := by
    rw [Set.compl_sdiff, Set.union_comm]
  have hunion : A ∪ (B \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.1
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hzp : z = p
        · rw [hzp]
          exact Or.inl ((show p ∈ A ∩ B from by rw [hint]; exact Or.inl rfl).1)
        · exact Or.inr ⟨h, hzp⟩
  have hmain : ∀ x : ℂ, x ∉ A ∪ B → ∀ y : ℂ, y ∉ A ∪ B →
      y ∈ connectedComponentIn ((A ∪ B)ᶜ) x := by
    intro x hx y hy
    have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
    have hyA : y ∈ Aᶜ := fun h => hy (Or.inl h)
    have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
    have hyB : y ∈ Bᶜ := fun h => hy (Or.inr h)
    have hx' : x ∉ A ∪ (B \ ({p} : Set ℂ)) := by rw [hunion]; exact hx
    have hy' : y ∉ A ∪ (B \ ({p} : Set ℂ)) := by rw [hunion]; exact hy
    have h1 : y ∈ connectedComponentIn Aᶜ x := hAc.subset_connectedComponentIn hxA subset_rfl hyA
    have h2 : y ∈ connectedComponentIn ((B \ ({p} : Set ℂ))ᶜ) x := by
      rw [hcomp]
      exact connectedComponentIn_mono x Set.subset_union_left
        (hBc.subset_connectedComponentIn hxB subset_rfl hyB)
    have h3 : y ∈ connectedComponentIn ((A ∪ (B \ ({p} : Set ℂ)))ᶜ) x :=
      janiszewski_pointInter hA hB'cpt hpair hx' hy' h1 h2
    rwa [hunion] at h3
  rcases Set.eq_empty_or_nonempty ((A ∪ B)ᶜ : Set ℂ) with hE | ⟨x₀, hx₀⟩
  · rw [hE]; exact isPreconnected_empty
  · have hsub : (A ∪ B)ᶜ ⊆ connectedComponentIn ((A ∪ B)ᶜ) x₀ := fun y hy => hmain x₀ hx₀ y hy
    have heq : (A ∪ B)ᶜ = connectedComponentIn ((A ∪ B)ᶜ) x₀ :=
      Subset.antisymm hsub (connectedComponentIn_subset _ _)
    rw [heq]
    exact isPreconnected_connectedComponentIn

/-- **Interior case, all four flavours.**  If any of `p`, `q` is an interior point of `A` or of
`B`, then `(A ∪ B)ᶜ` is preconnected. -/
theorem preconnected_compl_of_mem_interior_pair {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q})
    (hcase : p ∈ interior A ∨ p ∈ interior B ∨ q ∈ interior A ∨ q ∈ interior B) :
    IsPreconnected ((A ∪ B)ᶜ : Set ℂ) := by
  rcases hcase with h | h | h | h
  · exact preconnected_compl_of_mem_interior hA hB hAc hBc hpq hint h
  · have h' := preconnected_compl_of_mem_interior hB hA hBc hAc hpq
      (by rw [Set.inter_comm]; exact hint) h
    simpa [Set.union_comm] using h'
  · exact preconnected_compl_of_mem_interior hA hB hAc hBc (Ne.symm hpq)
      (by rw [hint, Set.pair_comm]) h
  · have h' := preconnected_compl_of_mem_interior hB hA hBc hAc (Ne.symm hpq)
      (by rw [Set.inter_comm, hint, Set.pair_comm]) h
    simpa [Set.union_comm] using h'

/-- **The target in the interior case.** -/
theorem janiszewski_twoPoints_compact_of_interior {A B : Set ℂ} (hA : IsCompact A)
    (hB : IsCompact B) (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ}
    (hpq : p ≠ q) (hint : A ∩ B = {p, q})
    (hcase : p ∈ interior A ∨ p ∈ interior B ∨ q ∈ interior A ∨ q ∈ interior B) :
    ∀ x y z : ℂ, x ∉ A ∪ B → y ∉ A ∪ B → z ∉ A ∪ B →
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ y ∨
      connectedComponentIn (A ∪ B)ᶜ x = connectedComponentIn (A ∪ B)ᶜ z ∨
      connectedComponentIn (A ∪ B)ᶜ y = connectedComponentIn (A ∪ B)ᶜ z := by
  have hpre := preconnected_compl_of_mem_interior_pair hA hB hAc hBc hpq hint hcase
  intro x y z hx hy hz
  exact Or.inl (connectedComponentIn_eq_of_isPreconnected hpre hx hy)

/-- **(P1, sharpened)**  If `p` is a limit point of both `Aᶜ` and `Bᶜ`, then for every small ball
`D ∋ p` (with `q ∉ D`) the set `(A ∪ B)ᶜ ∪ ((A ∪ B) ∩ D)` is preconnected.

This is the one-point Janiszewski theorem applied to the pair `(A \ D, B \ D)`: their
intersection is `{q}`, their complements are `Aᶜ ∪ D` and `Bᶜ ∪ D` (preconnected because
`p` is a limit point), and `((A \ D) ∪ (B \ D))ᶜ = (A ∪ B)ᶜ ∪ ((A ∪ B) ∩ D)`. -/
theorem preconnected_union_ball_inter {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hint : A ∩ B = {p, q})
    {ε : ℝ} (hε : 0 < ε) (hq : q ∉ Metric.ball p ε)
    (hpA : p ∈ closure (Aᶜ : Set ℂ)) (hpB : p ∈ closure (Bᶜ : Set ℂ)) :
    IsPreconnected ((A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball p ε)) := by
  have hDopen : IsOpen (Metric.ball p ε) := Metric.isOpen_ball
  have hA'cpt : IsCompact (A \ Metric.ball p ε) := hA.diff hDopen
  have hB'cpt : IsCompact (B \ Metric.ball p ε) := hB.diff hDopen
  have hinter : (A \ Metric.ball p ε) ∩ (B \ Metric.ball p ε) = {q} := by
    ext z
    constructor
    · rintro ⟨⟨hzA, hzD⟩, hzB, -⟩
      have hzpq : z ∈ ({p, q} : Set ℂ) := by rw [← hint]; exact ⟨hzA, hzB⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hzpq
      rcases hzpq with rfl | rfl
      · exact absurd (Metric.mem_ball_self hε) hzD
      · rfl
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hqAB : q ∈ A ∩ B := by rw [hint]; exact Or.inr rfl
      exact ⟨⟨hqAB.1, hq⟩, hqAB.2, hq⟩
  have hcomplA : (A \ Metric.ball p ε)ᶜ = (Aᶜ : Set ℂ) ∪ Metric.ball p ε := by
    rw [Set.compl_sdiff, Set.union_comm]
  have hcomplB : (B \ Metric.ball p ε)ᶜ = (Bᶜ : Set ℂ) ∪ Metric.ball p ε := by
    rw [Set.compl_sdiff, Set.union_comm]
  have hDpre : IsPreconnected (Metric.ball p ε) := (convex_ball p ε).isPreconnected
  have hA'pre : IsPreconnected ((A \ Metric.ball p ε)ᶜ) := by
    rw [hcomplA]
    obtain ⟨z, hzA, hzd⟩ := Metric.mem_closure_iff.mp hpA ε hε
    exact IsPreconnected.union z hzA (by rw [Metric.mem_ball, dist_comm]; exact hzd) hAc hDpre
  have hB'pre : IsPreconnected ((B \ Metric.ball p ε)ᶜ) := by
    rw [hcomplB]
    obtain ⟨z, hzB, hzd⟩ := Metric.mem_closure_iff.mp hpB ε hε
    exact IsPreconnected.union z hzB (by rw [Metric.mem_ball, dist_comm]; exact hzd) hBc hDpre
  have hset : ((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ
      = (A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball p ε) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [← hset]
  have hmain : ∀ x ∈ ((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ,
      ∀ y ∈ ((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ,
      y ∈ connectedComponentIn (((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ) x := by
    intro x hx y hy
    have hxA : x ∈ (A \ Metric.ball p ε)ᶜ := fun h => hx (Or.inl h)
    have hxB : x ∈ (B \ Metric.ball p ε)ᶜ := fun h => hx (Or.inr h)
    have hyA : y ∈ (A \ Metric.ball p ε)ᶜ := fun h => hy (Or.inl h)
    have hyB : y ∈ (B \ Metric.ball p ε)ᶜ := fun h => hy (Or.inr h)
    have h1 : y ∈ connectedComponentIn ((A \ Metric.ball p ε)ᶜ) x :=
      hA'pre.subset_connectedComponentIn hxA subset_rfl hyA
    have h2 : y ∈ connectedComponentIn ((B \ Metric.ball p ε)ᶜ) x :=
      hB'pre.subset_connectedComponentIn hxB subset_rfl hyB
    exact janiszewski_pointInter hA'cpt hB'cpt hinter hx hy h1 h2
  rcases Set.eq_empty_or_nonempty (((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ)
    with hE | ⟨x, hx⟩
  · rw [hE]; exact isPreconnected_empty
  · have hcomp : ((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ
        = connectedComponentIn (((A \ Metric.ball p ε) ∪ (B \ Metric.ball p ε))ᶜ) x :=
      Subset.antisymm (fun y hy => hmain x hx y hy) (connectedComponentIn_subset _ _)
    rw [hcomp]
    exact isPreconnected_connectedComponentIn

/-- **(Step 1, generic case)**  If `p` and `q` are limit points of both `Aᶜ` and `Bᶜ`, then any
continuum `C ⊆ A ∪ B` separating two points of `(A ∪ B)ᶜ` in different components of `Cᶜ` contains
both `p` and `q`.

Suppose `p ∉ C`.  Choose a ball `D ∋ p` with `D ∩ C = ∅` and `q ∉ D`.  The set
`(A ∪ B)ᶜ ∪ ((A ∪ B) ∩ D)` is preconnected by `preconnected_union_ball_inter` and is contained in
`Cᶜ` (as `D ∩ C = ∅`); it contains `x` and `y`, which are therefore in the same component of `Cᶜ`,
contradicting the separation. -/
theorem sep_continuum_contains_pair_of_closure
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q})
    (hpA : p ∈ closure (Aᶜ : Set ℂ)) (hpB : p ∈ closure (Bᶜ : Set ℂ))
    (hqA : q ∈ closure (Aᶜ : Set ℂ)) (hqB : q ∈ closure (Bᶜ : Set ℂ))
    {C : Set ℂ} (hCsub : C ⊆ A ∪ B) (hCcl : IsClosed C)
    {x y : ℂ} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (hsep : connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y) :
    p ∈ C ∧ q ∈ C := by
  have key : ∀ r : ℂ, r ∈ ({p, q} : Set ℂ) → r ∈ closure (Aᶜ : Set ℂ) →
      r ∈ closure (Bᶜ : Set ℂ) → r ∈ C := by
    intro r hr hrA hrB
    by_contra hrC
    have hrpq : r = p ∨ r = q := by simpa using hr
    -- the other point of the pair
    have hother : ∃ s : ℂ, s ∈ ({p, q} : Set ℂ) ∧ s ≠ r := by
      rcases hrpq with rfl | rfl
      · exact ⟨q, by simp, fun h => hpq h.symm⟩
      · exact ⟨p, by simp, hpq⟩
    obtain ⟨s, hs, hsr⟩ := hother
    -- a ball around `r` missing `C` and `s`
    have hnot : r ∉ closure C := by rw [hCcl.closure_eq]; exact hrC
    have hex : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ b ∈ C, ε₁ ≤ dist r b := by
      by_contra hcon
      apply hnot
      rw [Metric.mem_closure_iff]
      intro ε hε
      by_contra hcon2
      exact hcon ⟨ε, hε, fun b hb => not_lt.mp (fun hlt => hcon2 ⟨b, hb, hlt⟩)⟩
    obtain ⟨ε₁, hε₁, hε₁C⟩ := hex
    have hε₂ : 0 < dist r s := dist_pos.mpr (Ne.symm hsr)
    set ε : ℝ := min ε₁ (dist r s) / 2 with hεdef
    have hmin : 0 < min ε₁ (dist r s) := lt_min hε₁ hε₂
    have hε0 : 0 < ε := by rw [hεdef]; positivity
    have hεlt₁ : ε < ε₁ := by
      rw [hεdef]
      exact lt_of_lt_of_le (half_lt_self hmin) (min_le_left _ _)
    have hεle₂ : ε ≤ dist r s := by
      rw [hεdef]
      exact le_trans (le_of_lt (half_lt_self hmin)) (min_le_right _ _)
    have hεC : Metric.ball r ε ∩ C = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzball, hzC⟩
      have h1 : ε₁ ≤ dist r z := hε₁C z hzC
      have h2 : dist r z < ε := by rw [dist_comm]; exact Metric.mem_ball.mp hzball
      linarith
    have hsD : s ∉ Metric.ball r ε := by
      intro h
      rw [Metric.mem_ball, dist_comm] at h
      linarith
    -- the preconnectedness of the thickening, by symmetry in `p` and `q`
    have hpre : IsPreconnected ((A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball r ε)) := by
      refine preconnected_union_ball_inter hA hB hAc hBc ?_ hε0 hsD hrA hrB
      rcases hrpq with hp | hq
      · have hs' : s = q := by
          rcases (by simpa using hs : s = p ∨ s = q) with h | h
          · exact absurd (h.trans hp.symm) hsr
          · exact h
        rw [hp, hs']
        exact hint
      · have hs' : s = p := by
          rcases (by simpa using hs : s = p ∨ s = q) with h | h
          · exact h
          · exact absurd (h.trans hq.symm) hsr
        rw [hq, hs', hint, Set.pair_comm]
    -- it is contained in `Cᶜ`
    have hsub : (A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball r ε) ⊆ Cᶜ := by
      rintro z (hz | ⟨hzAB, hzD⟩)
      · exact fun hzC => hz (hCsub hzC)
      · exact fun hzC => (Set.eq_empty_iff_forall_notMem.mp hεC) z ⟨hzD, hzC⟩
    have hx' : x ∈ (A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball r ε) := Or.inl (by simpa using hx)
    have hy' : y ∈ (A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball r ε) := Or.inl (by simpa using hy)
    have hconn : y ∈ connectedComponentIn ((A ∪ B)ᶜ ∪ ((A ∪ B) ∩ Metric.ball r ε)) x :=
      hpre.subset_connectedComponentIn hx' subset_rfl hy'
    have hconn' : y ∈ connectedComponentIn Cᶜ x :=
      connectedComponentIn_mono x hsub hconn
    exact hsep (connectedComponentIn_eq hconn')
  exact ⟨key p (by simp) hpA hpB, key q (by simp) hqA hqB⟩

/-- **(Step 1)**  A continuum `C ⊆ A ∪ B` that separates two points `x y ∈ (A ∪ B)ᶜ` lying in
different components of `Cᶜ` must contain both `p` and `q`.

Case analysis: if any of `p`, `q` is an interior point of `A` or of `B`, then `(A ∪ B)ᶜ` is
preconnected (`preconnected_compl_of_mem_interior_pair`), so `x` and `y` lie in the same component
of `(A ∪ B)ᶜ ⊆ Cᶜ`, contradicting the separation.  Otherwise `p` and `q` are limit points of both
`Aᶜ` and `Bᶜ` and the generic case `sep_continuum_contains_pair_of_closure` applies. -/
theorem sep_continuum_contains_pair {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q})
    {C : Set ℂ} (hCsub : C ⊆ A ∪ B) (hCpre : IsPreconnected C) (hCcl : IsClosed C)
    {x y : ℂ} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (hsep : connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y) :
    p ∈ C ∧ q ∈ C := by
  by_cases hany : p ∈ interior A ∨ p ∈ interior B ∨ q ∈ interior A ∨ q ∈ interior B
  · exfalso
    have hpre := preconnected_compl_of_mem_interior_pair hA hB hAc hBc hpq hint hany
    have hx' : x ∈ (A ∪ B)ᶜ := by simpa using hx
    have hy' : y ∈ (A ∪ B)ᶜ := by simpa using hy
    have heq := connectedComponentIn_eq_of_isPreconnected hpre hx' hy'
    have hsub : (A ∪ B)ᶜ ⊆ Cᶜ := fun z hz => fun hzC => hz (hCsub hzC)
    have hyc : y ∈ connectedComponentIn Cᶜ x :=
      (connectedComponentIn_mono x hsub) (heq.symm ▸ mem_connectedComponentIn hy')
    exact hsep (connectedComponentIn_eq hyc)
  · push_neg at hany
    obtain ⟨hpA, hpB, hqA, hqB⟩ := hany
    have hcomplA : closure (Aᶜ : Set ℂ) = (interior A)ᶜ := closure_compl
    have hcomplB : closure (Bᶜ : Set ℂ) = (interior B)ᶜ := closure_compl
    exact sep_continuum_contains_pair_of_closure hA hB hAc hBc hpq hint
      (by rw [hcomplA]; exact hpA) (by rw [hcomplB]; exact hpB)
      (by rw [hcomplA]; exact hqA) (by rw [hcomplB]; exact hqB)
      hCsub hCcl hx hy hsep

/-- **(Step 2)**  Two points of `(A ∪ B)ᶜ` in different components of `(A ∪ B)ᶜ` are separated by a
continuum contained in `A ∪ B` and containing both `p` and `q`.  (The existence of the continuum is
Wilder's irreducible-cut theorem `Work.Smooth.JordanSeparation.exists_continuum_separating`, and the
`p, q ∈ C` part is Step 1.) -/
theorem exists_sep_continuum_pair {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q})
    {x y : ℂ} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (hsep : connectedComponentIn (A ∪ B)ᶜ x ≠ connectedComponentIn (A ∪ B)ᶜ y) :
    ∃ C : Set ℂ, C ⊆ A ∪ B ∧ IsPreconnected C ∧ IsClosed C ∧ p ∈ C ∧ q ∈ C ∧
      connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
  have hK : IsCompact (A ∪ B) := hA.union hB
  have hxy : y ∉ connectedComponentIn (A ∪ B)ᶜ x := fun h => hsep (connectedComponentIn_eq h)
  obtain ⟨C₀, hC₀sub, hC₀pre, -, hC₀sep⟩ :=
    Work.Smooth.JordanSeparation.exists_continuum_separating hK hx hy hxy
  have hsub : closure C₀ ⊆ A ∪ B := closure_minimal hC₀sub hK.isClosed
  have hpre : IsPreconnected (closure C₀) := hC₀pre.closure
  have hy_cl : y ∈ (closure C₀)ᶜ := fun h => hy (hsub h)
  have hsep' : connectedComponentIn (closure C₀)ᶜ x ≠ connectedComponentIn (closure C₀)ᶜ y := by
    intro h
    apply hC₀sep
    have hmono : connectedComponentIn (closure C₀)ᶜ x ⊆ connectedComponentIn C₀ᶜ x :=
      connectedComponentIn_mono x (fun z hz => fun hzC => hz (subset_closure hzC))
    have hyx : y ∈ connectedComponentIn (closure C₀)ᶜ x :=
      h.symm ▸ mem_connectedComponentIn hy_cl
    exact hmono hyx
  obtain ⟨hpC, hqC⟩ := sep_continuum_contains_pair hA hB hAc hBc hpq hint hsub hpre
    isClosed_closure hx hy hsep'
  exact ⟨closure C₀, hsub, hpre, isClosed_closure, hpC, hqC, hsep'⟩

/-- **(Frontier mechanism.)**  Let `C ⊆ A ∪ B` be a continuum with `p, q ∈ C`, let `U` be the
component of `x ∈ (A ∪ B)ᶜ` in `Cᶜ` (so `U = connectedComponentIn Cᶜ x`), and let `y ∈ (A ∪ B)ᶜ`
lie outside `U`.  Then `frontier U` is a **continuum contained in `A ∪ B` and containing both `p`
and `q`**.

* preconnected: the Borsuk/Brouwer property for the continuum `C`
  (`borsuk_frontier_connectedComponentIn`);
* `frontier U ⊆ C`: `frontier U = closure U \ U` (`U` is open), and `Cᶜ \ U` is open because its
  complement inside the open set `Cᶜ` is the union of the *other* components of `Cᶜ`, each open;
  so a ball around `z` misses `U`, contradicting `z ∈ closure U`;
* `U` is a component of `ℂ \ frontier U` (`closure U = U ∪ frontier U` and the disjoint open sets
  `U`, `(closure U)ᶜ` cover `ℂ \ frontier U`), so `frontier U` separates `x` from `y ∉ U` and
  Step 1 applies. -/
theorem frontier_component_contains_pair {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) {p q : ℂ} (hpq : p ≠ q)
    (hint : A ∩ B = {p, q})
    {C : Set ℂ} (hCsub : C ⊆ A ∪ B) (hCpre : IsPreconnected C) (hCcl : IsClosed C)
    {x y : ℂ} {U : Set ℂ} (hU : U = connectedComponentIn Cᶜ x)
    (hx : x ∈ (A ∪ B)ᶜ) (hy : y ∈ (A ∪ B)ᶜ) (hyU : y ∉ U) :
    IsPreconnected (frontier U) ∧ p ∈ frontier U ∧ q ∈ frontier U := by
  have hCcpt : IsCompact C := IsCompact.of_isClosed_subset (hA.union hB) hCcl hCsub
  have hCopen : IsOpen (Cᶜ : Set ℂ) := hCcl.isOpen_compl
  have hUopen : IsOpen U := by rw [hU]; exact hCopen.connectedComponentIn
  have hUsub : U ⊆ Cᶜ := by rw [hU]; exact connectedComponentIn_subset Cᶜ x
  have hxU : x ∈ U := by rw [hU]; exact mem_connectedComponentIn (fun hxC => hx (hCsub hxC))
  have hpre : IsPreconnected (frontier U) := by
    rw [hU]
    exact Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn hCcpt hCpre x
  -- `Cᶜ \ U` is open, because it is the union of the other components of the open set `Cᶜ`
  have hopen : IsOpen (Cᶜ \ U) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hVopen : IsOpen (connectedComponentIn Cᶜ z) := hCopen.connectedComponentIn
    have hzV : z ∈ connectedComponentIn Cᶜ z := mem_connectedComponentIn hz.1
    have hVsub : connectedComponentIn Cᶜ z ⊆ Cᶜ \ U := by
      intro w hw
      refine ⟨connectedComponentIn_subset Cᶜ z hw, ?_⟩
      intro hwU
      have h1 : connectedComponentIn Cᶜ z = connectedComponentIn Cᶜ w := connectedComponentIn_eq hw
      have h2 : connectedComponentIn Cᶜ w = connectedComponentIn Cᶜ x :=
        (connectedComponentIn_eq (hU ▸ hwU)).symm
      have hz' : z ∈ connectedComponentIn Cᶜ z := mem_connectedComponentIn hz.1
      rw [h1, h2, ← hU] at hz'
      exact hz.2 hz'
    exact Filter.mem_of_superset (hVopen.mem_nhds hzV) hVsub
  -- the frontier lies in `C`
  have hfrC : frontier U ⊆ C := by
    intro z hz
    by_contra hzC
    have hzU : z ∈ U := by
      by_contra hzU
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z ⟨hzC, hzU⟩
      obtain ⟨u, huU, hzu⟩ := Metric.mem_closure_iff.mp hz.1 ε hε
      exact (hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hzu))).2 huU
    rw [hUopen.frontier_eq] at hz
    exact hz.2 hzU
  -- `U` is a component of `ℂ \ frontier U`
  have hUcomp : connectedComponentIn (frontier U)ᶜ x ⊆ U := by
    have hsub : connectedComponentIn (frontier U)ᶜ x ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      have hz' : z ∉ frontier U := connectedComponentIn_subset _ _ hz
      rw [hUopen.frontier_eq] at hz'
      by_cases hzc : z ∈ closure U
      · exact Or.inl (by by_contra hzU; exact hz' ⟨hzc, hzU⟩)
      · exact Or.inr hzc
    have hdisj : Disjoint U (closure U)ᶜ := by
      rw [Set.disjoint_left]
      intro z hzU hzcl
      exact hzcl (subset_closure hzU)
    rcases (isPreconnected_connectedComponentIn (x := x) (F := (frontier U)ᶜ)).subset_or_subset
      hUopen isClosed_closure.isOpen_compl hdisj hsub with h | h
    · exact h
    · exfalso
      have hx' : x ∈ connectedComponentIn (frontier U)ᶜ x :=
        mem_connectedComponentIn (fun hxfr => (hUopen.frontier_eq ▸ hxfr).2 hxU)
      exact absurd (h hx') (fun hh => hh (subset_closure hxU))
  have hsepU : y ∉ connectedComponentIn (frontier U)ᶜ x := fun h => hyU (hUcomp h)
  have hsep : connectedComponentIn (frontier U)ᶜ x ≠ connectedComponentIn (frontier U)ᶜ y := by
    intro h
    have hyfr : y ∈ (frontier U)ᶜ := fun hfy => hy (hCsub (hfrC hfy))
    exact hsepU (h.symm ▸ mem_connectedComponentIn hyfr)
  obtain ⟨hp, hq⟩ := sep_continuum_contains_pair hA hB hAc hBc hpq hint
    (fun z hz => hCsub (hfrC hz)) hpre isClosed_frontier hx hy hsep
  exact ⟨hpre, hp, hq⟩


end

end Work.Spike
