/-
  `BadScale Y B E ε` is the set of scales `M > 0` at which some `M`-deep doubling ratio is at
  multiplicative distance `> ε` from every positive element of `E`.  The claim below is the
  `∅`-definability of the two-variable relation `{(M, ε) | M ∈ BadScale Y B E ε}` in `LRc`,
  given the `∅`-definability of `Y`, `B`, `E`.

  IMPORTANT CONSTRAINT.  The file does **not** import `Submission.Work.WilC4.DevBddDefs`, nor
  `DevBdd_definable`, `DevDeep_definable`, `DevRatW_definable`, `DevConc_definable`, `dev_rate`,
  or `dev_rate_devBdd`: those modules are *not* usable here, so the shortcut
  (`DevBdd_definable` plus the pointwise equivalence `M ∈ BadScale Y B E ε ↔ 0 < M ∧
  ¬ DevBdd Y B E M ε`, the latter proved in `dev_rate_devBdd.lean` as `mem_badScale_iff`) is
  replaced by a self-contained proof.  Reason: the public index abbreviations `dc dx dw dy`
  declared in `DevBddDefs` (as `DevI k → ℝ`) collide with the ones declared in
  `Submission.Work.WilC4.DeepThetaGDefs` (as `DRIdx k → ℝ`), and `DeepThetaGDefs` is in the
  import closure of `deep_ratio_bdd` / `dev_decay_E`; no module importing both vocabulary chains
  can elaborate.  Everything here uses only `ULPMDev`-level imports.

  ## The proof

  `Submission/Work/WilC4/badScale_aux.lean` declares the vocabulary: the index blocks
  `BSPar k = Fin k ⊕ Fin 2` (carrying `(c, x, w)`), `BSI k = Fin 2 ⊕ BSPar k` (carrying the free
  `(M, ε)` together with `(c, x, w)`), the ambient blocks `BSD k`, `BSR k`, `BSC k` of the three
  quantifier-free "bodies" `BSDeepBody B`, `BSRatWBody Y`, `BSConcBody E`, together with the
  projections

    `BSDeep B = {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ BSDeepBody B}`   (the deepness condition),
    `BSRatW Y = {g | ∃ u : Fin 3 → ℝ, Sum.elim g u ∈ BSRatWBody Y}`   (the doubling ratio),
    `BSSpec E = {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ BSConcBody E}`   (the failure of the
                                                                       cluster-value clause).

  Each body is a quantifier-free Boolean combination of reindexings of `Y`, `B`, `E` (along
  `GrSub`, `GrSub1`) and of the arithmetic atoms `IsDivR`, `≤`, `≠`, `=`; their `univ`-definability
  is proved in the modules `Submission/Work/WilC4/BSpieces/*.lean`, and
  `Set.Definable.exists_of_finite` / `forall_of_finite` turn the bodies into the projections.  The
  semantic identifications `mem_BSRatW_iff`, `mem_BSSpec_iff` and `BSpieces.mem_BSDeep_iff`
  reconstruct the predicates of `BadScale`, and the set identity `badScale_rel_eq` reassembles it.

  Every set is first shown `univ`-definable and converted to `∅`-definability with
  `definable_univ_iff_empty` (every real is a constant of `LRc`).
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMRoute
import Submission.Work.WilC4.ratGraph_definable
import Submission.Work.WilC4.DiagDefs
import Submission.Work.WilC4.definable_isGLB_family
import Submission.Work.WilC4.badScale_aux
import Submission.Work.WilC4.BSpieces.deepBody_definable
import Submission.Work.WilC4.BSpieces.mem_BSDeep_iff
import Submission.Work.WilC4.BSpieces.ratWBody_definable
import Submission.Work.WilC4.BSpieces.concBody_definable

set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)
open Work.WilC4.Route (Gr)

namespace BSAux

/-! ## 1. Membership descriptions -/

/-- Membership in the ratio body, read off the ambient coordinates: the two reindexings of `Y`
give the value at the `x` slot `sx` and the value at the auxiliary slot `Sum.inr 2`. -/
theorem mem_BSRatWBody_iff {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (g : BSI k → ℝ)
    (u : Fin 3 → ℝ) :
    Sum.elim g u ∈ BSRatWBody Y ↔
      (Gr Y (fun i : Fin k => g (sc i)) (g sx) (u 0) ∧
       Gr Y (fun i : Fin k => g (sc i)) (u 2) (u 1) ∧
       u 2 = 2 * g sx ∧ u 0 ≠ 0 ∧ g sw * u 0 = u 1) := by
  have hcomp : (Sum.elim g u) ∘ (yEmb k ∘ Fin.succ) = fun i : Fin k => g (sc i) := by
    funext i; rfl
  simp only [BSRatWBody, Set.mem_ofPred_eq, Set.mem_inter_iff, GrSub, Gr, hcomp,
    Sum.elim_inl, Sum.elim_inr]

/-- `g ∈ BSRatW Y` is the doubling-ratio relation `RatW` of `ULPMDev`. -/
theorem mem_BSRatW_iff {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (g : BSI k → ℝ) :
    g ∈ BSRatW Y ↔ RatW Y (fun i : Fin k => g (sc i)) (g sx) (g sw) := by
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_BSRatWBody_iff] at hu
    obtain ⟨h1, h2, h3, h4, h5⟩ := hu
    refine ⟨u 0, u 1, h1, ?_, h4, h5⟩
    rw [h3] at h2
    exact h2
  · rintro ⟨y, y', h1, h2, h3, h4⟩
    refine ⟨![y, y', 2 * g sx], ?_⟩
    rw [mem_BSRatWBody_iff]
    exact ⟨h1, h2, by simp, by simpa using h3, by simpa using h4⟩

/-- `g ∈ BSSpec E` is the clause `∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|`.  The auxiliary quotient `q`
of the body is universally quantified as well, which is equivalent since `q = w/ρ` is unique as
soon as `ρ ≠ 0`. -/
theorem mem_BSSpec_iff {k : ℕ} (E : Set ℝ) (g : BSI k → ℝ) :
    g ∈ BSSpec (k := k) E ↔
      ∀ ρ ∈ E, 0 < ρ → g sEps < |g sw / ρ - 1| := by
  constructor
  · intro h ρ hρE hρ0
    have hbody : Sum.elim g ![ρ, g sw / ρ] ∉ BSConcBody (k := k) E := h ![ρ, g sw / ρ]
    by_contra hcon
    apply hbody
    simp only [BSConcBody, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    refine ⟨hρE, hρ0, (isDivR_iff _ _ _).mpr rfl, ?_, ?_⟩
    · exact (abs_le.mp (le_of_not_gt hcon)).1
    · exact (abs_le.mp (le_of_not_gt hcon)).2
  · intro h u hbody
    simp only [BSConcBody, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hbody
    obtain ⟨hρE, hρ0, hdiv, h1, h2⟩ := hbody
    have hq : u 1 = g sw / u 0 := ((isDivR_iff _ _ _).mp hdiv).symm
    have habs : |g sw / u 0 - 1| ≤ g sEps := by
      rw [← hq]; exact abs_le.mpr ⟨h1, h2⟩
    exact absurd (h (u 0) hρE hρ0) (not_lt.mpr habs)

/-- The inner set `BSInner Y B E`, read off its four clauses. -/
theorem mem_BSInner_iff {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (B : Set (Fin (k+1) → ℝ))
    (E : Set ℝ) (g : BSI k → ℝ) :
    g ∈ BSInner Y B E ↔ 0 < g sx ∧ g ∈ BSDeep B ∧ g ∈ BSRatW Y ∧ g ∈ BSSpec E := by
  simp only [BSInner, BSPos, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- `BadScale` read as a formula, with the quantified blocks spelled out. -/
theorem mem_BadScale_iff {k : ℕ} (Y : Set (Fin (k+2) → ℝ)) (B : Set (Fin (k+1) → ℝ))
    (E : Set ℝ) (M ε : ℝ) :
    M ∈ BadScale Y B E ε ↔ 0 < M ∧ ∃ (c : Fin k → ℝ) (x w : ℝ),
      0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧ ∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1| :=
  Iff.rfl

/-! ## 2. Definability of the projections -/

theorem BSPos_definable {k : ℕ} : (∅ : Set ℝ).Definable LRc (BSPos (k := k)) :=
  definable_lt_const (ρ := BSI k) (0 : ℝ) (sx : BSI k)

theorem BSDeep_definable {k : ℕ} {B : Set (Fin (k+1) → ℝ)}
    (hB : (∅ : Set ℝ).Definable LRc B) :
    (∅ : Set ℝ).Definable LRc (BSDeep (k := k) B) := by
  have h := (BSpieces.deepBody_definable (k := k) hB).compl.forall_of_finite
    (α := BSI k) (β := Fin 2)
  have hset : {g : BSI k → ℝ | ∀ u : Fin 2 → ℝ, Sum.elim g u ∈ (BSDeepBody (k := k) B)ᶜ}
      = BSDeep (k := k) B := rfl
  rw [hset] at h
  exact (definable_univ_iff_empty).mp h

theorem BSRatW_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (BSRatW (k := k) Y) := by
  have h := (BSpieces.ratWBody_definable (k := k) hY).exists_of_finite (α := BSI k) (β := Fin 3)
  have hset : {g : BSI k → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim g u ∈ BSRatWBody (k := k) Y}
      = BSRatW (k := k) Y := rfl
  rw [hset] at h
  exact (definable_univ_iff_empty).mp h

theorem BSSpec_definable {k : ℕ} {E : Set ℝ}
    (hE : (∅ : Set ℝ).Definable₁ LRc E) :
    (∅ : Set ℝ).Definable LRc (BSSpec (k := k) E) := by
  have h := (BSpieces.concBody_definable (k := k) hE).compl.forall_of_finite
    (α := BSI k) (β := Fin 2)
  have hset : {g : BSI k → ℝ | ∀ u : Fin 2 → ℝ, Sum.elim g u ∈ (BSConcBody (k := k) E)ᶜ}
      = BSSpec (k := k) E := rfl
  rw [hset] at h
  exact (definable_univ_iff_empty).mp h

end BSAux

open BSAux

/-! ## 3. The semantic identity -/

/-- The relation of `BadScale` is exactly the outer positivity `0 < M` paired with the finite
existential projection of `BSInner` along the block `BSPar k` of parameters `(c, x, w)`. -/
theorem badScale_rel_eq {k : ℕ}
    (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ) :
    ({v : Fin 2 → ℝ | 0 < v 0} ∩
      {v : Fin 2 → ℝ | ∃ u : BSPar k → ℝ, Sum.elim v u ∈ BSInner Y B E})
      = {v : Fin 2 → ℝ | v 0 ∈ BadScale Y B E (v 1)} := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [mem_BadScale_iff]
  constructor
  · intro h
    obtain ⟨hM, u, hu⟩ := h
    rw [mem_BSInner_iff] at hu
    obtain ⟨hx, hdeep, hrat, hspec⟩ := hu
    exact ⟨hM, (fun i : Fin k => (Sum.elim v u) (sc i)), (Sum.elim v u) sx, (Sum.elim v u) sw,
      hx, (BSpieces.mem_BSDeep_iff B (Sum.elim v u)).mp hdeep,
      (mem_BSRatW_iff Y (Sum.elim v u)).mp hrat,
      (mem_BSSpec_iff E (Sum.elim v u)).mp hspec⟩
  · intro h
    obtain ⟨hM, c, x, w, hx, hdeep, hrat, hspec⟩ := h
    refine ⟨hM, Sum.elim c ![(x : ℝ), w], ?_⟩
    rw [mem_BSInner_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e1 : Sum.elim v (Sum.elim c ![(x : ℝ), w]) sx = x := rfl
      rw [e1]; exact hx
    · have e5 : (fun i : Fin k => (Sum.elim v (Sum.elim c ![(x : ℝ), w])) (sc i)) = c := rfl
      have e2 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sM = v 0 := rfl
      have e1 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sx = x := rfl
      rw [BSpieces.mem_BSDeep_iff B (Sum.elim v (Sum.elim c ![(x : ℝ), w]))]
      rw [e5, e2, e1]
      exact hdeep
    · have e5 : (fun i : Fin k => (Sum.elim v (Sum.elim c ![(x : ℝ), w])) (sc i)) = c := rfl
      have e1 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sx = x := rfl
      have e3 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sw = w := rfl
      rw [mem_BSRatW_iff Y (Sum.elim v (Sum.elim c ![(x : ℝ), w]))]
      rw [e5, e1, e3]
      exact hrat
    · have e4 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sEps = v 1 := rfl
      have e3 : (Sum.elim v (Sum.elim c ![(x : ℝ), w])) sw = w := rfl
      rw [mem_BSSpec_iff E (Sum.elim v (Sum.elim c ![(x : ℝ), w]))]
      intro ρ hρE hρ0
      rw [e4, e3]
      exact hspec ρ hρE hρ0

/-! ## 4. The theorem -/

theorem badScale_definable {k : ℕ}
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (B : Set (Fin (k + 1) → ℝ)) (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (E : Set ℝ) (hE : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc E) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {v : Fin 2 → ℝ | v 0 ∈ Work.WilC4.BadScale Y B E (v 1)} := by
  have hInner : (∅ : Set ℝ).Definable LRc (BSInner (k := k) Y B E) :=
    (((BSPos_definable (k := k)).inter (BSDeep_definable hB)).inter
      (BSRatW_definable hY)).inter (BSSpec_definable hE)
  have hExists : (∅ : Set ℝ).Definable LRc
      {v : Fin 2 → ℝ | ∃ u : BSPar k → ℝ, Sum.elim v u ∈ BSInner (k := k) Y B E} :=
    hInner.exists_of_finite (α := Fin 2) (β := BSPar k)
  have hPos : (∅ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | 0 < v 0} :=
    definable_lt_const (ρ := Fin 2) (0 : ℝ) (0 : Fin 2)
  rw [← badScale_rel_eq Y B E]
  exact hPos.inter hExists

end Work.WilC4
