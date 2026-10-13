import Mathlib
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilCrux.TripleMem
import Submission.Work.WilCrux.Clean.AccSetDefs
import Submission.Work.WilCrux.Clean.QsetMem
import Submission.Work.WilCrux.Clean.MemQset

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux.Clean

open WilkiesDesign

/-
## `Work.WilCrux.Clean.AccSetMem`

The *accumulation set* of an `Ω`-definable set `E ⊆ ℝ^{a+b}`,

`acc E = {w : ℝ^a | ∀ δ > 0, ∃ z : ℝ^b, 0 < ‖z‖ ∧ ‖z‖ < δ ∧ (w,z) ∈ E}`,

is `Ω`-definable.  The two quantifiers are absorbed in the `Ω`-calculus exactly as follows.

Let `Qset a b E ⊆ ℝ^{(a+1)+b}` (coordinates `(w, δ, z)`, see `AccSetDefs`) be the pullback of
`E` along `iIdx` — which reads `(w,z)` — intersected with `δ > 0`, `z ≠ 0` and `|z j| < δ`.
Write `J = projN b (Qset a b E) ⊆ ℝ^{a+1}`, so that `(w,δ) ∈ J` iff *some* `z` witnesses the
inner `∃` at scale `δ`.  Then

`w ∉ acc E ↔ ∃ δ > 0, (w,δ) ∉ J ↔ w ∈ projLast (Jᶜ ∩ {δ > 0})`,

so that `acc E = (projLast (Jᶜ ∩ {δ > 0}))ᶜ`: the *outer* `∀ δ > 0` becomes an `∃δ` after
negation (absorbed by the projection `projLast`), and the *inner* `∃ z` becomes a `∀ z` after
negation (absorbed by the complement of `J`).  Composing with the `Ω`-calculus gives the claim.

The complementary conjunct `δ > 0` in `Qset` is redundant in the sense of `MemQset` (the
condition `‖z‖ < δ` already forces `δ > 0`), but it keeps `Qset` `Ω`-definable for `b = 0`,
where the `b`-fold intersection of coordinate strips degenerates to `univ`.

The degenerate case `b = 0` is disposed of separately: `Fin 0 → ℝ` is a subsingleton, so
`acc E = ∅`, which is `Ω`-definable by `Work.WilG5.empty_mem`.

The pieces are:
* `Work.WilCrux.Clean.QsetMem` — `Qset a b E` is `Ω`-definable;
* `Work.WilCrux.Clean.MemQset` — the reading of `Qset` at a point `Fin.append (Fin.snoc v t) z`;
* `AccSetDefs` — the coordinate maps `zIdx`, `dIdx`, `iIdx`, the set `Qset` and the binary
  intersection `inter2_mem`.
-/

/-- **The accumulation set of an `Ω`-set is `Ω`-definable.**  If `E ⊆ ℝ^{a+b}` lies in
`S.Ω F D (a+b)`, then the set of `w : ℝ^a` such that the fibre `{z | (w,z) ∈ E}` has points of
arbitrarily small strictly positive norm (equivalently: `0` is a limit point of the fibre
`{z | (w,z) ∈ E} \ {0}`) lies in `S.Ω F' D' a` for some `F'`, `D'`. -/
theorem AccSetMem (S : WilkiesDesign.SOMin) {a b F D : ℕ} (E : Set (Fin (a + b) → ℝ))
    (hE : E ∈ S.Ω F D (a + b)) :
    ∃ F' D' : ℕ, {w : Fin a → ℝ | ∀ δ : ℝ, 0 < δ → ∃ z : Fin b → ℝ,
      0 < ‖z‖ ∧ ‖z‖ < δ ∧ Fin.append w z ∈ E} ∈ S.Ω F' D' a := by
  classical
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  · -- `b = 0`: `Fin 0 → ℝ` is a subsingleton, so the set is empty
    subst hb0
    refine ⟨a + 6, 4, ?_⟩
    have hset : {w : Fin a → ℝ | ∀ δ : ℝ, 0 < δ → ∃ z : Fin 0 → ℝ,
        0 < ‖z‖ ∧ ‖z‖ < δ ∧ Fin.append w z ∈ E} = (∅ : Set (Fin a → ℝ)) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨z, hz1, hz2, hz3⟩ := h 1 (by norm_num)
      have hz0 : z = 0 := by
        funext j
        exact IsEmpty.elim inferInstance j
      rw [hz0, norm_zero] at hz1
      exact absurd hz1 (lt_irrefl 0)
    rw [hset]
    exact Work.WilG5.empty_mem
  · -- main case: `b > 0`
    obtain ⟨FQ, DQ, hQ⟩ := QsetMem (S := S) (a := a) (b := b) (F := F) (D := D) (E := E) hE
    have hJ : Work.WilG5.projN b (Qset a b E) ∈ S.Ω (FQ + b) DQ (a + 1) :=
      Work.WilG5.projN_mem b FQ DQ hQ
    have hH : {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)} ∈ S.Ω ((a + 1) + 2) 3 (a + 1) := by
      have h := Work.WilCrux.posLin_mem (S := S) (N := a + 1)
        (MvPolynomial.X (Fin.last a) : MvPolynomial (Fin (a + 1)) ℝ)
        (Work.WilG5.td_X_le (Fin.last a)) D
      simpa using h
    have hJc : (Work.WilG5.projN b (Qset a b E))ᶜ ∈ S.Ω (FQ + b + 1) DQ (a + 1) := S.compl hJ
    have hG : (Work.WilG5.projN b (Qset a b E))ᶜ ∩
        {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)} ∈
        S.Ω (max (FQ + b + 1) ((a + 1) + 2) + 1) (DQ + 3) (a + 1) := inter2_mem hJc hH
    have hP : WilkiesDesign.projLast ((Work.WilG5.projN b (Qset a b E))ᶜ ∩
        {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)}) ∈
        S.Ω (max (FQ + b + 1) ((a + 1) + 2) + 1 + 1) (DQ + 3) a := S.proj hG
    refine ⟨max (FQ + b + 1) ((a + 1) + 2) + 1 + 1 + 1, DQ + 3, ?_⟩
    have heq : {w : Fin a → ℝ | ∀ δ : ℝ, 0 < δ → ∃ z : Fin b → ℝ,
          0 < ‖z‖ ∧ ‖z‖ < δ ∧ Fin.append w z ∈ E}
        = (WilkiesDesign.projLast ((Work.WilG5.projN b (Qset a b E))ᶜ ∩
            {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)}))ᶜ := by
      ext v
      constructor
      · -- a point of the accumulation set is not in the projection
        intro hv hmem
        rw [WilkiesDesign.projLast] at hmem
        obtain ⟨t, ht⟩ := hmem
        rw [Set.mem_inter_iff] at ht
        obtain ⟨htJ, htH⟩ := ht
        have ht_pos : 0 < t := by simpa only [Set.mem_ofPred_eq, Fin.snoc_last] using htH
        rw [Set.mem_compl_iff, Work.WilG5.projN] at htJ
        simp only [Set.mem_ofPred_eq, not_exists] at htJ
        obtain ⟨z, hz1, hz2, hz3⟩ := hv t ht_pos
        exact htJ z ((MemQset (a := a) (b := b) (E := E) hb v t z).mpr
          ⟨hz3, norm_pos_iff.mp hz1, hz2⟩)
      · -- conversely, a point outside the projection accumulates at `0`
        intro hv δ hδ
        have hnotin : Fin.snoc v δ ∉ (Work.WilG5.projN b (Qset a b E))ᶜ ∩
            {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)} := by
          intro hmem
          exact hv ⟨δ, hmem⟩
        have hHmem : Fin.snoc v δ ∈ {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a)} := by
          simp only [Set.mem_ofPred_eq, Fin.snoc_last]
          exact hδ
        have hJmem : Fin.snoc v δ ∈ Work.WilG5.projN b (Qset a b E) := by
          by_contra hc
          exact hnotin ⟨hc, hHmem⟩
        rw [Work.WilG5.projN] at hJmem
        obtain ⟨z, hz⟩ := hJmem
        obtain ⟨h1, h2, h3⟩ := (MemQset (a := a) (b := b) (E := E) hb v δ z).mp hz
        exact ⟨z, norm_pos_iff.mpr h2, h3, h1⟩
    rw [heq]
    exact Work.WilG5.mem_mono (S.compl hP) _ _ (le_refl _) (le_refl _)

end Work.WilCrux.Clean
