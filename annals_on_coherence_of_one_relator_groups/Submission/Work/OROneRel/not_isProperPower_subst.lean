import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.substDefs
import Submission.Work.OROneRel.powSubst_injective
import Submission.Work.OROneRel.npsubstDefs
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.eq_flatten_replicate_of_cyclicallyReduced_of_pow
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced
import Submission.Work.OROneRel.rotate_flatten_replicate
import Submission.Work.OROneRel.isProperPower_subst_iff_powSubst
import Submission.Work.OROneRel.parseT_blkT
import Submission.Work.OROneRel.powSubst_toWord
import Submission.Work.OROneRel.parseT_append_of_startsNonT
import Submission.Work.OROneRel.assembleT_parseT_of_startsNonT
import Submission.Work.OROneRel.isTRun_of_mem_parseT
import Submission.Work.OROneRel.parseT_flatten_replicate_of_startsNonT
import Submission.Work.OROneRel.isCyclicallyReduced_powSubst

namespace Work.OROneRel

universe u

variable {β : Type u}


/-! ## Elementary list facts -/

theorem StartsNonT.append_of_left {t : β} {A B : List (β × Bool)} (hA : StartsNonT t A)
    (hne : A ≠ []) : StartsNonT t (A ++ B) := by
  intro c rest h
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : a.1 ≠ t := hA a A' rfl
  rw [List.cons_append] at h
  injection h with h1 _
  rw [← h1]; exact ha

theorem assembleT_eq_nil_iff (P : List ((β × Bool) × List (β × Bool))) :
    assembleT P = [] ↔ P = [] := by
  constructor
  · intro h
    cases P with
    | nil => rfl
    | cons q P' =>
      obtain ⟨c, R⟩ := q
      rw [assembleT_cons] at h
      exact absurd h (by simp)
  · rintro rfl; rfl

theorem head?_flatten_replicate {σ : Type*} {A : List σ} {k : ℕ} (hk : 1 ≤ k) (hA : A ≠ []) :
    ((List.replicate k A).flatten).head? = A.head? := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  have hk' : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk']
  rw [List.replicate_succ, List.flatten_cons]
  simp

theorem parseT_ne_nil_of_startsNonT [DecidableEq β] {t : β} {L : List (β × Bool)}
    (hL : StartsNonT t L) (hne : L ≠ []) : parseT t L ≠ [] := by
  obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [parseT_cons_of_ne (hL c rest rfl)]
  simp

theorem blkT_length_of_all_fst_eq [DecidableEq β] {t : β} (p : ℤ) {X : List (β × Bool)}
    (hX : ∀ c ∈ X, c.1 = t) : (blkT t p X).length = p.natAbs * X.length := by
  induction X with
  | nil => simp [blkT]
  | cons c rest ih =>
    have hc : c.1 = t := hX c (by simp)
    have hrest : ∀ d ∈ rest, d.1 = t := fun d hd => hX d (by simp [hd])
    rw [blkT_cons, List.length_append, blk_of_eq hc, List.length_replicate, ih hrest,
      List.length_cons]
    ring

/-- `blk` in the form in which the colleague's `powSubst_toWord` states the block. -/
theorem blk_eq_ite [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0) (c : β × Bool) :
    blk t p c =
      (if c.1 = t then List.replicate p.natAbs (t, if 0 < p then c.2 else !c.2) else [c]) := by
  by_cases h : c.1 = t
  · rw [blk_of_eq h, if_pos h]
    have hsign : signShift p c.2 = (if 0 < p then c.2 else !c.2) := by
      rcases lt_or_gt_of_ne (Ne.symm hp) with hlt | hgt
      · rw [signShift_pos hlt, if_pos hlt]
      · rw [signShift_neg hgt, if_neg (by omega)]
    rw [hsign]
  · rw [blk_of_ne h, if_neg h]

/-! ## The word-level core

A `k`-th power of a word, substituted letter by letter by the blocks of `t ↦ t ^ p`, can only come
from a `k`-th power of the original word. -/

/-- **The core, for a word starting with a non-`t` letter.** -/
theorem exists_replicate_flatten_of_blkT_eq_flatten_of_startsNonT [DecidableEq β] {t : β} {p : ℤ}
    (hp : p ≠ 0) {L : List (β × Bool)} (hred : FreeGroup.IsReduced L) (hstarts : StartsNonT t L)
    {A : List (β × Bool)} {k : ℕ} (hk : 2 ≤ k) (hA : A ≠ [])
    (h : blkT t p L = (List.replicate k A).flatten) :
    ∃ V : List (β × Bool), V ≠ [] ∧ L = (List.replicate k V).flatten := by
  have hk1 : 1 ≤ k := by omega
  have hWstarts : StartsNonT t (blkT t p L) := startsNonT_blkT hstarts
  -- `A` starts with a non-`t` letter as well
  have hAstarts : StartsNonT t A := by
    intro c rest hc
    have hWhead : (blkT t p L).head? = some c := by
      rw [h, head?_flatten_replicate hk1 hA, hc]
      rfl
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp hWhead
    exact hWstarts c l hl
  -- the two run decompositions of `blkT t p L` agree
  have hpar : (parseT t L).map (fun q => (q.1, blkT t p q.2)) =
      (List.replicate k (parseT t A)).flatten := by
    rw [← parseT_blkT (t := t) p hstarts, h, parseT_flatten_replicate_of_startsNonT hAstarts k]
  -- undo the blocks on the runs
  have h3 : (parseT t L).map (fun q => (q.1, unblk t p (blkT t p q.2))) =
      ((List.replicate k (parseT t A)).flatten).map (fun q => (q.1, unblk t p q.2)) := by
    rw [← hpar, List.map_map]
    rfl
  have h4 : (parseT t L).map (fun q => (q.1, unblk t p (blkT t p q.2))) = parseT t L := by
    refine (List.map_congr_left fun q hq => ?_).trans (List.map_id (parseT t L))
    have hstep : unblk t p (blkT t p q.2) = q.2 :=
      unblk_blkT_of_isTRun (p := p) hp (isTRun_of_mem_parseT hred q hq)
    simp [hstep, Prod.mk.eta]
  have h5 : parseT t L =
      (List.replicate k ((parseT t A).map (fun q => (q.1, unblk t p q.2)))).flatten := by
    rw [← h4, h3, map_flatten_replicate]
  refine ⟨assembleT ((parseT t A).map (fun q => (q.1, unblk t p q.2))), ?_, ?_⟩
  · intro hnil
    have hP : (parseT t A).map (fun q => (q.1, unblk t p q.2)) = [] :=
      (assembleT_eq_nil_iff _).mp hnil
    exact parseT_ne_nil_of_startsNonT hAstarts hA (List.map_eq_nil_iff.mp hP)
  · rw [← assembleT_parseT_of_startsNonT hstarts, h5, assembleT_flatten_replicate]

/-- **The word-level core.**  If the block substitution of a cyclically reduced word is a `k`-th
power (as a word, `k ≥ 2`) of a nonempty word, then the word itself is a `k`-th power.  The all-`t`
case is excluded by the hypothesis that some letter of `L` differs from `t`. -/
theorem exists_replicate_flatten_of_blkT_eq_flatten [DecidableEq β] {t : β} {p : ℤ} (hp : p ≠ 0)
    {L : List (β × Bool)} (hcyc : FreeGroup.IsCyclicallyReduced L)
    (hnt : ∃ c ∈ L, c.1 ≠ t) {A : List (β × Bool)} {k : ℕ} (hk : 2 ≤ k) (hA : A ≠ [])
    (h : blkT t p L = (List.replicate k A).flatten) :
    ∃ V : List (β × Bool), V ≠ [] ∧ L = (List.replicate k V).flatten := by
  classical
  -- rotate `L` so that it starts with a non-`t` letter
  set R := L.takeWhile (isT t) with hR
  set M := L.dropWhile (isT t) with hM
  have hsplit : L = R ++ M := by
    rw [hR, hM]
    exact (List.takeWhile_append_dropWhile (p := isT t) (l := L)).symm
  have hnle : R.length ≤ L.length := by
    rw [hR]
    exact (List.takeWhile_prefix (isT t) (l := L)).sublist.length_le
  set L' := L.rotate R.length with hL'def
  have hL'eq : L' = M ++ R := by
    rw [hL'def, List.rotate_eq_drop_append_take hnle, hsplit, List.drop_left, List.take_left]
  have hMne : M ≠ [] := by
    intro hnil
    obtain ⟨c, hc, hct⟩ := hnt
    rw [hM] at hnil
    exact hct (isT_eq_true_iff.mp ((List.dropWhile_eq_nil_iff.mp hnil) c hc))
  have hstarts' : StartsNonT t L' := by
    rw [hL'eq]
    exact StartsNonT.append_of_left (hM ▸ startsNonT_dropWhile t L) hMne
  have hred' : FreeGroup.IsReduced L' :=
    isReduced_rotate_of_isCyclicallyReduced hcyc R.length
  have hlenR : (blkT t p R).length = p.natAbs * R.length := by
    rw [hR]
    exact blkT_length_of_all_fst_eq p (startsNonT_takeWhile_all t L)
  have hrot : (blkT t p L).rotate (p.natAbs * R.length) = blkT t p M ++ blkT t p R := by
    rw [← hlenR, hsplit, blkT_append]
    rw [List.rotate_eq_drop_append_take (by rw [List.length_append]; exact Nat.le_add_right _ _)]
    rw [List.drop_left, List.take_left]
  have h' : blkT t p L' = (List.replicate k (A.rotate (p.natAbs * R.length))).flatten := by
    calc blkT t p L' = blkT t p M ++ blkT t p R := by rw [hL'eq, blkT_append]
      _ = (blkT t p L).rotate (p.natAbs * R.length) := hrot.symm
      _ = ((List.replicate k A).flatten).rotate (p.natAbs * R.length) := by rw [h]
      _ = (List.replicate k (A.rotate (p.natAbs * R.length))).flatten :=
            rotate_flatten_replicate k _ A
  have hA' : A.rotate (p.natAbs * R.length) ≠ [] :=
    fun hnil => hA (List.rotate_eq_nil_iff.mp hnil)
  obtain ⟨V, hVne, hV⟩ :=
    exists_replicate_flatten_of_blkT_eq_flatten_of_startsNonT hp hred' hstarts' hk hA' h'
  refine ⟨V.rotate (L.length - R.length), fun hnil => hVne (List.rotate_eq_nil_iff.mp hnil), ?_⟩
  have hback : L = L'.rotate (L.length - R.length) := by
    rw [hL'def, List.rotate_rotate, Nat.add_sub_cancel' hnle, List.rotate_length]
  conv_lhs => rw [hback]
  rw [hV, rotate_flatten_replicate]

/-! ## The exponent sum sees only the letters of the word -/

/-- If the generator `a` does not occur in the word `L`, then the exponent sum of `a` in `mk L`
vanishes. -/
theorem sigma_mk_eq_one_of_notMem [DecidableEq β] (a : β) (L : List (β × Bool))
    (h : ∀ c ∈ L, c.1 ≠ a) : sigma a (FreeGroup.mk L) = 1 := by
  rw [sigma, FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons c rest ih =>
    have hc : c.1 ≠ a := h c (by simp)
    have hrest : ∀ d ∈ rest, d.1 ≠ a := fun d hd => h d (by simp [hd])
    rw [List.map_cons, List.prod_cons, ih hrest, mul_one]
    cases c.2 <;> simp [hc]

/-! ## The group-level statement -/

/-- The substituted relator `subst t x (σ_x T) (σ_t T) T` is not a proper power when `T` is
cyclically reduced, not a proper power, and `σ_x T ≠ 0`.  Proof route: `subst t x p q = α ∘ β` with `α`
the automorphism `x ↦ x t^{-q}` and `β : t ↦ t^p` fixing the other letters; `β` multiplies every
maximal `t`-run of a reduced word by `p` without changing the sequence of other letters, so a
proper-power decomposition of `β(T)` forces the same decomposition of `T` (syllables of the free
product `F(β \ {t}) * ⟨t⟩`; `¬ IsProperPower T` gives the contradiction). -/
theorem not_isProperPower_subst {β : Type u} (T : FreeGroup β) {t x : β} (hxt : x ≠ t)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator T)
    (hpp : ¬ Work.OROneRel.IsProperPower T)
    (hp : Multiplicative.toAdd (Work.OROneRel.sigma x T) ≠ 0) :
    ¬ Work.OROneRel.IsProperPower
      (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x T))
        (Multiplicative.toAdd (Work.OROneRel.sigma t T)) T) := by
  classical
  intro hcon
  -- reduce to the Nielsen substitution `t ↦ t^p`, where `t ^ p` is the image of `t`
  have hpw : IsProperPower (powSubst t (Multiplicative.toAdd (sigma x T)) T) :=
    (isProperPower_subst_iff_powSubst T hxt (Multiplicative.toAdd (sigma x T))
      (Multiplicative.toAdd (sigma t T))).mp hcon
  obtain ⟨U, k, hk, hUk⟩ := hpw
  have hT1 : T ≠ 1 := ne_one_of_not_isProperPower hpp
  have hLred : FreeGroup.IsReduced T.toWord := FreeGroup.isReduced_toWord
  have hLcyc : FreeGroup.IsCyclicallyReduced T.toWord := hcyc
  have hredW : FreeGroup.IsReduced (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord :=
    FreeGroup.isReduced_toWord
  have hWcyc : FreeGroup.IsCyclicallyReduced
      (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord := by
    simpa [FreeGroup.mk_toWord] using
      isCyclicallyReduced_powSubst (L := T.toWord) t (Multiplicative.toAdd (sigma x T)) hp
        hLred hLcyc
  -- the reduced word of the substituted relator is a `k`-th power of a word
  obtain ⟨A, hA⟩ := eq_flatten_replicate_of_cyclicallyReduced_of_pow hredW hWcyc hk
    (by rw [FreeGroup.mk_toWord]; exact hUk)
  have hWne : (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord ≠ [] := by
    intro h0
    refine hT1 (powSubst_injective t (Multiplicative.toAdd (sigma x T)) hp ?_)
    rw [map_one, FreeGroup.toWord_eq_nil_iff.mp h0]
  have hAne : A ≠ [] := by
    intro h0
    exact hWne (by rw [hA, h0]; simp)
  -- hence so is the block substitution of the word of `T`
  have hblk : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
      = (List.replicate k A).flatten := by
    have hgen : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
        = (powSubst t (Multiplicative.toAdd (sigma x T)) (FreeGroup.mk T.toWord)).toWord := by
      rw [powSubst_toWord (L := T.toWord) t (Multiplicative.toAdd (sigma x T)) hp hLred]
      simp only [blkT]
      congr 1
      exact List.map_congr_left fun c _ => blk_eq_ite hp c
    have h1 : blkT t (Multiplicative.toAdd (sigma x T)) T.toWord
        = (powSubst t (Multiplicative.toAdd (sigma x T)) T).toWord := by
      simpa [FreeGroup.mk_toWord] using hgen
    rw [h1, hA]
  -- some letter of `T` is different from `t`: the letter `x`
  have hnt : ∃ c ∈ T.toWord, c.1 ≠ t := by
    have hσx : sigma x T ≠ 1 := fun h1 => hp (by rw [h1]; rfl)
    have hx : x ∈ relatorLetters T := by
      by_contra hxm
      have hnot : ∀ c ∈ T.toWord, c.1 ≠ x := by
        intro c hc hcon
        exact hxm (by rw [relatorLetters]; exact ⟨c.2, by rw [← hcon]; exact hc⟩)
      exact hσx (by
        rw [← FreeGroup.mk_toWord (x := T)]
        exact sigma_mk_eq_one_of_notMem x T.toWord hnot)
    rw [relatorLetters] at hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨(x, b), hb, hxt⟩
  obtain ⟨V, hVne, hV⟩ :=
    exists_replicate_flatten_of_blkT_eq_flatten hp hLcyc hnt hk hAne hblk
  refine hpp ⟨FreeGroup.mk V, k, hk, ?_⟩
  rw [← FreeGroup.mk_toWord (x := T), hV, mk_flatten_replicate]

end Work.OROneRel
