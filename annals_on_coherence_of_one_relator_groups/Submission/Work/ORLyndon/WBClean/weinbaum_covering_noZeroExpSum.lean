import Mathlib
import Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_ne_zero
import Submission.Work.ORLyndon.WBClean.weinbaum_sigma_zero_half
import Submission.Work.OROneRel.wcp_localisation
import Submission.Work.OROneRel.letterCountNot_lt_half_standalone
import Submission.Work.OROneRel.relatorNorm_magRewRel_letterCountNot
import Submission.Work.OROneRel.exists_common_power
import Submission.Work.OROneRel.eq_flatten_replicate_of_cyclicallyReduced_of_pow
import Submission.Work.OROneRel.doubledWord_rotate_or_replicate
import Submission.Work.OROneRel.doubledWord_mk_eq_lift_sq
import Submission.Work.OROneRel.isCyclicallyReduced_doubledWord_of_relator


/-!
# Import-hygiene copy of `Submission.Work.OROneRel.weinbaum_covering_noZeroExpSum`

**This file is a verbatim copy** of `Submission/Work/OROneRel/weinbaum_covering_noZeroExpSum.lean`, moved into the *nested*
namespace `Work.OROneRel.WBClean` (so that inside it every unqualified name still resolves through
the parent namespace to the untouched `Work.OROneRel` development).  The reason is *import hygiene*:
the original reaches `Submission.Work.OROneRel.mrslAux`, which redeclares the public theorem
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` already declared by
`Submission.Work.OROneRel.magnus_step_root` — a dependency of
`Submission.Work.ORLyndon.epsNeZeroDescent` — so no module can import both cones.  Here the
duplicated theorem is renamed `Work.OROneRel.WBClean.toWord_pow_of_isCyclicallyReduced_wbc` and the
imports inside the copied chain are redirected; nothing else is changed.

Consumer: `Submission/Work/ORLyndon/occTerm_distinct_clean.lean`.  Everything in
`Submission/Work/ORLyndon/WBClean/` (and that file) can be deleted as soon as the duplicate
declaration is removed on the `OROneRel` side.
-/
/-!
# Weinbaum's theorem: the covering half-length case, with no zero exponent sum

This file proves `Work.OROneRel.WBClean.weinbaum_covering_noZeroExpSum`: the *half-length* form of Weinbaum's
theorem in the case in which **no** letter of the relator has exponent sum zero, under the additional
hypothesis that the subword `v` covers all the letters of `r`.

## The argument

Weinbaum's theorem in this case is reduced to its exponent-sum-zero case by *padding*, exactly as in
`Work.OROneRel.WBClean.weinbaumAt_of_expSum_ne_zero`.  Choose two distinct letters `x ≠ t` of `r` (they exist
because `2 ≤ relatorNorm r` and `r` is not a proper power, see
`Work.OROneRel.exists_two_mem_relatorLetters_ne`) and let `c = padC r x t` be the padding exponents
`c x = σ_t r`, `c t = -σ_x r`, supported on `{x,t}`.  The padding `padHom c : F α →* F (Option α)`
sends every occurrence of a generator `a` to the block `a * z ^ (c a) * a`, where `z = none` is a
fresh letter:

* `R = padRel c r` is cyclically reduced and contains `z`;
* `z` has **zero** exponent sum in `R`, because `Σ_a σ_a r * c a = σ_x r * σ_t r - σ_t r * σ_x r =
  0`; this is where the hypothesis that every letter has *nonzero* exponent sum enters: it makes `c`
  nonzero;
* the padding sends a subword of a power of `r` to a subword of a power of `R`, and is injective,
  hence sends nontrivial words to nontrivial words;
* the padding sends the normal closure of `r` into the normal closure of `R`, so a word which is
  trivial in `⟨α | r⟩` stays trivial in `⟨α, z | R⟩`;
* finally, since `2 * relatorNorm v ≤ relatorNorm r` and `v` is nontrivial, we have
  `relatorNorm v < relatorNorm r`, whence `relatorNorm (padHom c v) < relatorNorm (padRel c r)`.

So a counterexample `v` to the statement produces a counterexample `padHom c v` to Weinbaum's
theorem for the padded relator `R`, whose exponent-sum-zero case (`weinbaum_sigma_zero_half`,
combined with the complement trick `exists_complement_counterexample`) gives a contradiction.

## Dependency structure of this file

Everything here is proved inside this file from

* the padding library of this directory (`padDefs`, `toWord_padHom`,
  `pad_subword_of_isSubwordOf_pow`, `pad_isCyclicallyReduced`, `none_mem_relatorLetters_padRel`,
  `pad_length_lt`, `expSum_none_padRel_padC`, `exists_two_mem_relatorLetters_ne`),
* the "doubled word" chain proving that the padding of a relator which is not a proper power is not
  a proper power (`isCyclicallyReduced_doubledWord_of_relator`, `doubledWord_mk_eq_lift_sq`,
  `doubledWord_rotate_or_replicate`, `eq_flatten_replicate_of_cyclicallyReduced_of_pow`,
  `isProperPower_mk_of_rotate_eq`, `exists_common_power`), and
* the exponent-sum-zero half-length case of Weinbaum's theorem
  (`Work.OROneRel.WBClean.weinbaum_sigma_zero_half`).

In particular this file does *not* depend on the wrapper modules
`Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_ne_zero` /
`Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_eq_zero`: the two lemmas below are proved here
directly, so that the only unproved input in the closure is the exponent-sum-zero case itself.
-/

namespace Work.OROneRel

namespace WBClean

universe u

variable {α : Type u}

/-! ### The padding

Elementary facts about `padHom`, `padList` and the padded relator, proved directly here (the same
statements exist in `Submission.Work.ORLyndon.WBClean.weinbaumAt_of_expSum_ne_zero`, but re-proving them
keeps this file independent of that module).
-/

/-- Every generator block of the padding is nontrivial. -/
theorem wcp_padGen_ne_one (c : α → ℤ) (a : α) : padGen c a ≠ 1 := by
  intro h1
  have h2 : padProj (padGen c a) = 1 := by rw [h1, map_one]
  have h3 : padProj (padGen c a) = (FreeGroup.of a) ^ (2 : ℕ) := by
    rw [show padGen c a = padHom c (FreeGroup.of a) from (padHom_of c a).symm]
    have h := DFunLike.congr_fun (padProj_padHom c) (FreeGroup.of a)
    simpa using h
  rw [h3] at h2
  rcases (pow_eq_one_iff).mp h2 with h4 | h4
  · exact FreeGroup.of_ne_one a h4
  · omega

/-- Every block of the padding is nonempty. -/
theorem wcp_padBlock_ne_nil (c : α → ℤ) (p : α × Bool) : padBlock c p ≠ [] := by
  classical
  have hne : (if p.2 = true then padGen c p.1 else (padGen c p.1)⁻¹) ≠ 1 := by
    by_cases h : p.2 = true
    · rw [if_pos h]; exact wcp_padGen_ne_one c p.1
    · rw [if_neg h]; exact inv_ne_one.mpr (wcp_padGen_ne_one c p.1)
  have hmk : FreeGroup.mk (padBlock c p) =
      (if p.2 = true then padGen c p.1 else (padGen c p.1)⁻¹) := by
    unfold padBlock
    split <;> exact FreeGroup.mk_toWord
  intro h
  refine hne ?_
  rw [← hmk, h, FreeGroup.one_eq_mk]

/-- The padding of a nonempty word is nonempty. -/
theorem wcp_padList_ne_nil (c : α → ℤ) {L : List (α × Bool)} (hL : L ≠ []) :
    padList c L ≠ [] := by
  classical
  cases L with
  | nil => exact absurd rfl hL
  | cons p L' =>
    rw [padList, List.map_cons, List.flatten_cons]
    intro h
    exact wcp_padBlock_ne_nil c p (List.eq_nil_of_append_eq_nil h).1

/-- The padding is injective on nontrivial words: a nontrivial element has a nontrivial padded image,
because the block decomposition of the padding never cancels, so the padded word of a nonempty word
is nonempty. -/
theorem wcp_padHom_ne_one (c : α → ℤ) {v : FreeGroup α} (hv : v ≠ 1) : padHom c v ≠ 1 := by
  classical
  intro h1
  have htw : (padHom c v).toWord = padList c v.toWord := toWord_padHom c v
  have h2 : (padHom c v).toWord = [] := by rw [h1, FreeGroup.toWord_one]
  rw [htw] at h2
  have h3 : v.toWord = [] := by
    by_contra hne
    exact wcp_padList_ne_nil c hne h2
  exact hv (FreeGroup.toWord_eq_nil_iff.mp h3)

/-- Transfer of triviality along the padding: if `v` is trivial in `⟨α | r⟩` then its padded image
is trivial in `⟨α, z | padRel c r⟩`. -/
theorem wcp_mk_padHom_eq_one {c : α → ℤ} {r v : FreeGroup α}
    (h : PresentedGroup.mk ({r} : Set (FreeGroup α)) v = 1) :
    PresentedGroup.mk ({padRel c r} : Set (FreeGroup (PadT α))) (padHom c v) = 1 := by
  classical
  have hv : v ∈ Subgroup.normalClosure ({r} : Set (FreeGroup α)) :=
    (PresentedGroup.mk_eq_one_iff).mp h
  have hle : Subgroup.normalClosure ({r} : Set (FreeGroup α)) ≤
      (Subgroup.normalClosure ({padRel c r} : Set (FreeGroup (PadT α)))).comap (padHom c) := by
    refine Subgroup.normalClosure_le_normal ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.subset_normalClosure (by rfl)
  exact (PresentedGroup.mk_eq_one_iff).mpr (hle hv)

/-- A nontrivial word has positive norm. -/
theorem wcp_one_le_relatorNorm {v : FreeGroup α} (hv : v ≠ 1) : 1 ≤ relatorNorm v := by
  classical
  refine Nat.one_le_iff_ne_zero.mpr fun h0 => hv ?_
  simp only [relatorNorm] at h0
  exact FreeGroup.norm_eq_zero.mp h0

/-! ### Two commuting words are powers of a common word

The padded relator is not a proper power because the projection which kills the padding letter turns
a proper-power decomposition of `padRel c r` into a proper-power decomposition of the *doubled* word
of `r`; the doubled word has the letters of `r` in pairs, and a nontrivial cyclic period of the
doubled word forces `r` itself to be a proper power.  The latter step needs the classical fact that
two commuting words are powers of a common word, which is proved here (the statement also exists as
`Work.OROneRel.pow_common_of_append_comm`, but proving it here keeps this file independent of the
modules of the substitution machinery).
-/

/-- A nonempty list has positive length. -/
private lemma wcp_length_pos_of_ne_nil {σ : Type*} {l : List σ} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

/-- **Two commuting words are powers of a common word**, in the strong induction form. -/
private lemma wcp_pow_common_aux (σ : Type*) (n : ℕ) :
    ∀ {A B : List σ}, A.length + B.length ≤ n → A ≠ [] → B ≠ [] → A ++ B = B ++ A →
      ∃ (W : List σ) (p q : ℕ), W ≠ [] ∧ 1 ≤ p ∧ 1 ≤ q ∧
        A = (List.replicate p W).flatten ∧ B = (List.replicate q W).flatten := by
  induction n with
  | zero =>
      intro A B hlen hA hB _
      have h1 : 0 < A.length := wcp_length_pos_of_ne_nil hA
      have h2 : 0 < B.length := wcp_length_pos_of_ne_nil hB
      omega
  | succ n ih =>
      intro A B hlen hA hB h
      have hApos : 1 ≤ A.length := wcp_length_pos_of_ne_nil hA
      have hBpos : 1 ≤ B.length := wcp_length_pos_of_ne_nil hB
      rcases lt_trichotomy A.length B.length with hlt | heq | hgt
      · -- `A` is a prefix of `B`; write `B = A ++ D`, so that `A` commutes with `D`
        have hpre : A = B.take A.length := by
          have h1 : (A ++ B).take A.length = A := List.take_left
          rw [h] at h1
          rw [List.take_append_of_le_length (le_of_lt hlt)] at h1
          exact h1.symm
        have hBsplit : B = A ++ B.drop A.length := by
          have h1 : B = B.take A.length ++ B.drop A.length :=
            (List.take_append_drop A.length B).symm
          rw [← hpre] at h1
          exact h1
        have hDlen : (B.drop A.length).length = B.length - A.length := by rw [List.length_drop]
        have hDne : B.drop A.length ≠ [] := by
          intro h0
          have h1 : (B.drop A.length).length = 0 := by simpa using congrArg List.length h0
          rw [hDlen] at h1
          omega
        have hAD : A ++ B.drop A.length = B.drop A.length ++ A := by
          have h2 : A ++ (A ++ B.drop A.length) = (A ++ B.drop A.length) ++ A := by
            rw [← hBsplit]
            exact h
          rw [List.append_assoc] at h2
          exact List.append_cancel_left h2
        obtain ⟨W, p, q, hW, hp, hq, hAeq, hDeq⟩ := ih (by omega) hA hDne hAD
        refine ⟨W, p, p + q, hW, hp, by omega, hAeq, ?_⟩
        calc B = A ++ B.drop A.length := hBsplit
          _ = (List.replicate p W).flatten ++ (List.replicate q W).flatten := by rw [hDeq, hAeq]
          _ = (List.replicate (p + q) W).flatten := by
                rw [← List.flatten_append, ← List.replicate_add]
      · -- equal lengths: the two words are equal
        have hAB : A = B := by
          have h1 : (A ++ B).take A.length = A := List.take_left
          rw [h] at h1
          rw [List.take_left' heq.symm] at h1
          exact h1.symm
        exact ⟨A, 1, 1, hA, le_refl 1, le_refl 1, by simp [List.replicate_one],
          by simp [List.replicate_one, hAB]⟩
      · -- `B` is a prefix of `A`; the mirror image of the first case
        have hpre : B = A.take B.length := by
          have h1 : (B ++ A).take B.length = B := List.take_left
          rw [← h] at h1
          rw [List.take_append_of_le_length (le_of_lt hgt)] at h1
          exact h1.symm
        have hAsplit : A = B ++ A.drop B.length := by
          have h1 : A = A.take B.length ++ A.drop B.length :=
            (List.take_append_drop B.length A).symm
          rw [← hpre] at h1
          exact h1
        have hDlen : (A.drop B.length).length = A.length - B.length := by rw [List.length_drop]
        have hDne : A.drop B.length ≠ [] := by
          intro h0
          have h1 : (A.drop B.length).length = 0 := by simpa using congrArg List.length h0
          rw [hDlen] at h1
          omega
        have hBD : B ++ A.drop B.length = A.drop B.length ++ B := by
          have h2 : B ++ (B ++ A.drop B.length) = (B ++ A.drop B.length) ++ B := by
            rw [← hAsplit]
            exact h.symm
          rw [List.append_assoc] at h2
          exact List.append_cancel_left h2
        obtain ⟨W, p, q, hW, hp, hq, hBeq, hDeq⟩ := ih (by omega) hB hDne hBD
        refine ⟨W, p + q, p, hW, by omega, hp, ?_, hBeq⟩
        calc A = B ++ A.drop B.length := hAsplit
          _ = (List.replicate p W).flatten ++ (List.replicate q W).flatten := by rw [hDeq, hBeq]
          _ = (List.replicate (p + q) W).flatten := by
                rw [← List.flatten_append, ← List.replicate_add]

/-- **Two commuting words are powers of a common word.** -/
private lemma wcp_pow_common_of_append_comm {σ : Type*} {A B : List σ} (hA : A ≠ [])
    (hB : B ≠ []) (h : A ++ B = B ++ A) :
    ∃ (W : List σ) (p q : ℕ), W ≠ [] ∧ 1 ≤ p ∧ 1 ≤ q ∧
      A = (List.replicate p W).flatten ∧ B = (List.replicate q W).flatten :=
  wcp_pow_common_aux σ (A.length + B.length) le_rfl hA hB h

/-- **A word fixed by a nontrivial rotation is a proper power.**  If a nonempty word `L` is fixed by
the rotation `s` with `0 < s < L.length`, then `L` is a power of a shorter word: split
`L = A ++ B` into a prefix and a suffix; since `L.rotate s = L` the two blocks commute, so they are
powers of a common word, and `L = W ^ (p + q)` with `p, q ≥ 1`. -/
theorem wcp_isProperPower_mk_of_rotate_eq {α : Type u} {L : List (α × Bool)} {s : ℕ}
    (hs : 0 < s) (hsn : s < L.length) (h : L.rotate s = L) :
    IsProperPower (FreeGroup.mk L) := by
  have hsle : s ≤ L.length := hsn.le
  -- `L.rotate s = L.drop s ++ L.take s = L`, so the blocks `L.take s` and `L.drop s` commute.
  have hrot : L.drop s ++ L.take s = L := by
    have h1 : L.rotate s = L.drop s ++ L.take s := List.rotate_eq_drop_append_take hsle
    rw [h] at h1
    exact h1.symm
  have hcomm : L.take s ++ L.drop s = L.drop s ++ L.take s := by
    rw [hrot, List.take_append_drop]
  have hAne : L.take s ≠ [] := by
    intro hnil
    have hlen : (L.take s).length = 0 := List.length_eq_zero_iff.mpr hnil
    rw [List.length_take, Nat.min_eq_left hsle] at hlen
    omega
  have hBne : L.drop s ≠ [] := by
    intro hnil
    have hlen : (L.drop s).length = 0 := List.length_eq_zero_iff.mpr hnil
    rw [List.length_drop] at hlen
    omega
  obtain ⟨W, p, q, -, hp1, hq1, hAeq, hBeq⟩ :=
    wcp_pow_common_of_append_comm hAne hBne hcomm
  refine ⟨FreeGroup.mk W, p + q, by omega, ?_⟩
  rw [← List.take_append_drop s L, ← FreeGroup.mul_mk, hAeq, hBeq,
    mk_flatten_replicate, mk_flatten_replicate, ← pow_add]

/-! ### The padded relator is not a proper power

This is the analogue of `Work.OROneRel.not_isProperPower_padRel`, specialised to relators of norm
at least `2`, which is the only case that arises here (`relatorNorm r ≥ 2` follows from the
half-length hypothesis and `v ≠ 1`).  The specialisation removes the last case of the general proof
(`r = of x ^ (±1)`, which needs a separate argument for words of the shape
`of a * of b ^ m * of a`); all other cases are settled by the doubled-word argument.
-/

/-- A list of `n` copies of a single entry is the flattening of the list of `n` copies of that
entry. -/
private lemma wcp_replicate_eq_flatten_singletons {β : Type*} (n : ℕ) (p : β) :
    List.replicate n p = (List.replicate n [p]).flatten := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ih, List.singleton_append]

/-- The padding of a cyclically reduced relator of norm at least `2` which is not a proper power,
with padding exponents nonzero on some letter of the relator, is not a proper power. -/
theorem wcp_not_isProperPower_padRel {α : Type u} (c : α → ℤ) {r : FreeGroup α}
    (hcyc : IsCyclicallyReducedRelator r) (hr : ¬ IsProperPower r) (hn : 2 ≤ relatorNorm r)
    (hc : ∃ a ∈ relatorLetters r, c a ≠ 0) :
    ¬ IsProperPower (padRel c r) := by
  classical
  intro hpow
  obtain ⟨U, k, hk, hW⟩ := hpow
  have hwlen : 2 ≤ (FreeGroup.toWord r).length := by
    simpa only [relatorNorm, FreeGroup.norm] using hn
  -- the doubled word of `r` is cyclically reduced, hence reduced
  have hDcyc : FreeGroup.IsCyclicallyReduced
      ((FreeGroup.toWord r).map (fun p : α × Bool => [p, p])).flatten :=
    isCyclicallyReduced_doubledWord_of_relator hcyc
  have hDred : FreeGroup.IsReduced
      ((FreeGroup.toWord r).map (fun p : α × Bool => [p, p])).flatten := hDcyc.1
  -- killing the padding letter turns `padRel c r = U ^ k` into `mk D = (padProj U) ^ k`
  have hmkD : FreeGroup.mk ((FreeGroup.toWord r).map (fun p : α × Bool => [p, p])).flatten
      = (padProj U) ^ k := by
    rw [doubledWord_mk_eq_lift_sq]
    have h1 : FreeGroup.lift (fun a : α => FreeGroup.of a ^ (2 : ℕ)) r
        = padProj (padHom c r) := (DFunLike.congr_fun (padProj_padHom c) r).symm
    rw [h1, show padHom c r = U ^ k from hW, map_pow]
  -- hence the doubled word is a repetition
  obtain ⟨B, hB⟩ :=
    eq_flatten_replicate_of_cyclicallyReduced_of_pow hDred hDcyc hk hmkD
  rcases doubledWord_rotate_or_replicate (FreeGroup.toWord r) hwlen hk hB with
    ⟨s, hs0, hsn, hrot⟩ | ⟨p, hp⟩
  · -- a non-trivial cyclic period makes `r` a proper power
    refine hr ?_
    have h := wcp_isProperPower_mk_of_rotate_eq hs0 hsn hrot
    rwa [FreeGroup.mk_toWord] at h
  · -- a constant word of length `≥ 2` is a power of a single generator
    refine hr ⟨FreeGroup.mk [p], (FreeGroup.toWord r).length, hwlen, ?_⟩
    have hgen : ∀ (q : α × Bool) (n : ℕ),
        FreeGroup.mk (List.replicate n q) = (FreeGroup.mk [q]) ^ n := by
      intro q n
      rw [wcp_replicate_eq_flatten_singletons, mk_flatten_replicate]
    calc r = FreeGroup.mk (FreeGroup.toWord r) := (FreeGroup.mk_toWord (x := r)).symm
      _ = FreeGroup.mk (List.replicate (FreeGroup.toWord r).length p) := by
            conv_lhs => rw [hp]
      _ = (FreeGroup.mk [p]) ^ (FreeGroup.toWord r).length := hgen p _

/-! ### The exponent-sum-zero case of the induction

The exponent-sum-zero half-length case of Weinbaum's theorem is proved unconditionally in
`Submission.Work.ORLyndon.WBClean.weinbaum_sigma_zero_half` (`Work.OROneRel.WBClean.weinbaum_sigma_zero_half`), from
the exponent-sum-zero step `Work.OROneRel.WBClean.sigma_step` and the no-zero-exponent-sum case
`Work.OROneRel.WBClean.weinbaum_half_noZero`.  It is re-exported under the name used in this file so that the
padding argument below does not have to go through the wrapper modules of the neighbouring files.

(The earlier route to the no-zero case through Magnus' substitution and the transport
`Work.OROneRel.subst_transport`, together with the piece lemmas `wcp_localisation`,
`letterCountNot_lt_half_standalone`, `relatorNorm_magRewRel_letterCountNot` and the junction analysis
in `NOTES_wcp_transport_status.md`, is recorded in that note; it is not used below.) -/

/-- **Weinbaum's theorem at a relator with a letter of exponent sum zero, half-length form.** -/
theorem wcp_weinbaum_sigma_zero_half {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R)
    (hz : z ∈ relatorLetters R) (h : expSum z R = 1) :
    ∀ (k : ℕ) (w : FreeGroup β), IsSubwordOf w (R ^ k) →
      2 * relatorNorm w ≤ relatorNorm R → w ≠ 1 →
      PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1 :=
  weinbaum_sigma_zero_half R hcyc hpp hz h

/-! ### The zero exponent sum case, in full length

`wcp_weinbaum_sigma_zero_half` is the half-length form of Weinbaum's theorem at a relator with a
letter of exponent sum zero; the complementary-arc argument of
`Work.OROneRel.exists_complement_counterexample` upgrades it to the full-length form `|w| < |R|`,
which is what the padding argument consumes.
-/

/-- **Weinbaum's theorem at a relator with a letter of exponent sum zero, full-length form.**  If
`R` is cyclically reduced, is not a proper power and has a letter `z` of exponent sum zero, then
every nontrivial subword `w` of a power of `R` with `relatorNorm w < relatorNorm R` is nontrivial
in `⟨β | R⟩`. -/
theorem wcp_sigma_zero_full {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R)
    (hz : z ∈ relatorLetters R) (h : expSum z R = 1)
    (k : ℕ) (w : FreeGroup β) (hsub : IsSubwordOf w (R ^ k))
    (hlen : relatorNorm w < relatorNorm R) (hw1 : w ≠ 1) :
    PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1 := by
  intro hcontra
  -- cutting out the complementary arc of the cyclic word of `R` gives another counterexample
  obtain ⟨s, m, hsubs, hs1, hsnorm, hscontra⟩ :=
    exists_complement_counterexample hcyc hsub hlen hw1 hcontra
  have hsum : relatorNorm w + relatorNorm s = relatorNorm R := by omega
  rcases le_total (relatorNorm w) (relatorNorm s) with hle | hle
  · exact wcp_weinbaum_sigma_zero_half R hcyc hpp hz h k w hsub (by omega) hw1 hcontra
  · exact wcp_weinbaum_sigma_zero_half R hcyc hpp hz h m s hsubs (by omega) hs1 hscontra

/-! ### The target theorem -/

theorem weinbaum_covering_noZeroExpSum {α : Type u} (r : FreeGroup α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r) (hpp : ¬ Work.OROneRel.IsProperPower r)
    (hσ : ∀ a ∈ Work.OROneRel.relatorLetters r, Work.OROneRel.expSum a r ≠ 1)
    (k : ℕ) (v : FreeGroup α) (hsub : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hhalf : 2 * Work.OROneRel.relatorNorm v ≤ Work.OROneRel.relatorNorm r)
    (hcov : Work.OROneRel.relatorLetters r ⊆ Work.OROneRel.relatorLetters v)
    (hv1 : v ≠ 1) :
    PresentedGroup.mk ({r} : Set (FreeGroup α)) v ≠ 1 := by
  classical
  -- `v` is nontrivial, so `1 ≤ relatorNorm v`, and therefore `relatorNorm v < relatorNorm r`
  have hvpos : 1 ≤ relatorNorm v := wcp_one_le_relatorNorm hv1
  have hrpos : 2 ≤ relatorNorm r := by omega
  have hlen : relatorNorm v < relatorNorm r := by omega
  -- suppose for contradiction that `v` is trivial in `⟨α | r⟩`
  intro hmk
  -- two distinct letters of `r`
  obtain ⟨x, hx, t, ht, hxt⟩ := exists_two_mem_relatorLetters_ne r hrpos hpp
  -- the padding exponent `c x = σ_t r` is nonzero, because `t` has nonzero exponent sum
  have htnz : (expSum t r).toAdd ≠ 0 := by
    have ht' := hσ t ht
    simpa using ht'
  have hcx : padC r x t x ≠ 0 := by
    rw [show padC r x t x = (expSum t r).toAdd from by rw [padC]; simp]
    exact htnz
  -- the padded relator and the padded word
  have hRcyc : IsCyclicallyReducedRelator (padRel (padC r x t) r) :=
    pad_isCyclicallyReduced_aux (padC r x t) hcyc
  have hz : (none : Option α) ∈ relatorLetters (padRel (padC r x t) r) :=
    none_mem_padRel_aux hx hcx
  have hzexp : expSum (none : Option α) (padRel (padC r x t) r) = 1 :=
    expSum_none_padRel_aux r hxt
  have hsub' : IsSubwordOf (padHom (padC r x t) v) (padRel (padC r x t) r ^ k) :=
    pad_subword_aux (padC r x t) hcyc hsub
  have hlen' : relatorNorm (padHom (padC r x t) v) < relatorNorm (padRel (padC r x t) r) :=
    pad_length_lt_aux r v (padC r x t) k hcyc hsub hlen
  have hvne : padHom (padC r x t) v ≠ 1 := wcp_padHom_ne_one (padC r x t) hv1
  have hmk' : PresentedGroup.mk ({padRel (padC r x t) r} : Set (FreeGroup (Option α)))
      (padHom (padC r x t) v) = 1 := wcp_mk_padHom_eq_one hmk
  -- the padded relator is not a proper power
  have hppR : ¬ IsProperPower (padRel (padC r x t) r) :=
    wcp_not_isProperPower_padRel (padC r x t) hcyc hpp hrpos ⟨x, hx, hcx⟩
  -- the exponent-sum-zero case of Weinbaum's theorem rules this out
  exact wcp_sigma_zero_full (padRel (padC r x t) r) hRcyc hppR hz hzexp k
    (padHom (padC r x t) v) hsub' hlen' hvne hmk'

end WBClean

end Work.OROneRel
