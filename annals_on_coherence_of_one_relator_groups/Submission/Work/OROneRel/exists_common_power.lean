/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".

# Common powers in a free group

If `u ^ l = v ^ m` in a free group with `l, m ≥ 1`, then `u` and `v` are powers of a
common element.

The proof is elementary and rests on Mathlib's cyclic reduction of words.  With
`A = reduceCyclically (toWord u)`, `B = reduceCyclically (toWord v)` and conjugators
`c₁`, `c₂` (from `FreeGroup.reduceCyclically.conjugator`), Mathlib's formula
`FreeGroup.reduceCyclically.reduce_flatten_replicate` computes the reduced words of positive
powers:

`toWord (u ^ l) = c₁ ++ A^l ++ invRev c₁`  and  `toWord (v ^ m) = c₂ ++ B^m ++ invRev c₂`.

Applying cyclic reduction to the relator `u ^ l = v ^ m` strips both conjugators
(conjugating a word does not change its cyclic reduction), so `A^l = B^m` *as lists of
letters*.  The pure word-combinatorial fact that two nonempty words with equal powers are
powers of a common word (Fine--Wilf: a word of length `l|A| = m|B|` has periods `|A|` and
`|B|`, hence also period `gcd |A| |B|`) then gives a common block `W` with
`A = W^p` and `B = W^q`.  Finally, comparing the lengths of the two decompositions of the
same reduced word `toWord (u^l) = toWord (v^m)` shows `c₁ = c₂`, so that both `u` and `v`
are powers of `c₁ * mk W * c₁⁻¹`.

The extreme cases `u = 1` and `v = 1` are handled by torsion-freeness of free groups (the
`IsMulTorsionFree` instance in `Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`).
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.le_relatorNorm_pow

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Periods of repeated words -/

/-- The length of a repeated word. -/
theorem length_flatten_replicate {σ : Type*} (n : ℕ) (W : List σ) :
    (List.replicate n W).flatten.length = n * W.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

/-- In the word obtained by repeating `W` exactly `n` times, the entry at index `i` is
`W[i % W.length]`, whenever the index is in range. -/
theorem getElem?_flatten_replicate {σ : Type*} (n : ℕ) (W : List σ) (i : ℕ)
    (h : i < (List.replicate n W).flatten.length) :
    (List.replicate n W).flatten[i]? = W[i % W.length]? := by
  induction n generalizing i with
  | zero => exact absurd h (by simp)
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    by_cases hi : i < W.length
    · rw [List.getElem?_append_left hi, Nat.mod_eq_of_lt hi]
    · rw [List.getElem?_append_right (le_of_not_gt hi)]
      have h' : i - W.length < (List.replicate n W).flatten.length := by
        rw [length_flatten_replicate] at h ⊢
        have : (n + 1) * W.length = n * W.length + W.length := by ring
        omega
      rw [ih (i - W.length) h', Nat.mod_eq_sub_mod (le_of_not_gt hi)]

/-- A word made of copies of `W` has period `W.length`. -/
theorem hasPeriod_flatten_replicate {σ : Type*} (n : ℕ) (W : List σ) :
    (List.replicate n W).flatten.HasPeriod W.length := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [List.HasPeriod]
  rw [List.hasPeriod_iff_forall_getElem?_mod]
  intro i hi
  have hW : 0 < W.length := List.length_pos_iff.mpr (by rintro rfl; simp at hi)
  rw [getElem?_flatten_replicate n W i hi]
  rw [getElem?_flatten_replicate n W (i % W.length) (by
    rw [length_flatten_replicate]
    have hle : W.length ≤ n * W.length := by
      calc W.length = 1 * W.length := (one_mul _).symm
        _ ≤ n * W.length := Nat.mul_le_mul_right W.length hn
    have := Nat.mod_lt i hW
    omega)]
  rw [Nat.mod_mod]

/-- A prefix of a word with period `g`, whose length is a positive multiple of `g`, is a power
of the initial block of length `g`. -/
theorem take_eq_flatten_take_of_hasPeriod {σ : Type*} {K : List σ} {g p : ℕ} (hg : 0 < g)
    (hdvd : g ∣ p) (hp : 0 < p) (hpK : p ≤ K.length) (hper : K.HasPeriod g) :
    K.take p = (List.replicate (p / g) (K.take g)).flatten := by
  apply List.ext_getElem?
  intro i
  have hmod : ∀ j, j < K.length → K[j]? = K[j % g]? :=
    List.hasPeriod_iff_forall_getElem?_mod.mp hper
  have hpg : g ≤ K.length := le_trans (Nat.le_of_dvd hp hdvd) hpK
  have hlen : (List.replicate (p / g) (K.take g)).flatten.length = p := by
    rw [length_flatten_replicate, List.length_take, Nat.min_eq_left hpg, Nat.div_mul_cancel hdvd]
  rw [List.getElem?_take]
  by_cases hi : i < p
  · rw [if_pos hi, getElem?_flatten_replicate (p / g) (K.take g) i (by rw [hlen]; exact hi),
      List.length_take, Nat.min_eq_left hpg, List.getElem?_take, if_pos (Nat.mod_lt i hg)]
    exact hmod i (lt_of_lt_of_le hi hpK)
  · rw [if_neg hi, List.getElem?_eq_none (by rw [hlen]; exact le_of_not_gt hi)]

/-- **Free-monoid common root.**  If two nonempty words have a common power, they are powers
of a common word. -/
theorem pow_eq_common_root {σ : Type*} {A B : List σ} {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (hA : A ≠ []) (hB : B ≠ [])
    (h : (List.replicate l A).flatten = (List.replicate m B).flatten) :
    ∃ (W : List σ) (p q : ℕ), W ≠ [] ∧ 1 ≤ p ∧ 1 ≤ q ∧
      A = (List.replicate p W).flatten ∧ B = (List.replicate q W).flatten := by
  by_cases hl1 : l = 1
  · subst hl1
    have hmk : A = (List.replicate m B).flatten := by simpa using h
    exact ⟨B, m, 1, hB, hm, le_rfl, hmk, by simp⟩
  by_cases hm1 : m = 1
  · subst hm1
    have hmk : B = (List.replicate l A).flatten := by simpa using h.symm
    exact ⟨A, 1, l, hA, le_rfl, hl, by simp, hmk⟩
  have hl2 : 2 ≤ l := by omega
  have hm2 : 2 ≤ m := by omega
  have hp0 : 0 < A.length := List.length_pos_iff.mpr hA
  have hq0 : 0 < B.length := List.length_pos_iff.mpr hB
  have hgpos : 0 < (A.length).gcd (B.length) := Nat.gcd_pos_of_pos_left B.length hp0
  have hdvdp : (A.length).gcd (B.length) ∣ A.length := Nat.gcd_dvd_left A.length B.length
  have hdvdq : (A.length).gcd (B.length) ∣ B.length := Nat.gcd_dvd_right A.length B.length
  have hlenA : (List.replicate l A).flatten.length = l * A.length := length_flatten_replicate l A
  have hlenB' : (List.replicate l A).flatten.length = m * B.length := by
    rw [h, length_flatten_replicate]
  have hperKp : (List.replicate l A).flatten.HasPeriod A.length := hasPeriod_flatten_replicate l A
  have hperKq : (List.replicate l A).flatten.HasPeriod B.length := by
    rw [h]; exact hasPeriod_flatten_replicate m B
  have hfine : A.length + B.length - (A.length).gcd (B.length)
      ≤ (List.replicate l A).flatten.length := by
    have hp2 : 2 * A.length ≤ (List.replicate l A).flatten.length := by
      rw [hlenA]; exact Nat.mul_le_mul_right A.length hl2
    have hq2 : 2 * B.length ≤ (List.replicate l A).flatten.length := by
      rw [hlenB']; exact Nat.mul_le_mul_right B.length hm2
    omega
  have hper : (List.replicate l A).flatten.HasPeriod ((A.length).gcd (B.length)) :=
    List.HasPeriod.gcd hperKp hperKq hfine
  have hpg_le : A.length ≤ (List.replicate l A).flatten.length := by
    rw [hlenA]
    calc A.length = 1 * A.length := (one_mul _).symm
      _ ≤ l * A.length := Nat.mul_le_mul_right A.length hl
  have hqg_le : B.length ≤ (List.replicate l A).flatten.length := by
    rw [hlenB']
    calc B.length = 1 * B.length := (one_mul _).symm
      _ ≤ m * B.length := Nat.mul_le_mul_right B.length hm
  have hgp_le : (A.length).gcd (B.length) ≤ A.length := Nat.le_of_dvd hp0 hdvdp
  have hgq_le : (A.length).gcd (B.length) ≤ B.length := Nat.le_of_dvd hq0 hdvdq
  have hsplitA : (List.replicate l A).flatten = A ++ (List.replicate (l - 1) A).flatten := by
    have hl' : l = (l - 1) + 1 := by omega
    conv_lhs => rw [hl']
    rw [List.replicate_succ, List.flatten_cons]
  have hsplitB : (List.replicate m B).flatten = B ++ (List.replicate (m - 1) B).flatten := by
    have hm' : m = (m - 1) + 1 := by omega
    conv_lhs => rw [hm']
    rw [List.replicate_succ, List.flatten_cons]
  have htakeA : (List.replicate l A).flatten.take A.length = A := by
    rw [hsplitA, List.take_left]
  have htakeB : (List.replicate l A).flatten.take B.length = B := by
    rw [h, hsplitB, List.take_left]
  have hAeq : A = (List.replicate (A.length / (A.length).gcd (B.length))
      ((List.replicate l A).flatten.take ((A.length).gcd (B.length)))).flatten := by
    rw [← take_eq_flatten_take_of_hasPeriod (K := (List.replicate l A).flatten)
      (g := (A.length).gcd (B.length)) (p := A.length) hgpos hdvdp hp0 hpg_le hper]
    exact htakeA.symm
  have hBeq : B = (List.replicate (B.length / (A.length).gcd (B.length))
      ((List.replicate l A).flatten.take ((A.length).gcd (B.length)))).flatten := by
    rw [← take_eq_flatten_take_of_hasPeriod (K := (List.replicate l A).flatten)
      (g := (A.length).gcd (B.length)) (p := B.length) hgpos hdvdq hq0 hqg_le hper]
    exact htakeB.symm
  have hWne : (List.replicate l A).flatten.take ((A.length).gcd (B.length)) ≠ [] := by
    have hWlen : ((List.replicate l A).flatten.take ((A.length).gcd (B.length))).length
        = (A.length).gcd (B.length) := by
      rw [List.length_take, Nat.min_eq_left (le_trans hgp_le hpg_le)]
    rw [← List.length_pos_iff, hWlen]; exact hgpos
  refine ⟨(List.replicate l A).flatten.take ((A.length).gcd (B.length)),
    A.length / (A.length).gcd (B.length), B.length / (A.length).gcd (B.length),
    hWne, ?_, ?_, hAeq, hBeq⟩
  · rw [Nat.one_le_div_iff hgpos]; exact hgp_le
  · rw [Nat.one_le_div_iff hgpos]; exact hgq_le

/-! ## Auxiliary free group lemmas -/

/-- `mk` of a repeated word is the corresponding power. -/
theorem mk_flatten_replicate {β : Type*} (n : ℕ) (W : List (β × Bool)) :
    FreeGroup.mk (List.replicate n W).flatten = (FreeGroup.mk W) ^ n := by
  induction n with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero, FreeGroup.one_eq_mk]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- Powers of a conjugate. -/
theorem conj_mul_inv_pow {G : Type*} [Group G] (c x : G) (n : ℕ) :
    (c * x * c⁻¹) ^ n = c * x ^ n * c⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ih]; group

/-- Two `conjugator ++ core ++ invRev conjugator` decompositions of the same word with the same
core have the same conjugating part (compare the lengths). -/
theorem eq_of_append_invRev_eq {c₁ c₂ D : List (α × Bool)}
    (h : c₁ ++ D ++ FreeGroup.invRev c₁ = c₂ ++ D ++ FreeGroup.invRev c₂) : c₁ = c₂ := by
  have hlen : c₁.length = c₂.length := by
    have h' := congrArg List.length h
    simp only [List.length_append, FreeGroup.invRev_length] at h'
    omega
  rw [List.append_assoc, List.append_assoc] at h
  have htake := congrArg (fun l => l.take c₁.length) h
  have h1 : (c₁ ++ (D ++ FreeGroup.invRev c₁)).take c₁.length = c₁ := by
    rw [List.take_left]
  have h2 : (c₂ ++ (D ++ FreeGroup.invRev c₂)).take c₁.length = c₂ := by
    rw [List.take_append_of_le_length hlen.le, List.take_of_length_le hlen.ge]
  rw [h1, h2] at htake
  exact htake

/-- Cyclic reduction is the identity on a cyclically reduced word. -/
theorem reduceCyclically_eq_self_of_isCyclicallyReduced [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) : FreeGroup.reduceCyclically L = L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton a => simp
  | cons_append a l b ih =>
    rw [FreeGroup.reduceCyclically.cons_append]
    by_cases hc : b.1 = a.1 ∧ (!b.2) = a.2
    · rw [if_pos hc]
      exfalso
      have h' : FreeGroup.IsCyclicallyReduced ((a :: l) ++ [b]) := by
        rw [List.cons_append]; exact h
      rw [FreeGroup.isCyclicallyReduced_cons_append_iff] at h'
      have hb : b.2 = a.2 := h'.2 hc.1
      rw [hb] at hc
      exact absurd hc.2 (by simp)
    · rw [if_neg hc, List.cons_append]

/-- Conjugating a word by an arbitrary word does not change its cyclic reduction. -/
theorem reduceCyclically_append_invRev [DecidableEq α] (P M : List (α × Bool)) :
    FreeGroup.reduceCyclically (P ++ M ++ FreeGroup.invRev P) = FreeGroup.reduceCyclically M := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hq : FreeGroup.invRev [p] = [(p.1, !p.2)] := by simp [FreeGroup.invRev]
    rw [FreeGroup.invRev_cons, hq]
    have hreshape : ((p :: P) ++ M) ++ (FreeGroup.invRev P ++ [(p.1, !p.2)]) =
        p :: ((P ++ M ++ FreeGroup.invRev P) ++ [(p.1, !p.2)]) := by
      simp only [List.cons_append, List.append_assoc]
    rw [hreshape, FreeGroup.reduceCyclically.cons_append,
      if_pos ⟨rfl, by cases p.2 <;> rfl⟩]
    exact ih

/-- The cyclic reduction of the reduced word of a positive power is the concatenation of the
cyclic reductions of the reduced word of the base. -/
theorem reduceCyclically_toWord_pow [DecidableEq α] (x : FreeGroup α) {k : ℕ} (hk : 1 ≤ k) :
    FreeGroup.reduceCyclically (FreeGroup.toWord (x ^ k)) =
      (List.replicate k (FreeGroup.reduceCyclically (FreeGroup.toWord x))).flatten := by
  have hred : FreeGroup.IsReduced (FreeGroup.toWord x) := FreeGroup.isReduced_toWord
  rw [FreeGroup.toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate hred k, if_neg (by omega : k ≠ 0)]
  rw [reduceCyclically_append_invRev]
  exact reduceCyclically_eq_self_of_isCyclicallyReduced
    ((FreeGroup.reduceCyclically.isCyclicallyReduced hred).flatten_replicate k)

/-! ## The main theorem -/

theorem exists_common_power {α : Type u} {u v : FreeGroup α} {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (h : u ^ l = v ^ m) :
    ∃ (w : FreeGroup α) (a b : ℕ), 1 ≤ a ∧ 1 ≤ b ∧ u = w ^ a ∧ v = w ^ b := by
  classical
  rcases eq_or_ne u 1 with hu1 | hu
  · subst hu1
    have hv : v = 1 := by
      have h' : v ^ m = (1 : FreeGroup α) ^ m := by rw [← h]; simp
      exact IsMulTorsionFree.pow_left_injective (by omega : m ≠ 0) h'
    exact ⟨1, 1, 1, le_rfl, le_rfl, by simp, by rw [hv]; simp⟩
  rcases eq_or_ne v 1 with hv1 | hv
  · subst hv1
    have hu' : u = 1 := by
      have h1 : u ^ l = (1 : FreeGroup α) := by rw [h]; simp
      have h' : u ^ l = (1 : FreeGroup α) ^ l := by rw [h1, one_pow]
      exact IsMulTorsionFree.pow_left_injective (by omega : l ≠ 0) h'
    exact ⟨1, 1, 1, le_rfl, le_rfl, by rw [hu']; simp, by simp⟩
  have hLu : FreeGroup.toWord u ≠ [] := by
    intro hcon; exact hu (FreeGroup.toWord_eq_nil_iff.mp hcon)
  have hLv : FreeGroup.toWord v ≠ [] := by
    intro hcon; exact hv (FreeGroup.toWord_eq_nil_iff.mp hcon)
  set A : List (α × Bool) := FreeGroup.reduceCyclically (FreeGroup.toWord u) with hA
  set B : List (α × Bool) := FreeGroup.reduceCyclically (FreeGroup.toWord v) with hB
  set c₁ : List (α × Bool) := FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord u) with hc1
  set c₂ : List (α × Bool) := FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord v) with hc2
  have hAne : A ≠ [] := by
    rw [hA]; exact reduceCyclically_ne_nil_of_isReduced FreeGroup.isReduced_toWord hLu
  have hBne : B ≠ [] := by
    rw [hB]; exact reduceCyclically_ne_nil_of_isReduced FreeGroup.isReduced_toWord hLv
  have htu : FreeGroup.toWord (u ^ l)
      = c₁ ++ (List.replicate l A).flatten ++ FreeGroup.invRev c₁ := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord l,
      if_neg (by omega : l ≠ 0)]
  have htv : FreeGroup.toWord (v ^ m)
      = c₂ ++ (List.replicate m B).flatten ++ FreeGroup.invRev c₂ := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord m,
      if_neg (by omega : m ≠ 0)]
  have hlist : (List.replicate l A).flatten = (List.replicate m B).flatten := by
    have hcyc : FreeGroup.reduceCyclically (FreeGroup.toWord (u ^ l))
        = FreeGroup.reduceCyclically (FreeGroup.toWord (v ^ m)) := by rw [h]
    rwa [reduceCyclically_toWord_pow u hl, reduceCyclically_toWord_pow v hm] at hcyc
  obtain ⟨W, p, q, hWne, hp1, hq1, hAeq, hBeq⟩ := pow_eq_common_root hl hm hAne hBne hlist
  have hcc : c₁ = c₂ := by
    apply eq_of_append_invRev_eq
    rw [← htu, hlist, ← htv, h]
  have hu_dec : u = FreeGroup.mk c₁ * FreeGroup.mk A * (FreeGroup.mk c₁)⁻¹ := by
    have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically (FreeGroup.toWord u)
    rw [← hc1, ← hA] at hconj
    calc u = FreeGroup.mk (FreeGroup.toWord u) := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c₁ ++ A ++ FreeGroup.invRev c₁) := by rw [hconj]
      _ = FreeGroup.mk c₁ * FreeGroup.mk A * (FreeGroup.mk c₁)⁻¹ := by
            rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  have hv_dec : v = FreeGroup.mk c₂ * FreeGroup.mk B * (FreeGroup.mk c₂)⁻¹ := by
    have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically (FreeGroup.toWord v)
    rw [← hc2, ← hB] at hconj
    calc v = FreeGroup.mk (FreeGroup.toWord v) := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c₂ ++ B ++ FreeGroup.invRev c₂) := by rw [hconj]
      _ = FreeGroup.mk c₂ * FreeGroup.mk B * (FreeGroup.mk c₂)⁻¹ := by
            rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  have hmkA : FreeGroup.mk A = (FreeGroup.mk W) ^ p := by rw [hAeq, mk_flatten_replicate]
  have hmkB : FreeGroup.mk B = (FreeGroup.mk W) ^ q := by rw [hBeq, mk_flatten_replicate]
  refine ⟨FreeGroup.mk c₁ * FreeGroup.mk W * (FreeGroup.mk c₁)⁻¹, p, q, hp1, hq1, ?_, ?_⟩
  · rw [hu_dec, hmkA, conj_mul_inv_pow]
  · rw [hv_dec, hmkB, ← hcc, conj_mul_inv_pow]

end Work.OROneRel
