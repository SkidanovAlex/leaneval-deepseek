import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Fintype.BigOperators

set_option linter.unusedSimpArgs false

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

/-! ## Basic infrastructure for combinatorial lines and subspaces -/

/-- `Fintype` instance for combinatorial lines. -/
instance instLineFintype {α ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] :
    Fintype (Line α ι) :=
  Fintype.ofInjective (fun l : Line α ι => l.idxFun) (fun _ _ h => Line.ext h)

/-- `Fintype` instance for combinatorial subspaces. -/
instance instSubspaceFintype {η α ι : Type*} [Fintype η] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Fintype (Subspace η α ι) :=
  Fintype.ofInjective (fun S : Subspace η α ι => S.idxFun) (fun _ _ h => Subspace.ext h)

/-- `DecidableEq` instance for combinatorial lines. -/
instance instLineDecidableEq {α ι : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι] :
    DecidableEq (Line α ι) :=
  fun l m => decidable_of_iff (l.idxFun = m.idxFun)
    ⟨fun h => Line.ext h, fun h => congrArg Line.idxFun h⟩

/-- `DecidableEq` instance for combinatorial subspaces. -/
instance instSubspaceDecidableEq {η α ι : Type*} [DecidableEq η] [DecidableEq α] [DecidableEq ι]
    [Fintype ι] :
    DecidableEq (Subspace η α ι) :=
  fun l m => decidable_of_iff (l.idxFun = m.idxFun)
    ⟨fun h => Subspace.ext h, fun h => congrArg Subspace.idxFun h⟩

/-- A combinatorial line of `Fin n → Fin k` is a one-dimensional combinatorial subspace. -/
def lineToSubspace {k n : ℕ} (l : Line (Fin k) (Fin n)) : Subspace (Fin 1) (Fin k) (Fin n) where
  idxFun i := match l.idxFun i with
    | none => Sum.inr 0
    | some a => Sum.inl a
  proper e := by
    obtain ⟨i, hi⟩ := l.proper
    refine ⟨i, ?_⟩
    rw [hi]
    exact congrArg Sum.inr (Subsingleton.elim _ e)

@[simp] lemma lineToSubspace_apply {k n : ℕ} (l : Line (Fin k) (Fin n)) (x : Fin 1 → Fin k) :
    lineToSubspace l x = l (x 0) := by
  funext i
  rw [Subspace.coe_apply, Line.coe_apply, lineToSubspace]
  cases h : l.idxFun i <;> simp [h]

/-! ## Concatenation of words -/

/-- Concatenation of a word `x` of length `t` and a word `y` of length `n - t`. -/
def cat {α : Type*} {t n : ℕ} (ht : t ≤ n) (x : Fin t → α) (y : Fin (n - t) → α) : Fin n → α :=
  fun i => if h : (i : ℕ) < t then x ⟨i, h⟩ else y ⟨(i : ℕ) - t, by omega⟩

lemma cat_apply_of_lt {α : Type*} {t n : ℕ} (ht : t ≤ n) (x : Fin t → α) (y : Fin (n - t) → α)
    (i : Fin n) (h : (i : ℕ) < t) : cat ht x y i = x ⟨i, h⟩ := dif_pos h

lemma cat_apply_of_ge {α : Type*} {t n : ℕ} (ht : t ≤ n) (x : Fin t → α) (y : Fin (n - t) → α)
    (i : Fin n) (h : ¬ (i : ℕ) < t) : cat ht x y i = y ⟨(i : ℕ) - t, by omega⟩ := dif_neg h

/-- Deletion of the first `t` entries of a word. -/
def del {α : Type*} {t n : ℕ} (ht : t ≤ n) (z : Fin n → α) : Fin (n - t) → α :=
  fun j => z ⟨t + (j : ℕ), by omega⟩

/-- Restriction to the first `t` entries of a word. -/
def res {α : Type*} {t n : ℕ} (ht : t ≤ n) (z : Fin n → α) : Fin t → α :=
  fun i => z ⟨(i : ℕ), by omega⟩

@[simp] lemma del_cat {α : Type*} {t n : ℕ} (ht : t ≤ n) (x : Fin t → α)
    (y : Fin (n - t) → α) : del ht (cat ht x y) = y := by
  funext j
  rw [del, cat_apply_of_ge ht x y _ (by simp only [Fin.val_mk]; omega)]
  exact congrArg y (Fin.ext (by simp only [Fin.val_mk]; omega))

@[simp] lemma res_cat {α : Type*} {t n : ℕ} (ht : t ≤ n) (x : Fin t → α)
    (y : Fin (n - t) → α) : res ht (cat ht x y) = x := by
  funext j
  rw [res, cat_apply_of_lt ht x y _ j.2]

lemma cat_res_del {α : Type*} {t n : ℕ} (ht : t ≤ n) (z : Fin n → α) :
    cat ht (res ht z) (del ht z) = z := by
  funext i
  rw [cat]
  by_cases h : (i : ℕ) < t
  · rw [dif_pos h]
    exact congrArg z (Fin.ext (by simp))
  · rw [dif_neg h]
    exact congrArg z (Fin.ext (by simp only [del, Fin.val_mk]; omega))

/-! ## Gluing an `m'`-dimensional subspace and a line -/

/-- Given an `m'`-dimensional subspace of `Fin t → Fin k` and a combinatorial line in
`Fin (n - t) → Fin k`, produce the `(m'+1)`-dimensional subspace of `Fin n → Fin k`
whose first `t` coordinates run over the first subspace and whose last `n - t`
coordinates run over the line. -/
def mkSub {k t n m' : ℕ} (ht : t ≤ n) (σ : Subspace (Fin m') (Fin k) (Fin t))
    (l : Line (Fin k) (Fin (n - t))) : Subspace (Fin (m' + 1)) (Fin k) (Fin n) where
  idxFun i :=
    if h : (i : ℕ) < t then Sum.map id (Fin.castAdd 1) (σ.idxFun ⟨i, h⟩)
    else match l.idxFun ⟨(i : ℕ) - t, by omega⟩ with
      | none => Sum.inr (Fin.natAdd m' 0)
      | some a => Sum.inl a
  proper e := by
    rcases lt_or_ge (e : ℕ) m' with he | he
    · obtain ⟨i, hi⟩ := σ.proper (⟨e, he⟩ : Fin m')
      refine ⟨Fin.castLE ht i, ?_⟩
      have hlt : ((Fin.castLE ht i : Fin n) : ℕ) < t := i.2
      rw [dif_pos hlt]
      have hsub : (⟨(Fin.castLE ht i : Fin n), hlt⟩ : Fin t) = i := Fin.ext rfl
      rw [hsub, hi]
      exact congrArg Sum.inr (Fin.ext (by simp [Fin.castAdd]))
    · obtain ⟨j, hj⟩ := l.proper
      refine ⟨⟨t + (j : ℕ), by omega⟩, ?_⟩
      have hge : ¬ ((⟨t + (j : ℕ), by omega⟩ : Fin n) : ℕ) < t := by
        simp only [Fin.val_mk]; omega
      rw [dif_neg hge]
      have hsub : (⟨(↑(⟨t + (j : ℕ), by omega⟩ : Fin n)) - t, by omega⟩ : Fin (n - t)) = j :=
        Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [hsub, hj]
      exact congrArg Sum.inr (Fin.ext (by simp only [Fin.natAdd]; omega))

/-- The points of `mkSub ht σ l` are obtained by gluing a point of `σ` and a point of `l`. -/
lemma mkSub_apply {k t n m' : ℕ} (ht : t ≤ n) (σ : Subspace (Fin m') (Fin k) (Fin t))
    (l : Line (Fin k) (Fin (n - t))) (x : Fin (m' + 1) → Fin k) :
    mkSub ht σ l x = cat ht (σ (fun i => x (Fin.castAdd 1 i)))
      (l (x (Fin.natAdd m' 0))) := by
  funext i
  rw [Subspace.coe_apply]
  simp only [mkSub, cat]
  by_cases h : (i : ℕ) < t
  · rw [dif_pos h, dif_pos h, Subspace.coe_apply]
    cases hσ : σ.idxFun ⟨i, h⟩ <;> simp
  · rw [dif_neg h, dif_neg h, Line.coe_apply]
    cases hl : l.idxFun ⟨(i : ℕ) - t, by omega⟩ <;> simp

/-! ## Slicing a subset along the last `n - t` coordinates -/

/-- The slices `{x : Fin t → Fin k | cat ht x y ∈ T}` of `T` along the last `n - t`
coordinates partition `T`. -/
lemma card_filter_del_eq {k t n : ℕ} (ht : t ≤ n) (T : Finset (Fin n → Fin k))
    (y : Fin (n - t) → Fin k) :
    (T.filter (fun z => del ht z = y)).card
      = ((Finset.univ : Finset (Fin t → Fin k)).filter (fun x => cat ht x y ∈ T)).card := by
  apply Finset.card_bij (fun z _ => res ht z)
  · intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hz.2, cat_res_del]
    exact hz.1
  · intro z hz z' hz' heq
    rw [Finset.mem_filter] at hz hz'
    rw [← cat_res_del ht z, ← cat_res_del ht z', heq, hz.2, hz'.2]
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨cat ht x y, ?_, res_cat ht x y⟩
    rw [Finset.mem_filter]
    exact ⟨hx.2, del_cat ht x y⟩

/-- Total mass of `T` equals the sum of the masses of its slices. -/
lemma card_eq_sum_slices {k t n : ℕ} (ht : t ≤ n) (T : Finset (Fin n → Fin k)) :
    (T.card : ℝ) = ∑ y : Fin (n - t) → Fin k,
      (((Finset.univ : Finset (Fin t → Fin k)).filter (fun x => cat ht x y ∈ T)).card : ℝ) := by
  have h1 : T.card = ∑ y : Fin (n - t) → Fin k, (T.filter (fun z => del ht z = y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := del ht) (s := T) (t := Finset.univ)
      (fun a _ => Finset.mem_univ (del ht a))]
  rw [h1, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun y _ => by rw [card_filter_del_eq ht T y])

/-- The multidimensional density Hales–Jewett property for the alphabet `Fin k`. -/
def MultidimDHJ (k d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
      ∃ S : Subspace (Fin d) (Fin k) (Fin n), ∀ x : Fin d → Fin k, S x ∈ T

/-- Pigeonhole for real-valued counting: if `c ≤ |s|` then some fibre of `f` on `s` has at
least `c / D` elements, provided the image of `f` on `s` has at most `D` elements. -/
lemma exists_card_fiber_ge_div {ι β : Type*} [DecidableEq β] (s : Finset ι) (f : ι → β)
    (c : ℝ) (D : ℕ) (hcp : 0 < c) (hDpos : 0 < D) (hD : (s.image f).card ≤ D)
    (hc : c ≤ (s.card : ℝ)) :
    ∃ b, c / (D : ℝ) ≤ ((s.filter (fun x => f x = b)).card : ℝ) := by
  classical
  have hspos : 0 < s.card := by
    have h : (0 : ℝ) < (s.card : ℝ) := lt_of_lt_of_le hcp hc
    exact_mod_cast h
  have hne : (s.image f).Nonempty := Finset.image_nonempty.mpr (Finset.card_pos.mp hspos)
  by_contra h
  push Not at h
  have hsum_eq : (s.card : ℝ) = ∑ b ∈ s.image f, ((s.filter (fun x => f x = b)).card : ℝ) := by
    have h1 : s.card = ∑ b ∈ (s.image f), (s.filter (fun x => f x = b)).card :=
      Finset.card_eq_sum_card_image f s
    exact_mod_cast h1
  have hlt : ∑ b ∈ s.image f, ((s.filter (fun x => f x = b)).card : ℝ)
      < ∑ _b ∈ s.image f, (c / (D : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hne (fun b _ => h b)
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hDle : ((s.image f).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hbnd : ((s.image f).card : ℝ) * (c / (D : ℝ)) ≤ (D : ℝ) * (c / (D : ℝ)) :=
    mul_le_mul_of_nonneg_right hDle (by positivity)
  rw [mul_div_cancel₀ c (ne_of_gt hDposR)] at hbnd
  rw [← hsum_eq] at hlt
  linarith

/-- **Multidimensional DHJ from DHJ.**  If every `δ`-dense subset of `Fin n → Fin k` contains
a combinatorial line for all large `n`, then every `δ`-dense subset contains an
`m`-dimensional combinatorial subspace.  This is the induction of Furstenberg–Katznelson
(see e.g. Polymath, Proposition 2.2). -/
theorem mdhj_of_dhj (k : ℕ) (hk : 1 ≤ k)
    (hdhj : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ T : Finset (Fin n → Fin k), δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ S : Combinatorics.Subspace (Fin m) (Fin k) (Fin n),
          ∀ x : Fin m → Fin k, S x ∈ T := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have key : ∀ e : ℕ, MultidimDHJ k (e + 1) := by
    intro e
    induction e with
    | zero =>
      intro δ hδ
      obtain ⟨n₀, hn₀⟩ := hdhj δ hδ
      exact ⟨n₀, fun n hn T hT => by
        obtain ⟨l, hl⟩ := hn₀ n hn T hT
        exact ⟨lineToSubspace l, fun x => by
          rw [lineToSubspace_apply]
          exact hl (x 0)⟩⟩
    | succ e ih =>
      intro δ hδ
      obtain ⟨t₀, ht₀⟩ := ih (δ / 2) (by linarith)
      let t : ℕ := max t₀ (e + 1)
      have htt₀ : t₀ ≤ t := le_max_left _ _
      let M : ℕ := Fintype.card (Subspace (Fin (e + 1)) (Fin k) (Fin t)) + 1
      have hMpos : 0 < M := Nat.succ_pos _
      obtain ⟨n₁, hn₁⟩ := hdhj (δ / (2 * (M : ℝ))) (by positivity)
      refine ⟨t + n₁, fun n hn T hT => ?_⟩
      have htn : t ≤ n := by omega
      have hnt : n₁ ≤ n - t := by omega
      let S : (Fin (n - t) → Fin k) → Finset (Fin t → Fin k) :=
        fun y => (Finset.univ : Finset (Fin t → Fin k)).filter (fun x => cat htn x y ∈ T)
      let p : (Fin (n - t) → Fin k) → Prop :=
        fun y => (δ / 2) * (k : ℝ) ^ t ≤ ((S y).card : ℝ)
      let G : Finset (Fin (n - t) → Fin k) := Finset.univ.filter p
      have hS_le : ∀ y, ((S y).card : ℝ) ≤ (k : ℝ) ^ t := by
        intro y
        have hle : (S y).card ≤ (Finset.univ : Finset (Fin t → Fin k)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hle
        calc ((S y).card : ℝ) ≤ ((k ^ t : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (k : ℝ) ^ t := by push_cast; ring
      have hTsum : (T.card : ℝ) = ∑ y : Fin (n - t) → Fin k, ((S y).card : ℝ) := by
        dsimp only [S]
        exact card_eq_sum_slices htn T
      have hsplit : G.sum (fun y => ((S y).card : ℝ))
          + (Finset.univ.filter (fun y => ¬ p y)).sum (fun y => ((S y).card : ℝ))
          = ∑ y : Fin (n - t) → Fin k, ((S y).card : ℝ) := by
        dsimp only [G]
        rw [Finset.sum_filter_add_sum_filter_not]
      have hunivcard : (Finset.univ : Finset (Fin (n - t) → Fin k)).card = k ^ (n - t) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hcompl : ((Finset.univ.filter (fun y => ¬ p y)).card : ℝ)
          = (k : ℝ) ^ (n - t) - (G.card : ℝ) := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (n - t) → Fin k))) p
        have h2 : G.card + (Finset.univ.filter (fun y => ¬ p y)).card = k ^ (n - t) := by
          dsimp only [G]
          rw [← hunivcard]
          exact h
        have hc : ((G.card : ℕ) : ℝ)
            + (((Finset.univ.filter (fun y => ¬ p y)).card : ℕ) : ℝ)
            = ((k ^ (n - t) : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at hc
        linarith
      have hG : (δ / 2) * (k : ℝ) ^ (n - t) ≤ (G.card : ℝ) := by
        have hGl : G.sum (fun y => ((S y).card : ℝ)) ≤ (G.card : ℝ) * (k : ℝ) ^ t := by
          calc G.sum (fun y => ((S y).card : ℝ)) ≤ G.sum (fun _ => (k : ℝ) ^ t) :=
                Finset.sum_le_sum (fun y _ => hS_le y)
            _ = (G.card : ℝ) * (k : ℝ) ^ t := by rw [Finset.sum_const, nsmul_eq_mul]
        have hGcl : (Finset.univ.filter (fun y => ¬ p y)).sum (fun y => ((S y).card : ℝ))
            ≤ ((Finset.univ.filter (fun y => ¬ p y)).card : ℝ) * ((δ / 2) * (k : ℝ) ^ t) := by
          calc (Finset.univ.filter (fun y => ¬ p y)).sum (fun y => ((S y).card : ℝ))
              ≤ (Finset.univ.filter (fun y => ¬ p y)).sum (fun _ => (δ / 2) * (k : ℝ) ^ t) := by
                apply Finset.sum_le_sum
                intro y hy
                exact le_of_lt (not_le.mp (Finset.mem_filter.mp hy).2)
            _ = ((Finset.univ.filter (fun y => ¬ p y)).card : ℝ) * ((δ / 2) * (k : ℝ) ^ t) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hTle : (T.card : ℝ) ≤ (G.card : ℝ) * (k : ℝ) ^ t
            + ((k : ℝ) ^ (n - t) - (G.card : ℝ)) * ((δ / 2) * (k : ℝ) ^ t) := by
          calc (T.card : ℝ) = G.sum (fun y => ((S y).card : ℝ))
                + (Finset.univ.filter (fun y => ¬ p y)).sum (fun y => ((S y).card : ℝ)) := by
                rw [hsplit, hTsum]
            _ ≤ (G.card : ℝ) * (k : ℝ) ^ t
                + ((Finset.univ.filter (fun y => ¬ p y)).card : ℝ) * ((δ / 2) * (k : ℝ) ^ t) :=
                add_le_add hGl hGcl
            _ = (G.card : ℝ) * (k : ℝ) ^ t
                + ((k : ℝ) ^ (n - t) - (G.card : ℝ)) * ((δ / 2) * (k : ℝ) ^ t) := by
                rw [hcompl]
        have hmain : δ * ((k : ℝ) ^ t * (k : ℝ) ^ (n - t)) ≤ (G.card : ℝ) * (k : ℝ) ^ t
            + ((k : ℝ) ^ (n - t) - (G.card : ℝ)) * ((δ / 2) * (k : ℝ) ^ t) := by
          have hkpow : (k : ℝ) ^ n = (k : ℝ) ^ t * (k : ℝ) ^ (n - t) := by
            rw [← pow_add, Nat.add_sub_of_le htn]
          rw [hkpow] at hT
          exact le_trans hT hTle
        have hkt_pos : (0 : ℝ) < (k : ℝ) ^ t := pow_pos hkpos t
        have hstep : (δ / 2) * (k : ℝ) ^ (n - t) * (k : ℝ) ^ t ≤ (G.card : ℝ) * (k : ℝ) ^ t := by
          have h2 : (δ / 2) * (k : ℝ) ^ (n - t) * (k : ℝ) ^ t
              ≤ (G.card : ℝ) * (k : ℝ) ^ t * (1 - δ / 2) := by
            nlinarith [hmain]
          have h3 : (G.card : ℝ) * (k : ℝ) ^ t * (1 - δ / 2) ≤ (G.card : ℝ) * (k : ℝ) ^ t := by
            have hle : (1 - δ / 2 : ℝ) ≤ 1 := by linarith
            have hnn : (0 : ℝ) ≤ (G.card : ℝ) * (k : ℝ) ^ t := by positivity
            simpa using mul_le_mul_of_nonneg_left hle hnn
          linarith [h2, h3]
        exact (mul_le_mul_iff_of_pos_right hkt_pos).mp hstep
      have hgood : ∀ y ∈ G, ∃ σ : Subspace (Fin (e + 1)) (Fin k) (Fin t),
          ∀ x : Fin (e + 1) → Fin k, cat htn (σ x) y ∈ T := by
        intro y hy
        have hyG : (δ / 2) * (k : ℝ) ^ t ≤ ((S y).card : ℝ) := (Finset.mem_filter.mp hy).2
        obtain ⟨σ, hσ⟩ := ht₀ t htt₀ (S y) hyG
        exact ⟨σ, fun x => (Finset.mem_filter.mp (hσ x)).2⟩
      let f : {y : Fin (n - t) → Fin k // y ∈ G} → Subspace (Fin (e + 1)) (Fin k) (Fin t) :=
        fun y => Classical.choose (hgood y.1 y.2)
      have hf_spec : ∀ (y : {y : Fin (n - t) → Fin k // y ∈ G}) (x : Fin (e + 1) → Fin k),
          cat htn (f y x) y.1 ∈ T := fun y x => Classical.choose_spec (hgood y.1 y.2) x
      have hD : (G.attach.image f).card ≤ M :=
        le_trans (Finset.card_le_univ _) (Nat.le_succ _)
      obtain ⟨σ₀, hσ₀⟩ := exists_card_fiber_ge_div (s := G.attach) (f := f)
        ((δ / 2) * (k : ℝ) ^ (n - t)) M (mul_pos (by linarith) (pow_pos hkpos _)) hMpos hD
        (by rw [Finset.card_attach]; exact hG)
      let H : Finset (Fin (n - t) → Fin k) :=
        Finset.univ.filter (fun y => ∀ x : Fin (e + 1) → Fin k, cat htn (σ₀ x) y ∈ T)
      have hHcard : (δ / (2 * (M : ℝ))) * (k : ℝ) ^ (n - t) ≤ (H.card : ℝ) := by
        have hle : ((G.attach.filter (fun y => f y = σ₀)).card : ℝ) ≤ (H.card : ℝ) := by
          have hmap : Set.MapsTo (fun y : {y : Fin (n - t) → Fin k // y ∈ G} => y.1)
              ↑(G.attach.filter (fun y => f y = σ₀)) ↑H := by
            intro y hy
            rw [Finset.mem_coe, Finset.mem_filter] at hy
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            intro x
            rw [← hy.2]
            exact hf_spec y x
          calc ((G.attach.filter (fun y => f y = σ₀)).card : ℝ)
              = (((G.attach.filter (fun y => f y = σ₀)).image (fun y => y.1)).card : ℝ) := by
                rw [Finset.card_image_of_injective _ Subtype.val_injective]
            _ ≤ (H.card : ℝ) := by
                exact_mod_cast Finset.card_le_card (Finset.image_subset_iff.mpr hmap)
        have hMne : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
        have heq : (δ / (2 * (M : ℝ))) * (k : ℝ) ^ (n - t)
            = (δ / 2) * (k : ℝ) ^ (n - t) / (M : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
          ring
        rw [heq]
        exact le_trans hσ₀ hle
      obtain ⟨lam, hlam⟩ := hn₁ (n - t) hnt H hHcard
      refine ⟨mkSub htn σ₀ lam, fun x => ?_⟩
      rw [mkSub_apply]
      exact (Finset.mem_filter.mp (hlam (x (Fin.natAdd (e + 1) 0)))).2
        (fun i => x (Fin.castAdd 1 i))
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hres := key (m - 1) δ hδ
  rw [hm'] at hres
  exact hres

end

end Commons.Combinatorics.Ramsey