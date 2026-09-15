import Mathlib
import Submission.Commons.Combinatorics.Ramsey.card_varWord
import Submission.Commons.Combinatorics.DensityIncrement.part_pigeonhole_pos

/-!
# The insensitivity core of the Dodos–Kanellopoulos–Tyros density increment

We prove `Commons.Combinatorics.Ramsey.dkt_core_insens`, the combinatorial core of Corollary 11
of

* P. Dodos, V. Kanellopoulos, K. Tyros, *A simple proof of the density Hales–Jewett theorem*,
  arXiv:1209.4986.

Given a line-free set `A ⊆ [k+1]^m` of density at least `δ` together with the dichotomy of
Lemma 8 of *op. cit.* (either `A` is denser than `δ + η²/2` on the whole cube, or it has density
at least `δ - 2η` and at least a `θ/2`-fraction of the combinatorial lines of `[k]^m` are
contained in `A`), we produce a set `D ⊆ [k+1]^m` which is an intersection of `(i,k+1)`-insensitive
sets, has density at least `γ`, and satisfies `dens(A ∩ D) ≥ (δ + γ) dens(D)`.

The construction is the one of the paper: with the insensitive sets `Cᵢ = {x | x_{k+1→i} ∈ A}` and
`C = ⋂ᵢ Cᵢ` one takes the "first violation" partition of `[k+1]^m \ C` into the parts
`Pᵢ = (W \ Cᵢ) ∩ C₁ ∩ … ∩ C_{i-1}`, and the pigeonhole step selects the part on which `A` is
densest.
-/

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

variable {k n m : ℕ}

/-! ## The line through a point with a top letter -/

/-- The "top point" of the line whose pattern word is `g`: the point obtained by substituting the
letter `k+1` for every wildcard of `g`. -/
def topPt (g : Fin n → Option (Fin k)) : Fin n → Fin (k+1) :=
  fun j => ((g j).map Fin.castSucc).getD (Fin.last k)

@[simp] lemma topPt_apply (g : Fin n → Option (Fin k)) (j : Fin n) :
    topPt g j = ((g j).map Fin.castSucc).getD (Fin.last k) := rfl

lemma topPt_of_none {g : Fin n → Option (Fin k)} {j : Fin n} (h : g j = none) :
    topPt g j = Fin.last k := by rw [topPt_apply, h]; rfl

lemma topPt_of_some {g : Fin n → Option (Fin k)} {j : Fin n} {a : Fin k} (h : g j = some a) :
    topPt g j = Fin.castSucc a := by rw [topPt_apply, h]; rfl

lemma topPt_eq_last_iff {g : Fin n → Option (Fin k)} {j : Fin n} :
    topPt g j = Fin.last k ↔ g j = none := by
  cases hg : g j with
  | none =>
    have h : topPt g j = Fin.last k := topPt_of_none hg
    rw [h]; simp
  | some a =>
    have h : topPt g j = Fin.castSucc a := topPt_of_some hg
    rw [h]; simp [Fin.castSucc_ne_last]

/-- Substituting the letter `i` for the wildcards of `g` gives the `i`-th point of the line. -/
lemma replTop_topPt (i : Fin k) (g : Fin n → Option (Fin k)) :
    replTop i (topPt g) = linePt g i := by
  funext j
  rw [replTop, topPt_apply, linePt]
  cases h : g j with
  | none => simp [h]
  | some a => simp [h, Fin.castSucc_ne_last]

/-- The top point map is injective. -/
lemma topPt_injective (k n : ℕ) : Function.Injective (topPt (k := k) (n := n)) := by
  intro g h hgh
  funext j
  have hj : topPt g j = topPt h j := by rw [hgh]
  cases hh : h j with
  | none =>
    have hgj : g j = none := by
      have : topPt g j = Fin.last k := by rw [hj, topPt_of_none hh]
      exact topPt_eq_last_iff.mp this
    simp [hgj, hh]
  | some b =>
    have hgn : g j ≠ none := by
      intro hgn
      rw [topPt_of_none hgn, topPt_of_some hh] at hj
      exact Fin.castSucc_ne_last b hj.symm
    cases hg : g j with
    | none => exact absurd hg hgn
    | some a =>
      rw [topPt_of_some hg, topPt_of_some hh] at hj
      rw [Fin.castSucc_inj.mp hj]

/-- A combinatorial line of `[k+1]^n` all of whose points lie in `A`, built from a point `x ∈ A`
having a top letter and all of whose `(i,k+1)`-replacements lie in `A`. -/
lemma exists_line_of_top (A : Finset (Fin n → Fin (k+1))) {x : Fin n → Fin (k+1)}
    (hj : ∃ j, x j = Fin.last k) (hxA : x ∈ A)
    (hx : ∀ i : Fin k, replTop i x ∈ A) :
    ∃ l : Line (Fin (k+1)) (Fin n), ∀ v : Fin (k+1), l v ∈ A := by
  classical
  have hprop : ∃ j, (fun j => if x j = Fin.last k then none else some (x j)) j = none := by
    obtain ⟨j, hj⟩ := hj
    exact ⟨j, by simp [hj]⟩
  let lin : Line (Fin (k+1)) (Fin n) :=
    ⟨fun j => if x j = Fin.last k then none else some (x j), hprop⟩
  have hcast : ∀ u : Fin k, lin (Fin.castSucc u) = replTop u x := by
    intro u
    funext j
    rw [Line.coe_apply]
    simp only [lin]
    by_cases h : x j = Fin.last k <;> simp [h, replTop]
  have htop : lin (Fin.last k) = x := by
    funext j
    rw [Line.coe_apply]
    simp only [lin]
    by_cases h : x j = Fin.last k <;> simp [h]
  refine ⟨lin, fun v => ?_⟩
  rcases Fin.eq_castSucc_or_eq_last v with ⟨u, rfl⟩ | rfl
  · rw [hcast u]; exact hx u
  · rw [htop]; exact hxA

/-! ## Insensitive sets -/

/-- The relation defining `(i,k+1)`-insensitivity. -/
def SwapRel (i : Fin k) (x y : Fin n → Fin (k+1)) : Prop :=
  ∀ j, y j = x j ∨ (x j = Fin.last k ∧ y j = Fin.castSucc i) ∨
    (y j = Fin.last k ∧ x j = Fin.castSucc i)

lemma swapRel_symm {i : Fin k} {x y : Fin n → Fin (k+1)} (h : SwapRel i x y) :
    SwapRel i y x := by
  intro j
  rcases h j with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- Swapping `i` and the top letter does not change `replTop i`. -/
lemma replTop_eq_of_swap {i : Fin k} {x y : Fin n → Fin (k+1)} (h : SwapRel i x y) :
    replTop i y = replTop i x := by
  funext j
  rw [replTop, replTop]
  rcases h j with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1]
  · simp only [h1, h2, Fin.castSucc_ne_last, if_false, if_true]
  · simp only [h1, h2, Fin.castSucc_ne_last, if_false, if_true]

lemma isInsens_replTop (i : Fin k) (A : Finset (Fin n → Fin (k+1))) :
    IsInsens i (Finset.univ.filter (fun x => replTop i x ∈ A)) := by
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rw [replTop_eq_of_swap hy]
  exact hx

lemma isInsens_univ (k n : ℕ) (i : Fin k) :
    IsInsens i (Finset.univ : Finset (Fin n → Fin (k+1))) :=
  fun _ _ _ _ => Finset.mem_univ _

lemma IsInsens.compl {i : Fin k} {D : Finset (Fin n → Fin (k+1))} (h : IsInsens i D) :
    IsInsens i (Finset.univ \ D) := by
  intro x hx y hy
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
  intro hd
  exact hx (h y hd x (swapRel_symm hy))

/-! ## The top-free subcube -/

/-- The set of points of `[k+1]^n` without any top letter has cardinality `k^n`. -/
theorem card_noTop (k n : ℕ) :
    ((Finset.univ : Finset (Fin n → Fin (k+1))).filter
      (fun x => ∀ j, x j ≠ Fin.last k)).card = k^n := by
  classical
  have himg : (Finset.univ : Finset (Fin n → Fin (k+1))).filter
        (fun x => ∀ j, x j ≠ Fin.last k)
      = Finset.univ.image (kvec (k := k) (n := n)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨fun j => ⟨x j, ?_⟩, ?_⟩
      · have hlt : (x j).val < k + 1 := (x j).isLt
        have hne : (x j).val ≠ k := by
          intro h
          exact hx j (Fin.ext h)
        omega
      · funext j; exact Fin.ext rfl
    · rintro ⟨y, rfl⟩ j
      exact Fin.castSucc_ne_last (y j)
  rw [himg, Finset.card_image_of_injective _ (kvec_injective k n)]
  simp

/-- **Core insensitive-set lemma.** -/
theorem dkt_core_insens (k : ℕ) (hk : 2 ≤ k) (δ θ η γ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη : η = δ * θ / 48) (hγ : γ = δ * η^2 / k)
    (m : ℕ) (hm1 : 1 ≤ m) (hm : ((k : ℝ) ^ m) ≤ η * (((k+1 : ℕ) : ℝ) ^ m))
    (A : Finset (Fin m → Fin (k+1))) (hA : δ * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ))
    (hno : ¬ ∃ l : _root_.Combinatorics.Line (Fin (k+1)) (Fin m), ∀ v : Fin (k+1), l v ∈ A)
    (hcase : (δ + η^2/2) * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ) ∨
      ((δ - 2*η) * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ) ∧
       (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
         (((Commons.Combinatorics.Ramsey.varWord k m).filter
           (fun g => ∀ v : Fin k, Commons.Combinatorics.Ramsey.linePt g v ∈ A)).card : ℝ))) :
    ∃ D : Finset (Fin m → Fin (k+1)),
      (∃ Ds : Fin k → Finset (Fin m → Fin (k+1)),
        (∀ i, Commons.Combinatorics.Ramsey.IsInsens i (Ds i)) ∧
        D = Finset.univ.filter (fun x => ∀ i, x ∈ Ds i)) ∧
      γ * (((k+1 : ℕ) : ℝ) ^ m) ≤ (D.card : ℝ) ∧
      (δ + γ) * (D.card : ℝ) ≤ ((A ∩ D).card : ℝ) := by
  classical
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle1 : η ≤ 1 := by rw [hη]; nlinarith only [hδ.le, hδ1, hθ.le, hθ1]
  have hγnn : 0 ≤ γ := by rw [hγ]; positivity
  have hγle : γ ≤ η^2/2 := by
    rw [hγ, div_le_iff₀ hk0]
    nlinarith only [hδ1, sq_nonneg η, hkR]
  have hγle1 : γ ≤ 1 := by
    have h1 : η^2 ≤ 1 := by nlinarith only [hηle1, hηpos]
    linarith only [hγle, h1]
  have hγle3 : γ ≤ 3*η := by
    rw [hγ, div_le_iff₀ hk0]
    nlinarith only [hδ1, hηle1, hηpos, hkR, sq_nonneg η]
  have hδθ : δ * θ = 48 * η := by rw [hη]; ring
  have hδ3 : 0 < δ - 3*η := by
    have h1 : 3*η ≤ δ/16 := by rw [hη]; nlinarith only [hθ1, hδ.le, hθ.le]
    linarith
  have hXnn : (0:ℝ) ≤ (((k+1 : ℕ) : ℝ))^m := by positivity
  rcases hcase with hinc | ⟨hden, hlines⟩
  · -- Case 1: `A` is denser than `δ + η²/2` on the whole cube.
    have hcard : ((Finset.univ : Finset (Fin m → Fin (k+1))).card : ℝ)
        = (((k+1 : ℕ) : ℝ))^m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast; ring
    refine ⟨Finset.univ, ⟨fun _ => Finset.univ, fun i => isInsens_univ k m i, ?_⟩, ?_, ?_⟩
    · ext x; simp
    · rw [hcard]
      calc γ * (((k+1 : ℕ) : ℝ))^m ≤ 1 * (((k+1 : ℕ) : ℝ))^m :=
            mul_le_mul_of_nonneg_right hγle1 hXnn
        _ = (((k+1 : ℕ) : ℝ))^m := one_mul _
    · rw [hcard, Finset.inter_univ]
      have h1 : (δ + γ) * (((k+1 : ℕ) : ℝ))^m ≤ (δ + η^2/2) * (((k+1 : ℕ) : ℝ))^m :=
        mul_le_mul_of_nonneg_right (by linarith [hγle]) hXnn
      linarith [hinc, h1]
  · -- Case 2: the insensitive-set construction
    set N : ℝ := (((k+1 : ℕ) : ℝ))^m with hN
    have hNpos : 0 < N := by rw [hN]; positivity
    have hnK : ((k:ℝ)^m) ≤ η * N := by rw [hN]; exact hm
    have hden' : (δ - 2*η) * N ≤ (A.card : ℝ) := by rw [hN]; exact hden
    have hlines' : (θ/2) * (N - ((k:ℝ)^m))
        ≤ (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) := by
      rw [hN]; exact hlines
    -- the insensitive sets `Cᵢ` and their intersection `C`
    let Ci : Fin k → Finset (Fin m → Fin (k+1)) :=
      fun i => Finset.univ.filter (fun x => replTop i x ∈ A)
    let C : Finset (Fin m → Fin (k+1)) := Finset.univ.filter (fun x => ∀ i, x ∈ Ci i)
    have hmemCi : ∀ (i : Fin k) (x : Fin m → Fin (k+1)), x ∈ Ci i ↔ replTop i x ∈ A := by
      intro i x; simp [Ci]
    have hmemC : ∀ x : Fin m → Fin (k+1), x ∈ C ↔ ∀ i, x ∈ Ci i := by
      intro x; simp [C]
    -- the set of "good" lines
    set G := (varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A) with hG
    have hlinesG : (θ/2) * (N - ((k:ℝ)^m)) ≤ (G.card : ℝ) := by rw [hG]; exact hlines'
    have hGC : (G.card : ℝ) ≤ (C.card : ℝ) := by
      have h1 : G.card ≤ C.card := by
        refine Finset.card_le_card_of_injOn (topPt (k := k) (n := m)) ?_ ?_
        · intro g hg
          simp only [Finset.mem_coe, hG, Finset.mem_filter] at hg
          rw [Finset.mem_coe, hmemC]
          intro i
          rw [hmemCi, replTop_topPt]
          exact hg.2 i
        · intro g _ h _ hgh
          exact topPt_injective k m hgh
      exact_mod_cast h1
    have hGlower : (θ/2) * (N - ((k:ℝ)^m)) ≤ (C.card : ℝ) := le_trans hlinesG hGC
    -- `|C| ≥ (θ/4) N`
    have hCbound : (θ/4) * N ≤ (C.card : ℝ) := by
      have h1 : (1 - η) * N ≤ N - ((k:ℝ)^m) := by linarith [hnK]
      have h2 : (θ/2) * ((1-η) * N) ≤ (C.card : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ θ/2)
        linarith [this, hGlower]
      have h3 : (θ/4) * N ≤ (θ/2) * ((1-η)*N) := by
        have hηhalf : η ≤ 1/2 := by linarith
        have hθN : 0 ≤ θ * N := mul_nonneg hθ.le hNpos.le
        nlinarith only [hθN, hηhalf]
      linarith [h2, h3]
    -- `A ∩ C` consists of top-free points
    have hACtop : A ∩ C ⊆ (Finset.univ : Finset (Fin m → Fin (k+1))).filter
        (fun x => ∀ j, x j ≠ Fin.last k) := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨hxA, hxC⟩ := hx
      by_contra hcon
      push_neg at hcon
      obtain ⟨j0, hj0⟩ := hcon
      exact hno (exists_line_of_top A ⟨j0, hj0⟩ hxA
        (fun i => (hmemCi i x).mp ((hmemC x).mp hxC i)))
    have hACcard : ((A ∩ C).card : ℝ) ≤ η * N := by
      have h1 : (A ∩ C).card ≤ k^m := by
        calc (A ∩ C).card ≤ ((Finset.univ : Finset (Fin m → Fin (k+1))).filter
              (fun x => ∀ j, x j ≠ Fin.last k)).card := Finset.card_le_card hACtop
          _ = k^m := card_noTop k m
      calc ((A ∩ C).card : ℝ) ≤ ((k^m : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (k:ℝ)^m := by push_cast; ring
        _ ≤ η * N := hnK
    -- `|Cᶜ| = N - |C|`, hence `|Cᶜ| ≤ (1 - θ/4) N`
    have hcompl : ((Cᶜ).card : ℝ) = N - (C.card : ℝ) := by
      have hle : C.card ≤ (k+1)^m := by
        have := Finset.card_le_univ C
        simpa [Fintype.card_fun] using this
      rw [Finset.card_compl, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        Nat.cast_sub hle, hN]
      push_cast; ring
    have hWC : ((Cᶜ).card : ℝ) ≤ (1 - θ/4) * N := by
      rw [hcompl]; nlinarith only [hCbound]
    -- `|A \ C| ≥ (δ - 3η) N`
    have hAUC : (δ - 3*η) * N ≤ ((A \ C).card : ℝ) := by
      have hsub : A ⊆ (A ∩ C) ∪ (A \ C) := by
        intro x hx
        by_cases h : x ∈ C
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩))
      have h1 : A.card ≤ ((A ∩ C) ∪ (A \ C)).card := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (A ∩ C) (A \ C)
      have h3 : (A.card : ℝ) ≤ ((A ∩ C).card : ℝ) + ((A \ C).card : ℝ) := by
        exact_mod_cast le_trans h1 h2
      linarith [hden', hACcard, h3]
    -- the density of `A` on `W \ C` is at least `δ + 6η`
    have hCpos : 0 < ((Cᶜ).card : ℝ) := by
      have h3 : 0 < (δ - 3*η) * N := mul_pos hδ3 hNpos
      have hsub : A \ C ⊆ Cᶜ := by
        intro x hx
        rw [Finset.mem_compl]
        exact (Finset.mem_sdiff.mp hx).2
      have h4 : ((A \ C).card : ℝ) ≤ ((Cᶜ).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hAUC, h3, h4]
    have hratio : δ + 6*η ≤ ((A \ C).card : ℝ) / ((Cᶜ).card : ℝ) := by
      rw [le_div_iff₀ hCpos]
      have h1 : (δ + 6*η) * ((Cᶜ).card : ℝ) ≤ (δ + 6*η) * ((1 - θ/4) * N) :=
        mul_le_mul_of_nonneg_left hWC (by linarith [hδ.le, hηpos.le])
      have h2 : (δ + 6*η) * ((1 - θ/4) * N) ≤ (δ - 3*η) * N := by
        have h2a : (δ + 6*η) * (1 - θ/4) ≤ δ - 3*η := by
          nlinarith only [hδθ, hθ.le, hηpos.le, hδ.le]
        calc (δ + 6*η) * ((1 - θ/4) * N) = ((δ + 6*η) * (1 - θ/4)) * N := by ring
          _ ≤ (δ - 3*η) * N := mul_le_mul_of_nonneg_right h2a hNpos.le
      linarith [h1, h2, hAUC]
    -- the first-violation partition of `W \ C`
    let part : Fin k → Finset (Fin m → Fin (k+1)) :=
      fun i => Finset.univ.filter (fun x => x ∉ Ci i ∧ ∀ j, j < i → x ∈ Ci j)
    have hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (part i) (part j) := by
      intro i j hij
      rw [Finset.disjoint_left]
      intro x hxi hxj
      have hxi' := (Finset.mem_filter.mp hxi).2
      have hxj' := (Finset.mem_filter.mp hxj).2
      rcases lt_or_gt_of_ne hij with h | h
      · exact hxi'.1 (hxj'.2 i h)
      · exact hxj'.1 (hxi'.2 j h)
    have hcover : (Finset.univ : Finset (Fin m → Fin (k+1))).filter
          (fun x => ∃ i : Fin k, x ∉ Ci i) = Finset.univ.biUnion part := by
      ext x
      simp only [part, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨i0, hi0⟩
        set S := Finset.univ.filter (fun i : Fin k => x ∉ Ci i) with hS
        have hne : S.Nonempty := ⟨i0, by simp [hS, hi0]⟩
        have hminmem : S.min' hne ∈ S := Finset.min'_mem S hne
        have hmin := (Finset.mem_filter.mp hminmem).2
        refine ⟨S.min' hne, hmin, ?_⟩
        intro j hj
        by_contra hjc
        have hjS : j ∈ S := by simp [hS, hjc]
        have := Finset.min'_le S j hjS
        exact absurd hj (not_lt.mpr this)
      · rintro ⟨i, h1, _⟩
        exact ⟨i, h1⟩
    have hunion : Finset.univ.biUnion part = Cᶜ := by
      rw [← hcover]
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hmemC]
      constructor
      · rintro ⟨i, hi⟩ hC
        exact hi (hC i)
      · intro hx
        by_contra hcon
        push_neg at hcon
        exact hx hcon
    -- the two sum identities
    have hsumM : ∑ i : Fin k, ((part i).card : ℝ) = ((Cᶜ).card : ℝ) := by
      have hnat : (Finset.univ.biUnion part).card = ∑ i : Fin k, (part i).card := by
        rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
      have hcast : ((Finset.univ.biUnion part).card : ℝ) = ∑ i : Fin k, ((part i).card : ℝ) := by
        rw [hnat]; push_cast; ring
      rw [hunion] at hcast
      exact hcast.symm
    have hsumA : ∑ i : Fin k, ((A ∩ part i).card : ℝ) = ((A \ C).card : ℝ) := by
      have hdisjA : ∀ i j : Fin k, i ≠ j → Disjoint (A ∩ part i) (A ∩ part j) := fun i j hij =>
        Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj i j hij)
      have hnat : (Finset.univ.biUnion (fun i => A ∩ part i)).card
          = ∑ i : Fin k, (A ∩ part i).card := by
        rw [Finset.card_biUnion (fun i _ j _ hij => hdisjA i j hij)]
      have hunionA : Finset.univ.biUnion (fun i => A ∩ part i) = A \ C := by
        have h1 : Finset.univ.biUnion (fun i => A ∩ part i)
            = A ∩ Finset.univ.biUnion part := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
          constructor
          · rintro ⟨i, hxA, hxp⟩
            exact ⟨hxA, ⟨i, hxp⟩⟩
          · rintro ⟨hxA, i, hxp⟩
            exact ⟨i, hxA, hxp⟩
        rw [h1, hunion]
        ext x
        simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
      have hcast : ((Finset.univ.biUnion (fun i => A ∩ part i)).card : ℝ)
          = ∑ i : Fin k, ((A ∩ part i).card : ℝ) := by
        rw [hnat]; push_cast; ring
      rw [hunionA] at hcast
      exact hcast.symm
    -- the pigeonhole step
    have hratio' : (δ + 6*η) * ((Cᶜ).card : ℝ) ≤ ((A \ C).card : ℝ) := by
      rw [le_div_iff₀ hCpos] at hratio
      exact hratio
    have hkey : (δ + 3*η + (3*η/k) * (Fintype.card (Fin k) : ℝ)) * ((Cᶜ).card : ℝ)
        ≤ ((A \ C).card : ℝ) := by
      have hcard : (Fintype.card (Fin k) : ℝ) = k := by simp
      have hcalc : (3*η/k) * (k:ℝ) = 3*η := div_mul_cancel₀ (3*η) (by positivity)
      have h1 : δ + 3*η + (3*η/k) * (Fintype.card (Fin k) : ℝ) = δ + 6*η := by
        rw [hcard, hcalc]; ring
      rw [h1]; exact hratio'
    haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    obtain ⟨i₀, hi₀1, hi₀2⟩ :=
      Commons.Combinatorics.DensityIncrement.part_pigeonhole_pos (fun i : Fin k => ((part i).card : ℝ))
      (fun i : Fin k => ((A ∩ part i).card : ℝ)) ((Cᶜ).card : ℝ) ((A \ C).card : ℝ)
      (δ + 3*η) (3*η/k) (fun i => Nat.cast_nonneg _)
      (fun i => by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
      hsumM hsumA (Nat.cast_nonneg _) (div_nonneg (by linarith [hηpos.le]) hk0.le)
      (by linarith [hδ.le, hηpos.le]) hkey
    -- the final set
    let Ds : Fin k → Finset (Fin m → Fin (k+1)) :=
      fun i => if i = i₀ then (Ci i₀)ᶜ else if i < i₀ then Ci i else Finset.univ
    let D : Finset (Fin m → Fin (k+1)) := Finset.univ.filter (fun x => ∀ i, x ∈ Ds i)
    have hD : D = part i₀ := by
      ext x
      simp only [D, Ds, part, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · have h' : x ∈ (Ci i₀)ᶜ := by simpa using h i₀
          exact Finset.mem_compl.mp h'
        · intro j hj
          have h' : x ∈ Ci j := by
            simpa only [if_neg (ne_of_lt hj), if_pos hj] using h j
          exact h'
      · rintro ⟨h1, h2⟩ i
        by_cases hi : i = i₀
        · subst hi
          simpa using h1
        · by_cases hj : i < i₀
          · simpa only [if_neg hi, if_pos hj] using h2 i hj
          · rw [if_neg hi, if_neg hj]
            exact Finset.mem_univ x
    refine ⟨D, ⟨Ds, ?_, rfl⟩, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · have hDs : Ds i = (Ci i)ᶜ := by
          rw [show Ds i = (Ci i₀)ᶜ from by simp only [Ds]; exact if_pos hi, hi]
        rw [hDs]
        exact IsInsens.compl (isInsens_replTop i A)
      · by_cases hj : i < i₀
        · simp only [Ds, if_neg hi, if_pos hj]
          exact isInsens_replTop i A
        · simp only [Ds, if_neg hi, if_neg hj]
          exact isInsens_univ k m i
    · rw [hD]
      have hMbound : (δ - 3*η) * N ≤ ((Cᶜ).card : ℝ) := by
        have hsub : A \ C ⊆ Cᶜ := by
          intro x hx
          rw [Finset.mem_compl]
          exact (Finset.mem_sdiff.mp hx).2
        have h4 : ((A \ C).card : ℝ) ≤ ((Cᶜ).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        linarith [hAUC, h4]
      have h3ηk : (0:ℝ) ≤ 3*η/k := by positivity
      have hbig : (3*η/k) * ((δ - 3*η)*N) ≤ ((part i₀).card : ℝ) := by
        have h5 := mul_le_mul_of_nonneg_left hMbound h3ηk
        linarith [h5, hi₀1]
      have hγle : γ ≤ (3*η/k) * (δ - 3*η) := by
        have h1 : 3*η ≤ δ/16 := by rw [hη]; nlinarith only [hθ1, hδ.le, hθ.le]
        have hmain : δ * η^2 ≤ 3*η*(δ-3*η) := by
          nlinarith only [hδ1, hηle1, hηpos, hδθ, hδ.le, h1]
        rw [hγ]
        calc δ * η^2 / k = (δ * η^2) / k := rfl
          _ ≤ (3*η*(δ-3*η)) / k := div_le_div_of_nonneg_right hmain hk0.le
          _ = (3*η/k) * (δ-3*η) := by ring
      have h6 : γ * N ≤ (3*η/k) * (δ - 3*η) * N := by
        have := mul_le_mul_of_nonneg_right hγle hNpos.le
        linarith [this]
      linarith [hbig, h6]
    · rw [hD]
      have hδγ : δ + γ ≤ δ + 3*η := by linarith [hγle3]
      have h7 : (δ + γ) * ((part i₀).card : ℝ) ≤ (δ + 3*η) * ((part i₀).card : ℝ) :=
        mul_le_mul_of_nonneg_right hδγ (Nat.cast_nonneg _)
      linarith [h7, hi₀2]

end
end Commons.Combinatorics.Ramsey
