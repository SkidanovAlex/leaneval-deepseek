import Mathlib
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj
import Submission.Commons.Combinatorics.Ramsey.insens_lemma
import Submission.Commons.Combinatorics.Ramsey.kvec_injective
import Submission.Commons.Combinatorics.Ramsey.exists_subspace_dense_slices
import Submission.Commons.Combinatorics.Ramsey.dkt_dichotomy
import Submission.Commons.Combinatorics.Ramsey.dkt_insens_correlation
import Submission.Commons.Combinatorics.Ramsey.dkt_c5
import Submission.Commons.Combinatorics.Ramsey.dkt_tiling
import Submission.Commons.Combinatorics.Additive.Szemeredi.dhj_two

/-!
# The density-increment dichotomy of Dodos–Kanellopoulos–Tyros

Formalisation of Proposition 6 of

* P. Dodos, V. Kanellopoulos, K. Tyros, *A simple proof of the density Hales–Jewett
  theorem*, arXiv:1209.4986,

in the form requested as `Commons.Combinatorics.Ramsey.dkt_density_increment`: from the
density Hales–Jewett theorem for the alphabet `Fin k` and the Graham–Rothschild theorem for
combinatorial lines of `[k]^n`, one deduces that a dense subset of `[k+1]^n` either contains
a combinatorial line or is denser than `δ` on some `d`-dimensional subspace.

The proof follows DKT §4 closely: MDHJ and its "starred" form (in the commons), the
DKT dichotomy `dkt_dichotomy`, the correlation with an intersection of
`(i,k+1)`-insensitive sets `dkt_insens_correlation`, the tiling of such sets by subspaces
`dkt_tiling`, and a final averaging step.
-/

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

lemma dkt_wsubst_some {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (y : Fin m → Fin (k+1)) :
    wsubst S (fun e => some (y e)) = fun i => some (S y i) := by
  funext i
  rw [wsubst_apply, Subspace.coe_apply]
  cases h : S.idxFun i <;> simp

lemma dkt_scomp_apply {k m m' n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (T : Subspace (Fin m') (Fin (k+1)) (Fin m)) (y : Fin m' → Fin (k+1)) :
    scomp S T y = S (T y) := by
  funext i
  have h := congrFun (wsubst_scomp S T (fun e => some (y e))) i
  rw [dkt_wsubst_some, dkt_wsubst_some, dkt_wsubst_some] at h
  exact Option.some.inj h

/-- The pullback of a set along a subspace, in coordinates. -/
def dktPull {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (A : Finset (Fin n → Fin (k+1))) : Finset (Fin m → Fin (k+1)) :=
  Finset.univ.filter (fun x => S x ∈ A)

lemma mem_dktPull {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (A : Finset (Fin n → Fin (k+1))) (x : Fin m → Fin (k+1)) :
    x ∈ dktPull S A ↔ S x ∈ A := by
  simp [dktPull]

/-- The image of a line under a subspace. -/
def dktSline {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (l : Line (Fin (k+1)) (Fin m)) : Line (Fin (k+1)) (Fin n) where
  idxFun i := match S.idxFun i with
    | Sum.inl a => some a
    | Sum.inr e => l.idxFun e
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    obtain ⟨j, hj⟩ := S.proper i
    refine ⟨j, ?_⟩
    rw [hj]
    simp [hi]

lemma dktSline_apply {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (l : Line (Fin (k+1)) (Fin m)) (v : Fin (k+1)) :
    dktSline S l v = S (l v) := by
  funext i
  rw [Line.coe_apply, Subspace.coe_apply]
  simp only [dktSline]
  cases h : S.idxFun i <;> simp

lemma dkt_subspace_injective {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n)) :
    Function.Injective (fun x : Fin m → Fin (k+1) => S x) := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := S.proper e
  have h : S x i = S y i := congrFun hxy i
  rw [Subspace.apply_inr hi, Subspace.apply_inr hi] at h
  exact h

lemma dkt_not_line_pull {k m n : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (A : Finset (Fin n → Fin (k+1)))
    (hA : ¬ ∃ l : Line (Fin (k+1)) (Fin n), ∀ v : Fin (k+1), l v ∈ A) :
    ¬ ∃ l : Line (Fin (k+1)) (Fin m), ∀ v : Fin (k+1), l v ∈ dktPull S A := by
  rintro ⟨l, hl⟩
  exact hA ⟨dktSline S l, fun v => by
    rw [dktSline_apply]
    exact (mem_dktPull S A (l v)).mp (hl v)⟩

lemma dkt_card_filter_scomp {k m n d : ℕ} (S : Subspace (Fin m) (Fin (k+1)) (Fin n))
    (V : Subspace (Fin d) (Fin (k+1)) (Fin m)) (A : Finset (Fin n → Fin (k+1))) :
    ((Finset.univ : Finset (Fin d → Fin (k+1))).filter (fun x => scomp S V x ∈ A)).card
      = ((Finset.univ : Finset (Fin d → Fin (k+1))).filter
          (fun x => V x ∈ dktPull S A)).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_dktPull]
  rw [dkt_scomp_apply]

/-- For `η > 0` and `k ≥ 1` there is `M` with `k^m ≤ η (k+1)^m` for all `m ≥ M`. -/
lemma dkt_exists_pow_mul_le (k : ℕ) (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (k : ℝ)^m ≤ η * (((k+1:ℕ):ℝ))^m := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos' : (0:ℝ) < (k:ℝ) := by linarith
  have hq : (1:ℝ) < (((k+1:ℕ):ℝ)) / (k:ℝ) := by
    rw [lt_div_iff₀ hkpos']
    push_cast
    linarith
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (1/η) hq
  refine ⟨M, fun m hm => ?_⟩
  have h2 : (((k+1:ℕ):ℝ)/(k:ℝ))^M ≤ (((k+1:ℕ):ℝ)/(k:ℝ))^m :=
    pow_le_pow_right₀ hq.le hm
  have h3 : 1/η < (((k+1:ℕ):ℝ)/(k:ℝ))^m := lt_of_lt_of_le hM h2
  have h4 : 1 < η * ((((k+1:ℕ):ℝ)/(k:ℝ))^m) := by
    have := (div_lt_iff₀ hη).mp h3
    rwa [mul_comm] at this
  have hmul := mul_lt_mul_of_pos_right h4 (pow_pos hkpos' m)
  rw [one_mul] at hmul
  have heq : (((k+1:ℕ):ℝ)/(k:ℝ))^m * (k:ℝ)^m = (((k+1:ℕ):ℝ))^m := by
    rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hkpos')]
  rw [mul_assoc] at hmul
  rw [heq] at hmul
  exact le_of_lt hmul

/-- The points of a subspace that lie in `A`, as a set of coordinates. -/
lemma dkt_inter_image_eq {k d m : ℕ} (V : Subspace (Fin d) (Fin (k+1)) (Fin m))
    (A : Finset (Fin m → Fin (k+1))) :
    A ∩ Finset.univ.image (fun x => V x)
      = Finset.image (fun x => V x)
          ((Finset.univ : Finset (Fin d → Fin (k+1))).filter (fun x => V x ∈ A)) := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨hyA, x, hx⟩
    exact ⟨x, hx ▸ hyA, hx⟩
  · rintro ⟨x, hxA, hx⟩
    exact ⟨hx.symm ▸ hxA, x, hx⟩

/-- Final averaging step of the density-increment argument. -/
lemma dktFinalStep {k d m : ℕ} (hk : 1 ≤ k) {δ γ : ℝ} (hγ : 0 < γ) (hδγ : 0 < δ + γ/2)
    (A D : Finset (Fin m → Fin (k+1)))
    (VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin m)))
    (hDcard : γ * (((k+1:ℕ):ℝ)^m) ≤ (D.card : ℝ))
    (hDcorr : (δ + γ) * (D.card : ℝ) ≤ ((A ∩ D).card : ℝ))
    (hsub : ∀ S ∈ VS, ∀ x : Fin d → Fin (k+1), S x ∈ D)
    (hdisj : ∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
      Disjoint (Finset.univ.image (fun x => S x)) (Finset.univ.image (fun x => S' x)))
    (hcov : (D.card : ℝ) - γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤
      ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ)) :
    ∃ S ∈ VS, (δ + γ/2) * (((k+1:ℕ):ℝ)^d)
      ≤ ((A ∩ Finset.univ.image (fun x => S x)).card : ℝ) := by
  classical
  set U : Finset (Fin m → Fin (k+1)) :=
    VS.biUnion (fun S => Finset.univ.image (fun x => S x)) with hU
  have hKd : ∀ S : Subspace (Fin d) (Fin (k+1)) (Fin m),
      (Finset.univ.image (fun x : Fin d → Fin (k+1) => S x)).card = (k+1)^d := by
    intro S
    rw [Finset.card_image_of_injective _ (dkt_subspace_injective S), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hUsub : U ⊆ D := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨S, hS, hxS⟩ := hx
    rw [Finset.mem_image] at hxS
    obtain ⟨y, -, rfl⟩ := hxS
    exact hsub S hS y
  have hUle_D : (U.card : ℝ) ≤ (D.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hUsub
  have hDU : (((D \ U).card : ℕ) : ℝ) = (D.card : ℝ) - (U.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hUsub]
    exact Nat.cast_sub (Finset.card_le_card hUsub)
  have h1 : ((A ∩ D).card : ℝ) ≤ ((A ∩ U).card : ℝ) + (((D \ U).card : ℕ) : ℝ) := by
    have hsub' : A ∩ D ⊆ (A ∩ U) ∪ (D \ U) := by
      intro x hx
      rw [Finset.mem_inter] at hx
      by_cases hxU : x ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx.1, hxU⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx.2, hxU⟩)
    have h2 := Finset.card_le_card hsub'
    have h3 := Finset.card_union_le (A ∩ U) (D \ U)
    exact_mod_cast le_trans h2 h3
  have h3 : (((D \ U).card : ℕ) : ℝ) ≤ γ^2/2 * (((k+1:ℕ):ℝ)^m) := by
    rw [hDU]; linarith [hcov]
  have h4 : γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤ (γ/2) * (D.card : ℝ) := by
    nlinarith [hDcard, hγ]
  have h5 : (δ + γ/2) * (D.card : ℝ) ≤ ((A ∩ U).card : ℝ) := by
    nlinarith [hDcorr, h1, h3, h4]
  have h6 : ((A ∩ U).card : ℝ) ≤
      ∑ S ∈ VS, ((A ∩ Finset.univ.image (fun x => S x)).card : ℝ) := by
    have hsub'' : A ∩ U ⊆ VS.biUnion (fun S => A ∩ Finset.univ.image (fun x => S x)) := by
      intro x hx
      rw [Finset.mem_inter] at hx
      have hxU : x ∈ U := hx.2
      rw [hU, Finset.mem_biUnion] at hxU
      obtain ⟨S, hS, hxS⟩ := hxU
      exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_inter.mpr ⟨hx.1, hxS⟩⟩
    have h7 := Finset.card_le_card hsub''
    have h8 := Finset.card_biUnion_le (s := VS)
      (t := fun S => A ∩ Finset.univ.image (fun x => S x))
    exact_mod_cast le_trans h7 h8
  have hUcard : (U.card : ℝ) = ∑ S ∈ VS, (((k+1:ℕ):ℝ)^d) := by
    have hpw : (VS : Set (Subspace (Fin d) (Fin (k+1)) (Fin m))).PairwiseDisjoint
        (fun S => Finset.univ.image (fun x => S x)) := fun S hS S' hS' hne =>
      hdisj S hS S' hS' hne
    rw [hU, Finset.card_biUnion hpw, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun S _ => by rw [hKd S]; push_cast; ring)
  have h9 : (δ + γ/2) * (U.card : ℝ) ≤ ((A ∩ U).card : ℝ) := by
    have hpos : (0:ℝ) ≤ δ + γ/2 := le_of_lt hδγ
    have hmul := mul_le_mul_of_nonneg_left hUle_D hpos
    linarith [h5, hmul]
  have h10 : (δ + γ/2) * (∑ S ∈ VS, (((k+1:ℕ):ℝ)^d))
      ≤ ∑ S ∈ VS, ((A ∩ Finset.univ.image (fun x => S x)).card : ℝ) := by
    rw [← hUcard]
    exact le_trans h9 h6
  by_contra hcon
  push Not at hcon
  have hDpos : (0:ℝ) < (D.card : ℝ) := by
    have hh : (0:ℝ) < γ * (((k+1:ℕ):ℝ)^m) := by positivity
    linarith [hDcard]
  have hpos : 0 < δ + γ/2 := by linarith
  have hVSne : VS.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ∅ := by rw [hU, h]; simp
    have hzero : ((A ∩ U).card : ℝ) = 0 := by rw [hU0]; simp
    rw [hzero] at h5
    nlinarith [h5, hDpos, hpos]
  have hlt := Finset.sum_lt_sum_of_nonempty hVSne (fun S hS => hcon S hS)
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have h11 : (∑ S ∈ VS, (((k+1:ℕ):ℝ)^d)) = (VS.card : ℝ) * (((k+1:ℕ):ℝ)^d) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h11] at h10
  nlinarith [h10, hlt]


theorem dkt_density_increment (k : ℕ) (hk : 1 ≤ k)
    (hdhj : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (hgr : ∀ (M : ℕ), ∃ n : ℕ, ∀ n' : ℕ, n ≤ n' → ∀ C : Combinatorics.Line (Fin k) (Fin n') → Fin 2,
      ∃ S : Combinatorics.Subspace (Fin M) (Fin k) (Fin n'), ∃ c : Fin 2,
        ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ d : ℕ, 1 ≤ d → ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin (k+1)),
        δ * ((k+1 : ℕ) : ℝ) ^ n ≤ (T.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin (k+1)) (Fin n), ∀ x : Fin (k+1), l x ∈ T) ∨
        ∃ S : Combinatorics.Subspace (Fin d) (Fin (k+1)) (Fin n),
          (δ + γ) * ((k+1 : ℕ) : ℝ) ^ d
            ≤ ((Finset.univ : Finset (Fin d → Fin (k+1))).filter (fun x => S x ∈ T)).card := by
  intro δ hδ hδ1 d hd
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    obtain ⟨n₁, hn₁⟩ := _root_.Commons.Combinatorics.Additive.Szemeredi.dhj_two δ hδ
    refine ⟨1, one_pos, max n₁ 1, ?_⟩
    intro n hn T hT
    refine Or.inl ?_
    obtain ⟨w, P, hP, hw⟩ := hn₁ n (le_trans (le_max_left _ _) hn) T hT
    refine ⟨⟨fun i => if i ∈ P then none else some (w i), ?_⟩, fun v => ?_⟩
    · obtain ⟨i, hi⟩ := hP
      exact ⟨i, by simp [hi]⟩
    · have h1 : (fun i => (if i ∈ P then (none : Option (Fin (1+1))) else some (w i)).getD v)
          = (fun i => if i ∈ P then v else w i) := by
        funext i
        by_cases h : i ∈ P <;> simp [h]
      show (fun i => (if i ∈ P then (none : Option (Fin (1+1))) else some (w i)).getD v) ∈ T
      rw [h1]
      exact hw v
  · obtain ⟨m₀', hm₀'⟩ := hdhj (δ/4) (by linarith)
    set m₀ : ℕ := max m₀' 1 with hm₀def
    have hm₀1 : 1 ≤ m₀ := le_max_right _ _
    have hm₀_thr : ∀ n : ℕ, m₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
        (δ/4) * (k : ℝ)^n ≤ (T.card : ℝ) → ∃ l : Line (Fin k) (Fin n), ∀ x, l x ∈ T := by
      intro n hn T hT
      exact hm₀' n (le_trans (le_max_left _ _) hn) T hT
    have hKk : (0:ℝ) < (((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀ := by
      have h2 : ((k:ℝ)) < ((k+1:ℕ):ℝ) := by push_cast; linarith
      have h1 : (k:ℝ)^m₀ < (((k+1:ℕ):ℝ))^m₀ :=
        pow_lt_pow_left₀ h2 (by positivity) (by omega)
      linarith
    set θ : ℝ := min ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) 1 with hθdef
    have hθpos : 0 < θ := lt_min (div_pos (by linarith) hKk) one_pos
    have hθ1 : θ ≤ 1 := min_le_right _ _
    have hθm : θ * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) ≤ δ/4 := by
      have h1 : θ ≤ (δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) := min_le_left _ _
      have h2 : ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)
          = δ/4 := div_mul_cancel₀ _ hKk.ne'
      calc θ * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)
          ≤ ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) :=
            mul_le_mul_of_nonneg_right h1 hKk.le
        _ = δ/4 := h2
    set η : ℝ := δ * θ / 48 with hηdef
    set γ : ℝ := δ * η^2 / k with hγdef
    have hηpos : 0 < η := by rw [hηdef]; positivity
    have hγpos : 0 < γ := by rw [hγdef]; positivity
    have hη_le : η ≤ 1/48 := by
      rw [hηdef]
      have : δ * θ ≤ 1 := by nlinarith [hδ, hδ1, hθpos, hθ1]
      linarith
    have hγ_le_one : γ ≤ 1 := by
      rw [hγdef]
      have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
      have hη2 : η^2 ≤ 1 := by nlinarith [hη_le, hηpos]
      have hδk : δ / (k:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (k:ℝ))]
        linarith [hδ1, hk2']
      calc δ * η^2 / (k:ℝ) = (δ / (k:ℝ)) * η^2 := by ring
        _ ≤ 1 * 1 := by
              exact mul_le_mul hδk hη2 (by positivity) (by norm_num)
        _ = 1 := by ring
    set β : ℝ := γ^2/(4*k) with hβdef
    have hβpos : 0 < β := by rw [hβdef]; positivity
    have hβ1 : β ≤ 1 := by
      have h1 : γ^2 ≤ 1 := by nlinarith [hγ_le_one, hγpos]
      have h2 : (1:ℝ) ≤ 4 * (k:ℝ) := by
        have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
        linarith
      rw [hβdef, div_le_one (by positivity : (0:ℝ) < 4 * (k:ℝ))]
      linarith
    have hc5 : ∀ (m : ℕ), 1 ≤ m → ∀ β' : ℝ, 0 < β' → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Finset (Fin n → Fin (k+1)), β' * (((k+1:ℕ):ℝ))^n ≤ (D.card : ℝ) →
          ∃ V : Subspace (Fin m) (Fin (k+1)) (Fin n),
            ∀ x : Fin m → Fin k, V (kvec x) ∈ D := by
      intro m hm β' hβ'
      by_cases hβ'1 : β' ≤ 1
      · exact dkt_c5 k (by omega) hdhj
          (fun K m hK hm ε hε hε1 => exists_subspace_dense_slices K m hK hm ε hε hε1)
          m hm β' hβ' hβ'1
      · push Not at hβ'1
        refine ⟨0, fun n _ D hD => ?_⟩
        exfalso
        have h1 : (D.card : ℝ) ≤ (((k+1:ℕ):ℝ))^n := by
          have h2 : D.card ≤ Fintype.card (Fin n → Fin (k+1)) := Finset.card_le_univ D
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h2
          exact_mod_cast h2
        have h3 : (0:ℝ) < (((k+1:ℕ):ℝ))^n := by positivity
        nlinarith [hD, h1, hβ'1, h3]
    obtain ⟨Ntil, htil⟩ := dkt_tiling k hk2 hc5 d hd β hβpos hβ1
    obtain ⟨M₁, hM₁⟩ := dkt_exists_pow_mul_le k (by omega) hηpos
    set m : ℕ := m₀ + d + M₁ + Ntil + 1 with hmdef
    have hm_m₀ : m₀ ≤ m := by omega
    have hm_d : d ≤ m := by omega
    have hm_M₁ : M₁ ≤ m := by omega
    have hm_Ntil : Ntil ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    have hm_lam : (k:ℝ)^m ≤ η * (((k+1:ℕ):ℝ))^m := hM₁ m hm_M₁
    obtain ⟨ndich, hdich⟩ := dkt_dichotomy k hk2 hgr
        (fun K m hK hm ε hε hε1 => exists_subspace_dense_slices K m hK hm ε hε hε1)
        δ θ η hδ hδ1 hθpos hθ1 hηdef m₀ hm₀1 hm₀_thr hθm m hm_m₀
    refine ⟨γ/2, by linarith, max ndich 1, ?_⟩
    intro n hn T hT
    by_cases hline : ∃ l : Line (Fin (k+1)) (Fin n), ∀ x : Fin (k+1), l x ∈ T
    · exact Or.inl hline
    · refine Or.inr ?_
      have htwo : 2 * ((k : ℝ)) * β = γ^2/2 := by
        rw [hβdef]
        field_simp
        ring
      have hdensD_ge : γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤ γ * (((k+1:ℕ):ℝ)^m) := by
        have hle : γ^2/2 ≤ γ := by nlinarith [hγ_le_one, hγpos]
        exact mul_le_mul_of_nonneg_right hle (by positivity)
      obtain ⟨X, hX⟩ | ⟨W, hW1, hW2⟩ := hdich n (le_trans (le_max_left _ _) hn) T hT
      · -- Case (i): a dense `m`-dimensional subspace
        set A : Finset (Fin m → Fin (k+1)) := dktPull X T with hAdef
        have hAno : ¬ ∃ l : Line (Fin (k+1)) (Fin m), ∀ v, l v ∈ A := by
          rw [hAdef]; exact dkt_not_line_pull X T hline
        have hA2 : (δ - 2*η) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) := by
          have hle : δ - 2*η ≤ δ + η^2/2 := by nlinarith [hηpos]
          have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ (((k+1:ℕ):ℝ))^m)
          rw [hAdef]
          simp only [dktPull]
          linarith [hX, hmul]
        have hcase : (δ + η^2/2) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) ∨
            (θ/2) * ((((k+1:ℕ):ℝ)^m) - ((k:ℝ)^m)) ≤
              (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) :=
          Or.inl hX
        obtain ⟨D, ⟨Ds, hinsens, hDdef⟩, hDcard, hDcorr⟩ :=
          dkt_insens_correlation k hk2 δ θ η γ hδ hδ1 hθpos hθ1 hηdef hγdef m hm1
            hm_lam A hA2 hAno hcase
        have hdensD : 2 * ((k:ℝ)) * β * (((k+1:ℕ):ℝ))^m ≤ (D.card : ℝ) := by
          have h1 : (2 * ((k:ℝ)) * β) * (((k+1:ℕ):ℝ))^m = γ^2/2 * (((k+1:ℕ):ℝ))^m := by
            rw [htwo]
          rw [h1]
          linarith [hDcard, hdensD_ge]
        obtain ⟨VS, hVS_sub, hVS_disj, hVS_cov⟩ := htil m hm_Ntil Ds hinsens D hDdef hdensD
        have hcov' : (D.card : ℝ) - γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤
            ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ) := by
          rw [← htwo]; exact hVS_cov
        obtain ⟨V, hVmem, hVcard⟩ :=
          dktFinalStep (k := k) (d := d) (m := m) (by omega) hγpos (by positivity)
            A D VS hDcard hDcorr hVS_sub hVS_disj hcov'
        refine ⟨scomp X V, ?_⟩
        rw [dkt_card_filter_scomp]
        have hVc := hVcard
        rw [dkt_inter_image_eq V A, Finset.card_image_of_injective _ (dkt_subspace_injective V)] at hVc
        rw [hAdef] at hVc
        exact hVc
      · -- Case (ii): a subspace with many internal lines
        set A : Finset (Fin m → Fin (k+1)) := dktPull W T with hAdef
        have hAno : ¬ ∃ l : Line (Fin (k+1)) (Fin m), ∀ v, l v ∈ A := by
          rw [hAdef]; exact dkt_not_line_pull W T hline
        have hA2 : (δ - 2*η) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) := hW1
        have hcase : (δ + η^2/2) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) ∨
            (θ/2) * ((((k+1:ℕ):ℝ)^m) - ((k:ℝ)^m)) ≤
              (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) := by
          refine Or.inr ?_
          have heq : (varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)
              = (varWord k m).filter (fun g => ∀ v : Fin k, W (linePt g v) ∈ T) := by
            rw [hAdef]
            apply Finset.filter_congr
            intro g _
            simp only [mem_dktPull]
          rw [heq]; exact hW2
        obtain ⟨D, ⟨Ds, hinsens, hDdef⟩, hDcard, hDcorr⟩ :=
          dkt_insens_correlation k hk2 δ θ η γ hδ hδ1 hθpos hθ1 hηdef hγdef m hm1
            hm_lam A hA2 hAno hcase
        have hdensD : 2 * ((k:ℝ)) * β * (((k+1:ℕ):ℝ))^m ≤ (D.card : ℝ) := by
          have h1 : (2 * ((k:ℝ)) * β) * (((k+1:ℕ):ℝ))^m = γ^2/2 * (((k+1:ℕ):ℝ))^m := by
            rw [htwo]
          rw [h1]
          linarith [hDcard, hdensD_ge]
        obtain ⟨VS, hVS_sub, hVS_disj, hVS_cov⟩ := htil m hm_Ntil Ds hinsens D hDdef hdensD
        have hcov' : (D.card : ℝ) - γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤
            ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ) := by
          rw [← htwo]; exact hVS_cov
        obtain ⟨V, hVmem, hVcard⟩ :=
          dktFinalStep (k := k) (d := d) (m := m) (by omega) hγpos (by positivity)
            A D VS hDcard hDcorr hVS_sub hVS_disj hcov'
        refine ⟨scomp W V, ?_⟩
        rw [dkt_card_filter_scomp]
        have hVc := hVcard
        rw [dkt_inter_image_eq V A, Finset.card_image_of_injective _ (dkt_subspace_injective V)] at hVc
        rw [hAdef] at hVc
        exact hVc

end

end Commons.Combinatorics.Ramsey
