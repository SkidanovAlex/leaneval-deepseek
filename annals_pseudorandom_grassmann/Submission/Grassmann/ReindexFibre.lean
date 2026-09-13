import Submission.Grassmann.SwRoleUnfold

/-!
# P4: the reindexing of the switching sum by `Φ₃`

This file completes the reindexing step of §8: the switching sum `Σ_t [S≠0] 2^{26dS} L_{XtPred t}`
is bounded by `2^{C d² + 2} Σ_{(V₀,W)} D4 V₀ W (Lsub V₀ W f)`.

The chain is

* `sum_l4q_le_reindexSummand` — the per-`t` bound `l4q_lapMulN_le_swRole_rank` + the unfolding
  `inv_mul_swRoleSum` identify the sum with `q^{-mn} Σ_x reindexSummand d C f x`;
* `fiber_sum_le` — on a fibre of `Φ₃` over `⟨V₀,W,Z⟩` the summand is
  `2^{-4 d·rank Z}·fiberWeight·G V₀ W Z f`, and `fiber_weight_le_sharp` bounds the weighted fibre;
* `sum_all_rank_G_le` — the `Z`-sum of `2^{-16 d·rank Z}G` is at most `2·2^{mn}·D4`, by the
  removal of the extra `D_X`-derivatives (`sum_rank_G_le`).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## A power-of-two arithmetic helper -/

/-- `2^A·(2^B·(2^E·g)) = (2^E₂)⁻¹·2^(A+B+E+E₂)·g`. -/
lemma pow_inv_helper (A B E E2 : ℕ) (g : ℝ) :
    (2 : ℝ) ^ A * ((2 : ℝ) ^ B * ((2 : ℝ) ^ E * g))
      = ((2 : ℝ) ^ E2)⁻¹ * ((2 : ℝ) ^ (A + B + E + E2) * g) := by
  rw [show (2 : ℝ) ^ (A + B + E + E2)
      = (2 : ℝ) ^ A * ((2 : ℝ) ^ B * ((2 : ℝ) ^ E * (2 : ℝ) ^ E2)) by
    rw [show A + B + E + E2 = A + (B + (E + E2)) by ring, pow_add, pow_add, pow_add]]
  have h : (2 : ℝ) ^ E2 ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- `(2^E₁)⁻¹·((2^E₂)⁻¹·g) = (2^(E₁+E₂))⁻¹·g`. -/
lemma inv_pow_mul_inv_pow (E1 E2 : ℕ) (g : ℝ) :
    ((2 : ℝ) ^ E1)⁻¹ * (((2 : ℝ) ^ E2)⁻¹ * g) = ((2 : ℝ) ^ (E1 + E2))⁻¹ * g := by
  rw [pow_add, mul_inv, ← mul_assoc]

/-! ## Positivity of `G` -/

lemma G_nonneg (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : 0 ≤ G V₀ W Z f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma reindexSummand_nonneg (d C : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (x : Σ t : Triple m n, QPair m n t) : 0 ≤ reindexSummand d C f x := by
  rw [reindexSummand]
  split
  · exact mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (G_nonneg _ _ _ f)))
  · exact le_refl 0

/-! ## The `Z`-sum of `2^{-λ d·rank Z} G` -/

lemma sum_subtype_eq_sum_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (f : α → M) :
    (∑ a : {a // p a}, f a) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_subtype (s := Finset.univ.filter p) (fun a => by simp)]

set_option maxHeartbeats 2000000 in
/-- **The `Z`-sum of `2^{-λ d·rank Z} G`**: summing over all role-space matrices `Z` (of every
rank) the weight `2^{-λ d·rank Z}` against `G V₀ W Z f` costs at most `2·2^{mn}·D4`. -/
theorem sum_all_rank_G_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) {d lam : ℕ} (hd : 1 ≤ d) (hlam : 8 ≤ lam)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂,
        ((2 : ℝ) ^ (lam * d * Z.rank))⁻¹ * G V₀ W Z f)
      ≤ 2 * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)) := by
  classical
  set N : ℕ := Module.finrank 𝔽₂ W with hN
  set D0 : ℝ := (2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f) with hD0def
  have hD0 : (0 : ℝ) ≤ D0 := by rw [hD0def]; exact mul_nonneg (by positivity) (D4_nonneg _ _ _)
  have hrank : ∀ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂,
      Z.rank ∈ Finset.range (N + 1) := by
    intro Z
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (by simpa using Matrix.rank_le_width Z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (N + 1))
    (g := fun Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂ => Z.rank)
    (fun Z _ => hrank Z)]
  have hinner : ∀ k : ℕ,
      (∑ Z ∈ Finset.univ.filter (fun Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂ =>
          Z.rank = k), ((2 : ℝ) ^ (lam * d * Z.rank))⁻¹ * G V₀ W Z f)
        = ((2 : ℝ) ^ (lam * d * k))⁻¹ *
            (∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂ // Z.rank = k},
              G V₀ W Z.1 f) := by
    intro k
    rw [Finset.sum_filter, ← sum_subtype_eq_sum_ite
      (p := fun Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂ => Z.rank = k)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    rw [Z.2]
  have hper : ∀ k ∈ Finset.range (N + 1),
      (∑ Z ∈ Finset.univ.filter (fun Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin N) 𝔽₂ =>
          Z.rank = k), ((2 : ℝ) ^ (lam * d * Z.rank))⁻¹ * G V₀ W Z f)
        ≤ ((2 : ℝ) ^ (lam * d * k))⁻¹ * ((2 : ℝ) ^ (7 * d * k) * D0) := by
    intro k _
    rw [hinner k, hD0def]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sum_rank_G_le V₀ W hf k
  refine (Finset.sum_le_sum hper).trans ?_
  have hpow : ∀ k : ℕ, ((2 : ℝ) ^ (lam * d * k))⁻¹ * ((2 : ℝ) ^ (7 * d * k))
      = (((2 : ℝ) ^ ((lam - 7) * d))⁻¹) ^ k := by
    intro k
    have hexp : lam * d * k = 7 * d * k + (lam - 7) * d * k := by
      have h1 : lam - 7 + 7 = lam := Nat.sub_add_cancel (by omega)
      have h2 : lam * d * k = ((lam - 7) + 7) * d * k := by rw [h1]
      rw [h2, Nat.add_mul, Nat.add_mul]; ring
    have hA : ((2 : ℝ) ^ (lam * d * k))⁻¹ * ((2 : ℝ) ^ (7 * d * k))
        = ((2 : ℝ) ^ ((lam - 7) * d * k))⁻¹ := by
      rw [hexp, pow_add, mul_inv]
      field_simp
    rw [hA, inv_pow, ← pow_mul]
  have hgeom : (∑ k ∈ Finset.range (N + 1),
      (((2 : ℝ) ^ ((lam - 7) * d))⁻¹) ^ k) ≤ 2 := by
    have hkey : 1 ≤ (lam - 7) * d := by
      have h1 : 1 ≤ lam - 7 := by omega
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h2 : (2 : ℝ) ≤ 2 ^ ((lam - 7) * d) :=
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ((lam - 7) * d) := pow_le_pow_right₀ (by norm_num) hkey
    have hr : ((2 : ℝ) ^ ((lam - 7) * d))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)]
      simpa using h2
    exact geom_sum_le_two (by positivity) hr (N + 1)
  have hstep : (∑ k ∈ Finset.range (N + 1),
        ((2 : ℝ) ^ (lam * d * k))⁻¹ * ((2 : ℝ) ^ (7 * d * k) * D0))
      = (∑ k ∈ Finset.range (N + 1), (((2 : ℝ) ^ ((lam - 7) * d))⁻¹) ^ k) * D0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mul_assoc, hpow k]
  rw [hstep]
  exact mul_le_mul_of_nonneg_right hgeom hD0

/-! ## A rearrangement helper -/

lemma mul_inv_rearrange (a b P g : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ * (g * (P * b⁻¹)) = P * (a * b)⁻¹ * g := by
  rw [mul_inv]
  field_simp

/-! ## The fibre of `Φ₃` over `⟨V₀,W,Z⟩` -/

/-- On the fibre of `Φ₃`, `G` is constant. -/
lemma G_const_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    G (liftV x.1.1 x.2.1) (liftW x.1.2.1 x.2.2) (XsOf x.1 x.2) f = G V₀ W Z f := by
  cases hx
  rfl

set_option maxHeartbeats 4000000 in
/-- **The fibre sum over `Φ₃`**: on the fibre over `⟨V₀,W,Z⟩` the reindexed summand is
`2^{-4 d·rank Z}·fiberWeight·G`, and the strengthened weighted fibre bound
`fiber_weight_le_sharp2` gives `2^{C d²}·2^{-16 d·rank Z - 12 d}·G V₀ W Z f`. -/
theorem fiber_sum_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) (hC : 61 ≤ C) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩},
        reindexSummand d C f x.1)
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (16 * d * Z.rank + 12 * d))⁻¹ * G V₀ W Z f := by
  classical
  have hFibre : (∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩},
        reindexSummand d C f x.1)
      = ∑ x : FFib m n V₀ W Z d, reindexSummand d C f x.1 := by
    rw [sum_subtype_eq_sum_ite (p := fun x : Σ t : Triple m n, QPair m n t =>
          Phi3 x = ⟨V₀, W, Z⟩) (f := fun x => reindexSummand d C f x),
      sum_subtype_eq_sum_ite (p := fun x : Σ t : Triple m n, QPair m n t =>
          Phi3 x = ⟨V₀, W, Z⟩ ∧ ReindexGood d x ∧ 1 ≤ totOrder x.1 ∧ totOrder x.1 ≤ d)
        (f := fun x => reindexSummand d C f x)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : Phi3 x = ⟨V₀, W, Z⟩
    · rw [if_pos hx]
      by_cases hg : ReindexGood d x ∧ 1 ≤ totOrder x.1 ∧ totOrder x.1 ≤ d
      · rw [if_pos ⟨hx, hg⟩]
      · rw [if_neg (fun h => hg h.2), reindexSummand, if_neg hg]
    · rw [if_neg hx, if_neg (fun h => hx h.1)]
  have hpoint : ∀ x : FFib m n V₀ W Z d,
      reindexSummand d C f x.1
        = ((2 : ℝ) ^ (4 * d * Z.rank))⁻¹ * (fiberWeight d C x.1 * G V₀ W Z f) := by
    intro x
    obtain ⟨y, hy1, hy2, hy3, hy4⟩ := x
    show reindexSummand d C f y
      = ((2 : ℝ) ^ (4 * d * Z.rank))⁻¹ * (fiberWeight d C y * G V₀ W Z f)
    have hS := totOrder_of_fiber (V₀ := V₀) (W := W) (Z := Z) hy1 hy2 rfl rfl
    have hrk := rank_XsOf_of_fiber (V₀ := V₀) (W := W) (Z := Z) hy1
    have hfr := finrank_range_of_fiber (V₀ := V₀) (W := W) (Z := Z) (d := d) hy1 hy2 rfl rfl
    have hG := G_const_of_fiber (V₀ := V₀) (W := W) (Z := Z) hy1 f
    rw [reindexSummand, if_pos ⟨hy2, hy3, hy4⟩, hG]
    unfold fiberWeight
    rw [hS, hfr, hrk]
    exact pow_inv_helper (26 * d * (Module.finrank 𝔽₂ y.1.1 + (m - Module.finrank 𝔽₂ y.1.2.1) + Z.rank))
      (C * (d - (Module.finrank 𝔽₂ y.1.1 + (m - Module.finrank 𝔽₂ y.1.2.1) + Z.rank)) ^ 2)
      (3 * d * Z.rank) (4 * d * Z.rank) (G V₀ W Z f)
  rw [hFibre]
  have hsum : (∑ x : FFib m n V₀ W Z d, reindexSummand d C f x.1)
      = ((2 : ℝ) ^ (4 * d * Z.rank))⁻¹ *
          (G V₀ W Z f * ∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1) := by
    rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [hsum]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (fiber_weight_le_sharp2 V₀ W Z d C hC) (G_nonneg _ _ _ f)) (by positivity)).trans (le_of_eq ?_)
  have hgoal : (2:ℝ)^(16 * d * Z.rank + 12 * d)
      = (2:ℝ)^(4 * d * Z.rank) * (2:ℝ)^(12 * d * Z.rank + 12 * d) := by
    rw [← pow_add]; congr 1; ring
  rw [hgoal]
  exact mul_inv_rearrange ((2:ℝ)^(4*d*Z.rank)) ((2:ℝ)^(12*d*Z.rank+12*d)) ((2:ℝ)^(C*d^2))
    (G V₀ W Z f) (by positivity) (by positivity)

/-! ## The `Z`-sum of the fibre sums -/

set_option maxHeartbeats 4000000 in
/-- **The `Z`-sum of the fibre sums** over a fixed pair `(V₀,W)`. -/
theorem sum_Z_fiber_sum_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) (d C : ℕ) (hd : 1 ≤ d) (hC : 61 ≤ C)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂,
        ∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩},
          reindexSummand d C f x.1)
      ≤ (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
          D4 V₀ W (Lsub V₀ W f)) := by
  have hper : ∀ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂,
      (∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩},
          reindexSummand d C f x.1)
        ≤ (2 : ℝ) ^ (C * d ^ 2) * (((2 : ℝ) ^ (16 * d * Z.rank + 12 * d))⁻¹ * G V₀ W Z f) := by
    intro Z
    exact (fiber_sum_le V₀ W Z d C hC f).trans (le_of_eq (by ring))
  have hfac : (∑ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂,
        ((2 : ℝ) ^ (16 * d * Z.rank + 12 * d))⁻¹ * G V₀ W Z f)
      = ((2 : ℝ) ^ (12 * d))⁻¹ *
          ∑ Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂,
            ((2 : ℝ) ^ (16 * d * Z.rank))⁻¹ * G V₀ W Z f := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    rw [pow_add, mul_inv]
    ring
  calc (∑ Z, ∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩},
          reindexSummand d C f x.1)
      ≤ ∑ Z, (2 : ℝ) ^ (C * d ^ 2) * (((2 : ℝ) ^ (16 * d * Z.rank + 12 * d))⁻¹ * G V₀ W Z f) :=
        Finset.sum_le_sum (fun Z _ => hper Z)
    _ = (2 : ℝ) ^ (C * d ^ 2) *
          ∑ Z, (((2 : ℝ) ^ (16 * d * Z.rank + 12 * d))⁻¹ * G V₀ W Z f) := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ (C * d ^ 2) *
          (((2 : ℝ) ^ (12 * d))⁻¹ *
            ∑ Z, (((2 : ℝ) ^ (16 * d * Z.rank))⁻¹ * G V₀ W Z f)) := by rw [hfac]
    _ ≤ (2 : ℝ) ^ (C * d ^ 2) *
          (((2 : ℝ) ^ (12 * d))⁻¹ * (2 * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (sum_all_rank_G_le V₀ W hd (by norm_num : 8 ≤ 16) hf) (by positivity))
          (by positivity)
    _ = (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
          D4 V₀ W (Lsub V₀ W f)) := by ring

/-! ## The reindexed sum -/

/-- `∑_{P a} c·g a = c·∑_{P a} g a` (the `if`-guarded sum). -/
lemma sum_ite_const_mul_reindex {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (c : ℝ) (g : α → ℝ) :
    (∑ a, if P a then c * g a else 0) = c * ∑ a, if P a then g a else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : P a
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

set_option maxHeartbeats 8000000 in
/-- **The reindexed summand summed over the pairs `p` of a triple.** -/
theorem sum_reindexSummand_eq (t : Triple m n) (d C : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ht1 : 1 ≤ totOrder t) (htd : totOrder t ≤ d) :
    (∑ p : QPair m n t, reindexSummand d C f ⟨t, p⟩)
      = (2 : ℝ) ^ (26 * d * totOrder t) * ((2 : ℝ) ^ (C * (d - totOrder t) ^ (2 : ℕ)) *
          ∑ p : QPair m n t,
            (if ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t) then
              (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
                G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f else 0)) := by
  have hre : ∀ p : QPair m n t, reindexSummand d C f ⟨t, p⟩
      = (if ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t) then
          (2 : ℝ) ^ (26 * d * totOrder t) * ((2 : ℝ) ^ (C * (d - totOrder t) ^ (2 : ℕ)) *
            ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
              G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f)) else 0) := by
    intro p
    unfold reindexSummand
    by_cases h : ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t)
    · rw [if_pos ⟨h, ht1, htd⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.1), if_neg h]
  rw [Finset.sum_congr rfl (fun p _ => hre p)]
  rw [sum_ite_const_mul_reindex (fun p : QPair m n t =>
        ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t))
        ((2 : ℝ) ^ (26 * d * totOrder t))
        (fun p => (2 : ℝ) ^ (C * (d - totOrder t) ^ (2 : ℕ)) *
          ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
            G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f)),
    sum_ite_const_mul_reindex (fun p : QPair m n t =>
        ReindexGood d (⟨t, p⟩ : Σ t : Triple m n, QPair m n t))
        ((2 : ℝ) ^ (C * (d - totOrder t) ^ (2 : ℕ)))
        (fun p => (2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
          G (liftV t.1 p.1) (liftW t.2.1 p.2) (XsOf t p) f)]

set_option maxHeartbeats 8000000 in
/-- **The per-`t` bound of the reindexing.** -/
theorem sum_l4q_le_reindexSummand (d C : ℕ) (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ t : Triple m n, (if totOrder t = 0 then 0 else (2 : ℝ) ^ (26 * d * totOrder t) *
        l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))))
      ≤ ((2 : ℝ) ^ (m * n))⁻¹ * ∑ x : Σ t : Triple m n, QPair m n t,
          reindexSummand d C f x := by
  rw [Fintype.sum_sigma (f := reindexSummand d C f)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun t _ => ?_)
  by_cases ht0 : totOrder t = 0
  · rw [if_pos ht0]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun p _ => reindexSummand_nonneg d C f ⟨t, p⟩))
  · rw [if_neg ht0]
    by_cases htd : totOrder t ≤ d
    · have ht1 : 1 ≤ totOrder t := Nat.one_le_iff_ne_zero.mpr ht0
      have hmain := l4q_lapMulN_le_swRole_rank (m := m) (n := n) t hIH hf ht1 htd
      rw [inv_mul_swRoleSum t f d] at hmain
      rw [sum_reindexSummand_eq t d C f ht1 htd]
      refine (mul_le_mul_of_nonneg_left hmain (by positivity)).trans (le_of_eq ?_)
      ring
    · rw [l4q_lapMulN_XtPred_eq_zero_of_gt t hf (by omega), mul_zero]
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun p _ => reindexSummand_nonneg d C f ⟨t, p⟩))

/-! ## The final assembly of P4 -/

set_option maxHeartbeats 8000000 in
/-- **The reindexed sum, summed over all `(V₀,W,Z)`.** -/
theorem sum_reindexSummand_le (d C : ℕ) (hd : 1 ≤ d) (hC : 61 ≤ C)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ x : Σ t : Triple m n, QPair m n t, reindexSummand d C f x)
      ≤ (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
          ∑ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W : Submodule 𝔽₂ (Fin m → 𝔽₂),
            D4 V₀ W (Lsub V₀ W f)) := by
  classical
  have key1 : ∀ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂),
      (∑ W : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
            D4 V₀ W (Lsub V₀ W f)))
        = (2 : ℝ) ^ (m * n) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
            ∑ W : Submodule 𝔽₂ (Fin m → 𝔽₂), D4 V₀ W (Lsub V₀ W f)) := by
    intro V₀
    simp only [Finset.mul_sum]
  have hsplit : ∀ (F : (Σ (V : Submodule 𝔽₂ (Fin n → 𝔽₂))
        (W : Submodule 𝔽₂ (Fin m → 𝔽₂)),
        Matrix (Fin (n - Module.finrank 𝔽₂ V)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂) → ℝ),
      (∑ p, F p) = ∑ V₀, ∑ W, ∑ Z, F ⟨V₀, W, Z⟩ := by
    intro F
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun V₀ _ => ?_)
    rw [Fintype.sum_sigma]
  rw [← Fintype.sum_fiberwise (Phi3) (reindexSummand d C f)]
  rw [hsplit (fun p => ∑ x : {x : Σ t : Triple m n, QPair m n t // Phi3 x = p},
      reindexSummand d C f x.1)]
  refine (Finset.sum_le_sum (fun V₀ _ => Finset.sum_le_sum (fun W _ =>
    sum_Z_fiber_sum_le V₀ W d C hd hC hf))).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun V₀ _ => key1 V₀)]
  simp only [Finset.mul_sum]

set_option maxHeartbeats 8000000 in
/-- **P4**: the switching sum is bounded by `2^{C d² - 12 d + 1}` times the `D4`-sum.

The `2^{-12 d}` shave (which is `q^{-31 d}` in the paper, independent of the summation index)
is what lets the induction absorb the constant `162` of `after_restricting'` while keeping the
constant `C` fixed. -/
theorem sum_l4q_XtPred_le (d C : ℕ) (hC : 61 ≤ C) (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ t : Triple m n, (if totOrder t = 0 then 0 else (2 : ℝ) ^ (26 * d * totOrder t) *
        l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))))
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 *
          ∑ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂),
          ∑ W : Submodule 𝔽₂ (Fin m → 𝔽₂), D4 V₀ W (Lsub V₀ W f) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hzero : ∀ t : Triple m n, (if totOrder t = 0 then (0 : ℝ) else
        (2 : ℝ) ^ (26 * 0 * totOrder t) *
          l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))) = 0 := by
      intro t
      by_cases ht : totOrder t = 0
      · rw [if_pos ht]
      · rw [if_neg ht, l4q_lapMulN_XtPred_eq_zero_of_gt t hf (by omega), mul_zero]
    rw [Finset.sum_congr rfl (fun t _ => hzero t)]
    simp only [Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by norm_num))
      (Finset.sum_nonneg (fun V₀ _ => Finset.sum_nonneg (fun W _ => D4_nonneg _ _ _)))
  · have h1 := sum_l4q_le_reindexSummand (m := m) (n := n) d C hIH hf
    have h2 := sum_reindexSummand_le (m := m) (n := n) d C hd hC hf
    refine h1.trans ?_
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_)
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

end
end Submission.Grassmann
