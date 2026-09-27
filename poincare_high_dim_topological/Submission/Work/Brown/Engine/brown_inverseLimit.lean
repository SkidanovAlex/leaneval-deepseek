import Mathlib
import Submission.Work.Brown.Basic

/-!
# Morton Brown's theorem: the inverse limit of near homeomorphisms

M. Brown, *Some applications of an approximation theorem for inverse limits*,
Proc. Amer. Math. Soc. **11** (1960), 478–483:

> If `S` is the inverse limit of a sequence of copies of a compact metric space `X`
> and the bonding maps are near homeomorphisms, then `S` is homeomorphic to `X`.

This file proves the general statement

`Work.Brown.Engine.brown_inverseLimit`

that the inverse limit `{x : ℕ → X // ∀ k, f k (x (k+1)) = x k}` of a sequence of
near homeomorphisms `f k` of a compact metric space `X` is homeomorphic to `X`.

The proof follows Brown.  Choose homeomorphisms `g k` approximating `f k` very closely, and
consider

`F n s = lim_m (g n ∘ g (n+1) ∘ … ∘ g (m-1)) (s m)`   (`s` in the inverse limit).

The sequence whose limit defines `F n s` is Cauchy with a bound that is uniform in `s`; the
bound also shows `F n s` is close to `s n`, and a "Lebesgue" modulus argument for the system
`(f k)` shows distinct points of the inverse limit are separated in some coordinate, which
gives injectivity.  Surjectivity of `F 0` follows because it is a uniform limit of the
surjective maps `s ↦ (g 0 ∘ … ∘ g (m-1)) (s m)`.  Finally `F 0` is close to the projection,
so we obtain a homeomorphism.
-/

namespace Work.Brown.Engine

open Set Metric Function Filter Topology
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The limit space (inverse limit) of the system `f`. -/
abbrev IL (f : ℕ → X → X) : Type _ := { x : ℕ → X // ∀ k, f k (x (k + 1)) = x k }

/-! ## Iterated compositions -/

/-- `Gf f j d` is the composition `f j ∘ f (j+1) ∘ ⋯ ∘ f (j+d-1)` (`id` for `d = 0`): the
bonding map from level `j + d` down to level `j`. -/
def Gf (f : ℕ → X → X) (j : ℕ) : ℕ → X → X
  | 0 => id
  | (d + 1) => f j ∘ Gf f (j + 1) d

@[simp] lemma Gf_zero (f : ℕ → X → X) (j : ℕ) : Gf f j 0 = id := rfl

lemma Gf_succ (f : ℕ → X → X) (j d : ℕ) : Gf f j (d + 1) = f j ∘ Gf f (j + 1) d := rfl

lemma Gf_succ_apply (f : ℕ → X → X) (j d : ℕ) (x : X) :
    Gf f j (d + 1) x = f j (Gf f (j + 1) d x) := rfl

/-- `Gf f j d ∘ f (j+d) = Gf f j (d+1)`: composing one more bonding map on the right. -/
lemma Gf_mul_succ (f : ℕ → X → X) (d : ℕ) (j : ℕ) :
    Gf f j d ∘ f (j + d) = Gf f j (d + 1) := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih =>
    have h : j + (d + 1) = (j + 1) + d := by omega
    rw [h, Gf_succ f j (d + 1), Gf_succ f j d, ← ih (j + 1), Function.comp_assoc]

/-- The fundamental relation of the inverse limit: `Gf f j d (s (j+d)) = s j`. -/
lemma Gf_mem (f : ℕ → X → X) (s : IL f) (d : ℕ) :
    ∀ j, Gf f j d (s.1 (j + d)) = s.1 j := by
  induction d with
  | zero => intro j; simp
  | succ d ih =>
    intro j
    rw [Gf_succ_apply]
    have h : j + (d + 1) = (j + 1) + d := by omega
    rw [h, ih (j + 1), s.2 j]

/-! ## Moduli of uniform continuity -/

/-- Heine–Cantor: a continuous self-map of a compact metric space admits a positive modulus of
uniform continuity for every positive tolerance. -/
lemma exists_modulus_pos (φ : X → X) (hφ : Continuous φ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X, dist x y < δ → dist (φ x) (φ y) < η := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_univ.uniformContinuousOn_of_continuous hφ.continuousOn) η hη
  exact ⟨δ, hδ, fun x y hxy => h x trivial y trivial hxy⟩

/-- A chosen modulus of uniform continuity for `f j` at tolerance `η` (junk value `1` when
`η ≤ 0`). -/
noncomputable def fmod (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (j : ℕ) (η : ℝ) : ℝ :=
  if h : 0 < η then Classical.choose (exists_modulus_pos (f j) (hc j) h) else 1

lemma fmod_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (j : ℕ) {η : ℝ} (hη : 0 < η) :
    0 < fmod f hc j η := by
  rw [fmod, dif_pos hη]
  exact (Classical.choose_spec (exists_modulus_pos (f j) (hc j) hη)).1

lemma fmod_spec (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (j : ℕ) {η : ℝ} (hη : 0 < η)
    (x y : X) (hxy : dist x y < fmod f hc j η) : dist (f j x) (f j y) < η := by
  rw [fmod, dif_pos hη] at hxy
  exact (Classical.choose_spec (exists_modulus_pos (f j) (hc j) hη)).2 x y hxy

/-! ## The Lebesgue modulus -/

/-- `Tmod μ ξ k` is a common modulus of uniform continuity, at tolerance `ξ`, for all the
bonding maps `Gf f j (k-j)` with `j < k`.  It is defined recursively: the level `k+1` family
is `{f k} ∪ {Gf f j (k-j) ∘ f k : j < k}`, so one takes the minimum of `μ k ξ` (for `f k`)
and `μ k (Tmod μ ξ k)` (for the composites). -/
noncomputable def Tmod (μ : ℕ → ℝ → ℝ) (ξ : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => min (μ k ξ) (μ k (Tmod μ ξ k))

lemma Tmod_zero (μ : ℕ → ℝ → ℝ) (ξ : ℝ) : Tmod μ ξ 0 = 1 := rfl

lemma Tmod_succ (μ : ℕ → ℝ → ℝ) (ξ : ℝ) (k : ℕ) :
    Tmod μ ξ (k + 1) = min (μ k ξ) (μ k (Tmod μ ξ k)) := rfl

lemma Tmod_pos (μ : ℕ → ℝ → ℝ) (hμ : ∀ j η, 0 < η → 0 < μ j η) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ k, 0 < Tmod μ ξ k := by
  intro k
  induction k with
  | zero => rw [Tmod_zero]; exact one_pos
  | succ k ih => rw [Tmod_succ]; exact lt_min (hμ k ξ hξ) (hμ k _ ih)

/-- The defining property of `Tmod`. -/
lemma Tmod_spec {f : ℕ → X → X} (μ : ℕ → ℝ → ℝ)
    (hμ : ∀ j η, 0 < η → ∀ x y : X, dist x y < μ j η → dist (f j x) (f j y) < η)
    (hμpos : ∀ j η, 0 < η → 0 < μ j η) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ k (j : ℕ), j < k → ∀ x y : X,
      dist x y < Tmod μ ξ k → dist (Gf f j (k - j) x) (Gf f j (k - j) y) < ξ := by
  intro k
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro j hj x y hxy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
    · have hTk : 0 < Tmod μ ξ k := Tmod_pos μ hμpos ξ hξ k
      have hle : dist x y < μ k (Tmod μ ξ k) := lt_of_lt_of_le hxy (min_le_right _ _)
      have hf : dist (f k x) (f k y) < Tmod μ ξ k := hμ k _ hTk x y hle
      have hinterp := ih j hjk (f k x) (f k y) hf
      have h1 : k + 1 - j = (k - j) + 1 := by omega
      have h2 : j + (k - j) = k := by omega
      rw [h1, ← Gf_mul_succ f (k - j) j, h2]
      simpa only [Function.comp_apply] using hinterp
    · rw [hjk]
      have hle : dist x y < μ k ξ := lt_of_lt_of_le hxy (min_le_left _ _)
      have h1 : k + 1 - k = 1 := by omega
      rw [h1]
      simpa only [Gf_succ, Gf_zero, Function.comp_apply, id_eq] using hμ k ξ hξ x y hle

/-! ## The sequences `b, a, c, a', ε` -/

/-- The tolerances of the Lebesgue sequence. -/
noncomputable def bb (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)

/-- The Lebesgue modulus at level `k`: a common modulus of uniform continuity for the maps
`Gf f j (k-j)`, `j < k`, at tolerance `bb k`. -/
noncomputable def aa (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : ℝ :=
  Tmod (fmod f hc) (bb k) k

/-- Brown's "measure" sequence: positive, fast decreasing, and dominated by `aa`. -/
noncomputable def cc (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) : ℕ → ℝ :=
  fun k => Nat.rec (min (aa f hc 0) 1 / 4)
    (fun k ih => min (aa f hc (k + 1)) (ih / 4) / 4) k

/-- The level-`k` modulus at tolerance `cc k`. -/
noncomputable def a2 (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : ℝ :=
  Tmod (fmod f hc) (cc f hc k) k

/-- The accuracy with which `g k` approximates `f k`. -/
noncomputable def eps (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : ℝ :=
  min (cc f hc k / 4) (a2 f hc k / 2)

lemma bb_pos (k : ℕ) : 0 < bb k := by
  unfold bb; positivity

lemma bb_tendsto : Tendsto bb atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ))
    (by norm_num) (by norm_num)
  have h2 : Tendsto (fun k : ℕ => k + 1) atTop atTop := tendsto_add_atTop_nat 1
  have h3 : Tendsto (fun k : ℕ => (1/2:ℝ)^(k+1)) atTop (nhds 0) := h.comp h2
  unfold bb
  exact h3

lemma aa_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : 0 < aa f hc k :=
  Tmod_pos (fmod f hc) (fun _ _ h => fmod_pos f hc _ h) (bb k) (bb_pos k) k

lemma cc_zero (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) :
    cc f hc 0 = min (aa f hc 0) 1 / 4 := rfl

lemma cc_succ (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) :
    cc f hc (k + 1) = min (aa f hc (k + 1)) (cc f hc k / 4) / 4 := rfl

lemma cc_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) : ∀ k, 0 < cc f hc k := by
  intro k
  induction k with
  | zero => rw [cc_zero]; exact div_pos (lt_min (aa_pos f hc 0) one_pos) (by norm_num)
  | succ k ih =>
    rw [cc_succ]
    exact div_pos (lt_min (aa_pos f hc (k+1)) (div_pos ih (by norm_num))) (by norm_num)

lemma cc_lt_aa (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : cc f hc k < aa f hc k := by
  cases k with
  | zero =>
    rw [cc_zero]
    have := aa_pos f hc 0
    have h2 : min (aa f hc 0) 1 ≤ aa f hc 0 := min_le_left _ _
    linarith
  | succ k =>
    rw [cc_succ]
    have := aa_pos f hc (k+1)
    have h2 : min (aa f hc (k + 1)) (cc f hc k / 4) ≤ aa f hc (k + 1) := min_le_left _ _
    linarith

lemma cc_succ_le (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) :
    cc f hc (k + 1) ≤ cc f hc k / 16 := by
  rw [cc_succ]
  have h2 : min (aa f hc (k + 1)) (cc f hc k / 4) ≤ cc f hc k / 4 := min_le_right _ _
  linarith

lemma cc_geom (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) :
    ∀ i, cc f hc (k + i) ≤ cc f hc k * (1/16 : ℝ)^i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : k + (i + 1) = (k + i) + 1 := by omega
    rw [h1]
    have h2 := cc_succ_le f hc (k + i)
    calc cc f hc ((k + i) + 1) ≤ cc f hc (k + i) / 16 := h2
      _ ≤ (cc f hc k * (1/16:ℝ)^i) / 16 := by linarith [ih]
      _ = cc f hc k * (1/16:ℝ)^(i+1) := by ring

lemma cc_tendsto (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) :
    Tendsto (cc f hc) atTop (nhds 0) := by
  have hb : Tendsto (fun k => (1/16:ℝ)^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb2 : Tendsto (fun k => cc f hc 0 * (1/16:ℝ)^k) atTop (nhds 0) := by
    simpa using hb.const_mul (cc f hc 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb2 ?_ ?_
  · intro k; exact le_of_lt (cc_pos f hc k)
  · intro k
    have := cc_geom f hc 0 k
    simpa using this

lemma a2_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : 0 < a2 f hc k :=
  Tmod_pos (fmod f hc) (fun _ _ h => fmod_pos f hc _ h) (cc f hc k) (cc_pos f hc k) k

lemma eps_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) : 0 < eps f hc k := by
  unfold eps
  exact lt_min (div_pos (cc_pos f hc k) (by norm_num))
    (div_pos (a2_pos f hc k) (by norm_num))

lemma eps_le_cc (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) :
    eps f hc k ≤ cc f hc k / 4 := by
  unfold eps; exact min_le_left _ _

lemma eps_le_a2 (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) :
    eps f hc k ≤ a2 f hc k / 2 := by
  unfold eps; exact min_le_right _ _

lemma aa_spec (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) {j : ℕ} (hj : j < k)
    {x y : X} (h : dist x y < aa f hc k) :
    dist (Gf f j (k - j) x) (Gf f j (k - j) y) < bb k :=
  Tmod_spec (fmod f hc) (fun j η hη x y hxy => fmod_spec f hc j hη x y hxy)
    (fun j η hη => fmod_pos f hc j hη) (bb k) (bb_pos k) k j hj x y h

lemma a2_spec (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (k : ℕ) {j : ℕ} (hj : j < k)
    {x y : X} (h : dist x y < a2 f hc k) :
    dist (Gf f j (k - j) x) (Gf f j (k - j) y) < cc f hc k :=
  Tmod_spec (fmod f hc) (fun j η hη x y hxy => fmod_spec f hc j hη x y hxy)
    (fun j η hη => fmod_pos f hc j hη) (cc f hc k) (cc_pos f hc k) k j hj x y h

/-! ## The chosen approximating homeomorphisms -/

/-- A sequence of near homeomorphisms. -/
def IsNearSeq (f : ℕ → X → X) : Prop := ∀ k, Work.Brown.IsNearHomeo (f k)

/-- The composition system of a sequence of homeomorphisms, as plain functions. -/
abbrev gfun (g : ℕ → X ≃ₜ X) : ℕ → X → X := fun k => (g k : X → X)

/-- A chosen modulus of uniform continuity for a homeomorphism, at tolerance `η`. -/
noncomputable def hmod (h : X ≃ₜ X) (η : ℝ) : ℝ :=
  if hη : 0 < η then Classical.choose (exists_modulus_pos h h.continuous hη) else 1

lemma hmod_pos (h : X ≃ₜ X) {η : ℝ} (hη : 0 < η) : 0 < hmod h η := by
  rw [hmod, dif_pos hη]
  exact (Classical.choose_spec (exists_modulus_pos h h.continuous hη)).1

lemma hmod_spec (h : X ≃ₜ X) {η : ℝ} (hη : 0 < η) {x y : X} (hxy : dist x y < hmod h η) :
    dist (h x) (h y) < η := by
  rw [hmod, dif_pos hη] at hxy
  exact (Classical.choose_spec (exists_modulus_pos h h.continuous hη)).2 x y hxy

/-- The modulus function of the system of homeomorphisms `g`. -/
noncomputable def ghmod (g : ℕ → X ≃ₜ X) : ℕ → ℝ → ℝ := fun j η => hmod (g j) η

lemma ghmod_pos (g : ℕ → X ≃ₜ X) : ∀ j η, 0 < η → 0 < ghmod g j η :=
  fun j η hη => hmod_pos (g j) hη

lemma ghmod_spec (g : ℕ → X ≃ₜ X) :
    ∀ j η, 0 < η → ∀ x y, dist x y < ghmod g j η → dist (g j x) (g j y) < η :=
  fun j η hη x y hxy => hmod_spec (g j) hη hxy

/-- `Tmod` only depends on the first `r` moduli. -/
lemma Tmod_congr (μ μ' : ℕ → ℝ → ℝ) (ξ : ℝ) :
    ∀ r, (∀ k < r, μ k = μ' k) → Tmod μ ξ r = Tmod μ' ξ r := by
  intro r
  induction r with
  | zero => intro _; rw [Tmod_zero, Tmod_zero]
  | succ r ih =>
    intro h
    rw [Tmod_succ, Tmod_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h r (Nat.lt_succ_self r)]

/-- The accuracy with which the `r`-th homeomorphism is chosen: it must be within `eps` of
`f r` and small enough that the level-`r` Lebesgue modulus of the system `g` is at least it. -/
noncomputable def ThC (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (g : ℕ → X ≃ₜ X)
    (r : ℕ) : ℝ :=
  min (eps f hc r) (Tmod (ghmod g) (bb r) r) / 2

lemma ThC_pos (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (g : ℕ → X ≃ₜ X) (r : ℕ) :
    0 < ThC f hc g r := by
  rw [ThC]
  exact div_pos (lt_min (eps_pos f hc r)
    (Tmod_pos (ghmod g) (ghmod_pos g) (bb r) (bb_pos r) r)) (by norm_num)

lemma ThC_le_eps (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (g : ℕ → X ≃ₜ X) (r : ℕ) :
    ThC f hc g r ≤ eps f hc r / 2 := by
  rw [ThC]
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

lemma ThC_le_half (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (g : ℕ → X ≃ₜ X) (r : ℕ) :
    ThC f hc g r ≤ Tmod (ghmod g) (bb r) r / 2 := by
  rw [ThC]
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

lemma ThC_congr (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) {g g' : ℕ → X ≃ₜ X} {r : ℕ}
    (h : ∀ k < r, g k = g' k) : ThC f hc g r = ThC f hc g' r := by
  have ht : Tmod (ghmod g) (bb r) r = Tmod (ghmod g') (bb r) r := by
    apply Tmod_congr
    intro k hk
    funext η
    simp only [ghmod, h k hk]
  rw [ThC, ThC, ht]

/-- The recursive choice of the approximating homeomorphisms: at stage `n` the first `n` entries
have been chosen (the rest are `id`); the `n`-th is chosen close to `f n`. -/
noncomputable def stG (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) :
    ℕ → (ℕ → X ≃ₜ X) := fun n =>
  Nat.rec (fun _ => Homeomorph.refl X)
    (fun k g => Function.update g k
      (Classical.choose (hn k (ThC f hc g k) (ThC_pos f hc g k)))) n

lemma stG_succ (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (k : ℕ) :
    stG f hc hn (k + 1) = Function.update (stG f hc hn k) k
      (Classical.choose (hn k (ThC f hc (stG f hc hn k) k)
        (ThC_pos f hc (stG f hc hn k) k))) := rfl

lemma stG_succ_self (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (k : ℕ) :
    stG f hc hn (k + 1) k
      = Classical.choose (hn k (ThC f hc (stG f hc hn k) k)
          (ThC_pos f hc (stG f hc hn k) k)) := by
  rw [stG_succ, Function.update_self]

lemma stG_stable (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) :
    ∀ {n r : ℕ}, r < n → stG f hc hn n r = stG f hc hn (r + 1) r := by
  intro n
  induction n with
  | zero => intro r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ n ih =>
    intro r hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · rw [stG_succ, Function.update_of_ne (Nat.ne_of_lt hlt), ih hlt]
    · rw [heq]

lemma ThC_stable (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    {n r : ℕ} (hr : r ≤ n) :
    ThC f hc (stG f hc hn n) r = ThC f hc (stG f hc hn (n + 1)) r := by
  apply ThC_congr
  intro k hk
  rw [stG_succ, Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le hk hr))]

/-- The chosen approximating homeomorphisms. -/
noncomputable def gsys (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) :
    ℕ → X ≃ₜ X := fun r => stG f hc hn (r + 1) r

lemma ThC_gsys (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (r : ℕ) :
    ThC f hc (gsys f hc hn) r = ThC f hc (stG f hc hn r) r := by
  apply ThC_congr
  intro k hk
  rw [stG_stable f hc hn hk]
  rfl

lemma hg_spec (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (r : ℕ)
    (x : X) : dist (gsys f hc hn r x) (f r x) < ThC f hc (gsys f hc hn) r := by
  have h := (Classical.choose_spec (hn r (ThC f hc (stG f hc hn r) r)
    (ThC_pos f hc (stG f hc hn r) r))) x
  rw [ThC_gsys f hc hn r]
  simpa only [gsys, stG_succ_self] using h

lemma hg_eps (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (r : ℕ)
    (x : X) : dist (gsys f hc hn r x) (f r x) < eps f hc r := by
  have h1 := hg_spec f hc hn r x
  have h2 := ThC_le_eps f hc (gsys f hc hn) r
  have h3 : 0 < eps f hc r := eps_pos f hc r
  linarith

/-- The level-`r` Lebesgue property of the chosen system. -/
lemma hg_leb (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (r i : ℕ)
    (hi : i < r) {x y : X} (hxy : dist x y < ThC f hc (gsys f hc hn) r) :
    dist (Gf (gfun (gsys f hc hn)) i (r - i) x) (Gf (gfun (gsys f hc hn)) i (r - i) y) < bb r := by
  have hbr : 0 < bb r := bb_pos r
  have hmod := Tmod_spec (ghmod (gsys f hc hn)) (ghmod_spec (gsys f hc hn)) (ghmod_pos (gsys f hc hn))
    (bb r) hbr r i hi x y
  apply hmod
  have h2 := ThC_le_half f hc (gsys f hc hn) r
  have hT : 0 < Tmod (ghmod (gsys f hc hn)) (bb r) r :=
    Tmod_pos (ghmod (gsys f hc hn)) (ghmod_pos (gsys f hc hn)) (bb r) hbr r
  linarith

/-! ## The error bound of the approximation -/

/-- The bound on the accumulated error of the level-`n` approximants. -/
noncomputable def Bnd (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n d : ℕ) : ℝ :=
  eps f hc n + (Finset.range (d - 1)).sum (fun i => cc f hc (n + 1 + i))

lemma Bnd_zero (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n : ℕ) :
    Bnd f hc n 0 = eps f hc n := by
  simp [Bnd]

lemma Bnd_one (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n : ℕ) :
    Bnd f hc n 1 = eps f hc n := by
  simp [Bnd]

lemma Bnd_succ (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    Bnd f hc n (d + 1) = Bnd f hc n d + cc f hc (n + d) := by
  unfold Bnd
  rw [show d + 1 - 1 = (d - 1) + 1 by omega, Finset.sum_range_succ,
    show n + 1 + (d - 1) = n + d by omega]
  ring

lemma geom16 (N : ℕ) : (Finset.range N).sum (fun i => (1/16:ℝ)^i) ≤ 16/15 := by
  rw [geom_sum_eq (show (1/16:ℝ) ≠ 1 by norm_num)]
  have hle : (1/16:ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h : ((1/16:ℝ)^N - 1) / (1/16 - 1) = (1 - (1/16)^N) * (16/15) := by
    rw [div_eq_iff (by norm_num : (1/16:ℝ) - 1 ≠ 0)]
    ring
  rw [h]
  have h0 : (0:ℝ) ≤ (1/16)^N := by positivity
  have h1 : (1:ℝ) - (1/16)^N ≤ 1 := by linarith
  calc (1 - (1/16:ℝ)^N) * (16/15) ≤ 1 * (16/15) :=
        mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ = 16/15 := by ring

lemma Bnd_le (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n d : ℕ) :
    Bnd f hc n d ≤ eps f hc n + cc f hc n / 15 := by
  have hsum : (Finset.range (d - 1)).sum (fun i => cc f hc (n + 1 + i)) ≤ cc f hc n / 15 := by
    have h1 : ∀ i ∈ Finset.range (d - 1), cc f hc (n + 1 + i) ≤ cc f hc n * (1/16:ℝ)^(i+1) := by
      intro i _
      have hh := cc_geom f hc n (i + 1)
      rwa [show n + (i + 1) = n + 1 + i by omega] at hh
    calc (Finset.range (d - 1)).sum (fun i => cc f hc (n + 1 + i))
        ≤ (Finset.range (d - 1)).sum (fun i => cc f hc n * (1/16:ℝ)^(i+1)) := Finset.sum_le_sum h1
      _ = cc f hc n * (Finset.range (d - 1)).sum (fun i => (1/16:ℝ)^(i+1)) := by
            rw [Finset.mul_sum]
      _ ≤ cc f hc n * ((1/16) * (16/15)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt (cc_pos f hc n))
            have h2 : (Finset.range (d - 1)).sum (fun i => (1/16:ℝ)^(i+1))
                = (1/16) * (Finset.range (d - 1)).sum (fun i => (1/16:ℝ)^i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [pow_succ]; ring
            rw [h2]
            exact mul_le_mul_of_nonneg_left (geom16 (d - 1)) (by norm_num)
      _ = cc f hc n / 15 := by ring
  unfold Bnd
  linarith

lemma Bnd_nonneg (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n d : ℕ) :
    0 ≤ Bnd f hc n d := by
  have h1 : 0 < eps f hc n := eps_pos f hc n
  have h2 : ∀ i ∈ Finset.range (d - 1), 0 ≤ cc f hc (n + 1 + i) :=
    fun i _ => le_of_lt (cc_pos f hc _)
  unfold Bnd
  linarith [Finset.sum_nonneg h2]

/-- The main estimate: the `g`-composition and the `f`-composition differ by at most `Bnd`. -/
lemma Ebound (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (g : ℕ → X ≃ₜ X)
    (hg : ∀ k x, dist (g k x) (f k x) < eps f hc k) :
    ∀ d, ∀ n u, dist (Gf (gfun g) n d u) (Gf f n d u) ≤ Bnd f hc n d := by
  intro d
  induction d with
  | zero => intro n u; rw [Bnd_zero]; simpa using le_of_lt (eps_pos f hc n)
  | succ d ih =>
    intro n u
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [Bnd_one]
      simpa only [Gf_succ, Gf_zero, Function.comp_apply, id_eq] using le_of_lt (hg n u)
    · have hgd : Gf (gfun g) n (d + 1) u = Gf (gfun g) n d (g (n + d) u) := by
        rw [← Gf_mul_succ (gfun g) d n, Function.comp_apply]
      have hfd : Gf f n (d + 1) u = Gf f n d (f (n + d) u) := by
        rw [← Gf_mul_succ f d n, Function.comp_apply]
      rw [hgd, hfd, Bnd_succ f hc n hd]
      have ha2 : dist (g (n + d) u) (f (n + d) u) < a2 f hc (n + d) := by
        have h1 := hg (n + d) u
        have h2 := eps_le_a2 f hc (n + d)
        have h3 : 0 < a2 f hc (n + d) := a2_pos f hc (n + d)
        linarith
      have hspec := a2_spec f hc (n + d) (j := n) (by omega) (x := g (n + d) u)
        (y := f (n + d) u) ha2
      rw [show n + d - n = d by omega] at hspec
      calc dist (Gf (gfun g) n d (g (n + d) u)) (Gf f n d (f (n + d) u))
          ≤ dist (Gf (gfun g) n d (g (n + d) u)) (Gf f n d (g (n + d) u))
            + dist (Gf f n d (g (n + d) u)) (Gf f n d (f (n + d) u)) :=
              dist_triangle _ _ _
        _ ≤ Bnd f hc n d + cc f hc (n + d) := add_le_add (ih n (g (n + d) u)) (le_of_lt hspec)

/-! ## The inverse limit as a compact space -/

/-- A near homeomorphism of a compact metric space is surjective. -/
lemma surjective_of_isNearHomeo {f : X → X} (hf : Continuous f)
    (hn : Work.Brown.IsNearHomeo f) : Function.Surjective f := by
  intro y
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  by_contra hy
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl y hy
  obtain ⟨h, hh⟩ := hn ε hεpos
  have hmem : f (h.symm y) ∈ Set.range f := ⟨h.symm y, rfl⟩
  have hlt : dist y (f (h.symm y)) < ε := by
    have h1 := hh (h.symm y)
    rwa [Homeomorph.apply_symm_apply] at h1
  have hge : ε ≤ dist y (f (h.symm y)) := by
    by_contra hcon
    rw [not_le] at hcon
    have hb : f (h.symm y) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hcon
    exact (hε hb) hmem
  linarith

lemma isClosed_IL (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) :
    IsClosed {x : ℕ → X | ∀ k, f k (x (k + 1)) = x k} := by
  have h : {x : ℕ → X | ∀ k, f k (x (k + 1)) = x k}
      = ⋂ k, {x : ℕ → X | f k (x (k + 1)) = x k} := by
    ext x; simp
  rw [h]
  exact isClosed_iInter fun k =>
    isClosed_eq ((hc k).comp (continuous_apply (k + 1))) (continuous_apply k)

lemma compactSpace_IL (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) :
    CompactSpace (IL f) := by
  haveI : CompactSpace (ℕ → X) := Pi.compactSpace
  exact isCompact_iff_compactSpace.mp (isClosed_IL f hc).isCompact

/-- Iterating right inverses of the bonding maps. -/
noncomputable def rhoIte (rho : ℕ → X → X) (m : ℕ) : ℕ → X → X :=
  fun d => Nat.rec id (fun d' ih => rho (m + d') ∘ ih) d

@[simp] lemma rhoIte_zero (rho : ℕ → X → X) (m : ℕ) : rhoIte rho m 0 = id := rfl

lemma rhoIte_succ (rho : ℕ → X → X) (m d : ℕ) :
    rhoIte rho m (d + 1) = rho (m + d) ∘ rhoIte rho m d := rfl

lemma rhoIte_one (rho : ℕ → X → X) (m : ℕ) : rhoIte rho m 1 = rho m := by
  rw [show (1:ℕ) = 0 + 1 by omega, rhoIte_succ, rhoIte_zero, Nat.add_zero,
    Function.comp_id]

/-- Every coordinate of the inverse limit is surjective when the bonding maps are onto. -/
lemma surjective_eval (f : ℕ → X → X) (hc : ∀ k, Continuous (f k))
    (hsurj : ∀ k, Function.Surjective (f k)) (m : ℕ) :
    Function.Surjective (fun s : IL f => s.1 m) := by
  classical
  choose rho hrho using hsurj
  intro y
  set t : ℕ → X := fun j => if h : j ≤ m then Gf f j (m - j) y else rhoIte rho m (j - m) y
    with htab
  have ht : ∀ k, f k (t (k + 1)) = t k := by
    intro k
    rw [htab]
    dsimp only
    by_cases h1 : k + 1 ≤ m
    · have hk : k ≤ m := by omega
      rw [dif_pos h1, dif_pos hk, show m - (k + 1) = m - k - 1 by omega]
      conv_rhs => rw [show m - k = (m - k - 1) + 1 by omega]
      rw [Gf_succ]
      rfl
    · rw [dif_neg h1]
      by_cases h2 : k ≤ m
      · have hk : k = m := by omega
        rw [dif_pos h2, ← hk, show k - k = 0 by omega, Gf_zero]
        rw [show k + 1 - k = 1 by omega, rhoIte_one]
        exact hrho k y
      · rw [dif_neg h2]
        rw [show k + 1 - m = (k - m) + 1 by omega, rhoIte_succ,
          show m + (k - m) = k by omega, Function.comp_apply]
        exact hrho k _
  have htm : t m = y := by
    rw [htab]
    dsimp only
    rw [dif_pos (le_refl m), show m - m = 0 by omega, Gf_zero]
    rfl
  exact ⟨⟨t, ht⟩, htm⟩

lemma surjective_Gf (F : ℕ → X → X) (hF : ∀ k, Function.Surjective (F k)) :
    ∀ d n, Function.Surjective (Gf F n d) := by
  intro d
  induction d with
  | zero => intro n; rw [Gf_zero]; exact Function.surjective_id
  | succ d ih => intro n; rw [Gf_succ]; exact (hF n).comp (ih (n + 1))

/-! ## The telescoping estimate -/

/-- Splitting an iterated composition. -/
lemma Gf_add (F : ℕ → X → X) (n a b : ℕ) :
    Gf F n (a + b) = Gf F n a ∘ Gf F (n + a) b := by
  induction b with
  | zero => simp [Gf_zero]
  | succ b ih =>
    have h1 : a + (b + 1) = (a + b) + 1 := by omega
    have h2 : (n + a) + b = n + (a + b) := by omega
    rw [h1, ← Gf_mul_succ F (a + b) n, ih, ← Gf_mul_succ F b (n + a), h2,
      Function.comp_assoc]

/-! ## The Cauchy property of the approximants -/

lemma geom2 (N : ℕ) : (Finset.range N).sum (fun i => (1/2:ℝ)^i) ≤ 2 := by
  rw [geom_sum_eq (show (1/2:ℝ) ≠ 1 by norm_num)]
  have hle : (1/2:ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : (0:ℝ) ≤ (1/2)^N := by positivity
  have h : ((1/2:ℝ)^N - 1) / (1/2 - 1) = (1 - (1/2)^N) * 2 := by
    rw [div_eq_iff (by norm_num : (1/2:ℝ) - 1 ≠ 0)]
    ring
  rw [h]
  have h1 : (1:ℝ) - (1/2)^N ≤ 1 := by linarith
  calc (1 - (1/2:ℝ)^N) * 2 ≤ 1 * 2 := mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ = 2 := by ring

lemma sum_bb_le (m d : ℕ) : (Finset.range d).sum (fun i => bb (m + i)) ≤ (1/2:ℝ)^m := by
  have h1 : ∀ i, bb (m + i) = (1/2:ℝ)^(m+1) * (1/2)^i := by
    intro i
    unfold bb
    rw [← pow_add]
    congr 1
    omega
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
  calc (1/2:ℝ)^(m+1) * (Finset.range d).sum (fun i => (1/2:ℝ)^i)
      ≤ (1/2:ℝ)^(m+1) * 2 := mul_le_mul_of_nonneg_left (geom2 d) (by positivity)
    _ = (1/2:ℝ)^m := by rw [pow_succ]; ring

/-- Consecutive approximants at level `N` differ by at most `bb m` for `m > N`. -/
lemma step_bound (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (N : ℕ)
    (s : IL f) {m : ℕ} (hNm : N < m) :
    dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
      (Gf (gfun (gsys f hc hn)) N (m + 1 - N) (s.1 (m + 1))) < bb m := by
  have h1 : m + 1 - N = (m - N) + 1 := by omega
  have hsplit : Gf (gfun (gsys f hc hn)) N (m + 1 - N)
      = Gf (gfun (gsys f hc hn)) N (m - N) ∘ gfun (gsys f hc hn) m := by
    rw [h1, ← Gf_mul_succ (gfun (gsys f hc hn)) (m - N) N]
    rw [show N + (m - N) = m by omega]
  rw [hsplit, Function.comp_apply, ← s.2 m]
  calc dist (Gf (gfun (gsys f hc hn)) N (m - N) (f m (s.1 (m + 1))))
        (Gf (gfun (gsys f hc hn)) N (m - N) (gfun (gsys f hc hn) m (s.1 (m + 1))))
      = dist (Gf (gfun (gsys f hc hn)) N (m - N) (gfun (gsys f hc hn) m (s.1 (m + 1))))
          (Gf (gfun (gsys f hc hn)) N (m - N) (f m (s.1 (m + 1)))) := dist_comm _ _
    _ < bb m := hg_leb f hc hn m N hNm (hg_spec f hc hn m (s.1 (m + 1)))

/-- The telescoping bound: the `n`-th and `m`-th approximants differ by the sum of the
`bb r`. -/
lemma telescope (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) (N : ℕ)
    (s : IL f) : ∀ {n m : ℕ}, N < n → n ≤ m →
    dist (Gf (gfun (gsys f hc hn)) N (n - N) (s.1 n))
      (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
      ≤ (Finset.range (m - n)).sum (fun i => bb (n + i)) := by
  intro n m hN hnm
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hNm : N < m := lt_of_lt_of_le hN hnm
    have hstep := le_of_lt (step_bound f hc hn N s (m := m) hNm)
    calc dist (Gf (gfun (gsys f hc hn)) N (n - N) (s.1 n))
          (Gf (gfun (gsys f hc hn)) N ((m + 1) - N) (s.1 (m + 1)))
        ≤ dist (Gf (gfun (gsys f hc hn)) N (n - N) (s.1 n))
            (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
          + dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
            (Gf (gfun (gsys f hc hn)) N ((m + 1) - N) (s.1 (m + 1))) := dist_triangle _ _ _
      _ ≤ (Finset.range (m - n)).sum (fun i => bb (n + i)) + bb m := add_le_add ih hstep
      _ = (Finset.range ((m + 1) - n)).sum (fun i => bb (n + i)) := by
            rw [show m + 1 - n = (m - n) + 1 by omega, Finset.sum_range_succ,
              show n + (m - n) = m by omega]

lemma cauchy_approx (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) :
    CauchySeq (fun m => Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have ht : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k in atTop, (1/2:ℝ)^k < ε := ht.eventually (gt_mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M₀, hM₀⟩ := hev
  refine ⟨max (N + 1) M₀, fun m hm m' hm' => ?_⟩
  have hmle : max (N + 1) M₀ ≤ m := hm
  have hmle' : max (N + 1) M₀ ≤ m' := hm'
  have hmN : N < m := by
    have : N + 1 ≤ m := le_trans (le_max_left (N + 1) M₀) hmle
    omega
  have hM0le : M₀ ≤ m := le_trans (le_max_right (N + 1) M₀) hmle
  have hM0le' : M₀ ≤ m' := le_trans (le_max_right (N + 1) M₀) hmle'
  have hM0 : (1/2:ℝ)^m < ε :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hM0le)
      (hM₀ M₀ (le_refl M₀))
  have hM0' : (1/2:ℝ)^m' < ε :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hM0le')
      (hM₀ M₀ (le_refl M₀))
  rcases le_total m m' with h | h
  · have htel := telescope f hc hn N s hmN h
    have hsum := sum_bb_le m (m' - m)
    linarith
  · have hm'N : N < m' := by
      have hx : N + 1 ≤ m' := le_trans (le_max_left (N + 1) M₀) hmle'
      omega
    have htel := telescope f hc hn N s hm'N h
    have hsum := sum_bb_le m' (m - m')
    rw [dist_comm]
    linarith

/-! ## The limit map -/

lemma Bnd_le_cc (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (n d : ℕ) :
    Bnd f hc n d ≤ (19/60) * cc f hc n := by
  have h1 := Bnd_le f hc n d
  have h2 := eps_le_cc f hc n
  have h3 : 0 < cc f hc n := cc_pos f hc n
  linarith

/-- The limit of the approximants `Gf g N (m-N) (s m)`. -/
noncomputable def Gmap (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) : X :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchy_approx f hc hn N s))

lemma Gmap_spec (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) :
    Tendsto (fun m => Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) atTop
      (nhds (Gmap f hc hn N s)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchy_approx f hc hn N s))

/-- `Gmap f N` is close to the `N`-th coordinate projection. -/
lemma Gmap_close (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) :
    dist (Gmap f hc hn N s) (s.1 N) ≤ (19/60) * cc f hc N := by
  have h3 : Tendsto (fun m => dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (s.1 N))
      atTop (nhds (dist (Gmap f hc hn N s) (s.1 N))) :=
    (Gmap_spec f hc hn N s).dist tendsto_const_nhds
  refine le_of_tendsto_of_tendsto h3 tendsto_const_nhds ?_
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  calc dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (s.1 N)
      = dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (Gf f N (m - N) (s.1 m)) := by
        have hmem : s.1 N = Gf f N (m - N) (s.1 m) := by
          rw [← Gf_mem f s (m - N) N, show N + (m - N) = m by omega]
        rw [hmem]
    _ ≤ Bnd f hc N (m - N) := Ebound f hc (gsys f hc hn) (hg_eps f hc hn) (m - N) N (s.1 m)
    _ ≤ (19/60) * cc f hc N := Bnd_le_cc f hc N (m - N)

/-- The uniform rate of convergence of the approximants. -/
lemma Gmap_rate (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) {m : ℕ} (hm : N < m) :
    dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (Gmap f hc hn N s) ≤ (1/2:ℝ)^m := by
  have h3 : Tendsto (fun m' => dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
      (Gf (gfun (gsys f hc hn)) N (m' - N) (s.1 m'))) atTop
      (nhds (dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (Gmap f hc hn N s))) :=
    tendsto_const_nhds.dist (Gmap_spec f hc hn N s)
  refine le_of_tendsto_of_tendsto h3 tendsto_const_nhds ?_
  refine Filter.eventually_atTop.mpr ⟨m, fun m' hm' => ?_⟩
  calc dist (Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m))
        (Gf (gfun (gsys f hc hn)) N (m' - N) (s.1 m'))
      ≤ (Finset.range (m' - m)).sum (fun i => bb (m + i)) := telescope f hc hn N s hm hm'
    _ ≤ (1/2:ℝ)^m := sum_bb_le m (m' - m)

/-- The limit values form a thread of the `g`-system. -/
lemma Gmap_thread (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) (s : IL f) :
    Gmap f hc hn N s = gsys f hc hn N (Gmap f hc hn (N + 1) s) := by
  have h2 : Tendsto (fun m => gsys f hc hn N
      (Gf (gfun (gsys f hc hn)) (N + 1) (m - (N + 1)) (s.1 m))) atTop
      (nhds (gsys f hc hn N (Gmap f hc hn (N + 1) s))) :=
    ((gsys f hc hn N).continuous.tendsto _).comp (Gmap_spec f hc hn (N + 1) s)
  have hev : (fun m => Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) =ᶠ[atTop]
      (fun m => gsys f hc hn N (Gf (gfun (gsys f hc hn)) (N + 1) (m - (N + 1)) (s.1 m))) := by
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
    dsimp only
    have hsplit : Gf (gfun (gsys f hc hn)) N (m - N)
        = gsys f hc hn N ∘ Gf (gfun (gsys f hc hn)) (N + 1) (m - (N + 1)) := by
      rw [show m - N = 1 + (m - (N + 1)) by omega, Gf_add, Nat.add_comm]
      rfl
    rw [hsplit, Function.comp_apply]
  exact tendsto_nhds_unique (Gmap_spec f hc hn N s) (Filter.Tendsto.congr' hev.symm h2)

lemma continuous_Gf (F : ℕ → X → X) (hF : ∀ k, Continuous (F k)) :
    ∀ d n, Continuous (Gf F n d) := by
  intro d
  induction d with
  | zero => intro n; rw [Gf_zero]; exact continuous_id
  | succ d ih => intro n; rw [Gf_succ]; exact (hF n).comp (ih (n + 1))

/-- A uniform limit of continuous maps with rate `2^{-m}` is continuous. -/
lemma continuous_of_halflife_rate (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (φ : IL f → X) (u : ℕ → IL f → X) (huc : ∀ m, Continuous (u m))
    (hrate : ∀ᶠ m in atTop, ∀ s, dist (u m s) (φ s) ≤ (1/2:ℝ)^m) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have ht : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ m in atTop, (1/2:ℝ)^m < ε/4 := ht.eventually (gt_mem_nhds (by linarith))
  rcases (hev.and hrate).exists with ⟨m, hm1, hm2⟩
  have h1 : ∀ᶠ s in nhds s₀, dist (u m s) (u m s₀) < ε/2 :=
    Metric.tendsto_nhds.mp (huc m).continuousAt (ε/2) (by linarith)
  filter_upwards [h1] with s hs
  have h2 : dist (φ s) (u m s) ≤ (1/2:ℝ)^m := by rw [dist_comm]; exact hm2 s
  have h3 : dist (u m s₀) (φ s₀) ≤ (1/2:ℝ)^m := hm2 s₀
  calc dist (φ s) (φ s₀) ≤ dist (φ s) (u m s) + dist (u m s) (φ s₀) := dist_triangle _ _ _
    _ ≤ dist (φ s) (u m s) + (dist (u m s) (u m s₀) + dist (u m s₀) (φ s₀)) := by
          linarith [dist_triangle (u m s) (u m s₀) (φ s₀)]
    _ < ε := by linarith

lemma Gmap_continuous (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (N : ℕ) : Continuous (Gmap f hc hn N) := by
  refine continuous_of_halflife_rate f hc hn (Gmap f hc hn N)
    (fun m s => Gf (gfun (gsys f hc hn)) N (m - N) (s.1 m)) (fun m => ?_) ?_
  · exact (continuous_Gf (gfun (gsys f hc hn))
      (fun k => (gsys f hc hn k).continuous) (m - N) N).comp
      ((continuous_apply m).comp continuous_subtype_val)
  · refine Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
    intro s
    exact Gmap_rate f hc hn N s (by omega)

/-- A uniform limit of surjective maps with rate `2^{-m}` is surjective. -/
lemma surjective_of_eventually_rate (f : ℕ → X → X) (hc : ∀ k, Continuous (f k))
    (hn : IsNearSeq f) (φ : IL f → X) (hφ : Continuous φ) (u : ℕ → IL f → X)
    (hu : ∀ m, Function.Surjective (u m))
    (hrate : ∀ᶠ m in atTop, ∀ s, dist (u m s) (φ s) ≤ (1/2:ℝ)^m) :
    Function.Surjective φ := by
  haveI : CompactSpace (IL f) := compactSpace_IL f hc
  intro y
  by_contra hy
  have hclosed : IsClosed (Set.range φ) := (isCompact_range hφ).isClosed
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl y hy
  have ht : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ m in atTop, (1/2:ℝ)^m < ε := ht.eventually (gt_mem_nhds hεpos)
  rcases (hev.and hrate).exists with ⟨m, hm1, hm2⟩
  obtain ⟨s, hs⟩ := hu m y
  have hb : φ s ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, ← hs]
    exact lt_of_le_of_lt (by rw [dist_comm]; exact hm2 s) hm1
  exact (hε hb) ⟨s, rfl⟩

lemma Gmap_surj (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f) :
    Function.Surjective (Gmap f hc hn 0) := by
  refine surjective_of_eventually_rate f hc hn (Gmap f hc hn 0) (Gmap_continuous f hc hn 0)
    (fun m s => Gf (gfun (gsys f hc hn)) 0 m (s.1 m)) (fun m => ?_) ?_
  · exact (surjective_Gf (gfun (gsys f hc hn))
      (fun k => (gsys f hc hn k).surjective) m 0).comp
      (surjective_eval f hc (fun k => surjective_of_isNearHomeo (hc k) (hn k)) m)
  · refine Filter.eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    intro s
    exact Gmap_rate f hc hn 0 s (by omega)

/-- Distinct threads of the inverse limit are separated in some coordinate. -/
lemma separation (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    (s s' : IL f) (h : ∀ N, dist (s.1 N) (s'.1 N) ≤ cc f hc N) : s = s' := by
  have hzero : ∀ n, s.1 n = s'.1 n := by
    intro n
    have hlim : dist (s.1 n) (s'.1 n) = 0 := by
      apply le_antisymm _ dist_nonneg
      by_contra hcon
      rw [not_le] at hcon
      have hev : ∀ᶠ k in atTop, bb k < dist (s.1 n) (s'.1 n) :=
        bb_tendsto.eventually (gt_mem_nhds hcon)
      rcases (hev.and (Filter.eventually_gt_atTop n)).exists with ⟨k, hk1, hk2⟩
      have h1 : dist (s.1 k) (s'.1 k) < aa f hc k :=
        lt_of_le_of_lt (h k) (cc_lt_aa f hc k)
      have h2 := aa_spec f hc k hk2 (x := s.1 k) (y := s'.1 k) h1
      have h3 : s.1 k = s.1 (n + (k - n)) := by rw [show n + (k - n) = k by omega]
      have h3' : s'.1 k = s'.1 (n + (k - n)) := by rw [show n + (k - n) = k by omega]
      rw [h3, Gf_mem f s (k - n) n, h3', Gf_mem f s' (k - n) n] at h2
      linarith
    exact dist_eq_zero.mp hlim
  exact Subtype.ext (funext hzero)

/-- `Gmap f 0` is injective. -/
lemma Gmap_inj (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hn : IsNearSeq f)
    {s s' : IL f} (h : ∀ N, Gmap f hc hn N s = Gmap f hc hn N s') : s = s' := by
  by_contra hne
  have h2 : ∃ N, cc f hc N < dist (s.1 N) (s'.1 N) := by
    by_contra hcon
    rw [not_exists] at hcon
    exact hne (separation f hc hn s s' fun N => not_lt.mp (hcon N))
  obtain ⟨N, hN⟩ := h2
  have h1 := Gmap_close f hc hn N s
  have h1' := Gmap_close f hc hn N s'
  have h3 : dist (s.1 N) (s'.1 N) < cc f hc N := by
    calc dist (s.1 N) (s'.1 N)
        ≤ dist (s.1 N) (Gmap f hc hn N s) + dist (Gmap f hc hn N s) (s'.1 N) :=
          dist_triangle _ _ _
      _ = dist (s.1 N) (Gmap f hc hn N s) + dist (Gmap f hc hn N s') (s'.1 N) := by rw [h N]
      _ ≤ (19/60) * cc f hc N + (19/60) * cc f hc N := by
            rw [dist_comm (s.1 N) (Gmap f hc hn N s)]
            linarith
      _ < cc f hc N := by
            have := cc_pos f hc N
            linarith
  linarith

/-- **Morton Brown's inverse limit theorem.**  The inverse limit of any sequence of near
homeomorphisms of a compact metric space is homeomorphic to the space. -/
theorem brown_inverseLimit {X : Type*} [MetricSpace X] [CompactSpace X] (f : ℕ → X → X) (hc : ∀ k, Continuous (f k)) (hnear : ∀ k, Work.Brown.IsNearHomeo (f k)) : Nonempty ({x : ℕ → X // ∀ k, f k (x (k + 1)) = x k} ≃ₜ X) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : IsEmpty X := hX
    haveI : IsEmpty (ℕ → X) := ⟨fun g => isEmptyElim (g 0)⟩
    haveI : IsEmpty (IL f) := ⟨fun s => isEmptyElim s.1⟩
    exact ⟨{ toEquiv := Equiv.equivOfIsEmpty (IL f) X
             continuous_toFun := continuous_iff_continuousAt.mpr (fun x => isEmptyElim x)
             continuous_invFun := continuous_iff_continuousAt.mpr (fun x => isEmptyElim x) }⟩
  · haveI : Nonempty X := hX
    have hn : IsNearSeq f := hnear
    haveI : CompactSpace (IL f) := compactSpace_IL f hc
    have hinj : Function.Injective (Gmap f hc hn 0) := by
      intro s s' hss
      have hall : ∀ N, Gmap f hc hn N s = Gmap f hc hn N s' := by
        intro N
        induction N with
        | zero => exact hss
        | succ N ih =>
          have h1 : gsys f hc hn N (Gmap f hc hn (N + 1) s)
              = gsys f hc hn N (Gmap f hc hn (N + 1) s') := by
            rw [← Gmap_thread f hc hn N s, ← Gmap_thread f hc hn N s', ih]
          exact (gsys f hc hn N).injective h1
      exact Gmap_inj f hc hn hall
    have hsurj : Function.Surjective (Gmap f hc hn 0) := Gmap_surj f hc hn
    have hcont : Continuous (Gmap f hc hn 0) := Gmap_continuous f hc hn 0
    refine ⟨Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (Gmap f hc hn 0) ⟨hinj, hsurj⟩) ?_⟩
    rw [show ⇑(Equiv.ofBijective (Gmap f hc hn 0) ⟨hinj, hsurj⟩) = Gmap f hc hn 0 from
      funext (fun x => Equiv.ofBijective_apply _ _ x)]
    exact hcont

end Work.Brown.Engine
