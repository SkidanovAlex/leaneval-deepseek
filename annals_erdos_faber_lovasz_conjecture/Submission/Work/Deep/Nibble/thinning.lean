import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Prob.Spaces

/-!
# Thinning a matching

This module proves `Work.Deep.Nibble.thinning`, the second half of Corollary
`cor:sparse_egj` of Kang–Kühn–Methuku–Osthus (Annals 2023): given a matching `M₀` in a
hypergraph on `Fin n` whose edges have size at most `r`, and a finite family `(S a)_{a : σ}`
of vertex sets each of which meets `V(M₀)` in at least a `(1-3κ)`-fraction of its vertices,
and provided `2|σ| exp(-(3/8)κ²D^{1/20}/r) < 1`, one can delete edges of `M₀` (each kept
independently with probability `1-γ`) so that every `S a` loses a `(γ ± 4κ)`-fraction of its
vertices to the surviving matching.

The proof is the alteration argument described in the paper (p. 503):

* pass to the product space `↥M₀ → Bool` where coordinate `i` is `true` with probability
  `1-γ` (the finite probability space `Work.Deep.Prob.FinProbSpace.bernoulliConst`);
* for a fixed `a`, the number of vertices of `S a` covered by the kept edges is the sum of
  the independent contributions `|S a ∩ e|`, each of which is at most `C := r`; Bernstein's
  inequality in the form `chernoff_two_sided_finite_weighted` therefore gives
  `ℙ[|X - E X| ≥ κ|S a|] ≤ 2 exp (-(3/8) κ² |S a| / r)`, because `E X = (1-γ)u` with
  `u := |S a ∩ V(M₀)| ∈ [(1-3κ)|S a|, |S a|]`;
* the union bound over the `σ` sets gives a positive-probability good outcome, i.e. an
  actual outcome `s : ↥M₀ → Bool`, and the kept submatching is `keptMatching M₀ s`.

The load-bearing combinatorial inputs are the counting identities
`ncard_inter_iUnion` / `ncard_inter_iUnion_ite`: for pairwise disjoint edges `e i`,
`|T ∩ ⋃_{i∈I} e i| = ∑_{i∈I} |T ∩ e i|`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture (IsMatching matchVert edgeSize edgeSize_eq_ncard)

/-! ## Counting identities for pairwise disjoint families -/

/-- **Counting identity.** For a finite family `f` of pairwise disjoint sets and any set `T`,
the number of elements of `T` lying in the union is the sum of the numbers of elements of
`T` in the individual sets. -/
theorem ncard_inter_iUnion {α ι : Type*} [Fintype ι] [Finite α] (T : Set α) (f : ι → Set α)
    (h : Pairwise (fun i j => Disjoint (f i) (f j))) :
    (T ∩ ⋃ i, f i).ncard = ∑ i, (T ∩ f i).ncard := by
  rw [Set.inter_iUnion]
  rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (T ∩ f i))
    (fun i j hij => (h hij).mono Set.inter_subset_right Set.inter_subset_right)]
  rw [finsum_eq_sum_of_fintype]

/-- **Counting identity, Boolean-pattern form.** Keeping only the indices of a pattern `b`,
the contribution of the discarded sets is zero. -/
theorem ncard_inter_iUnion_ite {α ι : Type*} [Fintype ι] [Finite α] (T : Set α)
    (f : ι → Set α) (h : Pairwise (fun i j => Disjoint (f i) (f j))) (b : ι → Bool) :
    (T ∩ ⋃ i, (if b i then f i else ∅)).ncard = ∑ i, (if b i then (T ∩ f i).ncard else 0) := by
  rw [ncard_inter_iUnion T (fun i => if b i then f i else ∅) (fun i j hij => ?_)]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hb : b i = true
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      simp
  · have hsub : ∀ i, (if b i then f i else (∅ : Set α)) ⊆ f i := by
      intro i
      by_cases hb : b i = true
      · rw [if_pos hb]
      · rw [if_neg hb]; exact Set.empty_subset _
    exact (h hij).mono (hsub _) (hsub _)

/-- **The vertices of `T` lost to a matching.**  `|T ∖ V(M)| = |T| - |T ∩ V(M)|`. -/
theorem ncard_sdiff_matchVert {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {M : Set 𝓗} (T : Set (Fin n)) :
    ((T \ matchVert M).ncard : ℝ) = (T.ncard : ℝ) - ((T ∩ matchVert M).ncard : ℝ) := by
  have hset : T \ matchVert M = T \ (T ∩ matchVert M) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hset, Set.ncard_sdiff Set.inter_subset_left,
    Nat.cast_sub (Set.ncard_le_ncard Set.inter_subset_left)]

/-! ## The kept submatching -/

/-- The sub-matching of `M₀` obtained by keeping the edges whose index is `true` under the
Boolean pattern `s`. -/
def keptMatching {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} (M₀ : Set 𝓗)
    (s : ↥M₀ → Bool) : Set 𝓗 :=
  {j | ∃ (h : j ∈ M₀), s ⟨j, h⟩ = true}

/-- `keptMatching` is a subfamily of `M₀`. -/
theorem keptMatching_subset {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {M₀ : Set 𝓗} (s : ↥M₀ → Bool) : keptMatching M₀ s ⊆ M₀ :=
  fun _ h => h.1

/-- The vertex set of the kept submatching, as a union of the kept edges. -/
theorem matchVert_keptMatching {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {M₀ : Set 𝓗} (s : ↥M₀ → Bool) :
    matchVert (keptMatching M₀ s)
      = ⋃ i : ↥M₀, (if s i then ((i.1 : 𝓗) : Set (Fin n)) else ∅) := by
  unfold keptMatching matchVert
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_ite_empty_right, exists_prop]
  constructor
  · rintro ⟨i, ⟨h, hs⟩, hx⟩
    exact ⟨⟨i, h⟩, hs, hx⟩
  · rintro ⟨i, hs, hx⟩
    exact ⟨i.1, ⟨i.2, by simpa using hs⟩, hx⟩

/-- The vertex set of a matching `M₀`, indexed by its own elements. -/
theorem matchVert_eq_iUnion {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {M₀ : Set 𝓗} : matchVert M₀ = ⋃ i : ↥M₀, ((i.1 : 𝓗) : Set (Fin n)) := by
  unfold matchVert
  exact (Set.iUnion_subtype M₀ fun i : ↥M₀ => ((i.1 : 𝓗) : Set (Fin n))).symm

/-! ## The product Bernoulli space -/

/-- On the product space `ι → Bool` with coordinate `i` equal to `true` with probability `p`,
the probability of the event `t ≤ |Y s - μ|` is the sum of the atom weights over that event. -/
theorem prob_bernoulliConst_abs {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (Y : (ι → Bool) → ℝ) (μ t : ℝ) :
    (Work.Deep.Prob.FinProbSpace.bernoulliConst (ι := ι) p hp0 hp1).prob {s | t ≤ |Y s - μ|}
      = ∑ s : ι → Bool, (∏ i, (if s i then p else 1 - p)) *
          (if t ≤ |Y s - μ| then (1 : ℝ) else 0) := by
  rw [Work.Deep.Prob.FinProbSpace.prob]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : t ≤ |Y s - μ| <;>
    simp [Set.mem_ofPred_eq, h, Work.Deep.Prob.FinProbSpace.bernoulliConst_mass]

/-! ## Numeric lemmas -/

/-- **The Chernoff exponent is at most `-(3/8)κ²S/r`.**  Here `u` is the mean number of
vertices of `S` covered by `M₀`, which is at most `|S| = S`; the Bernstein denominator
`2r(u + κS/3)` is therefore at most `(8/3)rS`. -/
theorem chernoff_exponent_le {κ γ r S u : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hr : 0 < r)
    (hS : 0 < S) (hu0 : 0 ≤ u) (huS : u ≤ S) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    -(κ * S) ^ 2 / (2 * r * ((1 - γ) * u + κ * S / 3)) ≤ -(3 / 8) * κ ^ 2 * S / r := by
  have hDen_pos : 0 < 2 * r * ((1 - γ) * u + κ * S / 3) := by
    have h1 : 0 ≤ (1 - γ) * u := mul_nonneg (by linarith) hu0
    have h2 : 0 < κ * S / 3 := by positivity
    have : 0 < (1 - γ) * u + κ * S / 3 := by linarith
    positivity
  have hle : (1 - γ) * u + κ * S / 3 ≤ (4 / 3) * S := by
    have h1 : (1 - γ) * u ≤ S := by
      calc (1 - γ) * u ≤ 1 * u := mul_le_mul_of_nonneg_right (by linarith) hu0
        _ = u := one_mul _
        _ ≤ S := huS
    have h2 : κ * S / 3 ≤ S / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_of_le_one_left hS.le hκ1
    linarith
  have hDen_le : 2 * r * ((1 - γ) * u + κ * S / 3) ≤ (8 / 3) * r * S := by
    have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * r)
    linarith [this]
  have key : (3 / 8) * κ ^ 2 * S / r ≤ (κ * S) ^ 2 / (2 * r * ((1 - γ) * u + κ * S / 3)) := by
    calc (3 / 8) * κ ^ 2 * S / r = (κ * S) ^ 2 / ((8 / 3) * r * S) := by
          field_simp
      _ ≤ (κ * S) ^ 2 / (2 * r * ((1 - γ) * u + κ * S / 3)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hDen_pos hDen_le
  calc -(κ * S) ^ 2 / (2 * r * ((1 - γ) * u + κ * S / 3))
      = -((κ * S) ^ 2 / (2 * r * ((1 - γ) * u + κ * S / 3))) := by ring
    _ ≤ -((3 / 8) * κ ^ 2 * S / r) := neg_le_neg key
    _ = -(3 / 8) * κ ^ 2 * S / r := by ring

/-- Monotonicity of the exponent in the size of the vertex set: a larger `S` gives a smaller
exponent. -/
theorem exp_thinning_mono {κ r S D : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (hD : D ≤ S) :
    Real.exp (-(3 / 8) * κ ^ 2 * S / r) ≤ Real.exp (-(3 / 8 * κ ^ 2 * D / r)) := by
  apply Real.exp_le_exp.mpr
  have h : (3 / 8 * κ ^ 2 * D) / r ≤ (3 / 8 * κ ^ 2 * S) / r := by
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith [hD, hκ, sq_nonneg κ]
  calc -(3 / 8) * κ ^ 2 * S / r = -((3 / 8 * κ ^ 2 * S) / r) := by ring
    _ ≤ -((3 / 8 * κ ^ 2 * D) / r) := neg_le_neg h
    _ = -(3 / 8 * κ ^ 2 * D / r) := by ring

/-- **Final numeric step of the thinning lemma.**  If `A = S - Y` where `Y = |S ∩ V(M)|` is
the number of vertices of `S` covered by the kept matching `M`, if the deviation
`|Y - (1-γ)u|` of `Y` from its mean (with `u = |S ∩ V(M₀)|` the count for the full matching)
is less than `κS`, and if `(1-3κ)S ≤ u ≤ S`, then the kept matching removes a
`(γ ± 4κ)`-fraction of `S`. -/
theorem thinning_numeric {A S Y u κ γ : ℝ} (hA : A = S - Y)
    (hYdev : |Y - (1 - γ) * u| < κ * S) (hlow : (1 - 3 * κ) * S ≤ u) (hup : u ≤ S)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    |A - γ * S| ≤ 4 * κ * S := by
  rw [hA]
  have hkey : S - Y - γ * S = (1 - γ) * (S - u) - (Y - (1 - γ) * u) := by ring
  rw [hkey]
  have hb1 : 0 ≤ (1 - γ) * (S - u) := mul_nonneg (by linarith) (by linarith)
  have hb3 : (1 - γ) * (S - u) ≤ 3 * κ * S := by
    have h3 : S - u ≤ 3 * κ * S := by linarith
    calc (1 - γ) * (S - u) ≤ 1 * (S - u) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = S - u := one_mul _
      _ ≤ 3 * κ * S := h3
  calc |(1 - γ) * (S - u) - (Y - (1 - γ) * u)|
      ≤ |(1 - γ) * (S - u)| + |Y - (1 - γ) * u| := by
        have h := abs_add_le ((1 - γ) * (S - u)) (-(Y - (1 - γ) * u))
        rwa [abs_neg] at h
    _ = (1 - γ) * (S - u) + |Y - (1 - γ) * u| := by rw [abs_of_nonneg hb1]
    _ ≤ 3 * κ * S + κ * S := add_le_add hb3 (le_of_lt hYdev)
    _ = 4 * κ * S := by ring

/-! ## The thinning lemma -/

/-- **Thinning lemma (the second half of `cor:sparse_egj`).** Let `M₀` be a matching in a
hypergraph `𝓗` on `Fin n`, all of whose edges have size at most `r`, and let `(S a)_{a : σ}`
be a finite family of vertex sets with `|S a| ≥ D^{1/20}` and
`(1 - 3κ)·|S a| ≤ |S a ∩ V(M₀)|` for every `a`.  If `2·|σ|·exp(-(3/8)κ²D^{1/20}/r) < 1`
then there is a submatching `M ⊆ M₀` with `| |S a ∖ V(M)| - γ·|S a| | ≤ 4κ·|S a|` for
every `a`.

Proof (paper p. 503).  Keep each edge of `M₀` *independently* with probability `1-γ`.  For a
fixed `a` the random variable `X := |S a ∩ V(M)|` is a sum over the kept edges of the
independent terms `|S a ∩ e|`, each `≤ r`; hence `E X = (1-γ)·u` where
`u := |S a ∩ V(M₀)| ∈ [(1-3κ)|S a|, |S a|]`.  If `|X - (1-γ)|S a|| ≥ 4κ|S a|` then, since
`(1-γ)(|S a| - u) ≤ 3κ|S a|`, we get `|X - E X| ≥ κ|S a|`; the weighted Chernoff bound
`Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted`
(`Submission/Commons/Probability/Chernoff/chernoff_two_sided_finite_weighted.lean`, parameters
`C = r`, `∑ p_i X_i = E X ≤ |S a|`) bounds this by `2·exp(-(3/8)κ²|S a|/r) ≤
2·exp(-(3/8)κ²D^{1/20}/r)`.  The union bound over the `σ` sets gives a *positive-probability*
good outcome, so some outcome exists: this is the alteration/L¹ argument over the product
space `M₀ → Bool`, using the counting identity `|S ∩ ⋃_{i∈T} e_i| = ∑_{i∈T}|S ∩ e_i|` for
pairwise disjoint `e_i`. -/
theorem thinning {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (M₀ : Set 𝓗)
    (hM₀ : ErdosFaberLovaszConjecture.IsMatching 𝓗 M₀)
    (σ : Type) [Fintype σ] (S : σ → Set (Fin n))
    {κ γ D r : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 4) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hr : 0 < r) (hD1 : 1 ≤ D)
    (hsize : ∀ e ∈ M₀, ((ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n))) : ℝ) ≤ r)
    (hbig : ∀ a, D ^ ((1 : ℝ) / 20) ≤ ((S a).ncard : ℝ))
    (hlower : ∀ a, (1 - 3 * κ) * ((S a).ncard : ℝ) ≤
      ((S a ∩ ErdosFaberLovaszConjecture.matchVert M₀).ncard : ℝ))
    (hunion : 2 * (Fintype.card σ : ℝ) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) < 1) :
    ∃ M : Set 𝓗, M ⊆ M₀ ∧ ErdosFaberLovaszConjecture.IsMatching 𝓗 M ∧
      ∀ a, |(((S a) \ ErdosFaberLovaszConjecture.matchVert M).ncard : ℝ) - γ * ((S a).ncard : ℝ)|
        ≤ 4 * κ * ((S a).ncard : ℝ) := by
  classical
  haveI : Fintype ↥M₀ := Fintype.ofFinite _
  -- ## The edge family of `M₀`
  let E : ↥M₀ → Set (Fin n) := fun i => ((i.1 : 𝓗) : Set (Fin n))
  have hEdisj : Pairwise (fun i j : ↥M₀ => Disjoint (E i) (E j)) := by
    intro i j hij
    exact hM₀ i.2 j.2 (fun hc => hij (Subtype.ext hc))
  -- ## The two counting identities
  have hXsum : ∀ a : σ,
      (∑ i : ↥M₀, (((S a) ∩ E i).ncard : ℝ)) = (((S a) ∩ matchVert M₀).ncard : ℝ) := by
    intro a
    have h := ncard_inter_iUnion (S a) E hEdisj
    rw [matchVert_eq_iUnion]
    rw [← Nat.cast_sum, ← h]
  have hXsum_kept : ∀ (a : σ) (t : ↥M₀ → Bool),
      (((S a) ∩ matchVert (keptMatching M₀ t)).ncard : ℝ)
        = ∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0) := by
    intro a t
    have h := ncard_inter_iUnion_ite (S a) E hEdisj t
    rw [matchVert_keptMatching]
    rw [h, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ht : t i = true
    · rw [if_pos ht, if_pos ht]
    · rw [if_neg ht, if_neg ht]
      simp
  -- ## Elementary bounds on the sizes
  have hSa_pos : ∀ a : σ, 0 < ((S a).ncard : ℝ) := by
    intro a
    have h1 : (1 : ℝ) ≤ D ^ ((1 : ℝ) / 20) := Real.one_le_rpow hD1 (by norm_num)
    linarith [hbig a, h1]
  have hu_le : ∀ a : σ, ((S a ∩ matchVert M₀).ncard : ℝ) ≤ ((S a).ncard : ℝ) := by
    intro a
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left
  have hμ_le : ∀ a : σ,
      (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ)) ≤ ((S a).ncard : ℝ) := by
    intro a
    have h1 : (0 : ℝ) ≤ ((S a ∩ matchVert M₀).ncard : ℝ) := Nat.cast_nonneg _
    calc (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))
        = (1 - γ) * (∑ i : ↥M₀, (((S a) ∩ E i).ncard : ℝ)) := by rw [Finset.mul_sum]
      _ = (1 - γ) * ((S a ∩ matchVert M₀).ncard : ℝ) := by rw [hXsum a]
      _ ≤ 1 * ((S a ∩ matchVert M₀).ncard : ℝ) := mul_le_mul_of_nonneg_right (by linarith) h1
      _ = ((S a ∩ matchVert M₀).ncard : ℝ) := one_mul _
      _ ≤ ((S a).ncard : ℝ) := hu_le a
  have hμ_eq : ∀ a : σ, (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))
      = (1 - γ) * ((S a ∩ matchVert M₀).ncard : ℝ) := by
    intro a
    rw [← Finset.mul_sum, hXsum a]
  -- ## The product space and the bad events
  let P : Work.Deep.Prob.FinProbSpace (↥M₀ → Bool) :=
    Work.Deep.Prob.FinProbSpace.bernoulliConst (ι := ↥M₀) (1 - γ) (by linarith) (by linarith)
  let Bad : σ → Set (↥M₀ → Bool) := fun a =>
    {t | κ * ((S a).ncard : ℝ) ≤
      |(∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0)) -
        (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))|}
  -- ## Chernoff bound at a fixed `a`
  have hcher : ∀ a : σ, P.prob (Bad a) ≤
      2 * Real.exp (-(3 / 8) * κ ^ 2 * ((S a).ncard : ℝ) / r) := by
    intro a
    have hp0' : (0 : ℝ) ≤ 1 - γ := by linarith
    have hp1' : (1 : ℝ) - γ ≤ 1 := by linarith
    have hX0 : ∀ i : ↥M₀, 0 ≤ (((S a) ∩ E i).ncard : ℝ) := fun i => Nat.cast_nonneg _
    have hXC : ∀ i : ↥M₀, (((S a) ∩ E i).ncard : ℝ) ≤ r := by
      intro i
      have h1 : (((S a) ∩ E i).ncard : ℝ) ≤ ((E i).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_right : (S a) ∩ E i ⊆ E i)
      have h2 : ((E i).ncard : ℝ) ≤ r := by
        rw [← edgeSize_eq_ncard]
        exact hsize i.1 i.2
      linarith
    have ht : 0 ≤ κ * ((S a).ncard : ℝ) := mul_nonneg hκ0.le (Nat.cast_nonneg _)
    have hmain := Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
      (ι := ↥M₀) (p := fun _ : ↥M₀ => (1 - γ)) (hp0 := fun _ => hp0')
      (hp1 := fun _ => hp1') (X := fun i : ↥M₀ => (((S a) ∩ E i).ncard : ℝ))
      (hX0 := hX0) (C := r) (hC0 := hr.le) (hXC := hXC)
      (t := κ * ((S a).ncard : ℝ)) (ht := ht)
    have hglue := prob_bernoulliConst_abs (ι := ↥M₀) (p := 1 - γ) hp0' hp1'
      (fun t : ↥M₀ → Bool => ∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0))
      (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ)) (κ * ((S a).ncard : ℝ))
    have hbad_eq : Bad a = {t : ↥M₀ → Bool | κ * ((S a).ncard : ℝ) ≤
        |(∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0)) -
          (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))|} := rfl
    rw [hbad_eq, hglue]
    calc (∑ t : ↥M₀ → Bool, (∏ i, (if t i then 1 - γ else 1 - (1 - γ))) *
          (if κ * ((S a).ncard : ℝ) ≤
            |(∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0)) -
              (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))| then (1 : ℝ) else 0))
        ≤ 2 * Real.exp (-(κ * ((S a).ncard : ℝ)) ^ 2 /
            (2 * r * ((∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ)) +
              κ * ((S a).ncard : ℝ) / 3))) := hmain
      _ ≤ 2 * Real.exp (-(3 / 8) * κ ^ 2 * ((S a).ncard : ℝ) / r) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        rw [hμ_eq a]
        exact chernoff_exponent_le (S := ((S a).ncard : ℝ))
          (u := ((S a ∩ matchVert M₀).ncard : ℝ))
          hκ0 (by linarith) hr (hSa_pos a) (Nat.cast_nonneg _) (hu_le a) hγ0 hγ1
  -- ## The union bound
  have hsum_bad : (∑ a : σ, P.prob (Bad a)) < 1 := by
    have hstep : ∀ a : σ, P.prob (Bad a) ≤
        2 * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) := by
      intro a
      refine le_trans (hcher a) ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact exp_thinning_mono hr hκ0.le (hbig a)
    calc (∑ a : σ, P.prob (Bad a))
        ≤ ∑ a : σ, 2 * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) :=
          Finset.sum_le_sum (fun a _ => hstep a)
      _ = (Fintype.card σ : ℝ) * (2 * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 2 * (Fintype.card σ : ℝ) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / r)) := by
          ring
      _ < 1 := hunion
  -- ## A good outcome exists
  obtain ⟨t, ht⟩ := P.alteration Bad hsum_bad
  refine ⟨keptMatching M₀ t, keptMatching_subset t, hM₀.subset (keptMatching_subset t), ?_⟩
  intro a
  have hA := ncard_sdiff_matchVert (𝓗 := 𝓗) (M := keptMatching M₀ t) (S a)
  have hYdev : |((S a ∩ matchVert (keptMatching M₀ t)).ncard : ℝ) -
      (1 - γ) * ((S a ∩ matchVert M₀).ncard : ℝ)| < κ * ((S a).ncard : ℝ) := by
    rw [hXsum_kept a t, ← hXsum a, Finset.mul_sum]
    have h : ¬ (κ * ((S a).ncard : ℝ) ≤
        |(∑ i : ↥M₀, (if t i then (((S a) ∩ E i).ncard : ℝ) else 0)) -
          (∑ i : ↥M₀, (1 - γ) * (((S a) ∩ E i).ncard : ℝ))|) := ht a
    exact not_le.mp h
  exact thinning_numeric hA hYdev (hlower a) (hu_le a) hγ0 hγ1

end Work.Deep.Nibble
