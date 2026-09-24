import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn
import Submission.Work.Drive.isPreconnected_sdiff_finite
import Submission.Work.SimplyConnected.ABS.harnackReach
import Submission.Work.Drive.greenExhaustion_parabolicCase

/-!
# The normalised Green functions of an exhaustion are locally bounded off the pole

This is the classical theorem (Ahlfors, *Conformal invariants*, Ch. 10, the parabolic case of
uniformization; Hubbard, *Teichmüller theory* Vol. 1, Ch. 1).  `Ω` is an exhaustion of the surface
by nested relatively compact open sets with `⋃ Ω n = univ`, each carrying a Green function `G n`
with pole `a` (`Work.SimplyConnected.ABS.IsGreenOn`, extended by `0` off `Ω n`); the claim is that
`G n · - G n x₁` is uniformly bounded on every compact `K` disjoint from the pole.

The proof splits on whether the family `{G n}` is bounded at one point off the pole.

* **Bounded case** (`∃ x₀ ≠ a, ∃ C, ∀ n, G n x₀ ≤ C`), proved here as
  `Work.Drive.greenExhaustion_hyperbolicCase`.  Fix `N` with `K ∪ {x₁} ∪ {x₀} ⊆ Ω N` and put
  `U := Ω N \ {a}`, which is open and preconnected: either `Ω N = univ`, or `Ω N ≠ univ` and `Ω N`
  is preconnected by `Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn`; in both cases removing
  the single point `a` keeps it preconnected (`Work.Drive.isPreconnected_sdiff_finite`).  For
  `n ≥ N` the function `G n` is non-negative and harmonic on `U`, so the uniform Harnack bound on a
  compact subset of a preconnected open set
  (`Work.SimplyConnected.ABS.harnack_uniform_bound_of_preconnected`) gives
  `|G n x - G n x₁| ≤ 2 · 25 ^ m · G n x₀ ≤ 2 · 25 ^ m · C` for every `x ∈ K`.  The finitely many
  `n < N` contribute a finite bound: `G n` lies in `Ω n \ {a}` on `K ∩ Ω n` (where it is harmonic,
  hence continuous) and vanishes on `K \ Ω n`.

* **Unbounded case** (`∀ x ≠ a, ∀ C, ∃ n, C < G n x`).  This is the classical parabolic case of
  Ahlfors (Ch. 10): the normalised Green functions of an exhaustion of a parabolic surface converge
  locally uniformly, hence are in particular locally bounded.  This half is
  `Work.Drive.greenExhaustion_parabolicCase`.

The dichotomy is a pure case split: if the family is *not* bounded at any point off the pole, then
it is unbounded at every point off the pole.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace Work.Drive

/-- A compact set contained in a monotone union of open sets is contained in one member. -/
theorem exists_subset_iUnion_of_isCompact' {X : Type*} [TopologicalSpace X] {Ω : ℕ → Set X}
    (hΩo : ∀ n, IsOpen (Ω n)) (hmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ)
    {K : Set X} (hK : IsCompact K) : ∃ N : ℕ, K ⊆ Ω N := by
  classical
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩo (by rw [hcov]; exact subset_univ K)
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (ht hx)
    exact absurd hi (Finset.notMem_empty i)
  · exact ⟨t.max' hne, fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact hmono' i (t.max' hne) (Finset.le_max' t i hi) hxi⟩

/-- `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_abs_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The hyperbolic (bounded) case of the local boundedness of the normalised exhaustion Green
functions.**  See the module docstring for the proof. -/
theorem greenExhaustion_hyperbolicCase {a x₁ : X} (hx₁ : x₁ ≠ a) {Ω : ℕ → Set X}
    {G : ℕ → X → ℝ}
    (hΩopen : ∀ n, IsOpen (Ω n)) (hΩcomp : ∀ n, IsCompact (closure (Ω n)))
    (hΩmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hΩcover : (⋃ n, Ω n) = Set.univ)
    (hgreen : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hvanish : ∀ n, ∀ x, x ∉ Ω n → G n x = 0)
    (hbdd : ∃ x₀ : X, x₀ ≠ a ∧ ∃ C : ℝ, ∀ n, G n x₀ ≤ C) :
    ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
      |G n x - G n x₁| ≤ C := by
  classical
  obtain ⟨x₀, hx₀a, C₀, hC₀⟩ := hbdd
  intro K hK hKa
  -- a compact set containing `K`, `x₁`, `x₀` and `a`
  have hKcomp : IsCompact (K ∪ ({x₁, x₀, a} : Set X)) :=
    hK.union (Set.Finite.isCompact
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))))
  obtain ⟨N, hN⟩ := exists_subset_iUnion_of_isCompact' hΩopen hΩmono hΩcover hKcomp
  have hx₁_sub : x₁ ∈ Ω N := hN (Or.inr (by simp))
  have hx₀_sub : x₀ ∈ Ω N := hN (Or.inr (by simp))
  have hK_sub : K ⊆ Ω N := fun x hx => hN (Or.inl hx)
  -- the preconnected open set `U := Ω N \ {a}`
  have hUopen : IsOpen (Ω N \ {a}) := (hΩopen N).sdiff isClosed_singleton
  have hUpre : IsPreconnected (Ω N \ {a}) := by
    rcases eq_or_ne (Ω N) Set.univ with hU | hU
    · rw [hU]
      exact Work.Drive.isPreconnected_sdiff_finite isOpen_univ isPreconnected_univ {a}
        (Set.finite_singleton a)
    · exact Work.Drive.isPreconnected_sdiff_finite (hΩopen N)
        (Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn (hΩopen N) hU (hgreen N)) {a}
        (Set.finite_singleton a)
  have hx₀U : x₀ ∈ Ω N \ {a} := ⟨hx₀_sub, by simpa using hx₀a⟩
  have hx₁U : x₁ ∈ Ω N \ {a} := ⟨hx₁_sub, fun h => hx₁ h⟩
  have hKU : K ⊆ Ω N \ {a} := fun x hx => ⟨hK_sub hx, (hKa hx).2⟩
  have hK1comp : IsCompact (K ∪ {x₁}) := hK.union (Set.finite_singleton x₁).isCompact
  have hK1U : K ∪ {x₁} ⊆ Ω N \ {a} := by
    intro x hx
    rcases hx with hx | hx
    · exact hKU hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hx₁U
  obtain ⟨m, hm⟩ := Work.SimplyConnected.ABS.harnack_uniform_bound_of_preconnected hUopen hUpre
    hx₀U hK1comp hK1U
  have hpow : (0 : ℝ) ≤ 25 ^ m := by positivity
  -- uniform bound for the tail `n ≥ N`
  have htail : ∀ n ≥ N, ∀ x ∈ K, |G n x - G n x₁| ≤ 2 * 25 ^ m * C₀ := by
    intro n hn x hxK
    have hΩsub : Ω N ⊆ Ω n := by
      have hmono' : ∀ k : ℕ, Ω N ⊆ Ω (N + k) := by
        intro k
        induction k with
        | zero => simpa using subset_rfl
        | succ j ih =>
            have h' : Ω (N + j) ⊆ Ω (N + (j + 1)) := by
              rw [Nat.add_succ]; exact hΩmono (N + j)
            exact ih.trans h'
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact hmono' k
    have hharm : Submission.HarmonicOnX (G n) (Ω N \ {a}) := by
      intro y hy
      exact (hgreen n).2.1 y ⟨hΩsub hy.1, hy.2⟩
    have hpos : ∀ y ∈ Ω N \ {a}, 0 ≤ G n y := by
      intro y hy
      exact le_of_lt ((hgreen n).1 y (hΩsub hy.1) hy.2)
    have h1 := (hm x (Or.inl hxK) (G n) hharm hpos).1
    have h2 := (hm x₁ (Or.inr rfl) (G n) hharm hpos).1
    have hnonneg : 0 ≤ G n x₀ := le_of_lt ((hgreen n).1 x₀ (hΩsub hx₀_sub) hx₀a)
    have hbx : 0 ≤ G n x := hpos x (hKU hxK)
    have hbx₁ : 0 ≤ G n x₁ := hpos x₁ hx₁U
    calc |G n x - G n x₁| ≤ |G n x| + |G n x₁| := abs_sub_le_abs_add' _ _
      _ = G n x + G n x₁ := by rw [abs_of_nonneg hbx, abs_of_nonneg hbx₁]
      _ ≤ 25 ^ m * G n x₀ + 25 ^ m * G n x₀ := add_le_add h1 h2
      _ = 2 * 25 ^ m * G n x₀ := by ring
      _ ≤ 2 * 25 ^ m * C₀ := by
          have hle := hC₀ n
          nlinarith [hpow, hnonneg, hle]
  -- finite bound for the head `n < N`
  have hsingle : ∀ n : ℕ, ∃ B : ℝ, ∀ x ∈ K, |G n x - G n x₁| ≤ B := by
    intro n
    obtain ⟨Kc, hKccomp, hKcΩ, hKc⟩ := (hgreen n).2.2.1 1 one_pos
    have hKc' : ∀ x ∈ Ω n, 1 ≤ G n x → x ∈ Kc := by
      intro x hxΩ hxge
      by_contra hxKc
      exact absurd hxge (not_le.mpr (hKc x hxΩ hxKc))
    have hcont : ContinuousOn (G n) (K ∩ Kc) := by
      intro y hy
      have hyΩ : y ∈ Ω n := hKcΩ hy.2
      have hya : y ≠ a := fun h => (hKa hy.1).2 h
      exact (((hgreen n).2.1 y ⟨hyΩ, hya⟩).continuousAt).continuousWithinAt
    obtain ⟨b, hb⟩ := (hK.inter_right hKccomp.isClosed).exists_bound_of_continuousOn hcont
    have hb' : ∀ x ∈ K ∩ Kc, G n x ≤ b := fun x hx =>
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb x hx)
    refine ⟨max 1 b + |G n x₁|, fun x hxK => ?_⟩
    by_cases hxΩ : x ∈ Ω n
    · have hxpos : 0 ≤ G n x := le_of_lt ((hgreen n).1 x hxΩ (fun h => (hKa hxK).2 h))
      have hle : G n x ≤ max 1 b := by
        by_cases hge : 1 ≤ G n x
        · exact le_trans (hb' x ⟨hxK, hKc' x hxΩ hge⟩) (le_max_right _ _)
        · exact le_trans (le_of_lt (lt_of_not_ge hge)) (le_max_left _ _)
      calc |G n x - G n x₁| ≤ |G n x| + |G n x₁| := abs_sub_le_abs_add' _ _
        _ = G n x + |G n x₁| := by rw [abs_of_nonneg hxpos]
        _ ≤ max 1 b + |G n x₁| := add_le_add hle le_rfl
    · have hx0 : G n x = 0 := hvanish n x hxΩ
      rw [hx0, zero_sub, abs_neg]
      exact le_add_of_nonneg_left (le_trans zero_le_one (le_max_left 1 b))
  choose B hB using hsingle
  by_cases hN0 : N = 0
  · refine ⟨2 * 25 ^ m * C₀, fun n x hxK => ?_⟩
    exact htail n (by omega) x hxK
  · have hne : (Finset.range N).Nonempty :=
      ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hN0)⟩
    refine ⟨max (2 * 25 ^ m * C₀) ((Finset.range N).sup' hne B),
      fun n x hxK => ?_⟩
    by_cases hn : n < N
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
      exact le_trans (hB n x hxK) (le_trans (Finset.le_sup' B hmem) (le_max_right _ _))
    · exact le_trans (htail n (by omega) x hxK) (le_max_left _ _)

/-- **The normalised Green functions of an exhaustion are locally bounded off the pole.**

This is the classical theorem (Ahlfors, *Conformal invariants*, Ch. 10, the parabolic case of
uniformization; Hubbard, *Teichmüller theory* Vol. 1, Ch. 1).  `Ω` is an exhaustion of the surface by
nested relatively compact open sets with `⋃ Ω n = univ`, each carrying a Green function `G n` with
pole `a` (`Work.SimplyConnected.ABS.IsGreenOn`, extended by `0` off `Ω n`); the claim is that
`G n · - G n x₁` is uniformly bounded on every compact `K` disjoint from the pole.

Route.  Fix `m` so that `K ∪ {x₁} ⊆ Ω m` and put `D n := G n - G m` for `n ≥ m`, harmonic on `Ω m`
(the two poles cancel, and `D n` is bounded near `a`, hence extends across `a`) and positive.  For
`x ∈ K` one has `(G n x - G n x₁) - (G m x - G m x₁) = D n x - D n x₁`, so it suffices to bound
`|D n x - D n x₁|` uniformly in `n ≥ m`.

The proof is a case split.  If the family `{G n}` is bounded at one point off the pole, the uniform
Harnack bound on a preconnected neighbourhood of `K ∪ {x₁}` gives the result
(`Work.Drive.greenExhaustion_hyperbolicCase`).  Otherwise the family is unbounded at every point off
the pole and the classical parabolic case (`Work.Drive.greenExhaustion_parabolicCase`) applies. -/
theorem normalizedGreenExhaustion_locallyBounded {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a x₁ : X} (hx₁ : x₁ ≠ a) {Ω : ℕ → Set X} {G : ℕ → X → ℝ}
    (hΩopen : ∀ n, IsOpen (Ω n)) (hΩcomp : ∀ n, IsCompact (closure (Ω n)))
    (hΩmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hΩcover : (⋃ n, Ω n) = Set.univ)
    (hgreen : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hvanish : ∀ n, ∀ x, x ∉ Ω n → G n x = 0) :
    ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
      |G n x - G n x₁| ≤ C := by
  classical
  by_cases hbdd : ∃ x₀ : X, x₀ ≠ a ∧ ∃ C : ℝ, ∀ n, G n x₀ ≤ C
  · exact greenExhaustion_hyperbolicCase hx₁ hΩopen hΩcomp hΩmono hΩcover hgreen hvanish hbdd
  · refine greenExhaustion_parabolicCase hx₁ hΩopen hΩcomp hΩmono hΩcover hgreen hvanish
      (fun x hx C => ?_)
    by_contra hcon
    push_neg at hcon
    exact hbdd ⟨x, hx, C, hcon⟩

end Work.Drive
