import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.blockReduction
import Submission.Work.Drive.N2.blockSkeletonSmall
import Submission.Work.Drive.N2.windowDatumExists
import Submission.Work.Drive.N2.exists_globalLevelFlow_of_critical
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.exists_gapDrawings_of_certifiedWindows

/-!
# Tier E1: assembling the certified windows into the level-separating map

The coherent-window architecture of `Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md`
(§4, Tier E) closes the compact `n = 2` case by combining

* the value-axis skeleton `Work.Drive.N2.exists_blockSkeleton` (critical values `s`, separation `η`),
* one **certified window** at each critical value,
* the gap drawings `Work.Drive.N2C.exists_gapDrawings_of_certifiedWindows` (Tier C2), and
* `Work.Drive.N2.levelSeparatingMap_of_windows` (the block cover),

into a level-separating map `G : M → ℝ³`, which `Work.Drive.N2.embedding_of_levelSeparating` turns
into the target embedding `M ↪ ℝ⁴`.

This file performs the two remaining steps of that assembly:

* `Work.Drive.N2C.exists_criticalEnumVal` — the enumeration of the critical points *matched with the
  skeleton's values*: `f (p j) = s (Fin.castSucc j)`.  (`Work.Drive.N2.exists_criticalEnum` gives the
  enumeration without the matching, and the matching is *not* a consequence of its other rows — it
  has to be built by choosing the point of value `s (Fin.castSucc j)`.)
* `Work.Drive.N2C.levelSeparatingMap_of_certifiedWindows` — the certified windows (on the bands
  `Ioo (s j - 2η) (s j + 2η)`, certified at `s j ∓ 3η/2`) plus the skeleton/flow rows give the
  level-separating map.  The window rows are passed to `levelSeparatingMap_of_windows` after the
  inclusion `blockSet s η (j,1) ⊆ Ioo (s j - 2η) (s j + 2η)`, and the gap rows are exactly C2.
* `Work.Drive.N2C.exists_levelSeparatingMap_of_certifiedSupply` — the same, but starting from the
  *existence* of the certified windows at every critical point (the form in which Tier D, i.e.
  `Work.N2C.exists_certifiedWindow_extremum` and the saddle analogue, provides them): the skeleton,
  the critical-point enumeration, the datum and the window threshold are all produced here, and the
  separation constant `η` is shrunk to fit the thresholds.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The critical points matched with the skeleton's critical values.**

`Work.Drive.N2.exists_criticalEnum` produces an injective enumeration `p` of the critical points
covering all of them, but it does not record that `p j` is the point of value `s (Fin.castSucc j)`.
That matching is *not* a consequence of the other rows (any permutation of the critical points has
the same rows), so it must be produced by the choice: take `p j` to be a critical point of value
`s (Fin.castSucc j)`. -/
theorem exists_criticalEnumVal {f : M → ℝ} {n : ℕ} (s : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (hf : Work.Drive.Morse.IsMorseDistinct f)
    (hcrit : ∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔
      ∃ j : Fin n, t = s (Fin.castSucc j)) :
    ∃ p : Fin n → M,
      (∀ j : Fin n, Work.Drive.Morse.IsCritical f (p j) ∧ f (p j) = s (Fin.castSucc j)) ∧
      Function.Injective p ∧
      (∀ x : M, Work.Drive.Morse.IsCritical f x → ∃ j : Fin n, p j = x) := by
  have hex : ∀ j : Fin n, ∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = s (Fin.castSucc j) :=
    fun j => (hcrit (s (Fin.castSucc j))).2 ⟨j, rfl⟩
  let p : Fin n → M := fun j => Classical.choose (hex j)
  have hp : ∀ j : Fin n, Work.Drive.Morse.IsCritical f (p j) ∧ f (p j) = s (Fin.castSucc j) :=
    fun j => Classical.choose_spec (hex j)
  refine ⟨p, hp, ?_, ?_⟩
  · intro i j hij
    have hval : f (p i) = f (p j) := by rw [hij]
    have hsij : s (Fin.castSucc i) = s (Fin.castSucc j) := by
      rw [← (hp i).2, hval, (hp j).2]
    exact Fin.castSucc_inj.mp (hs.injective hsij)
  · intro x hx
    obtain ⟨j, hj⟩ := (hcrit (f x)).1 ⟨x, hx, rfl⟩
    exact ⟨j, (hf.2.2 x (p j) hx (hp j).1 (by rw [hj, (hp j).2])).symm⟩

/-- **The certified windows give the level-separating map.**  This is the assembly
`Work.Drive.N2.levelSeparatingMap_of_windows` with

* the window rows `hgw` (on the bands `Ioo (s j - 2η) (s j + 2η)`) restricted to the window blocks
  `blockSet s η (j,1) = Ioo (s j - 5η/8) (s j + 5η/8)`;
* the gap drawings and the two collar agreements supplied by the certified-window gap lemma
  `Work.Drive.N2C.exists_gapDrawings_of_certifiedWindows` (Tier C2), whose `hgw`/`hcertLo`/`hcertHi`
  hypotheses are exactly the certified windows. -/
theorem levelSeparatingMap_of_certifiedWindows [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] {n : ℕ} (hn : 0 < n) (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (η : ℝ) (hη : 0 < η)
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (u v : ℝ) (x : M), Φ (u, Φ (v, x)) = Φ (u + v, x))
    {K : Set M} (hKcl : IsClosed K)
    (hlaw : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ K) → f (Φ (t, y)) = f y + t)
    (hKval : ∀ y ∈ K, ∃ ℓ : Fin n, |f y - s (Fin.castSucc ℓ)| < η / 4)
    (hcrit : ∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔
      ∃ j : Fin n, t = s (Fin.castSucc j))
    (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (hgw : ∀ j : Fin n, Work.Drive.N2.GoodDrawingOn f
      (Set.Ioo (s (Fin.castSucc j) - 2 * η) (s (Fin.castSucc j) + 2 * η)) (gw j))
    (hcertLo : ∀ j : Fin n, IsCertifiedAt f (s (Fin.castSucc j) - 3 * η / 2) (gw j))
    (hcertHi : ∀ j : Fin n, IsCertifiedAt f (s (Fin.castSucc j) + 3 * η / 2) (gw j)) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  refine Work.Drive.N2.levelSeparatingMap_of_windows hn f hf s hs η hη hlo hhi hgap gw ?_ ?_
  · intro j
    refine (hgw j).mono ?_
    rw [Work.Drive.N2.blockSet_one]
    intro t ht
    exact ⟨by linarith [ht.1, hη], by linarith [ht.2, hη]⟩
  · exact exists_gapDrawings_of_certifiedWindows hn hf.1 hf hs hη hgap hlo hhi hΦsm hΦ0 hΦcomp
      hKcl hlaw hKval hcrit gw hgw hcertLo hcertHi

/-- **Tier E1: the level-separating map from a certified window supply.**

The single geometric input is `hwin`: at *every* critical point `p`, presented by a window datum `D`,
and for every half-width below a threshold, there is a drawing `W` of the band
`Ioo (f p - 2η) (f p + 2η)` which is good and certified at the two levels `f p ∓ 3η/2`.  That is
exactly the shape of the Tier D lemmas `Work.N2C.exists_certifiedWindow_extremum` (extremum case)
and its saddle analogue, whose `windowDatumExists`-produced datum is all they need.

Everything else is produced here: the skeleton, the critical-point enumeration matched with the
skeleton's values, one datum per critical point, the window at the shrunken separation constant, and
the global level flow (`Work.Drive.N2.exists_globalLevelFlow_of_critical`). -/
theorem exists_levelSeparatingMap_of_certifiedSupply [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [Nonempty M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (hmorse : Work.Drive.Morse.MorseLemma2)
    (hwin : ∀ (p : M) (D : Work.Drive.N2.WindowDatum f p),
      ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η' : ℝ, 0 < η' → η' ≤ η₁ →
        ∃ W : M → EuclideanSpace ℝ (Fin 3),
          Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η') (f p + 2 * η')) W ∧
          IsCertifiedAt f (f p - 3 * η' / 2) W ∧ IsCertifiedAt f (f p + 3 * η' / 2) W) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  classical
  obtain ⟨n, hn, s, η, hs, hη, _hη1, hgap, hcrit, hrange⟩ :=
    Work.Drive.N2.exists_blockSkeleton f hf
  obtain ⟨p, hp, hpinj, hpcover⟩ := exists_criticalEnumVal s hs hf hcrit
  -- one window datum at every critical point
  have hdat : ∀ j : Fin n, Nonempty (Work.Drive.N2.WindowDatum f (p j)) :=
    fun j => Work.Drive.N2.windowDatumExists f hf hmorse (hp j).1
  let D : ∀ j : Fin n, Work.Drive.N2.WindowDatum f (p j) :=
    fun j => Classical.choice (hdat j)
  -- the threshold of the certified window at each critical point
  have hthr : ∀ j : Fin n, ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η' : ℝ, 0 < η' → η' ≤ η₁ →
      ∃ W : M → EuclideanSpace ℝ (Fin 3),
        Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f (p j) - 2 * η') (f (p j) + 2 * η')) W ∧
        IsCertifiedAt f (f (p j) - 3 * η' / 2) W ∧ IsCertifiedAt f (f (p j) + 3 * η' / 2) W :=
    fun j => hwin (p j) (D j)
  choose η₁ hrow using hthr
  -- the finite minimum of the thresholds
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let c : ℝ := (Finset.univ : Finset (Fin n)).inf' hne η₁
  have hcpos : 0 < c := by
    change 0 < (Finset.univ : Finset (Fin n)).inf' hne η₁
    exact (Finset.lt_inf'_iff hne).mpr (fun j _ => (hrow j).1)
  have hcle : ∀ j : Fin n, c ≤ η₁ j := fun j => by
    change (Finset.univ : Finset (Fin n)).inf' hne η₁ ≤ η₁ j
    exact Finset.inf'_le η₁ (Finset.mem_univ j)
  -- shrink the skeleton to the smallest threshold
  obtain ⟨hs', hη'pos, hgap', hcrit', hrange'⟩ :=
    Work.Drive.N2.blockSkeleton_shrink hn hs hη hgap hcrit hrange (lt_min hη hcpos)
      (min_le_left _ _)
  -- the windows at the shrunken constant
  let gw : Fin n → M → EuclideanSpace ℝ (Fin 3) := fun j =>
    Classical.choose ((hrow j).2 (min η c) (lt_min hη hcpos)
      (le_trans (min_le_right _ _) (hcle j)))
  have hgw0 : ∀ j : Fin n, Work.Drive.N2.GoodDrawingOn f
      (Set.Ioo (f (p j) - 2 * min η c) (f (p j) + 2 * min η c)) (gw j) := fun j =>
    (Classical.choose_spec ((hrow j).2 (min η c) (lt_min hη hcpos)
      (le_trans (min_le_right _ _) (hcle j)))).1
  have hcertLo0 : ∀ j : Fin n, IsCertifiedAt f (f (p j) - 3 * min η c / 2) (gw j) := fun j =>
    (Classical.choose_spec ((hrow j).2 (min η c) (lt_min hη hcpos)
      (le_trans (min_le_right _ _) (hcle j)))).2.1
  have hcertHi0 : ∀ j : Fin n, IsCertifiedAt f (f (p j) + 3 * min η c / 2) (gw j) := fun j =>
    (Classical.choose_spec ((hrow j).2 (min η c) (lt_min hη hcpos)
      (le_trans (min_le_right _ _) (hcle j)))).2.2
  have hgw : ∀ j : Fin n, Work.Drive.N2.GoodDrawingOn f
      (Set.Ioo (s (Fin.castSucc j) - 2 * min η c) (s (Fin.castSucc j) + 2 * min η c)) (gw j) := by
    intro j
    rw [← (hp j).2]
    exact hgw0 j
  have hcertLo : ∀ j : Fin n, IsCertifiedAt f (s (Fin.castSucc j) - 3 * min η c / 2) (gw j) := by
    intro j
    rw [← (hp j).2]
    exact hcertLo0 j
  have hcertHi : ∀ j : Fin n, IsCertifiedAt f (s (Fin.castSucc j) + 3 * min η c / 2) (gw j) := by
    intro j
    rw [← (hp j).2]
    exact hcertHi0 j
  -- the global level flow
  obtain ⟨Φ, K, hΦsm, hΦ0, hΦcomp, hKcl, hKval0, hlaw⟩ :=
    Work.Drive.N2.exists_globalLevelFlow_of_critical f hf hmorse p (fun j => (hp j).1) hpinj hpcover
      (ε := min η c / 4) (by linarith [lt_min hη hcpos])
  have hKval : ∀ y ∈ K, ∃ ℓ : Fin n, |f y - s (Fin.castSucc ℓ)| < min η c / 4 := by
    intro y hy
    obtain ⟨j, hj⟩ := hKval0 y hy
    exact ⟨j, by rw [← (hp j).2]; exact hj⟩
  exact levelSeparatingMap_of_certifiedWindows hn f hf s hs' (min η c) (lt_min hη hcpos)
    (fun j => by have h := hgap' j; linarith) (fun x => (hrange' x).1) (fun x => (hrange' x).2)
    hΦsm hΦ0 hΦcomp hKcl hlaw hKval hcrit' gw hgw hcertLo hcertHi

/-- **Tier E1, final form: the level-separating map of the compact `n = 2` case from the two window
lemmas.**

The two geometric inputs are the extremum window (`hX`, i.e.
`Work.N2C.exists_certifiedWindow_extremum`) and the saddle window (`hS`, D2), both of which are
statements about a `Work.Drive.N2.WindowDatum f p` at a critical point `p` with the two signs `s₁`,
`s₂` equal (resp. distinct) at the marked index.  The empty manifold is handled separately: then any
map `M → ℝ³` is a level-separating map. -/
theorem exists_levelSeparatingMap_of_certifiedCases [T2Space M] [SecondCountableTopology M]
    [CompactSpace M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f)
    (hmorse : Work.Drive.Morse.MorseLemma2)
    (hX : ∀ (p : M) (D : Work.Drive.N2.WindowDatum f p), D.s₁ D.j = D.s₂ D.j →
      ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η' : ℝ, 0 < η' → η' ≤ η₁ →
        ∃ W : M → EuclideanSpace ℝ (Fin 3),
          Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η') (f p + 2 * η')) W ∧
          IsCertifiedAt f (f p - 3 * η' / 2) W ∧ IsCertifiedAt f (f p + 3 * η' / 2) W)
    (hS : ∀ (p : M) (D : Work.Drive.N2.WindowDatum f p), D.s₁ D.j ≠ D.s₂ D.j →
      ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η' : ℝ, 0 < η' → η' ≤ η₁ →
        ∃ W : M → EuclideanSpace ℝ (Fin 3),
          Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η') (f p + 2 * η')) W ∧
          IsCertifiedAt f (f p - 3 * η' / 2) W ∧ IsCertifiedAt f (f p + 3 * η' / 2) W) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  by_cases hM : Nonempty M
  · haveI := hM
    refine exists_levelSeparatingMap_of_certifiedSupply f hf hmorse (fun p D => ?_)
    by_cases h : D.s₁ D.j = D.s₂ D.j
    · exact hX p D h
    · exact hS p D h
  · haveI : IsEmpty M := ⟨fun x => hM ⟨x⟩⟩
    exact ⟨fun _ => 0, contMDiff_const, fun x => isEmptyElim x, fun x => isEmptyElim x⟩

end Work.Drive.N2C
