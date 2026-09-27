import Mathlib
import Submission.Work.Whitney.InsertedDoublePoint
import Submission.Work.Whitney.clean_region_of_arcs
import Submission.Work.Whitney.exists_disjoint_arcs_avoiding_finite
import Submission.Work.Whitney.ncard_doubleSet_cancel
import Submission.Work.Whitney.EndgameAux

/-!
# The reduction of the double point count, abstractly

This file isolates the **assembly** of the Whitney endgame from its two geometric inputs, so that
the combinatorics -- and in particular the *bookkeeping of the invariants* ("every double point is
simple", "every double point is transverse") -- can be checked independently of the (large) local
constructions.

The two invariants are

* `Work.Whitney.SimpleDP f` -- every double point of `f` has exactly two preimages;
* `Work.Whitney.TransDP A f` -- every double point of `f` is transverse, certified by two charts of
  the oriented atlas `A` whose `pairDet` does not vanish.

The interfaces:

* `Work.Whitney.HasInsertion` -- the *insertion* step: from a smooth immersion `f` with finitely
  many double points, an oriented atlas `A`, and a **simple** double point `(p₁,p₂)`, produce `f'`
  and a new double point `(p',q')` of the opposite sign (`Work.Whitney.InsertedDoublePoint`), and
  show that the two invariants are *preserved*.  The construction is
  `Work.Whitney.exists_insertedDoublePoint` (see
  `Submission/Work/Whitney/exists_insertedDoublePoint.lean`); the preservation of the invariants
  uses that the insertion is supported in a chart ball that can be chosen to avoid the finite set
  of preimages of the double points (`Work.Whitney.pairDet_congr`).

* `Work.Whitney.HasCancellation` -- the *cancellation* step (Whitney's trick,
  `Work.Whitney.cancel_double_points_oriented`): two transverse double points of opposite signs
  joined by a bigon inside a clean region `W` are removed.  The extra clause -- that the modified
  map has the same `pairDet` as the old one *at every pair of points outside `W`* -- is what makes
  the transversality of the *remaining* double points survive the modification; it holds because
  the push is a diffeomorphism of the target which is the identity near the image of the frontier
  of the collar (so the modification is "first order the identity" off `W`).

The main theorem `Work.Whitney.exists_reduce_double_points` combines the two: a simple transverse
double point is removed together with a freshly inserted partner of opposite sign, `ncard` drops by
`2`, and both invariants are preserved.  This is exactly what the iteration
(`Work.Whitney.exists_embedding_of_reduce`, in `endgame_abstract.lean`) consumes.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **Every double point of `f` has exactly two preimages.** -/
def SimpleDP {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  ∀ p : M × M, p ∈ doubleSet f → ∀ z : M, f z = f p.1 → z = p.1 ∨ z = p.2

/-- **Every double point of `f` is transverse**, certified by two charts of the oriented atlas
`A`. -/
def TransDP {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  ∀ p : M × M, p ∈ doubleSet f →
    ∃ c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      c₁ ∈ A ∧ c₂ ∈ A ∧ p.1 ∈ c₁.source ∧ p.2 ∈ c₂.source ∧
        pairDet f c₁ c₂ p.1 p.2 ≠ 0

/-- **An oriented atlas whose charts are genuine smooth charts.**  `Work.Whitney.IsOrientedAtlas`
alone only says that the pairwise transitions have *positive* determinant: it may be witnessed by
partial homeomorphisms that are not compatible with the smooth structure (for instance `x ↦ x³` on
`ℝ`), and then the chart representations `f ∘ c.symm` of a smooth `f` need not be differentiable --
which would make the `pairDet`-based sign statements meaningless.  All the interfaces below
therefore ask for an atlas of *smooth* charts. -/
def IsSmoothOrientedAtlas {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))) : Prop :=
  IsOrientedAtlas A ∧
  ∀ c ∈ A, (∀ x : M, x ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c x) ∧
    (∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)

/-- **The interface of the insertion step.**  Proposition-valued so that it can be passed around as
a hypothesis; the actual construction is `Work.Whitney.exists_insertedDoublePoint`. -/
def HasInsertion (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (doubleSet f).Finite)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (hsimple : SimpleDP f) (htrans : TransDP A f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂),
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      InsertedDoublePoint f A p₁ p₂ f' p' q' ∧ SimpleDP f' ∧ TransDP A f'

/-- **The interface of the cancellation step** (Whitney's trick), verbatim from
`Work.Whitney.cancel_double_points_oriented`, with the additional clause that the modification is
the identity on `pairDet` off the clean region `W`. -/
def HasCancellation (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : OppositeSign A f p₁ p₂ q₁ q₂),
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f' ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f' y)) ∧
      (∀ y : M, y ∉ W → f' y = f y) ∧
      doubleSet f' = doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} ∧
      (∀ (u v : M), u ∉ W → v ∉ W →
        ∀ (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
          u ∈ c₁.source → v ∈ c₂.source →
          pairDet f' c₁ c₂ u v = pairDet f c₁ c₂ u v)

/-- **The reduction step of the Whitney endgame.**  A simple transverse double point `(p₁,p₂)` of
a smooth immersion `f` of a compact connected `n`-manifold (`n ≥ 3`) into `ℝ^{2n}` can be removed,
together with a freshly inserted partner of opposite sign, lowering the cardinality of the double
point set by exactly `2` and preserving the simplicity and the transversality of all the remaining
double points. -/
theorem exists_reduce_double_points {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hins : HasInsertion n M) (hcancel : HasCancellation n M)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (doubleSet f).Finite)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (hsimple : SimpleDP f) (htrans : TransDP A f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂) :
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f'' ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f'' y)) ∧
      (doubleSet f'').Finite ∧
      (doubleSet f'').ncard + 2 = (doubleSet f).ncard ∧
      SimpleDP f'' ∧ TransDP A f'' := by
  classical
  -- ## Step 1: insert a double point of the opposite sign at a clean point.
  obtain ⟨f', p', q', hins', hsimple', htrans'⟩ :=
    hins f hf himm hfin A hA hsimple htrans p₁ p₂ hp₁p₂ hfp
  have hf'c := hins'.contMDiff
  have hf'imm := hins'.injective_mfderiv
  have hds := hins'.doubleSet_eq
  have hsign := hins'.oppositeSign
  have hf'fin := hins'.finite_doubleSet
  have hnewold := hins'.new_not_old
  obtain ⟨hp'q', hp'p₁, hp'p₂, hq'p₁, hq'p₂, -⟩ := hins'.distinct
  -- `(p₁,p₂)` and `(p',q')` are double points of `f'`
  have hmem₁₂ : (p₁, p₂) ∈ doubleSet f' := by
    rw [hds]; left; rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩
  have hmem' : (p', q') ∈ doubleSet f' := by rw [hds]; right; simp
  have hfp' : f' p₁ = f' p₂ := (mem_doubleSet.mp hmem₁₂).2
  have hfq' : f' p' = f' q' := (mem_doubleSet.mp hmem').2
  -- simplicity of `f'` at the two special values
  have hs₁ : ∀ z : M, f' z = f' p₁ → z = p₁ ∨ z = p₂ := fun z hz => hsimple' _ hmem₁₂ z hz
  have hs₂ : ∀ z : M, f' z = f' p' → z = p' ∨ z = q' := fun z hz => hsimple' _ hmem' z hz
  -- the finite set of double point preimages of `f'`
  set D : Set M := {y : M | ∃ z : M, z ≠ y ∧ f' z = f' y} with hDdef
  have hDmem : ∀ y : M, y ∈ D ↔ ∃ z : M, z ≠ y ∧ f' z = f' y := fun y => Iff.rfl
  have hDfin : D.Finite := by
    have h1 : D = Prod.fst '' (doubleSet f') := by
      ext y
      constructor
      · rintro ⟨z, hzy, hfz⟩
        exact ⟨(y, z), ⟨hzy.symm, hfz.symm⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw.1.symm, hw.2.symm⟩
    rw [h1]
    exact hf'fin.image Prod.fst
  have hp₁D : p₁ ∈ D := (hDmem p₁).mpr ⟨p₂, hp₁p₂.symm, hfp'.symm⟩
  have hp₂D : p₂ ∈ D := (hDmem p₂).mpr ⟨p₁, hp₁p₂, hfp'⟩
  have hp'D : p' ∈ D := (hDmem p').mpr ⟨q', hp'q'.symm, hfq'.symm⟩
  have hq'D : q' ∈ D := (hDmem q').mpr ⟨p', hp'q', hfq'⟩
  -- ## Step 2: the two arcs of the bigon, avoiding all other double points.
  obtain ⟨γ₁, γ₂, hγ₁c, hγ₂c, hγ₁0, hγ₁1, hγ₂0, hγ₂1, hγ₁inj, hγ₂inj,
    hγ₁D, hγ₂D, hγdisj⟩ :=
    exists_disjoint_arcs_avoiding_finite (n := n) hn D hDfin p₁ p₂ p' q'
      hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
  -- the endpoints are the only points of the arcs which lie in `D`
  have hend₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p₁ → t = 0 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₁D
    rcases hγ₁D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₁1] at h
      exact hp'p₁ h
  have hend₁' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p' → t = 1 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp'D
    rcases hγ₁D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₁0] at h
      exact hp'p₁ h.symm
    · exact h1
  have hne₁p₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ p₂ := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hp₁p₂ h
    · subst h1; rw [hγ₁1] at h; exact hp'p₂ h
  have hne₁q' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ q' := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hq'p₁ h.symm
    · subst h1; rw [hγ₁1] at h; exact hp'q' h
  have hend₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = p₂ → t = 0 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₂D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₂1] at h
      exact hq'p₂ h
  have hend₂' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = q' → t = 1 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₂D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₂0] at h
      exact hq'p₂ h.symm
    · exact h1
  -- ## Step 3: the clean region containing the arcs.
  obtain ⟨W, hWopen, hWcpt, hW₁, hW₂, hW₃, hW₄, hWchar, hWclean, hWsep, _⟩ :=
    exists_clean_region f' hf'fin p₁ p₂ p' q'
      hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq'
      (fun z hz => hs₁ z hz) (fun z hz => hs₂ z hz)
  -- ## Step 4: the arcs lie in the clean region.
  have hmemW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₁0]; exact hW₁
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₁1]; exact hW₃
    have hnotD : γ₁ t ∉ D := by
      intro hD
      rcases hγ₁D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (by simpa [hDmem] using hnotD)
  have hmemW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₂0]; exact hW₂
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₂1]; exact hW₄
    have hnotD : γ₂ t ∉ D := by
      intro hD
      rcases hγ₂D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (by simpa [hDmem] using hnotD)
  -- ## Step 5: the two image arcs meet only in the two double points (`hγend`).
  have hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f' (γ₁ s) = f' (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s hs t ht heq
    rcases hWclean (γ₁ s) (γ₂ t) (hmemW s hs) (hmemW₂ t ht) heq with
      h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hγdisj s hs t ht h
    · exact Or.inl ⟨hend₁ s hs h1, hend₂ t ht h2⟩
    · exact absurd h1 (hne₁p₂ s hs)
    · exact Or.inr ⟨hend₁' s hs h1, hend₂' t ht h2⟩
    · exact absurd h1 (hne₁q' s hs)
  -- ## Step 6: cancel the pair `((p₁,p₂), (p',q'))`.
  obtain ⟨f'', hf''c, hf''imm, hout, hds'', hagree⟩ :=
    hcancel hn f' hf'c hf'imm A hA W hWopen hWcpt p₁ p₂ p' q'
      hW₁ hW₂ hW₃ hW₄ hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
      hfp' hfq' hWclean hWsep γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hmemW hmemW₂ hγ₁inj hγ₂inj hγdisj hγend hsign
  -- ## Step 7: the invariants survive.
  have hsub : doubleSet f'' ⊆ doubleSet f' := by rw [hds'']; exact Set.sdiff_subset
  have hsimple'' : SimpleDP f'' := by
    intro p hp z hz
    by_cases hzp : z = p.1
    · exact Or.inl hzp
    have hmem : (z, p.1) ∈ doubleSet f'' := by
      rw [mem_doubleSet]; exact ⟨hzp, hz⟩
    exact hsimple' p (hsub hp) z (mem_doubleSet.mp (hsub hmem)).2
  -- the double points of `f''` lie outside the clean region
  have hfst : ∀ a b : M, (a, b) ∈ doubleSet f'' → a ∉ W := by
    intro a b hab hW
    have hab' : (a, b) ∈ doubleSet f' := hsub hab
    obtain ⟨habne, habeq⟩ := mem_doubleSet.mp hab'
    have hnot4 : (a, b) ∉ ({(p₁, p₂), (p₂, p₁), (p', q'), (q', p')} : Set (M × M)) := by
      intro h4
      rw [hds''] at hab
      exact hab.2 h4
    rw [hWchar] at hW
    rcases hW with hW | hW | hW | hW | hW
    · exact hW ⟨b, habne.symm, habeq.symm⟩
    · -- `a = p₁`
      have h := hs₁ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = p₂`
      have h := hs₁ b (by rw [← habeq, hW, hfp'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
    · -- `a = p'`
      have h := hs₂ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = q'`
      have h := hs₂ b (by rw [← habeq, hW, hfq'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
  have hnotW : ∀ p : M × M, p ∈ doubleSet f'' → p.1 ∉ W ∧ p.2 ∉ W := fun p hp =>
    ⟨hfst p.1 p.2 hp, hfst p.2 p.1 (by rw [mem_doubleSet] at hp ⊢; exact ⟨hp.1.symm, hp.2.symm⟩)⟩
  have htrans'' : TransDP A f'' := by
    intro p hp
    obtain ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c, hpd⟩ := htrans' p (hsub hp)
    obtain ⟨hnotW₁, hnotW₂⟩ := hnotW p hp
    exact ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c,
      by rw [hagree p.1 p.2 hnotW₁ hnotW₂ c₁ c₂ hp₁c hp₂c]; exact hpd⟩
  -- ## Step 8: the cardinality bookkeeping.
  refine ⟨f'', hf''c, hf''imm, ?_, ?_, hsimple'', htrans''⟩
  · rw [hds'']; exact hf'fin.sdiff
  · have h1 : (doubleSet f'').ncard + 4 = (doubleSet f').ncard :=
      ncard_doubleSet_cancel f' f'' p₁ p₂ p' q'
        hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq' hf'fin hds''
    have h2 : (doubleSet f').ncard = (doubleSet f).ncard + 2 :=
      ncard_doubleSet_insert f f' p' q' hp'q' hnewold hfin hds
    omega

end Work.Whitney
