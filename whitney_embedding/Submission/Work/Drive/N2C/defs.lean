import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.roundConfigDefs

/-!
# `N2C`: the vocabulary of the coherent-window architecture (compact `n = 2`)

The design is `Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md` §3.  Each critical point
gets a window drawing that is good on `(c - 2η, c + 2η)` and carries **certificates**: at the levels
`c ∓ 3η/2` its level picture is isotopic, through pictures of that level, to a disjoint round
configuration read through a parametrisation of the level.  The gaps then do all the isotopy.

This file is the shared vocabulary (imported by every lane):

* `LevelCurves f b n` — the parametrisation rows of the level `f = b` by `n` periodic curves
  (exactly the rows consumed by `collarFamily`, `exists_picture_of_config`, `roundConfigPictureGlobal`
  and `transportCurves`, plus the "mod 1" row);
* `IsLevelIsotopy f b e` — a jointly smooth family of *pictures* of the level `b` (the rows `hesm`,
  `heinj`, `heimm` of `Work.Drive.N2.collarDrawing_local` stated at the level);
* `IsCertifiedAt f u g` — `g` restricted to the level `u` is isotopic through pictures of that level
  to a disjoint round configuration read through a parametrisation of the level.

Tier A of the design (the trivial facts about this vocabulary) is included below: `A1`
(`LevelCurves.ofComponentCurves` from `exists_levelComponentCurves`), the empty-level constructor,
`A3` (`LevelCurves.reverse`) and `A4` (`isCertifiedAt_of_empty`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The parametrisation rows of a level.**  Exactly the rows consumed by
`Work.Drive.N2.collarFamily`, `Work.Drive.N2.exists_picture_of_config` and
`Work.Drive.N2.roundConfigPictureGlobal`, plus the "mod 1" row used by `Work.Drive.N2.transportCurves`
and `Work.Drive.N2.exists_levelDrawingFun`. -/
structure LevelCurves (f : M → ℝ) (b : ℝ) (n : ℕ) where
  γ : Fin n → ℝ → M
  sm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ i)
  val : ∀ i x, f (γ i x) = b
  per : ∀ i x, γ i (x + 1) = γ i x
  injIco : ∀ i, Set.InjOn (γ i) (Set.Ico 0 1)
  modOne : ∀ i x y, γ i x = γ i y → ∃ k : ℤ, x = y + k
  cover : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t
  disj : ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))
  ker : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ i x)),
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 → ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v

/-- **A level isotopy**: a jointly smooth family of pictures of the level `b`.  These are exactly the
rows `hesm`, `heinj` and `heimm` consumed by `Work.Drive.N2.collarDrawing_local`, stated at the level
itself. -/
def IsLevelIsotopy (f : M → ℝ) (b : ℝ) (e : ℝ → M → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => e p.1 p.2) (s, y)) ∧
  (∀ (s : ℝ) (x y : M), f x = b → f y = b → e s x = e s y → x = y) ∧
  (∀ (s : ℝ) (y : M), f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) (e s) y v = 0 → v = 0)

/-- **A certified level picture**: `g`, restricted to the level `u`, is isotopic through pictures of
that level to a disjoint round configuration read through a parametrisation of the level. -/
def IsCertifiedAt (f : M → ℝ) (u : ℝ) (g : M → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ (n : ℕ) (L : LevelCurves f u n) (D : Work.Drive.N2.RoundConfig n)
    (e : ℝ → M → EuclideanSpace ℝ (Fin 3)),
    D.Disjoint ∧ IsLevelIsotopy f u e ∧
    (∀ y : M, f y = u → e 0 y = g y) ∧
    (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = D.circle i x)

/-- The empty round configuration. -/
def roundConfigEmpty : Work.Drive.N2.RoundConfig 0 where
  pos := Fin.elim0
  rad := Fin.elim0
  hrad := fun i => i.elim0
  phase := Fin.elim0

/-! ### Tier A: trivial facts -/

/-- **A1 (empty level).**  On an empty level the parametrisation is indexed by `Fin 0`. -/
def LevelCurves.empty {f : M → ℝ} {b : ℝ} (h : ∀ x : M, f x ≠ b) : LevelCurves f b 0 where
  γ := Fin.elim0
  sm := fun i => i.elim0
  val := fun i => i.elim0
  per := fun i => i.elim0
  injIco := fun i => i.elim0
  modOne := fun i => i.elim0
  cover := fun x hx => absurd hx (h x)
  disj := fun i => i.elim0
  ker := fun i => i.elim0

/-- **A4.**  On an empty level every map is certified (with the empty round configuration). -/
theorem isCertifiedAt_of_empty {f : M → ℝ} {u : ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h : ∀ y : M, f y ≠ u) : IsCertifiedAt f u g := by
  refine ⟨0, LevelCurves.empty h, roundConfigEmpty, fun _ y => g y, ?_, ?_, ?_, ?_⟩
  · intro i
    exact i.elim0
  · refine ⟨?_, ?_, ?_⟩
    · intro s y hy
      exact absurd hy (h y)
    · intro s x y hx hy _
      exact absurd hx (h x)
    · intro s y hy
      exact absurd hy (h y)
  · intro y hy
    exact absurd hy (h y)
  · intro i
    exact i.elim0

-- A3 (`LevelCurves.reverse`) and A1/A2 (`ofComponentCurves`, `transport`) are left to the fleet;
-- the rows `injIco`/`ker` are the ones that need the periodicity argument and the chain rule.

end Work.Drive.N2C
