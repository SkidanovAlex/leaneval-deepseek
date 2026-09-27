import Mathlib
import Submission.Work.Drive.N2C.defs

/-!
# `N2C` A1: level curves from component curves

Given the parametrisations of the connected components of the level `f = a`
— periodic smooth curves `γ i` with `γ i (x + 1) = γ i x`, injective on `[0,1)`, covering
the level, pairwise disjoint, and whose derivative covers the kernel of `mfderiv f` — the
`LevelCurves` bundle of the level `f = a` exists.

Every row of `Work.Drive.N2C.LevelCurves` except `modOne` is one of the hypotheses, so the
mathematical content is exactly the **"mod 1" row**: two parameters of the same component
curve with the same image differ by an integer,

  `γ i x = γ i y → ∃ k : ℤ, x = y + k`,

which is the statement that `γ i` descends to an injection `ℝ/ℤ → M`.  The proof reduces both
parameters modulo `1` by `Int.fract` (using the periodicity to pass to the integer part, via
`Function.Periodic.int_mul`), applies injectivity on `[0,1)`, and concludes with
`Int.fract_eq_fract`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- Periodicity with period `1` gives periodicity with respect to every integer shift. -/
theorem eq_of_add_intCast_of_periodic {X : Type*} {γ : ℝ → X}
    (hper : ∀ x : ℝ, γ (x + 1) = γ x) (z : ℝ) (k : ℤ) : γ (z + k) = γ z := by
  have hp : Function.Periodic γ (1 : ℝ) := hper
  simpa using (hp.int_mul k) z

/-- A `1`-periodic curve depends only on the fractional part of the parameter. -/
theorem eq_fract_of_periodic {X : Type*} {γ : ℝ → X}
    (hper : ∀ x : ℝ, γ (x + 1) = γ x) (z : ℝ) : γ z = γ (Int.fract z) := by
  have h : γ (Int.fract z + ⌊z⌋) = γ (Int.fract z) :=
    eq_of_add_intCast_of_periodic hper (Int.fract z) ⌊z⌋
  rwa [Int.fract_add_floor] at h

/-- **A `1`-periodic curve injective on `[0,1)` is injective modulo `1`.** -/
theorem exists_int_sub_of_periodic_injOn {X : Type*} {γ : ℝ → X}
    (hper : ∀ x : ℝ, γ (x + 1) = γ x) (hinj : Set.InjOn γ (Set.Ico 0 1)) :
    ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k := by
  intro x y hxy
  have hfrac : Int.fract x = Int.fract y :=
    hinj ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
      ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
      (by rw [← eq_fract_of_periodic hper x, ← eq_fract_of_periodic hper y]; exact hxy)
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp hfrac
  exact ⟨k, by linarith⟩

theorem levelCurves_ofComponentCurves {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} {γ : Fin n → ℝ → M}
    (hsm : ∀ i : Fin n, ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) (γ i))
    (hper : ∀ (i : Fin n) (x : ℝ), γ i (x + 1) = γ i x)
    (hinj : ∀ i : Fin n, Set.InjOn (γ i) (Set.Ico 0 1))
    (hval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = a)
    (hker : ∀ (i : Fin n) (x : ℝ),
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (γ i x),
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) f (γ i x) v = 0 →
      ∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (γ i) x t = v)
    (hcover : ∀ x : M, f x = a → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))) :
    Nonempty (Work.Drive.N2C.LevelCurves f a n) := by
  have hmod : ∀ (i : Fin n) (x y : ℝ), γ i x = γ i y → ∃ k : ℤ, x = y + k :=
    fun i => exists_int_sub_of_periodic_injOn (hper i) (hinj i)
  exact ⟨LevelCurves.mk γ hsm hval hper hinj hmod hcover hdisj hker⟩

end Work.Drive.N2C
