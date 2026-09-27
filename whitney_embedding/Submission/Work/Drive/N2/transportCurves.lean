import Mathlib
import Submission.Work.Drive.Morse

/-!
# Transporting a level parametrisation along the level flow

The blocks of the compact `n = 2` assembly share **one** flow `Φ` (`Work.Drive.N2.bandLaw` supplies
its unit-speed law on ball-free value bands).  The drawings of two neighbouring blocks are compared by
transporting the picture of one reference level to the other along that flow, and the comparison is
*definitional* as soon as the parametrisations of the two levels are transported of one another: if
`γ` parametrises `Λ(b)` then `γ' := Φ (b' - b, γ ·)` parametrises `Λ(b')`, and a labelled round
configuration read on `Λ(b')` through `γ'` agrees, after composing with the flow transport, with the
same labels read on `Λ(b)` through `γ`.

This file proves that the transport of a parametrisation is a parametrisation with all the rows the
picture construction needs (smooth, on the level, periodic, injective modulo `1`, covering, disjoint
ranges).  It is the bookkeeping that makes the "recursive labelled angles" of the lead's plan
(`λ_i, ϑ_i` transported from band to band) literal: the labels may be *reused* across a critical-free
band, with no phase shift.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The transport of a level parametrisation.**  Let `Φ` be a flow with the unit-speed law on the
value interval `[a,b]` and let `γ` parametrise the level `f ⁻¹' {b}` (`b ∈ [a,b]`).  Then for
`b' ∈ [a,b]` the transported curves `γ' i t = Φ (b' - b, γ i t)` parametrise the level `f ⁻¹' {b'}`,
with the same rows. -/
theorem transportCurves {f : M → ℝ} {a b b' : ℝ} (hb : b ∈ Set.Icc a b) (hb' : b' ∈ Set.Icc a b)
    {Φ : ℝ × M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    {n : ℕ} (γ : Fin n → ℝ → M)
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ i))
    (hγval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = b)
    (hγper : ∀ i x, γ i (x + 1) = γ i x)
    (hγinj : ∀ (i : Fin n) (x y : ℝ), γ i x = γ i y → ∃ k : ℤ, x = y + k)
    (hγlev : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hγdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))) :
    let γ' : Fin n → ℝ → M := fun i t => Φ (b' - b, γ i t)
    (∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ' i)) ∧
    (∀ (i : Fin n) (x : ℝ), f (γ' i x) = b') ∧
    (∀ i x, γ' i (x + 1) = γ' i x) ∧
    (∀ (i : Fin n) (x y : ℝ), γ' i x = γ' i y → ∃ k : ℤ, x = y + k) ∧
    (∀ x : M, f x = b' → ∃ (i : Fin n) (t : ℝ), x = γ' i t) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ' i)) (Set.range (γ' j))) := by
  intro γ'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hΦsm.comp (contMDiff_const.prodMk (hγsm i))
  · intro i x
    have h := hΦf (γ i x) (b' - b) (by rw [hγval i x]; exact hb)
      (by rw [hγval i x]; constructor <;> linarith [hb'.1, hb'.2])
    rw [hγval i x] at h
    simpa using h
  · intro i x
    show Φ (b' - b, γ i (x + 1)) = Φ (b' - b, γ i x)
    rw [hγper i x]
  · intro i x y hxy
    have h1 : γ i x = γ i y := by
      have h2 := congrArg (fun z : M => Φ (b - b', z)) hxy
      rw [hΦcomp, hΦcomp] at h2
      have h3 : b - b' + (b' - b) = 0 := by ring
      rw [h3, hΦ0, hΦ0] at h2
      exact h2
    exact hγinj i x y h1
  · intro x hx
    have hy : f (Φ (b - b', x)) = b := by
      have h := hΦf x (b - b') (by rw [hx]; exact hb')
        (by rw [hx]; constructor <;> linarith [hb.1, hb.2])
      rw [hx] at h
      simpa using h
    obtain ⟨i, t, ht⟩ := hγlev (Φ (b - b', x)) hy
    refine ⟨i, t, ?_⟩
    show x = Φ (b' - b, γ i t)
    rw [← ht]
    have h4 : b' - b + (b - b') = 0 := by ring
    rw [hΦcomp, h4, hΦ0]
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨u, hu⟩ := hy
    have h1 : γ j u = γ i s := by
      have h2 := congrArg (fun z : M => Φ (b - b', z)) hu
      rw [hΦcomp, hΦcomp] at h2
      have h3 : b - b' + (b' - b) = 0 := by ring
      rw [h3, hΦ0, hΦ0] at h2
      exact h2
    exact Set.disjoint_left.mp (hγdisj i j hij) ⟨s, rfl⟩ ⟨u, h1⟩

end Work.Drive.N2
