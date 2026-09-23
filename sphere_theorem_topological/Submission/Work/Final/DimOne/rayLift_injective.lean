import Mathlib
import Submission.Work.Final.DimOne.Defs

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

/-!
# Injectivity of the descent of a periodic `GExp`-ray to the circle

`Work.Final.rayLift` descends the periodic ray `s ↦ GExp p (s • u)` (period `P`) to a map
`AddCircle P → M`.  Here we prove that this descent is injective, assuming:

* `P` is the *minimal* positive period of the ray (`hmin`), and
* any two distinct parameters `a ≠ b` with `f a = f b` produce a positive period `Q ≤ |b - a|`
  (`hsq`).

The mathematical content is one-dimensional and purely about the period group: two parameters give
the same point of `M` only if they differ by an integer multiple of `P`.  Indeed, writing
`b - a = k * P + r` with `k = ⌊(b - a)/P⌋` and `0 ≤ r < P`, periodicity gives `f (a + r) = f b`,
so if `r ≠ 0` then `hsq` produces a positive period `≤ r < P`, contradicting minimality of `P`.

The argument only uses the periodicity hypotheses, so it is isolated below as
`injective_periodic_lift` for a general function `ℝ → β`.  The geometric statements enter only
through the fact that the hypotheses on `GExp` are *definitionally* the periodicity conditions on
`fun s ↦ GExp (cov := cov) hmet p (s • u)`.
-/

/-- **A periodic function on `ℝ` with minimal period `P` and with the "two distinct parameters
giving the same value generate a period" property, descends injectively to `AddCircle P`.**

This is the abstract form of `Work.Final.DimOne.rayLift_injective`: for a function
`f : ℝ → β` with period `P > 0` (minimal among positive periods), if any `a ≠ b` with
`f a = f b` produces a positive period `Q ≤ |b - a|`, then `f` factors injectively through
`ℝ ⧸ ℤ ∙ P`. -/
private lemma injective_periodic_lift {β : Type*} {f : ℝ → β} {P : ℝ} (hP : 0 < P)
    (hper : Function.Periodic f P)
    (hmin : ∀ Q : ℝ, 0 < Q → Function.Periodic f Q → P ≤ Q)
    (hsq : ∀ a b : ℝ, a ≠ b → f a = f b →
      ∃ Q : ℝ, 0 < Q ∧ Q ≤ |b - a| ∧ Function.Periodic f Q) :
    Function.Injective (Function.Periodic.lift hper) := by
  -- two distinct parameters with the same value are at distance at least `P`
  have hsep : ∀ a b : ℝ, a ≠ b → f a = f b → P ≤ |b - a| := by
    intro a b hab heq
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := hsq a b hab heq
    exact le_trans (hmin Q hQ1 hQ3) hQ2
  -- key step: the difference of two parameters with the same value is an integer multiple of `P`
  have hkey : ∀ a b : ℝ, f a = f b → ∃ n : ℤ, b - a = n * P := by
    intro a b hab
    by_cases hab' : a = b
    · exact ⟨0, by simp [hab']⟩
    · -- Euclidean division of `b - a` by `P`
      set k : ℤ := Int.floor ((b - a) / P) with hkdef
      set r : ℝ := b - a - (k : ℝ) * P with hrdef
      have hr0 : 0 ≤ r := by
        have h1 : (k : ℝ) ≤ (b - a) / P := by rw [hkdef]; exact Int.floor_le _
        have h2 : (k : ℝ) * P ≤ ((b - a) / P) * P := mul_le_mul_of_nonneg_right h1 hP.le
        rw [div_mul_cancel₀ (b - a) hP.ne'] at h2
        rw [hrdef]; linarith
      have hrP : r < P := by
        have h1 : (b - a) / P < (k : ℝ) + 1 := by rw [hkdef]; exact Int.lt_floor_add_one _
        have h2 : ((b - a) / P) * P < ((k : ℝ) + 1) * P := mul_lt_mul_of_pos_right h1 hP
        rw [div_mul_cancel₀ (b - a) hP.ne'] at h2
        rw [hrdef]; linarith
      by_cases hr : r = 0
      · exact ⟨k, by rw [hrdef] at hr; linarith⟩
      · -- `r` is a nonzero remainder in `[0, P)`: periodicity transports `f b = f a` to `f (a + r) = f a`
        exfalso
        have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
        have hkp : Function.Periodic f ((k : ℝ) * P) := by
          simpa [zsmul_eq_mul] using hper.zsmul k
        have hb_eq : b = (a + r) + (k : ℝ) * P := by rw [hrdef]; ring
        have hfr : f a = f (a + r) := by
          have : f (a + r) = f b := by
            rw [hb_eq]
            exact (hkp (a + r)).symm
          rw [this]; exact hab
        have hne : a ≠ a + r := by intro h; exact hr (by linarith)
        have hle := hsep a (a + r) hne hfr
        have habs : |(a + r) - a| = r := by rw [add_sub_cancel_left, abs_of_pos hrpos]
        rw [habs] at hle
        -- `P ≤ r < P`, a contradiction
        linarith
  intro x y hxy
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  have hab : f a = f b := by
    simpa using hxy
  obtain ⟨n, hn⟩ := hkey a b hab
  rw [QuotientAddGroup.eq]
  rw [AddSubgroup.mem_zmultiples_iff]
  exact ⟨n, by rw [zsmul_eq_mul]; linarith [hn]⟩

set_option maxHeartbeats 1000000 in
theorem rayLift_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (hu : ‖u‖ = 1) {P : ℝ}
    (hP : 0 < P)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u))
    (hmin : ∀ Q : ℝ, 0 < Q →
      (∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u)) →
      P ≤ Q)
    (hsq : ∀ a b : ℝ, a ≠ b →
      GExp (cov := cov) hmet p (a • u) = GExp (cov := cov) hmet p (b • u) →
      ∃ Q : ℝ, 0 < Q ∧ Q ≤ |b - a| ∧ ∀ s : ℝ,
        GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u)) :
    Function.Injective (Work.Final.rayLift (cov := cov) hmet p u P hper) := by
  -- the hypotheses `hper`, `hmin`, `hsq` are *definitionally* the periodicity form expected by
  -- `injective_periodic_lift` for the ray `s ↦ GExp p (s • u)`, and `rayLift` is its descent
  exact injective_periodic_lift (f := fun s : ℝ => GExp (cov := cov) hmet p (s • u))
    hP hper hmin hsq

end Work.Final.DimOne
