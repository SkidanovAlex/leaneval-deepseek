import Mathlib
import Submission.Work.ELRig.CylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The range of a `1`-periodic-up-to-translation curve is closed

`Work.ELRig.RayCylLift` carries two continuous curves `γ₁, γ₂ : ℝ → ℂ` which are
*`1`-periodic up to the translation `w ↦ w + 1`*:
`γᵢ (s + 1) = γᵢ s + 1` (`RayCylLift.per₁`, `RayCylLift.per₂`).

The point of this file is that such a curve has **closed range**.  The reason is
purely topological and is the standard "fundamental domain" argument: with
`K := γ '' [0,1]` (compact, being the continuous image of a compact interval),
the periodicity gives

  `range γ = ⋃ n : ℤ, (fun k => k + (n : ℂ)) '' K`,

a locally finite union of compact — hence closed — sets.  (Local finiteness is
immediate because `K` is bounded, so only finitely many integral translates meet
a fixed ball.)

This is exactly what is needed to see that the two lift curves of a
`RayCylLift` have closed ranges, whence `range γ₁ ∪ range γ₂` is closed.
-/

open Filter

namespace Work.ELRig

/-- **Quasi-periodicity.**  If `γ (s + 1) = γ s + 1` then `γ (t + m) = γ t + m`
for every integer `m`. -/
theorem periodicShift_translate (γ : ℝ → ℂ) (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) :
    ∀ (m : ℤ) (t : ℝ), γ (t + (m : ℝ)) = γ t + (m : ℂ) := by
  have hnat : ∀ (j : ℕ) (t : ℝ), γ (t + (j : ℝ)) = γ t + (j : ℂ) := by
    intro j
    induction j with
    | zero => intro t; simp
    | succ j ih =>
      intro t
      have h1 : t + ((j + 1 : ℕ) : ℝ) = (t + (j : ℝ)) + 1 := by push_cast; ring
      rw [h1, hper, ih, Nat.cast_succ]
      ring
  intro m t
  rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
  · push_cast; exact hnat j t
  · have h := hnat j (t - (j : ℝ))
    have ht : t - (j : ℝ) + (j : ℝ) = t := by ring
    rw [ht] at h
    push_cast
    rw [h]; abel

/-- **The range of a continuous quasi-periodic curve is closed.**  The periodicity
`γ (s + 1) = γ s + 1` makes `range γ` the locally finite union of the compact sets
`γ '' [0,1] + n` (`n : ℤ`). -/
theorem isClosed_range_of_periodicShift {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) : IsClosed (Set.range γ) := by
  rw [← closure_subset_iff_isClosed]
  intro a ha
  rw [mem_closure_iff_seq_limit] at ha
  obtain ⟨u, hu, hux⟩ := ha
  -- write each `u n` as `γ (s n)`, and split `s n = fract (s n) + ⌊s n⌋`.
  have hs : ∀ n, ∃ r : ℝ, γ r = u n := fun n => hu n
  let sd : ℕ → ℝ := fun n => Classical.choose (hs n)
  have hspec : ∀ n, γ (sd n) = u n := fun n => Classical.choose_spec (hs n)
  -- the fundamental domain `K = γ '' [0,1]`, compact.
  set K : Set ℂ := γ '' Set.Icc 0 1 with hKdef
  have hK : IsCompact K := isCompact_Icc.image hcont
  let kk : ℕ → ℂ := fun n => γ (Int.fract (sd n))
  have hk_mem : ∀ n, kk n ∈ K := by
    intro n
    exact ⟨Int.fract (sd n), ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩
  -- extract a subsequence along which the fractional parts converge.
  obtain ⟨klim, hklim, phi, hphi, hkphi⟩ := hK.tendsto_subseq hk_mem
  have huphi : Tendsto (u ∘ phi) atTop (nhds a) := hux.comp hphi.tendsto_atTop
  -- the integer parts differ from the `u n` by the convergent `kk`.
  have hkey : ∀ j, ((⌊sd (phi j)⌋ : ℤ) : ℂ) = (u ∘ phi) j - (kk ∘ phi) j := by
    intro j
    simp only [Function.comp_apply]
    have htrans := periodicShift_translate γ hper ⌊sd (phi j)⌋ (Int.fract (sd (phi j)))
    rw [Int.fract_add_floor] at htrans
    rw [← hspec (phi j), htrans]
    simp only [kk]
    ring
  have hmphi : Tendsto (fun j => ((⌊sd (phi j)⌋ : ℤ) : ℂ)) atTop (nhds (a - klim)) := by
    have hfun : (fun j => ((⌊sd (phi j)⌋ : ℤ) : ℂ)) = (fun j => (u ∘ phi) j - (kk ∘ phi) j) :=
      funext hkey
    rw [hfun]
    exact huphi.sub hkphi
  -- `Int.cast` has closed range in `ℂ`, so the limit `a - klim` is an integer.
  have hmem : a - klim ∈ Set.range (Int.cast : ℤ → ℂ) :=
    Complex.isClosed_range_intCast.mem_of_tendsto hmphi
      (Eventually.of_forall (fun j => ⟨⌊sd (phi j)⌋, rfl⟩))
  obtain ⟨mm, hmm⟩ := hmem
  obtain ⟨t0, _ht0, ht0eq⟩ := hklim
  -- `a = klim + mm = γ t0 + mm = γ (t0 + mm)`, so `a` lies in the range.
  refine ⟨t0 + (mm : ℝ), ?_⟩
  rw [periodicShift_translate γ hper mm t0, ht0eq]
  rw [hmm]; ring

theorem range_lift_closed {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) :
    IsClosed (Set.range L.γ₁ ∪ Set.range L.γ₂) :=
  (isClosed_range_of_periodicShift L.cont₁ L.per₁).union
    (isClosed_range_of_periodicShift L.cont₂ L.per₂)

end Work.ELRig
