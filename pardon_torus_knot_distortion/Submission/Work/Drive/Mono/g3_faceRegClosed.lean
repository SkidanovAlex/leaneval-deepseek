import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Final.param_add_int_mul_two_pi
import Submission.Work.Drive.Final.fderiv_add_of_periodic
import Submission.Work.Core.torusMap_eq_iff

/-!
# `FaceRegClosed` of the `G3Extra` bundle of the junction route

The clause

`∀ p, par ψ p ∈ closure (PBox s c σ) → |slabFn c u v (par ψ p)| = h →
   fderiv ℝ (slabFnPar ψ c u v) p ≠ 0`

of `Work.Drive.Mono.G3Extra`, deduced from the triple-point transversality
`Work.Drive.Mono.SlabBoxCrossReg`, the "slab in belt" hypothesis (`σ 2` non-extremal) and the
face regularity on the *open* box (`Work.Drive.Mono.exists_tiltData_smallSlab_faceReg`'s `faceReg`
clause, the `hface` hypothesis here).

Mathematically: `slabFnPar ψ c u v` and `⟪v, par ψ ·⟫` differ by the constant `⟪v,c⟫ + u`, so it
suffices to show that the differential of `⟪v, par ψ ·⟫` does not vanish at `p`.

* If `par ψ p` is in the **open** box, the hypothesis `hface` (face regularity on the open box)
  provides a lift `p'` of `par ψ p` at which the differential is non-zero; the parametrisation is
  `2π`-periodic, hence `fderiv (⟪v, par ψ ·⟫)` is invariant under the period lattice, and the
  differential at `p` does not vanish either.
* On the **boundary** of the box, `closure PBox ∖ PBox = {boxNorm = s}`, so some coordinate
  `i ≠ 2` is extremal (`hbelt` excludes `i = 2`); writing `ε, η = ±1` for the signs of that
  coordinate and of the slab functional, the pair
  `q ↦ ((par ψ q) (σ i), ⟪v, par ψ q⟫)` has invertible derivative at `p` by `SlabBoxCrossReg`, so
  in particular the second component of that derivative is non-zero.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## Elementary ingredients -/

/-- The face functional `slabFnPar ψ c u v` and the pull-back `q ↦ ⟪v, par ψ q⟫` differ by the
constant `⟪v,c⟫ + u`, hence have the same derivative everywhere. -/
theorem g3_fderiv_slabFnPar_eq_inner (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3)
    (p : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  have h : Work.Drive.Final.slabFnPar ψ c u v
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := by
    funext q
    rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFn_apply]
  rw [h, fderiv_sub_const]

/-- `fderiv (slabFnPar ψ c u v)` is invariant under the period lattice `(2πℤ)²` of the
parametrisation. -/
theorem g3_fderiv_slabFnPar_eq_of_period (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3)
    {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q =
      fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q₀ := by
  rw [h]
  exact Work.Drive.Final.fderiv_add_of_periodic (fun x => by
    show Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ
        (x.1 + (k : ℝ) * (2 * Real.pi), x.2 + (m : ℝ) * (2 * Real.pi))) =
      Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ x)
    rw [Work.Drive.Final.param_add_int_mul_two_pi]) q₀

/-- If the pair `(A, B) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)` is invertible, then `B` is not the zero
functional: the invertible map is surjective, and the second coordinate of the value at the
preimage of `(0,1)` can only be `1`. -/
theorem g3_snd_ne_zero_of_isInvertible {A B : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : (A.prod B).IsInvertible) : B ≠ 0 := by
  intro hB
  obtain ⟨e, he⟩ := h
  have hw : (A.prod B) (e.symm (0, 1)) = (0, 1) := by
    rw [← he]
    exact e.apply_symm_apply (0, 1)
  have h2 : B (e.symm (0, 1)) = 1 := by
    have hh := congrArg Prod.snd hw
    rw [ContinuousLinearMap.prod_apply] at hh
    simpa using hh
  rw [hB] at h2
  simp at h2

/-- A coordinate attaining the maximum of the box norm. -/
theorem g3_exists_boxSide_mul_eq_of_boxNorm_eq (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (y : R3) (h : Submission.boxNorm c σ y = s) :
    ∃ i : Fin 3, |y (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [Submission.boxNorm] at h
  rcases max_eq_iff.mp h with ⟨h', _⟩ | ⟨h2, _⟩
  · rcases max_eq_iff.mp h' with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact ⟨0, by rw [div_eq_iff (Submission.boxSide_pos 0).ne'] at h0; rw [h0]; ring⟩
    · exact ⟨1, by rw [div_eq_iff (Submission.boxSide_pos 1).ne'] at h1; rw [h1]; ring⟩
  · exact ⟨2, by rw [div_eq_iff (Submission.boxSide_pos 2).ne'] at h2; rw [h2]; ring⟩

/-! ## The theorem -/

theorem g3_faceRegClosed {ψ : Submission.Diffeo} {s u h : ℝ}
    {c v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    (hSBCR : Work.Drive.Mono.SlabBoxCrossReg ψ c σ s v (inner ℝ v c + u) h)
    (hbelt : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    (hface : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v z| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) :
    ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h →
      fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p ≠ 0 := by
  intro p hcl hslab
  have hmem : Work.BoxShrink.Pinch.par ψ p ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.BoxShrink.Pinch.par_mem_carrier ψ p
  by_cases hbox : Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ
  · -- ### the parameter point lies over the *open* box: transfer the face regularity
    obtain ⟨p', hp', hne'⟩ := hface (Work.BoxShrink.Pinch.par ψ p) hmem hbox hslab
    -- `p` and `p'` differ by an element of the period lattice `(2πℤ)²`
    have hψeq : ψ (Work.Core.torusMap p'.1 p'.2) = ψ (Work.Core.torusMap p.1 p.2) := by
      have h2 : Work.BoxShrink.Pinch.par ψ (p'.1, p'.2) =
          Work.BoxShrink.Pinch.par ψ (p.1, p.2) := hp'
      rw [Work.BoxShrink.Pinch.par_apply, Work.BoxShrink.Pinch.par_apply] at h2
      exact h2
    have htm : Work.Core.torusMap p'.1 p'.2 = Work.Core.torusMap p.1 p.2 :=
      Submission.Diffeo.injective ψ hψeq
    obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := (Work.Core.torusMap_eq_iff p'.1 p'.2 p.1 p.2).mp htm
    have hpq : p = p' + ((↑(-k) : ℝ) * (2 * Real.pi), (↑(-m) : ℝ) * (2 * Real.pi)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add]
        rw [hk]; push_cast; ring
      · rw [Prod.snd_add]
        rw [hm]; push_cast; ring
    have hper := g3_fderiv_slabFnPar_eq_of_period ψ c u v (-k) (-m) hpq
    have hcomp : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p =
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p' :=
      hper.trans (g3_fderiv_slabFnPar_eq_inner ψ c u v p')
    rw [hcomp]
    exact hne'
  · -- ### the parameter point lies over the *boundary* of the box
    have hle : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) ≤ s :=
      Work.Drive.Mono.closure_PBox_subset_boxNorm_le s c σ hcl
    have hge : s ≤ Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) := by
      by_contra hlt
      exact hbox ((Submission.mem_PBox_iff s c σ _).mpr (not_le.mp hlt))
    have hbn : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s :=
      le_antisymm hle hge
    obtain ⟨i, hi⟩ := g3_exists_boxSide_mul_eq_of_boxNorm_eq c σ s _ hbn
    -- the extremal coordinate is not the `σ 2` one (`SlabInBelt`)
    have hi2 : i ≠ 2 := by
      intro h2
      have hb := hbelt (Work.BoxShrink.Pinch.par ψ p) hmem hcl (le_of_eq hslab)
      rw [h2] at hi
      rw [hi] at hb
      exact absurd hb (lt_irrefl _)
    -- the signs `ε` of the extremal coordinate and `η` of the slab functional
    obtain ⟨ε, hε, hcoord⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s := by
      rcases eq_or_eq_neg_of_abs_eq hi with h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [one_mul]; linarith [h1]⟩
      · exact ⟨-1, Or.inr rfl, by rw [neg_one_mul, neg_mul]; linarith [h1]⟩
    obtain ⟨η, hη, hinner⟩ : ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
        inner ℝ v (Work.BoxShrink.Pinch.par ψ p) = (inner ℝ v c + u) + η * h := by
      have hs : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h := by
        simpa [Work.Drive.Final.slabFn_apply] using hslab
      rcases eq_or_eq_neg_of_abs_eq hs with h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [one_mul]; linarith [h1]⟩
      · exact ⟨-1, Or.inr rfl, by rw [neg_one_mul]; linarith [h1]⟩
    -- triple-point transversality at `p`
    have hInv := hSBCR i hi2 ε hε η hη p hcoord hinner
    have hpair : fderiv ℝ (fun q : ℝ × ℝ =>
        ((Work.BoxShrink.Pinch.par ψ q) (σ i), inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p
        = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
          (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p :=
        ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) (σ i)).contDiff.contDiffAt.comp p
          (Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p :=
        ((innerSL ℝ v).contDiff.contDiffAt.comp p
          (Work.BoxShrink.Pinch.par_contDiff ψ).contDiffAt)
      exact (((h1.differentiableAt (by simp)).hasFDerivAt).prodMk
        ((h2.differentiableAt (by simp)).hasFDerivAt)).fderiv
    have hInv' : ((fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
        (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)).IsInvertible := by
      rw [← hpair]
      exact hInv
    have hBne : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 :=
      g3_snd_ne_zero_of_isInvertible hInv'
    rw [g3_fderiv_slabFnPar_eq_inner ψ c u v p]
    exact hBne

end

end Work.Drive.Mono
