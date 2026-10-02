import Mathlib
import Submission.Work.Stems.Collar.WangPowFormula
import Submission.Work.Stems.wangOddStepSphere
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.Stems.wangAllAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems

/-- **The Wang odd step over the sphere, in every degree up to a bound.**  This is the form usable
for *range models*: the fibre's rational cohomology is known only up to `T`, so only the two degrees
`t - b` and `t` (both `≤ t ≤ T`) are needed.  It is the same proof as
`Work.Stems.isZero_ratCoh_sphereFibration_all` with the bound carried along.

For a Hurewicz fibration `p : E → Sᵇ` (`b ≥ 2` odd) whose fibre is rationally a sphere pile —
`H^t(F;ℚ) = 0` unless `t` is a positive multiple of `b-1`, and `H^{(b-1)k}(F;ℚ) ≅ ℚ` — a class
`x ∈ H^{b-1}(F;ℚ)` whose low-degree transgression `θ^{low}(x)` does not vanish kills the whole
total space: `H^t(E;ℚ) = 0` for every `t ≥ b+1`.

The proof is the unbounded form of `Work.Stems.isZero_wangTotal` of `Submission/Work/Stems/wangOddStep.lean`:
`H^{n+b+1}(E)` is squeezed in the shifted Wang sequence between `β_n` and `α_{n+b+1}`, and at the
degrees where the fibre's cohomology does not vanish the two maps are controlled by the
transgression `θ`.  The transgression is a non-zero map between one-dimensional spaces there, which
is what makes `β_n` vanish (surjectivity) and `α_{n+b+1}` vanish (injectivity); the non-vanishing of
`θ` on the powers of `x` is the *power formula* `θ(x^{k+1}) = (k+1) · x^k ⌣ θ^{low}(x)`, together
with the fact that a non-zero class of `H⁰(F;ℚ)` (F is path-connected, so `H⁰(F;ℚ) ≅ ℚ`) is a
non-zero-divisor for the cup product. -/
theorem isZero_ratCoh_sphereFibration_upto (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b)
    (E : Type) [TopologicalSpace E] (p : C(E, Work.StemsB.SphModel b))
    (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty}))
    (hpc : PathConnectedSpace ↥(p ⁻¹' {OnePoint.infty}))
    (hpow : Work.Stems.Collar.WangPowFormula)
    (hlow : Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x ≠ 0)
    (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → (∀ k : ℕ, t ≠ (b - 1) * k) →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p)))
    (hgen : ∀ k : ℕ, 1 ≤ k → Nonempty
      (Work.Cohomology.singularCohomology ℚ ((b - 1) * k) (Work.StemsB.wangCohFsp b p) ≅
        ModuleCat.of ℚ ℚ)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) := by
  intro t ht _
  have keyT : (t - b - 1) + b + 1 = t := by omega
  rw [← keyT]
  refine isZero_wangTotal_of_zeroMaps (TopCat.of E) (Work.StemsB.Rat.wangA b p)
    (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
    (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) (t - b - 1) ?hβ ?hα
  · by_cases hsrc : Subsingleton
        ↥(Work.Cohomology.singularCohomology ℚ (t - b) (Work.StemsB.wangCohFsp b p))
    · intro c
      haveI : Subsingleton
          ↥(Work.Cohomology.singularCohomology ℚ ((t - b - 1) + 1) (Work.StemsB.wangCohFsp b p)) := by
        rw [show (t - b - 1) + 1 = t - b from by omega]
        exact hsrc
      rw [Subsingleton.elim c 0]
      exact map_zero _
    · obtain ⟨K, hK⟩ : ∃ K, t - b = (b - 1) * K := by
        by_contra h
        push_neg at h
        exact hsrc (hfib (t - b) (by omega) (by omega) h)
      have hK1 : 1 ≤ K := by
        by_contra h
        have h0 : K = 0 := by omega
        rw [h0, Nat.mul_zero] at hK
        omega
      have hidx : t - b - 1 = (b - 1) * ((K - 1) + 2) - b := by
        have h1 : (K - 1) + 2 = K + 1 := by omega
        rw [h1, Nat.mul_succ, ← hK]
        omega
      intro c
      have hsurj := thetaR_surjective_of_index b hb p d_G hT_G hT_O hidx
        (wangTheta_canon_surjective b hb p d_G hT_G hT_O x hbodd hpc hlow hpow hgen (K - 1))
      obtain ⟨v, hv⟩ := hsurj c
      have hEx := Work.StemsB.wangCohShiftExact₃R ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
        (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) (t - b - 1)
      exact (hEx c).mpr ⟨v, hv⟩
  · intro y
    by_cases htgt : Subsingleton
        ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p))
    · haveI : Subsingleton
          ↥(Work.Cohomology.singularCohomology ℚ ((t - b - 1) + b + 1)
            (Work.StemsB.wangCohFsp b p)) := by
        rw [show (t - b - 1) + b + 1 = t from by omega]
        exact htgt
      exact Subsingleton.elim _ _
    · obtain ⟨K, hK⟩ : ∃ K, t = (b - 1) * K := by
        by_contra h
        push_neg at h
        exact htgt (hfib t (by omega) (by omega) h)
      have hK2 : 2 ≤ K := by
        by_contra h
        have h1 : K ≤ 1 := by omega
        interval_cases K
        · rw [Nat.mul_zero] at hK
          omega
        · rw [Nat.mul_one] at hK
          omega
      have hidxθ : (t - b - 1) + 1 = (b - 1) * ((K - 2) + 2) - b := by
        have h1 : (K - 2) + 2 = K := by omega
        rw [h1, ← hK]
        omega
      have hθinj : Function.Injective
          (⇑(Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1))) :=
        thetaR_injective_of_index b hb p d_G hT_G hT_O hidxθ
          (wangTheta_canon_injective b hb p d_G hT_G hT_O x hbodd hpc hlow hpow hgen (K - 2))
      have hα1 : ∀ z : ↥(Work.Cohomology.singularCohomology ℚ (((t - b - 1) + 1) + b)
            (TopCat.of E)),
          ((Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (((t - b - 1) + 1) + b))).hom z = 0 := by
        intro z
        have hEx := Work.StemsB.wangCohShiftExact₂R ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
          (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
          (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1)
        have hz : (⇑(Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1)))
            ((⇑(Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
              (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
              (((t - b - 1) + 1) + b))) z) = 0 :=
          (hEx ((⇑(Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (((t - b - 1) + 1) + b))) z)).mpr ⟨z, rfl⟩
        exact hθinj (hz.trans (map_zero _).symm)
      have hidxα : (t - b - 1) + b + 1 = ((t - b - 1) + 1) + b := by omega
      have htr := wangCohShiftαR_transport (TopCat.of E) (Work.StemsB.Rat.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O) hidxα y
      have h2 := hα1 ((transIso (TopCat.of E) hidxα).hom y)
      rw [← htr] at h2
      exact Work.StemsB.iso_hom_injective_R ℚ (transIso (Work.StemsB.wangCohFsp b p) hidxα)
        (h2.trans (map_zero _).symm)

end Work.Stems
