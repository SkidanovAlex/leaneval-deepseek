import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.lowDimOn

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The induction assembling rectangular Sard's theorem

This file performs the (double) induction that proves Sard's theorem in the rectangular case
`n ≥ m` for `C^∞` maps, *given* the three steps of the classical proof:

* `SardSteps.notFlat` — the image of `{x | IsCriticalPoint f x} \ Zk f 1` is null (the straightening
  and Fubini step, proved from the induction hypothesis for `(n, m)`);
* `SardSteps.strata` — the image of each stratum difference `Zk f k \ Zk f (k+1)` is null (the
  hypersurface step, from the induction hypothesis for `(n, m)` with the *source* dimension lowered);
* `SardSteps.flat` — the image of the flat stratum `Zk f (K-1)` is null for `n < K * m` (the Taylor
  estimate, proved in `Sard/volume_image_eq_zero_of_isFlat.lean`).

The three steps are separated from the induction so that they can be proved independently; the main
result `sardEuclid_of_steps` (and `SardEuclid`/`SardRectangular`) is then a purely measure-theoretic
bookkeeping argument.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInf CInfOn VanishToOrder Zk IsCriticalPoint
  SardEuclid SardEuclidOn sardEuclid_of_sardEuclidOn)

/-- **The three steps of the classical proof of Sard's theorem**, in the exact form in which the
induction consumes them.  Each of them is proved elsewhere in this directory
(`notFlat_null`, `strataDifference_null`, `localFlat`). -/
structure SardSteps : Prop where
  /-- the non-flat piece `Crit f \ Zk f 1` (the straightening/Fubini step) -/
  notFlat : ∀ (n m : ℕ), SardEuclidOn n m →
    ∀ (f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1)))
      (U : Set (EuclideanSpace ℝ (Fin (n+1)))),
      IsOpen U → CInfOn f U →
        volume (f '' (({x | IsCriticalPoint f x} \ Zk f 1) ∩ U)) = 0
  /-- the stratum differences `Zk f k \ Zk f (k+1)` (the hypersurface step) -/
  strata : ∀ (n m k : ℕ), 1 ≤ k → SardEuclidOn n m →
    ∀ (f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin m))
      (U : Set (EuclideanSpace ℝ (Fin (n+1)))),
      IsOpen U → CInfOn f U → volume (f '' ((Zk f k \ Zk f (k+1)) ∩ U)) = 0
  /-- the flat piece `Zk f (K-1)` for `n < K * m` (the Taylor estimate) -/
  flat : ∀ (n m K : ℕ), 1 ≤ K → n < K * m →
    ∀ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
      (U : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen U → ContDiffOn ℝ K f U → volume (f '' (Zk f (K-1) ∩ U)) = 0

/-- The low-dimensional case of `SardEuclidOn`: for `n < m` every point is critical, so the claim
reduces to the nullity of the image of an open set under a locally Lipschitz map (`lowDimOn`). -/
theorem sardEuclidOn_of_lt {n m : ℕ} (h : n < m) : SardEuclidOn n m := by
  intro f U hU hf
  refine measure_mono_null ?_ (lowDimOn h hU (hf.of_le ENat.LEInfty.out))
  rintro z ⟨x, ⟨-, hxU⟩, rfl⟩
  exact ⟨x, hxU, rfl⟩

/-- **The induction.**  Given the three steps, Sard's theorem in the rectangular case holds for
`C^∞` maps `ℝⁿ → ℝᵐ`, in the localized form `SardEuclidOn`. -/
theorem sardEuclidOn_of_steps (h : SardSteps) : ∀ N n m : ℕ, n + m = N → SardEuclidOn n m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n m hN
    rcases lt_trichotomy n m with hlt | heq | hgt
    · exact sardEuclidOn_of_lt hlt
    · subst heq
      exact sardEuclidOn_self n
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · -- `m = 0`: the target is a point, so there are no critical points
        subst hm
        intro f U hU hf
        have hcrit : {x : EuclideanSpace ℝ (Fin n) | IsCriticalPoint f x} = ∅ := by
          ext x
          refine ⟨fun hx => hx (fun y => ⟨0, Subsingleton.elim ((fderiv ℝ f x) 0) y⟩),
            fun hx => hx.elim⟩
        rw [show f '' ({x | IsCriticalPoint f x} ∩ U) = ∅ by
          rw [hcrit, Set.empty_inter, Set.image_empty]]
        simp
      · -- `0 < m < n`: both `n` and `m` are successors
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hN' : N = n' + m' + 2 := by omega
        have h1 : SardEuclidOn n' m' := ih (n' + m') (by omega) n' m' rfl
        have h2 : SardEuclidOn n' (m' + 1) := ih (n' + (m' + 1)) (by omega) n' (m' + 1) rfl
        intro f U hU hf
        have hA : volume (f '' (({x | IsCriticalPoint f x} \ Zk f 1) ∩ U)) = 0 :=
          h.notFlat n' m' h1 f U hU hf
        have hB : ∀ k : ℕ, volume (f '' ((Zk f (k+1) \ Zk f (k+2)) ∩ U)) = 0 :=
          fun k => h.strata n' (m' + 1) (k+1) (by omega) h2 f U hU hf
        have hC : volume (f '' (Zk f (n' + 2) ∩ U)) = 0 := by
          refine h.flat (n' + 1) (m' + 1) (n' + 3) (by omega) (by nlinarith) f U hU ?_
          exact hf.of_le ENat.LEInfty.out
        have hBm : volume (⋃ k : ℕ, f '' ((Zk f (k+1) \ Zk f (k+2)) ∩ U)) = 0 :=
          measure_iUnion_null_iff.mpr hB
        have hupper : volume ((f '' (({x | IsCriticalPoint f x} \ Zk f 1) ∩ U)) ∪
            (⋃ k : ℕ, f '' ((Zk f (k+1) \ Zk f (k+2)) ∩ U)) ∪
            (f '' (Zk f (n' + 2) ∩ U))) = 0 :=
          measure_union_null (measure_union_null hA hBm) hC
        refine measure_mono_null ?_ hupper
        rintro z ⟨x, ⟨hx, hxU⟩, rfl⟩
        rcases isCriticalPoint_subset_decomp f (n' + 1) hx with (hA' | hB') | hC'
        · exact Or.inl (Or.inl ⟨x, ⟨hA', hxU⟩, rfl⟩)
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hB'
          exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k, ⟨x, ⟨hk, hxU⟩, rfl⟩⟩))
        · exact Or.inr ⟨x, ⟨hC', hxU⟩, rfl⟩

/-- **Sard's theorem in the rectangular case**, from the three steps. -/
theorem sardEuclid_of_steps (h : SardSteps) (n m : ℕ) : SardEuclid n m :=
  sardEuclid_of_sardEuclidOn (sardEuclidOn_of_steps h (n + m) n m rfl)

end Work.ThomBordism.Transversality.Sard
