/-
# The CKMRV kernel on the contour is bounded on the "middle range"

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) Theorem 4.9
constructs the kernel `K^{(d)}` for `d = 8` and `d = 24`.  On a compact `K ⊆ 𝒟` and the
contour `{it : ε ≤ t ≤ 1}` the kernel is bounded: the only poles of `z ↦ K(τ,z)` that can meet
the contour are the two `SL(2,ℤ)`-translates `z = τ` and `z = S τ`, and both have vanishing
residue (`Work.Residues.KPlusClear_diag`, `Work.Asymptotics.KClear_S_vanishing`), so they are
removable.

This file assembles the bound from the local estimates of
`Submission/Work/Asymptotics/KaxisMid/`:

* `Work.Asymptotics.KaxisMid.exists_local_bound_clean` — the bound at parameter points where
  `j τ ≠ j (it)`, obtained from Theorem 4.9(4) (`Work.Asymptotics.KClear_mg2`) and the continuity
  of `j`;
* `Work.Asymptotics.KaxisMid.exists_local_bound_coincidence` — the bound at the coincidences;
* compactness of `K × [ε,1]` turns the local bounds into a single constant.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KaxisMid

open Work.Kernels

/-- `Kaxis` on the parameter space is `Kfun` at the attached contour point. -/
lemma Kaxis_eq_Kfun_pz {ℓ : LogLambdaData} {d : ℕ} {K : Set ℍ} {ε : ℝ} (hε : 0 < ε)
    {q : ℍ × ℝ} (hq : q ∈ Pspace K ε) :
    Kaxis (Kfun ℓ d) q.1 q.2 = Kfun ℓ d q.1 (pz hε q hq) := by
  have hpos : 0 < q.2 := lt_of_lt_of_le hε (mem_Pspace.mp hq).2.1
  rw [Kaxis, dif_pos hpos]
  exact congrArg (Kfun ℓ d q.1) (UpperHalfPlane.ext rfl)

lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- The Euclidean distance of the attached contour points is the distance of the parameters. -/
lemma norm_pz_sub {K : Set ℍ} {ε : ℝ} (hε : 0 < ε) {q q' : ℍ × ℝ}
    (hq : q ∈ Pspace K ε) (hq' : q' ∈ Pspace K ε) :
    ‖((pz hε q hq : ℍ) : ℂ) - ((pz hε q' hq' : ℍ) : ℂ)‖ = |q.2 - q'.2| := by
  rw [pz_coe hε q hq, pz_coe hε q' hq', ← sub_mul, ← Complex.ofReal_sub, norm_mul,
    norm_ofReal_complex, Complex.norm_I, mul_one]

/-- **The CKMRV kernel on the contour is bounded on the "middle range" `ε ≤ t ≤ 1`, uniformly
for `τ` in a compact `K ⊆ 𝒟`.**

This is the easy half of the local flatness statement `Work.Asymptotics.Kaxis_local_flat`; it is
what replaces the global `(scale τ)`-constants of the (false) global version by compactness.
The content is that on a compact subset of `𝒟` the only poles of `z ↦ K(τ,z)` that can meet the
contour `{it : ε ≤ t ≤ 1}` are *removable*. -/
theorem Kaxis_local_middle (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → ε ≤ t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  by_cases hε1 : ε ≤ 1
  · have hP : IsCompact (Pspace K ε) := isCompact_Pspace hK ε
    -- the local bounds
    have hloc : ∀ p : Pspace K ε, ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
        ∀ (q : Pspace K ε), ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < r → |(q.1).2 - (p.1).2| < r →
          ‖Kaxis (Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ C := by
      intro p
      by_cases hcoin : jInvariantFun (p.1).1 = jInvariantFun (pz hε (p.1) p.2)
      · obtain ⟨C, hCpos, r, hrpos, H⟩ :=
          KaxisMid.exists_local_bound_coincidence ℓ d hd hK hsub hε
            ((p.1).1, (p.1).2) p.2 hcoin
        exact ⟨C, hCpos, r, hrpos, fun q hq1 hq2 => by
          rw [Kaxis_eq_Kfun_pz (K := K) (ℓ := ℓ) (d := d) hε q.2]
          exact H q.1 q.2 hq1 hq2⟩
      · obtain ⟨C, hCpos, r, hrpos, H⟩ :=
          exists_local_bound_clean ℓ d hd hK hε ((p.1).1, (p.1).2) p.2
            (fun h => hcoin h)
        refine ⟨C, hCpos, r, hrpos, fun q hq1 hq2 => ?_⟩
        rw [Kaxis_eq_Kfun_pz (K := K) (ℓ := ℓ) (d := d) hε q.2]
        exact H q.1 q.2 hq1 (by rwa [norm_pz_sub hε q.2 p.2])
    classical
    let Cf : Pspace K ε → ℝ := fun p => Classical.choose (hloc p)
    have hCfpos : ∀ p, 0 < Cf p := fun p => (Classical.choose_spec (hloc p)).1
    let rf : Pspace K ε → ℝ := fun p => Classical.choose (Classical.choose_spec (hloc p)).2
    have hrfpos : ∀ p, 0 < rf p :=
      fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).1
    have hbound : ∀ (p q : Pspace K ε),
        ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p → |(q.1).2 - (p.1).2| < rf p →
        ‖Kaxis (Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ Cf p :=
      fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).2
    -- the open cover
    have hopen : ∀ p : Pspace K ε, IsOpen {q : ℍ × ℝ |
        ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
      intro p
      have h1 : IsOpen {q : ℍ × ℝ | ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p} :=
        isOpen_lt (Continuous.norm ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
          continuous_const)) continuous_const
      have h2 : IsOpen {q : ℍ × ℝ | |q.2 - (p.1).2| < rf p} :=
        isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
      exact h1.inter h2
    have hcover : Pspace K ε ⊆ ⋃ p : Pspace K ε, {q : ℍ × ℝ |
        ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
      intro q hq
      refine Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
      exact ⟨by simpa using hrfpos ⟨q, hq⟩, by simpa using hrfpos ⟨q, hq⟩⟩
    obtain ⟨s, hs⟩ := hP.elim_finite_subcover
      (fun p : Pspace K ε => {q : ℍ × ℝ |
        ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p})
      hopen hcover
    have hsum : (0:ℝ) < (∑ p ∈ s, Cf p) + 1 := by
      have := Finset.sum_nonneg (s := s) (f := Cf) (fun p _ => (hCfpos p).le)
      linarith
    refine ⟨(∑ p ∈ s, Cf p) + 1, hsum, fun τ t hτK hεt ht1 => ?_⟩
    have hq : (τ, t) ∈ Pspace K ε := ⟨hτK, hεt, ht1⟩
    have hmem := hs hq
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨p, hps, hpU⟩ := hmem
    have hle := hbound p ⟨(τ, t), hq⟩ hpU.1 hpU.2
    refine le_trans (le_of_eq ?_) (le_trans hle ?_)
    · rfl
    · have := Finset.single_le_sum (s := s) (f := Cf) (fun x _ => (hCfpos x).le) hps
      linarith
  · rw [not_le] at hε1
    exact ⟨1, one_pos, fun τ t _ ht ht1 => absurd (lt_of_lt_of_le hε1 ht) (not_lt.mpr ht1)⟩

end Work.Asymptotics.KaxisMid
