import Mathlib
import Submission.Work.Diff.EXT.ConnCov.HonestTower.Kit
import Submission.Work.Diff.EXT.ConnCov.HonestTower.gp_smooth_step
import Submission.Work.Diff.EXT.ConnCov.HonestTower.gp_loc_step
import Submission.Work.Diff.EXT.ConnCov.HonestTower.gp_lin_step

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT.ConnCov.HonestTower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **The induction step** for the invariant of the packed honest tower. -/
theorem tensPropG_succ (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hih : TensPropG (I := I) (M := M) g base k) :
    TensPropG (I := I) (M := M) g base (k + 1) := by
  intro F hF
  refine ⟨gp_smooth_step hLC g base k hih hF, ?_, ?_⟩
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    refine Fin.cases ?_ ?_ s
    · rw [update_zero_eq_consG, update_zero_eq_consG, update_zero_eq_consG]
      exact gp_lin_dir_step hLC g base k hih (fun i => hF i.succ) hX₁ hX₂ hf₁ hf₂
    · intro j
      rw [update_succ_eq_consG, update_succ_eq_consG, update_succ_eq_consG]
      exact gp_lin_tail_step hLC g base k hih (fun i => hF i.succ) (hF 0) hX₁ hX₂ hf₁ hf₂ j
  · intro x F' hF' h
    exact gp_loc_step hLC g base k hih hF hF' h

/-- **The invariant for all levels**, from the four hypotheses on `base`. -/
theorem tensPropG_all (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hsm : ∀ (v : Fin 0 → Tf (I := I) (M := M)) (A B C : Tf (I := I) (M := M)),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) B → Sm (I := I) (M := M) C →
      CMDiff ∞ (base v A B C))
    (hlinA : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (B C : Tf (I := I) (M := M)) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (A C : Tf (I := I) (M := M)) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hvd : ∀ (b0 : Fin 0 → Tf (I := I) (M := M))
      (A A' B B' C C' : Tf (I := I) (M := M)) (x : M),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) A' →
      Sm (I := I) (M := M) B → Sm (I := I) (M := M) B' →
      Sm (I := I) (M := M) C → Sm (I := I) (M := M) C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x) :
    ∀ k : ℕ, TensPropG (I := I) (M := M) g base k := by
  intro k
  induction k with
  | zero => exact tensPropG_zero g hsm hlinA hlinB hvd
  | succ k ih => exact tensPropG_succ hLC g base k ih

/-- Additivity (two-term with constant coefficients `1`) in every slot, from the invariant. -/
theorem TensPropG_add (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) {k : ℕ}
    (h : TensPropG (I := I) (M := M) g base k)
    {F : Fin (k + 2) → Tf (I := I) (M := M)} (hF : ∀ s, Sm (I := I) (M := M) (F s))
    (s : Fin (k + 2)) {X Y : Tf (I := I) (M := M)}
    (hX : Sm (I := I) (M := M) X) (hY : Sm (I := I) (M := M) Y) :
    gP g base k (Function.update F s (X + Y))
      = gP g base k (Function.update F s X) + gP g base k (Function.update F s Y) := by
  have h1 := (h F hF).2.1 s X Y (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hX hY
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  have e1 : (fun _ : M => (1 : ℝ)) • X + (fun _ : M => (1 : ℝ)) • Y = X + Y := by
    funext z; simp
  have e2 : (fun _ : M => (1 : ℝ)) • gP g base k (Function.update F s X)
      = gP g base k (Function.update F s X) := by funext z; simp
  have e3 : (fun _ : M => (1 : ℝ)) • gP g base k (Function.update F s Y)
      = gP g base k (Function.update F s Y) := by funext z; simp
  rw [e1, e2, e3] at h1
  exact h1

/-- Scalar homogeneity in every slot, from the invariant. -/
theorem TensPropG_smul (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) {k : ℕ}
    (h : TensPropG (I := I) (M := M) g base k)
    {F : Fin (k + 2) → Tf (I := I) (M := M)} (hF : ∀ s, Sm (I := I) (M := M) (F s))
    (s : Fin (k + 2)) (c : ℝ) {X : Tf (I := I) (M := M)} (hX : Sm (I := I) (M := M) X) :
    gP g base k (Function.update F s ((fun _ : M => c) • X))
      = (fun _ : M => c) • gP g base k (Function.update F s X) := by
  have h1 := (h F hF).2.1 s X X (fun _ : M => c) (fun _ : M => (0 : ℝ)) hX hX
    (contMDiff_const (c := c)) (contMDiff_const (c := (0 : ℝ)))
  have e1 : (fun _ : M => c) • X + (fun _ : M => (0 : ℝ)) • X = (fun _ : M => c) • X := by
    funext z; simp
  have e2 : (fun _ : M => c) • gP g base k (Function.update F s X)
      + (fun _ : M => (0 : ℝ)) • gP g base k (Function.update F s X)
      = (fun _ : M => c) • gP g base k (Function.update F s X) := by funext z; simp
  rw [e1, e2] at h1
  exact h1

/-- **Single-slot value dependence of the packed honest tower.** -/
theorem gP_val_dep (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hsm : ∀ (v : Fin 0 → Tf (I := I) (M := M)) (A B C : Tf (I := I) (M := M)),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) B → Sm (I := I) (M := M) C →
      CMDiff ∞ (base v A B C))
    (hlinA : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (B C : Tf (I := I) (M := M)) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → Tf (I := I) (M := M)) (X₁ X₂ : Tf (I := I) (M := M))
      (f₁ f₂ : M → ℝ),
      CMDiff ∞ f₁ → CMDiff ∞ f₂ → Sm (I := I) (M := M) X₁ → Sm (I := I) (M := M) X₂ →
      ∀ (A C : Tf (I := I) (M := M)) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hvd : ∀ (b0 : Fin 0 → Tf (I := I) (M := M))
      (A A' B B' C C' : Tf (I := I) (M := M)) (x : M),
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) A' →
      Sm (I := I) (M := M) B → Sm (I := I) (M := M) B' →
      Sm (I := I) (M := M) C → Sm (I := I) (M := M) C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x)
    (k : ℕ) (x : M)
    {FS : Fin (k + 2) → Tf (I := I) (M := M)} (hFS : ∀ s, Sm (I := I) (M := M) (FS s))
    (s : Fin (k + 2)) {X X' : Tf (I := I) (M := M)}
    (hX : Sm (I := I) (M := M) X) (hX' : Sm (I := I) (M := M) X') (h : X x = X' x) :
    gP g base k (Function.update FS s X) x = gP g base k (Function.update FS s X') x := by
  have hTP := tensPropG_all hLC g hsm hlinA hlinB hvd k
  have h1 : ∀ (X₁ X₂ : Tf (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      CMDiff ∞ (T% X₁) → CMDiff ∞ (T% X₂) → CMDiff ∞ f₁ → CMDiff ∞ f₂ →
      (fun W : Tf (I := I) (M := M) => gP g base k (Function.update FS s W) x)
          (f₁ • X₁ + f₂ • X₂)
        = f₁ x * (fun W : Tf (I := I) (M := M) => gP g base k (Function.update FS s W) x) X₁
          + f₂ x * (fun W : Tf (I := I) (M := M) => gP g base k (Function.update FS s W) x) X₂ := by
    intro X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    have h2 := congrFun ((hTP FS hFS).2.1 s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂) x
    simpa only [Pi.add_apply, Pi.mul_apply, smul_eq_mul] using h2
  have h3 : ∀ (X Y : Tf (I := I) (M := M)), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
      X =ᶠ[𝓝 x] Y →
      (fun W : Tf (I := I) (M := M) => gP g base k (Function.update FS s W) x) X
        = (fun W : Tf (I := I) (M := M) => gP g base k (Function.update FS s W) x) Y := by
    intro X Y hX' hY' heq
    have h4 : ∀ q, (Function.update FS s X) q =ᶠ[𝓝 x] (Function.update FS s Y) q := by
      intro q
      rcases eq_or_ne q s with hq | hq
      · subst hq; rw [Function.update_self, Function.update_self]; exact heq
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]; try rfl
    exact (((hTP (Function.update FS s X) (sm_update hFS hX')).2.2 x
      (Function.update FS s Y) (sm_update hFS hY') h4)).eq_of_nhds
  exact Work.Diff.GE.field_value_dep_of_linear x h1 h3 hX hX' h

/-- **The finite-sum (single-slot) expansion** of the packed honest tower. -/
theorem gP_lin_sum (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) {k : ℕ}
    (h : TensPropG (I := I) (M := M) g base k)
    {F : Fin (k + 2) → Tf (I := I) (M := M)} (hF : ∀ s, Sm (I := I) (M := M) (F s))
    (s : Fin (k + 2)) {ι : Type*} [Fintype ι]
    (X : ι → Tf (I := I) (M := M)) (c : ι → ℝ) (S : Tf (I := I) (M := M))
    (hX : ∀ q, Sm (I := I) (M := M) (X q)) (hS : Sm (I := I) (M := M) S)
    (hrep : ∀ y : M, S y = ∑ q, c q • X q y) :
    ∀ y : M, gP g base k (Function.update F s S) y
      = ∑ q, c q * gP g base k (Function.update F s (X q)) y := by
  classical
  have hadd : ∀ (X₁ X₂ : Tf (I := I) (M := M)), Sm (I := I) (M := M) X₁ →
      Sm (I := I) (M := M) X₂ →
      ∀ y : M, gP g base k (Function.update F s (X₁ + X₂)) y
        = gP g base k (Function.update F s X₁) y + gP g base k (Function.update F s X₂) y := by
    intro X₁ X₂ h₁ h₂ y
    have hh := TensPropG_add hLC g base h hF s h₁ h₂
    exact congrFun hh y
  have hsmul : ∀ (f₀ : M → ℝ) (X₀ : Tf (I := I) (M := M)), CMDiff ∞ f₀ →
      Sm (I := I) (M := M) X₀ → ∀ y : M,
      gP g base k (Function.update F s (f₀ • X₀)) y
        = f₀ y * gP g base k (Function.update F s X₀) y := by
    intro f₀ X₀ hf₀ hX₀ y
    have hh := (h F hF).2.1 s X₀ X₀ f₀ (fun _ : M => (0 : ℝ)) hX₀ hX₀ hf₀
      (contMDiff_const (c := (0 : ℝ)))
    have hh' := congrFun hh y
    have e : f₀ • X₀ + (fun _ : M => (0 : ℝ)) • X₀ = f₀ • X₀ := by funext z; simp
    rw [e] at hh'
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply', Pi.zero_apply, smul_eq_mul,
      zero_mul, add_zero] using hh'
  have hsmE : ∀ (f₀ : ι → ℝ) (X₀ : ι → Tf (I := I) (M := M)),
      (∀ q, Sm (I := I) (M := M) (X₀ q)) →
      ∀ s' : Finset ι, Sm (I := I) (M := M) (fun y => ∑ q ∈ s', f₀ q • X₀ q y) := by
    intro f₀ X₀ hX₀ s'
    induction s' using Finset.induction_on with
    | empty =>
        have : (fun y : M => ∑ q ∈ (∅ : Finset ι), f₀ q • X₀ q y)
            = (0 : Tf (I := I) (M := M)) := by funext y; simp
        rw [this]; exact sm_zeroField
    | insert q s' hq ih =>
        have hh : (fun y : M => ∑ q' ∈ insert q s', f₀ q' • X₀ q' y)
            = (fun _ : M => f₀ q) • X₀ q
              + (fun y : M => ∑ q' ∈ s', f₀ q' • X₀ q' y) := by
          funext y; rw [Finset.sum_insert hq]; rfl
        rw [hh]
        exact (contMDiff_const (c := f₀ q)).smul_section (hX₀ q) |>.add_section ih
  have key : ∀ s' : Finset ι, ∀ (T : Tf (I := I) (M := M)), Sm (I := I) (M := M) T →
      (∀ y : M, T y = ∑ q ∈ s', c q • X q y) → ∀ y : M,
      gP g base k (Function.update F s T) y
        = ∑ q ∈ s', c q * gP g base k (Function.update F s (X q)) y := by
    intro s'
    induction s' using Finset.induction_on with
    | empty =>
        intro T hT hrepT y
        have h0 : T = (fun _ : M => (0 : ℝ)) • T := by funext z; rw [hrepT z]; simp
        rw [h0, hsmul (fun _ : M => (0 : ℝ)) T contMDiff_const hT y]
        simp
    | insert q s' hq ih =>
        intro T hT hrepT y
        have htail : Sm (I := I) (M := M) (fun y' : M => ∑ q' ∈ s', c q' • X q' y') :=
          hsmE c X hX s'
        have hsplit : T = (fun _ : M => c q) • X q
            + (fun y' : M => ∑ q' ∈ s', c q' • X q' y') := by
          funext y'
          rw [hrepT y', Finset.sum_insert hq, Pi.add_apply]
          rfl
        rw [hsplit, hadd ((fun _ : M => c q) • X q)
            (fun y' : M => ∑ q' ∈ s', c q' • X q' y')
            ((contMDiff_const (c := c q)).smul_section (hX q)) htail y,
          hsmul (fun _ : M => c q) (X q) contMDiff_const (hX q) y,
          ih (fun y' : M => ∑ q' ∈ s', c q' • X q' y') htail (fun _ => rfl) y,
          Finset.sum_insert hq]
  exact fun y => key Finset.univ S hS (fun y => hrep y) y

end Work.Diff.EXT.ConnCov.HonestTower
