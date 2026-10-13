import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilCrux.C1AsmDefs
import Submission.Work.WilCrux.AsmBCont
import Submission.Work.WilCrux.AsmSheetDiff
import Submission.Work.WilCrux.AsmDerivCont

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology ContDiff
open Filter

namespace Work.WilCrux

/-- The two blocks of `fderiv (famFun G)`: off the sheet, the Fréchet derivative of the joint
function is the pairing of the two partial derivatives. -/
theorem fderiv_famFun_eq_pairCLM {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ)
    (hF : HasFDerivAt (Work.WilG4c.famFun G)
      (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
      = pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w)
          (fderiv ℝ (fun z' : Fin b → ℝ => G w z') z) := by
  have happa : HasFDerivAt (fun w' : Fin a → ℝ => Fin.append w' z) (parIncl a b) w := by
    have hfun : (fun w' : Fin a → ℝ => Fin.append w' z)
        = fun w' => parIncl a b w' + fibIncl a b z := by
      funext w'; rw [append_eq_parIncl_add_fibIncl]
    rw [hfun]
    exact (parIncl a b).hasFDerivAt.add_const _
  have happb : HasFDerivAt (fun z' : Fin b → ℝ => Fin.append w z') (fibIncl a b) z := by
    have hfun : (fun z' : Fin b → ℝ => Fin.append w z')
        = fun z' => fibIncl a b z' + parIncl a b w := by
      funext z'
      rw [append_eq_parIncl_add_fibIncl]
      abel
    rw [hfun]
    exact (fibIncl a b).hasFDerivAt.add_const _
  have hpar : fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w
      = (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)).comp (parIncl a b) := by
    have hcomp := hF.comp (x := w) happa
    have hfun : Work.WilG4c.famFun G ∘ (fun w' : Fin a → ℝ => Fin.append w' z)
        = fun w' => G w' z := funext fun w' => famFun_append_eq G w' z
    rw [hfun] at hcomp
    exact hcomp.fderiv
  have hfib : fderiv ℝ (fun z' : Fin b → ℝ => G w z') z
      = (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)).comp (fibIncl a b) := by
    have hcomp := hF.comp (x := z) happb
    have hfun : Work.WilG4c.famFun G ∘ (fun z' : Fin b → ℝ => Fin.append w z')
        = fun z' => G w z' := funext fun z' => famFun_append_eq G w z'
    rw [hfun] at hcomp
    exact hcomp.fderiv
  have hpar' : ∀ u : Fin a → ℝ,
      (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)) (parIncl a b u)
        = fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w u := by
    intro u; simp only [hpar, ContinuousLinearMap.comp_apply]
  have hfib' : ∀ v : Fin b → ℝ,
      (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)) (fibIncl a b v)
        = fderiv ℝ (fun z' : Fin b → ℝ => G w z') z v := by
    intro v; simp only [hfib, ContinuousLinearMap.comp_apply]
  ext v
  calc fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) v
      = fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
          (parIncl a b (parProj a b v) + fibIncl a b (fibProj a b v)) := by
        rw [parIncl_parProj_add_fibIncl_fibProj]
    _ = fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (parIncl a b (parProj a b v))
        + fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (fibIncl a b (fibProj a b v)) := by
        rw [map_add]
    _ = fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w (parProj a b v)
        + fderiv ℝ (fun z' : Fin b → ℝ => G w z') z (fibProj a b v) := by
        rw [hpar', hfib']
    _ = pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' z) w)
          (fderiv ℝ (fun z' : Fin b → ℝ => G w z') z) v := by
        rw [pairCLM_apply]

/-- Every vector of `ℝ^{a+b}` is the gluing of its two blocks. -/
theorem append_parProj_fibProj {a b : ℕ} (v : Fin (a + b) → ℝ) :
    Fin.append (parProj a b v) (fibProj a b v) = v := by
  rw [append_eq_parIncl_add_fibIncl, parIncl_parProj_add_fibIncl_fibProj]

/-- **N4e (the `C^1` assembly, pure analysis).**  Suppose `G : R^a -> R^b -> R` has `C^1`
slices on the ball of radius `r0`, is jointly `C^1` at every off-sheet point `(w,z)`, `z != 0`,
`||z|| < r0`, and on an open `Q6`:

* `a(w) := G w 0` is `C^1` (`ha`),
* the slice derivative is uniformly continuous at the sheet: for every `w0 ∈ Q6` and `eps > 0`
  there is `eta > 0` with `||fderiv (G w) z - fderiv (G w) 0|| < eps` whenever
  `dist w w0 < eta`, `z != 0`, `||z|| < eta` (`hz`),
* the parameter partials converge to the derivative of `a` along the punctured sheet
  (`hw`).

Then `famFun G` is `C^1` at every sheet point `(w0, 0)`, `w0 ∈ Q6`.

Proof: at `(w,0)` (with `b w := fderiv ℝ (G w) 0`),
`F(w+h,z) - F(w,0) - Da(w) h - b(w) z`
`= [a(w+h) - a(w) - Da(w)h] + [b(w+h) - b(w)](z) + ∫_0^1 (fderiv (G(w+h))(t z) -
fderiv (G(w+h))(0))(z) dt`,
which is `o(||(h,z)||)`: the first bracket by `ha`; the second because `w ↦ b w` is continuous
(compare `b(w+h)` with `∂_{z_j}G(w+h,z0)` and `∂_{z_j}G(w,z0)` at a fixed `z0 != 0`, using `hz`
at `w+h` and `w` and continuity of the off-sheet partial); the integral by `hz` at `w+h`.  The
derivative at sheet points is `(Da(w), b(w))`, and its continuity at `(w0,0)` follows from `ha`,
the continuity of `b`, and `hz`/`hw` at the off-sheet points.  Use
`contDiffOn_succ_iff_hasFDerivWithinAt` (or `contDiffAt_iff_eventually`) with the explicit
continuous derivative `(Da(w), b(w))`. -/
theorem C1Assembly {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (hQ6 : IsOpen Q6) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q6, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q6, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (ha : ContDiffOn ℝ 1 (fun w => G w 0) Q6)
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε)
    (hw : ∀ w₀ ∈ Q6, ∀ i : Fin a, Filter.Tendsto
      (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) p.1 (Pi.single i 1))
      (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0)) :
    ∀ w₀ ∈ Q6, ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w₀ 0)
:= by
  intro w₀ hw₀
  have hb : ∀ w ∈ Q6, ContinuousWithinAt (fun w' => fderiv ℝ (G w') 0) Q6 w :=
    AsmBCont G Q6 r0 hr0 hoff hz
  set r1 : ℝ := r0 / 2 with hr1def
  have hr1 : 0 < r1 := by rw [hr1def]; linarith
  have hr1r0 : r1 ≤ r0 := by rw [hr1def]; linarith
  set S : Set (Fin (a + b) → ℝ) := {y | parProj a b y ∈ Q6 ∧ ‖fibProj a b y‖ < r1} with hSdef
  set f' : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) →L[ℝ] ℝ := fun y =>
    pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' (fibProj a b y)) (parProj a b y))
      (fderiv ℝ (G (parProj a b y)) (fibProj a b y)) with hf'def
  have hSopen : IsOpen S := by
    rw [hSdef]
    exact (hQ6.preimage (parProj a b).continuous).inter
      (isOpen_lt ((fibProj a b).continuous.norm) continuous_const)
  have hxS : Fin.append w₀ 0 ∈ S := by
    rw [hSdef]
    exact ⟨by rw [parProj_append]; exact hw₀, by rw [fibProj_append]; simpa using hr1⟩
  have hSnhds : S ∈ 𝓝 (Fin.append w₀ 0) := hSopen.mem_nhds hxS
  -- `f'` agrees with the true derivative off the sheet
  have hf'_off : ∀ y ∈ S, fibProj a b y ≠ 0 → f' y = fderiv ℝ (Work.WilG4c.famFun G) y := by
    intro y hy hyne
    have hyu := hy
    rw [hSdef] at hyu
    obtain ⟨hyQ, hyz⟩ := hyu
    have hyr : ‖fibProj a b y‖ < r0 := lt_of_lt_of_le hyz hr1r0
    have hyeq : Fin.append (parProj a b y) (fibProj a b y) = y := append_parProj_fibProj y
    have hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
        (Fin.append (parProj a b y) (fibProj a b y)) :=
      hoff (parProj a b y) hyQ (fibProj a b y) hyne hyr
    have hF := hC1.differentiableAt_one.hasFDerivAt
    have hA := fderiv_famFun_eq_pairCLM G (parProj a b y) (fibProj a b y) hF
    rw [hf'def]
    show pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' (fibProj a b y)) (parProj a b y))
        (fderiv ℝ (G (parProj a b y)) (fibProj a b y))
      = fderiv ℝ (Work.WilG4c.famFun G) y
    rw [← hA, hyeq]
  have hf'_cont : ContinuousOn f' S := by
    intro y hy
    have hyu := hy
    rw [hSdef] at hyu
    obtain ⟨hyQ, hyz⟩ := hyu
    rcases eq_or_ne (fibProj a b y) 0 with hz0 | hz0
    · -- sheet point: use the pointwise continuity child at `parProj y`
      have hyeq : Fin.append (parProj a b y) 0 = y := by
        rw [← hz0]; exact append_parProj_fibProj y
      have hD := AsmDerivCont G Q6 hQ6 (parProj a b y) hyQ r0 r1 hr0 hr1 hr1r0 hoff ha hz
        (hw (parProj a b y) hyQ) hb
      rw [hf'def]
      rw [← hyeq]
      exact hD
    · -- off-sheet point: `f' = fderiv (famFun G)` nearby, which is continuous there
      have hyr : ‖fibProj a b y‖ < r0 := lt_of_lt_of_le hyz hr1r0
      have hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) y := by
        have h := hoff (parProj a b y) hyQ (fibProj a b y) hz0 hyr
        rwa [append_parProj_fibProj y] at h
      have hcontF : ContinuousWithinAt (fderiv ℝ (Work.WilG4c.famFun G)) S y :=
        (hC1.continuousAt_fderiv (by simp)).continuousWithinAt
      have hne : {y' : Fin (a + b) → ℝ | fibProj a b y' ≠ 0} ∈ 𝓝 y :=
        IsOpen.mem_nhds (isOpen_ne.preimage (fibProj a b).continuous) hz0
      have hev : f' =ᶠ[𝓝[S] y] (fun y' => fderiv ℝ (Work.WilG4c.famFun G) y') := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with y' hyS hyne
        exact hf'_off y' hyS hyne
      exact hcontF.congr_of_eventuallyEq hev (hf'_off y hy hz0)
  have hf'_diff : ∀ y ∈ S, HasFDerivWithinAt (Work.WilG4c.famFun G) (f' y) S y := by
    intro y hy
    have hyu := hy
    rw [hSdef] at hyu
    obtain ⟨hyQ, hyz⟩ := hyu
    rcases eq_or_ne (fibProj a b y) 0 with hz0 | hz0
    · -- sheet point
      have h := AsmSheetDiff G Q6 hQ6 r0 hr0 hsl ha hz hb (parProj a b y) hyQ
      have hyeq : Fin.append (parProj a b y) 0 = y := by
        rw [← hz0]; exact append_parProj_fibProj y
      have h2 : pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y))
          (fderiv ℝ (G (parProj a b y)) 0) = f' y := by
        rw [hf'def]
        show pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) (parProj a b y))
            (fderiv ℝ (G (parProj a b y)) 0)
          = pairCLM a b (fderiv ℝ (fun w' : Fin a → ℝ => G w' (fibProj a b y)) (parProj a b y))
            (fderiv ℝ (G (parProj a b y)) (fibProj a b y))
        rw [hz0]
      rw [h2] at h
      rw [hyeq] at h
      exact h.hasFDerivWithinAt
    · -- off-sheet point
      have hyr : ‖fibProj a b y‖ < r0 := lt_of_lt_of_le hyz hr1r0
      have hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) y := by
        have h := hoff (parProj a b y) hyQ (fibProj a b y) hz0 hyr
        rwa [append_parProj_fibProj y] at h
      rw [hf'_off y hy hz0]
      exact (hC1.differentiableAt_one.hasFDerivAt).hasFDerivWithinAt
  have hmain : ContDiffWithinAt ℝ 1 (Work.WilG4c.famFun G) S (Fin.append w₀ 0) := by
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt (𝕜 := ℝ)
      (n := ((0 : ℕ) : ℕ∞ω)) (by simp)).mpr ?_
    refine ⟨S, ?_, ?_, f', hf'_diff, ?_⟩
    · exact mem_nhdsWithin.mpr ⟨S, hSopen, hxS, Set.inter_subset_left⟩
    · intro h
      exact absurd h (by simp)
    · change ContDiffWithinAt ℝ (0 : ℕ∞ω) f' S (Fin.append w₀ 0)
      rw [contDiffWithinAt_zero hxS]
      exact ⟨Set.univ, Filter.univ_mem, by simpa using hf'_cont⟩
  exact hmain.contDiffAt hSnhds

end Work.WilCrux
