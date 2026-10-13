import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.perz_iter_feps_le
import Submission.Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)
open Work.Spaces (HkIntegrand HkSq HkNorm HkMem Iz Iθ HkIntegrand_nonneg HkNorm_nonneg)

set_option maxHeartbeats 1600000

theorem perz_iter_feps_le_six {α C₀ Ce Cs R Lw ε τ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (hτ : 0 ≤ τ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ →
      Work.FTS.EpsEngine.XBall α ρ ε R C₀
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ → ∀ t : ℝ, t ∈ Set.Icc 0 τ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s z θ
        - Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (h0 : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g₀ z θ) ≤ Bz) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) τ)
        z θ) ≤ Bz := by
  -- the per-curve right-hand-side data, uniform in the Picard index, at level `6`
  obtain ⟨B, _hBpos, hdata⟩ :=
    RHSDataFepsSix.exists_RHSData_feps_six (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hτ hEll hstar hml
  have hdat : ∀ k : ℕ, RHSData α 6 τ B (Feps α ρ ε Φs E) g₀ k :=
    fun k => hdata k (fun s hs => hP k s hs) (fun s hs t ht => hEq k s hs t ht)
  -- the uniform `ℋ⁸`-size of the right-hand side
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball8 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  -- the trace-free per-`z` bound for `ℋ⁶`-profiles
  obtain ⟨Cperz, hCperzpos, hCperz⟩ := HkIntegrand_perz_six_noTraces
  intro z hz
  obtain ⟨Bz0, hBz0⟩ := h0 z hz
  set Cz : ℝ := Cperz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 with hCzdef
  have hCzpos : 0 < Cz := by
    rw [hCzdef]
    have h1 : (0 : ℝ) < 1 + (Work.Spaces.w z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (1 + Ce') ^ 2 := by positivity
    exact mul_pos (mul_pos hCperzpos h1) h2
  refine ⟨2 * max Bz0 0 + 2 * τ ^ 2 * Cz + 1, ?_⟩
  -- (1) the angular energy of the right-hand side along the `k`-th curve is bounded by `Cz`
  have hRHS : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ) ≤ Cz := by
    intro k s hs
    obtain ⟨hsm, hmem8, hbd8⟩ := hFeps (slice (iter (Feps α ρ ε Φs E) g₀ k) s) (hP k s hs)
    have h1 := hCperz α hα hsm hmem8 z hz
    have h2 : (1 + Work.Spaces.HkNorm α 8
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2
        ≤ (1 + Ce') ^ 2 := by
      have hXn : 0 ≤ Work.Spaces.HkNorm α 8
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) :=
        HkNorm_nonneg α 8 _
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ)
        ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α 8
                (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2 := h1
      _ ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cz := by rw [hCzdef]
  -- (2) the primitive of the right-hand side has an honest angular energy at `z`, `≤ τ² Cz`
  have hprim : ∀ k : ℕ,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 6
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        ≤ τ ^ 2 * Cz := by
    intro k
    exact Work.FTS.EpsEngine.PerzPrim.intervalIntegral_perz_le (α := α) (k := 6) (T := τ)
      (τ := τ) (Cz := Cz) (z := z)
      (H := fun s z θ => Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ)
      hτ ⟨hτ, le_rfl⟩ hτ
      (fun s hs => (hdat k).smo s hs)
      (fun s hs => (hdat k).mem s hs)
      (fun j i hji z' θ' hzθ => (hdat k).meas j i hji z' θ' hzθ)
      (fun K hK hKQ => (hdat k).sup K hK hKQ)
      (fun s hs => hRHS k s hs) hCzpos.le hz
  -- (3) `g₀` is smooth on the open quadrant
  have hg0sm : Work.FTS.EllipticEst.SmoothOpen g₀ := by
    have h := (hP 0 τ ⟨hτ, le_rfl⟩).smoothOpen
    rwa [show slice (iter (Feps α ρ ε Φs E) g₀ 0) τ = g₀ from by funext z θ; rfl] at h
  -- (4) the bound for every iterate
  intro n
  cases n with
  | zero =>
    have hslice0 : slice (iter (Feps α ρ ε Φs E) g₀ 0) τ = g₀ := by
      funext z θ; rfl
    rw [hslice0]
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g₀ z θ) ≤ max Bz0 0 :=
      le_trans hBz0 (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ τ ^ 2 * Cz := mul_nonneg (sq_nonneg τ) hCzpos.le
    have h3 : (0 : ℝ) ≤ max Bz0 0 := le_max_right _ _
    linarith
  | succ k =>
    have heq : slice (iter (Feps α ρ ε Φs E) g₀ (k + 1)) τ
        = fun z θ => g₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
      rfl
    rw [heq]
    have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ∫ s in (0 : ℝ)..τ,
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) :=
      smoothOpen_increment hg0sm (hP (k + 1) τ ⟨hτ, le_rfl⟩).smoothOpen
    have hmain := Work.FTS.EpsEngine.PerzPrim.integral_HkIntegrand_add_le (α := α) (k := 6)
      (f := g₀) (g := fun z θ => ∫ s in (0 : ℝ)..τ,
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ)
      hg0sm hQsm hz (B := max Bz0 0) (b := τ ^ 2 * Cz)
      (le_trans hBz0 (le_max_left _ _)) (le_max_right _ _) (hprim k).1 (hprim k).2
      (mul_nonneg (sq_nonneg τ) hCzpos.le)
    exact le_trans hmain (by linarith)

end Work.FTS.EpsEngine
