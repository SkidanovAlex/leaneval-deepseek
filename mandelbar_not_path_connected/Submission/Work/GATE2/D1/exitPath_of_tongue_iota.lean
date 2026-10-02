import Mathlib
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.PARIMPL.All
import Submission.Work.GATE2.D1.close_iterate_on_ball
import Submission.Work.GATE2.D1.green_comparison_near_compactum
import Submission.Work.GATE2.D1.psi_iterate_shift
import Submission.Work.GATE2.PL.deviation_small_near_compactum
import Submission.Work.GATE2.PL.bTongue_exitTime
import Submission.Work.GATE2.PL.Defs
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Contraction.green_eq_greenFun

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.GATE2.D1

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## Elementary Green facts -/

/-- The Green function at the critical value equals twice its value at the critical point. -/
private theorem green_crit (c : ℂ) : Work.Bottcher.green c c = 2 * Work.Bottcher.green c 0 := by
  have h := Work.Bottcher.Green.green_comm c 0
  simpa [LeanEval.ComplexAnalysis.Tantibar] using h

/-- The Green function commutes with the iterates of `T_c` up to the factor `2 ^ n`. -/
private theorem green_Tant_iterate (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.Bottcher.green c z := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Work.Bottcher.Green.green_comm, ih, pow_succ]
      ring

/-- The Green functional equation for the second return map `F_c = (T_c)^[10]`:
`G_c ((F_c)^[k] z) = 1024^k * G_c z`. -/
private theorem green_Ft_iterate (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.EL.F c)^[k] z) = (1024 : ℝ) ^ k * Work.Bottcher.green c z := by
  have hF : (Work.EL.F c)^[k] = (Tantibar c)^[10 * k] := by
    rw [Work.EL.F_eq_tantibar, ← Function.iterate_mul]
  rw [hF, green_Tant_iterate,
    show (2 : ℝ) ^ (10 * k) = (1024 : ℝ) ^ k by rw [pow_mul]; norm_num]

/-- A point whose `N`-th iterate under the second return map lies in the filled Julia set is
itself in the filled Julia set. -/
private theorem mem_K_of_iterate_mem_K {c : ℂ} (N : ℕ) {z : ℂ}
    (h : (Work.EL.F c)^[N] z ∈ Work.EL.K c) : z ∈ Work.EL.K c := by
  have hF : (Work.EL.F c)^[N] = (Tantibar c)^[10 * N] := by
    rw [Work.EL.F_eq_tantibar, ← Function.iterate_mul]
  rw [hF] at h
  simp only [Work.EL.K, Work.ParamRays.filledJulia, Work.ParamRays.BoundedOrbit,
    Work.ParamRays.orbit, Set.mem_setOf_eq] at h ⊢
  obtain ⟨M₁, hM₁⟩ := h
  refine ⟨M₁ + ∑ j ∈ Finset.range (10 * N), ‖(Tantibar c)^[j] z‖, fun n => ?_⟩
  have hM₁' : ∀ m : ℕ, ‖(Tantibar c)^[m] ((Tantibar c)^[10 * N] z)‖ ≤ M₁ := hM₁
  have hM₁nonneg : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁' 0)
  rcases le_or_gt (10 * N) n with hn | hn
  · have hn' : n = (n - 10 * N) + 10 * N := (Nat.sub_add_cancel hn).symm
    rw [hn', Function.iterate_add_apply]
    have := hM₁' (n - 10 * N)
    have hS : 0 ≤ ∑ j ∈ Finset.range (10 * N), ‖(Tantibar c)^[j] z‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    linarith
  · have hmem : n ∈ Finset.range (10 * N) := Finset.mem_range.mpr hn
    have hle : ‖(Tantibar c)^[n] z‖ ≤ ∑ j ∈ Finset.range (10 * N), ‖(Tantibar c)^[j] z‖ :=
      Finset.single_le_sum (f := fun j => ‖(Tantibar c)^[j] z‖) (fun i _ => norm_nonneg _) hmem
    linarith

/-! ## The critical domain -/

/-- The parameter potential of a root-parabolic parameter vanishes. -/
private theorem paramPotential_eq_zero_of_rootParabolic {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    Work.ParamRays.paramPotential c₀ = 0 := by
  have h : Work.ParamRays.greenFun c₀ 0 = 0 :=
    (Work.ParamRays.greenFun_eq_zero_iff c₀ 0).mpr
      ((Work.ParamRays.mem_mandelbar_iff_bounded c₀).mp (Work.FSeed.API.mem_Mandelbar d))
  simpa [Work.ParamRays.paramPotential] using h

/-- A point off the filled Julia set of a root-parabolic parameter lies in the critical domain. -/
private theorem mem_critDomain_of_notMem_K {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) {z : ℂ}
    (hz : z ∉ Work.EL.K c₀) : z ∈ Work.ParamRays.critDomain c₀ := by
  change Work.ParamRays.paramPotential c₀ < Work.ParamRays.greenFun c₀ z
  rw [paramPotential_eq_zero_of_rootParabolic d, ← Work.Bottcher.Contraction.green_eq_greenFun]
  exact Work.PARIMPL.green_pos_of_notMem_K hz

/-! ## A `ε`-`δ` form of the joint continuity of the iterates -/

/-- **Uniform continuity of the `N`-th iterate at a point of the `(c,z)`-plane.** -/
private theorem iter_close_at {c₀ z₀ : ℂ} (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ e z : ℂ, ‖e - c₀‖ < ρ → ‖z - z₀‖ < ρ →
      ‖(Work.PARIMPL.Ft e)^[N] z - (Work.PARIMPL.Ft c₀)^[N] z₀‖ ≤ ε := by
  intro ε hε
  have hcont : Continuous (fun p : ℂ × ℂ => ((Work.PARIMPL.Ft p.1)^[N]) p.2) :=
    Work.PARIMPL.continuous_orbit_pair N
  have hca := hcont.continuousAt (x := (c₀, z₀))
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨δ, hδpos, hδ⟩ := hca ε hε
  refine ⟨δ / 2, by linarith, ?_⟩
  intro e z he hz
  have hmem : dist (e, z) (c₀, z₀) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rw [dist_eq_norm]; linarith, by rw [dist_eq_norm]; linarith⟩
  simpa [dist_eq_norm, Prod.fst, Prod.snd] using le_of_lt (hδ hmem)


/-! ## The Fatou parametrisation lands in the filled Julia set -/

section Fatou

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
variable {v : ℝ}

/-- The invariant sub-petal `Pg` of the flower lies in the filled Julia set. -/
private theorem Pg_subset_K : FF.Pg ⊆ Work.EL.K c₀ :=
  FF.Pg_sub.trans (Work.ELRig.Pa_subset_K fl)

/-- **The principal Fatou parametrisation lands in the filled Julia set.**  At a level `w` of the
slit plane, `ψ w` is obtained from a far-right level (where `ψ` is the inverse Fatou coordinate,
hence a point of `Pg ⊆ K`) by applying `F^[N]`, and the filled Julia set is totally invariant
backwards (`mem_K_of_iterate_mem_K`). -/
private theorem psi_mem_K (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa v)
    {w : ℂ} (hw : w ∈ Work.GATE2.slitAt v) : hPL.ψ w ∈ Work.EL.K c₀ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (hPL.X - w.re)
  have hshift : (Work.EL.F c₀)^[N] (hPL.ψ w) = hPL.ψ (w + (N : ℂ)) :=
    psi_iterate_shift hPL N hw
  have hfar : hPL.X < (w + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hPg : hPL.ψ (w + (N : ℂ)) ∈ FF.Pg := (hPL.far _ hfar).1
  have hK : hPL.ψ (w + (N : ℂ)) ∈ Work.EL.K c₀ := Pg_subset_K FF hPg
  rw [← hshift] at hK
  exact mem_K_of_iterate_mem_K N hK

/-- The Fatou parametrisation is uniformly bounded on the slit plane. -/
private theorem psi_norm_le (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa v)
    {w : ℂ} (hw : w ∈ Work.GATE2.slitAt v) : ‖hPL.ψ w‖ ≤ max 2 ‖c₀‖ :=
  Work.ParamRays.norm_le_max_of_bounded c₀ _ (psi_mem_K FF hPL hw)

end Fatou

/-! ## Reparametrisation of the unit interval -/

/-- The point `2t` of the unit interval, when `t ≤ 1/2`. -/
private def rep (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : unitInterval :=
  ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h]⟩

/-- The point `2t - 1` of the unit interval, when `1/2 < t`. -/
private def repm (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : unitInterval :=
  ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h]⟩

@[simp] private theorem rep_val (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    ((rep t h : unitInterval) : ℝ) = 2 * (t : ℝ) := rfl

@[simp] private theorem repm_val (t : unitInterval) (h : 1 / 2 < (t : ℝ)) :
    ((repm t h : unitInterval) : ℝ) = 2 * (t : ℝ) - 1 := rfl

private theorem trans_le {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : γ.trans γ' t = γ (rep t h) := by
  rw [Path.trans_apply, dif_pos h]
  refine congrArg γ (Subtype.ext ?_)
  simp [rep]

private theorem trans_gt {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : γ.trans γ' t = γ' (repm t h) := by
  rw [Path.trans_apply, dif_neg (not_le.mpr h)]
  refine congrArg γ' (Subtype.ext ?_)
  simp [repm]

/-! ## The general D1 statement -/

/-- A bound on the range of the iterated difference of a straight segment. -/
private theorem norm_lineMap_sub_right (a b : ℂ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖AffineMap.lineMap a b s - b‖ ≤ ‖a - b‖ := by
  have heq : AffineMap.lineMap a b s - b = (1 - s) • (a - b) := by
    rw [AffineMap.lineMap_apply_module]; module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have := norm_nonneg (a - b)
  nlinarith

/-- A bound on the range of the initial segment of a straight segment. -/
private theorem norm_lineMap_sub_left (a b : ℂ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖AffineMap.lineMap a b s - a‖ ≤ ‖a - b‖ := by
  have heq : AffineMap.lineMap a b s - a = s • (b - a) := by
    rw [AffineMap.lineMap_apply_module]; module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, norm_sub_rev b a]
  have := norm_nonneg (a - b)
  nlinarith

/-- **D1, in the general form.**  From PL, the exit loop `ExitLoop` at the level `x₀` and the
floored UT, the exit-path datum `ExitPathData` at the level `x₀` with the root angle `α` and the
tongue predicate `bTongue` holds. -/
theorem exitPathData_of_exitLoop {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    {v : ℝ} {x₀ : ℝ} {α : ℝ}
    (hPa : Pa = fl.Pa) (hφa : φa = fl.φa) (hΨ : Ψ = fl.Ψ)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa v)
    (hEXL : Work.GATE2.ExitLoop c₀ fl.Ψ x₀ L.r₀ v α)
    (hUT : Work.GATE2.TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (hPL.X + 1) v) :
    Work.GATE2.ExitPathData c₀ P.Nm (Work.PARIMPL.transU P M.nIn) x₀ L.r₀
      (fun e => Work.GATE.bTongue (Work.PARIMPL.transU P M.nIn) x₀ L.r₀ e) α := by
  classical
  -- ### Compactness of `K₀`: a norm bound and a left bound on the real part
  obtain ⟨Bk, hBk⟩ : ∃ Bk : ℝ, ∀ w ∈ hEXL.K₀, ‖w‖ ≤ Bk :=
    hEXL.isCompact_K₀.isBounded.exists_norm_le
  have hx₀ball : (((x₀ : ℝ)) : ℂ) ∈ Metric.closedBall (((x₀ : ℝ)) : ℂ) L.r₀ := by
    rw [Metric.mem_closedBall, dist_self]; exact le_of_lt L.hr₀
  obtain ⟨lam₀, hlam₀, -, hK₀, -, -⟩ := hEXL.loop _ hx₀ball
  have hBk0 : 0 ≤ Bk := le_trans (norm_nonneg _) (hBk _ (hK₀ 0))
  -- ### The uniform constants
  set B : ℝ := Bk + ‖(((x₀ : ℝ)) : ℂ) - 1‖ + L.r₀ + 1 with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ ‖(((x₀ : ℝ)) : ℂ) - 1‖ := norm_nonneg _
    linarith [hBk0, L.hr₀]
  have hBpos : 0 < B := by linarith
  set W : ℝ := 2 * B + 2 + max 0 (v + B - (hPL.X + 1)) with hWdef
  have hWbig : 2 * B + 2 ≤ W := by
    rw [hWdef]
    exact le_add_of_nonneg_right (le_max_left _ _)
  set Xo : ℝ := Bk with hXodef
  -- ### The uniform deviations
  obtain ⟨ηd, hηdpos, ρd, hρdpos, hdevd⟩ :=
    Work.GATE2.PL.deviation_small_near_compactum (𝒦 := hEXL.𝒦) (α := α) (c₀ := c₀)
      hEXL.isCompact (fun z hz => mem_critDomain_of_notMem_K d (hEXL.offK z hz)) hEXL.win
  obtain ⟨ηg, hηgpos, ρg, hρgpos, hgreend⟩ :=
    Work.GATE2.D1.green_comparison_near_compactum (K := hEXL.𝒦) (c₀ := c₀)
      hEXL.isCompact (fun z hz => Work.PARIMPL.green_pos_of_notMem_K (hEXL.offK z hz))
  set η : ℝ := min (ηd / 2) (ηg / 2) with hηdef
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hηlt_d : η < ηd := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηlt_g : η < ηg := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- ### UT at the fixed box and window
  obtain ⟨X₁, ρUT, hX₁b, hρUTpos, hUT'⟩ := hUT B W Xo η hηpos
  have hXb : hPL.X + 1 ≤ X₁ := hX₁b
  have hXlt : hPL.X < X₁ := by linarith
  -- ### The integer `N₀` placing the levels in UT's box
  set N₀ : ℕ := Nat.ceil (max (X₁ + B - v) 0) with hN₀def
  have hN₀b : (N₀ : ℝ) < max (X₁ + B - v) 0 + 1 :=
    Nat.ceil_lt_add_one (le_max_right _ _)
  have hN₀low : X₁ + B ≤ v + (N₀ : ℝ) := by
    have h := le_trans (le_max_left _ _) (Nat.le_ceil (max (X₁ + B - v) 0))
    linarith
  have hN₀high : v + (N₀ : ℝ) + B ≤ X₁ + W := by
    rcases le_or_gt 0 (X₁ + B - v) with ha | ha
    · rw [max_eq_left ha] at hN₀b
      linarith
    · rw [max_eq_right (le_of_lt ha)] at hN₀b
      have hN₀0 : N₀ = 0 := by
        have h1 : (N₀ : ℝ) < 1 := by linarith
        have h2 : (N₀ : ℤ) < 1 := by exact_mod_cast h1
        omega
      rw [hN₀0]
      simp only [Nat.cast_zero, add_zero]
      have hle : v + B - X₁ ≤ max 0 (v + B - (hPL.X + 1)) := by
        refine le_trans ?_ (le_max_right _ _)
        linarith [hX₁b]
      have hWge : max 0 (v + B - (hPL.X + 1)) ≤ W := by
        rw [hWdef]; linarith [hBpos]
      linarith
  have hN₀far : hPL.X < v + (N₀ : ℝ) - B := by linarith [hN₀low, hXb]
  -- ### The radii
  obtain ⟨ρL, hρLpos, hρL⟩ := iter_close_at (c₀ := c₀) (z₀ := c₀) N₀ ρUT hρUTpos
  have hmemv : (v : ℂ) ∈ Work.GATE2.slitAt v := by
    rw [Work.GATE2.slitAt, Set.mem_ofPred_eq]
    rintro ⟨h1, h2⟩
    simp only [Complex.ofReal_im] at h1
    simp only [Complex.ofReal_re] at h2
    linarith
  have hψv : hPL.ψ (v : ℂ) = c₀ := hPL.ψv
  have hc₁ : hPL.ψ ((v : ℂ) + 1) = Work.EL.F c₀ c₀ := by
    have h := hPL.shift (v : ℂ) hmemv
    rw [hPL.ψv] at h
    exact h.symm
  obtain ⟨ρR, hρRpos, hρR⟩ := iter_close_at (c₀ := c₀) (z₀ := hPL.ψ ((v : ℂ) + 1)) N₀ ρUT hρUTpos
  obtain ⟨ρC, hρCpos, hρC⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ e : ℂ, ‖e - c₀‖ < ρ → ‖(Work.EL.F e) e - hPL.ψ ((v : ℂ) + 1)‖ < ρR := by
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp
      ((Work.PARIMPL.continuous_orbit_diag 1).continuousAt (x := c₀)) ρR hρRpos
    refine ⟨ρ, hρpos, fun e he => ?_⟩
    have h := hρ (x := e) (by rw [dist_eq_norm]; exact he)
    rw [show (((Work.PARIMPL.Ft e)^[1]) e) = (Work.EL.F e) e from rfl] at h
    rw [show (((Work.PARIMPL.Ft c₀)^[1]) c₀) = (Work.EL.F c₀) c₀ from rfl, ← hc₁] at h
    rwa [dist_eq_norm] at h
  obtain ⟨ρmid, hρmidpos, hρmid⟩ :=
    close_iterate_on_ball (c₀ := c₀) N₀ (max 2 ‖c₀‖) ρUT hρUTpos
  obtain ⟨ρt, hρtpos, hρt⟩ := Work.GATE2.PL.bTongue_exitTime
    (c₀ := c₀) (P := P) (M := M) (T := T) (y₀ := x₀) (r := L.r₀) (N₀ + 2)
  -- ### The outer radius
  set ρ : ℝ := min ρUT (min ρL (min ρR (min ρC (min ρmid (min ρd (min ρg ρt)))))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρUTpos (lt_min hρLpos (lt_min hρRpos (lt_min hρCpos
      (lt_min hρmidpos (lt_min hρdpos (lt_min hρgpos hρtpos))))))
  have hρ_UT : ρ ≤ ρUT := by rw [hρdef]; exact min_le_left _ _
  have hρ_L : ρ ≤ ρL := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_R : ρ ≤ ρR := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ_C : ρ ≤ ρC := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρ_mid : ρ ≤ ρmid := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hρ_d : ρ ≤ ρd := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hρ_g : ρ ≤ ρg := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hρ_t : ρ ≤ ρt := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))))
  refine ⟨ρ, hρpos, ?_⟩
  intro e he hbt hMb
  -- ### The tongue data
  have heball : dist e c₀ < ρ := Metric.mem_ball.mp he.2
  have hen : ‖e - c₀‖ < ρ := by rwa [dist_eq_norm] at heball
  have heballUT : e ∈ Metric.ball c₀ ρUT := Metric.mem_ball.mpr (lt_of_lt_of_le heball hρ_UT)
  obtain ⟨k, hkdist, hkge⟩ :=
    hρt e ⟨he.1, Metric.mem_ball.mpr (lt_of_lt_of_le heball hρ_t)⟩ hbt
  set m : ℕ := ((M.nIn : ℤ) - k).toNat with hmdef
  have hmz : (m : ℤ) = (M.nIn : ℤ) - k := by
    have h0 : (0 : ℤ) ≤ (M.nIn : ℤ) - k := by omega
    rw [hmdef, Int.toNat_of_nonneg h0]
  have hmge : N₀ + 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmzc : (m : ℂ) = (M.nIn : ℂ) - (k : ℂ) := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) hmz
    push_cast at h
    simpa using h
  set n : ℕ := m - 1 - N₀ with hndef
  have hnadd : n + N₀ = m - 1 := by omega
  set u₀ : ℂ := Work.PARIMPL.transU P M.nIn e - (k : ℂ) with hu₀def
  have hu₀dist : ‖u₀ - (((x₀ : ℝ)) : ℂ)‖ < L.r₀ / 2 := by
    have h1 : u₀ - (((x₀ : ℝ)) : ℂ) =
        (Work.PARIMPL.transU P M.nIn e) - (((x₀ + (k : ℝ) : ℝ)) : ℂ) := by
      rw [hu₀def]; push_cast; ring
    rw [h1]
    rwa [dist_eq_norm] at hkdist
  have hu₀ : u₀ ∈ Metric.closedBall (((x₀ : ℝ)) : ℂ) L.r₀ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [hu₀dist, L.hr₀]
  obtain ⟨lam, hlam0, hlam1, hlamK, hlampot, hlamW⟩ := hEXL.loop u₀ hu₀
  -- ### The path
  let P₂fun : unitInterval → ℂ := fun s => hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1)))
  have hP₂cont : Continuous P₂fun := by
    have hc : Continuous fun s : unitInterval => (v : ℂ) + (lam s - (u₀ - 1)) := by fun_prop
    have h := hPL.cont.comp_continuous hc (fun s => hlamW s)
    simpa [P₂fun, Function.comp_def] using h
  have hP₂src : P₂fun 0 = c₀ := by
    simp only [P₂fun, hlam0, sub_self, add_zero]
    exact hPL.ψv
  have hP₂tgt : P₂fun 1 = hPL.ψ ((v : ℂ) + 1) := by
    simp only [P₂fun, hlam1]
    congr 1
    ring
  let P₂ : Path c₀ (hPL.ψ ((v : ℂ) + 1)) :=
    ⟨⟨P₂fun, hP₂cont⟩, hP₂src, hP₂tgt⟩
  let σ : Path e (Work.EL.F e e) :=
    (Path.segment e c₀).trans (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))
  -- ### The three piece estimates
  have hfar₀ : hPL.X < v + (N₀ : ℝ) := by linarith [hN₀far, hBpos]
  have hfar₀' : hPL.X < ((v : ℂ) + (N₀ : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]; exact hfar₀
  have hfarR'' : hPL.X < ((v : ℂ) + (N₀ : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.one_re]
    linarith [hfar₀]
  -- left piece
  have Hleft : ∀ s : unitInterval,
      ‖(Work.EL.F e)^[m - 1] ((Path.segment e c₀) s) - fl.Ψ (u₀ - 1)‖ ≤ η := by
    intro s
    have hseg : ‖(Path.segment e c₀) s - c₀‖ ≤ ‖e - c₀‖ := by
      rw [Path.segment_apply]
      exact norm_lineMap_sub_right e c₀ (s : ℝ) s.2.1 s.2.2
    have hdist : ‖(Work.PARIMPL.Ft e)^[N₀] ((Path.segment e c₀) s)
        - hPL.ψ ((v : ℂ) + (N₀ : ℂ))‖ ≤ ρUT := by
      have h1 := hρL e ((Path.segment e c₀) s) (lt_of_lt_of_le hen hρ_L)
        (lt_of_le_of_lt hseg (lt_of_lt_of_le hen hρ_L))
      have h2 : (Work.PARIMPL.Ft c₀)^[N₀] c₀ = hPL.ψ ((v : ℂ) + (N₀ : ℂ)) := by
        have h := psi_iterate_shift hPL N₀ hmemv
        rwa [hPL.ψv] at h
      rwa [h2] at h1
    have hφyL : φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ))) = (v : ℂ) + (N₀ : ℂ) := by
      rw [hφa]; exact (hPL.far _ hfar₀').2
    have hyL_pa : hPL.ψ ((v : ℂ) + (N₀ : ℂ)) ∈ Pa := by
      rw [hPa]; exact FF.Pg_sub (hPL.far _ hfar₀').1
    have hboxL1 : X₁ ≤ (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))).re := by
      rw [hφyL]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
      linarith [hN₀low]
    have hboxL2 : (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))).re ≤ X₁ + W := by
      rw [hφyL]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
      linarith [hN₀high]
    have hboxL3 : |(φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))).im| ≤ B := by
      rw [hφyL, show ((v : ℂ) + (N₀ : ℂ)).im = 0 by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.natCast_im, zero_add, add_zero],
        abs_zero]
      exact le_of_lt hBpos
    have hU_eq : Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ))) = u₀ - 1 := by
      rw [hφyL, hu₀def]
      have key : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
            + ((v : ℂ) + (N₀ : ℂ)))
          = (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) + ((n : ℂ) + (N₀ : ℂ))) := by
        ring
      rw [key]
      have hnc : (n : ℂ) + (N₀ : ℂ) = (m : ℂ) - 1 := by
        rw [← Nat.cast_add, hnadd, Nat.cast_sub hm1, Nat.cast_one]
      rw [hnc, hmzc]
      ring
    have hrec : (-Xo) ≤ (u₀ - 1).re := by
      have h1 : ‖lam 0‖ ≤ Bk := hBk _ (hlamK 0)
      have h2 : -(‖lam 0‖) ≤ (lam 0).re := (abs_le.mp (Complex.abs_re_le_norm (lam 0))).1
      rw [← hlam0, hXodef]; linarith
    have hrec2 : (u₀ - 1).re < -1 := by
      rw [← hlam0]; exact hEXL.K₀_re _ (hlamK 0)
    have hstep := hUT' e ⟨he.1, heballUT⟩ (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))
      ((Work.PARIMPL.Ft e)^[N₀] ((Path.segment e c₀) s)) n hyL_pa hboxL1 hboxL2 hboxL3 hdist
    have hu1 : (-Xo) ≤ (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))).re := by rw [hU_eq]; exact hrec
    have hu2 : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ)))).re < -1 := by rw [hU_eq]; exact hrec2
    have hstep2 := hstep hu1 hu2
    rw [hU_eq, hΨ] at hstep2
    have hiter : (Work.PARIMPL.Ft e)^[n] ((Work.PARIMPL.Ft e)^[N₀] ((Path.segment e c₀) s))
        = (Work.PARIMPL.Ft e)^[m - 1] ((Path.segment e c₀) s) := by
      rw [← Function.iterate_add_apply, hnadd]
    rwa [hiter] at hstep2
  -- middle piece
  have Hmid : ∀ s : unitInterval,
      ‖(Work.EL.F e)^[m - 1] (P₂fun s) - fl.Ψ (lam s)‖ ≤ η := by
    intro s
    set δ : ℂ := lam s - (u₀ - 1) with hδdef
    have hδnorm : ‖δ‖ < B := by
      have h1 : ‖lam s‖ ≤ Bk := hBk _ (hlamK s)
      have hsplit : u₀ - 1 = (u₀ - (((x₀ : ℝ)) : ℂ)) + ((((x₀ : ℝ)) : ℂ) - 1) := by ring
      have h2 : ‖u₀ - 1‖ < ‖(((x₀ : ℝ)) : ℂ) - 1‖ + L.r₀ := by
        calc ‖u₀ - 1‖ = ‖(u₀ - (((x₀ : ℝ)) : ℂ)) + ((((x₀ : ℝ)) : ℂ) - 1)‖ := by rw [hsplit]
          _ ≤ ‖u₀ - (((x₀ : ℝ)) : ℂ)‖ + ‖(((x₀ : ℝ)) : ℂ) - 1‖ := norm_add_le _ _
          _ < L.r₀ / 2 + ‖(((x₀ : ℝ)) : ℂ) - 1‖ := by linarith [hu₀dist]
          _ ≤ ‖(((x₀ : ℝ)) : ℂ) - 1‖ + L.r₀ := by linarith [L.hr₀]
      have h3 : ‖δ‖ ≤ ‖lam s‖ + ‖u₀ - 1‖ := by rw [hδdef]; exact norm_sub_le _ _
      rw [hBdef]; linarith
    have hδre : |δ.re| ≤ B := le_trans (Complex.abs_re_le_norm δ) (le_of_lt hδnorm)
    have hδim : |δ.im| ≤ B := le_trans (Complex.abs_im_le_norm δ) (le_of_lt hδnorm)
    have hfarM : hPL.X < ((v : ℂ) + (N₀ : ℂ) + δ).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
      linarith [(abs_le.mp hδre).1, hN₀far]
    have hφyM : φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ)) = (v : ℂ) + (N₀ : ℂ) + δ := by
      rw [hφa]; exact (hPL.far _ hfarM).2
    have hyM_pa : hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ) ∈ Pa := by
      rw [hPa]; exact FF.Pg_sub (hPL.far _ hfarM).1
    have hboxM1 : X₁ ≤ (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))).re := by
      rw [hφyM]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
      linarith [(abs_le.mp hδre).1, hN₀low]
    have hboxM2 : (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))).re ≤ X₁ + W := by
      rw [hφyM]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
      linarith [(abs_le.mp hδre).2, hN₀high]
    have hboxM3 : |(φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))).im| ≤ B := by
      rw [hφyM]
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.natCast_im, zero_add, add_zero] using hδim
    have hshiftM : (Work.EL.F c₀)^[N₀] (hPL.ψ ((v : ℂ) + δ))
        = hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ) := by
      have h := psi_iterate_shift hPL N₀ (hlamW s)
      rw [← hδdef] at h
      rw [h]
      congr 1
      ring
    have hdistM : ‖(Work.PARIMPL.Ft e)^[N₀] (hPL.ψ ((v : ℂ) + δ))
        - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ)‖ ≤ ρUT := by
      have h1 := hρmid e (lt_of_lt_of_le hen hρ_mid) (hPL.ψ ((v : ℂ) + δ))
        (psi_norm_le FF hPL (hlamW s))
      rwa [hshiftM] at h1
    have hU_eqM : Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ)) = lam s := by
      rw [hφyM]
      have key : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
            + ((v : ℂ) + (N₀ : ℂ) + δ))
          = (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) + ((n : ℂ) + (N₀ : ℂ))) + δ := by ring
      rw [key, hδdef, hu₀def]
      have hnc : (n : ℂ) + (N₀ : ℂ) = (m : ℂ) - 1 := by
        rw [← Nat.cast_add, hnadd, Nat.cast_sub hm1, Nat.cast_one]
      rw [hnc, hmzc]
      ring
    have hUtM1 : (-Xo) ≤ (lam s).re := by
      have h1 : ‖lam s‖ ≤ Bk := hBk _ (hlamK s)
      have h2 : -(‖lam s‖) ≤ (lam s).re := (abs_le.mp (Complex.abs_re_le_norm (lam s))).1
      rw [hXodef]; linarith
    have hUtM2 : (lam s).re < -1 := hEXL.K₀_re _ (hlamK s)
    have hstep := hUT' e ⟨he.1, heballUT⟩ (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))
      ((Work.PARIMPL.Ft e)^[N₀] (hPL.ψ ((v : ℂ) + δ))) n hyM_pa hboxM1 hboxM2 hboxM3 hdistM
    have hu1 : (-Xo) ≤ (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))).re := by rw [hU_eqM]; exact hUtM1
    have hu2 : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + δ))).re < -1 := by rw [hU_eqM]; exact hUtM2
    have hstep2 := hstep hu1 hu2
    rw [hU_eqM, hΨ] at hstep2
    have hiter : (Work.PARIMPL.Ft e)^[n] ((Work.PARIMPL.Ft e)^[N₀] (hPL.ψ ((v : ℂ) + δ)))
        = (Work.PARIMPL.Ft e)^[m - 1] (hPL.ψ ((v : ℂ) + δ)) := by
      rw [← Function.iterate_add_apply, hnadd]
    rwa [hiter] at hstep2
  -- right piece
  have Hright : ∀ s : unitInterval,
      ‖(Work.EL.F e)^[m - 1]
        ((Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s) - fl.Ψ u₀‖ ≤ η := by
    intro s
    have hc₁slit : (v : ℂ) + 1 ∈ Work.GATE2.slitAt v :=
      Work.GATE2.PL.slitAt_add_one hmemv
    have hseg : ‖(Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s
        - hPL.ψ ((v : ℂ) + 1)‖ ≤ ‖(Work.EL.F e) e - hPL.ψ ((v : ℂ) + 1)‖ := by
      have h := norm_lineMap_sub_left (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e) (s : ℝ) s.2.1 s.2.2
      rw [Path.segment_apply]
      rwa [← norm_sub_rev (Work.EL.F e e) (hPL.ψ ((v : ℂ) + 1))] at h
    have hFclose : ‖(Work.EL.F e) e - hPL.ψ ((v : ℂ) + 1)‖ < ρR :=
      hρC e (lt_of_lt_of_le hen hρ_C)
    have hdist : ‖(Work.PARIMPL.Ft e)^[N₀] ((Path.segment (hPL.ψ ((v : ℂ) + 1))
          (Work.EL.F e e)) s) - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)‖ ≤ ρUT := by
      have h1 := hρR e ((Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s)
        (lt_of_lt_of_le hen hρ_R) (lt_of_le_of_lt hseg hFclose)
      have h2 : (Work.PARIMPL.Ft c₀)^[N₀] (hPL.ψ ((v : ℂ) + 1))
          = hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1) := by
        have h := psi_iterate_shift hPL N₀ hc₁slit
        rw [h]; congr 1; ring
      rwa [h2] at h1
    have hφyR : φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)) = (v : ℂ) + (N₀ : ℂ) + 1 := by
      rw [hφa]; exact (hPL.far _ hfarR'').2
    have hyR_pa : hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1) ∈ Pa := by
      rw [hPa]; exact FF.Pg_sub (hPL.far _ hfarR'').1
    have hboxR1 : X₁ ≤ (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))).re := by
      rw [hφyR]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.one_re]
      linarith [hN₀low, hBpos]
    have hboxR2 : (φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))).re ≤ X₁ + W := by
      rw [hφyR]; simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.one_re]
      linarith [hN₀high, hB1]
    have hboxR3 : |(φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))).im| ≤ B := by
      rw [hφyR, show ((v : ℂ) + (N₀ : ℂ) + 1).im = 0 by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.natCast_im, Complex.one_im,
          zero_add, add_zero], abs_zero]
      exact le_of_lt hBpos
    have hU_eqR : Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)) = u₀ := by
      rw [hφyR, hu₀def]
      have key : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
            + ((v : ℂ) + (N₀ : ℂ) + 1))
          = (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) + ((n : ℂ) + (N₀ : ℂ))) + 1 := by ring
      rw [key]
      have hnc : (n : ℂ) + (N₀ : ℂ) = (m : ℂ) - 1 := by
        rw [← Nat.cast_add, hnadd, Nat.cast_sub hm1, Nat.cast_one]
      rw [hnc, hmzc]
      ring
    have hUtR1 : (-Xo) ≤ u₀.re := by
      have h1 : ‖lam 1‖ ≤ Bk := hBk _ (hlamK 1)
      have h2 : -(‖lam 1‖) ≤ (lam 1).re := (abs_le.mp (Complex.abs_re_le_norm (lam 1))).1
      rw [← hlam1, hXodef]; linarith
    have hUtR2 : u₀.re < -1 := by rw [← hlam1]; exact hEXL.K₀_re _ (hlamK 1)
    have hstep := hUT' e ⟨he.1, heballUT⟩ (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))
      ((Work.PARIMPL.Ft e)^[N₀] ((Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s))
      n hyR_pa hboxR1 hboxR2 hboxR3 hdist
    have hu1 : (-Xo) ≤ (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))).re := by rw [hU_eqR]; exact hUtR1
    have hu2 : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1))).re < -1 := by rw [hU_eqR]; exact hUtR2
    have hstep2 := hstep hu1 hu2
    rw [hU_eqR, hΨ] at hstep2
    have hiter : (Work.PARIMPL.Ft e)^[n]
          ((Work.PARIMPL.Ft e)^[N₀] ((Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s))
        = (Work.PARIMPL.Ft e)^[m - 1]
          ((Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) s) := by
      rw [← Function.iterate_add_apply, hnadd]
    rwa [hiter] at hstep2
  -- ### The membership and floor data
  have hZleft : fl.Ψ (u₀ - 1) ∈ hEXL.𝒦 := (hEXL.discs u₀ hu₀).1
  have hZright : fl.Ψ u₀ ∈ hEXL.𝒦 := (hEXL.discs u₀ hu₀).2
  have hZmid : ∀ s : unitInterval, fl.Ψ (lam s) ∈ hEXL.𝒦 := fun s => hEXL.K₀_sub _ (hlamK s)
  have hfloorR : (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u₀ - 1))
      ≤ Work.Bottcher.green c₀ (fl.Ψ u₀) := by
    have h := hlampot 1
    rwa [hlam1] at h
  have hz0 : ‖(Work.EL.F e)^[m - 1] e - fl.Ψ (u₀ - 1)‖ ≤ η := by
    have h := Hleft 0
    have h0 : (Path.segment e c₀) (0 : unitInterval) = e := by
      rw [Path.segment_apply]; exact AffineMap.lineMap_apply_zero e c₀
    rwa [h0] at h
  have pot_main : ∀ z z₀ : ℂ, z₀ ∈ hEXL.𝒦 →
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u₀ - 1)) ≤ Work.Bottcher.green c₀ z₀ →
      ‖z - z₀‖ ≤ η →
      (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0 < Work.Bottcher.green e z := by
    intro z z₀ hz₀ hfloor hnear
    have hgc := hgreend e (lt_of_lt_of_le hen hρ_g) z₀ hz₀ (fl.Ψ (u₀ - 1)) hZleft hfloor
      z ((Work.EL.F e)^[m - 1] e) (lt_of_le_of_lt hnear hηlt_g) (lt_of_le_of_lt hz0 hηlt_g)
    rw [green_Ft_iterate e e (m - 1), green_crit e] at hgc
    linarith
  -- ### The two estimates on `σ`
  have hdevσ : ∀ t : unitInterval, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
      ((Work.EL.F e)^[m - 1] (σ t))| < (1 / 8192 : ℝ) := by
    intro t
    rcases le_or_gt ((t : unitInterval) : ℝ) (1 / 2) with ht | ht
    · have hσ : σ t = (Path.segment e c₀) (rep t ht) := by
        change ((Path.segment e c₀).trans
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))) t = _
        exact trans_le _ _ t ht
      rw [hσ]
      exact hdevd e (lt_of_lt_of_le hen hρ_d) _
        ⟨fl.Ψ (u₀ - 1), hZleft, lt_of_le_of_lt (Hleft (rep t ht)) hηlt_d⟩
    · have hσ : σ t =
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e))) (repm t ht) := by
        change ((Path.segment e c₀).trans
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))) t = _
        exact trans_gt _ _ t ht
      rw [hσ]
      rcases le_or_gt (((repm t ht : unitInterval)) : ℝ) (1 / 2) with hs | hs
      · have hσ2 : (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))
            (repm t ht) = P₂ (rep (repm t ht) hs) := trans_le _ _ _ hs
        rw [hσ2]
        exact hdevd e (lt_of_lt_of_le hen hρ_d) _
          ⟨fl.Ψ (lam (rep (repm t ht) hs)), hZmid _,
            lt_of_le_of_lt (Hmid (rep (repm t ht) hs)) hηlt_d⟩
      · have hσ2 : (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))
            (repm t ht)
            = (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) (repm (repm t ht) hs) :=
          trans_gt _ _ _ hs
        rw [hσ2]
        exact hdevd e (lt_of_lt_of_le hen hρ_d) _
          ⟨fl.Ψ u₀, hZright, lt_of_le_of_lt (Hright (repm (repm t ht) hs)) hηlt_d⟩
  have hpotσ : ∀ t : unitInterval, (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0
      < Work.Bottcher.green e ((Work.EL.F e)^[m - 1] (σ t)) := by
    intro t
    rcases le_or_gt ((t : unitInterval) : ℝ) (1 / 2) with ht | ht
    · have hσ : σ t = (Path.segment e c₀) (rep t ht) := by
        change ((Path.segment e c₀).trans
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))) t = _
        exact trans_le _ _ t ht
      rw [hσ]
      have hfloor : (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (u₀ - 1))
          ≤ Work.Bottcher.green c₀ (fl.Ψ (u₀ - 1)) := by
        have := Work.Bottcher.Green.green_nonneg c₀ (fl.Ψ (u₀ - 1)); linarith
      exact pot_main _ _ hZleft hfloor (Hleft (rep t ht))
    · have hσ : σ t =
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e))) (repm t ht) := by
        change ((Path.segment e c₀).trans
          (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))) t = _
        exact trans_gt _ _ t ht
      rw [hσ]
      rcases le_or_gt (((repm t ht : unitInterval)) : ℝ) (1 / 2) with hs | hs
      · have hσ2 : (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))
            (repm t ht) = P₂ (rep (repm t ht) hs) := trans_le _ _ _ hs
        rw [hσ2]
        exact pot_main _ _ (hZmid _) (hlampot (rep (repm t ht) hs)) (Hmid (rep (repm t ht) hs))
      · have hσ2 : (P₂.trans (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)))
            (repm t ht)
            = (Path.segment (hPL.ψ ((v : ℂ) + 1)) (Work.EL.F e e)) (repm (repm t ht) hs) :=
          trans_gt _ _ _ hs
        rw [hσ2]
        exact pot_main _ _ hZright hfloorR (Hright (repm (repm t ht) hs))
  exact ⟨m, hm1, (σ : C(unitInterval, ℂ)), Path.source σ, Path.target σ, hdevσ, hpotσ⟩

/-- **D1 for the `ι b`-tongue.**  The exit-path datum at the half-shifted leak level
`x* − j₀ + 1/2` and the second root angle `α₂`, from PL, EXL at the shifted level and the floored
UT.  This is the `iota` half of the drive `Work.GATE2.twoSided_of_PARIMPL_PL_EXL`. -/
theorem exitPath_of_tongue_iota {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((LeanEval.ComplexAnalysis.Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : Pa = fl.Pa) (hφa : φa = fl.φa) (hΨ : Ψ = fl.Ψ)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hPL : Work.GATE2.PrincipalParamFlower c₀ FF.Pg fl.φa
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL : Work.GATE2.ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2)
    (hUT : Work.GATE2.TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (hPL.X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ))) :
    Work.GATE2.ExitPathData c₀ P.Nm (Work.PARIMPL.transU P M.nIn)
      ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      (fun e => Work.GATE.iotaTongue (Work.PARIMPL.transU P M.nIn)
        (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha2 := by
  exact exitPathData_of_exitLoop
    (v := ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (x₀ := (L.xstar - (L.j₀ : ℝ)) + 1 / 2) (α := Work.EL.alpha2)
    FF hPa hφa hΨ hcrit hPL hEXL hUT

end Work.GATE2.D1
