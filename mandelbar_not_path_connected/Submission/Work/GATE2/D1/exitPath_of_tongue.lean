import Mathlib
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.PARIMPL.All
import Submission.Work.GATE2.PL.deviation_small_near_compactum
import Submission.Work.GATE2.PL.bTongue_exitTime
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.D1.close_iterate_on_ball
import Submission.Work.GATE2.D1.green_comparison_near_compactum
import Submission.Work.FSeed.API.mem_Mandelbar
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded
import Submission.Work.Escape.isCompact_filledJulia
import Submission.Work.Bottcher.Contraction.isPreconnected_green_le_greenParam

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
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section

namespace Work.GATE2.D1

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## Auxiliary facts -/

/-- The Green function at the critical value: `G_c c = 2 * G_c 0`. -/
theorem green_crit (c : ℂ) : Work.Bottcher.green c c = 2 * Work.Bottcher.green c 0 := by
  have h := Work.Bottcher.Green.green_comm c 0
  simpa using h

/-- The Green functional equation for the second return map `F_c = (T_c)^[10]`:
`G_c (F_c^[k] z) = 1024^k * G_c z`. -/
theorem green_Ft (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.EL.F c)^[k] z) = (1024 : ℝ) ^ k * Work.Bottcher.green c z := by
  have hF : (Work.EL.F c)^[k] = (Tantibar c)^[10 * k] := by
    rw [Work.EL.F_eq_tantibar, Function.iterate_mul]
  rw [hF, Work.Bottcher.Contraction.green_comm_iterate]
  congr 1
  rw [pow_mul]
  norm_num

/-- The parameter potential of a root-parabolic parameter vanishes. -/
theorem paramPotential_eq_zero_of_rootParabolic {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    Work.ParamRays.paramPotential c₀ = 0 :=
  (Work.ParamRays.paramPotential_eq_zero_iff c₀).mpr (Work.FSeed.API.mem_Mandelbar d)

/-- A point off the filled Julia set of a root-parabolic parameter lies in the critical domain. -/
theorem mem_critDomain_of_notMem_K {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) {z : ℂ}
    (hz : z ∉ Work.EL.K c₀) : z ∈ Work.ParamRays.critDomain c₀ := by
  rw [Work.ParamRays.mem_critDomain, paramPotential_eq_zero_of_rootParabolic d,
    ← Work.Bottcher.Contraction.green_eq_greenFun]
  exact Work.PARIMPL.green_pos_of_notMem_K hz

/-- Iterated form of the `PL` shift relation. -/
theorem psi_shift_iter {F g : ℂ → ℂ} {c₀ : ℂ} {Pg : Set ℂ} {φa : ℂ → ℂ} {v : ℝ}
    (hPL : Work.GATE2.PrincipalParam F g c₀ Pg φa v) (N : ℕ) {w : ℂ}
    (hw : w ∈ Work.GATE2.slitAt v) :
    F^[N] (hPL.ψ w) = hPL.ψ (w + (N : ℂ)) := by
  have hmem : ∀ n : ℕ, w + (n : ℂ) ∈ Work.GATE2.slitAt v := by
    intro n
    induction n with
    | zero => simpa using hw
    | succ n ih =>
      have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
      rw [h1]
      exact Work.GATE2.PL.slitAt_add_one ih
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hPL.shift _ (hmem n)]
    congr 1
    push_cast
    ring

/-! ## Reparametrisation of the unit interval -/

/-- The point `2t` of the unit interval, when `t ≤ 1/2`. -/
def rep (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : unitInterval :=
  ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2, h]⟩

/-- The point `2t - 1` of the unit interval, when `1/2 < t`. -/
def repm (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : unitInterval :=
  ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2, h]⟩

@[simp] theorem rep_val (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    ((rep t h : unitInterval) : ℝ) = 2 * (t : ℝ) := by simp [rep]

@[simp] theorem repm_val (t : unitInterval) (h : 1 / 2 < (t : ℝ)) :
    ((repm t h : unitInterval) : ℝ) = 2 * (t : ℝ) - 1 := by simp [repm]

theorem trans_le {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) : γ.trans γ' t = γ (rep t h) := by
  rw [Path.trans_apply, dif_pos h]
  refine congrArg γ (Subtype.ext ?_)
  simp [rep]

theorem trans_gt {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y) (γ' : Path y z)
    (t : unitInterval) (h : 1 / 2 < (t : ℝ)) : γ.trans γ' t = γ' (repm t h) := by
  rw [Path.trans_apply, dif_neg (not_le.mpr h)]
  refine congrArg γ' (Subtype.ext ?_)
  simp [repm]

/-- A point whose `N`-th iterate under the second return map lies in the filled Julia set is
itself in the filled Julia set. -/
theorem mem_K_of_iterate_mem_K {c : ℂ} (N : ℕ) {z : ℂ}
    (h : (Work.EL.F c)^[N] z ∈ Work.EL.K c) : z ∈ Work.EL.K c := by
  have hbridge : ∀ w : ℂ, w ∈ Work.EL.K c ↔ w ∈ Work.Escape.filledJulia (Tantibar c) := by
    intro w
    rw [Work.Escape.mem_filledJulia]
    constructor
    · rintro ⟨M, hM⟩
      exact isBounded_iff_forall_norm_le.mpr
        ⟨M, fun u hu => by obtain ⟨n, rfl⟩ := hu; exact hM n⟩
    · intro hw
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hw
      exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩
  have hF : (Work.EL.F c)^[N] = (Tantibar c)^[10 * N] := by
    rw [Work.EL.F_eq_tantibar, Function.iterate_mul]
  have hne : (Tantibar c)^[10 * N] z ∈ Work.Escape.filledJulia (Tantibar c) := by
    rw [← hF]; exact (hbridge _).mp h
  exact (hbridge z).mpr
    ((Work.Escape.mem_filledJulia_iff_iterate (Tantibar c) z (10 * N)).mpr hne)

/-- Points of the slit plane survive adding naturals. -/
theorem slitAt_add_nat {v : ℝ} (n : ℕ) {w : ℂ} (hw : w ∈ Work.GATE2.slitAt v) :
    w + (n : ℂ) ∈ Work.GATE2.slitAt v := by
  induction n with
  | zero => simpa using hw
  | succ k ih =>
    have h1 : w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 := by push_cast; ring
    rw [h1]
    exact Work.GATE2.PL.slitAt_add_one ih

/-! ## Norm bounds for straight segments -/

theorem norm_lineMap_le_max (a b : ℂ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖AffineMap.lineMap a b s‖ ≤ max ‖a‖ ‖b‖ := by
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  have heq : s • (b - a) + a = (1 - s) • a + s • b := by module
  rw [heq]
  have h := norm_add_le ((1 - s) • a) (s • b)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have ha : |1 - s| = 1 - s := abs_of_nonneg (by linarith)
  have hb : |s| = s := abs_of_nonneg h0
  rw [ha, hb] at h
  have h1' : (1 - s) * ‖a‖ ≤ (1 - s) * max ‖a‖ ‖b‖ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  have h2' : s * ‖b‖ ≤ s * max ‖a‖ ‖b‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) h0
  calc ‖(1 - s) • a + s • b‖ ≤ (1 - s) * ‖a‖ + s * ‖b‖ := h
    _ ≤ (1 - s) * max ‖a‖ ‖b‖ + s * max ‖a‖ ‖b‖ := add_le_add h1' h2'
    _ = max ‖a‖ ‖b‖ := by ring

theorem norm_lineMap_sub_right (a b : ℂ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖AffineMap.lineMap a b s - b‖ ≤ ‖a - b‖ := by
  have heq : AffineMap.lineMap a b s - b = AffineMap.lineMap (a - b) 0 s := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  rw [heq]
  have h := norm_lineMap_le_max (a - b) 0 s h0 h1
  rw [norm_zero, max_eq_left (norm_nonneg (a - b))] at h
  exact h

/-! ## D1: the exit-path datum of the tongue -/

theorem norm_lineMap_sub_left (a b : ℂ) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖AffineMap.lineMap a b s - a‖ ≤ ‖b - a‖ := by
  have heq : AffineMap.lineMap a b s - a = s • (b - a) := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  calc s * ‖b - a‖ ≤ 1 * ‖b - a‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖b - a‖ := one_mul _

/-- The norm bound for points of the filled Julia set. -/
theorem norm_le_of_mem_K {c z : ℂ} (h : z ∈ Work.EL.K c) : ‖z‖ ≤ max 2 ‖c‖ := by
  have hbridge : z ∈ Work.Escape.filledJulia (Tantibar c) := by
    rw [Work.Escape.mem_filledJulia]
    obtain ⟨M, hM⟩ := h
    exact isBounded_iff_forall_norm_le.mpr ⟨M, fun u hu => by
      obtain ⟨n, rfl⟩ := hu
      exact hM n⟩
  exact Work.Escape.norm_le_max_two_A_of_mem_filledJulia (Work.Escape.monicGrowth_Tantibar c)
    (by norm_num) hbridge

theorem exitPath_of_tongue {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
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
    (hEXL : Work.GATE2.ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hUT : Work.GATE2.TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (hPL.X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ))) :
    Work.GATE2.ExitPathData c₀ P.Nm (Work.PARIMPL.transU P M.nIn)
      (L.xstar - (L.j₀ : ℝ)) L.r₀
      (fun e => Work.GATE.bTongue (Work.PARIMPL.transU P M.nIn)
        (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha1 := by
  classical
  unfold Work.GATE2.ExitPathData
  let v : ℝ := (φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)
  let y₀ : ℝ := L.xstar - (L.j₀ : ℝ)
  let r : ℝ := L.r₀
  have hrpos : 0 < r := L.hr₀
  have hv_mem : (v : ℂ) ∈ Work.GATE2.slitAt v := by
    rw [Work.GATE2.slitAt, Set.mem_ofPred_eq]
    rintro ⟨-, h⟩
    simp only [Complex.ofReal_re] at h
    linarith
  have hv1_mem : ((v : ℂ) + 1) ∈ Work.GATE2.slitAt v := Work.GATE2.PL.slitAt_add_one hv_mem
  have hPgPa : FF.Pg ⊆ Pa := by rw [hPa]; exact FF.Pg_sub
  have hdom : ∀ z ∈ hEXL.𝒦, z ∈ Work.ParamRays.critDomain c₀ :=
    fun z hz => mem_critDomain_of_notMem_K d (hEXL.offK z hz)
  have hwinE : ∀ z ∈ hEXL.𝒦,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha1 z| < (1 / 16384 : ℝ) :=
    fun z hz => hEXL.win z hz
  obtain ⟨η_dev, hη_dev_pos, ρ_dev, hρ_dev_pos, hdev⟩ :=
    Work.GATE2.PL.deviation_small_near_compactum (c₀ := c₀) (α := Work.EL.alpha1)
      hEXL.isCompact hdom hwinE
  obtain ⟨η_g, hη_g_pos, ρ_g, hρ_g_pos, hgc⟩ :=
    green_comparison_near_compactum (c₀ := c₀) (K := hEXL.𝒦) hEXL.isCompact
      (fun z hz => Work.PARIMPL.green_pos_of_notMem_K (hEXL.offK z hz))
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, ∀ w ∈ hEXL.K₀, ‖w‖ ≤ B0 := by
    obtain ⟨r0, hr0⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hEXL.isCompact_K₀.isBounded
    refine ⟨r0, fun w hw => ?_⟩
    have h := hr0 hw
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  set B : ℝ := |B0| + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hK₀norm : ∀ w ∈ hEXL.K₀, ‖w‖ ≤ B := by
    intro w hw
    have h1 := hB0 w hw
    have h2 : B0 ≤ B := by rw [hB]; linarith [le_abs_self B0]
    linarith
  set Aβ : ℝ := -B - y₀ - r / 2 + 1 with hAβ
  set Bβ : ℝ := B - y₀ + r / 2 + 1 with hBβ
  set W : ℝ := max (Bβ - Aβ + 1) (v + Bβ - hPL.X + 2) with hWdef
  have hW1 : Bβ - Aβ + 1 ≤ W := by rw [hWdef]; exact le_max_left _ _
  have hW2 : v + Bβ - hPL.X + 2 ≤ W := by rw [hWdef]; exact le_max_right _ _
  set H : ℝ := B + r / 2 + 1 with hHdef
  set Xo : ℝ := B + 2 with hXodef
  set η : ℝ := min (η_dev / 2) (η_g / 2) with hηdef
  have hηpos : 0 < η := lt_min (by linarith) (by linarith)
  have hηdev : η < η_dev := by
    have h1 : η ≤ η_dev / 2 := by rw [hηdef]; exact min_le_left _ _
    linarith
  have hηg : η < η_g := by
    have h1 : η ≤ η_g / 2 := by rw [hηdef]; exact min_le_right _ _
    linarith
  obtain ⟨X₁, ρ_UT, hX₁ge, hρ_UT_pos, hUTspec⟩ := hUT H W Xo η hηpos
  set N₀ : ℕ := Nat.ceil (max (X₁ - Aβ - v) 0) with hN₀def
  have hN₀ge : X₁ - Aβ - v ≤ (N₀ : ℝ) := by
    rw [hN₀def]
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hN₀lt : (N₀ : ℝ) < max (X₁ - Aβ - v) 0 + 1 := by
    rw [hN₀def]
    exact Nat.ceil_lt_add_one (le_max_right _ _)
  have hlb : X₁ ≤ v + (N₀ : ℝ) + Aβ := by linarith [hN₀ge]
  have hub : v + (N₀ : ℝ) + Bβ ≤ X₁ + W := by
    by_cases hc : 0 ≤ X₁ - Aβ - v
    · have hmax : max (X₁ - Aβ - v) 0 = X₁ - Aβ - v := max_eq_left hc
      have h := hN₀lt
      rw [hmax] at h
      linarith [hW1]
    · have hc' : X₁ - Aβ - v < 0 := not_le.mp hc
      have hmax : max (X₁ - Aβ - v) 0 = 0 := max_eq_right (le_of_lt hc')
      have hN : (N₀ : ℝ) < 1 := by
        have h := hN₀lt
        rw [hmax] at h
        linarith
      have hkey : v + Bβ + 3 ≤ X₁ + W := by linarith [hW2, hX₁ge]
      linarith
  obtain ⟨ρ_bt, hρ_bt_pos, hbt⟩ :=
    Work.GATE2.PL.bTongue_exitTime (c₀ := c₀) (d := d) (P := P) (Pa := Pa) (φa := φa) (Ψ := Ψ)
      (M := M) (T := T) (y₀ := y₀) (r := r) (N₀ + 1)
  set BB : ℝ := max (max 2 ‖c₀‖) (max (‖c₀‖ + 1) (‖(Work.EL.F c₀) c₀‖ + 1)) with hBBdef
  obtain ⟨ρ_close, hρ_close_pos, hclose⟩ := close_iterate_on_ball (c₀ := c₀) N₀ BB (ρ_UT / 2) (by linarith)
  have hcontF : Continuous ((Work.EL.F c₀)^[N₀]) := by
    have h1 : Continuous (fun z : ℂ => (Work.Landing.Tsq c₀)^[5 * N₀] z) :=
      (Work.PARIMPL.continuous_tsqIter (5 * N₀)).comp (f := fun z : ℂ => (c₀, z))
        ((continuous_const : Continuous fun _ : ℂ => c₀).prodMk
          (continuous_id : Continuous fun z : ℂ => z))
    have hEq : (fun z : ℂ => (Work.Landing.Tsq c₀)^[5 * N₀] z) = (Work.EL.F c₀)^[N₀] := by
      funext z
      rw [Work.EL.F, Function.iterate_mul]
    rwa [hEq] at h1
  set c₁ : ℂ := (Work.EL.F c₀) c₀ with hc₁
  have hc₁eq : c₁ = hPL.ψ ((v : ℂ) + 1) := by
    have hψvF : (Work.EL.F c₀) c₀ = (Work.EL.F c₀) (hPL.ψ (v : ℂ)) := by rw [hPL.ψv]
    rw [hc₁, hψvF, hPL.shift (v : ℂ) hv_mem]
  have hval₀ : (Work.EL.F c₀)^[N₀] c₀ = hPL.ψ ((v : ℂ) + (N₀ : ℂ)) := by
    have h1 : (Work.EL.F c₀)^[N₀] (hPL.ψ (v : ℂ)) = hPL.ψ ((v : ℂ) + (N₀ : ℂ)) :=
      psi_shift_iter hPL N₀ hv_mem
    rwa [hPL.ψv] at h1
  have hval₁ : (Work.EL.F c₀)^[N₀] c₁ = hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1) := by
    have h1 : (Work.EL.F c₀)^[N₀] (hPL.ψ ((v : ℂ) + 1))
        = hPL.ψ (((v : ℂ) + 1) + (N₀ : ℂ)) := psi_shift_iter hPL N₀ hv1_mem
    rw [hc₁eq, h1]
    congr 1
    ring
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    Metric.continuousAt_iff.mp hcontF.continuousAt (ρ_UT / 2) (by linarith)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
    Metric.continuousAt_iff.mp (hcontF.continuousAt (x := c₁)) (ρ_UT / 2) (by linarith)
  have hcontFe : Continuous (fun e : ℂ => (Work.EL.F e) e) := by
    have h1 : Continuous (fun e : ℂ => (Work.Landing.Tsq e)^[5] e) :=
      (Work.PARIMPL.continuous_tsqIter 5).comp (f := fun e : ℂ => (e, e))
        (continuous_id.prodMk (continuous_id : Continuous fun z : ℂ => z))
    have hEq : (fun e : ℂ => (Work.Landing.Tsq e)^[5] e) = (fun e : ℂ => (Work.EL.F e) e) := by
      funext e
      rw [Work.EL.F]
    rwa [hEq] at h1
  obtain ⟨δe, hδe_pos, hδe⟩ :=
    Metric.continuousAt_iff.mp hcontFe.continuousAt (min (min δ₀ δ₁) 1)
      (lt_min (lt_min hδ₀_pos hδ₁_pos) one_pos)
  set ρ : ℝ := min ρ_UT (min ρ_dev (min ρ_g (min ρ_bt (min ρ_close (min δ₀ (min δ₁ (min δe 1)))))))
    with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ_UT_pos (lt_min hρ_dev_pos (lt_min hρ_g_pos (lt_min hρ_bt_pos
      (lt_min hρ_close_pos (lt_min hδ₀_pos (lt_min hδ₁_pos (lt_min hδe_pos one_pos)))))))
  have hρ_UT : ρ ≤ ρ_UT := by rw [hρdef]; exact min_le_left _ _
  have hρ_dev : ρ ≤ ρ_dev := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_g : ρ ≤ ρ_g := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ_bt : ρ ≤ ρ_bt := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρ_close : ρ ≤ ρ_close := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hρ_δ₀ : ρ ≤ δ₀ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hρ_δ₁ : ρ ≤ δ₁ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hρ_δe : ρ ≤ δe := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hρ_one : ρ ≤ 1 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))))))
  refine ⟨ρ, hρpos, ?_⟩
  intro e he hbT hM
  obtain ⟨heNm, heball⟩ := he
  have he_lt : ‖e - c₀‖ < ρ := by simpa [dist_eq_norm] using heball
  have he_UT : ‖e - c₀‖ < ρ_UT := lt_of_lt_of_le he_lt hρ_UT
  have he_dev : ‖e - c₀‖ < ρ_dev := lt_of_lt_of_le he_lt hρ_dev
  have he_g : ‖e - c₀‖ < ρ_g := lt_of_lt_of_le he_lt hρ_g
  have he_bt : ‖e - c₀‖ < ρ_bt := lt_of_lt_of_le he_lt hρ_bt
  have he_close : ‖e - c₀‖ < ρ_close := lt_of_lt_of_le he_lt hρ_close
  have he_δ₀ : ‖e - c₀‖ < δ₀ := lt_of_lt_of_le he_lt hρ_δ₀
  have he_δ₁ : ‖e - c₀‖ < δ₁ := lt_of_lt_of_le he_lt hρ_δ₁
  have he_δe : ‖e - c₀‖ < δe := lt_of_lt_of_le he_lt hρ_δe
  have he_one : ‖e - c₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le he_lt hρ_one)
  obtain ⟨k, hk_dist, hk_le⟩ := hbt e ⟨heNm, by simpa [dist_eq_norm] using he_bt⟩ hbT
  have hk0 : (0 : ℤ) ≤ (M.nIn : ℤ) - k := by omega
  set m : ℕ := ((M.nIn : ℤ) - k).toNat with hmdef
  have hm_cast : (m : ℤ) = (M.nIn : ℤ) - k := by
    rw [hmdef]; exact Int.toNat_of_nonneg hk0
  have hm_ge1 : 1 ≤ m := by
    have h : ((1 : ℕ) : ℤ) ≤ (m : ℤ) := by rw [hm_cast]; omega
    exact_mod_cast h
  have hmN₀ : N₀ + 1 ≤ m := by
    have h : ((N₀ + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by rw [hm_cast]; exact hk_le
    exact_mod_cast h
  set n : ℕ := m - 1 - N₀ with hndef
  have hnN₀ : n + N₀ = m - 1 := by rw [hndef]; omega
  have hmk : (m : ℤ) + k = M.nIn := by omega
  set u₀ : ℂ := Work.PARIMPL.transU P M.nIn e - (k : ℂ) with hu₀def
  have hu₀_dist : dist u₀ ((y₀ : ℝ) : ℂ) < r / 2 := by
    have h : u₀ - ((y₀ : ℝ) : ℂ) = Work.PARIMPL.transU P M.nIn e - (((y₀ + (k : ℝ)) : ℝ) : ℂ) := by
      rw [hu₀def]; push_cast; ring
    rw [dist_eq_norm, h]
    rwa [dist_eq_norm] at hk_dist
  have hu₀_im : |(u₀).im| ≤ r / 2 := by
    have h1 : |(u₀).im| ≤ ‖u₀ - ((y₀ : ℝ) : ℂ)‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (u₀ - ((y₀ : ℝ) : ℂ))
    rw [dist_eq_norm] at hu₀_dist
    linarith
  have hu₀_re : |(u₀).re - y₀| ≤ r / 2 := by
    have h1 : |(u₀).re - y₀| ≤ ‖u₀ - ((y₀ : ℝ) : ℂ)‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (u₀ - ((y₀ : ℝ) : ℂ))
    rw [dist_eq_norm] at hu₀_dist
    linarith
  have hu₀mem : u₀ ∈ Metric.closedBall ((y₀ : ℝ) : ℂ) r := by
    rw [Metric.mem_closedBall]
    linarith [hu₀_dist]
  obtain ⟨lam, hlam0, hlam1, hlamK, hlamPot, hlamW⟩ := hEXL.loop u₀ hu₀mem
  have hlamPot' : ∀ s : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (Ψ (u₀ - 1))
        ≤ Work.Bottcher.green c₀ (Ψ (lam s)) := by
    intro s
    have h := hlamPot s
    rwa [← hΨ] at h
  -- the path pieces
  let p₁ : Path e c₀ := Path.segment e c₀
  let p₂fun : unitInterval → ℂ := fun t => hPL.ψ ((v : ℂ) + (lam t - (u₀ - 1)))
  have hargcont : Continuous (fun t : unitInterval => (v : ℂ) + (lam t - (u₀ - 1))) := by fun_prop
  have hp₂cont : Continuous p₂fun :=
    ContinuousOn.comp_continuous hPL.cont hargcont (fun t => hlamW t)
  have hp₂src : p₂fun (0 : unitInterval) = c₀ := by
    simp only [p₂fun, hlam0]
    rw [show (v : ℂ) + ((u₀ - 1) - (u₀ - 1)) = (v : ℂ) by ring]
    exact hPL.ψv
  have hp₂tgt : p₂fun (1 : unitInterval) = c₁ := by
    simp only [p₂fun, hlam1]
    rw [show (v : ℂ) + (u₀ - (u₀ - 1)) = (v : ℂ) + 1 by ring]
    exact hc₁eq.symm
  let p₂ : Path c₀ c₁ := Path.mk ⟨p₂fun, hp₂cont⟩ hp₂src hp₂tgt
  let p₃ : Path c₁ ((Work.EL.F e) e) := Path.segment c₁ ((Work.EL.F e) e)
  let σp : Path e ((Work.EL.F e) e) := (p₁.trans p₂).trans p₃
  let q₁ : Path (u₀ - 1) (u₀ - 1) := Path.refl (u₀ - 1)
  let q₂ : Path (u₀ - 1) u₀ := Path.mk lam hlam0 hlam1
  let q₃ : Path u₀ u₀ := Path.refl u₀
  let lamP : Path (u₀ - 1) u₀ := (q₁.trans q₂).trans q₃
  have hp₁app : ∀ s : unitInterval, p₁ s = AffineMap.lineMap e c₀ (s : ℝ) :=
    fun s => Path.segment_apply e c₀ s
  have hp₂app : ∀ s : unitInterval, p₂ s = hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1))) := fun _ => rfl
  have hp₃app : ∀ s : unitInterval, p₃ s = AffineMap.lineMap c₁ ((Work.EL.F e) e) (s : ℝ) :=
    fun s => Path.segment_apply c₁ ((Work.EL.F e) e) s
  have hq₁app : ∀ s : unitInterval, q₁ s = u₀ - 1 := fun s => Path.refl_apply _ s
  have hq₂app : ∀ s : unitInterval, q₂ s = lam s := fun _ => rfl
  have hq₃app : ∀ s : unitInterval, q₃ s = u₀ := fun s => Path.refl_apply _ s
  have hσ0 : σp (0 : unitInterval) = e := σp.source
  have hσ1 : σp (1 : unitInterval) = (Work.EL.F e) e := σp.target
  have hlamP0 : lamP (0 : unitInterval) = u₀ - 1 := lamP.source
  -- membership results
  have hlamPK : ∀ t : unitInterval, lamP t ∈ hEXL.K₀ := by
    intro t
    by_cases h1 : (t : ℝ) ≤ 1 / 2
    · have hσt : lamP t = (q₁.trans q₂) (rep t h1) := by
        change ((q₁.trans q₂).trans q₃) t = _
        exact trans_le _ _ t h1
      rw [hσt]
      by_cases h2 : ((rep t h1 : unitInterval) : ℝ) ≤ 1 / 2
      · rw [trans_le _ _ _ h2, hq₁app, ← hlam0]
        exact hlamK 0
      · rw [trans_gt _ _ _ (not_le.mp h2), hq₂app]
        exact hlamK _
    · have ht : lamP t = q₃ (repm t (not_le.mp h1)) := by
        change ((q₁.trans q₂).trans q₃) t = _
        exact trans_gt _ _ t (not_le.mp h1)
      rw [ht, hq₃app, ← hlam1]
      exact hlamK 1
  have hlamPW : ∀ t : unitInterval,
      (v : ℂ) + (lamP t - (u₀ - 1)) ∈ Work.GATE2.slitAt v := by
    intro t
    by_cases h1 : (t : ℝ) ≤ 1 / 2
    · have hσt : lamP t = (q₁.trans q₂) (rep t h1) := by
        change ((q₁.trans q₂).trans q₃) t = _
        exact trans_le _ _ t h1
      rw [hσt]
      by_cases h2 : ((rep t h1 : unitInterval) : ℝ) ≤ 1 / 2
      · rw [trans_le _ _ _ h2, hq₁app, sub_self, add_zero]
        exact hv_mem
      · rw [trans_gt _ _ _ (not_le.mp h2), hq₂app]
        exact hlamW _
    · have ht : lamP t = q₃ (repm t (not_le.mp h1)) := by
        change ((q₁.trans q₂).trans q₃) t = _
        exact trans_gt _ _ t (not_le.mp h1)
      rw [ht, hq₃app,
        show (v : ℂ) + (u₀ - (u₀ - 1)) = (v : ℂ) + 1 by ring]
      exact hv1_mem
  have hlevel : ∀ l ∈ hEXL.K₀,
      X₁ ≤ ((v : ℂ) + (N₀ : ℂ) + (l - (u₀ - 1))).re ∧
      ((v : ℂ) + (N₀ : ℂ) + (l - (u₀ - 1))).re ≤ X₁ + W ∧
      |((v : ℂ) + (N₀ : ℂ) + (l - (u₀ - 1))).im| ≤ H := by
    intro l hl
    have hlB : ‖l‖ ≤ B := hK₀norm l hl
    have hlre1 : -B ≤ l.re := by
      have h := Complex.abs_re_le_norm l; rw [abs_le] at h; linarith
    have hlre2 : l.re ≤ B := by
      have h := Complex.abs_re_le_norm l; rw [abs_le] at h; linarith
    have hlim : |l.im| ≤ B := le_trans (Complex.abs_im_le_norm l) hlB
    have hre : ((v : ℂ) + (N₀ : ℂ) + (l - (u₀ - 1))).re
        = v + (N₀ : ℝ) + (l.re - (u₀).re + 1) := by
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re]
      ring
    have him : ((v : ℂ) + (N₀ : ℂ) + (l - (u₀ - 1))).im = l.im - (u₀).im := by
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.natCast_im,
        Complex.one_im]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hre]
      have h1 : l.re - (u₀).re + 1 ≥ Aβ := by
        have h2 := (abs_le.mp hu₀_re).2
        rw [hAβ]; linarith
      linarith [hlb]
    · rw [hre]
      have h1 : l.re - (u₀).re + 1 ≤ Bβ := by
        have h2 := (abs_le.mp hu₀_re).1
        rw [hBβ]; linarith
      linarith [hub]
    · rw [him]
      have h3 : |l.im - (u₀).im| ≤ B + r / 2 :=
        calc |l.im - (u₀).im| ≤ |l.im| + |(u₀).im| := by simpa using abs_sub_le l.im 0 (u₀).im
          _ ≤ B + r / 2 := add_le_add hlim hu₀_im
      rw [hHdef]; linarith
  -- the middle-piece norm bound
  have hmidnorm : ∀ s : unitInterval, ‖hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1)))‖ ≤ BB := by
    intro s
    have hlev := hlevel (lam s) (hlamK s)
    have hfar := hPL.far ((v : ℂ) + (N₀ : ℂ) + (lam s - (u₀ - 1)))
      (by linarith [hlev.1, hX₁ge])
    have hψK : hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lam s - (u₀ - 1))) ∈ Work.EL.K c₀ :=
      Work.ELRig.Pa_subset_K fl (FF.Pg_sub hfar.1)
    have hiter : (Work.EL.F c₀)^[N₀] (hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1)))) ∈ Work.EL.K c₀ := by
      rw [psi_shift_iter hPL N₀ (hlamW s)]
      convert hψK using 2
      ring
    have hK : hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1))) ∈ Work.EL.K c₀ :=
      mem_K_of_iterate_mem_K N₀ hiter
    calc ‖hPL.ψ ((v : ℂ) + (lam s - (u₀ - 1)))‖ ≤ max 2 ‖c₀‖ := norm_le_of_mem_K hK
      _ ≤ BB := by rw [hBBdef]; exact le_max_left _ _
  -- the pre-gate estimate
  have hC : ∀ t : unitInterval,
      ‖(Work.EL.F e)^[N₀] (σp t) - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)))‖ ≤ ρ_UT := by
    intro t
    by_cases h1 : (t : ℝ) ≤ 1 / 2
    · have hσt : σp t = (p₁.trans p₂) (rep t h1) := by
        change ((p₁.trans p₂).trans p₃) t = _
        exact trans_le _ _ t h1
      rw [hσt]
      by_cases h2 : ((rep t h1 : unitInterval) : ℝ) ≤ 1 / 2
      · -- first piece
        have hlt : lamP t = u₀ - 1 := by
          have : lamP t = (q₁.trans q₂) (rep t h1) := by
            change ((q₁.trans q₂).trans q₃) t = _
            exact trans_le _ _ t h1
          rw [this, trans_le _ _ _ h2, hq₁app]
        rw [trans_le _ _ _ h2, hp₁app, hlt,
          show (v : ℂ) + (N₀ : ℂ) + ((u₀ - 1) - (u₀ - 1)) = (v : ℂ) + (N₀ : ℂ) from by ring]
        have hs0 : (0 : ℝ) ≤ ((rep (rep t h1) h2 : unitInterval) : ℝ) := (rep _ _).2.1
        have hs1 : ((rep (rep t h1) h2 : unitInterval) : ℝ) ≤ 1 := (rep _ _).2.2
        have hznorm : ‖AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ)‖ ≤ BB := by
          have hmax := norm_lineMap_le_max e c₀ _ hs0 hs1
          have hen : ‖e‖ ≤ ‖c₀‖ + 1 := by
            calc ‖e‖ = ‖(e - c₀) + c₀‖ := by ring_nf
              _ ≤ ‖e - c₀‖ + ‖c₀‖ := norm_add_le _ _
              _ ≤ 1 + ‖c₀‖ := by linarith [he_one]
              _ = ‖c₀‖ + 1 := by ring
          have h1' : ‖e‖ ≤ BB := by
            rw [hBBdef]
            exact le_trans hen (le_trans (le_max_left _ _) (le_max_right _ _))
          have h2' : ‖c₀‖ ≤ BB := by
            rw [hBBdef]
            exact le_trans (le_max_right _ _) (le_max_left _ _)
          linarith [max_le h1' h2']
        have hzdist : ‖AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ) - c₀‖
            ≤ ‖e - c₀‖ := norm_lineMap_sub_right e c₀ _ hs0 hs1
        have hA := hclose e he_close _ hznorm
        have hB : ‖(Work.EL.F c₀)^[N₀] (AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ)) - hPL.ψ ((v : ℂ) + (N₀ : ℂ))‖
            < ρ_UT / 2 := by
          have h := hδ₀ (by rw [dist_eq_norm]; exact lt_of_le_of_lt hzdist he_δ₀)
          rw [dist_eq_norm, hval₀] at h
          exact h
        have hsplit : (Work.EL.F e)^[N₀] (AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ))
              - hPL.ψ ((v : ℂ) + (N₀ : ℂ))
            = ((Work.EL.F e)^[N₀] (AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ))
                - (Work.EL.F c₀)^[N₀] (AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ)))
              + ((Work.EL.F c₀)^[N₀] (AffineMap.lineMap e c₀ ((rep (rep t h1) h2 : unitInterval) : ℝ))
                - hPL.ψ ((v : ℂ) + (N₀ : ℂ))) := by ring
        rw [hsplit]
        exact le_trans (norm_add_le _ _) (by linarith [hA, hB])
      · -- middle piece
        have hlt : lamP t = lam (repm (rep t h1) (not_le.mp h2)) := by
          have : lamP t = (q₁.trans q₂) (rep t h1) := by
            change ((q₁.trans q₂).trans q₃) t = _
            exact trans_le _ _ t h1
          rw [this, trans_gt _ _ _ (not_le.mp h2), hq₂app]
        rw [trans_gt _ _ _ (not_le.mp h2), hp₂app, hlt]
        have htarget : (Work.EL.F c₀)^[N₀]
              (hPL.ψ ((v : ℂ) + (lam (repm (rep t h1) (not_le.mp h2)) - (u₀ - 1))))
            = hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lam (repm (rep t h1) (not_le.mp h2)) - (u₀ - 1))) := by
          rw [psi_shift_iter hPL N₀ (hlamW (repm (rep t h1) (not_le.mp h2)))]
          congr 1
          ring
        rw [← htarget]
        exact le_trans (hclose e he_close _ (hmidnorm (repm (rep t h1) (not_le.mp h2))))
          (by linarith)
    · -- third piece
      have hlt : lamP t = u₀ := by
        have ht : lamP t = q₃ (repm t (not_le.mp h1)) := by
          change ((q₁.trans q₂).trans q₃) t = _
          exact trans_gt _ _ t (not_le.mp h1)
        rw [ht, hq₃app]
      have hσt : σp t = p₃ (repm t (not_le.mp h1)) := by
        change ((p₁.trans p₂).trans p₃) t = _
        exact trans_gt _ _ t (not_le.mp h1)
      rw [hσt, hp₃app, hlt,
        show (v : ℂ) + (N₀ : ℂ) + (u₀ - (u₀ - 1)) = (v : ℂ) + (N₀ : ℂ) + 1 from by ring]
      set z₃ : ℂ :=
        AffineMap.lineMap c₁ ((Work.EL.F e) e) ((repm t (not_le.mp h1) : unitInterval) : ℝ) with hz₃
      have hs0 : (0 : ℝ) ≤ ((repm t (not_le.mp h1) : unitInterval) : ℝ) :=
        (repm t (not_le.mp h1)).2.1
      have hs1 : ((repm t (not_le.mp h1) : unitInterval) : ℝ) ≤ 1 :=
        (repm t (not_le.mp h1)).2.2
      have hFe : ‖(Work.EL.F e) e - c₁‖ < min δ₀ δ₁ := by
        have h := hδe (by simpa [dist_eq_norm] using he_δe)
        rw [dist_eq_norm, ← hc₁] at h
        exact lt_of_lt_of_le h (min_le_left _ _)
      have hFe1 : ‖(Work.EL.F e) e - c₁‖ < 1 := by
        have h := hδe (by simpa [dist_eq_norm] using he_δe)
        rw [dist_eq_norm, ← hc₁] at h
        exact lt_of_lt_of_le h (min_le_right _ _)
      have hznorm : ‖z₃‖ ≤ BB := by
        rw [hz₃]
        have hmax := norm_lineMap_le_max c₁ ((Work.EL.F e) e)
          ((repm t (not_le.mp h1) : unitInterval) : ℝ) hs0 hs1
        have hFen : ‖(Work.EL.F e) e‖ ≤ ‖c₁‖ + 1 := by
          calc ‖(Work.EL.F e) e‖ = ‖((Work.EL.F e) e - c₁) + c₁‖ := by ring_nf
            _ ≤ ‖(Work.EL.F e) e - c₁‖ + ‖c₁‖ := norm_add_le _ _
            _ ≤ 1 + ‖c₁‖ := by linarith [hFe1]
            _ = ‖c₁‖ + 1 := by ring
        have h1' : ‖c₁‖ ≤ BB := by
          rw [hBBdef]
          exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
        have h2' : ‖(Work.EL.F e) e‖ ≤ BB := by
          rw [hBBdef]
          exact le_trans hFen (le_trans (le_max_right _ _) (le_max_right _ _))
        exact le_trans hmax (max_le h1' h2')
      have hzdist : ‖z₃ - c₁‖ ≤ ‖(Work.EL.F e) e - c₁‖ := by
        rw [hz₃]
        exact norm_lineMap_sub_left c₁ ((Work.EL.F e) e)
          ((repm t (not_le.mp h1) : unitInterval) : ℝ) hs0 hs1
      have hA := hclose e he_close z₃ hznorm
      have hB : ‖(Work.EL.F c₀)^[N₀] z₃ - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)‖ < ρ_UT / 2 := by
        have hdist : dist z₃ c₁ < δ₁ := by
          rw [dist_eq_norm]
          exact lt_of_le_of_lt hzdist (lt_of_lt_of_le hFe (min_le_right _ _))
        have h := hδ₁ (x := z₃) hdist
        rw [dist_eq_norm, hval₁] at h
        exact h
      have hsplit : (Work.EL.F e)^[N₀] z₃ - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)
          = ((Work.EL.F e)^[N₀] z₃ - (Work.EL.F c₀)^[N₀] z₃)
            + ((Work.EL.F c₀)^[N₀] z₃ - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + 1)) := by ring
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (by linarith [hA, hB])
  -- the UT step
  have hD : ∀ t : unitInterval,
      ‖(Work.EL.F e)^[m - 1] (σp t) - Ψ (lamP t)‖ ≤ η := by
    intro t
    have hlK := hlamPK t
    have hlev := hlevel (lamP t) hlK
    have hwRe : hPL.X < ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))).re := by
      linarith [hlev.1, hX₁ge]
    have hfar := hPL.far ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))) hwRe
    have hφay : φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))))
        = (v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)) := by
      have heq : φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))))
          = fl.φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)))) :=
        congrFun hφa _
      rw [heq]; exact hfar.2
    have hyPa : hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))) ∈ Pa := hPgPa hfar.1
    have hclos : ‖(Work.EL.F e)^[N₀] (σp t)
        - hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)))‖ ≤ ρ_UT := hC t
    have hu : Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)))) = lamP t := by
      rw [hφay]
      have hnC : ((n : ℂ) + (N₀ : ℂ)) = (m : ℂ) - 1 := by
        rw [← Nat.cast_add, hnN₀, Nat.cast_sub hm_ge1]; ring
      have hmkC : ((m : ℂ) + (k : ℂ)) = (M.nIn : ℂ) := by exact_mod_cast hmk
      have hu₀' : (Work.PARIMPL.transU P M.nIn e) = u₀ + (k : ℂ) := by rw [hu₀def]; ring
      have hsub : Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
          + ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1)))
          = (Work.PARIMPL.transU P M.nIn e) - (M.nIn : ℂ)
            + ((n : ℂ) + (N₀ : ℂ)) + lamP t + 1 - u₀ := by ring
      rw [hsub, hnC, hu₀', ← hmkC]
      ring
    have hwin1 : (-Xo) ≤ (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))))).re := by
      rw [hu]
      have hlB : ‖lamP t‖ ≤ B := hK₀norm (lamP t) hlK
      have h1 : -(lamP t).re ≤ B := by
        have h := Complex.abs_re_le_norm (lamP t); rw [abs_le] at h; linarith
      rw [hXodef]; linarith
    have hwin2 : (Work.PARIMPL.transU P M.nIn e - (M.nIn : ℂ) - (v : ℂ) + (n : ℂ)
        + φa (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))))).re < -1 := by
      rw [hu]; exact hEXL.K₀_re (lamP t) hlK
    have key := hUTspec e ⟨heNm, by simpa [dist_eq_norm] using he_UT⟩
      (hPL.ψ ((v : ℂ) + (N₀ : ℂ) + (lamP t - (u₀ - 1))))
      ((Work.EL.F e)^[N₀] (σp t)) n hyPa
      (by rw [hφay]; exact hlev.1)
      (by rw [hφay]; exact hlev.2.1)
      (by rw [hφay]; exact hlev.2.2)
      hclos hwin1 hwin2
    rw [← Function.iterate_add_apply, hnN₀, hu] at key
    exact key
  -- the deviation estimate
  have hdev_all : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) Work.EL.alpha1
        ((Work.EL.F e)^[m - 1] (σp t))| < (1 / 8192 : ℝ) := by
    intro t
    have hlK := hlamPK t
    have hmemK : Ψ (lamP t) ∈ hEXL.𝒦 := by
      have h := hEXL.K₀_sub (lamP t) hlK
      have heq : Ψ (lamP t) = fl.Ψ (lamP t) := congrFun hΨ _
      rw [heq]
      exact h
    have hdist : ‖(Work.EL.F e)^[m - 1] (σp t) - Ψ (lamP t)‖ < η_dev :=
      lt_of_le_of_lt (hD t) hηdev
    exact hdev e he_dev _ ⟨Ψ (lamP t), hmemK, hdist⟩
  -- the potential estimate
  have hgreen_all : ∀ t : unitInterval,
      (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0
        < Work.Bottcher.green e ((Work.EL.F e)^[m - 1] (σp t)) := by
    intro t
    have hfloor : (3 / 4 : ℝ) * Work.Bottcher.green c₀ (Ψ (u₀ - 1))
        ≤ Work.Bottcher.green c₀ (Ψ (lamP t)) := by
      by_cases h1 : (t : ℝ) ≤ 1 / 2
      · have hlt : lamP t = (q₁.trans q₂) (rep t h1) := by
          change ((q₁.trans q₂).trans q₃) t = _
          exact trans_le _ _ t h1
        rw [hlt]
        by_cases h2 : ((rep t h1 : unitInterval) : ℝ) ≤ 1 / 2
        · rw [trans_le _ _ _ h2, hq₁app]
          linarith [Work.Bottcher.Green.green_nonneg c₀ (Ψ (u₀ - 1))]
        · rw [trans_gt _ _ _ (not_le.mp h2), hq₂app]
          exact hlamPot' _
      · have ht : lamP t = q₃ (repm t (not_le.mp h1)) := by
          change ((q₁.trans q₂).trans q₃) t = _
          exact trans_gt _ _ t (not_le.mp h1)
        rw [ht, hq₃app]
        have h := hlamPot' 1
        rwa [hlam1] at h
    have hzK : Ψ (lamP t) ∈ hEXL.𝒦 := by
      have h := hEXL.K₀_sub (lamP t) (hlamPK t)
      have heq : Ψ (lamP t) = fl.Ψ (lamP t) := congrFun hΨ _
      rw [heq]
      exact h
    have hwK : Ψ (u₀ - 1) ∈ hEXL.𝒦 := by
      have h := hEXL.K₀_sub (u₀ - 1) (by rw [← hlam0]; exact hlamK 0)
      have heq : Ψ (u₀ - 1) = fl.Ψ (u₀ - 1) := congrFun hΨ _
      rw [heq]
      exact h
    have hdw : ‖(Work.EL.F e)^[m - 1] (σp t) - Ψ (lamP t)‖ < η_g :=
      lt_of_le_of_lt (hD t) hηg
    have hdz : ‖(Work.EL.F e)^[m - 1] (σp (0 : unitInterval)) - Ψ (u₀ - 1)‖ < η_g := by
      have h := hD (0 : unitInterval)
      rw [hlamP0] at h
      exact lt_of_le_of_lt h hηg
    have hgc' := hgc e he_g (Ψ (lamP t)) hzK (Ψ (u₀ - 1)) hwK hfloor
      ((Work.EL.F e)^[m - 1] (σp t)) ((Work.EL.F e)^[m - 1] (σp (0 : unitInterval))) hdw hdz
    have hgf : Work.Bottcher.green e ((Work.EL.F e)^[m - 1] e)
        = (1024 : ℝ) ^ (m - 1) * (2 * Work.Bottcher.green e 0) := by
      rw [green_Ft e e (m - 1), green_crit e]
    rw [hσ0] at hgc'
    rw [hgf, show (1024 : ℝ) ^ (m - 1) * (2 * Work.Bottcher.green e 0)
        = 2 * ((1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0) from by ring] at hgc'
    linarith [hgc']
  exact ⟨m, hm_ge1, σp.toContinuousMap, hσ0, hσ1, hdev_all, hgreen_all⟩

end Work.GATE2.D1
