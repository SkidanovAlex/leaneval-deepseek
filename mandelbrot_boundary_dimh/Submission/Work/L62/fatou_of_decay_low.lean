/-
# The Fatou coordinate in the lift, lower end (`Work.L62.fatou_of_decay_low`)

This is the *lower-end* (negative imaginary direction) twin of `fatou_of_decay_up`/`lift_fatou`.
`H` is a holomorphic self-map of the lower half-plane `{Im < -y}` of the shape
`H w = w + γ + ρ w`, with `ρ` holomorphic there, decaying exponentially *toward* the end
`Im → -∞` at rate `M * exp (-2 * π * (-y - Im w))`, and with a uniform negative drift
`Im (H w - w) ≤ -κ` (`κ > 0`).

The map is asymptotically the translation `w ↦ w + (γ + c)`, and a Fatou coordinate is the
absolutely convergent series

`L w = w + ∑' n, (ρ (H^n w) - c)`,

which satisfies `L (H w) = L w + (γ + c)` by telescoping.  Convergence is geometric: the `n`-th
term is bounded by `M * exp (-2 * π * (Y - y - 1/2)) * exp (-2 * π * κ)^n` on the half-plane
`{Im < -Y + 1/2}` (this uses `hy : y + 1/2 ≤ Y`), and Cauchy's estimate on the disc of radius
`1/2` gives the same bound for the derivatives, whence `‖L' - 1‖ ≤ 1/2` deep in the half-plane
`{Im < -Y}` — exactly the hypothesis `hnum`.
-/
import Mathlib
import Submission.Work.L62.lift_fatou

namespace Work.L62

open Complex Filter Set Topology
open scoped Topology

noncomputable section

/-! ## Auxiliary analysis lemmas -/

/-- Iterates of a self-map of the *lower* half-plane `{Im < -y}` with uniform negative drift `κ`
stay in the half-plane, and their heights decrease at least linearly. -/
lemma iterate_im_low {H : ℂ → ℂ} {y κ : ℝ} {w : ℂ}
    (hmap : ∀ z : ℂ, z.im < -y → (H z).im < -y)
    (hdrift : ∀ z : ℂ, z.im < -y → (H z - z).im ≤ -κ) (hw : w.im < -y) (n : ℕ) :
    ((H^[n]) w).im < -y ∧ ((H^[n]) w).im ≤ w.im - n * κ := by
  induction n with
  | zero => exact ⟨by simpa using hw, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 : (H ((H^[n]) w)).im < -y := hmap _ h1
    have h4 : (H ((H^[n]) w) - (H^[n]) w).im ≤ -κ := hdrift _ h1
    have h5 : (H ((H^[n]) w) - (H^[n]) w).im
        = (H ((H^[n]) w)).im - ((H^[n]) w).im := Complex.sub_im _ _
    rw [Function.iterate_succ_apply']
    exact ⟨h3, by push_cast; linarith⟩

/-- Iterates of a function holomorphic on the lower half-plane `{Im < -y}` which maps it into
itself are holomorphic there. -/
lemma iterate_diff_low {H : ℂ → ℂ} {y : ℝ}
    (hH : DifferentiableOn ℂ H {z : ℂ | z.im < -y})
    (hmap : ∀ z : ℂ, z.im < -y → (H z).im < -y) (n : ℕ) :
    DifferentiableOn ℂ (H^[n]) {z : ℂ | z.im < -y} := by
  induction n with
  | zero => simpa using differentiableOn_id
  | succ n ih =>
    have hmt : Set.MapsTo (H^[n]) {z : ℂ | z.im < -y} {z : ℂ | z.im < -y} :=
      iterate_mapsTo (fun z hz => hmap z hz) n
    have h := hH.comp ih hmt
    rw [show H^[n + 1] = H ∘ H^[n] from
      funext fun x => Function.iterate_succ_apply' H n x]
    exact h

/-- Cauchy's estimate for a function decaying exponentially toward the lower end: if
`‖ψ w‖ ≤ M exp (-2 π (-y - Im w))` on `{Im < -y}`, then the same bound (with constant
`2 M exp π`) holds for the derivative one strip deeper, on `{Im < -y - 1/2}`. -/
lemma norm_deriv_le_of_decay_low {y M : ℝ} {ψ : ℂ → ℂ} (hM : 0 ≤ M)
    (hψd : DifferentiableOn ℂ ψ {w : ℂ | w.im < -y})
    (hdec : ∀ w : ℂ, w.im < -y → ‖ψ w‖ ≤ M * Real.exp (-2 * Real.pi * (-y - w.im))) :
    ∀ z : ℂ, z.im < -y - 1 / 2 →
      ‖deriv ψ z‖ ≤ (2 * M * Real.exp Real.pi) * Real.exp (-2 * Real.pi * (-y - z.im)) := by
  intro z hz
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hcl : closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | w.im < -y} := by
    intro w hw
    have hd : dist w z ≤ 1 / 2 :=
      Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw)
    have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
    have h5 : ‖w - z‖ ≤ 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
    have h6 : (w - z).im ≤ ‖w - z‖ := (abs_le.mp hle).2
    simp only [Set.mem_ofPred_eq]
    linarith
  have hdC : DiffContOnCl ℂ ψ (Metric.ball z (1 / 2)) :=
    DifferentiableOn.diffContOnCl (hψd.mono hcl)
  have hC : ∀ w ∈ Metric.sphere z (1 / 2),
      ‖ψ w‖ ≤ M * Real.exp (-2 * Real.pi * (-y - (z.im + 1 / 2))) := by
    intro w hw
    have hd : dist w z = 1 / 2 := Metric.mem_sphere.mp hw
    have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
    have h5 : ‖w - z‖ = 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
    have h6 : (w - z).im ≤ ‖w - z‖ := (abs_le.mp hle).2
    have hwy : w.im < -y := by linarith
    calc ‖ψ w‖ ≤ M * Real.exp (-2 * Real.pi * (-y - w.im)) := hdec w hwy
      _ ≤ M * Real.exp (-2 * Real.pi * (-y - (z.im + 1 / 2))) :=
          mul_le_mul_of_nonneg_left (exp_neg_two_pi_anti (by linarith)) hM
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := ψ) hR hdC hC
  have harg : -2 * Real.pi * (-y - (z.im + 1 / 2))
      = Real.pi + (-2 * Real.pi * (-y - z.im)) := by ring
  have haux : (M * Real.exp (-2 * Real.pi * (-y - (z.im + 1 / 2)))) / (1 / 2)
      = (2 * M * Real.exp Real.pi) * Real.exp (-2 * Real.pi * (-y - z.im)) := by
    rw [harg, Real.exp_add]
    ring
  rwa [haux] at hcauchy

/-- A series of holomorphic functions on the lower half-plane `{Im < -Y + 1/2}` dominated there
by the geometric progression `n ↦ A * r ^ n` (`0 ≤ r < 1`, `0 ≤ A`) converges on the deeper
half-plane `{Im < -Y}`; its sum is holomorphic there and its derivative is bounded by
`2 * A / (1 - r)` (Cauchy's estimate on the disc of radius `1 / 2`). -/
lemma tsum_geom_low {g : ℕ → ℂ → ℂ} {Y A r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hA : 0 ≤ A)
    (hdiff : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | z.im < -Y + 1 / 2})
    (hbd : ∀ (n : ℕ) (z : ℂ), z.im < -Y + 1 / 2 → ‖g n z‖ ≤ A * r ^ n) :
    (∀ z : ℂ, z.im < -Y → Summable fun n => g n z) ∧
    DifferentiableOn ℂ (fun z => ∑' n, g n z) {z : ℂ | z.im < -Y} ∧
    (∀ z : ℂ, z.im < -Y → ‖deriv (fun z => ∑' n, g n z) z‖ ≤ 2 * A / (1 - r)) := by
  have h1r : 0 < 1 - r := by linarith
  have htopen : IsOpen {z : ℂ | z.im < -Y} := isOpen_lt Complex.continuous_im continuous_const
  have htopen' : IsOpen {z : ℂ | z.im < -Y + 1 / 2} :=
    isOpen_lt Complex.continuous_im continuous_const
  have htconv : Convex ℝ {z : ℂ | z.im < -Y} := convex_halfSpace_im_lt (-Y)
  have hbd' : ∀ (n : ℕ) (z : ℂ), z.im < -Y → ‖deriv (g n) z‖ ≤ 2 * A * r ^ n := by
    intro n z hz
    have hR : (0 : ℝ) < 1 / 2 := by norm_num
    have hcl : closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | w.im < -Y + 1 / 2} := by
      intro w hw
      have hd : dist w z ≤ 1 / 2 :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw)
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      have h5 : ‖w - z‖ ≤ 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : (w - z).im ≤ ‖w - z‖ := (abs_le.mp hle).2
      simp only [Set.mem_ofPred_eq]
      linarith
    have hdC : DiffContOnCl ℂ (g n) (Metric.ball z (1 / 2)) :=
      DifferentiableOn.diffContOnCl ((hdiff n).mono hcl)
    have hsphere : ∀ w ∈ Metric.sphere z (1 / 2), ‖g n w‖ ≤ A * r ^ n := by
      intro w hw
      apply hbd n w
      have hd : dist w z = 1 / 2 := Metric.mem_sphere.mp hw
      have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h5 : ‖w - z‖ = 1 / 2 := by rw [dist_eq_norm] at hd; exact hd
      have h6 : (w - z).im ≤ ‖w - z‖ := (abs_le.mp hle).2
      have h4 : (w - z).im = w.im - z.im := Complex.sub_im w z
      linarith
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := g n) hR hdC hsphere
    have haux : (A * r ^ n) / (1 / 2) = 2 * A * r ^ n := by ring
    rw [haux] at hcauchy
    exact hcauchy
  have hAgeo : Summable (fun n : ℕ => A * r ^ n) := by
    simpa using (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hmaj : Summable (fun n : ℕ => 2 * A * r ^ n) := by
    simpa using (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * A)
  have hz₀ : (((-Y - 1 : ℝ) : ℂ) * Complex.I).im = -Y - 1 := by simp [Complex.mul_im]
  have hz₀mem : ((-Y - 1 : ℝ) : ℂ) * Complex.I ∈ {z : ℂ | z.im < -Y} := by
    simp only [Set.mem_ofPred_eq, hz₀]
    linarith
  have hbase : Summable (fun n : ℕ => g n (((-Y - 1 : ℝ) : ℂ) * Complex.I)) :=
    Summable.of_norm_bounded hAgeo (fun n => hbd n _ (by rw [hz₀]; linarith))
  have hmain : ∀ z : ℂ, z.im < -Y →
      HasDerivAt (fun z => ∑' n, g n z) (∑' n, deriv (g n) z) z := by
    intro z hz
    refine hasDerivAt_tsum_of_isPreconnected hmaj htopen htconv.isPreconnected
      (fun n u hu => ((hdiff n).differentiableAt (htopen'.mem_nhds (by
        simp only [Set.mem_ofPred_eq] at hu ⊢; linarith))).hasDerivAt)
      (fun n u hu => hbd' n u hu) hz₀mem hbase hz
  refine ⟨fun z hz => Summable.of_norm_bounded hAgeo (fun n => hbd n z (by linarith)),
    fun z hz => ((hmain z hz).differentiableAt).differentiableWithinAt, fun z hz => ?_⟩
  rw [(hmain z hz).deriv]
  have hsumm : Summable (fun n : ℕ => deriv (g n) z) :=
    Summable.of_norm_bounded hmaj (fun n => hbd' n z hz)
  calc ‖∑' n, deriv (g n) z‖ ≤ ∑' n, ‖deriv (g n) z‖ := norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n, 2 * A * r ^ n := Summable.tsum_le_tsum (fun n => hbd' n z hz) hsumm.norm hmaj
    _ = 2 * A / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-! ## The Fatou coordinate at the lower end -/

/-- **Fatou coordinate in the lift, lower end.**  `H` is a holomorphic self-map of the lower
half-plane `{Im < -y}` with increment `H w = w + γ + ρ w` (`ρ` holomorphic there), exponential
decay `‖ρ w - c‖ ≤ M exp (-2 π (-y - Im w))` toward the lower end, and uniform negative drift
`Im (H w - w) ≤ -κ` (`κ > 0`).  Then on the deeper half-plane `{Im < -Y}` (`Y ≥ y + 1/2`) there is
a "Fatou coordinate" `L` with `L (H w) = L w + (γ + c)` and `‖L' - 1‖ ≤ 1/2`, provided
`2 M exp (-2 π (Y - y - 1/2)) / (1 - exp (-2 π κ)) ≤ 1/2`. -/
theorem fatou_of_decay_low {y Y κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hy : y + 1 / 2 ≤ Y)
    {γ c : ℂ} {H ρ : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | Complex.im w < -y})
    (hmap : ∀ w : ℂ, Complex.im w < -y → Complex.im (H w) < -y)
    (hinc : ∀ w : ℂ, Complex.im w < -y → H w = w + γ + ρ w)
    (hρd : DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -y})
    (hdec : ∀ w : ℂ, Complex.im w < -y → ‖ρ w - c‖ ≤ M * Real.exp (-2 * Real.pi * (-y - Complex.im w)))
    (hdrift : ∀ w : ℂ, Complex.im w < -y → Complex.im (H w - w) ≤ -κ)
    (hnum : 2 * M * Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) /
      (1 - Real.exp (-2 * Real.pi * κ)) ≤ 1 / 2) :
    ∃ L : ℂ → ℂ, ∀ w : ℂ, Complex.im w < -Y → DifferentiableAt ℂ L w ∧
      L (H w) = L w + (γ + c) ∧ Complex.im (H w) < -Y ∧ ‖deriv L w - 1‖ ≤ 1 / 2 := by
  -- `ψ = ρ - c` is the exponentially decaying part
  set ψ : ℂ → ℂ := fun w => ρ w - c with hψdef
  have hψd : DifferentiableOn ℂ ψ {w : ℂ | w.im < -y} := by
    simpa only [hψdef] using hρd.sub_const c
  have hψdec : ∀ w : ℂ, w.im < -y → ‖ψ w‖ ≤ M * Real.exp (-2 * Real.pi * (-y - w.im)) := by
    intro w hw
    simpa only [hψdef] using hdec w hw
  -- the geometric rate and the domination constant
  set r : ℝ := Real.exp (-2 * Real.pi * κ) with hrdef
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  set A : ℝ := M * Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; exact mul_nonneg hM (Real.exp_pos _).le
  set g : ℕ → ℂ → ℂ := fun n z => ψ ((H^[n]) z) with hgdef
  have hgdiff : ∀ n : ℕ, DifferentiableOn ℂ (g n) {z : ℂ | z.im < -Y + 1 / 2} := by
    intro n
    have hsub : {z : ℂ | z.im < -Y + 1 / 2} ⊆ {z : ℂ | z.im < -y} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      linarith
    have hmt : Set.MapsTo (H^[n]) {z : ℂ | z.im < -Y + 1 / 2} {z : ℂ | z.im < -y} :=
      fun z hz => iterate_mapsTo (fun u hu => hmap u hu) n (hsub hz)
    have hcomp := hψd.comp ((iterate_diff_low hH hmap n).mono hsub) hmt
    simpa only [hgdef, Function.comp_def] using hcomp
  have hgbd : ∀ (n : ℕ) (z : ℂ), z.im < -Y + 1 / 2 → ‖g n z‖ ≤ A * r ^ n := by
    intro n z hz
    have hzy : z.im < -y := by linarith
    obtain ⟨h1, h2⟩ := iterate_im_low (y := y) (κ := κ) hmap hdrift hzy n
    have hψ := hψdec ((H^[n]) z) h1
    have hexp : Real.exp (-2 * Real.pi * (-y - ((H^[n]) z).im)) ≤
        Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) * r ^ n := by
      have harg : Y - y - 1 / 2 + n * κ ≤ -y - ((H^[n]) z).im := by linarith
      have hexp1 := exp_neg_two_pi_anti harg
      rw [hrdef]
      calc Real.exp (-2 * Real.pi * (-y - ((H^[n]) z).im))
          ≤ Real.exp (-2 * Real.pi * (Y - y - 1 / 2 + n * κ)) := hexp1
        _ = Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) * Real.exp (-2 * Real.pi * κ) ^ n := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            push_cast
            ring
    calc ‖g n z‖ = ‖ψ ((H^[n]) z)‖ := rfl
      _ ≤ M * Real.exp (-2 * Real.pi * (-y - ((H^[n]) z).im)) := hψ
      _ ≤ M * (Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) * r ^ n) :=
          mul_le_mul_of_nonneg_left hexp hM
      _ = A * r ^ n := by rw [hAdef]; ring
  obtain ⟨hsumm, hSdiff, hSderiv⟩ := tsum_geom_low (g := g) hr0 hr1 hA hgdiff hgbd
  set S : ℂ → ℂ := fun z => ∑' n, g n z with hSdef
  have htopenY : IsOpen {z : ℂ | z.im < -Y} := isOpen_lt Complex.continuous_im continuous_const
  have hS_at : ∀ z : ℂ, z.im < -Y → DifferentiableAt ℂ S z := by
    intro z hz
    have h : DifferentiableAt ℂ (fun z : ℂ => ∑' n, g n z) z :=
      hSdiff.differentiableAt (htopenY.mem_nhds hz)
    simpa only [hSdef] using h
  have hSbound : 2 * A / (1 - r) ≤ 1 / 2 := by
    have hrw : 2 * A / (1 - r) = 2 * M * Real.exp (-2 * Real.pi * (Y - y - 1 / 2)) /
        (1 - Real.exp (-2 * Real.pi * κ)) := by
      rw [hAdef, hrdef]
      ring
    rw [hrw]
    exact hnum
  have hSderiv' : ∀ z : ℂ, z.im < -Y → ‖deriv S z‖ ≤ 1 / 2 := by
    intro z hz
    have h : ‖deriv (fun z : ℂ => ∑' n, g n z) z‖ ≤ 2 * A / (1 - r) := hSderiv z hz
    have h2 : deriv S z = deriv (fun z : ℂ => ∑' n, g n z) z := by rw [hSdef]
    rw [h2]
    exact le_trans h hSbound
  set L : ℂ → ℂ := fun z => z + S z with hLdef
  have hLdiff : ∀ z : ℂ, z.im < -Y → DifferentiableAt ℂ L z := by
    intro z hz
    have h : DifferentiableAt ℂ (fun z : ℂ => z + S z) z :=
      differentiableAt_id.add (hS_at z hz)
    simpa only [hLdef] using h
  have hLderiv : ∀ z : ℂ, z.im < -Y → deriv L z = 1 + deriv S z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => z + S z) (1 + deriv S z) z :=
      (hasDerivAt_id z).add (hS_at z hz).hasDerivAt
    simpa only [hLdef] using h1.deriv
  have hLderiv1 : ∀ z : ℂ, z.im < -Y → ‖deriv L z - 1‖ ≤ 1 / 2 := by
    intro z hz
    rw [hLderiv z hz]
    have h : (1 + deriv S z) - 1 = deriv S z := by ring
    rw [h]
    exact hSderiv' z hz
  have hHdeep : ∀ w : ℂ, w.im < -Y → (H w).im < -Y := by
    intro w hw
    have hwy : w.im < -y := by linarith
    have h := hdrift w hwy
    have h2 : (H w - w).im = (H w).im - w.im := Complex.sub_im _ _
    linarith
  have hfun : ∀ w : ℂ, w.im < -Y → L (H w) = L w + (γ + c) := by
    intro w hw
    have hwy : w.im < -y := by linarith
    have hsm : Summable (fun n : ℕ => ψ ((H^[n]) w)) := by
      have h := hsumm w hw
      simpa only [hgdef] using h
    have hshift : (∑' n : ℕ, ψ ((H^[n]) (H w))) = (∑' n : ℕ, ψ ((H^[n]) w)) - ψ w := by
      have h1 : ∀ n : ℕ, ψ ((H^[n]) (H w)) = ψ ((H^[n + 1]) w) := by
        intro n
        have h2 : (H^[n]) (H w) = (H^[n + 1]) w := by
          simpa [Nat.succ_eq_add_one] using (Function.iterate_succ_apply H n w).symm
        rw [h2]
      calc (∑' n : ℕ, ψ ((H^[n]) (H w))) = ∑' n : ℕ, ψ ((H^[n + 1]) w) := tsum_congr h1
        _ = (∑' n : ℕ, ψ ((H^[n]) w)) - ψ w := by
            have h3 : (∑' b : ℕ, ψ ((H^[b + 1]) w)) + ψ w = ∑' b : ℕ, ψ ((H^[b]) w) := by
              have h4 := (Summable.tsum_eq_zero_add hsm).symm
              simpa [add_comm] using h4
            exact eq_sub_of_add_eq h3
    have hSeq : S (H w) = S w - ψ w := by
      simp only [hSdef, hgdef]
      exact hshift
    have hincw : H w = w + γ + ρ w := hinc w hwy
    simp only [hLdef]
    rw [hSeq, hincw]
    simp only [hψdef]
    ring
  exact ⟨L, fun w hw => ⟨hLdiff w hw, hfun w hw, hHdeep w hw, hLderiv1 w hw⟩⟩

end

end Work.L62
