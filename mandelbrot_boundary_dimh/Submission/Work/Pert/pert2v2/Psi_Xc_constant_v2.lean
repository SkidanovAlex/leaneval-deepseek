import Mathlib
import Submission.Work.Pert.pert2v2.Psi_Xc_constant
import Submission.Work.Pert.pert2v2.Psi_Xc_fatouUnique
import Submission.Work.Pert.pert2v2.exists_Psi_lower
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.pert2v2.XcV2_deep_legit
import Submission.Work.Pert.pert2v2.XcV2_increment
import Submission.Work.Pert.pert2v2.XcV2_deriv_bound

/-! Guidance from the project lead (the requester):

LEAD (Psi_Xc_constant_v2, L-A3 of pert2_v2). This replaces Pert/pert2v2/Psi_Xc_constant (its prover showed that the statement over ALL of QLeft (ξ₀+1) is too strong at shallow points; see NOTES_Psi_Xc_constant.md). v2 quantifies only over a DEEP-left sector QLeft Rd, with Rd chosen after Ξ′ and before Ψ.
Reuse, without re-proving, the proved helpers in Pert/pert2v2/Psi_Xc_constant.lean: Xc_ne_zero_of_mem, tau0_Xc, phi_norm_le, succ_mem_Dphi, Xc_add_one′, h_periodic, differentiableAt_Xc, PhiSec*. Import that module; its own top theorem has a sorry, but you do not use it. Also reuse Psi_Xc_fatouUnique.lean and exists_Psi_lower.lean.

## The proof implemented here (a variant of the lead's route)

Write `Xc d u = τ₀ (φ₀ u)` (the datum's curve, a semi-conjugacy from `u ↦ u+1` to
`F₀ = τ₀ ∘ f₀ ∘ τ₀`), `Q = Qreg none (some (-Ξ')) = {z | Re z + Ξ' < |Im z|}`,
`Dm w := |Im (Xc d w)| - Re (Xc d w) - Ξ'` (so `Xc d w ∈ Q ↔ 0 < Dm w`), and
`h w := Ψ (Xc d w) - w`.

1. `XcV2_deep_legit` : `Re w < -N` (N large) gives `Xc d w ∈ Q`.
2. `XcV2_increment` : `Dm (v-1) ≥ Dm v + 1/2` for `v ∈ QLeft ξ₀`, `‖v‖ ≥ R`.
3. `XcV2_deriv_bound` : `‖deriv (Ψ ∘ Xc d) v - 1‖ ≤ C / (-Re v)` deep left — this is
   `FatouDerivEstimate` (`hF.2.2.2.2.1`) applied with the constant field `v ≡ 1` on the ball of
   radius `-Re v / 2` (no near-translation input, and no Liouville/growth argument).

Then `h` is holomorphic on the deep half plane `H = {Re < -N_H}`, `1`-periodic there, and its
derivative vanishes there (the bound (3) at the arbitrarily deep translates `u - n` of `u ∈ H`),
so `h ≡ c` on `H`.  For `u ∈ QLeft R_d` with the two cone conditions the increment (2) shows that
the cone condition persists along `u, u-1, u-2, …` (`Dm (u-k) > 0` for all `k`), so the
periodicity `h (v+1) = h v` applies at every step, and `h u = h (u-n) = c` for `n` with
`u - n ∈ H`.
-/

namespace Work.Pert.pert2v2

open MandelDim Filter

open scoped Topology

noncomputable section

/-! ## 0. The three analysis inputs (proved by colleagues in parallel)

* `Work.Pert.pert2v2.XcV2_deep_legit`  — the curve enters the left cone deep left,
* `Work.Pert.pert2v2.XcV2_increment`   — the cone margin grows by `≥ 1/2` under `v ↦ v - 1`,
* `Work.Pert.pert2v2.XcV2_deriv_bound` — `FatouDerivEstimate` with the translation `v ≡ 1`.
-/

/-! ## 1. Elementary helpers -/

/-- `MandelDim.Qreg none (some (-Ξ'))` is the elementary set `{z | z.re + Ξ' < |z.im|}`. -/
theorem mem_Qreg_left_iff {Ξ' : ℝ} {z : ℂ} :
    z ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ↔ z.re + Ξ' < |z.im| := by
  constructor
  · intro h
    have h2 := h.2 (-(Ξ' : ℂ)) rfl
    simpa using h2
  · intro h
    refine ⟨by simp, fun b hb => ?_⟩
    rw [Option.mem_def, Option.some.injEq] at hb
    subst hb
    simpa using h

/-- The left cone is open. -/
theorem isOpen_Qreg_left (Ξ' : ℝ) : IsOpen (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := by
  have h : MandelDim.Qreg none (some (-(Ξ' : ℂ))) = {z : ℂ | z.re + Ξ' < |z.im|} := by
    ext z
    exact mem_Qreg_left_iff
  rw [h]
  exact isOpen_lt (Complex.continuous_re.add continuous_const) Complex.continuous_im.abs

/-- `QLeft` is antitone in its vertex parameter. -/
theorem QLeft_anti_v2 {ξ ξ' : ℝ} (h : ξ ≤ ξ') :
    MandelDim.QLeft ξ' ⊆ MandelDim.QLeft ξ := by
  intro w hw
  rw [Work.Parab.QLeft_iff] at hw ⊢
  set u : ℂ := w + (ξ : ℂ) with hu
  have hcast : ((ξ' : ℝ) : ℂ) = ((ξ : ℝ) : ℂ) + (((ξ' - ξ : ℝ)) : ℂ) := by push_cast; ring
  have hwu : w + (ξ' : ℂ) = u + ((ξ' - ξ : ℝ) : ℂ) := by rw [hu, hcast]; ring
  rw [hwu] at hw
  have hδ : 0 ≤ ξ' - ξ := by linarith
  have h1 : (u + ((ξ' - ξ : ℝ) : ℂ)).re = u.re + (ξ' - ξ) := by simp
  have h2 : ‖u + ((ξ' - ξ : ℝ) : ℂ)‖ ≤ ‖u‖ + (ξ' - ξ) := by
    have := norm_add_le u (((ξ' - ξ : ℝ)) : ℂ)
    rwa [Complex.norm_real, Real.norm_of_nonneg hδ] at this
  rw [h1] at hw
  linarith

/-- `QLeft ξ` is closed under `w ↦ w - 1`. -/
theorem QLeft_sub_one_v2 (ξ : ℝ) {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) :
    w - 1 ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff] at hw ⊢
  have hsplit : (w - 1) + (ξ : ℂ) = (w + (ξ : ℂ)) - 1 := by ring
  rw [hsplit]
  have hnorm : ‖w + (ξ : ℂ)‖ ≤ ‖(w + (ξ : ℂ)) - 1‖ + 1 := by
    have h2 : w + (ξ : ℂ) = ((w + (ξ : ℂ)) - 1) + 1 := by ring
    calc ‖w + (ξ : ℂ)‖ = ‖((w + (ξ : ℂ)) - 1) + 1‖ := congrArg norm h2
      _ ≤ ‖(w + (ξ : ℂ)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖(w + (ξ : ℂ)) - 1‖ + 1 := by simp
  have hre : ((w + (ξ : ℂ)) - 1).re = (w + (ξ : ℂ)).re - 1 := by simp
  rw [hre]
  linarith

/-- `QLeft ξ` is closed under all left translations by natural numbers. -/
theorem QLeft_sub_nat_v2 (ξ : ℝ) {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) (k : ℕ) :
    w - (k : ℂ) ∈ MandelDim.QLeft ξ := by
  induction k with
  | zero => simpa using hw
  | succ i ih =>
      have h1 : w - ((i : ℕ) : ℂ) - 1 = w - ((i + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [← h1]
      exact QLeft_sub_one_v2 ξ ih

/-- Derivative of `F - id`. -/
theorem deriv_sub_id {F : ℂ → ℂ} {v : ℂ} (hd : DifferentiableAt ℂ F v) :
    deriv (fun w : ℂ => F w - w) v = deriv F v - 1 := by
  have h2 : DifferentiableAt ℂ (fun w : ℂ => w) v := differentiableAt_id
  have h4 := deriv_sub (f := fun w : ℂ => F w) (g := fun w : ℂ => w) hd h2
  have h5 : deriv (fun w : ℂ => w) v = 1 := by simp
  have h3 : (fun w : ℂ => F w - w) = ((fun w : ℂ => F w) - fun w : ℂ => w) := rfl
  rw [h3, h4, h5]

/-- **The derivative of a `1`-periodic holomorphic function is `1`-periodic.** -/
theorem deriv_periodic_on {h : ℂ → ℂ} {H : Set ℂ} (hHopen : IsOpen H)
    (hper : ∀ v ∈ H, v + 1 ∈ H → h (v + 1) = h v)
    (hdiff : ∀ v ∈ H, DifferentiableAt ℂ h v) :
    ∀ v ∈ H, v + 1 ∈ H → deriv h (v + 1) = deriv h v := by
  intro v hv hv1
  have hshift : IsOpen {x : ℂ | x + 1 ∈ H} :=
    hHopen.preimage (continuous_id.add continuous_const)
  have hN : H ∩ {x : ℂ | x + 1 ∈ H} ∈ 𝓝 v :=
    Filter.inter_mem (hHopen.mem_nhds hv) (hshift.mem_nhds hv1)
  have hev : (fun x : ℂ => h (x + 1)) =ᶠ[𝓝 v] h := by
    filter_upwards [hN] with x hx
    exact hper x hx.1 hx.2
  have h2 : HasDerivAt h (deriv h (v + 1)) (v + 1) := (hdiff (v + 1) hv1).hasDerivAt
  have h1 : HasDerivAt (fun x : ℂ => x + 1) 1 v := (hasDerivAt_id v).add_const 1
  have hcomp : HasDerivAt (fun x : ℂ => h (x + 1)) (deriv h (v + 1)) v := by
    have hc := h2.comp v h1
    simpa only [Function.comp_def, mul_one] using hc
  have hcongr := hcomp.congr_of_eventuallyEq hev.symm
  have hfin := hcongr.deriv
  exact hfin.symm

/-- The half plane `{Re < -N}` is convex. -/
theorem convex_re_lt (N : ℝ) : Convex ℝ {w : ℂ | w.re < -N} := by
  have h : {w : ℂ | w.re < -N} = Complex.reLm ⁻¹' (Set.Iio (-N)) := by
    ext w
    simp
  rw [h]
  exact (convex_Iio (-N)).linear_preimage Complex.reLm

/-- **Vanishing of the derivative from a bound along the left translations.**  If `h` is
holomorphic on the half plane `{Re < -NH}`, `1`-periodic there, and `‖deriv h v‖` is bounded by
`C / (-NH - v.re + 1)` there, then `deriv h ≡ 0` on the half plane: the periodic derivative is
invariant under `v ↦ v - n`, and the bound at `v - n` tends to `0`. -/
theorem deriv_eq_zero_of_bound {h : ℂ → ℂ} {NH C : ℝ} (hC : 0 < C)
    (hdiff : DifferentiableOn ℂ h {w : ℂ | w.re < -NH})
    (hper : ∀ v : ℂ, v.re < -NH → (v + 1).re < -NH → h (v + 1) = h v)
    (hbound : ∀ v : ℂ, v.re < -NH → ‖deriv h v‖ ≤ C / (-NH - v.re + 1)) :
    ∀ u : ℂ, u.re < -NH → deriv h u = 0 := by
  have hHopen : IsOpen {w : ℂ | w.re < -NH} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hdiffAt : ∀ v : ℂ, v.re < -NH → DifferentiableAt ℂ h v :=
    fun v hv => (hdiff v hv).differentiableAt (hHopen.mem_nhds hv)
  have hderper : ∀ v : ℂ, v.re < -NH → (v - 1).re < -NH → deriv h v = deriv h (v - 1) := by
    intro v hv hv1
    have hstep := deriv_periodic_on hHopen (fun w hw hw1 => hper w hw hw1) hdiffAt (v - 1) hv1
      (by simpa using hv)
    simpa using hstep
  intro u hu
  have hmain : ∀ ε > 0, ‖deriv h u‖ < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
    have hchain : ∀ k : ℕ, deriv h u = deriv h (u - (k : ℂ)) := by
      intro k
      induction k with
      | zero => simp
      | succ j ih =>
          have hmemj : (u - (j : ℂ)).re < -NH := by
            have hre : (u - (j : ℂ)).re = u.re - (j : ℝ) := by simp
            have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            rw [hre]; linarith
          have hmemj1 : ((u - (j : ℂ)) - 1).re < -NH := by
            have hre : ((u - (j : ℂ)) - 1).re = u.re - (j : ℝ) - 1 := by simp
            have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            rw [hre]; linarith
          have hstep := hderper (u - (j : ℂ)) hmemj hmemj1
          have hcast : (u - (j : ℂ)) - 1 = u - ((j + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hcast] at hstep
          rw [ih]
          exact hstep
    rw [hchain n]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h2 : (0 : ℝ) < C / ε := div_pos hC hε
      linarith
    have hdeep : (u - (n : ℂ)).re < -NH := by
      have hre : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
      rw [hre]; linarith
    have hb := hbound _ hdeep
    have hval : C / (-NH - (u - (n : ℂ)).re + 1) < ε := by
      have hre : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
      have hlt1 : C / (n : ℝ) < ε := by
        rw [div_lt_iff₀ hnpos]
        have h : ε * (C / ε) < ε * (n : ℝ) := mul_lt_mul_of_pos_left hn hε
        have h2 : ε * (C / ε) = C := by field_simp
        linarith
      have hle1 : C / (-NH - (u - (n : ℂ)).re + 1) ≤ C / (n : ℝ) :=
        div_le_div_of_nonneg_left (a := C) (b := -NH - (u - (n : ℂ)).re + 1) (c := (n : ℝ))
          hC.le hnpos (by rw [hre]; linarith)
      linarith [hle1, hlt1]
    linarith [hb, hval]
  have hle : ‖deriv h u‖ ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by linarith [hmain ε hε])
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-! ## 2. The main theorem -/

theorem Psi_Xc_constant_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
    ∃ Rd : ℝ, d.ξ₀ + 1 ≤ Rd ∧
    ∀ Ψ : ℂ → ℂ,
    MandelDim.IsFatouCoordOn
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      Ψ (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
    ∃ c : ℂ, ∀ u : ℂ, u ∈ MandelDim.QLeft Rd →
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      MandelDim.tau0 (f₀ (MandelDim.tau0 (Work.Pert.Xc d u)))
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      Ψ (Work.Pert.Xc d u) = u + c := by
  classical
  -- (0) the radius of the disc around `0` contained in `D₀`
  obtain ⟨r, hrpos, hball⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ D₀ := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hd.1 (0 : ℂ) hd.2.1
    exact ⟨r, hr, hsub⟩
  -- (1) the increment constant (independent of `Ξ'` and of `Ψ`)
  obtain ⟨Rinc, hRinc0, hRinc⟩ := XcV2_increment d
  refine ⟨2 / r + 1, by positivity, fun Ξ' hΞ' => ?_⟩
  have hΞ'big : 2 / r < Ξ' := by linarith
  have hΞ'pos : 0 < Ξ' := by
    have : 0 < 2 / r := div_pos (by norm_num) hrpos
    linarith
  have hbig' : 2 / Ξ' < r := by
    rw [div_lt_iff₀ hΞ'pos]
    have h := (div_lt_iff₀ hrpos).mp hΞ'big
    linarith
  obtain ⟨Nleg₀, hNleg₀⟩ := XcV2_deep_legit d hΞ'pos
  set Nleg : ℝ := max Nleg₀ (d.ξ₀ + 1) with hNlegdef
  have hNleg_ge : Nleg₀ ≤ Nleg := le_max_left _ _
  have hNleg_le : d.ξ₀ + 1 ≤ Nleg := le_max_right _ _
  have hleg : ∀ u : ℂ, u.re < -Nleg →
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) :=
    fun u hu => hNleg₀ u (by linarith)
  refine ⟨max (d.ξ₀ + 1) (3 * Rinc + 3), le_max_left _ _, fun Ψ hΨ => ?_⟩
  -- constants of the `Ψ`-dependent part
  set Rd : ℝ := max (d.ξ₀ + 1) (3 * Rinc + 3) with hRddef
  have hRdξ : d.ξ₀ + 1 ≤ Rd := le_max_left _ _
  have hRdpos : 0 < Rd := by linarith [d.ξ₀_pos]
  have hRdinc : Rinc + 1 ≤ Rd / 3 := by
    have h : 3 * Rinc + 3 ≤ Rd := le_max_right _ _
    linarith
  have hQLeftξ : ∀ w : ℂ, w ∈ MandelDim.QLeft Rd → w ∈ MandelDim.QLeft d.ξ₀ :=
    fun w hw => QLeft_anti_v2 (by linarith [d.ξ₀_pos]) hw
  have hnorm : ∀ w : ℂ, w ∈ MandelDim.QLeft Rd → Rinc ≤ ‖w‖ := by
    intro w hw
    have h := Work.Parab.QLeft_subset_norm hRdpos hw
    have h2 : Rd / 3 < ‖w‖ := h
    linarith
  -- the cone condition as a scalar
  set Dm : ℂ → ℝ := fun w => |(Work.Pert.Xc d w).im| - (Work.Pert.Xc d w).re - Ξ' with hDmdef
  have hDm_iff : ∀ w : ℂ,
      Work.Pert.Xc d w ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ↔ 0 < Dm w := by
    intro w
    rw [mem_Qreg_left_iff]
    simp only [hDmdef]
    constructor <;> intro h <;> linarith
  have hDm_inc : ∀ v : ℂ, v ∈ MandelDim.QLeft d.ξ₀ → Rinc ≤ ‖v‖ →
      Dm v + 1 / 2 ≤ Dm (v - 1) := by
    intro v hv hvn
    have h := hRinc v hv hvn
    simp only [hDmdef]
    linarith
  -- (2) the derivative bound and the deep half plane
  obtain ⟨Nder, Cder, hCderpos, hder⟩ := XcV2_deriv_bound d hF hΨ hleg
  set NH : ℝ := max Nder (Nleg + 1) + 1 with hNHdef
  have hNH_der : Nder ≤ NH := by rw [hNHdef]; linarith [le_max_left Nder (Nleg + 1)]
  have hNH_leg : Nleg + 1 ≤ NH := by rw [hNHdef]; linarith [le_max_right Nder (Nleg + 1)]
  have hNH1 : 1 ≤ NH := by linarith [hNH_leg, hNleg_le, d.ξ₀_pos]
  have hHlegit : ∀ w : ℂ, w.re < -NH → w ∈ d.Dφ ∧ w + 1 ∈ d.Dφ ∧
      Work.Pert.Xc d w ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
    intro w hw
    have hwN : w.re < -Nleg := by linarith [hNH_leg]
    have hwξ : w.re < -d.ξ₀ := by linarith [hNleg_le]
    have hmem := hleg w hwN
    have hDφ : w ∈ d.Dφ := d.Q_sub (Work.Parab.halfplane_subset_QLeft d.ξ₀ hwξ)
    exact ⟨hDφ, succ_mem_Dphi d hΞ'pos hrpos hball hbig' hDφ hmem, hmem⟩
  -- the function whose constancy is at stake
  set h : ℂ → ℂ := fun w => Ψ (Work.Pert.Xc d w) - w with hhdef
  have hcompDiff : ∀ w : ℂ, w.re < -NH →
      DifferentiableAt ℂ (fun w : ℂ => Ψ (Work.Pert.Xc d w)) w := by
    intro w hw
    obtain ⟨hDφ, -, hXcQ⟩ := hHlegit w hw
    have hne : d.φ w ≠ 0 := by
      intro h0
      exact Xc_ne_zero_of_mem d hΞ'pos hXcQ (by simp [Work.Pert.Xc, MandelDim.tau0, h0])
    have hXcD : DifferentiableAt ℂ (Work.Pert.Xc d) w := differentiableAt_Xc d hDφ hne
    have hΨD : DifferentiableAt ℂ Ψ (Work.Pert.Xc d w) :=
      hΨ.1.differentiableAt ((isOpen_Qreg_left Ξ').mem_nhds hXcQ)
    exact hΨD.comp w hXcD
  have hderivAt : ∀ w : ℂ, w.re < -NH → DifferentiableAt ℂ h w := by
    intro w hw
    have h1 := hcompDiff w hw
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Ψ (Work.Pert.Xc d w) - w) w :=
      h1.sub differentiableAt_id
    simpa [hhdef] using h2
  have hdiffOn : DifferentiableOn ℂ h {w : ℂ | w.re < -NH} :=
    fun w hw => (hderivAt w hw).differentiableWithinAt
  have hper : ∀ w : ℂ, w.re < -NH → (w + 1).re < -NH → h (w + 1) = h w := by
    intro w hw hw1
    obtain ⟨hwDφ, -, hwQ⟩ := hHlegit w hw
    have hw1Dφ : w + 1 ∈ d.Dφ := (hHlegit (w + 1) hw1).1
    have hFQ : Work.Pert.F0f f₀ (Work.Pert.Xc d w)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
      have h := (hHlegit (w + 1) hw1).2.2
      rw [Xc_add_one' d hwDφ hw1Dφ] at h
      exact h
    have hstep := h_periodic d hΨ hwDφ hw1Dφ hwQ hFQ
    simpa [hhdef] using hstep
  -- the bound for `deriv h`
  have hbound : ∀ v : ℂ, v.re < -NH → ‖deriv h v‖ ≤ Cder / (-NH - v.re + 1) := by
    intro v hv
    have hvder : v.re ≤ -Nder := by linarith [hNH_der]
    have hb := hder v hvder
    have hsub : deriv h v = deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) v - 1 := by
      have h1 := hcompDiff v hv
      have h2 : h = fun w : ℂ => Ψ (Work.Pert.Xc d w) - w := rfl
      rw [h2]
      exact deriv_sub_id h1
    rw [hsub]
    have hden : 0 < -NH - v.re + 1 := by linarith
    have hle : Cder / (-v.re) ≤ Cder / (-NH - v.re + 1) :=
      div_le_div_of_nonneg_left (a := Cder) (b := -v.re) (c := -NH - v.re + 1)
        hCderpos.le hden (by linarith)
    linarith [hb, hle]
  -- (3) `h` is constant on the deep half plane
  obtain ⟨c, hc⟩ := IsOpen.exists_is_const_of_deriv_eq_zero
    (isOpen_lt Complex.continuous_re continuous_const)
    ((convex_re_lt NH).isPreconnected) hdiffOn
    (fun v hv => deriv_eq_zero_of_bound hCderpos hdiffOn hper hbound v hv)
  refine ⟨c, fun u huQLeft huQ huFQ => ?_⟩
  -- (4) the datum-level facts at `u`
  have huξ : u ∈ MandelDim.QLeft d.ξ₀ := hQLeftξ u huQLeft
  have huDφ : u ∈ d.Dφ := d.Q_sub huξ
  have hu1Dφ : u + 1 ∈ d.Dφ := succ_mem_Dphi d hΞ'pos hrpos hball hbig' huDφ huQ
  have hu1Q : Work.Pert.Xc d (u + 1) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
    rw [Xc_add_one' d huDφ hu1Dφ]
    exact huFQ
  -- (5) the cone condition persists to the left
  have hDm_all : ∀ k : ℕ, 0 < Dm (u - (k : ℂ)) := by
    intro k
    induction k with
    | zero =>
        have hh := (hDm_iff u).mp huQ
        simpa using hh
    | succ j ih =>
        have hmem : u - (j : ℂ) ∈ MandelDim.QLeft d.ξ₀ :=
          hQLeftξ _ (QLeft_sub_nat_v2 Rd huQLeft j)
        have hnrm : Rinc ≤ ‖u - (j : ℂ)‖ :=
          hnorm _ (QLeft_sub_nat_v2 Rd huQLeft j)
        have hinc := hDm_inc (u - (j : ℂ)) hmem hnrm
        have hcast : u - ((j + 1 : ℕ) : ℂ) = (u - (j : ℂ)) - 1 := by push_cast; ring
        rw [hcast]
        linarith
  -- (6) the chain of periodic steps down to the deep half plane
  have hchain : ∀ k : ℕ, h u = h (u - (k : ℂ)) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hvmem : u - ((j + 1 : ℕ) : ℂ) ∈ MandelDim.QLeft Rd :=
          QLeft_sub_nat_v2 Rd huQLeft (j + 1)
        have hv1mem : u - (j : ℂ) ∈ MandelDim.QLeft Rd :=
          QLeft_sub_nat_v2 Rd huQLeft j
        have hvDφ : u - ((j + 1 : ℕ) : ℂ) ∈ d.Dφ := d.Q_sub (hQLeftξ _ hvmem)
        have hv1Dφ : u - (j : ℂ) ∈ d.Dφ := d.Q_sub (hQLeftξ _ hv1mem)
        have hvp1 : u - ((j + 1 : ℕ) : ℂ) + 1 = u - (j : ℂ) := by push_cast; ring
        have hv1Dφ' : u - ((j + 1 : ℕ) : ℂ) + 1 ∈ d.Dφ := by
          rw [hvp1]; exact hv1Dφ
        have hvQ : Work.Pert.Xc d (u - ((j + 1 : ℕ) : ℂ))
            ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := (hDm_iff _).mpr (hDm_all (j + 1))
        have hFvQ : Work.Pert.F0f f₀ (Work.Pert.Xc d (u - ((j + 1 : ℕ) : ℂ)))
            ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
          have hEq : Work.Pert.F0f f₀ (Work.Pert.Xc d (u - ((j + 1 : ℕ) : ℂ)))
              = Work.Pert.Xc d (u - (j : ℂ)) := by
            have h := Xc_add_one' d hvDφ hv1Dφ'
            rw [hvp1] at h
            exact h.symm
          rw [hEq]
          exact (hDm_iff _).mpr (hDm_all j)
        have hstep := h_periodic d hΨ hvDφ hv1Dφ' hvQ hFvQ
        have hstep' : h (u - (j : ℂ)) = h (u - ((j + 1 : ℕ) : ℂ)) := by
          simp only [hhdef] at hstep ⊢
          rwa [hvp1] at hstep
        rw [ih, hstep']
  -- (7) land in the half plane
  obtain ⟨n, hn⟩ := exists_nat_gt (u.re + NH + 1)
  have hu_sub_H : (u - (n : ℂ)).re < -NH := by
    have hre : (u - (n : ℂ)).re = u.re - (n : ℝ) := by simp
    rw [hre]
    have h1 : u.re + NH < (n : ℝ) := by linarith [hn]
    linarith
  have hhu : h u = c := by
    rw [hchain n]
    exact hc _ hu_sub_H
  simp only [hhdef] at hhu
  have : Ψ (Work.Pert.Xc d u) = c + u := by
    rw [← hhu]
    ring
  simpa [add_comm] using this

end

end Work.Pert.pert2v2
