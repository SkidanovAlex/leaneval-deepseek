import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.rayPtCore
import Submission.Work.LandLeaves.family_repelling_expansion
import Submission.Work.LandLeaves.anchor_bound
import Submission.Work.LandLeaves.rpow_band
import Submission.Work.LandLeaves.transfer_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Quantitative decay of the ray tail at a repelling landing point (`landingDecay`)

The informal statement: if the dynamical ray of angle `θ` of the tricorn family lands at a
repelling point `y` of period `k` at the parameter `c` (`Work.Landing.landsAt c θ y`,
`Work.Landing.IsRepelling c k y`), and `θ` is periodic of period `2 * (k * q)` (so that the ray
is periodic of (tricorn, doubled) period `k * q`, `Work.Landing.PeriodicAngle`), then the tail of
the ray decays geometrically toward a continuous family `f ↦ yf f` of repelling fixed points of
`(T_f)^{2(kq)}` with `yf c = y`.

Precisely: there are `δ, η, C > 0`, a contraction rate `κ ∈ [0,1)` and a family `yf` such that for
every parameter `f` with `‖f - c‖ < δ`, every point `z` of the critical ray of `T_f` at angle `θ`
whose Böttcher level is `t ∈ (1, η ^ ((1/4^{kq})^m)]` satisfies

  `‖z - yf f‖ ≤ κ ^ m * C`.

The modulus `4^(kq) = Λ` is exactly the factor by which the level grows under the `kq`-th second
return map (`Work.LandLeaves.rayPt_iterate`), so the exponent `Λ^{-m}` records the `m` return
steps needed to bring the level down to the band `(1, η]`; each step costs the factor `κ` of the
uniform expansion `family_repelling_expansion`.

## Structure of the proof

* `Work.LandLeaves.rayPtCore` supplies the level point `rayPt c θ t` of the critical ray, its
  uniqueness/continuity, the return identity `rayPt_iterate`, and the abstract descent lemma
  `descent_membership`;
* `Work.LandLeaves.family_repelling_expansion` supplies the repelling fixed-point family `yf` and
  the uniform expansion of `(T_f)^{2(kq)}` about it;
* `Work.LandLeaves.anchor_bound` gives the level window `(1, η₀]` in which the ray is close to `y`
  at the parameter `c` (quantitative form of landing);
* `Work.LandLeaves.transfer_bound` transfers that window to nearby parameters `f`;
* `Work.LandLeaves.rpow_band` is the real-power bookkeeping that keeps the iterated levels inside
  the window;
* the levels are then iterated downwards, each return step costing a factor `κ`.
-/

namespace Work.LandLeaves

open Filter Set Classical
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

theorem landingDecay {c : ℂ} {θ : ℝ} {k q : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) (hland : Work.Landing.landsAt c θ y) (hq : 0 < q)
    (hper : Work.Landing.PeriodicAngle (Int.fract θ) (2 * (k * q))) :
    ∃ (δ η C κ : ℝ) (yf : ℂ → ℂ),
      0 < δ ∧ 1 < η ∧ 0 < C ∧ 0 ≤ κ ∧ κ < 1 ∧ ContinuousAt yf c ∧ yf c = y ∧
      (∀ (f : ℂ), ‖f - c‖ < δ → ∀ (m : ℕ) (z : ℂ), z ∈ Work.ParamRays.critDomain f →
        (∃ t : ℝ, 1 < t ∧ t ≤ η ^ (((1 : ℝ) / (4 : ℝ) ^ (k * q)) ^ m) ∧
            Work.Bottcher.varphiCrit f z = (t : ℂ) * Work.ParamRays.rayDir θ) →
        ‖z - yf f‖ ≤ κ ^ m * C) := by
  obtain ⟨δ₁, ρ₁, κ, yf, hδ₁, hρ₁, hκ0, hκ1, hyfc, hyfcont, hfixF, hexp⟩ :=
    Work.LandLeaves.family_repelling_expansion hrep hq
  obtain ⟨η₀, hη₀1, hanchor₀⟩ :=
    Work.LandLeaves.anchor_bound hland (ε := ρ₁ / 2) (by linarith)
  have hkq : 0 < k * q := Nat.mul_pos hrep.1.1 hq
  set Λ : ℝ := (4 : ℝ) ^ (k * q) with hΛdef
  have hΛ1 : 1 < Λ := by
    rw [hΛdef]
    exact one_lt_pow₀ (by norm_num) hkq.ne'
  set ℓ : ℝ := η₀ ^ (1 / Λ) with hℓdef
  have hℓ1 : 1 < ℓ := by
    rw [hℓdef]
    calc (1 : ℝ) = 1 ^ (1 / Λ) := (Real.one_rpow _).symm
      _ < η₀ ^ (1 / Λ) := Real.rpow_lt_rpow (by norm_num) hη₀1 (by positivity)
  have hℓη : ℓ < η₀ := by
    rw [hℓdef]
    calc η₀ ^ (1 / Λ) < η₀ ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hη₀1
            (by rw [one_div]; exact inv_lt_one_of_one_lt₀ hΛ1)
      _ = η₀ := Real.rpow_one η₀
  have hℓΛ : ℓ ^ Λ = η₀ := by
    rw [hℓdef, ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hη₀1)),
      one_div_mul_cancel (ne_of_gt (lt_trans zero_lt_one hΛ1)), Real.rpow_one]
  have hc : c ∈ Mandelbar := Work.LandLeaves.mem_mandelbar_of_landsAt hland
  have hanchorℓ : ∀ t : ℝ, ℓ ≤ t → t ≤ η₀ → ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c →
      Work.Bottcher.varphiCrit c z = (t : ℂ) * Work.ParamRays.rayDir θ → ‖z - y‖ ≤ ρ₁ / 2 :=
    fun t ht1 ht2 z hz hzφ => hanchor₀ t (by linarith) ht2 z hz hzφ
  obtain ⟨δ₂, hδ₂, htrans⟩ :=
    transfer_bound hc hℓ1 hℓη.le (by linarith) hanchorℓ hyfcont hyfc
  refine ⟨min δ₁ δ₂, η₀, ρ₁, κ, yf, lt_min hδ₁ hδ₂, hη₀1, hρ₁, hκ0, hκ1, hyfcont, hyfc, ?_⟩
  intro f hf m z hz htz
  obtain ⟨t, ht1, htm, htzval⟩ := htz
  have hf₁ : ‖f - c‖ < δ₁ := lt_of_lt_of_le hf (min_le_left _ _)
  have hf₂ : ‖f - c‖ < δ₂ := lt_of_lt_of_le hf (min_le_right _ _)
  set a : ℝ := Real.exp (Work.ParamRays.greenFun f 0) with hadef
  have ha1 : 1 ≤ a := by
    rw [hadef]; exact Real.one_le_exp (Work.ParamRays.greenFun_nonneg f 0)
  have ha_lt : a < t := by
    have h1 : ‖Work.Bottcher.varphiCrit f z‖ = Real.exp (Work.Bottcher.green f z) :=
      Work.Bottcher.norm_varphiCrit hz
    have h1' : t = Real.exp (Work.ParamRays.greenFun f z) := by
      rw [htzval, norm_mul, Work.ParamRays.norm_rayDir, mul_one,
        Complex.norm_of_nonneg (le_of_lt (lt_trans zero_lt_one ht1)),
        Work.Bottcher.CritBasic.green_eq] at h1
      exact h1
    rw [hadef, h1']
    exact Real.exp_lt_exp.mpr ((Work.ParamRays.mem_critDomain (c := f) (z := z)).mp hz)
  have hzpt : z = rayPt f θ t := rayPt_unique hz htzval ha_lt
  set D : ℝ → ℝ := fun s => ‖rayPt f θ s - yf f‖ with hDdef
  have hstep : ∀ s : ℝ, a < s → s ^ Λ ≤ η₀ → D s ≤ ρ₁ → D s ≤ κ * D (s ^ Λ) := by
    intro s has hsΛ hDs
    have h1 : ‖rayPt f θ s - yf f‖ ≤
        κ * ‖(Tantibar f)^[2 * (k * q)] (rayPt f θ s) - yf f‖ := hexp f hf₁ _ hDs
    have h2 : (Tantibar f)^[2 * (k * q)] (rayPt f θ s) = rayPt f θ (s ^ (4 ^ (k * q))) :=
      rayPt_iterate hper has
    have h3 : s ^ (4 ^ (k * q)) = s ^ Λ := by
      rw [hΛdef, ← Real.rpow_natCast s (4 ^ (k * q))]
      congr 1
      push_cast
      ring
    rw [h2, h3] at h1
    exact h1
  have hanch : ∀ s : ℝ, a < s → ℓ ≤ s → s ≤ η₀ → D s ≤ ρ₁ := by
    intro s has hℓs hsη
    have h1 := (rayPt_spec (f := f) (θ := θ) (t := s) has).1
    have h2 := (rayPt_spec (f := f) (θ := θ) (t := s) has).2
    exact htrans f hf₂ s hℓs hsη (rayPt f θ s) h1 h2
  have hmem : ∀ s : ℝ, a < s → s ≤ η₀ → D s ≤ ρ₁ := by
    by_cases haℓ : a < ℓ
    · have hanchb : ∀ s ∈ Set.Icc ℓ η₀, D s ≤ ρ₁ := by
        intro s hs
        exact hanch s (lt_of_lt_of_le haℓ hs.1) hs.1 hs.2
      have hcont : ∀ s ∈ Set.Ioc a η₀, ContinuousAt D s := by
        intro s hs
        have h1 : ContinuousAt (fun u : ℝ => rayPt f θ u) s :=
          (continuousOn_rayPt f θ).continuousAt (isOpen_Ioi.mem_nhds hs.1)
        simpa [hDdef] using (h1.sub continuousAt_const).norm
      exact descent_membership hΛ1 ha1 haℓ hℓη hρ₁ hκ0 hκ1 (le_of_eq hℓΛ) hcont hanchb hstep
    · intro s has hsη
      exact hanch s has (le_of_lt (lt_of_le_of_lt (le_of_not_gt haℓ) has)) hsη
  have hband : ∀ j : ℕ, j ≤ m → t ^ (Λ ^ (m - j)) ≤ η₀ := by
    intro j hj
    exact rpow_band hη₀1 hΛ1 ht1 hj (by rw [hΛdef]; exact htm)
  have ha_below : ∀ j : ℕ, j ≤ m → a < t ^ (Λ ^ (m - j)) := by
    intro j hj
    refine lt_of_lt_of_le ha_lt ?_
    have h1 : (1 : ℝ) ≤ Λ ^ (m - j) := one_le_pow₀ hΛ1.le
    calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ (Λ ^ (m - j)) := Real.rpow_le_rpow_of_exponent_le ht1.le h1
  have hiter : ∀ j : ℕ, j ≤ m → D (t ^ (Λ ^ (m - j))) ≤ κ ^ j * ρ₁ := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using hmem (t ^ (Λ ^ (m - 0))) (ha_below 0 (Nat.zero_le m))
          (hband 0 (Nat.zero_le m))
    | succ j ih =>
        intro hj
        have hj' : j ≤ m := le_trans (Nat.le_succ j) hj
        have hsΛ : (t ^ (Λ ^ (m - (j + 1)))) ^ Λ = t ^ (Λ ^ (m - j)) := by
          rw [← Real.rpow_mul (zero_le_one.trans ht1.le)]
          congr 1
          have h1 : m - (j + 1) + 1 = m - j := by omega
          rw [← pow_succ, h1]
        have hD : D (t ^ (Λ ^ (m - (j + 1)))) ≤ ρ₁ :=
          hmem _ (ha_below (j + 1) hj) (hband (j + 1) hj)
        have hsΛle : (t ^ (Λ ^ (m - (j + 1)))) ^ Λ ≤ η₀ := by
          rw [hsΛ]; exact hband j hj'
        have hst := hstep (t ^ (Λ ^ (m - (j + 1)))) (ha_below (j + 1) hj) hsΛle hD
        rw [hsΛ] at hst
        calc D (t ^ (Λ ^ (m - (j + 1))))
            ≤ κ * D (t ^ (Λ ^ (m - j))) := hst
          _ ≤ κ * (κ ^ j * ρ₁) := mul_le_mul_of_nonneg_left (ih hj') hκ0
          _ = κ ^ (j + 1) * ρ₁ := by ring
  have hfinal := hiter m (le_refl m)
  rw [Nat.sub_self, pow_zero, Real.rpow_one] at hfinal
  rw [hzpt]
  exact hfinal

end

end Work.LandLeaves
