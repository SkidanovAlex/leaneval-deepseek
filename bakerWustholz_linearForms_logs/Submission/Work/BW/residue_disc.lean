import Mathlib
import Submission.Work.BW.residue_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The residue formula on a disc

We prove `Work.BW.residue_disc` together with the auxiliary lemmas it needs.
-/

namespace Work.BW

open Complex Metric

open scoped Topology

/-- Membership transfer along an equality. -/
lemma mem_of_eq_mem {S : Finset ℂ} {z p : ℂ} (h : z = p) (hp : p ∈ S) : z ∈ (S : Set ℂ) := by
  rw [h]; exact hp

/-- `rD S n` does not vanish off `S`. -/
lemma rD_ne_zero {S : Finset ℂ} {n : ℂ → ℕ} {z : ℂ} (hz : ∀ p ∈ S, z ≠ p) : rD S n z ≠ 0 := by
  rw [rD, Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (sub_ne_zero.mpr (hz p hp))

/-- `rD S n` is entire. -/
lemma differentiableAt_rD (S : Finset ℂ) (n : ℂ → ℕ) (z : ℂ) :
    DifferentiableAt ℂ (rD S n) z := by
  unfold rD
  exact DifferentiableAt.fun_finsetProd fun p _ => (differentiableAt_id.sub_const p).pow (n p)

/-- `rF Y S n` is differentiable off `S`, for `Y` entire. -/
lemma differentiableAt_rF {Y : ℂ → ℂ} (hY : Differentiable ℂ Y) {S : Finset ℂ} {n : ℂ → ℕ}
    {z : ℂ} (hz : ∀ p ∈ S, z ≠ p) : DifferentiableAt ℂ (rF Y S n) z := by
  have h1 : DifferentiableAt ℂ Y z := hY.differentiableAt
  have h2 : DifferentiableAt ℂ (rD S n) z := differentiableAt_rD S n z
  have h3 : rD S n z ≠ 0 := rD_ne_zero hz
  have h4 : DifferentiableAt ℂ (Y / rD S n) z := h1.div h2 h3
  have hFr : rF Y S n = Y / rD S n := by
    funext w
    rw [rF, Pi.div_apply]
  rw [hFr]
  exact h4

/-- `rPrin a p N` is differentiable away from `p`. -/
lemma differentiableAt_rPrin (a : ℕ → ℂ) (p : ℂ) (N : ℕ) {z : ℂ} (hz : z ≠ p) :
    DifferentiableAt ℂ (rPrin a p N) z := by
  unfold rPrin
  exact DifferentiableAt.fun_sum fun i _ =>
    (differentiableAt_const (c := a i)).mul
      ((differentiableAt_id.sub_const p).zpow (Or.inl (sub_ne_zero.mpr hz)))

/-- Where `Y = W * rD`, the function `W` agrees with `rF Y S n`. -/
lemma rF_eq_of {W Y : ℂ → ℂ} {S : Finset ℂ} {n : ℂ → ℕ} {z : ℂ} (hz : z ∉ (S : Set ℂ))
    (h : Y z = W z * rD S n z) : rF Y S n z = W z := by
  have hne : rD S n z ≠ 0 :=
    rD_ne_zero fun p hp => by intro hzp; exact hz (mem_of_eq_mem hzp hp)
  rw [rF, h, mul_div_cancel_right₀ _ hne]

/-- A point of a sphere does not lie in the enclosed ball. -/
lemma ne_of_mem_sphere_of_mem_ball {c w z : ℂ} {ρ : ℝ} (_hρ : 0 < ρ)
    (hw : w ∈ Metric.ball c ρ) (hz : z ∈ Metric.sphere c ρ) : z ≠ w := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  rw [Metric.mem_ball, dist_eq_norm] at hw
  intro h
  rw [h] at hz
  linarith

/-- Integral of a principal part over a circle: only the `(z - w)⁻¹` term survives. -/
theorem circleIntegral_zpow_sum (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (w : ℂ)
    (hw : w ∈ Metric.ball c ρ) (N : ℕ) (a : ℕ → ℂ) :
    (∮ z in C(c, ρ), ∑ i ∈ Finset.range N, a i * (z - w) ^ ((i : ℤ) - (N : ℤ)))
      = 2 * (Real.pi : ℂ) * Complex.I * (if 0 < N then a (N - 1) else 0) := by
  have hInt : ∀ i ∈ Finset.range N,
      CircleIntegrable (fun z : ℂ => a i * (z - w) ^ ((i : ℤ) - (N : ℤ))) c ρ := by
    intro i _
    refine ContinuousOn.circleIntegrable hρ.le ?_
    have hz : ContinuousOn (fun z : ℂ => (z - w) ^ ((i : ℤ) - (N : ℤ)))
        (Metric.sphere c ρ) :=
      ((continuousOn_id' (Metric.sphere c ρ)).sub continuousOn_const).zpow₀ ((i : ℤ) - (N : ℤ))
        (fun z hz' => Or.inl (sub_ne_zero.mpr (ne_of_mem_sphere_of_mem_ball hρ hw hz')))
    exact continuousOn_const.mul hz
  rw [circleIntegral.integral_fun_sum hInt]
  have hterm : ∀ i : ℕ, (∮ z in C(c, ρ), a i * (z - w) ^ ((i : ℤ) - (N : ℤ)))
      = (if (i : ℤ) - (N : ℤ) = -1 then 2 * (Real.pi : ℂ) * Complex.I * a i else 0) := by
    intro i
    by_cases h : (i : ℤ) - (N : ℤ) = -1
    · have h1 : (∮ z in C(c, ρ), (z - w) ^ ((i : ℤ) - (N : ℤ)))
          = 2 * (Real.pi : ℂ) * Complex.I := by
        rw [h]
        simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := c) (w := w) (R := ρ) hw
      rw [if_pos h, circleIntegral.integral_const_mul, h1]
      ring
    · have h1 : (∮ z in C(c, ρ), (z - w) ^ ((i : ℤ) - (N : ℤ))) = 0 :=
        circleIntegral.integral_sub_zpow_of_ne h c w ρ
      rw [if_neg h, circleIntegral.integral_const_mul, h1, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hc : ((N - 1 : ℕ) : ℤ) - (N : ℤ) = -1 := by omega
    have hs : (∑ i ∈ Finset.range N,
          (if (i : ℤ) - (N : ℤ) = -1 then 2 * (Real.pi : ℂ) * Complex.I * a i else 0))
        = (if ((N - 1 : ℕ) : ℤ) - (N : ℤ) = -1 then
            2 * (Real.pi : ℂ) * Complex.I * a (N - 1) else 0) :=
      Finset.sum_eq_single (N - 1)
        (fun i hi hne => by
          rw [if_neg]
          intro h2
          have hi' : i < N := Finset.mem_range.mp hi
          exact hne (by omega))
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.sub_lt hN Nat.one_pos)) hmem)
    rw [hs, if_pos hc, if_pos hN]

/-- Away from a finite set, a point has a neighbourhood avoiding it. -/
lemma eventually_ne_finset {T : Finset ℂ} {z : ℂ} (hz : z ∉ T) :
    ∀ᶠ w in 𝓝 z, ∀ q ∈ T, w ≠ q := by
  have hopen : IsOpen (((T : Finset ℂ) : Set ℂ))ᶜ :=
    (Set.Finite.isClosed (Finset.finite_toSet T)).isOpen_compl
  filter_upwards [hopen.mem_nhds (by simpa using hz)] with w hw
  simp only [Set.mem_compl_iff, Finset.mem_coe] at hw
  exact fun q hq hwq => hw (by rw [hwq]; exact hq)

/-- `rPrin a q N` is analytic away from `q`. -/
lemma analyticAt_rPrin (a : ℕ → ℂ) (q : ℂ) (N : ℕ) {z : ℂ} (hz : z ≠ q) :
    AnalyticAt ℂ (rPrin a q N) z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact differentiableAt_rPrin a q N hw

/-- A finite sum of principal parts is analytic off the corresponding poles. -/
lemma analyticAt_finset_sum_rPrin (T : Finset ℂ) (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ) {z : ℂ}
    (hz : z ∉ T) : AnalyticAt ℂ (fun w => ∑ q ∈ T, rPrin (a q) q (N q) w) z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_finset hz] with w hw
  exact DifferentiableAt.fun_sum fun q hq => differentiableAt_rPrin (a q) q (N q) (hw q hq)

/-- The regular part `rNice` is analytic at the pole it is built from. -/
theorem analyticAt_rNice (Y : ℂ → ℂ) (S : Finset ℂ) (n : ℂ → ℕ) (H : ℂ → ℂ → ℂ) (p : ℂ)
    (hH : AnalyticAt ℂ (H p) 0) (hp : p ∈ S) : AnalyticAt ℂ (rNice Y S n H p) p := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => H p (z - p)) p := by
    simpa using hH.comp_sub p
  have h2 : AnalyticAt ℂ (fun z : ℂ => ∑ q ∈ S.erase p, rPrin (rC Y S n q) q (n q) z) p :=
    analyticAt_finset_sum_rPrin (S.erase p) (fun q => rC Y S n q) (fun q => n q)
      (Finset.notMem_erase p S)
  have h3 : AnalyticAt ℂ (rNice Y S n H p) p := by
    have h4 : rNice Y S n H p = (fun z : ℂ => H p (z - p))
        - fun z : ℂ => ∑ q ∈ S.erase p, rPrin (rC Y S n q) q (n q) z := by
      funext w
      rw [rNice, Pi.sub_apply]
    rw [h4]
    exact h1.sub h2
  exact h3

/-- Away from the pole `p`, the function `rG` coincides with `rNice p`. -/
lemma rG_eq_rNice {Y : ℂ → ℂ} {S : Finset ℂ} {n : ℂ → ℕ} {H : ℂ → ℂ → ℂ} {p : ℂ}
    (hp : p ∈ S) (hH : rIsExpansion Y S n H p) {w : ℂ} (hw : w ≠ p) :
    rG Y S n w = rNice Y S n H p w := by
  have hexp : rF Y S n w = rPrin (rC Y S n p) p (n p) w + H p (w - p) := by
    have h := hH.2.2 (w - p) (sub_ne_zero.mpr hw)
    have hzw : p + (w - p) = w := by ring
    simpa [hzw] using h
  have hsplit : (∑ q ∈ S, rPrin (rC Y S n q) q (n q) w)
      = rPrin (rC Y S n p) p (n p) w
        + ∑ q ∈ S.erase p, rPrin (rC Y S n q) q (n q) w := by
    rw [← Finset.sum_erase_add S (fun q => rPrin (rC Y S n q) q (n q) w) hp, add_comm]
  have hG : rG Y S n w = rF Y S n w - ∑ q ∈ S, rPrin (rC Y S n q) q (n q) w := rfl
  have hN : rNice Y S n H p w = H p (w - p)
      - ∑ q ∈ S.erase p, rPrin (rC Y S n q) q (n q) w := rfl
  rw [hG, hsplit, hexp, hN]
  ring

/-- Local expansion of `Y / ∏ (z - p')^(n p')` at the poles `p ∈ S`. -/
theorem exists_expansion_local (Y : ℂ → ℂ) (hY : Differentiable ℂ Y) (S : Finset ℂ)
    (n : ℂ → ℕ) : ∃ H : ℂ → ℂ → ℂ, ∀ p ∈ S, rIsExpansion Y S n H p := by
  classical
  have key : ∀ p : ℂ, ∃ F : ℂ → ℂ, p ∈ S →
      AnalyticAt ℂ F 0 ∧
      (∀ w, rU Y S n p w
        = (∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ i) + w ^ (n p) * F w) ∧
      (∀ w ≠ 0, rF Y S n (p + w) = rPrin (rC Y S n p) p (n p) (p + w) + F w) := by
    intro p
    have hU : AnalyticAt ℂ (rU Y S n p) 0 := by
      have hYan : AnalyticAt ℂ (fun w : ℂ => Y (p + w)) 0 :=
        (hY.comp ((differentiable_const p).add differentiable_id)).analyticAt 0
      have hDan : AnalyticAt ℂ (fun w : ℂ => rDp S n p (p + w)) 0 := by
        rw [analyticAt_iff_eventually_differentiableAt]
        exact Filter.Eventually.of_forall fun z => by
          unfold rDp
          exact DifferentiableAt.fun_finsetProd fun q _ =>
            (((differentiableAt_const (c := p)).add differentiableAt_id).sub_const q).pow (n q)
      have hne : rDp S n p (p + 0) ≠ 0 := by
        rw [add_zero, rDp, Finset.prod_ne_zero_iff]
        intro q hq
        exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hq)))
      have hdiv : AnalyticAt ℂ ((fun w : ℂ => Y (p + w))
          / fun w : ℂ => rDp S n p (p + w)) 0 := hYan.div hDan hne
      have hU' : rU Y S n p
          = (fun w : ℂ => Y (p + w)) / fun w : ℂ => rDp S n p (p + w) := by
        funext w
        rw [rU, Pi.div_apply]
      rw [hU']
      exact hdiv
    obtain ⟨F, hF, hFid⟩ := hU.exists_eq_sum_add_pow_mul (n p)
    have hnum : ∀ w : ℂ,
        (∑ i ∈ Finset.range (n p), (w ^ i / ↑i.factorial) • iteratedDeriv i (rU Y S n p) 0)
          = ∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ i := by
      intro w
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [rC]
      simp only [smul_eq_mul]
      ring
    refine ⟨F, fun hp => ⟨hF, ?_, ?_⟩⟩
    · intro w
      rw [hFid w, hnum w, smul_eq_mul]
    · intro w hw
      have hD : rD S n (p + w) = rDp S n p (p + w) * w ^ (n p) := by
        rw [rD, rDp, ← Finset.prod_erase_mul S (fun q => (p + w - q) ^ (n q)) hp,
          add_sub_cancel_left]
      have hsum : (∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ i) / w ^ (n p)
          = ∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ ((i : ℤ) - ((n p : ℕ) : ℤ)) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hz : w ^ ((i : ℤ) - ((n p : ℕ) : ℤ)) = w ^ i / w ^ (n p) := by
          rw [zpow_sub₀ hw, zpow_natCast, zpow_natCast]
        rw [← mul_div_assoc', ← hz]
      have hrem : (w ^ (n p) * F w) / w ^ (n p) = F w := by
        rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hw)]
      calc rF Y S n (p + w)
          = (Y (p + w) / rDp S n p (p + w)) / w ^ (n p) := by rw [rF, hD, ← div_div]
        _ = rU Y S n p w / w ^ (n p) := by rw [rU]
        _ = ((∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ i) + w ^ (n p) * F w)
              / w ^ (n p) := by rw [hFid w, hnum w, smul_eq_mul]
        _ = (∑ i ∈ Finset.range (n p), rC Y S n p i * w ^ ((i : ℤ) - ((n p : ℕ) : ℤ)))
              + F w := by rw [add_div, hsum, hrem]
        _ = rPrin (rC Y S n p) p (n p) (p + w) + F w := by
              rw [rPrin]
              simp only [add_sub_cancel_left]
  choose H hH using key
  exact ⟨H, hH⟩

/-- The corrected function `rPhi` is differentiable everywhere. -/
theorem differentiableAt_rPhi (Y : ℂ → ℂ) (hY : Differentiable ℂ Y) (S : Finset ℂ)
    (n : ℂ → ℕ) (H : ℂ → ℂ → ℂ) (hH : ∀ p ∈ S, rIsExpansion Y S n H p) (z : ℂ) :
    DifferentiableAt ℂ (rPhi Y S n H) z := by
  classical
  by_cases hzS : z ∈ S
  · have hev : rPhi Y S n H =ᶠ[𝓝 z] rNice Y S n H z := by
      refine (eventually_ne_finset (Finset.notMem_erase z S)).mono fun w hw => ?_
      rcases eq_or_ne w z with hwz | hwz
      · rw [hwz]
        have hz0 : (∑ p ∈ S, (if z = p then rNice Y S n H p z - rG Y S n p else 0))
            = rNice Y S n H z z - rG Y S n z := by
          rw [Finset.sum_eq_single z (fun p hp hpz => if_neg (Ne.symm hpz))
            (fun hz' => absurd hzS hz')]
          simp
        have hG0 : rPhi Y S n H z = rG Y S n z
            + ∑ p ∈ S, (if z = p then rNice Y S n H p z - rG Y S n p else 0) := rfl
        rw [hG0, hz0]
        ring
      · have hwS : w ∉ (S : Set ℂ) := by
          intro hwmem
          rw [← Finset.insert_erase hzS] at hwmem
          rcases Finset.mem_insert.mp hwmem with h | h
          · exact hwz h
          · exact hw w h rfl
        have h1 : rPhi Y S n H w = rG Y S n w := by
          have hz0 : (∑ p ∈ S, (if w = p then rNice Y S n H p w - rG Y S n p else 0)) = 0 :=
            Finset.sum_eq_zero fun p hp => if_neg (fun h => hwS (by rw [h]; exact hp))
          rw [show rPhi Y S n H w
                = rG Y S n w
                  + ∑ p ∈ S, (if w = p then rNice Y S n H p w - rG Y S n p else 0)
                from rfl, hz0, add_zero]
        rw [h1, rG_eq_rNice hzS (hH z hzS) hwz]
    exact (analyticAt_rNice Y S n H z (hH z hzS).1 hzS).differentiableAt.congr_of_eventuallyEq hev
  · have hev : rPhi Y S n H =ᶠ[𝓝 z] rG Y S n := by
      refine (eventually_ne_finset hzS).mono fun w hw => ?_
      have hwS : w ∉ (S : Set ℂ) := fun hmem => hw w hmem rfl
      have hz0 : (∑ p ∈ S, (if w = p then rNice Y S n H p w - rG Y S n p else 0)) = 0 :=
        Finset.sum_eq_zero fun p hp => if_neg (fun h => hwS (by rw [h]; exact hp))
      rw [show rPhi Y S n H w
            = rG Y S n w + ∑ p ∈ S, (if w = p then rNice Y S n H p w - rG Y S n p else 0)
            from rfl, hz0, add_zero]
    have hG : DifferentiableAt ℂ (rG Y S n) z := by
      have h1 : DifferentiableAt ℂ (rF Y S n) z :=
        differentiableAt_rF hY fun p hp => by intro h; exact hzS (by rw [h]; exact hp)
      have h2 : DifferentiableAt ℂ (fun w => ∑ p ∈ S, rPrin (rC Y S n p) p (n p) w) z :=
        DifferentiableAt.fun_sum fun p hp =>
          differentiableAt_rPrin (rC Y S n p) p (n p) (by intro h; exact hzS (by rw [h]; exact hp))
      have hG' : rG Y S n = fun w => rF Y S n w
          - ∑ p ∈ S, rPrin (rC Y S n p) p (n p) w := rfl
      rw [hG']
      exact h1.sub h2
    exact hG.congr_of_eventuallyEq hev

/-- Residue formula on a disc. Let `Y : ℂ → ℂ` be entire and let `W` agree off the finite set
`S ⊆ ball 0 R` with `Y z / ∏_{p ∈ S} (z - p) ^ (n p)` (the value of `W` at the poles themselves is
irrelevant). Then the integral of `W` over the big circle `C(0,R)` equals the sum of its integrals
over the small circles `C(p, ρ p)` around the poles, provided the small discs have positive radii,
lie in `ball 0 R`, and are separated from the other poles (`ρ p < ‖p - p'‖`). -/
theorem residue_disc (W Y : ℂ → ℂ) (R : ℝ) (S : Finset ℂ) (n : ℂ → ℕ) (ρ : ℂ → ℝ)
    (hR : 0 < R) (hS : ∀ p ∈ S, p ∈ Metric.ball 0 R) (hρ0 : ∀ p ∈ S, 0 < ρ p)
    (hρR : ∀ p ∈ S, Metric.closedBall p (ρ p) ⊆ Metric.ball 0 R)
    (hsep : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → ρ p < ‖p - p'‖)
    (hY : Differentiable ℂ Y)
    (hYeq : ∀ z ∈ Metric.closedBall 0 R, z ∉ (S : Set ℂ) →
      Y z = W z * (∏ p ∈ S, (z - p) ^ (n p))) :
    (∮ z in C(0, R), W z) = ∑ p ∈ S, ∮ z in C(p, ρ p), W z := by
  classical
  obtain ⟨H, hH⟩ := exists_expansion_local Y hY S n
  have hPhidiff : ∀ z : ℂ, DifferentiableAt ℂ (rPhi Y S n H) z :=
    fun z => differentiableAt_rPhi Y hY S n H hH z
  -- The pointwise splitting `rF = rPhi + principal parts` away from `S`.
  have hsplit : ∀ {z : ℂ}, z ∉ (S : Set ℂ) →
      rF Y S n z = rPhi Y S n H z + ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z := by
    intro z hz
    have h1 : rPhi Y S n H z = rG Y S n z := by
      have hzero : (∑ p ∈ S, (if z = p then rNice Y S n H p z - rG Y S n p else 0)) = 0 :=
        Finset.sum_eq_zero fun p hp => if_neg (by intro h; exact hz (mem_of_eq_mem h hp))
      change rG Y S n z + ∑ p ∈ S, (if z = p then rNice Y S n H p z - rG Y S n p else 0)
        = rG Y S n z
      rw [hzero, add_zero]
    have h2 : rG Y S n z = rF Y S n z - ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z := rfl
    rw [h1, h2]
    ring
  -- ### the big circle
  have hsphereBig : ∀ z ∈ Metric.sphere (0 : ℂ) R, z ∉ (S : Set ℂ) := by
    intro z hz hzS
    have hzn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hpn : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hS z hzS
    linarith
  have hW_big : (∮ z in C(0, R), W z) = ∮ z in C(0, R), rF Y S n z := by
    refine circleIntegral.integral_congr hR.le fun z hz => ?_
    exact (rF_eq_of (hz := hsphereBig z hz)
      (by simpa [rD] using hYeq z (Metric.sphere_subset_closedBall hz) (hsphereBig z hz))).symm
  have hsplitBig : (∮ z in C(0, R), rF Y S n z)
      = ∮ z in C(0, R), (rPhi Y S n H z + ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z) :=
    circleIntegral.integral_congr hR.le fun z hz => hsplit (hsphereBig z hz)
  have hIntPrinBig : ∀ p ∈ S, CircleIntegrable (rPrin (rC Y S n p) p (n p)) (0 : ℂ) R := by
    intro p hp
    refine ContinuousOn.circleIntegrable hR.le fun z hz => ?_
    have hzn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hpn : ‖p‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hS p hp
    have hzp : z ≠ p := by
      intro h
      rw [h] at hzn
      linarith
    exact (differentiableAt_rPrin (rC Y S n p) p (n p) hzp).continuousAt.continuousWithinAt
  have hIntPhiBig : CircleIntegrable (rPhi Y S n H) (0 : ℂ) R :=
    ContinuousOn.circleIntegrable hR.le fun z _ => (hPhidiff z).continuousAt.continuousWithinAt
  have hIntSumBig : CircleIntegrable (fun z => ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z)
      (0 : ℂ) R :=
    ContinuousOn.circleIntegrable hR.le fun z hz =>
      (DifferentiableAt.fun_sum fun p hp =>
        differentiableAt_rPrin (rC Y S n p) p (n p) (fun h => hsphereBig z hz (mem_of_eq_mem h hp))
        ).continuousAt.continuousWithinAt
  have hAddBig := circleIntegral.integral_add hIntPhiBig hIntSumBig
  have hZeroBig : (∮ z in C(0, R), rPhi Y S n H z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      (fun z _ => (hPhidiff z).continuousAt.continuousWithinAt) (fun z _ => hPhidiff z)
  have hSumBig := circleIntegral.integral_fun_sum hIntPrinBig
  have hPrinBig : ∀ p ∈ S, (∮ z in C(0, R), rPrin (rC Y S n p) p (n p) z)
      = 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) := by
    intro p hp
    have h := circleIntegral_zpow_sum (0 : ℂ) R hR p (hS p hp) (n p) (rC Y S n p)
    simpa [rPrin, rRes] using h
  have hBigFinal : (∮ z in C(0, R), rF Y S n z)
      = ∑ p ∈ S, 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) := by
    calc (∮ z in C(0, R), rF Y S n z)
        = ∮ z in C(0, R), (rPhi Y S n H z
            + ∑ p ∈ S, rPrin (rC Y S n p) p (n p) z) := hsplitBig
      _ = (∮ z in C(0, R), rPhi Y S n H z)
            + ∮ z in C(0, R), (∑ p ∈ S, rPrin (rC Y S n p) p (n p) z) := hAddBig
      _ = 0 + ∑ p ∈ S, ∮ z in C(0, R), rPrin (rC Y S n p) p (n p) z := by
            rw [hZeroBig, hSumBig]
      _ = ∑ p ∈ S, 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) := by
            rw [zero_add]
            exact Finset.sum_congr rfl hPrinBig
  -- ### the small circles
  have hsmall : ∀ p ∈ S,
      (∮ z in C(p, ρ p), rF Y S n z) = 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) ∧
      (∮ z in C(p, ρ p), W z) = ∮ z in C(p, ρ p), rF Y S n z := by
    intro p hp
    have hρp : 0 < ρ p := hρ0 p hp
    have hsphereSm : ∀ z ∈ Metric.sphere p (ρ p), z ∉ (S : Set ℂ) := by
      intro z hz hzS
      have hzρ : ‖z - p‖ = ρ p := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      rcases eq_or_ne z p with hzpeq | hzpne
      · rw [hzpeq, sub_self, norm_zero] at hzρ
        exact absurd hzρ.symm (ne_of_gt hρp)
      · have hne : p ≠ z := fun h => hzpne h.symm
        have hlt := hsep p hp z hzS hne
        rw [norm_sub_rev, hzρ] at hlt
        exact lt_irrefl (ρ p) hlt
    have hneBall : ∀ {z : ℂ}, z ∈ Metric.closedBall p (ρ p) →
        ∀ {q : ℂ}, q ∈ S → q ≠ p → z ≠ q := by
      intro z hz q hq hqp h
      have hzd : dist z p ≤ ρ p := by simpa [Metric.mem_closedBall] using hz
      have hpq : ρ p < dist p q := by
        simpa [dist_eq_norm] using hsep p hp q hq (fun h' => hqp h'.symm)
      have h1 : dist p q ≤ dist p z + dist z q := dist_triangle p z q
      have h2 : dist z q = 0 := by rw [h, dist_self]
      have h3 : dist p z = dist z p := dist_comm p z
      linarith
    have hIntPrinSm : ∀ q ∈ S, CircleIntegrable (rPrin (rC Y S n q) q (n q)) p (ρ p) := by
      intro q hq
      refine ContinuousOn.circleIntegrable hρp.le fun z hz => ?_
      have hzq : z ≠ q := by intro h; exact hsphereSm z hz (mem_of_eq_mem h hq)
      exact (differentiableAt_rPrin (rC Y S n q) q (n q) hzq).continuousAt.continuousWithinAt
    have hIntPhiSm : CircleIntegrable (rPhi Y S n H) p (ρ p) :=
      ContinuousOn.circleIntegrable hρp.le fun z _ => (hPhidiff z).continuousAt.continuousWithinAt
    have hIntSumSm : CircleIntegrable (fun z => ∑ q ∈ S, rPrin (rC Y S n q) q (n q) z) p (ρ p) :=
      ContinuousOn.circleIntegrable hρp.le fun z hz =>
        (DifferentiableAt.fun_sum fun q hq =>
          differentiableAt_rPrin (rC Y S n q) q (n q)
            (by intro h; exact hsphereSm z hz (mem_of_eq_mem h hq))).continuousAt.continuousWithinAt
    have hSplitSm : (∮ z in C(p, ρ p), rF Y S n z)
        = ∮ z in C(p, ρ p), (rPhi Y S n H z + ∑ q ∈ S, rPrin (rC Y S n q) q (n q) z) :=
      circleIntegral.integral_congr hρp.le fun z hz => hsplit (hsphereSm z hz)
    have hAddSm := circleIntegral.integral_add hIntPhiSm hIntSumSm
    have hZeroSm : (∮ z in C(p, ρ p), rPhi Y S n H z) = 0 :=
      circleIntegral_eq_zero_of_differentiable_on_off_countable hρp.le Set.countable_empty
        (fun z _ => (hPhidiff z).continuousAt.continuousWithinAt) (fun z _ => hPhidiff z)
    have hSumSm := circleIntegral.integral_fun_sum hIntPrinSm
    have hPrinSm : ∀ q ∈ S, (∮ z in C(p, ρ p), rPrin (rC Y S n q) q (n q) z)
        = (if q = p then 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) else 0) := by
      intro q hq
      by_cases hqp : q = p
      · rw [hqp, if_pos rfl]
        have h := circleIntegral_zpow_sum p (ρ p) hρp p
          (Metric.mem_ball.mpr (by simpa using hρp)) (n p) (rC Y S n p)
        simpa [rPrin, rRes] using h
      · rw [if_neg hqp]
        apply circleIntegral_eq_zero_of_differentiable_on_off_countable hρp.le Set.countable_empty
        · intro z hz
          have hzq : z ≠ q := hneBall hz hq hqp
          exact (differentiableAt_rPrin (rC Y S n q) q (n q) hzq).continuousAt.continuousWithinAt
        · intro z hz
          have hzq : z ≠ q := hneBall (Metric.ball_subset_closedBall hz.1) hq hqp
          exact differentiableAt_rPrin (rC Y S n q) q (n q) hzq
    refine ⟨?_, ?_⟩
    · calc (∮ z in C(p, ρ p), rF Y S n z)
          = ∮ z in C(p, ρ p), (rPhi Y S n H z
              + ∑ q ∈ S, rPrin (rC Y S n q) q (n q) z) := hSplitSm
        _ = (∮ z in C(p, ρ p), rPhi Y S n H z)
              + ∮ z in C(p, ρ p), (∑ q ∈ S, rPrin (rC Y S n q) q (n q) z) := hAddSm
        _ = 0 + ∑ q ∈ S, ∮ z in C(p, ρ p), rPrin (rC Y S n q) q (n q) z := by
              rw [hZeroSm, hSumSm]
        _ = 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) := by
              rw [zero_add]
              calc ∑ q ∈ S, (∮ z in C(p, ρ p), rPrin (rC Y S n q) q (n q) z)
                  = ∑ q ∈ S, (if q = p then 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p)
                      else 0) := Finset.sum_congr rfl hPrinSm
                _ = 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) :=
                    Finset.sum_ite_eq_of_mem' S p
                      (fun _ => 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p)) hp
    · refine circleIntegral.integral_congr hρp.le fun z hz => ?_
      have hzS := hsphereSm z hz
      have hzb : z ∈ Metric.closedBall (0 : ℂ) R :=
        Metric.ball_subset_closedBall (hρR p hp (Metric.sphere_subset_closedBall hz))
      exact (rF_eq_of (hz := hzS) (by simpa [rD] using hYeq z hzb hzS)).symm
  -- ### conclusion
  calc (∮ z in C(0, R), W z)
      = ∮ z in C(0, R), rF Y S n z := hW_big
    _ = ∑ p ∈ S, 2 * (Real.pi : ℂ) * I * rRes (rC Y S n p) (n p) := hBigFinal
    _ = ∑ p ∈ S, ∮ z in C(p, ρ p), W z := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact ((hsmall p hp).2.trans (hsmall p hp).1).symm

end Work.BW
