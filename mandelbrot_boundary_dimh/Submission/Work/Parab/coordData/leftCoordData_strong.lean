import Mathlib
import Submission.Work.Parab.LeftData
import Submission.Work.Parab.coordData.parabolicBounds_aeq
import Submission.Work.Parab.leftCoordData.exists_LeftCoordData
import Submission.Work.Parab.coverCone.norm_log_le_abs_log_add_pi

/-!
# The strengthened left coordinate data of a parabolic germ

`Work.Parab.coordData.leftCoordData_strong` re-runs the construction of
`Work.Parab.leftCoordData.exists_LeftCoordData` while keeping track of the two extra properties
needed downstream: the logarithmic coefficient `d.a` of the coordinate is `1 - a` for the germ's
quadratic coefficient `a`, and the coordinate is *proper at infinity* on its domain (`far values
come from far arguments`).  The construction is repeated (rather than derived from
`exists_LeftCoordData`) because both extra properties are properties of the *particular*
coordinate produced by the construction, not consequences of the fields of `LeftCoordData`.

Properness is proved by splitting the bounded part of the domain `L = {Re < -M₀} ∪ {ends}`:

* on the half-plane `{Re ζ < -M₀}` the coordinate is `-ψ (-ζ)` and the remainder
  `ψ w = w - c log w + O(1/Re w)` bounds it directly;
* on the ends (`M₁ < |Im ζ| ≤ R`, `Re ζ < 3 |Im ζ|`, `-ζ ∈ EscC`) the orbit-control lemma
  `Work.Parab.leftCoordData.orbit_ends_control` provides an index `n = nIdxC` at which the real
  part crosses the level `N`; the real parts grow by `≥ 1/2` per step, so `n ≤ 2 (N + 3 R) + 2`,
  and each step moves the point by at most `4 K / M₁`, giving both
  `‖wMap^[n] (-ζ)‖ ≤ R + n (1 + 4 K / M₁)` and the remainder `O(1/N)` at the crossing.
-/

namespace Work.Parab.coordData

set_option maxHeartbeats 2000000

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- For `0 < a ≤ t ≤ b` the absolute value of `log t` is bounded by the maximum of the absolute
values of `log a` and `log b`. -/
theorem abs_log_le_max_of_le {a t b : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    |Real.log t| ≤ max |Real.log a| |Real.log b| := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have hb : 0 < b := lt_of_lt_of_le ht htb
  have h1 : Real.log a ≤ Real.log t := Real.log_le_log ha hat
  have h2 : Real.log t ≤ Real.log b := Real.log_le_log ht htb
  by_cases h : 0 ≤ Real.log t
  · have hb0 : 0 ≤ Real.log b := le_trans h h2
    rw [abs_of_nonneg h, abs_of_nonneg hb0]
    exact le_trans h2 (le_max_right _ _)
  · have hlt : Real.log t < 0 := not_le.mp h
    have ha0 : Real.log a < 0 := lt_of_le_of_lt h1 hlt
    rw [abs_of_neg hlt, abs_of_neg ha0]
    exact le_trans (by linarith : -Real.log t ≤ -Real.log a) (le_max_left _ _)

/-- The ζ-plane left coordinate of a parabolic germ, in a strengthened form (the coefficient is
`ℂ`, as in `ParabolicBounds` and `exists_LeftCoordData`).  The construction of
`Work.Parab.leftCoordData.exists_LeftCoordData` (whose `Φ` is `-ΨC ∘ (-·)` on
`L = {Re < -M₀} ∪ {ends}`) also has the two extra properties needed downstream:
* the logarithmic coefficient of `Φ` is `1 - a` where `a` is the quadratic coefficient `h'(0)` of
  the germ (`ParabolicBounds f h a r A A'`), i.e. `d.a = 1 - a`;
* `Φ` is *proper at infinity* on `L`: far values come from far arguments.  This is what makes the
  `choose`-inverse `invOn Φ L` far out, and it is the hypothesis of
  `Work.Parab.inversion.inverse_asymptotic`.  It is NOT derivable from the fields of
  `LeftCoordData` (a bounded "blow-up" region can be added to `L`), so it must come from the
  construction. -/
theorem leftCoordData_strong {f : ℂ → ℂ} {D : Set ℂ} (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (d : Work.Parab.LeftCoordData f D) (h : ℂ → ℂ) (a : ℂ) (r A A' : ℝ),
      Work.FatouCoord.ParabolicBounds f h a r A A' ∧ d.a = 1 - a ∧
      (∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ d.L, N < ‖d.Φ ζ‖ → R < ‖ζ‖) := by
  classical
  -- ## 0. the quantitative data of `f` and of the reflected inverse germ `F`
  obtain ⟨h, a, r, A, A', hb, -⟩ := Work.Parab.basinEnters.exists_parabolicBounds_of_germ hg
  obtain ⟨finv, F, hF, r', A'', A''', hbF, hfinv, hffinv, hFdef⟩ :=
    Work.FatouCoord.Petal.reflected_inverse_germ hb
  obtain ⟨N, LF⟩ := Work.Parab.leftCoordData.exists_levelFacts hbF
  obtain ⟨Kts, hKtsnn, hrem⟩ := LF.rem
  have hr' : 0 < r' := hbF.hr
  -- ## 1. the orbit and asymptotic inputs
  obtain ⟨Mo, Co, hMopos, hConn, horb⟩ :=
    Work.Parab.leftCoordData.orbit_ends_control hbF (N := N) LF.pos
  obtain ⟨Na, hNapos, hNar, hasymF⟩ := Work.Parab.leftCoordData.psi_approx_of_ends hbF
  -- ## 2. the constants
  obtain ⟨M₀, hM0def⟩ : ∃ M : ℝ, M = |Mo| + |Na| + |N| + |1 / r| + |4 / r| + |4 / r'| + 10 :=
    ⟨_, rfl⟩
  obtain ⟨M₁, hM1def⟩ : ∃ M : ℝ,
      M = |Mo| + |Na| + |4 * N| + |1 / r| + |4 / r| + |4 / r'| + 20 := ⟨_, rfl⟩
  have hM0pos : 0 < M₀ := by rw [hM0def]; positivity
  have hM1pos : 0 < M₁ := by rw [hM1def]; positivity
  have hM0N : N ≤ M₀ := by rw [hM0def]; linarith [le_abs_self N,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0Mo : Mo ≤ M₀ := by rw [hM0def]; linarith [le_abs_self Mo,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0Na : Na ≤ M₀ := by rw [hM0def]; linarith [le_abs_self Na,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM0b : max (1 / r + 4) (4 / r' + 4) ≤ M₀ := by
    rw [hM0def]
    refine max_le ?_ ?_
    · linarith [le_abs_self (1 / r),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
    · linarith [le_abs_self (4 / r'),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1Mo : Mo ≤ M₁ := by rw [hM1def]; linarith [le_abs_self Mo,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1Na : Na ≤ M₁ := by rw [hM1def]; linarith [le_abs_self Na,abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1_4N : 4 * N ≤ M₁ := by rw [hM1def]; linarith [le_abs_self (4 * N),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  have hM1b : max (1 / r + 4) (4 / r' + 4) ≤ M₁ := by
    rw [hM1def]
    refine max_le ?_ ?_
    · linarith [le_abs_self (1 / r),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
    · linarith [le_abs_self (4 / r'),abs_nonneg Mo, abs_nonneg Na, abs_nonneg N, abs_nonneg (4 * N), abs_nonneg (1 / r), abs_nonneg (4 / r), abs_nonneg (4 / r')]
  -- ## 3. the domain and the coordinate
  obtain ⟨L, hLdef⟩ : ∃ S : Set ℂ, S = ({ζ : ℂ | ζ.re < -M₀} ∪
      {ζ : ℂ | -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) ∧
        M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im|}) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ g : ℂ → ℂ, g = (fun ζ => -Work.Parab.leftCoord.PsiC N
      (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) :=
    ⟨_, rfl⟩
  -- ## 4. the basic hypotheses of the extension lemmas
  have hGN : ∀ x : ℂ, N < x.re → N < (Work.FatouCoord.wMap F x).re := by
    intro x hx
    have hxnorm : N < ‖x‖ := lt_of_lt_of_le hx (Complex.re_le_norm x)
    have h := (LF.step.choose_spec.2 x hxnorm).2.2.2
    linarith
  have hmono : ∀ x : ℂ, N < ‖x‖ → x.re ≤ (Work.FatouCoord.wMap F x).re := by
    intro x hx
    have h := (LF.step.choose_spec.2 x hx).2.2.2
    linarith
  have hLsub : ∀ ζ ∈ L, -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := by
    intro ζ hζ
    rw [hLdef] at hζ
    rcases hζ with h | ⟨h1, -, -⟩
    · have hmem : ζ.re < -M₀ := h
      refine ⟨0, Work.Parab.leftCoord.GoodC.zero ?_⟩
      have hgoal : N < -ζ.re := by linarith
      simpa only [Complex.neg_re] using hgoal
    · exact h1
  have hLim_le : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L := by
    intro ζ h1 h2
    rw [hLdef]
    refine Or.inr ⟨?_, h1, h2⟩
    obtain ⟨n, hn1, -, hn3, -, -⟩ := horb (-ζ)
      (by simpa only [Complex.neg_im, abs_neg] using lt_of_le_of_lt hM1Mo h1)
      (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith)
    refine ⟨n, ?_, hn1⟩
    intro k hk
    have hk' := hn3 k hk
    simp only [Complex.neg_im, abs_neg] at hk'
    have h4 : N < |ζ.im| / 4 := by linarith
    linarith
  -- ## 5. the fields
  have hLopen : IsOpen L := by
    rw [hLdef]
    refine IsOpen.union (isOpen_lt Complex.continuous_re continuous_const) ?_
    exact ((Work.Parab.leftCoord.isOpen_EscC (N := N) (G := Work.FatouCoord.wMap F)
      LF.gdiff).preimage continuous_neg).inter
      ((isOpen_lt continuous_const (Continuous.abs Complex.continuous_im)).inter
        (isOpen_lt Complex.continuous_re
          (continuous_const.mul (Continuous.abs Complex.continuous_im))))
  have hΦholo : DifferentiableOn ℂ Φ L := by
    have h1 : DifferentiableOn ℂ (Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
        (Work.FatouCoord.fatouCoordW F (1 - (2 - a))))
        (Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F)) :=
      Work.Parab.leftCoord.PsiC_differentiableOn LF.abel hmono LF.gdiff LF.ψdiff
    have h2 : DifferentiableOn ℂ (fun ζ : ℂ => Work.Parab.leftCoord.PsiC N
        (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) L :=
      h1.comp differentiable_neg.differentiableOn fun ζ hζ => hLsub ζ hζ
    have h3 : DifferentiableOn ℂ (fun ζ : ℂ => -Work.Parab.leftCoord.PsiC N
        (Work.FatouCoord.wMap F) (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)) L :=
      h2.neg
    rwa [hΦdef]
  have hΦinj : Set.InjOn Φ L := by
    intro ζ1 hζ1 ζ2 hζ2 heq
    have hinj := Work.Parab.leftCoord.PsiC_injOn hGN LF.abel hmono LF.ψinj LF.ginj
    have h := hinj (hLsub ζ1 hζ1) (hLsub ζ2 hζ2) (by
      have h2 := congrArg (fun u : ℂ => -u) heq
      simp only [hΦdef] at h2
      simpa only [neg_neg] using h2)
    simpa using h
  have hΦabel : ∀ ζ ∈ L, Work.FatouCoord.wMap f ζ ∈ L →
      Φ (Work.FatouCoord.wMap f ζ) = Φ ζ + 1 := by
    intro ζ hζ hGζ
    have hx : -(Work.FatouCoord.wMap f ζ) ∈
        Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := hLsub _ hGζ
    have hbnd : max (1 / r + 4) (4 / r' + 4) ≤ ‖ζ‖ := by
      rw [hLdef] at hζ
      rcases hζ with h | ⟨-, h2, -⟩
      · have hmem : ζ.re < -M₀ := h
        have h3 : -ζ.re ≤ ‖ζ‖ := by
          have h4 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
          have h5 : -ζ.re ≤ |ζ.re| := neg_le_abs ζ.re
          linarith
        have h4 : M₀ ≤ -ζ.re := by linarith
        exact le_trans hM0b (le_trans h4 h3)
      · have h3 : M₁ ≤ ‖ζ‖ := by
          have h4 := Complex.abs_im_le_norm ζ
          linarith
        exact le_trans hM1b h3
    have hid : Work.FatouCoord.wMap F (-(Work.FatouCoord.wMap f ζ)) = -ζ :=
      Work.Parab.leftCoordData.wMap_F_neg_wMap hb hr' hfinv hFdef (le_max_left _ _) (le_max_right _ _) hbnd
    have habel := Work.Parab.leftCoord.PsiC_abel hGN LF.abel hx
    rw [hid] at habel
    have hmain : -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
        (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-(Work.FatouCoord.wMap f ζ))
        = -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ) + 1 := by
      rw [habel]; ring
    simpa only [hΦdef] using hmain
  have hΦasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)‖ < ε := by
    intro ε hε
    obtain ⟨R2, R2', hasym2⟩ := hasymF ε hε
    obtain ⟨Ld, hLddef⟩ : ∃ M : ℝ, M = max N (max Na (Kts / ε + R2' + 2)) + 1 := ⟨_, rfl⟩
    have hLdpos : 0 < Ld := by rw [hLddef]; positivity
    have hLdN : N ≤ Ld := by
      rw [hLddef]; linarith [le_max_left N (max Na (Kts / ε + R2' + 2))]
    have h0d : (0:ℝ) ≤ Kts / ε := div_nonneg hKtsnn hε.le
    have hLdNa : Na ≤ Ld := by
      rw [hLddef]
      linarith [le_trans (le_max_left Na (Kts / ε + R2' + 2))
        (le_max_right N (max Na (Kts / ε + R2' + 2)))]
    have hLdR : R2' ≤ Ld := by
      rw [hLddef]
      linarith [le_trans (le_max_right Na (Kts / ε + R2' + 2))
        (le_max_right N (max Na (Kts / ε + R2' + 2)))]
    obtain ⟨M2, C2, hM2pos, hC2nn, horb2⟩ :=
      Work.Parab.leftCoordData.orbit_ends_control hbF (N := Ld) hLdpos
    obtain ⟨M2', hM2def⟩ : ∃ M : ℝ, M = max (M2 + 1) (max (4 * N + 1) (R2 + 1)) := ⟨_, rfl⟩
    have hM2'lt : M2 < M2' := by
      rw [hM2def]; linarith [le_max_left (M2 + 1) (max (4 * N + 1) (R2 + 1))]
    have hM2'4N : 4 * N + 1 ≤ M2' := by
      rw [hM2def]
      linarith [le_trans (le_max_left (4 * N + 1) (R2 + 1))
        (le_max_right (M2 + 1) (max (4 * N + 1) (R2 + 1)))]
    have hM2'R2 : R2 + 1 ≤ M2' := by
      rw [hM2def]
      linarith [le_trans (le_max_right (4 * N + 1) (R2 + 1))
        (le_max_right (M2 + 1) (max (4 * N + 1) (R2 + 1)))]
    have hM2'pos : 0 < M2' := lt_trans hM2pos hM2'lt
    refine ⟨max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2), ?_⟩
    have endsCase : ∀ ζ : ℂ, M2' < |ζ.im| → ζ.re < 3 * |ζ.im| →
        ‖Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)‖ < ε := by
      intro ζ him hre
      obtain ⟨n, hn1, -, hn3, -, -⟩ := horb2 (-ζ)
        (by simp only [Complex.neg_im, abs_neg]; exact lt_trans hM2'lt him)
        (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith)
      have hgood : Work.Parab.leftCoord.GoodC N (Work.FatouCoord.wMap F) (-ζ) n := by
        refine ⟨fun k hk => ?_, by linarith⟩
        have hk' := hn3 k hk
        simp only [Complex.neg_im, abs_neg] at hk'
        have h4 : N < |ζ.im| / 4 := by linarith
        linarith
      have hxEsc : -ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := ⟨n, hgood⟩
      have hnle : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap F) (-ζ) ≤ n :=
        Work.Parab.leftCoord.nIdxC_le hgood
      have hstab := Work.Parab.leftCoord.psiC_iterate_ge hGN LF.abel hmono hxEsc hnle
      have hnorm := hasym2 (-ζ)
        (by simp only [Complex.neg_im, abs_neg]
            exact lt_trans (by linarith [hM2'R2] : R2 < M2') him)
        (by simp only [Complex.neg_re, Complex.neg_im, abs_neg]; linarith) n
        (fun k hk => by
          have hk' := hn3 k hk
          simpa only [Complex.neg_im, abs_neg] using hk')
        (by linarith [hLdNa, hn1]) (by linarith [hLdR, hn1])
      have hval : Φ ζ = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
          ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ)) := by
        have hPsi : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
            (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)
            = Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ) := by
          rw [hstab]; ring
        simp only [hΦdef, hPsi]
      rw [hval]
      have hgoal : -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ))
            - (ζ - (1 - a) * Complex.log (-ζ) - 0)
          = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a))
              ((Work.FatouCoord.wMap F)^[n] (-ζ)) - (n : ℂ)
              - ((-ζ) - (1 - (2 - a)) * Complex.log (-ζ))) := by
        ring
      rw [hgoal]
      simpa only [norm_neg] using hnorm
    intro ζ hζ hR
    rw [hLdef] at hζ
    by_cases hbig : M2' < |ζ.im|
    · refine endsCase ζ hbig ?_
      rcases hζ with h | ⟨-, -, h3⟩
      · have hmem : ζ.re < -M₀ := h
        have h2 : (0:ℝ) < |ζ.im| := lt_trans hM2'pos hbig
        linarith
      · exact h3
    · have hfar : ζ.re < -M₀ := by
        by_contra hcon
        push_neg at hcon
        have hends : M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im| := by
          rcases hζ with h | h
          · have hmem : ζ.re < -M₀ := h
            exfalso; linarith
          · exact ⟨h.2.1, h.2.2⟩
        obtain ⟨h1im, h1re⟩ := hends
        have hbnd : ‖ζ‖ ≤ M₀ + 4 * M2' := by
          have hsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have him : |ζ.im| ≤ M2' := not_lt.mp hbig
          have him2 : ζ.im ^ 2 ≤ M2' ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) him 2
          have hre_lo : -M₀ ≤ ζ.re := hcon
          have hre_hi : ζ.re ≤ 3 * M2' := by
            have h7 : 3 * |ζ.im| ≤ 3 * M2' := by linarith
            linarith
          have habsre : |ζ.re| ≤ M₀ + 3 * M2' := by
            rw [abs_le]; constructor <;> linarith
          have hre2 : ζ.re ^ 2 ≤ (M₀ + 3 * M2') ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) habsre 2
          have hmain : ‖ζ‖ ^ 2 ≤ (M₀ + 4 * M2') ^ 2 := by
            have h9 : ζ.re ^ 2 + ζ.im ^ 2 ≤ (M₀ + 3 * M2') ^ 2 + M2' ^ 2 := by linarith
            have h10 : (M₀ + 3 * M2') ^ 2 + M2' ^ 2 ≤ (M₀ + 4 * M2') ^ 2 := by
              nlinarith [hM0pos, hM2'pos, mul_pos hM0pos hM2'pos]
            linarith [hsq]
          have h := sq_le_sq.mp hmain
          rw [abs_of_nonneg (norm_nonneg ζ),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ M₀ + 4 * M2')] at h
          exact h
        have hRle : M₀ + 4 * M2' + 1 ≤ max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2) :=
          le_max_left _ _
        linarith
      have hn0 : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap F) (-ζ) = 0 := by
        refine Nat.le_zero.mp (Work.Parab.leftCoord.nIdxC_le ?_)
        refine Work.Parab.leftCoord.GoodC.zero ?_
        simp only [Complex.neg_re]
        linarith
      have hpsi : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)
          = Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ) := by
        rw [Work.Parab.leftCoord.PsiC_apply, hn0]
        simp
      have hremζ : ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖ ≤ Kts / (-ζ).re :=
        hrem _ (by simp only [Complex.neg_re]; linarith)
      have hdecomp : Φ ζ - (ζ - (1 - a) * Complex.log (-ζ) - 0)
          = -(Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
              - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)) := by
        simp only [hΦdef, hpsi, Work.FatouCoord.approxCoord_apply]
        ring
      have hden : 0 < (-ζ).re := by simp only [Complex.neg_re]; linarith
      have hrec : Kts / (-ζ).re < ε := by
        by_cases hKts0 : Kts = 0
        · rw [hKts0, zero_div]; exact hε
        · have hKts_pos : 0 < Kts := by
            rcases lt_or_eq_of_le hKtsnn with h | h
            · exact h
            · exact absurd h.symm hKts0
          rw [div_lt_iff₀ hden, Complex.neg_re]
          have hsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have him : |ζ.im| ≤ M2' := not_lt.mp hbig
          have him2 : ζ.im ^ 2 ≤ M2' ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) him 2
          have hRlow : Kts / ε + M2' + 2 ≤ max (M₀ + 4 * M2' + 1) (Kts / ε + M2' + 2) :=
            le_max_right _ _
          have hKε : 0 < Kts / ε := div_pos hKts_pos hε
          have h1 : Kts / ε + M2' < ‖ζ‖ :=
            lt_of_lt_of_le (by linarith : Kts / ε + M2' < Kts / ε + M2' + 2)
              (le_of_lt (lt_of_le_of_lt hRlow hR))
          have hsq2 : (Kts / ε) ^ 2 + M2' ^ 2 < ‖ζ‖ ^ 2 := by
            nlinarith [h1, hKε, hM2'pos]
          have hre2 : (Kts / ε) ^ 2 < ζ.re ^ 2 := by nlinarith [hsq, him2, hsq2]
          have habs1 : Kts / ε < |ζ.re| := by
            have h := sq_lt_sq.mp hre2
            rwa [abs_of_nonneg (le_of_lt hKε)] at h
          have hneg : ζ.re < 0 := by linarith
          rw [abs_of_neg hneg] at habs1
          rw [div_lt_iff₀ hε] at habs1
          nlinarith [habs1]
      rw [hdecomp, norm_neg]
      exact lt_of_le_of_lt hremζ hrec
  obtain ⟨ξ₁, hξ₁pos, himg⟩ := Work.Parab.leftCoordData.image_QLeft (Φ := Φ) (L := L)
    (M₀ := M₀) (M₁ := M₁) (a := 1 - a) hM0pos hM1pos
    (fun ζ hζ => by rw [hLdef]; exact Or.inl hζ) hLim_le
    hΦholo (fun ε hε => by
      obtain ⟨R, hR⟩ := hΦasym ε hε
      exact ⟨R, fun ζ hζ hRζ => by simpa only [sub_zero] using hR ζ hζ hRζ⟩)

  -- ## 6. properness at infinity: far values come from far arguments
  -- The ends half of the argument is the orbit-control estimate: on the bounded part of the ends
  -- the crossing index `nIdxC` is `≤ 2 (N + 3 R) + 2`, and the telescoping bound on the chart
  -- run controls `wMap^[nIdxC] (-ζ)`.
  have hproper : ∀ R : ℝ, ∃ N' : ℝ, ∀ ζ ∈ L, N' < ‖Φ ζ‖ → R < ‖ζ‖ := by
    intro R
    obtain ⟨Ks, hKsnn, hstep⟩ := LF.step
    obtain ⟨nMax, hnMaxdef⟩ : ∃ M : ℝ, M = max (2 * (N + 3 * R) + 2) 0 := ⟨_, rfl⟩
    obtain ⟨logU, hlogUdef⟩ : ∃ M : ℝ, M = max |Real.log M₁| |Real.log R| + Real.pi := ⟨_, rfl⟩
    obtain ⟨logU₀, hlogU₀def⟩ : ∃ M : ℝ, M = max |Real.log M₀| |Real.log R| + Real.pi := ⟨_, rfl⟩
    obtain ⟨Wb, hWbdef⟩ : ∃ M : ℝ, M = R + nMax * (1 + 4 * Ks / M₁) := ⟨_, rfl⟩
    obtain ⟨logW, hlogWdef⟩ : ∃ M : ℝ, M = max |Real.log N| |Real.log Wb| + Real.pi := ⟨_, rfl⟩
    obtain ⟨bndA, hbndAdef⟩ : ∃ M : ℝ, M = Kts / M₀ + R + ‖(1 : ℂ) - (2 - a)‖ * logU₀ := ⟨_, rfl⟩
    obtain ⟨NB, hNBdef⟩ : ∃ M : ℝ,
        M = Kts / N + nMax * (4 * Ks / M₁) + R + ‖(1 : ℂ) - (2 - a)‖ * (logW + 2 * logU) :=
      ⟨_, rfl⟩
    refine ⟨max bndA NB, ?_⟩
    intro ζ hζL hgt
    by_contra hcon
    rw [not_lt] at hcon
    rw [hLdef] at hζL
    have hcaseA : ζ.re < -M₀ → ‖Φ ζ‖ ≤ bndA := by
      intro hleft
      have hure : M₀ < (-ζ).re := by simp only [Complex.neg_re]; linarith
      have huN : N < (-ζ).re := lt_of_le_of_lt hM0N hure
      have hpsi0 : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ)
          = Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ) :=
        Work.Parab.leftCoord.PsiC_eq_of_re (G := Work.FatouCoord.wMap F) (x := -ζ) huN
      have hremζ : ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖ ≤ Kts / (-ζ).re := hrem (-ζ) huN
      have hunorm : ‖(-ζ)‖ ≤ R := by simpa using hcon
      have hlogu : ‖Complex.log (-ζ)‖ ≤ logU₀ := by
        have h1 := Work.Parab.coverCone.norm_log_le_abs_log_add_pi (-ζ)
        have h2 : |Real.log ‖(-ζ)‖| ≤ max |Real.log M₀| |Real.log R| :=
          abs_log_le_max_of_le hM0pos (le_trans (le_of_lt hure) (Complex.re_le_norm (-ζ))) hunorm
        rw [hlogU₀def]
        linarith
      have hPhiζ : Φ ζ = -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ) := by
        simp only [hΦdef]
      have hkey : ‖Φ ζ‖ = ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)‖ := by
        rw [hPhiζ, hpsi0]
        simp
      have hb1 : ‖Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖
          ≤ R + ‖(1 : ℂ) - (2 - a)‖ * logU₀ := by
        rw [Work.FatouCoord.approxCoord_apply]
        calc ‖(-ζ) - (1 - (2 - a)) * Complex.log (-ζ)‖
            ≤ ‖(-ζ)‖ + ‖(1 - (2 - a)) * Complex.log (-ζ)‖ := norm_sub_le _ _
          _ = ‖(-ζ)‖ + ‖(1 - (2 - a))‖ * ‖Complex.log (-ζ)‖ := by rw [norm_mul]
          _ ≤ R + ‖(1 : ℂ) - (2 - a)‖ * logU₀ := by
              have h3 := mul_le_mul_of_nonneg_left hlogu (norm_nonneg ((1 : ℂ) - (2 - a)))
              linarith
      have hdiv : Kts / (-ζ).re ≤ Kts / M₀ :=
        div_le_div_of_nonneg_left hKtsnn hM0pos (le_of_lt hure)
      have htri : ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)‖
          ≤ ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
              - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖
            + ‖Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (-ζ)
            - Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ))
          (Work.FatouCoord.approxCoord (1 - (2 - a)) (-ζ))
      rw [hkey, hbndAdef]
      linarith
    have hcaseB : (-ζ ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) ∧
        M₁ < |ζ.im| ∧ ζ.re < 3 * |ζ.im|) → ‖Φ ζ‖ ≤ NB := by
      rintro ⟨hE, him, hre3⟩
      obtain ⟨u, hudef⟩ : ∃ u : ℂ, u = -ζ := ⟨_, rfl⟩
      have huim : M₁ < |u.im| := by rw [hudef]; simpa using him
      have hure : -3 * |u.im| < u.re := by
        rw [hudef]
        simp only [Complex.neg_re, Complex.neg_im, abs_neg]
        linarith
      have hunorm : ‖u‖ ≤ R := by rw [hudef]; simpa using hcon
      have hEsc : u ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap F) := by
        rw [hudef]; exact hE
      obtain ⟨n, hnJ, hnmin, hn4, -, -⟩ := horb u (lt_of_le_of_lt hM1Mo huim) hure
      have hK4nn : 0 ≤ 4 * Ks / M₁ := div_nonneg (by linarith) (le_of_lt hM1pos)
      have hnN : ∀ k ≤ n, N < ‖((Work.FatouCoord.wMap F)^[k] u)‖ := by
        intro k hk
        have h4 := hn4 k hk
        have h5 : M₁ / 4 < |u.im| / 4 := by linarith
        linarith [hM1_4N]
      have hnormk : ∀ k ≤ n, M₁ / 4 ≤ ‖((Work.FatouCoord.wMap F)^[k] u)‖ := by
        intro k hk
        have h4 := hn4 k hk
        linarith [huim]
      have hGood : Work.Parab.leftCoord.GoodC N (Work.FatouCoord.wMap F) u n := ⟨hnN, hnJ⟩
      have hnIdx : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap F) u ≤ n :=
        Work.Parab.leftCoord.nIdxC_le hGood
      have hgrowth : ∀ k ≤ n, u.re + (k : ℝ) / 2 ≤ ((Work.FatouCoord.wMap F)^[k] u).re := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
            intro hk
            have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
            have hs := (hstep ((Work.FatouCoord.wMap F)^[k] u) (hnN k hk')).2
            rw [Function.iterate_succ_apply']
            push_cast
            linarith [ih hk']
      have hnle : (n : ℝ) ≤ nMax := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero]; rw [hnMaxdef]; exact le_max_right _ _
        · have h1 := hgrowth (n - 1) (by omega)
          have h2 : ((Work.FatouCoord.wMap F)^[n - 1] u).re ≤ N := hnmin (n - 1) (by omega)
          have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (show 1 ≤ n by omega)]
            norm_num
          have h4 : -3 * R < u.re := by
            have h5 : |u.im| ≤ R := le_trans (Complex.abs_im_le_norm u) hunorm
            linarith
          rw [hnMaxdef]
          linarith [le_max_left (2 * (N + 3 * R) + 2) (0 : ℝ)]
      have htel : ∀ k ≤ n, ‖((Work.FatouCoord.wMap F)^[k] u) - (u + (k : ℂ))‖
          ≤ (k : ℝ) * (4 * Ks / M₁) := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
            intro hk
            have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
            have hdec : ((Work.FatouCoord.wMap F)^[k+1] u) - (u + ((k+1 : ℕ) : ℂ))
                = (((Work.FatouCoord.wMap F)^[k+1] u) - (((Work.FatouCoord.wMap F)^[k] u) + 1))
                  + (((Work.FatouCoord.wMap F)^[k] u) - (u + (k : ℂ))) := by
              push_cast; ring
            have hfirst : ‖((Work.FatouCoord.wMap F)^[k+1] u)
                - (((Work.FatouCoord.wMap F)^[k] u) + 1)‖ ≤ 4 * Ks / M₁ := by
              have hs := (hstep ((Work.FatouCoord.wMap F)^[k] u) (hnN k hk')).1
              rw [Function.iterate_succ_apply']
              have h7 : Ks / ‖((Work.FatouCoord.wMap F)^[k] u)‖ ≤ Ks / (M₁ / 4) :=
                div_le_div_of_nonneg_left hKsnn (by linarith) (hnormk k hk')
              have h8 : Ks / (M₁ / 4) = 4 * Ks / M₁ := by field_simp
              linarith [hs, h7, h8.le, h8.ge]
            have hb := ih hk'
            have htri := norm_add_le (((Work.FatouCoord.wMap F)^[k+1] u)
              - (((Work.FatouCoord.wMap F)^[k] u) + 1))
              (((Work.FatouCoord.wMap F)^[k] u) - (u + (k : ℂ)))
            have hcast : (4 * Ks / M₁) + (k : ℝ) * (4 * Ks / M₁)
                = ((k : ℝ) + 1) * (4 * Ks / M₁) := by ring
            rw [hdec]
            push_cast
            linarith [htri, hfirst, hb, hcast]
      have hZ1 : ‖((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ))‖ ≤ nMax * (4 * Ks / M₁) :=
        le_trans (htel n le_rfl) (mul_le_mul_of_nonneg_right hnle hK4nn)
      have hZ2 : ‖((Work.FatouCoord.wMap F)^[n] u)‖ ≤ Wb := by
        have h3 : ‖u + (n : ℂ)‖ ≤ R + (n : ℝ) := by
          have h4 : ‖u + (n : ℂ)‖ ≤ ‖u‖ + ‖((n : ℕ) : ℂ)‖ := norm_add_le _ _
          rw [Complex.norm_natCast] at h4
          linarith
        have h6 : ((Work.FatouCoord.wMap F)^[n] u)
            = (((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ))) + (u + (n : ℂ)) := by ring
        rw [hWbdef]
        have h7 := norm_add_le (((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ))) (u + (n : ℂ))
        have h8 : nMax * (4 * Ks / M₁) + (R + (n : ℝ)) ≤ R + nMax * (1 + 4 * Ks / M₁) := by
          have h9 : nMax * (1 + 4 * Ks / M₁) = nMax + nMax * (4 * Ks / M₁) := by ring
          linarith
        calc ‖((Work.FatouCoord.wMap F)^[n] u)‖
            = ‖(((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ))) + (u + (n : ℂ))‖ :=
              congrArg Norm.norm h6
          _ ≤ nMax * (4 * Ks / M₁) + (R + (n : ℝ)) := by linarith [h7, hZ1, h3]
          _ ≤ R + nMax * (1 + 4 * Ks / M₁) := h8
      have hlogZn : ‖Complex.log (((Work.FatouCoord.wMap F)^[n] u))‖ ≤ logW := by
        have h1 := Work.Parab.coverCone.norm_log_le_abs_log_add_pi (((Work.FatouCoord.wMap F)^[n] u))
        have h2 := abs_log_le_max_of_le LF.pos (le_of_lt (hnN n le_rfl)) hZ2
        rw [hlogWdef]
        linarith
      have hlogu : ‖Complex.log u‖ ≤ logU := by
        have h1 := Work.Parab.coverCone.norm_log_le_abs_log_add_pi u
        have h2 : M₁ ≤ ‖u‖ := le_of_lt (lt_of_lt_of_le huim (Complex.abs_im_le_norm u))
        have h3 := abs_log_le_max_of_le hM1pos h2 hunorm
        rw [hlogUdef]
        linarith
      have hiter : Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          = Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
              (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) u + (n : ℂ) :=
        Work.Parab.leftCoord.psiC_iterate_ge hGN LF.abel hmono hEsc hnIdx
      have hdec : Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
            (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) u
          = (Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
              - Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u)))
            + (Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
              - Work.FatouCoord.approxCoord (1 - (2 - a)) u - (n : ℂ))
            + Work.FatouCoord.approxCoord (1 - (2 - a)) u := by
        rw [hiter]; ring
      have hPsiA : ‖Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))‖
          ≤ Kts / N := by
        have h1 := hrem (((Work.FatouCoord.wMap F)^[n] u)) hnJ
        have h2 : Kts / (((Work.FatouCoord.wMap F)^[n] u)).re ≤ Kts / N :=
          div_le_div_of_nonneg_left hKtsnn LF.pos (le_of_lt hnJ)
        linarith
      have hPsiB : ‖Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          - Work.FatouCoord.approxCoord (1 - (2 - a)) u - (n : ℂ)‖
          ≤ nMax * (4 * Ks / M₁) + ‖(1 : ℂ) - (2 - a)‖ * (logW + logU) := by
        have h3 : ‖Complex.log (((Work.FatouCoord.wMap F)^[n] u)) - Complex.log u‖ ≤ logW + logU :=
          le_trans (norm_sub_le _ _) (by linarith)
        have he : Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
            - Work.FatouCoord.approxCoord (1 - (2 - a)) u - (n : ℂ)
            = (((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ)))
              - (1 - (2 - a)) * (Complex.log (((Work.FatouCoord.wMap F)^[n] u)) - Complex.log u) := by
          rw [Work.FatouCoord.approxCoord_apply, Work.FatouCoord.approxCoord_apply]
          ring
        rw [he]
        have h4 : ‖(1 - (2 - a)) * (Complex.log (((Work.FatouCoord.wMap F)^[n] u)) - Complex.log u)‖
            ≤ ‖(1 : ℂ) - (2 - a)‖ * (logW + logU) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        linarith [norm_sub_le (((Work.FatouCoord.wMap F)^[n] u) - (u + (n : ℂ)))
          ((1 - (2 - a)) * (Complex.log (((Work.FatouCoord.wMap F)^[n] u)) - Complex.log u)),
          hZ1, h4]
      have hPsiCb : ‖Work.FatouCoord.approxCoord (1 - (2 - a)) u‖
          ≤ R + ‖(1 : ℂ) - (2 - a)‖ * logU := by
        rw [Work.FatouCoord.approxCoord_apply]
        calc ‖u - (1 - (2 - a)) * Complex.log u‖
            ≤ ‖u‖ + ‖(1 - (2 - a)) * Complex.log u‖ := norm_sub_le _ _
          _ = ‖u‖ + ‖(1 - (2 - a))‖ * ‖Complex.log u‖ := by rw [norm_mul]
          _ ≤ R + ‖(1 : ℂ) - (2 - a)‖ * logU := by
              have h3 := mul_le_mul_of_nonneg_left hlogu (norm_nonneg ((1 : ℂ) - (2 - a)))
              linarith
      have hPhiζ : Φ ζ = -Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) (-ζ) := by
        simp only [hΦdef]
      have hkey : ‖Φ ζ‖ = ‖Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap F)
          (Work.FatouCoord.fatouCoordW F (1 - (2 - a))) u‖ := by
        rw [hPhiζ, hudef]
        simp
      rw [hkey]
      have htri1 := norm_add_le
        ((Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u)))
          + (Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
            - Work.FatouCoord.approxCoord (1 - (2 - a)) u - (n : ℂ)))
        (Work.FatouCoord.approxCoord (1 - (2 - a)) u)
      have htri2 := norm_add_le
        (Work.FatouCoord.fatouCoordW F (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          - Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u)))
        (Work.FatouCoord.approxCoord (1 - (2 - a)) (((Work.FatouCoord.wMap F)^[n] u))
          - Work.FatouCoord.approxCoord (1 - (2 - a)) u - (n : ℂ))
      rw [hdec]
      rw [hNBdef]
      linarith [htri1, htri2, hPsiA, hPsiB, hPsiCb]
    rcases hζL with hL | hL
    · linarith [hcaseA hL, le_max_left bndA NB]
    · linarith [hcaseB hL, le_max_right bndA NB]
  refine ⟨⟨Φ, L, M₀, M₁, ξ₁, 1 - a, 0, hM0pos, hM1pos, hξ₁pos, hLopen,
    (fun ζ hζ => by rw [hLdef]; exact Or.inl hζ), hLim_le, hΦholo, hΦabel, hΦinj, hΦasym,
    himg⟩, h, a, r, A, A', hb, rfl, hproper⟩

end

end Work.Parab.coordData
