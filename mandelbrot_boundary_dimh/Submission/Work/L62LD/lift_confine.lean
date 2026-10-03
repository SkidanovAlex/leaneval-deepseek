import Mathlib
import Submission.Work.L62LD.setup

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

namespace LiftAux

/-! ## Auxiliary facts about `qlow` and the `1`-periodic drift `d.E - id`

These are the two mechanisms of the confinement: the cylinder coordinate `qlow` identifies
points modulo `ℤ`, so its preimage of a compactum of `lowOmega` avoiding the puncture lies in
the `ℤ`-invariant horn `hd.Bl`; and the drift `g w = d.E w - w` is `ℤ`-periodic on `hd.Bl`, so it
is bounded on that preimage. -/

/-- `qlow a = qlow b` iff `a - b` is an integer. -/
theorem qlow_eq_iff_exists_int (a b : ℂ) :
    Work.L62.qlow a = Work.L62.qlow b ↔ ∃ k : ℤ, a = b + (k : ℂ) := by
  constructor
  · intro h
    have h2 : MandelDim.piExp a = MandelDim.piExp b := by
      have h3 : MandelDim.tau0 (MandelDim.piExp a) = MandelDim.tau0 (MandelDim.piExp b) := by
        simpa only [Work.L62.qlow_eq_tau0] using h
      have h4 := congrArg MandelDim.tau0 h3
      rwa [Work.L62.tau0_invol (MandelDim.piExp a) (Work.Horn.MandelDim.piExp_ne_zero a),
        Work.L62.tau0_invol (MandelDim.piExp b) (Work.Horn.MandelDim.piExp_ne_zero b)] at h4
    exact (Work.L62.piExp_eq_iff_exists_int a b).mp h2
  · rintro ⟨k, rfl⟩
    exact Work.L62.qlow_add_int b k

/-- **The `qlow`-preimage of a compactum of `lowOmega` avoiding the puncture lies in `hd.Bl`.**
Indeed `lowOmega ∖ {0} = qlow '' hd.Bl` and `hd.Bl` is `ℤ`-invariant. -/
theorem qlow_preimage_subset_Bl {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {K_cyl : Set ℂ} (hK : K_cyl ⊆ Work.L62.lowOmega d hd) (hK0 : ∀ ζ ∈ K_cyl, ζ ≠ 0) :
    {w : ℂ | Work.L62.qlow w ∈ K_cyl} ⊆ hd.Bl := by
  intro w hw
  have hmem : Work.L62.qlow w ∈ Work.L62.lowOmega d hd := hK hw
  rw [Work.L62.lowOmega_eq_image_qlow] at hmem
  rcases hmem with h0 | ⟨w'', hw'', hq⟩
  · exact absurd h0 (hK0 _ hw)
  · obtain ⟨k, hk⟩ := (qlow_eq_iff_exists_int w'' w).mp hq
    have hwk : w = w'' + ((-k : ℤ) : ℂ) := by
      rw [hk]; push_cast; ring
    rw [hwk]
    exact (Work.L62.IsTInvariant.mem_add_int hd.Bl_T w'' (-k)).mp hw''

/-- `d.E` is holomorphic on the lower horn. -/
theorem differentiableOn_E_Bl' (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) :
    DifferentiableOn ℂ d.E hd.Bl :=
  d.Φ_holo.comp (d.φ_holo.mono fun _ hw => (hd.sub (Or.inr hw)).1)
    fun _ hw => (hd.sub (Or.inr hw)).2

theorem E_sub_id_add_nat {d : MandelDim.ParabData g₀ D} (hd : MandelDim.HornData d)
    {w : ℂ} (hw : w ∈ hd.Bl) (n : ℕ) :
    d.E (w + (n : ℂ)) - (w + (n : ℂ)) = d.E w - w := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w + (m : ℂ) ∈ hd.Bl := (Work.L62.IsTInvariant.mem_add_int hd.Bl_T w m).mp hw
      have hcast : w + ((m + 1 : ℕ) : ℂ) = (w + (m : ℂ)) + 1 := by push_cast; ring
      have hkey : d.E (w + (m : ℂ)) + 1 - ((w + (m : ℂ)) + 1) = d.E (w + (m : ℂ)) - (w + (m : ℂ)) := by
        ring
      rw [hcast, Work.L62.E_add_one_Bl d hd hmem, hkey]
      exact ih

theorem E_sub_id_sub_nat {d : MandelDim.ParabData g₀ D} (hd : MandelDim.HornData d)
    {w : ℂ} (hw : w ∈ hd.Bl) (n : ℕ) :
    d.E (w - (n : ℂ)) - (w - (n : ℂ)) = d.E w - w := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w - (m : ℂ) ∈ hd.Bl := by
        have h := (Work.L62.IsTInvariant.mem_add_int hd.Bl_T w (-(m : ℤ))).mp hw
        have h2 : w + ((↑(-(m : ℤ)) : ℂ)) = w - (m : ℂ) := by push_cast; ring
        rwa [h2] at h
      have hmem1 : w - (m : ℂ) - 1 ∈ hd.Bl := by
        refine (hd.Bl_T (w - (m : ℂ) - 1)).mpr ?_
        rw [show w - (m : ℂ) - 1 + 1 = w - (m : ℂ) by ring]
        exact hmem
      have hstep : d.E (w - (m : ℂ) - 1) - (w - (m : ℂ) - 1) = d.E (w - (m : ℂ)) - (w - (m : ℂ)) := by
        have h := Work.L62.E_add_one_Bl d hd hmem1
        rw [show w - (m : ℂ) - 1 + 1 = w - (m : ℂ) by ring] at h
        rw [h]; ring
      have hcast : w - ((m + 1 : ℕ) : ℂ) = w - (m : ℂ) - 1 := by push_cast; ring
      rw [hcast, hstep, ih]

/-- The drift `g w = d.E w - w` is invariant under all integer shifts of a point of `hd.Bl`. -/
theorem E_sub_id_add_int {d : MandelDim.ParabData g₀ D} (hd : MandelDim.HornData d)
    {w : ℂ} (hw : w ∈ hd.Bl) (k : ℤ) :
    d.E (w + (k : ℂ)) - (w + (k : ℂ)) = d.E w - w := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k).toNat - 1, by omega⟩
    subst hn
    have hcast : w + ((-((n : ℤ) + 1) : ℤ) : ℂ) = w - ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, E_sub_id_sub_nat hd hw (n + 1)]
  · subst hk; simp
  · obtain ⟨n, hnk⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hk)
    subst hnk
    simpa using E_sub_id_add_nat hd hw n

/-- **The drift `g w = d.E w - w` is bounded on the `qlow`-preimage of a compactum avoiding
`0`.**  `g` is `1`-periodic, hence on the `qlow`-preimage of a compactum it suffices to control
`g` on the compact fundamental window `{0 ≤ Re ≤ 1, K_cyl ∋ qlow}`. -/
theorem exists_bound_g {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d}
    {K_cyl : Set ℂ} (hKc : IsCompact K_cyl) (hK : K_cyl ⊆ Work.L62.lowOmega d hd)
    (hK0 : ∀ ζ ∈ K_cyl, ζ ≠ 0) :
    ∃ Cg : ℝ, ∀ w : ℂ, Work.L62.qlow w ∈ K_cyl → ‖d.E w - w‖ ≤ Cg := by
  have hqlow_cont : Continuous (fun w : ℂ => Work.L62.qlow w) := by
    unfold Work.L62.qlow Work.L62.flip MandelDim.piExp; fun_prop
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ K_cyl, δ ≤ ‖ζ‖ := by
    rcases Set.eq_empty_or_nonempty K_cyl with hemp | hne
    · exact ⟨1, one_pos, fun ζ hζ => absurd (hemp ▸ hζ) (Set.notMem_empty ζ)⟩
    · obtain ⟨ζ₀, hζ₀, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      exact ⟨‖ζ₀‖, norm_pos_iff.mpr (hK0 ζ₀ hζ₀), fun ζ hζ => (isMinOn_iff.mp hmin) ζ hζ⟩
  obtain ⟨M, hM⟩ := hKc.isBounded.exists_norm_le
  have hMη : ∀ w : ℂ, Work.L62.qlow w ∈ K_cyl → Real.exp (2 * Real.pi * w.im) ≤ M := by
    intro w hw
    rw [← Work.L62.norm_qlow w]
    exact hM _ hw
  set Rw : Set ℂ := {w : ℂ | Work.L62.qlow w ∈ K_cyl} ∩ {w : ℂ | 0 ≤ w.re} ∩
    {w : ℂ | w.re ≤ 1} with hRwdef
  have hRwsub : Rw ⊆ hd.Bl := fun w hw => qlow_preimage_subset_Bl hK hK0 hw.1.1
  have hRwclosed : IsClosed Rw := by
    rw [hRwdef]
    exact ((hKc.isClosed.preimage hqlow_cont).inter
      (isClosed_le continuous_const Complex.continuous_re)).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hRwbdd : Bornology.IsBounded Rw := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := 1 + |Real.log M / (2 * Real.pi)| + |Real.log δ / (2 * Real.pi)|)) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have him_up : w.im ≤ Real.log M / (2 * Real.pi) := by
      have h1 : Real.exp (2 * Real.pi * w.im) ≤ M := hMη w hw.1.1
      have h2 : 2 * Real.pi * w.im ≤ Real.log M := by
        have := Real.log_le_log (Real.exp_pos _) h1
        rwa [Real.log_exp] at this
      have h3 : w.im = (2 * Real.pi * w.im) / (2 * Real.pi) := by field_simp
      rw [h3]
      exact div_le_div_of_nonneg_right h2 h2π.le
    have him_low : Real.log δ / (2 * Real.pi) ≤ w.im := by
      have h1 : δ ≤ Real.exp (2 * Real.pi * w.im) := by
        rw [← Work.L62.norm_qlow w]; exact hδ _ hw.1.1
      have h2 : Real.log δ ≤ 2 * Real.pi * w.im := by
        have := Real.log_le_log hδpos h1
        rwa [Real.log_exp] at this
      exact (div_le_iff₀ h2π).mpr (by linarith)
    have him_abs : |w.im| ≤ |Real.log M / (2 * Real.pi)| + |Real.log δ / (2 * Real.pi)| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : -(Real.log δ / (2 * Real.pi)) ≤ |Real.log δ / (2 * Real.pi)| := neg_le_abs _
        have h2 : (0 : ℝ) ≤ |Real.log M / (2 * Real.pi)| := abs_nonneg _
        linarith [him_low]
      · have h1 : Real.log M / (2 * Real.pi) ≤ |Real.log M / (2 * Real.pi)| := le_abs_self _
        have h2 : (0 : ℝ) ≤ |Real.log δ / (2 * Real.pi)| := abs_nonneg _
        linarith [him_up]
    have hre : 0 ≤ w.re ∧ w.re ≤ 1 := ⟨hw.1.2, hw.2⟩
    have hnorm : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    have hreabs : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith [hre.1], hre.2⟩
    linarith [hnorm, him_abs, hreabs, abs_nonneg (Real.log M / (2 * Real.pi)),
      abs_nonneg (Real.log δ / (2 * Real.pi))]
  have hRwc : IsCompact Rw := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hRwclosed, hRwbdd⟩
  have hgcont : ContinuousOn (fun w => d.E w - w) Rw :=
    (((differentiableOn_E_Bl' d hd).sub differentiableOn_id).continuousOn).mono hRwsub
  obtain ⟨Cg, hCg⟩ := hRwc.exists_bound_of_continuousOn hgcont
  refine ⟨Cg, fun w hw => ?_⟩
  set k : ℤ := Int.floor w.re with hkdef
  set w' : ℂ := w - (k : ℂ) with hw'def
  have hre' : w'.re = w.re - (k : ℝ) := by
    simp only [hw'def, Complex.sub_re, Complex.ofReal_re, Complex.intCast_re]
  have hw're : 0 ≤ w'.re ∧ w'.re ≤ 1 := by
    constructor
    · have := Int.floor_le w.re; linarith
    · have := Int.lt_floor_add_one w.re; linarith
  have hshift : w' + (k : ℂ) = w := by rw [hw'def]; ring
  have hqw' : Work.L62.qlow w' = Work.L62.qlow w := by
    rw [← Work.L62.qlow_add_int w' k, hshift]
  have hmem' : w' ∈ Rw := by
    refine ⟨⟨?_, hw're.1⟩, hw're.2⟩
    show Work.L62.qlow w' ∈ K_cyl
    rw [hqw']; exact hw
  have hper : d.E w - w = d.E w' - w' := by
    have h1 := E_sub_id_add_int hd (hRwsub hmem') k
    rw [hshift] at h1
    exact h1
  rw [hper]
  exact hCg w' hmem'

end LiftAux

/-! ## The `K`-clause -/

theorem lift_confine {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ}
    {b : ℝ} {Λ : Set ℂ} (hΛ : Λ ⊆ Work.L62LD.downBox d hd b)
    {σ : ℂ → ℂ → ℂ} {H : ℂ → ℂ → ℂ}
    (hσsec : ∀ β ∈ Λ, ∀ y ∈ hd.Bl, d.E (σ β y) - β = y)
    (hσmem : ∀ β ∈ Λ, ∀ y ∈ hd.Bl, σ β y ∈ hd.Bl)
    (hlink : ∀ β ∈ Λ, ∀ w ∈ hd.Bl, H β (Work.L62.qlow w) = Work.L62.qlow (σ β w))
    {K₁ : Set ℂ} (hK₁c : IsCompact K₁) (hK₁Bl : K₁ ⊆ hd.Bl)
    {K_cyl : Set ℂ} (hK_cyl_c : IsCompact K_cyl) (hK_cylΩ : K_cyl ⊆ Work.L62.lowOmega d hd)
    (hK_cyl0 : ∀ ζ ∈ K_cyl, ζ ≠ 0)
    {J : ℕ} {W₁ : ℂ → Set ℂ} (hW₁K : ∀ β ∈ Λ, W₁ β ⊆ K₁)
    (hconfl : ∀ β ∈ Λ, ∀ j ≤ J, (H β)^[j] '' (Work.L62.qlow '' W₁ β) ⊆ K_cyl) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ hd.Bl ∧
      ∀ β ∈ Λ, ∀ j ≤ J, ((σ β)^[j]) '' W₁ β ⊆ K := by
  obtain ⟨Cg₀, hCg₀⟩ := LiftAux.exists_bound_g hK_cyl_c hK_cylΩ hK_cyl0
  set Cg : ℝ := max Cg₀ 0 with hCgdef
  have hCg0 : 0 ≤ Cg := le_max_right _ _
  have hCg : ∀ w : ℂ, Work.L62.qlow w ∈ K_cyl → ‖d.E w - w‖ ≤ Cg :=
    fun w hw => le_trans (hCg₀ w hw) (le_max_left _ _)
  set Mβ : ℝ := 1 + |b| with hMβdef
  have hMβ0 : 0 ≤ Mβ := by rw [hMβdef]; positivity
  have hMC : 0 ≤ Mβ + Cg := by linarith
  have hβnorm : ∀ β ∈ Λ, ‖β‖ ≤ Mβ := by
    intro β hβ
    have hdb := hΛ hβ
    simp only [downBox, Set.mem_inter_iff, Set.mem_setOf_eq] at hdb
    obtain ⟨⟨hre0, hre1, him⟩, _⟩ := hdb
    have hb0 : 0 ≤ b := le_trans (abs_nonneg β.im) him
    have hreabs : |β.re| ≤ 1 := by rw [abs_of_nonneg hre0]; exact hre1
    calc ‖β‖ ≤ |β.re| + |β.im| := Complex.norm_le_abs_re_add_abs_im β
      _ ≤ 1 + b := by linarith
      _ = Mβ := by rw [hMβdef, abs_of_nonneg hb0]
  obtain ⟨M₁, hM₁⟩ := hK₁c.isBounded.exists_norm_le
  set Rr : ℝ := M₁ + (J : ℝ) * (Mβ + Cg) with hRrdef
  -- the iterates stay in the lower horn
  have hiterBl : ∀ β ∈ Λ, ∀ y ∈ W₁ β, ∀ j : ℕ, (σ β)^[j] y ∈ hd.Bl := by
    intro β hβ y hy j
    induction j with
    | zero => simpa using hK₁Bl (hW₁K β hβ hy)
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hσmem β hβ _ ih
  -- `qlow` of the iterate is the cylinder iterate
  have hkey : ∀ β ∈ Λ, ∀ y ∈ W₁ β, ∀ j : ℕ,
      Work.L62.qlow ((σ β)^[j] y) = (H β)^[j] (Work.L62.qlow y) := by
    intro β hβ y hy j
    induction j with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rw [← hlink β hβ ((σ β)^[m] y) (hiterBl β hβ y hy m), ih]
        rw [Function.iterate_succ_apply']
  -- which therefore stays in the fixed compactum `K_cyl`
  have hcylpt : ∀ β ∈ Λ, ∀ y ∈ W₁ β, ∀ j ≤ J,
      Work.L62.qlow ((σ β)^[j] y) ∈ K_cyl := by
    intro β hβ y hy j hj
    rw [hkey β hβ y hy j]
    exact hconfl β hβ j hj ⟨Work.L62.qlow y, ⟨y, hy, rfl⟩, rfl⟩
  -- the drift bounds the norm of the iterates
  have hnorm_pt : ∀ j ≤ J, ∀ β ∈ Λ, ∀ y ∈ W₁ β,
      ‖(σ β)^[j] y‖ ≤ M₁ + (j : ℝ) * (Mβ + Cg) := by
    intro j
    induction j with
    | zero =>
        intro _ β hβ y hy
        simpa using hM₁ y (hW₁K β hβ hy)
    | succ m ih =>
        intro hm β hβ y hy
        have hmle : m ≤ J := Nat.le_of_succ_le hm
        have hiter_eq : (σ β)^[m + 1] y = σ β ((σ β)^[m] y) := Function.iterate_succ_apply' _ _ _
        rw [hiter_eq]
        have hu : (σ β)^[m] y ∈ hd.Bl := hiterBl β hβ y hy m
        have hsec := hσsec β hβ ((σ β)^[m] y) hu
        have hEu : d.E (σ β ((σ β)^[m] y)) = (σ β)^[m] y + β :=
          (sub_eq_iff_eq_add).mp hsec
        have hdecomp : σ β ((σ β)^[m] y)
            = (σ β)^[m] y + β - (d.E (σ β ((σ β)^[m] y)) - σ β ((σ β)^[m] y)) := by
          rw [hEu]; ring
        have hqlow : Work.L62.qlow (σ β ((σ β)^[m] y)) ∈ K_cyl := by
          have hthis := hcylpt β hβ y hy (m + 1) hm
          rwa [hiter_eq] at hthis
        have hg := hCg (σ β ((σ β)^[m] y)) hqlow
        have hih := ih hmle β hβ y hy
        have hβn := hβnorm β hβ
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have hb1 : ‖σ β ((σ β)^[m] y)‖ ≤ M₁ + ((m : ℝ) + 1) * (Mβ + Cg) := by
          have hdecomp_norm : ‖σ β ((σ β)^[m] y)‖
              = ‖(σ β)^[m] y + β
                  - (d.E (σ β ((σ β)^[m] y)) - σ β ((σ β)^[m] y))‖ :=
            congrArg (fun z => ‖z‖) hdecomp
          calc ‖σ β ((σ β)^[m] y)‖
              = ‖(σ β)^[m] y + β
                  - (d.E (σ β ((σ β)^[m] y)) - σ β ((σ β)^[m] y))‖ := hdecomp_norm
            _ ≤ ‖(σ β)^[m] y + β‖
                  + ‖d.E (σ β ((σ β)^[m] y)) - σ β ((σ β)^[m] y)‖ := norm_sub_le _ _
            _ ≤ (‖(σ β)^[m] y‖ + ‖β‖) + Cg := add_le_add (norm_add_le _ _) hg
            _ ≤ (M₁ + (m : ℝ) * (Mβ + Cg)) + Mβ + Cg := by linarith
            _ = M₁ + ((m : ℝ) + 1) * (Mβ + Cg) := by ring
        rw [hcast]
        exact hb1
  refine ⟨{w : ℂ | Work.L62.qlow w ∈ K_cyl} ∩ Metric.closedBall 0 Rr, ?_, ?_, ?_⟩
  · have hqlow_cont : Continuous (fun w : ℂ => Work.L62.qlow w) := by
      unfold Work.L62.qlow Work.L62.flip MandelDim.piExp; fun_prop
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact (hK_cyl_c.isClosed.preimage hqlow_cont).inter Metric.isClosed_closedBall
    · exact Metric.isBounded_closedBall.subset Set.inter_subset_right
  · intro w hw
    exact LiftAux.qlow_preimage_subset_Bl hK_cylΩ hK_cyl0 hw.1
  · intro β hβ j hj x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨hcylpt β hβ y hy j hj, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (hnorm_pt j hj β hβ y hy) ?_
    have hmul : (j : ℝ) * (Mβ + Cg) ≤ (J : ℝ) * (Mβ + Cg) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hMC
    rw [hRrdef]
    linarith

end

end Work.L62LD
