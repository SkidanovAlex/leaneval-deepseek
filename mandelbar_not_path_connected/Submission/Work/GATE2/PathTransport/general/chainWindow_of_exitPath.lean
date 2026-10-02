import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.PathTransport.dev_transport
import Submission.Work.GATE2.PathTransport.mem_critDomain_iterate
import Submission.Work.GATE2.PathTransport.continuousAt_deviation_fixed
import Submission.Work.GATE2.varphiCrit_F_iterate
import Submission.Work.GATE2.PathTransport.angle_F_iterate
import Submission.Work.GATE2.PathTransport.angle_torsion_const
import Submission.Work.GATE2.phase_gap_integrality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

namespace Work.GATE2.PathTransport.general

noncomputable section

/-! ## Auxiliary lemmas for `Work.GATE2.PathTransport.general.chainWindow_of_exitPath`

This file is the general-root-angle form of
`Submission/Work/GATE2/PathTransport/chainWindow_of_exitPath.lean`
(namespace `Work.GATE2.PathTransport`): the root-angle hypothesis `1023 * α = 371` is replaced by
`∃ s : ℤ, 1023 * α = (s : ℝ)`, which covers both root angles `α₁` (`1023 α₁ = 371`) and `α₂`
(`1023 α₂ = 404`) of the design.  Everything else, including every numeric bound, is verbatim.

The only arithmetic use of `371` in the `371` file is through
`Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul` (the integrality `(1024^j − 1) α ∈ ℤ`), used to
show that the twist `(1024^j) • (2πα)` is trivial in `Real.Angle` (and hence the `1024`-fold angle
equation along the high iterate).  Both are generalized here:
`exists_int_pow_sub_one_mul_general`, `nsmul_two_pi_alpha_general` and `angle_F_iterate_general`.

All other helpers (`coe_two_pi_deviation`, `nsmul_coe_two_pi_div`, `G`, `angle_torsion_const`,
`mem_critDomain_iterate`, `varphiCrit_F_iterate`, `continuousAt_deviation_fixed`,
`deviation_mem`) are `α`-agnostic and are copied verbatim from the `371` file. -/

/-- **Integrality of the root-angle twist, general root angle.**  If `1023 α` is an integer, then
so is `(1024^m − 1) α`, because `1023 ∣ 1024^m − 1` (`1024 ≡ 1` modulo `1023`). -/
theorem exists_int_pow_sub_one_mul_general {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ))
    (m : ℕ) : ∃ t : ℤ, ((((1024 ^ m : ℕ) : ℝ)) - 1) * α = (t : ℝ) := by
  obtain ⟨s, hs⟩ := hα
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1024 : ℤ) 1 m
  have hq' : (1024 : ℤ) ^ m - 1 = 1023 * q := by simpa using hq
  have hqR : (1024 : ℝ) ^ m - 1 = 1023 * (q : ℝ) := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) hq'
    push_cast at h
    simpa using h
  have hcast : (((1024 ^ m : ℕ) : ℝ)) = (1024 : ℝ) ^ m := by push_cast; ring
  refine ⟨q * s, ?_⟩
  rw [hcast, hqR]
  rw [show (1023 : ℝ) * (q : ℝ) * α = (q : ℝ) * (1023 * α) by ring, hs]
  push_cast
  ring

/-- **The twist of the root angle is trivial under the `1024`-fold iteration, general root
angle.**  For `1023 α ∈ ℤ` the angle `2π α` is fixed by the `1024^j`-fold multiple:
`(1024^j) • (2π α : Real.Angle) = (2π α : Real.Angle)`. -/
theorem nsmul_two_pi_alpha_general {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ)) (j : ℕ) :
    (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle) = ((2 * Real.pi * α : ℝ) : Real.Angle) := by
  obtain ⟨t, ht⟩ := exists_int_pow_sub_one_mul_general hα j
  rw [← Real.Angle.natCast_mul_eq_nsmul]
  refine (Real.Angle.angle_eq_iff_two_pi_dvd_sub
    (θ := (((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) (ψ := 2 * Real.pi * α)).mpr ⟨t, ?_⟩
  have hmain : ((((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) - (2 * Real.pi * α)
      = 2 * Real.pi * (t : ℝ) := by
    rw [show ((((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) - (2 * Real.pi * α)
        = 2 * Real.pi * (((((1024 ^ j : ℕ) : ℝ)) - 1) * α) by ring, ht]
  exact hmain

/-- **The `1024`-fold angle equation along the high iterate, general root angle**
(item (A1) of the design).  For a point `z` of the critical domain of `c`, the `α`-relative
Böttcher angle `A z := (arg (φ_c z) : Real.Angle) − (2π α : Real.Angle)` is multiplied by `1024^j`
under `(F_c)^[j]`, provided `1023 α ∈ ℤ`. -/
theorem angle_F_iterate_general {c z : ℂ} {α : ℝ} (hz : z ∈ Work.ParamRays.critDomain c)
    (hα : ∃ s : ℤ, 1023 * α = (s : ℝ)) (j : ℕ) :
    (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)
      = (1024 ^ j) • ((Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)) := by
  have hpow : (Work.Bottcher.varphiCrit c z) ^ (1024 ^ j)
      = Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z) :=
    Work.GATE2.varphiCrit_F_iterate hz j
  have hang : (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
      = (1024 ^ j) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle) := by
    rw [← hpow]
    exact Complex.arg_pow_coe_angle _ _
  rw [hang, nsmul_sub, nsmul_two_pi_alpha_general hα j]

/-- The geometric weight `G n = 1 + 1/1024 + … + (1/1024)^(n-1)`, in recursive form. -/
private noncomputable def G : ℕ → ℝ
  | 0 => 0
  | n + 1 => G n + (1 / 1024 : ℝ) ^ n

private theorem G_eq (n : ℕ) : G n = 1024 / 1023 * (1 - (1 / 1024 : ℝ) ^ n) := by
  induction n with
  | zero => rw [G]; norm_num
  | succ n ih => rw [G, ih, pow_succ]; ring

/-- The geometric weight is at most the sum of the full geometric series. -/
private theorem G_le (n : ℕ) : G n ≤ 1024 / 1023 := by
  rw [G_eq n]
  have h : (1 / 1024 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ (1 / 1024 : ℝ) ^ n := pow_nonneg (by norm_num) n
  nlinarith

private theorem G_zero : G 0 = 0 := by rw [G]

private theorem G_succ (n : ℕ) : G (n + 1) = G n + (1 / 1024 : ℝ) ^ n := by rw [G]

/-- **The angle of a Böttcher value versus its `α`-deviation.**  The `Real.Angle`-valued
Böttcher argument relative to the direction `α` is the image of `2π` times the deviation. -/
private theorem coe_two_pi_deviation (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    (((2 * Real.pi * Work.GATE.deviation φ α z : ℝ)) : Real.Angle)
      = (Complex.arg (φ z) : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle) := by
  rw [Work.GATE2.deviation_eq_devOfValue, Work.GATE2.devOfValue]
  have h : (2 * Real.pi) * (((Complex.arg (φ z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal / (2 * Real.pi))
      = ((Complex.arg (φ z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)).toReal := by
    field_simp
  rw [h, Real.Angle.coe_toReal]

/-- The `1024^j`-fold multiple of the angle of a divided deviation is the angle of the
undivided one. -/
private theorem nsmul_coe_two_pi_div (D : ℝ) (j : ℕ) :
    (1024 ^ j) • (((2 * Real.pi * D / (1024 : ℝ) ^ j : ℝ)) : Real.Angle)
      = (((2 * Real.pi * D : ℝ)) : Real.Angle) := by
  rw [← Real.Angle.natCast_mul_eq_nsmul]
  congr 1
  push_cast
  field_simp

/-- Extraction of an integer from the vanishing of the class of a real number. -/
private theorem exists_int_sub_of_coe_eq_zero {β : ℝ} (h : ((β : ℝ) : Real.Angle) = 0) :
    ∃ N : ℤ, β / (2 * Real.pi) = (N : ℝ) := by
  obtain ⟨m, hm⟩ := Real.Angle.coe_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  rw [zsmul_eq_mul] at hm
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-- The iterate of a map equals the iterate of its predecessor applied to the map. -/
private theorem iterate_sub_one_apply {f : ℂ → ℂ} {n : ℕ} {x : ℂ} (hn : 1 ≤ n) :
    f^[n] x = f^[n - 1] (f x) := by
  conv_lhs => rw [← Nat.sub_add_cancel hn]
  exact Function.iterate_succ_apply f (n - 1) x

/-- **Transport of the deviation along a path in the chart** (the design's (A4)), with the
critical-domain membership of the `j`-th image assumed explicitly. -/
private theorem dev_transport_aux {e : ℂ} {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ))
    (γ : C(unitInterval, ℂ)) (j : ℕ)
    (hdom : ∀ t : unitInterval, γ t ∈ Work.ParamRays.critDomain e)
    (hdomj : ∀ t : unitInterval, (Work.EL.F e)^[j] (γ t) ∈ Work.ParamRays.critDomain e)
    (hsmall : ∀ t : unitInterval, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
      ((Work.EL.F e)^[j] (γ t))| < 1 / 4) :
    ∃ N : ℤ, Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1) -
        Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
      = (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 1))
          - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 0)))
        / (1024 : ℝ) ^ j + (N : ℝ) := by
  have hnpos : (0 : ℝ) < (1024 : ℝ) ^ j := pow_pos (by norm_num) j
  -- continuity of the `Real.Angle`-valued Böttcher argument along `γ`
  have hAcont : Continuous (fun t : unitInterval =>
      (Complex.arg (Work.Bottcher.varphiCrit e (γ t)) : Real.Angle)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (Real.Angle.coe ∘ Complex.arg)
        (Work.Bottcher.varphiCrit e (γ t)) :=
      Complex.continuousAt_arg_coe_angle (Work.Bottcher.varphiCrit_ne_zero (hdom t))
    have h2 : ContinuousAt (Work.Bottcher.varphiCrit e) (γ t) :=
      (Work.Bottcher.varphiCrit_continuousOn e).continuousAt
        ((Work.ParamRays.isOpen_critDomain e).mem_nhds (hdom t))
    have h3 : ContinuousAt ((Real.Angle.coe ∘ Complex.arg) ∘ Work.Bottcher.varphiCrit e)
        (γ t) := h1.comp h2
    have h4 : ContinuousAt (((Real.Angle.coe ∘ Complex.arg) ∘ Work.Bottcher.varphiCrit e) ∘ γ) t :=
      h3.comp γ.continuous.continuousAt
    simpa only [Function.comp_def] using h4
  have hFcont : Continuous (Work.EL.F e) := by
    show Continuous ((Work.Landing.Tsq e)^[5])
    exact (Work.ELNest.continuous_tsq e).iterate 5
  have hγjc : Continuous (fun t : unitInterval => (Work.EL.F e)^[j] (γ t)) :=
    (hFcont.iterate j).comp γ.continuous
  have hDcont : Continuous (fun t : unitInterval =>
      Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (x := t)
      (f := fun t : unitInterval => (Work.EL.F e)^[j] (γ t))
      (continuousAt_deviation_fixed (hdomj t) (hsmall t)) hγjc.continuousAt
  -- the `Real.Angle`-valued comparison function
  let R : unitInterval → Real.Angle := fun t =>
    ((Complex.arg (Work.Bottcher.varphiCrit e (γ t)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle))
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ t)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle)
  have hRcont : Continuous R := by
    refine Continuous.sub (hAcont.sub continuous_const) ?_
    exact Real.Angle.continuous_coe.comp ((hDcont.const_mul (2 * Real.pi)).div_const _)
  have htors : ∀ t : unitInterval, (1024 ^ j) • R t = 0 := by
    intro t
    show (1024 ^ j) • (((Complex.arg (Work.Bottcher.varphiCrit e (γ t)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle))
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ t)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle)) = 0
    rw [nsmul_sub, ← angle_F_iterate_general (hdom t) hα j, nsmul_coe_two_pi_div,
      ← coe_two_pi_deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ t))]
    simp
  have hR01 : R 0 = R 1 := by
    have hh := angle_torsion_const (N := 1024 ^ j) (by positivity : 0 < 1024 ^ j)
      (f := ⟨R, hRcont⟩) (fun t => htors t)
    simpa using hh
  -- rewrite the endpoints through the deviation
  have hb0 : R 0 = (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        : ℝ)) : Real.Angle)
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 0)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) := by
    show ((Complex.arg (Work.Bottcher.varphiCrit e (γ 0)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle))
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 0)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) = _
    rw [← coe_two_pi_deviation (Work.Bottcher.varphiCrit e) α (γ 0)]
  have hb1 : R 1 = (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
        : ℝ)) : Real.Angle)
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 1)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) := by
    show ((Complex.arg (Work.Bottcher.varphiCrit e (γ 1)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle))
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 1)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) = _
    rw [← coe_two_pi_deviation (Work.Bottcher.varphiCrit e) α (γ 1)]
  have heq : (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        : ℝ)) : Real.Angle)
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 0)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle)
      = (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
        : ℝ)) : Real.Angle)
      - (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 1)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) := by
    rw [← hb0, ← hb1]
    exact hR01
  have h1 : (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        - 2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 0)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle)
      = (((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
        - 2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 1)) / (1024 : ℝ) ^ j : ℝ)) : Real.Angle) := by
    simpa only [← Real.Angle.coe_sub] using heq
  have h2 : ((((2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        - 2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 0)) / (1024 : ℝ) ^ j)
      - (2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
        - 2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ 1)) / (1024 : ℝ) ^ j) : ℝ)) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, sub_eq_zero]
    exact h1
  obtain ⟨mm, hmm⟩ := exists_int_sub_of_coe_eq_zero h2
  have hmm' : (mm : ℝ) = (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1))
      - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 0))
        - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 1)))
        / (1024 : ℝ) ^ j := by
    rw [← hmm]
    have hn : ((1024 : ℝ) ^ j) ≠ 0 := ne_of_gt hnpos
    field_simp
    ring
  refine ⟨-mm, ?_⟩
  push_cast
  rw [hmm']
  ring

/-- **General-root-angle form of `Work.GATE2.PathTransport.chainWindow_of_exitPath` (PT).**
This is the exactly-proved file `Submission/Work/GATE2/PathTransport/chainWindow_of_exitPath.lean`
(namespace `Work.GATE2.PathTransport`) with the root-angle hypothesis `hα : 1023 * α = 371` replaced
by `hα : ∃ s : ℤ, 1023 * α = (s : ℝ)`; everything else, including every numeric bound, is verbatim.
The design needs the two root angles `α₁` (`1023 α₁ = 371`) and `α₂` (`1023 α₂ = 404`), so the
single-integer form does not suffice.

Method: copy the `371` file into this path, rename the namespace to
`Work.GATE2.PathTransport.general`, and generalize the *only* arithmetic use of `371`:
* inside `dev_transport_aux`, replace
  `have hαint : ∃ t : ℤ, ((1024 : ℝ) - 1) * α = (t : ℝ) := by refine ⟨371, …⟩; …`
  by the derivation from the existential `hα` (take `t = s`, using `(1024 : ℝ) - 1 = 1023`);
* the private helpers `nsmul_two_pi_alpha` / `angle_F_iterate_aux` of that file (whose only use of
  `371` is `Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul`) must be generalized in the same file:
  their general form is `∃ t : ℤ, (((1024 ^ m : ℕ) : ℝ) - 1) * α = (t : ℝ)`, which follows from
  `sub_dvd_pow_sub_pow (1024 : ℤ) 1 m` (`1024^m - 1 = 1023 * q`) together with `1023 * α = s`,
  giving `(1024^m - 1) * α = q * s`.
All other helpers (`coe_two_pi_deviation`, `nsmul_coe_two_pi_div`, `G`, `angle_torsion_const`,
`mem_critDomain_iterate`, `varphiCrit_F_iterate`, `continuousAt_deviation_fixed`,
`deviation_mem`) are already `α`-agnostic and can be reused as they are (the `angle_F_iterate` of
the `371` namespace may NOT be used, since it demands `1023 * α = 371`; use the generalized local
copy). -/

theorem chainWindow_of_exitPath {e : ℂ} {α : ℝ} (hα : ∃ s : ℤ, 1023 * α = (s : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    (σ : C(unitInterval, ℂ)) (h0 : σ 0 = e) (h1 : σ 1 = Work.EL.F e e)
    (hdev : ∀ t, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
      ((Work.EL.F e)^[m - 1] (σ t))| < (1 / 8192 : ℝ))
    (hpot : ∀ t, (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0 <
      Work.Bottcher.green e ((Work.EL.F e)^[m - 1] (σ t))) :
    ∀ k ≤ m, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)| <
      (1 / 2048 : ℝ) := by
  have hFcont : Continuous (Work.EL.F e) := by
    show Continuous ((Work.Landing.Tsq e)^[5])
    exact (Work.ELNest.continuous_tsq e).iterate 5
  -- (A3): the whole orbit of every point of `σ` is in the critical domain
  have hcrit : ∀ (t : unitInterval) (i : ℕ), i ≤ m - 1 →
      (Work.EL.F e)^[i] (σ t) ∈ Work.ParamRays.critDomain e :=
    fun t i hi => mem_critDomain_iterate (c := e) (z := σ t) (j := m - 1) (hpot t) i hi
  -- the two top deviations, which are both `< 1/8192`
  have hstep : (Work.EL.F e)^[m] e = (Work.EL.F e)^[m - 1] (Work.EL.F e e) :=
    iterate_sub_one_apply (f := Work.EL.F e) (x := e) hm
  have hdt : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)|
      < (1 / 8192 : ℝ) := by
    have hh := hdev 1
    rw [h1, ← hstep] at hh
    exact hh
  have hdb : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e)|
      < (1 / 8192 : ℝ) := by
    have hh := hdev 0
    rwa [h0] at hh
  -- (A4): the one-step transport of the deviation
  have htrans : ∀ k ≤ m - 1, ∃ N : ℤ,
      Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
        - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)
      = (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
          - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
        / (1024 : ℝ) ^ (m - 1 - k) + (N : ℝ) := by
    intro k hk
    have hjk : m - 1 - k + k = m - 1 := Nat.sub_add_cancel hk
    let γ : C(unitInterval, ℂ) :=
      ⟨fun t => (Work.EL.F e)^[k] (σ t), (hFcont.iterate k).comp σ.continuous⟩
    have hγdom : ∀ t : unitInterval, γ t ∈ Work.ParamRays.critDomain e :=
      fun t => hcrit t k hk
    have hiter : ∀ t : unitInterval,
        (Work.EL.F e)^[m - 1 - k] (γ t) = (Work.EL.F e)^[m - 1] (σ t) := by
      intro t
      show (Work.EL.F e)^[m - 1 - k] ((Work.EL.F e)^[k] (σ t))
        = (Work.EL.F e)^[m - 1] (σ t)
      rw [← Function.iterate_add_apply, hjk]
    have hdomj : ∀ t : unitInterval,
        (Work.EL.F e)^[m - 1 - k] (γ t) ∈ Work.ParamRays.critDomain e := by
      intro t
      rw [hiter t]
      exact hcrit t (m - 1) le_rfl
    have hsmallj : ∀ t : unitInterval, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
        ((Work.EL.F e)^[m - 1 - k] (γ t))| < 1 / 4 := by
      intro t
      rw [hiter t]
      linarith [hdev t]
    obtain ⟨N, hN⟩ :=
      dev_transport_aux (e := e) (α := α) hα γ (m - 1 - k) hγdom hdomj hsmallj
    refine ⟨N, ?_⟩
    have hγ0 : γ 0 = (Work.EL.F e)^[k] e := by
      show (Work.EL.F e)^[k] (σ 0) = (Work.EL.F e)^[k] e
      rw [h0]
    have hγ1 : γ 1 = (Work.EL.F e)^[k + 1] e := by
      show (Work.EL.F e)^[k] (σ 1) = (Work.EL.F e)^[k + 1] e
      rw [h1]
      exact (Function.iterate_succ_apply (Work.EL.F e) k e).symm
    have hγ1' : (Work.EL.F e)^[m - 1 - k] (γ 1) = (Work.EL.F e)^[m] e := by
      rw [hγ1, ← Function.iterate_add_apply]
      congr 1
      omega
    have hγ0' : (Work.EL.F e)^[m - 1 - k] (γ 0) = (Work.EL.F e)^[m - 1] e := by
      rw [hγ0, ← Function.iterate_add_apply, hjk]
    rw [hγ1', hγ0', hγ1, hγ0] at hN
    exact hN
  -- (A5): the backward induction, with the geometric weight `G`
  have hkey : ∀ j : ℕ, ∀ k : ℕ, k ≤ m → m - k = j →
      |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)|
        ≤ 1 / 8192 + (2 / 8192) * G j := by
    intro j
    induction j with
    | zero =>
      intro k hk hjk
      have hkm : k = m := by omega
      rw [hkm, G_zero]
      linarith [hdt]
    | succ j ih =>
      intro k hk hjk
      rw [G_succ]
      have hk1 : k + 1 ≤ m := by omega
      have hmk : m - (k + 1) = j := by omega
      have ihk := ih (k + 1) hk1 hmk
      have hkj : k ≤ m - 1 := by omega
      obtain ⟨N, hN⟩ := htrans k hkj
      have hjk' : m - 1 - k = j := by omega
      rw [hjk'] at hN
      have hmem :=
        Work.GATE.deviation_mem (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)
      have hdk_le : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)|
          ≤ 1 / 2 := abs_le.mpr ⟨hmem.1.le, hmem.2⟩
      have hδ : |(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
            - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
          / (1024 : ℝ) ^ j| ≤ (2 / 8192 : ℝ) * (1 / 1024 : ℝ) ^ j := by
        have hn : (0 : ℝ) < (1024 : ℝ) ^ j := pow_pos (by norm_num) j
        have hval : (2 / 8192 : ℝ) / (1024 : ℝ) ^ j
            = (2 / 8192 : ℝ) * (1 / 1024 : ℝ) ^ j := by
          rw [one_div, inv_pow, div_eq_mul_inv]
        rw [← hval, abs_div, abs_of_pos hn, div_le_div_iff_of_pos_right hn]
        have htri : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
              - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e)|
            ≤ |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)|
              + |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e)| := by
          have hh := abs_add_le
            (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e))
            (-(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e)))
          simpa only [sub_eq_add_neg, abs_neg] using hh
        linarith
      have hsmall1 : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
            ((Work.EL.F e)^[k + 1] e)
          - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
              - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
            / (1024 : ℝ) ^ j| < 1 / 2 := by
        have htri : |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
              - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                  - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
                / (1024 : ℝ) ^ j|
            ≤ |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)|
              + |(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                  - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
                / (1024 : ℝ) ^ j| := by
          have hh := abs_add_le
            (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e))
            (-((Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
              / (1024 : ℝ) ^ j))
          simpa only [sub_eq_add_neg, abs_neg] using hh
        have hdiv : (2 / 8192 : ℝ) * (1 / 1024 : ℝ) ^ j ≤ 2 / 8192 := by
          have h1 : (1 / 1024 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
        have hGj : G j ≤ 1024 / 1023 := G_le j
        linarith
      have hNeq : (N : ℝ)
          = (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
              - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                  - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                    ((Work.EL.F e)^[m - 1] e))
                / (1024 : ℝ) ^ j)
            - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e) := by
        linarith [hN]
      have hN0 : N = 0 := by
        have h1 : |(N : ℝ)| < 1 := by
          rw [hNeq]
          have htri : |(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                  ((Work.EL.F e)^[k + 1] e)
                - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                    - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                      ((Work.EL.F e)^[m - 1] e))
                  / (1024 : ℝ) ^ j)
              - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)|
            ≤ |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
                - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                    - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                      ((Work.EL.F e)^[m - 1] e))
                  / (1024 : ℝ) ^ j|
              + |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)| := by
            have hh := abs_add_le
              (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
                - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                    - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                      ((Work.EL.F e)^[m - 1] e))
                  / (1024 : ℝ) ^ j)
              (-(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)))
            simpa only [sub_eq_add_neg, abs_neg] using hh
          linarith
        have h4 : (-1 : ℤ) < N := by
          exact_mod_cast (abs_lt.mp h1).1
        have h5 : N < 1 := by exact_mod_cast (abs_lt.mp h1).2
        omega
      have hdk_eq : Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k] e)
          = Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
            - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
              / (1024 : ℝ) ^ j := by
        have hz : (N : ℝ) = 0 := by simp [hN0]
        linarith [hNeq, hz]
      rw [hdk_eq]
      calc |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)
            - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
              / (1024 : ℝ) ^ j|
          ≤ |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e)|
            + |(Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m - 1] e))
              / (1024 : ℝ) ^ j| := by
            have htri := abs_add_le
              (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[k + 1] e))
              (-((Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[m] e)
                  - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
                    ((Work.EL.F e)^[m - 1] e))
                / (1024 : ℝ) ^ j))
            simpa only [sub_eq_add_neg, abs_neg] using htri
        _ ≤ 1 / 8192 + (2 / 8192) * (G j + (1 / 1024 : ℝ) ^ j) := by
            linarith [ihk, hδ]
  -- the conclusion
  intro k hk
  have hk' := hkey (m - k) k hk rfl
  have hG := G_le (m - k)
  have hfin : 1 / 8192 + (2 / 8192) * G (m - k) < 1 / 2048 := by linarith
  linarith



end

end Work.GATE2.PathTransport.general
