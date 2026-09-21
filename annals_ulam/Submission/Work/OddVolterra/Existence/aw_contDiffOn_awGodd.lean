import Mathlib
import Submission.Work.OddVolterra.Existence.aw_data
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Window.manifest_eq

/-!
# Smoothness of the localised odd state data `awGodd`

`awGodd n h s z = awChiG s z • KernelExt.GoddM n h s z` is the product of the smooth cutoff
`awChiG` (a bump in the slope variable times a bump in the state variable) and the manifest state
data `GoddM`.  Building on `KernelExt.Rnu_contDiff` the data `GoddM` is `C^∞` in `(s,z)` on every
region where the Abel radicand `krad h s t s` is positive at the two chord endpoints
`t = z 0`, `t = z 1`.

The cutoff is supported in `awSupp = {‖z - baseState s‖ ≤ 2/5, |s - 3/4| ≤ 11/40}`.  On `awSupp`
the two relevant endpoints satisfy `|z i| ≥ 17/25 - 2/5 = 7/25 > 1/5` (`profileX_ge_17_25`), and
`krad h s t s > 0` there (`krad_pos_of_add_pos`), because on the slope window the perturbation `h`
is supported in `[4/5, 9/10]` and small, while

`krad h σ t a = (t + H(a,σ)) (L_σ(t) + L_a(t))`

has both factors with the sign of `t` as soon as `|t| ≥ 1/5` and `σ + a > 1/10`.

On an *open* neighbourhood `awGood` of `awSupp` the manifest data is therefore `C^∞`, and the
cutoff is `C^∞` everywhere, so the product is `C^∞` on `awGood`; off `awSupp` the product
vanishes identically.  Since `awGood ∪ awSuppᶜ = univ` with both sets open, the local
characterisation of `ContDiffOn` gives the claim.

For the diagonal we use that on `σ = s` the `τ`-integrand of the manifest `G2M` does not depend on
`τ`, so `G2M(s,s,·) = KvecM(s,s,·) · ∫_0^1 (√(τ(1-τ)))⁻¹` (`G2M_diag`); this removes the singular
`τ`-weight from the picture.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra

noncomputable section

/-! ## The slope window of the cutoff -/

/-- The closed support region of the cutoff `awChiG`. -/
def awSupp : Set (ℝ × St) :=
  {p | |p.1 - 3 / 4| ≤ 11 / 40 ∧ ‖p.2 - baseState p.1‖ ≤ 2 / 5}

/-- An open neighbourhood of `awSupp` on which the manifest data is `C^∞`. -/
def awGood : Set (ℝ × St) :=
  {p | 9 / 20 < p.1 ∧ p.1 < 21 / 20 ∧ 1 / 5 < |p.2 0| ∧ 1 / 5 < |p.2 1|}

/-! ## Positivity of the Abel radicand on a widened slope box -/

/-- **Positivity of the Abel radicand.**  If the perturbation `h` is supported in `[4/5, 9/10]`
with `C¹`-norm at most `1/100`, then for `σ + a > 1/10` and `|t| ≥ 1/5` both factors of

`krad h σ t a = (t + H(a,σ)) (L_σ(t) + L_a(t))`

have the sign of `t`: `|H| ≤ 1/100 < 1/5 ≤ |t|`, and
`|h σ + h a| ≤ 1/50 < (σ+a)/5 ≤ (σ+a)|t|`.  (Only the smallness of `h` and `h'` is used; the
support hypothesis is part of the standing context.) -/
theorem krad_pos_of_add_pos {h : ℝ → ℝ}
    (_hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {a σ t : ℝ} (hS : 1 / 10 < σ + a) (ht : 1 / 5 ≤ |t|) : 0 < krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x; simpa using hsmall 1 (by norm_num) x
  have hbnd : |hquot h a σ| ≤ 1 / 100 := abs_hquot_le_state hh1
  have hb := abs_le.mp hbnd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hSpos : 0 < σ + a := by linarith
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    have h1 : (1 / 10 : ℝ) * (1 / 5) ≤ (σ + a) * (1 / 5) :=
      mul_le_mul_of_nonneg_right (le_of_lt hS) (by norm_num)
    have h2 : (1 / 10 : ℝ) * (1 / 5) = 1 / 50 := by norm_num
    linarith [hhl, h1, h2]
  have hhline : line h σ t + line h a t = (σ + a) * t + (h σ + h a) := by
    unfold line; ring
  rw [krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + hquot h a σ < 0 := by linarith [hb.2]
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hSpos)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by
      have h3 : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
      linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : 1 / 5 ≤ t := by
      have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + hquot h a σ := by linarith [hb.1]
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hSpos)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by
      have h3 : -((σ + a) * (1 / 5)) < h σ + h a := by
        have h4 : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
        linarith [neg_abs_le (h σ + h a)]
      linarith
    exact mul_pos h1 h2

/-- The radicand `krad h σ t a` is positive on the whole box `[9/20, 21/20]²` (in both orders of
`a` and `σ`) whenever `1/5 ≤ |t|`. -/
theorem krad_pos_box_wide {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ a σ t : ℝ, 9 / 20 ≤ a → a ≤ 21 / 20 → 9 / 20 ≤ σ → σ ≤ 21 / 20 →
      1 / 5 ≤ |t| → 0 < krad h σ t a := by
  intro a σ t ha _ hσ _ ht
  exact krad_pos_of_add_pos hsupp hsmall (by linarith) ht

/-! ## The ball profile on the slope window -/

/-- On `|s| ≤ 21/20` the ball profile stays above `17/25`. -/
lemma profileX_ge_17_25 {s : ℝ} (hs : |s| ≤ 21 / 20) :
    17 / 25 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 17 := by
    have hle : 1 + s ^ 2 ≤ (25 / 17 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 17 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 17 := Real.sqrt_sq (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 17 / 25 * Real.sqrt (1 + s ^ 2) ≤ 17 / 25 * (25 / 17) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

/-! ## Smoothness of the state base point and of the cutoff -/

/-- The ball state `s ↦ baseState s` is `C^∞`. -/
lemma contDiff_baseState_comp :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => baseState p.1) := by
  have hpx : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX :=
    Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  have hdpx : ContDiff ℝ (⊤ : ℕ∞) (deriv Commons.Geometry.Ulam.profileX) := by
    have h := hpx.iterate_deriv 1
    simpa [Function.iterate_one] using h
  rw [show (fun p : ℝ × St => baseState p.1) = fun p : ℝ × St =>
    ![Commons.Geometry.Ulam.profileX p.1, Commons.Geometry.Ulam.profileX p.1,
      deriv Commons.Geometry.Ulam.profileX p.1,
      deriv Commons.Geometry.Ulam.profileX p.1] from funext fun p => rfl]
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp <;> (first | exact hpx.comp contDiff_fst | exact hdpx.comp contDiff_fst)

/-! ## Smoothness of the cutoff -/

/-- The cutoff `awChiG` is `C^∞` on `ℝ × St`. -/
lemma contDiff_awChiG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => awChiG p.1 p.2) := by
  have hbase := contDiff_baseState_comp
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (awCs : ℝ → ℝ) p.1) :=
    (ContDiffBump.contDiff awCs).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => (awCz : St → ℝ) (p.2 - baseState p.1)) :=
    (ContDiffBump.contDiff awCz).comp (contDiff_snd.sub hbase)
  simpa only [awChiG] using h1.mul h2

/-! ## The diagonal reduction of `G2M` -/

/-- On the diagonal `σ = s` the `τ`-integrand of `G2M` is independent of `τ`, so the manifest
`τ`-average is the manifest kernel times the constant `∫_0^1 (√(τ(1-τ)))⁻¹`. -/
lemma G2M_diag (n : ℕ) (h : ℝ → ℝ) (s x y x' y' : ℝ) (i : Fin 2) :
    (Work.OddVolterra.KernelExt.G2M n h s s x y x' y') i =
      ((Work.OddVolterra.KernelExt.KvecM n h s s x y x' y') i) *
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ := by
  have hpt : ∀ τ : ℝ,
      (Work.OddVolterra.KernelExt.KvecM n h (s + τ * (s - s)) s x y x' y') i /
          Real.sqrt (τ * (1 - τ))
        = ((Work.OddVolterra.KernelExt.KvecM n h s s x y x' y') i) *
            (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    intro τ
    rw [show s + τ * (s - s) = s by ring, div_eq_mul_inv]
  simp only [Work.OddVolterra.KernelExt.G2M]
  rw [intervalIntegral.integral_congr (fun τ _ => hpt τ),
    intervalIntegral.integral_const_mul]

/-! ## Smoothness of the manifest data in `(s, z)` -/

/-- `Kden h p.1 p.1 (t p)` is `C^∞` on a set where it is positive. -/
lemma contDiffOn_Kden_diag {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × St)} {t : ℝ × St → ℝ} (ht : ContDiffOn ℝ (⊤ : ℕ∞) t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.1 (t p)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => Kden h p.1 p.1 (t p)) B := by
  have hquotB : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => hquot h p.1 p.1) B :=
    (Existence.hquot_contDiff hh).contDiffOn.comp
      (contDiffOn_fst.prodMk contDiffOn_fst) (fun _ _ => Set.mem_univ _)
  have hhB : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => h p.1) B :=
    hh.contDiffOn.comp contDiffOn_fst (fun _ _ => Set.mem_univ _)
  have hp1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => p.1 * t p) B := contDiffOn_fst.mul ht
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St =>
      (t p + hquot h p.1 p.1) * ((p.1 * t p + h p.1) + (p.1 * t p + h p.1))) B :=
    (ht.add hquotB).mul ((hp1.add hhB).add (hp1.add hhB))
  have hsqrt := hrad.sqrt (fun p hp => by
    have h := htpos p hp
    rw [Kden, Real.sqrt_pos, line] at h
    exact ne_of_gt h)
  simpa only [Kden, line] using hsqrt

/-- The first manifest kernel `K₁` on the diagonal, with a `C^∞` family of third coordinates, is
`C^∞` where `Kden` is positive. -/
lemma contDiffOn_K1M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × St)} {t : ℝ × St → ℝ} (ht : ContDiffOn ℝ (⊤ : ℕ∞) t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.1 (t p)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => Work.OddVolterra.KernelExt.K1M n h p.1 p.1 (t p)) B := by
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => Work.OddVolterra.KernelExt.J1M n h p.1 p.1 (t p)) B := by
    have hR : ContDiffOn ℝ (⊤ : ℕ∞)
        (Work.OddVolterra.KernelExt.Rnu ((n : ℝ) + 1 / 2) h (fun _ => (1 : ℝ)) (n + 1))
        Set.univ :=
      (Work.OddVolterra.KernelExt.Rnu_contDiff ((n : ℝ) + 1 / 2) hh contDiff_const (n + 1)
        ).contDiffOn
    have hPhi : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (p.1, (p.1, t p))) B :=
      contDiffOn_fst.prodMk (contDiffOn_fst.prodMk ht)
    have hcomp := hR.comp hPhi (fun _ _ => Set.mem_univ _)
    simpa only [Work.OddVolterra.KernelExt.J1M, Function.comp_def] using hcomp
  have hKd := contDiffOn_Kden_diag hh ht htpos
  exact hJ.div hKd (fun p hp => ne_of_gt (htpos p hp))

/-- The second manifest kernel `K₂` on the diagonal, with a `C^∞` family of third coordinates, is
`C^∞` where `Kden` is positive. -/
lemma contDiffOn_K2M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × St)} {t : ℝ × St → ℝ} (ht : ContDiffOn ℝ (⊤ : ℕ∞) t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.1 (t p)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => Work.OddVolterra.KernelExt.K2M n h p.1 p.1 (t p)) B := by
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
    unfold lineSlope
    fun_prop
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => Work.OddVolterra.KernelExt.J2M n h p.1 p.1 (t p)) B := by
    have hR : ContDiffOn ℝ (⊤ : ℕ∞)
        (Work.OddVolterra.KernelExt.Rnu ((n : ℝ) - 1 / 2) h
          (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) n) Set.univ :=
      (Work.OddVolterra.KernelExt.Rnu_contDiff ((n : ℝ) - 1 / 2) hh hinit n).contDiffOn
    have hPhi : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => (p.1, (p.1, t p))) B :=
      contDiffOn_fst.prodMk (contDiffOn_fst.prodMk ht)
    have hcomp := hR.comp hPhi (fun _ _ => Set.mem_univ _)
    simpa only [Work.OddVolterra.KernelExt.J2M, Function.comp_def] using hcomp
  have hKd := contDiffOn_Kden_diag hh ht htpos
  exact hJ.div hKd (fun p hp => ne_of_gt (htpos p hp))

/-- The `k`-th coordinate of the state is `C^∞`. -/
lemma contDiffOn_coord {B : Set (ℝ × St)} (k : Fin 4) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => p.2 k) B :=
  (contDiffOn_pi.mp (contDiffOn_snd : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => p.2) B)) k

/-- The manifest kernel, evaluated on the diagonal at the two chord endpoints `z 0`, `z 1` of the
state, is `C^∞` in `(s,z)` wherever the two radicands are positive. -/
lemma contDiffOn_KvecM_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set (ℝ × St)}
    (hpos0 : ∀ p ∈ B, 0 < Kden h p.1 p.1 (-(p.2 0)))
    (hpos1 : ∀ p ∈ B, 0 < Kden h p.1 p.1 (p.2 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St =>
        Work.OddVolterra.KernelExt.KvecM n h p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) B := by
  have hK1x := contDiffOn_K1M_diag n hh (t := fun p : ℝ × St => -(p.2 0))
    (contDiffOn_coord (B := B) 0).neg hpos0
  have hK1y := contDiffOn_K1M_diag n hh (t := fun p : ℝ × St => p.2 1)
    (contDiffOn_coord (B := B) 1) hpos1
  have hK2x := contDiffOn_K2M_diag n hh (t := fun p : ℝ × St => -(p.2 0))
    (contDiffOn_coord (B := B) 0).neg hpos0
  have hK2y := contDiffOn_K2M_diag n hh (t := fun p : ℝ × St => p.2 1)
    (contDiffOn_coord (B := B) 1) hpos1
  have hd2 := contDiffOn_coord (B := B) 2
  have hd3 := contDiffOn_coord (B := B) 3
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · refine (((hK1x.mul hd2).add (hK1y.mul hd3)).neg).congr (fun p _ => ?_)
    simp [Work.OddVolterra.KernelExt.KvecM]
  · refine (((hK2x.mul hd2).add (hK2y.mul hd3)).neg).congr (fun p _ => ?_)
    simp [Work.OddVolterra.KernelExt.KvecM]

/-- **The manifest state data is `C^∞` on `awGood`.**  There the two chord-endpoint radicands are
positive, so `KvecM` is `C^∞`; the diagonal reduction `G2M_diag` exhibits `GoddM` as that kernel
times the constant `∫_0^1 (√(τ(1-τ)))⁻¹`. -/
lemma contDiffOn_GoddM_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × St => Work.OddVolterra.KernelExt.GoddM n h p.1 p.2) awGood := by
  have hpos0 : ∀ p ∈ awGood, 0 < Kden h p.1 p.1 (-(p.2 0)) := by
    intro p hp
    obtain ⟨hs1, hs2, hz0, _⟩ := hp
    rw [Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (krad_pos_box_wide hsupp hsmall p.1 p.1 (-(p.2 0))
      (le_of_lt hs1) (le_of_lt hs2) (le_of_lt hs1) (le_of_lt hs2)
      (by simpa using (le_of_lt hz0)))
  have hpos1 : ∀ p ∈ awGood, 0 < Kden h p.1 p.1 (p.2 1) := by
    intro p hp
    obtain ⟨hs1, hs2, _, hz1⟩ := hp
    rw [Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (krad_pos_box_wide hsupp hsmall p.1 p.1 (p.2 1)
      (le_of_lt hs1) (le_of_lt hs2) (le_of_lt hs1) (le_of_lt hs2)
      (by simpa using (le_of_lt hz1)))
  have hK := contDiffOn_KvecM_diag n hh hpos0 hpos1
  have hKm : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St =>
      - (((Work.OddVolterra.KernelExt.KvecM n h p.1 p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) i) *
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹)) awGood := by
    intro i
    exact (((contDiffOn_pi.mp hK) i).mul contDiffOn_const).neg
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · refine (contDiffOn_coord (B := awGood) 0).congr (fun p _ => ?_)
    simp [Work.OddVolterra.KernelExt.GoddM]
  · refine (contDiffOn_coord (B := awGood) 1).congr (fun p _ => ?_)
    simp [Work.OddVolterra.KernelExt.GoddM]
  · refine (hKm 0).congr (fun p _ => ?_)
    simp only [Work.OddVolterra.KernelExt.GoddM]
    rw [G2M_diag n h p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) 0]
    simp
  · refine (hKm 1).congr (fun p _ => ?_)
    simp only [Work.OddVolterra.KernelExt.GoddM]
    rw [G2M_diag n h p.1 (p.2 0) (p.2 1) (p.2 2) (p.2 3) 1]
    simp

/-! ## The two open sets covering the space -/

/-- `awGood` is open. -/
lemma isOpen_awGood : IsOpen awGood := by
  have hcont0 : Continuous (fun p : ℝ × St => |p.2 0|) := by fun_prop
  have hcont1 : Continuous (fun p : ℝ × St => |p.2 1|) := by fun_prop
  simp only [awGood, Set.ofPred_and]
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const hcont0).inter (isOpen_lt continuous_const hcont1)))

/-- `awSupp` is closed. -/
lemma isClosed_awSupp : IsClosed awSupp := by
  simp only [awSupp, Set.ofPred_and]
  exact (isClosed_le (continuous_abs.comp (continuous_fst.sub continuous_const))
    continuous_const).inter
    (isClosed_le ((continuous_snd.sub contDiff_baseState_comp.continuous).norm) continuous_const)

/-- The support region is contained in the good open set: on it the ball profile is `≥ 17/25`, so
the two endpoints are at distance `> 1/5` from the axis. -/
lemma awSupp_subset_awGood : awSupp ⊆ awGood := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  have hb1 := abs_le.mp h1
  have hs1 : 9 / 20 < p.1 := by linarith [hb1.1]
  have hs2 : p.1 < 21 / 20 := by linarith [hb1.2]
  have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX p.1 :=
    profileX_ge_17_25 (by rw [abs_le]; exact ⟨by linarith [hb1.1], by linarith [hb1.2]⟩)
  have hcoord : ∀ i : Fin 4,
      |p.2 i - Commons.Geometry.Ulam.profileX p.1| ≤ 2 / 5 → 1 / 5 < |p.2 i| := by
    intro i hci
    have hlow := (abs_le.mp hci).1
    have : (1 : ℝ) / 5 < p.2 i := by linarith
    exact lt_of_lt_of_le this (le_abs_self _)
  have h0 : 1 / 5 < |p.2 0| := by
    have hcomp : |p.2 0 - baseState p.1 0| ≤ 2 / 5 := by
      have h := norm_le_pi_norm (p.2 - baseState p.1) 0
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h h2
    exact hcoord 0 hcomp
  have h1' : 1 / 5 < |p.2 1| := by
    have hcomp : |p.2 1 - baseState p.1 1| ≤ 2 / 5 := by
      have h := norm_le_pi_norm (p.2 - baseState p.1) 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h h2
    exact hcoord 1 hcomp
  exact ⟨hs1, hs2, h0, h1'⟩

/-- Off `awSupp` the cutoff vanishes, hence so does `awGodd`. -/
lemma awGodd_eq_zero_off_awSupp {n : ℕ} {h : ℝ → ℝ} {p : ℝ × St} (hp : p ∉ awSupp) :
    awGodd n h p.1 p.2 = 0 := by
  have hp' : ¬ (|p.1 - 3 / 4| ≤ 11 / 40 ∧ ‖p.2 - baseState p.1‖ ≤ 2 / 5) := hp
  rcases not_and_or.mp hp' with h1 | h2
  · rw [awGodd, awChiG, awCs_eq_zero (le_of_lt (not_le.mp h1)), zero_mul, zero_smul]
  · rw [awGodd, awChiG, awCz_eq_zero (le_of_lt (not_le.mp h2)), mul_zero, zero_smul]

/-! ## The target -/

theorem aw_contDiffOn_awGodd (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.Existence.awGodd n h p.1 p.2) Set.univ := by
  have hgam := contDiffOn_GoddM_diag n hh hsupp hsmall
  have hgood : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => awGodd n h p.1 p.2) awGood := by
    refine (contDiff_awChiG.contDiffOn.smul hgam).congr (fun p _ => ?_)
    rfl
  have hzero : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × St => awGodd n h p.1 p.2) awSuppᶜ :=
    (contDiffOn_const (c := (0 : St))).congr (fun p hp => awGodd_eq_zero_off_awSupp hp)
  refine contDiffOn_of_locally_contDiffOn (fun p _ => ?_)
  by_cases hp : p ∈ awGood
  · exact ⟨awGood, isOpen_awGood, hp, hgood.mono Set.inter_subset_right⟩
  · exact ⟨awSuppᶜ, isClosed_awSupp.isOpen_compl,
      fun hc => hp (awSupp_subset_awGood hc), hzero.mono Set.inter_subset_right⟩

end

end Work.OddVolterra.Existence
