import Mathlib
import Submission.Commons.Analysis.Complex.norm_cpow_real

/-!
# RegularSlit -- the explicit regular radial-slit conformal map
# (route-B seed: the sharp/attainment side of the radial-slit form of
# Dubinin's hedgehog theorem; STATUS §49.2)

STATUS: verified research-isolate module (0 sorries, axiom-clean
[propext, Classical.choice, Quot.sound]); unimported; Mathlib + one
commons lemma (`Commons.Analysis.Complex.norm_cpow_real`).  No dependency
on `Submission.lean`.

MATHEMATICAL BACKGROUND (STATUS §49).  Step3 (Dubinin's hedgehog
inequality, ALL s) is equivalent, by the exact duality
`cap(⋃_j[0,a_j]) = 1/rad(ℂ∖⋃_j {x·a_j^{-1} : x ≥ |a_j|^{-1}}, 0)`, to the
RADIAL-SLIT extremal theorem: for pairwise-distinct unit directions
v_1,…,v_s, the domain D = ℂ ∖ ⋃_j {x v_j : x ≥ 1} (contains 0 and the open
unit disk; equals the unit disk plus s exterior angular sectors) satisfies

    rad(D, 0) ≥ 4^{1/s},   equality iff the v_j are equiangular,

where rad(D,0) is the conformal radius at 0.  For the EQUIANGULAR slits
(v_j = the s-th roots of unity) the extremal value rad = 4^{1/s} is
realized by the explicit map

    f_s(ζ) = 4^{1/s} · ζ / (1 + ζ^s)^{2/s}   (𝔻 → D_s, f_s(0) = 0),

which is the subject of this module.  MACHINE-VERIFIED here (0 sorries,
axiom-clean):
  * `regSlit_deriv_eq`: the derivative on the unit disk,
        f_s'(ζ) = 4^{1/s}·(1 − ζ^s)·(1 + ζ^s)^{−(1+2/s)}
    (all powers principal; the base 1+ζ^s has positive real part there);
  * `regSlit_deriv_ne_zero`: f_s'(ζ) ≠ 0 at every ζ with ‖ζ‖ < 1, i.e.
    f_s is LOCALLY univalent at every point of the unit disk (the local
    half of conformality);
  * `regSlit_deriv_zero_norm`: ‖f_s'(0)‖ = 4^{1/s} — the sharp value of
    the radial-slit extremal constant, realized by f_s at 0;
  * the POWER IDENTITY `regSlit_pow`: (f_s(ζ))^s = oneSlit(ζ^s) for
    ‖ζ‖ < 1, where oneSlit(u) = 4u/(1+u)² is the s = 1 map
    (`regSlit_one_eq`) — the s-fold lift structure `f_s^s = f_1 ∘ (·^s)`;
  * the ONE-SLIT AVOIDANCE `one_slit_avoid`: oneSlit(u) ∉ [1,∞) for
    |u| < 1 (Cayley form `oneSlit u = 1 − cayley(u)²` with
    `cayley_re_pos`: Re(1−u)/(1+u) = (1−‖u‖²)/|1+u|² > 0);
  * the INCLUSION `regSlit_mapsTo_rayAvoiding`: f_s(𝔻) ⊆ D_s, where the
    equiangular s-slit domain is `rayAvoiding s := {w | w^s ∉ [1,∞)}`
    (the power-form description of ℂ ∖ ⋃_{k<s} {x·e^{2πik/s} : x ≥ 1};
    the k-indexed ray-set equality is a stated next step);
  * `regSlit_differentiableOn` (f_s analytic on 𝔻), `regSlit_zero`
    (f_s(0) = 0), and the MAP-FORM DUAL INEQUALITY
    `equiangular_dual_lower`: D_s admits an analytic map of the unit disk
    fixing 0 with ‖f'(0)‖ = 4^{1/s} — so any conformal-radius definition
    as a supremum of such ‖f'(0)‖ over maps into D_s is ≥ 4^{1/s} for the
    equiangular case;
  * s = 1 SURJECTIVITY `one_slit_surj`: oneSlit maps 𝔻 onto ℂ∖[1,∞) — the
    explicit inverse through y := √(1−v) (Re y > 0 on the slit plane) and
    u := (1−y)/(1+y) (‖u‖ < 1), with `cayley` as the key factor;
  * SURJECTIVITY `regSlit_surj`: every point of D_s is attained by f_s at
    some point of 𝔻 — v := w^s has the one-slit preimage u ∈ 𝔻, ζ₀ :=
    exp(log u/s) is an s-th root of u inside the disk, ω := w/f_s(ζ₀) is
    an s-th root of unity (ω^s = 1 by the power identity), and
    ζ := ζ₀·ω has ‖ζ‖ < 1 with f_s(ζ) = w;
  * the IMAGE THEOREM `regSlit_image_eq_rayAvoiding`:
    f_s(𝔻) = D_s (the open unit disk maps exactly onto the equiangular
    s-slit domain);
  * the RAY DESCRIPTION of D_s: `unitRoot s k := exp(2πk·I/s)`,
    `raySet s := ⋃_{k<s} {x·unitRoot s k : x ≥ 1}`;
    `pow_conditions_of_mem_raySet` (w on a ray ⟹ w^s ∈ [1,∞));
    `mem_raySet_of_pow_conditions` (the converse, CLASSIFIED through the
    argument-as-Angle group: `s•(arg w : Angle) = 0` from
    `arg_pow_coe_angle`, `Real.Angle.nsmul_eq_iff` with `k : Fin s`, the
    polar identity and 2π-periodicity of exp); and the CLOSED form
    `rayAvoiding_eq_compl_raySet`: `D_s = ℂ ∖ raySet s` — the complement
    of the union of the k-indexed equiangular radial slits.
  * INJECTIVITY and the CONFORMAL BIJECTION: `cayley_injOn_ball`
    (Möbius injectivity), `oneSlit_injOn_ball` (via the Cayley form
    `oneSlit u = 1 − cayley(u)²` and `cayley_re_pos`: the sign case
    `cayley u₁ = −cayley u₂` is impossible), `regSlit_injOn_ball` (the
    power identity pushes oneSlit-injectivity to the s-th powers; common
    nonzero factors cancel), `norm_pow_lt_one`;
  * `regSlit_bijOn_rayAvoiding` (f_s is a Set.BijOn of the unit disk onto
    D_s) and `equiangular_conformal_data`: an analytic bijection 𝔻 → D_s
    fixing 0 with ‖f'(0)‖ = 4^{1/s} — the exact dual at map level, from
    which a conformal-radius definition reads off rad(D_s,0) = 4^{1/s}
    (the supremum lower bound 4^{1/s} is realised by f_s).
(For s = 1 this recovers the classical f(ζ) = 4ζ/(1+ζ)² : 𝔻 → ℂ∖[1,∞),
|f'(0)| = 4.)  The BOUNDARY behaviour of f_s (on |z| = 1:
‖f_s(e^{it})‖ = |cos(st/2)|^{-2/s} ≥ 1, = 1 exactly at the slit tips
t = 2πk/s, → ∞ at the arc centres (2k+1)π/s, the s rays swept with
constant argument per arc) is stated in the background but NOT yet
formalised in this module.  This is the explicit sharp-side seed of
route B; the extremal INEQUALITY for arbitrary directions is the open
Dubinin/Gonchar content (routes A/B/C).
-/

noncomputable section

open scoped Real Topology BigOperators
open Set Filter Metric Complex

namespace Submission.RegularSlit

/-- The exponent `2/s` (complex division of the real number `2` by `s`):
the power in `(1 + ζ^s)^(2/s)`.  Equal to `↑(2 / (s : ℝ))` by
`Complex.ofReal_div`; the division form avoids coercion normal-form issues
in field algebra. -/
def slitExponent (s : ℕ) : ℂ := (2 : ℂ) / (s : ℂ)

/-- The leading coefficient `4^{1/s}` of the regular s-slit map, viewed as
a complex number. -/
def slitCoef (s : ℕ) : ℂ := (↑((4 : ℝ) ^ (1 / (s : ℝ))) : ℂ)

/-- **The regular radial-slit map** `f_s(ζ) := 4^{1/s}·ζ/(1+ζ^s)^{2/s}`
(principal complex powers).  For s = 1 this is the classical
`4ζ/(1+ζ)² : 𝔻 → ℂ∖[1,∞)`. -/
def regSlit (s : ℕ) (ζ : ℂ) : ℂ :=
  slitCoef s * (ζ / (1 + ζ ^ s) ^ slitExponent s)

/-- The coefficient `4^{1/s}` is a positive real, hence nonzero. -/
lemma slitCoef_ne_zero {s : ℕ} (_hs : 1 ≤ s) : slitCoef s ≠ 0 := by
  unfold slitCoef
  have hpos : 0 < (4 : ℝ) ^ (1 / (s : ℝ)) := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

/-- The coefficient is nonnegative as a real scalar. -/
lemma slitCoef_re_nonneg (s : ℕ) : 0 ≤ (slitCoef s).re := by
  unfold slitCoef
  simp
  exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _

/-- `s` is a nonzero complex number when `1 ≤ s`. -/
lemma cast_ne_zero {s : ℕ} (hs : 1 ≤ s) : (s : ℂ) ≠ 0 := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))
  exact Complex.ofReal_ne_zero.mpr hsR

/-- `(s : ℂ) · slitExponent s = 2` for `1 ≤ s`. -/
lemma cast_mul_slitExponent {s : ℕ} (hs : 1 ≤ s) :
    (s : ℂ) * slitExponent s = (2 : ℂ) := by
  unfold slitExponent
  have hz : (s : ℂ) ≠ 0 := cast_ne_zero hs
  field_simp [hz]

/-- `slitExponent s` is the real number `2/s` viewed in ℂ (for the
boundary-norm computation). -/
lemma slitExponent_eq_ofReal {s : ℕ} (hs : 1 ≤ s) :
    slitExponent s = (((2 : ℝ) / (s : ℝ)) : ℂ) := by
  unfold slitExponent
  rfl

/-- `a^(s−1) · a = a^s` for `1 ≤ s` (commutative power step). -/
lemma pow_pred_mul {α : Type*} [CommMonoid α] {s : ℕ} (hs : 1 ≤ s) (a : α) :
    a ^ (s - 1) * a = a ^ s := by
  have hs' : (s - 1) + 1 = s := by omega
  have hpow := pow_succ (a := a) (n := s - 1)
  rw [hs'] at hpow
  exact hpow.symm

/-- The base `1 + ζ^s` has positive real part on the open unit disk
(`s ≥ 1`), hence lies in the slit plane there (and is nonzero). -/
lemma one_add_pow_mem_slitPlane {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    1 + ζ ^ s ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hdec : ‖ζ ^ s‖ ≤ ‖ζ‖ := by
    calc
      ‖ζ ^ s‖ = ‖ζ‖ ^ s := by exact norm_pow ζ s
      _ ≤ ‖ζ‖ := by
        have h1 : ‖ζ‖ ^ (s - 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) (le_of_lt hζ)
        calc
          ‖ζ‖ ^ s = ‖ζ‖ * ‖ζ‖ ^ (s - 1) := by
            rw [← pow_pred_mul hs ‖ζ‖]
            ring
          _ ≤ ‖ζ‖ := by
            calc
              ‖ζ‖ * ‖ζ‖ ^ (s - 1) ≤ ‖ζ‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg ζ)
              _ = ‖ζ‖ := by rw [mul_one]
  have hrelo : -‖ζ ^ s‖ ≤ (ζ ^ s).re := by
    have h := Complex.re_le_norm (-(ζ ^ s))
    have h' : -(ζ ^ s).re ≤ ‖ζ ^ s‖ := by simpa using h
    linarith
  have hone : (1 : ℂ).re = 1 := by simp
  have h : 0 < 1 - ‖ζ‖ := sub_pos.mpr hζ
  calc
    0 < 1 - ‖ζ‖ := h
    _ ≤ 1 - ‖ζ ^ s‖ := by linarith
    _ ≤ (1 + ζ ^ s).re := by
      rw [Complex.add_re, hone]
      linarith

/-- `1 + ζ^s ≠ 0` on the unit disk. -/
lemma one_add_pow_ne_zero {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    1 + ζ ^ s ≠ 0 := by
  have hmem : 1 + ζ ^ s ∈ Complex.slitPlane := one_add_pow_mem_slitPlane hs hζ
  exact (Complex.mem_slitPlane_iff_arg.mp hmem).2

/-- `1 − ζ^s ≠ 0` on the unit disk (`s ≥ 1`). -/
lemma one_sub_pow_ne_zero {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    1 - ζ ^ s ≠ 0 := by
  intro hz
  have hz' : ζ ^ s = 1 := (sub_eq_zero.mp hz).symm
  have hlt : ‖ζ ^ s‖ < 1 := by
    calc
      ‖ζ ^ s‖ = ‖ζ‖ ^ s := by exact norm_pow ζ s
      _ ≤ ‖ζ‖ := by
        have h1 : ‖ζ‖ ^ (s - 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) (le_of_lt hζ)
        calc
          ‖ζ‖ ^ s = ‖ζ‖ * ‖ζ‖ ^ (s - 1) := by
            rw [← pow_pred_mul hs ‖ζ‖]
            ring
          _ ≤ ‖ζ‖ := by
            calc
              ‖ζ‖ * ‖ζ‖ ^ (s - 1) ≤ ‖ζ‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg ζ)
              _ = ‖ζ‖ := by rw [mul_one]
      _ < 1 := hζ
  rw [hz', norm_one] at hlt
  norm_num at hlt

/-- Pointwise identity rewriting the division by `(1+ζ^s)^e` as
multiplication by `(1+ζ^s)^{−e}` (always true: `cpow_neg`). -/
lemma regSlit_eq_neg_pow (s : ℕ) (ζ : ℂ) :
    regSlit s ζ = slitCoef s * (ζ * (1 + ζ ^ s) ^ (-slitExponent s)) := by
  unfold regSlit
  congr 1
  calc
    ζ / (1 + ζ ^ s) ^ slitExponent s = ζ * ((1 + ζ ^ s) ^ slitExponent s)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = ζ * (1 + ζ ^ s) ^ (-slitExponent s) := by
      congr 1
      exact (Complex.cpow_neg (1 + ζ ^ s) (slitExponent s)).symm

/-- The derivative of the regular slit map on the unit disk:
`f_s'(ζ) = 4^{1/s} · (1 − ζ^s) · (1 + ζ^s)^{−(1 + 2/s)}`. -/
theorem regSlit_deriv_eq {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    deriv (fun w : ℂ => regSlit s w) ζ =
      slitCoef s * ((1 - ζ ^ s) * (1 + ζ ^ s) ^ (-(1 + slitExponent s))) := by
  classical
  have hslit : 1 + ζ ^ s ∈ Complex.slitPlane := one_add_pow_mem_slitPlane hs hζ
  let e : ℂ := slitExponent s
  -- derivative of the base function g(w) := 1 + w^s is (s:ℂ)·ζ^(s-1)
  have hg : HasDerivAt (fun w : ℂ => 1 + w ^ s) ((s : ℂ) * ζ ^ (s - 1)) ζ := by
    have hp : HasDerivAt (fun w : ℂ => w ^ s) ((s : ℂ) * ζ ^ (s - 1)) ζ := by
      exact hasDerivAt_pow s ζ
    simpa [add_comm] using hp.const_add (1 : ℂ)
  -- derivative of (1+w^s)^(-e)
  have hgm : HasDerivAt (fun w : ℂ => (1 + w ^ s) ^ (-e))
      ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) ζ :=
    hg.cpow_const hslit
  have hgm_diff : DifferentiableAt ℂ (fun w : ℂ => (1 + w ^ s) ^ (-e)) ζ :=
    hgm.differentiableAt
  have hdid : deriv (fun w : ℂ => w) ζ = 1 := by
    simpa using (deriv_id ζ)
  have hEvd : deriv (fun w : ℂ => (1 + w ^ s) ^ (-e)) ζ =
      (-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1)) := hgm.deriv
  -- derivative of P(w) := w · (1+w^s)^(-e)
  have hP : deriv (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) ζ =
      (1 + ζ ^ s) ^ (-e) + ζ * ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) := by
    have hm := deriv_mul (𝕜 := ℂ) (c := fun w : ℂ => w) (d := fun w : ℂ => (1 + w ^ s) ^ (-e))
      differentiableAt_id hgm_diff
    have hEv : ((fun w : ℂ => w) * (fun w : ℂ => (1 + w ^ s) ^ (-e))) =ᶠ[𝓝 ζ]
        (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) := by
      exact Filter.Eventually.of_forall (fun w => rfl)
    calc
      deriv (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) ζ
          = deriv ((fun w : ℂ => w) * (fun w : ℂ => (1 + w ^ s) ^ (-e))) ζ := hEv.deriv_eq.symm
      _ = deriv (fun w : ℂ => w) ζ * (1 + ζ ^ s) ^ (-e) +
            ζ * deriv (fun w : ℂ => (1 + w ^ s) ^ (-e)) ζ := by
            simpa using hm
      _ = 1 * (1 + ζ ^ s) ^ (-e) + ζ * ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) := by
            rw [hdid, hEvd]
      _ = (1 + ζ ^ s) ^ (-e) + ζ * ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) := by
            rw [one_mul]
  -- P-derivative simplifies to (1−ζ^s)·B^(−e−1)
  have hval : (1 + ζ ^ s) ^ (-e) +
        ζ * ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) =
      (1 - ζ ^ s) * (1 + ζ ^ s) ^ (-e - 1) := by
    have hBne : (1 + ζ ^ s : ℂ) ≠ 0 := one_add_pow_ne_zero hs hζ
    have hb : (1 + ζ ^ s) ^ (-e) = (1 + ζ ^ s) ^ (-e - 1) * (1 + ζ ^ s) ^ (1 : ℂ) := by
      rw [← Complex.cpow_add (x := (1 + ζ ^ s)) (-e - 1) 1 hBne]
      congr 1
      ring
    have hstep : ζ * ((-e) * (1 + ζ ^ s) ^ (-e - 1) * ((s : ℂ) * ζ ^ (s - 1))) =
        -(e * (s : ℂ)) * (ζ * ζ ^ (s - 1)) * (1 + ζ ^ s) ^ (-e - 1) := by
      ring
    have hes : e * (s : ℂ) = (2 : ℂ) := by
      unfold e
      rw [mul_comm]
      exact cast_mul_slitExponent hs
    have hpp : ζ * ζ ^ (s - 1) = ζ ^ s := by
      rw [mul_comm]
      exact pow_pred_mul hs ζ
    rw [hb, hstep, hpp, hes]
    rw [Complex.cpow_one]
    ring
  have hP' : deriv (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) ζ =
      (1 - ζ ^ s) * (1 + ζ ^ s) ^ (-e - 1) := by
    rw [hP]
    exact hval
  -- derivative of regSlit = slitCoef * P
  have hdiffP : DifferentiableAt ℂ (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) ζ :=
    (hasDerivAt_id ζ).mul hgm |>.differentiableAt
  have hreg : deriv (fun w : ℂ => regSlit s w) ζ =
      slitCoef s * ((1 - ζ ^ s) * (1 + ζ ^ s) ^ (-e - 1)) := by
    have hEv : (fun w : ℂ => regSlit s w) =ᶠ[𝓝 ζ]
        (fun w : ℂ => slitCoef s * (w * (1 + w ^ s) ^ (-e))) := by
      exact Filter.Eventually.of_forall (fun w => regSlit_eq_neg_pow s w)
    calc
      deriv (fun w : ℂ => regSlit s w) ζ
          = deriv (fun w : ℂ => slitCoef s * (w * (1 + w ^ s) ^ (-e))) ζ := hEv.deriv_eq
      _ = slitCoef s * deriv (fun w : ℂ => w * (1 + w ^ s) ^ (-e)) ζ := by
            rw [deriv_const_mul (slitCoef s) hdiffP]
      _ = slitCoef s * ((1 - ζ ^ s) * (1 + ζ ^ s) ^ (-e - 1)) := by
            rw [hP']
  -- exponent cosmetics: −e−1 = −(1+e)
  have hfin : slitCoef s * ((1 - ζ ^ s) * (1 + ζ ^ s) ^ (-e - 1)) =
      slitCoef s * ((1 - ζ ^ s) * (1 + ζ ^ s) ^ (-(1 + slitExponent s))) := by
    congr 1
    congr 1
    congr 1
    dsimp [e]
    ring
  exact hreg.trans hfin

/-- The derivative of the regular slit map does not vanish on the unit disk
(`1 ≤ s`), so the map is locally univalent at every point of the disk. -/
theorem regSlit_deriv_ne_zero {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    deriv (fun w : ℂ => regSlit s w) ζ ≠ 0 := by
  rw [regSlit_deriv_eq hs hζ]
  have hc : slitCoef s ≠ 0 := slitCoef_ne_zero hs
  have h1 : (1 - ζ ^ s) ≠ 0 := one_sub_pow_ne_zero hs hζ
  have hB : (1 + ζ ^ s) ^ (-(1 + slitExponent s)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (one_add_pow_ne_zero hs hζ)
  exact mul_ne_zero hc (mul_ne_zero h1 hB)

/-- The initial derivative: `‖f_s'(0)‖ = 4^{1/s}` — the sharp conformal
radius of the regular s-slit domain (realized by f_s at 0). -/
theorem regSlit_deriv_zero_norm {s : ℕ} (hs : 1 ≤ s) :
    ‖deriv (fun w : ℂ => regSlit s w) 0‖ = (4 : ℝ) ^ (1 / (s : ℝ)) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by norm_num
  rw [regSlit_deriv_eq hs h0]
  have hs0 : 0 < s := by omega
  have hz : (0 : ℂ) ^ s = 0 := zero_pow (ne_of_gt hs0)
  have hcpow : (1 : ℂ) ^ (-(1 + slitExponent s)) = 1 := by
    exact Complex.one_cpow _
  have hval : slitCoef s * ((1 - (0 : ℂ) ^ s) * (1 + (0 : ℂ) ^ s) ^ (-(1 + slitExponent s))) =
      slitCoef s := by
    rw [hz]
    rw [sub_zero, add_zero]
    rw [Complex.one_cpow]
    simp
  rw [hval]
  unfold slitCoef
  rw [Complex.norm_real]
  have hpos : 0 ≤ (4 : ℝ) ^ (1 / (s : ℝ)) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]


/-! ## Part 2: the one-slit map, the power identity, and the radial-slit
domain (image programme, step 1)

The regular radial-slit domain of the equiangular case is

    D_s := {w | w^s ∉ [1, ∞)}   (equivalently ℂ ∖ ⋃_{k<s} {x·e^{2πik/s} : x ≥ 1}),

i.e. the set of points whose s-th power avoids the slit of the one-slit
domain ℂ∖[1,∞).  The map f_s satisfies the POWER IDENTITY on the unit
disk (proved below from the cpow laws; the base 1+ζ^s has positive real
part there):

    f_s(ζ)^s = f_1(ζ^s) =: oneSlit(ζ^s),   oneSlit(u) := 4u/(1+u)²,

which transfers the (classical, verified here) one-slit AVOIDANCE
(`oneSlit(u) ∉ [1,∞)` for |u| < 1) to f_s, giving
`f_s(𝔻) ⊆ D_s` (`regSlit_mapsTo_rayAvoiding`).  Together with the banked
`regSlit_deriv_zero_norm` (‖f_s'(0)‖ = 4^{1/s}) this yields the dual
inequality in its map form: the equiangular s-slit domain admits an
analytic map of the unit disk with f(0) = 0 and |f'(0)| = 4^{1/s}.
-/

/-- The s = 1 regular slit map (Joukowski-type): `oneSlit(u) = 4u/(1+u)²`,
mapping 𝔻 into ℂ∖[1,∞). -/
def oneSlit (u : ℂ) : ℂ := (4 : ℂ) * u / (1 + u) ^ 2

/-- `regSlit 1 = oneSlit` (definitional content of the s = 1 case). -/
lemma regSlit_one_eq (u : ℂ) : regSlit 1 u = oneSlit u := by
  unfold regSlit oneSlit
  have hc : slitCoef 1 = (4 : ℂ) := by
    unfold slitCoef
    norm_num
  have he : slitExponent 1 = (2 : ℂ) := by
    unfold slitExponent
    norm_num
  rw [hc, he]
  rw [← Complex.cpow_natCast]
  norm_num
  ring

/-- `slitCoef s ^ s = 4` (as complex numbers) for `1 ≤ s`. -/
lemma slitCoef_pow {s : ℕ} (hs : 1 ≤ s) : slitCoef s ^ s = (4 : ℂ) := by
  have hR : (((4 : ℝ) ^ (1 / (s : ℝ)) : ℝ) ^ s : ℝ) = 4 := by
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))
    rw [← Real.rpow_natCast (x := (4 : ℝ) ^ (1 / (s : ℝ))) (n := s)]
    rw [← Real.rpow_mul (x := (4 : ℝ)) (by norm_num : (0 : ℝ) ≤ 4)
      (1 / (s : ℝ)) (s : ℝ)]
    have h : (1 / (s : ℝ)) * (s : ℝ) = 1 := by field_simp [hsR]
    rw [h, Real.rpow_one]
  unfold slitCoef
  rw [← Complex.ofReal_pow]
  exact congrArg (fun r : ℝ => (r : ℂ)) hR

open Set Filter Metric Complex

/-- The real part of `1 + ζ^s` is positive on the unit disk. -/
lemma one_add_pow_re_pos {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    0 < (1 + ζ ^ s).re := by
  have hdec : ‖ζ ^ s‖ ≤ ‖ζ‖ := by
    calc
      ‖ζ ^ s‖ = ‖ζ‖ ^ s := by exact norm_pow ζ s
      _ ≤ ‖ζ‖ := by
        have h1 : ‖ζ‖ ^ (s - 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) (le_of_lt hζ)
        calc
          ‖ζ‖ ^ s = ‖ζ‖ * ‖ζ‖ ^ (s - 1) := by
            rw [← pow_pred_mul hs ‖ζ‖]
            ring
          _ ≤ ‖ζ‖ := by
            calc
              ‖ζ‖ * ‖ζ‖ ^ (s - 1) ≤ ‖ζ‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg ζ)
              _ = ‖ζ‖ := by rw [mul_one]
  have hre2 : -‖ζ ^ s‖ ≤ (ζ ^ s).re := by
    have h := Complex.re_le_norm (-(ζ ^ s))
    have h' : -(ζ ^ s).re ≤ ‖ζ ^ s‖ := by simpa using h
    linarith
  have hone : (1 : ℂ).re = 1 := by simp
  have hpos : 0 < 1 - ‖ζ‖ := sub_pos.mpr hζ
  calc
    0 < 1 - ‖ζ‖ := hpos
    _ ≤ 1 - ‖ζ ^ s‖ := by linarith
    _ ≤ (1 + ζ ^ s).re := by
      rw [Complex.add_re, hone]
      linarith

/-- The argument of `1 + ζ^s` is bounded by `π/2` in absolute value on the
unit disk (its real part is positive). -/
lemma one_add_pow_arg_bound {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    |(1 + ζ ^ s).arg| < Real.pi / 2 := by
  have hre : 0 < (1 + ζ ^ s).re := one_add_pow_re_pos hs hζ
  rw [abs_lt]
  constructor
  · -- -(π/2) < arg z
    exact (Complex.neg_pi_div_two_lt_arg_iff (z := 1 + ζ ^ s)).2 (Or.inl hre)
  · -- arg z < π/2
    exact (Complex.arg_lt_pi_div_two_iff (z := 1 + ζ ^ s)).2 (Or.inl hre)

/-- Power-law step used by the power identity: on the unit disk
`((1+ζ^s)^{−2/s})^s = (1+ζ^s)^{−2}` (principal powers agree here because
`Re(1+ζ^s) > 0` keeps the intermediate arguments inside the principal
range). -/
lemma one_add_pow_cpow_pow {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ((1 + ζ ^ s) ^ (-slitExponent s)) ^ s = (1 + ζ ^ s) ^ (-2 : ℂ) := by
  have hB : (1 + ζ ^ s : ℂ) ≠ 0 := one_add_pow_ne_zero hs hζ
  have harg : |(1 + ζ ^ s).arg| < Real.pi / 2 := one_add_pow_arg_bound hs hζ
  let e : ℂ := slitExponent s
  let r : ℝ := (2 : ℝ) / (s : ℝ)
  have hr : r = (2 : ℝ) / (s : ℝ) := rfl
  have he : e = (2 : ℂ) / (s : ℂ) := rfl
  -- (log B · (−e)).im = arg B · (−r)
  have hval : (Complex.log (1 + ζ ^ s) * (-e)).im = (1 + ζ ^ s).arg * (-r) := by
    rw [hr]; rw [he]
    simp [Complex.mul_im, Complex.log_im]
  -- |arg B · (−r)| < π  (since |arg B| < π/2 and r = 2/s ≤ 2)
  have h2r : 0 < r := by
    unfold r
    positivity
  have hrle : r ≤ 2 := by
    unfold r
    have hsRpos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hs)
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    rw [div_le_iff₀ hsRpos]
    nlinarith
  have hbm : |(1 + ζ ^ s).arg * (-r)| < Real.pi := by
    have habs : |(1 + ζ ^ s).arg * (-r)| = r * |(1 + ζ ^ s).arg| := by
      rw [abs_mul, abs_neg, abs_of_nonneg (le_of_lt h2r)]
      ring
    rw [habs]
    calc
      r * |(1 + ζ ^ s).arg| < r * (Real.pi / 2) := mul_lt_mul_of_pos_left harg h2r
      _ ≤ Real.pi := by
        have : r * (Real.pi / 2) = (r / 2) * Real.pi := by ring
        rw [this]
        have hr2 : r / 2 ≤ 1 := by
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa using hrle)
        calc
          (r / 2) * Real.pi ≤ 1 * Real.pi := mul_le_mul_of_nonneg_right hr2 Real.pi_nonneg
          _ = Real.pi := by rw [one_mul]
  -- exponent cpow_mul conditions
  have hcond1 : -Real.pi < (Complex.log (1 + ζ ^ s) * (-e)).im := by
    rw [hval]
    exact (abs_lt.mp hbm).1
  have hcond2 : (Complex.log (1 + ζ ^ s) * (-e)).im ≤ Real.pi := by
    rw [hval]
    exact le_of_lt (abs_lt.mp hbm).2
  have hmul := Complex.cpow_mul (x := (1 + ζ ^ s : ℂ)) (y := -e) (s : ℂ) hcond1 hcond2
  -- exponent arithmetic: (−e)·(s:ℂ) = −2
  have hExp : (-e) * (s : ℂ) = (-2 : ℂ) := by
    have hes : e * (s : ℂ) = (2 : ℂ) := by
      unfold e
      rw [mul_comm]
      exact cast_mul_slitExponent hs
    calc
      (-e) * (s : ℂ) = -(e * (s : ℂ)) := by ring
      _ = -(2 : ℂ) := by rw [hes]
  -- assemble
  calc
    ((1 + ζ ^ s) ^ (-e)) ^ s = ((1 + ζ ^ s) ^ (-e)) ^ ((s : ℂ)) := by
      rw [← Complex.cpow_natCast]
    _ = (1 + ζ ^ s) ^ ((-e) * (s : ℂ)) := hmul.symm
    _ = (1 + ζ ^ s) ^ (-2 : ℂ) := by rw [hExp]


/-- The POWER IDENTITY on the unit disk: `f_s(ζ)^s = f_1(ζ^s)` (the s-fold
lift of the one-slit map), i.e. `(regSlit s ζ)^s = oneSlit (ζ^s)` with
`oneSlit(u) = 4u/(1+u)²`.  Proof: expand `regSlit` by `regSlit_eq_neg_pow`,
distribute the s-th power, and use `slitCoef_pow` (coefficient ^s = 4) and
`one_add_pow_cpow_pow` ((1+ζ^s)^{−2/s})^s = (1+ζ^s)^{−2}. -/
theorem regSlit_pow {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    (regSlit s ζ) ^ s = oneSlit (ζ ^ s) := by
  have hB : (1 + ζ ^ s : ℂ) ≠ 0 := one_add_pow_ne_zero hs hζ
  have hneg : (1 + ζ ^ s) ^ (-2 : ℂ) = ((1 + ζ ^ s) ^ 2)⁻¹ := by
    rw [Complex.cpow_neg]
    congr 1
    norm_num
  calc
    (regSlit s ζ) ^ s = (slitCoef s * (ζ * (1 + ζ ^ s) ^ (-slitExponent s))) ^ s := by
      rw [regSlit_eq_neg_pow]
    _ = slitCoef s ^ s * (ζ * (1 + ζ ^ s) ^ (-slitExponent s)) ^ s := by
      rw [mul_pow]
    _ = slitCoef s ^ s * (ζ ^ s * ((1 + ζ ^ s) ^ (-slitExponent s)) ^ s) := by
      rw [mul_pow]
    _ = 4 * (ζ ^ s * ((1 + ζ ^ s) ^ (-slitExponent s)) ^ s) := by
      rw [slitCoef_pow hs]
    _ = 4 * (ζ ^ s * (1 + ζ ^ s) ^ (-2 : ℂ)) := by
      rw [one_add_pow_cpow_pow hs hζ]
    _ = oneSlit (ζ ^ s) := by
      unfold oneSlit
      rw [hneg]
      -- 4·(ζ^s·(B²)⁻¹) = 4·ζ^s/(1+ζ^s)²
      ring_nf


/-! ### Part 3: f_s maps the unit disk into the radial-slit domain

`oneSlit` (= f_1) avoids the slit [1,∞) on the unit disk; by the power
identity so does f_s (its s-th power stays in ℂ∖[1,∞)), which is exactly
the statement that f_s(𝔻) ⊆ D_s where D_s = {w : w^s ∉ [1,∞)} is the
equiangular s-slit domain (`rayAvoiding s`). -/

/-- The square of a complex number lies on the nonpositive real axis only
if the number itself has zero real part. -/
lemma sq_re_zero_of_sq_mem_nonpos {w : ℂ}
    (hw : ((w ^ 2 : ℂ)).im = 0 ∧ ((w ^ 2 : ℂ)).re ≤ 0) : w.re = 0 := by
  have h2re : ((w * w : ℂ).re) ≤ 0 := by
    simpa [pow_two] using hw.2
  have hc : w.re ^ 2 - w.im ^ 2 = (w * w).re := by
    rw [Complex.mul_re]
    ring
  have hre' : w.re ^ 2 - w.im ^ 2 ≤ 0 := by
    rw [hc]
    exact h2re
  have h2im : ((w * w : ℂ).im) = 0 := by
    simpa [pow_two] using hw.1
  have hci : 2 * w.re * w.im = (w * w).im := by
    rw [Complex.mul_im]
    ring
  have him' : 2 * w.re * w.im = 0 := by
    rw [hci]
    exact h2im
  by_cases hy : w.im = 0
  · -- im = 0: re² ≤ 0 forces re = 0
    have hx2 : w.re ^ 2 ≤ 0 := by
      have : w.re ^ 2 - w.im ^ 2 ≤ 0 := hre'
      simpa [hy] using this
    have hx2eq : w.re ^ 2 = 0 := le_antisymm hx2 (sq_nonneg w.re)
    exact sq_eq_zero_iff.mp hx2eq
  · -- im ≠ 0: 2·re·im = 0 gives re = 0
    have hxy : w.re * w.im = 0 := by
      nlinarith [him']
    exact (mul_eq_zero.mp hxy).resolve_right hy

/-- Cayley-type map `(1−u)/(1+u)`, used to write `oneSlit u = 1 − cayley(u)²`
and to control its real part on the unit disk. -/
def cayley (u : ℂ) : ℂ := (1 - u) / (1 + u)

/-- `oneSlit u = 1 − cayley(u)²` on the unit disk (i.e. wherever `1+u ≠ 0`). -/
lemma oneSlit_eq_one_sub_cayley_sq {u : ℂ} (hden : 1 + u ≠ 0) :
    oneSlit u = 1 - (cayley u) ^ 2 := by
  unfold oneSlit cayley
  field_simp [hden]
  ring

/-- The real part of the Cayley map is positive on the unit disk:
`Re((1−u)/(1+u)) = (1−‖u‖²)/|1+u|² > 0`. -/
lemma cayley_re_pos {u : ℂ} (hu : ‖u‖ < 1) : 0 < (cayley u).re := by
  unfold cayley
  have hden : (1 + u : ℂ) ≠ 0 := by
    intro hz
    have hz' : u + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  rw [Complex.div_re]
  -- numerator: (1−u.re)(1+u.re) + (−u.im)(u.im) = 1 − normSq u
  have hnum : (1 - u).re * (1 + u).re + (1 - u).im * (1 + u).im = 1 - Complex.normSq u := by
    simp [Complex.normSq_apply]
    ring
  -- denominator normSq(1+u) = |1+u|² > 0
  have hdenSq : 0 < Complex.normSq (1 + u) := by
    have hn : ‖1 + u‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hden)
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_ne_zero hn
  have hnumpos : 0 < 1 - Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    have hs : ‖u‖ ^ 2 < 1 := (sq_lt_one_iff₀ (norm_nonneg u)).2 hu
    linarith
  have hdnz : Complex.normSq (1 + u) ≠ 0 := ne_of_gt hdenSq
  have hcomb : ((1 - u).re * (1 + u).re) / Complex.normSq (1 + u) +
        ((1 - u).im * (1 + u).im) / Complex.normSq (1 + u) =
        (1 - Complex.normSq u) / Complex.normSq (1 + u) := by
    field_simp [hdnz]
    rw [hnum]
  rw [hcomb]
  exact div_pos hnumpos hdenSq


/-- `oneSlit` (= f_1) avoids the slit [1,∞) on the unit disk:
`oneSlit u ∉ [1,∞)` for ‖u‖ < 1.  (Cayley form: oneSlit u = 1 − w² with
`w := (1−u)/(1+u)` of positive real part; a value in [1,∞) would force
`w² ≤ 0` real, i.e. `w.re = 0`, contradiction.) -/
lemma one_slit_avoid {u : ℂ} (hu : ‖u‖ < 1) :
    ¬(((oneSlit u).im = 0) ∧ 1 ≤ (oneSlit u).re) := by
  intro h
  have hden : (1 + u : ℂ) ≠ 0 := by
    intro hz
    have hz' : u + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hid := oneSlit_eq_one_sub_cayley_sq (u := u) hden
  have hw2 : (cayley u) ^ 2 = 1 - oneSlit u := by
    rw [hid]
    ring
  have h1 : (1 - oneSlit u).im = 0 := by
    simp [h.1]
  have h2 : (1 - oneSlit u).re ≤ 0 := by
    rw [Complex.sub_re]
    simp
    linarith [h.2]
  have hwcond : (((cayley u) ^ 2 : ℂ)).im = 0 ∧ (((cayley u) ^ 2 : ℂ)).re ≤ 0 := by
    rw [hw2]
    exact ⟨h1, h2⟩
  have hwre : (cayley u).re = 0 := sq_re_zero_of_sq_mem_nonpos hwcond
  have hpos : 0 < (cayley u).re := cayley_re_pos hu
  linarith

/-- The equiangular s-slit domain: `D_s := {w | w^s ∉ [1,∞)}`, i.e. the
complement of the s rays `{x·e^{2πik/s} : x ≥ 1, k < s}` (see
`rayAvoiding_eq_compl_rays`, to be proved).  Contains the open unit disk. -/
def rayAvoiding (s : ℕ) : Set ℂ := {w | ¬(((w ^ s).im = 0) ∧ 1 ≤ (w ^ s).re)}

/-- The regular slit map sends the unit disk into the equiangular s-slit
domain: `f_s(𝔻) ⊆ D_s` (by the power identity, its s-th power stays in
ℂ∖[1,∞) — the avoidance of the one-slit map). -/
theorem regSlit_mapsTo_rayAvoiding (s : ℕ) (hs : 1 ≤ s) :
    MapsTo (regSlit s) (ball (0 : ℂ) 1) (rayAvoiding s) := by
  intro ζ hζ
  have hζn : ‖ζ‖ < 1 := by
    simpa [dist_eq_norm, sub_zero] using (Metric.mem_ball.mp hζ)
  have hpow := regSlit_pow hs hζn
  have hnorm : ‖ζ ^ s‖ < 1 := by
    calc
      ‖ζ ^ s‖ = ‖ζ‖ ^ s := by exact norm_pow ζ s
      _ ≤ ‖ζ‖ := by
        have h1 : ‖ζ‖ ^ (s - 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) (le_of_lt hζn)
        calc
          ‖ζ‖ ^ s = ‖ζ‖ * ‖ζ‖ ^ (s - 1) := by
            rw [← pow_pred_mul hs ‖ζ‖]
            ring
          _ ≤ ‖ζ‖ := by
            calc
              ‖ζ‖ * ‖ζ‖ ^ (s - 1) ≤ ‖ζ‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg ζ)
              _ = ‖ζ‖ := by rw [mul_one]
      _ < 1 := hζn
  intro h
  rw [hpow] at h
  exact one_slit_avoid (u := ζ ^ s) hnorm h


/-! ### Part 4: f_s is an analytic self-map of the unit disk into D_s with
the sharp initial derivative — the dual inequality in map form

`rad(D_s, 0)` (the conformal radius at 0 of the equiangular s-slit domain,
defined as the supremum of ‖f'(0)‖ over analytic f: 𝔻 → D_s with f(0)=0)
is at least `4^{1/s}`: the map `f_s` realises this value, is analytic on
the unit disk, fixes 0, and maps 𝔻 into D_s (`regSlit_mapsTo_rayAvoiding`).
-/

/-- `f_s(0) = 0`. -/
lemma regSlit_zero (s : ℕ) : regSlit s 0 = 0 := by
  unfold regSlit
  simp

/-- `f_s` is analytic (complex-differentiable) on the open unit disk. -/
lemma regSlit_differentiableOn (s : ℕ) (hs : 1 ≤ s) :
    DifferentiableOn ℂ (regSlit s) (ball (0 : ℂ) 1) := by
  intro ζ hζ
  have hζn : ‖ζ‖ < 1 := by
    simpa [dist_eq_norm, sub_zero] using (Metric.mem_ball.mp hζ)
  have hslit : 1 + ζ ^ s ∈ Complex.slitPlane := one_add_pow_mem_slitPlane hs hζn
  -- g(w) := 1 + w^s is differentiable at ζ (polynomial)
  have hp : DifferentiableAt ℂ (fun w : ℂ => w ^ s) ζ := by
    exact (hasDerivAt_pow s ζ).differentiableAt
  have hg : DifferentiableAt ℂ (fun w : ℂ => 1 + w ^ s) ζ := by
    simpa [add_comm] using (differentiableAt_const.add hp)
  -- (1 + w^s)^(−e) differentiable at ζ (cpow with base in slitPlane)
  have hg' : DifferentiableAt ℂ (fun w : ℂ => (1 + w ^ s) ^ (-slitExponent s)) ζ := by
    exact hg.cpow_const hslit
  -- w ↦ w·(1+w^s)^{−e} differentiable at ζ
  have hmul : DifferentiableAt ℂ (fun w : ℂ => w * (1 + w ^ s) ^ (-slitExponent s)) ζ := by
    exact (differentiableAt_id.mul hg')
  -- regSlit = C · (w·(1+w^s)^{−e}) pointwise: congr
  have hEv : (fun w : ℂ => regSlit s w) =ᶠ[𝓝 ζ]
      (fun w : ℂ => slitCoef s * (w * (1 + w ^ s) ^ (-slitExponent s))) := by
    exact Filter.Eventually.of_forall (fun w => regSlit_eq_neg_pow s w)
  have hmain : DifferentiableAt ℂ (fun w : ℂ => regSlit s w) ζ :=
    DifferentiableAt.congr_of_eventuallyEq (hmul.const_mul (slitCoef s)) hEv
  exact hmain.differentiableWithinAt

/-- The map-form dual inequality for the equiangular case: the equiangular
s-slit domain `D_s` admits an analytic map of the unit disk fixing 0,
with derivative `4^{1/s}` at 0, whose image lies in `D_s`.  In particular
any conformal-radius definition as a supremum of such ‖f'(0)‖ is
`≥ 4^{1/s}` for `D_s`. -/
theorem equiangular_dual_lower (s : ℕ) (hs : 1 ≤ s) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (0 : ℂ) 1) ∧ f 0 = 0 ∧
      MapsTo f (ball (0 : ℂ) 1) (rayAvoiding s) ∧
      ‖deriv f 0‖ = (4 : ℝ) ^ (1 / (s : ℝ)) := by
  refine ⟨regSlit s, regSlit_differentiableOn s hs, regSlit_zero s,
    regSlit_mapsTo_rayAvoiding s hs, ?_⟩
  exact regSlit_deriv_zero_norm hs


/-! ### Part 5: surjectivity of oneSlit onto ℂ∖[1,∞) — s = 1 image theorem

For v ∉ [1,∞) (i.e. ¬(v.im = 0 ∧ 1 ≤ v.re)): x := 1 − v ∈ slitPlane;
y := √x has positive real part (explicit: √x = exp(log x/2), so
Re √x = exp(log‖x‖/2)·cos(arg x/2) > 0); u := (1−y)/(1+y) has ‖u‖ < 1
(Re y > 0) and oneSlit u = 1 − cayley(u)² = 1 − y² = v.  So oneSlit is
surjective from the unit disk onto ℂ∖[1,∞). -/

/-- If `¬(v.im = 0 ∧ 1 ≤ v.re)` then `1 − v` lies in the slit plane (the
complement of the nonpositive real axis). -/
lemma one_sub_mem_slitPlane_of_not_real_ge {v : ℂ}
    (hv : ¬((v.im = 0) ∧ 1 ≤ v.re)) : 1 - v ∈ Complex.slitPlane := by
  change 0 < (1 - v).re ∨ (1 - v).im ≠ 0
  by_cases hre : 0 < (1 - v).re
  · exact Or.inl hre
  · right
    intro him
    have hrele : (1 - v).re ≤ 0 := le_of_not_gt hre
    have him' : -(v.im) = 0 := by
      have : (1 - v).im = 0 - v.im := by rw [Complex.sub_im, Complex.one_im]
      rw [this] at him
      simpa using him
    have hv0 : v.im = 0 := by linarith
    have hre1 : 1 ≤ v.re := by
      have : (1 - v).re = 1 - v.re := by rw [Complex.sub_re, Complex.one_re]
      rw [this] at hrele
      linarith
    exact hv ⟨hv0, hre1⟩

/-- Absolute value of the argument is < π/2 whenever the real part is
positive. -/
lemma re_pos_arg_abs_lt_pi_div_two {x : ℂ} (hx : 0 < x.re) :
    |x.arg| < Real.pi / 2 := by
  rw [abs_lt]
  constructor
  · exact (Complex.neg_pi_div_two_lt_arg_iff (z := x)).2 (Or.inl hx)
  · exact (Complex.arg_lt_pi_div_two_iff (z := x)).2 (Or.inl hx)

/-- Square root of a slit-plane point has positive real part (the branch
`√x = exp(log x/2)` has `Re = exp(log‖x‖/2)·cos(arg x/2) > 0`). -/
lemma sqrt_re_pos_of_slitPlane {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    0 < (Complex.sqrt x).re := by
  have hx0 : x ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hx).2
  have hxarg : x.arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp hx).1
  rw [sqrt_eq_exp hx0]
  rw [Complex.exp_re]
  -- (log x / 2).re = (log x).re / 2 ; (log x / 2).im = x.arg / 2
  have hlre : ((Complex.log x) / 2).re = (Complex.log x).re / 2 := by
    rw [Complex.div_re]
    norm_num [Complex.normSq_apply]
    ring
  have hlim : ((Complex.log x) / 2).im = x.arg / 2 := by
    rw [Complex.div_im]
    norm_num [Complex.normSq_apply]
    simp [Complex.log_im]
    ring
  rw [hlre, hlim]
  -- cos(arg x / 2) > 0 : arg x ∈ (−π,π) since ≠ π
  have harglo : -Real.pi < x.arg := (Complex.arg_mem_Ioc x).1
  have hargle : x.arg ≤ Real.pi := (Complex.arg_mem_Ioc x).2
  have harglt : x.arg < Real.pi := lt_of_le_of_ne hargle hxarg
  have hcospos : 0 < Real.cos (x.arg / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith
  -- exp((log x).re/2) > 0
  have hexppos : 0 < Real.exp ((Complex.log x).re / 2) := Real.exp_pos _
  exact mul_pos hexppos hcospos

/-- The inverse-Cayley point `(1−y)/(1+y)` lies in the unit disk whenever
`Re y > 0`: `|1−y| < |1+y|`. -/
lemma norm_div_one_sub_lt_one_of_re_pos {y : ℂ} (hy : 0 < y.re) :
    ‖(1 - y) / (1 + y)‖ < 1 := by
  have hden : (1 + y : ℂ) ≠ 0 := by
    intro hz
    have hre : (1 + y).re = 0 := by rw [hz]; simp
    have : (1 + y).re = 1 + y.re := by rw [Complex.add_re, Complex.one_re]
    rw [this] at hre
    linarith
  have hdennz : ‖1 + y‖ ≠ 0 := by
    exact (norm_ne_zero_iff.mpr hden)
  have hnn : 0 ≤ ‖1 - y‖ := norm_nonneg _
  -- square comparison: ‖1−y‖² < ‖1+y‖² ⟺ (1−y.re)²+y.im² < (1+y.re)²+y.im² ⟺ 4·y.re > 0
  have hsq : ‖1 - y‖ ^ 2 < ‖1 + y‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    nlinarith [hy]
  have hmain : ‖1 - y‖ < ‖1 + y‖ :=
    (sq_lt_sq₀ (norm_nonneg (1 - y)) (norm_nonneg (1 + y))).1 hsq
  -- divide by ‖1+y‖ > 0
  have hdiv : ‖1 - y‖ / ‖1 + y‖ < 1 := by
    rw [div_lt_one₀ (norm_pos_iff.mpr hden)]
    exact hmain
  -- ‖(1−y)/(1+y)‖ = ‖1−y‖/‖1+y‖
  simpa [norm_div] using hdiv

/-- `cayley ((1−y)/(1+y)) = y` wherever `1+y ≠ 0`. -/
lemma cayley_div_eq {y : ℂ} (hden : 1 + y ≠ 0) : cayley ((1 - y) / (1 + y)) = y := by
  unfold cayley
  field_simp [hden]
  ring


/-- **s = 1 surjectivity**: `oneSlit` maps the unit disk ONTO ℂ∖[1,∞).
For v outside the slit, `u := (1−√(1−v))/(1+√(1−v))` lies in the disk and
`oneSlit u = v` (Cayley form: y := √(1−v) has Re > 0, |u| < 1, and
oneSlit u = 1 − cayley(u)² = 1 − y² = v). -/
theorem one_slit_surj {v : ℂ} (hv : ¬((v.im = 0) ∧ 1 ≤ v.re)) :
    ∃ u : ℂ, ‖u‖ < 1 ∧ oneSlit u = v := by
  let x : ℂ := 1 - v
  have hxsp : x ∈ Complex.slitPlane := one_sub_mem_slitPlane_of_not_real_ge hv
  let y : ℂ := Complex.sqrt x
  have hyre : 0 < y.re := by
    dsimp [y]
    exact sqrt_re_pos_of_slitPlane hxsp
  let u : ℂ := (1 - y) / (1 + y)
  have hun : ‖u‖ < 1 := by
    dsimp [u]
    exact norm_div_one_sub_lt_one_of_re_pos hyre
  have h1py : (1 + y : ℂ) ≠ 0 := by
    intro hz
    have hre : (1 + y).re = 0 := by rw [hz]; simp
    have : (1 + y).re = 1 + y.re := by rw [Complex.add_re, Complex.one_re]
    rw [this] at hre
    linarith
  have h1pu : (1 + u : ℂ) ≠ 0 := by
    intro hz
    have hz' : u + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hcu : cayley u = y := by
    dsimp [u]
    exact cayley_div_eq (y := y) h1py
  have hy2 : y ^ 2 = x := by
    dsimp [y]
    have hx0 : x ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hxsp).2
    rw [sqrt_eq_exp hx0]
    have h := Complex.exp_nat_mul (Complex.log x / 2) 2
    rw [← h]
    have hz2 : ((2 : ℕ) : ℂ) * (Complex.log x / 2) = Complex.log x := by ring
    rw [hz2, Complex.exp_log hx0]
  have hu2 : oneSlit u = v := by
    have hid := oneSlit_eq_one_sub_cayley_sq (u := u) h1pu
    calc
      oneSlit u = 1 - (cayley u) ^ 2 := hid
      _ = 1 - y ^ 2 := by rw [hcu]
      _ = 1 - x := by rw [hy2]
      _ = v := by
        dsimp [x]
        ring
  refine ⟨u, hun, hu2⟩


/-! ### Part 6: surjectivity of f_s onto D_s

Given w with w^s ∉ [1,∞): v := w^s has a one-slit preimage u ∈ 𝔻
(one_slit_surj).  Take ζ₀ := exp(log u / s) (an s-th root of u inside the
disk), ω := w / f_s(ζ₀) (an s-th root of unity: ω^s = 1 because
f_s(ζ₀)^s = oneSlit(ζ₀^s) = oneSlit u = v = w^s).  Then ζ := ζ₀·ω satisfies
ζ^s = u, ‖ζ‖ < 1 (‖ω‖ = 1), and f_s(ζ) = ω·f_s(ζ₀) = w.  Hence
f_s(𝔻) ⊇ D_s; together with `regSlit_mapsTo_rayAvoiding` this gives
`f_s(𝔻) = D_s` (the set image of the unit disk under f_s is the
equiangular s-slit domain). -/

/-- A unit complex number whose s-th power is 1 has norm 1 (s ≥ 1). -/
lemma norm_eq_one_of_pow_eq_one {s : ℕ} (hs : 1 ≤ s) {ω : ℂ} (h : ω ^ s = 1) :
    ‖ω‖ = 1 := by
  have hns : ‖ω‖ ^ s = 1 := by
    rw [← norm_pow, h, norm_one]
  have hs0 : s ≠ 0 := by omega
  by_cases hlt : ‖ω‖ < 1
  · have : ‖ω‖ ^ s < 1 := pow_lt_one₀ (norm_nonneg ω) hlt hs0
    rw [hns] at this
    norm_num at this
  · have hle : 1 ≤ ‖ω‖ := le_of_not_gt hlt
    by_cases hgt : 1 < ‖ω‖
    · have : 1 < ‖ω‖ ^ s := one_lt_pow₀ hgt hs0
      rw [hns] at this
      norm_num at this
    · exact le_antisymm (le_of_not_gt hgt) hle

/-- An s-th root of u in the unit disk: `exp (log u / s)` has s-th power u
and norm < 1 whenever 0 < ‖u‖ < 1. -/
lemma exp_log_div_nat_pow {s : ℕ} (hs : 1 ≤ s) {u : ℂ} (hu0 : u ≠ 0) :
    (Complex.exp (Complex.log u / (s : ℂ))) ^ s = u := by
  have h := Complex.exp_nat_mul (Complex.log u / (s : ℂ)) s
  rw [← h]
  have hz : ((s : ℕ) : ℂ) * (Complex.log u / (s : ℂ)) = Complex.log u := by
    have hsC : (s : ℂ) ≠ 0 := cast_ne_zero hs
    field_simp [hsC]
  rw [hz, Complex.exp_log hu0]

/-- `‖exp (log u / s)‖ < 1` for 0 < ‖u‖ < 1. -/
lemma norm_exp_log_div_nat_lt_one {s : ℕ} (hs : 1 ≤ s) {u : ℂ}
    (hu0 : u ≠ 0) (hu1 : ‖u‖ < 1) :
    ‖Complex.exp (Complex.log u / (s : ℂ))‖ < 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.log u / (s : ℂ)).re = Real.log ‖u‖ / (s : ℝ) := by
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))
    rw [Complex.div_re]
    simp [Complex.log_re, Complex.normSq_apply]
    field_simp [hsR]
  rw [hre]
  have hxpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have he : Real.exp (Real.log ‖u‖) < Real.exp (0 : ℝ) := by
    rw [Real.exp_log hxpos, Real.exp_zero]
    exact hu1
  have hloglt : Real.log ‖u‖ < 0 := Real.exp_lt_exp.mp he
  have hsRpos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hs)
  have hdivlt : Real.log ‖u‖ / (s : ℝ) < 0 := by
    exact (div_lt_iff₀ hsRpos).2 (by simpa using hloglt)
  have hfinal : Real.exp (Real.log ‖u‖ / (s : ℝ)) < Real.exp (0 : ℝ) :=
    Real.exp_lt_exp.mpr hdivlt
  simpa [Real.exp_zero] using hfinal
/-- **Surjectivity of f_s onto D_s**: every point of the equiangular s-slit
domain is attained by f_s at some point of the unit disk. -/
theorem regSlit_surj (s : ℕ) (hs : 1 ≤ s) {w : ℂ} (hw : w ∈ rayAvoiding s) :
    ∃ ζ : ℂ, ‖ζ‖ < 1 ∧ regSlit s ζ = w := by
  classical
  by_cases hw0 : w = 0
  · -- w = 0 is attained at ζ = 0
    refine ⟨0, by norm_num, ?_⟩
    simpa [hw0] using (regSlit_zero s)
  · -- w ≠ 0: v := w^s, one-slit preimage u, s-th root ζ0, root of unity ω
    let v : ℂ := w ^ s
    have hv : ¬((v.im = 0) ∧ 1 ≤ v.re) := by
      dsimp [v, rayAvoiding] at hw ⊢
      exact hw
    rcases one_slit_surj (v := v) hv with ⟨u, hu1, hu2⟩
    by_cases hu0 : u = 0
    · -- u = 0 would force w^s = oneSlit 0 = 0, i.e. w = 0
      have hone0 : oneSlit (0 : ℂ) = 0 := by
        unfold oneSlit
        norm_num
      have hv0 : v = 0 := by
        rw [← hu2, hu0, hone0]
      have hws0 : w ^ s = 0 := by
        simpa [v] using hv0
      have hn : ‖w‖ ^ s = 0 := by
        rw [← norm_pow, hws0, norm_zero]
      have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      have hns : ‖w‖ ^ s ≠ 0 := pow_ne_zero s hwn
      exact False.elim (hns hn)
    · -- u ≠ 0
      let ζ0 : ℂ := Complex.exp (Complex.log u / (s : ℂ))
      have hζ0pow : ζ0 ^ s = u := by
        dsimp [ζ0]
        exact exp_log_div_nat_pow hs hu0
      have hζ0n : ‖ζ0‖ < 1 := by
        dsimp [ζ0]
        exact norm_exp_log_div_nat_lt_one hs hu0 hu1
      -- f_s(ζ0)^s = oneSlit(ζ0^s) = oneSlit u = w^s
      have hfs : regSlit s ζ0 ^ s = w ^ s := by
        rw [regSlit_pow hs hζ0n, hζ0pow, hu2]
      have hfζ0ne : regSlit s ζ0 ≠ 0 := by
        intro hz
        have hfs0 : regSlit s ζ0 ^ s = 0 := by
          rw [hz]
          exact zero_pow (by omega : s ≠ 0)
        have hwsp : w ^ s ≠ 0 := pow_ne_zero s hw0
        rw [hfs] at hfs0
        exact hwsp hfs0
      let ω : ℂ := w / regSlit s ζ0
      have hωpow : ω ^ s = 1 := by
        dsimp [ω]
        rw [div_pow, hfs]
        exact div_self (pow_ne_zero s hw0)
      have hωn : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_one hs hωpow
      let ζ : ℂ := ζ0 * ω
      have hζn : ‖ζ‖ < 1 := by
        dsimp [ζ]
        rw [norm_mul, hωn, mul_one]
        exact hζ0n
      -- f_s(ζ) = ω·f_s(ζ0): the factors (1+(ζ0ω)^s) and (1+ζ0^s) coincide
      have hfac : regSlit s ζ = ω * regSlit s ζ0 := by
        unfold regSlit
        dsimp [ζ]
        rw [show (ζ0 * ω) ^ s = ζ0 ^ s by
          rw [mul_pow, hωpow, mul_one]]
        have hbne : (1 + ζ0 ^ s : ℂ) ≠ 0 := by
          have h1u : (1 + u : ℂ) ≠ 0 := by
            intro hz
            have hz' : u + 1 = 0 := by simpa [add_comm] using hz
            have hu' : u = -1 := eq_neg_of_add_eq_zero_left hz'
            have hn1 : ‖u‖ = 1 := by
              rw [hu', norm_neg, norm_one]
            linarith
          rw [hζ0pow]
          exact h1u
        have hbpow : (1 + ζ0 ^ s : ℂ) ^ slitExponent s ≠ 0 := by
          rw [Complex.cpow_ne_zero_iff]
          exact Or.inl hbne
        field_simp [hbpow]
      have hmain : regSlit s ζ = w := by
        rw [hfac]
        dsimp [ω]
        exact div_mul_cancel₀ w hfζ0ne
      refine ⟨ζ, hζn, hmain⟩



/-! ### Part 7: the image theorem — f_s(𝔻) = D_s

Combining the inclusion (`regSlit_mapsTo_rayAvoiding`: f_s maps the unit
disk into D_s) with the surjectivity (`regSlit_surj`: D_s ⊆ f_s(𝔻)) gives
the geometric characterization: the image of the open unit disk under f_s
is exactly the equiangular s-slit domain `rayAvoiding s`. -/

/-- **Image theorem**: `f_s` maps the open unit disk ONTO the equiangular
s-slit domain: `(regSlit s) '' (ball 0 1) = rayAvoiding s`. -/
theorem regSlit_image_eq_rayAvoiding (s : ℕ) (hs : 1 ≤ s) :
    (regSlit s) '' (ball (0 : ℂ) 1) = rayAvoiding s := by
  ext w
  constructor
  · -- image ⊆ rayAvoiding: by the MapsTo property
    intro hw
    rcases hw with ⟨ζ, hζ, rfl⟩
    exact regSlit_mapsTo_rayAvoiding s hs hζ
  · -- rayAvoiding ⊆ image: by surjectivity
    intro hw
    rcases regSlit_surj s hs hw with ⟨ζ, hζn, hζeq⟩
    refine ⟨ζ, ?_, hζeq⟩
    simpa [dist_eq_norm, sub_zero] using hζn


/-! ### Part 8: the k-indexed ray description of D_s

`unitRoot s k := exp(2πk·I/s)` is the k-th s-th root of unity, and
`raySet s := ⋃_{k<s} {x·unitRoot s k : x ≥ 1}` is the union of the s rays
from the unit circle.  This part proves the two-way correspondence
`w^s ∈ [1,∞) ⟺ w ∈ raySet s`, giving
`rayAvoiding s = ℂ ∖ raySet s`.  The converse (the content) classifies
s-th roots of unity through the argument-as-Angle group:
`s • (arg u : Angle) = 0` (from u^s = 1 by `arg_pow_coe_angle`) and
`Real.Angle.nsmul_eq_iff` gives `(arg u : Angle) = (2πk/s : Angle)` with
`k : Fin s`; the polar identity `‖u‖·exp(arg u·I) = u` then yields
`u = unitRoot s k`. -/

/-- `2π·k` (the real arc length of k full turns). -/
def twoPiMul (k : ℕ) : ℝ := (2 : ℝ) * Real.pi * (k : ℝ)

/-- The real coefficient `2πk/s` of the k-th root of unity. -/
def unitRootReal (s : ℕ) (k : ℕ) : ℝ := (twoPiMul k) / (s : ℝ)

/-- The k-th s-th root of unity `exp(2πk·I/s)` (k : ℕ).  (Convention: the
real coefficient `unitRootReal s k` is coerced to ℂ as a single term
before multiplying by `I`, so exp-arguments have a uniform shape.) -/
def unitRoot (s : ℕ) (k : ℕ) : ℂ :=
  Complex.exp ((unitRootReal s k : ℂ) * Complex.I)

/-- The union of the s rays from the unit circle in the equiangular
directions: `raySet s := ⋃_{k<s} {x·unitRoot s k : x ≥ 1}`. -/
def raySet (s : ℕ) : Set ℂ :=
  {w | ∃ k : ℕ, k < s ∧ ∃ x : ℝ, 1 ≤ x ∧ w = (x : ℂ) * unitRoot s k}

/-- `exp (2πk·I) = 1` for every natural k (periodicity of exp over 2π). -/
lemma exp_two_pi_nat_mul_I (k : ℕ) :
    Complex.exp ((twoPiMul k : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_mul_I]
  have hx : twoPiMul k = (k : ℝ) * (2 * Real.pi) := by
    dsimp [twoPiMul]
    ring
  have hc : Complex.cos (twoPiMul k : ℂ) = 1 := by
    rw [← Complex.ofReal_cos, hx, Real.cos_nat_mul_two_pi]
    norm_num
  have hs : Complex.sin (twoPiMul k : ℂ) = 0 := by
    have hk : (k : ℝ) * (2 * Real.pi) = ((2 * (k : ℤ) : ℤ) : ℝ) * Real.pi := by
      norm_num
      ring
    rw [← Complex.ofReal_sin, hx, hk, Real.sin_int_mul_pi]
    norm_num
  rw [hc, hs]
  norm_num

/-- `2π·j` for an integer j. -/
def twoPiMulZ (j : ℤ) : ℝ := (2 : ℝ) * Real.pi * (j : ℝ)

/-- `exp (2πj·I) = 1` for every integer j (periodicity of exp over 2π). -/
lemma exp_two_pi_int_mul_I (j : ℤ) :
    Complex.exp ((twoPiMulZ j : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_mul_I]
  have hx : twoPiMulZ j = (j : ℝ) * (2 * Real.pi) := by
    dsimp [twoPiMulZ]
    ring
  have hc : Complex.cos (twoPiMulZ j : ℂ) = 1 := by
    rw [← Complex.ofReal_cos, hx, Real.cos_int_mul_two_pi]
    norm_num
  have hs : Complex.sin (twoPiMulZ j : ℂ) = 0 := by
    have hk : (j : ℝ) * (2 * Real.pi) = ((2 * j : ℤ) : ℝ) * Real.pi := by
      norm_num
      ring
    rw [← Complex.ofReal_sin, hx, hk, Real.sin_int_mul_pi]
    norm_num
  rw [hc, hs]
  norm_num

/-- The s-th power of an s-th root of unity is 1: `(unitRoot s k)^s = 1`
(for `1 ≤ s`). -/
lemma unitRoot_pow (s : ℕ) (hs : 1 ≤ s) (k : ℕ) :
    (unitRoot s k) ^ s = 1 := by
  have hsC : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hs))
  have hsa : (s : ℝ) * unitRootReal s k = twoPiMul k := by
    dsimp [unitRootReal]
    field_simp [hsC]
  calc
    (unitRoot s k) ^ s = Complex.exp ((unitRootReal s k : ℂ) * Complex.I) ^ s := by
      rfl
    _ = Complex.exp (((s : ℕ) : ℂ) * ((unitRootReal s k : ℂ) * Complex.I)) := by
      rw [← Complex.exp_nat_mul]
    _ = Complex.exp ((twoPiMul k : ℂ) * Complex.I) := by
      have hcoef : (((s : ℕ) : ℂ) * ((unitRootReal s k : ℂ) * Complex.I)) =
          ((twoPiMul k : ℂ) * Complex.I) := by
        have hprod : ((s : ℕ) : ℂ) * ((unitRootReal s k : ℝ) : ℂ) =
            (((s : ℝ) * unitRootReal s k : ℝ) : ℂ) := by
          change (((s : ℝ) : ℂ)) * (((unitRootReal s k : ℝ) : ℂ)) =
            (((s : ℝ) * unitRootReal s k : ℝ) : ℂ)
          rw [← Complex.ofReal_mul]
        calc
          ((s : ℕ) : ℂ) * ((unitRootReal s k : ℂ) * Complex.I)
              = (((s : ℕ) : ℂ) * (unitRootReal s k : ℂ)) * Complex.I := by
                rw [mul_assoc]
          _ = (((s : ℝ) * unitRootReal s k : ℝ) : ℂ) * Complex.I := by
                rw [hprod]
          _ = ((twoPiMul k : ℂ) * Complex.I) := by
                congr 1
                rw [hsa]
      rw [hcoef]
    _ = 1 := exp_two_pi_nat_mul_I k

/-- Roots of unity are unit vectors: `‖unitRoot s k‖ = 1`. -/
lemma norm_unitRoot (s : ℕ) (k : ℕ) : ‖unitRoot s k‖ = 1 := by
  unfold unitRoot
  rw [Complex.norm_exp]
  have hre : ((unitRootReal s k : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

lemma pow_conditions_of_mem_raySet {s : ℕ} (hs : 1 ≤ s) {w : ℂ}
    (hw : w ∈ raySet s) : ((w ^ s).im = 0) ∧ 1 ≤ (w ^ s).re := by
  rcases hw with ⟨k, hk, x, hx, hwx⟩
  have hws : w ^ s = (x : ℂ) ^ s := by
    rw [hwx, mul_pow, unitRoot_pow s hs k, mul_one]
  have hxs : 1 ≤ x ^ s := by
    exact one_le_pow₀ hx
  have hpow : (x : ℂ) ^ s = ((x ^ s : ℝ) : ℂ) := (Complex.ofReal_pow x s).symm
  constructor
  · calc
      (w ^ s).im = ((x : ℂ) ^ s).im := congrArg Complex.im hws
      _ = (((x ^ s : ℝ) : ℂ)).im := congrArg Complex.im hpow
      _ = 0 := by rw [Complex.ofReal_im]
  · have hre1 : 1 ≤ (((x ^ s : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      exact hxs
    calc
      1 ≤ ((x : ℂ) ^ s).re := by
        calc
          1 ≤ (((x ^ s : ℝ) : ℂ)).re := hre1
          _ = ((x : ℂ) ^ s).re := (congrArg Complex.re hpow).symm
      _ ≤ (w ^ s).re := by
        rw [hws]


/-! ### Part 9: converse of the ray description — classification

For w with `w^s ∈ [1,∞)` (i.e. `(w^s).im = 0 ∧ 1 ≤ (w^s).re`): t :=
(w^s).re ≥ 1, ‖w‖^s = t (so ‖w‖ ≥ 1), and the argument equation
`s • (arg w : Angle) = (arg (w^s) : Angle) = 0` (arg_pow_coe_angle) is
classified by `Real.Angle.nsmul_eq_iff` as `(arg w : Angle) =
(unitRootReal s k : Angle)` for some `k : Fin s`.  The polar identity and
exp-periodicity over 2π then give `w = ‖w‖ · unitRoot s k` — w lies on the
k-th ray. -/

/-- A unit-modulus lower bound: if `1 ≤ ‖u‖^s` then `1 ≤ ‖u‖` (s ≥ 1). -/
lemma one_le_norm_of_one_le_pow {s : ℕ} (hs : 1 ≤ s) {u : ℂ}
    (h : 1 ≤ ‖u‖ ^ s) : 1 ≤ ‖u‖ := by
  by_contra hlt
  have hlt' : ‖u‖ < 1 := lt_of_not_ge hlt
  have hpowlt : ‖u‖ ^ s < 1 := pow_lt_one₀ (norm_nonneg u) hlt' (by omega : s ≠ 0)
  linarith

/-- The real part of an s-th root of unity direction equals
`(2πk/s)` — identity needed to read the Angle classification. -/
lemma unitRootReal_eq_two_pi_mul {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    (k : ℝ) * (2 * Real.pi / (s : ℝ)) = unitRootReal s k := by
  dsimp [unitRootReal, twoPiMul]
  ring_nf

/-- **Converse of the ray description**: if `w^s ∈ [1,∞)` then w lies on
one of the k-indexed rays (`k < s`, `x ≥ 1`). -/
theorem mem_raySet_of_pow_conditions {s : ℕ} (hs : 1 ≤ s) {w : ℂ}
    (h : ((w ^ s).im = 0) ∧ 1 ≤ (w ^ s).re) : w ∈ raySet s := by
  classical
  let t : ℝ := (w ^ s).re
  have htim : (w ^ s).im = 0 := h.1
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact h.2
  -- w^s = (t : ℂ)  and  ‖w‖^s = t
  have hwsr : w ^ s = (t : ℂ) := by
    apply Complex.ext
    · dsimp [t]
    · simp [htim]
  have hnorm : ‖w‖ ^ s = t := by
    calc
      ‖w‖ ^ s = ‖w ^ s‖ := by rw [norm_pow]
      _ = ‖(t : ℂ)‖ := by rw [hwsr]
      _ = t := by
        rw [Complex.norm_real]
        exact abs_of_nonneg (le_trans zero_le_one ht1)
  have hwne0 : w ≠ 0 := by
    intro hz
    have : t = 0 := by
      rw [← hnorm, hz, norm_zero, zero_pow (by omega : s ≠ 0)]
    linarith
  have hw1 : 1 ≤ ‖w‖ := by
    have : 1 ≤ ‖w‖ ^ s := by simpa [hnorm] using ht1
    exact one_le_norm_of_one_le_pow hs this
  -- argument equation: s • (arg w : Angle) = 0
  have hwsarg : (w ^ s).arg = 0 := by
    rw [hwsr]
    exact Complex.arg_ofReal_of_nonneg (le_trans zero_le_one ht1)
  have hangle : (s : ℕ) • ((w.arg : Real.Angle)) = 0 := by
    rw [← Complex.arg_pow_coe_angle w s]
    simpa [hwsarg]
  have hns : s ≠ 0 := by omega
  have hangle' : (s : ℕ) • ((w.arg : Real.Angle)) = (s : ℕ) • (0 : Real.Angle) := by
    simpa using hangle
  rcases (Real.Angle.nsmul_eq_iff (ψ := (w.arg : Real.Angle)) (θ := 0)
      (n := s) hns).1 hangle' with ⟨k, hk⟩
  -- simplify: (arg w : Angle) = (unitRootReal s k : Angle)
  have hcoef : ((unitRootReal s k : ℝ) : Real.Angle) =
      (k : ℕ) • ((2 * Real.pi / (s : ℝ) : ℝ) : Real.Angle) := by
    rw [← Real.Angle.natCast_mul_eq_nsmul (x := (2 * Real.pi / (s : ℝ))) (n := k)]
    congr 1
    exact (unitRootReal_eq_two_pi_mul hs k).symm
  have hk' : (w.arg : Real.Angle) = (unitRootReal s k : Real.Angle) := by
    rw [hk]
    simp [hcoef]
  -- exp(w.arg·I) = exp(unitRootReal s k · I) by 2π-periodicity
  rcases (Real.Angle.angle_eq_iff_two_pi_dvd_sub (θ := w.arg)
      (ψ := unitRootReal s k)).1 hk' with ⟨j, hj⟩
  have hExp : Complex.exp (w.arg * Complex.I) =
      Complex.exp ((unitRootReal s k : ℂ) * Complex.I) := by
    have harg : w.arg = unitRootReal s k + twoPiMulZ j := by
      have : twoPiMulZ j = (2 * Real.pi * (j : ℝ)) := rfl
      dsimp [twoPiMulZ] at hj ⊢
      linarith
    calc
      Complex.exp (w.arg * Complex.I)
          = Complex.exp (((unitRootReal s k + twoPiMulZ j) : ℝ) * Complex.I) := by
            rw [harg]
      _ = Complex.exp (((unitRootReal s k : ℝ) : ℂ) * Complex.I +
            ((twoPiMulZ j : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.ofReal_add, add_mul]
      _ = Complex.exp ((unitRootReal s k : ℂ) * Complex.I) *
            Complex.exp ((twoPiMulZ j : ℂ) * Complex.I) := by
            rw [Complex.exp_add]
      _ = Complex.exp ((unitRootReal s k : ℂ) * Complex.I) * 1 := by
            rw [exp_two_pi_int_mul_I j]
      _ = Complex.exp ((unitRootReal s k : ℂ) * Complex.I) := by rw [mul_one]
  -- w = ‖w‖ · exp((unitRootReal s k)·I) = ‖w‖ · unitRoot s k
  have hwExp : w = (‖w‖ : ℂ) * Complex.exp ((unitRootReal s k : ℂ) * Complex.I) := by
    calc
      w = (‖w‖ : ℂ) * Complex.exp (w.arg * Complex.I) :=
            (Complex.norm_mul_exp_arg_mul_I w).symm
      _ = (‖w‖ : ℂ) * Complex.exp ((unitRootReal s k : ℂ) * Complex.I) := by
            rw [hExp]
  refine ⟨k.val, k.isLt, ‖w‖, hw1, ?_⟩
  rw [unitRoot]
  exact hwExp


/-! ### Part 10: the closed ray description of D_s

With the forward direction (`pow_conditions_of_mem_raySet`) and the
converse (`mem_raySet_of_pow_conditions`) the two descriptions agree:
`rayAvoiding s = ℂ ∖ raySet s`. -/

/-- **Closed ray description**: `D_s = rayAvoiding s` is the complement of
the union of the k-indexed rays `raySet s = ⋃_{k<s} {x·unitRoot s k :
x ≥ 1}`.  Together with `regSlit_image_eq_rayAvoiding` this identifies the
image of f_s as the complement of the equiangular radial slits. -/
theorem rayAvoiding_eq_compl_raySet (s : ℕ) (hs : 1 ≤ s) :
    rayAvoiding s = (raySet s)ᶜ := by
  ext w
  constructor
  · intro hw
    intro hwr
    have hc := pow_conditions_of_mem_raySet hs hwr
    exact hw hc
  · intro hw
    intro hc
    exact hw (mem_raySet_of_pow_conditions hs hc)


/-! ### Part 11: injectivity of oneSlit and f_s on the unit disk

Step 1 (Cayley): `cayley u := (1−u)/(1+u)` is a Möbius map, injective
wherever `1+u ≠ 0` (cross-multiplication), in particular on the unit disk.
Step 2 (oneSlit): `oneSlit u = 1 − cayley(u)²` (Cayley form), and on the
disk `Re cayley(u) > 0` (`cayley_re_pos`), so `oneSlit u₁ = oneSlit u₂`
gives `cayley(u₁)² = cayley(u₂)²`; the sign case `cayley u₁ = −cayley u₂`
is impossible by positivity of the real parts, leaving
`cayley u₁ = cayley u₂` and hence `u₁ = u₂`.  Step 3 (f_s): the power
identity `f_s(ζ)^s = oneSlit(ζ^s)` makes `f_s ζ₁ = f_s ζ₂` imply
`oneSlit(ζ₁^s) = oneSlit(ζ₂^s)`, so `ζ₁^s = ζ₂^s` (oneSlit injective),
and cancellation of the nonzero factors `4^{1/s}` and `(1+ζ₁^s)^{−2/s}`
gives `ζ₁ = ζ₂`. -/

/-- The Cayley map is injective on the unit disk: `(1−u₁)/(1+u₁) =
(1−u₂)/(1+u₂)` implies `u₁ = u₂` for |uᵢ| < 1. -/
lemma cayley_injOn_ball {u₁ u₂ : ℂ} (hu₁ : ‖u₁‖ < 1) (hu₂ : ‖u₂‖ < 1)
    (h : cayley u₁ = cayley u₂) : u₁ = u₂ := by
  unfold cayley at h
  have hd₁ : (1 + u₁ : ℂ) ≠ 0 := by
    intro hz
    have hz' : u₁ + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u₁ = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u₁‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hd₂ : (1 + u₂ : ℂ) ≠ 0 := by
    intro hz
    have hz' : u₂ + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u₂ = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u₂‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  field_simp [hd₁, hd₂] at h
  -- expand: (1−u₁)(1+u₂) = (1+u₁)(1−u₂) forces u₁ = u₂
  have hz : ((1 - u₁) * (1 + u₂) - (1 + u₁) * (1 - u₂)) = 0 := by
    rw [h]
    ring
  have hthis : ((1 - u₁) * (1 + u₂) - (1 + u₁) * (1 - u₂)) = 2 * (u₂ - u₁) := by ring
  have h2 : 2 * (u₂ - u₁) = 0 := by
    rw [hthis] at hz
    exact hz
  have hz' : u₂ - u₁ = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  exact (sub_eq_zero.mp hz').symm

/-- oneSlit is injective on the unit disk: `oneSlit u₁ = oneSlit u₂`
implies `u₁ = u₂` for |uᵢ| < 1. -/
lemma oneSlit_injOn_ball {u₁ u₂ : ℂ} (hu₁ : ‖u₁‖ < 1) (hu₂ : ‖u₂‖ < 1)
    (h : oneSlit u₁ = oneSlit u₂) : u₁ = u₂ := by
  have hd₁ : (1 + u₁ : ℂ) ≠ 0 := by
    intro hz
    have hz' : u₁ + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u₁ = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u₁‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hd₂ : (1 + u₂ : ℂ) ≠ 0 := by
    intro hz
    have hz' : u₂ + 1 = 0 := by simpa [add_comm] using hz
    have hu' : u₂ = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖u₂‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hid₁ := oneSlit_eq_one_sub_cayley_sq (u := u₁) hd₁
  have hid₂ := oneSlit_eq_one_sub_cayley_sq (u := u₂) hd₂
  -- oneSlit uᵢ = 1 − cayley(uᵢ)², so the squares are equal
  have hsq : (cayley u₁) ^ 2 = (cayley u₂) ^ 2 := by
    calc
      (cayley u₁) ^ 2 = 1 - (1 - (cayley u₁) ^ 2) := by ring
      _ = 1 - (1 - (cayley u₂) ^ 2) := by
            rw [← hid₁, ← hid₂]
            exact congrArg (fun z : ℂ => 1 - z) h
      _ = (cayley u₂) ^ 2 := by ring
  -- a² = b² gives (a−b)(a+b) = 0
  have hsub0 : (cayley u₁) ^ 2 - (cayley u₂) ^ 2 = 0 := sub_eq_zero.mpr hsq
  have hz : (cayley u₁ - cayley u₂) * (cayley u₁ + cayley u₂) = 0 := by
    have hx : (cayley u₁ - cayley u₂) * (cayley u₁ + cayley u₂) =
        (cayley u₁) ^ 2 - (cayley u₂) ^ 2 := by ring
    rw [hx]
    exact hsub0
  by_cases hsub : cayley u₁ = cayley u₂
  · exact cayley_injOn_ball hu₁ hu₂ hsub
  · have hdiff : cayley u₁ - cayley u₂ ≠ 0 := sub_ne_zero.mpr hsub
    have hsum0 : cayley u₁ + cayley u₂ = 0 := by
      by_contra hnz
      have hprod : (cayley u₁ - cayley u₂) * (cayley u₁ + cayley u₂) ≠ 0 :=
        mul_ne_zero hdiff hnz
      exact hprod hz
    have hre : (cayley u₁).re + (cayley u₂).re = 0 := by
      have hh := congrArg Complex.re hsum0
      rw [Complex.add_re, Complex.zero_re] at hh
      exact hh
    have hp₁ : 0 < (cayley u₁).re := cayley_re_pos hu₁
    have hp₂ : 0 < (cayley u₂).re := cayley_re_pos hu₂
    linarith


/-- If `‖ζ‖ < 1` then `‖ζ^s‖ < 1` (s ≥ 1). -/
lemma norm_pow_lt_one {s : ℕ} (hs : 1 ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖ζ ^ s‖ < 1 := by
  calc
    ‖ζ ^ s‖ = ‖ζ‖ ^ s := by exact norm_pow ζ s
    _ ≤ ‖ζ‖ := by
      have h1 : ‖ζ‖ ^ (s - 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) (le_of_lt hζ)
      calc
        ‖ζ‖ ^ s = ‖ζ‖ * ‖ζ‖ ^ (s - 1) := by
          rw [← pow_pred_mul hs ‖ζ‖]
          ring
        _ ≤ ‖ζ‖ := by
          calc
            ‖ζ‖ * ‖ζ‖ ^ (s - 1) ≤ ‖ζ‖ * 1 :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg ζ)
            _ = ‖ζ‖ := by rw [mul_one]
    _ < 1 := hζ

/-- f_s is injective on the unit disk (s ≥ 1): the power identity pushes
injectivity through oneSlit (`oneSlit_injOn_ball`), giving ζ₁^s = ζ₂^s;
cancelling the nonzero common factors `4^{1/s}` and `(1+ζ₁^s)^{−2/s}`
then yields ζ₁ = ζ₂. -/
theorem regSlit_injOn_ball (s : ℕ) (hs : 1 ≤ s) :
    Set.InjOn (regSlit s) (ball (0 : ℂ) 1) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ h
  have hζ₁n : ‖ζ₁‖ < 1 := by
    simpa [dist_eq_norm, sub_zero] using (Metric.mem_ball.mp hζ₁)
  have hζ₂n : ‖ζ₂‖ < 1 := by
    simpa [dist_eq_norm, sub_zero] using (Metric.mem_ball.mp hζ₂)
  have hnp₁ : ‖ζ₁ ^ s‖ < 1 := norm_pow_lt_one hs hζ₁n
  have hnp₂ : ‖ζ₂ ^ s‖ < 1 := norm_pow_lt_one hs hζ₂n
  -- (1) raise the equality to the s-th power
  have hfs : (regSlit s ζ₁) ^ s = (regSlit s ζ₂) ^ s := congrArg (fun z : ℂ => z ^ s) h
  have hpow₁ := regSlit_pow hs hζ₁n
  have hpow₂ := regSlit_pow hs hζ₂n
  -- (2) oneSlit injectivity on the s-th powers
  have hpow_eq : ζ₁ ^ s = ζ₂ ^ s := by
    have hone : oneSlit (ζ₁ ^ s) = oneSlit (ζ₂ ^ s) := by
      rw [← hpow₁, ← hpow₂]
      exact hfs
    exact oneSlit_injOn_ball hnp₁ hnp₂ hone
  -- (3) cancellation of the common factors
  have h1u : (1 + ζ₂ ^ s : ℂ) ≠ 0 := by
    intro hz
    have hz' : ζ₂ ^ s + 1 = 0 := by simpa [add_comm] using hz
    have hu' : ζ₂ ^ s = -1 := eq_neg_of_add_eq_zero_left hz'
    have hn : ‖ζ₂ ^ s‖ = 1 := by
      rw [hu', norm_neg, norm_one]
    linarith
  have hX : ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl h1u
  have he₁ := regSlit_eq_neg_pow s ζ₁
  have he₂ := regSlit_eq_neg_pow s ζ₂
  rw [he₁, he₂] at h
  rw [hpow_eq] at h
  have hCX : slitCoef s * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s)) ≠ 0 :=
    mul_ne_zero (slitCoef_ne_zero hs) hX
  have hring : (slitCoef s * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) * ζ₁ =
      (slitCoef s * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) * ζ₂ := by
    calc
      (slitCoef s * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) * ζ₁
          = slitCoef s * (ζ₁ * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) := by ring
      _ = slitCoef s * (ζ₂ * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) := h
      _ = (slitCoef s * ((1 + ζ₂ ^ s : ℂ) ^ (-slitExponent s))) * ζ₂ := by ring
  exact mul_left_cancel₀ hCX hring


/-! ### Part 12: the conformal bijection 𝔻 → D_s and the sharp radius

`regSlit s` is a bijection of the unit disk onto `D_s` (injective +
surjective + maps-into), analytic on the disk, fixes 0, and has
`‖f_s'(0)‖ = 4^{1/s}`.  This is the exact dual statement at the map level:
the equiangular s-slit domain admits a conformal parametrisation with the
sharp boundary-radius derivative — the seed from which a conformal-radius
definition reads off `rad(D_s, 0) = 4^{1/s}`. -/

/-- f_s is a bijection from the unit disk onto D_s. -/
theorem regSlit_bijOn_rayAvoiding (s : ℕ) (hs : 1 ≤ s) :
    Set.BijOn (regSlit s) (ball (0 : ℂ) 1) (rayAvoiding s) := by
  refine ⟨regSlit_mapsTo_rayAvoiding s hs, regSlit_injOn_ball s hs, ?_⟩
  intro w hw
  rcases regSlit_surj s hs hw with ⟨ζ, hζn, hζeq⟩
  refine ⟨ζ, ?_, hζeq⟩
  simpa [dist_eq_norm, sub_zero] using hζn

/-- **Bundled conformal data**: the equiangular s-slit domain D_s admits an
analytic bijection of the unit disk, fixing 0, with derivative 4^{1/s} at
0.  Any conformal-radius definition that is the supremum of ‖f'(0)‖ over
analytic maps 𝔻 → D_s fixing 0 therefore has `rad(D_s, 0) ≥ 4^{1/s}`, with
equality attained by this map. -/
theorem equiangular_conformal_data (s : ℕ) (hs : 1 ≤ s) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (0 : ℂ) 1) ∧ f 0 = 0 ∧
      Set.BijOn f (ball (0 : ℂ) 1) (rayAvoiding s) ∧
      ‖deriv f 0‖ = (4 : ℝ) ^ (1 / (s : ℝ)) := by
  refine ⟨regSlit s, regSlit_differentiableOn s hs, regSlit_zero s,
    regSlit_bijOn_rayAvoiding s hs, regSlit_deriv_zero_norm hs⟩

end Submission.RegularSlit

end
