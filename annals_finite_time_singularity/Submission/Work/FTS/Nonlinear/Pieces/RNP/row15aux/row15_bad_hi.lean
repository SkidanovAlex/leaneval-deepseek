import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Spaces.scoef
import Submission.Work.FM.Defs
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_SmoothQuadPthFstar
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bad
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.pth_Fstar_lower
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.notIntegrableOn_Itheta_of_rpow_lower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `row15_bad_hi`: the "bad" angular endpoint for the `N₂^{ss}` row, higher-derivative branch

Row 15 of the nonlinear estimates is about `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.  The companion lemma
`row15_bad` rules out the case in which `θ ↦ U(Φ̃_*)(z,θ)` is bounded away from `0` near
`θ = 0`: there `|N₂^{ss}|` itself blows up like `θ^{α/3-1}` and the `i = 0` slot of
`HkIntegrand α 4 (N₂^{ss})` is not integrable.

The present lemma covers the *higher-derivative* branch: if some `k`-th `z`-derivative
(`1 ≤ k ≤ 4`) of `U(Φ̃_*)` is bounded away from `0` near `θ = 0⁺` while all the lower ones tend
to `0`, then still `θ ↦ HkIntegrand α 4 (N₂^{ss}) z θ` is not integrable on `Iθ`.

The mathematics is the same one-sided blow-up test, one slot further up in the pure-`D_z`
block of the integrand.  With `U := Uop α (PhiTs α Φs)` and `P := ∂_θF_*`:

* `∂_θF_*` factorizes as `α(Γ'(θ)/c)·2z/(1+z)²`, so every `D_z^m P` is a `z`-dependent
  constant times `∂_θF_*` itself (`PthFstar_DzIter_le` below), while
  `|∂_θF_*| ≥ c·θ^{α/3-1}` near `0` (`pth_Fstar_lower`);
* the Leibniz rule `D_z^k (U·P) = Σ_b C(k,b) D_z^b U · D_z^{k-b} P` and the Stirling expansion
  `D_z^k = Σ_{j≤k} S(k,j) z^j ∂_z^j` convert the hypothesis on `∂_z^k U` into
  `|D_z^k U| ≥ ρ > 0` eventually and `D_z^b U → 0` for `b < k`
  (`DzIter_k_bounded_below`, `DzIter_low_vanish`), so the top term of the sum dominates
  (`DzIter_sum_lower_bound`);
* hence `|D_z^k (N₂^{ss})(z,θ)| ≳ θ^{α/3-1}`, and the `i = k` slot of the pure-`D_z` block of
  the integrand carries the weight `sin(2θ)^{-η}`, giving
  `HkIntegrand α 4 (N₂^{ss})(z,θ) ≳ θ^{2α/3-2-η}`.  Since `2α/3-2-η ≤ -7/3 < -1`, that power is
  not integrable at `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## Linear behaviour of `D_z^j` under multiplication by a factor depending only on `θ` -/

/-- A multiplier depending on the angle only passes through the radial iterates `D_z^j`:
`D_z^j (c(θ)·g)(z,θ) = c(θ)·D_z^j g (z,θ)`. -/
private theorem DzIter_theta_mul (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * g z θ) z θ
      = c θ * Work.Spaces.DzIter j g z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ n ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c θ * g z θ) z' θ) z
      = c θ * (z * deriv (fun z' => Work.Spaces.DzIter n g z' θ) z)
    rw [show (fun z' => Work.Spaces.DzIter n (fun z θ => c θ * g z θ) z' θ)
          = (fun z' => c θ * Work.Spaces.DzIter n g z' θ) from funext fun z' => ih z' θ,
      deriv_const_mul_field]
    ring

/-- The specialization of `DzIter_theta_mul` to a product of a `θ`-only factor and a
`z`-only factor. -/
private theorem DzIter_theta_mul_radial (c : ℝ → ℝ) (G : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * G z) z θ
      = c θ * Work.Spaces.DzIter j (fun z θ => G z) z θ :=
  DzIter_theta_mul c (fun z _ => G z) j z θ

/-- Multiplication by a constant passes through the radial iterates. -/
private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter j f z θ :=
  DzIter_theta_mul (fun _ => c) f j z θ

/-- `D_z^j` of a function of `z` alone does not depend on the angle. -/
private theorem DzIter_radial_indep (G : ℝ → ℝ) (j : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter j (fun z _ => G z) z θ = Work.Spaces.DzIter j (fun z _ => G z) z θ' := by
  induction j generalizing z θ θ' with
  | zero => rfl
  | succ n ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ) z
      = z * deriv (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ') z
    rw [show (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ)
          = (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ')
        from funext fun z' => ih z' θ θ']

/-- The Stirling number of the second kind on the diagonal: `S(n,n) = 1`. -/
private theorem scoef_self (n : ℕ) : Work.Spaces.scoef n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * Work.Spaces.scoef n (n + 1) + Work.Spaces.scoef n n = 1
    rw [Work.Spaces.scoef_succ_self_eq_zero n, ih]
    simp

/-- `(a / s^{q/2})² = a²·s^{-q}` for `s ≥ 0`. -/
private theorem div_sin_rpow_sq {a s q : ℝ} (hs : 0 ≤ s) :
    (a / s ^ (q / 2)) ^ 2 = a ^ 2 * s ^ (-q) := by
  have h1 : (s ^ (q / 2)) ^ 2 = s ^ q := by
    rw [← Real.rpow_natCast (s ^ (q / 2)) 2,
      ← Real.rpow_mul hs (q / 2) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  rw [div_pow, h1, div_eq_mul_inv, ← Real.rpow_neg hs q]

/-! ## The `θ`-only factorization of `∂_θ F_*` and its higher `D_z`-iterates -/

/-- **The `D_z`-iterates of `∂_θF_*` are bounded by `∂_θF_*` itself**, at fixed `z > 0`.

`∂_θF_*(z,θ) = (α Γ'(θ)/c(α)) · F̲(z)` with `F̲(z) = 2z/(1+z)² = FM.Fstar z` and
`Γ = Spaces.Gam α`, so `D_z` (which differentiates only the `z`-variable) acts on `F̲` alone:

  `D_z^m (∂_θF_*)(z,θ) = (α Γ'(θ)/c(α)) · (D_z^m F̲)(z)`   (`DzIter_theta_mul_radial`),

while `∂_θF_*(z,θ) = (α Γ'(θ)/c(α)) · F̲(z)`.  Hence the two are proportional with the
`θ`-independent ratio `(D_z^m F̲)(z)/F̲(z)`, and `F̲(z) > 0` for `z > 0`. -/
theorem PthFstar_DzIter_le {α z : ℝ} (hα : 0 < α) (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
        ≤ C * |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
  have hFpos : 0 < Work.FM.Fstar z := by
    rw [Work.FM.Fstar]
    exact div_pos (by linarith) (pow_pos (by linarith) 2)
  have hPfun : Work.Spaces.pth (Work.Construction.Fstar α)
      = fun z θ => (α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
          * Work.FM.Fstar z := by
    funext z' θ'
    rw [Work.Construction.pth_Fstar_eq hα]
    ring
  have hCpos : 0 < 1 + (∑ m ∈ Finset.range 5,
      |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z 0|) / Work.FM.Fstar z := by
    have hK : 0 ≤ ∑ m ∈ Finset.range 5,
        |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z 0| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have := div_nonneg hK hFpos.le
    linarith
  refine ⟨1 + (∑ m ∈ Finset.range 5,
      |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z 0|) / Work.FM.Fstar z,
    hCpos, ?_⟩
  intro m hm θ hθ
  rw [hPfun, DzIter_theta_mul_radial]
  change |(α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
        * Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z θ|
      ≤ (1 + (∑ i ∈ Finset.range 5, |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|)
          / Work.FM.Fstar z) * |(α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
          / Work.Spaces.c α) * Work.FM.Fstar z|
  rw [abs_mul, abs_mul, abs_of_pos hFpos]
  have hm5 : m < 5 := by omega
  have hKz : |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z 0|
      ≤ ∑ i ∈ Finset.range 5, |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0| :=
    Finset.single_le_sum
      (s := Finset.range 5)
      (f := fun i => |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hm5)
  have h1 : |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z θ|
      ≤ ∑ i ∈ Finset.range 5, |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0| := by
    rw [DzIter_radial_indep (fun z => Work.FM.Fstar z) m z θ 0]
    exact hKz
  have h2 : |α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
        * |Work.Spaces.DzIter m (fun z _ => Work.FM.Fstar z) z θ|
      ≤ |α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
        * (∑ i ∈ Finset.range 5,
            |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 : |α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
        * (∑ i ∈ Finset.range 5, |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|)
      ≤ (1 + (∑ i ∈ Finset.range 5, |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|)
          / Work.FM.Fstar z)
        * (|α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
          * Work.FM.Fstar z) := by
    have hSnn : 0 ≤ ∑ i ∈ Finset.range 5,
        |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have hid : (1 + (∑ i ∈ Finset.range 5,
            |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|) / Work.FM.Fstar z)
          * (|α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
            * Work.FM.Fstar z)
        = |α * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ / Work.Spaces.c α|
          * (Work.FM.Fstar z + ∑ i ∈ Finset.range 5,
              |Work.Spaces.DzIter i (fun z _ => Work.FM.Fstar z) z 0|) := by
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith [h2, h3]

/-! ## The Stirling bridge from `∂_z^j` to `D_z^j` -/

/-- A finite sum of functions tending to `0` at `0⁺` tends to `0`. -/
private theorem tendsto_sum_zero {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, Filter.Tendsto (fun θ => F i θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun θ => ∑ i ∈ s, F i θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : Filter.Tendsto (fun θ => F a θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      hF a (Finset.mem_insert_self a s)
    have h2 : Filter.Tendsto (fun θ => ∑ i ∈ s, F i θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds 0) :=
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have h3 := h1.add h2
    simpa [Finset.sum_insert ha] using h3

/-- **The lower `D_z`-iterates of `U` vanish at `θ → 0⁺`** as soon as the lower *plain*
`θ`-slices `∂_z^j U(z,·)` do.  The Stirling expansion `D_z^n = ∑_{j≤n} S(n,j) z^j ∂_z^j`
(`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`) writes `D_z^b U` for `b < k` as a finite
`θ`-independent combination of the `∂_z^j U` with `j ≤ b < k`; finitely many `b` are
involved, so the neighbourhood can be taken uniform. -/
theorem DzIter_low_vanish {U : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (k : ℕ) (hk4 : k ≤ 4)
    (hsq : Work.FTS.LocData.SmoothQuad U)
    (hlow : ∀ b : ℕ, b < k → Filter.Tendsto (fun θ => Work.Spaces.pzIter b U z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) ε, ∀ b : ℕ, b < k →
      |Work.Spaces.DzIter b U z θ| ≤ η := by
  intro ηs hηspos
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  set Kz : ℝ := ∑ b ∈ Finset.range k, ∑ j ∈ Finset.range (b + 1),
      (Work.Spaces.scoef b j : ℝ) * z ^ j with hKz
  have hKznn : 0 ≤ Kz := by
    rw [hKz]
    exact Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz0 j)
  have hKz1pos : 0 < Kz + 1 := by linarith
  set η' : ℝ := ηs / (Kz + 1) with hη'
  have hη'pos : 0 < η' := by rw [hη']; positivity
  -- a neighbourhood on which every `|∂_z^j U|` with `j < k` is `≤ η'`
  have hsumabs : Filter.Tendsto (fun θ => ∑ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_sum_zero (Finset.range k)
      (fun j hj => by simpa using (hlow j (Finset.mem_range.mp hj)).abs)
  have hsmall : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ| ≤ η' := by
    have hlt : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∑ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ|) < η' := by
      have h0 := (Metric.tendsto_nhds.mp hsumabs) η' hη'pos
      filter_upwards [h0] with θ hθ
      rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at hθ
    filter_upwards [hlt] with θ hθ j hj
    exact le_of_lt (lt_of_le_of_lt
      (Finset.single_le_sum (s := Finset.range k)
        (f := fun i => |Work.Spaces.pzIter i U z θ|) (fun i _ => abs_nonneg _) hj) hθ)
  rw [eventually_nhdsWithin_iff] at hsmall
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨min ε₀ (Real.pi / 2), lt_min hε₀pos (by linarith [Real.pi_pos]), ?_⟩
  intro θ hθ b hb
  have hθπ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩
  have hθε : θ ∈ Set.Ioo (0 : ℝ) ε₀ := ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_left _ _)⟩
  have hbound : ∀ j ≤ b, |Work.Spaces.pzIter j U z θ| ≤ η' := by
    intro j hj
    exact hε₀ (y := θ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hθ.1]; exact hθε.2) hθ.1 j
      (Finset.mem_range.mpr (lt_of_le_of_lt hj hb))
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (θ := θ) (h := U) (hsq.curry_z hθπ) b z hzI]
  calc |∑ j ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)|
      ≤ ∑ j ∈ Finset.range (b + 1), (Work.Spaces.scoef b j : ℝ) * (z ^ j * η') := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b j)), abs_mul,
          abs_of_nonneg (pow_nonneg hz0 j)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (hbound j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (pow_nonneg hz0 j))
          (Nat.cast_nonneg _)
    _ = η' * (∑ j ∈ Finset.range (b + 1), (Work.Spaces.scoef b j : ℝ) * z ^ j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ η' * Kz := by
        refine mul_le_mul_of_nonneg_left ?_ hη'pos.le
        rw [hKz]
        exact Finset.single_le_sum (s := Finset.range k)
          (f := fun i => ∑ j ∈ Finset.range (i + 1), (Work.Spaces.scoef i j : ℝ) * z ^ j)
          (fun i _ => Finset.sum_nonneg fun j _ =>
            mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz0 j))
          (Finset.mem_range.mpr hb)
    _ ≤ ηs := by
        rw [hη', div_mul_eq_mul_div, div_le_iff₀ hKz1pos]
        nlinarith [hηspos, hKznn]

/-- **The `k`-th `D_z`-iterate of `U` is bounded below near `θ = 0⁺`.**  With the Stirling
expansion, `D_z^k U z θ = z^k ∂_z^kU(z,θ) + ∑_{j<k} S(k,j) z^j ∂_z^jU(z,θ)`; the leading term
is `≥ z^k δ` eventually by hypothesis, while the finitely many lower ones tend to `0` by
`hlow`. -/
theorem DzIter_k_bounded_below {U : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (k : ℕ) (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hsq : Work.FTS.LocData.SmoothQuad U)
    (hlow : ∀ b : ℕ, b < k → Filter.Tendsto (fun θ => Work.Spaces.pzIter b U z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbig : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ ≤ |Work.Spaces.pzIter k U z θ|) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ρ ≤ |Work.Spaces.DzIter k U z θ| := by
  obtain ⟨δ, hδpos, hδev⟩ := hbig
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hzkpos : 0 < z ^ k := pow_pos hz k
  rw [eventually_nhdsWithin_iff] at hδev
  obtain ⟨εδ, hεδpos, hεδ⟩ := Metric.eventually_nhds_iff.mp hδev
  set Kz : ℝ := ∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * z ^ j with hKz
  have hKznn : 0 ≤ Kz := by
    rw [hKz]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz0 j)
  have hKz1pos : 0 < Kz + 1 := by linarith
  set η' : ℝ := z ^ k * δ / (2 * (Kz + 1)) with hη'
  have hη'pos : 0 < η' := by rw [hη']; positivity
  have hsumabs : Filter.Tendsto (fun θ => ∑ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_sum_zero (Finset.range k)
      (fun j hj => by simpa using (hlow j (Finset.mem_range.mp hj)).abs)
  have hsmall : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ| ≤ η' := by
    have hlt : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∑ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ|) < η' := by
      have h0 := (Metric.tendsto_nhds.mp hsumabs) η' hη'pos
      filter_upwards [h0] with θ hθ
      rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at hθ
    filter_upwards [hlt] with θ hθ j hj
    exact le_of_lt (lt_of_le_of_lt
      (Finset.single_le_sum (s := Finset.range k)
        (f := fun i => |Work.Spaces.pzIter i U z θ|) (fun i _ => abs_nonneg _) hj) hθ)
  rw [eventually_nhdsWithin_iff] at hsmall
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨z ^ k * δ / 2, by positivity, ?_⟩
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.mpr
    ⟨min εδ (min ε₀ (Real.pi / 2)), lt_min hεδpos (lt_min hε₀pos (by linarith [Real.pi_pos])), ?_⟩
  intro θ hdist hθpos
  have hdist' : |θ| < min εδ (min ε₀ (Real.pi / 2)) := by
    rwa [Real.dist_eq, sub_zero] at hdist
  have hθabs : |θ| = θ := abs_of_pos hθpos
  have hθlt : θ < min εδ (min ε₀ (Real.pi / 2)) := by rwa [hθabs] at hdist'
  have hθltπ : θ < Real.pi / 2 :=
    lt_of_lt_of_le hθlt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθltεδ : θ < εδ := lt_of_lt_of_le hθlt (min_le_left _ _)
  have hθltε₀ : θ < ε₀ := lt_of_lt_of_le hθlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθπ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθpos, hθltπ⟩
  have hδ : δ ≤ |Work.Spaces.pzIter k U z θ| :=
    hεδ (y := θ) (by rw [Real.dist_eq, sub_zero, hθabs]; exact hθltεδ) hθpos
  have hlow' : ∀ j ∈ Finset.range k, |Work.Spaces.pzIter j U z θ| ≤ η' :=
    hε₀ (y := θ) (by rw [Real.dist_eq, sub_zero, hθabs]; exact hθltε₀) hθpos
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hexp := Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (θ := θ) (h := U)
    (hsq.curry_z hθπ) k z hzI
  have htail : |∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)|
      ≤ η' * Kz := by
    calc |∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)|
        ≤ ∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * η') := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef k j)), abs_mul,
            abs_of_nonneg (pow_nonneg hz0 j)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hlow' j hj) (pow_nonneg hz0 j)) (Nat.cast_nonneg _)
      _ = η' * (∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * z ^ j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = η' * Kz := by rw [hKz]
  have hmain : z ^ k * δ ≤ |z ^ k * Work.Spaces.pzIter k U z θ| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 k)]
    exact mul_le_mul_of_nonneg_left hδ (pow_nonneg hz0 k)
  have hηK : η' * Kz ≤ z ^ k * δ / 2 := by
    rw [hη', div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Kz + 1))]
    nlinarith [hKznn, hzkpos]
  have hsum : z ^ k * δ / 2 ≤ z ^ k * δ - |∑ j ∈ Finset.range k,
      (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)| := by
    linarith [hηK, htail]
  have hsplit : |(∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ))
        + (Work.Spaces.scoef k k : ℝ) * (z ^ k * Work.Spaces.pzIter k U z θ)|
      = |(∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ))
        + z ^ k * Work.Spaces.pzIter k U z θ| := by
    rw [scoef_self, Nat.cast_one, one_mul]
  rw [hexp, Finset.sum_range_succ, hsplit]
  have htri : |z ^ k * Work.Spaces.pzIter k U z θ| ≤
      |(∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ))
        + z ^ k * Work.Spaces.pzIter k U z θ|
      + |∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)| := by
    have h0 := abs_add_le
      ((∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ))
        + z ^ k * Work.Spaces.pzIter k U z θ)
      (-(∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)))
    rw [abs_neg, show ((∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ))
        + z ^ k * Work.Spaces.pzIter k U z θ)
      + (-(∑ j ∈ Finset.range k, (Work.Spaces.scoef k j : ℝ) * (z ^ j * Work.Spaces.pzIter j U z θ)))
      = z ^ k * Work.Spaces.pzIter k U z θ from by ring] at h0
    exact h0
  linarith [hmain, hsum, htri]

/-! ## The elementary `Finset` estimate isolating the top term -/

/-- **Top-term isolation.**  If `|A k| ≥ ρ`, `|A b| ≤ η` for `b < k` and `|B m| ≤ c₀|B 0|`
for `m ≤ k`, then the binomial-weighted sum `∑_{b≤k} C(k,b) A b B(k-b)` is bounded below by
`(ρ/2)|B 0|` as soon as `η c₀ ∑_{b<k} C(k,b) ≤ ρ/2`. -/
theorem DzIter_sum_lower_bound {k : ℕ} (hk1 : 1 ≤ k) {A B : ℕ → ℝ} {c₀ ρ η : ℝ}
    (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hAk : ρ ≤ |A k|)
    (hAb : ∀ b : ℕ, b < k → |A b| ≤ η)
    (hB : ∀ m : ℕ, m ≤ k → |B m| ≤ c₀ * |B 0|)
    (hsmall : η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) ≤ ρ / 2) :
    ρ / 2 * |B 0| ≤ |∑ b ∈ Finset.range (k + 1), (k.choose b : ℝ) * (A b * B (k - b))| := by
  have hSnn : 0 ≤ ∑ b ∈ Finset.range k, (k.choose b : ℝ) :=
    Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  have hη0 : 0 ≤ η := by
    have := hAb 0 (by omega)
    exact le_trans (abs_nonneg _) this
  have htail : |∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b))|
      ≤ η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) * |B 0| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ b ∈ Finset.range k, |(k.choose b : ℝ) * (A b * B (k - b))|
        ≤ (k.choose b : ℝ) * (η * (c₀ * |B 0|)) := by
      intro b hb
      have hbk : b < k := Finset.mem_range.mp hb
      have h1 : |B (k - b)| ≤ c₀ * |B 0| := hB (k - b) (by omega)
      have h2 : |A b| ≤ η := hAb b hbk
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose b)), abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h1 (abs_nonneg _) hη0) (Nat.cast_nonneg _)
    calc ∑ b ∈ Finset.range k, |(k.choose b : ℝ) * (A b * B (k - b))|
        ≤ ∑ b ∈ Finset.range k, (k.choose b : ℝ) * (η * (c₀ * |B 0|)) :=
          Finset.sum_le_sum hterm
      _ = η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) * |B 0| := by
          rw [← Finset.sum_mul]
          ring
  have hbd0 : η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) * |B 0| ≤ ρ / 2 * |B 0| := by
    have h := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (B 0))
    calc η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) * |B 0|
        = (η * c₀ * (∑ b ∈ Finset.range k, (k.choose b : ℝ))) * |B 0| := by ring
      _ ≤ ρ / 2 * |B 0| := h
  have htri : |A k * B 0| ≤ |(∑ b ∈ Finset.range k,
        (k.choose b : ℝ) * (A b * B (k - b))) + A k * B 0|
      + |∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b))| := by
    have h0 := abs_add_le
      ((∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b))) + A k * B 0)
      (-(∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b))))
    rw [abs_neg, show ((∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b))) + A k * B 0)
      + (-(∑ b ∈ Finset.range k, (k.choose b : ℝ) * (A b * B (k - b)))) = A k * B 0 from by ring] at h0
    exact h0
  rw [Finset.sum_range_succ,
    show (k.choose k : ℝ) * (A k * B (k - k)) = A k * B 0 from by
      rw [Nat.choose_self, Nat.sub_self]; ring]
  have hAkB : ρ * |B 0| ≤ |A k * B 0| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hAk (abs_nonneg _)
  linarith [hAkB, htri, htail, hbd0]

theorem row15_bad_hi {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) (hz : 0 < z)
    (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hlow : ∀ b : ℕ, b < k → Filter.Tendsto (fun θ => Work.Spaces.pzIter b
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbig : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ ≤ |Work.Spaces.pzIter k (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|) :
    ¬MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ)
      Work.Spaces.Iθ := by
  set U : ℝ → ℝ → ℝ := Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) with hU
  set P : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Construction.Fstar α) with hP
  have hsqU : Work.FTS.LocData.SmoothQuad U := by
    rw [hU]
    exact Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop
      (Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth)
  have hsqP : Work.FTS.LocData.SmoothQuad P := by
    rw [hP]
    exact row15_SmoothQuadPthFstar α
  have hN2 : Work.FTS.Nonlin.N2ss α Φs = fun z θ => (-2 * U z θ) * P z θ := by
    rw [hU, hP]
    rfl
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  -- the Leibniz expansion of `D_z^k (N₂^{ss})` in the two factors `-2U` and `P`
  have hleib : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
        = ∑ b ∈ Finset.range (k + 1), (k.choose b : ℝ)
            * (Work.Spaces.DzIter b (fun z θ => -2 * U z θ) z θ
              * Work.Spaces.DzIter (k - b) P z θ) := by
    intro θ hθ
    have hsqf : Work.FTS.LocData.SmoothQuad (fun z θ => -2 * U z θ) :=
      Work.FTS.LocData.smoothQuad_const_mul (-2) hsqU
    rw [hN2]
    exact Work.FTS.H2.STQ.DzIter_mul_quad hsqf hsqP hzI hθ
  -- the constants
  obtain ⟨CP, hCPpos, hCP⟩ := PthFstar_DzIter_le (α := α) (z := z) hα hz
  obtain ⟨ρ, hρpos, hρev⟩ := DzIter_k_bounded_below (U := U) hz k hk1 hk4 hsqU hlow hbig
  obtain ⟨cP, hcPpos, hcP⟩ := pth_Fstar_lower (z := z) hα hα1 hz
  -- a neighbourhood on which `|D_z^k U| ≥ ρ`
  rw [eventually_nhdsWithin_iff] at hρev
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.eventually_nhds_iff.mp hρev
  -- the threshold for the vanishing lower iterates
  have hSsum0 : 0 ≤ ∑ b ∈ Finset.range k, (k.choose b : ℝ) :=
    Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  set ηs : ℝ := ρ / (2 * (CP * ((∑ b ∈ Finset.range k, (k.choose b : ℝ)) + 1))) with hηs
  have hηspos : 0 < ηs := by rw [hηs]; positivity
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := DzIter_low_vanish (U := U) hz k hk4 hsqU hlow ηs hηspos
  -- the working right neighbourhood of `0`
  set ε : ℝ := min ε₁ (min ε₂ (Real.pi / 6)) with hε
  have hεpos : 0 < ε := lt_min hε₁pos (lt_min hε₂pos (by linarith [Real.pi_pos]))
  have hεle₁ : ε ≤ ε₁ := by rw [hε]; exact min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := by rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle6 : ε ≤ Real.pi / 6 := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεlepi : ε ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- the smallness of the threshold
  have hsmall : ηs * CP * (∑ b ∈ Finset.range k, (k.choose b : ℝ)) ≤ ρ / 2 := by
    rw [hηs, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (CP * ((∑ b ∈ Finset.range k,
        (k.choose b : ℝ)) + 1)))]
    nlinarith [hSsum0, hCPpos, hρpos]
  -- ## the pointwise lower bound for `D_z^k (N₂^{ss})`
  have hcore : ∀ θ ∈ Set.Ioo (0 : ℝ) ε,
      (ρ * cP) * θ ^ (α / 3 - 1)
        ≤ |Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ| := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hθπ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθpos, by linarith [hθ.2, hεlepi, Real.pi_pos]⟩
    have hUk : ρ ≤ |Work.Spaces.DzIter k U z θ| :=
      hε₂ (y := θ)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact lt_of_lt_of_le hθ.2 hεle₂)
        hθpos
    have hUb : ∀ b < k, |Work.Spaces.DzIter b U z θ| ≤ ηs :=
      fun b hb => hε₁ θ ⟨hθpos, lt_of_lt_of_le hθ.2 hεle₁⟩ b hb
    have hPm : ∀ m ≤ k, |Work.Spaces.DzIter m P z θ|
        ≤ CP * |Work.Spaces.DzIter 0 P z θ| := by
      intro m hm
      rw [Work.Spaces.DzIter_zero]
      exact hCP m (le_trans hm hk4) θ hθπ
    have hsum := DzIter_sum_lower_bound (k := k) hk1
      (A := fun b => Work.Spaces.DzIter b U z θ)
      (B := fun m => Work.Spaces.DzIter m P z θ)
      (c₀ := CP) (ρ := ρ) (η := ηs) hρpos hCPpos hUk hUb hPm hsmall
    -- rewrite `D_z^k (N₂^{ss})` as `-2` times the sum
    have hsplit : Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
        = -2 * (∑ b ∈ Finset.range (k + 1), (k.choose b : ℝ)
            * (Work.Spaces.DzIter b U z θ * Work.Spaces.DzIter (k - b) P z θ)) := by
      rw [hleib θ hθπ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by
        rw [DzIter_const_mul]; ring
    have hstep1 : ρ * (cP * θ ^ (α / 3 - 1)) ≤ ρ * |Work.Spaces.DzIter 0 P z θ| := by
      refine mul_le_mul_of_nonneg_left ?_ hρpos.le
      rw [Work.Spaces.DzIter_zero]
      exact hcP θ ⟨hθpos, lt_of_lt_of_le hθ.2 hεle6⟩
    have hstep2 : ρ * |Work.Spaces.DzIter 0 P z θ|
        ≤ 2 * |∑ b ∈ Finset.range (k + 1), (k.choose b : ℝ)
            * (Work.Spaces.DzIter b U z θ * Work.Spaces.DzIter (k - b) P z θ)| := by
      linarith [hsum]
    rw [hsplit, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hstep1, hstep2]
  -- ## the `i = k` slot of the pure-`D_z` block
  have hslot : ∀ θ ∈ Set.Ioo (0 : ℝ) ε,
      (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ := by
    intro θ hθ
    rw [Work.Spaces.HkIntegrand]
    have h1 : (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (Work.FTS.Nonlin.N2ss α Φs) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      Finset.single_le_sum
        (s := Finset.range (4 + 1))
        (f := fun i => (Work.Spaces.DzIter i (Work.FTS.Nonlin.N2ss α Φs) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    have h2 : 0 ≤ ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    linarith [h1, h2]
  -- ## the final power comparison
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    have h1 : 0 < z ^ 2 := pow_pos hz 2
    positivity
  have hpow2 : ∀ θ ∈ Set.Ioo (0 : ℝ) ε,
      ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2 * ((Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsinpos : 0 < Real.sin (2 * θ) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθpos]) ?_
      linarith [hθ.2, hεlepi, Real.pi_pos]
    have ha : 0 ≤ (ρ * cP) * θ ^ (α / 3 - 1) := by positivity
    have hsq : ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2
        ≤ (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ) ^ 2 := by
      have h := pow_le_pow_left₀ ha (hcore θ hθ) 2
      simpa [sq_abs] using h
    have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinpos.le _)
    calc ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2 * ((Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hsq h1
      _ = (Work.Spaces.DzIter k (Work.FTS.Nonlin.N2ss α Φs) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [mul_pow, div_sin_rpow_sq hsinpos.le]
  have hpow : ∀ θ ∈ Set.Ioo (0 : ℝ) ε,
      ((ρ * cP) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta))
          * θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        ≤ ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsinpos : 0 < Real.sin (2 * θ) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθpos]) ?_
      linarith [hθ.2, hεlepi, Real.pi_pos]
    have hrpow2 : (θ ^ (α / 3 - 1)) ^ 2 = θ ^ (2 * α / 3 - 2) := by
      rw [← Real.rpow_natCast (θ ^ (α / 3 - 1)) 2,
        ← Real.rpow_mul hθpos.le (α / 3 - 1) ((2 : ℕ) : ℝ)]
      congr 1
      push_cast
      ring
    have hsinlow : (2 * θ) ^ (-Work.Spaces.eta)
        ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      have hs2θ0 : 0 ≤ 2 * θ := by linarith
      have hsinle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le hs2θ0
      exact Real.rpow_le_rpow_of_nonpos hsinpos hsinle (by rw [Work.Spaces.eta]; norm_num)
    have hexp1 : θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        = θ ^ (2 * α / 3 - 2) * θ ^ (-Work.Spaces.eta) := by
      have h := Real.rpow_add hθpos (2 * α / 3 - 2) (-Work.Spaces.eta)
      rw [show (2 : ℝ) * α / 3 - 2 + -Work.Spaces.eta
        = 2 * α / 3 - 2 - Work.Spaces.eta by ring] at h
      exact h
    calc ((ρ * cP) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta))
          * θ ^ (2 * α / 3 - 2 - Work.Spaces.eta)
        = (ρ * cP) ^ 2 * (Work.Spaces.w z) ^ 2
            * (2 ^ (-Work.Spaces.eta) * θ ^ (-Work.Spaces.eta))
            * θ ^ (2 * α / 3 - 2) := by
          rw [hexp1]; ring
      _ ≤ (ρ * cP) ^ 2 * (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) * θ ^ (2 * α / 3 - 2) := by
          have h2θ : 2 ^ (-Work.Spaces.eta) * θ ^ (-Work.Spaces.eta)
              = (2 * θ) ^ (-Work.Spaces.eta) :=
            (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθpos.le).symm
          rw [h2θ]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsinlow (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
            (Real.rpow_nonneg hθpos.le _)
      _ = ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
          have hkey : ((ρ * cP) * θ ^ (α / 3 - 1)) ^ 2
              = (ρ * cP) ^ 2 * θ ^ (2 * α / 3 - 2) := by
            rw [mul_pow, hrpow2]
          rw [hkey]; ring
  -- ## conclude
  have hp : 2 * α / 3 - 2 - Work.Spaces.eta ≤ -1 := by
    have h1 : 2 * α / 3 ≤ 2 / 3 := by linarith
    rw [Work.Spaces.eta]
    linarith
  have hC0pos : 0 < (ρ * cP) ^ 2 * (Work.Spaces.w z) ^ 2 * 2 ^ (-Work.Spaces.eta) := by
    refine mul_pos (mul_pos ?_ ?_) ?_
    · exact pow_pos (mul_pos hρpos hcPpos) 2
    · exact pow_pos hwpos 2
    · exact Real.rpow_pos_of_pos (by norm_num) _
  refine notIntegrableOn_Itheta_of_rpow_lower hC0pos hp
    (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ)
    ⟨ε, hεpos, hεlepi, fun θ hθ => ?_⟩
  exact le_trans (hpow θ hθ) (le_trans (hpow2 θ hθ) (hslot θ hθ))

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
