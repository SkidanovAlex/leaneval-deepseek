import Submission.Work.Landing.Land.Main
import Submission.Work.Landing.Family.deriv_tsq_iterate_odd_real
import Submission.Work.Landing.Family.iterate_one_eq_of_iterate_eq
import Submission.Work.Landing.Angle.firstReturn_rootAngles
import Submission.Work.Landing.Angle.exactPeriodAngle_paramAngle
import Submission.Work.Landing.Angle.periodicAngle_add_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The landing theorem for the tricorn family

On top of the ray transfer `Work.Landing.rayAccum_image` this file proves the landing statements
used by the rest of the project:

* `RayLands_image`, `rayAccum_iterate`, `RayLands_periodic` (for a fixed Böttcher coordinate);
* `landsAt_image`, `landsAt_iterate`, `landsAt_periodic`, `landsAt_unique` (parameterised form);
* `landsAt_repelling_or_parabolic` — **Milnor 18.10** for odd periods;
* the two concrete corners of the route: the root rays `371/1023`, `404/1023` are exchanged by
  the first return map (`rootRays_period`), and the window ray `23/63` cannot land at the
  characteristic parabolic point of the period-`5` orbit (`landsAt_paramAngle_not_parabolic`),
  together with the repelling form of that statement given the landing dichotomy for even periods.
-/

noncomputable section

open Classical
open Filter

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)
open scoped Topology ComplexConjugate

variable {c : ℂ} {φ : ℂ → ℂ} {θ : ℝ} {x y z : ℂ} {n k : ℕ}

/-! ## Landing at a fixed Böttcher coordinate -/

/-- The image of the landing point of a ray is the landing point of the image ray. -/
theorem RayLands_image (h : IsDynBottcher c φ) (hx : RayLands c φ θ x) :
    RayLands c φ (angDouble θ) (Tantibar c x) := by
  have hx' : rayAccum c φ θ = {x} := hx
  show rayAccum c φ (angDouble θ) = {Tantibar c x}
  rw [← rayAccum_image h θ, hx', Set.image_singleton]

/-- The `n`-fold transfer: the accumulation set of the ray at angle `(angDouble)^[n] θ` is the
image under `(T_c)^[n]` of the accumulation set of the ray at angle `θ`. -/
theorem rayAccum_iterate (h : IsDynBottcher c φ) (θ : ℝ) (n : ℕ) :
    rayAccum c φ ((angDouble)^[n] θ) = (Tantibar c)^[n] '' rayAccum c φ θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← rayAccum_image h, ih, ← Set.image_comp,
      Function.iterate_succ']

/-- **The landing point of a periodic ray is periodic.** -/
theorem RayLands_periodic (h : IsDynBottcher c φ) (hx : RayLands c φ θ x)
    (hper : PeriodicAngle θ n) : (Tantibar c)^[n] x = x := by
  have h1 : rayAccum c φ ((angDouble)^[n] θ) = {(Tantibar c)^[n] x} := by
    rw [rayAccum_iterate h θ n, (show rayAccum c φ θ = {x} from hx), Set.image_singleton]
  rw [PeriodicAngle] at hper
  rw [hper] at h1
  have hmem : (Tantibar c)^[n] x ∈ rayAccum c φ θ := by
    rw [h1]
    exact Set.mem_singleton _
  rw [(show rayAccum c φ θ = {x} from hx)] at hmem
  simpa using hmem

/-! ## The parameterised form -/

/-- The image of a landing point is the landing point of the image ray. -/
theorem landsAt_image (hx : landsAt c θ x) : landsAt c (angDouble θ) (Tantibar c x) := by
  obtain ⟨φ, hφ, hland⟩ := hx
  exact ⟨φ, hφ, RayLands_image hφ hland⟩

/-- Iterating `landsAt_image`. -/
theorem landsAt_iterate (hx : landsAt c θ x) (n : ℕ) :
    landsAt c ((angDouble)^[n] θ) ((Tantibar c)^[n] x) := by
  obtain ⟨φ, hφ, hland⟩ := hx
  refine ⟨φ, hφ, ?_⟩
  show rayAccum c φ ((angDouble)^[n] θ) = {(Tantibar c)^[n] x}
  rw [rayAccum_iterate hφ θ n, (show rayAccum c φ θ = {x} from hland), Set.image_singleton]

/-- **The landing point of a periodic ray is periodic.** -/
theorem landsAt_periodic (hx : landsAt c θ x) (hper : PeriodicAngle θ n) : (Tantibar c)^[n] x = x := by
  obtain ⟨φ, hφ, hland⟩ := hx
  exact RayLands_periodic hφ hland hper

/-- The accumulation set only depends on the values of the Böttcher coordinate on the escaping
set. -/
theorem rayAccum_congr {c : ℂ} {φ ψ : ℂ → ℂ} (h : ∀ w : ℂ, Escaping c w → φ w = ψ w) (θ : ℝ) :
    rayAccum c φ θ = rayAccum c ψ θ := by
  have htrunc : ∀ ρ : ℝ, trunc c φ θ ρ = trunc c ψ θ ρ := by
    intro ρ
    ext w
    constructor
    · rintro ⟨hw, hwρ⟩
      exact ⟨⟨hw.1, by simpa [← h w hw.1] using hw.2⟩, by simpa [← h w hw.1] using hwρ⟩
    · rintro ⟨hw, hwρ⟩
      exact ⟨⟨hw.1, by simpa [h w hw.1] using hw.2⟩, by simpa [h w hw.1] using hwρ⟩
  ext w
  simp only [rayAccum_def, Set.mem_setOf_eq, htrunc]

/-- The landing point of a ray is unique: a ray lands at a single point. -/
theorem landsAt_unique (hx : landsAt c θ x) (hy : landsAt c θ y) : x = y := by
  obtain ⟨φ, hφ, hx'⟩ := hx
  obtain ⟨ψ, hψ, hy'⟩ := hy
  have hcongr : rayAccum c φ θ = rayAccum c ψ θ :=
    rayAccum_congr (fun w hw => Work.ParamRays.isDynBottcher_unique hφ hψ hw) θ
  have hx'' : rayAccum c φ θ = {x} := hx'
  have hy'' : rayAccum c ψ θ = {y} := hy'
  rw [hcongr] at hx''
  rw [hx''] at hy''
  have hmem : y ∈ ({(x : ℂ)} : Set ℂ) := by
    rw [hy'']
    exact Set.mem_singleton y
  simpa [eq_comm] using hmem

/-! ## Milnor 18.10 -/

/-- **Milnor 18.10.**  A ray landing at a point of odd period `k` lands at a repelling or
parabolic periodic point.  The two inputs are `PeriodicRaysLand` (used implicitly: the ray has
already landed) and `AttractingCyclesInner` (attracting cycles are not on the boundary of the
basin of infinity); `deriv_tsq_iterate_odd_real` converts "not attracting" into the dichotomy. -/
theorem landsAt_repelling_or_parabolic (hland : landsAt c θ x) (hper : PeriodicAngle θ k)
    (hk : 0 < k) (hodd : Odd k) (hgeo : AttractingCyclesInner c) :
    IsRepelling c k x ∨ IsParabolic c k x := by
  have hxk : (Tantibar c)^[k] x = x := landsAt_periodic hland hper
  have hclos : x ∈ closure (escapingSet c) := by
    obtain ⟨φ, hφ, hland'⟩ := hland
    have hx' : x ∈ rayAccum c φ θ := by
      rw [show rayAccum c φ θ = {x} from hland']
      exact Set.mem_singleton x
    exact rayAccum_subset_closure_escaping c φ θ hx'
  have hnotattr : ¬ IsAttracting c k x := by
    intro hattr
    obtain ⟨ε, hε, hball⟩ := hgeo x ⟨k, hattr⟩
    rw [Metric.mem_closure_iff] at hclos
    obtain ⟨w, hw, hwd⟩ := hclos ε hε
    exact hball w (by simpa only [dist_comm x w, dist_eq_norm] using hwd) hw
  obtain ⟨r, hr, hrmul⟩ := Family.deriv_tsq_iterate_odd_real c hodd hxk
  have hge : 1 ≤ r := by
    have h1 : ¬ ‖deriv ((Work.Landing.Tsq c)^[k]) x‖ < 1 :=
      fun hlt => hnotattr ⟨⟨hk, hxk⟩, hlt⟩
    rw [hrmul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr] at h1
    exact not_lt.mp h1
  rcases lt_or_eq_of_le hge with hlt | heq
  · refine Or.inl ⟨⟨hk, hxk⟩, ?_⟩
    show 1 < ‖deriv ((Work.Landing.Tsq c)^[k]) x‖
    rw [hrmul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr]
    exact hlt
  · refine Or.inr ⟨⟨hk, hxk⟩, ?_⟩
    show deriv ((Work.Landing.Tsq c)^[k]) x = 1
    rw [hrmul, ← heq]
    simp

/-! ## The two concrete corners of the route -/

/-- **The root rays are exchanged by the first return map.**  If both root rays of the non-real
period-`5` component land at the same point `z` (the `rays` clause of `Work.EL.RootParabolic`),
then `z` is fixed by `(T_c)^5` and by `(T_c)^10`: `z` is the dynamic root of the period-`5` orbit. -/
theorem rootRays_period (h : RootRaysLand c z) :
    (Tantibar c)^[5] z = z ∧ (Tantibar c)^[10] z = z := by
  obtain ⟨h1, h2⟩ := h
  have hswap := Angle.firstReturn_rootAngles
  have h5 : (Tantibar c)^[5] z = z := by
    refine landsAt_unique ?_ h2
    simpa only [hswap.1] using landsAt_iterate h1 5
  refine ⟨h5, ?_⟩
  rw [show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, h5, h5]

/-- **Rotation number zero, provable form.**  If two rays land at the same point `z` and the second
angle is the `k`-fold angle-double of the first, then the `k`-th return map fixes `z` (hence so
does the `2k`-th): this is the dynamical content of "the rays landing at a periodic point are
permuted with rotation number zero". -/
theorem landsAt_pair_exchange {c : ℂ} {θ : ℝ} {z : ℂ} {k : ℕ}
    (h1 : landsAt c θ z) (h2 : landsAt c ((angDouble)^[k] θ) z) :
    (Tantibar c)^[k] z = z ∧ (Tantibar c)^[2 * k] z = z := by
  have hfix : (Tantibar c)^[k] z = z :=
    landsAt_unique (landsAt_iterate h1 k) h2
  refine ⟨hfix, ?_⟩
  rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hfix, hfix]

/-- **`hθ`, combinatorial part.**  The window angle `23/63` has exact period `6`.  The landing
point of a periodic ray is periodic, so a landing point of `R_c(23/63)` is fixed by `(T_c)^6`;
if it were also fixed by `(T_c)^5` it would be a fixed point of `T_c`, contradicting the exact
period `5` of the parabolic cycle.  Hence `R_c(23/63)` does not land at the characteristic
parabolic point. -/
theorem landsAt_paramAngle_not_parabolic (hland : landsAt c paramAngle z)
    (h5 : (Tantibar c)^[5] z = z) (hne : (Tantibar c) z ≠ z) : False := by
  have h6 : (Tantibar c)^[6] z = z := landsAt_periodic hland Angle.exactPeriodAngle_paramAngle.2.1
  exact hne (Family.iterate_one_eq_of_iterate_eq (Tantibar c) h5 h6 (by norm_num))

/-- **The landing dichotomy for the even period `6`** (Milnor 18.10 for an even period, together
with the exclusion of neutrally indifferent non-parabolic landing points, which is what the
endgame needs): the landing point of a ray of exact period `6` is repelling, unless it lies on a
parabolic cycle. -/
def EvenPeriodLandingDichotomy (c : ℂ) : Prop :=
  ∀ (θ : ℝ) (z : ℂ), PeriodicAngle θ 6 → ExactPeriodAngle θ 6 → landsAt c θ z →
    (∃ k : ℕ, (Tantibar c)^[k] z = z ∧ 1 < ‖multiplier2 c k z‖) ∨ (∃ m : ℕ, IsParabolic c m z)

/-- **`hθ`.**  With the landing dichotomy for even periods, the ray `23/63` lands at a repelling
periodic point. -/
theorem landsAt_paramAngle_repelling (hdich : EvenPeriodLandingDichotomy c)
    (hpar : ∀ m : ℕ, ¬ IsParabolic c m z) (hland : landsAt c paramAngle z) :
    ∃ k : ℕ, (Tantibar c)^[k] z = z ∧ 1 < ‖multiplier2 c k z‖ := by
  rcases hdich paramAngle z Angle.exactPeriodAngle_paramAngle.2.1 Angle.exactPeriodAngle_paramAngle
    hland with h | h
  · exact h
  · exact absurd h (by rintro ⟨m, hm⟩; exact hpar m hm)

end Work.Landing
