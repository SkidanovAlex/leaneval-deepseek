/-
# `Work.FTS.StrongPersist.H6Rows.MismatchSummand`

The four lemmas of the lead's ruling (2026-10-10, curric-46;
`StrongPersist/LEAD_strong_iface.md`, `REVIEW_strong_iface.md`,
`StrongPersist/LEAD_strong_iface.lean.txt`), copied verbatim into the
area's own buildable module.

They close the single obstructed Leibniz summand of the `A · D_z f` row of `Npair6`,
index `(a,b,a₁,b₁) = (1,5,1,0)`:

* `mismatch_pt` — the *pointwise* bound.  The coefficient's angular derivative is priced by the
  **flat order-0** norm through the σ-divisibility identity `D_θA = sin(2θ) · ∂_θA`: the gain
  `σ` converts the mismatched weight `σ^{-γ}` into `σ^{-η/2}·σ^{-γ/2}`, which is exactly the
  product of the two class weights carried by the two `f`-slots (`D_z⁶f` pure, `mixed 5 1 f`
  mixed).  This is why the refutations of the *per-summand* statements do not apply: they price
  the coefficient slot in `L²` (unbounded `∂_θA`), while the row's true coefficient
  `-2α·Vop(Ξ)` has bounded `∂_θ`.
* `mismatch_int` — the integrated form, `≤ Kθ/2 · HkSq α 6 f`.
* `abs_pth_le_coefTh` — the order-0 pointwise reading of the flat norm `CoefTh`.
* `L6Ctx.pth_Vop_le` — the **supply** of the flat price from `L6Ctx` itself, with no new
  clause: `|∂_θ Vop(Φ̃_f)| ≤ Ce α^{-1/2} Xn f` from `Ell6Ctx.hgo.Vth`
  (`VocabO.EllPkgGo.Vth`), and `|∂_θ Vop(Φ̃_*)| ≤ Cs α` from `StarPkgo.Vth`
  (`Ell6Ctx.hstar.Vth`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.H2.RegQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The mismatch summand, pointwise.**  For a coefficient `A` whose angular derivative is
priced by `Kθ`, the level-six integrand of the obstructed index `(1,5,1,0)` is `≤ Kθ/2` times
`HkIntegrand α 6 f`. -/
theorem mismatch_pt {α Kθ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A f : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hK : |Work.Spaces.pth A z θ| ≤ Kθ) :
    |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
        * Work.Spaces.DzIter 6 f z θ * Work.Spaces.mixed 5 1 f z θ|
      ≤ Kθ / 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  set s := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have hK0 : 0 ≤ Kθ := (abs_nonneg _).trans hK
  set Y := Work.Spaces.DzIter 6 f z θ
  set Z := Work.Spaces.mixed 5 1 f z θ
  set p := Work.Spaces.pth A z θ
  set W := Work.Spaces.w z with hWdef
  have hγ : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  set a := Y * (W / s ^ (Work.Spaces.eta / 2)) with ha
  set b := Z * Work.Spaces.Wt α z θ with hb
  -- the two slots of `HkIntegrand α 6 f`
  have hI : a ^ 2 + b ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    unfold Work.Spaces.HkIntegrand
    have h1 : a ^ 2 ≤ ∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      Finset.single_le_sum (f := fun i => (Work.Spaces.DzIter i f z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (fun i _ => sq_nonneg _) (by simp)
    have hnn : ∀ i j : ℕ, 0 ≤ (if 1 ≤ i ∧ i + j ≤ 6 then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i j; split_ifs <;> positivity
    have h2 : b ^ 2 ≤ ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0 := by
      have hin : b ^ 2 ≤ ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ 1 ∧ 1 + j ≤ 6 then (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) := by
        have := Finset.single_le_sum (f := fun j => if 1 ≤ 1 ∧ 1 + j ≤ 6 then
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          (fun j _ => hnn 1 j) (show (5 : ℕ) ∈ Finset.range (6 + 1) by simp)
        simpa using this
      exact hin.trans (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
          (show (1 : ℕ) ∈ Finset.range (6 + 1) by simp))
    exact add_le_add h1 h2
  -- the weight comparison `s^{1-γ} ≤ s^{-η/2} s^{-γ/2}`
  have hexp : s ^ (-(Work.Spaces.gam α)) * s
      ≤ s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2)) := by
    rw [← Real.rpow_add_one hs.ne', ← Real.rpow_add hs]
    apply Real.rpow_le_rpow_of_exponent_ge hs hs1
    rw [hγ, hη]; linarith
  have hW0 : 0 ≤ W := by
    rw [show W = (1 + z) ^ 2 / z ^ 2 from rfl]; positivity
  have hab : W ^ 2 * (s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2)))
      * (|Y| * |Z|) = |a| * |b| := by
    rw [ha, hb, abs_mul, abs_mul, Work.Spaces.Wt, Work.Spaces.wTheta, abs_mul,
      abs_div, abs_of_nonneg hW0, abs_of_pos (Real.rpow_pos_of_pos hs _),
      abs_of_pos (Real.rpow_pos_of_pos hs _), Real.rpow_neg hs.le]
    field_simp
  have hL : |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ * Y * Z|
      = W ^ 2 * (s ^ (-(Work.Spaces.gam α)) * s) * |p| * (|Y| * |Z|) := by
    have hD : Work.Spaces.Dth A z θ = s * p := rfl
    rw [hD, Work.FTS.TransportS.leafGam]
    simp only [abs_mul]
    rw [← hsdef, ← hWdef, abs_of_nonneg (sq_nonneg W), abs_of_pos (Real.rpow_pos_of_pos hs _),
      abs_of_pos hs]
    ring
  rw [hL]
  have hAM : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hYZ : 0 ≤ |Y| * |Z| := by positivity
  calc W ^ 2 * (s ^ (-(Work.Spaces.gam α)) * s) * |p| * (|Y| * |Z|)
      ≤ W ^ 2 * (s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2))) * Kθ
          * (|Y| * |Z|) := by
        apply mul_le_mul_of_nonneg_right _ hYZ
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) hK (abs_nonneg _)
          (by positivity)
    _ = Kθ * (|a| * |b|) := by rw [← hab]; ring
    _ ≤ Kθ * ((a ^ 2 + b ^ 2) / 2) := mul_le_mul_of_nonneg_left hAM hK0
    _ ≤ Kθ / 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
        have := mul_le_mul_of_nonneg_left hI hK0
        linarith

/-- **The mismatch summand, integrated**: linear in `HkSq α 6 f` (inside `H6Pair`'s budget). -/
theorem mismatch_int {α Kθ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A f : Fn}
    (hK : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.pth A z θ| ≤ Kθ)
    (hf : Work.Spaces.HkMem α 6 f) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
          * Work.Spaces.DzIter 6 f z θ * Work.Spaces.mixed 5 1 f z θ|
      ≤ Kθ / 2 * Work.Spaces.HkSq α 6 f := by
  have hK0 : 0 ≤ Kθ := (abs_nonneg _).trans (hK 1 1 one_pos one_pos
    (by linarith [Real.pi_gt_three]))
  have haeθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := (0 : ℝ))
      (b := π / 2))
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h
  have haez : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
    have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
    rwa [Measure.restrict_congr_set Ioi_ae_eq_Ici] at h
  have hinner : ∀ z : ℝ, 0 < z → z ∈ Work.Spaces.Iz →
      |∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
          * Work.Spaces.DzIter 6 f z θ * Work.Spaces.mixed 5 1 f z θ|
        ≤ Kθ / 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z hz hzI
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      ((hf.1 z hzI).const_mul _) ?_
    filter_upwards [haeθ] with θ hθ
    exact mismatch_pt hα hα1 hθ (hK z θ hz hθ.1 hθ.2)
  rw [Work.Spaces.HkSq, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (hf.2.const_mul _) ?_
  filter_upwards [haez, ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with z hz hzI
  exact hinner z hz hzI

/-- Order-0 pointwise reading of the flat norm. -/
theorem abs_pth_le_coefTh {l : ℕ} {V : Fn} (hmem : Work.FTS.VocabO.CoefThMem l V) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pth V z θ| ≤ Work.FTS.VocabO.CoefTh l V := by
  intro z θ hz hθ hθ'
  obtain ⟨K, hKb⟩ := hmem 0 0 (by omega)
  have h1 := Work.FTS.H2.le_supAbsO (g := Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
    hz hθ hθ' hKb
  have hnn : ∀ b i : ℕ, 0 ≤ (if b + i ≤ l then
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth V)) else 0) := by
    intro b i
    split_ifs
    · exact Real.sSup_nonneg (by rintro y ⟨_, _, _, _, _, rfl⟩; exact abs_nonneg _)
    · exact le_rfl
  have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
      ≤ Work.FTS.VocabO.CoefTh l V := by
    unfold Work.FTS.VocabO.CoefTh
    have hin : Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
        ≤ ∑ i ∈ Finset.range (l + 1), (if 0 + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 i (Work.Spaces.pth V)) else 0) := by
      have := Finset.single_le_sum (f := fun i => if 0 + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 i (Work.Spaces.pth V)) else 0)
        (fun i _ => hnn 0 i) (show 0 ∈ Finset.range (l + 1) by simp)
      simpa using this
    exact hin.trans (Finset.single_le_sum (f := fun b => ∑ i ∈ Finset.range (l + 1),
        if b + i ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth V))
        else 0) (fun b _ => Finset.sum_nonneg fun i _ => hnn b i)
        (show 0 ∈ Finset.range (l + 1) by simp))
  exact h1.trans h2

end Work.FTS.StrongPersist.H6Rows

namespace Work.FTS.StrongPersist.L6Ctx

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **Supply of the flat price from `L6Ctx`** (no new clause): the `D_z`-row coefficient's
perturbation half `Vop(Φ̃_f)` has `|∂_θ ·| ≤ Ce α^{-1/2} Xn f` on the open quadrant
(`Ell6Ctx.hgo.Vth`), the star half `|∂_θ ·| ≤ Cs α` (`StarPkgo.Vth`). -/
theorem pth_Vop_le {IP : ℝ → Fn → Fn → ℝ} {α M Ce Cs : ℝ} {E : Fn → Fn} {Φs : Fn}
    {g Φ : Fam} {τ : ℝ}
    (h : Work.FTS.StrongPersist.L6Ctx IP α M Ce Cs E Φs g Φ τ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α (slice g τ)
          (E (slice g τ)))) z θ|
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α (slice g τ)) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pth (Work.Construction.Vop (Work.Construction.PhiTil α
          (Work.Construction.Fstar α) Φs)) z θ| ≤ Cs * α) := by
  refine ⟨fun z θ hz hθ hθ' => ?_, fun z θ hz hθ hθ' => ?_⟩
  · exact (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh h.hell.hgo.Vth.1 z θ hz hθ hθ').trans
      h.hell.hgo.Vth.2
  · exact (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh h.hell.hstar.Vth.1 z θ hz hθ hθ').trans
      h.hell.hstar.Vth.2

end Work.FTS.StrongPersist.L6Ctx
