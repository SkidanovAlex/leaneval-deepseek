import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.cartan
import Submission.Work.L62.branch_unique
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.lift_section
import Submission.Work.Horn.basic
import Submission.Work.L62.avail_horn_section_up
import Submission.Work.L62.avail_descent_upper

/-!
# `Work.L62.avail_up` — the upper end is available only for `Im β > 0`

Shishikura's Lemma 6.2 pairs every `β` with the end (`B^u` or `B^ℓ`) that *avoids the critical
value* of `ĥ = Ẽ - β`.  Here we prove that the upper end can only be available when `Im β > 0`.

Setting (`d : ParabData g₀ D`, `hd : HornData d`): the lifted horn map `d.E = Φ ∘ φ` is
`T`-equivariant and holomorphic on the two components `hd.Bu` (upper) and `hd.Bl` (lower) of
`d.DE`, with `Bu ⊇ {η < Im ·}` and `Bu ⊆ {-η ≤ Im ·}` (`Bu_im_ge`), and its critical values form
the single `T`-orbit `hd.v + ℤ`.

**Hypothesis** (`AvailableUp`): `v - β ∉ Bu + ℤ`, i.e. the critical value of `ĥ = d.E - β` does
not lie in `B^u`.

**Conclusion**: `0 < Im β`.

The proof is Shishikura's Schwarz argument (§6, Step 2), transported to the workspace's sign
convention (`ĥ = Ẽ - β`, so that the pushed-down perturbation is `e^{-2πiβ}·pushdown Ẽ`):

* `avail_horn_section_up` provides a holomorphic `T`-equivariant section `σ` of `ĥ` over `Bu`
  (Lemma 5.3, i.e. the covering `d.E : Bu → ℂ` over the complement of the critical class), with
  `σ w = w + β + o(1)` at the upper end;
* `avail_descent_upper` pushes `σ` down to the cylinder: a holomorphic `H` on
  `Ω = {0} ∪ π(B^u)` with `H 0 = 0`, `H '' Ω ⊆ Ω`, `deriv H 0 = π(β) = e^{2πiβ}` and
  `pushdown ĥ ∘ H = id`;
* `Ω` is open, bounded and preconnected, so **Cartan's theorem** (`Work.L62.cartan`) gives
  `‖deriv H 0‖ ≤ 1`, with equality forcing `H` to be a bijection of `Ω`.  But `ĥ` is not
  injective on `Ω` (`HornData.inf_u`: every value has infinitely many preimages in `B^u`), and
  `pushdown ĥ ∘ H = id` then forbids `H` from being surjective.  Hence
  `‖e^{2πiβ}‖ = e^{-2π·Im β} < 1`, i.e. `0 < Im β`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Metric
open scoped Topology
open Work.Horn.MandelDim

noncomputable section

/-! ## Elementary facts about `π = piExp` -/

theorem piExp_eq_exp (w : ℂ) : piExp w = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) := rfl

theorem continuous_piExp : Continuous piExp := by
  have h : piExp = fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) := rfl
  rw [h]
  exact Complex.continuous_exp.comp (continuous_const.mul continuous_id)

private theorem isOpenMap_piExp : IsOpenMap piExp := by
  have he : piExp = fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) := rfl
  rw [he]
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have h2 : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))
      = Complex.exp ∘ ⇑(Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I) hc) := by
    funext w
    rw [Function.comp_apply, Homeomorph.coe_mulLeft₀]
  rw [h2]
  exact Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ hc).isOpenMap

private theorem isOpen_piExp_image {S : Set ℂ} (hS : IsOpen S) : IsOpen (piExp '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro ζ ⟨w, hw, rfl⟩
  exact isOpenMap_piExp.image_mem_nhds (hS.mem_nhds hw)

theorem norm_piExp (w : ℂ) : ‖piExp w‖ = Real.exp (-(2 * Real.pi) * w.im) := by
  rw [piExp_eq_exp w, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp

/-- The imaginary part of the lift `log ζ / (2πi)`. -/
private theorem log_div_im (ζ : ℂ) :
    (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im
      = -(Real.log ‖ζ‖ / (2 * Real.pi)) := by
  rw [Complex.div_im, Complex.log_re, Complex.log_im]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq ((2 : ℂ) * Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [show ((2 : ℂ) * Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h1, h2, h3]
  field_simp
  ring

/-! ## The cylinder neighbourhood `Ω = {0} ∪ π(B^u)` of the upper end -/

/-- The upper end of the cylinder, as a neighbourhood of `0 = π(+i∞)`: `{0} ∪ π '' B^u`. -/
def upOmega {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) (hd : HornData d) : Set ℂ :=
  insert 0 (piExp '' hd.Bu)

/-- Every point of the punctured disc of radius `e^{-2πη}` belongs to `π '' B^u`
(it has a lift above the line `Im = η`, which lies in `B^u`). -/
theorem mem_piExp_image_Bu_of_norm_lt {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D)
    (hd : HornData d) {ζ : ℂ} (hζ : ζ ≠ 0)
    (h : ‖ζ‖ < Real.exp (-(2 * Real.pi) * hd.η)) : ζ ∈ piExp '' hd.Bu := by
  refine ⟨Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I), hd.upper ?_, piExp_log_div ζ hζ⟩
  have hpos : (0 : ℝ) < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hlog : Real.log ‖ζ‖ < -(2 * Real.pi) * hd.η := by
    have h1 := Real.log_lt_log hpos h
    rwa [Real.log_exp] at h1
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlt : Real.log ‖ζ‖ / (2 * Real.pi) < -hd.η := by
    have h1 := div_lt_div_of_pos_right hlog h2pi
    rwa [show (-(2 * Real.pi) * hd.η) / (2 * Real.pi) = -hd.η by field_simp] at h1
  show hd.η < (Complex.log ζ / (2 * (Real.pi : ℂ) * Complex.I)).im
  rw [log_div_im]
  linarith

theorem upOmega_eq_ball_union {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D)
    (hd : HornData d) :
    upOmega d hd = ball 0 (Real.exp (-(2 * Real.pi) * hd.η)) ∪ piExp '' hd.Bu := by
  ext ζ
  constructor
  · intro hζ
    rcases mem_insert_iff.mp hζ with rfl | h
    · exact Or.inl (mem_ball_self (Real.exp_pos _))
    · by_cases hb : ‖ζ‖ < Real.exp (-(2 * Real.pi) * hd.η)
      · exact Or.inl (mem_ball_zero_iff.mpr hb)
      · exact Or.inr h
  · rintro (h | h)
    · rcases eq_or_ne ζ 0 with rfl | hne
      · exact mem_insert_iff.mpr (Or.inl rfl)
      · exact mem_insert_iff.mpr (Or.inr
          (mem_piExp_image_Bu_of_norm_lt d hd hne (mem_ball_zero_iff.mp h)))
    · exact mem_insert_iff.mpr (Or.inr h)

theorem isOpen_upOmega {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) (hd : HornData d) :
    IsOpen (upOmega d hd) := by
  rw [upOmega_eq_ball_union d hd]
  exact isOpen_ball.union (isOpen_piExp_image hd.Bu_open)

/-- `Ω` is bounded: `Bu ⊆ {-η ≤ Im ·}` gives `|π w| ≤ e^{2πη}`. -/
theorem isBounded_upOmega {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) (hd : HornData d) :
    Bornology.IsBounded (upOmega d hd) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    ⟨Real.exp (2 * Real.pi * hd.η), ?_⟩
  intro ζ hζ
  rcases mem_insert_iff.mp hζ with rfl | ⟨w, hw, rfl⟩
  · exact mem_closedBall_self (Real.exp_pos _).le
  · rw [mem_closedBall_zero_iff, norm_piExp]
    have him := Bu_im_ge d hd hw
    have h1 : -(2 * Real.pi) * w.im ≤ 2 * Real.pi * hd.η := by
      nlinarith [Real.pi_pos, him]
    exact Real.exp_le_exp.mpr h1

theorem preconnected_upOmega {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D)
    (hd : HornData d) : IsPreconnected (upOmega d hd) := by
  -- a point of `π '' B^u` which also lies in the ball: `π (i (η+1)) = e^{-2π(η+1)}`
  set z₀ : ℂ := piExp (Complex.I * (hd.η + 1)) with hz₀
  have hz₀S : z₀ ∈ piExp '' hd.Bu :=
    ⟨Complex.I * (hd.η + 1), hd.upper (by simp), rfl⟩
  have hnorm : ‖z₀‖ = Real.exp (-(2 * Real.pi) * (hd.η + 1)) := by
    rw [hz₀, norm_piExp]
    congr 1
    simp
  have hz₀B : z₀ ∈ Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi) * hd.η)) := by
    rw [mem_ball_zero_iff, hnorm]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hpre_ball : IsPreconnected (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi) * hd.η))) :=
    (convex_ball (0 : ℂ) _).isPreconnected
  have hpre_Bu : IsPreconnected (piExp '' hd.Bu) :=
    hd.Bu_conn.isPreconnected.image piExp continuous_piExp.continuousOn
  have hset : upOmega d hd
      = Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi) * hd.η)) ∪ piExp '' hd.Bu :=
    upOmega_eq_ball_union d hd
  rw [hset]
  exact IsPreconnected.union z₀ hz₀B hz₀S hpre_ball hpre_Bu

/-! ## Non-injectivity of `ĥ` on `Ω` -/

/-- **Two distinct preimages of the same value.**  By `HornData.inf_u`, the fibre of the
pushed-down map `pushdown (Ẽ - β)` over `π(y - β)` is infinite inside `B^u`; in particular it
contains two distinct points. -/
theorem exists_two_preimages {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) (hd : HornData d)
    {β : ℂ} {y : ℂ} :
    ∃ ζ₁ ζ₂ : ℂ, ζ₁ ∈ piExp '' hd.Bu ∧ ζ₂ ∈ piExp '' hd.Bu ∧ ζ₁ ≠ ζ₂ ∧
      pushdown (fun u => d.E u - β) ζ₁ = piExp (y - β) ∧
      pushdown (fun u => d.E u - β) ζ₂ = piExp (y - β) := by
  set S : Set ℂ := piExp '' {w : ℂ | w ∈ hd.Bu ∧ d.E w = y} with hS
  have hval : ∀ ζ ∈ S, pushdown (fun u => d.E u - β) ζ = piExp (y - β) := by
    rintro ζ ⟨w, ⟨hw, hEw⟩, rfl⟩
    rw [pushdown_piExp hd.Bu_T ?_ hw, hEw]
    intro u hu _
    show d.E (u + 1) - β = d.E u - β + 1
    rw [E_add_one_Bu d hd hu]
    ring
  have hsub : S ⊆ piExp '' hd.Bu := image_mono (fun w hw => hw.1)
  have hinf : S.Infinite := hd.inf_u y
  obtain ⟨a, haS⟩ := hinf.nonempty
  obtain ⟨b, hb⟩ := (hinf.sdiff (Set.finite_singleton a)).nonempty
  exact ⟨a, b, hsub haS, hsub hb.1, fun hab => hb.2 hab.symm, hval a haS, hval b hb.1⟩

/-! ## The sign implication -/

theorem avail_up {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ}
    (havoid : ∀ w ∈ hd.Bu, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)) : 0 < β.im := by
  -- the `T`-equivariant holomorphic section of `ĥ = d.E - β` over `B^u`
  obtain ⟨y₀, x₀, σ, hy₀, _hx₀, _hxy, hσd, _hσy, hσsec, hσeq, hσasymp⟩ :=
    avail_horn_section_up d hd havoid
  -- its descent to the cylinder
  obtain ⟨H, hH0, hHdiff, hHmem, hHderiv, hHsec⟩ :=
    avail_descent_upper d hd hσd (fun y hy => (hσsec y hy).1) (fun y hy => (hσsec y hy).2)
      hσeq hσasymp
  -- `Ω` and Cartan's theorem
  obtain ⟨hle, hrigid⟩ :=
    cartan (isOpen_upOmega d hd) (isBounded_upOmega d hd) (preconnected_upOmega d hd)
      hHdiff hHmem (mem_insert_iff.mpr (Or.inl rfl)) hH0
  have hderiv : deriv H 0 = piExp β := hHderiv.deriv
  -- strictness: `H` cannot be a bijection of `Ω`, because `ĥ` is not injective on `Ω`
  have hlt : ‖deriv H 0‖ < 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      obtain ⟨hsurj, -⟩ := hrigid h
      obtain ⟨ζ₁, ζ₂, hζ₁, hζ₂, hne, hv₁, hv₂⟩ := exists_two_preimages d hd (β := β) (y := y₀)
      obtain ⟨η₁, hη₁, hHη₁⟩ := hsurj (mem_insert_iff.mpr (Or.inr hζ₁))
      obtain ⟨η₂, hη₂, hHη₂⟩ := hsurj (mem_insert_iff.mpr (Or.inr hζ₂))
      have h1 : η₁ = pushdown (fun u => d.E u - β) ζ₁ := by
        rw [← hHsec η₁ hη₁, hHη₁]
      have h2 : η₂ = pushdown (fun u => d.E u - β) ζ₂ := by
        rw [← hHsec η₂ hη₂, hHη₂]
      have heq : η₁ = η₂ := by rw [h1, hv₁, ← hv₂, ← h2]
      exact hne (by rw [← hHη₁, heq, hHη₂])
  have hnorm : ‖piExp β‖ < 1 := by rw [← hderiv]; exact hlt
  rw [norm_piExp] at hnorm
  have hx : -(2 * Real.pi) * β.im < 0 := Real.exp_lt_one_iff.mp hnorm
  nlinarith [Real.pi_pos]

end

end Work.L62
