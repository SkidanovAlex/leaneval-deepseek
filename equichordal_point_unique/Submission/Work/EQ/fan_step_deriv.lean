import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.fan_base

namespace Work.EQ

open Complex

noncomputable section

/-- The principal square root of a real square: `((y : ℂ)^2)^{1/2} = |y|`. -/
lemma cpow_half_ofReal_sq (y : ℝ) : ((y : ℂ) ^ 2) ^ ((1 : ℂ) / 2) = ((|y| : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow]
  rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (sq_nonneg y)]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- **The backward branch on the real axis.**  For a real axis point `(x, 0)` the principal
square root `((x + a/2)^2)^{1/2}` is the modulus `|x + a/2|`, so `invBranch a s` maps it to the
axis point `(-x + (±1)(x + a/2)/|x + a/2|, 0)`.  No hypothesis on `x + a/2` is needed: both sides
degenerate to `(-x, 0)` when `x + a/2 = 0`. -/
lemma invBranch_axis_val (a : ℝ) (s : Bool) (x : ℝ) :
    invBranch a s ((x : ℂ), (0 : ℂ)) =
      (((-x + (if s then (1 : ℝ) else -1) * (x + a / 2) / |x + a / 2| : ℝ) : ℂ), (0 : ℂ)) := by
  have h1 : (x : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ) := by push_cast; ring
  have hd : ((((x + a / 2 : ℝ)) : ℂ) ^ 2) ^ ((1 : ℂ) / 2) = ((|x + a / 2| : ℝ) : ℂ) :=
    cpow_half_ofReal_sq (x + a / 2)
  have hz : (0 : ℂ) ^ 2 = 0 := by norm_num
  rcases s with _ | _ <;>
    simp only [invBranch, hz, add_zero, h1, hd, neg_zero, mul_zero, zero_div,
      Bool.false_eq_true, ite_true, ite_false] <;>
    refine Prod.ext ?_ ?_ <;> push_cast <;> ring

/-- **The derivative of the backward branch along the real axis.**  If `F, G` are differentiable
paths through an axis point `(x, 0)` off the isotropic point `x = -a/2`, then the first
coordinate of `invBranch a s (F, G)` is differentiable at `0` and the second one has derivative
`G'(0) * ((±1)/|x + a/2| - 1)` there: on the axis the Jacobian of `invBranch a s` is the diagonal
matrix `diag(-1, -1 + (±1)/|x + a/2|)`. -/
lemma invBranch_axis_deriv {a : ℝ} {s : Bool} {F G : ℂ → ℂ} {F' G' : ℂ} {x : ℝ}
    (hF : HasDerivAt F F' 0) (hG : HasDerivAt G G' 0)
    (hF0 : F 0 = (x : ℂ)) (hG0 : G 0 = 0) (hx : x + a / 2 ≠ 0) :
    DifferentiableAt ℂ (fun u => (invBranch a s (F u, G u)).1) 0 ∧
    HasDerivAt (fun u => (invBranch a s (F u, G u)).2)
      (G' * ((if s then (1 : ℂ) else -1) / ((|x + a / 2| : ℝ) : ℂ) - 1)) 0 := by
  have hR : ((|x + a / 2| : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, ne_eq, Complex.ofReal_inj]
    exact abs_ne_zero.mpr hx
  let c : ℂ := ((a / 2 : ℝ) : ℂ)
  let D : ℂ → ℂ := fun u => (F u + c) ^ 2 + G u ^ 2
  let ρ : ℂ → ℂ := fun u => D u ^ ((1 : ℂ) / 2)
  let sg : ℂ := (if s then (1 : ℂ) else -1)
  let D' : ℂ := ↑(2 : ℕ) * (F 0 + c) ^ (2 - 1) * F' + ↑(2 : ℕ) * G 0 ^ (2 - 1) * G'
  have hD0 : D 0 = (((x + a / 2) ^ 2 : ℝ) : ℂ) := by
    change (F 0 + c) ^ 2 + G 0 ^ 2 = (((x + a / 2) ^ 2 : ℝ) : ℂ)
    rw [hF0, hG0]
    rw [show (x : ℂ) + c = ((x + a / 2 : ℝ) : ℂ) by
          change (x : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ); push_cast; ring]
    rw [show (0 : ℂ) ^ 2 = 0 by norm_num, add_zero, ← Complex.ofReal_pow]
  have hslit : D 0 ∈ Complex.slitPlane := by
    rw [hD0, Complex.mem_slitPlane_iff]
    exact Or.inl (by rw [Complex.ofReal_re]; exact sq_pos_of_ne_zero hx)
  have hρ0 : ρ 0 = ((|x + a / 2| : ℝ) : ℂ) := by
    change D 0 ^ ((1 : ℂ) / 2) = ((|x + a / 2| : ℝ) : ℂ)
    rw [hD0, Complex.ofReal_pow]
    exact cpow_half_ofReal_sq (x + a / 2)
  have hρ0ne : ρ 0 ≠ 0 := by rw [hρ0]; exact hR
  have hD' : HasDerivAt D D' 0 := by
    have h1 : HasDerivAt (fun u : ℂ => (F u + c) ^ 2) (↑(2 : ℕ) * (F 0 + c) ^ (2 - 1) * F') 0 :=
      (hF.add_const c).pow 2
    have h2 : HasDerivAt (fun u : ℂ => G u ^ 2) (↑(2 : ℕ) * G 0 ^ (2 - 1) * G') 0 := hG.pow 2
    have h3 : HasDerivAt (fun u : ℂ => (F u + c) ^ 2 + G u ^ 2) D' 0 := h1.add h2
    exact h3
  obtain ⟨ρd, hρ'⟩ : ∃ ρd : ℂ, HasDerivAt ρ ρd 0 :=
    ⟨((1 : ℂ) / 2) * D 0 ^ ((1 : ℂ) / 2 - 1) * D', hD'.cpow_const hslit⟩
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun u : ℂ => -(F u)) (-F') 0 := hF.neg
    obtain ⟨q, h2⟩ : ∃ q : ℂ, HasDerivAt (fun u : ℂ => sg * (F u + c) / ρ u) q 0 :=
      ⟨_, ((hF.add_const c).const_mul sg).div hρ' hρ0ne⟩
    exact (h1.add h2).differentiableAt
  · have hfun : (fun u : ℂ => (invBranch a s (F u, G u)).2)
        = fun u : ℂ => -(G u) + sg * (G u) / ρ u := by
      funext u
      rfl
    have h1 : HasDerivAt (fun u : ℂ => -(G u)) (-G') 0 := hG.neg
    have h2 : HasDerivAt (fun u : ℂ => sg * (G u) / ρ u)
        ((sg * G' * ρ 0 - sg * G 0 * ρd) / ρ 0 ^ 2) 0 :=
      (hG.const_mul sg).div hρ' hρ0ne
    have h3 : HasDerivAt (fun u : ℂ => -(G u) + sg * (G u) / ρ u)
        (-G' + (sg * G' * ρ 0 - sg * G 0 * ρd) / ρ 0 ^ 2) 0 := h1.add h2
    rw [hfun]
    have hgoal : -G' + (sg * G' * ρ 0 - sg * G 0 * ρd) / ρ 0 ^ 2
        = G' * (sg / ((|x + a / 2| : ℝ) : ℂ) - 1) := by
      rw [hρ0, hG0]
      simp only [mul_zero, sub_zero, zero_mul]
      field_simp
      ring
    rw [hgoal] at h3
    exact h3

/-- **One step of the stable fan: centre and derivative recursion.** Let `ε` be a branch word
whose fan map is differentiable at `0` and whose centre is `(x, 0)` with `x + a/2 ≠ 0`. Then
prepending the letter `s` (`true` = principal branch `T`, `false` = non-principal branch `F`):
* the new centre is `-x + (±1)(x+a/2)/|x+a/2|`, again on the real axis;
* the new fan map is differentiable at `0`;
* the derivative of its second coordinate at `0` is `λ(-1 ± 1/|x+a/2|)` times that of `fan a h ε`.
This is the recursion behind Rychlik's product formula (110) for the characteristic value: on
the real axis the backward branch `invBranch a s` has diagonal derivative and the vertical
multiplier is `-1 + s/|x+a/2|`, and the argument is scaled by `λ`. -/
theorem fan_step_deriv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} (ε : List Bool) (s : Bool)
    {x : ℝ} (hc : fan a h ε 0 = ((x : ℂ), (0 : ℂ))) (hx : x + a / 2 ≠ 0)
    (hd₁ : DifferentiableAt ℂ (fun u => (fan a h ε u).1) 0)
    (hd₂ : DifferentiableAt ℂ (fun u => (fan a h ε u).2) 0) :
    fan a h (s :: ε) 0 =
        (((-x + (if s then 1 else -1) * (x + a / 2) / |x + a / 2| : ℝ) : ℂ), (0 : ℂ)) ∧
    DifferentiableAt ℂ (fun u => (fan a h (s :: ε) u).1) 0 ∧
    DifferentiableAt ℂ (fun u => (fan a h (s :: ε) u).2) 0 ∧
    deriv (fun u => (fan a h (s :: ε) u).2) 0 =
      ((eqLam a * (-1 + (if s then 1 else -1) / |x + a / 2|) : ℝ) : ℂ) *
        deriv (fun u => (fan a h ε u).2) 0 := by
  -- the shift `u ↦ λ u` is complex linear
  have hlin : HasDerivAt (fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u) (((eqLam a : ℝ) : ℂ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (((eqLam a : ℝ) : ℂ))
  -- the two coordinates of `u ↦ fan a h ε (λ u)`
  have hA' : HasDerivAt (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).1)
      (deriv (fun u : ℂ => (fan a h ε u).1) 0 * ((eqLam a : ℝ) : ℂ)) 0 := by
    have this := HasDerivAt.comp (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
      (h₂ := fun z : ℂ => (fan a h ε z).1)
      (h' := ((eqLam a : ℝ) : ℂ))
      (h₂' := deriv (fun u : ℂ => (fan a h ε u).1) 0) 0
      (by simpa only [mul_zero] using hd₁.hasDerivAt) hlin
    exact this
  have hB' : HasDerivAt (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).2)
      (deriv (fun u : ℂ => (fan a h ε u).2) 0 * ((eqLam a : ℝ) : ℂ)) 0 := by
    have this := HasDerivAt.comp (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
      (h₂ := fun z : ℂ => (fan a h ε z).2)
      (h' := ((eqLam a : ℝ) : ℂ))
      (h₂' := deriv (fun u : ℂ => (fan a h ε u).2) 0) 0
      (by simpa only [mul_zero] using hd₂.hasDerivAt) hlin
    exact this
  have hA0 : (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).1) 0 = (x : ℂ) := by
    change (fan a h ε (((eqLam a : ℝ) : ℂ) * 0)).1 = (x : ℂ)
    rw [mul_zero, hc]
  have hB0 : (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).2) 0 = 0 := by
    change (fan a h ε (((eqLam a : ℝ) : ℂ) * 0)).2 = 0
    rw [mul_zero, hc]
  obtain ⟨hFst, hSnd⟩ := invBranch_axis_deriv (a := a) (s := s) (x := x)
    (F := fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).1)
    (G := fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).2)
    (F' := deriv (fun u : ℂ => (fan a h ε u).1) 0 * ((eqLam a : ℝ) : ℂ))
    (G' := deriv (fun u : ℂ => (fan a h ε u).2) 0 * ((eqLam a : ℝ) : ℂ))
    hA' hB' hA0 hB0 hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hval : fan a h (s :: ε) 0 = invBranch a s ((x : ℂ), (0 : ℂ)) := by
      rw [fan, mul_zero, hc]
    rw [hval, invBranch_axis_val]
  · exact hFst
  · exact hSnd.differentiableAt
  · have hderiv : deriv (fun u : ℂ => (fan a h (s :: ε) u).2) 0
        = (deriv (fun u : ℂ => (fan a h ε u).2) 0 * ((eqLam a : ℝ) : ℂ)) *
          ((if s then (1 : ℂ) else -1) / ((|x + a / 2| : ℝ) : ℂ) - 1) := hSnd.deriv
    rw [hderiv]
    rcases s with _ | _ <;>
      simp only [Bool.false_eq_true, ite_true, ite_false] <;> push_cast <;> ring

end

end Work.EQ
