import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

open Finset

namespace Work.Maximal.mstOrtho

/-! ### Auxiliary circle-character lemmas

Everything here is elementary algebra of the characters `fourier n : 𝕋 → ℂ`, `n : ℤ`, on the
circle `𝕋 = AddCircle 1`. -/

/-- The character `fourier n` is additive in its *argument*: `fourier n (x + y) = fourier n x * fourier n y`. -/
lemma fourier_add_arg {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
  rfl

/-- The sesquilinear form of two characters: `fourier n x * conj (fourier n y) = fourier n (x - y)`. -/
lemma fourier_mul_conj {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n x * star (fourier n y) = fourier n (x - y) := by
  have hnorm : ‖fourier n y‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
  have h2 : fourier n y * star (fourier n y) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have h1 : fourier n x = fourier n y * fourier n (x - y) := by
    rw [← fourier_add_arg n y (x - y), add_sub_cancel]
  rw [h1, mul_assoc, mul_comm (fourier n (x - y)) (star (fourier n y)), ← mul_assoc, h2,
    one_mul]

/-- `fourier (-u) γ = (fourier (-1) γ)^u`. -/
lemma fourier_neg_nat {T : ℝ} (γ : AddCircle T) (u : ℕ) :
    fourier (-(u:ℤ)) γ = (fourier (-1) γ)^u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [show (-((u+1:ℕ):ℤ)) = -(u:ℤ) + (-1) by push_cast; ring, fourier_add, ih, pow_succ]

/-- The truncated geometric series vanishes at a nontrivial `Q`-th root of unity. -/
lemma geom_sum_eq_zero_of_pow_eq_one {z : ℂ} {Q : ℕ} (hz : z^Q = 1) (h : z ≠ 1) :
    ∑ u ∈ range Q, z^u = 0 := by
  rw [geom_sum_eq h Q, hz, sub_self, zero_div]

/-- **Sum of `u ↦ fourier (-u) γ` over a complete residue system.**  For a `Q`-torsion point `γ`
this sum is `Q` if `γ = 0` and `0` otherwise. -/
lemma fourier_range_sum_eq {Q : ℕ} {γ : Work.BourgainPlan.IonescuWainger.Circle}
    (hγ : fourier (Q:ℤ) γ = 1) :
    ∑ u ∈ range Q, fourier (-(u:ℤ)) γ = if γ = 0 then (Q:ℂ) else 0 := by
  by_cases h0 : γ = 0
  · subst h0; simp
  · rw [if_neg h0]
    rw [Finset.sum_congr rfl (fun u _ => fourier_neg_nat γ u)]
    refine geom_sum_eq_zero_of_pow_eq_one ?_ ?_
    · rw [← fourier_neg_nat γ Q, fourier_neg, hγ]; simp
    · intro hz1
      apply h0
      have hcoe : ((-γ : Work.BourgainPlan.IonescuWainger.Circle).toCircle : ℂ) = 1 := by
        have h := hz1; rw [fourier_apply] at h; simpa using h
      have hunit : ((-γ : Work.BourgainPlan.IonescuWainger.Circle).toCircle) = 1 :=
        Subtype.coe_injective hcoe
      have hzero : (-γ : Work.BourgainPlan.IonescuWainger.Circle) = 0 := by
        apply AddCircle.injective_toCircle (T := 1) one_ne_zero
        rw [hunit, AddCircle.toCircle_zero]
      exact neg_eq_zero.mp hzero

/-- `z * conj z = ‖z‖²` for a complex number. -/
lemma mul_star_eq_ofReal (z : ℂ) : z * star z = ↑(Complex.normSq z) := by
  rw [Complex.star_def, Complex.mul_conj]

/-- **Orthogonality of the circle characters `u ↦ e^{2πi u β}`, `β ∈ E`, over a complete residue
system `ℤ/Q`.**  If every `β ∈ E` is a `Q`-torsion point of `𝕋 = ℝ/ℤ` (`fourier Q β = 1`) then for
any weights `G : 𝕋 → ℂ` and any sequence `a : 𝕋 → ℂ`,
`Σ_{u ∈ range Q} ‖Σ_{β ∈ E} G β · e^{2πi(-u)β} · a β‖² = Q · Σ_{β ∈ E} ‖G β‖² · ‖a β‖²`.
Route: expand the square as `(Σ_β c_{uβ}a_β)(conj (Σ_{β'} c_{uβ'}a_{β'})) = Σ_{β,β'} c_{uβ}conj(c_{uβ'})a_β conj(a_{β'})`
with `c_{uβ} = G β e^{2πi(-u)β}`; the inner sums are
`Σ_{u ∈ range Q} c_{uβ} conj(c_{uβ'}) = G β conj(G β') · Σ_{u∈range Q} fourier (-u) (β - β')`,
and `u ↦ fourier (-u) γ` sums to `Q` when `γ = 0` and to `0` otherwise because for a `Q`-torsion
point `γ` with `z = fourier 1 γ` one has `z^Q = 1` and `Σ_{u<Q} z^u = (z^Q - 1)/(z - 1)`. -/
theorem range_fourier_sq_sum {Q : ℕ} {E : Finset Work.BourgainPlan.IonescuWainger.Circle}
    (hE : ∀ β ∈ E, fourier (Q : ℤ) β = 1)
    (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (a : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :
    ∑ u ∈ Finset.range Q,
        ‖∑ β ∈ E, G β * fourier (-(u : ℤ)) β * a β‖ ^ 2
      = (Q : ℝ) * ∑ β ∈ E, ‖G β‖ ^ 2 * ‖a β‖ ^ 2 := by
  let c : ℕ → Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
    fun u β => G β * fourier (-(u:ℤ)) β * a β
  let w : Work.BourgainPlan.IonescuWainger.Circle → Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
    fun β β' => G β * star (G β') * a β * star (a β')
  have hkey : ∀ (u : ℕ) (β β' : Work.BourgainPlan.IonescuWainger.Circle),
      c u β * star (c u β') = w β β' * fourier (-(u:ℤ)) (β - β') := by
    intro u β β'
    have hF : fourier (-(u:ℤ)) β * star (fourier (-(u:ℤ)) β') = fourier (-(u:ℤ)) (β - β') :=
      fourier_mul_conj _ _ _
    show (G β * fourier (-(u:ℤ)) β * a β) * star (G β' * fourier (-(u:ℤ)) β' * a β') = _
    calc (G β * fourier (-(u:ℤ)) β * a β) * star (G β' * fourier (-(u:ℤ)) β' * a β')
        = (G β * a β * star (a β') * star (G β'))
            * (fourier (-(u:ℤ)) β * star (fourier (-(u:ℤ)) β')) := by
          rw [star_mul, star_mul]; ring
      _ = (G β * a β * star (a β') * star (G β')) * fourier (-(u:ℤ)) (β - β') := by rw [hF]
      _ = (G β * star (G β') * a β * star (a β')) * fourier (-(u:ℤ)) (β - β') := by ring
  have hZ : ∀ β ∈ E, ∀ β' ∈ E,
      (∑ u ∈ range Q, fourier (-(u:ℤ)) (β - β')) = if β = β' then (Q:ℂ) else 0 := by
    intro β hβ β' hβ'
    have htors : fourier (Q:ℤ) (β - β') = 1 := by
      rw [← fourier_mul_conj (Q:ℤ) β β', hE β hβ, hE β' hβ']; simp
    rw [fourier_range_sum_eq htors]
    simp only [sub_eq_zero]
  have hdiag : ∀ β : Work.BourgainPlan.IonescuWainger.Circle,
      w β β = ↑(‖G β‖^2 * ‖a β‖^2) := by
    intro β
    show G β * star (G β) * a β * star (a β) = ↑(‖G β‖^2 * ‖a β‖^2)
    rw [show G β * star (G β) * a β * star (a β) = (G β * star (G β)) * (a β * star (a β))
          by ring, mul_star_eq_ofReal, mul_star_eq_ofReal, ← Complex.ofReal_mul,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  calc ∑ u ∈ range Q, ‖∑ β ∈ E, c u β‖^2
      = (∑ u ∈ range Q, (∑ β ∈ E, c u β) * star (∑ β ∈ E, c u β)).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    _ = (∑ u ∈ range Q, ∑ β ∈ E, ∑ β' ∈ E, c u β * star (c u β')).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        rw [star_sum, Finset.sum_mul_sum]
    _ = (∑ β ∈ E, ∑ β' ∈ E, ∑ u ∈ range Q, c u β * star (c u β')).re := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro β _
        rw [Finset.sum_comm]
    _ = (∑ β ∈ E, ∑ β' ∈ E, w β β' * (∑ u ∈ range Q, fourier (-(u:ℤ)) (β - β'))).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro β _
        apply Finset.sum_congr rfl
        intro β' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        exact hkey u β β'
    _ = (∑ β ∈ E, ∑ β' ∈ E, w β β' * (if β = β' then (Q:ℂ) else 0)).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro β hβ
        apply Finset.sum_congr rfl
        intro β' hβ'
        rw [hZ β hβ β' hβ']
    _ = (∑ β ∈ E, w β β * (Q:ℂ)).re := by
        congr 1
        apply Finset.sum_congr rfl
        intro β hβ
        have hstep : ∑ β' ∈ E, w β β' * (if β = β' then (Q:ℂ) else 0)
            = ∑ β' ∈ E, (if β = β' then w β β * (Q:ℂ) else 0) :=
          Finset.sum_congr rfl (fun β' _ => by by_cases h : β = β' <;> simp [h])
        rw [hstep, Finset.sum_ite_eq, if_pos hβ]
    _ = (Q:ℝ) * ∑ β ∈ E, ‖G β‖^2 * ‖a β‖^2 := by
        rw [Complex.re_sum]
        have hterm : ∀ β, (w β β * (Q:ℂ)).re = (Q:ℝ) * (‖G β‖^2 * ‖a β‖^2) := by
          intro β
          have hQ : (Q:ℂ) = ((Q:ℝ):ℂ) := by simp
          rw [hdiag β, hQ, ← Complex.ofReal_mul, Complex.ofReal_re]
          ring
        rw [Finset.sum_congr rfl (fun β _ => hterm β), Finset.mul_sum]

end Work.Maximal.mstOrtho
