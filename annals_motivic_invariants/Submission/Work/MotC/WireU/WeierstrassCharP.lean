import Mathlib
import Submission.Work.Genus.CharP.Defs
import Submission.Work.Genus.CharP.size_lt_of_pow_eq
import Submission.Work.Genus.CharP.isConst_of_w_eq_zero
import Submission.Work.Genus.CharP.isConst_of_isConst_abscissa
import Submission.Work.Genus.CharP.DescentBasic
import Submission.Work.Genus.CharP.equation_rootTwist
import Submission.Work.Genus.CharP.rootTwist_discriminant
import Submission.Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero
import Submission.Work.Genus.CharP.natDegree_num_pow
import Submission.Work.Genus.CharP.natDegree_denom_pow
import Submission.Work.Genus.Main.deriv_y_eq_zero
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero
import Submission.Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq
import Submission.Work.Genus.Main.w_sq_eq_aeval_curveCubic
import Submission.Work.Genus.Main.curveCubic_natDegree
import Submission.Work.Genus.Main.isCoprime_curveCubic_derivative
import Submission.Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC.WireU

open Work.Genus.CharP

/-- **The Frobenius descent (induction step).**  Strong induction on the size
`Size x = x.num.natDegree + x.denom.natDegree` of the abscissa, generalised over the curve `E` so
that it can be applied to the `p`-th root twist `E^{(1/p)}`. -/
private theorem aux {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [PerfectField F]
    (h2 : (2 : F) ≠ 0) :
    ∀ n : ℕ, ∀ (E : WeierstrassCurve F), E.Δ ≠ 0 → ∀ x y : RatFunc F,
      Size x = n → WEqn E x y → IsConst x ∧ IsConst y := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hΔ x y hsize h
    have hsize' : x.num.natDegree + x.denom.natDegree = n := hsize
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- The size of `x` is zero: then `x` is constant, and so is `y`.
      have hnum : x.num.natDegree = 0 := by omega
      have hden : x.denom.natDegree = 0 := by omega
      obtain ⟨x₀, hx₀⟩ := Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero hnum hden
      exact ⟨⟨x₀, hx₀⟩, isConst_of_isConst_abscissa E h ⟨x₀, hx₀⟩⟩
    · by_cases hw0 : 2 * y + algebraMap F (RatFunc F) E.a₁ * x
          + algebraMap F (RatFunc F) E.a₃ = 0
      · -- The completed ordinate vanishes: `A(x) = 0`, so `x` (and then `y`) is constant.
        exact isConst_of_w_eq_zero h2 E h hw0
      · -- `w ≠ 0`: differentiate and descend along the Frobenius.
        have h4 : (4 : F) ≠ 0 := by
          rw [show (4 : F) = 2 * 2 by norm_num]
          exact mul_ne_zero h2 h2
        have hA : (Work.Genus.curveCubic E).natDegree = 3 :=
          Work.Genus.Main.curveCubic_natDegree E h4
        have hsq : IsCoprime (Work.Genus.curveCubic E)
            (Polynomial.derivative (Work.Genus.curveCubic E)) :=
          Work.Genus.Main.isCoprime_curveCubic_derivative E h2 hΔ
        have hw_sq : (2 * y + algebraMap F (RatFunc F) E.a₁ * x
              + algebraMap F (RatFunc F) E.a₃) ^ 2
            = Polynomial.aeval x (Work.Genus.curveCubic E) :=
          Work.Genus.Main.w_sq_eq_aeval_curveCubic E h
        have hdx : Work.Genus.deriv x = 0 :=
          Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq h2 hA hsq hw0 hw_sq.symm
        have hdy : Work.Genus.deriv y = 0 :=
          Work.Genus.Main.deriv_y_eq_zero E h hw0 hdx
        -- In characteristic `p`, the kernel of `d/dt` consists of `p`-th powers.
        obtain ⟨X, hX⟩ := exists_pow_eq_of_deriv_eq_zero (p := p) hdx
        obtain ⟨Y, hY⟩ := exists_pow_eq_of_deriv_eq_zero (p := p) hdy
        have hlt : Size X < n := by
          have hn' : 0 < Size x := by rw [hsize]; exact hnpos
          have := size_lt_of_pow_eq (p := p) hX hn'
          rwa [hsize] at this
        -- `(X, Y)` is a point of the root twist `E^{(1/p)}`, which is again non-singular.
        have h' : (Y ^ p) ^ 2 + algebraMap F (RatFunc F) E.a₁ * X ^ p * Y ^ p
              + algebraMap F (RatFunc F) E.a₃ * Y ^ p
            = (X ^ p) ^ 3 + algebraMap F (RatFunc F) E.a₂ * (X ^ p) ^ 2
              + algebraMap F (RatFunc F) E.a₄ * X ^ p + algebraMap F (RatFunc F) E.a₆ := by
          rw [← hX, ← hY]
          exact h
        have hΔ' : (Work.Genus.rootTwist (p := p) E).Δ ≠ 0 := by
          intro h0
          have hh := Work.Genus.CharP.rootTwist_discriminant (p := p) E
          rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hh
          exact hΔ hh.symm
        have hrt : WEqn (Work.Genus.rootTwist (p := p) E) X Y :=
          Work.Genus.CharP.equation_rootTwist (p := p) E h'
        -- The induction hypothesis on the strictly smaller point `(X, Y)` of `E^{(1/p)}`.
        obtain ⟨hXc, hYc⟩ :=
          ih (Size X) hlt (Work.Genus.rootTwist (p := p) E) hΔ' X Y rfl hrt
        obtain ⟨X₀, hX₀⟩ := hXc
        obtain ⟨Y₀, hY₀⟩ := hYc
        exact ⟨⟨X₀ ^ p, by rw [hX, hX₀, ← map_pow]⟩,
          ⟨Y₀ ^ p, by rw [hY, hY₀, ← map_pow]⟩⟩

set_option maxHeartbeats 1000000 in
/-- **The genus chapter in characteristic `p`.**  Over a perfect field `F` of characteristic `p ≠ 2`,
every `F(t)`-point of a non-singular Weierstrass curve `E/F` is constant.  (In characteristic `p` the
Riemann–Hurwitz input only gives `deriv x = 0`, i.e. `x` is a `p`-th power; one then descends along
the Frobenius to the root twist `E^{(1/p)}`, which is again non-singular and has a strictly smaller
"size".)

Route: strong induction on `n := x.num.natDegree + x.denom.natDegree`, generalised over the curve `E`
(so that it can be applied to the root twist).  A `p`-th power has `p` times the size
(`Work.Genus.CharP.natDegree_num_pow`, `natDegree_denom_pow`), and size `0` forces `x ∈ F`
(`Work.Genus.Main.exists_algebraMap_eq_of_natDegree_eq_zero`; then
`y = (w - a₁x - a₃)/2 ∈ F` using `(2 : F) ≠ 0`, where `w = 2y + a₁x + a₃` and
`w ^ 2 = A(x)` for `A = Work.Genus.curveCubic E`).  Otherwise, with `A = curveCubic E`:
* `w = 0` gives `A(x) = 0` (`Work.Genus.Main.w_sq_eq_aeval_curveCubic`), so `x` is algebraic over `F`
  and hence constant (`Work.Genus.Main.exists_algebraMap_eq_of_isAlgebraic`; note `A ≠ 0` from
  `A.natDegree = 3`), and `y ∈ F` as above.
* `w ≠ 0`: `A.natDegree = 3` and `IsCoprime A A'` (`Work.Genus.Main.curveCubic_natDegree`,
  `isCoprime_curveCubic_derivative`), so `Work.Genus.Analysis.deriv_eq_zero_of_aeval_eq_sq` gives
  `deriv x = 0`, and `Work.Genus.Main.deriv_y_eq_zero` gives `deriv y = 0`.  Hence `x = X ^ p`,
  `y = Y ^ p` (`Work.Genus.CharP.exists_pow_eq_of_deriv_eq_zero`, using `[PerfectField F]` and
  `haveI : PerfectRing F p := PerfectField.toPerfectRing p`), and `(X, Y)` satisfies the equation of
  `E^{(1/p)}` (`Work.Genus.CharP.equation_rootTwist`) with `(E^{(1/p)}).Δ ≠ 0`
  (`Work.Genus.CharP.rootTwist_discriminant`); apply the induction hypothesis to `(E^{(1/p)}, X, Y)`,
  whose size is `size(x)/p < size(x)` (`natDegree_num_pow`). -/

theorem exists_algebraMap_of_weierstrass_charP {F : Type*} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] [PerfectField F] (h2 : (2 : F) ≠ 0) (E : WeierstrassCurve F) (hΔ : E.Δ ≠ 0)
    {x y : RatFunc F}
    (h : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
      = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
        + algebraMap F (RatFunc F) E.a₆) :
    (∃ x₀ : F, x = algebraMap F (RatFunc F) x₀) ∧ (∃ y₀ : F, y = algebraMap F (RatFunc F) y₀) := by
  exact aux h2 (Size x) E hΔ x y rfl h

end Work.MotC.WireU
