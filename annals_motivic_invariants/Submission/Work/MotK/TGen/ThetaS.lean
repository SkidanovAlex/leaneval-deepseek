import Mathlib
import Submission.Work.MotK.TGen.STRulingTheta
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-!
# `Work.MotK.TGen.ThetaS` — the ruling parameter is the ratio `S₃/S₄`

The ruling presentation `theta a b h : K[x₀,x₁,x₂] →ₐ[K] R[T]` (`R = ZRing a b h`) of the source
ruling divisor substitutes `x_j ↦ T·RVS (j+1) + RWS (j+1)`.  The point
`Sklein a b h i = kleinTwStereo a b h p (chart3) i` (`p = kleinPointT a b h`) lies on the ruling
line of the chart point, and its `3`rd and `4`th coordinates are the numerator and denominator of
the ruling parameter; the statement of this file is that `theta` of the *ratio* is `T`:

  `Polynomial.X * theta a b h (Sklein a b h 4) = theta a b h (Sklein a b h 3)`.

The proof goes through the *unprojected* ruling line.  In `K[x][T] = Polynomial (MvPolynomial
(Fin 3) K)`:

* `ZL a b h = T·rv + rw` — the ruling line of the fibre of `kleinTwP` over the chart point;
* `PL a b h = kleinPointT a b h` — the projection centre, as a constant vector;
* `VL a b h = π_p (ZL) = kleinTwPi PL ZL` — the ruling chart point (the image of `chart3` under the
  substitution of `theta`);
* and `theta a b h ∘ chart3` is `VL`, so `theta (Sklein i) = kleinTwStereo p VL i`.

Since `VL = kleinTwPi PL ZL`, `KleinTwStereo_pi_aux` gives immediately

  `θ(Sklein i) = q(ZL)·PL_i − b(PL,ZL)·ZL_i − q(PL)·(ZL_0)²·PL_i + 2·q(PL)·ZL_0·ZL_i`,

and reading this at `i = 3, 4` (with `ZL_3 = T`, `ZL_4 = 1`, `PL_4 = 0`) reduces the statement to

  `PL_3 · (q(ZL) − (ZL_0)² · q(PL)) = 0`,

which holds because `PL_3 = b/(a h)` vanishes as soon as `b = 0` or `a h = 0`, while otherwise
`q(ZL) = 0` (`b ≠ 0`, the ruling line lies on the quadric `q = 0`) and `q(PL) = 0` (`a h ≠ 0`,
the projection centre lies on the quadric).
-/

/-- The projection centre `p = kleinPointT a b h = (1, 0, 1, b/(a h), 0)` as a constant vector
in `K[x₀,x₁,x₂][T]`. -/
noncomputable def PL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (MvPolynomial.C (Work.MotK.kleinPointT a b h i))

/-- The ruling line `Z(T) = T·rv + rw` of the fibre of the twisted quadro map `kleinTwP` over the
chart point `chart3 a b h = (0, x₀, x₁, x₂, 1)`, as a vector in `K[x₀,x₁,x₂][T]`. -/
noncomputable def ZL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (Work.MotK.TwCensus.rv a b h i) * Polynomial.X
    + Polynomial.C (Work.MotK.TwCensus.rw a b h i)

/-- The ruling chart point `π_p (Z(T)) = T·RVS + RWS`: the image of `chart3` under the substitution
of `theta`. -/
noncomputable def VL (a b h : K) : Fin 5 → Polynomial (MvPolynomial (Fin 3) K) :=
  fun i => Polynomial.C (RVS a b h i) * Polynomial.X + Polynomial.C (RWS a b h i)

/-- **The substitution of `theta` on a single variable.** -/
theorem thPoly_X (a b h : K) (j : Fin 3) :
    thPoly a b h (MvPolynomial.X j)
      = Polynomial.C (RVS a b h (ch3' (K := K) j)) * Polynomial.X
        + Polynomial.C (RWS a b h (ch3' (K := K) j)) := by
  simp [thPoly, MvPolynomial.aeval_X]

/-- `VL` is the projection of the ruling line through the centre `PL`. -/
theorem VL_eq_kleinTwPi (a b h : K) : VL a b h = Work.MotK.kleinTwPi (PL a b h) (ZL a b h) := by
  funext i
  fin_cases i <;>
    simp [VL, PL, ZL, Work.MotK.kleinTwPi, RVS, RWS, Work.MotK.kleinPointT,
      Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw] <;>
    first | refl_ring1 | ring

/-- **The substitution of `theta` on the chart point** is the ruling chart point. -/
theorem thPoly_chart3 (a b h : K) :
    (fun i => thPoly a b h (Work.MotK.chart3 K i)) = VL a b h := by
  funext i
  fin_cases i <;>
    simp [VL, thPoly, Work.MotK.chart3, ch3', RVS, RWS, MvPolynomial.aeval_X,
      Work.MotK.kleinPointT, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw] <;>
    first | refl_ring1 | ring

/-- The substitution of `theta` on the projection centre. -/
theorem thPoly_pRa (a b h : K) :
    (fun i => thPoly a b h (Work.MotK.pRa a b h i)) = PL a b h := by
  funext i
  show thPoly a b h (MvPolynomial.C (Work.MotK.kleinPointT a b h i))
      = Polynomial.C (MvPolynomial.C (Work.MotK.kleinPointT a b h i))
  simp only [thPoly, MvPolynomial.aeval_C]
  rw [MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- **Naturality of the stereographic map under the substitution `theta`.** -/
theorem thPoly_Sklein_apply (a b h : K) (i : Fin 5) :
    thPoly a b h (Sklein a b h i)
      = Work.MotK.kleinTwStereo (Polynomial.C (MvPolynomial.C a))
          (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h))
          (PL a b h) (VL a b h) i := by
  have hnat := congrFun (map_kleinTwStereo' (R := MvPolynomial (Fin 3) K)
      (S := Polynomial (MvPolynomial (Fin 3) K)) (thPoly a b h).toRingHom
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.pRa a b h)
      (Work.MotK.chart3 K)) i
  have h1 : (fun i => (thPoly a b h).toRingHom (Work.MotK.pRa a b h i)) = PL a b h :=
    thPoly_pRa (K := K) a b h
  have h2 : (fun i => (thPoly a b h).toRingHom (Work.MotK.chart3 K i)) = VL a b h :=
    thPoly_chart3 (K := K) a b h
  have h3 : (thPoly a b h).toRingHom (MvPolynomial.C a)
      = Polynomial.C (MvPolynomial.C a) := by
    change thPoly a b h (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a)
    simp only [thPoly, MvPolynomial.aeval_C]
    rw [MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  have h4 : (thPoly a b h).toRingHom (MvPolynomial.C b)
      = Polynomial.C (MvPolynomial.C b) := by
    change thPoly a b h (MvPolynomial.C b) = Polynomial.C (MvPolynomial.C b)
    simp only [thPoly, MvPolynomial.aeval_C]
    rw [MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  have h5 : (thPoly a b h).toRingHom (MvPolynomial.C h)
      = Polynomial.C (MvPolynomial.C h) := by
    change thPoly a b h (MvPolynomial.C h) = Polynomial.C (MvPolynomial.C h)
    simp only [thPoly, MvPolynomial.aeval_C]
    rw [MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  rw [h1, h2, h3, h4, h5] at hnat
  simpa [Sklein] using hnat

/-- The ruling line `ZL` has `3`rd coordinate the ruling parameter `T`. -/
theorem ZL_three (a b h : K) : ZL a b h 3 = Polynomial.X := by
  simp [ZL, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw]

/-- The ruling line `ZL` has `4`th coordinate `1`. -/
theorem ZL_four (a b h : K) : ZL a b h 4 = 1 := by
  simp [ZL, Work.MotK.TwCensus.rv, Work.MotK.TwCensus.rw]

/-- The `3`rd coordinate of the projection centre is `b / (a h)`. -/
theorem PL_three (a b h : K) :
    PL a b h 3 = Polynomial.C (MvPolynomial.C (b / (a * h))) := by
  simp [PL, Work.MotK.kleinPointT]

/-- The `4`th coordinate of the projection centre vanishes. -/
theorem PL_four (a b h : K) : PL a b h 4 = 0 := by
  simp [PL, Work.MotK.kleinPointT]

/-- A non-zero element of `K` stays non-zero in the fraction field of `K[x₀,x₁,x₂][T]`. -/
private theorem algebraMap_frac_ne_zero {K : Type} [Field K] (x : K) (hx : x ≠ 0) :
    algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K))) x ≠ 0 := by
  intro h0
  exact hx ((algebraMap K (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))).injective
    (by rw [h0, map_zero]))

/-- **The ruling line lies on the twisted quadric** (`b ≠ 0` is needed only to clear the
denominators of `rv`, `rw`). -/
theorem kleinTwQ_ZL_aux (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C h)) (ZL a b h) = 0 := by
  have ha' := algebraMap_frac_ne_zero (K := K) a ha
  have hb' := algebraMap_frac_ne_zero (K := K) b hb
  apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
    (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
  simp only [Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, ZL, Work.MotK.TwCensus.rv,
    Work.MotK.TwCensus.rw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_eq, Matrix.of_apply, map_mul, map_add, map_sub, map_pow, map_neg, map_zero,
    map_one, map_div₀, MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]
  field_simp [ha', hb']
  first | refl_ring1 | ring

/-- **The projection centre lies on the twisted quadric** (`a h ≠ 0`). -/
theorem kleinTwQ_PL_aux (a b h : K) (hah : a * h ≠ 0) :
    Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
      (Polynomial.C (MvPolynomial.C h)) (PL a b h) = 0 := by
  have ha : a ≠ 0 := fun h0 => hah (by rw [h0, zero_mul])
  have hh : h ≠ 0 := fun h0 => hah (by rw [h0, mul_zero])
  have ha' := algebraMap_frac_ne_zero (K := K) a ha
  have hh' := algebraMap_frac_ne_zero (K := K) h hh
  apply IsFractionRing.injective (Polynomial (MvPolynomial (Fin 3) K))
    (FractionRing (Polynomial (MvPolynomial (Fin 3) K)))
  simp only [Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, PL, Work.MotK.kleinPointT,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Matrix.of_apply,
    map_mul, map_add, map_sub, map_pow, map_neg, map_zero, map_one, map_div₀,
    MvPolynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply]
  field_simp [ha', hh']
  first | refl_ring1 | ring

/-- **The difference of the two substituted coordinates**, computed via the stereographic
identity. -/
theorem thPoly_Sklein_diff (a b h : K) :
    thPoly a b h (Sklein a b h 3) - Polynomial.X * thPoly a b h (Sklein a b h 4)
      = PL a b h 3 * (Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a))
            (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (ZL a b h)
          - (ZL a b h 0) ^ 2 * Work.MotK.kleinTwQ (Polynomial.C (MvPolynomial.C a))
            (Polynomial.C (MvPolynomial.C b)) (Polynomial.C (MvPolynomial.C h)) (PL a b h)) := by
  have hK := Work.MotK.KleinTwStereo_pi_aux (R := Polynomial (MvPolynomial (Fin 3) K))
    (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C h)) (PL a b h) (ZL a b h)
  rw [thPoly_Sklein_apply, thPoly_Sklein_apply, VL_eq_kleinTwPi,
    congrFun hK 3, congrFun hK 4, ZL_three, ZL_four, PL_four]
  first | refl_ring1 | ring

/-- **The substituted coordinates satisfy `θ(S₃) = T·θ(S₄)`.** -/
theorem thPoly_Sklein (a b h : K) :
    thPoly a b h (Sklein a b h 3) = Polynomial.X * thPoly a b h (Sklein a b h 4) := by
  rw [← sub_eq_zero, thPoly_Sklein_diff]
  by_cases hb : b = 0
  · have h0 : PL a b h 3 = 0 := by rw [PL_three]; simp [hb]
    rw [h0, zero_mul]
  · by_cases hah : a * h = 0
    · have h0 : PL a b h 3 = 0 := by rw [PL_three]; simp [hah]
      rw [h0, zero_mul]
    · have ha : a ≠ 0 := fun h0 => hah (by rw [h0, zero_mul])
      rw [kleinTwQ_ZL_aux a b h ha hb, kleinTwQ_PL_aux a b h hah]
      first | refl_ring1 | ring

theorem ThetaS (K : Type) [Field K] (a b h : K) :
    Polynomial.X * Work.MotK.TGen.theta a b h (Work.MotK.TGen.Sklein a b h 4)
      = Work.MotK.TGen.theta a b h (Work.MotK.TGen.Sklein a b h 3) := by
  have hmain := thPoly_Sklein (K := K) a b h
  simp only [theta, AlgHom.comp_apply]
  rw [hmain, map_mul]
  rw [show Polynomial.mapAlgHom (Ideal.Quotient.mkₐ K
        (Ideal.radical (Work.MotK.TwCensus.ZI a b h))) Polynomial.X = Polynomial.X from by simp]

end Work.MotK.TGen
