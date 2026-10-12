import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.swhManifestReduced`

The pure-arithmetic reduction of the sliding-box manifest.

`Work.BoseB1Cube.swhManifestInst` produces, at every admissible `μ`, every `u ∈ goodSet` and every
normalised box-supported smooth state, the **fibre estimate**

    fib ≤ (W/V)·S + Cm·a·(√(Q·(W/V)·S) + Q)      (`W = bW`, `V = bV`, `S = bFlat`, `Q = bQ`),

together with the gap gate `4·Kg·μ·a ≤ bG` (`Kg` = the free gap coefficient, chosen large),
`Cm·(εη+1) ≤ Kg`, `Kg ≥ 17π/18` and the a-priori bound `W ≤ 17π·a·V` on the box fibre mass.
This file extracts from those data the two rows of the razor actually consumed downstream:

* the **demand** bound  `T − bG·Q ≤ (19/18 + Cm·a/(4 εη))·μWS/V`, and
* the **count** bound  `Q ≤ (19/18 + Cm·a/(4 εη))·WS/(2 Kg V a)`  whenever the gap pays,
  `bG·Q < T`.

Both are AM–GM: with the free parameter `εη` (`√(xy) ≤ εη x + y/(4εη)`, `sqrt_mul_le_param`), the
`√Q` term is absorbed on the one hand by the slack `Cm·a/(4 εη)` of the flat row and on the other
hand by the quadratic slack `Q·(μW/(18V) + μ Cm a (εη+1) − bG)`, which is negative by the gate
(`gate_arith`).  In the second conjunct the same negativity makes the coefficient of `Q` at least
`2 Kg μ a`, which is what turns the *strict* gap inequality `bG·Q < T` into an upper bound on `Q`;
`Kg ≥ 17π/18` supplies the row `(1/18)μ W Q/V ≤ Kg μ a Q`, i.e. the `1/9`-share of the kinetic
slot, and `Cm(εη+1) ≤ Kg` the fibre row.
-/

namespace Work.BoseB1Cube

/-- AM–GM with a free parameter: for `x, y ≥ 0` and `a > 0`, `√(x y) ≤ a x + y / (4a)`.
The proof is the identity `(a x + y/(4a))² − x y = (a x − y/(4a))²`, together with
`Real.sqrt_le_iff`. -/
lemma sqrt_mul_le_param {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 < a) :
    Real.sqrt (x * y) ≤ a * x + y / (4 * a) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h : (a * x + y / (4 * a)) ^ 2 - x * y = (a * x - y / (4 * a)) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg (a * x - y / (4 * a))]

/-- The gate arithmetic: `4 Kg μ a ≤ bG`, `Cm (εη+1) ≤ Kg`, `17π/18 ≤ Kg` and `W ≤ 17π a V`
give `2 Kg μ a + (μ W/(18V) + μ Cm a (εη+1)) ≤ bG`.

Indeed `W/(18V) ≤ 17π a/18 ≤ Kg a`, `Cm a (εη+1) ≤ Kg a`, so the bracket is at most
`2 Kg μ a` and the left side at most `4 Kg μ a ≤ bG`. -/
lemma gate_arith {μ a V W Cm εη Kg bG : ℝ}
    (hμ : 0 < μ) (_ha : 0 ≤ a) (hV : 0 < V) (_hW : 0 ≤ W) (_hCm : 0 ≤ Cm)
    (_hεη : 0 < εη) (_hKg : 0 < Kg)
    (hgate : 4 * Kg * μ * a ≤ bG)
    (hKg1 : Cm * (εη + 1) ≤ Kg) (hKg2 : 17 * Real.pi / 18 ≤ Kg)
    (hWup : W ≤ 17 * Real.pi * a * V) :
    2 * Kg * μ * a + (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1)) ≤ bG := by
  have hWV : W / V ≤ 17 * Real.pi * a := by
    rw [div_le_iff₀ hV]
    linarith
  have h1a : W / (18 * V) ≤ 17 * Real.pi * a / 18 := by
    rw [show W / (18 * V) = (W / V) / 18 by field_simp]
    exact div_le_div_of_nonneg_right hWV (by norm_num)
  have h1 : μ * (W / (18 * V)) ≤ μ * (17 * Real.pi * a / 18) :=
    mul_le_mul_of_nonneg_left h1a hμ.le
  have h2 : μ * (17 * Real.pi * a / 18) ≤ μ * Kg * a := by
    have h' : (17 * Real.pi / 18) * (μ * a) ≤ Kg * (μ * a) :=
      mul_le_mul_of_nonneg_right hKg2 (by positivity)
    nlinarith [h']
  have h3 : μ * Cm * a * (εη + 1) ≤ μ * Kg * a := by
    have h' : (Cm * (εη + 1)) * (μ * a) ≤ Kg * (μ * a) :=
      mul_le_mul_of_nonneg_right hKg1 (by positivity)
    nlinarith [h']
  have hkey : μ * (W / (18 * V)) + μ * Cm * a * (εη + 1) ≤ 2 * (Kg * μ * a) := by
    linarith
  nlinarith [hgate, hkey]

/-- The demand row, as pure arithmetic: given the AM–GM split of `√(Q(W/V)S)` and the gate
`μ W/(18V) + μ Cm a (εη+1) ≤ bG`, the manifest left side is dominated by
`(19/18 + Cm a/(4εη))·μWS/V`. -/
lemma manifestCore1 {μ a V W S Q Cm εη bG : ℝ}
    (hμ : 0 < μ) (_hV : 0 < V) (_hW : 0 ≤ W) (_hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (_hCm : 0 ≤ Cm) (_hεη : 0 < εη) (_ha : 0 ≤ a)
    (hb : Real.sqrt (Q * ((W / V) * S)) ≤ εη * Q + ((W / V) * S) / (4 * εη))
    (hgate : μ * (W / (18 * V)) + μ * Cm * a * (εη + 1) ≤ bG) :
    (1 / 18) * μ * ((S + Q) / V) * W
        + μ * ((W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q)) - bG * Q
      ≤ (19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V) := by
  have hc : 0 ≤ μ * Cm * a := by positivity
  have hstep : μ * Cm * a * Real.sqrt (Q * ((W / V) * S))
      ≤ μ * Cm * a * (εη * Q + ((W / V) * S) / (4 * εη)) :=
    mul_le_mul_of_nonneg_left hb hc
  have hQb : Q * (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1) - bG) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hQ (by linarith)
  ring_nf at *
  nlinarith [hstep, hQb]

/-- The count row, as pure arithmetic: if the gap pays, `bG·Q < T`, then the same AM–GM split
gives `Q·(bG − μW/(18V) − μ Cm a (εη+1)) < (19/18 + Cm a/(4εη))·μWS/V`, and the gate in the form
`2 Kg μ a ≤ bG − (μW/(18V) + μ Cm a (εη+1))` turns this into
`Q ≤ (19/18 + Cm a/(4εη))·WS/(2 Kg V a)`. -/
lemma manifestCore2 {μ a V W S Q Cm εη Kg bG : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (_hW : 0 ≤ W) (_hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hCm : 0 ≤ Cm) (hεη : 0 < εη) (hKg : 0 < Kg) (ha : 0 < a)
    (hb : Real.sqrt (Q * ((W / V) * S)) ≤ εη * Q + ((W / V) * S) / (4 * εη))
    (hd : 2 * Kg * μ * a ≤ bG - (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1)))
    (h : bG * Q < (1 / 18) * μ * ((S + Q) / V) * W
        + μ * ((W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q))) :
    Q ≤ (19 / 18 + Cm * a / (4 * εη)) * W * S / (2 * Kg * V * a) := by
  have hc : 0 ≤ μ * Cm * a := by positivity
  have hstep : μ * Cm * a * Real.sqrt (Q * ((W / V) * S))
      ≤ μ * Cm * a * (εη * Q + ((W / V) * S) / (4 * εη)) :=
    mul_le_mul_of_nonneg_left hb hc
  have hQD : Q * (bG - (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1))) <
      (19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V) := by
    ring_nf at *
    nlinarith [h, hstep]
  have hQD2 : Q * (2 * Kg * μ * a) < (19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V) := by
    have h2 : Q * (2 * Kg * μ * a)
        ≤ Q * (bG - (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1))) :=
      mul_le_mul_of_nonneg_left hd hQ
    linarith
  have hpos : 0 < 2 * Kg * μ * a := by positivity
  have hlt : Q < ((19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V)) / (2 * Kg * μ * a) :=
    (lt_div_iff₀ hpos).mpr hQD2
  have hid : ((19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V)) / (2 * Kg * μ * a)
      = (19 / 18 + Cm * a / (4 * εη)) * W * S / (2 * Kg * V * a) := by
    field_simp
  rw [hid] at hlt
  exact le_of_lt hlt

theorem swhManifestReduced {μ a V W S Q n Cm εη Kg bG fib T : ℝ}
    (hμ : 0 < μ) (ha : 0 ≤ a) (hV : 0 < V) (hW : 0 ≤ W) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hCm : 0 ≤ Cm) (hεη : 0 < εη) (hKg : 0 < Kg)
    (hgate : 4 * Kg * μ * a ≤ bG)
    (hKg1 : Cm * (εη + 1) ≤ Kg) (hKg2 : 17 * Real.pi / 18 ≤ Kg)
    (hWup : W ≤ 17 * Real.pi * a * V)
    (hSQ : S + Q = n)
    (hfib : fib ≤ (W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q))
    (hT : T = (1 / 18) * μ * (n / V) * W + μ * fib) :
    T - bG * Q ≤ (19 / 18 + Cm * a / (4 * εη)) * (μ * W * S / V) ∧
      (bG * Q < T → Q ≤ (19 / 18 + Cm * a / (4 * εη)) * W * S / (2 * Kg * V * a)) := by
  have hgate' : 2 * Kg * μ * a + (μ * (W / (18 * V)) + μ * Cm * a * (εη + 1)) ≤ bG :=
    gate_arith hμ ha hV hW hCm hεη hKg hgate hKg1 hKg2 hWup
  have hb : Real.sqrt (Q * ((W / V) * S)) ≤ εη * Q + ((W / V) * S) / (4 * εη) :=
    sqrt_mul_le_param hQ (mul_nonneg (div_nonneg hW hV.le) hS) hεη
  have hfibμ : μ * fib ≤ μ * ((W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q)) :=
    mul_le_mul_of_nonneg_left hfib hμ.le
  have hgateA : μ * (W / (18 * V)) + μ * Cm * a * (εη + 1) ≤ bG := by
    have h2 : (0 : ℝ) ≤ 2 * Kg * μ * a := by positivity
    linarith [hgate', h2]
  constructor
  · have hcore := manifestCore1 hμ hV hW hS hQ hCm hεη ha hb hgateA
    rw [hT, ← hSQ]
    linarith
  · intro hlt
    by_cases ha0 : a = 0
    · -- the case `a = 0`: `hWup` forces `W = 0`, hence `fib ≤ 0`, `T ≤ 0 ≤ bG·Q`:
      -- the gap antecedent is impossible.
      exfalso
      have hW0 : W = 0 := by
        have h : W ≤ 0 := by
          have hw := hWup
          rw [ha0] at hw
          simpa using hw
        linarith
      have hbG : 0 ≤ bG := by
        have h := hgate
        rw [ha0] at h
        simpa using h
      have hfib0 : fib ≤ 0 := by
        have h := hfib
        rw [hW0, ha0] at h
        simpa using h
      have hμfib : μ * fib ≤ 0 := by
        have := mul_le_mul_of_nonneg_left hfib0 hμ.le
        simpa using this
      have hT0 : T ≤ 0 := by
        rw [hT, hW0]
        have hzero : (1 / 18) * μ * (n / V) * 0 + μ * fib = μ * fib := by ring
        rw [hzero]
        exact hμfib
      have h1 : bG * Q < 0 := lt_of_lt_of_le hlt hT0
      have h2 : 0 ≤ bG * Q := mul_nonneg hbG hQ
      linarith
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hlt' : bG * Q < (1 / 18) * μ * ((S + Q) / V) * W
          + μ * ((W / V) * S + Cm * a * (Real.sqrt (Q * ((W / V) * S)) + Q)) := by
        rw [hT, ← hSQ] at hlt
        linarith
      exact manifestCore2 hμ hV hW hS hQ hCm hεη hKg hapos hb (by nlinarith [hgate']) hlt'

end Work.BoseB1Cube
