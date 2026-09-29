import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.IntervalCases
import Submission.Commons.Data.Nat.Choose.legendreU_recurrence

/-!
This file proves the `logPA_ode` identity: the coefficient sequence
`m ↦ u(a,m)·u(b,m)` (Legendre-type `u(t,m)`, coefficients of
`(1 - 2tX + X^2)^(-1/2)`) satisfies the order-two differential equation of
Calegari-Dimitrov-Tang (arXiv:2408.15403, eq. (ODE)).  Coefficient-wise, for
`n ≥ 7` the `x^n`-coefficient of the differential operator applied to `Y` is
an order-7 linear recurrence for the product sequence, proved from the two
three-term recurrences of `u(a,·)`, `u(b,·)` by the state-space certificate
(`claim7`) below; coefficients `n ≤ 6` are handled separately.

STATUS (development): state certificate + monomial machinery compile; the
final coefficient-identity lemma, the small cases and the theorem statement
are still to be finished.  See the HANDOFF.md in this directory.
-/

open scoped BigOperators
open PowerSeries

namespace Commons.RingTheory.PowerSeries

noncomputable section

def RecProp (t : ℚ) (f : ℕ → ℚ) : Prop :=
  ∀ N j : ℕ,
    f (N + j + 2) =
      (((2 * ((N + j + 1 : ℕ) : ℚ) + 1) * t) * f (N + j + 1) -
        ((N + j + 1 : ℕ) : ℚ) * f (N + j)) / (((N + j + 1 : ℕ) : ℚ) + 1)

def alpha (t : ℚ) (N : ℕ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | j + 2 =>
      let cur := alpha t N (j + 1)
      let prev := alpha t N j
      ( ((2 * ((N + j + 1 : ℕ) : ℚ) + 1) * t * cur.1 - ((N + j + 1 : ℕ) : ℚ) * prev.1) /
            (((N + j + 1 : ℕ) : ℚ) + 1),
        ((2 * ((N + j + 1 : ℕ) : ℚ) + 1) * t * cur.2 - ((N + j + 1 : ℕ) : ℚ) * prev.2) /
            (((N + j + 1 : ℕ) : ℚ) + 1) )

lemma bridge {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) : ∀ j : ℕ,
    f (N + j) = (alpha t N j).1 * f N + (alpha t N j).2 * f (N + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simp [alpha]
      | succ j =>
          cases j with
          | zero => simp [alpha]
          | succ j =>
              -- target: f (N + succ (succ j)) = (alpha t N (succ (succ j))).1 * f N + ...
              -- LHS defeq to f (N + j + 2)? N + succ(succ j) vs (N + j) + 2 : both = succ(succ(N + j))? N + succ(succ j) = succ(N + succ j) = succ (succ (N + j)); (N+j)+2 = succ(succ(N+j)).
              have hstep := hf N j
              -- rewrite LHS with hstep:
              rw [show N + Nat.succ (Nat.succ j) = N + j + 2 by omega] at *
              rw [hstep]
              -- now RHS has f (N + j + 1) and f (N + j); substitute ih (j+1), ih j
              have h1 := ih (j + 1) (by omega)
              have h2 := ih j (by omega)
              rw [show N + j + 1 = N + (j + 1) by omega]
              rw [h1]
              rw [h2]
              -- alpha arg succ(succ j): unfold
              simp [alpha]
              ring_nf
abbrev ac0 (N t : ℚ) : ℚ := N^5 + (20*(N^4)) + (155*(N^3)) + (580*(N^2)) + (1044*(N)) + (720)
abbrev ac1 (N t : ℚ) : ℚ := 0
abbrev ac2 (N t : ℚ) : ℚ := -(N^5) + (-19*(N^4)) + (-137*(N^3)) + (-461*(N^2)) + (-702*(N)) + (-360)
abbrev ac3 (N t : ℚ) : ℚ := (-2*(N^5*t)) + (-37*(N^4*t)) + (-258*(N^3*t)) + (-833*(N^2*t)) + (-1210*(N*t)) + (-600*(t))
abbrev ac4 (N t : ℚ) : ℚ := (-4*(N^5*t^2)) + N^5 + (-72*(N^4*t^2)) + (18*(N^4)) + (-487*(N^3*t^2)) + (122*(N^3)) + (-1524*(N^2*t^2)) + (384*(N^2)) + (-2155*(N*t^2)) + (549*(N)) + (-1050*(t^2)) + (270)
abbrev ac5 (N t : ℚ) : ℚ := (-8*(N^5*t^3)) + (4*(N^5*t)) + (-140*(N^4*t^3)) + (70*(N^4*t)) + (-922*(N^3*t^3)) + (462*(N^3*t)) + (-2821*(N^2*t^3)) + (1421*(N^2*t)) + (-3921*(N*t^3)) + (1991*(N*t)) + (-1890*(t^3)) + (966*(t))
abbrev ac6 (N t : ℚ) : ℚ := (-16*(N^5*t^4)) + (12*(N^5*t^2)) - (N^5) + (-272*(N^4*t^4)) + (204*(N^4*t^2)) + (-17*(N^4)) + (-1752*(N^3*t^4)) + (1317*(N^3*t^2)) + (-110*(N^3)) + (-5272*(N^2*t^4)) + (3981*(N^2*t^2)) + (-334*(N^2)) + (-7241*(N*t^4)) + (5502*(N*t^2)) + (-465*(N)) + (-3465*(t^4)) + (2646*(t^2)) + (-225)
abbrev bc0 (N t : ℚ) : ℚ := 0
abbrev bc1 (N t : ℚ) : ℚ := N^5 + (20*(N^4)) + (155*(N^3)) + (580*(N^2)) + (1044*(N)) + (720)
abbrev bc2 (N t : ℚ) : ℚ := (2*(N^5*t)) + (39*(N^4*t)) + (292*(N^3*t)) + (1041*(N^2*t)) + (1746*(N*t)) + (1080*(t))
abbrev bc3 (N t : ℚ) : ℚ := (4*(N^5*t^2)) - (N^5) + (76*(N^4*t^2)) + (-19*(N^4)) + (551*(N^3*t^2)) + (-138*(N^3)) + (1889*(N^2*t^2)) + (-476*(N^2)) + (3030*(N*t^2)) + (-776*(N)) + (1800*(t^2)) + (-480)
abbrev bc4 (N t : ℚ) : ℚ := (8*(N^5*t^3)) + (-4*(N^5*t)) + (148*(N^4*t^3)) + (-74*(N^4*t)) + (1042*(N^3*t^3)) + (-522*(N^3*t)) + (3467*(N^2*t^3)) + (-1747*(N^2*t)) + (5415*(N*t^3)) + (-2765*(N*t)) + (3150*(t^3)) + (-1650*(t))
abbrev bc5 (N t : ℚ) : ℚ := (16*(N^5*t^4)) + (-12*(N^5*t^2)) + N^5 + (288*(N^4*t^4)) + (-216*(N^4*t^2)) + (18*(N^4)) + (1976*(N^3*t^4)) + (-1485*(N^3*t^2)) + (124*(N^3)) + (6432*(N^2*t^4)) + (-4860*(N^2*t^2)) + (408*(N^2)) + (9873*(N*t^4)) + (-7539*(N*t^2)) + (640*(N)) + (5670*(t^4)) + (-4410*(t^2)) + (384)
abbrev bc6 (N t : ℚ) : ℚ := (32*(N^5*t^5)) + (-32*(N^5*t^3)) + (6*(N^5*t)) + (560*(N^4*t^5)) + (-560*(N^4*t^3)) + (105*(N^4*t)) + (3760*(N^3*t^5)) + (-3768*(N^3*t^3)) + (708*(N^3*t)) + (12040*(N^2*t^5)) + (-12124*(N^2*t^3)) + (2289*(N^2*t)) + (18258*(N*t^5)) + (-18544*(N*t^3)) + (3534*(N*t)) + (10395*(t^5)) + (-10710*(t^3)) + (2079*(t))
abbrev dd0 (N a b : ℚ) : ℚ := N^2 + (2*(N)/1) + 1
abbrev dd1 (N a b : ℚ) : ℚ := (-4*(N^2*a*b)/1) + (-12*(N*a*b)/1) + (-9*(a*b)/1)
abbrev dd2 (N a b : ℚ) : ℚ := (4*(N^2*a^2)/1) + (4*(N^2*b^2)/1) + (-3*(N^2)/1) + (16*(N*a^2)/1) + (16*(N*b^2)/1) + (-16*(N)/1) + (15*(a^2)/1) + (15*(b^2)/1) + (-22*(1)/1)
abbrev dd3 (N a b : ℚ) : ℚ := (16*(N*a*b)/1) + (56*(a*b)/1)
abbrev dd4 (N a b : ℚ) : ℚ := (-4*(N^2*a^2)/1) + (-4*(N^2*b^2)/1) + (3*(N^2)/1) + (-40*(N*a^2)/1) + (-40*(N*b^2)/1) + (26*(N)/1) + (-99*(a^2)/1) + (-99*(b^2)/1) + (57*(1)/1)
abbrev dd5 (N a b : ℚ) : ℚ := (4*(N^2*a*b)/1) + (44*(N*a*b)/1) + (121*(a*b)/1)
abbrev dd6 (N a b : ℚ) : ℚ := -(N^2) + (-12*(N)/1) + (-36*(1)/1)
abbrev Dfac (N : ℚ) : ℚ := (N + 2) * (N + 3) * (N + 4) * (N + 5) * (N + 6)

lemma alphaD (t : ℚ) (N j : ℕ) (hj : j ≤ 6) :
   (alpha t N j).1 * Dfac (N : ℚ) = (match j with | 0 => ac0 (N : ℚ) t | 1 => ac1 (N : ℚ) t | 2 => ac2 (N : ℚ) t | 3 => ac3 (N : ℚ) t | 4 => ac4 (N : ℚ) t | 5 => ac5 (N : ℚ) t | _ => ac6 (N : ℚ) t) /\
   (alpha t N j).2 * Dfac (N : ℚ) = (match j with | 0 => bc0 (N : ℚ) t | 1 => bc1 (N : ℚ) t | 2 => bc2 (N : ℚ) t | 3 => bc3 (N : ℚ) t | 4 => bc4 (N : ℚ) t | 5 => bc5 (N : ℚ) t | _ => bc6 (N : ℚ) t) := by
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  interval_cases j <;> (simp [alpha] <;> field_simp [h2, h3, h4, h5, h6] <;> ring_nf <;> try trivial)
abbrev S0d (N a b : ℚ) : ℚ := dd0 N a b * ac0 N a * ac0 N b + dd1 N a b * ac1 N a * ac1 N b + dd2 N a b * ac2 N a * ac2 N b + dd3 N a b * ac3 N a * ac3 N b + dd4 N a b * ac4 N a * ac4 N b + dd5 N a b * ac5 N a * ac5 N b + dd6 N a b * ac6 N a * ac6 N b
abbrev S1d (N a b : ℚ) : ℚ := dd0 N a b * ac0 N a * bc0 N b + dd1 N a b * ac1 N a * bc1 N b + dd2 N a b * ac2 N a * bc2 N b + dd3 N a b * ac3 N a * bc3 N b + dd4 N a b * ac4 N a * bc4 N b + dd5 N a b * ac5 N a * bc5 N b + dd6 N a b * ac6 N a * bc6 N b
abbrev S2d (N a b : ℚ) : ℚ := dd0 N a b * bc0 N a * ac0 N b + dd1 N a b * bc1 N a * ac1 N b + dd2 N a b * bc2 N a * ac2 N b + dd3 N a b * bc3 N a * ac3 N b + dd4 N a b * bc4 N a * ac4 N b + dd5 N a b * bc5 N a * ac5 N b + dd6 N a b * bc6 N a * ac6 N b
abbrev S3d (N a b : ℚ) : ℚ := dd0 N a b * bc0 N a * bc0 N b + dd1 N a b * bc1 N a * bc1 N b + dd2 N a b * bc2 N a * bc2 N b + dd3 N a b * bc3 N a * bc3 N b + dd4 N a b * bc4 N a * bc4 N b + dd5 N a b * bc5 N a * bc5 N b + dd6 N a b * bc6 N a * bc6 N b
lemma S0d_zero (N a b : ℚ) : S0d N a b = 0 := by ring
lemma S1d_zero (N a b : ℚ) : S1d N a b = 0 := by ring
lemma S2d_zero (N a b : ℚ) : S2d N a b = 0 := by ring
lemma S3d_zero (N a b : ℚ) : S3d N a b = 0 := by ring

lemma bridgeD0 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 0) = ac0 (N : ℚ) t * f N + bc0 (N : ℚ) t * f (N + 1) := by
  ring


lemma bridgeD1 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 1) = ac1 (N : ℚ) t * f N + bc1 (N : ℚ) t * f (N + 1) := by
  ring


lemma bridgeD2 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 2) = ac2 (N : ℚ) t * f N + bc2 (N : ℚ) t * f (N + 1) := by
  have hb : f (N + 2) = (alpha t N 2).1 * f N + (alpha t N 2).2 * f (N + 1) := bridge hf N 2
  rw [hb]
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  simp [alpha]
  field_simp [h2, h3, h4, h5, h6]
  ring_nf


lemma bridgeD3 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 3) = ac3 (N : ℚ) t * f N + bc3 (N : ℚ) t * f (N + 1) := by
  have hb : f (N + 3) = (alpha t N 3).1 * f N + (alpha t N 3).2 * f (N + 1) := bridge hf N 3
  rw [hb]
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  simp [alpha]
  field_simp [h2, h3, h4, h5, h6]
  ring_nf


lemma bridgeD4 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 4) = ac4 (N : ℚ) t * f N + bc4 (N : ℚ) t * f (N + 1) := by
  have hb : f (N + 4) = (alpha t N 4).1 * f N + (alpha t N 4).2 * f (N + 1) := bridge hf N 4
  rw [hb]
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  simp [alpha]
  field_simp [h2, h3, h4, h5, h6]
  ring_nf


lemma bridgeD5 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 5) = ac5 (N : ℚ) t * f N + bc5 (N : ℚ) t * f (N + 1) := by
  have hb : f (N + 5) = (alpha t N 5).1 * f N + (alpha t N 5).2 * f (N + 1) := bridge hf N 5
  rw [hb]
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  simp [alpha]
  field_simp [h2, h3, h4, h5, h6]
  ring_nf


lemma bridgeD6 {t : ℚ} {f : ℕ → ℚ} (hf : RecProp t f) (N : ℕ) :
    Dfac (N : ℚ) * f (N + 6) = ac6 (N : ℚ) t * f N + bc6 (N : ℚ) t * f (N + 1) := by
  have hb : f (N + 6) = (alpha t N 6).1 * f N + (alpha t N 6).2 * f (N + 1) := bridge hf N 6
  rw [hb]
  have h2 : (N : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (N : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (N : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (N : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (N : ℚ) + 6 ≠ 0 := by positivity
  simp [alpha]
  field_simp [h2, h3, h4, h5, h6]
  ring_nf

lemma claim7 (a b : ℚ) {f g : ℕ → ℚ} (hf : RecProp a f) (hg : RecProp b g) (N : ℕ) :
    dd0 (N : ℚ) a b * f (N + 0) * g (N + 0) + dd1 (N : ℚ) a b * f (N + 1) * g (N + 1) + dd2 (N : ℚ) a b * f (N + 2) * g (N + 2) + dd3 (N : ℚ) a b * f (N + 3) * g (N + 3) + dd4 (N : ℚ) a b * f (N + 4) * g (N + 4) + dd5 (N : ℚ) a b * f (N + 5) * g (N + 5) + dd6 (N : ℚ) a b * f (N + 6) * g (N + 6) = 0 := by
  have hD : Dfac (N : ℚ) ≠ 0 := by positivity
  have hD2 : Dfac (N : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hbig :
      Dfac (N : ℚ) ^ 2 * (dd0 (N : ℚ) a b * f (N + 0) * g (N + 0) + dd1 (N : ℚ) a b * f (N + 1) * g (N + 1) + dd2 (N : ℚ) a b * f (N + 2) * g (N + 2) + dd3 (N : ℚ) a b * f (N + 3) * g (N + 3) + dd4 (N : ℚ) a b * f (N + 4) * g (N + 4) + dd5 (N : ℚ) a b * f (N + 5) * g (N + 5) + dd6 (N : ℚ) a b * f (N + 6) * g (N + 6)) = (dd0 (N : ℚ) a b * (ac0 (N : ℚ) a * f N + bc0 (N : ℚ) a * f (N + 1)) * (ac0 (N : ℚ) b * g N + bc0 (N : ℚ) b * g (N + 1))) + (dd1 (N : ℚ) a b * (ac1 (N : ℚ) a * f N + bc1 (N : ℚ) a * f (N + 1)) * (ac1 (N : ℚ) b * g N + bc1 (N : ℚ) b * g (N + 1))) + (dd2 (N : ℚ) a b * (ac2 (N : ℚ) a * f N + bc2 (N : ℚ) a * f (N + 1)) * (ac2 (N : ℚ) b * g N + bc2 (N : ℚ) b * g (N + 1))) + (dd3 (N : ℚ) a b * (ac3 (N : ℚ) a * f N + bc3 (N : ℚ) a * f (N + 1)) * (ac3 (N : ℚ) b * g N + bc3 (N : ℚ) b * g (N + 1))) + (dd4 (N : ℚ) a b * (ac4 (N : ℚ) a * f N + bc4 (N : ℚ) a * f (N + 1)) * (ac4 (N : ℚ) b * g N + bc4 (N : ℚ) b * g (N + 1))) + (dd5 (N : ℚ) a b * (ac5 (N : ℚ) a * f N + bc5 (N : ℚ) a * f (N + 1)) * (ac5 (N : ℚ) b * g N + bc5 (N : ℚ) b * g (N + 1))) + (dd6 (N : ℚ) a b * (ac6 (N : ℚ) a * f N + bc6 (N : ℚ) a * f (N + 1)) * (ac6 (N : ℚ) b * g N + bc6 (N : ℚ) b * g (N + 1))) := by
    calc
      Dfac (N : ℚ) ^ 2 * (dd0 (N : ℚ) a b * f (N + 0) * g (N + 0) + dd1 (N : ℚ) a b * f (N + 1) * g (N + 1) + dd2 (N : ℚ) a b * f (N + 2) * g (N + 2) + dd3 (N : ℚ) a b * f (N + 3) * g (N + 3) + dd4 (N : ℚ) a b * f (N + 4) * g (N + 4) + dd5 (N : ℚ) a b * f (N + 5) * g (N + 5) + dd6 (N : ℚ) a b * f (N + 6) * g (N + 6))
          = (dd0 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 0)) * (Dfac (N : ℚ) * g (N + 0))) + (dd1 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 1)) * (Dfac (N : ℚ) * g (N + 1))) + (dd2 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 2)) * (Dfac (N : ℚ) * g (N + 2))) + (dd3 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 3)) * (Dfac (N : ℚ) * g (N + 3))) + (dd4 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 4)) * (Dfac (N : ℚ) * g (N + 4))) + (dd5 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 5)) * (Dfac (N : ℚ) * g (N + 5))) + (dd6 (N : ℚ) a b * (Dfac (N : ℚ) * f (N + 6)) * (Dfac (N : ℚ) * g (N + 6))) := by ring
      _ = (dd0 (N : ℚ) a b * (ac0 (N : ℚ) a * f N + bc0 (N : ℚ) a * f (N + 1)) * (ac0 (N : ℚ) b * g N + bc0 (N : ℚ) b * g (N + 1))) + (dd1 (N : ℚ) a b * (ac1 (N : ℚ) a * f N + bc1 (N : ℚ) a * f (N + 1)) * (ac1 (N : ℚ) b * g N + bc1 (N : ℚ) b * g (N + 1))) + (dd2 (N : ℚ) a b * (ac2 (N : ℚ) a * f N + bc2 (N : ℚ) a * f (N + 1)) * (ac2 (N : ℚ) b * g N + bc2 (N : ℚ) b * g (N + 1))) + (dd3 (N : ℚ) a b * (ac3 (N : ℚ) a * f N + bc3 (N : ℚ) a * f (N + 1)) * (ac3 (N : ℚ) b * g N + bc3 (N : ℚ) b * g (N + 1))) + (dd4 (N : ℚ) a b * (ac4 (N : ℚ) a * f N + bc4 (N : ℚ) a * f (N + 1)) * (ac4 (N : ℚ) b * g N + bc4 (N : ℚ) b * g (N + 1))) + (dd5 (N : ℚ) a b * (ac5 (N : ℚ) a * f N + bc5 (N : ℚ) a * f (N + 1)) * (ac5 (N : ℚ) b * g N + bc5 (N : ℚ) b * g (N + 1))) + (dd6 (N : ℚ) a b * (ac6 (N : ℚ) a * f N + bc6 (N : ℚ) a * f (N + 1)) * (ac6 (N : ℚ) b * g N + bc6 (N : ℚ) b * g (N + 1))) := by
          rw [bridgeD0 hf N, bridgeD0 hg N, bridgeD1 hf N, bridgeD1 hg N, bridgeD2 hf N, bridgeD2 hg N, bridgeD3 hf N, bridgeD3 hg N, bridgeD4 hf N, bridgeD4 hg N, bridgeD5 hf N, bridgeD5 hg N, bridgeD6 hf N, bridgeD6 hg N]
  have hz : Dfac (N : ℚ) ^ 2 * (dd0 (N : ℚ) a b * f (N + 0) * g (N + 0) + dd1 (N : ℚ) a b * f (N + 1) * g (N + 1) + dd2 (N : ℚ) a b * f (N + 2) * g (N + 2) + dd3 (N : ℚ) a b * f (N + 3) * g (N + 3) + dd4 (N : ℚ) a b * f (N + 4) * g (N + 4) + dd5 (N : ℚ) a b * f (N + 5) * g (N + 5) + dd6 (N : ℚ) a b * f (N + 6) * g (N + 6)) = 0 := by
    rw [hbig]
    rw [show (dd0 (N : ℚ) a b * (ac0 (N : ℚ) a * f N + bc0 (N : ℚ) a * f (N + 1)) * (ac0 (N : ℚ) b * g N + bc0 (N : ℚ) b * g (N + 1))) + (dd1 (N : ℚ) a b * (ac1 (N : ℚ) a * f N + bc1 (N : ℚ) a * f (N + 1)) * (ac1 (N : ℚ) b * g N + bc1 (N : ℚ) b * g (N + 1))) + (dd2 (N : ℚ) a b * (ac2 (N : ℚ) a * f N + bc2 (N : ℚ) a * f (N + 1)) * (ac2 (N : ℚ) b * g N + bc2 (N : ℚ) b * g (N + 1))) + (dd3 (N : ℚ) a b * (ac3 (N : ℚ) a * f N + bc3 (N : ℚ) a * f (N + 1)) * (ac3 (N : ℚ) b * g N + bc3 (N : ℚ) b * g (N + 1))) + (dd4 (N : ℚ) a b * (ac4 (N : ℚ) a * f N + bc4 (N : ℚ) a * f (N + 1)) * (ac4 (N : ℚ) b * g N + bc4 (N : ℚ) b * g (N + 1))) + (dd5 (N : ℚ) a b * (ac5 (N : ℚ) a * f N + bc5 (N : ℚ) a * f (N + 1)) * (ac5 (N : ℚ) b * g N + bc5 (N : ℚ) b * g (N + 1))) + (dd6 (N : ℚ) a b * (ac6 (N : ℚ) a * f N + bc6 (N : ℚ) a * f (N + 1)) * (ac6 (N : ℚ) b * g N + bc6 (N : ℚ) b * g (N + 1))) = (f N) * (g N) * (S0d (N : ℚ) a b) + (f N) * (g (N + 1)) * (S1d (N : ℚ) a b) + (f (N + 1)) * (g N) * (S2d (N : ℚ) a b) + (f (N + 1)) * (g (N + 1)) * (S3d (N : ℚ) a b) by ring]
    rw [S0d_zero (N : ℚ) a b, S1d_zero (N : ℚ) a b, S2d_zero (N : ℚ) a b, S3d_zero (N : ℚ) a b]
    ring
  exact (mul_eq_zero.mp hz).resolve_left hD2



/-! ## The power series, its coefficients, and the coefficient plumbing -/

def usum (t : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    (Nat.choose m (2 * j) : ℚ) * (Nat.choose (2 * j) j : ℚ) * t ^ (m - 2 * j) *
      (((t * t - 1) / 4) ^ j)

def ycoef (a b : ℚ) (m : ℕ) : ℚ := usum a m * usum b m

def Yser (a b : ℚ) : PowerSeries ℚ := PowerSeries.mk (fun m => ycoef a b m)

/-- the binomial-sum sequence satisfies the three-term recurrence -/
lemma RecProp_usum (t : ℚ) : RecProp t (usum t) := by
  intro N j
  have hm : 1 ≤ N + j + 1 := by omega
  have h := Commons.Data.Nat.Choose.legendreU_recurrence t (N + j + 1) hm
  dsimp at h
  change (((N + j + 1 : ℕ) : ℚ) + 1) * usum t (N + j + 2) =
      ((2 * ((N + j + 1 : ℕ) : ℚ) + 1) * t) * usum t (N + j + 1) -
        ((N + j + 1 : ℕ) : ℚ) * usum t (N + j) at h
  rw [eq_div_iff (by positivity : (((N + j + 1 : ℕ) : ℚ) + 1) ≠ 0)]
  simpa [mul_comm] using h

/-- coefficient of `X^k · φ` at `n + k` is the `n`-th coefficient of `φ`. -/
lemma coeff_X_pow_mul_add (φ : PowerSeries ℚ) (n k : ℕ) :
    PowerSeries.coeff (n + k) (X ^ k * φ) = PowerSeries.coeff n φ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc]
      have h1 : PowerSeries.coeff ((n + k) + 1) (X * (X ^ k * φ)) =
          PowerSeries.coeff (n + k) (X ^ k * φ) := by
        simpa [Nat.add_comm] using (PowerSeries.coeff_succ_X_mul (n + k) (X ^ k * φ))
      have hi : n + (k + 1) = (n + k) + 1 := by omega
      rw [hi]
      rw [h1]
      exact ih

lemma coeff_X_pow_mul (φ : PowerSeries ℚ) (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff n (X ^ k * φ) = PowerSeries.coeff (n - k) φ := by
  have hn : n = (n - k) + k := by omega
  have h := coeff_X_pow_mul_add φ (n - k) k
  rwa [← hn] at h

lemma coeff_X_pow_mul_of_lt (φ : PowerSeries ℚ) (n k : ℕ) (hk : n < k) :
    PowerSeries.coeff n (X ^ k * φ) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      cases n with
      | zero =>
          rw [pow_succ']
          simp
      | succ n' =>
          rw [pow_succ', mul_assoc, PowerSeries.coeff_succ_X_mul]
          have hn'k : n' < k := by omega
          exact ih n' hn'k

lemma coeff_der2 (Y : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y)) =
      ((n + 1) * (n + 2) : ℕ) * PowerSeries.coeff (n + 2) Y := by
  rw [PowerSeries.coeff_derivative]
  rw [PowerSeries.coeff_derivative]
  norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring

lemma coeff_C_mul (c : ℚ) (φ : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (C c * φ) = c * PowerSeries.coeff n φ := by
  exact _root_.PowerSeries.coeff_C_mul n φ c

lemma coeff_add_s (A B : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (A + B) = PowerSeries.coeff n A + PowerSeries.coeff n B := by simp

lemma coeff_sub_s (A B : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (A - B) = PowerSeries.coeff n A - PowerSeries.coeff n B := by simp

/-! ## The differential operator of the paper and its monomial form -/

def Q4fac (a b : ℚ) : PowerSeries ℚ :=
  (1 : PowerSeries ℚ) - C (4 * a * b) * X
    + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * X ^ 2
    - C (4 * a * b) * X ^ 3 + X ^ 4

def P2fac (a b : ℚ) : PowerSeries ℚ := (X - 1) * X * (X + 1) * Q4fac a b

def P1fac (a b : ℚ) : PowerSeries ℚ :=
  (-1 : PowerSeries ℚ) + C (8 * a * b) * X
    + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2
    + C (16 * a * b) * X ^ 3
    + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4
    - C (8 * a * b) * X ^ 5 + 3 * X ^ 6

def P0fac (a b : ℚ) : PowerSeries ℚ :=
  C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X
    + C (8 * a * b) * X ^ 2
    - C (a ^ 2 + b ^ 2 + 2) * X ^ 3
    - C (a * b) * X ^ 4 + X ^ 5

def P2sum (a b : ℚ) : PowerSeries ℚ :=
  -X + C (4 * a * b) * X ^ 2 + C (3 - 4 * a ^ 2 - 4 * b ^ 2) * X ^ 3
    + C (4 * a ^ 2 + 4 * b ^ 2 - 3) * X ^ 5 - C (4 * a * b) * X ^ 6 + X ^ 7

lemma P2fac_eq_sum (a b : ℚ) : P2fac a b = P2sum a b := by
  unfold P2fac P2sum Q4fac
  have h1 : (1 : PowerSeries ℚ) - C (4 * a ^ 2 + 4 * b ^ 2 - 2) =
      C (3 - 4 * a ^ 2 - 4 * b ^ 2) := by
    calc
      (1 : PowerSeries ℚ) - C (4 * a ^ 2 + 4 * b ^ 2 - 2)
          = C (1 : ℚ) - C (4 * a ^ 2 + 4 * b ^ 2 - 2) := by simp
      _ = C (1 - (4 * a ^ 2 + 4 * b ^ 2 - 2)) := by rw [← map_sub]
      _ = C (3 - 4 * a ^ 2 - 4 * b ^ 2) := by congr 1; ring
  have h2 : C (4 * a ^ 2 + 4 * b ^ 2 - 2) - 1 =
      C (4 * a ^ 2 + 4 * b ^ 2 - 3) := by
    calc
      C (4 * a ^ 2 + 4 * b ^ 2 - 2) - (1 : PowerSeries ℚ)
          = C (4 * a ^ 2 + 4 * b ^ 2 - 2) - C (1 : ℚ) := by simp
      _ = C ((4 * a ^ 2 + 4 * b ^ 2 - 2) - 1) := by rw [← map_sub]
      _ = C (4 * a ^ 2 + 4 * b ^ 2 - 3) := by congr 1; ring
  rw [← h1, ← h2]
  ring

lemma C_natCast (r : ℕ) : (r : PowerSeries ℚ) = C (r : ℚ) := by
  exact (map_natCast (C : ℚ →+* PowerSeries ℚ) r).symm

def LHS_series (a b : ℚ) : PowerSeries ℚ :=
  P2fac a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))
    + P1fac a b * PowerSeries.derivative (R := ℚ) (Yser a b) + P0fac a b * Yser a b

/-- The seven-term coefficient of `x^n` matching `claim7` at `N = n - 5`. -/
def c7sum (a b : ℚ) (n : ℕ) : ℚ :=
  dd0 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n - 5)
    + dd1 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n - 4)
    + dd2 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n - 3)
    + dd3 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n - 2)
    + dd4 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n - 1)
    + dd5 ((n - 5 : ℕ) : ℚ) a b * ycoef a b n
    + dd6 ((n - 5 : ℕ) : ℚ) a b * ycoef a b (n + 1)

/-! ## monomial coefficient lemmas -/

lemma monDer2 (c : ℚ) (a b : ℚ) (n d : ℕ) (hd : d ≤ n) :
    coeff n (C c * X ^ d * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))) =
      c * (((n - d) + 1) * ((n - d) + 2) : ℕ) * ycoef a b ((n - d) + 2) := by
  rw [mul_assoc, coeff_C_mul]
  rw [coeff_X_pow_mul (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))) n d hd]
  rw [coeff_der2]
  simp [Yser]
  ring

lemma monDer (c : ℚ) (a b : ℚ) (n d : ℕ) (hd : d ≤ n) :
    coeff n (C c * X ^ d * PowerSeries.derivative (R := ℚ) (Yser a b)) =
      c * ((n - d) + 1 : ℕ) * ycoef a b ((n - d) + 1) := by
  rw [mul_assoc, coeff_C_mul]
  rw [coeff_X_pow_mul (PowerSeries.derivative (R := ℚ) (Yser a b)) n d hd]
  rw [PowerSeries.coeff_derivative]
  simp [Yser]
  ring

lemma monY (c : ℚ) (a b : ℚ) (n d : ℕ) (hd : d ≤ n) :
    coeff n (C c * X ^ d * Yser a b) = c * ycoef a b (n - d) := by
  rw [mul_assoc, coeff_C_mul]
  rw [coeff_X_pow_mul (Yser a b) n d hd]
  simp [Yser]



/-! ## The coefficient identity for large `n` -/

/-- coefficient of `P2·Y''` at `x^n`, `n ≥ 7`; six monomials. -/
lemma coeff_P2_der2_full (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P2sum a b * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))) =
      (-1 : ℚ) * ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 1) + 2)
      + (4 * a * b) * ((((n - 2 + 1) * (n - 2 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 2) + 2)
      + (3 - 4 * a ^ 2 - 4 * b ^ 2) * ((((n - 3 + 1) * (n - 3 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 3) + 2)
      + (4 * a ^ 2 + 4 * b ^ 2 - 3) * ((((n - 5 + 1) * (n - 5 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 5) + 2)
      - (4 * a * b) * ((((n - 6 + 1) * (n - 6 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 6) + 2)
      + (1 : ℚ) * ((((n - 7 + 1) * (n - 7 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 7) + 2) := by
  let D2 : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))
  have mX1 : coeff n ((-X) * D2) = - ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ) * ycoef a b ((n - 1) + 2)) := by
    have hX0 : coeff n (X * D2) = coeff (n - 1) D2 := by
      simpa using (coeff_X_pow_mul D2 n 1 (by omega))
    have hX : coeff n (X * D2) = ((((n - 1 + 1) * (n - 1 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 1) + 2) := by
      rw [hX0, coeff_der2]
      simp [Yser] <;> ring
    have hneg : coeff n ((-X) * D2) = - coeff n (X * D2) := by simp
    rw [hneg, hX]
  have mC2 : coeff n (C (4 * a * b) * X ^ 2 * D2) = (4 * a * b) * ((((n - 2 + 1) * (n - 2 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 2) + 2) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 2 (by omega)]
    rw [coeff_der2]
    simp [Yser] <;> ring
  have mC3 : coeff n (C (3 - 4 * a ^ 2 - 4 * b ^ 2) * X ^ 3 * D2) = (3 - 4 * a ^ 2 - 4 * b ^ 2) * ((((n - 3 + 1) * (n - 3 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 3) + 2) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 3 (by omega)]
    rw [coeff_der2]
    simp [Yser] <;> ring
  have mC5 : coeff n (C (4 * a ^ 2 + 4 * b ^ 2 - 3) * X ^ 5 * D2) = (4 * a ^ 2 + 4 * b ^ 2 - 3) * ((((n - 5 + 1) * (n - 5 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 5) + 2) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 5 (by omega)]
    rw [coeff_der2]
    simp [Yser] <;> ring
  have mC6 : coeff n (C (4 * a * b) * X ^ 6 * D2) = (4 * a * b) * ((((n - 6 + 1) * (n - 6 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 6) + 2) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul D2 n 6 (by omega)]
    rw [coeff_der2]
    simp [Yser] <;> ring
  have mO7 : coeff n (X ^ 7 * D2) = ((((n - 7 + 1) * (n - 7 + 2) : ℕ) : ℚ)) * ycoef a b ((n - 7) + 2) := by
    rw [coeff_X_pow_mul D2 n 7 (by omega)]
    rw [coeff_der2]
    simp [Yser] <;> ring
  unfold P2sum
  change coeff n ((-X + C (4 * a * b) * X ^ 2 + C (3 - 4 * a ^ 2 - 4 * b ^ 2) * X ^ 3
      + C (4 * a ^ 2 + 4 * b ^ 2 - 3) * X ^ 5 - C (4 * a * b) * X ^ 6 + X ^ 7) * D2) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [mX1, mC2, mC3, mC5, mC6, mO7]
  ring_nf <;> norm_num


/-- coefficient of `P1·Y'` at `x^n`, `n ≥ 7`; seven monomials. -/
lemma coeff_P1_der_full (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P1fac a b * PowerSeries.derivative (R := ℚ) (Yser a b)) =
      - (((n + 1 : ℕ) : ℚ)) * ycoef a b (n + 1)
      + (8 * a * b) * ((((n - 1 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 1) + 1)
      + (5 - 12 * a ^ 2 - 12 * b ^ 2) * ((((n - 2 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 2) + 1)
      + (16 * a * b) * ((((n - 3 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 3) + 1)
      + (4 * a ^ 2 + 4 * b ^ 2 - 7) * ((((n - 4 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 4) + 1)
      - (8 * a * b) * ((((n - 5 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 5) + 1)
      + 3 * ((((n - 6 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 6) + 1) := by
  let E1 : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (Yser a b)
  have hm0 : coeff n (((-1 : PowerSeries ℚ)) * E1) = - (((n + 1 : ℕ) : ℚ)) * ycoef a b (n + 1) := by
    have hE : coeff n E1 = ((n + 1 : ℕ)) * ycoef a b (n + 1) := by
      rw [PowerSeries.coeff_derivative]
      simp [Yser] <;> ring
    have hneg : coeff n (((-1 : PowerSeries ℚ)) * E1) = - coeff n E1 := by
      rw [show ((-1 : PowerSeries ℚ)) * E1 = - E1 by simp]
      simp
    rw [hneg, hE] <;> ring
  have hm1 : coeff n (C (8 * a * b) * X * E1) = (8 * a * b) * ((((n - 1 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 1) + 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    have hX : coeff n (X * E1) = coeff (n - 1) E1 := by
      simpa using (coeff_X_pow_mul E1 n 1 (by omega))
    rw [hX]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  have hm2 : coeff n (C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2 * E1) = (5 - 12 * a ^ 2 - 12 * b ^ 2) * ((((n - 2 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 2) + 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 2 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  have hm3 : coeff n (C (16 * a * b) * X ^ 3 * E1) = (16 * a * b) * ((((n - 3 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 3) + 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 3 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  have hm4 : coeff n (C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4 * E1) = (4 * a ^ 2 + 4 * b ^ 2 - 7) * ((((n - 4 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 4) + 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 4 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  have hm5 : coeff n (C (8 * a * b) * X ^ 5 * E1) = (8 * a * b) * ((((n - 5 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 5) + 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 5 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  have hm6 : coeff n (3 * X ^ 6 * E1) = 3 * ((((n - 6 + 1) : ℕ) : ℚ)) * ycoef a b ((n - 6) + 1) := by
    have hc : (3 : PowerSeries ℚ) = C (3 : ℚ) := C_natCast 3
    rw [hc, mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul E1 n 6 (by omega)]
    rw [PowerSeries.coeff_derivative]
    simp [Yser] <;> ring
  unfold P1fac
  change coeff n (((-1 : PowerSeries ℚ) + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2 + C (16 * a * b) * X ^ 3 + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4 - C (8 * a * b) * X ^ 5 + 3 * X ^ 6) * E1) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  ring_nf <;> exact C_natCast 3
lemma coeff_P0_full (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (P0fac a b * Yser a b) =
      (a * b) * ycoef a b n
      + (1 - 3 * a ^ 2 - 3 * b ^ 2) * ycoef a b (n - 1)
      + (8 * a * b) * ycoef a b (n - 2)
      - (a ^ 2 + b ^ 2 + 2) * ycoef a b (n - 3)
      - (a * b) * ycoef a b (n - 4)
      + ycoef a b (n - 5) := by
  have h0 : coeff n (C ((a * b)) * Yser a b) = (a * b) * ycoef a b n := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    simp [Yser] <;> ring
  have h1 : coeff n (C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X * Yser a b) = (1 - 3 * a ^ 2 - 3 * b ^ 2) * ycoef a b (n - 1) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    have hX : coeff n (X * Yser a b) = coeff (n - 1) (Yser a b) := by
      simpa using (coeff_X_pow_mul (Yser a b) n 1 (by omega))
    rw [hX]
    simp [Yser] <;> ring
  have h2 : coeff n (C ((8 * a * b)) * X ^ 2 * Yser a b) = (8 * a * b) * ycoef a b (n - 2) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul (Yser a b) n 2 (by omega)]
    simp [Yser] <;> ring
  have h3 : coeff n (C ((a ^ 2 + b ^ 2 + 2)) * X ^ 3 * Yser a b) = (a ^ 2 + b ^ 2 + 2) * ycoef a b (n - 3) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul (Yser a b) n 3 (by omega)]
    simp [Yser] <;> ring
  have h4 : coeff n (C ((a * b)) * X ^ 4 * Yser a b) = (a * b) * ycoef a b (n - 4) := by
    rw [mul_assoc, _root_.PowerSeries.coeff_C_mul]
    rw [coeff_X_pow_mul (Yser a b) n 4 (by omega)]
    simp [Yser] <;> ring
  have h5 : coeff n (X ^ 5 * Yser a b) = ycoef a b (n - 5) := by
    rw [coeff_X_pow_mul (Yser a b) n 5 (by omega)]
    simp [Yser]
  unfold P0fac
  change coeff n ((C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2 - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5) * Yser a b) = _
  simp only [add_mul, sub_mul]
  simp only [coeff_add_s, coeff_sub_s]
  rw [h0, h1, h2, h3, h4, h5] <;> ring


/-! ## Coefficient identity (large n) -/

lemma coeff_LHS_eq_c7sum (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) :
    coeff n (LHS_series a b) = c7sum a b n := by
  rw [LHS_series]
  rw [P2fac_eq_sum]
  simp only [coeff_add_s]
  rw [coeff_P2_der2_full a b n hn, coeff_P1_der_full a b n hn, coeff_P0_full a b n hn]
  rw [show (n - 7) + 1 = n - 6 by omega]
  rw [show (n - 1) + 1 = n by omega]
  rw [show (n - 1) + 2 = n + 1 by omega]
  rw [show (n - 2) + 1 = n - 1 by omega]
  rw [show (n - 2) + 2 = n by omega]
  rw [show (n - 3) + 1 = n - 2 by omega]
  rw [show (n - 3) + 2 = n - 1 by omega]
  rw [show (n - 4) + 1 = n - 3 by omega]
  rw [show (n - 5) + 1 = n - 4 by omega]
  rw [show (n - 5) + 2 = n - 3 by omega]
  rw [show (n - 6) + 1 = n - 5 by omega]
  rw [show (n - 6) + 2 = n - 4 by omega]
  rw [show (n - 7) + 2 = n - 5 by omega]
  push_cast
  unfold c7sum
  rw [show ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
  rw [show ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 by rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num]
  rw [show ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 by rw [Nat.cast_sub (by omega : 3 ≤ n)]; norm_num]
  rw [show ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 by rw [Nat.cast_sub (by omega : 4 ≤ n)]; norm_num]
  rw [show ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 by rw [Nat.cast_sub (by omega : 5 ≤ n)]; norm_num]
  rw [show ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 by rw [Nat.cast_sub (by omega : 6 ≤ n)]; norm_num]
  ring

/-- the seven-term combination is zero for `n ≥ 7` (recurrence at `N = n - 5`). -/
lemma c7sum_zero (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) : c7sum a b n = 0 := by
  have hc := claim7 a b (RecProp_usum a) (RecProp_usum b) (n - 5)
  rw [show (n - 5) + 0 = n - 5 by omega,
      show (n - 5) + 1 = n - 4 by omega,
      show (n - 5) + 2 = n - 3 by omega,
      show (n - 5) + 3 = n - 2 by omega,
      show (n - 5) + 4 = n - 1 by omega,
      show (n - 5) + 5 = n by omega,
      show (n - 5) + 6 = n + 1 by omega] at hc
  have hc' : c7sum a b n =
      dd0 (((n - 5 : ℕ) : ℚ)) a b * usum a (n - 5) * usum b (n - 5)
      + dd1 (((n - 5 : ℕ) : ℚ)) a b * usum a (n - 4) * usum b (n - 4)
      + dd2 (((n - 5 : ℕ) : ℚ)) a b * usum a (n - 3) * usum b (n - 3)
      + dd3 (((n - 5 : ℕ) : ℚ)) a b * usum a (n - 2) * usum b (n - 2)
      + dd4 (((n - 5 : ℕ) : ℚ)) a b * usum a (n - 1) * usum b (n - 1)
      + dd5 (((n - 5 : ℕ) : ℚ)) a b * usum a n * usum b n
      + dd6 (((n - 5 : ℕ) : ℚ)) a b * usum a (n + 1) * usum b (n + 1) := by
    unfold c7sum ycoef
    ring
  rw [hc']
  exact hc

/-- coefficient of `x^n` of the ODE expression vanishes for `n ≥ 7`. -/
lemma coeff_LHS_zero (a b : ℚ) (n : ℕ) (hn : 7 ≤ n) : coeff n (LHS_series a b) = 0 := by
  rw [coeff_LHS_eq_c7sum a b n hn, c7sum_zero a b n hn]


/-! ## Small coefficients `n ≤ 6` -/

lemma usum_eval0 (t : ℚ) : usum t 0 = 1 := by unfold usum; norm_num [Nat.choose, Finset.sum_range_succ]
lemma usum_eval1 (t : ℚ) : usum t 1 = t := by unfold usum; norm_num [Nat.choose, Finset.sum_range_succ]
lemma usum_eval2 (t : ℚ) : usum t 2 = (3 * t^2 - 1) / 2 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf
lemma usum_eval3 (t : ℚ) : usum t 3 = (5 * t^3 - 3 * t) / 2 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf
lemma usum_eval4 (t : ℚ) : usum t 4 = (35 * t^4 - 30 * t^2 + 3) / 8 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf
lemma usum_eval5 (t : ℚ) : usum t 5 = (63 * t^5 - 70 * t^3 + 15 * t) / 8 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf
lemma usum_eval6 (t : ℚ) : usum t 6 = (231 * t^6 - 315 * t^4 + 105 * t^2 - 5) / 16 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf
lemma usum_eval7 (t : ℚ) : usum t 7 = (429 * t^7 - 693 * t^5 + 315 * t^3 - 35 * t) / 16 := by
  unfold usum
  norm_num [Nat.choose, Finset.sum_range_succ]
  ring_nf

lemma coeff_C_pow_D2 (c : ℚ) (a b : ℚ) (n d : ℕ) :
    coeff n (C c * X ^ d * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))) =
      if h : d ≤ n then c * (((n - d) + 1) * ((n - d) + 2) : ℕ) * ycoef a b ((n - d) + 2) else 0 := by
  by_cases h : d ≤ n
  · rw [monDer2 c a b n d h]
    simp [h]
  · have hz : coeff n (C c * X ^ d * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))) = 0 := by
      rw [mul_assoc, coeff_C_mul]
      rw [coeff_X_pow_mul_of_lt (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))) n d (by omega)]
      simp
    rw [hz]
    simp [h]

lemma coeff_C_pow_E1 (c : ℚ) (a b : ℚ) (n d : ℕ) :
    coeff n (C c * X ^ d * PowerSeries.derivative (R := ℚ) (Yser a b)) =
      if h : d ≤ n then c * ((n - d) + 1 : ℕ) * ycoef a b ((n - d) + 1) else 0 := by
  by_cases h : d ≤ n
  · rw [monDer c a b n d h]
    simp [h]
  · have hz : coeff n (C c * X ^ d * PowerSeries.derivative (R := ℚ) (Yser a b)) = 0 := by
      rw [mul_assoc, coeff_C_mul]
      rw [coeff_X_pow_mul_of_lt (PowerSeries.derivative (R := ℚ) (Yser a b)) n d (by omega)]
      simp
    rw [hz]
    simp [h]

lemma coeff_C_pow_Y (c : ℚ) (a b : ℚ) (n d : ℕ) :
    coeff n (C c * X ^ d * Yser a b) = if h : d ≤ n then c * ycoef a b (n - d) else 0 := by
  by_cases h : d ≤ n
  · rw [monY c a b n d h]
    simp [h]
  · have hz : coeff n (C c * X ^ d * Yser a b) = 0 := by
      rw [mul_assoc, coeff_C_mul]
      rw [coeff_X_pow_mul_of_lt (Yser a b) n d (by omega)]
      simp
    rw [hz]
    simp [h]

lemma coeff_C_F (c : ℚ) (a b : ℚ) (n : ℕ) :
    coeff n (C c * Yser a b) = c * ycoef a b n := by
  rw [coeff_C_mul]
  simp [Yser]

lemma coeff_C_E1 (c : ℚ) (a b : ℚ) (n : ℕ) :
    coeff n (C c * PowerSeries.derivative (R := ℚ) (Yser a b)) = c * ((n + 1 : ℕ)) * ycoef a b (n + 1) := by
  rw [coeff_C_mul]
  rw [PowerSeries.coeff_derivative]
  simp [Yser]
  ring

lemma coeff_LHS_small (a b : ℚ) (n : ℕ) (hn : n ≤ 6) : coeff n (LHS_series a b) = 0 := by
  interval_cases n
  all_goals
    rw [LHS_series, P2fac_eq_sum]
    unfold P2sum P1fac P0fac
    simp only [add_mul, sub_mul, coeff_add_s, coeff_sub_s]
    rw [show (-X : PowerSeries ℚ) = C (-1 : ℚ) * X by simp]
    rw [show ((-1 : PowerSeries ℚ)) = C (-1 : ℚ) by simp]
    rw [show (3 : PowerSeries ℚ) = C (3 : ℚ) by exact C_natCast 3]
    rw [show (X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b)))) = C (1 : ℚ) * X ^ 7 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))) by simp]
    rw [show (X ^ 5 * Yser a b) = C (1 : ℚ) * X ^ 5 * Yser a b by simp]
    rw [show (C (-1 : ℚ)) * X * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))) = C (-1 : ℚ) * X ^ 1 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Yser a b))) by rw [pow_one]]
    rw [show (C (8 * a * b)) * X * PowerSeries.derivative (R := ℚ) (Yser a b) = C (8 * a * b) * X ^ 1 * PowerSeries.derivative (R := ℚ) (Yser a b) by rw [pow_one]]
    rw [show (C (1 - 3 * a ^ 2 - 3 * b ^ 2)) * X * Yser a b = C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X ^ 1 * Yser a b by rw [pow_one]]
    repeat' rw [coeff_C_pow_D2]
    repeat' rw [coeff_C_pow_E1]
    repeat' rw [coeff_C_pow_Y]
    repeat' rw [coeff_C_E1]
    repeat' rw [coeff_C_F]
    norm_num
    repeat' rw [ycoef]
    repeat' rw [usum_eval0]
    repeat' rw [usum_eval1]
    repeat' rw [usum_eval2]
    repeat' rw [usum_eval3]
    repeat' rw [usum_eval4]
    repeat' rw [usum_eval5]
    repeat' rw [usum_eval6]
    repeat' rw [usum_eval7]
    ring

/-- the ODE holds as an identity of power series: every coefficient vanishes. -/
lemma ode_main (a b : ℚ) : LHS_series a b = 0 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n ≤ 6
  · simpa using coeff_LHS_small a b n hn
  · have hn7 : 7 ≤ n := by omega
    simpa using coeff_LHS_zero a b n hn7


/-- the ODE of Calegari–Dimitrov–Tang (arXiv:2408.15403, eq. (ODE)): the
coefficient sequence `m ↦ u(a,m)·u(b,m)` of the product of two
Legendre-type generating functions satisfies `P2·Y''+P1·Y'+P0·Y = 0`. -/
theorem logPA_ode (a b : ℚ) :
    let U : ℚ → ℕ → ℚ := fun t m =>
        Finset.sum (Finset.range (m / 2 + 1)) (fun j =>
          (Nat.choose m (2 * j) : ℚ) * (Nat.choose (2 * j) j : ℚ) * t ^ (m - 2 * j) *
            (((t * t - 1) / 4) ^ j))
    let Y : PowerSeries ℚ := PowerSeries.mk (fun m => U a m * U b m)
    let Q4 : PowerSeries ℚ :=
        (1 : PowerSeries ℚ) - PowerSeries.C (4 * a * b) * PowerSeries.X
          + PowerSeries.C (4 * a ^ 2 + 4 * b ^ 2 - 2) * PowerSeries.X ^ 2
          - PowerSeries.C (4 * a * b) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4
    let P2 : PowerSeries ℚ := (PowerSeries.X - 1) * PowerSeries.X * (PowerSeries.X + 1) * Q4
    let P1 : PowerSeries ℚ :=
        (-1 : PowerSeries ℚ) + PowerSeries.C (8 * a * b) * PowerSeries.X
          + PowerSeries.C (5 - 12 * a ^ 2 - 12 * b ^ 2) * PowerSeries.X ^ 2
          + PowerSeries.C (16 * a * b) * PowerSeries.X ^ 3
          + PowerSeries.C (4 * a ^ 2 + 4 * b ^ 2 - 7) * PowerSeries.X ^ 4
          - PowerSeries.C (8 * a * b) * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6
    let P0 : PowerSeries ℚ :=
        PowerSeries.C (a * b) + PowerSeries.C (1 - 3 * a ^ 2 - 3 * b ^ 2) * PowerSeries.X
          + PowerSeries.C (8 * a * b) * PowerSeries.X ^ 2
          - PowerSeries.C (a ^ 2 + b ^ 2 + 2) * PowerSeries.X ^ 3
          - PowerSeries.C (a * b) * PowerSeries.X ^ 4 + PowerSeries.X ^ 5
    P2 * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) Y))
      + P1 * PowerSeries.derivative (R := ℚ) Y + P0 * Y = 0 := by
  dsimp
  change LHS_series a b = 0
  exact ode_main a b

end
end Commons.RingTheory.PowerSeries