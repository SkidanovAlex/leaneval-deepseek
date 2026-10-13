import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.Taylor

/-- Pure real-arithmetic core of the "move `x` to the nearest point `z` of the zero set" step.
Variables are the reals `D = dist x y`, `dxz = dist z x`, `dzy = dist z y`, `T = ⟨g,κ⟩(x)`,
`Tz = ⟨g,κ⟩(z)`, `E = eaEval g z`.  From the Lipschitz estimate `|Tz - T| ≤ Λ · dxz`, the Taylor
remainder estimate `|E - Tz| ≤ Crew · dzy^{κ+1}`, the geometric facts `dxz ≤ C₃ · D^{κ+1}` and
`dzy ≤ 2·D`, the strict inequality `D^κ < T` and the smallness `(Λ C₃ + Crew·2^{κ+1}) · D < 1`, it
concludes `E > 0`:
`E ≥ T - Λ·dxz - Crew·dzy^{κ+1} ≥ T - D^{κ+1}(Λ C₃ + Crew·2^{κ+1})`
`  > D^κ - D^{κ+1}(Λ C₃ + Crew·2^{κ+1}) = D^κ · (1 - D(Λ C₃ + Crew·2^{κ+1})) ≥ 0`. -/
private lemma E3_arith_core (D dxz dzy T Tz E Λ C₃ Crew : ℝ) (κ : ℕ)
    (_hC₃ : 0 ≤ C₃) (hΛ : 0 ≤ Λ) (hCrew : 0 ≤ Crew)
    (hD : 0 ≤ D) (hdz : 0 ≤ dzy)
    (hT : D ^ κ < T)
    (hxz : dxz ≤ C₃ * D ^ (κ + 1))
    (hzy : dzy ≤ 2 * D)
    (hL : |Tz - T| ≤ Λ * dxz)
    (hR : |E - Tz| ≤ Crew * dzy ^ (κ + 1))
    (hd3 : (Λ * C₃ + Crew * 2 ^ (κ + 1)) * D < 1) :
    0 < E := by
  -- `Λ · dxz ≤ Λ C₃ · D^{κ+1}`.
  have h1 : Λ * dxz ≤ Λ * C₃ * D ^ (κ + 1) := by
    calc Λ * dxz ≤ Λ * (C₃ * D ^ (κ + 1)) := mul_le_mul_of_nonneg_left hxz hΛ
      _ = Λ * C₃ * D ^ (κ + 1) := by ring
  -- `Crew · dzy^{κ+1} ≤ Crew · 2^{κ+1} · D^{κ+1}`.
  have h2a : dzy ^ (κ + 1) ≤ (2 * D) ^ (κ + 1) := pow_le_pow_left₀ hdz hzy (κ + 1)
  have h2b : (2 * D) ^ (κ + 1) = 2 ^ (κ + 1) * D ^ (κ + 1) := by rw [mul_pow]
  have h2 : Crew * dzy ^ (κ + 1) ≤ Crew * 2 ^ (κ + 1) * D ^ (κ + 1) := by
    calc Crew * dzy ^ (κ + 1) ≤ Crew * (2 * D) ^ (κ + 1) := mul_le_mul_of_nonneg_left h2a hCrew
      _ = Crew * (2 ^ (κ + 1) * D ^ (κ + 1)) := by rw [h2b]
      _ = Crew * 2 ^ (κ + 1) * D ^ (κ + 1) := by ring
  -- Lower bound on `E`, then the exact factorization of the deficit.
  have hLn : -(Λ * dxz) ≤ Tz - T := neg_le_of_abs_le hL
  have hRn : -(Crew * dzy ^ (κ + 1)) ≤ E - Tz := neg_le_of_abs_le hR
  have hElow : T - (Λ * C₃ + Crew * 2 ^ (κ + 1)) * D ^ (κ + 1) ≤ E := by
    nlinarith [h1, h2, hLn, hRn]
  have hpow : (Λ * C₃ + Crew * 2 ^ (κ + 1)) * D ^ (κ + 1)
      = ((Λ * C₃ + Crew * 2 ^ (κ + 1)) * D) * D ^ κ := by rw [pow_succ]; ring
  have hElow' : T - ((Λ * C₃ + Crew * 2 ^ (κ + 1)) * D) * D ^ κ ≤ E := by
    linarith [hElow, hpow]
  -- The product `D^κ · (1 - D(Λ C₃ + Crew·2^{κ+1}))` is nonnegative and strictly below `E`.
  have hp : 0 ≤ D ^ κ := pow_nonneg hD κ
  have hfac : 0 ≤ D ^ κ * (1 - ((Λ * C₃ + Crew * 2 ^ (κ + 1)) * D)) :=
    mul_nonneg hp (by linarith [hd3])
  nlinarith [hElow', hT, hd3, hp, hfac]

/-- The arithmetic core of the "move `x` to the nearest point `z` of the zero set" step.  All the
estimates about `eaTaylor`/`eaEval` are supplied *pointwise at `(z,x)`* (`hLipx`, `hRemz`) and all
the geometric facts as hypotheses (`hxz`, `hzy`), so what remains is the pure real arithmetic: with
`d = dist x y`,
`eaEval c g z ≥ T (x) - Λ · dist z x - Crew · (dist z y)^{κ+1}`
`             > d^κ - d^{κ+1} (Λ C₃ + Crew · 2^{κ+1}) > 0`
(the last because `d (Λ C₃ + Crew · 2^{κ+1}) < 1` and `d^κ ≥ 0`).  This is used in the `(⇐)`
direction of `E3_taylor_closure` to see that the point `z` still satisfies the strict inequalities
`g > 0`, i.e. that moving `x` by `o (d^κ)` keeps it in `B.holds`. -/
theorem E3_pos_of_perturb_pointwise {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (B : WilkiesDesign.E.Basic k r) (y x z : Fin k → ℝ) (κ : ℕ) (C₃ Λ Crew : ℝ)
    (hC₃ : 0 ≤ C₃) (hΛ : 0 ≤ Λ) (hCrew : 0 ≤ Crew) (hκ : 1 ≤ κ)
    (hT : ∀ g ∈ B.pos, dist x y ^ κ < WilkiesDesign.E.eaTaylor c g κ y x)
    (hxz : dist x z ≤ C₃ * dist x y ^ (κ + 1))
    (hzy : dist z y ≤ 2 * dist x y)
    (hLipx : ∀ g ∈ B.pos,
      |WilkiesDesign.E.eaTaylor c g κ y z - WilkiesDesign.E.eaTaylor c g κ y x|
        ≤ Λ * dist z x)
    (hRemz : ∀ g ∈ B.pos,
      |WilkiesDesign.E.eaEval c g z - WilkiesDesign.E.eaTaylor c g κ y z|
        ≤ Crew * dist z y ^ (κ + 1))
    (hd3 : (Λ * C₃ + Crew * 2 ^ (κ + 1)) * dist x y < 1) :
    ∀ g ∈ B.pos, 0 < WilkiesDesign.E.eaEval c g z := by
  have _hκ : 1 ≤ κ := hκ
  intro g hg
  exact E3_arith_core (dist x y) (dist z x) (dist z y)
    (WilkiesDesign.E.eaTaylor c g κ y x) (WilkiesDesign.E.eaTaylor c g κ y z)
    (WilkiesDesign.E.eaEval c g z) Λ C₃ Crew κ
    hC₃ hΛ hCrew dist_nonneg dist_nonneg (hT g hg)
    (by rw [dist_comm]; exact hxz) hzy (hLipx g hg) (hRemz g hg) hd3

end Work.WilE3.Taylor
