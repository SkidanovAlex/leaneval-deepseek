import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_l2
import Submission.Work.LT.l2norm_triangle
import Submission.Work.LT.relT_fhat_add
import Submission.Work.LT.relT_l2sq_mulLeft
import Submission.Work.LT.relT_smooth_contract
import Submission.Work.LT.relT_smooth_arith
import Submission.Work.LT.relT_smooth_mass

namespace Work.LT

/-! **Lipschitz ("smoothness") estimate for the Fourier mass under the dual transvections.**

With `m z := l2sq (fhat p a b c z f)`, the dual action of the four transvections changes the mass
of a finite set `B` of character indices by at most `2 ε_y √(m B) + ε_y²`, where
`ε_y = ‖L_y f − f‖` for the corresponding `y` (left translation `(L_y f) g = f (y * g)`).

ROUTE (given the four Fourier hypotheses as assumptions).
* `fhat` is additive in its function argument (direct from the definition), and so is the map
  `h ↦ fun g => ∑ z ∈ B, fhat p a b c z h g`; hence
  `∑_{z∈B} fhat p a b c z (L_y f) = (∑_{z∈B} fhat p a b c z f) ∘ (· * y)`-style identities reduce to
  the conjugation hypothesis with `k = ±1`:
  `fhat p a b c z (L_y f) = L_y (fhat p a b c (M z) f)` where `M = Mab p (-k)` (resp. `Mba p (-k)`).
* `l2sq` is invariant under `g ↦ y*g` (`Equiv.sum_comp` with `Equiv.mulLeft y`).
* By the sub-sum Plancherel hypothesis, `l2sq (∑_{z∈B} fhat p a b c z (L_y f)) = ∑_{w ∈ B.image M} m w`
  (`Finset.sum_image` needs `M` injective on `B`: `Mab p k` and `Mba p k` are bijections of
  `(Z/p)²`, e.g. `Mab p k = (u,v) ↦ (u, uk+v)`).
* So `√(m (B.image M)) = l2norm (∑_{z∈B} (L_y f)_z)`, and the reverse triangle inequality
  (`l2norm_sub_rev` in `relT_l2`) together with the contraction `l2norm (P_B h) ≤ l2norm h` gives
  `|√(m (B.image M)) − √(m B)| ≤ ε_y`. (The contraction uses the sub-sum Plancherel hypothesis at
  `B = univ` together with the **inversion hypothesis** `∑_z fhat p a b c z h = h`, which is why it
  is supplied below.)
* Finally `|a² − b²| = |a − b|(a + b)` with `a = √(m (B.image M))`, `b = √(m B)`, `a ≤ b + ε_y`,
  `b² = m B`, `√(m B) ≥ 0` and `ε_y² = l2sq (L_y f − f)` (`l2norm h ^ 2 = l2sq h`).
The four conjuncts correspond to `M = T₁⁺ = (z₁+z₂,z₂)` from `y = E_ba(-1)`,
`M = T₁⁻ = (z₁-z₂,z₂)` from `y = E_ba(1)`, `M = T₂⁺ = (z₁,z₂+z₁)` from `y = E_ab(-1)`,
`M = T₂⁻ = (z₁,z₂-z₁)` from `y = E_ab(1)`. -/
private theorem smooth_step
    (p : ℕ) [Fact p.Prime] {a b c : Fin 3}
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (hinv : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
         (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g)
    (hplan : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
         (B : Finset (ZMod p × ZMod p)),
        l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h))
    (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (M : ZMod p × ZMod p → ZMod p × ZMod p) (hMinj : Function.Injective M)
    (hconj : ∀ (z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        fhat p a b c z (fun x => f (y * x)) g = fhat p a b c (M z) f (y * g))
    (B : Finset (ZMod p × ZMod p)) :
    |(∑ w ∈ B.image M, l2sq (fhat p a b c w f)) - ∑ z ∈ B, l2sq (fhat p a b c z f)|
      ≤ 2 * l2norm (fun g => f (y * g) - f g)
          * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
        + l2sq (fun g => f (y * g) - f g) := by
  have hsqrt : |Real.sqrt (∑ w ∈ B.image M, l2sq (fhat p a b c w f))
      - Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))|
        ≤ l2norm (fun g => f (y * g) - f g) := by
    have hA : l2norm (fun g => ∑ z ∈ B, fhat p a b c z (fun x => f (y * x)) g)
        = Real.sqrt (∑ w ∈ B.image M, l2sq (fhat p a b c w f)) := by
      rw [l2norm]
      exact congrArg Real.sqrt (relT_smooth_mass p hplan f y M hMinj hconj B)
    have hB : l2norm (fun g => ∑ z ∈ B, fhat p a b c z f g)
        = Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)) := by
      rw [l2norm]
      exact congrArg Real.sqrt (hplan f B)
    have hcontra : l2norm ((fun g => ∑ z ∈ B, fhat p a b c z (fun x => f (y * x)) g)
        - (fun g => ∑ z ∈ B, fhat p a b c z f g)) ≤ l2norm (fun g => f (y * g) - f g) := by
      rw [← (relT_fhat_add).2.2 p B (fun x => f (y * x)) f]
      exact relT_smooth_contract p hinv hplan B ((fun x => f (y * x)) - f)
    rw [← hA, ← hB]
    exact le_trans (l2norm_sub_rev _ _) hcontra
  have hA0 : 0 ≤ ∑ w ∈ B.image M, l2sq (fhat p a b c w f) :=
    Finset.sum_nonneg fun w _ => l2sq_nonneg _
  have hB0 : 0 ≤ ∑ z ∈ B, l2sq (fhat p a b c z f) :=
    Finset.sum_nonneg fun z _ => l2sq_nonneg _
  have he2 : l2norm (fun g => f (y * g) - f g) ^ 2 = l2sq (fun g => f (y * g) - f g) :=
    Real.sq_sqrt (l2sq_nonneg _)
  have key := relT_smooth_arith (Real.sqrt (∑ w ∈ B.image M, l2sq (fhat p a b c w f)))
      (Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f)))
      (l2norm (fun g => f (y * g) - f g)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hsqrt
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, he2] at key
  exact key

theorem relT_smooth :
    ∀ (p : ℕ) [Fact p.Prime] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
        (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
             (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            ∑ z : ZMod p × ZMod p, fhat p a b c z h g = h g) →
        (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
             (B : Finset (ZMod p × ZMod p)),
            l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h)) →
        (∀ (k : ZMod p) (z : ZMod p × ZMod p)
             (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z (fun x => f (sl3E p a b k * x)) g
              = fhat p a b c (Mab p (-k) z) f (sl3E p a b k * g)) →
        (∀ (k : ZMod p) (z : ZMod p × ZMod p)
             (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z (fun x => f (sl3E p b a k * x)) g
              = fhat p a b c (Mba p (-k) z) f (sl3E p b a k * g)) →
        ∀ B : Finset (ZMod p × ZMod p),
          |(∑ z ∈ B.image (fun z => (z.1 + z.2, z.2)), l2sq (fhat p a b c z f))
              - ∑ z ∈ B, l2sq (fhat p a b c z f)|
            ≤ 2 * l2norm (fun g => f (sl3E p b a (-1) * g) - f g)
                * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
              + l2sq (fun g => f (sl3E p b a (-1) * g) - f g)
        ∧ |(∑ z ∈ B.image (fun z => (z.1 - z.2, z.2)), l2sq (fhat p a b c z f))
              - ∑ z ∈ B, l2sq (fhat p a b c z f)|
            ≤ 2 * l2norm (fun g => f (sl3E p b a 1 * g) - f g)
                * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
              + l2sq (fun g => f (sl3E p b a 1 * g) - f g)
        ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 + z.1)), l2sq (fhat p a b c z f))
              - ∑ z ∈ B, l2sq (fhat p a b c z f)|
            ≤ 2 * l2norm (fun g => f (sl3E p a b (-1) * g) - f g)
                * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
              + l2sq (fun g => f (sl3E p a b (-1) * g) - f g)
        ∧ |(∑ z ∈ B.image (fun z => (z.1, z.2 - z.1)), l2sq (fhat p a b c z f))
              - ∑ z ∈ B, l2sq (fhat p a b c z f)|
            ≤ 2 * l2norm (fun g => f (sl3E p a b 1 * g) - f g)
                * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
              + l2sq (fun g => f (sl3E p a b 1 * g) - f g) := by

  intro p hp a b c hab hac hbc f hinv hplan hconjab hconjba B
  have key1 : |(∑ z ∈ B.image (fun z : ZMod p × ZMod p => (z.1 + z.2, z.2)),
        l2sq (fhat p a b c z f)) - ∑ z ∈ B, l2sq (fhat p a b c z f)|
      ≤ 2 * l2norm (fun g => f (sl3E p b a (-1) * g) - f g)
          * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
        + l2sq (fun g => f (sl3E p b a (-1) * g) - f g) := by
    have himg : B.image (fun z : ZMod p × ZMod p => (z.1 + z.2, z.2)) = B.image (Mba p 1) := by
      congr 1
      funext z
      simp [Mba]
    rw [himg]
    exact smooth_step p f hinv hplan (sl3E p b a (-1)) (Mba p 1) (MbaEquiv p 1).injective
      (fun z g => by simpa [Mba] using hconjba (-1) z g) B
  have key2 : |(∑ z ∈ B.image (fun z : ZMod p × ZMod p => (z.1 - z.2, z.2)),
        l2sq (fhat p a b c z f)) - ∑ z ∈ B, l2sq (fhat p a b c z f)|
      ≤ 2 * l2norm (fun g => f (sl3E p b a 1 * g) - f g)
          * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
        + l2sq (fun g => f (sl3E p b a 1 * g) - f g) := by
    have himg : B.image (fun z : ZMod p × ZMod p => (z.1 - z.2, z.2)) = B.image (Mba p (-1)) := by
      congr 1
      funext z
      simp [Mba]
      ring
    rw [himg]
    exact smooth_step p f hinv hplan (sl3E p b a 1) (Mba p (-1)) (MbaEquiv p (-1)).injective
      (fun z g => hconjba 1 z g) B
  have key3 : |(∑ z ∈ B.image (fun z : ZMod p × ZMod p => (z.1, z.2 + z.1)),
        l2sq (fhat p a b c z f)) - ∑ z ∈ B, l2sq (fhat p a b c z f)|
      ≤ 2 * l2norm (fun g => f (sl3E p a b (-1) * g) - f g)
          * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
        + l2sq (fun g => f (sl3E p a b (-1) * g) - f g) := by
    have himg : B.image (fun z : ZMod p × ZMod p => (z.1, z.2 + z.1)) = B.image (Mab p 1) := by
      congr 1
      funext z
      simp [Mab]
      ring
    rw [himg]
    exact smooth_step p f hinv hplan (sl3E p a b (-1)) (Mab p 1) (MabEquiv p 1).injective
      (fun z g => by simpa [Mab] using hconjab (-1) z g) B
  have key4 : |(∑ z ∈ B.image (fun z : ZMod p × ZMod p => (z.1, z.2 - z.1)),
        l2sq (fhat p a b c z f)) - ∑ z ∈ B, l2sq (fhat p a b c z f)|
      ≤ 2 * l2norm (fun g => f (sl3E p a b 1 * g) - f g)
          * Real.sqrt (∑ z ∈ B, l2sq (fhat p a b c z f))
        + l2sq (fun g => f (sl3E p a b 1 * g) - f g) := by
    have himg : B.image (fun z : ZMod p × ZMod p => (z.1, z.2 - z.1)) = B.image (Mab p (-1)) := by
      congr 1
      funext z
      simp [Mab]
      ring
    rw [himg]
    exact smooth_step p f hinv hplan (sl3E p a b 1) (Mab p (-1)) (MabEquiv p (-1)).injective
      (fun z g => hconjab 1 z g) B
  exact ⟨key1, key2, key3, key4⟩

end Work.LT
