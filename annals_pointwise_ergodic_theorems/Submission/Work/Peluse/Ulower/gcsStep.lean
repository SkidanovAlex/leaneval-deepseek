import Mathlib
import Submission.Work.Peluse.Concat.gowersCS
import Submission.Work.Peluse.Ulower.rankInduction

/-!
# The Gowers--Cauchy--Schwarz step of the phase elimination (Peluse, Lemma 7.5)

This module instantiates `Work.Peluse.Concat.gowersCS` (the GCS inequality for a product of
`1`-bounded functions, each independent of one coordinate) at the direction set
`Q = arithIcc 1 D` and at the *blind* phase `θ u v = ∑ i, ψ i u v` of the target
`Work.Peluse.Ulower.lemma75_control`.  Writing `G_{u,v} = cubeTerm u v f`, the conclusion is

```
‖ D^{-s} ∑_{v ∈ Q^s} G_{u,v}(x) conj(G_{u,v}(z)) ∏ i, e(ψ i u v · (x-z)) ‖^{2^s}
  ≤ ‖ D^{-2s} ∑_{v⁰,v¹ ∈ Q^s} ∏_{ω : Fin s → Bool}
        star^{|ω|} ( G_{u, mix_ω v⁰ v¹}(x) · conj (G_{u, mix_ω v⁰ v¹}(z)) ) ‖ ,
```

the `ℓ²`-aggregate GCS step of `NOTES_lemma75_GCS_route.md` §1.  The hypothesis
`hind : ∀ i u v a b, ψ i u (Function.update v i a) = ψ i u (Function.update v i b)` is exactly the
blindness of `ψ i` in the `i`-th coordinate of `v`; it is what makes `e(ψ i u v (x-z))` blind in
`v i`, i.e. a legitimate `g`-factor of `gowersCS`.

The mathematical content is entirely in `gowersCS`; what is proved here is the bookkeeping:
`Fintype.card (↥(arithIcc 1 D)) = D` and the identification of the two sums.  Use
`prod_exp_psi` to convert the `∏ i, e(ψ i · (x-z))` form into `e((∑ i, ψ i) · (x-z))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- `∏ i, e(ψ i · t) = e((∑ i, ψ i) · t)`: the product of the single-coordinate exponentials is the
exponential of the total phase `θ u v = ∑ i, ψ i u v`. -/
lemma prod_exp_psi (s : ℕ) (ψs : Fin s → ℝ) (t : ℝ) :
    (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I * ψs i * t))
      = Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψs i) * t) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

/-- **The GCS step of the phase elimination.**  `gowersCS` instantiated at `Q = arithIcc 1 D` and
at the blind phase `θ u v = ∑ i, ψ i u v`. -/
theorem gcsStep (s D : ℕ) (hs : 1 ≤ s) (hD : 1 ≤ D) (f : ℤ → ℂ) (u : Fin s → ℤ)
    (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ)
    (hind : ∀ i u v a b, ψ i u (Function.update v i a) = ψ i u (Function.update v i b))
    (x z : ℤ) :
    ‖(D : ℂ)⁻¹ ^ s *
        ∑ v : Fin s → ↥(Work.Peluse.arithIcc 1 D),
          (Work.Peluse.cubeTerm u (fun i => (v i).1) f x *
              star (Work.Peluse.cubeTerm u (fun i => (v i).1) f z)) *
            (∏ i : Fin s, Complex.exp (2 * Real.pi * Complex.I *
              (ψ i u (fun j => (v j).1)) * ((x : ℝ) - (z : ℝ))))‖ ^ (2 ^ s)
      ≤ ‖(D : ℂ)⁻¹ ^ (2 * s) *
        ∑ v0 : Fin s → ↥(Work.Peluse.arithIcc 1 D),
          ∑ v1 : Fin s → ↥(Work.Peluse.arithIcc 1 D),
            ∏ ω : Fin s → Bool,
              (star^[Work.Peluse.weight ω])
                (Work.Peluse.cubeTerm u
                    (fun i => (Work.Peluse.Concat.mix ω v0 v1 i).1) f x *
                  star (Work.Peluse.cubeTerm u
                    (fun i => (Work.Peluse.Concat.mix ω v0 v1 i).1) f z))‖ := by
  classical
  have hcard : Fintype.card ↥(Work.Peluse.arithIcc 1 D) = D := by
    rw [Fintype.card_coe, card_arithIcc_one]
  have hb0 : ∀ i : Fin s, ∀ v v' : Fin s → ↥(Work.Peluse.arithIcc 1 D),
      (∀ j, j ≠ i → v j = v' j) →
      ψ i u (fun j => (v j).1) = ψ i u (fun j => (v' j).1) := by
    intro i v v' hv
    have hfun : (fun j => (v j).1) = Function.update (fun j => (v' j).1) i ((v i).1) := by
      funext j
      rcases eq_or_ne j i with hji | hji
      · subst hji; rw [Function.update_self]
      · rw [Function.update_of_ne hji]; exact congrArg Subtype.val (hv j hji)
    rw [hfun, hind i _ _ _ (v' i), Function.update_eq_self]
  have key := Work.Peluse.Concat.gowersCS s ↥(Work.Peluse.arithIcc 1 D)
    (fun v => Work.Peluse.cubeTerm u (fun i => (v i).1) f x *
      star (Work.Peluse.cubeTerm u (fun i => (v i).1) f z))
    (fun i v => Complex.exp (2 * Real.pi * Complex.I * (ψ i u (fun j => (v j).1)) *
      ((x : ℝ) - (z : ℝ))))
    (fun i v => by
      rw [Complex.norm_exp]
      simp)
    (fun i v v' hv => by rw [hb0 i v v' hv])
  rw [hcard] at key
  simpa only [Work.Peluse.Concat.mix] using key

end

end Work.Peluse.Ulower
