import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

noncomputable section

/-! ## Auxiliary identities -/

/-- `Work.MotK.kleinP` is homogeneous of degree two in the coordinates: every monomial of every
Pfaffian `p_k` is `x i * x l` up to a scalar. -/
theorem kleinP_smul {R : Type*} [CommRing R] (a b c : R) (x : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => c * x i) k = c ^ 2 * Work.MotK.kleinP a b x k := by
  fin_cases k <;>
    simp [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4] <;> ring

/-- The defining property of `Work.MotV.root5`, extracted from its `Classical.choose`. -/
theorem root5_spec {𝕜 : Type*} [Field 𝕜] (h : RatFunc 𝕜) :
    root5 h ^ 5 = algebraMap (RatFunc 𝕜) (Kb 𝕜) h := by
  unfold root5
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap (RatFunc 𝕜) (Kb 𝕜) h)
    (by norm_num : 0 < 5))

/-! ## Node KF (bridge equation), in the form in which it is provable -/

/-- **Node KF, from the Klein identities at `Kb 𝕜`.**

The bridge equation consumes exactly two inputs about `Work.MotV.kleinCoord D` at
`L = Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`: the Klein identity (`hkleinK`) and the non-vanishing of
the zeroth coordinate (`hκ0`), both *evaluated at `Kb 𝕜` itself*.  In `Work.MotV.KleinData.Good`
these are the fields `klein_eq` and `coord0_ne`, but their quantifier is `∀ (L : Type)`, a *small*
universe, so `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜) : Type u` cannot be substituted there when
`𝕜 : Type u` with `u ≠ 0`.  Supplying `fun k => hD.klein_eq (Kb 𝕜) k` is legal precisely when
`𝕜 : Type`, which is the universe of the design file `MOTIVIC_S45_STATEMENTS.lean.txt` and of the
challenge (`ChallengeDeps.lean`: `variable (𝕜 𝔽 : Type)`). -/
theorem twCoord_eq_of_klein {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜)
    (hkleinK : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b)
      (kleinCoord D (Kb 𝕜)) k = 0)
    (hκ0 : kleinCoord D (Kb 𝕜) 0 ≠ 0)
    (h : RatFunc 𝕜) (hh : h ≠ 0) (k : Fin 5) :
    kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (algebraMap (RatFunc 𝕜) (Om D) h)
      (twCoord D h) k = 0 := by
  let w : Om D := algebraMap (Kb 𝕜) (Om D) (root5 h)
  have hw_eq : algebraMap (Kb 𝕜) (Om D) (root5 h) = w := rfl
  -- `w` is a fifth root of the twist parameter `h`
  have hw5 : w ^ 5 = algebraMap (RatFunc 𝕜) (Om D) h := by
    show (algebraMap (Kb 𝕜) (Om D) (root5 h)) ^ 5 = _
    rw [← map_pow, root5_spec, IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Kb 𝕜) (Om D)]
  -- hence `w ≠ 0`, because `algebraMap` out of a field is injective
  have hAlg_ne : algebraMap (RatFunc 𝕜) (Om D) h ≠ 0 := by
    intro hA0
    have h1 : (1 : Om D) = 0 := by
      have hh1 := congrArg (algebraMap (RatFunc 𝕜) (Om D)) (mul_inv_cancel₀ hh)
      rw [map_mul, map_one, hA0, zero_mul] at hh1
      exact hh1.symm
    exact one_ne_zero h1
  have hwnz : w ≠ 0 := fun h0 => hAlg_ne (by rw [← hw5, h0, zero_pow (by norm_num)])
  -- the defining identity of the twisted coordinates: `w^i * y_i = κ_i / κ_0`
  have htw : ∀ i : Fin 5, twCoord D h i
      = (algebraMap (Kb 𝕜) (Om D) (root5 h))⁻¹ ^ (i : ℕ) *
        (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := fun i => rfl
  have hpoint : ∀ i : Fin 5, w ^ (i : ℕ) * twCoord D h i
      = kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0 := by
    intro i
    rw [htw i, hw_eq, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hwnz, one_pow, one_mul]
  -- `κ = κ 0 • (κ_i / κ_0)`, so homogeneity of degree two gives the vanishing of `kleinP` on
  -- the coordinates `κ_i / κ_0`
  have hkleinK' := hkleinK k
  have hsplit : kleinCoord D (Kb 𝕜) =
      fun i => kleinCoord D (Kb 𝕜) 0 * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by
    funext i
    exact (mul_div_cancel₀ (kleinCoord D (Kb 𝕜) i) hκ0).symm
  have hhom : ∀ (c : Om D) (z : Fin 5 → Om D),
      Work.MotK.kleinP (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (fun i => c * z i) k
        = c ^ 2 * Work.MotK.kleinP (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) z k :=
    fun c z => kleinP_smul _ _ c z k
  have hz : Work.MotK.kleinP (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b)
      (fun i => kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) k = 0 := by
    rw [hsplit, hhom] at hkleinK'
    exact (mul_eq_zero.mp hkleinK').resolve_left (pow_ne_zero 2 hκ0)
  -- `kleinTw_subst` turns this into the twisted Klein equation
  have hfun : (fun i : Fin 5 => w ^ (i : ℕ) * twCoord D h i)
      = (fun i => kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := funext hpoint
  have hsub := kleinTw_subst (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) w
    (twCoord D h) k
  rw [hfun, hz] at hsub
  have hfin : kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (w ^ 5)
      (twCoord D h) k = 0 :=
    (mul_eq_zero.mp hsub.symm).resolve_left (pow_ne_zero _ hwnz)
  rw [hw5] at hfin
  exact hfin

/-- **Node KF at universe `0`.**  The bridge equation as it appears in the design file
`MOTIVIC_S45_STATEMENTS.lean.txt` (`{𝕜 : Type}`) and as it is needed by the challenge, whose base
field is small (`ChallengeDeps.lean`: `variable (𝕜 𝔽 : Type)`; `theorem_1_2_2 (𝕜 : Subfield ℂ)`).
Here `Kb 𝕜` is a small type, so `Work.MotV.KleinData.Good.klein_eq`/`coord0_ne` do apply at
`L = Kb 𝕜` and the bridge equation follows. -/
theorem twCoord_eq_univ0 {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good) (h : RatFunc 𝕜)
    (hh : h ≠ 0) (k : Fin 5) :
    kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (algebraMap (RatFunc 𝕜) (Om D) h)
      (twCoord D h) k = 0 :=
  twCoord_eq_of_klein D (fun k => hD.klein_eq (Kb 𝕜) k) (hD.coord0_ne (Kb 𝕜)) h hh k

/-! ## The obstruction for `{𝕜 : Type*}`: the counterexample data

The four lemmas below are the machine-checked part of the counterexample to `twCoord_eq` as
stated with `{𝕜 : Type*}`.  They show: for Klein data whose coordinate matrix is the delta of
`(0,0)`, the twisted point is `(1,0,0,0,0)`, where the `k = 0` twisted Klein equation takes the
value `-a*b ≠ 0`.  Such data satisfies `D.Good` vacuously whenever `𝕜 : Type u` (`u ≠ 0`) admits no
`𝕜`-algebra in universe `0` (e.g. a field of cardinality at least the first inaccessible), because
then the three `∀ (L : Type)` fields of `Good` are vacuous. -/

/-- With `coord = δ_{(0,0)}` the Klein coordinates are `κ_i = if i = 0 then 1 else 0`. -/
theorem kleinCoord_delta {𝕜 L : Type} [Field 𝕜] [Field L] [Algebra 𝕜 L] (D : KleinData 𝕜)
    (h0 : ∀ m : Fin 5, D.coord (0 : Fin 5) m = if m = 0 then 1 else 0)
    (hne : ∀ (i : Fin 5) (m : Fin 5), i ≠ 0 → D.coord i m = 0) :
    kleinCoord D L = fun i => if i = 0 then 1 else 0 := by
  funext i
  rw [kleinCoord]
  by_cases hi : i = 0
  · rw [ite_eq_left hi, hi, Finset.sum_eq_single (0 : Fin 5)]
    · simp [h0]
    · intro m _ hm; simp [h0 m, hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hi]
    exact Finset.sum_eq_zero fun m _ => by rw [hne i m hi, map_zero, map_zero, zero_mul]

/-- With those Klein coordinates the twisted point is `(1,0,0,0,0)`. -/
theorem twCoord_delta {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (h : RatFunc 𝕜)
    (hκ : kleinCoord D (Kb 𝕜) = fun i => if i = 0 then 1 else 0) :
    twCoord D h = ![1, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [twCoord, hκ]

/-- On the point `(1,0,0,0,0)` the twisted Klein equation `k = 0` has the value `-a*b`. -/
theorem kleinTw_origin {F : Type*} [CommRing F] (a b h : F) :
    kleinTw a b h ![1, 0, 0, 0, 0] 0 = -a * b := by
  simp [kleinTw, twMon]

/-- **The counterexample.**  For the delta configuration the bridge equation fails at `k = 0`
(here `a = algebraMap 𝕜 (Om D) D.a`, etc.); so the equation genuinely needs the Klein relations,
which for `{𝕜 : Type*}` are not available at `Kb 𝕜`. -/
theorem not_kleinTw_delta {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (h : RatFunc 𝕜)
    (hab : D.a * D.b ≠ 0)
    (hκ : kleinCoord D (Kb 𝕜) = fun i => if i = 0 then 1 else 0) :
    kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (algebraMap (RatFunc 𝕜) (Om D) h)
      (twCoord D h) 0 ≠ 0 := by
  have hmap_ne : ∀ x : 𝕜, x ≠ 0 → algebraMap 𝕜 (Om D) x ≠ 0 := by
    intro x hx h0
    have h1 : (1 : Om D) = 0 := by
      have hh1 := congrArg (algebraMap 𝕜 (Om D)) (mul_inv_cancel₀ hx)
      rw [map_mul, map_one, h0, zero_mul] at hh1
      exact hh1.symm
    exact one_ne_zero h1
  rw [twCoord_delta D h hκ, kleinTw_origin, neg_mul, neg_ne_zero]
  exact mul_ne_zero (hmap_ne D.a fun hz => hab (by rw [hz, zero_mul]))
    (hmap_ne D.b fun hz => hab (by rw [hz, mul_zero]))

/-! ## Node KF, as requested -/

/-- Node KF (bridge equation): the twisted coordinates `twCoord D h` of the T-twist satisfy the
twisted Klein equations `kleinTw`, for `h ≠ 0`.

Route.  `Work.MotV.twCoord D h i = w^{-i} * (κ i / κ 0)` where `w = algebraMap (Kb 𝕜) (Om D)
(root5 h)`, `κ = kleinCoord D (Kb 𝕜)`, and `root5 h ^ 5 = algebraMap (RatFunc 𝕜) (Kb 𝕜) h` by
`Classical.choose_spec` of `IsAlgClosed.exists_pow_nat_eq`.  So `kleinCoord D (Kb 𝕜)` is
`κ 0 • (fun i => w^i * twCoord D h i)`.  `Work.MotK.kleinP` is homogeneous of degree two in the
coordinates (each monomial is `x i * x j` up to a scalar), so `D.Good.klein_eq` for `L = Kb 𝕜`
gives `0 = (κ 0)^2 * kleinP a b (fun i => w^i * twCoord D h i) k`.  The proved identity
`kleinTw_subst` identifies the last factor with `w^(4k) * kleinTw a b (w^5) (twCoord D h) k`, and
`w^5 = algebraMap h ≠ 0`, `κ 0 ≠ 0` (`D.Good.coord0_ne`) finish.  Note the scalar-change lemmas
`algebraMap (Kb 𝕜) (Om D) (algebraMap 𝕜 (Kb 𝕜) D.a) = algebraMap 𝕜 (Om D) D.a` are needed because
`klein_eq` lives over `Kb 𝕜` while the conclusion lives over `Om D`.

**This statement, with `{𝕜 : Type*}`, is not provable, and is false in the standard semantics.**
The step "`D.Good.klein_eq` for `L = Kb 𝕜`" is illegitimate as soon as `𝕜` is not a small type:
`KleinData.Good.klein_eq` (like `coord0_ne` and `T_diag`) quantifies over `L : Type`, i.e. over
the universe `0`, whereas `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜) : Type u` when `𝕜 : Type u`.  Lean
confirms this: `hD.klein_eq (Kb 𝕜)` does not elaborate for `{𝕜 : Type*}` -- "the argument `𝕜` has
type `Type u` ... but is expected to have type `Type`" -- while the identical line elaborates for
`{𝕜 : Type}`.  See `twCoord_eq_of_klein` (the two Klein inputs disambiguated at `Kb 𝕜`) and
`twCoord_eq_univ0` (the statement at universe `0`, which is the form in the design file and the
form the challenge needs).

Since the Klein relations among `kleinCoord D (Kb 𝕜)` are available *only* through `klein_eq`, the
conclusion does not follow from `D.Good` for a large `𝕜`: if `𝕜 : Type u` (`u ≠ 0`) admits no
`𝕜`-algebra in universe `0`, then the three `∀ (L : Type)` fields of `Good` are vacuous, and the
delta configuration above (`a = b = 1`, `E : y² = x³ + x + 1` with `j = 6912/31`, so `elliptic`,
`ab_ne`, `j_ne_zero`, `j_ne` all hold) satisfies `D.Good` while
`kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (algebraMap (RatFunc 𝕜) (Om D) h)
(twCoord D h) 0 ≠ 0` (`not_kleinTw_delta`), contradicting the conclusion for `k = 0`.

**Conclusion for this area.**  The statement of this node is therefore made at `{𝕜 : Type}`, the
universe of the design file's `bridge`/`twist_regular`/`twist_natural`/`twist_iso_point`/`rigidity`/
`constantsOnly_twist` (and of the challenge: `ChallengeDeps.lean` has `variable (𝕜 𝔽 : Type)`,
`theorem_1_2_2 (hn) (𝕜 : Subfield ℂ)`).  This is the only place where this area deviates from the
letter of `MOTIVIC_S45_STATEMENTS.lean.txt` (which writes `{𝕜 : Type*}` here); at `{𝕜 : Type}`,
`Kb 𝕜` is a small type and the three universe-`0` fields of `D.Good` do apply at `L = Kb 𝕜`. -/
theorem twCoord_eq {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good) (h : RatFunc 𝕜)
    (hh : h ≠ 0) (k : Fin 5) :
    kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b) (algebraMap (RatFunc 𝕜) (Om D) h)
      (twCoord D h) k = 0 :=
  twCoord_eq_of_klein D (fun k => hD.klein_eq (Kb 𝕜) k) (hD.coord0_ne (Kb 𝕜)) h hh k

end

end Work.MotV
