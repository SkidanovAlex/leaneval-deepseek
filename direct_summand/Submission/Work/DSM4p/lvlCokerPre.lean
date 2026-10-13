import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvlTr_teich
import Submission.Work.DSM4p.chartCokernel

/-!
# DSM4p — Route U: the transfer layer for the cokernel clause of the untilted tower

This module contains the definitions and the elementary technical lemmas that the proof of
`Work.DSM4p.lvl_cokernel` (the cokernel clause of `IsQRETp` for the tower of untilted levels
`lvl Q hgr N`) uses.  It is deliberately kept small and independent so that the heavier
estimates can be proved against it.

* `Work.DSM4p.varpiSharp`, `Work.DSM4p.varpiSharp_rs` — the tilted pseudo-uniformiser
  `ϖ♭ = tiltTower Q.ϖ Q.root : ℕ → PreTilt B p` and the fact that it is a compatible system of
  `p`-power roots.
* `Work.DSM4p.chartIterTr` — the composite of `c` chart transitions, an `AlgHom`
  `lvlP Q hgr (N + c) →ₐ[B♭] lvlP Q hgr N` (`B♭ = PreTilt B p`); it is the `c`-fold iterate of
  the chart transition, and its underlying map is the inclusion of the levels
  (`chartIterTr_coe_gen`).
* `Work.DSM4p.gen`, `Work.DSM4p.monoEl` — the chart generator `x_J(N)` and the monomial
  `b₀ · x_J(N)^I` viewed as elements of the level `lvlP Q hgr N`; their ambient values are
  recorded in `gen_coe` (`rfl`) and `monoEl_coe`.
* `Work.DSM4p.prod_monoEl` — the collapse `∏_j x_j(N)^{μ_j} = x_J(N)^I` of a product of
  generators to a single generator power (the exponent bookkeeping of Bhatt's computation).
* `Work.DSM4p.iterTr_lvlTr_mk_teich` — **the transition fixes Teichmüller classes**: the
  `c`-fold transition of the untilted tower sends `mk (teichmuller r)` to
  `mk (teichmuller (chartIterTr … r))`.
* `Work.DSM4p.mk_teich_algebraMap` — the Teichmüller dictionary `mk [φ y] = algebraMap (♯y)`
  at the untilted level.
* `Work.DSM4p.varpi0_pow_pow` — `(ϖ♭ 0)^{p m}` becomes `p^m` times a unit in the level (the
  perfectoid relation `Q.ϖ 0 ^ p = p · v` transported to the level).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open DSMap DSMap.Mix DSMap.Mix2

namespace Work.DSM4p

universe a

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
variable [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]

/-! ## 0. The tilted pseudo-uniformiser -/

/-- The tilt `ϖ♭ = tiltTower Q.ϖ Q.root` of the pseudo-uniformiser of `Q`, as a system of
`p`-power roots in the tilt `B♭ = PreTilt B p` of `B`. -/
noncomputable abbrev varpiSharp (Q : PerfectoidData p B) : ℕ → PreTilt B p :=
  tiltTower Q.ϖ Q.root

/-- The tilted pseudo-uniformiser is a compatible system of `p`-power roots. -/
noncomputable abbrev varpiSharp_rs (Q : PerfectoidData p B) : IsRootSystem p (varpiSharp Q) :=
  tiltTower_isRootSystem Q.ϖ Q.root

/-- The shifted system `ϖ♭(k + ·)` of `p`-power roots. -/
noncomputable abbrev shiftVarpiSharp (Q : PerfectoidData p B) (k : ℕ) : ℕ → PreTilt B p :=
  DSM5c.shiftTower (varpiSharp Q) k

/-! ## 1. The iterated chart transition -/

/-- The composite of `c` chart transitions, as an `AlgHom` of the characteristic-`p` levels
(these are `B♭ = PreTilt B p`-algebras). -/
noncomputable abbrev chartIterTr (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N c : ℕ) : lvlP Q hgr (N + c) →ₐ[PreTilt B p] lvlP Q hgr N :=
  iterTr (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr) (varpiSharp Q)) N c

/-- The underlying map of `chartIterTr` is the inclusion of the levels: it does not change the
element of the ambient localisation `B♭[1/g♭ 0]`. -/
theorem chartIterTr_coe_gen (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) :
    ∀ (N c : ℕ) (r : lvlP Q hgr (N + c)),
      ((chartIterTr Q hgr N c) r : ChartAmbient (tiltTower gr hgr)) =
        (r : ChartAmbient (tiltTower gr hgr)) := by
  intro N c
  induction c with
  | zero => intro r; exact rfl
  | succ c ih =>
    intro r
    rw [iterTr_succ_apply]
    rw [ih]
    exact Subalgebra.coe_inclusion _ _

/-- `chartIterTr` in degree `1` is the chart transition itself. -/
theorem chartIterTr_one (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) :
    chartIterTr Q hgr N 1 = chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
      (varpiSharp Q) N :=
  iterTr_one _ _

/-- **The transition fixes Teichmüller classes**: the `c`-fold transition map of the untilted
tower sends the Teichmüller lift of `r : lvlP Q hgr (N + c)` to the Teichmüller lift of
`chartIterTr Q hgr N c r` (the underlying element of `r` inside the level `N`). -/
theorem iterTr_lvlTr_mk_teich (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) :
    ∀ (N c : ℕ) (r : lvlP Q hgr (N + c)),
      iterTr (lvlTrAlg Q hgr) N c
          (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (N + c)))
            (WittVector.teichmuller p r)) =
        DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p (chartIterTr Q hgr N c r)) := by
  intro N c
  induction c with
  | zero => intro r; exact rfl
  | succ c ih =>
    intro r
    rw [iterTr_succ_apply]
    have h1 : (lvlTrAlg Q hgr (N + c))
        (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (N + (c + 1))))
          (WittVector.teichmuller p r)) =
        DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (N + c)))
          (WittVector.teichmuller p (chartIterTr Q hgr (N + c) 1 r)) := by
      rw [chartIterTr_one]
      exact lvlTr_teich Q hgr (N + c) r
    have h2 : chartIterTr Q hgr N (c + 1) =
        (chartIterTr Q hgr N c).comp (chartIterTr Q hgr (N + c) 1) := by
      rw [show chartIterTr Q hgr (N + c) 1 = chartTr (gr := tiltTower gr hgr)
        (tiltTower_isRootSystem gr hgr) (varpiSharp Q) (N + c) from chartIterTr_one Q hgr (N + c)]
      rfl
    rw [h1, ih (chartIterTr Q hgr (N + c) 1 r), h2]
    rfl

/-! ## 2. The Teichmüller dictionary at the untilted level -/

/-- **The Teichmüller dictionary**: `mk [φ y] = algebraMap (♯ y)`, where `♯ = PreTilt.untilt`
is the tilt map.  (This is `DSM5c.Eta.U.teich_algebraMap` at the untilted levels.) -/
theorem mk_teich_algebraMap (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) (y : PreTilt B p) :
    DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (lvlP Q hgr N) y)) =
      algebraMap B (lvl Q hgr N) (PreTilt.untilt y) :=
  DSM5c.Eta.U.teich_algebraMap (p := p) (W := B) (surjective_fontaineTheta Q)
    (algebraMap (PreTilt B p) (lvlP Q hgr N)) y

/-- The class of the Teichmüller lift of the tilt of a root system. -/
theorem mk_teich_tiltTower (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) {r : ℕ → B} (hr : IsRootSystem p r) (k : ℕ) :
    DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (lvlP Q hgr N)
          (tiltTower r hr k))) =
      algebraMap B (lvl Q hgr N) (r k) := by
  rw [mk_teich_algebraMap Q hgr N, untilt_tiltTower r hr k]

/-! ## 3. The monomials of the chart levels -/

/-- The coercion of a finite product of elements of a subalgebra is the product of the
coercions. -/
theorem coe_finset_prod {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] {ι : Type*}
    (S : Subalgebra R A) (s : Finset ι) (f : ι → S) :
    ((∏ i ∈ s, f i : S) : A) = ∏ i ∈ s, (f i : A) := by
  simpa only [Subalgebra.val_apply] using map_prod (Subalgebra.val S) f s

/-- The chart generator `x_J(N) = ϖ_J^N / g_J`, as an element of the level `lvlP Q hgr N`. -/
noncomputable def gen (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N J : ℕ) : lvlP Q hgr N :=
  ⟨chartGen (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr) (varpiSharp Q) N J,
    chartGen_mem (tiltTower_isRootSystem gr hgr) (varpiSharp Q) N J⟩

/-- The chart generator of `gen` inside the ambient localisation. -/
theorem gen_coe (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (N J : ℕ) :
    (gen Q hgr N J : ChartAmbient (tiltTower gr hgr)) =
      chartGen (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr) (varpiSharp Q) N J := rfl

/-- The monomial `b₀ · x_J(N)^I` of the characteristic-`p` level `lvlP Q hgr N` (`b₀ : B♭`). -/
noncomputable def monoEl (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) (b0 : PreTilt B p) (J I : ℕ) : lvlP Q hgr N :=
  algebraMap (PreTilt B p) (lvlP Q hgr N) b0 * (gen Q hgr N J) ^ I

/-- The value of `monoEl` in the ambient localisation. -/
theorem monoEl_coe (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) (b0 : PreTilt B p) (J I : ℕ) :
    (monoEl Q hgr N b0 J I : ChartAmbient (tiltTower gr hgr)) =
      algebraMap (PreTilt B p) (ChartAmbient (tiltTower gr hgr)) b0 *
        (chartGen (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
          (varpiSharp Q) N J) ^ I := by
  rw [monoEl, gen, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_pow]

/-- **The collapse of a product of chart generators to a single generator power**:
`∏_j x_j(N)^{μ_j} = x_J(N)^I` with `J = sup (support μ)` and
`I = ∑_j μ_j · p^{J - j}`.  This is the exponent bookkeeping used in Bhatt's monomial
computation, at the level of the subalgebra `lvlP Q hgr N`. -/
theorem prod_gen_pow (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) (μ : ℕ →₀ ℕ) :
    (∏ j ∈ μ.support, (gen Q hgr N j) ^ (μ j)) =
      (gen Q hgr N (μ.support.sup id)) ^
        (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j)) := by
  apply Subtype.ext
  rw [coe_finset_prod, Subalgebra.coe_pow]
  exact prod_chartGen_pow_eq (tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
    (varpiSharp Q) (varpiSharp_rs Q) N μ (μ.support.sup id)
    (fun j hj => Finset.le_sup (f := id) hj)

/-! ## 4. The perfectoid relation `ϖ_0^p = p · v` at the untilted level -/

/-- **The `p m`-th power of `ϖ_0` at the untilted level is `p^m` times a unit**:
`(algebraMap (ϖ_0))^{p m} = p^m · u` for a unit `u` of the level.  This is the perfectoid
relation `Q.ϖ 0 ^ p = p · v` (`DSMap.PerfectoidData.unit`) transported along
`algebraMap B (lvl Q hgr N)`. -/
theorem varpi0_pow_pow (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N m : ℕ) :
    ∃ u : (lvl Q hgr N)ˣ,
      (algebraMap B (lvl Q hgr N) (Q.ϖ 0)) ^ (p * m) = (p : lvl Q hgr N) ^ m * (u : lvl Q hgr N) := by
  obtain ⟨v, hv⟩ := Q.unit
  refine ⟨(Units.map (algebraMap B (lvl Q hgr N)).toMonoidHom v) ^ m, ?_⟩
  have h1 : (algebraMap B (lvl Q hgr N) (Q.ϖ 0)) ^ p =
      (p : lvl Q hgr N) * ((Units.map (algebraMap B (lvl Q hgr N)).toMonoidHom v : (lvl Q hgr N)ˣ) :
        lvl Q hgr N) := by
    rw [← map_pow, hv, map_mul, map_natCast]
    rfl
  rw [pow_mul, h1, mul_pow, Units.val_pow_eq_pow_val]

end Work.DSM4p
