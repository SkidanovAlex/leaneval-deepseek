import Submission.Work.DSMap.Mix2
import Submission.Work.DSPB1.All

/-!
# DSM5c — basic vocabulary: the tilt of a compatible tower of `p`-th roots

This is the bottom layer of the subproject `DSM5c` of the `direct_summand` development, the
mixed-characteristic node **M5c** (`DSMap.Mix2.area_M5c`, design
`sources/dsmap/direct_summand_mix2.md` §Task 1 (4) and `sources/dsmap/direct_summand_mix_design.md`
§3, nodes PB1–PB5, M5b, M5c).

The frozen statement `DSMap.Mix2.area_M5c` is about a perfectoid ring `W` with data
`QW : DSMap.PerfectoidData p W`, a finite family `t : ι → W` together with a *compatible system of
`p`-power roots* `tr : ι → ℕ → W` (`tr i 0 = t i`, `tr i (k+1) ^ p = tr i k`), one index `j₀` and
one exponent `e` with `t j₀ = QW.ϖ 0 ^ e`.

The characteristic-`p` input `area_M5b` lives on the **tilt** `R := PreTilt W p` of `W`, applied to
the *tilted* generators `t♭ i` and the element `T♭` whose power is `t♭ j₀`.  This file provides the
vocabulary for that transfer:

* `Work.DSM5c.tiltOf` — the tilt `(tr k mod p)_k ∈ PreTilt W p` of a compatible tower;
* `Work.DSM5c.tiltOf_varpi` — for the `ϖ`-tower of a `PerfectoidData` this is exactly `PB1`'s
  `Work.DSPB1.varpiTilt` (the `♯`-element `ϖ♭` with `PreTilt.untilt ϖ♭ = ϖ 0`, `DSMap.Mix` PB1);
* `Work.DSM5c.tiltOf_pow` — the tilt of the tower `k ↦ tr k ^ e` is the `e`-th power of the tilt
  (this is the algebraic content of the "Precision 1" remark of the design: `t_{j₀} = ϖ₀^e` is a
  *`♯`-element*, so the tilted ideal `J♭` contains a power of `ϖ♭`);
* `Work.DSM5c.tiltGens`, `Work.DSM5c.tiltVarpi` and
  `Work.DSM5c.tiltGens_j₀_eq_tiltVarpi_pow` — the tilted M5b-datum attached to the M5c data, with
  `t♭ j₀ = (ϖ♭) ^ e` when the root tower of `t j₀` is the canonical one
  (`tr j₀ k = QW.ϖ k ^ e`), which is the normalisation produced by the nodes `DEN`/`ROOTS` of the
  M5c proof (`Submission/Work/DSDEN`, `Submission/Work/DSROOTS`); see `NOTES.md` §4 for the
  discussion of an arbitrary root tower.

## Conventions

`PreTilt W p = Perfection (W ⧸ (p)) p` is Mathlib's tilt: a compatible system `(x k)_k` with
`(x (k+1)) ^ p = x k`; `PreTilt.coeff k` is its `k`-th coefficient in `W ⧸ (p)`.  The
`p`-power-root operator inside the tilt is `(frobeniusEquiv (PreTilt W p) p).symm` (so `k`-fold
iteration inverts `p ^ k`-th powers).  Following `Submission/Work/DSPB1/Basic.lean` we write the
tilt of a `p`-power tower as `tiltOf`, so that the M5b input can be consumed verbatim.

Because `PreTilt O p` is a `def` for `Perfection (ModP O p) p`, the elimination principle
`Perfection.ext` is reached through the local `tilt_ext` below, which is stated in terms of
`PreTilt.coeff` (the only form in which the goal uses the reducible unfolding reliably).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.DSM5c

universe a

open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]

/-! ## The tilt of a compatible tower -/

/-- **The tilt of a compatible system of `p`-power roots**: the element of
`PreTilt W p = Perfection (W ⧸ (p)) p` whose `k`-th coefficient is `tr k` modulo `p`.

The compatibility `(tr (k+1) mod p) ^ p = tr k mod p` is exactly the hypothesis `htr`. -/
def tiltOf (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) : PreTilt W p :=
  ⟨fun k => Ideal.Quotient.mk (Ideal.span {(p : W)}) (tr k), fun k => by
    rw [← map_pow, htr k]⟩

/-- The `k`-th coefficient of the tilt of a tower is the `k`-th term of the tower modulo `p`. -/
@[simp] theorem coeff_tiltOf (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (k : ℕ) :
    PreTilt.coeff k (tiltOf tr htr) =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (tr k) :=
  rfl

/-- **Elimination principle for the tilt**: two elements of `PreTilt W p` agree as soon as all their
coefficients do.  This is `Perfection.ext`, restated in `PreTilt.coeff` form (the shape in which
proofs about `tiltOf` are carried out). -/
theorem tilt_ext {x y : PreTilt W p}
    (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) : x = y :=
  Perfection.ext fun n => by
    rw [← PreTilt.coeff_def, ← PreTilt.coeff_def]
    exact h n

/-- Two tilts of towers agree as soon as the towers agree. -/
theorem tiltOf_congr {tr tr' : ℕ → W} (h : tr = tr')
    (htr : ∀ k, tr (k + 1) ^ p = tr k) (htr' : ∀ k, tr' (k + 1) ^ p = tr' k) :
    tiltOf tr htr = tiltOf tr' htr' := by
  subst h
  rfl

/-- Characterisation of `tiltOf` by its coefficients. -/
theorem tiltOf_eq_iff (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (x : PreTilt W p) :
    x = tiltOf tr htr ↔ ∀ k, PreTilt.coeff k x =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (tr k) := by
  constructor
  · intro h k; rw [h, coeff_tiltOf]
  · intro h; exact tilt_ext fun k => by rw [h k, coeff_tiltOf]

/-! ## Compatibility with `PB1` (`Work.DSPB1.varpiTilt`) -/

/-- **`PB1` square**: for the `ϖ`-tower of a `PerfectoidData` the tilt of the tower is exactly
`Work.DSPB1.varpiTilt`, the element whose untilt is `ϖ 0` (`DSMap.Mix.perfectoid_varpiFlat_proved`).
So `tiltOf` extends the `PB1` vocabulary of `Submission/Work/DSPB1` to arbitrary compatible
systems. -/
theorem tiltOf_varpi (Q : PerfectoidData p W) :
    tiltOf (fun k => Q.ϖ k) (fun k => Q.root k) = Work.DSPB1.varpiTilt Q :=
  tilt_ext fun n => by rw [coeff_tiltOf, Work.DSPB1.coeff_varpiTilt]

/-! ## Powers of towers: the "Precision 1" input -/

/-- The tower `k ↦ tr k ^ e` is again compatible (it is the tower of the `e`-th power). -/
theorem pow_tower_compat (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (e : ℕ) :
    ∀ k, (tr (k + 1) ^ e) ^ p = tr k ^ e := by
  intro k
  rw [← pow_mul, Nat.mul_comm e p, pow_mul, htr k]

/-- **The tilt of an `e`-th power tower is the `e`-th power of the tilt** (M5c "Precision 1",
design Task 1 (2)): if a compatible tower is the `e`-th power of a compatible tower, then its tilt
is the `e`-th power of the tilt.  This is what makes the tilted ideal `J♭ = (t♭ i)` contain a power
of `ϖ♭` when the generator is the `♯`-element `ϖ₀ ^ e`: in the tilt, the generator `t♭ j₀` is then
literally `(ϖ♭) ^ e`. -/
theorem tiltOf_pow (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (e : ℕ) :
    tiltOf (fun k => tr k ^ e) (pow_tower_compat tr htr e) = tiltOf tr htr ^ e :=
  tilt_ext fun n => by rw [map_pow, coeff_tiltOf, coeff_tiltOf, map_pow]

/-! ## Shifting a tower: the Frobenius action on the tilt -/

/-- The shifted tower of a compatible system (dropping the `0`-th term) is compatible. -/
theorem shift_tower_compat (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) :
    ∀ k, tr (k + 1 + 1) ^ p = tr (k + 1) := fun k => htr (k + 1)

/-- The `n`-th coefficient of the `p`-th root of an element of the tilt is its `(n+1)`-st
coefficient. -/
theorem coeff_symm_frobenius (x : PreTilt W p) (n : ℕ) :
    PreTilt.coeff n ((frobeniusEquiv (PreTilt W p) p).symm x) = PreTilt.coeff (n + 1) x := by
  rw [show (frobeniusEquiv (PreTilt W p) p).symm x =
      (frobeniusEquiv (PreTilt W p) p).symm^[1] x from rfl,
    PreTilt.coeff_iterate_frobeniusEquiv_symm, Nat.add_comm]

/-- **The tilt of the shifted tower is the `p`-th root of the tilt**: `k`-fold iteration of this
identity says that the tilt of the `k`-shifted tower is the `k`-th `p`-power root of the tilt of the
tower, i.e. it describes the Frobenius action on `PreTilt W p` in terms of the tower. -/
theorem tiltOf_shift (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) :
    (frobeniusEquiv (PreTilt W p) p).symm (tiltOf tr htr) =
      tiltOf (fun k => tr (k + 1)) (shift_tower_compat tr htr) :=
  tilt_ext fun n => by
    rw [coeff_symm_frobenius, coeff_tiltOf, coeff_tiltOf]

/-- The `k`-shifted tower of a compatible system. -/
def shiftTower (tr : ℕ → W) (k : ℕ) : ℕ → W := fun n => tr (n + k)

theorem shiftTower_compat (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (k : ℕ) :
    ∀ n, shiftTower tr k (n + 1) ^ p = shiftTower tr k n := by
  intro n
  show tr (n + 1 + k) ^ p = tr (n + k)
  rw [show n + 1 + k = (n + k) + 1 from by omega]
  exact htr (n + k)

/-- **Iterated form**: the `k`-th `p`-power root of the tilt of a tower is the tilt of the
`k`-shifted tower. -/
theorem tiltOf_shiftTower (tr : ℕ → W) (htr : ∀ k, tr (k + 1) ^ p = tr k) (k : ℕ) :
    (frobeniusEquiv (PreTilt W p) p).symm^[k] (tiltOf tr htr) =
      tiltOf (shiftTower tr k) (shiftTower_compat tr htr k) := by
  induction k with
  | zero =>
    exact tiltOf_congr (tr := tr) (tr' := shiftTower tr 0)
      (by funext n; rw [shiftTower, Nat.add_zero]) _ _
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, tiltOf_shift]
    refine tiltOf_congr (tr := shiftTower (shiftTower tr k) 1) (tr' := shiftTower tr (k + 1)) ?_ _ _
    funext n
    simp only [shiftTower]
    congr 1
    omega

/-! ## The tilted datum attached to the M5c hypotheses -/

section TiltedDatum

variable {ι : Type a}

/-- **The tilted generators**: the tilt of the root tower of each `t i`. -/
noncomputable def tiltGens (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) : ι → PreTilt W p :=
  fun i => tiltOf (tr i) (htr i)

@[simp] theorem coeff_tiltGens (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (i : ι) (k : ℕ) :
    PreTilt.coeff k (tiltGens t tr htr0 htr i) =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (tr i k) :=
  coeff_tiltOf _ _ _

/-- The `0`-th coefficient of a tilted generator is `t i` modulo `p`. -/
theorem coeff_zero_tiltGens (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (i : ι) :
    PreTilt.coeff 0 (tiltGens t tr htr0 htr i) =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (t i) := by
  rw [coeff_tiltGens, htr0 i]

/-- **The `♯`-element `ϖ♭`** of the tilt: the tilt of the `ϖ`-tower (`PB1`).
It is the `T♭` of the characteristic-`p` input when one generator is `ϖ₀ ^ e`. -/
noncomputable def tiltVarpi (Q : PerfectoidData p W) : PreTilt W p :=
  tiltOf (fun k => Q.ϖ k) (fun k => Q.root k)

theorem tiltVarpi_eq_varpiTilt (Q : PerfectoidData p W) :
    tiltVarpi Q = Work.DSPB1.varpiTilt Q :=
  tiltOf_varpi Q

/-- The `k`-th coefficient of `ϖ♭` is `ϖ k mod p`. -/
@[simp] theorem coeff_tiltVarpi (Q : PerfectoidData p W) (k : ℕ) :
    PreTilt.coeff k (tiltVarpi Q) =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) (Q.ϖ k) :=
  coeff_tiltOf _ _ _

/-- **Precision 1 of the M5c design, tilted form**: if the root tower of the generator `t j₀` is the
canonical tower of `ϖ₀ ^ e` (`tr j₀ k = ϖ k ^ e`, which is what the nodes `DEN`/`ROOTS` of the M5c
proof produce), then the tilted generator at `j₀` is exactly `(ϖ♭) ^ e`.  This is the hypothesis
`t j₀ = T ^ e` of `DSMap.Mix2.area_M5b` for `T := tiltVarpi Q`. -/
theorem tiltGens_j₀_eq_tiltVarpi_pow (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k)
    (j₀ : ι) (e : ℕ) (hcanon : ∀ k, tr j₀ k = Q.ϖ k ^ e) :
    tiltGens t tr htr0 htr j₀ = tiltVarpi Q ^ e :=
  tilt_ext fun n => by
    rw [coeff_tiltGens, hcanon n]
    simp only [map_pow, coeff_tiltVarpi]

end TiltedDatum

end Work.DSM5c
