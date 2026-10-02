import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.Series
import Submission.Work.Cohomology.gradedComm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Chern relation from the Whitney formula: the series vocabulary

This module is the definitional base of
`Submission/Work/Whitney/chernRelation_of_whitneyFormula.lean`, whose target is the classical
statement that the Whitney sum formula *at the same total rank* implies the Grothendieck/Chern
relation over the projectivisation:

`Σ_{j=0}^{m} (-1)^j c_{m-j}(E) ζ^j = 0`   in `H^{2m}(P(E);ℤ)`.

The proof is the *telescoping* of the signed geometric series `1 - ζ t + ζ² t² - …` against the
recursion `x_k = c_k(Q) + ζ c_{k-1}(Q)` (the Whitney formula for the splitting
`π^*E ≅ ℓ ⊕ Q` of the splitting principle).  This file fixes the vocabulary:

* `zPow z` — the powers of a degree-`2` class as a graded series
  (`(i : ℕ) → Coh ℤ (2*i) B`), and `LerayHirsch.zetaPow Z = zPow (zeta Z)`;
* `geoSeriesOf z` — the **signed geometric series** `i ↦ (-1)^i z^i`, defined by the recursion
  `g₀ = 1`, `g_{i+1} = - gᵢ ⌣ z` (the **right** multiplication, which is the direction in which
  `zPow`/`zetaPow` recurse);
* `twoTermSeries z` — the series `1 + z t`, i.e. `i ↦ (1 if i = 0, z if i = 1, 0 else)`, the Chern
  series of a complex line bundle (`chernSeries ℓ = twoTermSeries ζ`);
* the bilinearity of the graded product `Work.Whitney.cupChern` (`add` and `neg` in each variable)
  and its **commutativity in even degrees** (`cupChern_comm`), the algebraic inputs of the
  telescoping.
-/

namespace Work.Whitney.ChernRel

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Powers of a degree-`2` class, and the signed geometric series -/

/-- **The powers of a degree-`2` class `z`**, as a graded series: `zPow z 0 = 1` and
`zPow z (i+1) = z^i ⌣ z`.  This is `Work.LerayHirsch.zetaPow` with the class `ζ` generalised to an
arbitrary `z` (needed to state the telescoping identity for the Chern series of an arbitrary
bundle). -/
noncomputable def zPow (z : Coh ℤ 2 B) : (i : ℕ) → Coh ℤ (2 * i) B
  | 0 => cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
  | i + 1 => Work.Whitney.cupChern i 1 (zPow z i) z

theorem zPow_zero (z : Coh ℤ 2 B) :
    zPow z 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := cohTransport_rfl _

theorem zPow_succ (z : Coh ℤ 2 B) (i : ℕ) :
    zPow z (i + 1) = Work.Whitney.cupChern i 1 (zPow z i) z := rfl

/-- `ζ^i` is `zPow` of `ζ`. -/
theorem zetaPow_eq_zPow {m : ℕ} {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.LerayHirsch.zetaPow Z = zPow (Work.LerayHirsch.zeta Z) := by
  funext i
  induction i with
  | zero =>
    rw [Work.LerayHirsch.zetaPow_zero, zPow_zero]
    exact cohTransport_rfl _
  | succ i ih => rw [Work.LerayHirsch.zetaPow_succ, zPow_succ, ih]

/-- **The signed geometric series** `i ↦ (-1)^i z^i` of a degree-`2` class, defined by the
recursion `g₀ = 1`, `g_{i+1} = - gᵢ ⌣ z`.  Its convolution inverse is `1 + z t`
(`twoTermSeries z`). -/
noncomputable def geoSeriesOf (z : Coh ℤ 2 B) : (i : ℕ) → Coh ℤ (2 * i) B
  | 0 => cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
  | i + 1 => - Work.Whitney.cupChern i 1 (geoSeriesOf z i) z

theorem geoSeriesOf_zero (z : Coh ℤ 2 B) :
    geoSeriesOf z 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := cohTransport_rfl _

theorem geoSeriesOf_succ (z : Coh ℤ 2 B) (i : ℕ) :
    geoSeriesOf z (i + 1) = - Work.Whitney.cupChern i 1 (geoSeriesOf z i) z := rfl

/-! ## The two-term series `1 + z t` -/

/-- **The two-term series `1 + z t`**: `0 ↦ 1`, `1 ↦ z`, `i ↦ 0` for `i ≥ 2`.  It is the Chern
series of a complex line bundle. -/
noncomputable def twoTermSeries (z : Coh ℤ 2 B) : (i : ℕ) → Coh ℤ (2 * i) B
  | 0 => cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))
  | 1 => cohTransport (rfl : 2 = 2 * 1) z
  | _ + 2 => 0

theorem twoTermSeries_zero (z : Coh ℤ 2 B) :
    twoTermSeries z 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := cohTransport_rfl _

theorem twoTermSeries_one (z : Coh ℤ 2 B) : twoTermSeries z 1 = z := cohTransport_rfl _

theorem twoTermSeries_of_two_le (z : Coh ℤ 2 B) {i : ℕ} (h : 2 ≤ i) :
    twoTermSeries z i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rfl

/-! ## Bilinearity of the graded product -/

/-- The degree cast is the identity when the two degrees are equal. -/
theorem cohTransport_self {n : ℕ} (h : n = n) (x : Coh ℤ n B) : cohTransport h x = x :=
  (Work.LerayHirsch.cohTransport_congr_proof h rfl).trans (Work.Thom.cohTransport_rfl x)

theorem cupChern_add_left (a b : ℕ) (x x' : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b (x + x') y
      = Work.Whitney.cupChern a b x y + Work.Whitney.cupChern a b x' y := by
  have key := Work.Cohomology.cupH'_add_left ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x x' y
  exact (congrArg (fun t => Work.Thom.cohTransport (Nat.mul_add 2 a b).symm t) key).trans
    (map_add (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm) _ _)

theorem cupChern_add_right (a b : ℕ) (x : Coh ℤ (2 * a) B) (y y' : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b x (y + y')
      = Work.Whitney.cupChern a b x y + Work.Whitney.cupChern a b x y' := by
  have key := Work.Cohomology.cupH'_add_right ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y y'
  exact (congrArg (fun t => Work.Thom.cohTransport (Nat.mul_add 2 a b).symm t) key).trans
    (map_add (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm) _ _)

theorem cupChern_neg_left (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b (-x) y = -Work.Whitney.cupChern a b x y := by
  have key : (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) (-x) y
      = - (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x y := by
    rw [show (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) (-x)
        = -(Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x from map_neg _ x]
    exact LinearMap.neg_apply _ _
  exact (congrArg (fun t => Work.Thom.cohTransport (Nat.mul_add 2 a b).symm t) key).trans
    (map_neg (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm) _)

theorem cupChern_neg_right (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b x (-y) = -Work.Whitney.cupChern a b x y := by
  have key : (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x (-y)
      = - (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x y :=
    map_neg ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x) y
  exact (congrArg (fun t => Work.Thom.cohTransport (Nat.mul_add 2 a b).symm t) key).trans
    (map_neg (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm) _)

/-- **Commutativity of the graded product in even degrees** (the sign `(-1)^{4ab} = 1`). -/
theorem cupChern_comm (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b x y
      = cohTransport (by omega : 2 * (b + a) = 2 * (a + b)) (Work.Whitney.cupChern b a y x) := by
  have h2 : (-1 : ℤ) ^ ((2 * a) * (2 * b)) = 1 := by
    rw [show (2 * a) * (2 * b) = 2 * (2 * (a * b)) by ring]
    exact Even.neg_one_pow ⟨2 * (a * b), by ring⟩
  have hg := Work.Cohomology.gradedComm ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y
  rw [h2] at hg
  simp only [one_smul] at hg
  set U := (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x y with hUdef
  set V := (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a)) y x with hVdef
  have hU : U = cohTransport ((Nat.add_comm (2 * a) (2 * b)).symm) V := by
    have h1 : cohTransport (Nat.add_comm (2 * a) (2 * b)) U = V := by
      rw [← Work.LerayHirsch.eqRec_eq_cohTransport]; exact hg
    calc U = cohTransport ((Nat.add_comm (2 * a) (2 * b)).trans
            (Nat.add_comm (2 * a) (2 * b)).symm) U := (cohTransport_self _ U).symm
      _ = cohTransport ((Nat.add_comm (2 * a) (2 * b)).symm)
            (cohTransport (Nat.add_comm (2 * a) (2 * b)) U) :=
          (Work.Whitney.cohTransport_trans _ _ U).symm
      _ = cohTransport ((Nat.add_comm (2 * a) (2 * b)).symm) V := by rw [h1]
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def, show
    (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b)) x y = U from rfl,
    show (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * a)) y x = V from rfl, hU]
  rw [Work.Whitney.cohTransport_trans, Work.Whitney.cohTransport_trans]

/-! ## `geoSeriesOf` as the signed series `(-1)^i z^i` -/

/-- **The geometric series is the signed power series**: `geoSeriesOf z i = (-1)^i z^i`.  This is
the form in which it is compared with the classes appearing in the Chern relation. -/
theorem geoSeriesOf_eq_smul (z : Coh ℤ 2 B) (i : ℕ) :
    geoSeriesOf z i = (-1 : ℤ) ^ i • zPow z i := by
  induction i with
  | zero =>
    rw [geoSeriesOf_zero, zPow_zero, show (-1 : ℤ) ^ 0 = (1 : ℤ) from rfl]
    exact (one_zsmul _).symm
  | succ i ih =>
    rw [geoSeriesOf_succ, ih, zPow_succ]
    rcases Nat.even_or_odd i with hEven | hOdd
    · rw [Even.neg_one_pow hEven, one_zsmul,
        show (-1 : ℤ) ^ (i + 1) = -1 from
          Odd.neg_one_pow (Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hEven)),
        neg_one_zsmul]
    · rw [Odd.neg_one_pow hOdd, neg_one_zsmul, cupChern_neg_left, neg_neg,
        show (-1 : ℤ) ^ (i + 1) = 1 from
          Even.neg_one_pow (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hOdd)),
        one_zsmul]

end

end Work.Whitney.ChernRel
