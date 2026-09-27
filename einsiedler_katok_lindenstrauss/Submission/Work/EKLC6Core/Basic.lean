import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLComp.ent_id

/-!
# `EKLC6Core.Basic` — vocabulary for component C6 (entropy ↔ leafwise measures, Pisa §7)

Component C6 of the EKL contract is

`0 < ent μ (aDiag t ·) ↔ ∃ i j, t i < t j ∧ ¬ CrossSection μ (Uij ·)`

(EKL (7), Pisa Theorems 7.6/7.7 and Corollary 7.7, together with Pisa 6.23 and the product
structure of leaf-wise measures, Pisa 8.5/8.8).

Pisa's proof of Theorem 7.6 introduces the *entropy contribution*

`D_μ(a,U)(x) = lim_n log μ_x^U (a^{-n} B₁^U a^n) / n`

of an `a`-normalised closed subgroup `U ≤ G⁻` of the stable horospherical subgroup of `a`.
This module fixes the vocabulary for that computation, in the normalisation of the frozen
contract (`ν x (Box1 U) = 1`):

* `conjBy t S` — the image of `S` under conjugation by `aDiag t`;
* `conjBox U t` — `aDiag t · Box1 U · (aDiag t)⁻¹`, i.e. the box of "radius `e^{t i - t j}`"
  (for `U = Uij`, `t i < t j` this is the contracted box `u_ij([-λ,λ])`, `λ = e^{t i - t j} < 1`);
* `ACovariant ν X''` — EKL (4)/Pisa 7.16: the `A`-covariance of a leaf-wise system, on `X''`
  (this is *not* a field of `IsLeafwise`; it is proved in `P_Leafwise`'s second half);
* `growthFun U ν t x = -log (ν x (conjBox U t))` — the pointwise information whose Birkhoff
  average along `a^{-1}` is the entropy contribution `D_μ(a,U)`.

The main identity of this module (`Work.EKLC6Core.covariant_mul`) is Pisa 7.16 + 7.18 in
normalised form: the boxes multiply along the orbit, so that the limit defining `D_μ(a,U)`
is a Birkhoff average.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Conjugation by the diagonal flow -/

/-- The image of a set of matrices under conjugation by `aDiag t`. -/
def conjBy (t : Fin 3 → ℝ) (S : Set SL3) : Set SL3 :=
  (fun g => aDiag t * g * (aDiag t)⁻¹) '' S

/-- The image of the normalising box `Box1 U` under conjugation by `aDiag t`: for `U = Uij` and
`t i < t j` this is the contracted box (`u_ij([-λ,λ])`, `λ = e^{t i - t j} < 1`) in which the
entropy contribution is measured (Pisa 7.16, 7.34). -/
def conjBox (U : Subgroup SL3) (t : Fin 3 → ℝ) : Set SL3 := conjBy t (Box1 U)

@[simp] theorem conjBy_zero (S : Set SL3) : conjBy 0 S = S := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [aDiag_zero] using hh
  · intro hg
    exact ⟨g, hg, by simp [aDiag_zero]⟩

@[simp] theorem conjBox_zero (U : Subgroup SL3) : conjBox U 0 = Box1 U := conjBy_zero _

/-- Conjugation is an action of the additive group of exponent vectors. -/
theorem conjBy_add (s t : Fin 3 → ℝ) (S : Set SL3) :
    conjBy (s + t) S = conjBy s (conjBy t S) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨aDiag t * h * (aDiag t)⁻¹, ⟨h, hh, rfl⟩, ?_⟩
    show aDiag s * (aDiag t * h * (aDiag t)⁻¹) * (aDiag s)⁻¹ =
      aDiag (s + t) * h * (aDiag (s + t))⁻¹
    rw [← aDiag_add, mul_inv_rev]
    group
  · rintro ⟨h, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    show aDiag (s + t) * k * (aDiag (s + t))⁻¹ =
      aDiag s * (aDiag t * k * (aDiag t)⁻¹) * (aDiag s)⁻¹
    rw [← aDiag_add, mul_inv_rev]
    group

theorem conjBox_add (U : Subgroup SL3) (s t : Fin 3 → ℝ) :
    conjBox U (s + t) = conjBy s (conjBox U t) := conjBy_add s t _

/-- Conjugation by `aDiag t` inverts that by `aDiag (-t)`. -/
theorem conjBy_neg_conjBy (t : Fin 3 → ℝ) (S : Set SL3) :
    conjBy (-t) (conjBy t S) = S := by
  rw [← conjBy_add, neg_add_cancel, conjBy_zero]

/-! ## The `A`-covariance of a leaf-wise system -/

/-- **EKL (4) / Pisa 7.16**: the `A`-covariance of a leaf-wise system on the conull set `X''`.
This is the second-half hypothesis of `P_Leafwise` (field `U7`); it is *not* a field of
`IsLeafwise`. -/
def ACovariant (ν : X3 → Measure SL3) (X'' : Set X3) : Prop :=
  ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag t • x) = c • (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹)

/-! ## σ-algebra conditional entropy

Pisa 7.6 compares the entropy `h_μ(a)` with `H_μ(A | a^{-1}A)`, where `A` is a countably
generated σ-algebra whose atoms are `U`-plaques.  The frozen contract only defines the
conditional entropy of a *finite partition* (`Hcond`); here is the σ-algebra version used by
the C6 argument, defined as the supremum over the finite sub-partitions of `A` (which for
countably generated `A` is the usual information-theoretic conditional entropy, by the
martingale convergence theorem). -/

/-- `H_μ(A | A')`, defined as the supremum (in `ℝ≥0∞`) of the entropies `H_μ(P | A')` of the
finite partitions `P` whose σ-algebra is contained in `A`.  (For countably generated `A` this is
`ofReal` of the usual conditional entropy `∫ -log μ_x^{A'}([x]_A) dμ`.) -/
def HcondSig {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    (A A' : MeasurableSpace X) : ℝ≥0∞ :=
  ⨆ (P : {P : @FinPart X mX // @partSigma X mX P ≤ A}), ENNReal.ofReal (@Hcond X mX μ P.1 A')

/-! ## The entropy contribution -/

/-- The pointwise "information" whose Birkhoff average along the `a^{-1}`-orbit is the entropy
contribution `D_μ(a,U)` of Pisa 7.6 (normalised form of Pisa 7.18): the negative logarithm of
the mass of the contracted box. -/
def growthFun (U : Subgroup SL3) (ν : X3 → Measure SL3) (t : Fin 3 → ℝ) (x : X3) : ℝ :=
  - Real.log ((ν x (conjBox U t)).toReal)

/-! ## The contracted horospherical subgroup of `aDiag t` -/

/-- The subgroup generated by the root groups contracted by `aDiag t` (the stable horospherical
subgroup `G⁻(t)` of Pisa 7.3): the join of the `Uij` with `t i < t j`. -/
def Uminus (t : Fin 3 → ℝ) : Subgroup SL3 :=
  ⨆ (i : Fin 3) (j : Fin 3) (hij : i ≠ j) (hlt : t i < t j), Uij hij

/-! ## The degenerate case `Uminus t = ⊥`

`Uminus t` is the join of the root groups `Uij` with `t i < t j` (`Work.EKLC6Core.Uminus`).  When
it is trivial there is no contracted root group, i.e. `t` is constant, i.e. `aDiag t = 1`; the map
`x ↦ aDiag t • x` is then the identity and its entropy vanishes.  These are the three lemmas used
by `ent_le_growth_of_aerg` (and its `_along` variants) to dispose of the degenerate case.
-/

/-- No root group `Uij` is trivial. -/
theorem Uij_ne_bot {i j : Fin 3} (hij : i ≠ j) : (Uij hij : Subgroup SL3) ≠ ⊥ := by
  intro hbot
  have hmem : uij hij 1 ∈ (Uij hij : Set SL3) := by
    rw [Work.EKLContract.Lemmas.Uij_range]
    exact ⟨1, rfl⟩
  rw [show ((Uij hij : Subgroup SL3) : Set SL3) = ((⊥ : Subgroup SL3) : Set SL3) from by
        rw [hbot]] at hmem
  have h1 : uij hij 1 = (1 : SL3) := Subgroup.mem_bot.mp hmem
  have happ := Work.EKLContract.Lemmas.horoUij_toMat hij 1
  have hthis : toMat (uij hij 1) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    rw [h1, toMat_one]
  rw [happ] at hthis
  simp [Matrix.add_apply, hij] at hthis

/-- `Uminus t = ⊥` forces `t` to be constant. -/
theorem constant_of_uminus_eq_bot (t : Fin 3 → ℝ) (h : Uminus t = ⊥) :
    ∀ i j : Fin 3, t i = t j := by
  have key : ∀ {i j : Fin 3}, t i < t j → False := by
    intro i j hlt
    have hij : i ≠ j := fun hh => by rw [hh] at hlt; exact lt_irrefl _ hlt
    have hsub : (Uij hij : Subgroup SL3) ≤ Uminus t := by
      intro g hg
      rw [Uminus]
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
        (Subgroup.mem_iSup_of_mem hij (Subgroup.mem_iSup_of_mem hlt hg)))
    rw [h] at hsub
    exact Uij_ne_bot hij (le_bot_iff.mp hsub)
  intro i j
  rcases lt_trichotomy (t i) (t j) with hlt | heq | hgt
  · exact (key hlt).elim
  · exact heq
  · exact (key hgt).elim

/-- A constant `t` gives `aDiag t = 1`. -/
theorem aDiag_eq_one_of_constant (t : Fin 3 → ℝ) (ht : ∀ i j : Fin 3, t i = t j) :
    aDiag t = 1 := by
  apply ext_toMat
  rw [toMat_aDiag, toMat_one]
  congr 1
  ext i
  have hsum : (∑ j, t j) = 3 * t i := by
    rw [Finset.sum_congr rfl (fun j _ => ht j i)]; simp
  rw [hsum]
  norm_num

/-- `Uminus t = ⊥` gives `aDiag t = 1`. -/
theorem aDiag_eq_one_of_uminus_eq_bot (t : Fin 3 → ℝ) (h : Uminus t = ⊥) :
    aDiag t = 1 :=
  aDiag_eq_one_of_constant t (constant_of_uminus_eq_bot t h)

/-- In the degenerate case `Uminus t = ⊥` the entropy of `aDiag t ·` vanishes. -/
theorem ent_aDiag_eq_zero_of_uminus_eq_bot {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ) (h : Uminus t = ⊥) :
    ent μ (fun x : X3 => aDiag t • x) = 0 := by
  have h1 : aDiag t = 1 := aDiag_eq_one_of_uminus_eq_bot t h
  have hfun : (fun x : X3 => aDiag t • x) = id := by
    funext x; rw [h1]; simp
  rw [hfun]
  exact Work.EKLComp.ent_id μ


end Work.EKLC6Core

end
