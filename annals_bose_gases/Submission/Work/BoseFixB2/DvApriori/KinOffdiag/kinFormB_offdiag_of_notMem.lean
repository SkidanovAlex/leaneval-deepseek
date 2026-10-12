import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Qfree_fibre_eq
import Submission.Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq
import Submission.Work.BoseFixB2.DvApriori.jointProj_aP_eq_self
import Submission.Work.BoseFixB2.Polar.boxFormB_smul
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseFixB2.Polar.polB_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.KinOffdiag.kinFormB_offdiag_of_notMem`

The slot-`a` summand of the box-restricted kinetic word `kinFormB` is **off-diagonal
diagonal in the joint sectors** of a slot `a` that lies outside one of the two sector sets:

    ∫_{abox n ℓ} θ₀(x_a)·[fsT(fibre_a(E_SΦ + E_TΦ)) − fsT(fibre_a(E_SΦ − E_TΦ))] = 0
      whenever  a ∉ S  or  a ∉ T.

## The mechanism

`fsT ℓ d s εT b u` (FS `eq:DefT`) reads its one-body state only through the box mean-free
projection `Q_uψ` (`Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq`).  The joint sector
projection `E_U = ∏_{i∈U}Q_i ∏_{i∉U}P_i` applies the slot mean `P_a` at slot `a` as soon
as `a ∉ U`, so its slot-`a` fibre is **box-mean-free**:

    Qfree ℓ 0 (fibre_a(E_UΦ)(x)) = fibre_a(Q_a E_UΦ)(x) = 0      (a ∉ U),

(`Qfree_fibre_eq` + `jointProj_aP_eq_self`, which says `P_a E_UΦ = E_UΦ`, i.e.
`Q_a E_UΦ = 0`).  Since on the box mean-free part the word is `2`-homogeneous, the
polarisation `fsT(p+q) − fsT(p−q)` of a mean-free state `p` against anything vanishes;
that is `fsT_add_sub_eq_of_Qfree_eq_zero` below.  The integrand is therefore *pointwise*
zero, and the integral of the zero function is zero (no integrability input is needed).
-/

namespace Work.BoseFixB2.DvApriori.KinOffdiag

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Elementary fibre facts -/

/-- `z ↦ Function.update x j z` is continuous in `z` (the other coordinates are frozen). -/
lemma continuous_update_fin {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => Function.update x j z := by
  have h2 : Continuous fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 j p.2 := continuous_update j
  exact h2.comp (continuous_const.prodMk continuous_id)

/-- The slot-`j` fibre is additive in the state. -/
lemma fibre_add_fun {n : ℕ} (j : Fin n) (Ψ₁ Ψ₂ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    (Work.BoseKinLoc.fibre n j (fun y => Ψ₁ y + Ψ₂ y) x)
      = fun z => Work.BoseKinLoc.fibre n j Ψ₁ x z + Work.BoseKinLoc.fibre n j Ψ₂ x z := rfl

/-- The slot-`j` fibre is subtractive in the state. -/
lemma fibre_sub_fun {n : ℕ} (j : Fin n) (Ψ₁ Ψ₂ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    (Work.BoseKinLoc.fibre n j (fun y => Ψ₁ y - Ψ₂ y) x)
      = fun z => Work.BoseKinLoc.fibre n j Ψ₁ x z - Work.BoseKinLoc.fibre n j Ψ₂ x z := rfl

/-! ## 2. The polarised word of a mean-free state -/

/-- **Polarised vanishing.**  If the box-mean-free part of `p` (or of `q`) vanishes, then the
one-body word `fsT ℓ d s εT b 0` cannot distinguish the functions `p + q` and `p − q`.

Both sides are then equal to `fsT` of the *non-degenerate* argument: `Qfree` is additive and
subtractive in the state (`Qfree_add`, `Qfree_sub`), so
`Qfree (p+q) = Qfree p + Qfree q = Qfree q` and `Qfree (p−q) = Qfree p − Qfree q = −Qfree q`,
while `fsT` is even (`fsT_neg`, i.e. the word is `2`-homogeneous) and reads its state only
through `Qfree` (`fsT_congr_of_Qfree_eq`). -/
theorem fsT_add_sub_eq_of_Qfree_eq_zero {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {p q : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hpq : Work.BoseKinLoc.Qfree ℓ 0 p = (fun _ => (0 : ℝ)) ∨
      Work.BoseKinLoc.Qfree ℓ 0 q = (fun _ => (0 : ℝ)))
    (hpc : Continuous p) (hqc : Continuous q) :
    Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z => p z + q z)
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (fun z => p z - q z) := by
  rcases hpq with hp | hq
  · -- `Qfree p = 0`: both sides equal `fsT q`
    have h1 : Work.BoseKinLoc.Qfree ℓ 0 (fun z => p z + q z) = Work.BoseKinLoc.Qfree ℓ 0 q := by
      rw [Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ 0 hpc hqc]
      funext z
      rw [congrFun hp z, zero_add]
    have h2 : Work.BoseKinLoc.Qfree ℓ 0 (fun z => p z - q z)
        = Work.BoseKinLoc.Qfree ℓ 0 (fun z => -(q z)) := by
      rw [Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ 0 hpc hqc,
        Work.BoseFixB2.Polar.PolB.Qfree_neg_fun ℓ 0 q]
      funext z
      rw [congrFun hp z, zero_sub]
    rw [Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq h1,
      Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq h2,
      Work.BoseFixB2.Polar.PolB.fsT_neg ℓ d s εT b 0 q]
  · -- `Qfree q = 0`: both sides equal `fsT p`
    have h1 : Work.BoseKinLoc.Qfree ℓ 0 (fun z => p z + q z) = Work.BoseKinLoc.Qfree ℓ 0 p := by
      rw [Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ 0 hpc hqc]
      funext z
      rw [congrFun hq z, add_zero]
    have h2 : Work.BoseKinLoc.Qfree ℓ 0 (fun z => p z - q z) = Work.BoseKinLoc.Qfree ℓ 0 p := by
      rw [Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ 0 hpc hqc]
      funext z
      rw [congrFun hq z, sub_zero]
    rw [Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq h1,
      Work.BoseFixB2.DvApriori.fsT_congr_of_Qfree_eq h2]

/-! ## 3. The main theorem -/

theorem kinFormB_offdiag_of_notMem {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (a : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (ha : (a : ℕ) ∉ S ∨ (a : ℕ) ∉ T) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  have hΨS : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hΨT : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ T Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  -- the integrand vanishes pointwise
  have hzero : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.indU ℓ 0 (x a) *
        (Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
         - Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) = 0 := by
    intro x
    have hcontS : Continuous (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ) x) :=
      hΨS.continuous.comp (continuous_update_fin a x)
    have hcontT : Continuous (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ T Φ) x) :=
      hΨT.continuous.comp (continuous_update_fin a x)
    -- the slot-`a` fibre of a sector omitting `a` is box-mean-free
    have hmf : ∀ U : Finset ℕ, (a : ℕ) ∉ U →
        Work.BoseKinLoc.Qfree ℓ 0
            (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ U Φ) x)
          = (fun _ => (0 : ℝ)) := by
      intro U hU
      have hUdiff : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ U Φ) :=
        Work.BoseFixB2.Sector.jointProj_contDiff hℓ U hΦ
      have hself : Submission.BoseGases.aP ℓ a (Work.BoseFixB2.jointProj ℓ U Φ)
          = Work.BoseFixB2.jointProj ℓ U Φ :=
        Work.BoseFixB2.DvApriori.jointProj_aP_eq_self hℓ hU a.isLt hΦ
      have haQ : Submission.BoseGases.aQ ℓ a (Work.BoseFixB2.jointProj ℓ U Φ) = 0 := by
        funext y
        simp only [Submission.BoseGases.aQ, hself, Pi.zero_apply, sub_self]
      rw [Work.BoseFixB2.DvApriori.Qfree_fibre_eq hℓ a hUdiff x, haQ]
      rfl
    have hpq : Work.BoseKinLoc.Qfree ℓ 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ) x)
            = (fun _ => (0 : ℝ))
        ∨ Work.BoseKinLoc.Qfree ℓ 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ T Φ) x)
            = (fun _ => (0 : ℝ)) := by
      rcases ha with haS | haT
      · exact Or.inl (hmf S haS)
      · exact Or.inr (hmf T haT)
    -- rewrite the two fibres as the pointwise sum and difference
    have hsum : Work.BoseKinLoc.fibre n a
        (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x
        = fun z => (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ) x) z
            + (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ T Φ) x) z := by
      funext z
      simp only [Work.BoseKinLoc.fibre, Pi.add_apply]
    have hsub : Work.BoseKinLoc.fibre n a
        (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x
        = fun z => (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ) x) z
            - (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ T Φ) x) z := by
      funext z
      simp only [Work.BoseKinLoc.fibre, Pi.sub_apply]
    have key := fsT_add_sub_eq_of_Qfree_eq_zero (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
      (p := Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ) x)
      (q := Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ T Φ) x) hℓ hpq hcontS hcontT
    rw [hsum, hsub, key, sub_self, mul_zero]
  -- the integral of a pointwise vanishing integrand is zero
  have hz : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x a) *
      (Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
       - Work.BoseKinLoc.fsT ℓ d s εT b 0
          (Work.BoseKinLoc.fibre n a (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
      = fun _ => (0 : ℝ) := funext hzero
  rw [hz]
  simp

end Work.BoseFixB2.DvApriori.KinOffdiag
