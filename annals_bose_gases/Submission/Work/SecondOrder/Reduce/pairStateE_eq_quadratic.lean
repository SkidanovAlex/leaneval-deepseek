import ChallengeDeps
import Submission.Work.SecondOrder.Reduce.fderiv_pairState_kcDir
import Submission.Work.SecondOrder.Reduce.qLHSword_pairState_eq_doubleSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SecondOrder.Reduce

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The quadratic-form expansion of the pair-state energy

`pairStateE` is the `H_Λ(μ)`-energy word of the pair-excited (quasi-free) state
`pairState N ψ wt G`.  Since the state is a finite linear combination of its
matching components (`pairState_eq_sum_components`), its energy is the
corresponding *quadratic form* in those components: this file proves

    pairStateE N ℓ μ v h ψ wt G
      = Σ_{p ∈ pmatch N} Σ_{q ∈ pmatch N} wt(nPair p) · wt(nPair q) · pairBilin p q ,

i.e. the energy is the weighted double sum of the Bogoliubov bilinear form
`pairBilin` over pairs of partial matchings.  This is the formalised Wick
expansion of the quasi-free energy: the Gibbs/variational computation of the
second-order (Bogoliubov) energy then organises itself around the union graph of
`(p, q)`.

`pairStateE` splits into its kinetic word `kinWord` and its potential word
`qLHSword`; both are computed separately and are two instances of the same
elementary finite-Fubini computation.

* **Kinetic half** (`kinWord_pairState_eq_doubleSum`, below).  By
  `fderiv_pairState_kcDir` the directional derivative of the state along the
  corpus direction `kcDir N i k` is the weighted sum of the directional
  derivatives of the components; the integral of the square of that finite sum
  expands by `integral_sq_sum_finset`, and the sums over the directions `(i,k)`
  are moved past those over the matchings `(p,q)` by `sum_four_comm`.  This also
  uses the additivity of `fderiv` over a finite sum, i.e. genuinely the
  linearity of the kinetic word in the state.

* **Potential half** (`qLHSword_pairState_eq_doubleSum`, proved in the sibling
  module `Reduce.qLHSword_pairState_eq_doubleSum`): expanding
  `pairState = Σ_p wt(nPair p) · pairComp p` inside `qLHSword` and applying
  finite Fubini with the potential profile
  `−μ Σᵢ ∫w₁(xᵢ,·) + ½ Σ_{r ∈ pairSet N} w(x_{r.1},x_{r.2})` carried along.

* **Assembly.**  `doubleSum_mul_add` distributes the double sum over the
  kinetic and potential summands of `pairBilin`, and the two sides match
  definitionally.
-/

/-! ## The finite-sum expansion engine -/

/-- **Expansion of the integral of a squared finite sum.**  For a finite family
`f` of functions whose pairwise products are integrable,

    ∫ (Σ_p f_p)² = Σ_{p,q} ∫ f_p · f_q .

This is `Finset.sum_mul_sum` followed by finite Fubini (`integral_finsetSum`)
applied twice. -/
private lemma integral_sq_sum_finset {ι X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (f : ι → X → ℝ)
    (h : ∀ p ∈ s, ∀ q ∈ s, Integrable (fun x => f p x * f q x) μ) :
    ∫ x, (∑ p ∈ s, f p x)^2 ∂μ = ∑ p ∈ s, ∑ q ∈ s, ∫ x, f p x * f q x ∂μ := by
  have h1 : ∀ x, (∑ p ∈ s, f p x)^2 = ∑ p ∈ s, ∑ q ∈ s, f p x * f q x := by
    intro x; rw [sq, Finset.sum_mul_sum]
  rw [funext h1]
  rw [integral_finsetSum s (f := fun p => fun x => ∑ q ∈ s, f p x * f q x)
        (fun p hp => integrable_finsetSum s (fun q hq => h p hp q hq))]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [integral_finsetSum s (f := fun q => fun x => f p x * f q x) (fun q hq => h p hp q hq)]

/-- **Reordering a sum over four finite index sets.**  Swapping the block
`(a, b)` past the block `(c, d)` in a fourfold finite sum — the bookkeeping that
turns `Σᵢ Σₖ Σ_p Σ_q` into `Σ_p Σ_q Σᵢ Σₖ` (the directions `(i,k)` are summed
last in the quadratic form, the partial matchings `(p,q)` first). -/
private lemma sum_four_comm {ι κ ρ σ : Type*} [DecidableEq ι] [DecidableEq κ]
    [DecidableEq ρ] [DecidableEq σ] (s₁ : Finset ι) (s₂ : Finset κ) (s₃ : Finset ρ)
    (s₄ : Finset σ) (f : ι → κ → ρ → σ → ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d)
      = ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d := by
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ s₁) => (Finset.sum_comm (s := s₂) (t := s₃)
    (f := fun b c => ∑ d ∈ s₄, f a b c d)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ =>
    (Finset.sum_comm (s := s₂) (t := s₄) (f := fun b d => f a b c d))))]
  rw [Finset.sum_comm (s := s₁) (t := s₃) (f := fun a c => ∑ d ∈ s₄, ∑ b ∈ s₂, f a b c d)]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm (s := s₁) (t := s₄)
    (f := fun a d => ∑ b ∈ s₂, f a b c d))

/-- **Distributing the double sum of a product with a sum.**  For any finite
index set and coefficients `a, b, c`,

    Σ_{p,q} a_{pq} (b_{pq} + c_{pq}) = Σ_{p,q} a_{pq} b_{pq} + Σ_{p,q} a_{pq} c_{pq} ,

the linearity that splits the quadratic form into its kinetic and potential
halves. -/
private lemma doubleSum_mul_add {ι₁ : Type*} [DecidableEq ι₁] (s : Finset ι₁)
    (a b c : ι₁ → ι₁ → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, a p q * (b p q + c p q))
      = (∑ p ∈ s, ∑ q ∈ s, a p q * b p q) + (∑ p ∈ s, ∑ q ∈ s, a p q * c p q) := by
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
    mul_add (a p q) (b p q) (c p q)))]
  simp only [Finset.sum_add_distrib]

/-! ## The kinetic half -/

/-- **The kinetic word of the pair state is the weighted double sum of the
kinetic pairings of its components.**  Using
`fderiv_pairState_kcDir`, the directional derivative of the state is the
weighted sum of the directional derivatives of the components; the square of
that finite sum expands by `integral_sq_sum_finset`, and the sums over the
corpus directions `(i,k)` are moved past the sums over the matchings `(p,q)`
by `sum_four_comm`. -/
private theorem kinWord_pairState_eq_doubleSum {N : ℕ} {ℓ : ℝ} {psi : ℝ³ → ℝ}
    {wt : ℕ → ℝ} {G : ℝ³ → ℝ³ → ℝ}
    (hpsi : ContDiff ℝ 1 psi)
    (hG : ContDiff ℝ 1 (fun p : ℝ³ × ℝ³ => G p.1 p.2))
    (hkin : ∀ p ∈ Work.SecondOrder.pmatch N, ∀ q ∈ Work.SecondOrder.pmatch N,
      ∀ i : Fin N, ∀ k : Fin 3,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        fderiv ℝ (Work.SecondOrder.pairComp N psi G p) x (Submission.BoseGases.kcDir N i k)
          * fderiv ℝ (Work.SecondOrder.pairComp N psi G q) x
              (Submission.BoseGases.kcDir N i k))
        (Submission.BoseGases.abox N ℓ)) :
    kinWord N ℓ (pairState N psi wt G)
      = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N, wt (nPair p) * wt (nPair q) *
          (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N ℓ,
            fderiv ℝ (pairComp N psi G p) x (kcDir N i k)
              * fderiv ℝ (pairComp N psi G q) x (kcDir N i k)) := by
  have hz : ∀ (i : Fin N) (k : Fin 3),
      (∫ x in abox N ℓ, (fderiv ℝ (pairState N psi wt G) x (kcDir N i k)) ^ 2)
        = ∑ p ∈ pmatch N, ∑ q ∈ pmatch N, wt (nPair p) * wt (nPair q) *
            ∫ x in abox N ℓ, fderiv ℝ (pairComp N psi G p) x (kcDir N i k)
              * fderiv ℝ (pairComp N psi G q) x (kcDir N i k) := by
    intro i k
    have hder : ∀ x : Submission.BoseGases.X N,
        fderiv ℝ (pairState N psi wt G) x (kcDir N i k)
          = ∑ p ∈ pmatch N, wt (nPair p)
              * fderiv ℝ (pairComp N psi G p) x (kcDir N i k) :=
      fun x => fderiv_pairState_kcDir hpsi hG x i k
    have hint : ∀ p ∈ pmatch N, ∀ q ∈ pmatch N, Integrable (fun x : X N =>
        (wt (nPair p) * fderiv ℝ (pairComp N psi G p) x (kcDir N i k))
          * (wt (nPair q) * fderiv ℝ (pairComp N psi G q) x (kcDir N i k)))
        (volume.restrict (abox N ℓ)) := by
      intro p hp q hq
      refine ((hkin p hp q hq i k).const_mul (wt (nPair p) * wt (nPair q))).congr
        (Filter.Eventually.of_forall (fun x => by ring))
    simp only [hder]
    rw [integral_sq_sum_finset (volume.restrict (abox N ℓ)) (pmatch N)
      (fun p x => wt (nPair p) * fderiv ℝ (pairComp N psi G p) x (kcDir N i k)) hint]
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
    rw [show (fun x : Submission.BoseGases.X N =>
          (wt (nPair p) * fderiv ℝ (pairComp N psi G p) x (kcDir N i k))
            * (wt (nPair q) * fderiv ℝ (pairComp N psi G q) x (kcDir N i k)))
        = fun x : Submission.BoseGases.X N => (wt (nPair p) * wt (nPair q)) *
            (fderiv ℝ (pairComp N psi G p) x (kcDir N i k)
              * fderiv ℝ (pairComp N psi G q) x (kcDir N i k)) by
          funext x; ring]
    rw [integral_const_mul]
  unfold kinWord
  simp only [hz]
  rw [sum_four_comm (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin 3)) (pmatch N)
    (pmatch N) (fun i k p q => wt (nPair p) * wt (nPair q)
      * ∫ x in abox N ℓ, fderiv ℝ (pairComp N psi G p) x (kcDir N i k)
          * fderiv ℝ (pairComp N psi G q) x (kcDir N i k))]
  refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
  simp only [← Finset.mul_sum]

/-! ## The quadratic-form expansion -/

theorem pairStateE_eq_quadratic {N : ℕ} {ℓ μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧
      _root_.BoseGases.IsScatteringSolution w v)
    {psi : EuclideanSpace ℝ (Fin 3) → ℝ} {wt : ℕ → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hℓ : 0 < ℓ) (hpsi : ContDiff ℝ 1 psi)
    (hG : ContDiff ℝ 1 (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2))
    (hkin : ∀ p ∈ Work.SecondOrder.pmatch N, ∀ q ∈ Work.SecondOrder.pmatch N,
      ∀ i : Fin N, ∀ k : Fin 3,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        fderiv ℝ (Work.SecondOrder.pairComp N psi G p) x (Submission.BoseGases.kcDir N i k)
          * fderiv ℝ (Work.SecondOrder.pairComp N psi G q) x
              (Submission.BoseGases.kcDir N i k))
        (Submission.BoseGases.abox N ℓ))
    (hpot : ∀ p ∈ Work.SecondOrder.pmatch N, ∀ q ∈ Work.SecondOrder.pmatch N,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.SecondOrder.pairComp N psi G p x * Work.SecondOrder.pairComp N psi G q x *
          (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
            + (1 / 2) * (∑ r ∈ Submission.BoseGases.pairSet N,
                Submission.BoseGases.wPairC ℓ v (x r.1) (x r.2))))
        (Submission.BoseGases.abox N ℓ)) :
    Work.SecondOrder.pairStateE N ℓ μ v h psi wt G
      = ∑ p ∈ Work.SecondOrder.pmatch N, ∑ q ∈ Work.SecondOrder.pmatch N,
          wt (Work.SecondOrder.nPair p) * wt (Work.SecondOrder.nPair q)
            * Work.SecondOrder.pairBilin N ℓ μ v h psi G p q := by
  unfold Work.SecondOrder.pairStateE Work.SecondOrder.pairBilin
  rw [kinWord_pairState_eq_doubleSum hpsi hG hkin,
    qLHSword_pairState_eq_doubleSum h hpot,
    doubleSum_mul_add (Work.SecondOrder.pmatch N)]

end Work.SecondOrder.Reduce
