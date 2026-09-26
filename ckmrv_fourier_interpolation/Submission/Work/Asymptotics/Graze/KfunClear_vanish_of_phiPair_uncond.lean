/-
# Unconditional vanishing of the cleared kernel on the orbit of `φ`-annihilated elements

The conditional statement `Work.Asymptotics.KfunClear_vanish_of_phiPair` shows

  `KfunClear ℓ d (δ • z) z = 0`   whenever `j'(z) ≠ 0`

for every `δ ∈ SL(2,ℤ)` with `φ₊(δ) + φ₋(δ) = 0` (CKMRV (3.12)).  The hypothesis `j'(z) ≠ 0`
comes from the residue computation, which identifies the residue with
`AfunFun ℓ d (δz) z / j'(δz)`.

Here we remove that hypothesis.  The slice `z ↦ AfunFun ℓ d (δ • z) z` is *continuous* on `ℍ`
(it is the joint continuous function `AfunFun` composed with the continuous Möbius action),
and it vanishes on the dense set `{z | j'(z) ≠ 0}` (`exists_jprime_ne_zero_near`).  Hence it
vanishes identically (`isClosed_eq` + density), and `KfunClear = Δ(τ)Δ(z)^e · AfunFun` gives
the claim.
-/
import Mathlib
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.exists_jprime_ne_zero_near

namespace Work.Asymptotics.Graze

open UpperHalfPlane

theorem KfunClear_vanish_of_phiPair_uncond (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hδ : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
        + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0) :
    ∀ z : UpperHalfPlane, Work.Kernels.KfunClear ℓ d (δ • z) z = 0 := by
  intro z
  -- the Möbius action `w ↦ δ • w` is continuous
  have hsmul : Continuous (fun w : UpperHalfPlane => δ • w) := by
    simpa only [ModularGroup.sl_moeb] using continuous_const_smul (δ : GL (Fin 2) ℝ)
  have hpair : Continuous (fun w : UpperHalfPlane => (δ • w, w)) :=
    Continuous.prodMk hsmul continuous_id
  have hg : Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      Work.Asymptotics.AfunFun ℓ d p.1 p.2) := Work.Asymptotics.continuous_AfunFun ℓ d
  -- the slice `w ↦ AfunFun ℓ d (δ • w) w` is continuous
  have hcomp : Continuous ((fun p : UpperHalfPlane × UpperHalfPlane =>
      Work.Asymptotics.AfunFun ℓ d p.1 p.2) ∘ (fun w : UpperHalfPlane => (δ • w, w))) :=
    Continuous.comp hg hpair
  have hcont : Continuous (fun w : UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d (δ • w) w) := by
    have heq : ((fun p : UpperHalfPlane × UpperHalfPlane =>
        Work.Asymptotics.AfunFun ℓ d p.1 p.2) ∘ (fun w : UpperHalfPlane => (δ • w, w)))
        = (fun w : UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d (δ • w) w) := rfl
    rw [heq] at hcomp
    exact hcomp
  -- the slice vanishes wherever `j'` does not vanish
  have hzero : ∀ w : UpperHalfPlane, Work.Residues.jprime w ≠ 0 →
      Work.Asymptotics.AfunFun ℓ d (δ • w) w = 0 := by
    intro w hw
    have hk := Work.Asymptotics.KfunClear_vanish_of_phiPair ℓ d hd δ hδ w hw
    rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d (δ • w) w] at hk
    exact (mul_eq_zero.mp hk).resolve_left
      (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
        (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)))
  -- `{j' ≠ 0}` is dense
  have hdense : Dense {w : UpperHalfPlane | Work.Residues.jprime w ≠ 0} := by
    rw [Metric.dense_iff]
    intro w ε hε
    obtain ⟨w', hw', hj⟩ := Work.Asymptotics.exists_jprime_ne_zero_near w ε hε
    exact ⟨w', ⟨by rw [Metric.mem_ball, dist_comm]; exact hw', hj⟩⟩
  -- hence the slice vanishes identically
  have hall : ∀ w : UpperHalfPlane, Work.Asymptotics.AfunFun ℓ d (δ • w) w = 0 := by
    intro w
    have hclosed : IsClosed
        {w : UpperHalfPlane | Work.Asymptotics.AfunFun ℓ d (δ • w) w = 0} :=
      isClosed_eq hcont continuous_const
    have hsub : {w : UpperHalfPlane | Work.Residues.jprime w ≠ 0} ⊆
        {w : UpperHalfPlane | Work.Asymptotics.AfunFun ℓ d (δ • w) w = 0} := hzero
    have hsub' : (Set.univ : Set UpperHalfPlane) ⊆
        {w : UpperHalfPlane | Work.Asymptotics.AfunFun ℓ d (δ • w) w = 0} := by
      rw [← hdense.closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    exact hsub' (Set.mem_univ w)
  rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d (δ • z) z, hall z, mul_zero]

end Work.Asymptotics.Graze
