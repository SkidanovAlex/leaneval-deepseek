import Mathlib
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.kappa_span
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.Fund.kappa_one
import Submission.Work.KT.k0_basic

namespace Work.KT.ExtGen

noncomputable section

/-! ## `ℤ`-linearity of the Bott map in its second variable

`Fund.bottMap X μ b = μ (Fund.s X b) (Fund.beta X)`: the pull-back `Fund.s X` along the projection
`X × S² → X` is additive and `μ` is additive in its first variable, so `bottMap X μ` is additive;
its `ℤ`-homogeneity (with scalars of the free-abelian structure of `K₀`, which is all that
`Work.KT.kappa_span` produces) follows by induction over finite sums. -/

/-- Additivity of the Bott map in its second variable. -/
lemma bottMap_add (X : Type) [TopologicalSpace X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    (a b : K0 C(X, ℂ)) :
    Fund.bottMap X μ (a + b) = Fund.bottMap X μ a + Fund.bottMap X μ b := by
  simp only [Fund.bottMap, map_add, AddMonoidHom.add_apply]

/-- The Bott map sends `0` to `0`. -/
lemma bottMap_zero (X : Type) [TopologicalSpace X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) :
    Fund.bottMap X μ 0 = 0 := by
  simp only [Fund.bottMap, map_zero, AddMonoidHom.zero_apply]

/-- `ℤ`-homogeneity of the Bott map in its second variable. -/
lemma bottMap_zsmul (X : Type) [TopologicalSpace X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    (k : ℤ) (a : K0 C(X, ℂ)) :
    Fund.bottMap X μ (k • a) = k • Fund.bottMap X μ a := by
  simp only [Fund.bottMap, map_zsmul, AddMonoidHom.zsmul_apply]

/-- `ℤ`-linearity of the Bott map on finite linear combinations. -/
lemma bottMap_sum (X : Type) [TopologicalSpace X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    {ι : Type} [Fintype ι] (c : ι → ℤ) (bb : ι → K0 C(X, ℂ)) :
    Fund.bottMap X μ (∑ i, c i • bb i) = ∑ i, c i • Fund.bottMap X μ (bb i) := by
  classical
  have key : ∀ s : Finset ι,
      Fund.bottMap X μ (s.sum fun i => c i • bb i)
        = s.sum fun i => c i • Fund.bottMap X μ (bb i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, bottMap_zero X μ]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, bottMap_add X μ, ih,
          bottMap_zsmul X μ]
  simpa using key Finset.univ

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **Surjectivity half of the fundamental product, relative form (Hatcher VBKT Thm 2.2).**
With `M = K0 C(X × S2, ℂ)`, `A = K0 C(X, ℂ)`, `s = fst*`, `γ = snd*(cls hopfIdem)`, `β = γ - 1`,
the Bott map `bottMap X μ : A → M`, `b ↦ μ (s b) β`, hits every class killed by **both** disc
restrictions `Fund.pullUp X`, `Fund.pullDn X` (equivalently: by the base-point restriction
`Fund.r X`, since `ker r = ker pullUp = ker pullDn`; see `Work.KT.ExtGen.ker_r_subset_ker_pullDn`).

Proof: apply `Work.KT.kappa_span` (GEN) to obtain
`z = ∑ i, c i • (κ(u i) - κ(1))`; rewrite `Fund.kappa X (N i) 1` as `cls (Mat.one C(X × S2, ℂ) (N i))`
by `Fund.kappa_one`; apply `hD` to each summand (supplied by `EG.kappa_reduce` / `Fund.kappa_lin`
once those land); reassemble with the `ℤ`-linearity of `bottMap X μ` in its last variable
(`μ (s ·) β`, via `map_sum`, `map_zsmul`).

The hypothesis `hμ : IsK0Mul μ` is not used by the argument (only linearity in the last variable
is); it is kept because it is part of the intended context and is available at every call site. -/
theorem bottMap_surjective (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ)
    (hD : ∀ (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ),
      ∃ b : K0 C(X, ℂ),
        Work.KT.Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n)
          = Work.KT.Fund.bottMap X μ b) :
    ∀ z : K0 C(X × S2, ℂ), K0.map (Work.KT.Fund.pullUp X) z = 0 →
      K0.map (Work.KT.Fund.pullDn X) z = 0 →
      ∃ b : K0 C(X, ℂ), z = Work.KT.Fund.bottMap X μ b := by
  intro z h₁ h₂
  obtain ⟨m, N, u, c, hz⟩ := Work.KT.kappa_span X z h₁ h₂
  -- the individual `b`'s supplied by `hD`, one for each summand of `kappa_span`
  let bb : Fin m → K0 C(X, ℂ) := fun i => (hD (N i) (u i)).choose
  have hbb : ∀ i : Fin m,
      Fund.kappa X (N i) (u i) - cls (Mat.one C(X × S2, ℂ) (N i))
        = Fund.bottMap X μ (bb i) := fun i => (hD (N i) (u i)).choose_spec
  -- rewrite the trivial clutching classes `κ(1)` using `Fund.kappa_one`
  have hz' : z = ∑ i, c i •
      (Fund.kappa X (N i) (u i) - cls (Mat.one C(X × S2, ℂ) (N i))) := by
    rw [hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fund.kappa_one]
  refine ⟨∑ i, c i • bb i, ?_⟩
  rw [hz', bottMap_sum X μ c bb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbb i]

end

end Work.KT.ExtGen
