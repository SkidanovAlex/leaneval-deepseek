/-
# Reduction of the rigidity lemma to the one-function statement

CKMRV's `lem:noPsolutions` is applied to the *eigenfunctions* of the slash action of `S`
on the pair `(g, g̃)`.  This file performs that reduction, in the form used in Section 8 of
the paper:  from the single-function statement `Work.Rigidity.SingleRigidity` one recovers
the two-variable statement `Work.FE.HomogeneousRigidity`.

With `k = n/2` the two combinations

  `g + g̃`   and   `g − g̃`

are anti-invariant and invariant for `|_k S` respectively; both are killed by `(T − I)²`
and both inherit the decay bound.  Hence `SingleRigidity k (-1) c` kills the first and
`SingleRigidity k 1 c` the second, and `g`, `g̃` are recovered from them.

The `S`-invariance of the two combinations uses `(i/τ)^k = τ^{-k}`, i.e. `4 | k`, and the
fact that `S² = (STS)³` acts trivially at even weight; the algebraic content is the pair of
identities

  `(f + f̃) ∣[k] S = -(f + f̃)`,   `(f − f̃) ∣[k] S = f − f̃`,

proved below from the single relation `f(τ) + (i/τ)^k f̃(-1/τ) = 0`.

## Main results

* `Work.Rigidity.homogeneousRigidity_of_singleRigidity` : the reduction.
* `Work.Rigidity.slashFactor_eight`, `slashFactor_twentyfour` : the identification
  `slashFactor n τ = τ^{-n/2}` at the two weights.
* `Work.Rigidity.homogeneousRigidity_eight_of`, `homogeneousRigidity_twentyfour_of` :
  the two target theorems, conditional on the four single-function statements.
-/
import Mathlib
import Submission.Work.Rigidity.Basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-! ## The slash factor at the two weights -/

lemma slashFactor_eight (z : ℂ) : Work.FE.slashFactor 8 z = z ^ (-4 : ℤ) := by
  unfold Work.FE.slashFactor
  norm_num only [Nat.cast_ofNat, OfNat.ofNat]
  rw [Complex.cpow_ofNat, div_pow, Complex.I_pow_four, one_div, zpow_neg z 4]
  simp

/-- `(i/z)^12 = z^{-12}`: at `n = 24` the slash factor is the weight-`12` factor of
automorphy. -/
lemma slashFactor_twentyfour (z : ℂ) : Work.FE.slashFactor 24 z = z ^ (-12 : ℤ) := by
  unfold Work.FE.slashFactor
  norm_num only [Nat.cast_ofNat, OfNat.ofNat]
  rw [Complex.cpow_ofNat, div_pow,
    show Complex.I ^ (12 : ℕ) = 1 by
      rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, Complex.I_pow_four, one_pow],
    one_div, zpow_neg z 12]
  simp

/-! ## The reduction -/

/-- **The eigenfunction reduction, with an extra hypothesis `P` carried along.**

Suppose `(i/τ)^k = τ^{-k}` on the upper half plane, `k` is even, `P` is a class of functions
closed under `+` and `-`, and no nonzero `S`-eigenfunction of weight `k` and eigenvalue `±1`
in `P` with the strip decay exists.  Then a solution `(g, g̃)` of the homogeneous system whose
two components lie in `P` (in `τ`, for each fixed `x`) vanishes identically.

Instantiating `P := fun _ => True` gives `homogeneousRigidity_of_singleRigidity`;
instantiating `P := Work.Kernels.InP` gives the paper-faithful
`Work.Rigidity.homogeneousRigidityP_of_singleRigidityP`. -/
theorem homogeneousRigidity_of_eigen {n : ℕ} [NeZero n] {c : ℝ} {k : ℤ}
    (P : (ℍ → ℂ) → Prop)
    (hadd : ∀ {f g : ℍ → ℂ}, P f → P g → P (f + g))
    (hneg : ∀ {f : ℍ → ℂ}, P f → P (-f))
    (hsf : ∀ τ : ℍ, Work.FE.slashFactor n (τ : ℂ) = (τ : ℂ) ^ (-k))
    (hkeven : Even k)
    (hRneg : ∀ f : ℍ → ℂ, P f → MDiff f → AnnT2 f → SlashEigen k (-1 : ℂ) f →
      StripDecay c f → f = 0)
    (hRpos : ∀ f : ℍ → ℂ, P f → MDiff f → AnnT2 f → SlashEigen k (1 : ℂ) f →
      StripDecay c f → f = 0)
    (g gt : ℂ → Work.FE.E n → ℂ)
    (hPg : ∀ x : Work.FE.E n, P (fun s : ℍ => g (s : ℂ) x))
    (hPgt : ∀ x : Work.FE.E n, P (fun s : ℍ => gt (s : ℂ) x))
    (hg : ∀ x, DifferentiableOn ℂ (fun τ : ℂ => g τ x) {τ : ℂ | 0 < τ.im})
    (hgt : ∀ x, DifferentiableOn ℂ (fun τ : ℂ => gt τ x) {τ : ℂ | 0 < τ.im})
    (hT2g : ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0)
    (hT2gt : ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      gt (τ + 2) x - 2 * gt (τ + 1) x + gt τ x = 0)
    (hS : ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      g τ x + Work.FE.slashFactor n τ * gt (-1 / τ) x = 0)
    (hdecg : Work.FE.TendsToZeroInStrip n c g)
    (hdecgt : Work.FE.TendsToZeroInStrip n c gt) :
    ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im → g τ x = 0 ∧ gt τ x = 0 := by
  intro τ x hτ
  let f : ℍ → ℂ := fun s => g (s : ℂ) x
  let ft : ℍ → ℂ := fun s => gt (s : ℂ) x
  have hPf : P f := hPg x
  have hPft : P ft := hPgt x
  have hmf : MDiff f := mdifferentiable_of_differentiableOn (hg x)
  have hmft : MDiff ft := mdifferentiable_of_differentiableOn (hgt x)
  have hT2f : AnnT2 f := T2op_of_complex (fun s hs => hT2g s x hs)
  have hT2ft : AnnT2 ft := T2op_of_complex (fun s hs => hT2gt s x hs)
  have hdecf : StripDecay c f := stripDecay_of_tendsToZeroInStrip hdecg
  have hdecft : StripDecay c ft := stripDecay_of_tendsToZeroInStrip hdecgt
  -- the third functional equation, on `ℍ`
  have hSeq : ∀ s : ℍ, f s + (s : ℂ) ^ (-k) * ft (ModularGroup.S • s) = 0 := by
    intro s
    have h := hS (s : ℂ) x s.im_pos
    rw [hsf s] at h
    rw [neg_one_div] at h
    rw [← coe_S_smul s] at h
    exact h
  -- the same equation at `S • s`, using `S • (S • s) = s`
  have hSeq2 : ∀ s : ℍ, f (ModularGroup.S • s) + (s : ℂ) ^ k * ft s = 0 := by
    intro s
    have h := hSeq (ModularGroup.S • s)
    rw [S_smul_S_smul] at h
    rw [coe_S_smul, zpow_neg_inv (s : ℂ) hkeven] at h
    exact h
  have hAs : ∀ s : ℍ, (s : ℂ) ^ (-k) * (s : ℂ) ^ k = 1 := by
    intro s
    rw [← zpow_add₀ (coe_ne_zero s)]
    simp
  -- the anti-invariant combination
  have hfp : SlashEigen k (-1 : ℂ) (f + ft) := by
    intro s
    rw [Work.Kernels.slash_S_apply]
    simp only [Pi.add_apply]
    have h1 := hSeq s
    have h2 := hSeq2 s
    have e1 : (s : ℂ) ^ (-k) * ft (ModularGroup.S • s) = -f s := by
      linear_combination h1
    have e2a : f (ModularGroup.S • s) = -((s : ℂ) ^ k * ft s) := by
      linear_combination h2
    have e2b : (s : ℂ) ^ (-k) * f (ModularGroup.S • s) = -ft s := by
      rw [e2a, show (s : ℂ) ^ (-k) * -((s : ℂ) ^ k * ft s)
            = -((s : ℂ) ^ (-k) * (s : ℂ) ^ k) * ft s by ring, hAs s]
      ring
    calc (f (ModularGroup.S • s) + ft (ModularGroup.S • s)) * (s : ℂ) ^ (-k)
        = (s : ℂ) ^ (-k) * f (ModularGroup.S • s)
            + (s : ℂ) ^ (-k) * ft (ModularGroup.S • s) := by ring
      _ = -ft s + -f s := by rw [e2b, e1]
      _ = (-1 : ℂ) * (f s + ft s) := by ring
  -- the invariant combination
  have hfm : SlashEigen k (1 : ℂ) (f + -ft) := by
    intro s
    rw [Work.Kernels.slash_S_apply]
    simp only [Pi.add_apply, Pi.neg_apply]
    have h1 := hSeq s
    have h2 := hSeq2 s
    have e1 : (s : ℂ) ^ (-k) * ft (ModularGroup.S • s) = -f s := by
      linear_combination h1
    have e2a : f (ModularGroup.S • s) = -((s : ℂ) ^ k * ft s) := by
      linear_combination h2
    have e2b : (s : ℂ) ^ (-k) * f (ModularGroup.S • s) = -ft s := by
      rw [e2a, show (s : ℂ) ^ (-k) * -((s : ℂ) ^ k * ft s)
            = -((s : ℂ) ^ (-k) * (s : ℂ) ^ k) * ft s by ring, hAs s]
      ring
    calc (f (ModularGroup.S • s) + -ft (ModularGroup.S • s)) * (s : ℂ) ^ (-k)
        = (s : ℂ) ^ (-k) * f (ModularGroup.S • s)
            + (s : ℂ) ^ (-k) * (-ft (ModularGroup.S • s)) := by ring
      _ = -ft s + -((s : ℂ) ^ (-k) * ft (ModularGroup.S • s)) := by rw [e2b]; ring
      _ = -ft s + -(-f s) := by rw [e1]
      _ = (1 : ℂ) * (f s + -ft s) := by ring
  have hT2neg : Work.Kernels.T2op (-ft) = 0 := by rw [T2op_neg, hT2ft, neg_zero]
  have hT2fp : AnnT2 (f + ft) := Work.Kernels.T2op_add hT2f hT2ft
  have hT2fm : AnnT2 (f + -ft) := Work.Kernels.T2op_add hT2f hT2neg
  have hdecfp : StripDecay c (f + ft) := hdecf.add hdecft
  have hdecfm : StripDecay c (f + -ft) := hdecf.add hdecft.neg
  have hfp0 : f + ft = 0 := hRneg (f + ft) (hadd hPf hPft) (hmf.add hmft) hT2fp hfp hdecfp
  have hfm0 : f + -ft = 0 :=
    hRpos (f + -ft) (hadd hPf (hneg hPft)) (hmf.add hmft.neg) hT2fm hfm hdecfm
  -- `f + ft = 0` and `f - ft = 0` give `f = ft = 0` over any `ℂ`-vector space
  have key : ∀ a b : ℂ, a + b = 0 → a + -b = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 h2
    have e1 : a = -b := add_eq_zero_iff_eq_neg.mp h1
    have e2 : a = b := by
      have h := add_eq_zero_iff_eq_neg.mp h2
      simpa using h
    have hb : b = -b := by
      nth_rewrite 1 [← e2]
      exact e1
    have hb0 : b = 0 := by
      have h4 : b + b = 0 := by
        have := congrArg (fun z : ℂ => z + b) hb
        simpa using this
      have h5 : (2 : ℂ) * b = 0 := by rw [two_mul]; exact h4
      exact (mul_eq_zero.mp h5).resolve_left two_ne_zero
    exact ⟨by rw [e2, hb0], hb0⟩
  have hboth : f = 0 ∧ ft = 0 := by
    have hfun : ∀ s : ℍ, f s = 0 ∧ ft s = 0 := fun s =>
      key (f s) (ft s)
        (by have := congrFun hfp0 s; simpa using this)
        (by have := congrFun hfm0 s; simpa using this)
    exact ⟨funext (fun s => (hfun s).1), funext (fun s => (hfun s).2)⟩
  obtain ⟨hf0, hft0⟩ := hboth
  refine ⟨?_, ?_⟩
  · have := congrFun hf0 (⟨τ, hτ⟩ : ℍ)
    simpa [f] using this
  · have := congrFun hft0 (⟨τ, hτ⟩ : ℍ)
    simpa [ft] using this

/-- **Reduction of the two-variable rigidity statement to the one-function statement.**
Suppose `(i/τ)^k = τ^{-k}` on the upper half plane, `k` is even, and no nonzero
`S`-eigenfunction of weight `k` and eigenvalue `±1` with the strip decay exists.  Then the
homogeneous system of `Work.FE.HomogeneousRigidity n c` has only the zero solution. -/
theorem homogeneousRigidity_of_singleRigidity {n : ℕ} [NeZero n] {c : ℝ} {k : ℤ}
    (hsf : ∀ τ : ℍ, Work.FE.slashFactor n (τ : ℂ) = (τ : ℂ) ^ (-k))
    (hkeven : Even k)
    (hRneg : SingleRigidity k (-1 : ℂ) c) (hRpos : SingleRigidity k (1 : ℂ) c) :
    Work.FE.HomogeneousRigidity n c := by
  intro g gt
  exact homogeneousRigidity_of_eigen (fun _ : ℍ → ℂ => True) (fun _ _ => trivial)
    (fun _ => trivial) hsf hkeven
    (fun f _ => hRneg f) (fun f _ => hRpos f) g gt
    (fun _ => trivial) (fun _ => trivial)


/-! ## The two target theorems, conditional on the four single-function statements -/

/-- **The `E₈` case.**  `HomogeneousRigidity 8 0` from the two weight-`4` single-function
statements. -/
theorem homogeneousRigidity_eight_of (hneg : SingleRigidity 4 (-1 : ℂ) 0)
    (hpos : SingleRigidity 4 (1 : ℂ) 0) : Work.FE.HomogeneousRigidity 8 0 :=
  homogeneousRigidity_of_singleRigidity (n := 8) (k := 4) (c := 0)
    (fun τ => slashFactor_eight (τ : ℂ)) ⟨2, by norm_num⟩ hneg hpos

/-- **The Leech case.**  `HomogeneousRigidity 24 1` from the two weight-`12` single-function
statements. -/
theorem homogeneousRigidity_twentyfour_of (hneg : SingleRigidity 12 (-1 : ℂ) 1)
    (hpos : SingleRigidity 12 (1 : ℂ) 1) : Work.FE.HomogeneousRigidity 24 1 :=
  homogeneousRigidity_of_singleRigidity (n := 24) (k := 12) (c := 1)
    (fun τ => slashFactor_twentyfour (τ : ℂ)) ⟨6, by norm_num⟩ hneg hpos

end Work.Rigidity
