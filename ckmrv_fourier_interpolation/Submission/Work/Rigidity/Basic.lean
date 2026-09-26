/-
# The rigidity chapter of CKMRV: the uniqueness lemma `lem:noPsolutions`

This chapter is the formal home of CKMRV Lemma `lem:noPsolutions`
(Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the E8 and Leech
lattices and interpolation formulas*, Ann. of Math. 196 (2022)), the "rigidity" input of
Section 8: a solution of the homogeneous functional equations that decays fast enough along
the strip `-1 ≤ Re τ ≤ 1` must vanish.  It is what makes the sampling map surjective, hence
what turns the functional equations into the interpolation formula.

The paper proves the lemma in the following steps (Sections 3.2--3.3 and the proof of
Theorem 1.10):

1.  A pair `(g, g̃)` solving the homogeneous system is split into the *eigenfunctions* of
    the slash action of `S`.  With `k = d/2` the operators

      `g + g̃`  and  `g − g̃`

    are anti-invariant and invariant for `|_k S` respectively, so they lie in
    `Ann_k(𝓘₊, 𝒫)` and `Ann_k(𝓘₋, 𝒫)`.
2.  Those two spaces are described explicitly, as `φ_2 M_{k−2} + φ_0 M_k + φ_{−2} M_{k+2}`
    and `ψ_4 M_{k−4} + ψ_2 M_{k−2} + ψ_0 M_k`.
3.  A `q`-expansion argument shows that no nonzero element of the relevant space is
    `o(e^{−2πc Im τ})` for `(k, c) = (4, 0)` and `(12, 1)`.

This file contains the definitions of the chapter together with the elementary transfer and
algebra lemmas; `Reduction.lean` performs Step 1 and reduces the two target theorems to the
single-function statements introduced here.

## Main definitions

* `Work.Rigidity.InStrip` : the strip `-1 ≤ Re τ ≤ 1`.
* `Work.Rigidity.StripDecay` : `f = o(e^{−2πc Im τ})` along the strip.
* `Work.Rigidity.SlashEigen` : `f ∣[k] S = ε · f`.
* `Work.Rigidity.AnnT2` : `(T − I)² f = 0`.
* `Work.Rigidity.SingleRigidity k ε c` : no nonzero `f` annihilated by `(T − I)²`, of
  `S`-eigenvalue `ε` at weight `k`, decays like `o(e^{−2πc Im τ})` in the strip.  This is
  the paper's `lem:noPsolutions` in the normalisation in which it is applied.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.FunctionalEquations.Gap

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-! ## The strip and the decay condition -/

/-- The vertical strip `-1 ≤ Re τ ≤ 1` of `lem:noPsolutions`. -/
def InStrip (τ : ℍ) : Prop := -1 ≤ τ.re ∧ τ.re ≤ 1

/-- `StripDecay c f` : `f` is `o(e^{-2π c Im τ})` as `Im τ → ∞` along the strip
`-1 ≤ Re τ ≤ 1`; this is the decay hypothesis of `lem:noPsolutions` with `c = n₀ - 1`. -/
def StripDecay (c : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ φ : ℝ → ℝ, Tendsto φ atTop (𝓝 0) ∧
    ∀ τ : ℍ, InStrip τ → ‖f τ‖ ≤ φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))

lemma StripDecay.add {c : ℝ} {f g : ℍ → ℂ} (hf : StripDecay c f) (hg : StripDecay c g) :
    StripDecay c (f + g) := by
  obtain ⟨φ, hφ, hφ'⟩ := hf
  obtain ⟨ψ, hψ, hψ'⟩ := hg
  refine ⟨fun y => φ y + ψ y, by simpa using hφ.add hψ, fun τ hτ => ?_⟩
  have hexp : 0 ≤ Real.exp (-(2 * Real.pi * c * τ.im)) := Real.exp_nonneg _
  have h1 := hφ' τ hτ
  have h2 := hψ' τ hτ
  simp only [Pi.add_apply]
  calc ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ φ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))
          + ψ τ.im * Real.exp (-(2 * Real.pi * c * τ.im)) := add_le_add h1 h2
    _ = (φ τ.im + ψ τ.im) * Real.exp (-(2 * Real.pi * c * τ.im)) := by ring

lemma StripDecay.neg {c : ℝ} {f : ℍ → ℂ} (hf : StripDecay c f) : StripDecay c (-f) := by
  obtain ⟨φ, hφ, hφ'⟩ := hf
  exact ⟨φ, hφ, fun τ hτ => by simpa using hφ' τ hτ⟩

lemma StripDecay.sub {c : ℝ} {f g : ℍ → ℂ} (hf : StripDecay c f) (hg : StripDecay c g) :
    StripDecay c (f - g) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

/-! ## Transfer from functions of `ℂ` to functions on `ℍ` -/

/-- Holomorphy on the upper half plane, transferred from `ℂ`. -/
lemma mdifferentiable_of_differentiableOn {n : ℕ} [NeZero n] {g : ℂ → Work.FE.E n → ℂ}
    {x : Work.FE.E n} (hg : DifferentiableOn ℂ (fun τ : ℂ => g τ x)
      {τ : ℂ | 0 < τ.im}) :
    MDiff (fun τ : ℍ => g (τ : ℂ) x) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine hg.congr (fun z hz => ?_)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- The operator `(T − I)²`, transferred from `ℂ` to `ℍ`. -/
lemma T2op_of_complex {n : ℕ} [NeZero n] {g : ℂ → Work.FE.E n → ℂ} {x : Work.FE.E n}
    (hg : ∀ (τ : ℂ), 0 < τ.im → g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0) :
    Work.Kernels.T2op (fun τ : ℍ => g (τ : ℂ) x) = 0 := by
  funext τ
  have h := hg (τ : ℂ) τ.im_pos
  simp only [Work.Kernels.T2op, Pi.zero_apply, UpperHalfPlane.coe_vadd]
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- The strip decay condition of `Work.FE`, transferred to `ℍ`. -/
lemma stripDecay_of_tendsToZeroInStrip {n : ℕ} [NeZero n] {c : ℝ}
    {g : ℂ → Work.FE.E n → ℂ} {x : Work.FE.E n}
    (h : Work.FE.TendsToZeroInStrip n c g) :
    StripDecay c (fun τ : ℍ => g (τ : ℂ) x) := by
  obtain ⟨φ, hφ, hφ'⟩ := h x
  exact ⟨φ, hφ, fun τ hτ => hφ' (τ : ℂ) τ.im_pos hτ.1 hτ.2⟩

/-! ## The single-function rigidity statement -/

/-- `SlashEigen k ε f` : `f` is an eigenfunction of the weight-`k` slash action of `S`
with eigenvalue `ε`. -/
def SlashEigen (k : ℤ) (ε : ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, (f ∣[k] ModularGroup.S) τ = ε * f τ

/-- `AnnT2 f` : `f` is annihilated by `(T − I)²`. -/
def AnnT2 (f : ℍ → ℂ) : Prop := Work.Kernels.T2op f = 0

/-- **The paper's `lem:noPsolutions` in the form in which it is applied.**  No nonzero
holomorphic `f : ℍ → ℂ` that is annihilated by `(T − I)²` and is an eigenfunction of `|_k S`
with eigenvalue `ε`, and decays like `o(e^{−2π c Im τ})` along the strip `-1 ≤ Re τ ≤ 1`,
exists.

For `k = 4` (`c = 0`) and `k = 12` (`c = 1`) this is exactly CKMRV Lemma `lem:noPsolutions`
for the two weights used in Section 8, one eigenvalue at a time. -/
def SingleRigidity (k : ℤ) (ε : ℂ) (c : ℝ) : Prop :=
  ∀ f : ℍ → ℂ, MDiff f → AnnT2 f → SlashEigen k ε f → StripDecay c f → f = 0


/-- The converse transfer: holomorphy of `fun τ : ℍ => g τ x` gives the `ℂ`-differentiability
on the upper half plane required by `Work.FE.HomogeneousRigidity`. -/
lemma differentiableOn_of_mdifferentiable {n : ℕ} [NeZero n] {g : ℂ → Work.FE.E n → ℂ}
    {x : Work.FE.E n} (h : MDiff (fun τ : ℍ => g (τ : ℂ) x)) :
    DifferentiableOn ℂ (fun τ : ℂ => g τ x) {τ : ℂ | 0 < τ.im} := by
  rw [UpperHalfPlane.mdifferentiable_iff] at h
  exact h.congr (fun z hz => by
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz])

/-! ## Elementary algebra -/

/-- The upper half plane has no zero: `(τ : ℂ) ≠ 0`. -/
lemma coe_ne_zero (τ : ℍ) : (τ : ℂ) ≠ 0 :=
  fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im, h]; simp)

/-- `(T − I)²` is odd under negation of the function. -/
lemma T2op_neg (F : ℍ → ℂ) :
    Work.Kernels.T2op (-F) = -(Work.Kernels.T2op F) := by
  funext τ
  simp only [Work.Kernels.T2op, Pi.neg_apply]
  ring

/-- `S` has order two on `ℍ`: `S • (S • τ) = τ`. -/
lemma S_smul_S_smul (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  simp only [UpperHalfPlane.modular_S_smul]
  rw [UpperHalfPlane.ext_iff]
  simp

/-- The upper half plane point `S • τ` is `-(τ : ℂ)⁻¹`. -/
lemma coe_S_smul (τ : ℍ) : (((ModularGroup.S • τ : ℍ)) : ℂ) = -(τ : ℂ)⁻¹ := by
  simp only [UpperHalfPlane.modular_S_smul, inv_neg]

/-- `-1 / z = -z⁻¹`. -/
lemma neg_one_div (z : ℂ) : -1 / z = -z⁻¹ := by ring

/-- The factor `(-z⁻¹)^(-k)` equals `z^k` when `k` is even: the invariance of the slash
action under the substitution `τ ↦ -1/τ`. -/
lemma zpow_neg_inv (z : ℂ) {k : ℤ} (hk : Even k) : (-(z⁻¹)) ^ (-k) = z ^ k := by
  rw [zpow_neg (-(z⁻¹)) k, ← inv_zpow (-(z⁻¹)) k,
    show (-(z⁻¹))⁻¹ = -z by rw [inv_neg, inv_inv]]
  exact hk.neg_zpow z

end Work.Rigidity
