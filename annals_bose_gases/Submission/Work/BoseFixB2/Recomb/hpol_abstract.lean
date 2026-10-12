import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB2.Polar.additive_bddAbove_continuous
import Submission.Work.BoseFixB2.Polar.polarForm_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Recomb.hpol_abstract`

**Nonnegative quadratic forms are homogeneously polarised.**

For a function `Q : V → ℝ` on a real vector space which satisfies the parallelogram law,
is `2`-homogeneous and is nonnegative, the polar form
`B x y = (Q (x + y) - Q (x - y)) / 4` is `ℝ`-homogeneous in its first variable:

`Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y))`.

This is the hypothesis `hpol` of `Work.BoseFixB2.Polar.par_polarisation_hpol` (and of
`Work.BoseFixB2.Recomb.jvn_polar_expansion`), and it is *not* a formal consequence of the
parallelogram law plus `2`-homogeneity alone: the defect
`t ↦ (Q (t • x + y) - Q (t • x - y)) - t * (Q (x + y) - Q (x - y))` is then an arbitrary
derivation of `ℝ` (`Work.BoseFixB2.Polar.par_polarisation` records the counterexample).
Nonnegativity rules it out, because the parallelogram law gives

`Q (s • x + y) = s ^ 2 * Q x + Q y + 2 * A s`,  `Q (s • x - y) = s ^ 2 * Q x + Q y - 2 * A s`

for `A s = (Q (s • x + y) - Q (s • x - y)) / 4`, so `0 ≤ Q (s • x ± y)` bounds
`|A s| ≤ (s ^ 2 * Q x + Q y) / 2`; `A` is additive (parallelogram law only,
`Work.BoseFixB2.Polar.polarForm_add`), hence continuous
(`Work.BoseFixB2.Polar.additive_bddAbove_continuous`), hence `ℝ`-linear with `A 0 = 0`.

The remaining content of the file is the **smooth-state interface**: the words of FS
`eq:DefT` have their parallelogram law only on `C^∞` states, so the abstract lemma is
applied on the `ℝ`-submodule `SmoothFn` of smooth functions; `hpol_of_par_nonneg_smooth`
unpacks that application into a statement about raw functions (no `Submodule` coercion in
the interface), which is the form in which the four summands of `fsT` are handled.
-/

noncomputable section

open scoped Topology

namespace Work.BoseFixB2.Recomb

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Additive functions of `ℝ` -/

/-- **An additive continuous function `ℝ → ℝ` is `ℝ`-linear.**  Such an `F` is `ℚ`-linear
(`map_rat_smul`), hence agrees with `t ↦ t * F 1` on the rationals, which are dense in `ℝ`;
both sides being continuous, the equality holds everywhere. -/
private lemma additive_continuous_eq_mul (F : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, F (s + t) = F s + F t) (hcont : Continuous F) (t : ℝ) :
    F t = t * F 1 := by
  have hF0 : F 0 = 0 := by
    have h := hadd 0 0
    rw [zero_add] at h
    linarith
  let f : ℝ →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  have hfcont : Continuous f := hcont
  have hkey : (f : ℝ → ℝ) = fun t => t * F 1 := by
    refine (Rat.denseRange_cast).equalizer hfcont ?_ ?_
    · fun_prop
    · funext q
      have h := map_rat_smul f q (1 : ℝ)
      rw [Rat.smul_one_eq_cast, Rat.smul_def] at h
      simpa [f] using h
  exact congr_fun hkey t

/-! ## 2. The abstract lemma -/

/-- **Homogeneous polarisation of a nonnegative quadratic form.**

For `Q : V → ℝ` on a real vector space satisfying the parallelogram law, `2`-homogeneity
and nonnegativity, the polar form is `ℝ`-homogeneous in its first argument. -/
theorem hpol_par_hom_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (hnn : ∀ x : V, 0 ≤ Q x) :
    ∀ (t : ℝ) (x y : V), Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)) := by
  intro t x y
  have hQ0 : Q (0 : V) = 0 := by
    have h := hhom 0 (0 : V)
    simpa using h
  have hQneg : ∀ z : V, Q (-z) = Q z := by
    intro z
    have h := hhom (-1) z
    simpa using h
  -- the polar form along the line `s ↦ s • x + y`
  set A : ℝ → ℝ := fun s => (Q (s • x + y) - Q (s • x - y)) / 4 with hA
  have hAval : ∀ s : ℝ, A s = (Q (s • x + y) - Q (s • x - y)) / 4 := by
    intro s
    simp only [hA]
  -- additivity of `A`, from the parallelogram law
  have hAadd : ∀ s u : ℝ, A (s + u) = A s + A u := by
    intro s u
    have h := Work.BoseFixB2.Polar.polarForm_add Q hpar hhom (s • x) (u • x) y
    rw [← add_smul] at h
    simpa only [hAval] using h
  have hA0 : A 0 = 0 := by
    have h := hAadd 0 0
    rw [zero_add] at h
    linarith
  have hAneg : ∀ s : ℝ, A (-s) = -A s := by
    intro s
    have h := hAadd s (-s)
    rw [add_neg_cancel, hA0] at h
    linarith
  -- the two quadratic identities along the line
  have hsum : ∀ s : ℝ, Q (s • x + y) + Q (s • x - y) = 2 * (s ^ 2 * Q x) + 2 * Q y := by
    intro s
    have h := hpar (s • x) y
    rw [hhom s x] at h
    linarith
  have hphi : ∀ s : ℝ, Q (s • x + y) = s ^ 2 * Q x + Q y + 2 * A s := by
    intro s
    have h1 := hsum s
    have h2 := hAval s
    linarith
  have hphi' : ∀ s : ℝ, Q (s • x - y) = s ^ 2 * Q x + Q y - 2 * A s := by
    intro s
    have h1 := hphi (-s)
    have h2 : Q ((-s) • x + y) = Q (s • x - y) := by
      rw [neg_smul, show -(s • x) + y = -(s • x - y) by abel, hQneg]
    rw [h2, hAneg s] at h1
    have hs2 : (-s) ^ 2 = s ^ 2 := by ring
    rw [hs2] at h1
    linarith
  -- nonnegativity bounds `A`
  have hbound : ∀ s : ℝ, |A s| ≤ (s ^ 2 * Q x + Q y) / 2 := by
    intro s
    have h1 := hnn (s • x + y)
    have h2 := hnn (s • x - y)
    have hp := hphi s
    have hp' := hphi' s
    rw [abs_le]
    constructor <;> linarith
  -- hence `A` is continuous and `ℝ`-linear
  have hcont : Continuous A := by
    refine Work.BoseFixB2.Polar.additive_bddAbove_continuous hAadd
      ⟨(Q x + Q y) / 2, 1, one_pos, ?_⟩
    intro s hs
    have hb := abs_le.mp (hbound s)
    have hs2 : s ^ 2 ≤ 1 := by
      have hlt := abs_lt.mp hs
      nlinarith [hlt.1, hlt.2]
    have hQx : 0 ≤ Q x := hnn x
    have hprod : 0 ≤ (1 - s ^ 2) * Q x := mul_nonneg (by linarith) hQx
    linarith [hb.1, hb.2, hprod]
  have hlin : A t = t * A 1 := additive_continuous_eq_mul A hAadd hcont t
  have hl : Q (t • x + y) - Q (t • x - y) = 4 * A t := by
    have h := hAval t
    linarith
  have hr : Q (x + y) - Q (x - y) = 4 * A 1 := by
    have h := hAval 1
    simp only [one_smul] at h
    linarith
  rw [hl, hr, hlin]
  ring

/-! ## 3. The smooth-state interface -/

/-- The `ℝ`-submodule of `C^∞` one-body states `ℝ³ → ℝ`.  This is the largest state space on
which the parallelogram law for the words of FS `eq:DefT` is available. -/
def SmoothFn : Submodule ℝ (EuclideanSpace ℝ (Fin 3) → ℝ) where
  carrier := {ψ | ContDiff ℝ (⊤ : ℕ∞) ψ}
  zero_mem' := by
    show ContDiff ℝ (⊤ : ℕ∞) (0 : EuclideanSpace ℝ (Fin 3) → ℝ)
    exact contDiff_const
  add_mem' := by
    intro a b ha hb
    show ContDiff ℝ (⊤ : ℕ∞) (a + b)
    have ha' : ContDiff ℝ (⊤ : ℕ∞) a := by simpa using ha
    have hb' : ContDiff ℝ (⊤ : ℕ∞) b := by simpa using hb
    exact ha'.add hb'
  smul_mem' := by
    intro c x hx
    show ContDiff ℝ (⊤ : ℕ∞) (c • x)
    have hx' : ContDiff ℝ (⊤ : ℕ∞) x := by simpa using hx
    exact ContDiff.const_smul c hx'

namespace SmoothFn

lemma mem_mk {Φ : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Φ ∈ SmoothFn := by
  change ContDiff ℝ (⊤ : ℕ∞) Φ
  exact h

lemma contDiff (x : SmoothFn) : ContDiff ℝ (⊤ : ℕ∞) (x : EuclideanSpace ℝ (Fin 3) → ℝ) := by
  change (x : EuclideanSpace ℝ (Fin 3) → ℝ) ∈ SmoothFn
  exact x.2

lemma coe_add' (x y : SmoothFn) :
    ((x + y : SmoothFn) : EuclideanSpace ℝ (Fin 3) → ℝ)
      = fun z => (x : EuclideanSpace ℝ (Fin 3) → ℝ) z
        + (y : EuclideanSpace ℝ (Fin 3) → ℝ) z := by
  funext z
  simp only [Submodule.coe_add, Pi.add_apply]

lemma coe_sub' (x y : SmoothFn) :
    ((x - y : SmoothFn) : EuclideanSpace ℝ (Fin 3) → ℝ)
      = fun z => (x : EuclideanSpace ℝ (Fin 3) → ℝ) z
        - (y : EuclideanSpace ℝ (Fin 3) → ℝ) z := by
  funext z
  simp only [Submodule.coe_sub, Pi.sub_apply]

lemma coe_smul' (c : ℝ) (x : SmoothFn) :
    ((c • x : SmoothFn) : EuclideanSpace ℝ (Fin 3) → ℝ)
      = fun z => c * (x : EuclideanSpace ℝ (Fin 3) → ℝ) z := by
  funext z
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

end SmoothFn

/-- **The abstract lemma on smooth states, in raw-function form.**  The parallelogram law,
`2`-homogeneity and nonnegativity are only required *for smooth states* (which is exactly
what the words of FS `eq:DefT` provide); the conclusion is stated for arbitrary real `t` and
smooth `f, g`, with no `Submodule` coercion in sight. -/
theorem hpol_of_par_nonneg_smooth (Q : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ)
    (hpar : ∀ {f g : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      Q (fun z => f z + g z) + Q (fun z => f z - g z) = 2 * Q f + 2 * Q g)
    (hhom : ∀ (c : ℝ) {f : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      Q (fun z => c * f z) = c ^ 2 * Q f)
    (hnn : ∀ {f : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → 0 ≤ Q f)
    (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Q (fun z => t * f z + g z) - Q (fun z => t * f z - g z)
      = t * (Q (fun z => f z + g z) - Q (fun z => f z - g z)) := by
  set Q' : SmoothFn → ℝ := fun ψ => Q (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) with hQ'
  have hpar' : ∀ x y : SmoothFn, Q' (x + y) + Q' (x - y) = 2 * Q' x + 2 * Q' y := by
    intro x y
    have h := hpar (SmoothFn.contDiff x) (SmoothFn.contDiff y)
    simp only [hQ', SmoothFn.coe_add', SmoothFn.coe_sub']
    exact h
  have hhom' : ∀ (c : ℝ) (x : SmoothFn), Q' (c • x) = c ^ 2 * Q' x := by
    intro c x
    have h := hhom c (SmoothFn.contDiff x)
    simp only [hQ', SmoothFn.coe_smul']
    exact h
  have hnn' : ∀ x : SmoothFn, 0 ≤ Q' x := by
    intro x
    exact hnn (SmoothFn.contDiff x)
  have hmain := hpol_par_hom_nonneg Q' hpar' hhom' hnn' t ⟨f, SmoothFn.mem_mk hf⟩
    ⟨g, SmoothFn.mem_mk hg⟩
  simp only [hQ', SmoothFn.coe_add', SmoothFn.coe_sub', SmoothFn.coe_smul'] at hmain
  exact hmain

end Work.BoseFixB2.Recomb
