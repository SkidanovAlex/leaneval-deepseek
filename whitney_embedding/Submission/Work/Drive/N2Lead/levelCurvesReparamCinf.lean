import Mathlib
import Submission.Work.Drive.N2C.defs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

/-- **Shifting the argument by an integer.**  If `h (x + 1) = h x + δ`, then
`h (z + n) = h z + n * δ` for every integer `n`.

The proof passes to the (`1`-periodic) function `z ↦ h z - δ * z`. -/
theorem intShift_apply {h : ℝ → ℝ} {δ : ℝ} (hper : ∀ x : ℝ, h (x + 1) = h x + δ)
    (n : ℤ) (z : ℝ) : h (z + n) = h z + n * δ := by
  have hg : Function.Periodic (fun z : ℝ => h z - δ * z) 1 := by
    intro z
    show h (z + 1) - δ * (z + 1) = h z - δ * z
    rw [hper z]; ring
  have hz := (hg.int_mul n) z
  simp only [mul_one] at hz
  have h2 : δ * (z + (n : ℝ)) - δ * z = δ * n := by ring
  linarith

/-- A `1`-periodic curve is invariant under every integer shift of the parameter. -/
theorem periodic_eq_of_add_int {X : Type*} {γ : ℝ → X}
    (hper : ∀ x : ℝ, γ (x + 1) = γ x) (z : ℝ) (k : ℤ) : γ (z + k) = γ z := by
  have hp : Function.Periodic γ (1 : ℝ) := hper
  simpa using (hp.int_mul k) z

/-- **Reparametrising a parametrisation of a regular level (`C^∞` data).**

`L : LevelCurves f u n` parametrises a level by `n` periodic curves.  If `h i : ℝ → ℝ` are `C^∞`
bijections of `ℝ` with `h i (x + 1) = h i x + δ i`, `δ i ∈ {1, -1}`, and nowhere vanishing
derivative, then `x ↦ L.γ i (h i x)` is again a `LevelCurves f u n` (all eight rows: smoothness, the
level row, the period, injectivity on `[0,1)`, the "mod one" row, the cover row, disjointness and the
kernel row of the derivative).

The smoothness level is `((⊤ : ℕ∞) : WithTop ℕ∞)` (plain `C^∞`), deliberately NOT the bare `⊤` of
`ContDiff ℝ ⊤`, which in this library means *analytic*.

Proof hints for the rows: `per` uses `L.per` (and `L.per` backwards for `δ i = -1`); `injIco` and
`modOne` use `L.modOne` together with `h i (y + m) = h i y + m * δ i` for integers `m` (iterating
`hper`, including negative `m`), which turns integer differences into integer differences; `cover`
and `disj` use `Function.Surjective` (`range` is unchanged) and `L.cover`/`L.disj`; the `ker` row
uses the chain rule `mfderiv (L.γ i ∘ h i) x = mfderiv (L.γ i) (h i x) ∘ mfderiv (h i) x`, that
`mfderiv (h i) x` is multiplication by `deriv (h i) x` (surjective onto `ℝ` by `hderiv`), and then
`L.ker`. -/
theorem levelCurvesReparamCinf {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {u : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n)
    {h : Fin n → ℝ → ℝ} {δ : Fin n → ℝ} (hδ : ∀ i, δ i = 1 ∨ δ i = -1)
    (hsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i)) (hinj : ∀ i, Function.Injective (h i))
    (hsurj : ∀ i, Function.Surjective (h i)) (hderiv : ∀ i x, deriv (h i) x ≠ 0)
    (hper : ∀ i x, h i (x + 1) = h i x + δ i) :
    ∃ L' : Work.Drive.N2C.LevelCurves f u n, ∀ i x, L'.γ i x = L.γ i (h i x) := by
  let γ' : Fin n → ℝ → M := fun i x => L.γ i (h i x)
  have hγ' : ∀ (i : Fin n) (x : ℝ), γ' i x = L.γ i (h i x) := fun i x => rfl
  -- smoothness: compose the smooth curve with the smooth reparametrisation
  have hsm' : ∀ i : Fin n, ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤:ℕ∞):WithTop ℕ∞) (γ' i) := by
    intro i
    have hh : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞) (h i) :=
      (hsm i).contMDiff
    exact (L.sm i).comp hh
  -- the value row is immediate
  have hval' : ∀ (i : Fin n) (x : ℝ), f (γ' i x) = u := fun i x => L.val i (h i x)
  -- periodicity: `γ i` is invariant under `± 1`, and `δ i = ± 1`
  have hper' : ∀ (i : Fin n) (x : ℝ), γ' i (x + 1) = γ' i x := by
    intro i x
    rw [hγ' i (x + 1), hγ' i x, hper i x]
    rcases hδ i with h1 | h1
    · rw [h1]
      simpa using periodic_eq_of_add_int (L.per i) (h i x) (1 : ℤ)
    · rw [h1]
      simpa using periodic_eq_of_add_int (L.per i) (h i x) (-1 : ℤ)
  -- the "mod 1" row: `h` is injective, and `δ i = ± 1`, so `h x = h y + k` forces `x - y ∈ ℤ`
  have hmod' : ∀ (i : Fin n) (x y : ℝ), γ' i x = γ' i y → ∃ k : ℤ, x = y + k := by
    intro i x y hxy
    rw [hγ' i x, hγ' i y] at hxy
    obtain ⟨k, hk⟩ := L.modOne i (h i x) (h i y) hxy
    rcases hδ i with h1 | h1
    · refine ⟨k, ?_⟩
      have hshift := intShift_apply (h := h i) (δ := δ i) (hper i) k y
      rw [h1, mul_one] at hshift
      exact hinj i (hk.trans hshift.symm)
    · refine ⟨-k, ?_⟩
      have hshift := intShift_apply (h := h i) (δ := δ i) (hper i) (-k) y
      rw [h1] at hshift
      have hcast : ((-k : ℤ) : ℝ) * (-1 : ℝ) = (k : ℝ) := by push_cast; ring
      rw [hcast] at hshift
      exact hinj i (hk.trans hshift.symm)
  -- injectivity on `[0,1)`, read off from the "mod 1" row
  have hinjIco' : ∀ i : Fin n, Set.InjOn (γ' i) (Set.Ico 0 1) := by
    intro i x hx y hy hxy
    obtain ⟨k, hk⟩ := hmod' i x y hxy
    have hx' : (0:ℝ) ≤ x ∧ x < 1 := by simpa [Set.mem_Ico] using hx
    have hy' : (0:ℝ) ≤ y ∧ y < 1 := by simpa [Set.mem_Ico] using hy
    have hk1 : (k:ℝ) < 1 := by linarith
    have hk2 : (-1:ℝ) < (k:ℝ) := by linarith
    have hklt : k < 1 := by exact_mod_cast hk1
    have hkgt : -1 < k := by exact_mod_cast hk2
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    simpa using hk
  -- covering: `h` is surjective, so nothing changes
  have hcover' : ∀ x : M, f x = u → ∃ (i : Fin n) (t : ℝ), x = γ' i t := by
    intro x hx
    obtain ⟨i, t, ht⟩ := L.cover x hx
    obtain ⟨s, hs⟩ := hsurj i t
    exact ⟨i, s, by rw [hγ' i s, hs]; exact ht⟩
  -- disjointness of the ranges: the ranges are those of the curves of `L`
  have hdisj' : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ' i)) (Set.range (γ' j)) := by
    intro i j hij
    have h1 : Set.range (γ' i) = Set.range (L.γ i) := by
      ext z; constructor
      · rintro ⟨x, rfl⟩; exact ⟨h i x, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := hsurj i y
        exact ⟨x, by rw [hγ' i x, hx]⟩
    have h2 : Set.range (γ' j) = Set.range (L.γ j) := by
      ext z; constructor
      · rintro ⟨x, rfl⟩; exact ⟨h j x, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := hsurj j y
        exact ⟨x, by rw [hγ' j x, hx]⟩
    rw [h1, h2]
    exact L.disj i j hij
  -- the kernel row: the chain rule with the (surjective) derivative of `h`
  have hker' : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ' i x)),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ' i x) v = 0 →
      ∃ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' i) x t = v := by
    intro i x v hv
    have hv' : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i (h i x)) v = 0 := hv
    obtain ⟨s, hs⟩ := L.ker i (h i x) v hv'
    have hh : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞) (h i) :=
      (hsm i).contMDiff
    have hmd_h : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (h i) x :=
      hh.mdifferentiableAt (by simp)
    have hdiff_h : DifferentiableAt ℝ (h i) x :=
      mdifferentiableAt_iff_differentiableAt.mp hmd_h
    have hmd_g : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) (h i x) :=
      (L.sm i).mdifferentiableAt (by simp)
    -- `mfderiv (h i) x` is multiplication by `deriv (h i) x ≠ 0`, hence surjective
    have hdv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (h i) x (s / deriv (h i) x) = s := by
      have hdh : HasDerivAt (h i) (deriv (h i) x) x := hasDerivAt_deriv_iff.mpr hdiff_h
      have hmf : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (h i) x
          ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (h i) x)) := (hdh.hasFDerivAt).hasMFDerivAt
      rw [hmf.mfderiv]
      change ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (h i) x)) (s / deriv (h i) x) = s
      rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
      exact div_mul_cancel₀ s (hderiv i x)
    refine ⟨s / deriv (h i) x, ?_⟩
    have hcomp := mfderiv_comp_apply (x := x) (f := h i) (g := L.γ i) hmd_g hmd_h
      (s / deriv (h i) x)
    rw [show γ' i = (L.γ i ∘ h i) from rfl, hcomp, hdv, hs]
  exact ⟨{ γ := γ', sm := hsm', val := hval', per := hper', injIco := hinjIco',
           modOne := hmod', cover := hcover', disj := hdisj', ker := hker' },
         fun i x => rfl⟩

end Work.Drive.N2Lead
