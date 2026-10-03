import Mathlib

namespace Work.PlanarSC

open unitInterval

/-- **Path lifting for the squaring map.**

Let `γ : [0,1] → ℂ` be a continuous map avoiding `0`, and let `w` be a square root of `γ 0`.
Then there is a continuous square root of `γ` on `[0,1]` starting at `w`.

The proof writes the lift through the exponential covering `ℂ → ℂ*`: choose `e` with
`exp e = w ^ 2`, lift `γ` to `L` with `exp ∘ L = γ` and `L 0 = e` (path lifting for a covering
map), and set `δ t = exp (L t / 2)`. -/
lemma exists_continuous_sqrt_path {γ : C(I, ℂ)} (hγ : ∀ t, γ t ≠ 0) {w : ℂ}
    (hw : w ^ 2 = γ 0) : ∃ δ : C(I, ℂ), δ 0 = w ∧ ∀ t, δ t ^ 2 = γ t := by
  have hw_ne : w ≠ 0 := by
    intro h; exact hγ 0 (by rw [← hw, h]; simp)
  let e : ℂ := 2 * Complex.log w
  have he_exp : Complex.exp e = w ^ 2 := by
    simp only [e]; rw [two_mul, Complex.exp_add, Complex.exp_log hw_ne, pow_two]
  -- view `γ` as a path in `{z : ℂ // z ≠ 0}`
  let γ' : C(I, {z : ℂ // z ≠ 0}) := ⟨fun t => ⟨γ t, hγ t⟩, by fun_prop⟩
  let p : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩
  have hcov : IsCoveringMap p := Complex.isCoveringMap_exp
  have hγ'0 : γ' 0 = p e := by
    apply Subtype.ext
    show γ 0 = Complex.exp e
    rw [he_exp, hw]
  -- lift `γ` through `exp`
  let L : C(I, ℂ) := hcov.liftPath γ' e hγ'0
  have hL0 : L 0 = e := hcov.liftPath_zero γ' e hγ'0
  have hL_lift : ∀ t, Complex.exp (L t) = γ t := by
    intro t
    have := congrFun (hcov.liftPath_lifts γ' e hγ'0) t
    exact Subtype.ext_iff.mp this
  refine ⟨⟨fun t => Complex.exp (L t / 2), by fun_prop⟩, ?_, ?_⟩
  · show Complex.exp (L 0 / 2) = w
    rw [hL0]
    have : e / 2 = Complex.log w := by simp only [e]; ring
    rw [this, Complex.exp_log hw_ne]
  · intro t
    show Complex.exp (L t / 2) ^ 2 = γ t
    have ha : L t / 2 + L t / 2 = L t := by ring
    rw [pow_two, ← Complex.exp_add, ha, hL_lift t]

/-- If `Ω` is open and connected, misses `0`, and contains a full circle centred at `0`,
then the preimage `{w : ℂ | w ^ 2 ∈ Ω}` of `Ω` under the squaring map is preconnected.

This is the "$0 \notin Ω$, and `Ω` winds once around `0`" case: the circle `{‖z‖ = R} ⊆ Ω`
supplies a loop of odd winding about `0`, so the two sheets of the double cover `w ↦ w ^ 2`
are exchanged, and the preimage is a single connected component.  Concretely we show it is
path connected: every `w` with `w ^ 2 ∈ Ω` can be joined inside the preimage to a point of the
circle of radius `√R`, both by lifting a path in `Ω` from `w ^ 2` to `R` (via
`exists_continuous_sqrt_path`), and the circle of radius `√R` is contained in the preimage and
path connected.  The two square roots `√R` and `-√R` are joined by the semicircle
`t ↦ √R · exp (π i t)`, whose square has modulus `R` and hence lies in `Ω`. -/
theorem isPreconnected_sq_preimage_of_contains_circle {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (h0 : (0 : ℂ) ∉ Ω) (hcirc : ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ = R → w ∈ Ω) :
    IsPreconnected {w : ℂ | w ^ 2 ∈ Ω} := by
  obtain ⟨R, hRpos, hcircR⟩ := hcirc
  set A : Set ℂ := {w : ℂ | w ^ 2 ∈ Ω} with hA
  set s : ℂ := (Real.sqrt R : ℂ) with hs
  have hRmem : (R : ℂ) ∈ Ω := hcircR _ (by simp [abs_of_pos hRpos])
  have hs2 : s ^ 2 = (R : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt hRpos.le]
  have hsnorm : ‖s‖ = Real.sqrt R := by
    rw [hs]; simp [abs_of_nonneg (Real.sqrt_nonneg R)]
  have hsA : s ∈ A := by
    show s ^ 2 ∈ Ω
    rw [hs2]; exact hRmem
  -- `Ω` is path connected as an open connected subset of `ℂ`
  have hΩpc : IsPathConnected Ω := hΩo.isConnected_iff_isPathConnected.mp hΩc
  -- the semicircle `t ↦ √R · exp (π i t)` joins `s` to `-s` inside `A`
  have hsemi : JoinedIn A s (-s) := by
    apply JoinedIn.ofLine (f := fun t : ℝ => s * Complex.exp (↑(Real.pi * t) * Complex.I))
    · fun_prop
    · simp
    · simp [Complex.exp_pi_mul_I]
    · intro z hz
      rcases hz with ⟨t, ht, rfl⟩
      show (s * Complex.exp (↑(Real.pi * t) * Complex.I)) ^ 2 ∈ Ω
      apply hcircR
      rw [norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hsnorm, Real.sq_sqrt hRpos.le]
  have hApc : IsPathConnected A := by
    refine ⟨s, hsA, ?_⟩
    intro y hy
    have hy2 : y ^ 2 ∈ Ω := hy
    -- join `y ^ 2` to `R` inside `Ω`
    obtain ⟨γ, hγmem⟩ := hΩpc.joinedIn (y ^ 2) hy2 (R : ℂ) hRmem
    have hγnz : ∀ t, γ.toContinuousMap t ≠ 0 := by
      intro t ht
      exact h0 (ht ▸ hγmem t)
    -- lift that path to a square root starting at `y`
    obtain ⟨δ, hδ0, hδ2⟩ :=
      exists_continuous_sqrt_path (γ := γ.toContinuousMap) (w := y) hγnz γ.source.symm
    have hδA : ∀ t, δ t ∈ A := by
      intro t
      show δ t ^ 2 ∈ Ω
      rw [hδ2 t]
      exact hγmem t
    have hjoin1 : JoinedIn A y (δ 1) :=
      ⟨Path.mk δ hδ0 rfl, fun t => hδA t⟩
    have hδ1sq : δ 1 ^ 2 = R := by
      rw [hδ2 1]; exact γ.target
    have hu : δ 1 ^ 2 = s ^ 2 := by rw [hδ1sq, hs2]
    have hjoin2 : JoinedIn A (δ 1) s := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hu with h | h
      · rw [h]; exact JoinedIn.refl hsA
      · rw [h]; exact hsemi.symm
    exact (hjoin1.trans hjoin2).symm
  exact hApc.isConnected.isPreconnected

end Work.PlanarSC
