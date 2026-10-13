import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

/-! ## The iterated Leibniz rule for the radial factor `R z`

`D_z = z ∂_z` and `D_θ = sin 2θ ∂_θ` are derivations; a factor `R z` depending only on `z`
is invisible to `D_θ`, and for `D_z` the binomial rule

  `D_z^i (R · h) = Σ_{b ≤ i} C(i,b) · (D_z^b R) · (D_z^{i-b} h)`

holds pointwise wherever the two factors are differentiable often enough.  Since here `R` is
only `C⁴` (not `C^∞`), the abstract `DerivLike` machinery of `Work.Spaces` (which is stated
for the analytic class `⊤`) does not apply; instead we use the one-variable Leibniz rule
`dzdIter_mul_leibniz` of `Pieces/rowsN0Q`, which only asks for the differentiability of the
iterates and is therefore available. -/

/-- `Dzd = z ∂_z` lowers the smoothness order by one on the open half-line. -/
private lemma contDiffOn_Dzd_of_contDiffOn {u : ℝ → ℝ} {m : ℕ}
    (hu : ContDiffOn ℝ (m + 1) u (Set.Ioi (0:ℝ))) :
    ContDiffOn ℝ m (Work.Elliptic.Dzd u) (Set.Ioi (0:ℝ)) := by
  have hderiv : ContDiffOn ℝ m (deriv u) (Set.Ioi (0:ℝ)) :=
    (ContDiffOn.derivWithin hu (uniqueDiffOn_Ioi 0) (le_refl _)).congr
      (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  show ContDiffOn ℝ m (fun z => z * deriv u z) (Set.Ioi (0:ℝ))
  simpa only [id_eq] using
    (contDiffOn_id (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (s := Set.Ioi (0:ℝ))).mul hderiv

/-- The iterates of `Dzd = z ∂_z` lose one smoothness order each: if `R` is `C^n` on `(0,∞)`
then `DzdIter b R` is `C^{n-b}` there. -/
private lemma contDiffOn_DzdIter_of_contDiffOn {R : ℝ → ℝ} {n : ℕ}
    (hR : ContDiffOn ℝ n R (Set.Ioi (0:ℝ))) :
    ∀ b : ℕ, b ≤ n →
      ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b R)
        (Set.Ioi (0:ℝ)) := by
  intro b
  induction b with
  | zero => intro _; simpa using hR
  | succ b ih =>
      intro hb
      have hb' : b ≤ n := by omega
      have hle : 1 ≤ n - b := by omega
      have hprev : ContDiffOn ℝ (((n - b : ℕ) : WithTop ℕ∞)) (Work.Elliptic.DzdIter b R)
          (Set.Ioi (0:ℝ)) := ih hb'
      have hprev' : ContDiffOn ℝ (((n - b - 1 + 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.DzdIter b R) (Set.Ioi (0:ℝ)) := by
        rwa [Nat.sub_add_cancel hle]
      have hstep : ContDiffOn ℝ (((n - b - 1 : ℕ) : WithTop ℕ∞))
          (Work.Elliptic.Dzd (Work.Elliptic.DzdIter b R)) (Set.Ioi (0:ℝ)) :=
        contDiffOn_Dzd_of_contDiffOn (u := Work.Elliptic.DzdIter b R) (m := n - b - 1) hprev'
      rw [Work.Elliptic.DzdIter_succ, Nat.sub_succ]
      exact hstep

/-- Differentiability of the `Dzd`-iterates of a `C^n` function of `z` alone. -/
private lemma differentiableAt_DzdIter_of_contDiffOn {R : ℝ → ℝ} {n : ℕ}
    (hR : ContDiffOn ℝ n R (Set.Ioi (0:ℝ))) {b : ℕ} (hb : b + 1 ≤ n) {z : ℝ}
    (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter b R) z := by
  have h := contDiffOn_DzdIter_of_contDiffOn hR b (by omega)
  have hne : (((n - b : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    have hb0 : (n - b : ℕ) ≠ 0 := by omega
    exact_mod_cast hb0
  exact (h.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- The differentiability input of the two Leibniz rules, for `R` a `C⁴` function of `z`. -/
private lemma dzdIter_diff_of_contDiffOn_four {R : ℝ → ℝ}
    (hR : ContDiffOn ℝ 4 R (Set.Ioi (0:ℝ))) :
    ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0:ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b R) z := by
  intro b hb z hz
  exact differentiableAt_DzdIter_of_contDiffOn hR (b := b)
    (hb := show b + 1 ≤ 4 from by omega) hz

theorem dzIter_mixed_mul_rad {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hR : ContDiffOn ℝ 4 R (Set.Ioi (0:ℝ))) (hh : Work.FTS.LocData.SmoothQuad h) :
    (∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ)) ∧
    (∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ)) := by
  have hRdiff := dzdIter_diff_of_contDiffOn_four hR
  constructor
  · intro i hi z hz θ hθ
    -- `D_z^i (R·h)` is the `DzdIter i` of the `θ`-slice `z' ↦ R z' · h z' θ`
    rw [DzIter_slice (fun z θ => R z * h z θ) i z θ,
      dzdIter_mul_leibniz i R (fun z' => h z' θ)
        (fun b hb z' hz' => hRdiff b (by omega) z' hz')
        (fun b _ z' hz' => by
          have hmem : z' ∈ Set.Ioi (-1 : ℝ) := by
            rw [Set.mem_Ioi] at hz' ⊢
            linarith
          have h1 : DifferentiableAt ℝ (fun u => Work.Spaces.mixed b 0 h u θ) z' :=
            hh.differentiableAt_slice_mixed b 0 hmem hθ
          have h2 : (fun u => Work.Spaces.mixed b 0 h u θ)
              = fun u => Work.Elliptic.DzdIter b (fun z' => h z' θ) u := by
            funext u
            rw [Work.Spaces.mixed_zero_right]
            exact DzIter_slice h b u θ
          rwa [h2] at h1) z hz]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [DzIter_slice h (i - b) z θ]
  · intro i j hi hij z hz θ hθ
    exact radial_leibniz R h j i (by omega) hz hθ hh hRdiff

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
