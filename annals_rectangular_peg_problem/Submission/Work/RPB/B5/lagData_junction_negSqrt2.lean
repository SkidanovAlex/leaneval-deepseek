import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff
import Submission.Work.RPB.B5.contDiffAt_ite_right_of_jets

/-!
# B5: the junction `x = -√2` of the assembled family (value and `x`-derivative)

The assembled family `ℓ = lagPt W Γc Ac rho` is the collar
`collarPt Γc Ac τ (sig x) t = levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t)` for `x ≤ -√2`
(with `sig x = x²/2 - 1 ≥ 0`) and the chord chart `W τ t (rho τ x t)` for `-√2 ≤ x`.  At the
junction `x = -√2` (`sig (-√2) = 0`) the two formulas have the same value *and* the same
`x`-derivative, `derivWithin` on the collar side being taken over the half line `(-∞, -√2]`.

Both statements are consequences of the jet hypothesis `LagData.σjet`: the collar's level profile
`σ ↦ levelPt (Γc τ σ t) σ (Ac τ σ t)` and the chart's profile `σ ↦ W τ t (ρh τ t σ)` have the
same `σ`-jets of order `≤ 8` at `σ = 0` (the collar's being one-sided, for `σ ≥ 0`).  Composing
with the level `σ = sig x`, whose derivative at `-√2` is `-√2 ≠ 0`, gives the value and the
derivative.

## The steps of the proof

Writing `F σ = levelPt (Γc τ σ t) σ (Ac τ σ t)` and `G σ = W τ t (ρh τ t σ)`:

* `F 0 = G 0` is `σjet` at `k = 0`; together with `rho τ (-√2) t = 0` (`hrhom`) and
  `ρh τ t 0 = 0` (`hρh0`) this is the value statement;
* `G` is `C⁸` at `0` (the `ρ`-slice of `W` composed with the `σ`-slice of the level inverse `ρh`,
  both slices of `ContDiffOn` statements on *open* boxes, `hWsm` and `hρh`),
* `F` is `C⁸` at `0` as well: the `σ`-slices of `Γc` and `Ac` are smooth because the constraint
  `σ ≥ 0` of the fields `hΓsm`/`hAsm` applies to the *third* argument; shifting the angle by
  `2πk` into the half line `{t ≥ 0}` (`hΓper`, `hAper`) shows every slice is smooth, and
  `levelPt` is smooth (`chartJets_levelPt_contDiff`);
* hence the *seam function* `F' σ = if 0 < σ then F σ else G σ` is `C⁸` at `0`
  (`contDiffAt_ite_right_of_jets`, with `σjet` giving the required matching of the one-sided
  jets), and `deriv F' 0 = deriv G 0` because `F' = G` on `(-∞, 0]`;
* near `x = -√2` the reparametrisation `rho` agrees with `ρh (sig ·)` on a two-sided
  neighbourhood (`hrhonearδ`), so the right-hand side is `(-√2) • deriv G 0` by the chain rule;
  on the left of `-√2` the family is `F (sig ·) = F' (sig ·)` (`sig x ≥ 0` there), so the
  one-sided derivative equals `(-√2) • deriv F' 0 = (-√2) • deriv G 0`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary facts about `sig` -/

/-- `sig (-√2) = 0`. -/
private lemma sig_neg_sqrt_two : sig (-Real.sqrt 2) = 0 := by
  simp only [sig, neg_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

/-- On the collar's range `x ≤ -√2` the attached level `sig x = x²/2 - 1` is nonnegative. -/
private lemma sig_nonneg_of_le {x : ℝ} (hx : x ≤ -Real.sqrt 2) : 0 ≤ sig x := by
  have hsq : (2 : ℝ) ≤ x ^ 2 := by
    have hx' : Real.sqrt 2 ≤ -x := by linarith [Real.sqrt_nonneg 2]
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hx' 2
    rwa [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), neg_sq] at h
  simp only [sig]
  linarith

/-- `deriv sig (-√2) = -√2`. -/
private lemma hasDerivAt_sig_neg_sqrt_two :
    HasDerivAt sig (-Real.sqrt 2) (-Real.sqrt 2) := by
  show HasDerivAt (fun x : ℝ => x ^ 2 / 2 - 1) (-Real.sqrt 2) (-Real.sqrt 2)
  have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - 1) (-(2 * Real.sqrt 2) / 2) (-Real.sqrt 2) := by
    simpa using ((hasDerivAt_pow 2 (-Real.sqrt 2)).div_const 2).sub_const 1
  rwa [show -(2 * Real.sqrt 2) / 2 = -Real.sqrt 2 from by ring] at h

/-- The chain rule for a vector-valued function composed with a real-valued one. -/
private lemma deriv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (g : ℝ → ℝ) (x : ℝ) (hF : DifferentiableAt ℝ F (g x))
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => F (g y)) x = deriv g x • deriv F (g x) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt
  have hd : deriv (fun y => F (g y)) x = fderiv ℝ F (g x) (deriv g x) := by
    simpa only [Function.comp_def] using h.deriv
  rw [hd, fderiv_eq_smul_deriv]

/-! ## Slicing the smoothness fields

`chartJets_levelPt_contDiff` provides the smoothness of the level chart.  What remains is to
extract one-variable slices from the `ContDiffOn` fields of `LagData`. -/

/-- The `ρ`-slice at `ρ = 0` of a function smooth on a box `Icc 0 1 × univ × Ioo a b` with
`a < 0 < b` is smooth at `0`. -/
private theorem slice_contDiffAt_openBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × (ℝ × ℝ) → E} {a b τ t : ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ n F (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b))
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ha : a < 0) (hb : 0 < b) :
    ContDiffAt ℝ n (fun ρ : ℝ => F (τ, t, ρ)) 0 := by
  have hglob : ContDiff ℝ n (fun ρ : ℝ => (τ, t, ρ)) := by fun_prop
  have hi : ContDiffWithinAt ℝ n (fun ρ : ℝ => (τ, t, ρ)) (Set.Ioo a b) 0 :=
    hglob.contDiffWithinAt
  have hFW : ContDiffWithinAt ℝ n F (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b)
      (τ, t, 0) := hF.contDiffWithinAt (x := (τ, t, 0)) ⟨hτ, Set.mem_univ t, ha, hb⟩
  have hmt : Set.MapsTo (fun ρ : ℝ => (τ, t, ρ)) (Set.Ioo a b)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo a b) :=
    fun ρ hρ => ⟨hτ, Set.mem_univ t, hρ⟩
  exact (hFW.comp (0 : ℝ) hi hmt).contDiffAt (isOpen_Ioo.mem_nhds ⟨ha, hb⟩)

/-- Iterating the quasi-periodicity relation `f τ σ (t + 2π) = f τ σ t + c`. -/
private lemma quasi_periodic_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) (k : ℕ) (τ σ t : ℝ) :
    f τ σ (t + 2 * Real.pi * (k : ℝ)) = f τ σ t + (k : ℝ) • c := by
  induction k generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [show t + 2 * Real.pi * ((n : ℝ) + 1)
        = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi by ring]
    rw [hper τ σ (t + 2 * Real.pi * (n : ℝ)), ih t]
    rw [add_smul, one_smul]
    abel

/-- The `σ`-slice at `σ = 0` of a family `f` which is `C⁸` on the set where the *third* argument
is `≥ 0` (and the first lies in `Icc 0 1`) and quasi-periodic in the third argument with shift
`c`: shifting the third argument into the half line `{t ≥ 0}` makes the slice smooth. -/
private theorem slice_contDiffAt_halfSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ContDiffAt ℝ 8 (fun σ : ℝ => f τ σ t) 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < t + 2 * Real.pi * (k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (-t / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_lt_mul_of_pos_right hk hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  have hshift : ContDiffAt ℝ 8 (fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ))) 0 := by
    have hpt : (τ, (0, t + 2 * Real.pi * (k : ℝ))) ∈
        Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ) :=
      ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    have hFw : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))
        (τ, (0, t + 2 * Real.pi * (k : ℝ))) := hsm.contDiffWithinAt hpt
    have hg : ContDiffWithinAt ℝ 8 (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ))))
        Set.univ 0 :=
      (by fun_prop : ContDiff ℝ 8
        (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ))))).contDiffWithinAt
    have hmt : Set.MapsTo (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ)))) Set.univ
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
      fun σ _ => ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    simpa only [Function.comp_def] using (hFw.comp (0 : ℝ) hg hmt).contDiffAt (by simp)
  have heq : (fun σ : ℝ => f τ σ t)
      = fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ)) - (k : ℝ) • c := by
    funext σ
    rw [quasi_periodic_nat f c hper k τ σ t]
    abel
  rw [heq]
  exact hshift.sub contDiffAt_const

/-! ## The junction -/

theorem lagData_junction_negSqrt2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      (Work.RPB.B5.collarPt D.Γc D.Ac τ (Work.RPB.B5.sig (-Real.sqrt 2)) t
        = D.W τ t (D.rho τ (-Real.sqrt 2) t)) ∧
      (derivWithin (fun x : ℝ => Work.RPB.B5.collarPt D.Γc D.Ac τ (Work.RPB.B5.sig x) t)
          (Set.Iic (-Real.sqrt 2)) (-Real.sqrt 2)
        = deriv (fun x : ℝ => D.W τ t (D.rho τ x t)) (-Real.sqrt 2)) := by
  intro τ hτ t
  -- the collar's level profile `F` and the chart's level profile `G`
  set F : ℝ → Work.RPV.PS := fun σ => Work.RPV.levelPt (D.Γc τ σ t) σ (D.Ac τ σ t) with hFdef
  set G : ℝ → Work.RPV.PS := fun σ => D.W τ t (D.ρh τ t σ) with hGdef
  -- ## smoothness of the chart side `G` at `0`
  have hGcd : ContDiffAt ℝ 8 G 0 := by
    have hWslice : ContDiffAt ℝ 8 (fun ρ : ℝ => D.W τ t ρ) (D.ρh τ t 0) := by
      rw [D.hρh0 τ hτ t]
      exact slice_contDiffAt_openBox D.hWsm hτ (by linarith [D.hρ₀]) D.hρ₀
    have hρhslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.ρh τ t σ) 0 :=
      slice_contDiffAt_openBox D.hρh hτ (by linarith [D.hκ]) D.hκ
    have h := hWslice.comp (0 : ℝ) hρhslice
    simpa only [Function.comp_def, hGdef] using h
  have hGdiff : DifferentiableAt ℝ G 0 := hGcd.differentiableAt (by norm_num)
  -- ## smoothness of the collar side `F` at `0`
  have hΓslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.Γc τ σ t) 0 :=
    slice_contDiffAt_halfSpace D.Γc 0 D.hΓsm
      (fun τ σ t => by rw [D.hΓper τ σ t, add_zero]) hτ t
  have hAslice : ContDiffAt ℝ 8 (fun σ : ℝ => D.Ac τ σ t) 0 :=
    slice_contDiffAt_halfSpace D.Ac (2 * Real.pi) D.hAsm
      (fun τ σ t => D.hAper τ σ t) hτ t
  have hFcd : ContDiffAt ℝ 8 F 0 := by
    have hinner : ContDiffAt ℝ 8 (fun σ : ℝ => (D.Γc τ σ t, (σ, D.Ac τ σ t))) 0 :=
      hΓslice.prodMk ((contDiffAt_id (x := (0 : ℝ))).prodMk hAslice)
    have houter : ContDiffAt ℝ 8 (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
        (D.Γc τ 0 t, (0, D.Ac τ 0 t)) := chartJets_levelPt_contDiff.contDiffAt
    have h := houter.comp (0 : ℝ) hinner
    simpa only [Function.comp_def, hFdef] using h
  -- ## the two profiles have the same value at `0` (`σjet` at order `0`)
  have h0val : Work.RPV.levelPt (D.Γc τ 0 t) 0 (D.Ac τ 0 t) = D.W τ t (D.ρh τ t 0) := by
    have h := D.σjet τ hτ t 0 (by norm_num)
    simpa only [iteratedDerivWithin_zero, iteratedDeriv_zero] using h
  have hFG0 : F 0 = G 0 := h0val
  have hsig0 : sig (-Real.sqrt 2) = 0 := sig_neg_sqrt_two
  have hsigDiff : DifferentiableAt ℝ sig (-Real.sqrt 2) :=
    hasDerivAt_sig_neg_sqrt_two.differentiableAt
  have hGat : DifferentiableAt ℝ G (sig (-Real.sqrt 2)) := by
    rw [hsig0]; exact hGdiff
  constructor
  · -- ### the value at the junction
    rw [hsig0, D.hrhom τ hτ t]
    show Work.RPV.levelPt (D.Γc τ 0 t) 0 (D.Ac τ 0 t) = D.W τ t 0
    rw [h0val, D.hρh0 τ hτ t]
  · -- ### the one-sided `x`-derivative at the junction
    -- the one-sided jets of `F` match the jets of `G` at `0`
    have hjet : ∀ j ≤ 8, iteratedDerivWithin j F (Set.Ioi 0) 0 = iteratedDeriv j G 0 := by
      intro j hj
      simpa only [hFdef, hGdef] using D.σjet τ hτ t j hj
    -- the seam function `F'` is `C⁸` at `0`, and its derivative at `0` is `deriv G 0`
    set F' : ℝ → Work.RPV.PS := fun σ => if 0 < σ then F σ else G σ with hF'def
    have hF'cd : ContDiffAt ℝ ((8 : ℕ) : WithTop ℕ∞) F' 0 := by
      have h := contDiffAt_ite_right_of_jets 8 G F 0 hGcd hFcd.contDiffWithinAt hjet
      simpa only [hF'def] using h
    have hF'diff : DifferentiableAt ℝ F' 0 := hF'cd.differentiableAt (by norm_num)
    have hEqOn : Set.EqOn F' G (Set.Iic (0 : ℝ)) := by
      intro σ hσ
      show (if 0 < σ then F σ else G σ) = G σ
      rw [ite_eq_right (not_lt.mpr hσ)]
    have hF'0 : F' 0 = G 0 := by
      show (if 0 < (0 : ℝ) then F 0 else G 0) = G 0
      rw [ite_eq_right (lt_irrefl 0)]
    have hderivF' : deriv F' 0 = deriv G 0 := by
      rw [← hF'diff.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))]
      rw [derivWithin_congr hEqOn hF'0]
      exact hGdiff.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
    -- `sig x ≥ 0` on the collar's range, so the collar branch is `F' (sig ·)`
    have hEvenOn : Set.EqOn (fun x : ℝ => collarPt D.Γc D.Ac τ (sig x) t)
        (fun x : ℝ => F' (sig x)) (Set.Iic (-Real.sqrt 2)) := by
      intro x hx
      have hx' : 0 ≤ sig x := sig_nonneg_of_le hx
      have h2 : collarPt D.Γc D.Ac τ (sig x) t = F (sig x) := rfl
      rcases lt_or_eq_of_le hx' with hlt | heq
      · have h1 : F' (sig x) = F (sig x) := by
          show (if 0 < sig x then F (sig x) else G (sig x)) = F (sig x)
          rw [ite_eq_left hlt]
        exact h2.trans h1.symm
      · have h1 : F' (sig x) = G (sig x) := by
          show (if 0 < sig x then F (sig x) else G (sig x)) = G (sig x)
          rw [← heq, ite_eq_right (lt_irrefl 0)]
        exact h2.trans ((by rw [← heq, hFG0] : F (sig x) = G (sig x)).trans h1.symm)
    -- the left-hand side
    have hLHS : derivWithin (fun x : ℝ => collarPt D.Γc D.Ac τ (sig x) t)
        (Set.Iic (-Real.sqrt 2)) (-Real.sqrt 2) = (-Real.sqrt 2) • deriv G 0 := by
      have hpt : (-Real.sqrt 2 : ℝ) ∈ Set.Iic (-Real.sqrt 2) := Set.mem_Iic.mpr le_rfl
      rw [derivWithin_congr hEvenOn (hEvenOn hpt)]
      have hF'at : DifferentiableAt ℝ F' (sig (-Real.sqrt 2)) := by
        rw [hsig0]; exact hF'diff
      have hdiff : DifferentiableAt ℝ (fun x : ℝ => F' (sig x)) (-Real.sqrt 2) :=
        hF'at.comp (-Real.sqrt 2) hsigDiff
      rw [hdiff.derivWithin (uniqueDiffWithinAt_Iic (-Real.sqrt 2))]
      rw [deriv_comp_smul F' sig (-Real.sqrt 2) hF'at hsigDiff,
        hasDerivAt_sig_neg_sqrt_two.deriv, hsig0, hderivF']
    -- the right-hand side: `rho` agrees with `ρh (sig ·)` near `-√2`
    have hrhs : deriv (fun x : ℝ => D.W τ t (D.rho τ x t)) (-Real.sqrt 2)
        = (-Real.sqrt 2) • deriv G 0 := by
      obtain ⟨δ, hδpos, _hδ14, _hδκ, hδnear, _⟩ := D.hrhonearδ
      have hev : (fun x : ℝ => D.W τ t (D.rho τ x t))
          =ᶠ[𝓝 (-Real.sqrt 2)] (fun x : ℝ => D.W τ t (D.ρh τ t (sig x))) := by
        have hmem : Set.Ioo (-Real.sqrt 2 - δ) (-Real.sqrt 2 + δ) ∈ 𝓝 (-Real.sqrt 2) :=
          isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
        filter_upwards [hmem] with x hx
        rw [hδnear τ hτ x hx t]
      rw [hev.deriv_eq]
      show deriv (fun y : ℝ => G (sig y)) (-Real.sqrt 2) = (-Real.sqrt 2) • deriv G 0
      rw [deriv_comp_smul G sig (-Real.sqrt 2) hGat hsigDiff,
        hasDerivAt_sig_neg_sqrt_two.deriv, hsig0]
    exact hLHS.trans hrhs.symm

end Work.RPB.B5
