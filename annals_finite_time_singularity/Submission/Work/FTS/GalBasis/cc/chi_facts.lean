import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.CutSpec
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.GalBasis.FamEAux.Ext

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D`-iterates of constants and of pointwise-zero functions

These are the two elementary facts behind the passage from `ψ N` to the complement
`χ = 1 - ψ N`: a constant has vanishing iterated `D`-derivatives as soon as the order is
positive (the outermost operator carries a `z` or a `sin 2θ` factor in front of a
derivative of a constant), and the iterates of a function which vanishes identically
vanish identically. -/

/-- The `D_θ`-iterates of positive order of the constant `1` vanish. -/
private lemma DthIter_succ_const_one (n : ℕ) : ∀ z θ : ℝ,
    Work.Spaces.DthIter (n + 1) (fun _ _ : ℝ => (1 : ℝ)) z θ = 0 := by
  induction n with
  | zero => intro z θ; simp [Work.Spaces.Dth, Work.Spaces.pth]
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' : ℝ => Work.Spaces.DthIter (n + 1) (fun _ _ : ℝ => (1 : ℝ)) z θ')
          = fun _ => (0 : ℝ) := funext fun θ' => ih z θ'
      rw [hfun, deriv_const, mul_zero]

/-- The `D_z`-iterates of positive order of the constant `1` vanish. -/
private lemma DzIter_succ_const_one (n : ℕ) : ∀ z θ : ℝ,
    Work.Spaces.DzIter (n + 1) (fun _ _ : ℝ => (1 : ℝ)) z θ = 0 := by
  induction n with
  | zero => intro z θ; simp [Work.Spaces.Dz, Work.Spaces.pz]
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter (n + 1) (fun _ _ : ℝ => (1 : ℝ)) z' θ)
          = fun _ => (0 : ℝ) := funext fun z' => ih z' θ
      rw [hfun, deriv_const, mul_zero]

/-- Every `D_z`-iterate of a function which vanishes identically vanishes identically. -/
private lemma DzIter_eq_zero_of_pointwise_zero {g : ℝ → ℝ → ℝ} (h : ∀ z θ, g z θ = 0) :
    ∀ (j : ℕ) (z θ : ℝ), Work.Spaces.DzIter j g z θ = 0 := by
  intro j
  induction j with
  | zero => intro z θ; exact h z θ
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter n g z' θ) = fun _ => (0 : ℝ) :=
        funext fun z' => ih z' θ
      rw [hfun, deriv_const, mul_zero]

/-- Every `D_θ`-iterate of a function which vanishes identically vanishes identically. -/
private lemma DthIter_eq_zero_of_pointwise_zero {g : ℝ → ℝ → ℝ} (h : ∀ z θ, g z θ = 0) :
    ∀ (i : ℕ) (z θ : ℝ), Work.Spaces.DthIter i g z θ = 0 := by
  intro i
  induction i with
  | zero => intro z θ; exact h z θ
  | succ n ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' : ℝ => Work.Spaces.DthIter n g z θ') = fun _ => (0 : ℝ) :=
        funext fun θ' => ih z θ'
      rw [hfun, deriv_const, mul_zero]

/-- Every mixed iterate of a function which vanishes identically vanishes identically. -/
private lemma mixed_eq_zero_of_pointwise_zero {g : ℝ → ℝ → ℝ} (h : ∀ z θ, g z θ = 0)
    (j i : ℕ) (z θ : ℝ) : Work.Spaces.mixed j i g z θ = 0 := by
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_pointwise_zero
    (fun z θ => DthIter_eq_zero_of_pointwise_zero h i z θ) j z θ

/-- Every mixed iterate of positive total order of the constant `1` vanishes. -/
private lemma mixed_const_one (j i : ℕ) (hji : 1 ≤ j + i) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (1 : ℝ)) z θ = 0 := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Work.Spaces.mixed_zero_right]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact DzIter_succ_const_one n z θ
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp only [Work.Spaces.mixed]
    exact DzIter_eq_zero_of_pointwise_zero
      (fun z θ => DthIter_succ_const_one n z θ) j z θ

/-- The complement of a function which is `C^∞` on the open quadrant is `C^∞` on the open
quadrant. -/
private lemma SmoothOpen_one_sub {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 1 - F z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => 1 - F z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ : ℝ => 1 - F z θ)
      = fun p : ℝ × ℝ => (1 : ℝ) - (fun p : ℝ × ℝ => F p.1 p.2) p from rfl]
  exact (contDiffOn_const (c := (1 : ℝ))).sub h

/-- Congruence of the mixed operators for two functions agreeing on the open quadrant. -/
private lemma mixed_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j i : ℕ)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
  refine Work.FTS.GalBasis.mixed_congr_of_eventuallyEq j i ?_
  filter_upwards [Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp] with p hp'
  obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
  exact h p.1 p.2 hz' h1' h2'

/-! ## The three clauses -/

/-- **The pointwise identity behind all three clauses**: on the open quadrant `D_z^jD_θ^i` of
the complement `1 - ψ N` is the negative of that of `ψ N`, as soon as `j + i ≥ 1`.  It is the
linearity of the mixed operators (`SmoothOpen.mixed_add`) applied to the pointwise identity
`(1 - ψ N) + ψ N = 1` and the vanishing of the iterates of the constant. -/
private lemma mixed_one_sub_eq_neg {ψ : ℕ → Fn} {K : ℝ} (hs : CutSpec ψ K) (N : ℕ)
    (j i : ℕ) (hji : 1 ≤ j + i) (z θ : ℝ) (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ
      = - Work.Spaces.mixed j i (ψ N) z θ := by
  have hψ : Work.FTS.EllipticEst.SmoothOpen (ψ N) := (hs.smooth N).contDiffOn
  have hχ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 1 - ψ N z θ) :=
    SmoothOpen_one_sub hψ
  have hadd := Work.FTS.EllipticEst.SmoothOpen.mixed_add hχ hψ j i z θ hz h1 h2
  have hstep : Work.Spaces.mixed j i (fun z θ => (1 - ψ N z θ) + ψ N z θ) z θ
      = Work.Spaces.mixed j i (fun _ _ : ℝ => (1 : ℝ)) z θ :=
    mixed_congr_Q0 (fun z θ _ _ _ => by ring) j i hz h1 h2
  have hzero : Work.Spaces.mixed j i (fun _ _ : ℝ => (1 : ℝ)) z θ = 0 :=
    mixed_const_one j i hji z θ
  rw [hstep, hzero] at hadd
  linarith [hadd]

/-- **The mechanism of the second clause**: at a point of the open plateau, `1 - ψ N` vanishes
on a whole neighbourhood, hence so do all its mixed derivatives. -/
private lemma compl_eventuallyEq_zero_of_plateau {ψ : ℕ → Fn} {K : ℝ} (hs : CutSpec ψ K)
    (N : ℕ) {z θ : ℝ} (hzp : z ∈ Set.Ioo (plo N) (phiN N))
    (hθp : θ ∈ Set.Ioo (qlo N) (qhi N)) :
    Function.uncurry (fun z θ : ℝ => 1 - ψ N z θ)
      =ᶠ[𝓝 (z, θ)] Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) := by
  have hopen : IsOpen (Set.Ioo (plo N) (phiN N) ×ˢ Set.Ioo (qlo N) (qhi N)) :=
    isOpen_Ioo.prod isOpen_Ioo
  filter_upwards [hopen.mem_nhds (show (z, θ) ∈ Set.Ioo (plo N) (phiN N)
      ×ˢ Set.Ioo (qlo N) (qhi N) from ⟨hzp, hθp⟩)] with p hp
  obtain ⟨hz1, hz2⟩ := hp.1
  obtain ⟨hθ1, hθ2⟩ := hp.2
  have hone : ψ N p.1 p.2 = 1 :=
    hs.one N p.1 p.2 ⟨⟨le_of_lt hz1, le_of_lt hz2⟩, ⟨le_of_lt hθ1, le_of_lt hθ2⟩⟩
  simp [Function.uncurry, hone]

/-- Route.  All three clauses follow from `mixed j i χ = -mixed j i (ψ N)` on the open quadrant
for `j + i ≥ 1` (obtained from `SmoothOpen.mixed_add` applied to the pointwise identity
`χ + ψ = 1`, the constant having vanishing `D`-iterates), together with the `CutSpec` clauses.
Clause 2 additionally uses that a point of the *open* plateau has a neighbourhood on which
`ψ N ≡ 1` (so `χ` is locally constant there, and all its `D`-iterates vanish); for that use
`DzIter_eq_zero_of_isOpen_const`, `DthIter_eq_zero_of_isOpen_const` of `CutSpec.lean`. -/
theorem chi_facts {ψ : ℕ → Work.FTS.Galerkin.Fn} {K : ℝ} (hs : CutSpec ψ K) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ N : ℕ,
      (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ| ≤ K') ∧
      (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ ≠ 0 →
        (z ∉ Set.Ioo (plo N) (phiN N) ∨ θ ∉ Set.Ioo (qlo N) (qhi N))) ∧
      (∀ j i : ℕ, 1 ≤ i → j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ ≠ 0 →
        (θ ∈ Set.Icc (tlo N) (2 / ((N : ℝ) + 1)) ∨
          θ ∈ Set.Icc (Real.pi / 2 - 2 / ((N : ℝ) + 1)) (thi N))) := by
  refine ⟨K + 1, by linarith [hs.Kpos], fun N => ⟨?_, ?_, ?_⟩⟩
  · -- Clause 1: the uniform bound.
    intro j i hji z θ hz h1 h2
    rcases Nat.eq_zero_or_pos (j + i) with h | h
    · have hj : j = 0 := by omega
      have hi : i = 0 := by omega
      subst hj
      subst hi
      show |1 - ψ N z θ| ≤ K + 1
      have hle : ψ N z θ ≤ 1 := hs.leone N z θ
      have hnn : 0 ≤ ψ N z θ := hs.nonneg N z θ
      rw [abs_of_nonneg (by linarith)]
      linarith [hs.Kpos]
    · have hid := mixed_one_sub_eq_neg hs N j i h z θ hz h1 h2
      rw [hid, abs_neg]
      have hb := hs.bound N j i hji z θ
      linarith [hs.Kpos]
  · -- Clause 2: the open plateau is derivative-free.
    intro j i hji z θ hz h1 h2 hne
    by_cases hzp : z ∈ Set.Ioo (plo N) (phiN N)
    · by_cases hθp : θ ∈ Set.Ioo (qlo N) (qhi N)
      · exfalso
        have hcong : Work.Spaces.mixed j i (fun z θ : ℝ => 1 - ψ N z θ) z θ
            = Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) z θ :=
          Work.FTS.GalBasis.mixed_congr_of_eventuallyEq j i
            (compl_eventuallyEq_zero_of_plateau hs N hzp hθp)
        have hz0 : Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
          mixed_eq_zero_of_pointwise_zero (fun _ _ => rfl) j i z θ
        exact hne (hcong.trans hz0)
      · exact Or.inr hθp
    · exact Or.inl hzp
  · -- Clause 3: the angular layers carry all the `θ`-derivatives.
    intro j i hi hji z θ hz h1 h2 hne
    by_contra hnot
    have hlayer : NotInThetaLayer N θ :=
      ⟨fun hA => hnot (Or.inl hA), fun hB => hnot (Or.inr hB)⟩
    have hψ : Work.Spaces.mixed j i (ψ N) z θ = 0 := hs.lay N j i hi z θ hlayer
    have hχ := mixed_one_sub_eq_neg hs N j i (by omega) z θ hz h1 h2
    exact hne (by rw [hχ, hψ, neg_zero])

end Work.FTS.GalBasis.cc
