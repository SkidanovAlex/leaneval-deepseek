import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Submission.Work.BoseBox.CNodeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open scoped ContDiff Topology Real NNReal

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Whole-space integration by parts, twice: `∫ f·(−D²_u f) = ∫ (D_u f)²`. -/
lemma wholeSpace_dir2_eq {N : ℕ} {f : X N → ℝ} {u : X N} (hf : ContDiff ℝ ∞ f)
    (hcs : HasCompactSupport f) :
    (∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)))
      = ∫ x, (fderiv ℝ f x u) ^ 2 := by
  let g : X N → ℝ := fun z => fderiv ℝ f z u
  have hg_cd : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact firstDir_contDiff hf u
  have hg_c : Continuous g := hg_cd.continuous
  have hf_c : Continuous f := hf.continuous
  have hD2_cd : ContDiff ℝ ∞ (fun x : X N => fderiv ℝ g x u) := by
    dsimp [g]
    exact secondDir_contDiff_u hf u
  have hD2_c : Continuous (fun x : X N => fderiv ℝ g x u) := hD2_cd.continuous
  have hg_hcs : HasCompactSupport g := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport g) (by
      simpa [g] using (tsupport_firstDir_subset (f := f) u))
  have hD2_hcs : HasCompactSupport (fun x : X N => fderiv ℝ g x u) := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport (fun x : X N => fderiv ℝ g x u)) (by
      simpa [g] using (tsupport_secondDir_subset (f := f) u))
  have hfg_c : Continuous (fun x : X N => f x * g x) := hf_c.mul hg_c
  have hfg_h : HasCompactSupport (fun x : X N => f x * g x) := hcs.mul_right
  have hfg : Integrable (fun x : X N => f x * g x) volume :=
    integrable_cont_hcs hfg_c hfg_h
  have hfD2_c : Continuous (fun x : X N => f x * fderiv ℝ g x u) := hf_c.mul hD2_c
  have hfD2_h : HasCompactSupport (fun x : X N => f x * fderiv ℝ g x u) := hcs.mul_right
  have hfD2 : Integrable (fun x : X N => f x * fderiv ℝ g x u) volume :=
    integrable_cont_hcs hfD2_c hfD2_h
  have hgg_c : Continuous (fun x : X N => fderiv ℝ f x u * g x) := hg_c.mul hg_c
  have hgg_h : HasCompactSupport (fun x : X N => fderiv ℝ f x u * g x) := hg_hcs.mul_right
  have hgg : Integrable (fun x : X N => fderiv ℝ f x u * g x) volume :=
    integrable_cont_hcs hgg_c hgg_h
  have hf_diff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := fun x hx =>
    hf.differentiable (by norm_num) x
  have hg_diff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := fun x hx =>
    hg_cd.differentiable (by norm_num) x
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := f) (g := g) (v := u)
    (μ := volume) hgg hfD2 hfg hf_diff hg_diff
  have hgoal : (∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)))
      = ∫ x, (g x) ^ 2 := by
    calc
      (∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)))
          = ∫ x, -(f x * fderiv ℝ g x u) := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [g]
            ring
      _ = -(∫ x, f x * fderiv ℝ g x u) := by rw [integral_neg]
      _ = ∫ x, (g x) ^ 2 := by
            rw [hmain]
            calc
              -(-(∫ x, fderiv ℝ f x u * g x)) = ∫ x, fderiv ℝ f x u * g x := by simp
              _ = ∫ x, (g x) ^ 2 := by
                    apply integral_congr_ae
                    filter_upwards with x
                    dsimp [g]
                    rw [pow_two]
  simpa only [g] using hgoal

/-- The pointwise sum of squares of the coordinate second derivatives is the same
for the ONB `euclBasis3` (used by `coordDir`) and the standard coordinate vectors
`kcStdBasis` (used by `kcDir`). -/
lemma sum_sq_coordDir_eq_kcDir {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ 2 f) (x : X N)
    (i : Fin N) :
    (∑ k : Fin 3, (fderiv ℝ f x (coordDir N i k)) ^ 2) =
      (∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) := by
  have h1 : ∀ k : Fin 3, fderiv ℝ f x (coordDir N i k)
      = fderiv ℝ (fun z : ℝ³ => f (Function.update x i z)) (x i) (euclBasis3 k) := by
    intro k
    have h := bridgeSliceFderivApply N i x hf (x i) (euclBasis3 k)
    simp only [Function.update_eq_self] at h
    rw [h]
    rw [show coordDir N i k = Function.update (0 : X N) i (euclBasis3 k) from by
      ext j
      by_cases hj : j = i
      · rw [hj]; simp [coordDir, coordBasis, Function.update]
      · simp [coordDir, Function.update, hj]]
  have h2 : ∀ k : Fin 3, fderiv ℝ f x (kcDir N i k)
      = fderiv ℝ (fun z : ℝ³ => f (Function.update x i z)) (x i) (kcStdBasis k) := by
    intro k
    have h := bridgeSliceFderivApply N i x hf (x i) (kcStdBasis k)
    simp only [Function.update_eq_self] at h
    rw [h]
    rw [show kcDir N i k = Function.update (0 : X N) i (kcStdBasis k) from by
      ext j
      by_cases hj : j = i
      · rw [hj]; simp [kcDir, Function.update]
      · simp [kcDir, Function.update, hj]]
  calc
    (∑ k : Fin 3, (fderiv ℝ f x (coordDir N i k)) ^ 2)
        = ∑ k : Fin 3,
            (fderiv ℝ (fun z : ℝ³ => f (Function.update x i z)) (x i) (euclBasis3 k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [h1 k]
    _ = ∑ k : Fin 3,
            (fderiv ℝ (fun z : ℝ³ => f (Function.update x i z)) (x i) (kcStdBasis k)) ^ 2 :=
          sum_fderiv_onb_eq_coord (φ := fun z : ℝ³ => f (Function.update x i z)) (x i)
    _ = ∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← h2 k]

/-- Per-slot kinetic identity: the box integral of `Ψ·(−ΔᵢΨ)` is the box integral of
the sum of squares of the coordinate derivatives of `Ψ` in slot `i`. -/
theorem boxInt_kinetic_term_eq_gradSum {N : ℕ} {L : ℝ} (hL : 0 < L)
    (Ψ : _root_.BoseGases.CInfty0Box N L) (i : Fin N) :
    (∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
      = ∑ k : Fin 3, ∫ x in box N L,
          (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2 := by
  set F : X N → ℝ := (Ψ : X N → ℝ) with hF
  have hFcd : ContDiff ℝ ∞ F := psi_contDiff Ψ
  have hFcs : HasCompactSupport F := hasCompactSupport_Ψ hL Ψ
  have hF2 : ContDiff ℝ 2 F := psi_contDiff_two Ψ
  have hFsupp : tsupport F ⊆ interior (box N L) := Ψ.support
  have hnode : ∀ x : X N, x ∉ box N L → F x = 0 := by
    intro x hx
    have hz : x ∉ interior (box N L) := fun h => hx (interior_subset h)
    exact psi_eq_zero_of_not_mem_interior Ψ hz
  have hdf : ∀ x : X N, x ∉ box N L → fderiv ℝ F x = 0 := by
    intro x hx
    have hts : x ∉ tsupport F := fun h => hx (interior_subset (hFsupp h))
    exact fderiv_of_notMem_tsupport ℝ hts
  -- box integral = whole-space integral
  have hbox : (∫ x in box N L, F x * (-(partialLaplacian i F x)))
      = ∫ x : X N, F x * (-(partialLaplacian i F x)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hnode x hx]; simp
  -- the bridge to the sum of second directional derivatives
  have hbr := partialLaplacian_eq_sum_secondDir N i (f := F) hF2
  have hpoint : (fun x : X N => F x * (-(partialLaplacian i F x)))
      = fun x : X N => ∑ k : Fin 3,
          F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
            (coordDir N i k)) := by
    funext x
    rw [congrFun hbr x, ← Finset.sum_neg_distrib, Finset.mul_sum]
  -- integrability over the whole space of each summand
  have hIntG : ∀ k : Fin 3, Integrable (fun x : X N =>
      F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
        (coordDir N i k))) volume := by
    intro k
    have hcont : Continuous (fun x : X N =>
        F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
          (coordDir N i k))) :=
      hFcd.continuous.mul ((secondDir_contDiff_u hFcd (coordDir N i k)).continuous.neg)
    exact integrable_cont_hcs hcont hFcs.mul_right
  -- integrability over the box of the squared directional derivatives
  have hIntB : ∀ (u : X N), IntegrableOn (fun x : X N => (fderiv ℝ F x u) ^ 2)
      (box N L) volume := by
    intro u
    exact integrableOn_box_of_continuous hL
      ((firstDir_contDiff hFcd u).continuous.pow 2)
  calc
    (∫ x in box N L, F x * (-(partialLaplacian i F x)))
        = ∫ x : X N, F x * (-(partialLaplacian i F x)) := hbox
    _ = ∫ x : X N, ∑ k : Fin 3,
          F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
            (coordDir N i k)) := by rw [hpoint]
    _ = ∑ k : Fin 3, ∫ x : X N,
          F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
            (coordDir N i k)) := by
          rw [integral_finsetSum (s := Finset.univ) (μ := volume)
            (f := fun (k : Fin 3) (x : X N) =>
              F x * (-(fderiv ℝ (fun z : X N => fderiv ℝ F z (coordDir N i k)) x)
                (coordDir N i k))) (fun k _ => hIntG k)]
    _ = ∑ k : Fin 3, ∫ x : X N, (fderiv ℝ F x (coordDir N i k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          exact wholeSpace_dir2_eq (u := coordDir N i k) hFcd hFcs
    _ = ∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ F x (coordDir N i k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L)
            (fun x hx => by rw [hdf x hx]; simp)).symm
    _ = ∫ x in box N L, ∑ k : Fin 3, (fderiv ℝ F x (coordDir N i k)) ^ 2 := by
          exact (integral_finsetSum (s := Finset.univ)
            (μ := volume.restrict (box N L))
            (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ F x (coordDir N i k)) ^ 2)
            (fun k _ => hIntB (coordDir N i k))).symm
    _ = ∫ x in box N L, ∑ k : Fin 3, (fderiv ℝ F x (kcDir N i k)) ^ 2 := by
          apply setIntegral_congr_fun (box_measurable N L)
          intro x hx
          simp only []
          exact sum_sq_coordDir_eq_kcDir hF2 x i
    _ = ∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ F x (kcDir N i k)) ^ 2 := by
          exact integral_finsetSum (s := Finset.univ)
            (μ := volume.restrict (box N L))
            (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ F x (kcDir N i k)) ^ 2)
            (fun k _ => hIntB (kcDir N i k))


/-- `kineticEnergy` is the gradient word `kinGradC`. -/
theorem kineticEnergy_eq_kinGradC {N : ℕ} {L : ℝ} (hL : 0 < L)
    (Ψ : _root_.BoseGases.CInfty0Box N L) :
    kineticEnergy N L Ψ = kinGradC N L (Ψ : X N → ℝ) := by
  unfold kineticEnergy kinGradC
  apply Finset.sum_congr rfl
  intro i _
  exact boxInt_kinetic_term_eq_gradSum hL Ψ i

lemma sum_pairSet_eq_two_mul_sum_lt {N : ℕ} (g : Fin N → Fin N → ℝ)
    (hsym : ∀ i j, g i j = g j i) :
    (∑ p ∈ pairSet N, g p.1 p.2)
      = 2 * ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), g p.1 p.2 := by
  set A : Fin N → Fin N → ℝ := fun i j => if i < j then g i j else 0 with hA
  have hleft : (∑ p ∈ pairSet N, g p.1 p.2) = ∑ i : Fin N, ∑ j : Fin N, (A i j + A j i) := by
    rw [show pairSet N = (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 ≠ p.2) from rfl]
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [A]
    by_cases hij : i = j
    · subst hij; simp
    · rcases lt_or_gt_of_ne hij with h | h
      · rw [if_pos hij, if_pos h, if_neg (not_lt.mpr (le_of_lt h)), add_zero]
      · rw [if_pos hij, if_neg (not_lt.mpr (le_of_lt h)), if_pos h, zero_add]
        exact hsym i j
  have hright : (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), g p.1 p.2)
      = ∑ i : Fin N, ∑ j : Fin N, A i j := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hsplit : (∑ i : Fin N, ∑ j : Fin N, (A i j + A j i)) = 2 * ∑ i : Fin N, ∑ j : Fin N, A i j := by
    have hin : ∀ i : Fin N, (∑ j : Fin N, (A i j + A j i)) = (∑ j, A i j) + (∑ j, A j i) :=
      fun i => Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_add_distrib]
    have hswap : (∑ i : Fin N, ∑ j : Fin N, A j i) = ∑ i : Fin N, ∑ j : Fin N, A i j := by
      rw [Finset.sum_comm]
    rw [hswap, two_mul]
  rw [hleft, hsplit, hright]

theorem interactionEnergy_eq_potIntC {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hvrad : _root_.BoseGases.IsRadial v)
    (Ψ : _root_.BoseGases.CInfty0Box N L) :
    interactionEnergy N L v Ψ = potIntC N L v (Ψ : X N → ℝ) := by
  have hpair : ∀ x : X N,
      (∑ p ∈ pairSet N, v (x p.1 - x p.2))
        = 2 * (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            v (x p.1 - x p.2)) := by
    intro x
    exact sum_pairSet_eq_two_mul_sum_lt (fun i j => v (x i - x j))
      (fun i j => hvrad _ _ (norm_sub_rev _ _))
  have hLHS : interactionEnergy N L v Ψ
      = ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 *
          (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            v (x p.1 - x p.2)) := rfl
  have hRHS : potIntC N L v (Ψ : X N → ℝ)
      = (1 / 2 : ℝ) * ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 *
          (∑ p ∈ pairSet N, v (x p.1 - x p.2)) := rfl
  rw [hLHS, hRHS]
  have h1 : (∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 * (∑ p ∈ pairSet N, v (x p.1 - x p.2)))
      = 2 * ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 *
          (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            v (x p.1 - x p.2)) := by
    calc
      (∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 * (∑ p ∈ pairSet N, v (x p.1 - x p.2)))
        = ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 *
            (2 * (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
              v (x p.1 - x p.2))) := by
            apply setIntegral_congr_fun (box_measurable N L)
            intro x hx
            simp only []
            rw [hpair x]
      _ = ∫ x in box N L, 2 * ((Ψ : X N → ℝ) x ^ 2 *
            (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
              v (x p.1 - x p.2))) := by
            apply setIntegral_congr_fun (box_measurable N L)
            intro x hx
            simp only []
            ring
      _ = 2 * ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 *
            (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
              v (x p.1 - x p.2)) := by
            rw [integral_const_mul]
  rw [h1]
  ring


/-- The Rayleigh quotient times the box norm² is the `𝓗`-expectation. -/
lemma rayl_mul_boxSqC {v : ℝ³ → ℝ} {N : ℕ} {L : ℝ} (hL : 0 < L)
    (Ψ : _root_.BoseGases.CInfty0Box N L) :
    Work.UBB.Rayl N L v Ψ * boxSqC N L (Ψ : X N → ℝ)
      = ∫ x in box N L, (Ψ : X N → ℝ) x * 𝓗 N v (Ψ : X N → ℝ) x := by
  have hsq : 0 < ∫ x in box N L, (Ψ : X N → ℝ) x ^ 2 := by
    rw [← boxInt_sq_eq Ψ]
    exact boxInt_sq_pos hL Ψ
  have hne : boxSqC N L (Ψ : X N → ℝ) ≠ 0 := ne_of_gt hsq
  have hden : (√ (∫ x in box N L, (Ψ : X N → ℝ) x * (Ψ : X N → ℝ) x)) ^ 2
      = boxSqC N L (Ψ : X N → ℝ) := by
    rw [Real.sq_sqrt (integral_nonneg (fun x => mul_self_nonneg _))]
    exact boxInt_sq_eq Ψ
  unfold Work.UBB.Rayl
  rw [hden]
  exact div_mul_cancel₀ _ hne


/-- **The Rayleigh quotient splits into the Dirichlet gradient word and the interaction term.**

For a smooth state `Ψ` of the box `(N,L)` (supported in the interior of `[0,L]³ᴺ`), a
radial `v ∈ L¹`, multiplying the corpus quotient `Work.UBB.Rayl N L v Ψ` by the box
norm² `boxSqC N L Ψ` gives the `𝓗`-expectation, which splits into the gradient word
`kinGradC N L Ψ = ΣᵢΣ_k∫_{Ωᴺ}(∂_{ik}Ψ)²` and the interaction term
`potIntC N L v Ψ = (1/2)Σ_{p∈pairSet N}∫_{Ωᴺ}Ψ²v(x_{p.1}−x_{p.2})`.

Ingredients available: `Submission.BoseGases.energy_decomposition_admissible` gives
`⟪Ψ,𝓗 N v Ψ⟫ = kineticEnergy N L Ψ + interactionEnergy N L v Ψ` under `MemLp v 1`;
`kineticEnergy N L Ψ = Σᵢ∫_{Ωᴺ}Ψ·(−Δ⁽ⁱ⁾Ψ)` by definition, and the per-slot equality
`∫Ψ·(−Δ⁽ⁱ⁾Ψ) = Σ_k∫(∂_{ik}Ψ)²` is the one proved inside
`Submission.BoxEnergy.wholeSpace_dir2_nonneg` (with
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`,
`Bridge.partialLaplacian_eq_sum_secondDir`, and `setIntegral_eq_integral_of_forall_compl_eq_zero`
for the box/whole-space comparison); `Rayl N L v Ψ * boxSqC N L Ψ = ⟪Ψ,𝓗 N v Ψ⟫` is the
unfolding plus `(√(∫Ψ²))² = ∫Ψ²` (`∫Ψ² ≥ 0`).  The interaction term: for even `v` (a
radial `v` is even) `potIntC` equals `∫Ψ²Σ_{i<j}v(xᵢ−xⱼ) = interactionEnergy N L v Ψ`
(`pairSet N` is the set of *ordered* distinct pairs).

This is the bridge the `C` node (`Work.BoseBox.CompareBox`) consumes. -/
theorem rayl_decomp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {N : ℕ} {L : ℝ} (hL : 0 < L)
    (hv : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (Ψ : _root_.BoseGases.CInfty0Box N L) :
    Work.UBB.Rayl N L v Ψ * Work.BoseBox.boxSqC N L (Ψ : Submission.BoseGases.X N → ℝ)
      = Work.BoseBox.kinGradC N L (Ψ : Submission.BoseGases.X N → ℝ)
        + Work.BoseBox.potIntC N L v (Ψ : Submission.BoseGases.X N → ℝ) := by
  rw [rayl_mul_boxSqC (v := v) hL Ψ,
    energy_decomposition_admissible N hL hv Ψ,
    kineticEnergy_eq_kinGradC hL Ψ,
    interactionEnergy_eq_potIntC hvrad Ψ]

end Work.BoseBox
