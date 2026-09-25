import Mathlib
import Submission.Work.NN.Final.DbarSolvableAux
import Submission.Work.NN.Final.DbarScale
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.Transport
import Submission.Work.NN.Final.FlatDbarInstance
import Submission.Work.NN.Final.Proj
import Submission.Work.NN.Final.Estimate
import Submission.Work.NN.Final.exists_extension
import Submission.Work.NN.Final.Lcoef_holderNorm_zero
import Submission.Work.NN.Final.Lcoef_holderNorm_one
import Submission.Work.NN.Final.proj02_integrable_flat
import Submission.Work.NN.Final.antilinear_sub_stdForm_bound
import Submission.Work.NN.Core.Solver
import Submission.Work.NN.Core.SmallBall
import Submission.Work.NN.Assemble.Setup
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Newton.exists_holFrame_of_C1small
import Submission.Work.NN.Newton.exists_rescale_C1small

namespace Work.NN.Final

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Work.NN.Core
open Set
open scoped ContDiff

noncomputable section

variable {n : ℕ}
/-! ## §4  The analytic input (temporary copies of the delegated lemmas)

The following statement is the content of the delegated lemma `NN/Final/exists_holFrame_of_small_integrable`;
it is copied here so that this module compiles while that lemma is being proved, and is replaced by
the corresponding `import` once it lands. (`Work.NN.Final.Atr_contDiffOn_aux` is proved in
`Submission.Work.NN.Final.DbarSolvableAux`, and `Work.NN.Final.exists_rescale_vecHolder_c` in
`Submission.Work.NN.Final.DbarScale`.) -/

/-- **The perturbative core of Newlander–Nirenberg in the flat model `ℂⁿ`.** -/
theorem dbarSolvable_of_perturb_C1 {n : ℕ} {U : Set (LeanEval.Geometry.NewlanderNirenberg.E n)} (hU : IsOpen U) {J : LeanEval.Geometry.NewlanderNirenberg.E n → LeanEval.Geometry.NewlanderNirenberg.E n →L[ℝ] LeanEval.Geometry.NewlanderNirenberg.E n} (hJ : LeanEval.Geometry.NewlanderNirenberg.IsAlmostComplexOn J U) (hN : LeanEval.Geometry.NewlanderNirenberg.NijenhuisVanishesOn J U) (h0 : (0 : LeanEval.Geometry.NewlanderNirenberg.E n) ∈ U) {T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ] Submission.F n} (hT : ∀ v, T (J 0 v) = Complex.I • T v) : Submission.DbarSolvable J U 0 T := by
  rcases n with _ | m
  · -- `n = 0`: both `E 0` and `ℂ^0` are singletons, and there is nothing to solve
    refine ⟨U, hU, h0, subset_refl U, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j),
      (fun j => Fin.elim0 j), ?_⟩
    intro y _
    haveI hsub : Subsingleton (LeanEval.Geometry.NewlanderNirenberg.E 0) := ⟨fun a b => by
      apply WithLp.ofLp_injective
      funext i
      exact i.elim0⟩
    haveI hsub2 : Subsingleton (Fin 0 → ℂ) := ⟨fun a b => funext fun i => i.elim0⟩
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩
  · -- the analytic input at the unit polydisc
    obtain ⟨ε, hεpos, Hcore⟩ :=
      Work.NN.Newton.exists_holFrame_of_C1small (n := m + 1) (Nat.succ_pos m) (α := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)
    obtain ⟨μ₁, hμ₁pos, hsmall₁⟩ :=
      Work.NN.Newton.exists_rescale_C1small (n := m + 1) (α := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num) hU h0 (hJ.1.of_le (by simp)) hT hεpos
    -- the domain condition for small scales
    obtain ⟨μ₀, hμ₀pos, hdom₀⟩ := exists_small_dom (n := m + 1) (U := U) (T := T) hU h0
    set μ : ℝ := min μ₀ μ₁ with hμdef
    have hμpos : 0 < μ := lt_min hμ₀pos hμ₁pos
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have hμle₀ : μ ≤ μ₀ := min_le_left _ _
    have hμle₁ : μ ≤ μ₁ := min_le_right _ _
    -- the domain condition
    have hdom : ∀ z : Cn (m + 1), z ∈ pd (m + 1) (fun _ => 1) 4 →
        tupleDerivInv (Tsh T μ hμne) z ∈ U := by
      intro z hz
      rw [tupleDerivInv_Tsh]
      exact hdom₀ μ hμpos hμle₀ z hz
    -- the smallness at the chosen scale
    have hsmall : ∀ w : Cn (m + 1), ‖w‖ ≤ 1 → ∀ j : Fin (m + 1),
        Work.CR.Flat.holderNorm 1 (1 / 2) (fun z => Atr J (Tsh T μ hμne) z w j)
          (pd (m + 1) (fun _ => 1) 4) ≤ ENNReal.ofReal ε :=
      fun w hw j => hsmall₁ μ hμpos hμle₁ w hw j
    have hsmooth : ∀ k : ℕ, ContDiffOn ℝ k (Atr J (Tsh T μ hμne))
        (pd (m + 1) (fun _ => 1) 4) := by
      intro k
      exact (Atr_contDiffOn_aux (n := m + 1) (U := U) (J := J) (T := Tsh T μ hμne)
        (k := (k : ℕ∞)) (hJ := hJ.1.of_le (by simp))).mono (fun z hz => hdom z hz)
    have hA0 : Atr J (Tsh T μ hμne) 0 = 0 := by
      refine ContinuousLinearMap.ext fun w => ?_
      exact Atr_zero J (Tsh T μ hμne) (Tsh_intertwines J T μ hμne hT) w
    have hsq : ∀ z, z ∈ pd (m + 1) (fun _ => 1) 4 → ∀ v : Cn (m + 1),
        (JstdCn (m + 1) + Atr J (Tsh T μ hμne)) z
          ((JstdCn (m + 1) + Atr J (Tsh T μ hμne)) z v) = -v := by
      intro z hz v
      rw [Jstd_add_Atr_Tsh]
      exact Jtr_sq J (Tsh T μ hμne) z
        (fun w => hJ.2 (tupleDerivInv (Tsh T μ hμne) z) (hdom z hz) w) v
    have hint : ∀ u : Cn (m + 1) → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
        ∀ z, z ∈ pd (m + 1) (fun _ => 1) 4 → ∀ V W : Cn (m + 1),
          proj02 (JstdCn (m + 1) + Atr J (Tsh T μ hμne))
            (fun z' => dOne (fun z'' =>
              dbarCn (JstdCn (m + 1) + Atr J (Tsh T μ hμne)) u z'') z') z V W = 0 := by
      intro u hu z hz V' W
      rw [Jstd_add_Atr_Tsh]
      exact proj02_integrable_flat (n := m + 1) hU hJ hN (Tsh T μ hμne) hu (hdom z hz) V' W
    obtain ⟨V, hVopen, h0V, hVsub, u, hu⟩ :=
      Hcore (Atr J (Tsh T μ hμne)) hsmooth hsq hint hsmall
    -- transport the frame to `E (m+1)`
    have hVU : V ⊆ {z : Cn (m + 1) | tupleDerivInv (Tsh T μ hμne) z ∈ U} :=
      fun z hz => hdom z (hVsub hz)
    refine ⟨(tupleDeriv (Tsh T μ hμne)) ⁻¹' V, ?_, ?_, ?_,
      (fun j y => zcoord T j y - u j (tupleDeriv (Tsh T μ hμne) y)), ?_, ?_, ?_⟩
    · exact hVopen.preimage (tupleDeriv (Tsh T μ hμne)).continuous
    · show tupleDeriv (Tsh T μ hμne) 0 ∈ V
      rw [map_zero]
      exact h0V
    · intro y hy
      have h1 : tupleDerivInv (Tsh T μ hμne) (tupleDeriv (Tsh T μ hμne) y) ∈ U := hVU hy
      rwa [tupleDerivInv_tupleDeriv] at h1
    · -- smoothness of the corrections
      intro j
      refine (contDiff_zcoord T j).contDiffOn.sub ?_
      exact (hu.1 j).comp (by fun_prop) (fun y hy => hy)
    · -- the `∂̄`-equation
      intro j y hy
      have hzd : DifferentiableAt ℝ (zcoord T j) y :=
        ((contDiff_zcoord T j).differentiable (by simp)).differentiableAt
      have hud : DifferentiableAt ℝ
          (fun y : EN (m + 1) => u j (tupleDeriv (Tsh T μ hμne) y)) y :=
        (((hu.1 j).contDiffAt (hVopen.mem_nhds hy)).differentiableAt (by simp)).comp y
          (tupleDeriv (Tsh T μ hμne)).differentiableAt
      show Submission.dbar J
          (fun y : EN (m + 1) => zcoord T j y - u j (tupleDeriv (Tsh T μ hμne) y)) y
        = (Complex.I / 2) • ((fderiv ℝ (zcoord T j) y).comp (J y - Submission.stdOf T y))
      rw [Submission.dbar_sub J _ _ y hzd hud]
      rw [Work.NN.Core.dbar_zcoord_eq J j y, Work.NN.Core.dbarPert_perturbation]
      have hzero : Submission.dbar J
          (fun y : EN (m + 1) => u j (tupleDeriv (Tsh T μ hμne) y)) y = 0 := by
        rw [dbar_comp_tupleDeriv J (Tsh T μ hμne) (u j) y]
        rw [show Jtr J (Tsh T μ hμne) = JstdCn (m + 1) + Atr J (Tsh T μ hμne) from
          (Jstd_add_Atr_Tsh J T μ hμne).symm]
        rw [hu.2.1 j (tupleDeriv (Tsh T μ hμne) y) hy]
        rfl
      rw [hzero, sub_zero]
    · -- invertibility of the differential
      intro y hy
      have hud : ∀ j : Fin (m + 1),
          DifferentiableAt ℝ (u j) (tupleDeriv (Tsh T μ hμne) y) := fun j =>
        ((hu.1 j).contDiffAt (hVopen.mem_nhds hy)).differentiableAt (by simp)
      have hfun : (fun y : EN (m + 1) => fun j : Fin (m + 1) => zcoord T j y -
            (zcoord T j y - u j (tupleDeriv (Tsh T μ hμne) y)))
          = (fun y : EN (m + 1) => fun j : Fin (m + 1) =>
              u j (tupleDeriv (Tsh T μ hμne) y)) := by
        funext y j
        ring
      rw [hfun, fderiv_tuple_comp_tupleDeriv hud]
      exact (hu.2.2 (tupleDeriv (Tsh T μ hμne) y) hy).comp
        (bijective_tupleDeriv (Tsh T μ hμne))

end

end Work.NN.Final
