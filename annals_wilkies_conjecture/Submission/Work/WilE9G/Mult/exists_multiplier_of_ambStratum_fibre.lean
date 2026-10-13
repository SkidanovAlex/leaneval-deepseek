/-
  WilE9G.Mult — the "fibre multiplier" (KKT) statement for an ambient stratum.

  Main theorem: if `z ∈ S.X.set` is a *local* maximiser of an EA-function `χ` on the fibre of
  the base projection `π_n` through `z`, and the base projection is submersive along `S` at `z`
  (so that `(π_n, h) : ℝ^N → ℝ^n × ℝ^{S.j}` is submersive at `z`), then the fibre-derivatives of
  `χ` at `z` are a linear combination (with coefficients `μ` independent of the fibre direction
  `l`) of the fibre-derivatives of the equations `h a`.

  The mathematics is Lagrange multipliers for the constraint system `(h a = 0, π_n = π_n z)`;
  the constraint qualification is `S.Good` (the Jacobian of `h` has rank `S.j`) together with
  `S.IsBaseSubmersiveAt` (`π_n` maps `ker dh` onto `ℝ^n`), which together make the combined
  differential surjective.
-/
import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.Strat.hasStrictFDerivAt_eaEval
import Submission.Work.WilE9G.Mult.exists_multiplier_of_isLocalExtrOn_levelSet
import Submission.Work.WilE9G.Mult.surjective_pi_of_rank_eq_card
import Submission.Work.WilE9G.Mult.exists_of_surjective_of_forall_proj

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped Topology

namespace Work.WilE9G.Mult

open WilkiesDesign WilkiesDesign.E

/-! ## Elementary API for the base projection -/

/-- The projection to the first `n` coordinates, as a continuous linear map. -/
def projBaseCLM {N n : ℕ} (hn : n ≤ N) : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj (Fin.castLE hn i))

theorem projBaseCLM_apply {N n : ℕ} (hn : n ≤ N) (v : Fin N → ℝ) :
    projBaseCLM hn v = projBase hn v := by
  funext i
  rw [projBaseCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
  rfl

/-- The base coordinate `π_n(·) i`, shifted by a constant, is strictly differentiable with
derivative the `i`-th coordinate projection. -/
theorem hasStrictFDerivAt_projBase_apply {N n : ℕ} (hn : n ≤ N) (i : Fin n) (c : ℝ)
    (z : Fin N → ℝ) :
    HasStrictFDerivAt (fun w : Fin N → ℝ => projBase hn w i - c)
      ((ContinuousLinearMap.proj (Fin.castLE hn i) : (Fin N → ℝ) →L[ℝ] ℝ)) z := by
  have h : (fun w : Fin N → ℝ => projBase hn w i - c)
      = fun w => (ContinuousLinearMap.proj (Fin.castLE hn i) : (Fin N → ℝ) →L[ℝ] ℝ) w - c := by
    funext w; rfl
  rw [h]
  exact (ContinuousLinearMap.hasStrictFDerivAt _).sub_const c

/-- A base coordinate vanishes on the standard basis vector of a fibre direction. -/
theorem proj_apply_single_natAdd {n m : ℕ} (i : Fin n) (l : Fin m) :
    (ContinuousLinearMap.proj (Fin.castLE (Nat.le_add_right n m) i) :
        (Fin (n + m) → ℝ) →L[ℝ] ℝ) (Pi.single (Fin.natAdd n l) 1) = 0 := by
  rw [ContinuousLinearMap.proj_apply]
  refine Pi.single_eq_of_ne (i := Fin.natAdd n l) (i' := Fin.castLE (Nat.le_add_right n m) i) ?_ 1
  intro h
  have hval : (Fin.castLE (Nat.le_add_right n m) i).val = (Fin.natAdd n l).val := by rw [h]
  rw [Fin.val_castLE, Fin.val_natAdd] at hval
  omega

/-! ## The main theorem -/

theorem exists_multiplier_of_ambStratum_fibre {n m : ℕ}
    (S : Work.WilE9G.AmbStratum (n + (1 + m))) (hS : S.Good)
    (z : Fin (n + (1 + m)) → ℝ) (hz : z ∈ S.X.set)
    (hsub : Work.WilE9G.AmbStratum.IsBaseSubmersiveAt S (Nat.le_add_right n (1 + m)) z)
    (χ : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (hmax : ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin (n + (1 + m)) → ℝ, dist w z < ε → w ∈ S.X.set →
      Work.WilE9G.projBase (Nat.le_add_right n (1 + m)) w
        = Work.WilE9G.projBase (Nat.le_add_right n (1 + m)) z →
      WilkiesDesign.E.eaEval S.X.c χ w ≤ WilkiesDesign.E.eaEval S.X.c χ z) :
    ∃ μ : Fin S.j → ℝ, ∀ l : Fin (1 + m),
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c (Fin.natAdd n l) χ) z
        = ∑ a, μ a * WilkiesDesign.E.eaEval S.X.c
            (WilkiesDesign.E.eaD S.X.c (Fin.natAdd n l) (S.h a)) z := by
  classical
  -- The equations vanish at `z`, since `z` lies on the stratum.
  have hz0 : ∀ a, eaEval S.X.c (S.h a) z = 0 := AmbStratum_eq_zero S hS hz
  -- `X.set` is locally the zero set of the equations, with an explicit radius.
  obtain ⟨ε₁, hε₁pos, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ w : Fin (n + (1 + m)) → ℝ,
      dist w z < ε₁ → (∀ a, eaEval S.X.c (S.h a) w = 0) → w ∈ S.X.set := by
    have hl := AmbStratum_locality S hS hz
    rw [Metric.eventually_nhds_iff] at hl
    exact hl
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := hmax
  have hεpos : 0 < min ε₀ ε₁ := lt_min hε₀pos hε₁pos
  -- The constraint system: the equations `h a` and the `n` base coordinates, shifted by `π_n z`.
  let G : Fin S.j ⊕ Fin n → (Fin (n + (1 + m)) → ℝ) → ℝ := Sum.elim
      (fun a w => eaEval S.X.c (S.h a) w)
      (fun i w => projBase (Nat.le_add_right n (1 + m)) w i
        - projBase (Nat.le_add_right n (1 + m)) z i)
  -- The symbolic derivative of the equations.
  let A : Fin S.j → (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ := fun a =>
      ∑ l : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c l (S.h a)) z •
        (ContinuousLinearMap.proj l : (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ)
  let P : (Fin (n + (1 + m)) → ℝ) →L[ℝ] (Fin n → ℝ) := projBaseCLM (Nat.le_add_right n (1 + m))
  -- The derivatives of the constraints.
  let f' : Fin S.j ⊕ Fin n → (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ := Sum.elim A
      (fun i : Fin n => (ContinuousLinearMap.proj (Fin.castLE (Nat.le_add_right n (1 + m)) i) :
        (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ))
  -- The symbolically differentiated `χ`.
  let φ' : (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ :=
      ∑ l : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c l χ) z •
        (ContinuousLinearMap.proj l : (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ)
  -- Strict differentiability of the constraints.
  have hf' : ∀ b : Fin S.j ⊕ Fin n, HasStrictFDerivAt (G b) (f' b) z := by
    intro b
    rcases b with a | i
    · have h := Work.Strat.hasStrictFDerivAt_eaEval S.X.c (S.h a) z
      simpa only [G, f', A, Sum.elim_inl] using h
    · have h := hasStrictFDerivAt_projBase_apply (Nat.le_add_right n (1 + m)) i
          (projBase (Nat.le_add_right n (1 + m)) z i) z
      simpa only [G, f', Sum.elim_inr] using h
  -- `z` is a local maximiser of `χ` on the common level set of the constraints.
  have hloc : IsLocalExtrOn (fun w : Fin (n + (1 + m)) → ℝ => eaEval S.X.c χ w)
      {y | ∀ b : Fin S.j ⊕ Fin n, G b y = G b z} z := by
    refine Or.inr ?_
    show ∀ᶠ y in 𝓝[{y : Fin (n + (1 + m)) → ℝ |
        ∀ b : Fin S.j ⊕ Fin n, G b y = G b z}] z,
      eaEval S.X.c χ y ≤ eaEval S.X.c χ z
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds z hεpos] with y hy hyl
    have hy' : dist y z < min ε₀ ε₁ := by simpa [Metric.mem_ball] using hy
    have hbase : projBase (Nat.le_add_right n (1 + m)) y
        = projBase (Nat.le_add_right n (1 + m)) z := by
      funext i
      have h2 := hyl (Sum.inr i)
      simp only [G, Sum.elim_inr] at h2
      linarith
    have hh0 : ∀ a, eaEval S.X.c (S.h a) y = 0 := by
      intro a
      have h2 := hyl (Sum.inl a)
      simp only [G, Sum.elim_inl] at h2
      rw [hz0 a] at h2
      exact h2
    exact hε₀ y (lt_of_lt_of_le hy' (min_le_left _ _))
      (hε₁ y (lt_of_lt_of_le hy' (min_le_right _ _)) hh0) hbase
  have hφstrict : HasStrictFDerivAt (fun w : Fin (n + (1 + m)) → ℝ => eaEval S.X.c χ w) φ' z :=
    Work.Strat.hasStrictFDerivAt_eaEval S.X.c χ z
  -- The Jacobian of the equations has full rank, so `d h` is surjective.
  have hAsurj : Function.Surjective (ContinuousLinearMap.pi A) := by
    have hrank : (Matrix.of (fun a : Fin S.j => fun l : Fin (n + (1 + m)) =>
        eaEval S.X.c (eaD S.X.c l (S.h a)) z)).rank = S.j := AmbStratum_rank S hS hz
    have := surjective_pi_of_rank_eq_card
      (fun a : Fin S.j => fun l : Fin (n + (1 + m)) => eaEval S.X.c (eaD S.X.c l (S.h a)) z) hrank
    simpa only [A] using this
  -- Base-submersivity: `π_n` maps `ker dh` onto `ℝ^n`.
  have hcond : ∀ w : Fin n → ℝ, ∃ v : Fin (n + (1 + m)) → ℝ,
      P v = w ∧ ContinuousLinearMap.pi A v = 0 := by
    intro w
    obtain ⟨v, hv, hv0⟩ := hsub w
    refine ⟨v, ?_, ?_⟩
    · have hPv : P v = projBase (Nat.le_add_right n (1 + m)) v :=
        projBaseCLM_apply (Nat.le_add_right n (1 + m)) v
      rw [hPv]
      exact hv
    · funext a
      show A a v = 0
      have hfa := (Work.Strat.hasStrictFDerivAt_eaEval S.X.c (S.h a) z).hasFDerivAt.fderiv
      have hthis : (∑ l : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c l (S.h a)) z •
          (ContinuousLinearMap.proj l : (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ)) v = 0 := by
        rw [← hfa]
        exact hv0 a
      exact hthis
  -- Hence the combined differential of the constraints is surjective.
  have hsurj : Function.Surjective (fun v : Fin (n + (1 + m)) → ℝ =>
      fun b : Fin S.j ⊕ Fin n => f' b v) := by
    intro φ
    obtain ⟨v, hvP, hvD⟩ := exists_of_surjective_of_forall_proj P (ContinuousLinearMap.pi A)
      hAsurj hcond (fun i => φ (Sum.inr i)) (fun a => φ (Sum.inl a))
    refine ⟨v, ?_⟩
    funext b
    rcases b with a | i
    · show f' (Sum.inl a) v = φ (Sum.inl a)
      have h1 : f' (Sum.inl a) = A a := rfl
      rw [h1]
      exact congrFun hvD a
    · show f' (Sum.inr i) v = φ (Sum.inr i)
      have h1 : f' (Sum.inr i) v = P v i := by
        simp only [f', P, projBaseCLM, Sum.elim_inr, ContinuousLinearMap.pi_apply,
          ContinuousLinearMap.proj_apply]
      rw [h1, hvP]
  -- Lagrange multipliers for the constraint system.
  obtain ⟨c, hc⟩ := exists_multiplier_of_isLocalExtrOn_levelSet hloc hf' hφstrict hsurj
  refine ⟨fun a => c (Sum.inl a), fun l => ?_⟩
  have h1 := hc (Pi.single (Fin.natAdd n l) 1)
  rw [Fintype.sum_sum_type] at h1
  have hL : φ' (Pi.single (Fin.natAdd n l) 1)
      = eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) χ) z :=
    Work.WilE5.Strat.sum_smul_proj_single (fun i => eaEval S.X.c (eaD S.X.c i χ) z)
      (Fin.natAdd n l)
  rw [hL] at h1
  have hfirst : (∑ a : Fin S.j, c (Sum.inl a) * f' (Sum.inl a) (Pi.single (Fin.natAdd n l) 1))
      = ∑ a : Fin S.j,
          c (Sum.inl a) * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    have h2 : f' (Sum.inl a) (Pi.single (Fin.natAdd n l) 1)
        = eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z := by
      show (∑ i : Fin (n + (1 + m)), eaEval S.X.c (eaD S.X.c i (S.h a)) z •
          (ContinuousLinearMap.proj i : (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ))
            (Pi.single (Fin.natAdd n l) 1) = _
      exact Work.WilE5.Strat.sum_smul_proj_single
        (fun i => eaEval S.X.c (eaD S.X.c i (S.h a)) z) (Fin.natAdd n l)
    exact h2
  have hsecond : (∑ i : Fin n, c (Sum.inr i) * f' (Sum.inr i) (Pi.single (Fin.natAdd n l) 1))
      = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h2 : f' (Sum.inr i) (Pi.single (Fin.natAdd n l) 1) = 0 := by
      show (ContinuousLinearMap.proj (Fin.castLE (Nat.le_add_right n (1 + m)) i) :
          (Fin (n + (1 + m)) → ℝ) →L[ℝ] ℝ) (Pi.single (Fin.natAdd n l) 1) = 0
      exact proj_apply_single_natAdd i l
    rw [h2, mul_zero]
  rw [hfirst, hsecond, add_zero] at h1
  exact h1

end Work.WilE9G.Mult
