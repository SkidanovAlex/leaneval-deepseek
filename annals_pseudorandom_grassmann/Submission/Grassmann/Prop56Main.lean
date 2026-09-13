import Submission.Grassmann.TransposeBS
import Submission.Commons.LinearAlgebra.Matrix.sum_comp_mul_mul_add

/-!
# Proposition 5.6 of arXiv:2209.04243: the induction

This file assembles the proof that restriction-globalness implies small generalised influences
(Proposition 5.6).  The two analytic ingredients (`globalBS_restr_TOp`, `inflBS2_mul_reduction`)
live in `Submission.Grassmann.Prop56`; the duality reducing the `codim W₁` direction to the
`dim V₁` direction lives in `Submission.Grassmann.TransposeBS`.  Here we supply

* the "peeling" of a line from `ker Q` (`exists_factor_of_ker_ne_bot`);
* the isometry `l2sq (restr Q ι (shift T g)) = l2sq g` when `ker Q = ⊥` and `range ι = ⊤`;
* the resulting strong induction on `d`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Peeling a line off `ker Q` -/

/-- **Peeling a line off the kernel of `Q`.**  If `Q` has nontrivial kernel there is a
factorisation `Q = Q₂ * Q₁` where `Q₁` is surjective with one-dimensional kernel
`span {v}`, `v ≠ 0`. -/
lemma exists_factor_of_ker_ne_bot {n n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (h : LinearMap.ker Q.mulVecLin ≠ ⊥) :
    ∃ (n'' : ℕ) (Q₁ : Matrix (Fin n'') (Fin n) 𝔽₂) (Q₂ : Matrix (Fin n') (Fin n'') 𝔽₂)
      (v : Fin n → 𝔽₂), v ≠ 0 ∧ Q = Q₂ * Q₁ ∧
        LinearMap.range Q₁.mulVecLin = ⊤ ∧
        LinearMap.ker Q₁.mulVecLin = Submodule.span 𝔽₂ {v} := by
  classical
  obtain ⟨v, hvm, hv⟩ : ∃ v ∈ LinearMap.ker Q.mulVecLin, v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Submodule.eq_bot_iff _ |>.mpr (fun x hx => by
      by_contra hx0
      exact hx0 (hc x hx)))
  set p : Submodule 𝔽₂ (Fin n → 𝔽₂) := Submodule.span 𝔽₂ {v} with hp
  have hfin : Module.finrank 𝔽₂ ↥p = 1 := by rw [hp]; exact finrank_span_singleton hv
  have hle : p ≤ LinearMap.ker Q.mulVecLin := by
    rw [hp]
    exact (Submodule.span_singleton_le_iff_mem v _).mpr hvm
  have hdim : Module.finrank 𝔽₂ ((Fin n → 𝔽₂) ⧸ p) =
      Module.finrank 𝔽₂ (Fin (n - 1) → 𝔽₂) := by
    have h1 := Submodule.finrank_quotient_add_finrank p
    rw [show Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n from Module.finrank_fin_fun (ZMod 2)] at h1
    rw [hfin, add_comm] at h1
    have h2 : Module.finrank 𝔽₂ (Fin (n - 1) → 𝔽₂) = n - 1 := Module.finrank_fin_fun (ZMod 2)
    rw [h2]
    omega
  let e : ((Fin n → 𝔽₂) ⧸ p) ≃ₗ[𝔽₂] (Fin (n - 1) → 𝔽₂) := LinearEquiv.ofFinrankEq _ _ hdim
  have hQ1 : (LinearMap.toMatrix' (e.toLinearMap.comp p.mkQ)
      : Matrix (Fin (n - 1)) (Fin n) 𝔽₂).mulVecLin = e.toLinearMap.comp p.mkQ := by
    rw [← Matrix.toLin'_apply']; exact toLin'_toMatrix' _
  have hQ2 : (LinearMap.toMatrix'
      ((p.liftQ Q.mulVecLin hle).comp e.symm.toLinearMap)
      : Matrix (Fin n') (Fin (n - 1)) 𝔽₂).mulVecLin =
      (p.liftQ Q.mulVecLin hle).comp e.symm.toLinearMap := by
    rw [← Matrix.toLin'_apply']; exact toLin'_toMatrix' _
  refine ⟨n - 1, LinearMap.toMatrix' (e.toLinearMap.comp p.mkQ),
    LinearMap.toMatrix' ((p.liftQ Q.mulVecLin hle).comp e.symm.toLinearMap), v, hv, ?_, ?_, ?_⟩
  · refine Matrix.toLin'.injective ?_
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_mul, hQ1, hQ2]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.liftQ_apply, Submodule.mkQ_apply]
  · rw [hQ1, LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective p (e.symm y)
    refine ⟨x, ?_⟩
    rw [LinearMap.comp_apply, hx]
    exact e.apply_symm_apply y
  · rw [hQ1, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

/-! ## The isometry at order zero -/

/-- **Restriction of order zero is an isometry for the normalised `L²` norm.**  When `Q` is
injective and `ι` is surjective, the affine map `A ↦ ι * A * Q + T` is a uniform covering with
`2^{m'n'-mn}`-element fibres, so restricting does not change `‖·‖₂²`. -/
theorem l2sq_restr_shift_eq_of_order_zero {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = ⊥) (hι : LinearMap.range ι.mulVecLin = ⊤)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr Q ι (shift T g)) = l2sq g := by
  classical
  have hQinj : Function.Injective Q.mulVecLin := by
    rw [← LinearMap.ker_eq_bot]; exact hQ
  have hιsurj : Function.Surjective ι.mulVecLin := by
    rw [← LinearMap.range_eq_top]; exact hι
  have hmm : m ≤ m' := by
    have h1 : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) = m := by
      rw [hι, finrank_top, Module.finrank_fin_fun]
    have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) ≤ m' := by
      rw [show Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) = ι.rank from rfl]
      exact Matrix.rank_le_width ι
    omega
  have hnn : n ≤ n' := by
    have h0 : Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) = 0 := by
      rw [hQ]; simp
    have h1 : Module.finrank 𝔽₂ ↥(LinearMap.range Q.mulVecLin) = n := by
      have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      rw [Module.finrank_fin_fun, h0, add_zero] at h
      exact h
    have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range Q.mulVecLin) ≤ n' := by
      rw [show Module.finrank 𝔽₂ ↥(LinearMap.range Q.mulVecLin) = Q.rank from rfl]
      exact Matrix.rank_le_height Q
    omega
  have hsum : (∑ A : Matrix (Fin m') (Fin n') 𝔽₂, ‖g (ι * A * Q + T)‖ ^ 2) =
      ((2 : ℝ) ^ (m' * n' - m * n)) *
        ∑ B : Matrix (Fin m) (Fin n) 𝔽₂, ‖g B‖ ^ 2 := by
    have h := Commons.LinearAlgebra.Matrix.sum_comp_mul_mul_add Q ι hQinj hιsurj T
      (fun B : Matrix (Fin m) (Fin n) 𝔽₂ => ‖g B‖ ^ 2)
    simpa using h
  rw [l2sq, l2sq]
  simp only [restr, shift]
  rw [hsum]
  have hle_mn : m * n ≤ m' * n' := Nat.mul_le_mul hmm hnn
  have hpow : (2 : ℝ) ^ (m' * n') =
      (2 : ℝ) ^ (m * n) * (2 : ℝ) ^ (m' * n' - m * n) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, mul_inv]
  field_simp

/-! ## The total mass is bounded by globalness -/

lemma l2sq_le_of_GlobalBS {m n : ℕ} (d : ℕ) {ε : ℝ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : GlobalBS d ε f) : l2sq f ≤ ε := by
  have hn : Module.finrank 𝔽₂ ↥(LinearMap.ker (1 : Matrix (Fin n) (Fin n) 𝔽₂).mulVecLin) = 0 := by
    rw [Matrix.mulVecLin_one, LinearMap.ker_id]; simp
  have h0 : hybridOrder (1 : Matrix (Fin n) (Fin n) 𝔽₂) (1 : Matrix (Fin m) (Fin m) 𝔽₂) = 0 := by
    rw [hybridOrder_one, hn]
  have h00 : hybridOrder (1 : Matrix (Fin n) (Fin n) 𝔽₂) (1 : Matrix (Fin m) (Fin m) 𝔽₂) ≤ d := by
    rw [h0]; exact Nat.zero_le d
  have h := hf (Q := (1 : Matrix (Fin n) (Fin n) 𝔽₂)) (ι := (1 : Matrix (Fin m) (Fin m) 𝔽₂)) h00 0
  rwa [show restr (1 : Matrix (Fin n) (Fin n) 𝔽₂) (1 : Matrix (Fin m) (Fin m) 𝔽₂)
    (shift 0 f) = f from by
      funext A; simp only [restr, shift, Matrix.one_mul, Matrix.mul_one, add_zero]] at h

/-! ## The constant and the induction -/

/-- The constant of Proposition 5.6: `C d = 100^d · 2^{2d(d+1)} = q^{10d²}` for `q = 2`
(asymptotically). -/
def C (d : ℕ) : ℝ := 100 ^ d * 2 ^ (2 * d * (d + 1))

lemma one_le_C (d : ℕ) : (1 : ℝ) ≤ C d := by
  have h1 : (1 : ℝ) ≤ 100 ^ d := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * d * (d + 1)) := one_le_pow₀ (by norm_num)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 100 ^ d * (2 : ℝ) ^ (2 * d * (d + 1)) := by
        exact mul_le_mul h1 h2 (by norm_num) (by positivity)
    _ = C d := rfl

lemma C_rec {d : ℕ} (hd : 1 ≤ d) : C d = C (d - 1) * 100 * (2 : ℝ) ^ (4 * d) := by
  have key : (2 * d * (d + 1) : ℕ) = 2 * (d - 1) * ((d - 1) + 1) + 4 * d := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.sub_add_cancel hd).symm⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hp : (2 : ℝ) ^ (2 * d * (d + 1)) =
      (2 : ℝ) ^ (2 * (d - 1) * ((d - 1) + 1)) * (2 : ℝ) ^ (4 * d) := by
    rw [← pow_add]
    exact congrArg _ key
  have h100 : (100 : ℝ) ^ d = 100 ^ (d - 1) * 100 := by
    conv_lhs => rw [show d = (d - 1) + 1 from (Nat.sub_add_cancel hd).symm]
    rw [pow_succ]
  rw [C, C, hp, h100]
  ring

/-- **Proposition 5.6 of arXiv:2209.04243.**  A `(d,ε)`-restriction global function `f` has
small generalised influences on its level-`d` part: for every pair `(V₁,W₁)` of order at most
`d` and every shift `T`, `I_{V₁,W₁,T}[f^{=d}] ≤ C d · ε`. -/
theorem prop_5_6 : ∀ d : ℕ, ∀ (ε : ℝ), 0 ≤ ε →
    ∀ (m n : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ),
      GlobalBS d ε f → SmallInfl d (C d * ε) (nprojPure d f) := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih ε hε m n f hf m' n' Q ι T hord
  rcases Nat.eq_zero_or_pos (hybridOrder Q ι) with hc | hc
  · -- the order is zero: restriction is an isometry
    have hker : LinearMap.ker Q.mulVecLin = ⊥ := by
      have h := hc
      rw [hybridOrder] at h
      exact Submodule.finrank_eq_zero.mp (by omega)
    have htop : LinearMap.range ι.mulVecLin = ⊤ := by
      have h := hc
      rw [hybridOrder] at h
      have h0 : Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) = 0 := by omega
      have hle : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) ≤ m := by
        have := Submodule.finrank_le (LinearMap.range ι.mulVecLin)
        rwa [Module.finrank_fin_fun] at this
      have h1 : Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) = m := by omega
      exact Submodule.eq_top_of_finrank_eq (by
        rw [show Module.finrank 𝔽₂ (Fin m → 𝔽₂) = m from Module.finrank_fin_fun (ZMod 2)]
        exact h1)
    have hpred : hybridPred Q ι = fun _ : Matrix (Fin n) (Fin m) 𝔽₂ => True := by
      funext X
      refine propext ⟨fun _ => trivial, fun _ => ?_⟩
      exact ⟨by rw [hker]; exact bot_le,
        fun u _ => by rw [htop]; exact Submodule.mem_top⟩
    rw [inflBS2, hpred, lapMulN_top,
      l2sq_restr_shift_eq_of_order_zero Q ι hker htop T (nprojPure d f)]
    have h2 : l2sq (nprojPure d f) ≤ ε :=
      (l2sq_nprojPure_le d f).trans (l2sq_le_of_GlobalBS d hf)
    calc l2sq (nprojPure d f) ≤ ε := h2
      _ ≤ C d * ε := by
          have h1 := one_le_C d
          nlinarith [hε, h1]
  · have hd1 : 1 ≤ d := le_trans hc hord
    have hε' : 0 ≤ 100 * (2 : ℝ) ^ (4 * d) * ε := by positivity
    by_cases hQb : LinearMap.ker Q.mulVecLin = ⊥
    · -- `V₁ = 0`: transpose and peel a line in the transposed space
      have hne : LinearMap.ker (Matrix.mulVecLin ιᵀ) ≠ ⊥ := by
        intro h0
        have hzero : Module.finrank 𝔽₂ ↥(LinearMap.ker (Matrix.mulVecLin ιᵀ)) = 0 := by
          rw [h0]; simp
        have hQtop : Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ)) = n := by
          have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
          rw [show Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n from Module.finrank_fin_fun (ZMod 2),
            hQb] at h
          simp only [finrank_bot, add_zero] at h
          rw [show Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ)) =
            Module.finrank 𝔽₂ ↥(LinearMap.range Q.mulVecLin) from Matrix.rank_transpose Q]
          exact h
        have h1 : hybridOrder (Matrix.transpose ι) (Matrix.transpose Q) = 0 := by
          rw [show hybridOrder (Matrix.transpose ι) (Matrix.transpose Q) =
              Module.finrank 𝔽₂ ↥(LinearMap.ker (Matrix.mulVecLin ιᵀ)) +
                (n - Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ))) from rfl,
            hzero, hQtop]
          simp
        have h2 : hybridOrder (Matrix.transpose ι) (Matrix.transpose Q) = hybridOrder Q ι :=
          hybridOrder_transpose Q ι
        omega
      obtain ⟨n'', Q₁, Q₂, v, hv, hfac, hrange, hker⟩ :=
        exists_factor_of_ker_ne_bot (Matrix.transpose ι) hne
      have hf' : GlobalBS d ε (transposeFun f) := (GlobalBS_transpose f).mp hf
      let F : Matrix (Fin n) (Fin n'') 𝔽₂ → ℂ :=
        restr Q₁ (1 : Matrix (Fin n) (Fin n) 𝔽₂)
          (shift (Matrix.transpose T) (TOp v d (transposeFun f)))
      have hg : GlobalBS (d - 1) (100 * (2 : ℝ) ^ (4 * d) * ε) F :=
        globalBS_restr_TOp hε hf' hd1 Q₁ v hv hker hrange (Matrix.transpose T)
      have hord₂ : hybridOrder Q₂ (Matrix.transpose Q) ≤ d - 1 := by
        have h1 : hybridOrder (Q₂ * Q₁) (Matrix.transpose Q) =
            hybridOrder Q₁ (1 : Matrix (Fin n) (Fin n) 𝔽₂) + hybridOrder Q₂ (Matrix.transpose Q) :=
          hybridOrder_mul Q₁ Q₂ (Matrix.transpose Q) hrange
        rw [hybridOrder_one Q₁, hker, finrank_span_singleton hv] at h1
        have h2 : hybridOrder (Q₂ * Q₁) (Matrix.transpose Q) = hybridOrder Q ι := by
          rw [← hfac, hybridOrder_transpose Q ι]
        omega
      have hIH : SmallInfl (d - 1) (C (d - 1) * (100 * (2 : ℝ) ^ (4 * d) * ε))
          (nprojPure (d - 1) F) :=
        ih (d - 1) (by omega) (100 * (2 : ℝ) ^ (4 * d) * ε) hε' n n'' F hg
      have hred := hIH (Q := Q₂) (ι := Matrix.transpose Q) 0 hord₂
      rw [inflBS2_transpose Q ι T f, hfac,
        inflBS2_mul_reduction Q₁ Q₂ (Matrix.transpose Q) hv hker hrange d hd1
          (Matrix.transpose T) (transposeFun f)]
      refine hred.trans (le_of_eq ?_)
      rw [C_rec hd1]; ring
    · -- `dim V₁ ≥ 1`: peel a line off `ker Q`
      obtain ⟨n'', Q₁, Q₂, v, hv, hfac, hrange, hker⟩ := exists_factor_of_ker_ne_bot Q hQb
      have hord₂ : hybridOrder Q₂ ι ≤ d - 1 := by
        have h1 : hybridOrder (Q₂ * Q₁) ι =
            hybridOrder Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) + hybridOrder Q₂ ι :=
          hybridOrder_mul Q₁ Q₂ ι hrange
        rw [hybridOrder_one Q₁, hker, finrank_span_singleton hv] at h1
        have h2 : hybridOrder (Q₂ * Q₁) ι = hybridOrder Q ι := by rw [← hfac]
        omega
      let F : Matrix (Fin m) (Fin n'') 𝔽₂ → ℂ :=
        restr Q₁ (1 : Matrix (Fin m) (Fin m) 𝔽₂) (shift T (TOp v d f))
      have hg : GlobalBS (d - 1) (100 * (2 : ℝ) ^ (4 * d) * ε) F :=
        globalBS_restr_TOp hε hf hd1 Q₁ v hv hker hrange T
      have hIH : SmallInfl (d - 1) (C (d - 1) * (100 * (2 : ℝ) ^ (4 * d) * ε))
          (nprojPure (d - 1) F) :=
        ih (d - 1) (by omega) (100 * (2 : ℝ) ^ (4 * d) * ε) hε' m n'' F hg
      have hred := hIH (Q := Q₂) (ι := ι) 0 hord₂
      rw [hfac, inflBS2_mul_reduction Q₁ Q₂ ι hv hker hrange d hd1 T f]
      refine hred.trans (le_of_eq ?_)
      rw [C_rec hd1]; ring

end

end Submission.Grassmann
