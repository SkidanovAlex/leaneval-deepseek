import Submission.Work.PTGeometric.RieszProj.Symm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rank count for the Riesz projection

If `S` is self-adjoint and within `1/4` of a rank-`k` orthogonal projection `P`, then exactly `k`
eigenvalues of `S` (with multiplicity) lie in the top cluster, i.e. `topCard S hSsym hn = k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open scoped ContDiff InnerProduct
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-- Multiplication in the endomorphism ring is composition. -/
lemma end_mul_apply {f g : Amb n →ₗ[ℝ] Amb n} (x : Amb n) : (f * g) x = f (g x) := by
  rw [Module.End.mul_eq_comp, LinearMap.comp_apply]

/-- **The rank count.**  If `S` is self-adjoint and `‖S - P‖ < 1/4` for a rank-`k` orthogonal
projection `P`, then `S` has exactly `k` eigenvalues in the top cluster. -/
lemma topCard_eq {S P : EndOp n}
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hn : Module.finrank ℝ (Amb n) = n)
    (hP : P ∈ Gr n k) (h : ‖S - P‖ < 1/4) : topCard S hSsym hn = k := by
  have hCl : Cluster S := Cluster.of_dist hP h
  set Φ : Amb n →ₗ[ℝ] Amb n := (Phi S : Amb n →ₗ[ℝ] Amb n) with hΦ
  -- Idempotency of `Φ`.
  have hΦself : ∀ y : Amb n, Φ (Φ y) = Φ y := by
    intro y
    have h1 : (Phi S * Phi S : EndOp n) y = (Phi S : EndOp n) y := by
      rw [Phi_mul_self hSsym hCl hn]
    rw [ContinuousLinearMap.mul_apply] at h1
    exact h1
  have hΦidem : Φ * Φ = Φ := by
    refine LinearMap.ext fun y => ?_
    rw [end_mul_apply]
    exact hΦself y
  -- Idempotency of `P`.
  have hPself : ∀ y : Amb n, (P : Amb n →ₗ[ℝ] Amb n) ((P : Amb n →ₗ[ℝ] Amb n) y)
      = (P : Amb n →ₗ[ℝ] Amb n) y := by
    intro y
    have h1 : (P * P : EndOp n) y = (P : EndOp n) y := by rw [hP.2.1]
    rw [ContinuousLinearMap.mul_apply] at h1
    exact h1
  have hPidem : (P : Amb n →ₗ[ℝ] Amb n) * (P : Amb n →ₗ[ℝ] Amb n)
      = (P : Amb n →ₗ[ℝ] Amb n) := by
    refine LinearMap.ext fun y => ?_
    rw [end_mul_apply]
    exact hPself y
  -- `finrank (range P) = k`.
  have hPfin : Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) = k := by
    have hp : LinearMap.IsProj (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n))
        (P : Amb n →ₗ[ℝ] Amb n) :=
      (LinearMap.isProj_range_iff_isIdempotentElem _).mpr hPidem
    have h1 : LinearMap.trace ℝ (Amb n) (P : Amb n →ₗ[ℝ] Amb n)
        = (Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hp.trace
    have h2 : LinearMap.trace ℝ (Amb n) (P : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hP.2.2
    have h3 : (Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
      rw [← h1, h2]
    exact Nat.cast_injective h3
  -- `finrank (range Φ) = topCard`.
  have htopfin : Module.finrank ℝ (LinearMap.range Φ) = topCard S hSsym hn := by
    have hp : LinearMap.IsProj (LinearMap.range Φ) Φ :=
      (LinearMap.isProj_range_iff_isIdempotentElem _).mpr hΦidem
    have h1 : LinearMap.trace ℝ (Amb n) Φ = (Module.finrank ℝ (LinearMap.range Φ) : ℝ) :=
      hp.trace
    have h2 : LinearMap.trace ℝ (Amb n) Φ = (topCard S hSsym hn : ℝ) := by
      rw [hΦ]
      exact trace_Phi_eq_topCard hSsym hCl hn
    have h3 : (Module.finrank ℝ (LinearMap.range Φ) : ℝ) = (topCard S hSsym hn : ℝ) := by
      rw [← h1, h2]
    exact Nat.cast_injective h3
  -- On `range Φ` the quadratic form of `S` is at least `3/4`.
  have hΦself' : ∀ x ∈ LinearMap.range Φ, Phi S x = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact hΦself y
  have hquarter : ∀ x ∈ LinearMap.range Φ, inner ℝ ((S - P) x) x ≤ ‖S - P‖ * ‖x‖ ^ 2 := by
    intro x _
    calc inner ℝ ((S - P) x) x ≤ ‖(S - P) x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖S - P‖ * ‖x‖) * ‖x‖ := by
          gcongr
          exact (S - P).le_opNorm x
      _ = ‖S - P‖ * ‖x‖ ^ 2 := by ring
  have hsplit : ∀ x : Amb n, inner ℝ (S x) x
      = inner ℝ (P x) x + inner ℝ ((S - P) x) x := by
    intro x
    have hv : P x + (S - P) x = S x := by rw [sub_apply]; abel
    rw [← hv, inner_add_left]
  -- `P` is injective on `range Φ`.
  have hPne : ∀ x ∈ LinearMap.range Φ, P x = 0 → x = 0 := by
    intro x hx hPx
    by_contra hx0
    have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h7 : inner ℝ (S x) x < (1/4) * ‖x‖ ^ 2 := by
      rw [hsplit x, hPx, inner_zero_left, zero_add]
      calc inner ℝ ((S - P) x) x ≤ ‖S - P‖ * ‖x‖ ^ 2 := hquarter x hx
        _ < (1/4) * ‖x‖ ^ 2 := by nlinarith [h, hpos]
    have h8 := three_quarters_mul_le_of_Phi_eq_self hSsym hCl hn (hΦself' x hx)
    nlinarith [h7, h8, hpos]
  have hle1 : Module.finrank ℝ (LinearMap.range Φ) ≤ k := by
    set Ψ : (LinearMap.range Φ) →ₗ[ℝ] Amb n :=
      (P : Amb n →ₗ[ℝ] Amb n).comp (LinearMap.range Φ).subtype with hΨ
    have hinj : Function.Injective Ψ := by
      intro x y hxy
      have hxy' : P (x : Amb n) = P (y : Amb n) := hxy
      have hsub : (x : Amb n) - (y : Amb n) ∈ LinearMap.range Φ := sub_mem x.2 y.2
      have hzero : P ((x : Amb n) - (y : Amb n)) = 0 := by rw [map_sub, hxy', sub_self]
      exact Subtype.ext (sub_eq_zero.mp (hPne _ hsub hzero))
    have hker : LinearMap.ker Ψ = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    have h1 : Module.finrank ℝ (LinearMap.range Ψ) = Module.finrank ℝ (LinearMap.range Φ) := by
      have h3 := LinearMap.finrank_range_add_finrank_ker Ψ
      rw [hker, finrank_bot, add_zero] at h3
      exact h3
    have h2 : LinearMap.range Ψ ≤ LinearMap.range (P : Amb n →ₗ[ℝ] Amb n) := by
      rintro y ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    calc Module.finrank ℝ (LinearMap.range Φ) = Module.finrank ℝ (LinearMap.range Ψ) := h1.symm
      _ ≤ Module.finrank ℝ (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)) :=
          Submodule.finrank_mono h2
      _ = k := hPfin
  -- `1 - P` is injective on `ker Φ`.
  have hKne : ∀ x ∈ LinearMap.ker Φ, x ≠ 0 → ((1 : EndOp n) - P) x ≠ 0 := by
    intro x hx hx0 hzero
    have hΦx : Phi S x = 0 := hx
    have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h8 : inner ℝ (S x) x ≤ (1/4) * ‖x‖ ^ 2 :=
      le_quarter_mul_of_Phi_eq_zero hSsym hCl hn hΦx
    have h10 : -(‖S - P‖ * ‖x‖ ^ 2) ≤ inner ℝ ((S - P) x) x := by
      have habs := abs_real_inner_le_norm ((S - P) x) x
      have h11 : ‖(S - P) x‖ ≤ ‖S - P‖ * ‖x‖ := (S - P).le_opNorm x
      have h12 : ‖(S - P) x‖ * ‖x‖ ≤ ‖S - P‖ * ‖x‖ ^ 2 := by
        calc ‖(S - P) x‖ * ‖x‖ ≤ (‖S - P‖ * ‖x‖) * ‖x‖ := by gcongr
          _ = ‖S - P‖ * ‖x‖ ^ 2 := by ring
      rw [abs_le] at habs
      linarith [habs.1, h12]
    have hlt : inner ℝ (P x) x < (1/2) * ‖x‖ ^ 2 := by
      rw [hsplit x] at h8
      nlinarith [h8, h10, h, hpos]
    have hnorm : ‖((1 : EndOp n) - P) x‖ ^ 2 = ‖x‖ ^ 2 - inner ℝ (P x) x := by
      have h1 : ((1 : EndOp n) - P) x = x - P x := by rw [sub_apply, one_apply_eq_self]
      have h2 : inner ℝ x (P x) = inner ℝ (P x) x := real_inner_comm (P x) x
      have h3 : inner ℝ (P x) x = ‖P x‖ ^ 2 := inner_P_eq_norm_sq hP x
      rw [h1, norm_sub_sq_real, h2, h3]
      ring
    have hpos2 : 0 < ‖((1 : EndOp n) - P) x‖ ^ 2 := by rw [hnorm]; linarith
    rw [hzero, norm_zero] at hpos2
    norm_num at hpos2
  have hle2 : Module.finrank ℝ (LinearMap.ker Φ) ≤ n - k := by
    set Ω : (LinearMap.ker Φ) →ₗ[ℝ] Amb n :=
      (((1 : EndOp n) - P : EndOp n) : Amb n →ₗ[ℝ] Amb n).comp
        (LinearMap.ker Φ).subtype with hΩ
    have hinj : Function.Injective Ω := by
      intro x y hxy
      have hxy' : ((1 : EndOp n) - P) (x : Amb n) = ((1 : EndOp n) - P) (y : Amb n) := hxy
      have hsub : (x : Amb n) - (y : Amb n) ∈ LinearMap.ker Φ := sub_mem x.2 y.2
      have hzero : ((1 : EndOp n) - P) ((x : Amb n) - (y : Amb n)) = 0 := by
        rw [map_sub, hxy', sub_self]
      by_contra hne
      exact hKne _ hsub (sub_ne_zero.mpr (fun hc => hne (Subtype.ext hc))) hzero
    have hker : LinearMap.ker Ω = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    have h1 : Module.finrank ℝ (LinearMap.range Ω) = Module.finrank ℝ (LinearMap.ker Φ) := by
      have h3 := LinearMap.finrank_range_add_finrank_ker Ω
      rw [hker, finrank_bot, add_zero] at h3
      exact h3
    have h2 : LinearMap.range Ω ≤ LinearMap.ker (P : Amb n →ₗ[ℝ] Amb n) := by
      rintro y ⟨x, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      have h1 : Ω x = ((1 : EndOp n) - P) (x : Amb n) := by
        rw [hΩ]
        rfl
      rw [h1]
      show (P : EndOp n) (((1 : EndOp n) - P) (x : Amb n)) = 0
      rw [sub_apply, one_apply_eq_self]
      show (P : EndOp n) ((x : Amb n) - P (x : Amb n)) = 0
      rw [map_sub, ← ContinuousLinearMap.mul_apply, hP.2.1, sub_self]
    have hkerP : Module.finrank ℝ (LinearMap.ker (P : Amb n →ₗ[ℝ] Amb n)) = n - k := by
      have h3 := LinearMap.finrank_range_add_finrank_ker (P : Amb n →ₗ[ℝ] Amb n)
      rw [hPfin, hn] at h3
      omega
    calc Module.finrank ℝ (LinearMap.ker Φ) = Module.finrank ℝ (LinearMap.range Ω) := h1.symm
      _ ≤ Module.finrank ℝ (LinearMap.ker (P : Amb n →ₗ[ℝ] Amb n)) := Submodule.finrank_mono h2
      _ = n - k := hkerP
  -- Assemble.
  have h3 : Module.finrank ℝ (LinearMap.range Φ) + Module.finrank ℝ (LinearMap.ker Φ) = n := by
    have h4 := LinearMap.finrank_range_add_finrank_ker Φ
    rwa [hn] at h4
  have hkn : k ≤ n := by
    have h4 := (LinearMap.range (P : Amb n →ₗ[ℝ] Amb n)).finrank_le
    rw [hPfin, hn] at h4
    exact h4
  have h4 : Module.finrank ℝ (LinearMap.range Φ) = k := by omega
  omega

end

end Work.PTGeometric
