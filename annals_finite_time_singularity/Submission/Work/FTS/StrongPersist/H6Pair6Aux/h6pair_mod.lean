import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N0_zero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Pair6Aux.h6pair_mod` — the modulation bound `|muDyn| ≤ K α^{-10}(1+M)^4`

`muDyn α Φ g τ = Construction.mufunS α (N0 α F f) (N α F Φ) f` with `f = slice g τ`,
`Φ = slice Φ τ`, `F = F_* + f` (`Ftau`), and

  `mufunS α N0v Nv g = (1/(2α))·(L₁₂(N0v)(0) + L₁₂(Nv)(0)) + (1/(2α))·L₁₂(3 D_θg/(1+z))(0)`

(`Construction/Defs.lean:205`, `Construction/MufunS.lean:65`).  Hence `muDyn` is bounded by
`(1/(2α))` times the *three zero-mode estimates* of the paper's Proposition `muestimate`
(tex 1508–1526), evaluated at the slice `f` and the elliptic solution `Ψ = slice Φ τ`:

* the transport zero mode `|L₁₂(3 D_θ f/(1+z))(0)| ≤ C |f|_{ℋ⁴}`, which is
  `StrongPersist.L3Aux.Transport_L12_zero_le`, *already proved* in this area (a ∂_θ-integration
  by parts plus weighted Cauchy–Schwarz; no elliptic input);
* the `N₀` zero mode `|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K α^{-9}(1+M)⁴` (`h6pair_N0_zero`, the
  level-six analogue of the *proved* level-four row `Nonlinear.Pieces.rl0_bound`; `N₀` involves
  `F_*` and `f` only);
* the `N` zero mode `|L₁₂(N α (F_*+f) Ψ)(0)| ≤ K α^{-9}(1+M)⁴` (`h6pair_N_zero`), which is the
  half carrying the elliptic residual `PhiTil α F Ψ`.

The assembly below (`h6pair_mod_of_pieces`) is pure bookkeeping: the triangle inequality, the
`Xn α f ≤ M` datum of `L6Ctx`, and the arithmetic
`(1/(2α))·(CA·M + (KN0+KN)·α^{-9}(1+M)⁴) ≤ K α^{-10}(1+M)⁴` (using `M α^9 ≤ (1+M)⁴` for
`M ≥ 0`, `α ≤ 1`).

See `H6Pair6Aux/NOTES_H6Pair6Aux_route.md` for the route, the level-four analogues and the exact
interface input that the `N`-half consumes.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn Fam slice muDyn)

noncomputable section

/-- The transport zero mode `|L₁₂(3 D_θf/(1+z))(0)| ≤ C|f|_{ℋ⁴}` in the exact spelling of the
`muDyn` decomposition: this is `L3Aux.Transport_L12_zero_le` with
`Coercivity.Transport f = 3 D_θf/(1+z)` and `Coercivity.L12f = Construction.L12` unfolded. -/
theorem transport_zero_le' : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn),
    0 < α → α ≤ 1 → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  refine ⟨C, hC, fun α f hα hα1 hm => ?_⟩
  have := h α f hα hα1 hm
  simpa only [Work.Coercivity.Transport, Work.Coercivity.L12f, Work.Construction.L12,
    Work.FM.L12, Work.FM.L12dens, Work.Elliptic.L12, Work.Elliptic.L12dens] using this

/-- **The modulation bound from the three zero-mode estimates.**  This is the whole `muDyn`
argument: the decomposition `mufunS = (1/(2α))(L₁₂N₀ + L₁₂N) + (1/(2α))L₁₂(Transport)`, the
triangle inequality, and the arithmetic of the `α`-powers. -/
theorem h6pair_mod_of_pieces (Ce : ℝ)
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn),
      0 < α → α ≤ 1 → Work.Spaces.HkMem α 4 f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ C * Work.FTS.Nonlin.Xn α f)
    (hN0 : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        |Work.Construction.L12 (Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) 0|
          ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
    (hN : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Fn) (M Cs : ℝ) (E : Fn → Fn),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        Ell6Ctx α Ce Cs E Φs f Ψ →
        |Work.Construction.L12 (Work.Construction.N α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
          ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :
    ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Fam) (τ M Cs : ℝ)
        (E : Fn → Fn) (Φs : Fn), 0 ≤ τ →
        L6Ctx (IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        |muDyn α Φ g τ| ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by
  obtain ⟨CA, hCA0, hA'⟩ := hA
  obtain ⟨KN0, αN0, hKN00, hαN00, hN0'⟩ := hN0
  obtain ⟨KN, αN, hKN0, hαN0, hN'⟩ := hN
  refine ⟨(CA + KN0 + KN + 1) / 2, min 1 (min αN0 αN), by positivity,
    lt_min one_pos (lt_min hαN00 hαN0), ?_⟩
  intro α hαle g Φ τ M Cs E Φs hτ hctx
  have hα : 0 < α := hαle.1
  have hα1 : α ≤ 1 := le_trans hαle.2 (min_le_left _ _)
  have hαN0le : α ≤ αN0 := le_trans hαle.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hαNle : α ≤ αN := le_trans hαle.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαN0mem : α ∈ Set.Ioc 0 αN0 := ⟨hα, hαN0le⟩
  have hαNmem : α ∈ Set.Ioc 0 αN := ⟨hα, hαNle⟩
  -- the data supplied by `L6Ctx`
  have hreg := hctx.hreg
  have hsm6 : Work.FTS.EllipticEst.SmoothOpen (slice g τ) := hreg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 (slice g τ) := hreg.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 (slice g τ) :=
    Work.FTS.StrongPersist.HkMem_four_of_six hsm6 hmem6
  have hbdd := hctx.hbdd
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 (slice g τ)) hbdd
  -- the three zero-mode bounds
  have hbA : |Work.Construction.L12
      (fun z θ => 3 * Work.Spaces.Dth (slice g τ) z θ / (1 + z)) 0| ≤ CA * M := by
    refine le_trans (hA' α (slice g τ) hα hα1 hmem4) ?_
    exact mul_le_mul_of_nonneg_left hbdd hCA0.le
  have hbN0 : |Work.Construction.L12 (Work.Construction.N0 α
      (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0|
      ≤ KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 :=
    hN0' α hαN0mem (slice g τ) M hreg hctx.h7 hbdd
  have hbN : |Work.Construction.L12 (Work.Construction.N α
      (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0|
      ≤ KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 :=
    hN' α hαNmem (slice g τ) (slice Φ τ) Φs M Cs E hreg hctx.h7 hbdd hctx.hell
  -- unfold `muDyn`
  have hmu : muDyn α Φ g τ
      = (1 / (2 * α)) * (Work.Construction.L12 (Work.Construction.N0 α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0
            + Work.Construction.L12 (Work.Construction.N α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0)
        + (1 / (2 * α)) * Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth (slice g τ) z θ / (1 + z)) 0 := rfl
  rw [hmu]
  -- the triangle inequality
  have hpos : (0 : ℝ) < 1 / (2 * α) := by positivity
  have htri : |(1 / (2 * α)) * (Work.Construction.L12 (Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0
          + Work.Construction.L12 (Work.Construction.N α
            (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0)
      + (1 / (2 * α)) * Work.Construction.L12
          (fun z θ => 3 * Work.Spaces.Dth (slice g τ) z θ / (1 + z)) 0|
      ≤ (1 / (2 * α)) * (CA * M + KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : |(1 / (2 * α)) * (Work.Construction.L12 (Work.Construction.N0 α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0
            + Work.Construction.L12 (Work.Construction.N α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0)|
        ≤ (1 / (2 * α)) * (KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
            + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
      rw [abs_mul, abs_of_pos hpos]
      refine mul_le_mul_of_nonneg_left ?_ hpos.le
      linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0)
            (Work.Construction.L12 (Work.Construction.N α
              (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0),
        hbN0, hbN]
    have h2 : |(1 / (2 * α)) * Work.Construction.L12
          (fun z θ => 3 * Work.Spaces.Dth (slice g τ) z θ / (1 + z)) 0|
        ≤ (1 / (2 * α)) * (CA * M) := by
      rw [abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left hbA hpos.le
    have h3 := abs_add_le ((1 / (2 * α)) * (Work.Construction.L12 (Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice g τ)) 0
          + Work.Construction.L12 (Work.Construction.N α
            (fun z θ => Work.Construction.Fstar α z θ + slice g τ z θ) (slice Φ τ)) 0))
        ((1 / (2 * α)) * Work.Construction.L12
          (fun z θ => 3 * Work.Spaces.Dth (slice g τ) z θ / (1 + z)) 0)
    have hexp : (1 / (2 * α)) * (KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
            + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
        + (1 / (2 * α)) * (CA * M)
        = (1 / (2 * α)) * (CA * M + KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
            + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
    linarith [h3, h1, h2, hexp.le, hexp.ge]
  -- the arithmetic
  refine le_trans htri ?_
  have hαinv : (1 : ℝ) / (2 * α) = (1 / 2) * α ^ (-(1 : ℝ)) := by
    rw [div_eq_mul_inv, Real.rpow_neg_one]; ring
  have hpow : α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ)) = α ^ (-(10 : ℝ)) := by
    rw [← Real.rpow_add hα]; norm_num
  have hα9 : α ^ (9 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
  have hMle : M ≤ (1 + M) ^ 4 := by nlinarith [hM0, sq_nonneg (1 + M), sq_nonneg M]
  have hkey : M * α ^ (9 : ℝ) ≤ (1 + M) ^ 4 := by
    calc M * α ^ (9 : ℝ) ≤ M * 1 := mul_le_mul_of_nonneg_left hα9 hM0
      _ = M := mul_one M
      _ ≤ (1 + M) ^ 4 := hMle
  have hnine : α ^ (-(9 : ℝ)) * (M * α ^ (9 : ℝ)) = M := by
    rw [mul_comm M (α ^ (9 : ℝ)), ← mul_assoc, ← Real.rpow_add hα,
      show (-(9 : ℝ)) + (9 : ℝ) = 0 by norm_num, Real.rpow_zero, one_mul]
  have hAterm : α ^ (-(1 : ℝ)) * M ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by
    have h1 : M ≤ α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
      calc M = α ^ (-(9 : ℝ)) * (M * α ^ (9 : ℝ)) := hnine.symm
        _ ≤ α ^ (-(9 : ℝ)) * (1 + M) ^ 4 :=
            mul_le_mul_of_nonneg_left hkey (Real.rpow_pos_of_pos hα _).le
    calc α ^ (-(1 : ℝ)) * M ≤ α ^ (-(1 : ℝ)) * (α ^ (-(9 : ℝ)) * (1 + M) ^ 4) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hα _).le
      _ = α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by rw [← mul_assoc, hpow]
  have hstepA : (1 / (2 * α)) * (CA * M) ≤ (CA / 2) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : (1 / (2 * α)) * (CA * M) = (CA / 2) * (α ^ (-(1 : ℝ)) * M) := by
      rw [hαinv]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hAterm (by positivity)
  have hstepB : (1 / (2 * α)) * (KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
      = (KN0 / 2) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : (1 / (2 * α)) * (KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
        = (KN0 / 2) * ((α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ))) * (1 + M) ^ 4) := by
      rw [hαinv]; ring
    rw [h1, hpow]
  have hstepC : (1 / (2 * α)) * (KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
      = (KN / 2) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4) := by
    have h1 : (1 / (2 * α)) * (KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
        = (KN / 2) * ((α ^ (-(1 : ℝ)) * α ^ (-(9 : ℝ))) * (1 + M) ^ 4) := by
      rw [hαinv]; ring
    rw [h1, hpow]
  have hnn : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := by
    have h1 : (0 : ℝ) < α ^ (-(10 : ℝ)) := Real.rpow_pos_of_pos hα _
    have h2 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
    exact mul_nonneg h1.le h2
  have hfin : (1 / (2 * α)) * (CA * M + KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
        + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
      ≤ ((CA + KN0 + KN + 1) / 2) * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4) := by
    have hexp : (1 / (2 * α)) * (CA * M + KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4
          + KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
        = (1 / (2 * α)) * (CA * M) + (1 / (2 * α)) * (KN0 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4)
          + (1 / (2 * α)) * (KN * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by ring
    rw [hexp, hstepB, hstepC]
    linarith [hstepA, hnn]
  refine le_trans hfin (le_of_eq ?_)
  ring

/-- **The modulation bound at level six** (the `muDyn` bound consumed by `H6Pair6`): for data in
`L6Ctx` the modulation constant is at most `K α^{-10}(1+M)^4`, where `M` bounds the `ℋ⁴`-norm of
the slice.  Proved from the three zero-mode estimates of the paper's `prop:muestimate`. -/
theorem h6pair_mod (Ce : ℝ) (hCe : 0 < Ce) : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      |Work.FTS.Galerkin.muDyn α Φ g τ| ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 :=
  h6pair_mod_of_pieces Ce transport_zero_le' h6pair_N0_zero (h6pair_N_zero Ce hCe)

end

end Work.FTS.StrongPersist.H6Pair6Aux
