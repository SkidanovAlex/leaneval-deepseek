import Submission.Grassmann.SwCollapse

/-!
# The role-space form of the switching sum (arXiv:2209.04243, §8)

This file keeps the switching sum in its *role-space* form, with the `Σ_{T'}` inside, so that the
**sharp** corollary `XNormSum.sum_inv_pow_sq_l2sq_plLE_le`
(`Σ_X q^{-4d·rank X}(l2sq (L_X h))² ≤ 2 (l2sq h)²`, no `q^{4d²}` loss) can be applied *after* the
reindexing of the sum by `(t,p) ↦ (V₃,W₃,XsOf t p)`.

* `DopRole X h = restr (Qp (range X)) (Ip (ker X)) (L_X h)` — the role-space `X`-derivative;
* `SwTermRole t p f` — a switching summand with the `Σ_{T'}` and the role-space derivative;
* `SwTerm_eq_SwTermRole` — the two forms agree on the `Fr`-locus;
* `SwRoleSum t f d` and `SwSumP_eq_SwRoleSum` — `SwSumP` in role-space form;
* **`l4q_lapMulN_le_swRole_rank`** — the per-triple bound of §8 with *all* normalising constants
  cancelling, the sharp switching factor `2 ^ (3 d · rank X)`, and the `Σ_{T'}` kept:
  `l4q (L_{XtPred t} (Lsub t.1 t.2.1 f)) ≤ q^{-mn} · 2 ^ (C (d - S)²) · q^{-M'N'} ·
     2 ^ (3 d · rank X) · SwRoleSum t f d`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The role-space form of the switching sum (keeping the `T'`-sum)

The lossy step "bound a single summand by `2 ^ (4 d²) · 2 (l2sq h)²`" of `SwTerm_le` throws away
the `Σ_{T'}` and, worse, is only valid with an extra `2 ^ (4 d²)` that the constant bookkeeping of
the induction cannot absorb.  Instead we keep the switching sum in its *role-space* form, so that
`XNormSum.sum_inv_pow_sq_l2sq_plLE_le` (the **sharp** `Σ_X q^{-4d·rank X}(l2sq (L_X h))² ≤ 2 (l2sq h)²`)
can be applied *after* the reindexing.
-/

/-- The role-space restricted `X`-derivative `D_X h = restr (Qp (range X)) (Ip (ker X)) (L_X h)`. -/
noncomputable def DopRole {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ (LinearMap.ker X.mulVecLin)))
      (Fin (n - Module.finrank 𝔽₂ (LinearMap.range X.mulVecLin))) 𝔽₂ → ℂ :=
  restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
    (lapMulN (plLE X) h)

/-- The role-space form of a switching summand. -/
noncomputable def SwTermRole {m n : ℕ} (t : Triple m n) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
      ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
    ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
      (l2sq (DopRole (XsOf t p)
        (Dop0S (liftV t.1 p.1) (liftW t.2.1 p.2) T' f))) ^ 2

set_option maxHeartbeats 100000000 in
/-- **The switching summand equals its role-space form.** -/
theorem SwTerm_eq_SwTermRole (t : Triple m n) (p : QPair m n t)
    (hp : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    SwTerm t (pV t p) (pW t p) p f = SwTermRole t p f := by
  rw [SwTerm, SwTermRole, liftV_pV t p, liftW_pW t p]
  congr 1
  refine Finset.sum_congr rfl (fun T' _ => ?_)
  rw [l2sq_restr_eq_DopRole t p hp.1 hp.2 T' f, DopRole, XrR_eq, XrK_eq]

/-- The switching sum in role-space form. -/
def SwRoleSum (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ p : QPair m n t,
    (if p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤ then
      (if SwGuard t d (pV t p) (pW t p) then SwTermRole t p f else 0) else 0)

/-- **`SwSumP` is its role-space form.** -/
theorem SwSumP_eq_SwRoleSum (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    SwSumP t f d = SwRoleSum t f d := by
  unfold SwSumP SwRoleSum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : p.1 ⊓ VrOf t = ⊥ ∧ p.2 ⊔ WrOf t = ⊤
  · rw [if_pos hp, if_pos hp]
    by_cases hg : SwGuard t d (pV t p) (pW t p)
    · rw [if_pos hg, if_pos hg, SwTerm_eq_SwTermRole t p hp f]
    · rw [if_neg hg, if_neg hg]
  · rw [if_neg hp, if_neg hp]

/-- **The per-triple bound in role-space form** (all normalising constants cancelling, the sharp
`2 ^ (3 d · rank X)` switching factor, and the `Σ_{T'}` kept). -/
theorem l4q_lapMulN_le_swRole_rank (t : Triple m n) {C d : ℕ} (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (ht1 : 1 ≤ totOrder t) (htd : totOrder t ≤ d) :
    l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) ≤
      ((2 : ℝ) ^ (m * n))⁻¹ *
        ((2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
          (((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
              ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
            ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
              SwRoleSum t f d))) := by
  have hSw : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, SwSum t T f d) = SwRoleSum t f d :=
    ((Finset.sum_congr rfl (fun T _ => SwSum_eq_SwColl t T f d)).trans
      ((sum_SwColl_eq_SwFinal t f d).trans (SwFinal_eq_SwSumP t f d))).trans
      (SwSumP_eq_SwRoleSum t f d)
  have hmain := sum_l4q_DopXq_le_SwSum_rank (C := C) (d := d) hIH hf t ht1 htd
  rw [rank_XtOf t.1 t.2.1 t.2.2] at hmain
  rw [hSw] at hmain
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (m * n) := by positivity
  calc l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))
      = ((2 : ℝ) ^ (m * n))⁻¹ *
          ((2 : ℝ) ^ (m * n) * l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ = ((2 : ℝ) ^ (m * n))⁻¹ *
          (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) := by
        rw [sum_l4q_DopXq_eq]
    _ ≤ ((2 : ℝ) ^ (m * n))⁻¹ *
          ((2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
            (((2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
                ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))))⁻¹ *
              ((2 : ℝ) ^ (3 * d * Module.finrank 𝔽₂ (LinearMap.range t.2.2)) *
                SwRoleSum t f d))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
end
end Submission.Grassmann
