import Submission.Grassmann.SwitchStep
import Submission.Grassmann.UpperBound

/-!
# Step (E) of §8 of arXiv:2209.04243: the induction step assembled

This file continues `SwitchStep.lean`.  The remaining chain of the induction step is:

1. apply the induction hypothesis `IHyp C (d-1)` to `DopXq … T f` (its degree is `d - |t|` by
   `degLe_DopXq`);
2. bound the resulting sum over `(V₄,W₄)` by the switching sum (`sum_D4_DopXq_le`);
3. sum over the shift `T` and identify the result with `q^{mn} · l4q (L_{P_t}[f])`;
4. reindex the double sum.

Steps 1 and 2 are carried out here.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The kernel and the range of the section of a triple -/

/-- The kernel of the map `X` of a triple is the preimage of the section `trW₁ t`. -/
theorem ker_section (t : Triple m n) :
    LinearMap.ker t.2.2 = Submodule.comap t.2.1.subtype (trW₁ t) := by
  rw [trW₁, Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]

/-- The range of the map `X` of a triple is the coordinate image of the section `trV₁ t`. -/
theorem range_section (t : Triple m n) :
    LinearMap.range t.2.2 = Submodule.map (Submodule.mkQ t.1) (trV₁ t) := by
  rw [trV₁, Submodule.map_comap_eq, Submodule.range_mkQ, top_inf_eq]

/-! ## The finrank bookkeeping of a triple -/

/-- The dimension of the coordinate space `Wco W₂ W₁` of a section is the dimension of the
kernel of `X`. -/
theorem finrank_Wco_section (t : Triple m n) :
    Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) = Module.finrank 𝔽₂ (LinearMap.ker t.2.2) := by
  rw [Wco, ← ker_section t]
  exact LinearEquiv.finrank_map_eq (ecW t.2.1).symm _

/-- The dimension of the coordinate space `Vco V₂ V₁` of a section is the rank of `X`. -/
theorem finrank_Vco_section (t : Triple m n) :
    Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)) = Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
  rw [Vco, ← range_section t]
  exact LinearEquiv.finrank_map_eq (Qe t.1) _

/-- Rank–nullity for the map `X` of a triple. -/
theorem finrank_W2_eq (t : Triple m n) :
    Module.finrank 𝔽₂ t.2.1 =
      Module.finrank 𝔽₂ (LinearMap.ker t.2.2) + Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
  have h := LinearMap.finrank_range_add_finrank_ker t.2.2
  omega

/-- The complement dimension `dim W₂ - dim Wco W₂ W₁` of a section is the rank of `X`. -/
theorem finrank_W2_sub_Wco_section (t : Triple m n) :
    Module.finrank 𝔽₂ t.2.1 - Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) =
      Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
  rw [finrank_Wco_section, finrank_W2_eq t]
  omega

/-! ## Step 1: the induction hypothesis applied to `DopXq` -/

/-- **The induction hypothesis applied to the `X`-derivative**: for `DegLe d f`, the function
`DopXq … T f` has degree `≤ d - |t|` and hence satisfies the induction hypothesis at level
`d - |t|`. -/
theorem l4q_DopXq_le_IHyp {C D d : ℕ} (hIH : IHyp C D) {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (hD : d - totOrder t ≤ D) :
    l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f) ≤
      (2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
        ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
            Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂),
          ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂),
            (if Module.finrank 𝔽₂ V₄ +
                (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) - Module.finrank 𝔽₂ W₄) ≤
                d - totOrder t
              then D4 V₄ W₄ (Lsub V₄ W₄ (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f))
              else 0) :=
  hIH _ _ _ _ hD (degLe_DopXq hf (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T
    (trV₁_ge t) (trW₁_le t) (ker_section t) (range_section t))

/-! ## Step 2: the `(V₄,W₄)`-sum bounded by the switching sum -/

/-- The inner switching sum of `stepD_bound_le`. -/
abbrev SwInner (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ∑ S : Matrix (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))))
        (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))) 𝔽₂,
    ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
        Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
      (l2sq (SwitchSummandS (Vco t.1 (trV₁ t)) (Wco t.2.1 (trW₁ t))
        (liftV (Vco t.1 (trV₁ t)) V₄) (liftW (Wco t.2.1 (trW₁ t)) W₄) p.1 p.2
        (XtOf t.1 t.2.1 t.2.2)
        (0 + Ip (Wco t.2.1 (trW₁ t)) * S * Qp (Vco t.1 (trV₁ t)))
        (Dop0S t.1 t.2.1 T f))) ^ 2

lemma SwInner_nonneg (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    0 ≤ SwInner t V₄ W₄ T f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The `(V₄,W₄)`-guard of the switching sum, with an explicit type signature so that lambdas
over it elaborate with the intended domain. -/
abbrev SwGuard (t : Triple m n) (d : ℕ) :
    Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂) →
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂) → Prop :=
  fun V₄ W₄ => Module.finrank 𝔽₂ V₄ +
    (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) - Module.finrank 𝔽₂ W₄) ≤ d

/-- The switching sum with the `(V₄,W₄)`-guard at level `d`. -/
def SwSum (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ V₄, ∑ W₄, (if SwGuard t d V₄ W₄ then SwInner t V₄ W₄ T f else 0)

lemma SwSum_nonneg (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : 0 ≤ SwSum t T f d := by
  unfold SwSum
  exact Finset.sum_nonneg fun V₄ _ => Finset.sum_nonneg fun W₄ _ => by
    split
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    · exact le_refl 0

/-- The switching sum grows with the guard. -/
lemma SwSum_mono (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {d₀ d : ℕ} (h : d₀ ≤ d) :
    SwSum t T f d₀ ≤ SwSum t T f d := by
  unfold SwSum
  refine Finset.sum_le_sum fun V₄ _ => Finset.sum_le_sum fun W₄ _ => ?_
  by_cases hg : SwGuard t d₀ V₄ W₄
  · rw [if_pos hg, if_pos (by rw [SwGuard] at hg ⊢; omega)]
  · rw [if_neg hg]
    split
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    · exact le_refl 0

/-- A constant can be pulled out of a guarded double sum. -/
lemma sum_ite_mul_const {α β : Type*} [Fintype α] [Fintype β] (p : α → β → Prop)
    [DecidableRel p] (c : ℝ) (F : α → β → ℝ) :
    (∑ a, ∑ b, (if p a b then c * F a b else 0)) =
      c * ∑ a, ∑ b, (if p a b then F a b else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : p a b <;> simp [h]

/-- **Steps 1+2, sharpened**: the `L⁴`-norm of the `X`-derivative is bounded by the induction
hypothesis, applied at degree `d - |t|`, followed by the switching step.  The Cauchy–Schwarz
factor of the switching step is the *sharp* `2 ^ (3 d · rank (XtOf t))` (see
`SwitchStep.stepD_bound_le_rank`), which is what makes the constant bookkeeping of the induction
close. -/
theorem l4q_DopXq_le_SwSum_rank {C d : ℕ} (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) (t : Triple m n)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (ht1 : 1 ≤ totOrder t) (htd : totOrder t ≤ d) :
    l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f) ≤
      (2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
        ((((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) *
            ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))))⁻¹) *
          ((2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank) * SwSum t T f d)) := by
  have hXker : LinearMap.ker (XtOf t.1 t.2.1 t.2.2).mulVecLin = Wco t.2.1 (trW₁ t) := by
    rw [ker_XtOf, ker_section t, Wco]
  have hXrange : LinearMap.range (XtOf t.1 t.2.1 t.2.2).mulVecLin = Vco t.1 (trV₁ t) := by
    rw [range_XtOf, range_section t, Vco]
  have hstep1 : (∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂),
      ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂),
        (if Module.finrank 𝔽₂ V₄ +
            (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) - Module.finrank 𝔽₂ W₄) ≤
            d - totOrder t
          then D4 V₄ W₄ (Lsub V₄ W₄ (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f))
          else 0)) ≤
      ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂),
      ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂),
        (if Module.finrank 𝔽₂ V₄ +
            (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) - Module.finrank 𝔽₂ W₄) ≤ d
          then D4 V₄ W₄ (Lsub V₄ W₄ (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f))
          else 0) := by
    refine Finset.sum_le_sum (fun V₄ _ => Finset.sum_le_sum (fun W₄ _ => ?_))
    by_cases hg : Module.finrank 𝔽₂ V₄ +
        (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) - Module.finrank 𝔽₂ W₄) ≤ d - totOrder t
    · rw [if_pos hg, if_pos (by omega)]
    · rw [if_neg hg]
      split
      · exact D4_nonneg _ _ _
      · exact le_refl 0
  have hstep2 := sum_D4_DopXq_le_rank (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f (trV₁_ge t)
    (trW₁_le t) hXker hXrange d
  have hfac : (∑ V₄, ∑ W₄, (if SwGuard t d V₄ W₄ then
        (((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) *
            ((n - Module.finrank 𝔽₂ t.1) -
              Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))))⁻¹) *
          ((2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank) * SwInner t V₄ W₄ T f)
        else 0)) =
      (((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) *
          ((n - Module.finrank 𝔽₂ t.1) -
            Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))))⁻¹) *
        ((2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank) * SwSum t T f d) := by
    rw [sum_ite_mul_const (SwGuard t d)
      (((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) *
          ((n - Module.finrank 𝔽₂ t.1) -
            Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))))⁻¹)
      (fun V₄ W₄ => (2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank) * SwInner t V₄ W₄ T f)]
    congr 1
    unfold SwSum
    exact sum_ite_mul_const (SwGuard t d) ((2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank))
      (fun V₄ W₄ => SwInner t V₄ W₄ T f)
  refine (l4q_DopXq_le_IHyp hIH hf t T (by omega)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hstep1.trans (hstep2.trans (le_of_eq hfac))


/-- **Steps 1–3 combined, sharpened**. -/
theorem sum_l4q_DopXq_le_SwSum_rank {C d : ℕ} (hIH : IHyp C (d - 1))
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) (t : Triple m n)
    (ht1 : 1 ≤ totOrder t) (htd : totOrder t ≤ d) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) ≤
      (2 : ℝ) ^ (C * (d - totOrder t) ^ 2) *
        ((((2 : ℝ) ^ (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t)) *
            ((n - Module.finrank 𝔽₂ t.1) -
              Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))))⁻¹) *
          ((2 : ℝ) ^ (3 * d * (XtOf t.1 t.2.1 t.2.2).rank) *
            ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, SwSum t T f d)) := by
  refine (Finset.sum_le_sum (fun T _ => l4q_DopXq_le_SwSum_rank hIH hf t T ht1 htd)).trans ?_
  exact le_of_eq (by simp only [Finset.mul_sum])

/-! ## Step 3: summing over the shift -/

/-- **Step 3**: summing `l4q (DopXq … T f)` over the shift `T` gives `q^{mn}` times the fourth
moment of the big-space multiplier `L_{XtPred t}`. -/
theorem sum_l4q_DopXq_eq (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        l4q (DopXq (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) =
      (2 : ℝ) ^ (m * n) * l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) := by
  rw [Finset.sum_congr rfl (fun T _ =>
    l4q_DopXq_eq_DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f (trV₁_ge t) (trW₁_le t))]
  exact sum_l4q_DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 f (trV₁_ge t) (trW₁_le t)

end

end Submission.Grassmann
