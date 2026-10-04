import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE
import Submission.Work.Diff.STE.B3.Rper_eq_perPhi_perMat
import Submission.Work.Diff.STE.B3.VarCoef.CPair_chart_term_eq_periodised
import Submission.Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp
import Submission.Work.Diff.STE.B3.VarCoef.POp_adjoint_L2re
import Submission.Work.Diff.STE.B3.VarCoef.cutOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.varLapOp_preserves
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.VarCoefAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart term of the commutator pairing in the `XOp`/`pairP` vocabulary

The chart term of the pair estimate is the difference of component pairings

  `CPair_l (S_l (R_l f), R_l (Q u)) − CPair_l (S_l (R_l (Q f)), R_l u)`,

where `S_l = STruncR ρ ε` is the Friedrichs cutoff of the localised component `R_l`.

`VarCoef.CPair_chart_term_eq_periodised` rewrites it in the flat vocabulary,

  `Σ_{ab} L2re (Rper_l f a b) (flatCut ρ ε (Rper_l (Q u) a b)) − Σ_{ab} L2re (Rper_l (Q f) a b) (flatCut ρ ε (Rper_l u a b))`,

and `VarCoef.Rper_Qk_eq_perPhi_POp` gives the chart-`l` expansion of `Rper_l (Q_k h)`,
`Rper_l (Q_k h) = perPhi · Σ_{icd} (co_l i a b c d) · varLapPow_k (A_i, B_i) (Σ_{c'd'} (ci_l i c d c' d') · perMat_l h)`.

The present file performs the *last* bookkeeping step: writing the two periodised pairings in the
form in which the flat commutation estimates of the `VarCoef` layer consume them, namely as

  `Σ_α Σ_β ⟨perMat_l f α, XOp (perPhiR_l) (cutOp ρ ε) (pairP_αβ (perMat_l u β))⟩`,

where `XOp ψ S = M_ψ ∘ S ∘ M_ψ` is the cutoff sandwich and `pairP_αβ` is the scalar operator
`Σ_{icd} POp (ci i c d β) (co i α c d) (varLapOp (A i, B i)) k` of the chart expression.

The mathematical content is exactly two applications of the *self-adjointness of a real multiplier*
`L2re (M_ψ x) y = L2re x (M_ψ y)` (`VarCoef.mulOp_L2re_adjoint`) together with the additivity of
`L2re` and of the Friedrichs cutoff over finite sums; the chart expansion is turned into the
`pairP` form by the linearity of `varLapPow` over finite sums of smooth periodic functions.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Elementary manipulations of finite sums -/

/-- `∑ x : κ₁ × κ₂, G x = ∑ a, ∑ b, G (a, b)`.  This moves between the iterated sums of the chart
computation and the sums over the product index `α : Fin n × Fin n` of the target. -/
theorem sum_univ_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] {R : Type*} [AddCommMonoid R]
    (G : κ₁ × κ₂ → R) : (∑ x : κ₁ × κ₂, G x) = ∑ a, ∑ b, G (a, b) := by
  rw [← Finset.univ_product_univ (α := κ₁) (β := κ₂), Finset.sum_product]

/-- Multiplication by a fixed coefficient commutes with a finite sum of functions. -/
theorem mulOp_finset_sum {κ : Type*} (ψ : (ι → ℝ) → ℝ) (s : Finset κ)
    (W : κ → (ι → ℝ) → ℂ) :
    mulOp ψ (∑ β ∈ s, W β) = ∑ β ∈ s, mulOp ψ (W β) := by
  funext z
  simp only [mulOp, Finset.sum_apply]
  rw [Finset.mul_sum]

/-! ## 2. The order calculus for `varLapPow` and the composed operators -/

/-- `varLapPow k A B = (varLap A B)^[k]` is an operator of order `2k` when the coefficients are
smooth and `1`-periodic. -/
theorem isOrd_varLapPow
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) (k : ℕ) :
    ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ)) C ((varLapOp A B)^[k]) := by
  obtain ⟨C, Cl, h⟩ := varLap_isCommOrd (id : Op ι) linSP_id Preserves.id A B hA hAp hB hBp
    (fun m hm hmp => mulOp_isOrd m hm hmp) (fun i => pdOp_isOrd i)
    (fun m _ _ => ⟨0, IsOrd.congr (IsOrd.zero' (-1))
      (fun f _ => by funext x; simp [commOp_apply])⟩)
    (fun i => ⟨0, IsOrd.congr (IsOrd.zero' 0)
      (fun f _ => by funext x; simp [commOp_apply])⟩)
  exact ⟨_, iterConst_isOrd h.ord k⟩

/-- `varLapPow k A B` is additive (and `ℂ`-homogeneous) on smooth `1`-periodic functions. -/
theorem linSP_varLapPow
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) (k : ℕ) :
    LinSP ((varLapOp A B)^[k]) :=
  (isOrd_varLapPow A B hA hAp hB hBp k).elim fun _ h => h.lin

/-- `varLapPow k A B` preserves smooth `1`-periodic functions. -/
theorem pres_varLapPow
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) (k : ℕ) :
    Preserves ((varLapOp A B)^[k]) :=
  (isOrd_varLapPow A B hA hAp hB hBp k).elim fun _ h => h.pres

/-- The composite `POp c c' (varLapOp A B) k = M_{c'} ∘ D^k ∘ M_c` preserves smooth `1`-periodic
functions. -/
theorem pres_POp
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (c c' : (ι → ℝ) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c') (k : ℕ) :
    Preserves (POp c c' (varLapOp A B) k) := by
  show Preserves (fun f => mulOp c' ((varLapOp A B)^[k] (mulOp c f)))
  exact Preserves.comp
    (T := fun g => mulOp c' ((varLapOp A B)^[k] g)) (U := mulOp c)
    (Preserves.comp (T := mulOp c') (U := (varLapOp A B)^[k])
      (pres_mulOp c' hc' hc'p) (pres_varLapPow A B hA hAp hB hBp k))
    (pres_mulOp c hc hcp)

/-- The `pairP` operator of the chart expansion preserves smooth `1`-periodic functions. -/
theorem pres_pairP_op {ι₀ : Type*} [Fintype ι₀]
    (A : ι₀ → ι → ι → (ι → ℝ) → ℝ) (B : ι₀ → ι → (ι → ℝ) → ℝ)
    (ci co : ι₀ → ι → ι → ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b))
    (hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b))
    (hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a))
    (hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a))
    (hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d'))
    (hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d'))
    (hco : ∀ i a b c d, ContDiff ℝ (⊤ : ℕ∞) (co i a b c d))
    (hcop : ∀ i a b c d, Work.Diff.STE.Periodic1 (co i a b c d))
    (k : ℕ) (α β : ι × ι) :
    Preserves (∑ i : ι₀, ∑ c : ι, ∑ d : ι,
      POp (ci i c d β.1 β.2) (co i α.1 α.2 c d) (varLapOp (A i) (B i)) k) := by
  refine Preserves.finset_sum Finset.univ _ (fun i _ => ?_)
  refine Preserves.finset_sum Finset.univ _ (fun c _ => ?_)
  refine Preserves.finset_sum Finset.univ _ (fun d _ => ?_)
  exact pres_POp (A i) (B i) (hA i) (hAp i) (hB i) (hBp i)
    (ci i c d β.1 β.2) (co i α.1 α.2 c d) (hci i c d β.1 β.2) (hcip i c d β.1 β.2)
    (hco i α.1 α.2 c d) (hcop i α.1 α.2 c d) k

/-! ## 3. The two `L2re` manipulations of the cutoff sandwich -/

/-- **The first half of the chart term.**  Moving the inner weight `ψ` across the pairing and
distributing the cutoff over the sum over `β`:

  `L2re (M_ψ X) (S (M_ψ (Σ_β W_β))) = Σ_β L2re X (XOp ψ S (W_β))`. -/
theorem L2re_mulOp_cutOp_mulOp_sum
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (ψ : (ι → ℝ) → ℝ) (hψc : Continuous (fun z => ((ψ z : ℝ) : ℂ)))
    {κ : Type*} [Fintype κ]
    (X : (ι → ℝ) → ℂ) (hXc : Continuous X)
    (W : κ → (ι → ℝ) → ℂ) (hW : ∀ β, SmoothPer (mulOp ψ (W β))) :
    Work.Diff.STE.L2re (mulOp ψ X) (cutOp ρ ε (mulOp ψ (∑ β, W β)))
      = ∑ β, Work.Diff.STE.L2re X (XOp ψ (cutOp ρ ε) (W β)) := by
  rw [mulOp_L2re_adjoint]
  have hstep : cutOp ρ ε (mulOp ψ (∑ β, W β)) = ∑ β, cutOp ρ ε (mulOp ψ (W β)) := by
    rw [mulOp_finset_sum]
    exact linSP_map_finset_sum (cutOp_isOrd ρ hρ ε).lin Finset.univ _ (fun β _ => hW β)
  have hstep2 : mulOp ψ (∑ β, cutOp ρ ε (mulOp ψ (W β))) = ∑ β, XOp ψ (cutOp ρ ε) (W β) := by
    rw [mulOp_finset_sum]; rfl
  rw [hstep, hstep2, finset_sum_apply_eq]
  exact L2re_finset_sum_snd Finset.univ (fun β => XOp ψ (cutOp ρ ε) (W β)) X
    (fun β _ => hψc.mul ((cutOp_isOrd ρ hρ ε).pres _ (hW β)).continuous) hXc

/-- **The second half of the chart term.**  Moving the outer weight `ψ` of the first argument across
the pairing and distributing the sum over `β`:

  `L2re (M_ψ (Σ_β V_β)) (S (M_ψ Y)) = Σ_β L2re (V_β) (XOp ψ S Y)`. -/
theorem L2re_mulOp_sum_cutOp_mulOp
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (ψ : (ι → ℝ) → ℝ)
    {κ : Type*} [Fintype κ]
    (V : κ → (ι → ℝ) → ℂ) (hVc : ∀ β, Continuous (V β))
    (Y : (ι → ℝ) → ℂ) (hYc : Continuous (XOp ψ (cutOp ρ ε) Y)) :
    Work.Diff.STE.L2re (mulOp ψ (∑ β, V β)) (cutOp ρ ε (mulOp ψ Y))
      = ∑ β, Work.Diff.STE.L2re (V β) (XOp ψ (cutOp ρ ε) Y) := by
  rw [mulOp_L2re_adjoint]
  rw [show mulOp ψ (cutOp ρ ε (mulOp ψ Y)) = XOp ψ (cutOp ρ ε) Y from rfl]
  rw [finset_sum_apply_eq]
  exact L2re_finset_sum_fst Finset.univ V (XOp ψ (cutOp ρ ε) Y) (fun β _ => hVc β) hYc

/-! ## 4. The chart expansion in the `pairP` vocabulary -/

/-- **The chart expansion of `Qk` summed over its "inner" index.**  The pointwise value of the sum
over `β` of `pairP_αβ` applied to the `β`-component of the chart matrix is the chart-`l` expression
of `Q_k` evaluated on the full periodised chart matrix.  This is the linearity of `varLapPow` in the
inner summand together with the reordering of the three sums. -/
theorem pairP_expand {ι₀ : Type*} [Fintype ι₀]
    (A : ι₀ → ι → ι → (ι → ℝ) → ℝ) (B : ι₀ → ι → (ι → ℝ) → ℝ)
    (ci co : ι₀ → ι → ι → ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b))
    (hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b))
    (hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a))
    (hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a))
    (hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d'))
    (hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d'))
    (k : ℕ) (p : ι → ι → (ι → ℝ) → ℂ) (hp : ∀ c d, SmoothPer (p c d))
    (α : ι × ι) (z : ι → ℝ) :
    (∑ β : ι × ι, (∑ i : ι₀, ∑ c : ι, ∑ d : ι,
        POp (ci i c d β.1 β.2) (co i α.1 α.2 c d) (varLapOp (A i) (B i)) k) (p β.1 β.2)) z
      = ∑ i : ι₀, ∑ c : ι, ∑ d : ι, ((co i α.1 α.2 c d z : ℝ) : ℂ) *
          varLapPow k (A i) (B i)
            (fun w => ∑ c' : ι, ∑ d' : ι, ((ci i c d c' d' w : ℝ) : ℂ) * p c' d' w) z := by
  have hL : (∑ β : ι × ι, (∑ i : ι₀, ∑ c : ι, ∑ d : ι,
        POp (ci i c d β.1 β.2) (co i α.1 α.2 c d) (varLapOp (A i) (B i)) k) (p β.1 β.2)) z
      = ∑ β : ι × ι, ∑ i : ι₀, ∑ c : ι, ∑ d : ι,
          ((co i α.1 α.2 c d z : ℝ) : ℂ) *
          varLapPow k (A i) (B i)
            (fun w => ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w) z := by
    simp only [Finset.sum_apply, POp, compOp, mulOp]; rfl
  rw [hL]
  have hreorder : (∑ β : ι × ι, ∑ i : ι₀, ∑ c : ι, ∑ d : ι,
          ((co i α.1 α.2 c d z : ℝ) : ℂ) *
          varLapPow k (A i) (B i)
            (fun w => ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w) z)
      = ∑ i : ι₀, ∑ c : ι, ∑ d : ι, ∑ β : ι × ι,
          ((co i α.1 α.2 c d z : ℝ) : ℂ) *
          varLapPow k (A i) (B i)
            (fun w => ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w) z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_comm]
  rw [hreorder]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.mul_sum]
  have hmulsum : (∑ β : ι × ι, mulOp (ci i c d β.1 β.2) (p β.1 β.2))
      = fun w => ∑ β : ι × ι, ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w := by
    funext w; simp only [mulOp, Finset.sum_apply]
  have hconv : (fun w => ∑ β : ι × ι, ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w)
      = fun w => ∑ c' : ι, ∑ d' : ι, ((ci i c d c' d' w : ℝ) : ℂ) * p c' d' w := by
    funext w
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hlin := linSP_map_finset_sum (T := (varLapOp (A i) (B i))^[k])
      (linSP_varLapPow (A i) (B i) (hA i) (hAp i) (hB i) (hBp i) k) Finset.univ
      (fun β : ι × ι => mulOp (ci i c d β.1 β.2) (p β.1 β.2))
      (fun β _ => SmoothPer.mulOp' (hci i c d β.1 β.2) (hcip i c d β.1 β.2) (hp β.1 β.2))
  have hV : (∑ β : ι × ι, varLapPow k (A i) (B i)
        (fun w => ((ci i c d β.1 β.2 w : ℝ) : ℂ) * p β.1 β.2 w))
      = varLapPow k (A i) (B i)
          (fun w => ∑ c' : ι, ∑ d' : ι, ((ci i c d c' d' w : ℝ) : ℂ) * p c' d' w) := by
    rw [← hconv, ← hmulsum]
    exact hlin.symm
  rw [← Finset.sum_apply, hV]

/-- The function-level form of `pairP_expand`. -/
theorem pairP_expand_fun {ι₀ : Type*} [Fintype ι₀]
    (A : ι₀ → ι → ι → (ι → ℝ) → ℝ) (B : ι₀ → ι → (ι → ℝ) → ℝ)
    (ci co : ι₀ → ι → ι → ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b))
    (hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b))
    (hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a))
    (hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a))
    (hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d'))
    (hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d'))
    (k : ℕ) (p : ι → ι → (ι → ℝ) → ℂ) (hp : ∀ c d, SmoothPer (p c d))
    (α : ι × ι) :
    (∑ β : ι × ι, (∑ i : ι₀, ∑ c : ι, ∑ d : ι,
        POp (ci i c d β.1 β.2) (co i α.1 α.2 c d) (varLapOp (A i) (B i)) k) (p β.1 β.2))
      = fun z => ∑ i : ι₀, ∑ c : ι, ∑ d : ι, ((co i α.1 α.2 c d z : ℝ) : ℂ) *
          varLapPow k (A i) (B i)
            (fun w => ∑ c' : ι, ∑ d' : ι, ((ci i c d c' d' w : ℝ) : ℂ) * p c' d' w) z :=
  funext fun z => pairP_expand A B ci co hA hAp hB hBp hci hcip k p hp α z

/-- An equality of the second arguments of a `mulOp`, written so that the first argument of `mulOp`
is an explicitly evaluated weight. -/
theorem mulOp_congr {ψ : (ι → ℝ) → ℝ} {A B : (ι → ℝ) → ℂ} (h : A = B) :
    (fun z => ((ψ z : ℝ) : ℂ) * A z) = mulOp ψ B := by
  rw [h]; rfl

end Work.Diff.STE.B3.VarCoef

namespace Work.Diff.STE.B3.VarCoef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 5. The chart-`l` form of the two `Rper` families -/

/-- `Rper_l h = perPhi_l · perMat_l h`, with the weight written through its real part
`perPhiR_l`. -/
theorem Rper_eq_mulOp_perMat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper l h a b
      = mulOp (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b) := by
  rw [Work.Diff.STE.B3.Rper_eq_perPhi_perMat (I := I) (M := M) D η hη1 hηt l h a b,
    Work.Diff.STE.B3.VarCoef.perPhi_eq_ofReal_perPhiR (I := I) (M := M) D l]
  rfl

/-- `Rper_l (Q_k h) = perPhi_l · Σ_β pairP_{αβ}(perMat_l h)`, the chart-`l` expansion of the
localised `Q_k h` written through the `pairP` operator of the scalar chart expression. -/
theorem Rper_Qk_eq_mulOp_pairP
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b'))
    (hS : ∀ c' d' : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.VarCoef.SmoothPer
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d'))
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper l (Work.Diff.STE.B3.Qk D k h) a b
      = mulOp (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
          (∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h β.1 β.2)) := by
  rw [Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp (I := I) (M := M) D k l η hη1 hηt
      ce.A ce.B ce.ci ce.co ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip ce.hco ce.hcop
      ce.hCE h a b hh,
    Work.Diff.STE.B3.VarCoef.perPhi_eq_ofReal_perPhiR (I := I) (M := M) D l]
  exact mulOp_congr (A := fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ((ce.co i a b c d z : ℝ) : ℂ) *
          Work.Diff.STE.B3.VarCoef.varLapPow k (ce.A i) (ce.B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ce.ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z)
    (B := ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h β.1 β.2))
    (pairP_expand_fun (A := ce.A) (B := ce.B) (ci := ce.ci) (co := ce.co)
      ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip k
      (fun c' d' => Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d') hS (a, b)).symm

end Work.Diff.STE.B3.VarCoef

namespace Work.Diff.STE.B3.VarCoef

/-! ## 6. The target -/

theorem chartTerm_eq_XP
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f u : Work.Diff.STE.Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hQf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k f) a b))
    (hQu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k u) a b))
    (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 1 / 4 → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hφ : Work.Diff.STE.B3.VarCoef.SmoothPer
      (fun z => ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)))
    (hF : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b))
    (hU : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b))
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l) :
    (Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε (D.R l f a b) z)
        (D.R l (Work.Diff.STE.B3.Qk D k u))
      - Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε
          (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z) (D.R l u))
    = (∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ( Work.Diff.STE.L2re
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
        - Work.Diff.STE.L2re
            (Work.Diff.STE.B3.VarCoef.pairP ce β α
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)) )) := by
  classical
  -- ## Step 1: reduce the component pairings to the flat periodised form
  rw [Work.Diff.STE.B3.VarCoef.CPair_chart_term_eq_periodised (I := I) (M := M)
    D ρ hρ k ε hε f u hf hu hQf hQu l]
  simp only [← Work.Diff.STE.B3.VarCoef.cutOp_apply]
  -- ## Step 2: the two `Rper` families in the `mulOp`/`pairP` form
  have hψc : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)) :=
    hφ.continuous
  have h1 : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.L2re (D.Rper l f a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l (Work.Diff.STE.B3.Qk D k u) a b))
        = ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b)
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
                  (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
    intro a b
    rw [Rper_eq_mulOp_perMat (I := I) (M := M) D η hη1 hηt l f a b,
      Rper_Qk_eq_mulOp_pairP (I := I) (M := M) D k l η hη1 hηt ce u hu hU a b]
    exact L2re_mulOp_cutOp_mulOp_sum ρ hρ ε
      (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l) hψc
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b) (hF a b).continuous
      (fun β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))
      (fun β => SmoothPer.mul hφ (pres_pairP_op ce.A ce.B ce.ci ce.co ce.hA ce.hAp ce.hB ce.hBp
        ce.hci ce.hcip ce.hco ce.hcop k (a, b) β
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2) (hU β.1 β.2)))
  have h2 : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.STE.L2re (D.Rper l (Work.Diff.STE.B3.Qk D k f) a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l u a b))
        = ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b)) := by
    intro a b
    rw [Rper_Qk_eq_mulOp_pairP (I := I) (M := M) D k l η hη1 hηt ce f hf hF a b,
      Rper_eq_mulOp_perMat (I := I) (M := M) D η hη1 hηt l u a b]
    exact L2re_mulOp_sum_cutOp_mulOp ρ ε
      (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
      (fun β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.VarCoef.pairP ce (a, b) β
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
      (fun β => (pres_pairP_op ce.A ce.B ce.ci ce.co ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip
        ce.hco ce.hcop k (a, b) β
        (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2) (hF β.1 β.2)).continuous)
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b)
      (hψc.mul (((cutOp_isOrd ρ hρ ε).pres _
        (SmoothPer.mul hφ (hU a b))).continuous))
  -- ## Step 3: assemble the two sums
  have hT1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (D.Rper l f a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l (Work.Diff.STE.B3.Qk D k u) a b)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.VarCoef.pairP ce α β
                  (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hT2 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (D.Rper l (Work.Diff.STE.B3.Qk D k f) a b)
          (Work.Diff.STE.B3.VarCoef.cutOp ρ ε (D.Rper l u a b)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u α.1 α.2)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hT1, hT2]
  -- ## Step 4: the final re-indexing of the subtracted double sum
  have hswap : (∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce β α
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
            (Work.Diff.STE.B3.VarCoef.XOp
              (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
              (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
              (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
      = ∑ α : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce α β
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f β.1 β.2))
              (Work.Diff.STE.B3.VarCoef.XOp
                (Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l)
                (Work.Diff.STE.B3.VarCoef.cutOp ρ ε)
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u α.1 α.2)) :=
    Finset.sum_comm
  simp only [Finset.sum_sub_distrib]
  rw [hswap]

end Work.Diff.STE.B3.VarCoef
