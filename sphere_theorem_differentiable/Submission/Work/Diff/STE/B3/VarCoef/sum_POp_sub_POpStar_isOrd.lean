import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.POp_sub_star_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.POpStar_negB_isOrd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Order `2k - 1` for the summed "defect" operator

`POp c c' D k = M_{c'} ∘ D^k ∘ M_c` and `POpStar c c' A B k = M_c ∘ (varLapStar A B)^k ∘ M_{c'}`, and
`varLapStar A (-B)` is the `L2re`-adjoint of `varLap A B` (`POp_adjoint_L2re.lean`).  The target of
this file is the **summed** (over a finite index set `κ`) version of the pair estimate: if the two
families of "coefficient products" have the same total,

  `∑_γ d_γ · c_γ = ∑_γ d'_γ · c'_γ`   pointwise,

then

  `Σ_γ POp (c γ) (d γ) (varLap A B) k − Σ_γ POpStar (c' γ) (d' γ) A (−B) k`

is an operator of order `2k - 1`: the two order-`2k` principal symbols
`(∑_γ d_γ c_γ) · |ξ|^{2k}` and `(∑_γ d'_γ c'_γ) · |ξ|^{2k}` cancel exactly.

## Proof

Write `D := varLapOp A B` and `D* := varLapStarOp A (fun a => -B a)`.  The operator is split as

`T = [Σ_γ M_{d γ} D^k M_{c γ} − Σ_γ M_{d' γ} D^k M_{c' γ}]
     + [Σ_γ M_{d' γ} D^k M_{c' γ} − Σ_γ M_{c' γ} (D*)^k M_{d' γ}]`.

* In the **first** bracket the identity `M_d D^k M_c = M_d M_c D^k + M_d [D^k, M_c]` is applied term
  by term.  The `M_d M_c D^k` parts cancel *globally* by `hprod` (`sum_mulOp_comp_mulOp_congr`),
  and what is left is `Σ_γ M_{d γ} [D^k, M_{c γ}] − Σ_γ M_{d' γ} [D^k, M_{c' γ}]`, a difference of
  sums of commutators; each `[D^k, M_{c γ}]` has order `2k - 1` (`isOrd_commOp_iterate`, from the
  `IsCommOrd` certificate `varLapOp_isCommOrd_mulOp`), and composing with the order-`0` multiplier
  `M_{d γ}` preserves that order (`IsOrd.comp`, `IsOrd.sum`).
* In the **second** bracket each chart is handled separately: for a single `γ`
  `M_{d' γ} D^k M_{c' γ} − M_{c' γ} (D*)^k M_{d' γ}` is the adjoint pair of `POp_sub_star_isOrd`
  combined with the `B ↦ −B` correction `POpStar_negB_isOrd`
  (`POp_sub_POpStar_negB_isOrd` below), hence of order `2k - 1`; a finite sum of such terms has
  order `2k - 1` (`IsOrd.sum`).
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Elementary operator identities -/

/-- The pointwise expansion of a single `POp` term against its commutator with the inner
multiplier: `M_{m'} D^k M_m = M_{m'} M_m D^k + M_{m'} [D^k, M_m]`. -/
theorem POp_apply_eq_sum_comm (m m' : (ι → ℝ) → ℝ) (D : Op ι) (k : ℕ)
    (f : (ι → ℝ) → ℂ) :
    POp m m' D k f
      = compOp (mulOp m') (compOp (mulOp m) ((D)^[k])) f
        + compOp (mulOp m') (commOp ((D)^[k]) (mulOp m)) f := by
  funext x
  simp only [POp, compOp_apply, commOp_apply, mulOp, Pi.add_apply, Pi.sub_apply]
  ring

/-- The summed version of `POp_apply_eq_sum_comm`. -/
theorem sum_POp_apply_eq {κ : Type*} [Fintype κ] (c d : κ → (ι → ℝ) → ℝ) (D : Op ι) (k : ℕ) :
    (∑ γ : κ, POp (c γ) (d γ) D k)
      = (∑ γ : κ, compOp (mulOp (d γ)) (compOp (mulOp (c γ)) ((D)^[k])))
        + (∑ γ : κ, compOp (mulOp (d γ)) (commOp ((D)^[k]) (mulOp (c γ)))) := by
  funext f
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun γ _ => POp_apply_eq_sum_comm (c γ) (d γ) D k f)

/-- The difference of two sums of operators is the sum of the differences. -/
theorem sumOp_sub_sumOp {κ : Type*} [Fintype κ] (T S : κ → Op ι) :
    (∑ γ : κ, T γ) - (∑ γ : κ, S γ) = ∑ γ : κ, (T γ - S γ) := by
  funext f
  simp only [Finset.sum_apply, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

/-- **The global cancellation of the principal symbols.**  If the two families have the same total
product, then the sums of multiplier composites agree. -/
theorem sum_mulOp_comp_mulOp_congr {κ : Type*} [Fintype κ]
    (c d c' d' : κ → (ι → ℝ) → ℝ) (E : Op ι)
    (hprod : ∀ z : ι → ℝ, (∑ γ : κ, d γ z * c γ z) = (∑ γ : κ, d' γ z * c' γ z)) :
    (∑ γ : κ, compOp (mulOp (d γ)) (compOp (mulOp (c γ)) E))
      = (∑ γ : κ, compOp (mulOp (d' γ)) (compOp (mulOp (c' γ)) E)) := by
  funext f x
  have key : ∀ (e e' : κ → ℝ),
      (∑ γ : κ, ((e γ : ℝ) : ℂ) * (((e' γ : ℝ) : ℂ) * E f x))
        = ((∑ γ : κ, e γ * e' γ : ℝ) : ℂ) * E f x := by
    intro e e'
    have h1 : (∑ γ : κ, ((e γ : ℝ) : ℂ) * (((e' γ : ℝ) : ℂ) * E f x))
        = ∑ γ : κ, (((e γ * e' γ : ℝ)) : ℂ) * E f x :=
      Finset.sum_congr rfl (fun γ _ => by push_cast; ring)
    rw [h1, ← Finset.sum_mul, ← Complex.ofReal_sum]
  simp only [Finset.sum_apply, compOp_apply, mulOp]
  rw [key (fun γ => d γ x) (fun γ => c γ x), key (fun γ => d' γ x) (fun γ => c' γ x), hprod x]

/-! ## 2. The per-chart adjoint pair with the `B ↦ −B` correction -/

/-- **The adjoint pair of a single chart, with the correct sign of `B`.**  Both
`POp c c' (varLap A B) k - POpStar c c' A B k` (`POp_sub_star_isOrd`) and
`POpStar c c' A B k - POpStar c c' A (-B) k` (`POpStar_negB_isOrd`) have order `2k - 1`, and their
sum telescopes to `POp c c' (varLap A B) k - POpStar c c' A (-B) k`. -/
theorem POp_sub_POpStar_negB_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {c c' : (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c') :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.POp c c' (Work.Diff.STE.B3.VarCoef.varLapOp A B) k
        - Work.Diff.STE.B3.VarCoef.POpStar c c' A (fun a => -(B a)) k) := by
  obtain ⟨C1, h1⟩ := POp_sub_star_isOrd (A := A) (B := B) (c := c) (c' := c')
    k hk hA hAp hB hBp hc hcp hc' hc'p
  obtain ⟨C2, h2⟩ := POpStar_negB_isOrd (A := A) (B := B) (c := c) (c' := c')
    k hk hA hAp hB hBp hc hcp hc' hc'p
  refine ⟨fun t => 2 * (C1 t + C2 t), ?_⟩
  refine IsOrd.congr (T := (POp c c' (varLapOp A B) k - POpStar c c' A B k)
      + (POpStar c c' A B k - POpStar c c' A (fun a => -(B a)) k)) (IsOrd.add h1 h2) ?_
  intro f _
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

/-! ## 3. The target -/

theorem sum_POp_sub_POpStar_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    [Fintype κ] (k : ℕ) (hk : 1 ≤ k)
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ}
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (c d c' d' : κ → (ι → ℝ) → ℝ)
    (hc : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (c γ)) (hcp : ∀ γ, Work.Diff.STE.Periodic1 (c γ))
    (hd : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (d γ)) (hdp : ∀ γ, Work.Diff.STE.Periodic1 (d γ))
    (hc' : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (c' γ)) (hc'p : ∀ γ, Work.Diff.STE.Periodic1 (c' γ))
    (hd' : ∀ γ, ContDiff ℝ (⊤ : ℕ∞) (d' γ)) (hd'p : ∀ γ, Work.Diff.STE.Periodic1 (d' γ))
    (hprod : ∀ z : ι → ℝ, (∑ γ : κ, d γ z * c γ z) = (∑ γ : κ, d' γ z * c' γ z)) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      ((∑ γ : κ, Work.Diff.STE.B3.VarCoef.POp (c γ) (d γ)
          (Work.Diff.STE.B3.VarCoef.varLapOp A B) k)
        - (∑ γ : κ, Work.Diff.STE.B3.VarCoef.POpStar (c' γ) (d' γ) A
          (fun a => -(B a)) k)) := by
  classical
  -- ### step 1: the second pair of sums, chart by chart
  have hQ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      ((∑ γ : κ, POp (c' γ) (d' γ) (varLapOp A B) k)
        - (∑ γ : κ, POpStar (c' γ) (d' γ) A (fun a => -(B a)) k)) := by
    have hpair : ∀ γ : κ, ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (POp (c' γ) (d' γ) (varLapOp A B) k
          - POpStar (c' γ) (d' γ) A (fun a => -(B a)) k) :=
      fun γ => POp_sub_POpStar_negB_isOrd (A := A) (B := B) (c := c' γ) (c' := d' γ)
        k hk hA hAp hB hBp (hc' γ) (hc'p γ) (hd' γ) (hd'p γ)
    choose Cf hCf using hpair
    refine ⟨_, IsOrd.congr (IsOrd.sum Finset.univ
      (fun γ : κ => POp (c' γ) (d' γ) (varLapOp A B) k
        - POpStar (c' γ) (d' γ) A (fun a => -(B a)) k) Cf (fun γ _ => hCf γ)) ?_⟩
    intro f _
    exact congrFun (sumOp_sub_sumOp
      (fun γ : κ => POp (c' γ) (d' γ) (varLapOp A B) k)
      (fun γ : κ => POpStar (c' γ) (d' γ) A (fun a => -(B a)) k)).symm f
  -- ### step 2: the first pair of sums, via the commutator expansion
  -- the per-chart order certificate for `[D^k, M_m]`
  have hcomm : ∀ (m : (ι → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (commOp (((varLapOp A B))^[k]) (mulOp m)) := by
    intro m hm hmp
    obtain ⟨CD, CSD, hVLC⟩ := varLapOp_isCommOrd_mulOp m hm hmp A B hA hAp hB hBp
    have hδ : IsOrd 1 CSD (commOp (mulOp m) (varLapOp A B)) :=
      IsOrd.mono_d hVLC.comm (by norm_num)
    obtain ⟨C, hC⟩ := isOrd_commOp_iterate (D := varLapOp A B) (L := mulOp m)
      (CD := CD) (δ := 1) (Cδ := CSD) hVLC.ord hδ (linSP_mulOp m) (pres_mulOp m hm hmp) k
    have h1 : IsOrd (1 + 2 * (k : ℤ) - 2) C (commOp (((varLapOp A B))^[k]) (mulOp m)) :=
      IsOrd.congr (T := -(commOp (mulOp m) (((varLapOp A B))^[k]))) (IsOrd.neg hC)
        (fun f _ => (commOp_pow_mulOp_eq_neg (varLapOp A B) m k f).symm)
    exact ⟨C, IsOrd.mono_d h1 (by omega)⟩
  -- the sum of the commutators, with the outer order-`0` multipliers
  have hCC : ∀ (c d : κ → (ι → ℝ) → ℝ), (∀ γ, ContDiff ℝ (⊤ : ℕ∞) (c γ)) →
      (∀ γ, Work.Diff.STE.Periodic1 (c γ)) → (∀ γ, ContDiff ℝ (⊤ : ℕ∞) (d γ)) →
      (∀ γ, Work.Diff.STE.Periodic1 (d γ)) →
      ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (∑ γ : κ, compOp (mulOp (d γ)) (commOp (((varLapOp A B))^[k]) (mulOp (c γ)))) := by
    intro c d hc hcp hd hdp
    have hterm : ∀ γ : κ, ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (compOp (mulOp (d γ)) (commOp (((varLapOp A B))^[k]) (mulOp (c γ)))) := by
      intro γ
      obtain ⟨C, hC⟩ := hcomm (c γ) (hc γ) (hcp γ)
      obtain ⟨Cm, hCm⟩ := mulOp_isOrd (d γ) (hd γ) (hdp γ)
      exact ⟨_, IsOrd.mono_d (IsOrd.comp (T := mulOp (d γ))
        (U := commOp (((varLapOp A B))^[k]) (mulOp (c γ))) hCm hC) (by omega)⟩
    choose C hC using hterm
    exact ⟨_, IsOrd.sum Finset.univ _ C (fun γ _ => hC γ)⟩
  have hB1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      ((∑ γ : κ, POp (c γ) (d γ) (varLapOp A B) k)
        - (∑ γ : κ, POp (c' γ) (d' γ) (varLapOp A B) k)) := by
    obtain ⟨C1, hC1⟩ := hCC c d hc hcp hd hdp
    obtain ⟨C2, hC2⟩ := hCC c' d' hc' hc'p hd' hd'p
    refine ⟨_, IsOrd.congr (IsOrd.sub hC1 hC2) (fun f _ => ?_)⟩
    have e1 := sum_POp_apply_eq c d (varLapOp A B) k
    have e2 := sum_POp_apply_eq c' d' (varLapOp A B) k
    have e3 := sum_mulOp_comp_mulOp_congr c d c' d' (((varLapOp A B))^[k]) hprod
    simp only [Pi.sub_apply]
    rw [e1, e2, e3]
    simp only [Pi.add_apply]
    abel
  -- ### step 3: assemble
  obtain ⟨Cb, hB1'⟩ := hB1
  obtain ⟨Cq, hQ'⟩ := hQ
  refine ⟨_, IsOrd.congr (IsOrd.add hB1' hQ') (fun f _ => ?_)⟩
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

end Work.Diff.STE.B3.VarCoef
