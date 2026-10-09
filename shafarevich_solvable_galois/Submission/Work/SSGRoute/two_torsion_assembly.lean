import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` two-torsion lifting from the graded-piece statements

This file isolates the **assembly** of the `p = 2` half of
`Work.SSGRoute.flowGroup_two_torsion_lift` (Schmidt–Wingberg, Step 1a, clause (B) at `p = 2`):

> for `γ ∈ Γ_n(τ)` with `γ ^ 2 = 1` and `flowQuot γ ≠ 1` there is `y ∈ Γ_n(τ+1)` with
> `y ^ 2 = 1` and `LiftsFlowAt y γ`.

The mathematical input is the family of **graded-step** statements
`Work.SSGRoute.GradedStep`: for every `σ = (i,j)` with `1 ≤ j ≤ i`, every element of the kernel of
the projection `Q_{σ+1} → Q_σ` which is anti-fixed under the involution `δ ∈ G` is a `δ`-difference
in `Q_{σ+1}`.  Equivalently (via the kernel identification `E(σ) = ker(Q_{σ+1} → Q_σ)`), every
`δ`-fixed element of the graded piece `E(σ)` is a `δ`-difference *in the ambient group* `Q_{σ+1}`.
This is the statement computed level by level by `Submission/Work/SSGRoute/gradedPiece_*` (the
`p = 2` correction of Shafarevich's theorem).

What is proved *here* is the reduction of that family to the lifting statement:

* `Work.SSGRoute.antifixed_is_delta_difference_of_gradedStep` — descent along the refined
  filtration: every anti-fixed element of `Q_σ` is a `δ`-difference, for all `σ`.  The descent uses
  the centrality of the kernel (`Work.SSGRoute.flowQuotSucc_ker_central`) in its *weak* form: the
  `δ`-difference witness may lie in the ambient group.  The strong form, with the witness inside
  the kernel, is **false** already for `E(2,2) ≅ 𝔽₂` with trivial `δ`-action: `[a,b] = ν(ab)` in
  `Q_{(3,1)} = F/P₃`, but `[a,b] ≠ e⁻¹e` for every `e ∈ E(2,2)` (where `e⁻¹e = 1`).
* `Work.SSGRoute.two_torsion_lift_two_of_gradedStep` — the resulting `2`-torsion lifting, in exactly
  the shape consumed by `Work.SSGRoute.two_torsion_lift_of_halves` (and hence by
  `Work.SSGRoute.stage_local_shrinking`).
-/

open scoped Pointwise

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 4000000

variable (G : Type*) [Group G]

/-- **The graded-step hypothesis** (`p = 2`, involution `δ`): for every `σ = (i,j)` with
`1 ≤ j ≤ i`, every element of the kernel of `Q_{σ+1} → Q_σ` which is anti-fixed under `δ` is a
`δ`-difference in `Q_{σ+1}`. -/
def GradedStep (n : ℕ) (δ : G) : Prop :=
  ∀ (i j : ℕ), 1 ≤ j → j ≤ i →
    ∀ c : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
      flowQuotSucc 2 G n i j c = 1 →
      flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
        c = (flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ e)⁻¹ * e

/-- **The anti-fixed-elements-are-differences predicate**: every anti-fixed element of `Q_{(i,j)}`
is a `δ`-difference. -/
def IsDelta (n i j : ℕ) (δ : G) : Prop :=
  ∀ a : flowQuotient 2 G n i j,
    flowAction 2 G n i j δ a = a⁻¹ →
    ∃ r : flowQuotient 2 G n i j, a = (flowAction 2 G n i j δ r)⁻¹ * r

/-- An involution of a group acting as an automorphism of order `2`. -/
theorem mulEquiv_sq_apply {A : Type*} [Group A] (f : A ≃* A) (hf : f * f = 1) (x : A) :
    f (f x) = x := by
  have h := congrArg (fun g : A ≃* A => g x) hf
  simpa using h

/-- The automorphism of `Q_σ` induced by `δ` has order `2` when `δ * δ = 1`. -/
theorem flowAction_mul_self (n : ℕ) (δ : G) (hδ : δ * δ = 1) (i j : ℕ) :
    flowAction 2 G n i j δ * flowAction 2 G n i j δ = 1 := by
  rw [← map_mul (flowAction 2 G n i j), hδ, map_one]

/-- The projection `Q_{σ+1} → Q_σ` is equivariant for the induced actions. -/
theorem flowQuotSucc_flowAction_two {n : ℕ} (i j : ℕ) (g : G)
    (x : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotSucc 2 G n i j (flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 g x)
      = flowAction 2 G n i j g (flowQuotSucc 2 G n i j x) := by
  exact flowQuotSucc_smul (p := 2) (G := G) (m := n) i j g x

section Descent

/-- **One descent step.**  If every anti-fixed element of `Q_σ` is a `δ`-difference, and the
graded step at `σ` holds, then every anti-fixed element of `Q_{σ+1}` is a `δ`-difference.

The proof is the bookkeeping of `Work.SSGRoute.central_descent_antifixed_weak`, carried out
directly in the quotient `Q_{σ+1}` (so that no quotient isomorphism is needed). -/
theorem descent_step {n : ℕ} {δ : G} (hδ : δ * δ = 1) (i j : ℕ)
    (hquot : IsDelta G n i j δ)
    (hstep : ∀ c : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
      flowQuotSucc 2 G n i j c = 1 →
      flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
        c = (flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ e)⁻¹ * e) :
    ∀ x : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
      flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ x = x⁻¹ →
      ∃ w : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
        x = (flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ w)⁻¹ * w := by
  intro x hx
  -- abbreviations for the two actions
  set δ' := flowAction 2 G n (tauSucc i j).1 (tauSucc i j).2 δ with hδ'def
  set δq := flowAction 2 G n i j δ with hδqdef
  have hδ'a : ∀ y, δ' (δ' y) = y :=
    mulEquiv_sq_apply δ' (by rw [hδ'def,
      flowAction_mul_self (G := G) n δ hδ (tauSucc i j).1 (tauSucc i j).2])
  -- the class of `x` in `Q_σ` is anti-fixed
  have hxq : δq (flowQuotSucc 2 G n i j x) = (flowQuotSucc 2 G n i j x)⁻¹ := by
    rw [hδqdef, ← flowQuotSucc_flowAction_two (G := G) i j δ x, hx]
    exact map_inv (flowQuotSucc 2 G n i j) x
  obtain ⟨r, hr⟩ := hquot _ hxq
  obtain ⟨r', hr'⟩ := flowQuotSucc_surjective (p := 2) (G := G) n i j r
  set x' := (δ' r')⁻¹ * r' with hx'def
  have hx' : δ' x' = x'⁻¹ := by
    rw [hx'def, map_mul, map_inv, hδ'a r', mul_inv_rev, inv_inv]
  have hcl : flowQuotSucc 2 G n i j x' = flowQuotSucc 2 G n i j x := by
    rw [hx'def, map_mul, map_inv, hδ'def, flowQuotSucc_flowAction_two (G := G) i j δ r', hr', hr]
  -- `c = x * x'⁻¹` lies in the kernel and is anti-fixed
  set c := x * x'⁻¹ with hcdef
  have hc : flowQuotSucc 2 G n i j c = 1 := by
    rw [hcdef, map_mul, map_inv, hcl, mul_inv_cancel]
  have hcmem : c ∈ (flowQuotSucc 2 G n i j).ker := by
    rw [MonoidHom.mem_ker]; exact hc
  have hcx : c * x = x * c := by
    have h : x * c * x⁻¹ = c := flowQuotSucc_ker_central (p := 2) (G := G) n i j x c hcmem
    calc c * x = (x * c * x⁻¹) * x := by rw [h]
      _ = x * c := by group
  have hcanti : δ' c = c⁻¹ := by
    have h2 : x'⁻¹ * x = x * x'⁻¹ := by
      have h3 : x * (x'⁻¹ * x) = x * (x * x'⁻¹) := by
        conv_lhs => rw [← mul_assoc]
        rw [hcdef] at hcx
        exact hcx
      exact mul_left_cancel h3
    rw [hcdef, map_mul, map_inv, hx, hx', inv_inv]
    have h4 := congrArg Inv.inv h2
    simpa using h4
  -- the graded step gives the witness `e` (in the ambient group)
  obtain ⟨e, he⟩ := hstep c hc hcanti
  refine ⟨e * r', ?_⟩
  have hx1 : x = ((δ' e)⁻¹ * e) * ((δ' r')⁻¹ * r') := by
    rw [← he, hcdef, hx'def, mul_assoc, inv_mul_cancel, mul_one]
  have hce : flowQuotSucc 2 G n i j ((δ' e)⁻¹ * e) = 1 := by
    rw [← he]; exact hc
  have hcent : ∀ y : flowQuotient 2 G n (tauSucc i j).1 (tauSucc i j).2,
      ((δ' e)⁻¹ * e) * y = y * ((δ' e)⁻¹ * e) := by
    intro y
    have h := flowQuotSucc_ker_central (p := 2) (G := G) n i j y ((δ' e)⁻¹ * e)
      (by rw [MonoidHom.mem_ker]; exact hce)
    have h2 : y * ((δ' e)⁻¹ * e) = ((δ' e)⁻¹ * e) * y := by
      calc y * ((δ' e)⁻¹ * e) = (y * ((δ' e)⁻¹ * e) * y⁻¹) * y := by group
        _ = ((δ' e)⁻¹ * e) * y := by rw [h]
    exact h2.symm
  have hkey : ((δ' e)⁻¹ * e) * ((δ' r')⁻¹ * r') = (δ' r')⁻¹ * (δ' e)⁻¹ * (e * r') := by
    rw [show ((δ' e)⁻¹ * e) * ((δ' r')⁻¹ * r') = ((δ' e)⁻¹ * e) * (δ' r')⁻¹ * r' from by
      group]
    rw [hcent ((δ' r')⁻¹)]
    group
  rw [hx1, hkey, map_mul δ' e r', mul_inv_rev]

/-- The quotient `Q_{(1,1)}` is trivial. -/
theorem flowQuotient_one_one_subsingleton {n : ℕ} :
    Subsingleton (flowQuotient 2 G n 1 1) := by
  have htop : (flowTerm 2 G n 1 1).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))
      = ⊤ := by
    rw [flowTerm, refinedTerm_one, pSeries_one, Subgroup.top_subgroupOf]
  rw [show flowQuotient 2 G n 1 1 = ((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) ⧸
      (flowTerm 2 G n 1 1).subgroupOf ⊤) from rfl, htop]
  exact QuotientGroup.subsingleton_iff.mpr rfl

/-- **Descent along the refined filtration.**  From the graded-step hypotheses follows: every
anti-fixed element of every `Q_σ` (`1 ≤ j ≤ i`) is a `δ`-difference. -/
theorem antifixed_is_delta_difference_of_gradedStep {n : ℕ} {δ : G} (hδ : δ * δ = 1)
    (h : GradedStep G n δ) :
    ∀ (i j : ℕ), 1 ≤ j → j ≤ i → IsDelta G n i j δ := by
  have step : ∀ (i j : ℕ), 1 ≤ j → j ≤ i → IsDelta G n i j δ →
      IsDelta G n (tauSucc i j).1 (tauSucc i j).2 δ :=
    fun i j hj hji hq => descent_step (G := G) (n := n) (δ := δ) hδ i j hq (h i j hj hji)
  have main : ∀ i : ℕ, ∀ j : ℕ, 1 ≤ j → j ≤ i → IsDelta G n i j δ := by
    intro i
    induction i with
    | zero => intro j hj hji; omega
    | succ i ih =>
      -- `H(i+1,1)` from `H(i,i)`
      have h1 : IsDelta G n (i + 1) 1 δ := by
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · -- `Q_{(1,1)}` is trivial
          subst hi0
          intro a _
          haveI : Subsingleton (flowQuotient 2 G n 1 1) :=
            flowQuotient_one_one_subsingleton (G := G)
          refine ⟨1, ?_⟩
          rw [Subsingleton.elim a 1, map_one, inv_one, one_mul]
        · rw [← show (tauSucc i i).1 = i + 1 from by rw [tauSucc_fst, if_neg (by omega)],
            ← show (tauSucc i i).2 = 1 from by rw [tauSucc_snd, if_neg (by omega)]]
          exact step i i (by omega) le_rfl (ih i (by omega) le_rfl)
      -- inner induction on `j`
      have hinner : ∀ j : ℕ, 1 ≤ j → j ≤ i + 1 → IsDelta G n (i + 1) j δ := by
        intro j
        induction j with
        | zero => intro hj _; omega
        | succ j' ihj =>
          intro hj hle
          rcases Nat.eq_zero_or_pos j' with h0 | hpos
          · subst h0
            simpa using h1
          · rw [← show (tauSucc (i + 1) j').1 = i + 1 from
                by rw [tauSucc_fst, if_pos (by omega)],
              ← show (tauSucc (i + 1) j').2 = j' + 1 from
                by rw [tauSucc_snd, if_pos (by omega)]]
            exact step (i + 1) j' hpos (by omega) (ihj (by omega) (by omega))
      exact hinner
  exact main

end Descent

/-- **The `2`-torsion lifting at `p = 2`, from the graded-step family.**  This is the conclusion of
`Work.SSGRoute.two_torsion_lift_two`, in exactly the shape consumed by
`Work.SSGRoute.two_torsion_lift_of_halves`. -/
theorem two_torsion_lift_two_of_gradedStep (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (h : ∀ δ : K ≃ₐ[ℚ] K, δ * δ = 1 → δ ≠ 1 → GradedStep (K ≃ₐ[ℚ] K) n δ) :
    ∀ γ : flowGroup 2 (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot 2 (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  intro γ hγ hδ
  set δ : K ≃ₐ[ℚ] K := γ.right with hδdef
  have hδδ : δ * δ = 1 := by
    rw [hδdef]
    have h3 := congrArg SemidirectProduct.right hγ
    rw [pow_two, SemidirectProduct.mul_def] at h3
    simpa using h3
  have hleft : (flowAction 2 (K ≃ₐ[ℚ] K) n i j δ) γ.left = γ.left⁻¹ := by
    rw [hδdef]
    have h5 := congrArg SemidirectProduct.left hγ
    rw [pow_two, SemidirectProduct.mul_def] at h5
    have h6 : γ.left * (flowAction 2 (K ≃ₐ[ℚ] K) n i j γ.right) γ.left = 1 := by
      simpa using h5
    conv_rhs => rw [mul_eq_one_iff_eq_inv.mp h6]
    rw [inv_inv]
  have hδ1 : δ ≠ 1 := by
    rw [hδdef]
    exact hδ
  obtain ⟨r, hr⟩ := antifixed_is_delta_difference_of_gradedStep (G := K ≃ₐ[ℚ] K) (n := n)
    (δ := δ) hδδ (h δ hδδ hδ1) i j hj hji γ.left hleft
  obtain ⟨r', hr'⟩ := flowQuotSucc_surjective (p := 2) (G := K ≃ₐ[ℚ] K) n i j r
  set δ' := flowAction 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 δ with hδ'def
  have hδ'a : ∀ y, δ' (δ' y) = y :=
    mulEquiv_sq_apply δ'
      (by rw [hδ'def,
        flowAction_mul_self (G := K ≃ₐ[ℚ] K) n δ hδδ (tauSucc i j).1 (tauSucc i j).2])
  set b : flowQuotient 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 := (δ' r')⁻¹ * r'
    with hbdef
  have hb1 : flowQuotSucc 2 (K ≃ₐ[ℚ] K) n i j b = γ.left := by
    rw [hbdef, map_mul, map_inv, hδ'def]
    rw [flowQuotSucc_flowAction_two (G := K ≃ₐ[ℚ] K) i j δ r', hr']
    exact hr.symm
  have hb2 : δ' b = b⁻¹ := by
    rw [hbdef, map_mul, map_inv, hδ'a r', mul_inv_rev, inv_inv]
  refine ⟨SemidirectProduct.mk b δ, ?_, ?_⟩
  · refine (liftsFlowAt_iff_flowGroupSucc 2 K n i j ⟨b, δ⟩ γ).mpr ?_
    rw [flowGroupSucc_mk, hb1, hδdef]
  · rw [pow_two, SemidirectProduct.mul_def]
    refine SemidirectProduct.ext ?_ ?_
    · show b * δ' b = 1
      rw [hb2, mul_inv_cancel]
    · show δ * δ = (1 : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right
      rw [show (1 : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right = 1 from rfl]
      exact hδδ


/-- **`L(τ)` from the anti-fixed-difference statement `H` directly.**  Same proof as
`two_torsion_lift_two_of_gradedStep`, with the descent replaced by the hypothesis that every
anti-fixed element of `Q_{(i,j)}` is already a `δ`-difference.  This is the interface of the
`p`-central route (`Work.SSGRoute.PCNormAll`, whose assembly
`pcentral_norm_all_of_layer_statements` is proved). -/
theorem two_torsion_lift_two_of_isDelta (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (h : ∀ δ : K ≃ₐ[ℚ] K, δ * δ = 1 → δ ≠ 1 → IsDelta (K ≃ₐ[ℚ] K) n i j δ) :
    ∀ γ : flowGroup 2 (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot 2 (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  intro γ hγ hδ
  set δ : K ≃ₐ[ℚ] K := γ.right with hδdef
  have hδδ : δ * δ = 1 := by
    rw [hδdef]
    have h3 := congrArg SemidirectProduct.right hγ
    rw [pow_two, SemidirectProduct.mul_def] at h3
    simpa using h3
  have hδ1 : δ ≠ 1 := by
    rw [hδdef]
    exact hδ
  have hleft : (flowAction 2 (K ≃ₐ[ℚ] K) n i j δ) γ.left = γ.left⁻¹ := by
    rw [hδdef]
    have h5 := congrArg SemidirectProduct.left hγ
    rw [pow_two, SemidirectProduct.mul_def] at h5
    have h6 : γ.left * (flowAction 2 (K ≃ₐ[ℚ] K) n i j γ.right) γ.left = 1 := by
      simpa using h5
    conv_rhs => rw [mul_eq_one_iff_eq_inv.mp h6]
    rw [inv_inv]
  obtain ⟨r, hr⟩ := h δ hδδ hδ1 γ.left hleft
  obtain ⟨r', hr'⟩ := flowQuotSucc_surjective (p := 2) (G := K ≃ₐ[ℚ] K) n i j r
  set δ' := flowAction 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 δ with hδ'def
  have hδ'a : ∀ y, δ' (δ' y) = y :=
    mulEquiv_sq_apply δ'
      (by rw [hδ'def,
        flowAction_mul_self (G := K ≃ₐ[ℚ] K) n δ hδδ (tauSucc i j).1 (tauSucc i j).2])
  set b : flowQuotient 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 := (δ' r')⁻¹ * r'
    with hbdef
  have hb1 : flowQuotSucc 2 (K ≃ₐ[ℚ] K) n i j b = γ.left := by
    rw [hbdef, map_mul, map_inv, hδ'def]
    rw [flowQuotSucc_flowAction_two (G := K ≃ₐ[ℚ] K) i j δ r', hr']
    exact hr.symm
  have hb2 : δ' b = b⁻¹ := by
    rw [hbdef, map_mul, map_inv, hδ'a r', mul_inv_rev, inv_inv]
  refine ⟨SemidirectProduct.mk b δ, ?_, ?_⟩
  · refine (liftsFlowAt_iff_flowGroupSucc 2 K n i j ⟨b, δ⟩ γ).mpr ?_
    rw [flowGroupSucc_mk, hb1, hδdef]
  · rw [pow_two, SemidirectProduct.mul_def]
    refine SemidirectProduct.ext ?_ ?_
    · show b * δ' b = 1
      rw [hb2, mul_inv_cancel]
    · show δ * δ = (1 : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right
      rw [show (1 : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right = 1 from rfl]
      exact hδδ

end Work.SSGRoute
