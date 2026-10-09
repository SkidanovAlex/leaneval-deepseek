import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.CC.MagFourMap
import Submission.Work.SSGRoute.CC.MagFourFreeGroup
import Submission.Work.SSGRoute.CC.MagFourRealizePort
import Submission.Work.SSGRoute.CC.Mag4Pure
import Submission.Work.SSGRoute.CC.Mag4MemWsub
import Submission.Work.SSGRoute.CC.FlgThetaSpanLePort
import Submission.Work.SSGRoute.CC.FreeLieFourFixedGeneration
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Port of `Submission/Work/SSGRoute/gradedStep_diagonal_zmodTwo_four.lean`

Verbatim copy, wrapped in the fresh namespace `Work.SSGRoute.LNS3B`, with the realization module
replaced by `Submission/Work/SSGRoute/lns3/MagFourRealizePort.lean` (which uses the proved
double-word class computation).  Provides `Work.SSGRoute.CC.LNS3B.gradedStep_diagonal_zmodTwo_four`,
the `(4,4)` diagonal graded step for `G = Multiplicative (ZMod 2)`, free of `sorryAx`.
-/

namespace Work.SSGRoute.CC.LNS3B

/-!
# The `(4,4)` diagonal graded step at `G = ℤ/2`

See `PLAN_gradedStep_diagonal_zmodTwo_four_status.md` for the state of this proof.

The argument is in fact uniform in the finite group `G` and the involution `δ ≠ 1 ∈ G`: it is
proved here as `Work.SSGRoute.diagonal_four_general`, and the target
`Work.SSGRoute.gradedStep_diagonal_zmodTwo_four` is its specialisation to
`G = Multiplicative (ZMod 2)` and `δ = ofAdd 1`.

Chain of reductions (all proved):

* `Work.SSGRoute.CC.mag4` — the mod-`2` degree-`4` component of the Magnus image at truncation `5` —
  descends to `E(4,4) = γ₄P₅/P₅` (`mag4_eq_zero_of_mem_pSeries`), lands in `Wsub` on `γ₄`
  (`mag4_mem_Wsub`), is surjective onto `Wsub` (`mag4_surjective`) and natural under the letter
  permutation (`mag4_congr`);
* `Work.SSGRoute.CC.freeLieFourFixedGeneration` decomposes a `σ`-fixed `v ∈ Wsub` as
  `(w + σw) + θ` with `θ ∈ flgThetaSpan`, and `flgThetaSpan_le` rewrites `flgThetaSpan` as
  `(1+σ)Wsub + selfSpan + brkSpan`;
* each of the three summands is realised by a norm `ν(E) = (δ • E)⁻¹ E`
  (`realize_flgDeltaW`, `realize_selfSpan`, `realize_brkSpan`), and `normG_mul_mag4` makes `mag4 ∘ ν`
  additive over products;
* finally `mag4_pure` identifies the kernel of `mag4` on `γ₄` with `P₅`, which converts the
  equality of classes into the required `δ`-difference.
-/

open scoped commutatorElement

set_option maxHeartbeats 2000000


open Work.CohomologicalShrinking

noncomputable section

/-- In characteristic `2`, `a + a = 0`. -/
theorem add_self_zmodTwo {M : Type*} (a : MonoidAlgebra (ZMod 2) M) : a + a = 0 := by
  conv_lhs => rw [← one_smul (ZMod 2) a, ← one_smul (ZMod 2) a, ← add_smul]
  rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]

namespace gsdFour

variable {G : Type*} [Group G] {n : ℕ}

/-! ## The permutation of the basis of `F(n)` and the descended action -/

/-- The permutation `(i, g) ↦ (i, δ * g)` of the basis of the free operator group `F(n)`. -/
abbrev basisPerm (G : Type*) [Group G] (n : ℕ) (δ : G) : (Fin n × G) ≃ (Fin n × G) :=
  Work.Shrinking.freeOperatorGenPerm (G := G) n δ

@[simp] theorem basisPerm_apply (G : Type*) [Group G] (n : ℕ) (δ : G) (x : Fin n × G) :
    basisPerm G n δ x = (x.1, δ * x.2) := rfl

theorem basisPerm_involutive (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (x : Fin n × G) : basisPerm G n δ (basisPerm G n δ x) = x := by
  simp only [basisPerm_apply]
  rw [← mul_assoc, hδ, one_mul]

theorem basisPerm_ne_self (G : Type*) [Group G] (n : ℕ) (δ : G) (hδ1 : δ ≠ 1)
    (x : Fin n × G) : basisPerm G n δ x ≠ x := by
  intro h
  have h2 : δ * x.2 = x.2 := by
    simpa [basisPerm, Work.Shrinking.freeOperatorGenPerm] using congrArg Prod.snd h
  exact hδ1 (mul_right_cancel (by rw [h2, one_mul]))

/-- The action of `δ` on `F(n)` is the automorphism induced by `basisPerm`. -/
theorem smul_eq_freeGroupCongr (G : Type*) [Group G] (n : ℕ) (δ : G)
    (x : Work.Shrinking.freeOperatorGroup G n) :
    δ • x = FreeGroup.freeGroupCongr (basisPerm G n δ) x := rfl

/-! ## The quotient `Q_{(τ+1)}` and its action on representatives -/

/-- The action of `δ` on `Q_{(τ+1)}` on representatives. -/
theorem flowAction_mk_top (G : Type*) [Group G] (n j : ℕ) (δ : G)
    (y : Work.Shrinking.freeOperatorGroup G n) :
    (flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
        (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨y, Subgroup.mem_top y⟩)
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨δ • y, Subgroup.mem_top _⟩ := by
  have hP : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)) = ⊤ :=
    Subgroup.map_top_of_surjective _
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ).surjective
  have hK : Subgroup.map (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ).toMonoidHom
      (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 :=
    map_refinedTerm_eq 2 _ (tauSucc j j).1 (tauSucc j j).2
  change Work.Shrinking.quotAut ⊤ (flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2) δ hP hK
    (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) ⟨y, Subgroup.mem_top y⟩)
    = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤))
    (Subtype.ext (by simp [Work.Shrinking.subAut_coe]))

/-- Multiplication in `Q_{(τ+1)}` on representatives. -/
theorem flowQuot_mk_top_mul (G : Type*) [Group G] (n j : ℕ)
    (y z : Work.Shrinking.freeOperatorGroup G n) :
    (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      * QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨z, Subgroup.mem_top z⟩
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y * z, Subgroup.mem_top _⟩ := by
  rw [← map_mul]
  rfl

/-- Inversion in `Q_{(τ+1)}` on representatives. -/
theorem flowQuot_mk_top_inv (G : Type*) [Group G] (n j : ℕ)
    (y : Work.Shrinking.freeOperatorGroup G n) :
    ((QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩)⁻¹
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y⁻¹, Subgroup.mem_top _⟩ := by
  rw [← map_inv]
  rfl

/-- A class in `Q_{(τ+1)}` is trivial exactly when the representative lies in the refined term. -/
theorem mk_top_eq_one_iff (G : Type*) [Group G] (n j : ℕ)
    (y : Work.Shrinking.freeOperatorGroup G n) :
    (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1
    ↔ y ∈ flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

end gsdFour

/-! ## The general `(4,4)` diagonal graded step -/

open gsdFour

theorem diagonal_four_general (G : Type) [Group G] [Fintype G] (δ : G) (hδ : δ * δ = 1)
    (hδ1 : δ ≠ 1) (n : ℕ) :
    ∀ c : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2,
      flowQuotSucc 2 G n 4 4 c = 1 →
      flowAction 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2,
        c = (flowAction 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2 δ e)⁻¹ * e := by
  classical
  intro c hc hanti
  -- Step 1: lift `c` to `F`, and record that it lies in `F^{(4,4)}`
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤) c
  set y : Work.Shrinking.freeOperatorGroup G n :=
    (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))).1 with hy
  have hyc : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = c := by
    rw [← hx]
  have hymem : y ∈ flowTerm 2 G n 4 4 := by
    have h2 : (flowQuotSucc 2 G n 4 4 (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨y, Subgroup.mem_top y⟩)) = 1 := by
      rw [hyc]
      exact hc
    rw [flowQuotSucc_mk] at h2
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  -- Step 2: write `y = a * b` with `a ∈ γ₄` and `b ∈ P₅`
  have hN : (flowTerm 2 G n 4 4).Normal :=
    Work.CohomologicalShrinking.refinedTerm_normal 2 _ _ _
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right
      (s := pSeries 2 (Work.Shrinking.freeOperatorGroup G n) 4 ⊓
        centralSeries (Work.Shrinking.freeOperatorGroup G n) 4)
      (t := pSeries 2 (Work.Shrinking.freeOperatorGroup G n) 5)).mp hymem
  have haγ : a ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 3 :=
    ha.2
  have hbP : b ∈ Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) 4 := hb
  have hac : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨a, Subgroup.mem_top a⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = c := by
    have hb' : b ∈ flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2 := by
      show b ∈ refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) 5 1
      rw [refinedTerm_one]
      exact hb
    have hb1 : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨b, Subgroup.mem_top b⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = 1 :=
      (mk_top_eq_one_iff G n 4 b).mpr hb'
    rw [← hyc, ← hab, ← flowQuot_mk_top_mul G n 4 a b, hb1, mul_one]
  -- Step 3: the degree-4 class of `a`, and its `σ`-fixedness
  have hvW : mag4 (Fin n × G) a ∈ Wsub (Fin n × G) := mag4_mem_Wsub haγ
  have hδaγ : δ • a ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 3 := by
    rw [smul_eq_freeGroupCongr]
    exact freeGroupCongr_mem_lowerCentralSeries_three _
      (basisPerm G n δ) haγ
  have hmem : (δ • a) * a ∈ flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2 := by
    have hq : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨(δ • a) * a, Subgroup.mem_top _⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = 1 := by
      have h2 : (⟨δ • a, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup
            (Work.Shrinking.freeOperatorGroup G n))) * ⟨a, Subgroup.mem_top _⟩
          = ⟨(δ • a) * a, Subgroup.mem_top _⟩ := rfl
      rw [← h2, map_mul]
      have hanti' : (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
          ⟨δ • a, Subgroup.mem_top _⟩
        : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = c⁻¹ := by
        rw [← hanti, ← hac]
        exact (flowAction_mk_top G n 4 δ a).symm
      rw [hanti', ← hac, inv_mul_cancel]
    exact (mk_top_eq_one_iff G n 4 ((δ • a) * a)).mp hq
  have hmemP : (δ • a) * a
      ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup (Fin n × G)) 4 := by
    have hh := hmem
    rw [show (flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2)
        = refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) 5 1 from rfl] at hh
    rw [refinedTerm_one] at hh
    exact hh
  have hmag : mag4 (Fin n × G) (δ • a) = mag4 (Fin n × G) a := by
    have h0 : mag4 (Fin n × G) ((δ • a) * a) = 0 :=
      mag4_eq_zero_of_mem_pSeries (Subgroup.mul_mem _ hδaγ haγ) hmemP
    rw [mag4_mul hδaγ haγ] at h0
    rw [add_eq_zero_iff_eq_neg] at h0
    rw [h0, neg_eq_self_zmodTwo]
  have hfix : sigA (Fin n × G) (basisPerm G n δ) (mag4 (Fin n × G) a) = mag4 (Fin n × G) a := by
    rw [← mag4_congr (Fin n × G) (basisPerm G n δ) a]
    rw [← smul_eq_freeGroupCongr G n δ a, hmag]
  -- Step 4: the abstract degree-4 statement
  obtain ⟨w, hwW, hlt⟩ := freeLieFourFixedGeneration (Fin n × G) (basisPerm G n δ)
    (basisPerm_involutive G n δ hδ) (basisPerm_ne_self G n δ hδ1)
    (sigAL (Fin n × G) (basisPerm G n δ)) (fun p q => sigA_mul _ _ p q)
    (sigA_one _ _) (fun x => sigA_single _ _ x) (mag4 (Fin n × G) a) hvW hfix
  have hlt2 := flgThetaSpan_le (Fin n × G) (basisPerm G n δ) (basisPerm_involutive G n δ hδ) hlt
  obtain ⟨θ₁, hθ₁, s₂, hs₂, hsum⟩ := Submodule.mem_sup.mp hlt2
  obtain ⟨θ₀, hθ₀, s₁, hs₁, hsum2⟩ := Submodule.mem_sup.mp hθ₁
  -- Step 5: realise the three pieces
  have hΔw : (w + sigA (Fin n × G) (basisPerm G n δ) w)
      ∈ flgDeltaW (Fin n × G) (sigAL (Fin n × G) (basisPerm G n δ)) := by
    rw [flgDeltaW, Submodule.mem_map]
    refine ⟨w, hwW, ?_⟩
    rw [LinearMap.add_apply, LinearMap.id_apply]
    exact add_comm _ _
  have hΔ : (w + sigA (Fin n × G) (basisPerm G n δ) w) + θ₀
      ∈ flgDeltaW (Fin n × G) (sigAL (Fin n × G) (basisPerm G n δ)) :=
    Submodule.add_mem _ hΔw hθ₀
  obtain ⟨z₀, hz₀γ, hz₀mag⟩ := realize_flgDeltaW (Fin n × G) (basisPerm G n δ)
    ((w + sigA (Fin n × G) (basisPerm G n δ) w) + θ₀) hΔ
  obtain ⟨e₂, he₂γ, he₂mag⟩ := realize_selfSpan (Fin n × G) (basisPerm G n δ)
    (basisPerm_involutive G n δ hδ) (basisPerm_ne_self G n δ hδ1) s₁ hs₁
  obtain ⟨e₃, he₃γ, he₃mag⟩ := realize_brkSpan (Fin n × G) (basisPerm G n δ)
    (basisPerm_involutive G n δ hδ) s₂ hs₂
  have h23 := normG_mul_mag4 (Fin n × G) (basisPerm G n δ) e₂ e₃ he₂γ he₃γ
  have h123 := normG_mul_mag4 (Fin n × G) (basisPerm G n δ) z₀ (e₂ * e₃) hz₀γ h23.1
  have hmageq : mag4 (Fin n × G)
      (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))
      = mag4 (Fin n × G) a := by
    rw [h123.2, h23.2, hz₀mag, he₂mag, he₃mag]
    rw [show mag4 (Fin n × G) a
        = (mag4 (Fin n × G) a - (w + sigA (Fin n × G) (basisPerm G n δ) w))
          + (w + sigA (Fin n × G) (basisPerm G n δ) w) from (sub_add_cancel _ _).symm]
    -- `hsum` is phrased with the linear map `sigAL`, the goal with the ring hom `sigA`
    have hsumA : θ₁ + s₂
        = mag4 (Fin n × G) a - (w + sigA (Fin n × G) (basisPerm G n δ) w) := hsum
    rw [← hsumA, ← hsum2]
    abel
  -- Step 6: conclude by purity
  have hEγ : normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃))
      ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 3 := h123.1
  have huγ : a * (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))⁻¹
      ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 3 :=
    Subgroup.mul_mem _ haγ (Subgroup.inv_mem _ hEγ)
  have humag : mag4 (Fin n × G)
      (a * (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))⁻¹) = 0 := by
    rw [mag4_mul haγ (Subgroup.inv_mem _ hEγ), mag4_inv hEγ, hmageq]
    exact add_self_zmodTwo _
  have huP : a * (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))⁻¹
      ∈ Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) 4 :=
    mag4_pure huγ humag
  have hclass : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨a, Subgroup.mem_top a⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2)
      = QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)), Subgroup.mem_top _⟩ := by
    have huP' : a * (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))⁻¹
        ∈ flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2 := by
      rw [show (flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2)
          = refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) 5 1 from rfl, refinedTerm_one]
      exact huP
    have h1 : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨a * (normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)))⁻¹, Subgroup.mem_top _⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2) = 1 :=
      (mk_top_eq_one_iff G n 4 _).mpr huP'
    have h2 : (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
        ⟨a, Subgroup.mem_top a⟩
      : flowQuotient 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2)
        * (QuotientGroup.mk'
          ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
          ⟨normG (Fin n × G) (basisPerm G n δ) (z₀ * (e₂ * e₃)), Subgroup.mem_top _⟩)⁻¹ = 1 := by
      rw [flowQuot_mk_top_inv, flowQuot_mk_top_mul]
      exact h1
    exact mul_inv_eq_one.mp h2
  refine ⟨QuotientGroup.mk'
    ((flowTerm 2 G n (tauSucc 4 4).1 (tauSucc 4 4).2).subgroupOf ⊤)
    ⟨z₀ * (e₂ * e₃), Subgroup.mem_top _⟩, ?_⟩
  rw [← hac, hclass]
  rw [flowAction_mk_top G n 4 δ (z₀ * (e₂ * e₃))]
  rw [← map_inv, ← map_mul]
  rfl

/-! ## The target -/

/-- **The `(4,4)` diagonal instance of the `p = 2` graded step, in target shape.**

`n` arbitrary, `G = Multiplicative (ZMod 2)`, `δ = ofAdd 1`, `Q_{(i,j)} = flowQuotient 2 G n i j`,
`E = ker(flowQuotSucc 2 G n 4 4)` (the diagonal layer `γ₄P₅/P₅` of `F(n)`); every `δ`-anti-fixed `c ∈ E`
is a `δ`-difference `c = (flowAction 2 G n _ _ δ e)⁻¹ * e` in the ambient quotient `Q_{(tauSucc 4 4)}`.
The witness `e` is required only in the *ambient* `Q_{(5,1)}`: the strong form with `e ∈ E` is FALSE.

This is one instance of `Work.SSGRoute.gradedStep_diagonal` (the even-diagonal family of the refined-pair
graded step `Work.SSGRoute.GradedStep`), and the open part of the surviving route to
`Work.SSGRoute.freeGroup_refinedTerm_lifting_fin_zmodTwo` (the `LayerGen` route is refuted; see
`Submission/Work/SSGRoute/STATUS_freeGroup_refinedTerm_lifting_fin_zmodTwo.md`).  It is true, with
concrete witnesses (exact Magnus-model computations): the `DiagonalCore` formulation of this instance is
**FALSE** (the `δ`-paired products `⁅A⁻¹,(δ•A)⁻¹⁆` have weight `2·wt(A)`, below the graded piece), so a
proof must not use that generating family.

Working witness families (per `NOTE_witnesses_diagonal_four_from_lns3_agent.md`, verified for `m ≤ 5`):
* self pairs: `w = A·[x⁻¹,σx]·A` with `A = x·σx` (for `X = {a,b}`, `σ` = swap: `A = ab`,
  `w = a b a b⁻¹ a⁻¹ b a b = A·[a⁻¹,b]·A`);
* twisted/cross pairs: `⁅x⁻¹,y⁆·⁅σx⁻¹,σy⁆`; the older candidate `(x_i x_j)·[x_i⁻¹,x_j]·(x_i x_j)` is
  recorded in §6 of `GRADEDSTEP_DIAGONAL_FOUR_DIAGNOSIS.md` as *failing* the `2`-adic congruence.
Structurally the witnesses have even abelianisation (`x₁(w) ∈ 2·I`) and `σ`-symmetric degree-`2` Magnus
image modulo `8`, which is what makes the carry terms `(σx)^k·x` cancel in degree `4` of
`(1+σx)⁻¹(1+x)`. -/
theorem gradedStep_diagonal_zmodTwo_four (n : ℕ) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 (Multiplicative (ZMod 2)) n
        (Work.CohomologicalShrinking.tauSucc 4 4).1 (Work.CohomologicalShrinking.tauSucc 4 4).2,
      Work.SSGRoute.flowQuotSucc 2 (Multiplicative (ZMod 2)) n 4 4 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 (Multiplicative (ZMod 2)) n
        (Work.CohomologicalShrinking.tauSucc 4 4).1 (Work.CohomologicalShrinking.tauSucc 4 4).2
        (Multiplicative.ofAdd (1 : ZMod 2)) c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 (Multiplicative (ZMod 2)) n
            (Work.CohomologicalShrinking.tauSucc 4 4).1
            (Work.CohomologicalShrinking.tauSucc 4 4).2,
        c = (Work.CohomologicalShrinking.flowAction 2 (Multiplicative (ZMod 2)) n
              (Work.CohomologicalShrinking.tauSucc 4 4).1
              (Work.CohomologicalShrinking.tauSucc 4 4).2
              (Multiplicative.ofAdd (1 : ZMod 2)) e)⁻¹ * e :=
  diagonal_four_general (Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2))
    (by decide) (by decide) n

end

end Work.SSGRoute.CC.LNS3B
