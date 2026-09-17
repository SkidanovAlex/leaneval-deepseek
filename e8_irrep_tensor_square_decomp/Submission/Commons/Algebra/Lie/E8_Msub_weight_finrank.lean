import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_simple_root_weightSpace_finrank_compat
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_W_le_Msub
import Submission.Commons.Algebra.Lie.e8_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis
import Submission.Commons.Algebra.Lie.UniversalEnveloping.lift_incl_range
import Submission.Commons.Algebra.Lie.UniversalEnveloping.lift_incl_injective
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
import Submission.Commons.LinearAlgebra.exists_separating_functional
import Submission.Commons.Algebra.BigOperators.exists_equiv_sortedList_fun

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section
open scoped BigOperators

namespace Commons.Algebra.Lie

open Commons.Algebra.Lie.SerreConstruction
open Commons.LinearAlgebra.Matrix.Cartan

abbrev PR : Type := ↥(E8posRoots.P)

noncomputable instance PR.linearOrder : LinearOrder PR :=
  LinearOrder.lift' (fun α : PR => Finset.equivFin (E8posRoots.P) α)
    (fun a b h => (Finset.equivFin (E8posRoots.P)).injective h)

def PRle (a b : PR) : Prop := (Finset.equivFin (E8posRoots.P) a) ≤ (Finset.equivFin (E8posRoots.P) b)

/-- The weight space of `U(e₈)` at an integral weight. -/
def uwZ (μ : Fin 8 → ℤ) : Submodule ℂ U8 := uW (fun i => (μ i : ℂ))

lemma mem_uwZ_iff {μ : Fin 8 → ℤ} {x : U8} :
    x ∈ uwZ μ ↔ ∀ i : Fin 8, hh i * x - x * hh i = ((μ i : ℤ) : ℂ) • x := by
  rw [uwZ, mem_uW_iff]
  simp only [Ring.lie_def]

lemma posRoot_isPosRoot (α : PR) : E8posRoots.IsPosRoot (α : Fin 8 → ℤ) :=
  (E8posRoots.memP _).mp α.2

lemma posRoot_qZ (α : PR) : E8NormTwo.qZ (α : Fin 8 → ℤ) = 2 := (posRoot_isPosRoot α).1
lemma posRoot_ne_zero (α : PR) : (α : Fin 8 → ℤ) ≠ 0 := (posRoot_isPosRoot α).2.1
lemma posRoot_coords_nonneg (α : PR) (i : Fin 8) : 0 ≤ E8posRoots.coords (α : Fin 8 → ℤ) i :=
  (posRoot_isPosRoot α).2.2 i

lemma exists_coords_repr (α : PR) :
    ∃ n : Fin 8 → ℕ, n ≠ 0 ∧
      (α : Fin 8 → ℤ) = Commons.Algebra.Lie.wcoord (fun i => (n i : ℤ)) := by
  have hne : (α : Fin 8 → ℤ) ≠ 0 := posRoot_ne_zero α
  refine ⟨fun i => (E8posRoots.coords (α : Fin 8 → ℤ) i).toNat, ?_, ?_⟩
  · intro h
    refine hne ?_
    have h1 : E8posRoots.coords (α : Fin 8 → ℤ) = 0 := by
      funext i
      have hh := congrFun h i
      simp only [Pi.zero_apply] at hh
      have h2 : 0 ≤ E8posRoots.coords (α : Fin 8 → ℤ) i := posRoot_coords_nonneg α i
      exact le_antisymm (Int.toNat_eq_zero.mp hh) h2
    have h3 := E8posRoots.mulVec_coords (α : Fin 8 → ℤ)
    rw [h1, Matrix.mulVec_zero] at h3
    exact h3.symm
  · have hcast : (fun i => (((E8posRoots.coords (α : Fin 8 → ℤ) i).toNat : ℕ) : ℤ))
        = E8posRoots.coords (α : Fin 8 → ℤ) := by
      funext j
      exact Int.toNat_of_nonneg (posRoot_coords_nonneg α j)
    rw [hcast]
    exact (E8posRoots.mulVec_coords (α : Fin 8 → ℤ)).symm

lemma e8Nrm_eq_qZ (μ : Fin 8 → ℤ) : e8Nrm μ = (E8NormTwo.qZ μ : ℚ) :=
  E8NormTwo.e8q_eq_qZ μ

lemma e8Nrm_neg (μ : Fin 8 → ℤ) : e8Nrm (-μ) = e8Nrm μ := by
  rw [e8Nrm_eq_qZ, e8Nrm_eq_qZ, E8_qZ_neg]

theorem finrank_e8W_neg_posRoot (α : PR) :
    Module.finrank ℂ ↥(e8W (-(α : Fin 8 → ℤ))) = 1 := by
  have h2 : e8Nrm (-(α : Fin 8 → ℤ)) = 2 := by
    rw [e8Nrm_neg, e8Nrm_eq_qZ, posRoot_qZ]
    norm_num
  exact e8_root_weightSpace_finrank_eq_one (-(α : Fin 8 → ℤ)) (neg_ne_zero.mpr (posRoot_ne_zero α)) h2

lemma e8W_neg_wcoord_eq (n : Fin 8 → ℕ) :
    e8W (-(Commons.Algebra.Lie.wcoord (fun i => (n i : ℤ)))) = W (-(NWtSum n)) := by
  have hfun : (fun j => (((-(Commons.Algebra.Lie.wcoord (fun i => (n i : ℤ)))) j : ℤ) : ℂ))
      = -(NWtSum n) := by
    funext j
    rw [NWtSum_eq_wcoord]
    simp
  show W (fun j => (((-(Commons.Algebra.Lie.wcoord (fun i => (n i : ℤ)))) j : ℤ) : ℂ))
      = W (-(NWtSum n))
  rw [hfun]

theorem e8W_neg_le_Msub (α : PR) : e8W (-(α : Fin 8 → ℤ)) ≤ (Msub : Submodule ℂ L8) := by
  obtain ⟨n, hn0, hn⟩ := exists_coords_repr α
  rw [hn, e8W_neg_wcoord_eq n]
  exact e8_W_le_Msub hn0

lemma exists_rv (α : PR) :
    ∃ y : Msub, (y : L8) ∈ e8W (-(α : Fin 8 → ℤ)) ∧ (y : L8) ≠ 0 := by
  have hne : e8W (-(α : Fin 8 → ℤ)) ≠ ⊥ := by
    intro h
    have h1 := finrank_e8W_neg_posRoot α
    rw [h, finrank_bot] at h1
    exact one_ne_zero h1.symm
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨⟨x, e8W_neg_le_Msub α hx⟩, hx, hx0⟩

/-- A chosen nonzero root vector of weight `-α` in the negative part `Msub`. -/
noncomputable def rv (α : PR) : Msub := Classical.choose (exists_rv α)

lemma rv_spec (α : PR) :
    (rv α : L8) ∈ e8W (-(α : Fin 8 → ℤ)) ∧ (rv α : L8) ≠ 0 :=
  Classical.choose_spec (exists_rv α)

lemma rv_mem (α : PR) : (rv α : L8) ∈ e8W (-(α : Fin 8 → ℤ)) := (rv_spec α).1
lemma rv_ne_zero (α : PR) : (rv α : L8) ≠ 0 := (rv_spec α).2

/-! ## The weight of `-∑ mᵢαᵢ` as a lattice vector -/

/-- The lattice vector (in `ω`-coordinates) of the weight `-∑ mᵢαᵢ`. -/
def mWt (m : Fin 8 → ℕ) : Fin 8 → ℤ := -(Commons.Algebra.Lie.wcoord (fun i => (m i : ℤ)))

lemma wcoord_nat (m : Fin 8 → ℕ) :
    Commons.Algebra.Lie.wcoord (fun i => (m i : ℤ)) = CartanMatrix.E₈.mulVec (fun i => (m i : ℤ)) := rfl

lemma coords_wcoord (m : Fin 8 → ℤ) :
    E8posRoots.coords (Commons.Algebra.Lie.wcoord m) = m := by
  have h : Commons.Algebra.Lie.wcoord m = CartanMatrix.E₈.mulVec m := rfl
  rw [h, E8posRoots.coords, Matrix.mulVec_mulVec, E8NormTwo.E8inv_mul_E8, Matrix.one_mulVec]

lemma coords_mWt (m : Fin 8 → ℕ) :
    E8posRoots.coords (mWt m) = -(fun i => (m i : ℤ)) := by
  rw [mWt, E8posRoots.coords_neg, coords_wcoord]

lemma W_neg_NWtSum_eq_e8W (m : Fin 8 → ℕ) : W (-(NWtSum m)) = e8W (mWt m) :=
  (e8W_neg_wcoord_eq m).symm

lemma mWt_ne_zero {m : Fin 8 → ℕ} (hm : m ≠ 0) : mWt m ≠ 0 := by
  intro h
  refine hm ?_
  funext i
  have h1 : E8posRoots.coords (mWt m) i = -(m i : ℤ) := by
    rw [coords_mWt m]; rfl
  rw [h] at h1
  have h2 : E8posRoots.coords (0 : Fin 8 → ℤ) i = 0 := by
    simp [E8posRoots.coords]
  rw [h2] at h1
  exact_mod_cast (neg_eq_zero.mp h1.symm : ((m i : ℤ)) = 0)

/-- `Msub ⊓ W 0 = ⊥`. -/
lemma Msub_inf_W_zero : (Msub : Submodule ℂ L8) ⊓ W 0 = ⊥ := by
  have h := W_zero_inf_nplus_sup_nminus
  rw [inf_comm] at h
  refine le_bot_iff.mp ?_
  calc (Msub : Submodule ℂ L8) ⊓ W 0
      ≤ ((nplus : Submodule ℂ L8) ⊔ (nminus : Submodule ℂ L8)) ⊓ W 0 :=
        inf_le_inf_right _ le_sup_right
    _ = ⊥ := h

lemma e8W_neg_eq_span_rv (α : PR) :
    e8W (-(α : Fin 8 → ℤ)) = ℂ ∙ (rv α : L8) :=
  eq_span_singleton_of_mem_of_finrank_eq_one (finrank_e8W_neg_posRoot α) (rv_mem α) (rv_ne_zero α)

theorem Mm_le_span_rv (m : Fin 8 → ℕ) :
    Mm m ≤ Submodule.span ℂ (Set.range (fun α : PR => (rv α : L8))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Mm, NWtSum_zero, neg_zero, Msub_inf_W_zero]
    exact bot_le
  have hν0 : mWt m ≠ 0 := mWt_ne_zero hm
  by_cases hq : E8NormTwo.qZ (mWt m) = 2
  · have hsign := E8_coords_same_sign (mWt m) hν0 hq
    rcases hsign with hpos | hneg
    · exfalso
      have hcoord : E8posRoots.coords (mWt m) = -(fun i => (m i : ℤ)) := coords_mWt m
      have h1 : m = 0 := by
        funext i
        show m i = 0
        have hp := hpos i
        rw [← E8posRoots.coords_apply] at hp
        have h2 : E8posRoots.coords (mWt m) i = -(m i : ℤ) := by rw [hcoord]; rfl
        rw [h2] at hp
        omega
      exact hm h1
    · have hneg' : ∀ i, E8posRoots.coords (mWt m) i ≤ 0 := by
        intro i
        have h := hneg i
        rwa [← E8posRoots.coords_apply] at h
      have hmem : (-(mWt m)) ∈ E8posRoots.P := by
        rw [E8posRoots.memP]
        refine ⟨?_, ?_, ?_⟩
        · rw [E8_qZ_neg]; exact hq
        · exact neg_ne_zero.mpr hν0
        · intro i
          rw [E8posRoots.coords_neg]
          simp only [Pi.neg_apply]
          have := hneg' i
          omega
      set α : PR := ⟨-(mWt m), hmem⟩ with hα
      have hαval : (α : Fin 8 → ℤ) = -(mWt m) := by rw [hα]
      have hmWt : mWt m = -(α : Fin 8 → ℤ) := by rw [hαval, neg_neg]
      rw [Mm]
      refine le_trans inf_le_right ?_
      rw [W_neg_NWtSum_eq_e8W m, hmWt, e8W_neg_eq_span_rv α]
      exact Submodule.span_mono (by rintro x ⟨y, rfl⟩; exact ⟨α, rfl⟩)
  · have hq' : e8Nrm (mWt m) ≠ 2 := by
      rw [e8Nrm_eq_qZ]
      exact_mod_cast hq
    have hbot : e8W (mWt m) = ⊥ := e8W_eq_bot_of_not_root (mWt m) hν0 hq'
    rw [Mm, W_neg_NWtSum_eq_e8W m, hbot]
    exact le_trans inf_le_right bot_le

theorem linearIndependent_rv : LinearIndependent ℂ (fun α : PR => rv α) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : (∑ β ∈ (Finset.univ : Finset PR), g β • (rv β : L8)) = 0 := by
    have h := congrArg (fun y : Msub => (y : L8)) hg
    simpa using h
  intro α
  set wt : PR → Fin 8 → ℂ := fun β => fun i => (((-(β : Fin 8 → ℤ)) i : ℤ) : ℂ) with hwt
  have hwt_inj : Function.Injective wt := by
    intro a b hab
    apply Subtype.ext
    funext i
    have h1 := congrFun hab i
    simp only [hwt] at h1
    have h3 : (-(a : Fin 8 → ℤ)) i = (-(b : Fin 8 → ℤ)) i := Int.cast_injective h1
    simp only [Pi.neg_apply] at h3
    omega
  have hy : ∀ β ∈ (Finset.univ : Finset PR), g β • (rv β : L8) ∈ W (wt β) := by
    intro β _
    exact W_smul_mem _ (rv_mem β)
  have hz : (∑ β ∈ (Finset.univ : Finset PR), g β • (rv β : L8)) ∈ W (wt α) := by
    rw [hsum]
    exact Submodule.zero_mem _
  have hke := killer_extract (Finset.univ : Finset PR) wt (fun β => g β • (rv β : L8)) hy hz
  have hsingle : (∑ β ∈ (Finset.univ.filter (fun β => wt β = wt α)), g β • (rv β : L8))
      = g α • (rv α : L8) := by
    have hfilter : (Finset.univ.filter (fun β => wt β = wt α)) = {α} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ α, rfl⟩
      · intro b hb
        exact hwt_inj (Finset.mem_filter.mp hb).2
    rw [hfilter, Finset.sum_singleton]
  rw [hsum, hsingle] at hke
  rcases smul_eq_zero.mp hke.symm with h | h
  · exact h
  · exact absurd h (rv_ne_zero α)

/-- The `rv α` span `Msub` as a submodule of `L8`. -/
theorem span_rv_eq_Msub :
    Submodule.span ℂ (Set.range (fun α : PR => (rv α : L8))) = (Msub : Submodule ℂ L8) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨α, rfl⟩
    exact (rv α).2
  · have hMsub : (Msub : Submodule ℂ L8) = ⨆ m : Fin 8 → ℕ, Mm m :=
      le_antisymm Msub_le_iSup_Mm (iSup_le fun m => inf_le_left)
    rw [hMsub]
    exact iSup_le Mm_le_span_rv

theorem span_rv_eq_top : Submodule.span ℂ (Set.range rv) = ⊤ := by
  have hmap : (Submodule.span ℂ (Set.range rv)).map (Msub.incl : Msub →ₗ[ℂ] L8)
      = Submodule.span ℂ (Set.range (fun α : PR => (rv α : L8))) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨α, rfl⟩, rfl⟩; exact ⟨α, rfl⟩
    · rintro ⟨α, rfl⟩; exact ⟨rv α, ⟨α, rfl⟩, rfl⟩
  rw [Submodule.eq_top_iff']
  intro x
  have hx : (x : L8) ∈ (Submodule.span ℂ (Set.range rv)).map (Msub.incl : Msub →ₗ[ℂ] L8) := by
    rw [hmap, span_rv_eq_Msub]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

/-- The basis of `Msub` given by the root vectors. -/
noncomputable def MsubBasis : Module.Basis PR ℂ Msub :=
  Module.Basis.mk linearIndependent_rv (le_of_eq span_rv_eq_top.symm)

@[simp] lemma MsubBasis_apply (α : PR) : MsubBasis α = rv α :=
  Module.Basis.mk_apply _ _ _

/-- The algebra morphism `U(Msub) → U(e₈)` induced by the inclusion. -/
noncomputable def phi : UniversalEnvelopingAlgebra ℂ Msub →ₐ[ℂ] U8 :=
  UniversalEnvelopingAlgebra.lift ℂ
    ((UniversalEnvelopingAlgebra.ι ℂ).comp (Msub.incl : Msub →ₗ⁅ℂ⁆ L8))

lemma phi_range :
    phi.range = Algebra.adjoin ℂ (Set.range (fun x : Msub => UniversalEnvelopingAlgebra.ι ℂ (x : L8))) :=
  (Commons.Algebra.Lie.UniversalEnveloping.lift_incl_range Msub).symm

/-- **PBW basis of `U(Msub)`.** -/
noncomputable def pbwB :
    Module.Basis {w : List PR // w.Pairwise PRle} ℂ
      (UniversalEnvelopingAlgebra ℂ Msub) :=
  Classical.choose (Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis ℂ Msub PR MsubBasis)

lemma pbwB_apply (w : {w : List PR // w.Pairwise PRle}) :
    pbwB w = (w.1.map (fun i => UniversalEnvelopingAlgebra.ι ℂ (MsubBasis i))).prod :=
  Classical.choose_spec (Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis ℂ Msub PR MsubBasis) w

/-- The images in `U(e₈)` of the PBW monomials of `U(Msub)`. -/
noncomputable def mB (w : {w : List PR // w.Pairwise PRle}) : U8 := phi (pbwB w)

lemma phi_iota (x : Msub) :
    phi (UniversalEnvelopingAlgebra.ι ℂ x) = UniversalEnvelopingAlgebra.ι ℂ (x : L8) := by
  rw [phi, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

lemma mB_eq_prod (w : {w : List PR // w.Pairwise PRle}) :
    mB w = (w.1.map (fun i => UniversalEnvelopingAlgebra.ι ℂ ((rv i : Msub) : L8))).prod := by
  have h1 : mB w
      = (w.1.map (fun i => phi (UniversalEnvelopingAlgebra.ι ℂ (MsubBasis i)))).prod := by
    rw [mB, pbwB_apply, map_list_prod, List.map_map]
    rfl
  rw [h1]
  refine congrArg List.prod (List.map_congr_left ?_)
  intro i _
  rw [MsubBasis_apply, phi_iota]

/-! ## Weights of the monomials `mB w` -/

lemma wspWeight_iff_uwZ {μ : Fin 8 → ℤ} {u : U8} : wspWeight μ u ↔ u ∈ uwZ μ := by
  rw [mem_uwZ_iff]
  simp only [wspWeight, wspH, hh, Int.cast_smul_eq_zsmul]

lemma uwZ_mul {μ ν : Fin 8 → ℤ} {x y : U8} (hx : x ∈ uwZ μ) (hy : y ∈ uwZ ν) :
    x * y ∈ uwZ (μ + ν) := by
  rw [← wspWeight_iff_uwZ] at hx hy ⊢
  exact wspWeight.mul hx hy

lemma one_mem_uwZ (μ : Fin 8 → ℤ) (h : μ = 0) : (1 : U8) ∈ uwZ μ := by
  subst h
  rw [mem_uwZ_iff]
  intro i
  simp

/-- The sum of the weights of the elements of a list of positive roots. -/
def wsum (w : List PR) : Fin 8 → ℤ := (w.map (fun α : PR => (α : Fin 8 → ℤ))).sum

@[simp] lemma wsum_nil : wsum ([] : List PR) = 0 := rfl

lemma wsum_cons (a : PR) (t : List PR) :
    wsum (a :: t) = (a : Fin 8 → ℤ) + wsum t := by
  simp [wsum]

lemma iota_rv_mem_uwZ (α : PR) :
    UniversalEnvelopingAlgebra.ι ℂ ((rv α : Msub) : L8) ∈ uwZ (-(α : Fin 8 → ℤ)) := by
  rw [uwZ]
  exact iota_mem_uW (rv_mem α)

lemma prod_mem_uwZ (w : List PR) :
    (w.map (fun α : PR => UniversalEnvelopingAlgebra.ι ℂ ((rv α : Msub) : L8))).prod
      ∈ uwZ (-(wsum w)) := by
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, wsum_nil, neg_zero]
      exact one_mem_uwZ 0 rfl
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, wsum_cons, neg_add]
      exact uwZ_mul (iota_rv_mem_uwZ a) ih

lemma mB_mem (w : {w : List PR // w.Pairwise PRle}) : mB w ∈ uwZ (-(wsum w.1)) := by
  rw [mB_eq_prod]
  exact prod_mem_uwZ w.1

lemma phi_injective : Function.Injective phi :=
  Commons.Algebra.Lie.UniversalEnveloping.lift_incl_injective Msub

lemma linearIndependent_mB : LinearIndependent ℂ mB := by
  rw [linearIndependent_iff]
  intro c hc
  have h2 : Finsupp.linearCombination ℂ (fun w => phi (pbwB w)) c
      = phi (Finsupp.linearCombination ℂ pbwB c) := by
    have h := congrArg (fun L : ({w : List PR // w.Pairwise PRle} →₀ ℂ) →ₗ[ℂ] U8 => L c)
      (Finsupp.linearCombination_linear_comp ℂ (v := pbwB) phi.toLinearMap)
    simpa [Function.comp_def] using h
  have h3 : phi (Finsupp.linearCombination ℂ pbwB c) = 0 := by
    rw [← h2]
    exact hc
  have h4 : Finsupp.linearCombination ℂ pbwB c = 0 := by
    apply phi_injective
    rw [h3, map_zero]
  exact (linearIndependent_iff.mp pbwB.linearIndependent) c h4

lemma range_phi_le_span_mB :
    (phi.range.toSubmodule) ≤ Submodule.span ℂ (Set.range mB) := by
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  obtain ⟨u, rfl⟩ := (AlgHom.mem_range phi).mp hy
  have hu : u ∈ Submodule.span ℂ (Set.range pbwB) := by
    rw [pbwB.span_eq]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro z ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [Algebra.smul_def, map_mul, phi.commutes, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c ha

lemma span_mB_le_range_phi : Submodule.span ℂ (Set.range mB) ≤ (phi.range.toSubmodule) := by
  rw [Submodule.span_le]
  rintro y ⟨w, rfl⟩
  exact ⟨pbwB w, rfl⟩

/-! ## Killing the off-weight terms -/

/-- A sum of weight vectors of `U(e₈)` with **distinct** weights, all different from `ν`, which
lies in the weight space `ν`, must be zero termwise. -/
lemma sum_eq_zero_of_mem_uwZ {σ : Type*} [Fintype σ] (μ : σ → Fin 8 → ℤ) (x : σ → U8)
    (ν : Fin 8 → ℤ) (hμ : Function.Injective μ) (hx : ∀ m, x m ∈ uwZ (μ m))
    (hsum : ∑ m, x m ∈ uwZ ν) (hne : ∀ m, μ m ≠ ν) : ∀ m, x m = 0 := by
  classical
  set T : Finset (Fin 8 → ℂ) :=
    (Finset.univ.image (fun m : σ => fun i => ((μ m i : ℤ) : ℂ))) ∪
      {fun i => ((ν i : ℤ) : ℂ)} with hT
  obtain ⟨d, hd⟩ := Commons.LinearAlgebra.exists_separating_functional T
  have hmemμ : ∀ m : σ, (fun i => ((μ m i : ℤ) : ℂ)) ∈ T := by
    intro m
    rw [hT]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ m))
  have hmemν : (fun i => ((ν i : ℤ) : ℂ)) ∈ T := by
    rw [hT]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  refine sum_eq_zero_of_mem_uW (fun m : σ => fun i => ((μ m i : ℤ) : ℂ)) x
    (fun i => ((ν i : ℤ) : ℂ)) (fun m => hx m) hsum d ?_ ?_
  · intro m m' h
    refine hμ (funext fun i => ?_)
    have h2 := hd _ (hmemμ m) _ (hmemμ m') h
    exact Int.cast_injective (congrFun h2 i)
  · intro m h
    exact absurd (funext fun i => Int.cast_injective (congrFun (hd _ (hmemμ m) _ hmemν h) i))
      (hne m)

lemma sum_filter_eq_zero_of_mem_uwZ {σ : Type*} [Fintype σ] (μ : σ → Fin 8 → ℤ) (x : σ → U8)
    (ν : Fin 8 → ℤ) (hμ : Function.Injective μ) (hx : ∀ m, x m ∈ uwZ (μ m))
    (hsum : ∑ m, x m ∈ uwZ ν) :
    ∑ m ∈ Finset.univ.filter (fun m => μ m ≠ ν), x m = 0 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset σ) (fun m => μ m ≠ ν) x
  set s : Finset σ := Finset.univ.filter (fun m => μ m ≠ ν) with hs
  have hcompl : (∑ m ∈ Finset.univ.filter (fun m => ¬ (μ m ≠ ν)), x m) ∈ uwZ ν := by
    refine Submodule.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    have hm' : μ m = ν := by simpa using hm.2
    rw [← hm']
    exact hx m
  have hdiff : (∑ m ∈ s, x m) ∈ uwZ ν := by
    have h1 : (∑ m ∈ s, x m)
        = (∑ m ∈ Finset.univ, x m) - (∑ m ∈ Finset.univ.filter (fun m => ¬ (μ m ≠ ν)), x m) := by
      rw [← hsplit]; abel
    rw [h1]
    exact Submodule.sub_mem _ (by simpa using hsum) hcompl
  have hgoal : ∀ m : ↥s, x m.1 = 0 :=
    sum_eq_zero_of_mem_uwZ (fun m : ↥s => μ m.1) (fun m : ↥s => x m.1) ν
      (fun a b h => Subtype.ext (hμ h)) (fun m => hx m.1)
      (by rw [Finset.univ_eq_attach, Finset.sum_attach]; exact hdiff)
      (fun m => (Finset.mem_filter.mp m.2).2)
  rw [← Finset.sum_attach (s := s)]
  exact Finset.sum_eq_zero (fun m _ => hgoal m)

/-! ## The `-γ`-weight part of the image of `U(n⁻)` -/

/-- The `-γ`-weight part of the image of `U(Msub)` in `U(e₈)`. -/
def Wgamma (γ : Fin 8 → ℤ) : Submodule ℂ U8 := phi.range.toSubmodule ⊓ uwZ (-γ)

/-- The sorted lists of positive roots whose weights sum to `γ`. -/
def Sgamma (γ : Fin 8 → ℤ) : Type :=
  {w : {w : List PR // w.Pairwise PRle} // wsum w.1 = γ}

lemma mB_mem_Wgamma {γ : Fin 8 → ℤ} (w : {w : List PR // w.Pairwise PRle})
    (hw : wsum w.1 = γ) : mB w ∈ Wgamma γ := by
  refine ⟨⟨pbwB w, rfl⟩, ?_⟩
  have h := mB_mem w
  rwa [hw] at h

lemma Wgamma_le_span (γ : Fin 8 → ℤ) :
    Wgamma γ ≤ Submodule.span ℂ (Set.range (fun w : Sgamma γ => mB w.1)) := by
  classical
  intro x hx
  obtain ⟨hxA, hxw⟩ := hx
  have hxspan : x ∈ Submodule.span ℂ (Set.range mB) := range_phi_le_span_mB hxA
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hxspan
  obtain ⟨c, hc⟩ := hxspan
  set wt : {w : List PR // w.Pairwise PRle} → Fin 8 → ℤ := fun w => -(wsum w.1) with hwt
  set T : Finset (Fin 8 → ℤ) := c.support.image wt with hT
  set g : (Fin 8 → ℤ) → U8 :=
    fun m => ∑ w ∈ c.support.filter (fun w => wt w = m), c w • mB w with hg
  have hxT : x = ∑ m ∈ T, g m := by
    rw [← hc, hT, hg]
    exact (Finset.sum_fiberwise_of_maps_to (fun w _ => Finset.mem_image_of_mem wt ‹w ∈ c.support›)
      (fun w => c w • mB w)).symm
  have hg_mem : ∀ m ∈ T, g m ∈ uwZ m := by
    intro m _
    refine Submodule.sum_mem _ (fun w hw => ?_)
    rw [Finset.mem_filter] at hw
    rw [← hw.2]
    exact Submodule.smul_mem _ _ (mB_mem w)
  have hsum_mem : ∑ m ∈ T, g m ∈ uwZ (-γ) := hxT ▸ hxw
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun m => m = -γ) g
  have hpart_mem : (∑ m ∈ T.filter (fun m => m = -γ), g m) ∈ uwZ (-γ) := by
    refine Submodule.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact hm.2 ▸ hg_mem m hm.1
  have hrest_mem : (∑ m ∈ T.filter (fun m => m ≠ -γ), g m) ∈ uwZ (-γ) := by
    have h1 : (∑ m ∈ T.filter (fun m => m ≠ -γ), g m)
        = (∑ m ∈ T, g m) - (∑ m ∈ T.filter (fun m => m = -γ), g m) := by
      rw [← hsplit]; abel
    rw [h1]
    exact Submodule.sub_mem _ hsum_mem hpart_mem
  have hkill : ∑ m ∈ T.filter (fun m => m ≠ -γ), g m = 0 := by
    rw [← Finset.sum_attach (s := T.filter (fun m : Fin 8 → ℤ => m ≠ -γ))]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    exact sum_eq_zero_of_mem_uwZ
      (fun m : ↥(T.filter (fun m : Fin 8 → ℤ => m ≠ -γ)) => (m : Fin 8 → ℤ))
      (fun m : ↥(T.filter (fun m : Fin 8 → ℤ => m ≠ -γ)) => g m.1) (-γ)
      (fun a b h => Subtype.ext h)
      (fun m => hg_mem m.1 (Finset.mem_of_mem_filter m.1 m.2))
      (by rw [Finset.univ_eq_attach, Finset.sum_attach]; exact hrest_mem)
      (fun m => (Finset.mem_filter.mp m.2).2) m
  have hxfinal : x = ∑ m ∈ T.filter (fun m => m = -γ), g m := by
    rw [hxT, ← hsplit, hkill, add_zero]
  rw [hxfinal]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  rw [Finset.mem_filter] at hm
  refine Submodule.sum_mem _ (fun w hw => ?_)
  rw [Finset.mem_filter] at hw
  have hcond : wsum w.1 = γ := by
    have h1 : wt w = m := hw.2
    have h2 : m = -γ := hm.2
    simp only [hwt] at h1
    rw [h2] at h1
    exact neg_inj.mp h1
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨w, hcond⟩, rfl⟩)

lemma span_le_Wgamma (γ : Fin 8 → ℤ) :
    Submodule.span ℂ (Set.range (fun w : Sgamma γ => mB w.1)) ≤ Wgamma γ := by
  rw [Submodule.span_le]
  rintro y ⟨w, rfl⟩
  exact mB_mem_Wgamma w.1 w.2

theorem Wgamma_eq_span (γ : Fin 8 → ℤ) :
    Wgamma γ = Submodule.span ℂ (Set.range (fun w : Sgamma γ => mB w.1)) :=
  le_antisymm (Wgamma_le_span γ) (span_le_Wgamma γ)

/-- The family of monomials, as elements of `Wgamma γ`. -/
noncomputable def WgammaFam (γ : Fin 8 → ℤ) (w : Sgamma γ) : ↥(Wgamma γ) :=
  ⟨mB w.1, mB_mem_Wgamma w.1 w.2⟩

lemma linearIndependent_WgammaFam (γ : Fin 8 → ℤ) :
    LinearIndependent ℂ (WgammaFam γ) := by
  refine LinearIndependent.of_comp (Submodule.subtype (Wgamma γ)) ?_
  convert linearIndependent_mB.comp (fun w : Sgamma γ => (w.1 : {w : List PR // w.Pairwise PRle}))
    Subtype.val_injective using 1
  ext w
  rfl

lemma span_WgammaFam_eq_top (γ : Fin 8 → ℤ) :
    Submodule.span ℂ (Set.range (WgammaFam γ)) = ⊤ := by
  have hmap : (Submodule.span ℂ (Set.range (WgammaFam γ))).map (Submodule.subtype (Wgamma γ))
      = Submodule.span ℂ (Set.range (fun w : Sgamma γ => mB w.1)) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨WgammaFam γ w, ⟨w, rfl⟩, rfl⟩
  rw [Submodule.eq_top_iff']
  intro y
  have hy : (y : U8) ∈ (Submodule.span ℂ (Set.range (WgammaFam γ))).map
      (Submodule.subtype (Wgamma γ)) := by
    rw [hmap, ← Wgamma_eq_span γ]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : z = y := Subtype.ext hzy
  rwa [← hzy']

/-- A basis of the `-γ`-weight part of the image of `U(n⁻)`, indexed by the sorted lists of
positive roots whose weights sum to `γ`. -/
noncomputable def WgammaBasis (γ : Fin 8 → ℤ) : Module.Basis (Sgamma γ) ℂ ↥(Wgamma γ) :=
  Module.Basis.mk (linearIndependent_WgammaFam γ) (le_of_eq (span_WgammaFam_eq_top γ).symm)

/-! ## Heights and the finiteness of the index sets -/

instance PRleDecidableRel : DecidableRel PRle :=
  fun a b => inferInstanceAs (Decidable ((Finset.equivFin (E8posRoots.P) a) ≤
    (Finset.equivFin (E8posRoots.P) b)))

instance PRleIsTrans : IsTrans PR PRle :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩

instance PRleAntisymm : Std.Antisymm PRle :=
  ⟨fun _ _ hab hba => (Finset.equivFin (E8posRoots.P)).injective (le_antisymm hab hba)⟩

instance PRleTotal : Std.Total PRle := ⟨fun a b => le_total _ _⟩

/-- The height functional `v ↦ ∑ᵢ (A⁻¹v)ᵢ` as a `ℤ`-linear map. -/
noncomputable def htLin : (Fin 8 → ℤ) →ₗ[ℤ] ℤ where
  toFun := E8NormTwo.e8ht
  map_add' := by
    intro a b
    simp only [E8NormTwo.e8ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    simp only [E8NormTwo.e8ht, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

lemma htLin_apply (v : Fin 8 → ℤ) : htLin v = E8NormTwo.e8ht v := rfl

/-- The height of a positive root is at least `1`. -/
lemma one_le_e8ht_posRoot (α : PR) : 1 ≤ E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
  have hsum : E8NormTwo.e8ht (α : Fin 8 → ℤ)
      = ∑ i, E8posRoots.coords (α : Fin 8 → ℤ) i := rfl
  rw [hsum]
  obtain ⟨i, hi⟩ : ∃ i, E8posRoots.coords (α : Fin 8 → ℤ) i ≠ 0 := by
    by_contra h
    push Not at h
    refine posRoot_ne_zero α ?_
    have h2 := E8posRoots.mulVec_coords (α : Fin 8 → ℤ)
    rw [show E8posRoots.coords (α : Fin 8 → ℤ) = 0 from funext h, Matrix.mulVec_zero] at h2
    exact h2.symm
  have h1 : (1 : ℤ) ≤ E8posRoots.coords (α : Fin 8 → ℤ) i := by
    have := posRoot_coords_nonneg α i
    omega
  calc (1 : ℤ) ≤ E8posRoots.coords (α : Fin 8 → ℤ) i := h1
    _ ≤ ∑ j, E8posRoots.coords (α : Fin 8 → ℤ) j :=
        Finset.single_le_sum (fun j _ => posRoot_coords_nonneg α j) (Finset.mem_univ i)

lemma e8ht_posRoot_nonneg (α : PR) : 0 ≤ E8NormTwo.e8ht (α : Fin 8 → ℤ) :=
  le_trans (by norm_num) (one_le_e8ht_posRoot α)

lemma e8ht_add (a b : Fin 8 → ℤ) :
    E8NormTwo.e8ht (a + b) = E8NormTwo.e8ht a + E8NormTwo.e8ht b := by
  simp only [E8NormTwo.e8ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma e8ht_nsmul (k : ℕ) (v : Fin 8 → ℤ) :
    E8NormTwo.e8ht (k • v) = (k : ℤ) * E8NormTwo.e8ht v := by
  induction k with
  | zero => simp [E8NormTwo.e8ht]
  | succ k ih => rw [succ_nsmul, e8ht_add, ih]; push_cast; ring

lemma e8ht_sum_nsmul (k : PR → ℕ) :
    E8NormTwo.e8ht (∑ α, k α • (α : Fin 8 → ℤ))
      = ∑ α, (k α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
  calc E8NormTwo.e8ht (∑ α, k α • (α : Fin 8 → ℤ))
      = htLin (∑ α, k α • (α : Fin 8 → ℤ)) := rfl
    _ = ∑ α, htLin (k α • (α : Fin 8 → ℤ)) := map_sum htLin _ _
    _ = ∑ α, (k α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [htLin_apply]
        exact e8ht_nsmul (k α) (α : Fin 8 → ℤ)

/-- The set of functions `k : PR → ℕ` with `∑_α k_α α = γ` is finite. -/
lemma finite_fun_sum_eq (γ : Fin 8 → ℤ) :
    ({k : PR → ℕ | ∑ α, k α • (α : Fin 8 → ℤ) = γ}).Finite := by
  classical
  set N : ℕ := (E8NormTwo.e8ht γ).toNat with hNdef
  refine Set.Finite.subset
    (Finset.finite_toSet (Fintype.piFinset (fun _ : PR => Finset.range (N + 1)))) ?_
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro α
  rw [Finset.mem_range]
  have hsum := e8ht_sum_nsmul k
  rw [hk] at hsum
  have h2 : (k α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) ≤ E8NormTwo.e8ht γ := by
    rw [hsum]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (Int.natCast_nonneg (k i)) (e8ht_posRoot_nonneg i))
      (Finset.mem_univ α)
  have h3 : (k α : ℤ) ≤ E8NormTwo.e8ht γ := by
    have h4 : (k α : ℤ) * 1 ≤ (k α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) :=
      mul_le_mul_of_nonneg_left (one_le_e8ht_posRoot α) (by positivity)
    linarith
  have h0 : 0 ≤ E8NormTwo.e8ht γ := le_trans (by positivity) h3
  have hN : (N : ℤ) = E8NormTwo.e8ht γ := Int.toNat_of_nonneg h0
  omega

noncomputable instance fintype_fun_sum_eq (γ : Fin 8 → ℤ) :
    Fintype {k : PR → ℕ // ∑ α, k α • (α : Fin 8 → ℤ) = γ} :=
  (finite_fun_sum_eq γ).fintype

/-- Flattening a pair of subtype conditions. -/
noncomputable def flattenSgamma (γ : Fin 8 → ℤ) :
    Sgamma γ ≃ {w : List PR // w.Pairwise PRle ∧ wsum w = γ} where
  toFun w := ⟨w.1.1, w.1.2, w.2⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  left_inv w := rfl
  right_inv w := rfl

/-- The sorted lists of positive roots summing to `γ` form a finite type, by comparison with the
finite set of multiplicity functions. -/
noncomputable instance fintypeSgamma (γ : Fin 8 → ℤ) : Fintype (Sgamma γ) :=
  let e := Classical.choose (Commons.Algebra.BigOperators.exists_equiv_sortedList_fun (ι := PR)
    PRle (fun α : PR => (α : Fin 8 → ℤ)) γ)
  Fintype.ofEquiv _ (e.symm.trans (flattenSgamma γ).symm)

/-! ## The target definitions and theorem -/

noncomputable def E8KostantId.KcountP (γ : Fin 8 → ℤ) : ℕ :=
  Nat.card {k : ↥Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P → ℕ //
    ∑ α : ↥Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P, k α • (α : Fin 8 → ℤ) = γ}

noncomputable def E8KostantId.wtPartM (γ : Fin 8 → ℤ) :
    Submodule ℂ (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)) :=
  Submodule.span ℂ {u : UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ) |
    u ∈ Algebra.adjoin ℂ (Set.range (fun x : Commons.Algebra.Lie.SerreConstruction.Msub =>
          UniversalEnvelopingAlgebra.ι ℂ (x : LieAlgebra.e₈ ℂ))) ∧
    ∀ i : Fin 8,
      UniversalEnvelopingAlgebra.ι ℂ (Commons.Algebra.Lie.SerreConstruction.SerreH i) * u
        - u * UniversalEnvelopingAlgebra.ι ℂ (Commons.Algebra.Lie.SerreConstruction.SerreH i)
      = -(((γ i : ℤ)) : ℂ) • u}

lemma wtPartM_eq_Wgamma (γ : Fin 8 → ℤ) : E8KostantId.wtPartM γ = Wgamma γ := by
  have hset : {u : U8 |
        u ∈ Algebra.adjoin ℂ (Set.range (fun x : Msub =>
          UniversalEnvelopingAlgebra.ι ℂ (x : L8))) ∧
        ∀ i : Fin 8, UniversalEnvelopingAlgebra.ι ℂ (SerreH i) * u
            - u * UniversalEnvelopingAlgebra.ι ℂ (SerreH i) = -(((γ i : ℤ)) : ℂ) • u}
      = ↑(phi.range.toSubmodule ⊓ uwZ (-γ)) := by
    ext u
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
      mem_uwZ_iff, hh, Pi.neg_apply, Int.cast_neg]
    rw [phi_range]
  rw [E8KostantId.wtPartM, hset, Submodule.span_eq]
  rfl

lemma finrank_Wgamma (γ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Wgamma γ) = Nat.card (Sgamma γ) := by
  rw [Module.finrank_eq_card_basis (WgammaBasis γ), Nat.card_eq_fintype_card]

lemma card_Sgamma (γ : Fin 8 → ℤ) : Nat.card (Sgamma γ) = E8KostantId.KcountP γ := by
  obtain ⟨e, -⟩ := Commons.Algebra.BigOperators.exists_equiv_sortedList_fun (ι := PR) PRle
    (fun α : PR => (α : Fin 8 → ℤ)) γ
  rw [E8KostantId.KcountP]
  exact Nat.card_congr ((flattenSgamma γ).trans e)

theorem E8_Msub_weight_finrank (γ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(E8KostantId.wtPartM γ) = E8KostantId.KcountP γ := by
  rw [wtPartM_eq_Wgamma γ, finrank_Wgamma γ, card_Sgamma γ]

end Commons.Algebra.Lie
