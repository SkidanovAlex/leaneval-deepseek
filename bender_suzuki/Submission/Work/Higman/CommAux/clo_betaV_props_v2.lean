import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.H8.pairing_foundations
import Submission.Work.Higman.clo_betaV_aux
import Submission.Work.Higman.h8_bracket
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.clo_pair_props

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.CommAux

open Work.Higman

variable {P : Type} [Group P] [Finite P]
variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-! ## Additivity of the bracket on the second layer, modulo `A⁴`

The bracket `⁅u, a⁆` of `u ∈ C` with `a ∈ A` lies in `A²` (unipotence) and is additive modulo
`A⁴` in each variable (`h8_bracket`).  After raising to `2 ^ (e-2)` — which kills exactly `A⁴`
(`powSub_four_ker`) — this becomes exact additivity in the group `Ω₁(P)`. -/

/-- **Additivity of `a ↦ ⁅u, a⁆^2^(e-2)` in the first variable.** -/
theorem betaV_comm_pow_add_left (S : CloH8Data h A C) (u v : ↥C) (a : ↥A) :
    (⁅(u : P) * (v : P), (a : P)⁆) ^ 2 ^ (S.e - 2)
      = (⁅(u : P), (a : P)⁆) ^ 2 ^ (S.e - 2)
        * (⁅(v : P), (a : P)⁆) ^ 2 ^ (S.e - 2) := by
  obtain ⟨_, _, _, h4, _⟩ := h8_bracket h S.hA S.hAC S.hCd
  have hx : ⁅(u : P), (a : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA (u : P) (a : P) a.2
  have hy : ⁅(v : P), (a : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA (v : P) (a : P) a.2
  have hxy : ⁅(u : P), (a : P)⁆ * ⁅(v : P), (a : P)⁆ ∈ powSub A 2 :=
    (powSub A 2).mul_mem hx hy
  have hw : ⁅(u : P) * (v : P), (a : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA ((u : P) * (v : P)) (a : P) a.2
  have hc : ⁅(u : P) * (v : P), (a : P)⁆
      * (⁅(u : P), (a : P)⁆ * ⁅(v : P), (a : P)⁆)⁻¹ ∈ powSub A 4 := by
    simpa only [commutatorElement_def]
      using h4 (u : P) u.2 (v : P) v.2 (a : P) a.2
  have hmain := pow_two_pow_sub_two_class h S.hA S.he1 hxy hw hc
  rw [hmain,
    mul_pow_of_mem h S.hA (powSub_le (A := A) (n := 2) (by norm_num) hx)
      (powSub_le (A := A) (n := 2) (by norm_num) hy) (2 ^ (S.e - 2))]

/-- **Additivity of `a ↦ ⁅u, a⁆^2^(e-2)` in the second variable.** -/
theorem betaV_comm_pow_add_right (S : CloH8Data h A C) (u : ↥C) (a b : ↥A) :
    (⁅(u : P), (a : P) * (b : P)⁆) ^ 2 ^ (S.e - 2)
      = (⁅(u : P), (a : P)⁆) ^ 2 ^ (S.e - 2)
        * (⁅(u : P), (b : P)⁆) ^ 2 ^ (S.e - 2) := by
  obtain ⟨_, _, _, _, h5⟩ := h8_bracket h S.hA S.hAC S.hCd
  have hx : ⁅(u : P), (a : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA (u : P) (a : P) a.2
  have hy : ⁅(u : P), (b : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA (u : P) (b : P) b.2
  have hxy : ⁅(u : P), (a : P)⁆ * ⁅(u : P), (b : P)⁆ ∈ powSub A 2 :=
    (powSub A 2).mul_mem hx hy
  have hw : ⁅(u : P), (a : P) * (b : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA (u : P) ((a : P) * (b : P)) (A.mul_mem a.2 b.2)
  have hc : ⁅(u : P), (a : P) * (b : P)⁆
      * (⁅(u : P), (a : P)⁆ * ⁅(u : P), (b : P)⁆)⁻¹ ∈ powSub A 4 := by
    simpa only [commutatorElement_def]
      using h5 (u : P) u.2 (a : P) a.2 (b : P) b.2
  have hmain := pow_two_pow_sub_two_class h S.hA S.he1 hxy hw hc
  rw [hmain,
    mul_pow_of_mem h S.hA (powSub_le (A := A) (n := 2) (by norm_num) hx)
      (powSub_le (A := A) (n := 2) (by norm_num) hy) (2 ^ (S.e - 2))]

/-- The product in `A` of lifts of `w` and `w'` is a lift of `w * w'`. -/
theorem cloLiftA_mul_spec (S : CloH8Data h A C) (w w' : ↥(omega1 P)) :
    (((cloLiftA S w * cloLiftA S w' : ↥A) : P)) ^ 2 ^ (S.e - 1)
      = (((w * w' : ↥(omega1 P)) : P)) := by
  rw [Subgroup.coe_mul,
    mul_pow_of_mem h S.hA (cloLiftA S w).2 (cloLiftA S w').2 (2 ^ (S.e - 1)),
    cloLiftA_spec S w, cloLiftA_spec S w', Subgroup.coe_mul]

theorem clo_betaV_props_v2 {P : Type} [Group P] [Finite P] {h : Work.Higman.IsSuzuki2Grp P}
    {A C : Subgroup P} [A.Normal] (S : Work.Higman.CloH8Data h A C) :
    (∀ (x : ↥C ⧸ (A.subgroupOf C)) (u : ↥C) (w : ↥(Work.Higman.omega1 P)) (a : ↥A),
      QuotientGroup.mk u = x → (a : P) ^ 2 ^ (S.e - 1) = (w : P) →
      ((Work.Higman.cloBetaV S x w : ↥(Work.Higman.omega1 P)) : P)
        = ((commutatorElement (G := P)).bracket ((u : P)) ((a : P))) ^ 2 ^ (S.e - 2)) ∧
    (∀ x x' : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(Work.Higman.omega1 P),
      Work.Higman.cloBetaV S (x * x') w = Work.Higman.cloBetaV S x w * Work.Higman.cloBetaV S x' w) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w w' : ↥(Work.Higman.omega1 P),
      Work.Higman.cloBetaV S x (w * w') = Work.Higman.cloBetaV S x w * Work.Higman.cloBetaV S x w') ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(Work.Higman.omega1 P),
      Work.Higman.cloXiOm h (Work.Higman.cloBetaV S x w) =
        Work.Higman.cloBetaV S (Work.Higman.cloXiQuot h S.hA.map_eq S.hCinv x)
          (Work.Higman.cloXiOm h w)) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), Work.Higman.cloBetaV S x (Work.Higman.cloSM S x) = 1) ∧
    (∃ x : ↥C ⧸ (A.subgroupOf C), ∃ w : ↥(Work.Higman.omega1 P),
      Work.Higman.cloBetaV S x w ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. the representative formula
    intro x u w a hu haw
    exact H8.cloBetaV_mk S x w u a hu haw
  · -- 2. additivity in the first variable
    intro x x' w
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    rw [H8.cloBetaV_mk S (x * x') w (cloRepC x * cloRepC x') (cloLiftA S w)
          (by rw [QuotientGroup.mk_mul, cloRepC_spec, cloRepC_spec]) (cloLiftA_spec S w),
        H8.cloBetaV_mk S x w (cloRepC x) (cloLiftA S w) (cloRepC_spec x) (cloLiftA_spec S w),
        H8.cloBetaV_mk S x' w (cloRepC x') (cloLiftA S w) (cloRepC_spec x') (cloLiftA_spec S w)]
    simpa only [Subgroup.coe_mul] using
      betaV_comm_pow_add_left S (cloRepC x) (cloRepC x') (cloLiftA S w)
  · -- 3. additivity in the second variable
    intro x w w'
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    have hab := cloLiftA_mul_spec S w w'
    rw [H8.cloBetaV_mk S x (w * w') (cloRepC x) (cloLiftA S w * cloLiftA S w')
          (cloRepC_spec x) hab,
        H8.cloBetaV_mk S x w (cloRepC x) (cloLiftA S w) (cloRepC_spec x) (cloLiftA_spec S w),
        H8.cloBetaV_mk S x w' (cloRepC x) (cloLiftA S w') (cloRepC_spec x) (cloLiftA_spec S w')]
    simpa only [Subgroup.coe_mul] using
      betaV_comm_pow_add_right S (cloRepC x) (cloLiftA S w) (cloLiftA S w')
  · -- 4. `ξ`-equivariance
    intro x w
    induction x using QuotientGroup.induction_on with
    | _ u =>
      rw [cloXiQuot_mk h S.hA.map_eq S.hCinv u]
      apply Subtype.ext
      rw [cloXiOm_apply]
      let a₀ : ↥A := cloLiftA S w
      have haw : ((a₀ : P)) ^ 2 ^ (S.e - 1) = (w : P) := cloLiftA_spec S w
      let a' : ↥A := ⟨h.xi (a₀ : P), by
        have hmem := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) a₀.2
        rwa [S.hA.map_eq] at hmem⟩
      have haw' : ((a' : P)) ^ 2 ^ (S.e - 1) = (cloXiOm h w : P) := by
        show (h.xi (a₀ : P)) ^ 2 ^ (S.e - 1) = (cloXiOm h w : P)
        rw [← map_pow, haw, cloXiOm_apply]
      rw [H8.cloBetaV_mk S (QuotientGroup.mk u) w u a₀ rfl haw,
        H8.cloBetaV_mk S (QuotientGroup.mk (cloXiC h S.hCinv u)) (cloXiOm h w)
          (cloXiC h S.hCinv u) a' rfl haw']
      rw [map_pow, cloXiSub_apply h S.hCinv u,
        map_commutatorElement (h.xi : MulAut P) (u : P) (a₀ : P)]
  · -- 5. `cloBetaV` vanishes on the diagonal `w = cloSM S x`
    intro x
    induction x using QuotientGroup.induction_on with
    | _ u =>
      apply Subtype.ext
      rw [Subgroup.coe_one]
      let a : ↥A := ⟨(u : P) ^ 2, S.hC2 (pow_mem_powSub (A := C) (n := 2) u.2)⟩
      have haw : ((a : P)) ^ 2 ^ (S.e - 1) = (cloSM S (QuotientGroup.mk u) : P) := by
        show ((u : P) ^ 2) ^ 2 ^ (S.e - 1) = _
        rw [cloSM_mk S u, ← pow_mul,
          show 2 * 2 ^ (S.e - 1) = 2 ^ S.e from by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel S.he]]
      rw [H8.cloBetaV_mk S (QuotientGroup.mk u) (cloSM S (QuotientGroup.mk u)) u a rfl haw]
      have hcomm : ⁅(u : P), ((u : P) ^ 2)⁆ = 1 := by rw [commutatorElement_def]; group
      change (⁅(u : P), ((u : P) ^ 2)⁆) ^ 2 ^ (S.e - 2) = 1
      rw [hcomm, one_pow]
  · -- 6. non-triviality
    by_contra hcon
    push_neg at hcon
    have hall : ∀ x ∈ C, ∀ y ∈ A, ⁅x, y⁆ ∈ powSub A 4 := by
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ powSub A 2 := commutator_mem_powSub_two h S.hA x y hy
      have hw : y ^ 2 ^ (S.e - 1) ∈ omega1 P :=
        mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hy
      have hz : ((cloBetaV S (QuotientGroup.mk ⟨x, hx⟩) ⟨y ^ 2 ^ (S.e - 1), hw⟩
            : ↥(omega1 P)) : P) = (⁅x, y⁆) ^ 2 ^ (S.e - 2) :=
        H8.cloBetaV_mk S _ _ ⟨x, hx⟩ ⟨y, hy⟩ rfl rfl
      have h2 : (⁅x, y⁆) ^ 2 ^ (S.e - 2) = 1 := by
        rw [← hz, hcon]
        rfl
      exact (powSub_four_ker h S.hA S.he1 S.hkey hmem).mpr h2
    have hle : ⁅C, A⁆ ≤ powSub A 4 := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact hall x hx y hy
    have hle2 : powSub A 2 ≤ powSub A 4 := by
      rw [← commutator_C_A_eq h S.hA S.hCn S.hC2 S.hCd]
      exact hle
    have h42 : powSub A 4 ≤ powSub A 2 := by
      have hstep := powSub_powSub S.hA.abelian 2 2
      rw [show (2 : ℕ) * 2 = 4 from by norm_num] at hstep
      rw [← hstep]
      exact powSub_le (A := powSub A 2) (n := 2) (by norm_num)
    exact H8.powSub_two_ne_powSub_four S (le_antisymm hle2 h42)

end Work.Higman.CommAux
