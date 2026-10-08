import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Dade.complement_and_sqrtSet

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical

variable {G : Type*} [Group G] [Finite G]

/-!
# The objects of Dade's Theorem 6.8

Let `S` be a Sylow `2`-subgroup of a finite group `G` and `d : GenQuaternionData ↥S` its
generalized quaternion presentation (`τ = d.tau` of order `2 ^ n`, `n ≥ 2`).  This file
introduces the three objects of Dade's proof:

* `sigma S d = τ ^ 2`, of order `2 ^ (n-1)`,
* `iota S d = τ ^ (2 ^ (n-1))`, the unique involution of `S`,
* `Hsub S d = N_G (⟨σ⟩)`, the normalizer of `⟨σ⟩` (the normalizer of the TI set `√σ`).
-/

/-- `σ = τ ^ 2`: the square of the generalized-quaternion generator `τ`. -/
def sigma (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) : G :=
  ((d.tau : ↥S) : G) ^ 2

/-- `ι = τ ^ (2 ^ (n-1))`: the unique involution of `S`. -/
def iota (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) : G :=
  ((d.tau : ↥S) : G) ^ (2 ^ (d.n - 1))

/-- `H = N_G (⟨σ⟩)`: the normalizer of `⟨σ⟩`, the normalizer of the TI set `√σ`. -/
def Hsub (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) : Subgroup G :=
  Subgroup.normalizer (Subgroup.zpowers (sigma S d))

@[simp] lemma sigma_def (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    sigma S d = ((d.tau : ↥S) : G) ^ 2 := rfl

@[simp] lemma iota_def (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    iota S d = ((d.tau : ↥S) : G) ^ (2 ^ (d.n - 1)) := rfl

@[simp] lemma Hsub_def (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    Hsub S d = Subgroup.normalizer (Subgroup.zpowers (sigma S d)) := rfl

/-- `σ` has order `2 ^ (n-1)`. -/
lemma orderOf_sigma (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    orderOf (sigma S d) = 2 ^ (d.n - 1) := tau_sq_order S d

/-- `ι` is an involution. -/
lemma orderOf_iota (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    orderOf (iota S d) = 2 := by
  have h := (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).2.2.1
  have hcoe : iota S d = (((d.tau ^ (2 ^ (d.n - 1)) : ↥S)) : G) := by
    rw [iota_def, Subgroup.coe_pow]
  rw [hcoe, Subgroup.orderOf_coe]
  exact h

/-- `ι ^ 2 = 1`. -/
lemma iota_sq (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    iota S d ^ 2 = 1 := by
  rw [show (2 : ℕ) = orderOf (iota S d) from (orderOf_iota S d).symm]
  exact pow_orderOf_eq_one _

/-- `ι` is a power of `σ`: `ι = σ ^ (2 ^ (n-2))`. -/
lemma iota_eq_sigma_zpow (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : iota S d = sigma S d ^ (2 ^ (d.n - 2)) := by
  rw [iota_def, sigma_def]
  rw [← pow_mul]
  congr 1
  have h : 2 ^ (d.n - 1) = 2 ^ (d.n - 2) * 2 := by
    rw [show d.n - 1 = (d.n - 2) + 1 by omega, pow_succ]
  rw [h]
  ring

/-- `ι ∈ ⟨σ⟩`. -/
lemma iota_mem_zpowers_sigma (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    iota S d ∈ Subgroup.zpowers (sigma S d) := by
  rw [iota_eq_sigma_zpow S d hn]
  exact Subgroup.npow_mem_zpowers (sigma S d) (2 ^ (d.n - 2))

/-- `σ ≠ 1`. -/
lemma sigma_ne_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : sigma S d ≠ 1 := by
  simp only [sigma_def]
  exact tau_sq_ne_one S d hn

/-- `1 ∉ √σ`. -/
lemma one_notMem_sqrtSet (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : (1 : G) ∉ Work.BrauerSuzuki.sqrtSet (sigma S d) := by
  rw [Work.BrauerSuzuki.mem_sqrtSet, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
  exact sigma_ne_one S d hn

/-- `ι` is the unique involution of the Sylow subgroup `S`. -/
lemma eq_iota_of_mem_sylow_of_orderOf_eq_two (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    {x : G} (hx : x ∈ (S : Subgroup G)) (hx2 : orderOf x = 2) : x = iota S d := by
  have hbasic := (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).2.2.2.1
  have hmem : (⟨x, hx⟩ : ↥S) = d.tau ^ (2 ^ (d.n - 1)) :=
    hbasic (⟨x, hx⟩ : ↥S) (by rw [Subgroup.orderOf_mk]; exact hx2)
  have hcoe := congrArg (Subtype.val) hmem
  rw [iota_def]
  simpa using hcoe

/-- `ι ∈ S`. -/
lemma iota_mem_sylow (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    iota S d ∈ (S : Subgroup G) := by
  rw [iota_def]
  exact (S : Subgroup G).pow_mem d.tau.2 _

end Work.BrauerSuzuki.Dade
