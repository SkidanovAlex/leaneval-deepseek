import Mathlib
import Submission.Work.Hering.AppVIII.CTwoStepDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The maps induced on `C/Z` and on `Z` by an automorphism of `C(n,ε)`

For `α ∈ Aut C(n,ε)` (`n = 2s+1`, `ε ≠ 0`), the centre is `Z(C) = kerFst = {⟨0,z⟩}`, so `α`
induces additive bijections `fstFun α : K × K → K × K` (on `C/Z`) and `sndFun α : K → K` (on
`Z`), linked by `sndFun α (quadC s ε u) = quadC s ε (fstFun α u)` (the two-step form of "an
automorphism of a central extension commutes with the associated quadratic map").
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

variable {s : ℕ} {ε : KC s}

/-- `α ∈ Aut C(n,ε)` maps the centre into itself. -/
theorem map_mem_center (α : MulAut (CTypeC s ε)) {x : CTypeC s ε}
    (hx : x ∈ Subgroup.center (CTypeC s ε)) : α x ∈ Subgroup.center (CTypeC s ε) := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  obtain ⟨w, rfl⟩ : ∃ w, y = α w := ⟨α.symm y, by simp⟩
  rw [← map_mul, ← map_mul, hx w]

/-- **The centre of `C(n,ε)` is `kerFst`** (for `ε ≠ 0`). -/
theorem mem_center_iff_fst_eq_zero (hε : ε ≠ 0) (x : CTypeC s ε) :
    x ∈ Subgroup.center (CTypeC s ε) ↔ x.fst = 0 := by
  refine ⟨fun h => ?_, fun h => TwoStep.kerFst_le_center h⟩
  rw [TwoStep.mem_center_iff] at h
  have h1 := h (0, 1)
  have h2 := h (1, 0)
  simp only [cCocycle, map_one, sqrtF, map_zero, mul_one, one_mul, mul_zero, zero_mul,
    zero_add, add_zero] at h1 h2
  have h1'' : ε * sqrtF (KC s) x.fst.1 = 0 :=
    add_right_cancel (h1.trans (zero_add x.fst.2).symm)
  have h1' : sqrtF (KC s) x.fst.1 = 0 := (mul_eq_zero.mp h1'').resolve_left hε
  have h3 : x.fst.1 = 0 := by
    have hs := sqrtF_sq (KC s) x.fst.1
    rw [h1', zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    exact hs.symm
  have h2' : x.fst.2 = 0 := by
    rw [h3, map_zero, zero_add] at h2
    have h2a : ε * thetaC s (x.fst.2 * x.fst.2) = 0 := by simpa using h2.symm
    have h2b : thetaC s (x.fst.2 * x.fst.2) = 0 := (mul_eq_zero.mp h2a).resolve_left hε
    have h4 : thetaC s (x.fst.2 * x.fst.2) = thetaC s 0 := by simpa using h2b
    have h5 : x.fst.2 * x.fst.2 = 0 := (thetaC s).injective h4
    exact mul_self_eq_zero.mp h5
  exact Prod.ext h3 h2'

/-- The `A`-coordinate of `α ⟨0,z⟩` is `0`: `α` preserves `kerFst`. -/
theorem fst_alpha_zero (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (z : KC s) :
    (α ⟨0, z⟩).fst = 0 :=
  (mem_center_iff_fst_eq_zero hε _).mp (map_mem_center α
    ((mem_center_iff_fst_eq_zero hε _).mpr rfl))

/-- Every element of `C(n,ε)` is `⟨u,0⟩ * ⟨0,z⟩`. -/
theorem mk_eq_mul (x : CTypeC s ε) : x = ⟨x.fst, 0⟩ * ⟨0, x.snd⟩ := by
  ext <;> simp [cocC, TwoStep.snd_mul, Biadd.zero_right]

/-- The pointwise description of `α` in terms of `fstFun` and `sndFun`. -/
theorem alpha_apply (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (u : KC s × KC s) (z : KC s) :
    α ⟨u, z⟩ = ⟨fstFun α u, (α ⟨u, 0⟩).snd + sndFun α z⟩ := by
  have h : (⟨u, z⟩ : CTypeC s ε) = ⟨u, 0⟩ * ⟨0, z⟩ := mk_eq_mul ⟨u, z⟩
  rw [h, map_mul]
  ext <;> simp [fstFun, sndFun, cocC, TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right,
    fst_alpha_zero hε α z]

/-- `(α ⟨u,z⟩).fst = fstFun α u`. -/
theorem fst_alpha_apply (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (u : KC s × KC s) (z : KC s) :
    (α ⟨u, z⟩).fst = fstFun α u := by
  rw [alpha_apply hε]

/-- `(α v).fst = fstFun α v.fst` for every `v`. -/
theorem fst_alpha_eq (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (v : CTypeC s ε) :
    (α v).fst = fstFun α v.fst := by
  conv_lhs => rw [show v = (⟨v.fst, v.snd⟩ : CTypeC s ε) from rfl]
  exact fst_alpha_apply hε α v.fst v.snd

/-- `fstFun α` is additive. -/
theorem fstFun_add (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (u v : KC s × KC s) :
    fstFun α (u + v) = fstFun α u + fstFun α v := by
  have hmul : (⟨u, 0⟩ : CTypeC s ε) * ⟨v, 0⟩ = ⟨u + v, cocC s ε u v⟩ := by
    ext <;> simp [cocC]
  have hmul2 : (⟨u + v, 0⟩ : CTypeC s ε) * ⟨0, cocC s ε u v⟩ = ⟨u + v, cocC s ε u v⟩ := by
    ext <;> simp [cocC, TwoStep.snd_mul, Biadd.zero_right]
  calc fstFun α (u + v) = (α ⟨u + v, 0⟩).fst := rfl
    _ = (α ⟨u + v, 0⟩).fst + (α ⟨0, cocC s ε u v⟩).fst := by
          rw [fst_alpha_zero hε α (cocC s ε u v), add_zero]
    _ = (α ⟨u + v, 0⟩ * α ⟨0, cocC s ε u v⟩).fst := by rw [TwoStep.fst_mul]
    _ = (α (⟨u + v, 0⟩ * ⟨0, cocC s ε u v⟩)).fst := by rw [map_mul]
    _ = (α ⟨u + v, cocC s ε u v⟩).fst := by rw [hmul2]
    _ = (α (⟨u, 0⟩ * ⟨v, 0⟩)).fst := by rw [hmul]
    _ = (α ⟨u, 0⟩ * α ⟨v, 0⟩).fst := by rw [map_mul]
    _ = (α ⟨u, 0⟩).fst + (α ⟨v, 0⟩).fst := by rw [TwoStep.fst_mul]
    _ = fstFun α u + fstFun α v := rfl

/-- `sndFun α` is additive. -/
theorem sndFun_add (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (z z' : KC s) :
    sndFun α (z + z') = sndFun α z + sndFun α z' := by
  have hmul : (⟨0, z⟩ : CTypeC s ε) * ⟨0, z'⟩ = ⟨0, z + z'⟩ := by
    ext <;> simp [cocC, TwoStep.snd_mul, Biadd.zero_left]
  calc sndFun α (z + z') = (α ⟨0, z + z'⟩).snd := rfl
    _ = (α (⟨0, z⟩ * ⟨0, z'⟩)).snd := by rw [hmul]
    _ = (α ⟨0, z⟩ * α ⟨0, z'⟩).snd := by rw [map_mul]
    _ = (α ⟨0, z⟩).snd + (α ⟨0, z'⟩).snd + cocC s ε 0 0 := by
          rw [TwoStep.snd_mul, fst_alpha_zero hε α z, fst_alpha_zero hε α z']
          rfl
    _ = (α ⟨0, z⟩).snd + (α ⟨0, z'⟩).snd := by simp [cocC, Biadd.zero_left]

/-- The two-step form of "an automorphism commutes with the quadratic map":
`sndFun α (quadC s ε u) = quadC s ε (fstFun α u)`. -/
theorem sndFun_quadC (α : MulAut (CTypeC s ε)) (u : KC s × KC s) :
    sndFun α (quadC s ε u) = quadC s ε (fstFun α u) := by
  have hsq : (⟨u, 0⟩ : CTypeC s ε) ^ 2 = ⟨0, quadC s ε u⟩ := TwoStep.sq_eq _
  calc sndFun α (quadC s ε u) = (α ⟨0, quadC s ε u⟩).snd := rfl
    _ = (α ((⟨u, 0⟩ : CTypeC s ε) ^ 2)).snd := by rw [hsq]
    _ = (α (⟨u, 0⟩ : CTypeC s ε) ^ 2).snd := by rw [map_pow]
    _ = (⟨0, cocC s ε (fstFun α u) (fstFun α u)⟩ : CTypeC s ε).snd := by
          rw [TwoStep.sq_eq]
          rfl
    _ = quadC s ε (fstFun α u) := rfl

/-- `α ↦ fstFun α` is multiplicative. -/
theorem fstFun_mul (hε : ε ≠ 0) (α β : MulAut (CTypeC s ε)) :
    fstFun (α * β) = fstFun α ∘ fstFun β := by
  funext u
  show ((α * β) ⟨u, 0⟩).fst = fstFun α (fstFun β u)
  calc ((α * β) ⟨u, 0⟩).fst = (α (β ⟨u, 0⟩)).fst := rfl
    _ = fstFun α ((β ⟨u, 0⟩).fst) := fst_alpha_eq hε α (β ⟨u, 0⟩)
    _ = fstFun α (fstFun β u) := rfl

/-- `fstFun 1 = id`. -/
theorem fstFun_one : fstFun (1 : MulAut (CTypeC s ε)) = id := rfl

/-- The map `u ↦ quadC s ε u` is onto `K` (it contains `x ↦ x·θx = x ^ (2^s+1)`). -/
theorem quadC_surjective : Function.Surjective (quadC s ε) := by
  intro z
  obtain ⟨x, hx⟩ := surjective_pow_two_pow_add_one s z
  refine ⟨(x, 0), ?_⟩
  have hθ : thetaC s x = x ^ 2 ^ s := frobeniusEquiv_pow_apply (2 * s + 1) s x
  show quadC s ε (x, 0) = z
  simp only [quadC, cCocycle, Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero, add_zero, hθ]
  rw [show x * x ^ 2 ^ s = x ^ (2 ^ s + 1) from (pow_succ' x (2 ^ s)).symm]
  exact hx

/-- If `fstFun α = id` then `sndFun α = id`. -/
theorem sndFun_eq_id (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) (h : fstFun α = id) :
    sndFun α = id := by
  funext z
  obtain ⟨u, rfl⟩ := quadC_surjective (s := s) (ε := ε) z
  rw [sndFun_quadC, h]
  rfl

/-- `fstFun α` is injective. -/
theorem fstFun_injective (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) :
    Function.Injective (fstFun α) := by
  intro u v huv
  have hker : ∀ w : CTypeC s ε, (α w).fst = 0 → w.fst = 0 := by
    intro w hw
    have hw' : α w ∈ Subgroup.center (CTypeC s ε) :=
      (mem_center_iff_fst_eq_zero hε _).mpr hw
    have hw'' : w ∈ Subgroup.center (CTypeC s ε) := by
      have h := map_mem_center α.symm hw'
      simpa using h
    exact (mem_center_iff_fst_eq_zero hε w).mp hw''
  have hw : (α (⟨u, 0⟩ * (⟨v, 0⟩ : CTypeC s ε)⁻¹)).fst = 0 := by
    rw [map_mul, map_inv, TwoStep.fst_mul, TwoStep.fst_inv]
    change fstFun α u + fstFun α v = 0
    rw [huv]
    exact AddExpTwo.add_self _
  have hthis : u + v = 0 := by
    have h := hker _ hw
    rwa [TwoStep.fst_mul, TwoStep.fst_inv] at h
  calc u = u + 0 := (add_zero u).symm
    _ = u + (u + v) := by rw [hthis, add_zero]
    _ = u + u + v := (add_assoc u u v).symm
    _ = v := by rw [AddExpTwo.add_self, zero_add]

/-- `fstFun α` is bijective. -/
theorem fstFun_bijective (hε : ε ≠ 0) (α : MulAut (CTypeC s ε)) :
    Function.Bijective (fstFun α) :=
  ⟨fstFun_injective hε α,
    (Finite.injective_iff_surjective.mp (fstFun_injective hε α))⟩

end Work.Hering.AppVIII
