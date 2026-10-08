/-
# Automorphisms of a two-step group: the induced maps on `A` and `Z`

For a two-step group `TwoStep A Z b` (with `b` biadditive) whose centre is `kerFst`
(the hypothesis `hZ` below, which holds for Higman's families `A`, `B`, `C`, `D`), every
automorphism `α` induces

* an additive map `fstFun α : A → A` on the quotient `P/Z` (via `α ⟨u,0⟩`),
* an additive map `sndFun α : Z → Z` on the centre (via `α ⟨0,z⟩`),

linked by `sndFun α (b u u) = b (fstFun α u) (fstFun α u)`.  When in addition the squaring map
`u ↦ b u u` is onto (`hq`), the kernel of `α ↦ fstFun α` is abelian: it consists of the
translations `⟨u,z⟩ ↦ ⟨u, s u + z⟩`.
-/
import Mathlib
import Submission.Work.Higman.Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

namespace TSA

variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z} [Biadd b]
  [AddExpTwo A] [AddExpTwo Z]

/-- The map induced by `α` on the `A`-coordinate: `u ↦ (α ⟨u,0⟩).fst`. -/
def fstFun (α : MulAut (TwoStep A Z b)) (u : A) : A := (α ⟨u, 0⟩).fst

/-- The map induced by `α` on the centre: `z ↦ (α ⟨0,z⟩).snd`. -/
def sndFun (α : MulAut (TwoStep A Z b)) (z : Z) : Z := (α ⟨0, z⟩).snd

/-- An automorphism maps the centre into itself. -/
theorem map_mem_center (α : MulAut (TwoStep A Z b)) {x : TwoStep A Z b}
    (hx : x ∈ Subgroup.center (TwoStep A Z b)) : α x ∈ Subgroup.center (TwoStep A Z b) := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  obtain ⟨w, rfl⟩ : ∃ w, y = α w := ⟨α.symm y, by simp⟩
  rw [← map_mul, ← map_mul, hx w]

/-- The `A`-coordinate of `α ⟨0,z⟩` is zero: `α` preserves `kerFst`. -/
theorem fst_alpha_zero (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) (z : Z) :
    (α ⟨0, z⟩).fst = 0 :=
  (hZ _).mp (map_mem_center α ((hZ _).mpr rfl))

/-- Every element is `⟨u,0⟩ * ⟨0,z⟩`. -/
theorem mk_eq_mul (x : TwoStep A Z b) : x = ⟨x.fst, 0⟩ * ⟨0, x.snd⟩ := by
  ext <;> simp [TwoStep.snd_mul, Biadd.zero_right]

/-- The pointwise description of `α` in terms of `fstFun` and `sndFun`. -/
theorem alpha_apply (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b))
    (u : A) (z : Z) :
    α ⟨u, z⟩ = ⟨fstFun α u, (α ⟨u, 0⟩).snd + sndFun α z⟩ := by
  have h : (⟨u, z⟩ : TwoStep A Z b) = ⟨u, 0⟩ * ⟨0, z⟩ := mk_eq_mul ⟨u, z⟩
  rw [h, map_mul]
  ext <;> simp [fstFun, sndFun, TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right,
    fst_alpha_zero hZ α z]

/-- `(α ⟨u,z⟩).fst = fstFun α u`. -/
theorem fst_alpha_apply (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b))
    (u : A) (z : Z) : (α ⟨u, z⟩).fst = fstFun α u := by
  rw [alpha_apply hZ]

/-- `(α v).fst = fstFun α v.fst` for every `v`. -/
theorem fst_alpha_eq (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b))
    (v : TwoStep A Z b) : (α v).fst = fstFun α v.fst := by
  conv_lhs => rw [show v = (⟨v.fst, v.snd⟩ : TwoStep A Z b) from rfl]
  exact fst_alpha_apply hZ α v.fst v.snd

/-- `fstFun α` is additive. -/
theorem fstFun_add (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) (u v : A) :
    fstFun α (u + v) = fstFun α u + fstFun α v := by
  have hmul : (⟨u, 0⟩ : TwoStep A Z b) * ⟨v, 0⟩ = ⟨u + v, b u v⟩ := by
    ext <;> simp [TwoStep.snd_mul, Biadd.zero_right]
  have hmul2 : (⟨u + v, 0⟩ : TwoStep A Z b) * ⟨0, b u v⟩ = ⟨u + v, b u v⟩ := by
    ext <;> simp [TwoStep.snd_mul, Biadd.zero_right]
  calc fstFun α (u + v) = (α ⟨u + v, 0⟩).fst := rfl
    _ = (α ⟨u + v, 0⟩).fst + (α ⟨0, b u v⟩).fst := by
          rw [fst_alpha_zero hZ α (b u v), add_zero]
    _ = (α ⟨u + v, 0⟩ * α ⟨0, b u v⟩).fst := by rw [TwoStep.fst_mul]
    _ = (α (⟨u + v, 0⟩ * ⟨0, b u v⟩)).fst := by rw [map_mul]
    _ = (α ⟨u + v, b u v⟩).fst := by rw [hmul2]
    _ = (α (⟨u, 0⟩ * ⟨v, 0⟩)).fst := by rw [hmul]
    _ = (α ⟨u, 0⟩ * α ⟨v, 0⟩).fst := by rw [map_mul]
    _ = (α ⟨u, 0⟩).fst + (α ⟨v, 0⟩).fst := by rw [TwoStep.fst_mul]
    _ = fstFun α u + fstFun α v := rfl

/-- `sndFun α` is additive. -/
theorem sndFun_add (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) (z z' : Z) :
    sndFun α (z + z') = sndFun α z + sndFun α z' := by
  have hmul : (⟨0, z⟩ : TwoStep A Z b) * ⟨0, z'⟩ = ⟨0, z + z'⟩ := by
    ext <;> simp [TwoStep.snd_mul, Biadd.zero_left]
  calc sndFun α (z + z') = (α ⟨0, z + z'⟩).snd := rfl
    _ = (α (⟨0, z⟩ * ⟨0, z'⟩)).snd := by rw [hmul]
    _ = (α ⟨0, z⟩ * α ⟨0, z'⟩).snd := by rw [map_mul]
    _ = (α ⟨0, z⟩).snd + (α ⟨0, z'⟩).snd + b 0 0 := by
          rw [TwoStep.snd_mul, fst_alpha_zero hZ α z, fst_alpha_zero hZ α z']
    _ = (α ⟨0, z⟩).snd + (α ⟨0, z'⟩).snd := by simp [Biadd.zero_left]

/-- The two-step form of "an automorphism commutes with the squaring map":
`sndFun α (b u u) = b (fstFun α u) (fstFun α u)`. -/
theorem sndFun_quad (α : MulAut (TwoStep A Z b)) (u : A) :
    sndFun α (b u u) = b (fstFun α u) (fstFun α u) := by
  have hsq : (⟨u, 0⟩ : TwoStep A Z b) ^ 2 = ⟨0, b u u⟩ := TwoStep.sq_eq _
  calc sndFun α (b u u) = (α ⟨0, b u u⟩).snd := rfl
    _ = (α ((⟨u, 0⟩ : TwoStep A Z b) ^ 2)).snd := by rw [hsq]
    _ = (α (⟨u, 0⟩ : TwoStep A Z b) ^ 2).snd := by rw [map_pow]
    _ = (⟨0, b (fstFun α u) (fstFun α u)⟩ : TwoStep A Z b).snd := by
          rw [TwoStep.sq_eq]
          rfl
    _ = b (fstFun α u) (fstFun α u) := rfl

/-- `α ↦ fstFun α` is multiplicative. -/
theorem fstFun_mul (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α β : MulAut (TwoStep A Z b)) :
    fstFun (α * β) = fstFun α ∘ fstFun β := by
  funext u
  show ((α * β) ⟨u, 0⟩).fst = fstFun α (fstFun β u)
  calc ((α * β) ⟨u, 0⟩).fst = (α (β ⟨u, 0⟩)).fst := rfl
    _ = fstFun α ((β ⟨u, 0⟩).fst) := fst_alpha_eq hZ α (β ⟨u, 0⟩)
    _ = fstFun α (fstFun β u) := rfl

/-- `fstFun 1 = id`. -/
theorem fstFun_one : fstFun (1 : MulAut (TwoStep A Z b)) = id := rfl

/-- If the squaring map `u ↦ b u u` is onto and `fstFun α = id`, then `sndFun α = id`. -/
theorem sndFun_eq_id (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0)
    (hq : ∀ z : Z, ∃ u : A, b u u = z) (α : MulAut (TwoStep A Z b)) (h : fstFun α = id) :
    sndFun α = id := by
  funext z
  obtain ⟨u, rfl⟩ := hq z
  rw [sndFun_quad, h]
  rfl

/-- `fstFun α` is injective. -/
theorem fstFun_injective (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) :
    Function.Injective (fstFun α) := by
  intro u v huv
  have hker : ∀ w : TwoStep A Z b, (α w).fst = 0 → w.fst = 0 := by
    intro w hw
    have hw' : α w ∈ Subgroup.center (TwoStep A Z b) := (hZ _).mpr hw
    have hw'' : w ∈ Subgroup.center (TwoStep A Z b) := by
      have h := map_mem_center α.symm hw'
      simpa using h
    exact (hZ w).mp hw''
  have hw : (α (⟨u, 0⟩ * (⟨v, 0⟩ : TwoStep A Z b)⁻¹)).fst = 0 := by
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
theorem fstFun_bijective (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) [Finite A] :
    Function.Bijective (fstFun α) :=
  ⟨fstFun_injective hZ α, (Finite.injective_iff_surjective.mp (fstFun_injective hZ α))⟩

/-- `α ⟨0,z⟩ = ⟨0, sndFun α z⟩`. -/
theorem alpha_zero_apply (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) (z : Z) :
    α ⟨0, z⟩ = ⟨0, sndFun α z⟩ := by
  have hzero : (α (⟨0, 0⟩ : TwoStep A Z b)).snd = 0 := by
    rw [show (⟨0, 0⟩ : TwoStep A Z b) = 1 from rfl, map_one]
    rfl
  have hf0 : fstFun α 0 = 0 := by
    show (α (⟨0, 0⟩ : TwoStep A Z b)).fst = 0
    exact fst_alpha_zero hZ α 0
  rw [alpha_apply hZ α 0 z, hf0, hzero, zero_add]

/-- `sndFun α` is injective. -/
theorem sndFun_injective (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) :
    Function.Injective (sndFun α) := by
  intro z z' h
  have h1 : α (⟨0, z⟩ : TwoStep A Z b) = α ⟨0, z'⟩ := by
    rw [alpha_zero_apply hZ α z, alpha_zero_apply hZ α z', h]
  have h2 := α.injective h1
  simpa using h2

/-- `sndFun α` is bijective. -/
theorem sndFun_bijective (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0) (α : MulAut (TwoStep A Z b)) [Finite Z] :
    Function.Bijective (sndFun α) :=
  ⟨sndFun_injective hZ α, (Finite.injective_iff_surjective.mp (sndFun_injective hZ α))⟩

/-- The pointwise description of an automorphism inducing the identity on `A`. -/
theorem apply_of_fst_eq_id (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0)
    (hq : ∀ z : Z, ∃ u : A, b u u = z) (γ : MulAut (TwoStep A Z b)) (h : fstFun γ = id)
    (u : A) (z : Z) : γ ⟨u, z⟩ = ⟨u, (γ ⟨u, 0⟩).snd + z⟩ := by
  rw [alpha_apply hZ γ u z, h, sndFun_eq_id hZ hq γ h]
  rfl

/-- The kernel of `α ↦ fstFun α` is abelian. -/
theorem kernel_comm (hZ : ∀ x : TwoStep A Z b,
    x ∈ Subgroup.center (TwoStep A Z b) ↔ x.fst = 0)
    (hq : ∀ z : Z, ∃ u : A, b u u = z) (α β : MulAut (TwoStep A Z b))
    (hα : fstFun α = id) (hβ : fstFun β = id) : α * β = β * α := by
  apply MulEquiv.ext
  intro x
  obtain ⟨u, z⟩ := x
  show α (β (⟨u, z⟩ : TwoStep A Z b)) = β (α ⟨u, z⟩)
  rw [apply_of_fst_eq_id hZ hq β hβ u z,
    apply_of_fst_eq_id hZ hq α hα u ((β ⟨u, 0⟩).snd + z),
    apply_of_fst_eq_id hZ hq α hα u z,
    apply_of_fst_eq_id hZ hq β hβ u ((α ⟨u, 0⟩).snd + z)]
  congr 1
  abel

end TSA

end Work.Hering.AppVIII
