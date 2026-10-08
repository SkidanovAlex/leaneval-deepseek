import Mathlib
import Submission.Work.NPC.Fpf.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Fixed-point-free automorphisms: the elementary API (A8b, part 1)

This is the first of the files implementing the elementary route to **Thompson's theorem** in the
solvable case, i.e. the theorem that a finite **solvable** group with a fixed-point-free
automorphism of prime order is nilpotent.  It is the input the odd-order drive needs for
"A8b: the Frobenius kernel is nilpotent"
(`Submission/Work/NOTES_LEAD_ft_npc.md` §2, lemmas F1--F4).

The definitions `Work.NPC.Fpf.IsFpf` (`∀ x, α x = x → x = 1`) and `Work.NPC.Fpf.IsInv`
(`∀ x, α x ∈ H ↔ x ∈ H`) live in area A9's module `Submission.Work.NPC.Fpf.Defs` and are imported,
not duplicated.  Here we provide

* `isFpf_mulInv_injective`, `isFpf_mulInv_injective'` (F1) and their bijective forms (F2);
* `isFpf_pow` (F3): a nontrivial power `α ^ i` with `0 < i < q` of an fpf automorphism `α` of prime
  order `q` is again fpf;
* `isFpf_restrict` (F4): the restriction of an fpf automorphism to an invariant subgroup is fpf;
* the invariance API (`isInv_of_characteristic`, `IsInv.inf`, ...) used to produce invariant
  subgroups.
-/

universe u

namespace Work.Frobenius.Fpf

open Work.NPC.Fpf

variable {K : Type*}

section Group

variable [Group K]

/-- **F1.**  If `α` is fixed-point-free then `x ↦ x⁻¹ * α x` is injective. -/
theorem isFpf_mulInv_injective {α : MulAut K} (hα : IsFpf α) :
    Function.Injective (fun x : K => x⁻¹ * α x) := by
  intro x y hxy
  change x⁻¹ * α x = y⁻¹ * α y at hxy
  have h2 : α y = y * x⁻¹ * α x := by
    calc α y = y * (y⁻¹ * α y) := by group
      _ = y * (x⁻¹ * α x) := by rw [hxy]
      _ = y * x⁻¹ * α x := by group
  have h3 : α (y * x⁻¹) = y * x⁻¹ := by
    have h4 : α (y * x⁻¹) = α y * (α x)⁻¹ := by simp
    rw [h4, h2]
    group
  have h4 : y * x⁻¹ = 1 := hα _ h3
  rw [mul_eq_one_iff_eq_inv, inv_inv] at h4
  exact h4.symm

/-- **F1.**  If `α` is fixed-point-free then `x ↦ α x * x⁻¹` is injective. -/
theorem isFpf_mulInv_injective' {α : MulAut K} (hα : IsFpf α) :
    Function.Injective (fun x : K => α x * x⁻¹) := by
  intro x y hxy
  change α x * x⁻¹ = α y * y⁻¹ at hxy
  have h2 : α y = α x * x⁻¹ * y := by
    calc α y = (α y * y⁻¹) * y := by group
      _ = (α x * x⁻¹) * y := by rw [hxy]
      _ = α x * x⁻¹ * y := by group
  have h3 : α (x⁻¹ * y) = x⁻¹ * y := by
    have h4 : α (x⁻¹ * y) = (α x)⁻¹ * α y := by simp
    rw [h4, h2]
    group
  have h4 : x⁻¹ * y = 1 := hα _ h3
  rw [inv_mul_eq_one] at h4
  exact h4

/-- **F2.**  For a finite group, `x ↦ x⁻¹ * α x` is bijective. -/
theorem isFpf_mulInv_bijective [Finite K] {α : MulAut K} (hα : IsFpf α) :
    Function.Bijective (fun x : K => x⁻¹ * α x) :=
  Finite.injective_iff_bijective.mp (isFpf_mulInv_injective hα)

/-- **F2.**  For a finite group, `x ↦ α x * x⁻¹` is bijective. -/
theorem isFpf_mulInv_bijective' [Finite K] {α : MulAut K} (hα : IsFpf α) :
    Function.Bijective (fun x : K => α x * x⁻¹) :=
  Finite.injective_iff_bijective.mp (isFpf_mulInv_injective' hα)

/-- **F3.**  A free power `α ^ i` (`0 < i < q`) of an automorphism `α` of prime order `q` with
`IsFpf α` is again fixed-point-free. -/
theorem isFpf_pow {α : MulAut K} {q : ℕ} (hq : q.Prime) (hαq : α ^ q = 1) (hα : IsFpf α)
    {i : ℕ} (hi0 : 0 < i) (hiq : i < q) : IsFpf (α ^ i) := by
  intro x hx
  have hord : orderOf α ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hαq
  rcases hq.eq_one_or_self_of_dvd (orderOf α) hord with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    exact hα x (by rw [h1]; rfl)
  · have hqi : ¬ q ∣ i := fun h => by
      have := Nat.le_of_dvd hi0 h
      omega
    have hcop : i.Coprime (orderOf α) := by
      rw [h1]
      exact (hq.coprime_iff_not_dvd.mpr hqi).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := α) (n := i) hcop
    have hfix : ∀ m : ℕ, ((α ^ i) ^ m) x = x := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, hx]
    have hαx : α x = x := by
      rw [← hm]
      exact hfix m
    exact hα x hαx

/-- **F4.**  The restriction of a fixed-point-free automorphism to an invariant subgroup is
fixed-point-free. -/
theorem isFpf_restrict {α : MulAut K} {H : Subgroup K} (hH : IsInv α H) (hα : IsFpf α) :
    IsFpf (hH.restrictEquiv) := by
  intro x hx
  refine Subtype.ext (hα (x : K) ?_)
  have := congrArg (fun y : ↥H => (y : K)) hx
  simpa [IsInv.restrictEquiv_apply] using this

/-! ### The invariance API -/

/-- If a subgroup is mapped to itself by `α`, it is invariant. -/
theorem isInv_of_map_eq {α : MulAut K} {H : Subgroup K} (hmap : H.map α.toMonoidHom = H) :
    IsInv α H := by
  intro x
  constructor
  · intro hx
    have hx' : α x ∈ H.map α.toMonoidHom := by rw [hmap]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := α.injective hyx
    rw [hyx'] at hy
    exact hy
  · intro hx
    have hx' : α x ∈ H.map α.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap] at hx'

/-- A characteristic subgroup is invariant under every automorphism. -/
theorem isInv_of_characteristic {α : MulAut K} {H : Subgroup K} (h : H.Characteristic) :
    IsInv α H :=
  isInv_of_map_eq ((Subgroup.characteristic_iff_map_eq.mp h) α)

/-- The trivial subgroup is invariant. -/
theorem isInv_bot (α : MulAut K) : IsInv α (⊥ : Subgroup K) := by
  intro x
  simp

/-- The whole group is invariant. -/
theorem isInv_top (α : MulAut K) : IsInv α (⊤ : Subgroup K) := by
  intro x
  simp

/-- An intersection of invariant subgroups is invariant. -/
theorem isInv_inf {α : MulAut K} {H L : Subgroup K} (hH : IsInv α H) (hL : IsInv α L) :
    IsInv α (H ⊓ L) := by
  intro x
  simp only [Subgroup.mem_inf]
  rw [hH x, hL x]

/-- A join of invariant subgroups is invariant. -/
theorem isInv_sup {α : MulAut K} {H L : Subgroup K} (hH : IsInv α H) (hL : IsInv α L) :
    IsInv α (H ⊔ L) :=
  isInv_of_map_eq (by rw [Subgroup.map_sup, hH.map_eq, hL.map_eq])

end Group

end Work.Frobenius.Fpf
