import Mathlib
import Submission.Work.ZassenhausSuzuki.Core
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Suzuki 1962, Lemma 6 (conjugacy of the cyclic Hua subgroup)

For `A = A(K,θ)` (`K = GF(2^n)`, `θ ≠ 1` of odd order) every cyclic subgroup `Z' ≤ Aut(A)` of
order `2^n − 1` acting without non-trivial fixed points on the involutions is `Aut(A)`-conjugate
to the standard torus `Λ = im(hLamHom θ)`.

The two inputs are
* `Work.ZassenhausSuzuki.SzAuto.aut_V_action_scalar` (an automorphism of order `2^n−1` acts on
  `A/Z(A)` as a scalar), and
* `Work.ZassenhausSuzuki.SzAuto.conj_of_complements` (complements of an abelian normal Hall
  subgroup are conjugate).
The remaining content is the bookkeeping around the kernel `Vtriv` of the action on `A/Z(A)`.
-/

noncomputable section

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open SzA

variable {n : ℕ}

/-- Automorphisms preserve the centre. -/
theorem mulAut_mem_center {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g']

/-- `⟨0,b⟩` is central. -/
theorem mk_zero_mem_center (θ : GaloisField 2 n ≃+* GaloisField 2 n) (b : GaloisField 2 n) :
    (⟨0, b⟩ : SzA (GaloisField 2 n) θ) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
  rw [Subgroup.mem_center_iff]
  intro y
  ext <;> simp [add_comm]

/-- In `A(K,θ)` (`θ ≠ 1`, characteristic two) an element is an involution iff it is central. -/
theorem sq_eq_one_iff_mem_center (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (x : SzA (GaloisField 2 n) θ) :
    x * x = 1 ↔ x ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
  constructor
  · intro hx
    rw [SzA.mem_center_iff θ hθ]
    have hsq : x * x = (⟨0, x.a * θ x.a⟩ : SzA (GaloisField 2 n) θ) := SzA.sq_eq θ x
    rw [hsq] at hx
    have hb := congrArg SzA.b hx
    simp only [one_b] at hb
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact (map_eq_zero θ).mp h
  · intro hx
    have ha : x.a = 0 := (SzA.mem_center_iff θ hθ x).mp hx
    obtain ⟨b, rfl⟩ : ∃ b, x = ⟨0, b⟩ := ⟨x.b, by ext <;> simp [ha]⟩
    ext <;> simp [CharTwo.add_self_eq_zero]

/-- An automorphism of `A(K,θ)` maps `⟨0,b⟩` into `{(0,ψ b)}`. -/
theorem aut_zero_coord (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (φ : MulAut (SzA (GaloisField 2 n) θ)) (b : GaloisField 2 n) :
    ∃ b', φ (⟨0, b⟩ : SzA (GaloisField 2 n) θ) = ⟨0, b'⟩ := by
  have hmem := mulAut_mem_center φ (mk_zero_mem_center θ b)
  refine ⟨(φ ⟨0, b⟩).b, ?_⟩
  ext
  · exact (SzA.mem_center_iff θ hθ _).mp hmem
  · rfl

/-- The subgroup of automorphisms of `A(K,θ)` acting trivially on `A/Z(A)`. -/
def Vtriv (θ : GaloisField 2 n ≃+* GaloisField 2 n) :
    Subgroup (MulAut (SzA (GaloisField 2 n) θ)) where
  carrier := {φ | ∀ x : SzA (GaloisField 2 n) θ, φ x * x⁻¹ ∈ Subgroup.center _}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro φ ψ hφ hψ x
    have h1 : ψ x * x⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := hψ x
    have h3 : φ (ψ x * x⁻¹) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
      mulAut_mem_center φ h1
    have h2 : φ x * x⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := hφ x
    have hkey : φ (ψ x) * x⁻¹ = φ (ψ x * x⁻¹) * (φ x * x⁻¹) := by
      rw [map_mul, map_inv φ x]
      group
    rw [MulAut.mul_apply, hkey]
    exact Subgroup.mul_mem (Subgroup.center (SzA (GaloisField 2 n) θ)) h3 h2
  inv_mem' := by
    intro φ hφ x
    have h1 : φ (φ.symm x) * (φ.symm x)⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
      hφ (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := Subgroup.inv_mem (Subgroup.center (SzA (GaloisField 2 n) θ)) h1
    have hinv : (x * (φ.symm x)⁻¹)⁻¹ = φ.symm x * x⁻¹ := by group
    rw [hinv] at h2
    simpa only [MulAut.inv_apply] using h2

/-- `Vtriv` is normal in `MulAut A`. -/
theorem Vtriv_normal (θ : GaloisField 2 n ≃+* GaloisField 2 n) : (Vtriv θ).Normal := by
  refine Subgroup.Normal.mk ?_
  intro φ hφ g
  intro x
  have h1 : φ (g.symm x) * (g.symm x)⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
    hφ (g.symm x)
  have h2 : g (φ (g.symm x) * (g.symm x)⁻¹) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
    mulAut_mem_center g h1
  have hkey : (g * φ * g⁻¹) x * x⁻¹ = g (φ (g.symm x) * (g.symm x)⁻¹) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply g x]
  rw [hkey]
  exact h2

end Work.ZassenhausSuzuki

namespace Work.ZassenhausSuzuki

open SzA

variable {n : ℕ}

/-- An automorphism trivial on `A/Z(A)` fixes the involution `⟨0,1⟩`. -/
theorem Vtriv_fixes_involution (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) :
    φ (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) = ⟨0, 1⟩ := by
  obtain ⟨b', hb'⟩ := aut_zero_coord θ hθ φ 1
  have h1 : (φ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)).a = 1 := by
    have hmem := hφ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)
    have hz := (SzA.mem_center_iff θ hθ _).mp hmem
    have hneg : (-1 : GaloisField 2 n) = 1 := CharTwo.neg_eq 1
    simp only [SzA.mul_a, SzA.inv_a, hneg] at hz
    have hsum : (φ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)).a + 1 = 1 + 1 := by
      rw [hz, CharTwo.add_self_eq_zero]
    exact add_right_cancel hsum
  obtain ⟨c, hc⟩ : ∃ c, φ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ) = ⟨1, c⟩ :=
    ⟨(φ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)).b, by ext <;> simp [h1]⟩
  have hsq : (⟨1, c⟩ : SzA (GaloisField 2 n) θ) * ⟨1, c⟩ = ⟨0, 1⟩ := by
    ext <;> simp [CharTwo.add_self_eq_zero]
  have hb'1 : b' = 1 := by
    have h3a : φ (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) =
        (⟨1, c⟩ : SzA (GaloisField 2 n) θ) * ⟨1, c⟩ := by
      have hXY : (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) =
          (⟨1, 0⟩ : SzA (GaloisField 2 n) θ) * ⟨1, 0⟩ := by
        ext <;> simp [CharTwo.add_self_eq_zero]
      rw [hXY, map_mul, hc]
    rw [hb', hsq] at h3a
    have := congrArg SzA.b h3a
    simpa using this
  rw [hb', hb'1]

end Work.ZassenhausSuzuki

namespace Work.ZassenhausSuzuki

open SzA

variable {n : ℕ}

