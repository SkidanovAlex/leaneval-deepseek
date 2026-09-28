import Mathlib
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Lat.exists_int_extends
import Submission.Work.HP.Vero.span_realify_latOrth_inf

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-! ## Saturation of `latOrth`

The lattice `latOrth c = ker (Fintype.linearCombination ℤ c)` is saturated, since `ℤ` has no zero
divisors: if `n • y` pairs to zero with `c` then so does `y` (for `n ≠ 0`).  Intersections of
saturated lattices are saturated. -/

lemma dual_isSat_latOrth {ι : Type*} [Fintype ι] (c : ι → ℤ) : IsSat (latOrth c) := by
  intro y ⟨m, hm, hmy⟩
  rw [latOrth, LinearMap.mem_ker] at hmy ⊢
  rw [map_smul] at hmy
  exact (mul_eq_zero.mp hmy).resolve_left hm

lemma dual_isSat_inf {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℤ))
    (h₁ : IsSat L₁) (h₂ : IsSat L₂) : IsSat (L₁ ⊓ L₂) := by
  intro y ⟨m, hm, hmy⟩
  rw [Submodule.mem_inf] at hmy ⊢
  exact ⟨h₁ y ⟨m, hm, hmy.1⟩, h₂ y ⟨m, hm, hmy.2⟩⟩

/-- The standard bilinear form `⟨x,y⟩ = ∑ i, x i * y i` on `ι → ℝ`.  (The plain function type
`ι → ℝ` carries no `InnerProductSpace` instance, so the form is defined by hand.) -/
def dualDotForm {ι : Type*} [Fintype ι] : LinearMap.BilinForm ℝ (ι → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (fun x y z => by simp [Finset.sum_add_distrib, add_mul])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring))
    (fun x y z => by simp [Finset.sum_add_distrib, mul_add])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dualDotForm_apply (x y : ι → ℝ) : dualDotForm x y = ∑ i, x i * y i := rfl

lemma dualDotForm_comm (x y : ι → ℝ) : dualDotForm x y = dualDotForm y x := by
  rw [dualDotForm_apply, dualDotForm_apply]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma dualDotForm_toR (v : ι → ℤ) (x : ι → ℝ) :
    dualDotForm (toR v) x = ∑ i, x i * (v i : ℝ) := by
  rw [dualDotForm_comm, dualDotForm_apply]; rfl

lemma dualDotForm_refl : (dualDotForm (ι := ι)).IsRefl := by
  intro x y h; rw [dualDotForm_comm] at h; exact h

lemma dualDotForm_nondegen : (dualDotForm (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx; funext i; have h := hx (Pi.single i 1)
    simp [dualDotForm_apply, Pi.single_apply, Finset.sum_ite_eq'] at h; exact h
  · intro x hx; funext i; have h := hx (Pi.single i 1)
    simp [dualDotForm_apply, Pi.single_apply, Finset.sum_ite_eq'] at h; exact h

/-- The orthogonal complement of `span{v,w}` with respect to `dualDotForm` is the intersection of the two
real kernels of the functionals attached to `v` and `w`. -/
lemma dual_orthogonal_span_pair (v w : ι → ℤ) :
    (dualDotForm (ι := ι)).orthogonal (Submodule.span ℝ {toR v, toR w})
      = (Fintype.linearCombination ℝ (fun i => (v i : ℝ))).ker
        ⊓ (Fintype.linearCombination ℝ (fun i => (w i : ℝ))).ker := by
  ext x
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
      LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearCombination_apply]; simp only [smul_eq_mul]
      have h1 := h (toR v) (Submodule.subset_span (by simp))
      rwa [dualDotForm_toR] at h1
    · rw [Fintype.linearCombination_apply]; simp only [smul_eq_mul]
      have h1 := h (toR w) (Submodule.subset_span (by simp))
      rwa [dualDotForm_toR] at h1
  · rintro ⟨hv, hw⟩ y hy
    rw [Fintype.linearCombination_apply] at hv hw
    simp only [smul_eq_mul] at hv hw
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_left, dualDotForm_toR, dualDotForm_toR, hv, hw]
    ring

/-- A real vector that pairs integrally with every element of a saturated lattice
`K ⊆ ℤ^ι` differs from a vector of `ℤ^ι` by an element of `(span_ℝ K)^⊥`.  This is the lattice
reflexivity step: the functional `k ↦ ⟨t,k⟩` on `K` is integral, hence (by
`Work.HP.Lat.exists_int_extends`) restricts from an integer vector `b`, and `b - t` is orthogonal
to all of `K`, hence to `span_ℝ K`. -/
lemma dual_extraction (v w : ι → ℤ) (t : ι → ℝ)
    (ht : ∀ k : ι → ℤ, k ∈ (latOrth v ⊓ latOrth w) → dualDotForm (intCastPi k) t = 0) :
    ∃ lam mu : ℝ, ∀ m, t m = lam * (v m : ℝ) + mu * (w m : ℝ) := by
  have hmem : t ∈ (dualDotForm (ι := ι)).orthogonal
      (Submodule.span ℝ (((latOrth v ⊓ latOrth w).map intCastPi : Submodule ℤ (ι → ℝ)) :
        Set (ι → ℝ))) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    refine Submodule.span_induction (p := fun x _ => dualDotForm x t = 0) ?_ ?_ ?_ ?_ hu
    · rintro x ⟨k, hk, rfl⟩; exact ht k hk
    · simp
    · intro x y _ _ hpx hpy; rw [LinearMap.BilinForm.add_left, hpx, hpy, add_zero]
    · intro a x _ hpx; rw [LinearMap.BilinForm.smul_left, hpx, mul_zero]
  rw [span_realify_latOrth_inf v w, ← dual_orthogonal_span_pair v w] at hmem
  rw [LinearMap.BilinForm.orthogonal_orthogonal dualDotForm_nondegen dualDotForm_refl] at hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨lam, mu, hlm⟩ := hmem
  refine ⟨lam, mu, fun m => ?_⟩
  have := congr_fun hlm m
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toR] using this.symm

end Work.HP.Vero

namespace Work.HP.Vero

open Work.HP

/-- Every element of the dual lattice of `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` is the orthogonal projection of
an integer vector: it differs from an integer vector by an element of `span_ℝ(ν₂(x), ν₂(y))`.

This is the paper's "Lemma Schmidt quotient" for the lattice `Q₂ = span_ℝ(ν₂(x),ν₂(y)) ∩ ℤ^{N}`,
which is primitive (it is a saturation): `(Q₂^⊥)^* = ℤ^{N}/Q₂`.

Proof: `K := Λ_{ν₂(x)} ∩ Λ_{ν₂(y)} = ℤ^N ∩ span_ℝ(ν₂x,ν₂y)^⊥` is saturated, and
`span_ℝ(realify K) = span_ℝ(ν₂x,ν₂y)^⊥` (`span_realify_latOrth_inf`).  For `a` in the dual, the
functional `k ↦ ⟨a,k⟩` on `K` is integral, so `exists_int_extends` produces `b ∈ ℤ^N` with
`⟨b - a, K⟩ = 0`; then `b - a ∈ (span_ℝ K)^⊥ = span_ℝ(ν₂x,ν₂y)`, which is the claim. -/
theorem dualLat_int_shift {n : ℕ} (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (a : Mon 2 n → ℝ)
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) :
    ∃ b : Mon 2 n → ℤ, ∃ lam mu : ℝ, ∀ m : Mon 2 n,
      (b m : ℝ) - a m = lam * toR (veronese 2 n x) m + mu * toR (veronese 2 n y) m := by
  classical
  have hsat : IsSat (Gam 2 n x y) := by
    show IsSat (latOrth (veronese 2 n x) ⊓ latOrth (veronese 2 n y))
    exact dual_isSat_inf _ _ (dual_isSat_latOrth _) (dual_isSat_latOrth _)
  -- The pairing of `a` with `K` is integral, giving a `ℤ`-linear functional `φ` on `K`.
  have hspec : ∀ z : (Gam 2 n x y), ∃ k : ℤ, ∑ i, a i * (z.1 i : ℝ) = k := by
    intro z
    have hz : (intCastPi z.1 : Mon 2 n → ℝ) ∈ realify (Gam 2 n x y) :=
      Submodule.mem_map.mpr ⟨z.1, z.2, rfl⟩
    obtain ⟨k, hk⟩ := ha.2 (intCastPi z.1) hz
    exact ⟨k, by simpa using hk⟩
  let φfun : (Gam 2 n x y) → ℤ := fun z => Classical.choose (hspec z)
  have hφspec : ∀ z : (Gam 2 n x y), (φfun z : ℝ) = ∑ i, a i * (z.1 i : ℝ) :=
    fun z => (Classical.choose_spec (hspec z)).symm
  have hφadd : ∀ z z' : (Gam 2 n x y), φfun (z + z') = φfun z + φfun z' := by
    intro z z'
    have hcast : ((φfun (z + z') : ℤ) : ℝ) = ((φfun z + φfun z' : ℤ) : ℝ) := by
      rw [Int.cast_add, hφspec (z + z'), hφspec z, hφspec z']
      simp only [Submodule.coe_add, Pi.add_apply, Int.cast_add]
      rw [Finset.sum_congr rfl (fun i _ => mul_add (a i) _ _), Finset.sum_add_distrib]
    exact Int.cast_injective hcast
  have hφsmul : ∀ (c : ℤ) (z : (Gam 2 n x y)), φfun (c • z) = c • φfun z := by
    intro c z
    have hcast : ((φfun (c • z) : ℤ) : ℝ) = ((c * φfun z : ℤ) : ℝ) := by
      rw [Int.cast_mul, hφspec (c • z), hφspec z]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    exact Int.cast_injective hcast
  let φ : (Gam 2 n x y) →ₗ[ℤ] ℤ :=
    { toFun := φfun, map_add' := hφadd, map_smul' := hφsmul }
  -- `φ` is the restriction of the functional of an integer vector `b`.
  obtain ⟨b, hb⟩ := Work.HP.Lat.exists_int_extends (Gam 2 n x y) hsat φ
  -- Hence `b - a` pairs to zero with all of `K`.
  have hkey : ∀ k : Mon 2 n → ℤ,
      k ∈ (latOrth (veronese 2 n x) ⊓ latOrth (veronese 2 n y)) →
      dualDotForm (intCastPi k) (fun m => (b m : ℝ) - a m) = 0 := by
    intro k hk
    have h1 : ((φ ⟨k, hk⟩ : ℤ) : ℝ) = ∑ i, (b i : ℝ) * (k i : ℝ) := by
      rw [hb ⟨k, hk⟩]; push_cast; rfl
    have h2 : ((φ ⟨k, hk⟩ : ℤ) : ℝ) = ∑ i, a i * (k i : ℝ) := hφspec ⟨k, hk⟩
    have h3 : ∑ i, (b i : ℝ) * (k i : ℝ) = ∑ i, a i * (k i : ℝ) := by rw [← h1, h2]
    rw [dualDotForm_apply]
    have h4 : ∑ i, (intCastPi k : Mon 2 n → ℝ) i * ((b i : ℝ) - a i)
        = ∑ i, (b i : ℝ) * (k i : ℝ) - ∑ i, a i * (k i : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [intCastPi_apply]; ring)
    rw [h4, h3, sub_self]
  -- `b - a` is orthogonal to `K`, so lies in `span_ℝ(ν₂x,ν₂y)`.
  obtain ⟨lam, mu, hlm⟩ :=
    dual_extraction (veronese 2 n x) (veronese 2 n y) (fun m => (b m : ℝ) - a m) hkey
  exact ⟨b, lam, mu, fun m => by simpa [toR] using hlm m⟩

end Work.HP.Vero
