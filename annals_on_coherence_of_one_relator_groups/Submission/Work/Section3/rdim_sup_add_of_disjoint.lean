import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.rdim_range_of_idempotent
import Submission.Work.ORHughesFree.NaturalExtension.rdim_prod_add
import Submission.Work.ORHughesFree.NaturalExtension.rdim_map_of_leftInverse
import Submission.Work.ORHughesFree.Section3.vnIsoInvariance
import Submission.Work.Section3.rk_add_of_orthogonal_idempotent

set_option maxHeartbeats 1000000

namespace Work.Section3

open Matrix Work.ORHughesFree

/-- **Additivity of the row-wise dimension on disjoint submodules.**

For a von Neumann regular ring `U` with a Sylvester rank function `ρ` and two left submodules
`V, C ≤ Uⁿ` whose sum `V ⊔ C` is finitely generated and which meet in `0`, the row-wise
dimension `rdim` (see `NaturalExtension.DualityDefs`) is additive:

  `rdim ρ (V ⊔ C) = rdim ρ V + rdim ρ C`.

PROOF.  Because `V ⊔ C` is finitely generated and `U` is von Neumann regular, `V ⊔ C` is the
range of an idempotent endomorphism `q` of `Uⁿ` (`regular_fgSubmodule_projection`), with kernel
`K`.  Since `V ⊓ C = ⊥`, the pair `(V, C ⊔ K)` is complementary in `Uⁿ`: it spans `Uⁿ` because
`V ⊔ C ⊔ K = range q ⊔ ker q = ⊤`, and it meets in `0` because any `x = c + k ∈ V` with
`c ∈ C`, `k ∈ K` satisfies `x = q x = q c + q k = c`, hence `x ∈ V ⊓ C = ⊥`.

Let `E := Submodule.projection V (C ⊔ K)` be the projection onto `V` along `C ⊔ K` (so `E` is
the identity on `V` and kills `C`).  The linear map `η z = (E z, (1 - E) z)` has the left
inverse `ξ (a, b) = a + b`, and it maps `V ⊔ C` onto the product `V × C`: on a vector
`a + b` with `a ∈ V`, `b ∈ C` it is `(a, b)`, and conversely `η (a + b) = (a, b)`.
The dimension is invariant under `η` (`rdim_map_of_leftInverse`) and additive on an external
product (`rdim_prod_add`), which gives the result. -/
theorem rdim_sup_add_of_disjoint {U : Type*} [Ring U] [Work.ORHughesFree.VonNeumannRegularRing U]
    (ρ : Work.ORHughesFree.SylvesterRank U) {n : ℕ} {V C : Submodule U (Fin n → U)}
    (hW : (V ⊔ C).FG) (h : V ⊓ C = ⊥) :
    Work.ORHughesFree.NaturalExtension.rdim ρ (V ⊔ C) =
      Work.ORHughesFree.NaturalExtension.rdim ρ V +
      Work.ORHughesFree.NaturalExtension.rdim ρ C := by
  classical
  obtain ⟨q, hq, hqr⟩ :=
    Work.ORHughesFree.DivisionRank.regular_fgSubmodule_projection n (V ⊔ C) hW
  set K : Submodule U (Fin n → U) := LinearMap.ker q with hK
  have hqfix : ∀ x ∈ q.range, q x = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    show q (q y) = q y
    rw [← LinearMap.comp_apply, hq]
  -- `V` and `C ⊔ K` are complementary.
  have hinf : V ⊓ (C ⊔ K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxV, hxc⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, hcC, k, hkK, hck⟩ := Submodule.mem_sup.mp hxc
    have hcW : c ∈ V ⊔ C := Submodule.mem_sup_right (S := V) hcC
    have hqc : q c = c := hqfix c (by rw [hqr]; exact hcW)
    have hqk : q k = 0 := hkK
    have hxW : x ∈ V ⊔ C := Submodule.mem_sup_left (T := C) hxV
    have hqx : q x = x := hqfix x (by rw [hqr]; exact hxW)
    have hqck : q (c + k) = c := by rw [map_add, hqc, hqk, add_zero]
    have hxc' : x = c := by rw [hqx.symm, ← hck, hqck]
    have hcV : c ∈ V := hxc' ▸ hxV
    have hcmem : c ∈ V ⊓ C := Submodule.mem_inf.mpr ⟨hcV, hcC⟩
    rw [h] at hcmem
    rw [Submodule.mem_bot] at hcmem ⊢
    exact hxc'.trans hcmem
  have hsup : V ⊔ (C ⊔ K) = ⊤ := by
    have hqidem : IsIdempotentElem q := by
      show q * q = q
      rw [Module.End.mul_eq_comp]; exact hq
    have hcomplq : IsCompl q.range q.ker := LinearMap.IsIdempotentElem.isCompl hqidem
    have h1 : V ⊔ (C ⊔ K) = (V ⊔ C) ⊔ K := by rw [sup_assoc]
    rw [h1, ← hqr]
    exact hcomplq.sup_eq_top
  have hcompl : IsCompl V (C ⊔ K) :=
    isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  -- The projection onto `V` along `C ⊔ K`.
  set E : Module.End U (Fin n → U) := Submodule.projection V (C ⊔ K) hcompl with hE
  have hEidem : E * E = E := by
    rw [hE]; exact Submodule.isIdempotentElem_projection hcompl
  have hErange : E.range = V := by
    rw [hE]; exact Submodule.range_projection hcompl
  have hEker : E.ker = C ⊔ K := by
    rw [hE]; exact Submodule.ker_projection hcompl
  have hEfix : ∀ x ∈ V, E x = x := by
    intro x hx
    have hxr : x ∈ E.range := by rw [hErange]; exact hx
    obtain ⟨y, hy⟩ := hxr
    calc E x = E (E y) := by rw [hy]
      _ = (E * E) y := by rw [Module.End.mul_apply]
      _ = E y := by rw [hEidem]
      _ = x := hy
  have hEC : ∀ x ∈ C, E x = 0 := by
    intro x hx
    have hxk : x ∈ E.ker := by rw [hEker]; exact Submodule.mem_sup_left (T := K) hx
    exact LinearMap.mem_ker.mp hxk
  -- `η z = (E z, (1 - E) z)` maps `V ⊔ C` onto `V × C`.
  have hmap : Submodule.map (LinearMap.prod E (1 - E)) (V ⊔ C) = Submodule.prod V C := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Submodule.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
      have h1 : E y = a := by rw [← hab, map_add, hEfix a ha, hEC b hb, add_zero]
      have h2 : (1 - E) y = b := by
        rw [← hab, LinearMap.sub_apply, Module.End.one_apply, map_add, hEfix a ha, hEC b hb,
          add_zero, add_sub_cancel_left]
      have hpair : (LinearMap.prod E (1 - E)) y = (a, b) := by
        rw [LinearMap.prod_apply, Function.prod_apply, h1, h2]
      rw [hpair]
      exact Submodule.mem_prod.mpr ⟨ha, hb⟩
    · intro z hz
      rw [Submodule.mem_map]
      rw [Submodule.mem_prod] at hz
      obtain ⟨a, b⟩ := z
      refine ⟨a + b, Submodule.mem_sup.mpr ⟨a, hz.1, b, hz.2, rfl⟩, ?_⟩
      have h1 : E (a + b) = a := by rw [map_add, hEfix a hz.1, hEC b hz.2, add_zero]
      have h2 : (1 - E) (a + b) = b := by
        rw [LinearMap.sub_apply, Module.End.one_apply, map_add, hEfix a hz.1, hEC b hz.2,
          add_zero, add_sub_cancel_left]
      rw [LinearMap.prod_apply, Function.prod_apply, h1, h2]
  -- The maps `η` and `ξ`.
  set e : ((Fin n → U) × (Fin n → U)) ≃ₗ[U] (Fin (n + n) → U) :=
    Work.ORHughesFree.Section3.prodFinLinearEquiv n n
  set η : (Fin n → U) →ₗ[U] (Fin (n + n) → U) :=
    e.toLinearMap ∘ₗ (LinearMap.prod E ((1 : Module.End U (Fin n → U)) - E)) with hηdef
  set ξ : (Fin (n + n) → U) →ₗ[U] (Fin n → U) :=
    (LinearMap.fst U (Fin n → U) (Fin n → U) + LinearMap.snd U (Fin n → U) (Fin n → U)) ∘ₗ
      e.symm.toLinearMap with hξdef
  have hξη : ξ ∘ₗ η = LinearMap.id := by
    apply LinearMap.ext
    intro z
    simp only [hηdef, hξdef, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prod_apply, Function.prod_apply]
    rw [← LinearMap.add_apply,
      show E + (1 - E) = (1 : Module.End U (Fin n → U)) from by abel, Module.End.one_apply]
    rfl
  have hmapη : Submodule.map η (V ⊔ C)
      = Submodule.map (e : ((Fin n → U) × (Fin n → U)) →ₗ[U] (Fin (n + n) → U))
          (Submodule.prod V C) := by
    rw [hηdef, Submodule.map_comp, hmap]
  rw [show NaturalExtension.rdim ρ (V ⊔ C)
        = NaturalExtension.rdim ρ (Submodule.map η (V ⊔ C)) from
      (NaturalExtension.rdim_map_of_leftInverse ρ hξη (V ⊔ C)).symm]
  rw [hmapη]
  exact NaturalExtension.rdim_prod_add ρ e V C

end Work.Section3
