import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Approximation

open IsDedekindDomain
open scoped Pointwise

noncomputable section

/-- **The open-set form of weak approximation.**

If the diagonal image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense, then a finite product of nonempty
open subsets of the factors meets that image: there is `a : K` whose `𝔮`-component lies in the
prescribed open set, simultaneously for all `𝔮 ∈ S`. -/
theorem exists_forall_mem_open_of_isWeakApproximation {K : Type*} [Field K] [NumberField K]
    (S : Finset (NK.Chebotarev.PrimeIdeal K))
    (h : NK.UchidaKummer.IsWeakApproximation K S)
    (U : ∀ 𝔮 : S, Set (𝔮.1.adicCompletion K)) (hU : ∀ 𝔮, IsOpen (U 𝔮))
    (hne : ∀ 𝔮, (U 𝔮).Nonempty) :
    ∃ a : K, ∀ 𝔮 : S, algebraMap K (𝔮.1.adicCompletion K) a ∈ U 𝔮 := by
  have hd : DenseRange (fun a : K => fun 𝔮 : S => algebraMap K (𝔮.1.adicCompletion K) a) := h
  obtain ⟨a, ha⟩ := hd.exists_mem_open
    (isOpen_set_pi Set.finite_univ (fun 𝔮 _ => hU 𝔮))
    ⟨fun 𝔮 => (hne 𝔮).some, fun 𝔮 _ => (hne 𝔮).some_mem⟩
  exact ⟨a, fun 𝔮 => ha 𝔮 (Set.mem_univ 𝔮)⟩

/-- **A coset of an open subgroup of the unit group is open in the ambient division ring.**

For a topological division ring `A` whose units are open and carry the subspace topology
(`IsOpenUnits`, automatic for fields such as the `𝔮`-adic completions), the image in `A` of a
left coset `u • N` of an open subgroup `N ≤ Aˣ` is open in `A`.  This is what makes the
`ℓ`-power class conditions of the Kummer argument open conditions on `K_𝔮`. -/
theorem isOpen_unitsVal_image_smul_subgroup {A : Type*} [DivisionRing A] [TopologicalSpace A]
    [IsTopologicalDivisionRing A] [IsOpenUnits A] (u : Aˣ) (N : Subgroup Aˣ)
    (hN : IsOpen (N : Set Aˣ)) :
    IsOpen ((fun x : Aˣ => (x : A)) '' (u • (N : Set Aˣ))) :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := A)).isOpenMap _ (hN.smul u)

/-- **The Kummer local surjection of §5**, deduced from weak approximation and the openness of
the local `ℓ`-th power subgroups.

See the module docstring: pick representatives `u_𝔮` of the prescribed local classes, note that
the cosets `u_𝔮 (K_𝔮ˣ)^ℓ` are open subsets of `K_𝔮`, and apply the density of `K` in the finite
product to obtain a global element with the required classes. -/
theorem isKummerSurjective_of_weakApproximation {K : Type*} [Field K] [NumberField K]
    (ℓ : ℕ) (S : Finset (NK.Chebotarev.PrimeIdeal K))
    (h : NK.UchidaKummer.IsWeakApproximation K S)
    (ho : NK.UchidaKummer.IsOpenEllPowSubgroup K ℓ) :
    NK.UchidaKummer.IsKummerSurjective K ℓ S := by
  intro y
  -- Representatives of the prescribed classes in `K_𝔮ˣ / (K_𝔮ˣ)^ℓ`.
  let u : ∀ 𝔮 : S, (𝔮.1.adicCompletion K)ˣ := fun 𝔮 => Quotient.out (y 𝔮)
  have hu : ∀ 𝔮 : S,
      QuotientGroup.mk' (ellPowSubgroup (𝔮.1.adicCompletion K) ℓ) (u 𝔮) = y 𝔮 := by
    intro 𝔮
    rw [QuotientGroup.mk'_apply]
    exact Quotient.out_eq (y 𝔮)
  -- The coset `u_𝔮 · (K_𝔮ˣ)^ℓ`, as an open subset of `K_𝔮`.
  have hcoset : ∀ 𝔮 : S, IsOpen
      ((fun x : (𝔮.1.adicCompletion K)ˣ => (x : 𝔮.1.adicCompletion K)) ''
        ((u 𝔮) • (ellPowSubgroup (𝔮.1.adicCompletion K) ℓ : Set (𝔮.1.adicCompletion K)ˣ))) :=
    fun 𝔮 => isOpen_unitsVal_image_smul_subgroup (u 𝔮)
      (ellPowSubgroup (𝔮.1.adicCompletion K) ℓ) (ho 𝔮.1)
  have hU : ∀ 𝔮 : S,
      ((fun x : (𝔮.1.adicCompletion K)ˣ => (x : 𝔮.1.adicCompletion K)) ''
        ((u 𝔮) • (ellPowSubgroup (𝔮.1.adicCompletion K) ℓ :
          Set (𝔮.1.adicCompletion K)ˣ))).Nonempty := by
    intro 𝔮
    exact ⟨(u 𝔮 : 𝔮.1.adicCompletion K), u 𝔮 * 1, ⟨1, one_mem _, by simp⟩, by simp⟩
  -- Weak approximation: a global element lying in every prescribed coset.
  obtain ⟨a, ha⟩ := exists_forall_mem_open_of_isWeakApproximation S h _ hcoset hU
  -- Each coset membership exhibits a witness in `(K_𝔮ˣ)^ℓ`.
  have hwit : ∀ 𝔮 : S, ∃ c : (𝔮.1.adicCompletion K)ˣ,
      c ∈ ellPowSubgroup (𝔮.1.adicCompletion K) ℓ ∧
      (u 𝔮 : 𝔮.1.adicCompletion K) * (c : 𝔮.1.adicCompletion K)
        = algebraMap K (𝔮.1.adicCompletion K) a := by
    intro 𝔮
    obtain ⟨z, hz, hzval⟩ := ha 𝔮
    obtain ⟨c, hc, hcz⟩ := hz
    refine ⟨c, hc, ?_⟩
    have hzval' : (z : 𝔮.1.adicCompletion K) = algebraMap K (𝔮.1.adicCompletion K) a := hzval
    have hcz' : (u 𝔮 * c : (𝔮.1.adicCompletion K)ˣ) = z := by simpa [smul_eq_mul] using hcz
    rw [← hzval', ← hcz']
    simp
  by_cases hS : S.Nonempty
  · -- `a` is nonzero away from the empty case, hence a unit of `K`.
    obtain ⟨𝔮₀, h𝔮₀⟩ := hS
    have ha0 : a ≠ 0 := by
      intro h0
      obtain ⟨c, _, hceq⟩ := hwit ⟨𝔮₀, h𝔮₀⟩
      rw [h0, map_zero] at hceq
      exact mul_ne_zero (Units.ne_zero (u ⟨𝔮₀, h𝔮₀⟩)) (Units.ne_zero c) hceq
    refine ⟨Units.mk0 a ha0, fun 𝔮 => ?_⟩
    obtain ⟨c, hc, hceq⟩ := hwit 𝔮
    -- The global class and the representative differ by an `ℓ`-th power locally.
    have huc : Units.map (algebraMap K (𝔮.1.adicCompletion K)).toMonoidHom (Units.mk0 a ha0)
        = u 𝔮 * c := by
      apply Units.ext
      rw [Units.coe_map, Units.val_mul, Units.val_mk0]
      exact hceq.symm
    simp only [localPowClass, MonoidHom.comp_apply]
    rw [huc, ← hu 𝔮, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hcc : (u 𝔮 * c)⁻¹ * u 𝔮 = c⁻¹ := by group
    rw [hcc]
    exact Subgroup.inv_mem _ hc
  · -- `S = ∅`: any global unit works.
    refine ⟨1, fun 𝔮 => ?_⟩
    exact absurd ⟨𝔮.1, 𝔮.2⟩ hS

end

end NK.UchidaKummer.Approximation
